/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Construction
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Sublists

/-!
# Effectivity, part 1: the value of a game is computable

The effectivity of the game value, used for `forces_computable` in `Verification.lean` and by
`Effectivity/StateTwin.lean`.  The game value `Arena.Forces` is decided by the instance
`decidableWinsF` (`Game.lean`), a recursion whose parameters change; its `Computable` proof goes
through a table of values on the finite box of states (positions below the starting position,
budgets below the starting budgets), computed level by level like `GD.tab` in
`RandomStrings/Effective/GameValues.lean`.

The list evaluator `forcesL` is primitive recursive and agrees with `forcesB`.  The correctness
and primitive-recursion proofs are split into small lemmas.

## Interface

`costU`, `valueL`, `forcesB`, `valueL_eq`, `costU_eq` and `forcesB_computable` are the
declarations used by `Effectivity/StateTwin.lean`.  The only project import is
`TTMeet2014.Construction`; all other imports are from Mathlib.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

/-- The weight of a list of strings in the units `2 ^ (-N)`: `cost (unitWeight N) l.toFinset`
when `l` has no duplicates (`costU_eq`). -/
def costU (N : ℕ) (l : List Str) : ℕ := (l.map (unitWeight N)).sum

/-- The outcome vector of a position given as a list: `ar.value B.toFinset` (`valueL_eq`). -/
def valueL (ar : Arena) (B : List Str) : List Bool :=
  ar.tables.map fun t => t.evalB fun z => decide (z ∈ B)

/-- The game value on list data: the set `S` of outcome vectors, given as a list, is winning in
`G(a, b)` at the position `A`, given as a list of strings. -/
def forcesB (ar : Arena) (S : List (List Bool)) (A : List Str) (a b : ℕ) : Bool :=
  decide (ar.Forces S.toFinset A.toFinset a b)

/-- List membership gives the same oracle as finset membership; use `List.mem_toFinset`. -/
theorem valueL_eq (ar : Arena) (B : List Str) : valueL ar B = ar.value B.toFinset := by
  simp [valueL, Arena.value]

/-- A duplicate-free list sums each weight once; use `List.sum_toFinset`. -/
theorem costU_eq {N : ℕ} {l : List Str} (hl : l.Nodup) :
    costU N l = cost (unitWeight N) l.toFinset := by
  exact (List.sum_toFinset (unitWeight N) hl).symm

/-- A position, the opponent's remaining budget, and our remaining budget. -/
abbrev State := List Str × ℕ × ℕ

/-- A finite table of Boolean values indexed by states. -/
abbrev Tbl := List (State × Bool)

/-- Lookup uses the first matching entry, and returns `false` when there is none. -/
def lookupT (v : State) (tbl : Tbl) : Bool :=
  tbl.foldr (fun p r => bif decide (p.1 = v) then p.2 else r) false

/-- Every subposition and every pair of budgets below the starting budgets. -/
def box (A₀ : List Str) (a₀ b₀ : ℕ) : List State :=
  A₀.sublists.flatMap fun A => (List.range (a₀ + 1)).flatMap fun a =>
    (List.range (b₀ + 1)).map fun b => (A, a, b)

/-- Boolean universal quantification, written as a fold for `Primrec.list_foldr`. -/
def allB {β : Type*} (l : List β) (p : β → Bool) : Bool :=
  l.foldr (fun a b => p a && b) true

/-- Boolean existential quantification, written as a fold for `Primrec.list_foldr`. -/
def anyB {β : Type*} (l : List β) (p : β → Bool) : Bool :=
  l.foldr (fun a b => p a || b) false

/-- Delete every string belonging to the move, retaining the order of the position. -/
def removeL (A m : List Str) : List Str := A.filter fun z => decide (z ∉ m)

/-- The state after the opponent's move and our reply. -/
def afterState (N : ℕ) (u : State) (m p : List Str) : State :=
  (removeL (removeL u.1 m) p, u.2.1 - costU N m, u.2.2 - costU N p)

/-- Test a reply, using the current outcome for a double pass and the preceding table otherwise. -/
def replyT (N : ℕ) (tables : List TTable) (S : List (List Bool))
    (u : State) (acc : Tbl) (m p : List Str) : Bool :=
  decide (costU N p ≤ u.2.2) &&
    (if m = [] ∧ p = [] then decide (valueL ⟨tables, N⟩ u.1 ∈ S)
     else lookupT (afterState N u m p) acc)

/-- An unaffordable opponent move is ignored; an affordable one needs a successful reply. -/
def moveT (N : ℕ) (tables : List TTable) (S : List (List Bool))
    (u : State) (acc : Tbl) (m : List Str) : Bool :=
  !(decide (costU N m ≤ u.2.1)) ||
    anyB (removeL u.1 m).sublists (replyT N tables S u acc m)

/-- One unfolding of `WinsF`, consulting `acc` for all recursive states. -/
def levelT (N : ℕ) (tables : List TTable) (S : List (List Bool))
    (u : State) (acc : Tbl) : Bool :=
  allB u.1.sublists (moveT N tables S u acc)

/-- Evaluate all states in a fixed box, one fuel level at a time. -/
def tab (N : ℕ) (tables : List TTable) (S : List (List Bool)) (U : List State) : ℕ → Tbl
  | 0 => U.map fun u => (u, decide (valueL ⟨tables, N⟩ u.1 ∈ S))
  | n + 1 => U.map fun u => (u, levelT N tables S u (tab N tables S U n))

/-- The list evaluator starts from the duplicate-free position and its finite box. -/
def forcesL (ar : Arena) (S : List (List Bool)) (A : List Str) (a b : ℕ) : Bool :=
  let A' := A.dedup
  lookupT (A', a, b) (tab ar.scale ar.tables S (box A' a b) A'.length)

/-- Expand the three finite enumerations with `List.mem_sublists` and `List.mem_range`. -/
theorem mem_box {A A₀ : List Str} {a b a₀ b₀ : ℕ} :
    (A, a, b) ∈ box A₀ a₀ b₀ ↔ A.Sublist A₀ ∧ a ≤ a₀ ∧ b ≤ b₀ := by
  simp [box, List.mem_sublists, Nat.lt_succ_iff]

/-- Lookup in a mapped table reads the associated function, even if keys repeat. -/
theorem lookupT_map (L : List State) (f : State → Bool) (v : State) (hv : v ∈ L) :
    lookupT v (L.map fun u => (u, f u)) = f v := by
  induction L with
  | nil => simp at hv
  | cons w L ih =>
    change (bif decide (w = v) then f w else lookupT v (L.map fun u => (u, f u))) = f v
    by_cases hw : w = v
    · subst hw; simp
    · simp only [hw, decide_false, Bool.cond_false]
      exact ih ((List.mem_cons.1 hv).resolve_left (Ne.symm hw))

/-- Represent a subset by filtering the original list; use `List.filter_sublist` and extensionality
with `List.mem_toFinset`, `List.mem_filter`, and the subset hypothesis. -/
theorem exists_sublist_toFinset {A : List Str} {s : Finset Str} (hs : s ⊆ A.toFinset) :
    ∃ l ∈ A.sublists, l.toFinset = s := by
  refine ⟨A.filter (fun z => decide (z ∈ s)), List.mem_sublists.2 List.filter_sublist, ?_⟩
  ext z
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hs h), h⟩⟩

/-- Replace a powerset universal quantifier using `exists_sublist_toFinset`; the other direction
uses `List.Sublist.subset` and `Finset.mem_powerset`.  No duplicate-free hypothesis is needed. -/
theorem forall_powerset_iff_sublists {A : List Str} (P : Finset Str → Prop) :
    (∀ m ∈ A.toFinset.powerset, P m) ↔ ∀ m ∈ A.sublists, P m.toFinset := by
  constructor
  · intro h m hm
    apply h _ (Finset.mem_powerset.2 ?_)
    intro z hz
    exact List.mem_toFinset.2 ((List.mem_sublists.1 hm).subset (List.mem_toFinset.1 hz))
  · intro h m hm
    obtain ⟨l, hl, rfl⟩ := exists_sublist_toFinset (Finset.mem_powerset.1 hm)
    exact h l hl

/-- Replace a powerset existential quantifier using `exists_sublist_toFinset` and, in the reverse
direction, `List.Sublist.subset` and `Finset.mem_powerset`. -/
theorem exists_powerset_iff_sublists {A : List Str} (P : Finset Str → Prop) :
    (∃ m ∈ A.toFinset.powerset, P m) ↔ ∃ m ∈ A.sublists, P m.toFinset := by
  constructor
  · rintro ⟨m, hm, hP⟩
    obtain ⟨l, hl, rfl⟩ := exists_sublist_toFinset (Finset.mem_powerset.1 hm)
    exact ⟨l, hl, hP⟩
  · rintro ⟨m, hm, hP⟩
    refine ⟨m.toFinset, Finset.mem_powerset.2 ?_, hP⟩
    intro z hz
    exact List.mem_toFinset.2 ((List.mem_sublists.1 hm).subset (List.mem_toFinset.1 hz))

/-- Filtering away list membership implements finset difference; prove by membership extensionality
using `List.mem_filter`, `List.mem_toFinset`, and `Finset.mem_sdiff`. -/
theorem toFinset_filter_not_mem (A m : List Str) :
    (A.filter (fun z => decide (z ∉ m))).toFinset = A.toFinset \ m.toFinset := by
  ext z
  simp

/-- The named deletion operation has the same finset as set difference. -/
theorem removeL_toFinset (A m : List Str) :
    (removeL A m).toFinset = A.toFinset \ m.toFinset :=
  toFinset_filter_not_mem A m

/-- A list represents the empty finset precisely when it is empty. -/
theorem toFinset_eq_empty_iff (l : List Str) : l.toFinset = ∅ ↔ l = [] :=
  List.toFinset_eq_empty_iff l

/-- A state in the box inherits `Nodup` from the starting position by `List.Sublist.nodup`. -/
theorem nodup_of_mem_box {A₀ A : List Str} {a₀ b₀ a b : ℕ}
    (hA₀ : A₀.Nodup) (hu : (A, a, b) ∈ box A₀ a₀ b₀) : A.Nodup :=
  (mem_box.1 hu).1.nodup hA₀

/-- Two filters only shorten the position and subtraction only decreases budgets; use
`List.filter_sublist`, `List.Sublist.trans`, `Nat.sub_le`, and `mem_box`. -/
theorem afterState_mem_box {A₀ : List Str} {a₀ b₀ N : ℕ} {u : State}
    (hu : u ∈ box A₀ a₀ b₀) (m p : List Str) :
    afterState N u m p ∈ box A₀ a₀ b₀ := by
  obtain ⟨hA, ha, hb⟩ := mem_box.1 hu
  exact mem_box.2 ⟨List.filter_sublist.trans (List.filter_sublist.trans hA),
    (Nat.sub_le _ _).trans ha, (Nat.sub_le _ _).trans hb⟩

/-- Interpret the universal fold; induction uses `Bool.and_eq_true` and `List.forall_mem_cons`. -/
theorem allB_iff {β : Type*} (l : List β) (p : β → Bool) :
    allB l p = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [allB]
  | cons x l ih => simp [allB, List.foldr_cons, ← ih]

/-- Interpret the existential fold; induction uses `Bool.or_eq_true` and `List.mem_cons`. -/
theorem anyB_iff {β : Type*} (l : List β) (p : β → Bool) :
    anyB l p = true ↔ ∃ x ∈ l, p x = true := by
  induction l with
  | nil => simp [anyB]
  | cons x l ih => simp [anyB, List.foldr_cons, ← ih]

/-- The universal fold agrees with `List.all` by their true-value characterizations. -/
theorem allB_eq_all {β : Type*} (l : List β) (p : β → Bool) : allB l p = l.all p := by
  rw [Bool.eq_iff_iff, allB_iff, List.all_eq_true]

/-- The existential fold agrees with `List.any` by their true-value characterizations. -/
theorem anyB_eq_any {β : Type*} (l : List β) (p : β → Bool) : anyB l p = l.any p := by
  rw [Bool.eq_iff_iff, anyB_iff, List.any_eq_true]

/-- Correctness of one reply.  Obtain `Nodup` for both moves by `List.Sublist.nodup` and
`nodup_of_mem_box`; rewrite the recursive lookup with `afterState_mem_box` and `hacc`, then use
`costU_eq`, `removeL_toFinset`, `valueL_eq`, and `toFinset_eq_empty_iff`. -/
theorem replyT_spec {N n a₀ b₀ : ℕ} {tables : List TTable} {S : List (List Bool)}
    {A₀ : List Str} {u : State} {acc : Tbl} (hA₀ : A₀.Nodup)
    (hu : u ∈ box A₀ a₀ b₀)
    (hacc : ∀ v ∈ box A₀ a₀ b₀, lookupT v acc =
      decide (WinsF (unitWeight N) (fun B => (Arena.mk tables N).value B ∈ S.toFinset)
        n v.1.toFinset v.2.1 v.2.2))
    {m p : List Str} (hm : m ∈ u.1.sublists) (hp : p ∈ (removeL u.1 m).sublists) :
    replyT N tables S u acc m p = decide (cost (unitWeight N) p.toFinset ≤ u.2.2 ∧
      if m.toFinset = ∅ ∧ p.toFinset = ∅ then (Arena.mk tables N).value u.1.toFinset ∈
        S.toFinset else WinsF (unitWeight N)
          (fun B => (Arena.mk tables N).value B ∈ S.toFinset) n
          ((u.1.toFinset \ m.toFinset) \ p.toFinset)
          (u.2.1 - cost (unitWeight N) m.toFinset)
          (u.2.2 - cost (unitWeight N) p.toFinset)) := by
  have hA := nodup_of_mem_box hA₀ hu
  have hmN := (List.mem_sublists.1 hm).nodup hA
  have hpN := (List.mem_sublists.1 hp).nodup (List.filter_sublist.nodup hA)
  rw [Bool.eq_iff_iff]
  by_cases hpass : m = [] ∧ p = []
  · rcases hpass with ⟨rfl, rfl⟩
    simp [replyT, costU, valueL_eq]
  · simp only [replyT, hpass, ite_false, Bool.and_eq_true, decide_eq_true_iff,
      toFinset_eq_empty_iff]
    rw [hacc _ (afterState_mem_box (N := N) hu m p), decide_eq_true_iff]
    simp only [afterState, removeL_toFinset, costU_eq hmN, costU_eq hpN]

/-- Correctness for one opponent move. -/
theorem moveT_spec {N n a₀ b₀ : ℕ} {tables : List TTable} {S : List (List Bool)}
    {A₀ : List Str} {u : State} {acc : Tbl} (hA₀ : A₀.Nodup)
    (hu : u ∈ box A₀ a₀ b₀)
    (hacc : ∀ v ∈ box A₀ a₀ b₀, lookupT v acc =
      decide (WinsF (unitWeight N) (fun B => (Arena.mk tables N).value B ∈ S.toFinset)
        n v.1.toFinset v.2.1 v.2.2))
    {m : List Str} (hm : m ∈ u.1.sublists) :
    moveT N tables S u acc m = decide (cost (unitWeight N) m.toFinset ≤ u.2.1 →
      ∃ p ∈ (u.1.toFinset \ m.toFinset).powerset, cost (unitWeight N) p ≤ u.2.2 ∧
        if m.toFinset = ∅ ∧ p = ∅ then (Arena.mk tables N).value u.1.toFinset ∈
          S.toFinset else WinsF (unitWeight N)
            (fun B => (Arena.mk tables N).value B ∈ S.toFinset) n
            ((u.1.toFinset \ m.toFinset) \ p)
            (u.2.1 - cost (unitWeight N) m.toFinset) (u.2.2 - cost (unitWeight N) p)) := by
  have hmN := (List.mem_sublists.1 hm).nodup (nodup_of_mem_box hA₀ hu)
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  by_cases hb : cost (unitWeight N) m.toFinset ≤ u.2.1
  · simp only [moveT, costU_eq hmN, hb, decide_true, Bool.not_true, Bool.false_or,
      anyB_iff, true_implies]
    rw [← removeL_toFinset u.1 m, exists_powerset_iff_sublists]
    refine exists_congr fun p => and_congr_right fun hp => ?_
    simpa only [removeL_toFinset, decide_eq_true_iff] using
      (Bool.eq_iff_iff.1 (replyT_spec hA₀ hu hacc hm hp))
  · simp [moveT, costU_eq hmN, hb]

/-- Assemble the opponent-move tests using `allB_iff`, `forall_powerset_iff_sublists`, and
`moveT_spec`, after unfolding `WinsF` once. -/
theorem levelT_spec {N n a₀ b₀ : ℕ} {tables : List TTable} {S : List (List Bool)}
    {A₀ : List Str} {u : State} {acc : Tbl} (hA₀ : A₀.Nodup)
    (hu : u ∈ box A₀ a₀ b₀)
    (hacc : ∀ v ∈ box A₀ a₀ b₀, lookupT v acc =
      decide (WinsF (unitWeight N) (fun B => (Arena.mk tables N).value B ∈ S.toFinset)
        n v.1.toFinset v.2.1 v.2.2)) :
    levelT N tables S u acc = decide (WinsF (unitWeight N)
      (fun B => (Arena.mk tables N).value B ∈ S.toFinset) (n + 1)
      u.1.toFinset u.2.1 u.2.2) := by
  rw [Bool.eq_iff_iff]
  simp only [levelT, allB_iff, decide_eq_true_iff, WinsF,
    forall_powerset_iff_sublists]
  exact forall₂_congr fun m hm => by rw [moveT_spec hA₀ hu hacc hm, decide_eq_true_iff]

/-- Correctness at every fuel level follows by induction, `lookupT_map`, and `levelT_spec`. -/
theorem tab_spec {N a₀ b₀ : ℕ} {tables : List TTable} {S : List (List Bool)}
    {A₀ : List Str} (hA₀ : A₀.Nodup) (n : ℕ) :
    ∀ v ∈ box A₀ a₀ b₀, lookupT v (tab N tables S (box A₀ a₀ b₀) n) =
      decide (WinsF (unitWeight N) (fun B => (Arena.mk tables N).value B ∈ S.toFinset)
        n v.1.toFinset v.2.1 v.2.2) := by
  induction n with
  | zero =>
    intro v hv
    rw [tab, lookupT_map _ _ _ hv]
    simp [WinsF, valueL_eq]
  | succ n ih =>
    intro v hv
    rw [tab, lookupT_map _ _ _ hv]
    exact levelT_spec hA₀ hv ih

/-- Tabulation at the initial state gives the original game. -/
theorem forcesL_eq (ar : Arena) (S : List (List Bool)) (A : List Str) (a b : ℕ) :
    forcesL ar S A a b = forcesB ar S A a b := by
  have hv : (A.dedup, a, b) ∈ box A.dedup a b :=
    mem_box.2 ⟨List.Sublist.refl _, le_rfl, le_rfl⟩
  unfold forcesL
  rw [tab_spec (List.nodup_dedup A) _ _ hv]
  have hcard : A.toFinset.card = A.dedup.length := by
    simpa using List.toFinset_card_of_nodup (List.nodup_dedup A)
  simp only [List.toFinset_dedup]
  cases ar
  simp only [forcesB, Arena.Forces, Forces, Wins, Arena.w, hcard]

/-- The defining recursion has a fixed table accumulator, as required by `Primrec.nat_rec`. -/
theorem tab_eq_nat_rec (N : ℕ) (tables : List TTable) (S : List (List Bool))
    (U : List State) (n : ℕ) :
    tab N tables S U n = Nat.rec (U.map fun u => (u, decide (valueL ⟨tables, N⟩ u.1 ∈ S)))
      (fun _ acc => U.map fun u => (u, levelT N tables S u acc)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tab, ih]

/-- An arena is encoded by its tables and scale; there is no quotient data in this encoding. -/
def arenaEquiv : Arena ≃ List TTable × ℕ where
  toFun ar := (ar.tables, ar.scale)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The product encoding makes all arena fields primitive codable. -/
instance arenaPrimcodable : Primcodable Arena := Primcodable.ofEquiv _ arenaEquiv

/-- Reading the tables is a product projection after `Primrec.of_equiv`. -/
theorem arena_tables_primrec : Primrec Arena.tables :=
  Primrec.fst.comp (Primrec.of_equiv (e := arenaEquiv))

/-- Reading the scale is a product projection after `Primrec.of_equiv`. -/
theorem arena_scale_primrec : Primrec Arena.scale :=
  Primrec.snd.comp (Primrec.of_equiv (e := arenaEquiv))

/-- Constructing an arena is the inverse of its primitive-recursive product equivalence. -/
theorem arena_mk_primrec : Primrec₂ Arena.mk :=
  (Primrec.of_equiv_symm (e := arenaEquiv)).to₂

/-- Uniform universal folds use `Primrec.list_foldr` and `Primrec.and`. -/
theorem allB_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {p : α → β → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec fun a => allB (l a) (p a) :=
  Primrec.list_foldr hl (Primrec.const true)
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- Uniform existential folds use `Primrec.list_foldr` and `Primrec.or`. -/
theorem anyB_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {p : α → β → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec fun a => anyB (l a) (p a) :=
  Primrec.list_foldr hl (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- Test membership by `List.idxOf < List.length`; use `Primrec.list_idxOf`,
`Primrec.nat_lt.decide`, `Primrec.list_length`, and `List.idxOf_lt_length_iff`. -/
theorem list_mem_decide_primrec {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec₂ fun (z : α) (l : List α) => decide (z ∈ l) := by
  refine (Primrec.nat_lt.decide.comp Primrec.list_idxOf
    (Primrec.list_length.comp Primrec.snd)).of_eq ?_
  intro q
  rw [decide_eq_decide]
  exact List.idxOf_lt_length_iff

/-- String membership is the specialization of `list_mem_decide_primrec`. -/
theorem mem_decide_primrec : Primrec₂ fun (z : Str) (l : List Str) => decide (z ∈ l) :=
  (list_mem_decide_primrec (α := Str)).of_eq fun _ _ => by rw [Bool.eq_iff_iff]; simp

/-- Compose exponentiation (`Primrec₂.unpaired'.1 Nat.Primrec.pow`) with length, addition and
truncated subtraction. -/
theorem unitWeight_primrec : Primrec₂ unitWeight := by
  exact ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
      (Primrec.list_length.comp Primrec.snd))).of_eq fun _ => rfl

/-- Summing the mapped weights is a fold of additions; induct on the list using `List.sum_cons`
and `List.map_cons` to identify it with `costU`. -/
theorem costU_eq_foldr (N : ℕ) (l : List Str) :
    costU N l = l.foldr (fun z acc => unitWeight N z + acc) 0 := by
  induction l with
  | nil => rfl
  | cons z l ih => simpa [costU] using congrArg (unitWeight N z + ·) ih

/-- Apply `Primrec.list_foldr` with `unitWeight_primrec` and `Primrec.nat_add`, then rewrite with
`costU_eq_foldr`. -/
theorem costU_primrec : Primrec₂ costU := by
  have h : Primrec fun q : ℕ × List Str =>
      q.2.foldr (fun z acc => unitWeight q.1 z + acc) 0 :=
    Primrec.list_foldr Primrec.snd (Primrec.const 0)
      (Primrec.nat_add.comp
        (unitWeight_primrec.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun q => (costU_eq_foldr q.1 q.2).symm

/-- A clause is a universal fold of Boolean equality tests; use `allB_primrec`,
`mem_decide_primrec`, `Primrec.eq.decide`, and `Clause.holds_eq_true`. -/
theorem clauseHolds_primrec :
    Primrec₂ fun (B : List Str) (c : Clause) => c.holds (fun z => decide (z ∈ B)) := by
  have h : Primrec fun q : List Str × Clause =>
      allB q.2 (fun r => decide (decide (r.1 ∈ q.1) = r.2)) :=
    allB_primrec Primrec.snd (Primrec.eq.decide.comp
      (mem_decide_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)).to₂
  refine h.of_eq fun q => ?_
  rw [Bool.eq_iff_iff, allB_iff, Clause.holds_eq_true]
  simp only [decide_eq_true_iff]

/-- A table is an existential fold over its clauses; use `anyB_primrec`,
`clauseHolds_primrec`, and `anyB_eq_any`. -/
theorem evalTable_primrec :
    Primrec₂ fun (B : List Str) (t : TTable) => t.evalB (fun z => decide (z ∈ B)) := by
  have h : Primrec fun q : List Str × TTable =>
      anyB q.2 (fun c => c.holds (fun z => decide (z ∈ q.1))) :=
    anyB_primrec Primrec.snd
      (clauseHolds_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact h.of_eq fun q => anyB_eq_any q.2 _

/-- Map the table evaluator over the arena's tables with `Primrec.list_map`. -/
theorem valueL_primrec : Primrec₂ valueL := by
  exact Primrec.list_map (arena_tables_primrec.comp Primrec.fst)
    (evalTable_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

/-- `List.sublists` is a fold that doubles the accumulator; induct using `List.sublists_cons`. -/
theorem sublists_eq_foldr (A : List Str) :
    A.sublists = A.foldr (fun z acc => acc.flatMap fun l => [l, z :: l]) [[]] := by
  induction A with
  | nil => rfl
  | cons z A ih => simp only [List.sublists_cons, List.foldr_cons, ih, List.bind_eq_flatMap]

/-- Use `Primrec.list_foldr` with `Primrec.list_flatMap` and `Primrec.list_cons`, then
`sublists_eq_foldr`; the accumulator step is `acc.flatMap (fun l => [l, z :: l])`. -/
theorem sublists_primrec : Primrec (List.sublists : List Str → List (List Str)) := by
  have h : Primrec fun A : List Str =>
      A.foldr (fun z acc => acc.flatMap fun l => [l, z :: l]) [[]] :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp Primrec.snd (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd) (Primrec.const []))).to₂).to₂
  exact h.of_eq fun A => (sublists_eq_foldr A).symm

/-- Deduplication is a membership-guarded fold; induct using `List.dedup_cons'`. -/
theorem dedup_eq_foldr (A : List Str) :
    A.dedup = A.foldr (fun z acc => if z ∈ acc then acc else z :: acc) [] := by
  induction A with
  | nil => rfl
  | cons z A ih => simp only [List.dedup_cons', List.foldr_cons, ih]

/-- Fold using `Primrec.cond`, `mem_decide_primrec`, and `Primrec.list_cons`; identify the fold
by `dedup_eq_foldr` and `Bool.cond_decide`. -/
theorem dedup_primrec : Primrec (List.dedup : List Str → List Str) := by
  have h : Primrec fun A : List Str =>
      A.foldr (fun z acc => bif decide (z ∈ acc) then acc else z :: acc) [] :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.cond (mem_decide_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun A => by
    simpa only [Bool.cond_decide] using (dedup_eq_foldr A).symm

/-- Filtering is a guarded cons fold; induct on the list using `List.filter_cons`. -/
theorem removeL_eq_foldr (A m : List Str) :
    removeL A m = A.foldr (fun z acc => if z ∈ m then acc else z :: acc) [] := by
  induction A with
  | nil => rfl
  | cons z A ih =>
    rw [List.foldr_cons, ← ih]
    by_cases hz : z ∈ m <;> simp [removeL, hz]

/-- Use `Primrec.list_foldr`, a conditional membership test (`mem_decide_primrec`), and cons;
identify the fold by `removeL_eq_foldr`. -/
theorem removeL_primrec : Primrec₂ removeL := by
  have h : Primrec fun q : List Str × List Str =>
      q.1.foldr (fun z acc => bif decide (z ∈ q.2) then acc else z :: acc) [] :=
    Primrec.list_foldr Primrec.fst (Primrec.const [])
      (Primrec.cond (mem_decide_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun q => by
    simpa only [Bool.cond_decide] using (removeL_eq_foldr q.1 q.2).symm

/-- Enumerate sublists, two `List.range`s and state triples via `Primrec.list_flatMap`,
`Primrec.list_range`, `Primrec.nat_add`, and `Primrec.list_map`. -/
theorem box_primrec : Primrec fun q : List Str × ℕ × ℕ => box q.1 q.2.1 q.2.2 := by
  exact (Primrec.list_flatMap (sublists_primrec.comp Primrec.fst)
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 1)))
      (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.const 1)))
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂).to₂).of_eq fun _ => rfl

/-- A lookup is a fold using `Primrec.eq.decide` and `Primrec.cond`; no unique-key hypothesis
is needed. -/
theorem lookupT_primrec : Primrec₂ lookupT := by
  exact (Primrec.list_foldr (f := fun q : State × Tbl => q.2) (g := fun _ => false)
    (h := fun q p => bif decide (p.1.1 = q.1) then p.1.2 else p.2)
    Primrec.snd (Primrec.const false)
    (Primrec.cond (Primrec.eq.decide.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

/-- Compose two `removeL_primrec` calls and two truncated subtractions (`Primrec.nat_sub`)
of `costU_primrec`; assemble the three coordinates using `Primrec.pair`. -/
theorem afterState_primrec : Primrec fun q : ℕ × State × List Str × List Str =>
    afterState q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hN : Primrec fun q : ℕ × State × List Str × List Str => q.1 := Primrec.fst
  have hu : Primrec fun q : ℕ × State × List Str × List Str => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hm : Primrec fun q : ℕ × State × List Str × List Str => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hp : Primrec fun q : ℕ × State × List Str × List Str => q.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((removeL_primrec.comp (removeL_primrec.comp (Primrec.fst.comp hu) hm) hp).pair
    ((Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp hu))
      (costU_primrec.comp hN hm)).pair
      (Primrec.nat_sub.comp (Primrec.snd.comp (Primrec.snd.comp hu))
        (costU_primrec.comp hN hp)))).of_eq fun _ => rfl

/-- Parameters shared by every entry in a table: scale, tables, and the target vectors. -/
abbrev GameArgs := ℕ × List TTable × List (List Bool)

/-- Parameters of one transition: game data, the current state, and the preceding table. -/
abbrev EvalArgs := GameArgs × State × Tbl

/-- Primitive recursion of one reply uses `Primrec.nat_le.decide`, `costU_primrec`,
`Primrec.cond` on two empty-list tests, `valueL_primrec`, `mem_decide_primrec`,
`afterState_primrec`, and `lookupT_primrec`. -/
theorem replyT_primrec : Primrec fun q : (EvalArgs × List Str) × List Str =>
    replyT q.1.1.1.1 q.1.1.1.2.1 q.1.1.1.2.2 q.1.1.2.1 q.1.1.2.2 q.1.2 q.2 := by
  have hctx : Primrec fun q : (EvalArgs × List Str) × List Str => q.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hdata := Primrec.fst.comp hctx
  have hN := Primrec.fst.comp hdata
  have hu := Primrec.fst.comp (Primrec.snd.comp hctx)
  have hacc := Primrec.snd.comp (Primrec.snd.comp hctx)
  have hm : Primrec fun q : (EvalArgs × List Str) × List Str => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hp : Primrec fun q : (EvalArgs × List Str) × List Str => q.2 := Primrec.snd
  have hlegal := Primrec.nat_le.decide.comp (costU_primrec.comp hN hp)
    (Primrec.snd.comp (Primrec.snd.comp hu))
  have hpass := Primrec.and.comp (Primrec.eq.decide.comp hm (Primrec.const []))
    (Primrec.eq.decide.comp hp (Primrec.const []))
  have htarget := mem_decide_primrec.comp
    (valueL_primrec.comp (arena_mk_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp hdata)) hN) (Primrec.fst.comp hu))
    (Primrec.snd.comp (Primrec.snd.comp hdata))
  have hrec := lookupT_primrec.comp
    (afterState_primrec.comp (hN.pair (hu.pair (hm.pair hp)))) hacc
  refine (Primrec.and.comp hlegal (Primrec.cond hpass htarget hrec)).of_eq fun q => ?_
  simp only [← Bool.decide_and, Bool.cond_decide]
  rfl

/-- Fold over replies with `anyB_primrec` and `replyT_primrec`; combine with the negated budget
test using `Primrec.or`, `Primrec.not`, `costU_primrec`, and `Primrec.nat_le.decide`. -/
theorem moveT_primrec : Primrec fun q : EvalArgs × List Str =>
    moveT q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2.1 q.1.2.2 q.2 := by
  have hN : Primrec fun q : EvalArgs × List Str => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec fun q : EvalArgs × List Str => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hany : Primrec fun q : EvalArgs × List Str =>
      anyB (removeL q.1.2.1.1 q.2).sublists
        (replyT q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2.1 q.1.2.2 q.2) :=
    anyB_primrec (sublists_primrec.comp
      (removeL_primrec.comp (Primrec.fst.comp hu) Primrec.snd)) replyT_primrec.to₂
  exact (Primrec.or.comp (Primrec.not.comp (Primrec.nat_le.decide.comp
    (costU_primrec.comp hN Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp hu))))
    hany).of_eq fun _ => rfl

/-- Assemble the outer universal fold using `allB_primrec`, `sublists_primrec`, and
`moveT_primrec`. -/
theorem levelT_primrec : Primrec fun q : (ℕ × List TTable × List (List Bool)) × State × Tbl =>
    levelT q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
  exact allB_primrec (sublists_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
    moveT_primrec.to₂

/-- The initial table is a primitive-recursive map of terminal outcome tests; use
`Primrec.list_map`, `valueL_primrec`, `arena_mk_primrec`, and `mem_decide_primrec`. -/
theorem tab_zero_primrec : Primrec fun q : GameArgs × List State =>
    q.2.map fun u => (u, decide (valueL ⟨q.1.2.1, q.1.1⟩ u.1 ∈ q.1.2.2)) := by
  have hdata : Primrec fun q : (GameArgs × List State) × State => q.1.1 :=
    Primrec.fst.comp Primrec.fst
  exact Primrec.list_map Primrec.snd
    (Primrec.snd.pair (mem_decide_primrec.comp
      (valueL_primrec.comp (arena_mk_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp hdata)) (Primrec.fst.comp hdata))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp hdata)))).to₂

/-- A table update maps `levelT_primrec` over the fixed state list using `Primrec.list_map`. -/
theorem tab_step_primrec : Primrec fun q : (GameArgs × List State) × Tbl =>
    q.1.2.map fun u =>
      (u, levelT q.1.1.1 q.1.1.2.1 q.1.1.2.2 u q.2) := by
  have hdata : Primrec fun q : ((GameArgs × List State) × Tbl) × State => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  exact Primrec.list_map (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.pair (levelT_primrec.comp
      (hdata.pair (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))))).to₂

/-- Tabulation is a fixed-parameter `Primrec.nat_rec`, with the initial and update maps proved
separately; `tab_eq_nat_rec` identifies the recursion. -/
theorem tab_primrec : Primrec fun q : ((ℕ × List TTable × List (List Bool)) × List State) × ℕ =>
    tab q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 q.2 := by
  have h := Primrec.nat_rec tab_zero_primrec
    (tab_step_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun q n => (tab_eq_nat_rec q.1.1 q.1.2.1 q.1.2.2 q.2 n).symm

/-- Compose `dedup_primrec`, `box_primrec`, `tab_primrec`, `Primrec.list_length`, and
`lookupT_primrec` at the initial state; all parameters are product projections. -/
theorem forcesL_primrec :
    Primrec fun p : (List TTable × ℕ) × List (List Bool) × List Str × ℕ × ℕ =>
      forcesL ⟨p.1.1, p.1.2⟩ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  let D := (List TTable × ℕ) × List (List Bool) × List Str × ℕ × ℕ
  have hN : Primrec fun p : D => p.1.2 := Primrec.snd.comp Primrec.fst
  have htables : Primrec fun p : D => p.1.1 := Primrec.fst.comp Primrec.fst
  have hS : Primrec fun p : D => p.2.1 := Primrec.fst.comp Primrec.snd
  have hA : Primrec fun p : D => p.2.2.1.dedup :=
    dedup_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec fun p : D => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun p : D => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (lookupT_primrec.comp (hA.pair (ha.pair hb))
    (tab_primrec.comp (((hN.pair (htables.pair hS)).pair
      (box_primrec.comp (hA.pair (ha.pair hb)))).pair
      (Primrec.list_length.comp hA)))).of_eq fun _ => rfl

/-- **The value of a game is computable** from its finite description: tables, unit, target,
position and budgets. -/
theorem forcesB_computable :
    Computable fun p : (List TTable × ℕ) × List (List Bool) × List Str × ℕ × ℕ =>
      forcesB ⟨p.1.1, p.1.2⟩ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  exact forcesL_primrec.to_comp.of_eq fun p => forcesL_eq _ _ _ _ _

end Kolmogorov.RandomStrings.TTMeet
