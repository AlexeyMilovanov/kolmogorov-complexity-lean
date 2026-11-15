/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Computability.Halting
import Mathlib.Data.List.GetD

/-!
# Effective finite truth tables and unbounded truth-table reducibility

Section 1.1 of Cai, Downey, Epstein, Lempp, Miller (LMCS 10(3:15), 2014) defines a tt-reduction
by two computable functions: `f m` bounds the use and `g m` lists the output for each row
`σ ∈ 2 ^ f m`.  Here a table is a finite object over strings:

* `TTable`: a list of clauses (a disjunctive normal form).  `ofRows` turns a query list with its
  accepting rows into a table, with `evalB_ofRows`, so the paper's rows are a special case; a
  table's queries are `TTable.queries`.
* `TTReducible X R`: a *total computable* table generator whose table evaluates correctly on the
  actual oracle.  This is the classical unbounded reducibility, and it is not the polynomial-time
  class `PolyTimeTT` of `RandomStrings/TT.lean`.
* `tableAt i k s`: the effective enumeration of partial generators with stage convergence
  (`tableAt_mono`, `tableAt_eq_none_of_le`, `tableAt_primrec`), and `exists_index`: every total
  computable generator has an index.  The paper's pairs `⟨i_f, i_g⟩` are replaced by one index for
  the whole table.  Argument `k` is the `k`-th bit, naming the string `strOf k`
  (`strOf_encode`, a computable surjection `ℕ → Str`).

This module depends only on Mathlib.  `Str` is `List Bool`, which is definitionally
`Kolmogorov.BitString`.
-/

namespace Kolmogorov.RandomStrings.TTMeet

/-- Strings; `List Bool` is definitionally `Kolmogorov.BitString`. -/
abbrev Str : Type := List Bool

/-- A conjunction of literals `z ∈ oracle ↔ b`. -/
abbrev Clause : Type := List (Str × Bool)

/-- A finite truth table, as a disjunction of clauses. -/
abbrev TTable : Type := List Clause

/-- The clause holds on the oracle `o`. -/
def Clause.holds (c : Clause) (o : Str → Bool) : Bool :=
  c.all fun q => o q.1 == q.2

/-- The value of a table on the oracle `o`. -/
def TTable.evalB (t : TTable) (o : Str → Bool) : Bool :=
  t.any fun c => c.holds o

/-- The strings mentioned by a table. -/
def TTable.queries (t : TTable) : List Str :=
  t.flatMap fun c => c.map Prod.fst

/-- A clause holds on `o` iff all its literals do: `o z = b` for every `(z, b)` in it. -/
theorem Clause.holds_eq_true {c : Clause} {o : Str → Bool} :
    c.holds o = true ↔ ∀ q ∈ c, o q.1 = q.2 := by
  simp [Clause.holds]

/-- A table evaluates to `true` on `o` iff one of its clauses holds on `o`. -/
theorem TTable.evalB_eq_true {t : TTable} {o : Str → Bool} :
    t.evalB o = true ↔ ∃ c ∈ t, c.holds o = true := by
  simp [TTable.evalB]

/-- The queries of a table are the strings occurring in a literal of one of its clauses. -/
theorem TTable.mem_queries {t : TTable} {z : Str} :
    z ∈ t.queries ↔ ∃ c ∈ t, ∃ b, (z, b) ∈ c := by
  simp only [TTable.queries, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨c, hc, ⟨z', b⟩, hq, rfl⟩
    exact ⟨c, hc, b, hq⟩
  · rintro ⟨c, hc, b, hq⟩
    exact ⟨c, hc, (z, b), hq, rfl⟩

/-- The value of a table depends only on the oracle's values on its queries. -/
theorem TTable.evalB_congr {t : TTable} {o o' : Str → Bool}
    (h : ∀ z ∈ t.queries, o z = o' z) : t.evalB o = t.evalB o' := by
  have key : ∀ c ∈ t, c.holds o = c.holds o' := by
    intro c hc
    rw [Bool.eq_iff_iff, Clause.holds_eq_true, Clause.holds_eq_true]
    refine forall₂_congr fun q hq => ?_
    rw [h q.1 (TTable.mem_queries.2 ⟨c, hc, q.2, by simpa using hq⟩)]
  rw [Bool.eq_iff_iff, TTable.evalB_eq_true, TTable.evalB_eq_true]
  exact exists_congr fun c => and_congr_right fun hc => by rw [key c hc]

/-! ### Rows: the paper's form of a table -/

/-- The table with query list `Q` accepting exactly the listed rows. -/
def ofRows (Q : List Str) (rows : List (List Bool)) : TTable :=
  (rows.filter fun r => r.length == Q.length).map fun r => Q.zip r

/-- A zipped clause holds iff the row is the vector of answers. -/
theorem holds_zip (Q : List Str) (r : List Bool) (o : Str → Bool) (h : r.length = Q.length) :
    Clause.holds (Q.zip r) o = true ↔ Q.map o = r := by
  induction Q generalizing r with
  | nil =>
    have : r = [] := List.length_eq_zero_iff.1 (by simpa using h)
    subst this
    simp [Clause.holds]
  | cons z Q ih =>
    obtain _ | ⟨b, r⟩ := r
    · simp at h
    · have hr : r.length = Q.length := by simpa using h
      have := ih r hr
      simp only [Clause.holds, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq,
        List.map_cons, List.cons.injEq] at this ⊢
      rw [this]

/-- `ofRows` evaluates by looking the vector of answers up in the rows. -/
theorem evalB_ofRows (Q : List Str) (rows : List (List Bool)) (o : Str → Bool) :
    (ofRows Q rows).evalB o = decide (Q.map o ∈ rows) := by
  rw [Bool.eq_iff_iff, TTable.evalB_eq_true, decide_eq_true_iff]
  simp only [ofRows, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨c, ⟨r, ⟨hr, hl⟩, rfl⟩, hc⟩
    rwa [(holds_zip Q r o hl).1 hc]
  · intro h
    exact ⟨_, ⟨Q.map o, ⟨h, by simp⟩, rfl⟩, (holds_zip Q _ o (by simp)).2 rfl⟩

/-! ### Oracles as sets, reducibility -/

open Classical in
/-- The characteristic function of a set of strings.  Oracles are sets (`prefixRandom U`); this is
the one place where a set is turned into a Boolean function, and it is never used by the stage
construction. -/
noncomputable def chi (R : Set Str) : Str → Bool := fun z => decide (z ∈ R)

/-- `chi R z` is `true` iff `z ∈ R`. -/
@[simp] theorem chi_eq_true {R : Set Str} {z : Str} : chi R z = true ↔ z ∈ R := by
  simp [chi]

/-- The table accepts on the oracle `R`. -/
def TTable.Accepts (t : TTable) (R : Set Str) : Prop := t.evalB (chi R) = true

/-- The generator `g` computes `X` from the oracle `R`. -/
def IsTTReduction (g : Str → TTable) (X R : Set Str) : Prop :=
  ∀ x, x ∈ X ↔ (g x).Accepts R

/-- Unbounded truth-table reducibility: a total computable generator of finite tables. -/
def TTReducible (X R : Set Str) : Prop :=
  ∃ g : Str → TTable, Computable g ∧ IsTTReduction g X R

/-! ### Computable sets are tt-reducible to anything -/

/-- A computable set is tt-reducible to every oracle: the table asks nothing. -/
theorem ttReducible_of_computablePred {X : Set Str}
    (hX : ComputablePred fun x => x ∈ X) (R : Set Str) : TTReducible X R := by
  obtain ⟨f, hf, hfX⟩ := ComputablePred.computable_iff.1 hX
  refine ⟨fun x => bif f x then [[]] else [], ?_, fun x => ?_⟩
  · exact Computable.cond hf (Computable.const _) (Computable.const _)
  · have hx : x ∈ X ↔ f x = true := by
      have := congrFun hfX x
      exact iff_of_eq this
    rw [hx]
    change f x = true ↔ TTable.Accepts (bif f x then [[]] else []) R
    cases f x <;> simp [TTable.Accepts, TTable.evalB, Clause.holds]

/-! ### The enumeration of partial generators -/

/-- The `k`-th string of the computable surjection `ℕ → Str`. -/
def strOf (k : ℕ) : Str := (Encodable.decode k : Option Str).getD []

/-- `strOf` inverts `Encodable.encode`; in particular every string is `strOf k` for some `k`. -/
@[simp] theorem strOf_encode (x : Str) : strOf (Encodable.encode x) = x := by
  simp [strOf]

/-- `strOf` is primitive recursive. -/
theorem strOf_primrec : Primrec strOf :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- Stage `s` of the `i`-th partial generator on the bit `k`: the `s`-step evaluation of the code
with number `i`, read as a table.  `none` means undefined so far, or not a table. -/
def tableAt (i k s : ℕ) : Option TTable :=
  (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code i) k).bind Encodable.decode

/-- Stage approximations are primitive recursive, uniformly in the index. -/
theorem tableAt_primrec : Primrec fun p : ℕ × ℕ × ℕ => tableAt p.1 p.2.1 p.2.2 := by
  have h1 : Primrec fun p : ℕ × ℕ × ℕ =>
      Nat.Partrec.Code.evaln p.2.2 (Denumerable.ofNat Nat.Partrec.Code p.1) p.2.1 :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.snd.comp Primrec.snd).pair
          ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst)).pair
        (Primrec.fst.comp Primrec.snd))
  exact Primrec.option_bind h1 ((Primrec.decode (α := TTable)).comp Primrec.snd).to₂

/-- Convergence is stable, with the same table. -/
theorem tableAt_mono {i k s s' : ℕ} {t : TTable} (hs : s ≤ s') (h : tableAt i k s = some t) :
    tableAt i k s' = some t := by
  unfold tableAt at h ⊢
  obtain ⟨n, hn, hd⟩ := Option.bind_eq_some_iff.1 h
  rw [Nat.Partrec.Code.evaln_mono hs hn]
  simpa using hd

/-- Nothing converges on the bit `k` before stage `k + 1`, so at each stage only finitely many
tables are defined. -/
theorem tableAt_eq_none_of_le {i k s : ℕ} (h : s ≤ k) : tableAt i k s = none := by
  unfold tableAt
  cases hn : Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code i) k with
  | none => rfl
  | some n =>
    have := Nat.Partrec.Code.evaln_bound (Option.mem_def.2 hn)
    omega

/-- A table is unique across stages. -/
theorem tableAt_unique {i k s s' : ℕ} {t t' : TTable} (h : tableAt i k s = some t)
    (h' : tableAt i k s' = some t') : t = t' := by
  have := tableAt_mono (le_max_left s s') h
  rw [tableAt_mono (le_max_right s s') h'] at this
  exact (Option.some.inj this).symm

/-- The `i`-th partial generator is total. -/
def IsTotalGen (i : ℕ) : Prop := ∀ k, ∃ s t, tableAt i k s = some t

/-- Every total computable generator has an index in the enumeration. -/
theorem exists_index {g : Str → TTable} (hg : Computable g) :
    ∃ i, ∀ k, (∃ s, tableAt i k s = some (g (strOf k))) ∧
      ∀ s t, tableAt i k s = some t → t = g (strOf k) := by
  have hf : Computable fun k : ℕ => Encodable.encode (g (strOf k)) :=
    Computable.encode.comp (hg.comp strOf_primrec.to_comp)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf.partrec)
  refine ⟨Encodable.encode c, fun k => ?_⟩
  have hmem : ∀ s n, Nat.Partrec.Code.evaln s c k = some n →
      n = Encodable.encode (g (strOf k)) := by
    intro s n hn
    have h := Nat.Partrec.Code.evaln_sound (Option.mem_def.2 hn)
    rw [hc, PFun.coe_val] at h
    exact Part.mem_some_iff.1 h
  have hsome : tableAt (Encodable.encode c) k =
      fun s => (Nat.Partrec.Code.evaln s c k).bind Encodable.decode := by
    funext s
    simp [tableAt]
  constructor
  · have h : Encodable.encode (g (strOf k)) ∈ c.eval k := by
      rw [hc]
      simp
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.1 h
    refine ⟨s, ?_⟩
    rw [hsome]
    simp [Option.mem_def.1 hs]
  · intro s t ht
    rw [hsome] at ht
    obtain ⟨n, hn, hd⟩ := Option.bind_eq_some_iff.1 ht
    rw [hmem s n hn] at hd
    simpa using hd.symm

/-- The tables of the first `n` bits at stage `s`, if all have converged. -/
def tablesUpTo (i s : ℕ) : ℕ → Option (List TTable)
  | 0 => some []
  | n + 1 => do
    let l ← tablesUpTo i s n
    let t ← tableAt i n s
    pure (l ++ [t])

/-- Convergence of the first `n` tables is stable. -/
theorem tablesUpTo_mono {i s s' : ℕ} (hs : s ≤ s') {n : ℕ} {l : List TTable}
    (h : tablesUpTo i s n = some l) : tablesUpTo i s' n = some l := by
  induction n generalizing l with
  | zero => simpa [tablesUpTo] using h
  | succ n ih =>
    simp only [tablesUpTo, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h ⊢
    obtain ⟨l', hl', t, ht, rfl⟩ := h
    exact ⟨l', ih hl', t, tableAt_mono hs ht, rfl⟩

/-- Tables of a total generator are eventually all defined. -/
theorem exists_tablesUpTo {i : ℕ} (h : IsTotalGen i) (n : ℕ) :
    ∃ s l, tablesUpTo i s n = some l := by
  induction n with
  | zero => exact ⟨0, [], rfl⟩
  | succ n ih =>
    obtain ⟨s, l, hl⟩ := ih
    obtain ⟨s', t, ht⟩ := h n
    refine ⟨max s s', l ++ [t], ?_⟩
    simp only [tablesUpTo, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq]
    exact ⟨l, tablesUpTo_mono (le_max_left _ _) hl, t, tableAt_mono (le_max_right _ _) ht, rfl⟩

end Kolmogorov.RandomStrings.TTMeet
