import KolmogorovMathlib.StrongMerging.Lower.ReservoirGame
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetComputable

/-!
# Coding toolkit for the effective reservoir game

The codings of the events and states of the game with natural-number points
(`resEventEquiv`, `reservoirStateEquiv`), the computability predicates `IsComputableGame` and
`IsComputableSources`, and a `Finset ℕ` toolkit reducing finite-set operations to list
operations.

Part of `KolmogorovMathlib.StrongMerging.Lower.ReservoirComputable`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Lower

/-- Events with natural-number points as a sum type. -/
def resEventEquiv : ResEvent ℕ ≃ ℕ ⊕ (Finset ℕ × ℕ) ⊕ List (Finset ℕ) where
  toFun
    | .point u => Sum.inl u
    | .set Q i => Sum.inr (Sum.inl (Q, i))
    | .table P => Sum.inr (Sum.inr P)
  invFun
    | Sum.inl u => .point u
    | Sum.inr (Sum.inl (Q, i)) => .set Q i
    | Sum.inr (Sum.inr P) => .table P
  left_inv e := by cases e <;> rfl
  right_inv x := by rcases x with u | ⟨Q, i⟩ | P <;> rfl

instance : Primcodable (ResEvent ℕ) :=
  Primcodable.ofEquiv _ resEventEquiv

instance : Inhabited (ResEvent ℕ) :=
  ⟨.point 0⟩

/-- The board fields, as a tuple. -/
abbrev BoardTuple : Type :=
  List (List (Finset ℕ)) × List (Finset ℕ × ℕ) × Finset ℕ × List (Finset ℕ) × ℕ × Finset ℕ ×
    Finset ℕ × List ℕ × ℕ × ℕ × ℕ

/-- Boards with natural-number points as tuples. -/
def reservoirStateEquiv : ReservoirState ℕ ≃ BoardTuple where
  toFun st := (st.tables, st.stored, st.marks, st.markedCells, st.center, st.live, st.epochLive,
    st.emitted, st.ordinaryResets, st.pointCharge, st.cellCharge)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
    x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (ReservoirState ℕ) :=
  Primcodable.ofEquiv _ reservoirStateEquiv

/-- A family of games `G p` whose data are computable in the parameter `p`. -/
structure IsComputableGame {π : Type*} [Primcodable π] (G : π → ResGame ℕ) : Prop where
  centers : Computable fun p => (G p).centers
  sphere : Computable₂ fun p z => (G p).sphere z
  N : Computable fun p => (G p).N
  ell : Computable fun p => (G p).ell
  delta : Computable fun p => (G p).delta
  fallback : Computable fun p => (G p).fallback

/-- A family of event sources whose bounded evaluators are computable in the parameter. -/
structure IsComputableSources {π : Type*} [Primcodable π] (src : π → EventSources ℕ) : Prop where
  numPt : Computable fun p => (src p).numPt
  ptEval : Computable fun x : π × ℕ × ℕ => (src x.1).ptEval x.2.1 x.2.2
  numSet : Computable fun p => (src p).numSet
  setEval : Computable fun x : π × ℕ × ℕ => (src x.1).setEval x.2.1 x.2.2
  setCost : Computable₂ fun p c => (src p).setCost c
  numTab : Computable fun p => (src p).numTab
  tabEval : Computable fun x : π × ℕ × ℕ × ℕ => (src x.1).tabEval x.2.1 x.2.2.1 x.2.2.2

/-! ### A `Finset ℕ` toolkit

Mathlib codes `Finset ℕ` through `Denumerable` (`Primcodable.ofDenumerable`).
`Kolmogorov.computable_finsetSort` reads off the sorted list of a finite set; with its converse
`computable_listToFinset`, every finite-set operation of the game reduces to a list operation. -/

/-- The sorted list of the set of a list of naturals is the filter of a long enough range. -/
private theorem primrec_sortToFinset_aux (l : List ℕ) :
    l.toFinset.sort (· ≤ ·) =
      (List.range (l.foldr (· + ·) 0 + 1)).filter (fun n => decide (∃ a ∈ l, a = n)) := by
  have hsorted : ((List.range (l.foldr (· + ·) 0 + 1)).filter
      (fun n => decide (∃ a ∈ l, a = n))).SortedLT :=
    ((List.sortedLT_range _).pairwise.filter _).sortedLT
  have hfin : ((List.range (l.foldr (· + ·) 0 + 1)).filter
      (fun n => decide (∃ a ∈ l, a = n))).toFinset = l.toFinset := by
    ext n
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
      exists_eq_right]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨Nat.lt_succ_of_le ?_, h⟩
      have := List.le_sum_of_mem h
      simpa [List.sum] using this
  rw [← hfin]
  exact (List.toFinset_sort _ hsorted.nodup).2 hsorted.sortedLE.pairwise

/-- **The sorted list of the finite set of a list is primitive recursive.**
Proof sketch: `l.toFinset.sort (· ≤ ·)` is the insertion sort of `l.dedup`; both are list
recursions (`Primrec.list_foldr` with an insertion step `List.orderedInsert`, and a
duplicate-removal step using `Primrec.list_any`-style membership), and the identification uses
`Finset.sort_eq`-style uniqueness of a sorted duplicate-free list with the given elements
(`List.eq_of_perm_of_sorted`).  [leaf: medium] -/
theorem primrec_sortToFinset : Primrec fun l : List ℕ => l.toFinset.sort (· ≤ ·) := by
  have hsum : Primrec fun l : List ℕ => l.foldr (· + ·) 0 :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  have hmem : PrimrecRel fun (L : List ℕ) (b : ℕ) => ∃ a ∈ L, a = b :=
    PrimrecRel.exists_mem_list Primrec.eq
  have hfilt := (PrimrecRel.listFilter (R := fun (n : ℕ) (L : List ℕ) => ∃ a ∈ L, a = n)
    (by simpa using hmem.swap)).comp (Primrec.list_range.comp (Primrec.succ.comp hsum))
      Primrec.id
  exact hfilt.of_eq fun l => (primrec_sortToFinset_aux l).symm

/-- `Denumerable.lower'` as a left fold with a moving base point. -/
private theorem exists_computable_finset_of_sort_aux (l : List ℕ) (n : ℕ) (acc : List ℕ) :
    (l.foldl (fun p m => (m + 1, (m - p.1) :: p.2)) (n, acc)).2 =
      (Denumerable.lower' l n).reverse ++ acc := by
  induction l generalizing n acc with
  | nil => rfl
  | cons m t ih =>
    rw [List.foldl_cons, ih]
    simp [Denumerable.lower']

/-- **A finite set of naturals is computable from its sorted list.**  Some computable `g`
inverts `Finset.sort`.
Proof sketch: by `Denumerable.finset` (`Mathlib/Logic/Equiv/Finset.lean`) the code of a finite
set `F` in Mathlib's `Primcodable (Finset ℕ)` (`Primcodable.ofDenumerable`) is the code of
`Denumerable.lower' (F.sort (· ≤ ·)) 0`; take `g l = Denumerable.ofNat (Finset ℕ)
(Encodable.encode (Denumerable.lower' l 0))`, so `encode (g l) = encode (lower' l 0)`, and
`lower'` is a primitive recursive list recursion (compare `raiseFold` and `primrec_raiseFold` in
`MonotoneComplexity/LevinSchnorr/FinsetComputable.lean`, which handle the inverse `raise'`).
[leaf: medium] -/
theorem exists_computable_finset_of_sort :
    ∃ g : List ℕ → Finset ℕ, Computable g ∧ ∀ F : Finset ℕ, g (F.sort (· ≤ ·)) = F := by
  refine ⟨fun l => Denumerable.ofNat (Finset ℕ) (Encodable.encode
    (l.foldl (fun p m => (m + 1, (m - p.1) :: p.2)) ((0 : ℕ), ([] : List ℕ))).2.reverse),
    ?_, fun F => ?_⟩
  · have hstep : Primrec₂ fun (_ : List ℕ) (q : (ℕ × List ℕ) × ℕ) =>
        (q.2 + 1, (q.2 - q.1.1) :: q.1.2) :=
      (Primrec.pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_cons.comp
          (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).to₂
    have hfold := Primrec.list_foldl Primrec.id (Primrec.const ((0 : ℕ), ([] : List ℕ))) hstep
    exact ((Primrec.ofNat (Finset ℕ)).comp (Primrec.encode.comp
      (Primrec.list_reverse.comp (Primrec.snd.comp hfold)))).to_comp
  · simp only
    rw [exists_computable_finset_of_sort_aux, List.append_nil, List.reverse_reverse,
      Kolmogorov.ofNat_finset_eq_raise'Finset, Denumerable.ofNat_encode]
    apply Finset.eq_of_veq
    change ((Denumerable.raise' (Denumerable.lower' (F.sort (· ≤ ·)) 0) 0 : List ℕ) :
      Multiset ℕ) = F.val
    rw [Denumerable.raise_lower' (fun n _ => Nat.zero_le n) (Finset.sortedLT_sort _),
      Finset.sort_eq]

/-- **Building a finite set from a list is computable** for Mathlib's `Primcodable (Finset ℕ)`:
sort the list's set, then invert `Finset.sort`. -/
theorem computable_listToFinset : Computable fun l : List ℕ => l.toFinset := by
  obtain ⟨g, hg, hgF⟩ := exists_computable_finset_of_sort
  exact (hg.comp primrec_sortToFinset.to_comp).of_eq fun l => hgF _

/-- The cardinality of a finite set of naturals is computable. -/
theorem computable_finsetCard : Computable fun F : Finset ℕ => F.card :=
  (Computable.list_length.comp computable_finsetSort).of_eq fun F => by simp

/-- Filtering a finite set of naturals by a computable Boolean predicate is computable. -/
theorem computable_finsetFilter {α : Type*} [Primcodable α] {f : α → Finset ℕ}
    {p : α → ℕ → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).filter fun u => p a u = true :=
  (computable_listToFinset.comp
    (Kolmogorov.computable_list_filter (computable_finsetSort.comp hf) hp)).of_eq fun a => by
      rw [List.toFinset_filter, Finset.sort_toFinset]

/-- Membership in a finite set of naturals is computable. -/
theorem computable_finsetMem : Computable fun x : ℕ × Finset ℕ => decide (x.1 ∈ x.2) := by
  have hp : Computable fun y : (ℕ × Finset ℕ) × ℕ => decide (y.2 = y.1.1) :=
    (Kolmogorov.primrec_decideEq.to_comp.comp Computable.snd
      (Computable.fst.comp Computable.fst)).of_eq fun _ => rfl
  refine (Kolmogorov.computable_list_any (computable_finsetSort.comp Computable.snd)
    hp.to₂).of_eq fun x => ?_
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨b, hb, hbx⟩
    rw [decide_eq_true_iff] at hbx
    have hb' : b = x.1 := hbx
    rw [← hb']
    simpa using hb
  · intro h
    exact ⟨x.1, by simpa using h, by simp⟩

/-- Union of finite sets of naturals is computable. -/
theorem computable_finsetUnion : Computable fun x : Finset ℕ × Finset ℕ => x.1 ∪ x.2 :=
  (computable_listToFinset.comp (Computable.list_append.comp
    (computable_finsetSort.comp Computable.fst) (computable_finsetSort.comp Computable.snd))).of_eq
    fun x => by rw [List.toFinset_append, Finset.sort_toFinset, Finset.sort_toFinset]

/-- Membership in the second component, as a computable binary predicate. -/
theorem computable_memSnd : Computable fun y : (Finset ℕ × Finset ℕ) × ℕ =>
    decide (y.2 ∈ y.1.2) :=
  (computable_finsetMem.comp (Computable.pair Computable.snd
    (Computable.snd.comp Computable.fst))).of_eq fun _ => rfl

/-- Intersection of finite sets of naturals is computable. -/
theorem computable_finsetInter : Computable fun x : Finset ℕ × Finset ℕ => x.1 ∩ x.2 :=
  (computable_finsetFilter Computable.fst computable_memSnd.to₂).of_eq fun x => by
    ext u
    simp

/-- Difference of finite sets of naturals is computable. -/
theorem computable_finsetSdiff : Computable fun x : Finset ℕ × Finset ℕ => x.1 \ x.2 := by
  have hp : Computable fun y : (Finset ℕ × Finset ℕ) × ℕ => !decide (y.2 ∈ y.1.2) :=
    (Primrec.not.to_comp.comp computable_memSnd).of_eq fun _ => rfl
  refine (computable_finsetFilter Computable.fst hp.to₂).of_eq fun x => ?_
  ext u
  simp

/-- Inserting a natural into a finite set is computable. -/
theorem computable_finsetInsert : Computable fun x : ℕ × Finset ℕ => insert x.1 x.2 :=
  (computable_listToFinset.comp (Computable.list_cons.comp Computable.fst
    (computable_finsetSort.comp Computable.snd))).of_eq fun x => by
      rw [List.toFinset_cons, Finset.sort_toFinset]

/-- Erasing a natural from a finite set is computable. -/
theorem computable_finsetErase : Computable fun x : Finset ℕ × ℕ => x.1.erase x.2 := by
  have hp : Computable fun y : (Finset ℕ × ℕ) × ℕ => !decide (y.2 = y.1.2) :=
    (Primrec.not.to_comp.comp (Kolmogorov.primrec_decideEq.to_comp.comp Computable.snd
      (Computable.snd.comp Computable.fst))).of_eq fun _ => rfl
  refine (computable_finsetFilter Computable.fst hp.to₂).of_eq fun x => ?_
  ext u
  simp [and_comm]

/-- Inclusion of finite sets of naturals is decidable by a computable test. -/
theorem computable_finsetSubset : Computable fun x : Finset ℕ × Finset ℕ => decide (x.1 ⊆ x.2) := by
  have h : Computable fun x : Finset ℕ × Finset ℕ => decide ((x.1 \ x.2).card = 0) :=
    (Kolmogorov.primrec_decideEq.to_comp.comp (computable_finsetCard.comp computable_finsetSdiff)
      (Computable.const 0)).of_eq fun _ => rfl
  refine h.of_eq fun x => ?_
  simp [Finset.sdiff_eq_empty_iff_subset]

/-- Left folds, specialised: `List.flatMap` along a computable list is computable. -/
theorem computable_flatMap {α β γ : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    [Primcodable γ] {f : α → List β} {g : α → β → List γ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).flatMap (g a) := by
  have key : ∀ (a : α) (l : List β) (acc : List γ),
      l.foldl (fun s b => s ++ g a b) acc = acc ++ l.flatMap (g a) := by
    intro a l
    induction l with
    | nil => intro acc; simp
    | cons b l ih => intro acc; rw [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]
  have hh : Computable fun y : α × (List γ × β) => y.2.1 ++ g y.1 y.2.2 :=
    (Computable.list_append.comp (Computable.fst.comp Computable.snd)
      (hg.comp Computable.fst (Computable.snd.comp Computable.snd))).of_eq fun _ => rfl
  refine (Kolmogorov.computable_list_foldl hf (Computable.const []) hh.to₂).of_eq fun a => ?_
  exact (key a (f a) []).trans (List.nil_append _)

end Kolmogorov.StrongMerging.Lower
