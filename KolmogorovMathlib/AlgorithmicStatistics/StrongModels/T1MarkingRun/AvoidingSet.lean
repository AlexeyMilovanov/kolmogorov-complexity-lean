import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingCount
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector

/-!
# The avoiding set of the marking construction

`exists_t1_avoiding_set_structural` is the structural endpoint of the chronological marking
run: a set of `2 ^ (k - epsilon)` strings of length `n` that escapes every mark the
construction places.  The run itself is in `T1MarkingRun/Part01`, its counting in
`T1MarkingCount`, and the quantitative form of this statement is `exists_t1_avoiding_set_core`
in `T1Core`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Structural endpoint of the chronological marking construction: existence of
a `2^(k-ε)`-element cube of length-`n` strings together with a surviving element
avoiding all three extensional marking families.

This is the *counting* half of the source proof of Theorem `t1` (items (a)–(d)
minus the complexity clause `K(A) ≤ ε + O(log n)` of (a)).  The source is
explicit that this half is easy — "we cannot let `A` be *any* `2^{k-ε}`-element
non-covered set, as in that case `K(A)` could be large" — the entire difficulty
of `t1` lives in the *complexity* of `A`, which is the separate obligation
`exists_t1_avoiding_set_core` for a future reachable-run worker.  Hence the
structural existence follows
directly from the already-proved static union bound `t1_unmarked_card_ge_half`:
the unmarked length-`n` set has at least `2^(n-1) ≥ 2^(k-ε)` elements, every one
of which avoids the three families; extract a `2^(k-ε)`-subset and take any
element.  (Avoiding `∃ d, T1CMarked` in particular avoids the fixed-budget
`T1CMarked V n k (ε + logSlack cDesc n)`.) -/
theorem exists_t1_avoiding_set_structural
    (V : Map) (_hV : isOptimalConditional V) :
    ∀ cDesc, ∃ c0 _cSparse : Nat, ∀ n k epsilon,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      ∃ A x,
        A ⊆ stringsOfLength n ∧
        A.card = 2 ^ (k - epsilon) ∧
        x ∈ A ∧
        ¬ T1BMarked V n epsilon x ∧
        ¬ T1CMarked V n k
          (epsilon + logSlack cDesc n) x ∧
        ¬ T1DMarked V n k x := by
  classical
  intro cDesc
  refine ⟨0, 0, ?_⟩
  intro n k epsilon _hc0 hεk hkn
  have hεn : epsilon + 4 ≤ n := by omega
  set Marked : Finset BitString :=
    (stringsOfLength n).filter
      (fun x => T1BMarked V n epsilon x ∨
        (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x)
    with hMarkedDef
  have hMarkedSpec : ∀ x ∈ Marked,
      T1BMarked V n epsilon x ∨
        (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x := by
    intro x hx
    rw [hMarkedDef] at hx
    exact (Finset.mem_filter.mp hx).2
  have hge : 2 ^ (n - 1) ≤ (stringsOfLength n \ Marked).card :=
    t1_unmarked_card_ge_half V n k epsilon hεn hkn Marked hMarkedSpec
  have hcard_le : 2 ^ (k - epsilon) ≤ (stringsOfLength n \ Marked).card :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hge
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard_le
  have hAstr : A ⊆ stringsOfLength n := hAsub.trans Finset.sdiff_subset
  have hApos : 0 < A.card := by rw [hAcard]; positivity
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hApos
  have hxdiff := hAsub hx
  rw [Finset.mem_sdiff] at hxdiff
  obtain ⟨hxstr, hxnm⟩ := hxdiff
  have hxnotP : ¬ (T1BMarked V n epsilon x ∨
      (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x) := by
    intro hPx
    apply hxnm
    rw [hMarkedDef]
    exact Finset.mem_filter.mpr ⟨hxstr, hPx⟩
  push_neg at hxnotP
  obtain ⟨hxB, hxC, hxD⟩ := hxnotP
  exact ⟨A, x, hAstr, hAcard, hx, hxB,
    hxC (epsilon + logSlack cDesc n), hxD⟩

end Kolmogorov
