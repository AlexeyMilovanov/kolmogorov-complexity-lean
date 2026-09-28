/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.Prediction
import KolmogorovMathlib.Complexity.NatComplexity

/-!
# Busy-beaver infrastructure (SUV Sections 1.2 and 5.7.7; milestone C11b)

Two elementary facts that the busy-beaver layer of
`KolmogorovMathlib/MonotoneComplexity/Omega/SolovayFunctions.lean` needs and that are
not themselves part of Section 5.7:

* `finite_setOf_condK_le` — **there are only finitely many objects of complexity `≤ n`**
  (SUV Section 1.2, p. 21; the counting fact that makes `B(n)` and `BP(n)` of p. 169
  genuine maxima).  This is the elementary half of the argument of
  `Prefix/TotalCountingBound.lean`: choose for each object one producing program of
  length `≤ n`; determinism of `Part` makes that choice injective, and there are only
  finitely many programs of length `≤ n` (`boundedPrograms`).  It is stated for the raw
  `condK` and an arbitrary injective coding `e`, so that it applies verbatim to prefix
  complexity (`e = natToBitString`) and to plain complexity (`e = Nat.bits`).
* `exists_tsum_tail_lt` — **the tails of a finite `ℝ≥0∞`-series are eventually small**
  (SUV p. 170: the domain fact behind `BP'`, i.e. behind `BPprime_ne_top`), with the
  splitting identity `tsum_eq_sum_range_add_tsum_tail` it rests on.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Finitely many objects of bounded complexity (SUV p. 21) -/

/-- **SUV Section 1.2 (p. 21), the counting fact behind the busy-beaver functions.**
Along any injective coding `e` there are only finitely many indices whose complexity
(relative to any decompressor `D`) is at most `n`. -/
theorem finite_setOf_condK_le {ι : Type*} (D : Map) (e : ι → BitString)
    (he : Function.Injective e) (n : ℕ) :
    {k : ι | condK D (e k) [] ≤ (n : ENat)}.Finite := by
  classical
  have hex : ∀ k ∈ {k : ι | condK D (e k) [] ≤ (n : ENat)},
      ∃ p : BitString, programLength p ≤ n ∧ produces D p [] (e k) := by
    intro k hk
    exact (condK_le_iff D (e k) [] n).1 hk
  choose! p hplen hprod using hex
  refine Set.Finite.of_finite_image (f := p) ?_ ?_
  · refine Set.Finite.subset (Finset.finite_toSet (boundedPrograms n).toFinset) ?_
    rintro _ ⟨k, hk, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact (mem_boundedPrograms_iff (p k) n).2 (hplen k hk)
  · intro k hk k' hk' hpp
    have h1 : e k ∈ D (p k, ([] : BitString)) := hprod k hk
    have h2 : e k' ∈ D (p k', ([] : BitString)) := hprod k' hk'
    rw [hpp] at h1
    exact he (Part.mem_unique h1 h2)

/-! ### Tails of a finite `ℝ≥0∞`-series (SUV p. 170) -/

/-- Splitting a series at a cutoff: the head is the finite sum over `range (N+1)` and
the tail is the `N`-guarded series.  Both parts are taken in `ℝ≥0∞`, where `tsum_add`
holds unconditionally. -/
theorem tsum_eq_sum_range_add_tsum_tail (f : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n, f n
      = (∑ n ∈ Finset.range (N + 1), f n) + ∑' n, (if N < n then f n else 0) := by
  have hsplit : ∀ n, f n = (if N < n then 0 else f n) + (if N < n then f n else 0) := by
    intro n
    by_cases h : N < n <;> simp [h]
  have hhead : (∑' n, (if N < n then 0 else f n)) = ∑ n ∈ Finset.range (N + 1), f n := by
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn' : n < N + 1 := Finset.mem_range.1 hn
      have : ¬ N < n := by omega
      simp [this]
    · intro n hn
      have hn' : ¬ n < N + 1 := fun h => hn (Finset.mem_range.2 h)
      have : N < n := by omega
      simp [this]
  calc ∑' n, f n
      = ∑' n, ((if N < n then 0 else f n) + (if N < n then f n else 0)) := tsum_congr hsplit
    _ = (∑' n, (if N < n then 0 else f n)) + ∑' n, (if N < n then f n else 0) :=
        ENNReal.tsum_add
    _ = (∑ n ∈ Finset.range (N + 1), f n) + ∑' n, (if N < n then f n else 0) := by
        rw [hhead]

/-- **SUV p. 170.** A series of nonnegative reals with finite sum has arbitrarily small
tails: for every `ε > 0` there is a cutoff `N` past which the total mass is `< ε`. -/
theorem exists_tsum_tail_lt {f : ℕ → ℝ≥0∞} (hf : (∑' n, f n) ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, (∑' n, (if N < n then f n else 0)) < ε := by
  by_contra hcon
  push_neg at hcon
  have hle : ∀ j : ℕ, (∑ n ∈ Finset.range j, f n) + ε ≤ ∑' n, f n := by
    intro j
    have hsub : Finset.range j ⊆ Finset.range (j + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have h1 : (∑ n ∈ Finset.range j, f n) ≤ ∑ n ∈ Finset.range (j + 1), f n :=
      Finset.sum_le_sum_of_subset hsub
    calc (∑ n ∈ Finset.range j, f n) + ε
        ≤ (∑ n ∈ Finset.range (j + 1), f n) + ∑' n, (if j < n then f n else 0) :=
          add_le_add h1 (hcon j)
      _ = ∑' n, f n := (tsum_eq_sum_range_add_tsum_tail f j).symm
  have hsup : (∑' n, f n) + ε ≤ ∑' n, f n := by
    calc (∑' n, f n) + ε = (⨆ j, ∑ n ∈ Finset.range j, f n) + ε := by
          rw [ENNReal.tsum_eq_iSup_nat]
      _ = ⨆ j, ((∑ n ∈ Finset.range j, f n) + ε) := ENNReal.iSup_add _
      _ ≤ ∑' n, f n := iSup_le hle
  have heq : (∑' n, f n) + ε = (∑' n, f n) + 0 := by
    simpa using le_antisymm hsup le_self_add
  exact absurd ((ENNReal.add_right_inj hf).1 heq) (ne_of_gt hε)

end Kolmogorov
