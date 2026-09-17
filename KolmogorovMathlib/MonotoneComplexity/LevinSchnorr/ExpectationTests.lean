/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.PrefixSumRatioLSC
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# The expectation-bounded tests of SUV Problems 146 and 147

SUV Problem 146 (Section 5.6, p. 150) asserts that `t(ω) = ∑_{x ⊑ ω} m(x)/p(x)` is an
expectation-bounded randomness test for `μ`, where `m` is the discrete a priori probability
and `p(x) = μ(Ω_x)`; Problem 147 asserts the same for the supremum version
`sup_{x ⊑ ω} m(x)/p(x)`.

`IsExpectationBoundedRandomnessTest μ u` is a conjunction of two unrelated statements:
lower semicomputability of `u`, and `∫ u dμ ≤ 1`.  This module proves the *integral* half of
both, in the exact form the source gives it —

> "Its integral is `∑_x p(x) · m(x)/p(x) = ∑_x m(x) ≤ 1`" (SUV p. 150)

— the semicomputability half, which the source disposes of in one clause ("lower
semicomputability follows from that of `m` and computability of `μ`"), is proved in
`LevinSchnorr/PrefixRatioLSC.lean` and `LevinSchnorr/PrefixSumRatioLSC.lean`.

## Main results

* `sum_range_sum_levelFinset_le_tsum` — the level decomposition of a sum over all strings;
* `lintegral_prefixSumRatio_le` — `∫ ∑_{x ⊑ ω} m(x)/p(x) dμ ≤ 1` (proved);
* `prefixSupRatio_le_prefixSumRatio` — the supremum is below the sum (proved);
Both semicomputability halves are proved too, in `LevinSchnorr/PrefixRatioLSC.lean` (the
supremum) and `LevinSchnorr/PrefixSumRatioLSC.lean` (the sum), so Problems 146 and 147 are
established apart from their maximality halves.
-/

namespace Kolmogorov

open MeasureTheory

open scoped ENNReal

/-! ### Level decomposition of a sum over strings -/

/-- Every partial sum of the level sums `∑_{|y| = i} g(y)` is bounded by the sum of `g` over
all strings: the levels are pairwise disjoint finite sets of strings. -/
lemma sum_range_sum_levelFinset_le_tsum (g : BitString → ℝ≥0∞) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∑ y ∈ levelFinset i, g y ≤ ∑' x : BitString, g x := by
  classical
  have hdisj : ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint levelFinset := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    rw [mem_levelFinset] at hy hy'
    exact hij (hy ▸ hy')
  rw [← Finset.sum_biUnion hdisj]
  exact ENNReal.sum_le_tsum _

/-- The `tsum` form of the level decomposition. -/
lemma tsum_sum_levelFinset_le_tsum (g : BitString → ℝ≥0∞) :
    ∑' i : ℕ, ∑ y ∈ levelFinset i, g y ≤ ∑' x : BitString, g x := by
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => sum_range_sum_levelFinset_le_tsum g N

/-! ### The integral of the prefix ratio -/

/-- The source's computation `∑_x p(x) · m(x)/p(x) = ∑_x m(x)`, one level at a time.  At a
null cylinder the `ℝ≥0∞` product `(m(x)/0) · 0` is `0`, so the identity becomes an
inequality, which is all that is needed. -/
lemma lintegral_ratio_comp_cantorPrefix_le (m : BitString → ℝ≥0∞) (μ : Measure CantorSeq)
    [IsFiniteMeasure μ] (n : ℕ) :
    ∫⁻ w, m (cantorPrefix w n) / cantorMass μ (cantorPrefix w n) ∂μ
      ≤ ∑ y ∈ levelFinset n, m y := by
  rw [lintegral_comp_cantorPrefix μ n fun y => m y / cantorMass μ y]
  refine Finset.sum_le_sum fun y _ => ?_
  rcases eq_or_ne (cantorMass μ y) 0 with hy | hy
  · simp [hy]
  · rw [ENNReal.div_mul_cancel hy (measure_ne_top μ _)]

/-- **SUV Problem 146 (p. 150), the integral half**: `∫ ∑_{x ⊑ ω} m(x)/p(x) dμ ≤ 1` for any
semimeasure `m`. -/
theorem lintegral_prefixSumRatio_le {m : BitString → ℝ≥0∞} (μ : Measure CantorSeq)
    [IsFiniteMeasure μ] (hm : (∑' x : BitString, m x) ≤ 1) :
    ∫⁻ w, prefixSumRatio m μ w ∂μ ≤ 1 := by
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun w : CantorSeq => m (cantorPrefix w n) / cantorMass μ (cantorPrefix w n)) μ :=
    fun n => (measurable_comp_cantorPrefix n fun y => m y / cantorMass μ y).aemeasurable
  calc ∫⁻ w, prefixSumRatio m μ w ∂μ
      = ∑' n : ℕ, ∫⁻ w, m (cantorPrefix w n) / cantorMass μ (cantorPrefix w n) ∂μ := by
        simp only [prefixSumRatio]
        exact lintegral_tsum hmeas
    _ ≤ ∑' n : ℕ, ∑ y ∈ levelFinset n, m y :=
        ENNReal.tsum_le_tsum fun n => lintegral_ratio_comp_cantorPrefix_le m μ n
    _ ≤ ∑' x : BitString, m x := tsum_sum_levelFinset_le_tsum m
    _ ≤ 1 := hm

/-- SUV Problem 147 (p. 150): the supremum version is pointwise below the sum of
Problem 146. -/
lemma prefixSupRatio_le_prefixSumRatio (m : BitString → ℝ≥0∞) (μ : Measure CantorSeq)
    (w : CantorSeq) : prefixSupRatio m μ w ≤ prefixSumRatio m μ w :=
  iSup_le fun n => ENNReal.le_tsum n

/-- **SUV Problem 147 (p. 150), the integral half**: `∫ sup_{x ⊑ ω} m(x)/p(x) dμ ≤ 1`. -/
theorem lintegral_prefixSupRatio_le {m : BitString → ℝ≥0∞} (μ : Measure CantorSeq)
    [IsFiniteMeasure μ] (hm : (∑' x : BitString, m x) ≤ 1) :
    ∫⁻ w, prefixSupRatio m μ w ∂μ ≤ 1 :=
  le_trans (lintegral_mono fun w => prefixSupRatio_le_prefixSumRatio m μ w)
    (lintegral_prefixSumRatio_le μ hm)

end Kolmogorov
