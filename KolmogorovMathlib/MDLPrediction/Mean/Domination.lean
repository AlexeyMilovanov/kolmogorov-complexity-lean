/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Compiler

/-!
# Uniform domination of the first-exit mean tree

The tree may lose mass at a first exit. Its root is one and every finite prefix-free
set has mass at most one. Uniform family domination charges a single machine constant.
Blueprint nodes: `exp:mean`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- One constant uniformly dominates the first-exit mean tree for every pair of
computable proper measures and valid numeric indices. Blueprint node `exp:mean`. -/
theorem meanTree_uniform_domination (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
      [IsProbabilityMeasure Q], ∀ eP eQ,
        IsComputableMeasureIndex P eP → IsComputableMeasureIndex Q eQ →
          ∀ x, meanTree P Q x ≤
            (2 : ℝ≥0∞) ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + c) *
                universalContinuousSemimeasure x := by
  obtain ⟨ν, hν_lsc, hν_free, hν_eq⟩ := exp_mean_sanitize
  obtain ⟨C, hC⟩ :=
    exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree U hU ν hν_lsc hν_free
  obtain ⟨c_1, hc1⟩ := exp_mean_compiler U hU ν hν_eq
  use c_1 + C
  intro P Q _ _ eP eQ heP heQ x
  have hp_comp : IsComputableMeasure P := (isComputableMeasure_iff_exists_index P).mpr ⟨eP, heP⟩
  have hq_comp : IsComputableMeasure Q := (isComputableMeasure_iff_exists_index Q).mpr ⟨eQ, heQ⟩
  obtain ⟨e, he_eq, he_bound⟩ := hc1 P Q hp_comp hq_comp
  have h1 := hC e x
  rw [he_eq] at h1
  have h_le : (KPNat U e).toNat + C ≤ (computableMeasureComplexity U P).toNat +
      (computableMeasureComplexity U Q).toNat + (c_1 + C) := by
    have h_bound_nat : (KPNat U e).toNat ≤ (computableMeasureComplexity U P).toNat +
      (computableMeasureComplexity U Q).toNat + c_1 := by exact_mod_cast he_bound
    omega
  have h3 : (2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) := by
    apply pow_le_pow_of_le_one zero_le _ h_le
    exact ENNReal.inv_le_one.mpr one_le_two
  have h4 : (2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) * meanTree P Q x ≤
            (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) * meanTree P Q x := by
    gcongr
  have h5 := le_trans h4 h1
  have h6 : (2 : ℝ≥0∞) ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) *
            ((2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) * meanTree P Q x) ≤
            (2 : ℝ≥0∞) ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) * 
              universalContinuousSemimeasure x := by
    gcongr
  have h7 : (2 : ℝ≥0∞) ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) *
            ((2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C))) = 1 := by
    rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel]
    · simp
    · simp
  have h8 : (2 : ℝ≥0∞) ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) *
            ((2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + (c_1 + C)) * meanTree P Q x) =
            meanTree P Q x := by
    rw [← mul_assoc, h7, one_mul]
  rwa [h8] at h6

/-- The mean tree has a finite prefix-free mass budget.
Blueprint node `exp:mean`. -/
theorem meanTree_prefixFree_budget (P Q : Measure CantorSeq)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (S : Finset BitString) (hS : IsPrefixFree (S : Set BitString)) :
    ∑ x ∈ S, meanTree P Q x ≤ 1 := by
  apply IsContinuousTreeSemimeasure.sum_antichain_le
  · exact exp_mean_tree P Q
  · intro y hy z hz hyz
    exact hS (Finset.mem_coe.mpr hy) (Finset.mem_coe.mpr hz) hyz

end Kolmogorov.MDLPrediction
