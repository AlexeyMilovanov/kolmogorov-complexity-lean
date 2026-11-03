/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Domination
import KolmogorovMathlib.MDLPrediction.Core.Budget
import KolmogorovMathlib.MDLPrediction.Analysis.Products

/-!
# Product comparison for two proper measures

Uniform mean-tree domination and two endpoint budgets give the product inequality.
Properness also identifies the squared errors for bit zero and a realized bit.
Blueprint nodes: `exp:pair-product`, `exp:zero-one`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal BigOperators


/-! ## Bounding the mean tree and the universal semimeasure -/

/-- Two endpoint budgets bound the squared universal semimeasure. -/
private lemma universalContinuousSemimeasure_sq_le (P Q : Measure CantorSeq)
    (x : BitString) (D : ℕ)
    (hDP : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ D * cantorMass P x)
    (hDQ : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ D * cantorMass Q x) :
    (universalContinuousSemimeasure x) ^ 2 ≤
      (2 : ℝ≥0∞) ^ (2 * D) * cantorMass P x * cantorMass Q x := by
  calc
    (universalContinuousSemimeasure x) ^ 2 =
      (universalContinuousSemimeasure x) * (universalContinuousSemimeasure x) := by rw [pow_two]
    _ ≤ ((2 : ℝ≥0∞) ^ D * cantorMass P x) * ((2 : ℝ≥0∞) ^ D * cantorMass Q x) := by
      exact mul_le_mul' hDP hDQ
    _ = (2 : ℝ≥0∞) ^ (2 * D) * cantorMass P x * cantorMass Q x := by
      have : (2 : ℝ≥0∞) ^ (2 * D) = (2 : ℝ≥0∞) ^ D * (2 : ℝ≥0∞) ^ D := by
        rw [two_mul, pow_add]
      rw [this]
      ring

/-- Combine mean-tree domination with the squared universal bound. -/
private lemma meanTree_sq_le_of_domination
    {K D : ℕ} {mean M P Q : ℝ≥0∞}
    (h1 : mean ≤ (2 : ℝ≥0∞) ^ K * M)
    (h2 : M ^ 2 ≤ (2 : ℝ≥0∞) ^ (2 * D) * P * Q) :
    mean ^ 2 ≤ (2 : ℝ≥0∞) ^ (2 * (K + D)) * P * Q := by
  calc
    mean ^ 2 ≤ ((2 : ℝ≥0∞) ^ K * M) ^ 2 := by
      exact pow_le_pow_left' h1 2
    _ = (2 : ℝ≥0∞) ^ (2 * K) * M ^ 2 := by
      rw [mul_pow, ←pow_mul]
      have : K * 2 = 2 * K := mul_comm K 2
      rw [this]
    _ ≤ (2 : ℝ≥0∞) ^ (2 * K) * ((2 : ℝ≥0∞) ^ (2 * D) * P * Q) := by
      exact mul_le_mul' le_rfl h2
    _ = (2 : ℝ≥0∞) ^ (2 * (K + D)) * P * Q := by
      have : (2 : ℝ≥0∞) ^ (2 * (K + D)) = (2 : ℝ≥0∞) ^ (2 * K) * (2 : ℝ≥0∞) ^ (2 * D) := by
        rw [mul_add, pow_add]
      rw [this]
      ring

/-- Convert a finite mean-tree square inequality to real numbers. -/
private lemma meanTree_toReal_sq_le
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (x : BitString) (K : ℕ)
    (h : (meanTree P Q x) ^ 2 ≤ (2 : ℝ≥0∞) ^ K * cantorMass P x * cantorMass Q x) :
    ((meanTree P Q x).toReal) ^ 2 ≤
      (2 : ℝ) ^ K * (cantorMass P x).toReal * (cantorMass Q x).toReal := by
  have hmP_ne_top : cantorMass P x ≠ ⊤ := measure_ne_top P _
  have hmQ_ne_top : cantorMass Q x ≠ ⊤ := measure_ne_top Q _
  have h_ne_top : (2 : ℝ≥0∞) ^ K * cantorMass P x * cantorMass Q x ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top (by simp) hmP_ne_top
    · exact hmQ_ne_top
  have h_mean_pow_ne_top : (meanTree P Q x) ^ 2 ≠ ⊤ := by
    intro H
    rw [H] at h
    exact h_ne_top (top_le_iff.mp h)
  have H2 := (ENNReal.toReal_le_toReal h_mean_pow_ne_top h_ne_top).mpr h
  have H3 : ((meanTree P Q x) ^ 2).toReal = ((meanTree P Q x).toReal) ^ 2 := by
    rw [pow_two, pow_two, ENNReal.toReal_mul]
  rw [H3] at H2
  have H4 : ((2 : ℝ≥0∞) ^ K * cantorMass P x * cantorMass Q x).toReal =
      (2 : ℝ) ^ K * (cantorMass P x).toReal * (cantorMass Q x).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
    have : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [this]
  rw [H4] at H2
  exact H2

/-- On common positive support the mean tree is the real conditional product. -/
private lemma meanTree_toReal_eq_condProb_prod (P Q : Measure CantorSeq)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (x : BitString)
    (hP : 0 < cantorMass P x) (hQ : 0 < cantorMass Q x) :
    (meanTree P Q x).toReal = ∏ i : Fin x.length,
      (condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) +
        condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) / 2 := by
  have hcommon : CommonPositivePrefixes P Q x := exp_mean_support P Q x hP hQ
  rw [meanTree_product P Q x hcommon]
  have H : ∏ i : Fin x.length,
      ENNReal.ofReal ((condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) +
        condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) / 2) =
      ENNReal.ofReal (∏ i : Fin x.length,
      ((condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) +
        condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) / 2)) := by
    apply Eq.symm
    apply ENNReal.ofReal_prod_of_nonneg
    intro i _
    have h1 := condProb_nonneg (cantorMass P) (x.take i.val) (x[i.val]'i.isLt)
    have h2 := condProb_nonneg (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)
    linarith
  rw [H]
  apply ENNReal.toReal_ofReal
  apply Finset.prod_nonneg
  intro i _
  have h1 := condProb_nonneg (cantorMass P) (x.take i.val) (x[i.val]'i.isLt)
  have h2 := condProb_nonneg (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)
  linarith

/-- Domination and two deficiency budgets bound the squared product of the
mean realized-bit conditionals. Blueprint node `exp:pair-product`. -/
theorem exp_pair_product (U : Map)
    (c : ℕ)
    (hdom : ∀ (R S : Measure CantorSeq) [IsProbabilityMeasure R]
      [IsProbabilityMeasure S], ∀ eR eS,
        IsComputableMeasureIndex R eR → IsComputableMeasureIndex S eS →
          ∀ y, meanTree R S y ≤
            (2 : ℝ≥0∞) ^ ((computableMeasureComplexity U R).toNat +
              (computableMeasureComplexity U S).toNat + c) *
                universalContinuousSemimeasure y)
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPc : IsComputableMeasure P)
    (hQc : IsComputableMeasure Q) (x : BitString)
    (hP : 0 < cantorMass P x) (hQ : 0 < cantorMass Q x) (D : ℕ)
    (hDP : universalContinuousSemimeasure x ≤
      (2 : ℝ≥0∞) ^ D * cantorMass P x)
    (hDQ : universalContinuousSemimeasure x ≤
      (2 : ℝ≥0∞) ^ D * cantorMass Q x) :
    (∏ i : Fin x.length,
      (condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) +
        condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) / 2) ^ 2 ≤
      (2 : ℝ) ^ (2 * ((computableMeasureComplexity U P).toNat +
        (computableMeasureComplexity U Q).toNat + c + D)) *
        (cantorMass P x).toReal * (cantorMass Q x).toReal := by
  obtain ⟨eP, heP⟩ := (isComputableMeasure_iff_exists_index P).mp hPc
  obtain ⟨eQ, heQ⟩ := (isComputableMeasure_iff_exists_index Q).mp hQc
  have H1 := hdom P Q eP eQ heP heQ x
  have H2 := universalContinuousSemimeasure_sq_le P Q x D hDP hDQ
  have H3 := meanTree_sq_le_of_domination H1 H2
  let K := (computableMeasureComplexity U P).toNat + (computableMeasureComplexity U Q).toNat + c
  have H4 := meanTree_toReal_sq_le P Q x (2 * (K + D)) H3
  have H5 := meanTree_toReal_eq_condProb_prod P Q x hP hQ
  rw [←H5]
  exact H4

/-- At a positive parent, the squared bit-zero discrepancy equals the squared
discrepancy at either realized bit. Blueprint node `exp:zero-one`. -/
theorem exp_zero_one (P Q : Measure CantorSeq) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (y : BitString) (b : Bool)
    (hP : 0 < cantorMass P y) (hQ : 0 < cantorMass Q y) :
    (condProb (cantorMass P) y false - condProb (cantorMass Q) y false) ^ 2 =
      (condProb (cantorMass P) y b - condProb (cantorMass Q) y b) ^ 2 := by
  cases b
  · rfl
  · have h1 : condProb (cantorMass P) y false + condProb (cantorMass P) y true = 1 :=
      condProb_cantorMass_add_eq_one P (ne_of_gt hP)
    have h2 : condProb (cantorMass Q) y false + condProb (cantorMass Q) y true = 1 :=
      condProb_cantorMass_add_eq_one Q (ne_of_gt hQ)
    have eq1 : condProb (cantorMass P) y true = 1 - condProb (cantorMass P) y false := by linarith
    have eq2 : condProb (cantorMass Q) y true = 1 - condProb (cantorMass Q) y false := by linarith
    rw [eq1, eq2]
    ring

end Kolmogorov.MDLPrediction
