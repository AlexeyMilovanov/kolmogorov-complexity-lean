/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.AlgorithmicRandomness.Measure

/-!
# A priori path budgets

`PathBudget` uses a natural multiplicative exponent. It compares the universal continuous
semimeasure with a proper measure along every path prefix. The positive-mass log form uses
the repository's unrounded real `KA`; the paper's rounded convention costs one unit.

Blueprint nodes: `base:budget`, `base:budget-log`, `base:budget-positive`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- A uniform multiplicative deficiency bound along the prefixes of a path.
Blueprint node `base:budget`. -/
def PathBudget (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ) : Prop :=
  ∀ n, universalContinuousSemimeasure (cantorPrefix w n) ≤
    (2 : ℝ≥0∞) ^ D * cantorMass P (cantorPrefix w n)

/-- A budget gives positive mass to every prefix of the path.
Blueprint node `base:budget-positive`. -/
theorem base_budget_positive (P : Measure CantorSeq) (w : CantorSeq)
    (D n : ℕ) (h : PathBudget P w D) :
    0 < cantorMass P (cantorPrefix w n) := by
  have H := h n
  have hpos := universalContinuousSemimeasure_pos (cantorPrefix w n)
  contrapose H
  push Not at H ⊢
  have h0 : cantorMass P (cantorPrefix w n) = 0 := le_antisymm H zero_le
  rw [h0, mul_zero]
  exact hpos

/-- On positive mass, the multiplicative budget and real deficiency bound are equivalent.
Blueprint node `base:budget-log`. -/
theorem base_budget_log (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (x : BitString) (D : ℕ) (hpos : 0 < cantorMass P x) :
    universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ D * cantorMass P x ↔
      -Real.logb 2 (cantorMass P x).toReal - KA x ≤ (D : ℝ) := by
  have hmP_ne_top : cantorMass P x ≠ ⊤ := measure_ne_top P _
  have hmP_pos : (cantorMass P x).toReal > 0 := ENNReal.toReal_pos hpos.ne' hmP_ne_top
  have h_ne_top_ucs : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have h_pos_ucs : universalContinuousSemimeasure x > 0 := universalContinuousSemimeasure_pos x
  have hmU_pos : (universalContinuousSemimeasure x).toReal > 0 :=
    ENNReal.toReal_pos h_pos_ucs.ne' h_ne_top_ucs
  have h_KA : KA x = - Real.logb 2 (universalContinuousSemimeasure x).toReal := rfl
  rw [h_KA]
  have h_mul_ne_top : (2 : ℝ≥0∞) ^ D * cantorMass P x ≠ ⊤ := ENNReal.mul_ne_top (by simp) hmP_ne_top
  rw [← ENNReal.toReal_le_toReal h_ne_top_ucs h_mul_ne_top]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  have h_toReal_2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  rw [h_toReal_2]
  have H : -Real.logb 2 (cantorMass P x).toReal -
      -Real.logb 2 (universalContinuousSemimeasure x).toReal =
      Real.logb 2 ((universalContinuousSemimeasure x).toReal / (cantorMass P x).toReal) := by
    rw [sub_neg_eq_add, add_comm, ← sub_eq_add_neg, Real.logb_div hmU_pos.ne' hmP_pos.ne']
  rw [H]
  have h_log : Real.logb 2 ((universalContinuousSemimeasure x).toReal /
      (cantorMass P x).toReal) ≤ ↑D ↔
      (universalContinuousSemimeasure x).toReal / (cantorMass P x).toReal ≤ (2 : ℝ) ^ (D : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (div_pos hmU_pos hmP_pos)]
  rw [h_log]
  have hd_pow : (2 : ℝ) ^ (D : ℝ) = (2 : ℝ) ^ D := Real.rpow_natCast 2 D
  rw [hd_pow]
  exact Iff.symm (div_le_iff₀ hmP_pos)

end Kolmogorov.MDLPrediction
