/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Argmin
import KolmogorovMathlib.MDLPrediction.Core.Budget
import KolmogorovMathlib.MDLPrediction.Core.TwoPart

/-!
# Bounds for a winner on a budgeted path

The same two-part coding constant is passed to every winner bound. All cylinders used in
real logarithms have positive mass. The path index `n` fixes the prefix `cantorPrefix w n`.

Blueprint nodes: `base:winner`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal


/-- The score, coding, and budget inequalities jointly bound model complexity and mass. -/
private theorem winner_score_bounds
    (kP kQ D c : ℕ) (a b A : ℝ)
    (hbudget : -a - A ≤ (D : ℝ))
    (hcode : A ≤ (kQ : ℝ) - b + (c : ℝ))
    (hscore : 3 * (kQ : ℝ) - b ≤ 3 * (kP : ℝ) - a) :
    2 * (kQ : ℝ) ≤ 3 * (kP : ℝ) + (D : ℝ) + (c : ℝ) ∧
      -b - A ≤ ((3 * kP + D : ℕ) : ℝ) := by
  constructor
  · linarith
  · have hkQ : 0 ≤ (kQ : ℝ) := Nat.cast_nonneg _
    have hcast : (3 * (kP : ℝ) + (D : ℝ)) = ((3 * kP + D : ℕ) : ℝ) := by push_cast; rfl
    rw [← hcast]
    linarith

/-- Cancel the power of two in a bound on universal mass. -/
private theorem inv_pow_mul_universal_le_mass
    (Q : Measure CantorSeq) (x : BitString) (N : ℕ)
    (h : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ N * cantorMass Q x) :
    (2 : ℝ≥0∞)⁻¹ ^ N * universalContinuousSemimeasure x ≤ cantorMass Q x := by
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ N * universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞)⁻¹ ^ N * ((2
      : ℝ≥0∞) ^ N * cantorMass Q x) := by
    gcongr
  apply le_trans h2
  rw [← mul_assoc, ← ENNReal.inv_pow]
  have hinv : ((2 : ℝ≥0∞) ^ N)⁻¹ * (2 : ℝ≥0∞) ^ N = 1 := by
    apply ENNReal.inv_mul_cancel
    · exact ne_of_gt (ENNReal.pow_pos (by norm_num) _)
    · exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  rw [hinv, one_mul]
/-- A winner retains a fixed fraction of universal mass at every budgeted prefix.
Blueprint node `base:winner`. -/
theorem winner_bounds (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ)
    (hc : ∀ R : Measure CantorSeq, IsProbabilityMeasure R →
      IsComputableMeasure R → ∀ x : BitString, 0 < cantorMass R x →
        KA x ≤ (computableMeasureComplexity U R).toNat -
          Real.logb 2 (cantorMass R x).toReal + c)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (hP : IsComputableMeasure P)
    (w : CantorSeq) (D n : ℕ) (hbudget : PathBudget P w D)
    (Q : Measure CantorSeq) (hQ : IsGlobalWinner U hU Q (cantorPrefix w n)) :
    (2 : ℝ≥0∞)⁻¹ ^ (3 * (computableMeasureComplexity U P).toNat + D) *
      universalContinuousSemimeasure (cantorPrefix w n) ≤
        cantorMass Q (cantorPrefix w n) := by
  let x := cantorPrefix w n
  have hm : 0 < universalContinuousSemimeasure x := universalContinuousSemimeasure_pos x
  have hp : 0 < cantorMass P x := base_budget_positive P w D n hbudget
  have hq : 0 < cantorMass Q x := hQ.2.2.1
  have hbudgetlog := (base_budget_log P x D hp).mp (hbudget n)
  have hcode := hc Q hQ.1 hQ.2.1 x hq
  have hscore_ereal := hQ.2.2.2 P inferInstance hP hp
  unfold score at hscore_ereal
  have hP_ne_zero : cantorMass P x ≠ 0 := ne_of_gt hp
  have hQ_ne_zero : cantorMass Q x ≠ 0 := ne_of_gt hq
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hQ_ne_zero h)), ite_eq_right_iff.mpr
      (fun h => False.elim (hP_ne_zero h))] at hscore_ereal
  have hscore : (3 * (computableMeasureComplexity U Q).toNat : ℝ) - Real.logb 2
      (cantorMass Q x).toReal ≤
                (3 * (computableMeasureComplexity U P).toNat : ℝ) - Real.logb 2
                    (cantorMass P x).toReal :=
    EReal.coe_le_coe_iff.mp hscore_ereal
  have halg := winner_score_bounds (computableMeasureComplexity U P).toNat
      (computableMeasureComplexity U Q).toNat D c
    (Real.logb 2 (cantorMass P x).toReal) (Real.logb 2 (cantorMass Q x).toReal) (KA x)
    hbudgetlog hcode hscore
  have hMtop : universalContinuousSemimeasure x ≠ ⊤ := by
    have h1 := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.le_one x
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hQtop : cantorMass Q x ≠ ⊤ := by
    have : IsProbabilityMeasure Q := hQ.1
    have h1 : cantorMass Q x ≤ 1 := prob_le_one
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hlog : Real.logb 2 ((universalContinuousSemimeasure x).toReal / (cantorMass Q
      x).toReal) ≤ ((3 * (computableMeasureComplexity U P).toNat + D : ℕ) : ℝ) := by
    have hKA : KA x = - Real.logb 2 (universalContinuousSemimeasure x).toReal := by rfl
    have halg2 : Real.logb 2 (universalContinuousSemimeasure x).toReal - Real.logb 2
        (cantorMass Q x).toReal ≤ ((3 * (computableMeasureComplexity U P).toNat + D : ℕ) : ℝ) := by
      have halgh2 := halg.2
      rw [hKA] at halgh2
      linarith
    have hmreal : 0 < (universalContinuousSemimeasure x).toReal := ENNReal.toReal_pos
        (ne_of_gt hm) hMtop
    have hqreal : 0 < (cantorMass Q x).toReal := ENNReal.toReal_pos (ne_of_gt hq) hQtop
    rw [Real.logb_div hmreal.ne' hqreal.ne']
    exact halg2
  have hlog2 : (universalContinuousSemimeasure x).toReal / (cantorMass Q x).toReal ≤ 2 ^
      ((3 * (computableMeasureComplexity U P).toNat + D : ℕ) : ℝ) := by
    have hmreal : 0 < (universalContinuousSemimeasure x).toReal := ENNReal.toReal_pos
        (ne_of_gt hm) hMtop
    have hqreal : 0 < (cantorMass Q x).toReal := ENNReal.toReal_pos (ne_of_gt hq) hQtop
    exact (Real.logb_le_iff_le_rpow (by norm_num) (div_pos hmreal hqreal)).mp hlog
  have hqreal2 : 0 < (cantorMass Q x).toReal := ENNReal.toReal_pos (ne_of_gt hq) hQtop
  have h3 : (universalContinuousSemimeasure x).toReal ≤ 2 ^ ((3 *
      (computableMeasureComplexity U P).toNat + D : ℕ) : ℝ) * (cantorMass Q x).toReal :=
      (div_le_iff₀ hqreal2).mp hlog2
  have h4 : 2 ^ ((3 * (computableMeasureComplexity U P).toNat + D : ℕ) : ℝ) *
      (cantorMass Q x).toReal = ((2 : ℝ≥0∞) ^ (3 * (computableMeasureComplexity U
      P).toNat + D) * cantorMass Q x).toReal := by
    rw [ENNReal.toReal_mul]
    have hpow : ((2 : ℝ≥0∞) ^ (3 * (computableMeasureComplexity U P).toNat + D)).toReal
        = 2 ^ ((3 * (computableMeasureComplexity U P).toNat + D : ℕ) : ℝ) := by
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      exact (Real.rpow_natCast 2 _).symm
    rw [hpow]
  rw [h4] at h3
  have h5 : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ (3 *
      (computableMeasureComplexity U P).toNat + D) * cantorMass Q x := by
    apply (ENNReal.toReal_le_toReal hMtop ?_).mp
    · exact h3
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hQtop
  exact inv_pow_mul_universal_le_mass Q x _ h5

/-- A winner's model complexity is bounded by the source model's complexity and budget.
Blueprint node `base:winner`. -/
theorem winner_bounds_complexity (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ)
    (hc : ∀ R : Measure CantorSeq, IsProbabilityMeasure R →
      IsComputableMeasure R → ∀ x : BitString, 0 < cantorMass R x →
        KA x ≤ (computableMeasureComplexity U R).toNat -
          Real.logb 2 (cantorMass R x).toReal + c)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (hP : IsComputableMeasure P)
    (w : CantorSeq) (D n : ℕ) (hbudget : PathBudget P w D)
    (Q : Measure CantorSeq) (hQ : IsGlobalWinner U hU Q (cantorPrefix w n)) :
    2 * (computableMeasureComplexity U Q).toNat ≤
      3 * (computableMeasureComplexity U P).toNat + D + c := by
  let x := cantorPrefix w n
  have hp : 0 < cantorMass P x := base_budget_positive P w D n hbudget
  have hq : 0 < cantorMass Q x := hQ.2.2.1
  have H_score := hQ.2.2.2 P inferInstance hP hp
  unfold score at H_score
  have hp_ne_zero : cantorMass P x ≠ 0 := hp.ne'
  have hq_ne_zero : cantorMass Q x ≠ 0 := hq.ne'
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hq_ne_zero h))] at H_score
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hp_ne_zero h))] at H_score
  have H_score_real := EReal.coe_le_coe_iff.mp H_score
  have H_Q := hc Q hQ.1 hQ.2.1 x hq
  have H_budget := (base_budget_log P x D hp).mp (hbudget n)
  have h_bound_real : (2 : ℝ) * ((computableMeasureComplexity U Q).toNat : ℝ) ≤ 
      (3 : ℝ) * ((computableMeasureComplexity U P).toNat : ℝ) + (D : ℝ) + (c : ℝ) := by
    linarith [H_score_real, H_Q, H_budget]
  exact_mod_cast h_bound_real

/-- The source mass dominates universal mass along a budgeted path; all three masses are
positive at a winner prefix. Blueprint node `base:winner`. -/
theorem winner_bounds_mass (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (w : CantorSeq) (D n : ℕ) (hbudget : PathBudget P w D)
    (Q : Measure CantorSeq) (hQ : IsGlobalWinner U hU Q (cantorPrefix w n)) :
    (2 : ℝ≥0∞)⁻¹ ^ D * universalContinuousSemimeasure (cantorPrefix w n) ≤
        cantorMass P (cantorPrefix w n) ∧
      0 < universalContinuousSemimeasure (cantorPrefix w n) ∧
      0 < cantorMass P (cantorPrefix w n) ∧
      0 < cantorMass Q (cantorPrefix w n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← ENNReal.inv_pow, mul_comm]
    apply (ENNReal.mul_inv_le_iff _ _).mpr
    · rw [mul_comm]
      exact hbudget n
    · exact pow_ne_zero D (by norm_num)
    · exact ENNReal.pow_ne_top (by norm_num)
  · exact universalContinuousSemimeasure_pos _
  · exact base_budget_positive P w D n hbudget
  · exact hQ.2.2.1

end Kolmogorov.MDLPrediction
