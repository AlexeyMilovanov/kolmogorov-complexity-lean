/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model
import KolmogorovMathlib.Solomonoff.Domination

/-!
# Uniform two-part code bound

The coding constant depends on the fixed optimal prefix machine and precedes the choice
of computable probability measure and cylinder. All log claims require positive mass.

Blueprint nodes: `base:two-part`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- A uniform coding bound for all computable proper measures and positive cylinders.
Blueprint node `base:two-part`. -/
theorem KA_le_measure_code (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ P : Measure CantorSeq, IsProbabilityMeasure P →
      IsComputableMeasure P → ∀ x : BitString, 0 < cantorMass P x →
        KA x ≤ (computableMeasureComplexity U P).toNat -
          Real.logb 2 (cantorMass P x).toReal + c := by
  obtain ⟨C, hC⟩ := exists_const_two_pow_complexity_mul_cantorMass_le_universal U hU
  use C
  intro P _ hP x hx
  have h := hC P hP x
  have h_m_pos : 0 < (universalContinuousSemimeasure x).toReal := by
    apply ENNReal.toReal_pos
    · exact (universalContinuousSemimeasure_pos x).ne'
    · exact universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hp_pos : 0 < (cantorMass P x).toReal := by
    apply ENNReal.toReal_pos
    · exact hx.ne'
    · apply ne_top_of_le_ne_top (ENNReal.one_ne_top)
      exact prob_le_one
  have hp_le_one : (cantorMass P x).toReal ≤ 1 := by
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  have h_toReal := ENNReal.toReal_mono
    (universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x) h
  rw [ENNReal.toReal_mul] at h_toReal
  rw [ENNReal.toReal_pow] at h_toReal
  rw [ENNReal.toReal_inv] at h_toReal
  rw [ENNReal.toReal_ofNat] at h_toReal
  unfold KA
  have hl := (Real.logb_le_logb (by norm_num : (1:ℝ) < 2) (by positivity) h_m_pos).mpr h_toReal
  have h_log_mul : Real.logb 2 ((2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U P).toNat + C) *
      (cantorMass P x).toReal) =
      Real.logb 2 ((2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U P).toNat + C)) +
      Real.logb 2 (cantorMass P x).toReal := by
    apply Real.logb_mul
    · positivity
    · exact hp_pos.ne'
  rw [h_log_mul] at hl
  have h_log_pow : Real.logb 2 ((2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U P).toNat + C)) =
      -(((computableMeasureComplexity U P).toNat + C : ℕ) : ℝ) := by
    have h_log_inv : Real.logb 2 (2 : ℝ)⁻¹ = -1 := by
      rw [Real.logb_inv]
      norm_num
    rw [Real.logb_pow, h_log_inv]
    ring
  rw [h_log_pow] at hl
  push_cast at hl ⊢
  linarith
end Kolmogorov.MDLPrediction
