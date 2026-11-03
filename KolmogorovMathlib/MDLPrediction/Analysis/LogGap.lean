/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary logarithmic and binary mean gaps

The analytic estimates are real valued. Their positivity hypotheses precede every
logarithm whose value is used in an inequality.

Blueprint nodes: `exp:convex`, `exp:log-nonneg`.
-/

namespace Kolmogorov.MDLPrediction

/-- The tangent-line lower bound for the negative logarithm.
Blueprint node `exp:log-nonneg`. -/
theorem exp_log_nonneg {t : ℝ} (ht1 : t < 1) :
    t ≤ -Real.log (1 - t) := by
  have h1 : 0 < 1 - t := sub_pos.mpr ht1
  have h2 := Real.log_le_sub_one_of_pos h1
  linarith

/-- The logarithmic binary mean gap controls squared separation.
Blueprint node `exp:convex`. -/
theorem log_mean_gap_ge_sq {p q : ℝ}
    (hp : 0 < p ∧ p ≤ 1) (hq : 0 < q ∧ q ≤ 1) :
    (p - q) ^ 2 / (8 * Real.log 2) ≤
      Real.logb 2 ((p + q) / 2) -
        (Real.logb 2 p + Real.logb 2 q) / 2 := by
  have hl2 : 0 < Real.log 2 := by positivity
  have hS0 : 0 < p + q := add_pos hp.1 hq.1
  have hS0_ne : p + q ≠ 0 := ne_of_gt hS0
  set t := ((p - q) / (p + q)) ^ 2
  have ht1 : t < 1 := by
    change ((p - q) / (p + q)) ^ 2 < 1
    rw [sq_lt_one_iff_abs_lt_one]
    rw [abs_div, abs_of_pos hS0]
    rw [div_lt_one hS0]
    rcases le_total p q with hpq_le | hpq_ge
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have H := exp_log_nonneg ht1
  have H2 : Real.logb 2 ((p + q) / 2) - (Real.logb 2 p + Real.logb 2 q) / 2 =
            -(Real.log (1 - t)) / (2 * Real.log 2) := by
    dsimp only [t]
    have h1 : 1 - ((p - q) / (p + q)) ^ 2 = 4 * p * q / (p + q) ^ 2 := by
      have hd : (p + q) ^ 2 ≠ 0 := pow_ne_zero 2 hS0_ne
      calc
        1 - ((p - q) / (p + q)) ^ 2 = 1 - (p - q) ^ 2 / (p + q) ^ 2 := by rw [div_pow]
        _ = ((p + q) ^ 2 - (p - q) ^ 2) / (p + q) ^ 2 := by
          rw [← div_self hd, sub_div]
        _ = 4 * p * q / (p + q) ^ 2 := by
          congr 1
          ring
    change Real.log _ / Real.log 2 - (Real.log p / Real.log 2 + Real.log q / Real.log 2) / 2 = _
    rw [h1]
    have h_log1 : Real.log ((p + q) / 2) = Real.log (p + q) - Real.log 2 := by
      rw [Real.log_div hS0_ne (by positivity)]
    have h_log_frac : Real.log (4 * p * q / (p + q) ^ 2) =
      Real.log 4 + Real.log p + Real.log q - 2 * Real.log (p + q) := by
      have hp0_ne : p ≠ 0 := ne_of_gt hp.1
      have hq0_ne : q ≠ 0 := ne_of_gt hq.1
      have h4p0_ne : 4 * p ≠ 0 := mul_ne_zero (by norm_num) hp0_ne
      rw [Real.log_div (mul_ne_zero h4p0_ne hq0_ne) (pow_ne_zero 2 hS0_ne)]
      rw [Real.log_mul h4p0_ne hq0_ne, Real.log_mul (by norm_num) hp0_ne]
      rw [Real.log_pow]
      ring
    have h_log4 : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [this, Real.log_pow]
      norm_cast
    rw [h_log1, h_log_frac, h_log4]
    ring
  rw [H2]
  have H3 : (p - q) ^ 2 / 4 ≤ t := by
    dsimp only [t]
    have hS2 : p + q ≤ 2 := by linarith
    have hS2_sq : (p + q) ^ 2 ≤ 4 := by
      have h : (p + q) ^ 2 ≤ 2 ^ 2 := sq_le_sq.mpr (by
        rw [abs_of_pos hS0, abs_of_pos (by positivity)]
        exact hS2)
      linarith
    rw [div_pow]
    have hdiv : 1 / (4 : ℝ) ≤ 1 / (p + q) ^ 2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact hS2_sq
    have H3_mul : (p - q) ^ 2 * (1 / 4) ≤ (p - q) ^ 2 * (1 / (p + q) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
    have H3_1 : (p - q) ^ 2 * (1 / 4) = (p - q) ^ 2 / 4 := by ring
    have H3_2 : (p - q) ^ 2 * (1 / (p + q) ^ 2) = (p - q) ^ 2 / (p + q) ^ 2 := by ring
    rwa [H3_1, H3_2] at H3_mul
  have H4 : (p - q) ^ 2 / (8 * Real.log 2) = ((p - q) ^ 2 / 4) / (2 * Real.log 2) := by ring
  rw [H4]
  have H5 : ((p - q) ^ 2 / 4) / (2 * Real.log 2) ≤ -Real.log (1 - t) / (2 * Real.log 2) := by
    apply div_le_div_of_nonneg_right
    · calc
        (p - q) ^ 2 / 4 ≤ t := H3
        _ ≤ -Real.log (1 - t) := H
    · positivity
  exact H5

end Kolmogorov.MDLPrediction
