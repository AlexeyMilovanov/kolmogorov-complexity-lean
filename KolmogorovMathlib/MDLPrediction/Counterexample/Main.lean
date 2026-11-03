/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Counterexample.Deficiency
import KolmogorovMathlib.MDLPrediction.Core.Budget
import Mathlib.Analysis.SpecialFunctions.CompareExp

/-!
# Failure of a measure-uniform prefix-deficiency drop

The positive-mass deficiency has no universal logarithmic-drop constant as the
computable measure varies. A fixed-measure version may use a constant depending
on that measure; the printed varying-measure application cannot use such a constant.

Blueprint nodes: `audit:lemma5`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

open scoped ENNReal

/-- The linear branch length eventually exceeds any logarithmic drop bound. -/
private lemma exists_large_drop (C c : ℝ) :
  ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) - c > 2 * Real.logb 2 (max 1 (2 * (k : ℝ) - (KA [true] : ℝ))) + C := by
  set a : ℝ := KA [true]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : 0 < Real.log 2 / 8 := by positivity
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (Real.isLittleO_log_id_atTop.def he)
  obtain ⟨k, hk⟩ := exists_nat_ge (max (max 1 ((X + a) / 2)) (max ((1 + a) / 2) (2 * c +
      2 * C - a / 2 + 1)))
  have hk_real : (max (max 1 ((X + a) / 2)) (max ((1 + a) / 2) (2 * c + 2 * C - a / 2 +
      1))) ≤ (k : ℝ) := hk
  have hk0 : (1 : ℝ) ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk_real)
  have hk1 : (X + a) / 2 ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk_real)
  have hk2 : (1 + a) / 2 ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk_real)
  have hk3 : 2 * c + 2 * C - a / 2 + 1 ≤ k := (le_max_right _ _).trans ((le_max_right _
      _).trans hk_real)
  refine ⟨k, by exact_mod_cast hk0, ?_⟩
  have hy1 : 1 ≤ 2 * (k : ℝ) - a := by linarith
  rw [max_eq_right hy1]
  have hlog := hX _ (by linarith : X ≤ 2 * (k : ℝ) - a)
  simp only [id, Real.norm_eq_abs] at hlog
  rw [abs_of_nonneg (Real.log_nonneg hy1), abs_of_nonneg (by linarith)] at hlog
  have hlogb : Real.logb 2 (2 * (k : ℝ) - a) ≤ (2 * (k : ℝ) - a) / 8 := by
    rw [Real.logb, div_le_iff₀ hl2]
    linarith
  linarith

/-- The explicit deficiency drop contradicts a measure independent bound. -/
private lemma drop_violates_uniform_bound
    (C c : ℝ) (k : ℕ)
    (h_growth : (k : ℝ) - c > 2 * Real.logb 2 (max 1 (2 * (k : ℝ) - (KA [true] : ℝ))) + C)
    (z : BitString)
    (hs : 0 < cantorMass (atomicWitness k z) [true])
    (hh : 0 < cantorMass (atomicWitness k z) (true :: z))
    (h_drop : positiveDeficiency (atomicWitness k z) [true] hs -
      positiveDeficiency (atomicWitness k z) (true :: z) hh ≥ (k : ℝ) - c)
    (hmass : cantorMass (atomicWitness k z) [true] = (2 : ℝ≥0∞)⁻¹ ^ (2 * k)) :
    ¬ (positiveDeficiency (atomicWitness k z) (true :: z) hh ≥
      positiveDeficiency (atomicWitness k z) [true] hs -
        2 * Real.logb 2 (max 1 (positiveDeficiency (atomicWitness k z) [true] hs)) - C) := by
  have hds : positiveDeficiency (atomicWitness k z) [true] hs = 2 * (k : Real) - KA [true] := by
    unfold positiveDeficiency
    rw [hmass, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Real.logb_pow,
      Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  intro h
  rw [hds] at h h_drop
  linarith

/-- No constant independent of the varying computable proper measure controls
prefix deficiency drop by twice the logarithm of the earlier deficiency.
Blueprint node `audit:lemma5`. -/
theorem uniformPrefixDropFalse :
    ¬ ∃ C : ℝ, ∀ (Q : Measure CantorSeq) (s h : BitString),
      IsProbabilityMeasure Q → IsComputableMeasure Q → s <+: h →
      ∀ hs : 0 < cantorMass Q s, ∀ hh : 0 < cantorMass Q h,
        positiveDeficiency Q h hh ≥ positiveDeficiency Q s hs -
          2 * Real.logb 2 (max 1 (positiveDeficiency Q s hs)) - C := by
  intro ⟨C, hC⟩
  rcases audit_drop with ⟨c, hc⟩
  rcases exists_large_drop C c with ⟨k, hk, h_growth⟩
  rcases hc k hk with ⟨z, hz_len, hz_ka_lower, hz_ka_upper, h_prob, h_comp, hs, hh, h_drop⟩
  have h_mass : cantorMass (atomicWitness k z) [true] = (2 : ℝ≥0∞)⁻¹ ^ (2 * k) := by
    have h_atomic := audit_atomic k z
    exact h_atomic.2.2.1
  have h_s_prefix_h : [true] <+: (true :: z) := ⟨z, rfl⟩
  have h_Q := hC (atomicWitness k z) [true] (true :: z) h_prob h_comp h_s_prefix_h hs hh
  exact drop_violates_uniform_bound C c k h_growth z hs hh h_drop
    h_mass h_Q

end Kolmogorov.MDLPrediction
