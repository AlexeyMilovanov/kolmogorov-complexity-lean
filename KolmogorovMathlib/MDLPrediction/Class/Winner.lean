/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Compiler
import KolmogorovMathlib.MDLPrediction.Core.Budget

/-!
# Bounds on a class minimizer along a budgeted path

Constants for the universal two-part code and the class compiler precede the
target measure, selected winner, prefix, and path budget.
Blueprint nodes: `enum:winner`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- A path budget bounds the negative log cylinder mass at each prefix. -/
private lemma budget_log_le (P : Measure CantorSeq) (w : CantorSeq)
    (D : ℕ) (x : BitString) (hP : IsProbabilityMeasure P) (hx : ∃ n : ℕ, x = cantorPrefix w n)
    (hbudget : PathBudget P w D) :
    0 < cantorMass P x ∧ -Real.logb 2 (cantorMass P x).toReal - KA x ≤ (D : ℝ) := by
  obtain ⟨n, rfl⟩ := hx
  have hpos : 0 < cantorMass P (cantorPrefix w n) := base_budget_positive P w D n hbudget
  have hlog : -Real.logb 2 (cantorMass P (cantorPrefix w n)).toReal -
      KA (cantorPrefix w n) ≤ (D : ℝ) :=
    (base_budget_log P (cantorPrefix w n) D hpos).mp (hbudget n)
  exact ⟨hpos, hlog⟩

/-- The class compiler bounds absolute complexity by relative complexity. -/
private lemma computableMeasureComplexity_le_classComplexity_add (U : Map) (hU :
  IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq) (hQ : Q ∈ A.carrier)
    (cA : ℕ) (hcA : ∀ i : ℕ, KPNat U (A.toIndex i) ≤ KPNat U i + cA) :
    (computableMeasureComplexity U Q).toNat ≤ classComplexity U hU A Q + cA := by
  obtain ⟨h_fin, i, hi_eq, hi_k⟩ := enum_relative_attained U hU A Q hQ
  have hi_spec : IsComputableMeasureIndex (A.A i).measure (A.toIndex i) := A.toIndex_spec i
  have heq : (A.A i).measure = Q := hi_eq
  have hi_spec' : IsComputableMeasureIndex Q (A.toIndex i) := by
    rw [← heq]
    exact hi_spec
  have h1 : computableMeasureComplexity U Q ≤ KPNat U (A.toIndex i) :=
    computableMeasureComplexity_le U hi_spec'
  have h2 : KPNat U (A.toIndex i) ≤ KPNat U i + cA := hcA i
  have h3 : computableMeasureComplexity U Q ≤ classComplexityENat U hU A Q + cA := by
    calc
      computableMeasureComplexity U Q ≤ KPNat U (A.toIndex i) := h1
      _ ≤ KPNat U i + (cA : ENat) := h2
      _ = classComplexityENat U hU A Q + cA := by rw [hi_k]
  have h_right_fin : classComplexityENat U hU A Q + cA ≠ ⊤ := by
    exact WithTop.add_ne_top.mpr ⟨h_fin, ENat.natCast_ne_top cA⟩
  have h_le := ENat.toNat_le_toNat h3 h_right_fin
  rw [ENat.toNat_add h_fin (ENat.natCast_ne_top cA), ENat.toNat_natCast] at h_le
  exact h_le

/-- A score winner receives enough mass along the budgeted path. -/
private lemma winner_mass_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (P Q : Measure CantorSeq) (D : ℕ) (x : BitString)
    (hP : IsProbabilityMeasure P) (hQ : IsProbabilityMeasure Q)
    (hmP : 0 < cantorMass P x) (hmQ : 0 < cantorMass Q x)
    (h_score : 3 * (classComplexity U hU A Q : ℝ) - Real.logb 2 (cantorMass Q x).toReal ≤
      3 * (classComplexity U hU A P : ℝ) - Real.logb 2 (cantorMass P x).toReal)
    (h_budget : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ D * cantorMass P x) :
    universalContinuousSemimeasure x ≤
      (2 : ℝ≥0∞) ^ (3 * classComplexity U hU A P + D) * cantorMass Q x := by
  have hP_ne_top : cantorMass P x ≠ ⊤ := by
    have _inst1 : IsProbabilityMeasure P := by exact hP
    exact measure_ne_top P _
  have hQ_ne_top : cantorMass Q x ≠ ⊤ := by
    have _inst2 : IsProbabilityMeasure Q := by exact hQ
    exact measure_ne_top Q _
  have hp : 0 < (cantorMass P x).toReal := ENNReal.toReal_pos hmP.ne' hP_ne_top
  have hq : 0 < (cantorMass Q x).toReal := ENNReal.toReal_pos hmQ.ne' hQ_ne_top
  have hlog : Real.logb 2 ((cantorMass P x).toReal / (cantorMass Q x).toReal) ≤
      ((3 * classComplexity U hU A P : ℕ) : ℝ) := by
    rw [Real.logb_div hp.ne' hq.ne']
    push_cast
    have hkQ_nonneg : 0 ≤ (classComplexity U hU A Q : ℝ) := Nat.cast_nonneg _
    linarith
  rw [Real.logb_le_iff_le_rpow (by norm_num) (div_pos hp hq), Real.rpow_natCast,
    div_le_iff₀ hq] at hlog
  have h_le : cantorMass P x ≤ (2 : ℝ≥0∞) ^ (3 * classComplexity U hU A P) * cantorMass Q x := by
    rw [← ENNReal.toReal_le_toReal hP_ne_top (ENNReal.mul_ne_top (by simp) hQ_ne_top)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    exact hlog
  calc
    universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ D * cantorMass P x := h_budget
    _ ≤ (2 : ℝ≥0∞) ^ D * ((2 : ℝ≥0∞) ^ (3 * classComplexity U hU A P) * cantorMass Q x) := by gcongr
    _ = (2 : ℝ≥0∞) ^ (3 * classComplexity U hU A P + D) * cantorMass Q x := by
      rw [← mul_assoc, ← pow_add, add_comm D]

/-- The score and budget inequalities bound winner complexity. -/
private lemma winner_complexity_ineq (kP kQ D cU cA : ℕ) (log_mP log_mQ KA_x : ℝ)
    (h_score : 3 * (kQ : ℝ) - log_mQ ≤ 3 * (kP : ℝ) - log_mP)
    (h_budget : -log_mP - KA_x ≤ (D : ℝ))
    (h_cU : KA_x ≤ (kQ : ℝ) - log_mQ + (cU : ℝ) + (cA : ℝ)) :
    2 * kQ ≤ 3 * kP + D + cU + cA := by
  have h : (2 * kQ : ℝ) ≤ 3 * kP + D + cU + cA := by linarith
  exact_mod_cast h

/-- A class score winner has enough cylinder mass and bounded relative complexity
along a path budgeted by a class member. Blueprint node `enum:winner`. -/
theorem class_winner_bounds (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ cU cA : ℕ,
      (∀ R : Measure CantorSeq, IsProbabilityMeasure R →
        IsComputableMeasure R → ∀ x : BitString, 0 < cantorMass R x →
          KA x ≤ (computableMeasureComplexity U R).toNat -
            Real.logb 2 (cantorMass R x).toReal + cU) ∧
      (∀ i : ℕ, KPNat U (A.toIndex i) ≤ KPNat U i + cA) ∧
      ∀ (P Q : Measure CantorSeq) (w : CantorSeq) (D : ℕ) (x : BitString),
        P ∈ A.carrier → (∃ n : ℕ, x = cantorPrefix w n) →
        PathBudget P w D → IsClassWinner U hU A Q x →
          universalContinuousSemimeasure x ≤
            (2 : ℝ≥0∞) ^ (3 * classComplexity U hU A P + D) *
              cantorMass Q x ∧
          2 * classComplexity U hU A Q ≤
            3 * classComplexity U hU A P + D + cU + cA := by
  obtain ⟨cU, hcU⟩ := KA_le_measure_code U hU
  obtain ⟨cA, hcA⟩ := enum_compiler U hU A
  use cU, cA
  refine ⟨hcU, hcA, ?_⟩
  intros P Q w D x hP_in hx hbudget hQ_winner
  have hQ_in := hQ_winner.1
  have hmQ_pos := hQ_winner.2.1
  have hP_prob : IsProbabilityMeasure P := by
    obtain ⟨i, hi⟩ := hP_in
    rw [← hi]
    exact (A.A i).probability
  have hQ_prob : IsProbabilityMeasure Q := by
    obtain ⟨i, hi⟩ := hQ_in
    rw [← hi]
    exact (A.A i).probability
  have hQ_comp : IsComputableMeasure Q := by
    obtain ⟨i, hi⟩ := hQ_in
    rw [← hi]
    exact (A.A i).computable
  obtain ⟨hmP_pos, h_budget_log⟩ := budget_log_le P w D x hP_prob hx hbudget
  have h_score : 3 * (classComplexity U hU A Q : ℝ) - Real.logb 2 (cantorMass Q x).toReal ≤
    3 * (classComplexity U hU A P : ℝ) - Real.logb 2 (cantorMass P x).toReal :=
      by
        have h := hQ_winner.2.2 P hP_in hmP_pos
        simp only [classScore, hmQ_pos.ne', hmP_pos.ne', ↓reduceIte,
          EReal.coe_le_coe_iff] at h
        exact h
  have h_bridge : (computableMeasureComplexity U Q).toNat ≤ classComplexity U hU A Q + cA :=
    computableMeasureComplexity_le_classComplexity_add U hU A Q hQ_in cA hcA
  have h_two_part := hcU Q hQ_prob hQ_comp x hmQ_pos
  have h_cU : KA x ≤ (classComplexity U hU A Q : ℝ) -
      Real.logb 2 (cantorMass Q x).toReal + (cU : ℝ) + (cA : ℝ) := by
    have h1 : ((computableMeasureComplexity U Q).toNat : ℝ) ≤
        (classComplexity U hU A Q + cA : ℝ) := by
      exact_mod_cast h_bridge
    linarith [h_two_part]
  have h_budget_at_x : universalContinuousSemimeasure x ≤ (2 : ℝ≥0∞) ^ D * cantorMass P x := by
    obtain ⟨n, hn⟩ := hx
    rw [hn]
    exact hbudget n
  constructor
  · exact winner_mass_le U hU A P Q D x hP_prob hQ_prob hmP_pos hmQ_pos h_score
      h_budget_at_x
  · apply winner_complexity_ineq (classComplexity U hU A P)
      (classComplexity U hU A Q) D cU cA
      (Real.logb 2 (cantorMass P x).toReal) (Real.logb 2 (cantorMass Q x).toReal) (KA x)
    · exact h_score
    · exact h_budget_log
    · exact h_cU
end Kolmogorov.MDLPrediction
