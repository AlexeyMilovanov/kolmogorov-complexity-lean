/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Budget
import Mathlib.Topology.Basic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria

/-!
# A priori budget-failure tail

The estimate requires properness only. Failure of every natural budget is a null event.

Blueprint node: `exp:tail`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- The event that a path violates a given natural multiplicative budget.
Blueprint node `exp:tail`. -/
def budgetFailure (P : Measure CantorSeq) (d : ℕ) : Set CantorSeq :=
  {w | ∃ n, (2 : ℝ≥0∞) ^ d * cantorMass P (cantorPrefix w n) <
    universalContinuousSemimeasure (cantorPrefix w n)}

/-- The measure of a budget-failure event has a geometric tail.
Blueprint node `exp:tail`. -/
theorem measure_budget_failure_le (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (d : ℕ) : P (budgetFailure P d) ≤ (2 : ℝ≥0∞)⁻¹ ^ d := by
  have H := measure_prefixHitSet_le_of_tsum_antichain_le P universalContinuousSemimeasure d
    tsum_antichain_universalContinuousSemimeasure_le_one
  have h_eq : budgetFailure P d = prefixHitSet {x | (2 : ℝ≥0∞) ^ d * cantorMass P x <
      universalContinuousSemimeasure x} := by
    ext w
    rfl
  rw [h_eq]
  exact H


/-- A path with no finite budget lies in every budget-failure event. -/
private lemma no_budget_subset_iInter_failure (P : Measure CantorSeq) :
    {w | ¬ ∃ D : ℕ, PathBudget P w D} ⊆ ⋂ d : ℕ, budgetFailure P d := by
  intro w hw
  simp only [Set.mem_ofPred_eq, not_exists] at hw
  simp only [Set.mem_iInter, budgetFailure, Set.mem_ofPred_eq]
  intro d
  have hw_d := hw d
  unfold PathBudget at hw_d
  push Not at hw_d
  exact hw_d

/-- Paths having no finite natural budget form a null set.
Blueprint node `exp:tail`. -/
theorem measure_no_budget_eq_zero (P : Measure CantorSeq)
    [IsProbabilityMeasure P] :
    P {w | ¬ ∃ D : ℕ, PathBudget P w D} = 0 := by
  have H (d : ℕ) : P (budgetFailure P d) ≤ (2 : ℝ≥0∞)⁻¹ ^ d := measure_budget_failure_le P d
  have H3 : ∀ d : ℕ, P {w | ¬ ∃ D : ℕ, PathBudget P w D} ≤ (2 : ℝ≥0∞)⁻¹ ^ d := by
    intro d
    calc
      P {w | ¬ ∃ D : ℕ, PathBudget P w D} ≤ P (⋂ d : ℕ, budgetFailure P d) :=
        measure_mono (no_budget_subset_iInter_failure P)
      _ ≤ P (budgetFailure P d) := measure_mono (Set.iInter_subset _ d)
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ d := H d
  have h2 : Filter.Tendsto (fun (d : ℕ) => (2 : ℝ≥0∞)⁻¹ ^ d) Filter.atTop (nhds 0) := by
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have H4 : P {w | ¬ ∃ D : ℕ, PathBudget P w D} ≤ 0 :=
    ge_of_tendsto h2 (Filter.Eventually.of_forall H3)
  exact le_antisymm H4 (zero_le)
end Kolmogorov.MDLPrediction
