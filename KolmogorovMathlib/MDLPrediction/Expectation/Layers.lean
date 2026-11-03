/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Expectation.Tail

/-!
# Least natural path budgets and geometric layers

The default value outside the full-measure set of budgeted paths is irrelevant
to the layer bounds. The least budget is selected by natural well ordering.

Blueprint node: `exp:budget-layers`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- The least natural budget when one exists, and zero on the null complement.
Blueprint node `exp:budget-layers`. -/
noncomputable def leastBudget (P : Measure CantorSeq) (w : CantorSeq) : ℕ :=
  by
    classical
    exact if h : ∃ D : ℕ, PathBudget P w D then Nat.find h else 0

/-- Almost every path of a proper measure has a natural budget.
Blueprint node `exp:budget-layers`. -/
theorem ae_exists_budget (P : Measure CantorSeq) [IsProbabilityMeasure P] :
    ∀ᵐ w ∂P, ∃ D : ℕ, PathBudget P w D := by
  rw [ae_iff]
  exact measure_no_budget_eq_zero P

/-- The measure of every positive least-budget layer decays geometrically.
Blueprint node `exp:budget-layers`. -/
theorem exp_budget_layers (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d) :
    P {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d} ≤
      (2 : ℝ≥0∞)⁻¹ ^ (d - 1) := by
  have H : {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d} ⊆ budgetFailure P (d - 1) := by
    intro w hw
    simp only [Set.mem_ofPred_eq, budgetFailure] at hw ⊢
    rcases hw with ⟨hw_ex, hw_least⟩
    unfold leastBudget at hw_least
    classical
    rw [dite_eq_left] at hw_least
    swap
    · exact hw_ex
    have h_not : ¬ PathBudget P w (d - 1) := by
      intro h
      have h_find : @Nat.find (fun n => PathBudget P w n) _ hw_ex ≤ d - 1 :=
        @Nat.find_min' (fun n => PathBudget P w n) _ hw_ex (d - 1) h
      omega
    unfold PathBudget at h_not
    push Not at h_not
    exact h_not
  exact (measure_mono H).trans (measure_budget_failure_le P (d - 1))

/-- The least-budget zero layer has measure at most one.
Blueprint node `exp:budget-layers`. -/
theorem exp_budget_zero_layer (P : Measure CantorSeq) [IsProbabilityMeasure P] :
    P {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = 0} ≤ 1 := by
  exact prob_le_one

end Kolmogorov.MDLPrediction
