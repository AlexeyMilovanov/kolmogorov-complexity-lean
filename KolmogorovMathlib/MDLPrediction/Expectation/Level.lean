/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model
import KolmogorovMathlib.Solomonoff.Expectation
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# One-level cylinder expectation

Every level of the binary tree is a finite cylinder partition. The formula
uses a nonnegative real function and evaluates the lintegral in `ENNReal`.

Blueprint node: `exp:level-integral`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal BigOperators

/-- The lintegral of a nonnegative function of one prefix is its weighted
finite-level cylinder sum. Blueprint node `exp:level-integral`. -/
theorem exp_level_integral (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (n : ℕ) (e : BitString → ℝ) :
    (∫⁻ w, ENNReal.ofReal (e (cantorPrefix w n)) ∂P) =
      ∑ x ∈ levelFinset n, cantorMass P x * ENNReal.ofReal (e x) := by
  have H := lintegral_comp_cantorPrefix P n (fun x => ENNReal.ofReal (e x))
  rw [H]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]

end Kolmogorov.MDLPrediction
