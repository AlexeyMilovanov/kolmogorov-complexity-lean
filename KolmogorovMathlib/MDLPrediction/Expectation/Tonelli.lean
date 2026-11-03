/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Expectation.Level
import KolmogorovMathlib.MDLPrediction.Core.Argmin
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings
import Mathlib.MeasureTheory.Integral.Lebesgue.Add


/-!
# Nonnegative Tonelli and length reindexing

The exchange works for changing finite-prefix functions. Summing by levels
enumerates each finite bitstring once.

Blueprint nodes: `exp:tonelli-sum`, `exp:tonelli`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal BigOperators

/-- A countable sum of measurable nonnegative path functions exchanges with
the lintegral. Blueprint node `exp:tonelli-sum`. -/
theorem exp_tonelli_sum (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (f : ℕ → BitString → ℝ≥0∞) :
    (∫⁻ w, ∑' n, f n (cantorPrefix w n) ∂P) =
      ∑' n, ∫⁻ w, f n (cantorPrefix w n) ∂P := by
  exact lintegral_tsum fun n =>
    (Kolmogorov.measurable_comp_cantorPrefix n (f n)).aemeasurable

/-- Equivalence between bitstrings and their length-indexed levels. -/
private def bitStringEquivLengthSigma :
    BitString ≃ Σ n : ℕ, {x : BitString // x ∈ levelFinset n} where
  toFun x := ⟨x.length, ⟨x, mem_levelFinset.mpr rfl⟩⟩
  invFun p := p.2.1
  left_inv x := rfl
  right_inv p := by
    rcases p with ⟨n, x, hx⟩
    dsimp
    have : x.length = n := mem_levelFinset.mp hx
    cases this
    rfl

/-- A nonnegative bitstring sum reindexes by word length.
Blueprint node `exp:tonelli-sum`. -/
theorem exp_tonelli_sum_reindex (g : BitString → ℝ≥0∞) :
    (∑' x : BitString, g x) = ∑' n : ℕ, ∑ x ∈ levelFinset n, g x := by
  have H := Equiv.tsum_eq bitStringEquivLengthSigma.symm g
  rw [← H]
  rw [ENNReal.tsum_sigma']
  congr 1
  ext n
  have : (fun (b : ↥(levelFinset n)) =>
      g (bitStringEquivLengthSigma.symm ⟨n, b⟩)) = fun b => g b.val := by
    ext b
    rfl
  rw [this]
  rw [Finset.tsum_subtype]

/-- The path lintegral of a changing predictor equals both the weighted tree
sum and its sum by levels. Blueprint node `exp:tonelli`. -/
theorem integral_path_error_eq_tsum (P : Measure CantorSeq)
    [IsProbabilityMeasure P] (h : BitString → ℝ) :
    let e : BitString → ℝ≥0∞ := fun x =>
      ENNReal.ofReal ((h x - condProb (cantorMass P) x false) ^ 2)
    (∫⁻ w, ∑' n : ℕ, e (cantorPrefix w n) ∂P) =
      (∑' x : BitString, cantorMass P x * e x) ∧
    (∑' x : BitString, cantorMass P x * e x) =
      (∑' n : ℕ, ∑ x ∈ levelFinset n, cantorMass P x * e x) := by
  intro e
  have h1 : (∫⁻ (w : CantorSeq), ∑' (n : ℕ), e (cantorPrefix w n) ∂P) =
      ∑' (n : ℕ), ∑ x ∈ levelFinset n, cantorMass P x * e x := by
    have ht := exp_tonelli_sum P (fun _ x => e x)
    rw [ht]
    congr 1
    ext n
    have h_level := exp_level_integral P n
      (fun x => (h x - condProb (cantorMass P) x false) ^ 2)
    exact h_level
  have h2 : (∑' x : BitString, cantorMass P x * e x) =
      ∑' n : ℕ, ∑ x ∈ levelFinset n, cantorMass P x * e x := by
    exact exp_tonelli_sum_reindex (fun x => cantorMass P x * e x)
  constructor
  · rw [h1, ←h2]
  · rw [h2]

end Kolmogorov.MDLPrediction
