import KolmogorovMathlib.MonotoneComplexity.StreamTopology
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProductMeasure

/-!
# Cylinder masses

This module provides the mass of a cylinder for the uniform measure, using
`infinitePi_pi`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The cylinder of `x` is the product set fixing the first `|x|` coordinates to the bits of `x`. -/
lemma cantorCylinder_eq_pi (x : BitString) :
    cantorCylinder x = (Finset.range x.length : Set ℕ).pi (fun i =>
    {b | ∀ h : i < x.length,
    b = x[i]'h}) := by
  ext w
  simp only [cantorCylinder, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro hw i hi h
    exact hw i hi
  · intro hw i hi
    exact hw i hi hi

/-- The uniform measure of the cylinder of `x` is `2 ^ (-|x|)`. -/
lemma uniformMeasure_cantorCylinder (x : BitString) :
    uniformMeasure (cantorCylinder x) = (2 : ℝ≥0∞)⁻¹ ^ x.length := by
  rw [cantorCylinder_eq_pi]
  unfold uniformMeasure bernoulliMeasure
  have H2 : ∀ i (hi : i < x.length),
      {b | ∀ (h : i < x.length), b = x[i]'h} = {x[i]'hi} := by
    intro i hi
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hb; exact hb hi
    · intro hb h; rw [hb]
  have hmeas : ∀ i ∈ Finset.range x.length,
      MeasurableSet {b | ∀ (h : i < x.length), b = x[i]'h} := by
    intro i hi
    rw [H2 i (Finset.mem_range.mp hi)]
    exact measurableSet_singleton _
  rw [Measure.infinitePi_pi _ hmeas]
  have H : ∀ i ∈ Finset.range x.length,
      (PMF.toMeasure (PMF.bernoulli (1 / 2) (by norm_num))) {b | ∀ (h : i < x.length),
    b = x[i]'h} = (2 : ℝ≥0∞)⁻¹ :=
    by
    intro i hi
    rw [H2 i (Finset.mem_range.mp hi)]
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    have hx := x[i]'(Finset.mem_range.mp hi)
    revert hx
    intro hx
    cases hx
    · simp [PMF.bernoulli]
    · simp [PMF.bernoulli]
  rw [Finset.prod_congr rfl H]
  simp

end Kolmogorov
