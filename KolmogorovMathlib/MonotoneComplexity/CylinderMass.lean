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
  simp only [cantorCylinder, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
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
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hb; exact hb hi
    · intro hb h; rw [hb]
  have hmeas : ∀ i ∈ Finset.range x.length,
      MeasurableSet {b | ∀ (h : i < x.length), b = x[i]'h} := by
    intro i hi
    rw [H2 i (Finset.mem_range.mp hi)]
    exact measurableSet_singleton _
  rw [Measure.infinitePi_pi _ hmeas]
  have len : ∏ i ∈ Finset.range x.length, (2⁻¹ : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ x.length := by
    rw [Finset.prod_const, Finset.card_range]
  rw [← len]
  apply Finset.prod_congr rfl
  intro i hi
  rw [H2 i (Finset.mem_range.mp hi)]
  have hhalf : ((1/2 : NNReal) : ℝ≥0∞) = 2⁻¹ := by
    rw [show ((1/2 : NNReal) : ℝ≥0∞) = ((1 : ℝ≥0∞) / 2) from
      ENNReal.coe_div (by norm_num), div_eq_mul_inv, one_mul]
  cases hx_eq : x[i]'(Finset.mem_range.mp hi)
  · have hcoe : unitInterval.toNNReal
        (unitInterval.symm ⟨(1/2 : NNReal), by norm_num, by norm_num⟩) = 1/2 := by
      ext
      rw [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      norm_num
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
        (measurableSet_singleton _) (by simp) rfl, hcoe, hhalf]
  · have hcoe : unitInterval.toNNReal
        ⟨(1/2 : NNReal), by norm_num, by norm_num⟩ = 1/2 := rfl
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
        (measurableSet_singleton _) rfl (by simp), hcoe, hhalf]

end Kolmogorov
