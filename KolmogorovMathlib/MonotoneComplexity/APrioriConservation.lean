import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.GeneratorComposition
import KolmogorovMathlib.MonotoneComplexity.SemimeasureRealization

/-!
# A priori complexity is not increased by computable stream maps

Computable transformations of infinite sequences can only destroy a priori complexity.
`generatedTreeSemimeasure_le_of_streamLowerGraph` pushes the mass of a generator forward along a
computable stream map, `KA_le_KA_add_logb_of_mass_le_mul` turns a mass inequality with a positive
finite factor into an additive complexity inequality, and `exists_const_KA_le_comp` combines them:
for a computable stream map `f` there is a constant `c` with `KA (f x) ≤ KA x + c` on all
prefixes.
-/

namespace Kolmogorov

/-- Composing a generator with a computable stream map moves mass forward: the mass of `x` is at
most
the mass the composite assigns to any output `y` that `x` forces. -/
lemma generatedTreeSemimeasure_le_of_streamLowerGraph
    (G : ProbabilisticGenerator) {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) {x y : BitString}
    (hxy : streamLowerGraph f x y) :
    generatedTreeSemimeasure G x ≤ generatedTreeSemimeasure (generatorComposition G f hf) y := by
  unfold generatedTreeSemimeasure
  apply MeasureTheory.measure_mono
  intro w hw
  have hw_le : BitStream.finite x ≤ G.output w := hw
  have h_mono : f (BitStream.finite x) ≤ f (G.output w) := hf.1.1 hw_le
  exact le_trans hxy h_mono

/-- A mass inequality with a positive finite factor `c` translates into a complexity inequality with
additive term `log₂ c`. -/
lemma KA_le_KA_add_logb_of_mass_le_mul {x y : BitString} {c : ENNReal}
    (hc_top : c ≠ ⊤) (hc0 : c ≠ 0)
    (h : universalContinuousSemimeasure x
          ≤ c * universalContinuousSemimeasure y) :
    KA y ≤ KA x + Real.logb 2 c.toReal := by
  unfold KA
  have hy_top : universalContinuousSemimeasure y ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top y
  have hx_top : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hmul_top : c * universalContinuousSemimeasure y ≠ ⊤ :=
    ENNReal.mul_ne_top hc_top hy_top
  have h_real := (ENNReal.toReal_le_toReal hx_top hmul_top).mpr h
  rw [ENNReal.toReal_mul] at h_real
  have hx_pos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne' hx_top
  have hc_pos : 0 < c.toReal :=
    ENNReal.toReal_pos hc0 hc_top
  have hy_pos : 0 < (universalContinuousSemimeasure y).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos y).ne' hy_top
  have hlog : Real.logb 2 (universalContinuousSemimeasure x).toReal ≤
      Real.logb 2 (c.toReal * (universalContinuousSemimeasure y).toReal) :=
    (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      hx_pos (mul_pos hc_pos hy_pos)).mpr h_real
  rw [Real.logb_mul hc_pos.ne' hy_pos.ne'] at hlog
  linarith

/-- A computable stream map cannot create a priori complexity: its outputs are at most as complex as
the inputs forcing them, up to a constant. -/
theorem exists_const_KA_le_comp
    {f : BitStream → BitStream} (hf : IsComputableStreamMap f) :
    ∃ c : ℝ, ∀ x y : BitString,
      streamLowerGraph f x y → KA y ≤ KA x + c := by
  let G := Classical.choose (exists_probabilisticGenerator_generatedTreeSemimeasure_eq
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure)
  have hG := Classical.choose_spec (exists_probabilisticGenerator_generatedTreeSemimeasure_eq
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure)
  let H := generatorComposition G f hf
  have hH : IsLowerSemicomputableContinuousSemimeasure (generatedTreeSemimeasure H) :=
    generatorComposition_isLowerSemicomputableContinuousSemimeasure G hf
  obtain ⟨c, hc_top, hc⟩ := universalContinuousSemimeasure_isMaximal _ hH
  refine ⟨Real.logb 2 c.toReal, fun x y hxy => ?_⟩
  have h1 : universalContinuousSemimeasure x ≤ generatedTreeSemimeasure H y := by
    rw [← hG x]
    exact generatedTreeSemimeasure_le_of_streamLowerGraph G hf hxy
  have h2 : generatedTreeSemimeasure H y ≤ c * universalContinuousSemimeasure y :=
    hc y
  have h3 : universalContinuousSemimeasure x ≤ c * universalContinuousSemimeasure y :=
    le_trans h1 h2
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at h3
    have hpos := universalContinuousSemimeasure_pos x
    exact (not_le.mpr hpos) h3
  exact KA_le_KA_add_logb_of_mass_le_mul hc_top hc0 h3

end Kolmogorov
