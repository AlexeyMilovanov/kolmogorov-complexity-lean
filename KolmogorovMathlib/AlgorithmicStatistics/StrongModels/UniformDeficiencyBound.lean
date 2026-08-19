import KolmogorovMathlib.AlgorithmicStatistics.FiniteSetModel
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic

open ENNReal

namespace Kolmogorov

theorem deficiencyLe_codedUniformOn_finiteSetLogCard
    (U : Map) {B : Finset BitString} (hB : B.Nonempty) {z : BitString}
    (hz : z ∈ B) :
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn B hB) z
      (finiteSetLogCard B) := by
  have hkey : (2 : ℝ≥0∞)⁻¹ ^ (finiteSetLogCard B) *
      complexityWeight (KP U z (codedUniformOn B hB).code) ≤ (B.card : ℝ≥0∞)⁻¹ := by
    have h1 : complexityWeight (KP U z (codedUniformOn B hB).code) ≤ 1 := complexityWeight_le_one _
    have h2 : (2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B ≤ (B.card : ℝ≥0∞)⁻¹ := by
      have hc := finiteSetLogCard_spec B
      have h3 : (B.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ finiteSetLogCard B := by
        exact_mod_cast hc
      have h4 : (2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B = ((2 : ℝ≥0∞) ^ finiteSetLogCard B)⁻¹ :=
        ENNReal.inv_pow.symm
      rw [h4]
      exact ENNReal.inv_le_inv.mpr h3
    calc (2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B * complexityWeight (KP U z (codedUniformOn B hB).code)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B * 1 := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B := mul_one _
      _ ≤ (B.card : ℝ≥0∞)⁻¹ := h2
  have hne0 : ((2 : ℝ≥0∞) ^ finiteSetLogCard B) ≠ 0 := pow_ne_zero (finiteSetLogCard B) two_ne_zero
  have hnetop : ((2 : ℝ≥0∞) ^ finiteSetLogCard B) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hcancel : (2 : ℝ≥0∞) ^ finiteSetLogCard B * (2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B = 1 := by
    rw [ENNReal.inv_pow.symm, ENNReal.mul_inv_cancel hne0 hnetop]
  unfold CodedFiniteDistribution.DeficiencyLe
  rw [codedUniformOn_mass_of_mem B hB z hz]
  calc complexityWeight (KP U z (codedUniformOn B hB).code)
      = (2 : ℝ≥0∞) ^ finiteSetLogCard B *
          ((2 : ℝ≥0∞)⁻¹ ^ finiteSetLogCard B *
            complexityWeight (KP U z (codedUniformOn B hB).code)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ finiteSetLogCard B * (B.card : ℝ≥0∞)⁻¹ := by gcongr

end Kolmogorov
