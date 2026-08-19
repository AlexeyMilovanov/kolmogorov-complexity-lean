import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Properties

/-!
# Optimality Deficiency and Randomness Optimality (P-RO)

This module relates randomness deficiency to optimality deficiency.
In particular, it proves that randomness deficiency is bounded by optimality
deficiency up to a constant (P-RO: `d(x | P) ≤ δ(x,P) + O(1)`).
-/

namespace Kolmogorov

open scoped ENNReal

/-- Multiplicative addition for `complexityWeight` on `ENat`.
Turns an additive bound `a + b` inside `complexityWeight` into a multiplicative
bound `complexityWeight a * complexityWeight b`. -/
theorem complexityWeight_add (a b : ENat) :
    complexityWeight (a + b) = complexityWeight a * complexityWeight b := by
  induction a using ENat.recTopCoe with
  | top =>
      rw [top_add, complexityWeight_top, zero_mul]
  | coe k =>
      induction b using ENat.recTopCoe with
      | top =>
          rw [add_top, complexityWeight_top, mul_zero]
      | coe m =>
          rw [← Nat.cast_add, complexityWeight_coe, complexityWeight_coe, complexityWeight_coe,
               pow_add]

/-- Randomness deficiency is bounded by optimality deficiency up to a constant:
`d(x | P) ≤ δ(x,P) + c`.
Multiplicatively, if `2^{-KP(x)} ≤ 2^beta * 2^{-KP(P)} * P(x)`,
then `2^{-KP(x | P)} ≤ 2^{beta + c} * P(x)`. -/
theorem randomness_optimality (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ P : CodedFiniteDistribution, ∀ x : BitString, ∀ beta : ℕ,
      OptimalityDeficiencyLe U P x beta →
      CodedFiniteDistribution.DeficiencyLe U P x (beta + c) := by
  obtain ⟨c_upper, h_upper⟩ := KPPair_chain_upper_weak U hU
  obtain ⟨c_right, h_right⟩ := KPPlain_right_le_KPPair U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  use c_upper + c_right
  intro P x beta h_opt
  unfold CodedFiniteDistribution.DeficiencyLe
  unfold OptimalityDeficiencyLe at h_opt
  -- We want to prove `CW(x|P) ≤ 2^{beta+c} * P(x)`
  by_cases h_xP : KP U x P.code = ⊤
  · rw [h_xP, complexityWeight_top]
    exact zero_le
  -- The upper bound on `KPPlain U x` via the pair `(P.code, x)`.
  -- Note that `pairCode P.code x` has `P.code` on the left and `x` on the right.
  have h1 : KPPlain U x ≤ KPPlain U P.code + KP U x P.code + (c_upper + c_right : ℕ) := by
    calc
      KPPlain U x ≤ KPPair U P.code x + (c_right : ENat) := h_right P.code x
      _ ≤ KPPlain U P.code + KP U x P.code + (c_upper : ENat) + (c_right : ENat) := by
        gcongr
        exact h_upper P.code x
      _ = KPPlain U P.code + KP U x P.code + (c_upper + c_right : ℕ) := by
        push_cast
        abel
  have h2 : complexityWeight (KPPlain U P.code + KP U x P.code + (c_upper + c_right : ℕ)) ≤
      complexityWeight (KPPlain U x) :=
    complexityWeight_le_of_le h1
  rw [complexityWeight_add_nat, complexityWeight_add] at h2
  -- Now we know `CW(P) * CW(x|P) * 2^{-c} ≤ CW(x) ≤ 2^beta * CW(P) * P(x)`
  have h3 : complexityWeight (KPPlain U P.code) * complexityWeight (KP U x P.code) * (2 : ℝ≥0∞)⁻¹ ^
      (c_upper + c_right) ≤
      (2 : ℝ≥0∞) ^ beta * (complexityWeight (KPPlain U P.code) * P.mass x) :=
    le_trans h2 h_opt
  -- `P.code` has finite plain complexity.
  have h_P_ne_top : KPPlain U P.code ≠ ⊤ := by
    intro h_top
    have h_bound := h_len P.code
    rw [h_top] at h_bound
    exact WithTop.top_le_iff.mp h_bound |> ENat.coe_ne_top _
  have h_CW_P_pos : 0 < complexityWeight (KPPlain U P.code) :=
    (complexityWeight_pos_iff _).mpr h_P_ne_top
  -- We can now divide both sides by `CW(P)`.
  have h4 : complexityWeight (KP U x P.code) * (2 : ℝ≥0∞)⁻¹ ^ (c_upper + c_right) ≤ (2 : ℝ≥0∞) ^
      beta * P.mass x := by
    -- `CW(P) * (CW(x|P) * 2^{-c}) ≤ CW(P) * (2^beta * P(x))`
    have h3_rewrite : complexityWeight (KPPlain U P.code) *
        (complexityWeight (KP U x P.code) * (2 : ℝ≥0∞)⁻¹ ^ (c_upper + c_right)) ≤
        complexityWeight (KPPlain U P.code) * ((2 : ℝ≥0∞) ^ beta * P.mass x) := by
      calc
        complexityWeight (KPPlain U P.code) *
            (complexityWeight (KP U x P.code) * (2 : ℝ≥0∞)⁻¹ ^ (c_upper + c_right))
            = complexityWeight (KPPlain U P.code) * complexityWeight (KP U x P.code) * (2 : ℝ≥0∞)⁻¹
                ^ (c_upper + c_right) := by rw [mul_assoc]
        _ ≤ (2 : ℝ≥0∞) ^ beta * (complexityWeight (KPPlain U P.code) * P.mass x) := h3
        _ = complexityWeight (KPPlain U P.code) * ((2 : ℝ≥0∞) ^ beta * P.mass x) := by ring
    exact (ENNReal.mul_le_mul_iff_right (ne_of_gt h_CW_P_pos)
      (complexityWeight_ne_top _)).mp h3_rewrite
  -- Multiply by `2^c`.
  calc
    complexityWeight (KP U x P.code)
        = complexityWeight (KP U x P.code) * (2 : ℝ≥0∞)⁻¹ ^ (c_upper + c_right) * (2 : ℝ≥0∞) ^
            (c_upper + c_right) := by
          rw [mul_assoc, ← ENNReal.inv_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
               mul_one]
    _ ≤ ((2 : ℝ≥0∞) ^ beta * P.mass x) * (2 : ℝ≥0∞) ^ (c_upper + c_right) := by
          gcongr
    _ = (2 : ℝ≥0∞) ^ (beta + (c_upper + c_right)) * P.mass x := by
          rw [pow_add]
          ring

/-- The converse deficiency bridge: if `d(x|P) ≤ beta`, then `δ(x,P) ≤ beta + O(log |P|)`.
This explicitly accounts for the information term by absorbing the complexity of `P`. -/
theorem optimalityDeficiency_of_randomnessDeficiency (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (x : BitString) (alpha beta : ℕ),
      P.complexity U ≤ (alpha : ENat) →
      CodedFiniteDistribution.DeficiencyLe U P x beta →
      OptimalityDeficiencyLe U P x (beta + alpha + c) := by
  obtain ⟨c1, hc1⟩ := KP_le_KPPlain U hU
  use c1
  intro P x alpha beta h_alpha hdef
  unfold CodedFiniteDistribution.DeficiencyLe at hdef
  unfold OptimalityDeficiencyLe
  have h1 : KP U x P.code ≤ KPPlain U x + (c1 : ENat) := hc1 x P.code
  have h2 : complexityWeight (KPPlain U x + (c1 : ENat)) ≤ complexityWeight (KP U x P.code) :=
    complexityWeight_le_of_le h1
  rw [complexityWeight_add_nat] at h2
  have h3 : complexityWeight (KPPlain U x) ≤ (2 : ℝ≥0∞) ^ (beta + c1) * P.mass x := by
    calc
      complexityWeight (KPPlain U x) = complexityWeight (KPPlain U x) * (2 : ℝ≥0∞)⁻¹ ^ c1 *
          (2 : ℝ≥0∞) ^ c1 := by
        rw [mul_assoc, ← ENNReal.inv_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
             mul_one]
      _ ≤ complexityWeight (KP U x P.code) * (2 : ℝ≥0∞) ^ c1 := by gcongr
      _ ≤ ((2 : ℝ≥0∞) ^ beta * P.mass x) * (2 : ℝ≥0∞) ^ c1 := by gcongr
      _ = (2 : ℝ≥0∞) ^ (beta + c1) * P.mass x := by
        rw [mul_right_comm, ← pow_add]
  have h_alpha_cw : complexityWeight (alpha : ENat) ≤ complexityWeight (P.complexity U) :=
    complexityWeight_le_of_le h_alpha
  have h_one : (1 : ℝ≥0∞) ≤ complexityWeight (P.complexity U) * (2 : ℝ≥0∞) ^ alpha := by
    calc
      1 = (2 : ℝ≥0∞)⁻¹ ^ alpha * (2 : ℝ≥0∞) ^ alpha := by
        rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      _ ≤ complexityWeight (P.complexity U) * (2 : ℝ≥0∞) ^ alpha := by
        have h_def : (2 : ℝ≥0∞)⁻¹ ^ alpha = complexityWeight (alpha : ℕ) := rfl
        rw [h_def]
        gcongr
  calc
    complexityWeight (KPPlain U x) = complexityWeight (KPPlain U x) * 1 := by rw [mul_one]
    _ ≤ ((2 : ℝ≥0∞) ^ (beta + c1) * P.mass x) *
        (complexityWeight (P.complexity U) * (2 : ℝ≥0∞) ^ alpha) := by
      gcongr
    _ = (2 : ℝ≥0∞) ^ (beta + alpha + c1) * (complexityWeight (P.complexity U) * P.mass x) := by
      rw [pow_add, pow_add]
      ring

end Kolmogorov
