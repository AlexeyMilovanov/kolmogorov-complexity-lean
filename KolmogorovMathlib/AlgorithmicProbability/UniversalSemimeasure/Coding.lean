/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Enumeration

namespace Kolmogorov

open scoped ENNReal

/-! ### Coding Theorem against Abstract Universal Semimeasure -/

/-- The coding theorem formulated against the abstract universal semimeasure:
the prefix complexity weight `2^{-KP_U(x|empty)}` and the universal semimeasure
`m(x)` dominate each other. -/
theorem universalSemimeasure_equiv_prefixComplexity
    {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m)
    {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c1 c2 : ℝ≥0∞, 0 < c1 ∧ 0 < c2 ∧
      (∀ x, c1 * m x ≤ prefixComplexityWeight U x) ∧
      (∀ x, c2 * prefixComplexityWeight U x ≤ m x) := by
  obtain ⟨c₁, hc₁⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight hm.1 hU
  obtain ⟨c₂, hc₂_pos, hc₂⟩ := prefixComplexityWeight_le_universalSemimeasure hm hU
  refine ⟨(2 : ℝ≥0∞)⁻¹ ^ c₁, c₂, ?_, hc₂_pos, hc₁, hc₂⟩
  exact ENNReal.pow_pos (pos_iff_ne_zero.mpr inv_two_ne_zero) c₁

end Kolmogorov
