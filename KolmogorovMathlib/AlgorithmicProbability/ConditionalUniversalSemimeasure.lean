/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding

/-!
# Conditional Universal Lower-Semicomputable Semimeasures

This module formulates conditional universal semimeasures and the conditional
coding theorem, establishing the equivalence `K(x | z) = -log m(x | z) + O(1)`
in the project's multiplicative `complexityWeight` / domination style.
-/

namespace Kolmogorov

open scoped ENNReal

/-- A conditional universal semimeasure dominates every lower-semicomputable
conditional semimeasure by a positive multiplicative constant. -/
def IsConditionalUniversalSemimeasure (m : BitString → BitString → ℝ≥0∞) : Prop :=
  IsConditionalSemimeasure m ∧ IsLSC m ∧
  ∀ m', IsConditionalSemimeasure m' → IsLSC m' →
    ∃ c : ℝ≥0∞, 0 < c ∧ Dominates m m' c

/-- The prefix complexity weight `2^{-KP_U(x|z)}`. -/
noncomputable def conditionalPrefixComplexityWeight (U : Map) (x z : BitString) : ℝ≥0∞ :=
  complexityWeight (KP U x z)

/-- The conditional coding theorem / equivalence: a conditional universal semimeasure `m`
and the optimal prefix-complexity weight dominate each other up to multiplicative constants.
This is the `complexityWeight` form of `K(x | z) = -log m(x | z) + O(1)`. -/
theorem conditional_coding_equivalence (U : Map) (hU : IsOptimalPrefixConditional U)
    (m : BitString → BitString → ℝ≥0∞) (hm : IsConditionalUniversalSemimeasure m) :
    (∃ c : ℝ≥0∞, 0 < c ∧ Dominates m (conditionalPrefixComplexityWeight U) c) ∧
    (∃ c : ℕ, ∀ x z, (2 : ℝ≥0∞)⁻¹ ^ c * m x z ≤
      conditionalPrefixComplexityWeight U x z) := by
  refine ⟨?_, ?_⟩
  · -- m dominates complexityWeight
    have hU_semi : IsConditionalSemimeasure (aprioriMeasure U) :=
      aprioriMeasure_isConditionalSemimeasure U hU.isPrefixMachine
    have hU_lsc : IsLSC (aprioriMeasure U) :=
      aprioriMeasure_isLSC U hU.isPrefixDecompressor
    obtain ⟨c, hc_pos, hc_dom⟩ := hm.2.2 (aprioriMeasure U) hU_semi hU_lsc
    refine ⟨c, hc_pos, fun x z => ?_⟩
    calc
      c * conditionalPrefixComplexityWeight U x z
          ≤ c * aprioriMeasure U x z := by
            gcongr
            exact complexityWeight_KP_le_aprioriMeasure U x z
      _ ≤ m x z := hc_dom x z
  · -- complexityWeight dominates m
    obtain ⟨M, hM, c₀, hM_bound⟩ :=
      kraftChaitin_realization_bound hm.2.1 0 (fun z => by simpa using hm.1 z)
    obtain ⟨c, hc⟩ := complexityWeight_dominates_of_prefix_realization hU hM hM_bound
    exact ⟨c, hc⟩

end Kolmogorov
