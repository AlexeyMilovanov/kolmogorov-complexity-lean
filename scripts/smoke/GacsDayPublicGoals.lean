import KolmogorovMathlib.MonotoneComplexity.GacsDayTheorems
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame

namespace Kolmogorov

/-- This compile-time sentinel freezes the source-level statement of Theorem 88. -/
example :
    ∃ C : ℕ, ∃ σ : ℕ → ClientStrategy, Computable₂ σ ∧
      ∀ d ≥ 1,
        IsUniformWinningStrategy (C * d) (2 ^ ((C * d) ^ (C * d))) d (σ d) :=
  gacsDay_game

/-- This compile-time sentinel freezes the source-level statement of Theorem 87. -/
example (D : BitStream → BitStream) (hD : IsOptimalMonotoneDecompressor D) :
    (¬ ∃ c : ℝ, ∀ x, ((KMOf D x).toNat : ℝ) ≤ KA x + c) ∧
      ∃ c : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ x : BitString, x.length = n ∧
        KA x + Real.logb 2 (Real.logb 2 n) -
            c * Real.logb 2 (Real.logb 2 (Real.logb 2 n)) ≤
          ((KMOf D x).toNat : ℝ) :=
  gacsDay_separation D hD

/-- A family-game witness is mechanically nonempty. -/
example {kappa alpha beta : ℚ} {epsDepth deltaDepth h b n : ℕ}
    {A : Allocation} {σ : ClientFamilyStrategy}
    (hSpec : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A σ) :
    1 ≤ n :=
  hSpec.nonempty

/-- The public endpoint is fed by one jointly computable construction, not by an
unrelated existential witness at every amplification stage: a single ladder of
schemes, computable in the stage, carries the pinned rung from stage `3` on. -/
example : PinnedGrayUniformInductionStatement :=
  ⟨canonicalPinnedScheme, canonicalPinnedScheme_computable, pinnedChargedRung_canonicalPinned⟩

/-- The game endpoint is discharged by that ladder and nothing else. -/
example : GacsDayGameStatement :=
  gacsDayGameStatement_of_pinnedUniform
    ⟨canonicalPinnedScheme, canonicalPinnedScheme_computable, pinnedChargedRung_canonicalPinned⟩

end Kolmogorov
