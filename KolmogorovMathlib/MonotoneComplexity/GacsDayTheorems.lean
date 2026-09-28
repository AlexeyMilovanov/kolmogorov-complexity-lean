import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding
import KolmogorovMathlib.MonotoneComplexity.GacsDayFamilyGame
import KolmogorovMathlib.MonotoneComplexity.GacsDaySeparationReduction
import KolmogorovMathlib.MonotoneComplexity.GacsDayMixture
import KolmogorovMathlib.MonotoneComplexity.GacsDayPinnedEndgame
import KolmogorovMathlib.MonotoneComplexity.GacsDayRequestFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayStaticWin

/-!
# Public Gacs-Day endpoints

This module owns the two source-level conclusions of SUV Theorems 88 and 87.
Supporting modules may evolve underneath it, but these declarations must not be
deleted, renamed, weakened, or replaced by conditional versions.
-/

namespace Kolmogorov

/-- **Theorem 88 (Gács–Day game).** There is a computable family of client strategies,
uniformly winning with linear constants.  The endpoint name of the game half of the
Gács–Day theorem; the proof is the pinned-endgame construction. -/
theorem gacsDay_game : GacsDayGameStatement := gacsDayGameStatement_of_canonicalPinned

/-- **SUV Theorem 87 (Day).** For every optimal monotone decompressor, the gap
`KM(x) - KA(x)` is unbounded and is at least
`log log n - O(log log log n)` for some `n`-bit string at infinitely many
lengths. The exact quantified inequality is frozen in
`GacsDaySeparationStatement`. -/
theorem gacsDay_separation
    (D : BitStream → BitStream)
    (hD : IsOptimalMonotoneDecompressor D) :
    GacsDaySeparationStatement D := by
  apply gacsDaySeparationStatement_of_quantitative D
  obtain ⟨C, σ, hcomp, hwin⟩ :=
    binaryGacsDay_of_gacsDay_sharp gacsDayGameStatement_of_canonicalPinned
  obtain ⟨μ, A, hchild, hroot, hwitness, hmono, hsup, hAcomp⟩ :=
    exists_gacsDayRequestFamily D hD C σ hcomp hwin
  apply gacsDayQuantitative_of_requestFamily D C μ hchild hroot hwitness
  exact gacsDayMixture_isLSC μ ⟨A, hmono, hsup, hAcomp⟩

end Kolmogorov
