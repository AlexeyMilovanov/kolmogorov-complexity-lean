import KolmogorovMathlib.Restricted.HammingGap.Part01
import KolmogorovMathlib.Restricted.HammingGap.HelperLemmasHammingVolume
import KolmogorovMathlib.Restricted.Examples.HammingBalls
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The Hamming-ball gap for restricted profiles

This module collects the combinatorial and effective parts of the Hamming-gap construction.
`HammingGap.Part01` builds large sets with bounded intersections with Hamming balls.
`HammingGap.HelperLemmasHammingVolume` makes the construction computable, establishes the
coding and volume estimates, and proves `prop_hamming_gap`.

The result supplies a concrete separation between restricted profile coordinates.
-/
