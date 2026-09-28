import KolmogorovMathlib.AlgorithmicRandomness.DeficiencyCore
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.ProbabilityBounded
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationBounded
import KolmogorovMathlib.AlgorithmicRandomness.DeficiencyComparison

/-!
# Randomness deficiency: the deficiency group

The randomness deficiency of a sequence, in its two forms, and the comparison between them.
The parts are `DeficiencyCore` (the deficiency of a Martin-Löf test and the existence of a
maximal test), `LowerSemicomputableFun` (lower-semicomputable functions on Cantor space),
`ProbabilityBounded` and `ExpectationBounded` (the two notions of randomness test),
`LSCCharacterizations` (their lower-semicomputable descriptions) and `DeficiencyComparison`
(the two deficiencies agree up to a logarithmic correction).
-/
