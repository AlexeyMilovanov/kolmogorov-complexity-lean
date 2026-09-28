import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.MonotoneLimits
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.Characterization
import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.LSCConstruction
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Lower-semicomputable functions on Cantor space: the characterisation group

SUV Theorem 40 — lower semicomputability of `f : CantorSeq → ℝ≥0∞` is equivalent to being a
supremum, a monotone limit, or a sum of computable basic functions.  `DyadicEnumeration`
enumerates the superlevel sets of an approximation, `MonotoneLimits` relates the three
presentations to each other, and `Characterization` states the equivalence as
`lowerSemicomputableFun_characterizations`.
-/
