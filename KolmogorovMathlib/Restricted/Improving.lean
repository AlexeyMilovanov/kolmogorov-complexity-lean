import KolmogorovMathlib.Restricted.Improving.RestrictedDescriptions
import KolmogorovMathlib.Restricted.Improving.UniformComputability
import KolmogorovMathlib.Restricted.Improving.UniformComputabilityMarkedCode
import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

/-!
# Restricted Improving Descriptions

This file assembles the improving descriptions theorem (P-IMP) in the restricted
case. It proves both the size half (using `BasicProfile.lean`'s cover shift) and
the complexity half (using `Selection.lean`'s strategy).
-/
