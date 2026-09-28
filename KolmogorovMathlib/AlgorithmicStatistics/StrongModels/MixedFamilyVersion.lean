import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyVersion.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyVersion.Part02
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyVersion.Part03
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MixedFamilyRun
import KolmogorovMathlib.Restricted.FamilyCurve

/-!
# Mixed-family version decoding

The mixed anchored executor rebuilds models in a good family `𝒢`, while its
event stream enumerates forbidden descriptions from a possibly larger family
`ℬ`.  This file gives the corresponding fixed-family version decoder.  Both
families are fixed parameters of the partial-recursive procedure, so no family
data is encoded at run time.
-/
