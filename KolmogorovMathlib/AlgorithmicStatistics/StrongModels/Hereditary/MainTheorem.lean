import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Budget
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Core

/-!
# The hereditary theorem

`thm_hereditary` (VS40 `thm:hereditary`): for an optimal plain conditional machine and an
optimal total conditional machine, `ThmHereditaryStatement` holds — a minimal sufficient
statistic inherits the strong models of the string it describes.  The proof combines the
strong approximation lemma with `normality_of_plain_to_strong_nearby`; its parts are in
`Hereditary/Core`, `Hereditary/Budget`, `HereditaryLift`, `FamilyStep`, `LchLemma` and
`PropMinHereditary`.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- The hereditary theorem: for optimal plain and total conditional machines the statement
`ThmHereditaryStatement` holds, that is, minimal sufficient statistics inherit their strong
models. -/
theorem thm_hereditary
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ThmHereditaryStatement V T := by
  obtain ⟨cKappa, cNormal, hApprox⟩ := lemma_hereditary_strong_approximation V T hV hT
  refine ⟨cKappa, cNormal, ?_⟩
  intro x n A hA epsilon delta hn hStrong hSuff hNormal hMin
  apply normality_of_plain_to_strong_nearby
  intro i j hPlain
  exact hApprox x n A hA epsilon delta hn hStrong hSuff hNormal hMin i j hPlain

end Kolmogorov
