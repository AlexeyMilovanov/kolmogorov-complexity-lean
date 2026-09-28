import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Budget
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.Core
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Hereditary.MainTheorem
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchLemma
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary

/-!
# Public hereditary-theorem assembly

The constructive pieces of the source's `G → L → M → M₁ → F` argument live in
`HereditaryLift`, `LchLemma`, and `FamilyStep`.  This worker contains only
the unchanged public endpoint while the remaining quantitative assembly is
open.

In particular, we deliberately do not introduce abstract plain-to-total
upgrades or unconditional `A₁ → M₁` bounds here.  Such statements are false
without the partition, descent, membership, and intersection-size hypotheses
that constitute the proof of the theorem.
-/
