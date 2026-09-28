import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.Filtered
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.PlainTotal
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.TotalStrength
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift

/-!
# The partition-intersection step in the hereditary construction

This file implements the `M → M₁` counting and total-selection step from the
proof of VS40 Theorem `thm:hereditary`.  The selector is deliberately total on
every context: its ordinary partition program is run at the fixed empty
context, and all subsequent decoding, filtering, and indexing is computable
post-processing of the varying finite-set context.
-/
