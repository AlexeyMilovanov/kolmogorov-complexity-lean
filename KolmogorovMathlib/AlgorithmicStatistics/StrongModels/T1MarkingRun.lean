import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun.AvoidingSet
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingCount
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector

/-!
# The marking run of Theorem T1: the group

The chronological marking construction used to separate the plain and the strong description
profile.  `T1MarkingStreams` supplies the four enumerations that are marked, `T1MarkingCount`
counts the marks, `T1SparseSelector` selects an unmarked block, `T1MarkingRun.Part01` turns
the whole thing into one event stream, and `T1MarkingRun.AvoidingSet` states what it produces:
a set of `2 ^ (k - epsilon)` strings avoiding every mark.
-/
