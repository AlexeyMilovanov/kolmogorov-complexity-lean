import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.StatePrimrec
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Transitions
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Computable
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Histories
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part03
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams

/-!
# The marking run of Theorem T1: state, transitions, semantics

The effective run that maintains the avoiding set of Theorem T1.  `T1Run.Part01` defines its
state, `T1Run.Transitions` its five branches, `T1Run.StatePrimrec` and `T1Run.Computable`
their effectiveness, and `T1Run.Part03` and `T1Run.Histories` their semantics — what each
event changes and what it leaves alone.  The events it consumes come from `T1MarkingStreams`
and `T1MarkingRun`, and its rebuilds from `T1SparseSelector`.
-/
