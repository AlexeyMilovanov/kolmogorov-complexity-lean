import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting.GapBounds
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting.IndexSelector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting.Part02
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

/-!
# Gap counting: the group

A string whose optimality gap is realized has many two-part descriptions.  `GapBounds`
supplies the complexity bounds and the candidate enumeration, `IndexSelector` the properties
of that enumeration and the counting step, and `Part02` the statement
`manyIJDescriptions_of_realizedSetOptimalityGap`.
-/
