import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation.Statements
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FullCube
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingPredicates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock

/-!
# Strange strings

This file starts the constructive part of VS40 Section 7.  In particular, it
contains the source-exact coding lemma `l1`.  The theorem `t1` is deliberately
not declared yet: its source statement refers to the two polygons in Figure 6,
and a public Lean declaration must first spell out those polygons and the
marking-game construction that realizes them.
-/
