import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Reduction
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic

/-!
# Strong sufficient statistics

The total-complexity conclusion of VS40 Theorem `thm:step-wise`.  If a total program `p` maps `x` to
the canonical code
of `A`, and `B` is another sufficient statistic for `x`, the source considers

`D = {x' in B | p(x') = [A]}`.

The elementary set-theoretic and witness-extraction facts, the executable
finite filter, and its two conditional-complexity bounds are proved below.
The cardinality stage uses exact plain two-stage coding.  The final heavy-fibre
stage constructs an explicit total selector, proves its evaluation on a
fixed-width heavy-output index, and transfers it to an optimal total machine.
-/
