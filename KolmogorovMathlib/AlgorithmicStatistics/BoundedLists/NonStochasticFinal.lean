import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal.Part01
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal.Part02
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin

/-!
# VS40 Section 4, Milestone B8: non-stochastic objects, final treatment

This file contains the final results of VS40 Section 4 on non-stochastic objects:
- `prop:dilemma`: A dilemma between stochasticity and containing substantial
  information about `Omega_n`.
- `prop:information-rare`: The total mass of objects containing large mutual
  information with a given string is small.
- `prop:nonstochastic-counting-improved`: The improved counting theorem for
  non-stochastic objects with logarithmic slack.
-/
