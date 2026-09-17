/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.EnumerationTail
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.Position
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal

/-!
# VS40 Section 4: lists of strings of bounded complexity

For a machine `V` and a bound `m`, `completedBoundedOutput c m` is the list of all strings of
plain complexity at most `m`, in the order in which the enumeration produces them.  This
directory develops that list: its stage enumeration and the counter `omegaCount` of its length
(`Basic`, `OmegaCount`), the busy-beaver completion times (`BusyBeaver`), the tail after a given
element (`EnumerationTail`), the equivalence between a high-bit prefix of `Omega_m` and the list
(`OmegaPrefix`), positions inside the list (`Position`), the bridge to the ordinary description
profile (`TailProfile`), the standard blocks of the list (`StandardBlock`), and the
non-stochastic objects it produces (`NonStochastic`).
-/
