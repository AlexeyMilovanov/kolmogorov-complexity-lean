/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicStatistics.FiniteDistribution
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelCover
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2CoarseOutcome
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Ordering
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendSource
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2WaitTest
import KolmogorovMathlib.Prefix.ExactBudget
import KolmogorovMathlib.Restricted.FamilyCurve.BadSets
import KolmogorovMathlib.Restricted.FamilyCurve.GoodSets

/-!
# Modules outside the main development line

The modules collected here are not used by anything else in the library: they
are alternative developments, spare interfaces and side results that would
otherwise be maximal build roots of their own.  Importing them from the
aggregate root keeps the library a single build root, so that one `lake build`
covers every module and the co-import smoke test sees the whole tree at once.
-/
