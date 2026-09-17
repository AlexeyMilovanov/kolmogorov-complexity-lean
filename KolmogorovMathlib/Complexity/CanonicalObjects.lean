/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.CanonicalObjects.HubReductions
import KolmogorovMathlib.Complexity.CanonicalObjects.HubEdges
import KolmogorovMathlib.Complexity.CanonicalObjects.PrimitiveReductions
import KolmogorovMathlib.Complexity.CanonicalObjects.HubEquivalence
import KolmogorovMathlib.Complexity.CanonicalObjects.Counting
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.BusyBeaver
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import Mathlib.Computability.PartrecCode

/-!
# The nine canonical objects of level `n`

SUV Theorem 15: nine objects associated with the strings of length `n` — the list of strings
of complexity at most `n`, their number, the busy beaver, the maximal halting time, the list
of halting programs, the halting count, the slowest halting program, the graph of `C`, and the
first incompressible string — all have complexity `n + O(1)` and all determine one another.

`HubReductions` defines the objects and composes the reductions through the hub,
`HubEdges` and `HubEquivalence` supply the individual edges, `PrimitiveReductions` the
effective functions they use, and `Counting` the counting bounds.
-/
