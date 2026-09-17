/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Foundation.FixedPointFree.HighComplexityTask
import KolmogorovMathlib.Foundation.FixedPointFree.ArslanovCompleteness
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Foundation.RSeparability
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import Mathlib.Computability.PartrecCode

/-!
# Fixed-point-free functions and Arslanov's criterion

Group of the material on tasks no fixed-point-free function can solve: `HighComplexityTask`
compares the high-complexity, diagonal and fixed-point-free tasks and shows the halting oracle
solves them, and `ArslanovCompleteness` proves Arslanov's completeness criterion — an enumerable
oracle computing a fixed-point-free function computes the halting problem — through a
parametrised form of Kleene's recursion theorem. The complexity-theoretic input (incompressible
strings, selectors, counting) comes from the modules imported alongside.
-/
