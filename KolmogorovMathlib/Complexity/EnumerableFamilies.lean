/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.EnumerableFamilies.CountingBounds
import KolmogorovMathlib.Complexity.EnumerableFamilies.Enumeration
import KolmogorovMathlib.Complexity.EnumerableFamilies.CalibratedBlocks
import KolmogorovMathlib.Complexity.EnumerableFamilies.CalibratedComplexity
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import Mathlib.Computability.PartrecCode

/-!
# SUV Chapter 1

Book-facing theorems and exercises of Chapter 1 (plain Kolmogorov complexity)
of Shen–Uspensky–Vereshchagin that were not already present in the library.

Conventions.

* `C(x)` is `plainK U x` for an optimal conditional decompressor `U`
  (`isOptimalConditional U`), and `C(n)` for a natural number is `plainKNat U n`.
* `O(1)` error terms are existentially quantified natural constants; `O(log n)`
  terms use `Nat.log 2` or the library slack function `logSlack`.
* The machine-level objects of Theorem 15 are built from the library's
  `Code`-level snapshots (`completedBoundedOutput`, `busyBeaver`,
  `boundedPrograms`, `haltsWithin`), with `IsCodeFor c U` connecting them to `U`.
-/
