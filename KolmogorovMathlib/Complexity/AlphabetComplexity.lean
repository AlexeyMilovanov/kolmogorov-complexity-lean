/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.AlphabetComplexity.QAryDecompressors
import KolmogorovMathlib.Complexity.AlphabetComplexity.AlphabetChangeBound
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.LayeredDecompressors
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import Mathlib.Computability.PartrecCode

/-!
# Complexity over other description alphabets

What changes when descriptions are written over a `q`-letter alphabet rather than over bits.
`QAryDecompressors` proves the exact four-letter case (SUV Exercise 4) and
`AlphabetChangeBound` the general statement (SUV Exercise 5): rescaled by `log₂ q`, the
`q`-ary complexity agrees with the binary one up to a constant.
-/
