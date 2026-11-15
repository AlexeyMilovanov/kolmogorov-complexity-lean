/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.OracleComputability
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Entropy.Codes.Alphabet
import KolmogorovMathlib.Entropy.Inequalities.Fano
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.MonotoneComplexity.Dimension.Hausdorff
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.Oracle.Universal.Optimal
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.TwoStage

/-!
# The library API used by Chapter 8

The imports of the existing declarations that the complexity modules of `Applications` build on:
plain, prefix and monotone complexity, coding, entropy, effective dimension, and oracle complexity.
The purely combinatorial modules of `Applications` do not import this file.  See
`docs/suv_chapters_08_09.md`.
-/
