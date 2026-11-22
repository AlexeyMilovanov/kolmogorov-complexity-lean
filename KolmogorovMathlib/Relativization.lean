/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Relativization.Definitions
import KolmogorovMathlib.Relativization.Typization
import KolmogorovMathlib.Relativization.CombinatorialEntropy
import KolmogorovMathlib.Relativization.Bunches
import KolmogorovMathlib.Relativization.QuantifierFree
import KolmogorovMathlib.Relativization.Existential
import KolmogorovMathlib.Relativization.Stochastic
import KolmogorovMathlib.Relativization.CommonInformation

/-!
# Stability of properties of Kolmogorov complexity under relativization

This module imports the formalization of An. A. Muchnik and A. E. Romashchenko, *Stability of
properties of Kolmogorov complexity under relativization* (Problems of Information Transmission
46(1), 2010): the definitions, the quantifier-free statements, the typization lemmas, combinatorial
entropy, the bunch covers, the extraction of common information (Theorem 2), the existential
statements (Theorems 4 and 5) and the non-stochastic pairs (Theorem 6). See
`docs/muchnik_romashchenko_2010.md` for the dictionary between the paper and the declarations.
-/
