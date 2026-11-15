/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Realization
import KolmogorovMathlib.RandomStrings.TTMeet2014.Approximation
import KolmogorovMathlib.RandomStrings.TTMeet2014.Posner
import KolmogorovMathlib.RandomStrings.TTMeet2014.ParityExample
import KolmogorovMathlib.RandomStrings.PrefixForm
import KolmogorovMathlib.RandomStrings.Effective

/-!
# The boundary between the Mathlib-only layer and the library

The modules imported first depend on Mathlib only.  `Adaptive`, `OptimalBridge` and `Main` import
this module, and with it the library API they use: `prefixRandom`, `PolyTimeOracle`, `EXPSPACE` and
the AFG theorem from `PrefixForm`; the clocked machines and their primitive recursive evaluation
from `Effective`; `KPPlain`, `IsOptimalPrefixConditional`, `IsEntropyFun` and
`exists_isOptimalPrefixConditional_min_toNat` through `PrefixForm`.

This module has no declarations: it only fixes the imports at the boundary (see
`docs/random_strings_tt_meet_2014.md`, section 6).
-/
