/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable.Theorem181
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable.RandomnessTests
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable.ComputableMartingales

/-!
# Lower semicomputable martingales (SUV Section 9.7, pp. 277-279)

A function on strings is lower semicomputable when the pairs `⟨r, x⟩` with rational `r < m(x)` form
an enumerable set (p. 277): this is `IsLowerSemicomputableOnStrings`, literally through the
library's `IsRE`.  The functions considered here are `IsFairCapital` and not `IsMartingale`, since
the initial capital is not required to be `1`: Problem 265 explains why it should not be.

The measure `π` is computable throughout.  Positivity of the cylinders is required only where the
statement divides by `π(x)`: in `isLargest_universalRatio` and in Problem 265, whose claim is false
in general without it, because a capital on a null cylinder is unconstrained.
-/
