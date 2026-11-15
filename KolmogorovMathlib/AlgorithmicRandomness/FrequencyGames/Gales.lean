/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Gales.GalesAndNullSets
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Gales.LowerSemicomputableGales
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Gales.EffectiveDimensionViaGales

/-!
# Martingales and effective dimension (SUV Section 9.10, pp. 284-287)

An `α`-gale is the capital of a gambler taxed by the factor `2^{α-1}` after each game:
`2^α m(x) = m(x0) + m(x1)`.  The classical notions `IsAlphaNull`, `hausdorffDim` and the effective
notions `IsEffectiveAlphaNull`, `effectiveHausdorffDim` are those of the library (Section 5.8).

The correspondence is asymmetric in the effective case: an effective `α`-null set gives a lower
semicomputable `α`-gale (Theorem 185), but a lower semicomputable `α`-gale only gives effective
`β`-nullity for `β > α` (Theorem 186).

In Theorem 187 the infimum runs over all computable `α > 0`, including `α > 1`, although the book
introduces gales for `α ∈ (0, 1]`.  This is needed: for `A = Ω` no `α ≤ 1` qualifies, because of
Theorem 180, while the dimension is `1`.
-/
