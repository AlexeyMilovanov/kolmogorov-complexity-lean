/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.Defs
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.NormalSequences
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.AlignedNormality
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.NormalInBase
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.Champernowne
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.ComputableNormal
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.PredictionAndBets

/-!
# Mises-Church randomness (SUV Section 9.3, pp. 264-267)

A *Church-admissible* selection rule is `S_R` for a decidable `R` (the library's `IsDecidableSet`).
`IsMisesChurchRandomAt p ω` says that every such rule selects from `ω` a finite sequence or one with
limit frequency `p`; `IsMisesChurchRandom` is the case `p = 1/2`.

Besides the headline statements (Theorems 167-171) this module fixes the notions used by the
problems: occurrence frequencies and normality (`IsNormal`, p. 265), aligned blocks, digits of a
real in base `b` (`IsNormalInBase`), Champernowne's sequence, and the bounded-bet game of p. 266.

The sign convention of the bounded-bet game of Theorem 170 is that a positive value is a bet on `0`;
Section 9.12 uses the opposite one (p. 293).  Both are kept, as `betGain` and `betGainOnOne`.
-/
