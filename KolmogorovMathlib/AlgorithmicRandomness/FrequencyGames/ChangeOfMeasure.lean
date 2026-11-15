/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.IndependentTrials
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.SeparatedCriterion
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.VovkDichotomy
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.BookmakerGame
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.FrequencyDeviation
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.VanLambalgen
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.KLRandomness
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.Separations

/-!
# Change in the measure and randomness (SUV Section 9.13, pp. 296-309)

`independentTrials p hp` is the measure of independent trials with success probability `p i` in the
`i`-th trial, of which the library's `bernoulliMeasure` is the constant case.

**Conditional probabilities.**  `condOne μ x` is the library's `condProb (cantorMass μ) x true`,
that is, `μ(x1) / μ(x)`.  When `μ(x) = 0` Lean's value is the junk `0`.  No theorem here depends on
that value: along a Martin-Löf random sequence the masses are positive (`random_prefix_mass_pos`),
and the measure statements hold up to the null set of such prefixes.

**Reuse.**  Theorem 197 is the library's `vovk_merging_summable`, which needs no separation
hypothesis.
-/
