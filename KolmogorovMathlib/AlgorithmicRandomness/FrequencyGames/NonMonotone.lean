/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.KLRules
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MartinLofImpliesStochastic
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.BoundedBetStrategy
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikCoding
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikWitnesses
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikStages
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.MuchnikTheorem
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.ChurchDaleySeparation
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.KLBetting
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.KLTotalMartingales

/-!
# Non-monotonic selection rules (SUV Section 9.12, pp. 290-296)

A Kolmogorov-Loveland rule is a pair `(F, G)` of partial functions on the strings of revealed bits.
`F` says which card to turn over next, `G` whether the card about to be turned over is selected.
The structure `KLRule` carries the book's condition that `F` differs on compatible strings, so no
position is queried twice along a run.  The point of `G`'s signature is that it sees only the
revealed bits *before* the current one, so the decision to select is made before the value is seen.

The semantics is exactly the book's two phases, as in the proof of Theorem 202: `revealed` computes
the sequence of revealed bits, which stops when `F` is undefined, and the output is the selection
`selectedBits (partialRuleSet G)` from it, which stops when `G` is undefined.

Monotone rules are a special case: `KLRule.ofMonotone r` has `F(x) = |x|`, and
`KLRule.output_ofMonotone` identifies its output with `S_r`.  This is Theorem 192(a).
-/
