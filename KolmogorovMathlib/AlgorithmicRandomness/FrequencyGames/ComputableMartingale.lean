/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.RandomnessBasics
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.LogComplexityConstruction
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.MartinLofSeparation
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.MisesChurchSeparation
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.ZerosDominateWin
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.BoundedConditionalComplexity
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.UniversalComplexityBound
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.ConditionalMeasures

/-!
# Computable martingales (SUV Section 9.8, pp. 279-282)

`IsComputablyRandom π ω`: no computable `π`-martingale wins on `ω`, with the initial capital free.
The book assumes `π` computable with `π(Ω_x) > 0` for all `x` (p. 279).  These hypotheses are
separate from the definition and appear where used.  Theorem 182(a) also holds with null cylinders;
its statement here makes that harmless generalization explicit.

`IsComputableOnStrings` and `IsLowerSemicomputableOnStrings` are different notions and no statement
identifies them; the relation between them is Problem 265.
-/
