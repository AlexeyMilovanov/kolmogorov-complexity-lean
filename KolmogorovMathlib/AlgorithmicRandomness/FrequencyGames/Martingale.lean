/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Martingale.Martingales
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Martingale.DoobTheorem

/-!
# Martingales (SUV Section 9.5, pp. 270-275)

A gambler's capital is a function `m` on finite histories.  For a measure `π` the fairness condition
is the book's product form

`m(x) π(x) = m(x0) π(x0) + m(x1) π(x1)`,

which is meaningful whatever the masses are: on a cylinder of `π`-measure `0` it imposes nothing,
and no conditional probability `π(xb)/π(x)` is ever formed.  Three separate notions are kept apart:

* `IsFairCapital π m`: non-negative and fair; the initial capital is free, as in Sections 9.7-9.9;
* `IsMartingale π m`: in addition `m(Λ) = 1`, as in Sections 9.5-9.6;
* `IsSuperfairCapital π m`: the inequality `≥`, the book's supermartingales (p. 278).

On a sequence, `Wins` (unbounded), `StronglyWins` (tends to `+∞`) and `HasFiniteLimit` are three
different things: they are the distinctions of p. 273 and of Doob's theorem.

The uniform case reduces to `m(x) = (m(x0) + m(x1)) / 2` by `isFairCapital_uniform_iff`.
-/
