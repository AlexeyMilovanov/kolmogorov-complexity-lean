/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Order.NormalizedSlack
import KolmogorovMathlib.PointToSet.Order.AchievingOracles

/-!
# Vanishing coding overhead and attained oracle minima

This directory contains the order-theoretic part of the point-to-set principles: the oracle
infimum in each principle is shown to be attained, and the coding overheads that arise when one
oracle is replaced by a stronger one are shown to vanish in the limit. Signed assertions use
`EReal` and nonnegative assertions use `ENNReal`. Rational thresholds state almost-attainment
without any arithmetic on infinite critical values. Every oracle comparison uses total
characteristic oracles and the same fixed metric presentation.

* `Order.NormalizedSlack`: a fixed or logarithmic coding overhead vanishes after division by
  the time (`order:slack`), and oracle monotonicity of complexity is transferred through the
  finite-scale infima and time limits defining pointwise pressure and BS dimension.
* `Order.AchievingOracles`: a lower bound approached by oracles above a base oracle is attained
  by the join of countably many of them, also simultaneously for all stronger oracles
  (`order:attainment`).

The pressure and BS dimension modules (`Pressure`, `BSDimension`) use these results to turn
the infima over oracles in Main A and Main B into minima attained in every upper cone.
-/
