/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Lower.Realizers
import KolmogorovMathlib.PointToSet.BSDimension.Lower.MassDichotomy
import KolmogorovMathlib.PointToSet.BSDimension.Lower.NullCovers
import KolmogorovMathlib.PointToSet.BSDimension.Lower.EffectiveEqSup

/-!
# Positive-average localization and lower BS dimension

This directory carries the lower half of the point-to-set principle for the Barreira–Schmeling
(BS) dimension (Main B): the comparison between the classical lower BS dimension of a set `Z`
of points with positive lower Birkhoff average and its effective, oracle-relative version.
Hypotheses are pointwise positivity of the lower averages, which may be infinite; uniform
positive bounds are used only on the countable exhaustion pieces or on the eventual realizer
tail of a point. Effective statements fix the metric presentation and use an admissible
oracle; the exponent of a witness is an arbitrary nonnegative real.

* `Lower.Realizers`: ideal realizers of Bowen balls and the analytic facts about the lower
  covering masses.
* `Lower.MassDichotomy`: the lower covering mass is countably subadditive and jumps from
  infinity to zero at the dimension, and the dyadic definition is the limit over all radii.
* `Lower.NullCovers`: null covers of a set, and their relation to the classical lower BS
  dimension and to its effective version.
* `Lower.EffectiveEqSup`: the effective lower BS dimension of `Z` equals the supremum of the
  pointwise dimensions of its points.

The results are combined with the upper-dimension modules in `BSDimension.Upper`, which
contain the final statement `bsPointToSet`; the Bowen equations of `BowenEquation` and the
conformal dimension theorem are consequences of that principle.
-/
