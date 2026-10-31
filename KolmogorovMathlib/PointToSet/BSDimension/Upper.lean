/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Upper.ScaleLimits
import KolmogorovMathlib.PointToSet.BSDimension.Upper.UniformNets
import KolmogorovMathlib.PointToSet.BSDimension.Upper.OracleAttainment
import KolmogorovMathlib.PointToSet.BSDimension.Upper.PointToSetPrinciple

/-!
# Modified upper BS dimension and the BS point-to-set principles

This directory completes the proof of the point-to-set principle for Barreira–Schmeling (BS)
dimension (Main B, `bsPointToSet` and `bsPointToSet_upper`): for a set `Z` with positive lower
Birkhoff average, the lower and the modified upper BS dimension of `Z` are the minima, over all
oracles, of the supremum of the relative pointwise dimensions over `Z`. Finite and zero capacity
thresholds are compared only after a countable positive-average refinement. The nets used to
code covers reach every positive order, but only their eventual slice masses must be finite.

* `Upper.ScaleLimits`: the upper capacity and its countable modification are monotone and
  antitone in the radius, the dyadic supremum is a limit over all radii, and finite and zero
  thresholds are compared on pieces with a uniform positive lower average.
* `Upper.UniformNets`: every exponent above the modified upper BS dimension admits a uniform net.
* `Upper.OracleAttainment`: an effective net bounds the upper pointwise dimensions of the
  points of `Z`, and oracles attaining the classical dimension exist.
* `Upper.PointToSetPrinciple`: the principle itself, with the minima ranging over all oracles
  and attained in every upper cone of oracles.

The principle is used by `BowenEquation` to turn dimensions into roots of pressure, and by the
conformal dimension theorem through its Hausdorff and packing analogues.
-/
