/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.PackingSeparatedDefs
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.RadiusComparison
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.CoveringComparison
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.RawThresholdCounterexample

/-!
# Packing and separated BS dimension comparisons

This directory formalizes the Barreira–Schmeling (BS) half of Appendix A (nodes 112--121): the
upper BS dimension defined through covers agrees with the packing and the separated versions.
The packing interpretation is what links the upper BS dimension to packing dimension in the
conformal dimension theorem (`Conformal.TheoremE`). All masses and dimensions are `ENNReal`,
and critical infima range over nonnegative real exponents. Packing and separated costs reuse
`bsBallWeight` with the chosen radius; covering masses, capacities and positive-average pieces
are those of `BSDimension`.

* `BSDimension.PackingSeparatedDefs`: packing and separated BS contents.
* `BSDimension.RadiusComparison`: comparison of packing and separated sums across radii.
* `BSDimension.CoveringComparison`: comparison of the covering, separated and packing
  thresholds. Finite and zero raw thresholds are identified only on pieces with a uniform
  positive average; general positive-average sets are compared after countable modification,
  before taking scale-zero limits.
* `BSDimension.RawThresholdCounterexample`: an example showing that this localization is
  necessary.
-/
