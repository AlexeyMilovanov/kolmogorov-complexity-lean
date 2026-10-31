/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.DimensionTheorem
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.ActualDiameterBounds
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.ActualDiameterCounterexample

/-!
# Conformal dimension theorem and corrected Bowen consequences

This directory proves the conformal dimension theorem (Main E) and its Bowen-equation
consequences. `dimensionTheorem` identifies Hausdorff dimension with the lower covering
Barreira–Schmeling dimension on the conformal locus, and `dimensionTheorem_upper` and
`dimensionTheorem_packing` identify the specified-radius packing dimension with the modified
upper and the packing Barreira–Schmeling dimension (see `PackingEquivalences.BSDimension`).
`bowenEquation` transfers the pressure cuts, with their
infinite endpoints, and the root characterizations of `BowenEquation` to classical dimension,
keeping the finite-dimension or finite-entropy and uniform-average hypotheses of the corrected
Bowen theorems. The proof compares the classical formulas of `Conformal.Classical` with the
dynamical ones through the pointwise identities of `Conformal.Distortion`.

* `TheoremE.DimensionTheorem`: `dimensionTheorem` and `bowenEquation`.
* `TheoremE.BallComparison`: counterexamples showing that the uncorrected comparisons between
  Bowen balls and metric balls fail, which justify the indexing and the positive slack.
* `TheoremE.FactorialUltrametric`, `FactorialPackingGeometry`, `FactorialBoxBounds`,
  `ActualDiameterBounds`, `ActualDiameterCounterexample`: a compact factorial ultrametric
  product where packing dimension defined by actual diameters differs from the
  specified-radius packing dimension, showing that the specified-radius definition is needed.
-/
