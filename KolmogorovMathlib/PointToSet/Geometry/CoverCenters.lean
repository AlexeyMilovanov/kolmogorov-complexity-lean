/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.CenterPolicies
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.PressureIndependence
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.BSDimensionIndependence

/-!
# Ambient and covered-set centers

The pressure and Barreira–Schmeling (BS) dimension of a set `Z` are defined with covers whose
centers may lie anywhere in the ambient space. This directory shows that the choice of centers
does not matter: requiring the centers to lie in `Z` itself gives the same quantities. This
lets the point-to-set principles, whose covers are centered at ideal points, be applied to
covers centered in the set.

The ambient cases reuse the covering infima of the main definitions. The self cases restrict
their covering classes, keeping global supremum weights and indexed lower covers with
repetitions. Countable modifications require pieces inside the target and apply the policy
separately to each piece; unrestricted self decompositions are distinct definitions.

* `CoverCenters.CenterPolicies`: ambient and self-centered covering policies, and the
  relocation of a useful Bowen ball to a point of the target at the cost of doubling its radius.
* `CoverCenters.PressureIndependence`: the scale-zero pressure does not depend on the centers.
  Scale limits use a limsup, with convergence stated separately.
* `CoverCenters.BSDimensionIndependence`: the same for BS dimension. BS upper capacities keep
  the finite threshold throughout the comparisons; no raw finite-to-zero conversion is made for
  self-centered pieces.
-/
