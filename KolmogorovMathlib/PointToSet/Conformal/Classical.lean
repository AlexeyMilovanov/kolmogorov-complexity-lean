/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical.HausdorffCovers
import KolmogorovMathlib.PointToSet.Conformal.Classical.HausdorffPointToSet
import KolmogorovMathlib.PointToSet.Conformal.Classical.PackingModifiedBox
import KolmogorovMathlib.PointToSet.Conformal.Classical.PackingPointDimension
import KolmogorovMathlib.PointToSet.Conformal.Classical.PointToSetPrinciple

/-!
# Classical Hausdorff and specified-radius packing interfaces

This directory proves the point-to-set principle for the classical dimensions, which is the
classical half of the conformal dimension theorem (Main E). Hausdorff dimension is Mathlib's
metric dimension `_root_.dimH`; packing dimension uses the explicit specified-radius contents
from `Conformal.Defs`, and its identification with the modified upper box dimension assumes only
separability. The oracle statements use one fixed presentation and no admissibility hypothesis.
Oracle minima are expressed by infimum identities and by attainment in every upper cone.

* `Classical.HausdorffCovers`: Hausdorff dimension via covers by ideal dyadic balls.
* `Classical.HausdorffPointToSet`: Hausdorff dimension and the static point dimensions.
* `Classical.PackingModifiedBox`: packing dimension equals modified upper box dimension.
* `Classical.PackingPointDimension`: packing dimension is bounded by the point dimensions.
* `Classical.PointToSetPrinciple`: `classicalPointToSet` and its upper-dimension and cone
  versions, with the achieving oracles for Hausdorff and packing dimension.

`Conformal.TheoremE` combines these formulas with the Barreira–Schmeling point-to-set
principle and the pointwise comparison of `Conformal.Distortion`.
-/
