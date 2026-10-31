/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Distortion.DistortionModuli
import KolmogorovMathlib.PointToSet.Conformal.Distortion.PointwiseDimension

/-!
# Distortion, orbit scales and pointwise conformal dimensions

This directory contains the dynamical estimates for uniformly conformal systems that reduce the
conformal dimension theorem (Main E) to the point-to-set principles. It relates the radii of
Bowen balls to the Birkhoff sums of the potential, so that the static point dimension of a point
and its Barreira–Schmeling dimension agree on the conformal locus.

* `Distortion.DistortionModuli`: distortion moduli and orbit scales. The distance estimate for
  the Birkhoff sum `Sₙu` uses the Bowen ball `Bₙ₊₁`, which observes the endpoint at time `n`;
  local distortion and tempered contraction each use a positive half-error slack, and potential
  variation is compared with ratio distortion with a factor two.
* `Distortion.PointwiseDimension`: the pointwise comparison of static and Barreira–Schmeling
  dimensions. Neither the sampling of scales nor the orbit denominator estimates assumes
  monotonicity of the sampled scales.

These comparisons are used by `Conformal.TheoremE` together with `Conformal.Classical`.
-/
