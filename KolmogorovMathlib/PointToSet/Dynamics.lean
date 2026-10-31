/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics.BirkhoffComputability
import KolmogorovMathlib.PointToSet.Dynamics.BowenBalls
import KolmogorovMathlib.PointToSet.Dynamics.PointwiseQuantities
import KolmogorovMathlib.PointToSet.Dynamics.PresentationChangeBS

/-!
# Bowen geometry, finite-scale costs and changes of presentation

This directory provides the dynamical vocabulary shared by the pressure and the
Barreira–Schmeling (BS) parts of the proof. Mathlib's `birkhoffSum` and `Dynamics.dynEntourage`
both observe times `0, ..., n - 1`, so Bowen balls and Birkhoff sums are indexed consistently.
Costs are infima in `EReal` or `ENNReal`, and attainment of an infimum is a separate theorem.

* `Dynamics.BirkhoffComputability`: computable Birkhoff sums and Bowen distances, and
  enumerability of strict comparisons with computable real families.
* `Dynamics.BowenBalls`: Bowen balls, the oscillation of uniformly continuous potentials, the
  finite-scale pressure and BS costs as indexed infima, and their attainment under local bounds.
* `Dynamics.PointwiseQuantities`: the pointwise pressure and the pointwise BS dimension, and
  the independence of the pointwise pressure of the chosen presentation.
* `Dynamics.PresentationChangeBS`: the same independence for the pointwise BS dimensions.

The pointwise quantities are defined here, rather than in the pressure and BS directories,
because the invariance of the effective dimensions under a change of presentation is needed
before those directories. These pointwise quantities are what the suprema over a set `Z` in
the point-to-set principles consist of; they are compared with the topological pressure
(`Pressure.Lower`, `Pressure.Upper`) and with the BS dimension (`BSDimension.Lower`,
`BSDimension.Upper`).
-/
