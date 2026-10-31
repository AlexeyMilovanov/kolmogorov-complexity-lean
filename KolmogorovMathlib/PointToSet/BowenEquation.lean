/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation.SlopeBounds
import KolmogorovMathlib.PointToSet.BowenEquation.Pointwise
import KolmogorovMathlib.PointToSet.BowenEquation.PointwiseCriticalValue
import KolmogorovMathlib.PointToSet.BowenEquation.SetCriticalValue
import KolmogorovMathlib.PointToSet.BowenEquation.SetRoot
import KolmogorovMathlib.PointToSet.BowenEquation.NonuniformCounterexample
import KolmogorovMathlib.PointToSet.BowenEquation.ConstantExponent

/-!
# Pointwise Bowen equations and corrected set-level roots

This directory proves the Bowen equations (Main C and D) that tie the pressure of the potentials
`-s u` to the Barreira–Schmeling (BS) dimension, using the point-to-set principles for pressure
and for BS dimension. `LimitSide` selects the lower or the upper pressure and dimension. Signed
costs stay in `EReal` and dimensions stay in `ENNReal`; real parameters use `toReal` only under
finite-value hypotheses or the finite-value conclusions stated immediately before a root.

* `BowenEquation.SlopeBounds`: finite-scale Bowen equation and the affine bounds on pressure
  through the zero.
* `BowenEquation.Pointwise`: the same bounds for a point, passed to the scale-zero limit.
* `BowenEquation.PointwiseCriticalValue`: `pointwiseBowenEquation`, the effective BS dimension
  of a point as the critical value of its pressure.
* `BowenEquation.SetCriticalValue`: `setBowenCriticalValue`, the classical BS dimension of a
  set as the critical value of its Bowen pressure, including empty sets and infinite dimensions.
* `BowenEquation.SetRoot`: `setBowenRootOfFiniteBSDimension`, existence and uniqueness of a
  root under nonemptiness, finite BS dimension and a uniform finite upper-average bound.
* `BowenEquation.NonuniformCounterexample`: uniqueness from finite entropy and a uniform
  positive lower average, and `counterexampleNonuniformBowenExistence`, which shows that
  finite entropy alone does not give existence of a root.
* `BowenEquation.ConstantExponent`: the dimensions when both averages equal the same constant.

No pressure is evaluated at an infinite parameter. The conformal dimension theorem
(`Conformal.TheoremE`) transfers these equations to Hausdorff and packing dimension.
-/
