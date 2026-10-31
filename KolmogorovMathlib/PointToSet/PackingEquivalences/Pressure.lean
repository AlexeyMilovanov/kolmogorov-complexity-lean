/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.PackingSeparatedDefs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.ScaleDichotomy
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.ModifiedSeparated
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.Equivalence

/-!
# Packing, separated and covering upper pressures

This directory formalizes the pressure half of Appendix A (nodes 103--111): the upper pressure
defined through covers agrees with the packing and the separated versions, so that it can be
used in either form in the point-to-set principle for upper pressure (`Pressure.Upper`) and in
the packing interpretation of the conformal dimension theorem. Contents are extended
nonnegative sums and critical pressures are signed extended reals. The supremum weights and
covering partition sums of the main definitions are reused throughout. Countable modification
precedes the scale-zero limit. Since supremum weights need not be monotone in the radius,
scale-zero pressures are defined by a continuous-radius limsup, with convergence stated
separately.

* `Pressure.PackingSeparatedDefs`: packing contents and separated pressure.
* `Pressure.ScaleDichotomy`: packing pressure thresholds and comparisons across scales.
* `Pressure.ModifiedSeparated`: the countable separated modification of the upper pressure.
* `Pressure.Equivalence`: the equivalence of the definitions of upper pressure.
-/
