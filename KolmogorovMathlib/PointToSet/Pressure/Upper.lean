/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Upper.ScaleComparison
import KolmogorovMathlib.PointToSet.Pressure.Upper.UniformNets
import KolmogorovMathlib.PointToSet.Pressure.Upper.EffectiveEqSup
import KolmogorovMathlib.PointToSet.Pressure.Upper.PointToSetPrinciple

/-!
# Uniform nets and upper pressure

This directory proves the upper half of the point-to-set principle for topological pressure
(Main A): the upper pressure of a set `Z` is the minimum over oracles `A` of the supremum over
`x ∈ Z` of the `A`-relative effective pressure (`upperPressure_pointToSet`), and the same for
upper entropy. The upper pressure is the countable modification of the centered upper
capacity; uniform nets describe it discretely. Coding uses only a sufficiently late tail of
each slice, with its existential cutoff fixed before the dynamic order and the ideal index.
Attainment is stated separately from the infimum formulas, including simultaneous attainment.

* `Upper.ScaleComparison`: comparison of the upper pressure across scales.
* `Upper.UniformNets`: uniform nets and the characterization of the upper pressure by them.
* `Upper.EffectiveEqSup`: the effective upper pressure equals the supremum of the pointwise
  pressures.
* `Upper.PointToSetPrinciple`: `upperPressure_pointToSet` and its attainment statements.

Together with `Pressure.Lower` this gives Main A; `PackingEquivalences.Pressure` shows that the
upper pressure can equivalently be defined through packing or separated sets.
-/
