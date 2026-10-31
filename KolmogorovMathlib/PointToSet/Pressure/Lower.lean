/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.BowenGeometry
import KolmogorovMathlib.PointToSet.Pressure.Lower.CenteredContents
import KolmogorovMathlib.PointToSet.Pressure.Lower.NullCovers
import KolmogorovMathlib.PointToSet.Pressure.Lower.PointwiseTails
import KolmogorovMathlib.PointToSet.Pressure.Lower.PointToSetPrinciple
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyZeroPotential
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyZeroPotentialVariants
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyCharacterization
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet
import KolmogorovMathlib.PointToSet.Pressure.Lower.SymbolicOrbitComplexity

/-!
# Lower pressure, oracle attainment and entropy

This directory proves the lower half of the point-to-set principle for topological pressure
(Main A): the lower pressure of a set `Z` is the minimum over oracles `A` of the supremum over
`x ∈ Z` of the `A`-relative effective pressure (`lowerPressure_pointToSet`), together with its
specialization to entropy. The definitions come from `Pressure.Defs` and the pointwise
pressure from `Dynamics`. Entropy statements have no admissibility hypothesis on the oracle;
pressure coding statements keep that hypothesis.

* `Lower.BowenGeometry`: Bowen geometry and the scale-zero lower pressure.
* `Lower.CenteredContents`: centered pressure limits, and the failure of monotonicity of
  supremum weights.
* `Lower.NullCovers`: null covers and the lower topological pressure.
* `Lower.PointwiseTails`: monotonicity of the pointwise pressures and the null pressure cover
  given by a strict complexity threshold.
* `Lower.PointToSetPrinciple`: `lowerPressure_pointToSet`, its attainment on an upper cone of
  oracles, and the basic facts about entropies and orbit complexity.
* `Lower.EntropyZeroPotential`, `EntropyZeroPotentialVariants`, `EntropyCharacterization`:
  entropy as zero-potential pressure, its nonnegativity and effective variants, and the
  characterization of entropy by orbit complexity.
* `Lower.EntropyPointToSet`: the effective characterization of entropy for every oracle, and
  the point-to-set principle for lower entropy.
* `Lower.SymbolicOrbitComplexity`: orbit complexity of isometries and of the symbolic shift.

The upper pressure is treated in `Pressure.Upper`, and the pressure equivalences of
`PackingEquivalences.Pressure` and the Bowen equations of `BowenEquation` build on both.
-/
