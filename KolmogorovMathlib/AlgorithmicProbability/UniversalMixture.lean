/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Domination
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A Concrete Universal Mixture

The abstract `mixture_isUniversalFor` of `Domination` shows that *any*
subnormalized weight sequence with strictly positive weights yields a mixture
that dominates every member of a countable family of conditional semimeasures.
That theorem is, however, **parametric in the weights**: until a concrete such
sequence is exhibited, its hypotheses could in principle be unsatisfiable.

This module supplies the witness. The **dyadic weights**

```
w i = 2^{-(i+1)}        (i.e. 1/2, 1/4, 1/8, …)
```

are strictly positive, finite, and sum to exactly `1`. Feeding `.le` of that
equality to `mixture_isUniversalFor` makes the universal-mixture theory
**non-vacuous**: there is a genuine universal mixture for every countable family
of conditional semimeasures, and in particular for any countable family of
prefix machines' a priori semimeasures.

Everything stays in `ℝ≥0∞`: only the elementary geometric-series fact
`∑_i 2^{-(i+1)} = 1`, no logarithms, no computability, and no coding-theorem
equality. The weight family is fixed and concrete; the semimeasure family stays
abstract (building it from `KP` would be circular), exactly as in `Domination`.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The **dyadic weight** sequence `w i = 2^{-(i+1)}`, written with the `(2⁻¹)`
base so the elementary `pow` API and the geometric-series lemmas apply. The
exponent is `i + 1` (not `i`) so the weights sum to `1` rather than `2`. -/
noncomputable def dyadicWeight (i : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ (i + 1)

/-- Each dyadic weight is strictly positive (a power of the nonzero base `2⁻¹`). -/
theorem dyadicWeight_pos (i : ℕ) : 0 < dyadicWeight i := by
  rw [dyadicWeight]
  exact ENNReal.pow_pos (pos_iff_ne_zero.mpr inv_two_ne_zero) _

/-- Each dyadic weight is finite (a power of the finite base `2⁻¹`). -/
theorem dyadicWeight_ne_top (i : ℕ) : dyadicWeight i ≠ ⊤ :=
  ENNReal.pow_ne_top inv_two_ne_top

/-- **The dyadic weights sum to one.** This is the geometric series
`∑_i 2^{-(i+1)} = 2⁻¹ · (1 - 2⁻¹)⁻¹ = 2⁻¹ · 2 = 1`, assembled from Mathlib's
`ENNReal.tsum_geometric_add_one`, `ENNReal.one_sub_inv_two`, and
`ENNReal.inv_mul_cancel`. Being an equality, `.le` reuses it as the
subnormalization hypothesis of `mixture_isUniversalFor`. -/
theorem tsum_dyadicWeight : (∑' i, dyadicWeight i) = 1 := by
  simp only [dyadicWeight]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- **A concrete universal mixture for any countable family of conditional
semimeasures.** The dyadic-weighted mixture dominates every component by a
strictly positive constant and is itself a conditional semimeasure. This is
`mixture_isUniversalFor` instantiated at the concrete `dyadicWeight`, discharging
its subnormalization hypothesis with `tsum_dyadicWeight.le` and its positivity
hypothesis with `dyadicWeight_pos`. -/
theorem mixture_dyadicWeight_isUniversalFor
    (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (hμ : ∀ i, IsConditionalSemimeasure (μ i)) :
    IsUniversalFor (mixture dyadicWeight μ) μ :=
  mixture_isUniversalFor dyadicWeight μ tsum_dyadicWeight.le dyadicWeight_pos hμ

/-- **Machine-layer payoff.** For any countable family of prefix machines, the
dyadic-weighted mixture of their a priori semimeasures is universal for that
family. This ties the concrete universal mixture to the prefix-machine theory via
`aprioriMeasure_isConditionalSemimeasure`. -/
theorem mixture_dyadicWeight_aprioriMeasure_isUniversalFor
    (M : ℕ → Map) (hM : ∀ i, IsPrefixMachine (M i)) :
    IsUniversalFor (mixture dyadicWeight (fun i => aprioriMeasure (M i)))
      (fun i => aprioriMeasure (M i)) :=
  mixture_dyadicWeight_isUniversalFor (fun i => aprioriMeasure (M i))
    (fun i => aprioriMeasure_isConditionalSemimeasure (M i) (hM i))

end Kolmogorov
