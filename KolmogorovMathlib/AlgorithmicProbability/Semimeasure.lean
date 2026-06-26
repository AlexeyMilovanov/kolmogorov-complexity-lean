/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Machine
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Machine-Induced A Priori Semimeasure

This module introduces the (conditional) **a priori semimeasure** induced by a
map `M`. For a context `y`, it assigns to each output `x` the total weight

```
m_M(x | y) = ∑_{p : M(p, y) = x} 2^{-|p|},
```

summing the weight `2^{-|p|}` over every program `p` that produces `x` from `y`.
We work entirely in `ℝ≥0∞` (`ENNReal`): the sum is a `tsum` over all bitstrings,
written with an indicator so that the index set is the total, countable type
`BitString` rather than a subtype. This avoids subtype-index gymnastics and lets
us apply `ENNReal.le_tsum` directly.

The headline result of this slot is the **easy direction** of the coding
relationship: any single program `p` producing `x` contributes its weight, so
its weight is a lower bound on the semimeasure. This holds for *every* map; the
prefix-machine hypothesis is reserved for the (later, harder) normalization
direction `∑_x m_M(x | y) ≤ 1`, which needs the Kraft inequality and is **not**
attempted here.

We deliberately do **not** package the bound as `2^{-KP(x|y)} ≤ m_M(x | y)`:
`KP` lands in `ENat`, and raising `2⁻¹` to an `ENat` exponent needs a custom
`⊤ ↦ 0` convention. The term-level bound below is the clean, reusable core; the
`KP` packaging is a follow-up once such an exponent helper exists.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The **weight** `2^{-|p|}` of a program `p`, as an extended nonnegative real.
We use `(2⁻¹)^|p|` (a `Monoid.npow`) rather than a negative/`zpow` exponent so
that the elementary `pow` API applies. -/
noncomputable def progWeight (p : BitString) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ programLength p

open Classical in
/-- The (conditional) **a priori semimeasure** `m_M(x | y)` induced by a map `M`.
It sums the weight `2^{-|p|}` over every program `p` that produces `x` from `y`,
realized as a `tsum` over all of `BitString` with an indicator summand. -/
noncomputable def aprioriMeasure (M : Map) (x y : BitString) : ℝ≥0∞ :=
  ∑' p : BitString, if produces M p y x then progWeight p else 0

/-! ### Elementary positivity / finiteness of weights -/

/-- The base `2⁻¹` is nonzero in `ℝ≥0∞` (because `2 ≠ ⊤`). -/
theorem inv_two_ne_zero : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by
  simp [ENNReal.inv_eq_zero]

/-- The base `2⁻¹` is finite in `ℝ≥0∞` (because `2 ≠ 0`). -/
theorem inv_two_ne_top : (2 : ℝ≥0∞)⁻¹ ≠ ⊤ := by
  simp [ENNReal.inv_eq_top]

/-- Every program weight is strictly positive. -/
theorem progWeight_pos (p : BitString) : 0 < progWeight p := by
  rw [progWeight]
  exact ENNReal.pow_pos (pos_iff_ne_zero.mpr inv_two_ne_zero) _

/-- Every program weight is finite. -/
theorem progWeight_ne_top (p : BitString) : progWeight p ≠ ⊤ :=
  ENNReal.pow_ne_top inv_two_ne_top

/-! ### The easy coding direction -/

/-- **Easy coding direction.** Any program `p` that produces `x` from `y`
contributes its weight `2^{-|p|}` to the a priori semimeasure, hence that weight
is a lower bound on `m_M(x | y)`. This holds for an arbitrary map `M`; no
prefix-freeness is required. -/
theorem progWeight_le_aprioriMeasure {M : Map} {p x y : BitString}
    (h : produces M p y x) : progWeight p ≤ aprioriMeasure M x y := by
  classical
  rw [aprioriMeasure]
  calc
    progWeight p = (if produces M p y x then progWeight p else 0) := by rw [if_pos h]
    _ ≤ ∑' q : BitString, if produces M q y x then progWeight q else 0 :=
      ENNReal.le_tsum p

/-- If some program produces `x` from `y`, then the a priori semimeasure is
strictly positive. -/
theorem aprioriMeasure_pos_of_produces {M : Map} {p x y : BitString}
    (h : produces M p y x) : 0 < aprioriMeasure M x y :=
  lt_of_lt_of_le (progWeight_pos p) (progWeight_le_aprioriMeasure h)

/-- **Vanishing direction.** If *no* program produces `x` from `y`, then the a
priori semimeasure `m_M(x | y)` is `0`: every indicator summand vanishes. The
contrapositive of `aprioriMeasure_pos_of_produces`, stated as an equality so it
can rewrite directly. -/
theorem aprioriMeasure_eq_zero_of_forall_not_produces {M : Map} {x y : BitString}
    (h : ∀ p, ¬ produces M p y x) : aprioriMeasure M x y = 0 := by
  classical
  rw [aprioriMeasure]
  refine (tsum_congr (fun p => ?_)).trans tsum_zero
  rw [if_neg (h p)]

/-- Support hook for the (future) Kraft / normalization direction: every program
contributing a *nonzero* term to `m_M(x | y)` lies in the halting domain of `M`
at `y`. For a prefix machine this domain is prefix-free, which is the structure
the Kraft inequality will exploit. -/
theorem mem_domainAt_of_produces {M : Map} {p x y : BitString}
    (h : produces M p y x) : p ∈ domainAt M y :=
  produces_mem_domainAt h

end Kolmogorov
