/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Bounds

/-!
# Countable Mixtures of Conditional Semimeasures

A *universal* semimeasure is built as a weighted countable mixture of a family of
semimeasures, and what makes such a mixture "universal" is **domination**: each
component, scaled by its weight, sits below the mixture. This module isolates the
purely measure-theoretic backbone of that construction, before any computability,
logarithm, or coding-theorem equality enters the picture.

For a weight sequence `w : ℕ → ℝ≥0∞` and a family
`μ : ℕ → BitString → BitString → ℝ≥0∞`, the mixture is

```
mixture w μ x y = ∑_i w i · μ i x y.
```

We prove three facts, all in `ℝ≥0∞`:

* `tsum_mixture_eq` — the total output mass of the mixture factors as
  `∑_i w i · (∑_x μ i x y)` (an equality, just `tsum` rearrangement);
* `weight_mul_le_mixture` — **domination**: `w i · μ i x y ≤ mixture w μ x y`, the
  one-term lower bound that the coding/universality theory stands on;
* `mixture_isConditionalSemimeasure` — if `∑_i w i ≤ 1` and every `μ i` is a
  conditional semimeasure, then so is the mixture.

The family is kept *abstract* (`μ : ℕ → …`): building it from `KP` would be
circular, and the mixture's lower-semicomputability is a strictly later concern.
A closing corollary instantiates the family at a sequence of prefix-machine a
priori semimeasures, connecting the abstract result to the machine layer.

Everything stays an inequality (`≤ 1`); no normalization equality is claimed.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The **weighted countable mixture** of a family of conditional measures. For a
context `y` and output `x`, it sums each component `μ i x y` against its weight
`w i`. -/
noncomputable def mixture (w : ℕ → ℝ≥0∞) (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (x y : BitString) : ℝ≥0∞ :=
  ∑' i, w i * μ i x y

/-- **Total mass of a mixture.** Summing the mixture over all outputs `x` equals
the weighted sum of each component's total mass: `∑_x ∑_i = ∑_i ∑_x` (unconditional
in `ℝ≥0∞`), then `w i` factors out of the inner sum. -/
theorem tsum_mixture_eq (w : ℕ → ℝ≥0∞) (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (y : BitString) :
    (∑' x : BitString, mixture w μ x y) = ∑' i, w i * (∑' x : BitString, μ i x y) := by
  simp only [mixture]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun i => ENNReal.tsum_mul_left

/-- **Domination.** Each weighted component lies below the mixture: it is a single
term of the defining `tsum`. This one-term bound is the measure-theoretic core of
the coding theorem. -/
theorem weight_mul_le_mixture (w : ℕ → ℝ≥0∞) (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (i : ℕ) (x y : BitString) :
    w i * μ i x y ≤ mixture w μ x y :=
  ENNReal.le_tsum i

/-- **A mixture of conditional semimeasures is a conditional semimeasure.** If the
weights are subnormalized (`∑_i w i ≤ 1`) and every component is a conditional
semimeasure, then so is the mixture: each inner total mass is `≤ 1`, so the
weighted total is at most `∑_i w i ≤ 1`. -/
theorem mixture_isConditionalSemimeasure
    (w : ℕ → ℝ≥0∞) (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (hw : (∑' i, w i) ≤ 1) (hμ : ∀ i, IsConditionalSemimeasure (μ i)) :
    IsConditionalSemimeasure (mixture w μ) := by
  intro y
  rw [tsum_mixture_eq]
  calc
    (∑' i, w i * (∑' x : BitString, μ i x y)) ≤ ∑' i, w i * 1 :=
      ENNReal.tsum_le_tsum fun i => by gcongr; exact hμ i y
    _ = ∑' i, w i := by simp
    _ ≤ 1 := hw

/-- **Instantiation at prefix-machine a priori semimeasures.** Mixing a countable
family of prefix machines' a priori semimeasures with subnormalized weights yields
a conditional semimeasure. This connects the abstract mixture to the machine layer
via `aprioriMeasure_isConditionalSemimeasure`. -/
theorem mixture_aprioriMeasure_isConditionalSemimeasure
    (w : ℕ → ℝ≥0∞) (M : ℕ → Map) (hw : (∑' i, w i) ≤ 1)
    (hM : ∀ i, IsPrefixMachine (M i)) :
    IsConditionalSemimeasure (mixture w (fun i => aprioriMeasure (M i))) :=
  mixture_isConditionalSemimeasure w (fun i => aprioriMeasure (M i)) hw
    (fun i => aprioriMeasure_isConditionalSemimeasure (M i) (hM i))

end Kolmogorov
