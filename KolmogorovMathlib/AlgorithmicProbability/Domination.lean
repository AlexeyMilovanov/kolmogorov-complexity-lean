/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Mixture
import KolmogorovMathlib.AlgorithmicProbability.Coding

/-!
# Multiplicative Domination and Universality

A *universal* semimeasure is one that **dominates** an entire countable family of
semimeasures: each member, scaled by a positive constant, sits below it. This
module isolates the purely order-theoretic notion of multiplicative domination,
before any computability or coding-theorem equality enters the picture.

For `μ, ν : BitString → BitString → ℝ≥0∞` and a constant `c : ℝ≥0∞`, we write
`Dominates μ ν c` for the pointwise bound `c · ν x y ≤ μ x y`. This is the
standard `≤×` form: an **inequality**, never an equality, and never a logarithm.

The results are:

* `Dominates.refl`, `Dominates.trans`, `Dominates.mono_const` — the order
  algebra of domination (reflexive, composable, constant-weakenable);
* `mixture_dominates_component` — a mixture dominates each component with that
  component's own weight (a repackaging of `weight_mul_le_mixture`);
* `IsUniversalFor` / `mixture_isUniversalFor` — universality packaged as
  "conditional semimeasure + dominates every member by a positive constant",
  established for a subnormalized mixture with strictly positive weights;
* `mixture_aprioriMeasure_dominates_complexityWeight` — the multiplicative
  coding payoff `w i · 2^{-KP_{M i}} ≤ mixture`, combining domination with the
  easy coding bound of `Coding`.

The family is kept *abstract* (`μ : ℕ → …`): enumerating semimeasures is a
computability obligation for a much later slot, so no existence of a universal
semimeasure over *all* lower-semicomputable semimeasures is claimed here.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Multiplicative domination.** `μ` dominates `ν` with constant `c` when, for
every context `y` and output `x`, the scaled value `c · ν x y` lies below
`μ x y`. The standard `≤×` form behind universal semimeasures. -/
def Dominates (μ ν : BitString → BitString → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  ∀ x y, c * ν x y ≤ μ x y

/-- **Reflexivity.** Every function dominates itself with constant `1`. -/
theorem Dominates.refl (μ : BitString → BitString → ℝ≥0∞) :
    Dominates μ μ 1 := fun x y => by rw [one_mul]

/-- **Constant weakening.** A domination by `c` weakens to any smaller constant
`d ≤ c`. -/
theorem Dominates.mono_const {μ ν : BitString → BitString → ℝ≥0∞}
    {c d : ℝ≥0∞} (hcd : d ≤ c) (h : Dominates μ ν c) :
    Dominates μ ν d := fun x y =>
  le_trans (by gcongr) (h x y)

/-- **Transitivity.** Dominations compose, multiplying their constants:
`μ ≽_c ν` and `ν ≽_d ρ` give `μ ≽_{c·d} ρ`. -/
theorem Dominates.trans {μ ν ρ : BitString → BitString → ℝ≥0∞}
    {c d : ℝ≥0∞} (hμν : Dominates μ ν c) (hνρ : Dominates ν ρ d) :
    Dominates μ ρ (c * d) := fun x y =>
  calc
    (c * d) * ρ x y = c * (d * ρ x y) := by rw [mul_assoc]
    _ ≤ c * ν x y := by gcongr; exact hνρ x y
    _ ≤ μ x y := hμν x y

/-- **A mixture dominates each component** with that component's own weight. This
is `weight_mul_le_mixture` recast in the `Dominates` vocabulary, so downstream
files never touch the raw `tsum` index again. -/
theorem mixture_dominates_component (w : ℕ → ℝ≥0∞)
    (μ : ℕ → BitString → BitString → ℝ≥0∞) (i : ℕ) :
    Dominates (mixture w μ) (μ i) (w i) :=
  fun x y => weight_mul_le_mixture w μ i x y

/-- **Universality of `ν` for a countable family `μ`.** `ν` is a conditional
semimeasure and dominates every member of the family by a strictly positive
constant. The constant is allowed to depend on the index `i`. -/
def IsUniversalFor (ν : BitString → BitString → ℝ≥0∞)
    (μ : ℕ → BitString → BitString → ℝ≥0∞) : Prop :=
  IsConditionalSemimeasure ν ∧ ∀ i, ∃ c : ℝ≥0∞, 0 < c ∧ Dominates ν (μ i) c

/-- **A subnormalized mixture with strictly positive weights is universal.** If
`∑_i w i ≤ 1`, every weight is strictly positive, and every component is a
conditional semimeasure, then the mixture is universal for the family: it is a
conditional semimeasure (by `mixture_isConditionalSemimeasure`) and dominates
each component `μ i` by its weight `w i > 0`. -/
theorem mixture_isUniversalFor (w : ℕ → ℝ≥0∞)
    (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (hw_sum : (∑' i, w i) ≤ 1) (hw_pos : ∀ i, 0 < w i)
    (hμ : ∀ i, IsConditionalSemimeasure (μ i)) :
    IsUniversalFor (mixture w μ) μ :=
  ⟨mixture_isConditionalSemimeasure w μ hw_sum hμ,
   fun i => ⟨w i, hw_pos i, mixture_dominates_component w μ i⟩⟩

/-- **Multiplicative coding payoff.** A mixture of prefix-machine a priori
semimeasures dominates each component machine's complexity weight `2^{-KP}`,
scaled by that component's weight:
`w i · 2^{-KP_{M i}(x | y)} ≤ mixture w (m_{M ·}) x y`.

This chains the easy coding bound `complexityWeight_KP_le_aprioriMeasure` with
mixture domination `weight_mul_le_mixture`. It is the `≤×` form of the coding
theorem: an inequality, with no logarithm and no equality claim. -/
theorem mixture_aprioriMeasure_dominates_complexityWeight
    (w : ℕ → ℝ≥0∞) (M : ℕ → Map) (i : ℕ) (x y : BitString) :
    w i * complexityWeight (KP (M i) x y)
      ≤ mixture w (fun j => aprioriMeasure (M j)) x y :=
  calc
    w i * complexityWeight (KP (M i) x y)
        ≤ w i * aprioriMeasure (M i) x y := by
          gcongr; exact complexityWeight_KP_le_aprioriMeasure (M i) x y
    _ ≤ mixture w (fun j => aprioriMeasure (M j)) x y :=
        weight_mul_le_mixture w (fun j => aprioriMeasure (M j)) i x y

end Kolmogorov
