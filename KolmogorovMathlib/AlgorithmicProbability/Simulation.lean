/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Domination

/-!
# Semimeasure Domination Under Program Simulation

This module proves the *semimeasure-side* analogue of the invariance theorem: if
one map `N` can be **simulated** by another map `M` through an injective,
length-bounded program translation `t`, then the a priori semimeasure of `M`
multiplicatively dominates that of `N`.

Concretely, suppose there is an injection `t : BitString → BitString` on programs
with a uniform length overhead `|t p| ≤ |p| + c`, such that whenever `N`'s program
`p` produces `x` from `y`, the translated program `t p` produces the *same* output
`x` from `y` on `M`. Then

```
2^{-c} · m_N(x | y) ≤ m_M(x | y)   for all x, y,
```

i.e. `Dominates (aprioriMeasure M) (aprioriMeasure N) (2^{-c})`.

The proof is a reindexing of the defining `tsum`: each program `p` of `N` is sent
to `t p`, its weight `2^{-|p|}` shrinks by at most `2^{-c}` (length overhead), and
injectivity guarantees the `M`-side terms are not double-counted. We use
`Summable.tsum_le_tsum_of_inj` for the reindex; `ENNReal` is unconditionally
summable, so no summability side goals survive.

Everything stays in `ℝ≥0∞` with multiplicative (`≤×`) constants — no logarithms,
no equality, and no claim of optimality. The translation `t` is an explicit
hypothesis: this is **not** derived from `KP`-invariance, which only bounds the
*shortest* program and says nothing about the total program mass.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Weight of a length-bounded translate.** If the translated program `t p` is
no longer than `|p| + c`, its weight is at least `2^{-c}` times the weight of `p`.
A smaller exponent on the base `2⁻¹ ≤ 1` yields a larger value, so the bounded
length overhead controls the weight loss. This is the reusable kernel behind the
domination theorem (compare `complexityWeight_le_of_le` in `Coding`). -/
theorem progWeight_translate_ge {t : BitString → BitString} {c : ℕ} {p : BitString}
    (hlen : programLength (t p) ≤ programLength p + c) :
    (2 : ℝ≥0∞)⁻¹ ^ c * progWeight p ≤ progWeight (t p) := by
  rw [progWeight, progWeight, ← pow_add]
  apply pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two)
  omega

/-- **Semimeasure domination from simulation (pointwise form).** If `N`'s programs
inject via `t` into `M`'s programs producing the same output, with uniform length
overhead `≤ c`, then the a priori semimeasure of `M` dominates that of `N` by the
factor `2^{-c}`. -/
theorem aprioriMeasure_dominates_of_simulation
    {M N : Map} (t : BitString → BitString) (ht : Function.Injective t) (c : ℕ)
    (hlen : ∀ p, programLength (t p) ≤ programLength p + c)
    (hsim : ∀ p y x, produces N p y x → produces M (t p) y x)
    (x y : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure N x y ≤ aprioriMeasure M x y := by
  rw [aprioriMeasure, aprioriMeasure, ← ENNReal.tsum_mul_left]
  refine ENNReal.summable.tsum_le_tsum_of_inj t ht (fun _ _ => zero_le) (fun p => ?_)
    ENNReal.summable
  by_cases hp : produces N p y x
  · rw [if_pos hp, if_pos (hsim p y x hp)]
    exact progWeight_translate_ge (hlen p)
  · rw [if_neg hp, mul_zero]
    exact zero_le

/-- **Semimeasure domination from simulation**, packaged in the `Dominates`
vocabulary of `Domination`. The dominating constant is `2^{-c}`, where `c` is the
length overhead of the simulating translation. -/
theorem aprioriMeasure_dominates_of_simulation'
    {M N : Map} (t : BitString → BitString) (ht : Function.Injective t) (c : ℕ)
    (hlen : ∀ p, programLength (t p) ≤ programLength p + c)
    (hsim : ∀ p y x, produces N p y x → produces M (t p) y x) :
    Dominates (aprioriMeasure M) (aprioriMeasure N) ((2 : ℝ≥0∞)⁻¹ ^ c) :=
  fun x y => aprioriMeasure_dominates_of_simulation t ht c hlen hsim x y

/-- **Non-vacuity.** The simulation hypotheses are satisfiable: a map simulates
itself via the identity translation with zero overhead, recovering the reflexive
domination `Dominates (aprioriMeasure N) (aprioriMeasure N) 1`. -/
theorem aprioriMeasure_dominates_self (N : Map) :
    Dominates (aprioriMeasure N) (aprioriMeasure N) 1 := by
  have h := aprioriMeasure_dominates_of_simulation' (M := N) (N := N) id
    Function.injective_id 0 (fun p => by simp) (fun _ _ _ hp => hp)
  simpa using h

/-! ### Packaged program simulations

The raw theorems above take the translation `t`, its injectivity, its length
bound, and its simulation property as four separate hypotheses. In practice these
always travel together, so we bundle them into a single structure
`ProgramSimulation M N c` recording that `N`'s programs translate into `M`'s with
constant overhead `c`. The bundled form is convenient to pass around, compose, and
instantiate, and it immediately yields the semimeasure domination of `M` over `N`.
This is a thin wrapper: it adds no mathematical content beyond the raw theorems. -/

/-- A **program simulation** of `N` by `M` with overhead `c`: an injective,
length-bounded translation of `N`'s programs into `M`'s programs that preserves
the produced output. This is exactly the data consumed by
`aprioriMeasure_dominates_of_simulation`, packaged as a structure. No prefix-machine
hypothesis is required; injectivity and the constant length bound are all that the
domination argument uses. -/
structure ProgramSimulation (M N : Map) (c : ℕ) where
  /-- The translation of `N`'s programs into `M`'s programs. -/
  translate : BitString → BitString
  /-- Distinct `N`-programs translate to distinct `M`-programs (no mass collapse). -/
  injective : Function.Injective translate
  /-- The translation inflates program length by at most the constant `c`. -/
  length_le : ∀ p, programLength (translate p) ≤ programLength p + c
  /-- Translated programs reproduce the same output on `M`. -/
  simulates : ∀ p y x, produces N p y x → produces M (translate p) y x

/-- **Pointwise domination from a packaged simulation.** Specialises
`aprioriMeasure_dominates_of_simulation` to the bundled data. -/
theorem ProgramSimulation.aprioriMeasure_bound
    {M N : Map} {c : ℕ} (h : ProgramSimulation M N c) (x y : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure N x y ≤ aprioriMeasure M x y :=
  aprioriMeasure_dominates_of_simulation h.translate h.injective c h.length_le h.simulates x y

/-- **Domination from a packaged simulation**, in the `Dominates` vocabulary: a
`ProgramSimulation M N c` makes `aprioriMeasure M` dominate `aprioriMeasure N` with
constant `2^{-c}`. -/
theorem ProgramSimulation.aprioriMeasure_dominates
    {M N : Map} {c : ℕ} (h : ProgramSimulation M N c) :
    Dominates (aprioriMeasure M) (aprioriMeasure N) ((2 : ℝ≥0∞)⁻¹ ^ c) :=
  aprioriMeasure_dominates_of_simulation' h.translate h.injective c h.length_le h.simulates

/-- **Reflexivity / non-vacuity.** Every map simulates itself via the identity
translation with zero overhead, witnessing that `ProgramSimulation` is inhabited. -/
def ProgramSimulation.refl (M : Map) : ProgramSimulation M M 0 where
  translate := id
  injective := Function.injective_id
  length_le := fun p => by simp
  simulates := fun _ _ _ hp => hp

/-- Self-domination recovered through the packaged simulation, matching
`aprioriMeasure_dominates_self`. -/
theorem aprioriMeasure_dominates_self_via_programSimulation (M : Map) :
    Dominates (aprioriMeasure M) (aprioriMeasure M) 1 := by
  have h := (ProgramSimulation.refl M).aprioriMeasure_dominates
  simpa using h

end Kolmogorov
