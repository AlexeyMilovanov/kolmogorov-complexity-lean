/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Domination
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.AlgorithmicProbability.UniversalMixture
import KolmogorovMathlib.Prefix.Optimal

/-!
# Universal Lower-Semicomputable Semimeasures: Definitions

This file contains the unary interface and structural predicates for universal
lower-semicomputable semimeasures. Proofs about this interface live in
`UniversalSemimeasure.Basic`.
-/

namespace Kolmogorov

open scoped ENNReal

/-- A unary semimeasure on strings is a function `m : BitString → ℝ≥0∞` whose
total mass is at most `1`. Nonnegativity is built into `ℝ≥0∞`. -/
def IsSemimeasure (m : BitString → ℝ≥0∞) : Prop :=
  (∑' x : BitString, m x) ≤ 1

/-- A lower-semicomputable unary semimeasure is a semimeasure with a uniform
computable monotone dyadic approximation from below. We reuse the existing
conditional `IsLSC` interface with a dummy context. -/
def IsLowerSemicomputableSemimeasure (m : BitString → ℝ≥0∞) : Prop :=
  IsSemimeasure m ∧ IsLSC (fun x _ => m x)

/-- Domination for unary semimeasures: `m₁` dominates `m₂` with multiplicative
constant `c` if `c * m₂ x ≤ m₁ x` for all `x`. -/
def DominatesUnary (m₁ m₂ : BitString → ℝ≥0∞) (c : ℝ≥0∞) : Prop :=
  ∀ x, c * m₂ x ≤ m₁ x

/-- A universal (maximal) lower-semicomputable semimeasure dominates every
lower-semicomputable semimeasure by some positive multiplicative constant. -/
def IsUniversalSemimeasure (m : BitString → ℝ≥0∞) : Prop :=
  IsLowerSemicomputableSemimeasure m ∧
  ∀ m', IsLowerSemicomputableSemimeasure m' →
    ∃ c : ℝ≥0∞, 0 < c ∧ DominatesUnary m m' c

/-- Synonym matching the book terminology: a universal semimeasure is a maximal
lower-semicomputable semimeasure. -/
abbrev IsMaximalLowerSemicomputableSemimeasure (m : BitString → ℝ≥0∞) : Prop :=
  IsUniversalSemimeasure m

/-- The prefix complexity weight `2^{-KP_U(x|[])}`. -/
noncomputable def prefixComplexityWeight (U : Map) (x : BitString) : ℝ≥0∞ :=
  complexityWeight (KP U x [])

/-! ### Unary mixtures -/

/-- Weighted countable mixture of unary semimeasures. -/
noncomputable def unaryMixture (w : ℕ → ℝ≥0∞)
    (μ : ℕ → BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' i, w i * μ i x

/-- Universality for a fixed countable family of unary semimeasures. -/
def IsUniversalForUnary (ν : BitString → ℝ≥0∞)
    (μ : ℕ → BitString → ℝ≥0∞) : Prop :=
  IsSemimeasure ν ∧ ∀ i, ∃ c : ℝ≥0∞, 0 < c ∧ DominatesUnary ν (μ i) c

end Kolmogorov
