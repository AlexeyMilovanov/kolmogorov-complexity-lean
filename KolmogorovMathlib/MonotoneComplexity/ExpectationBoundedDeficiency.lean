/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationBounded
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

/-!
# Expectation-bounded randomness deficiency of infinite sequences

Shen-Uspensky-Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*,
Section 3.5 (Theorem 42, p. 62) and Problem 185 (p. 182).

The *expectation-bounded randomness deficiency* of an infinite sequence is the
binary logarithm of a maximal expectation-bounded randomness test.  Theorem 42
provides the test; this module names the maximality property and the logarithm,
so that the Chapter 5 clusters (C10 Problems 146-147, C12 Problem 185) refer to
one notion instead of spelling maximality out inline.

These declarations belong beside the expectation-bounded test API of the
randomness layer; this module is their present home.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The binary logarithm of an extended nonnegative real, with the conventions
`log 0 = ⊥` and `log ⊤ = ⊤`.  Used to pass from the multiplicative maximal test
of Theorem 42 to the additive deficiency of SUV §3.5. -/
noncomputable def ennrealLogbTwo (t : ℝ≥0∞) : EReal :=
  if t = 0 then ⊥ else if t = ⊤ then ⊤ else ((Real.logb 2 t.toReal : ℝ) : EReal)

/-- A *maximal* expectation-bounded randomness test with respect to `μ`: the
conclusion of SUV Theorem 42 (§3.5), named so that the expectation-bounded
randomness deficiency `ennrealLogbTwo (u ω)` of an infinite sequence can be
referred to. -/
def IsMaximalExpectationBoundedTest (μ : Measure CantorSeq) (u : CantorSeq → ℝ≥0∞) : Prop :=
  IsExpectationBoundedRandomnessTest μ u ∧
    ∀ v, IsExpectationBoundedRandomnessTest μ v → ∃ c : NNReal, ∀ w, v w ≤ c * u w

/-- Maximal expectation-bounded tests exist, by SUV Theorem 42. -/
theorem exists_isMaximalExpectationBoundedTest {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) : ∃ u, IsMaximalExpectationBoundedTest μ u :=
  exists_maximal_expectation_bounded_test hμ

end Kolmogorov
