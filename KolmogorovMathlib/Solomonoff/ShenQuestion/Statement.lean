/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure

/-!
# Shen's question on the a priori probability of a prefix: the statement

Let `M` be the universal lower semicomputable continuous semimeasure
(`universalContinuousSemimeasure`), `Q y x = Q(y | x)` a lower semicomputable
conditional continuous semimeasure and `m` a lower semicomputable discrete semimeasure.
Shen's functional is

  `f(x) = sup { λ | ∀ y, λ · Q(y | x) ≤ M(x y) }  ( = inf_y M(x y) / Q(y | x) )`.

It is classical that `f(x) ≥ c · m(x)` for a positive constant `c` (mixture argument).
Shen asked whether `f ≍ m`, i.e. whether also `f(x) ≤ C · m(x)`.  The answer is
negative, in the strong form `shen_negative` below: for **every** lsc `Q` and **every**
lsc discrete `m` and every `R` there is a string `u` with `0 < f(u)` and
`f(u) ≥ c · R · m(u)`.  Universality is used only for `M`.

This file fixes the definitions and the basic lemmas about `shenF`; the main theorem
`shen_negative` and its corollaries are stated and proved in
`KolmogorovMathlib.Solomonoff.ShenQuestion.Main`.

Conventions (inherited from `KolmogorovMathlib`): `BitString = List Bool`; two-argument
functions are written `(out, ctx)`, so `Q y x = Q(y | x)`; a continuous semimeasure has
root mass exactly `1` (`IsContinuousTreeSemimeasure`); lower semicomputability is
`IsLSC` (computable monotone dyadic stages with supremum the function); a lower
semicomputable discrete semimeasure is `IsLowerSemicomputableSemimeasure` (`∑' m ≤ 1`
and `IsLSC` with a dummy condition), and `IsUniversalSemimeasure` is the universal one.
-/

open scoped ENNReal BigOperators

namespace Kolmogorov
namespace Shen

/-- Conditional continuous (tree) semimeasure: for every condition `x` the function
`y ↦ Q y x` is a continuous semimeasure (root mass `1`, children sum `≤` parent). -/
def IsConditionalContinuousTreeSemimeasure (Q : BitString → BitString → ℝ≥0∞) : Prop :=
  ∀ x, IsContinuousTreeSemimeasure (fun y => Q y x)

/-- Lower semicomputable conditional continuous semimeasure (uniformly in the condition). -/
def IsLSCConditionalContinuousSemimeasure (Q : BitString → BitString → ℝ≥0∞) : Prop :=
  IsConditionalContinuousTreeSemimeasure Q ∧ IsLSC Q

/-- Universal conditional continuous semimeasure: lsc, and dominating every lsc conditional
continuous semimeasure with a constant that does not depend on the condition. -/
def IsUniversalConditionalContinuousSemimeasure (Q : BitString → BitString → ℝ≥0∞) : Prop :=
  IsLSCConditionalContinuousSemimeasure Q ∧
    ∀ Q', IsLSCConditionalContinuousSemimeasure Q' →
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ y x, Q' y x ≤ c * Q y x

/-- Shen's functional, division-free form:
`shenF M Q x = sup { λ | ∀ y, λ · Q(y | x) ≤ M(x ++ y) }`. -/
noncomputable def shenF (M : BitString → ℝ≥0∞) (Q : BitString → BitString → ℝ≥0∞)
    (x : BitString) : ℝ≥0∞ :=
  sSup {l : ℝ≥0∞ | ∀ y, l * Q y x ≤ M (x ++ y)}

/-- Every `λ` with `λ · Q(y | x) ≤ M(x y)` for all `y` is at most `f(x)`. -/
theorem le_shenF {M : BitString → ℝ≥0∞} {Q : BitString → BitString → ℝ≥0∞} {x : BitString}
    {l : ℝ≥0∞} (h : ∀ y, l * Q y x ≤ M (x ++ y)) : l ≤ shenF M Q x :=
  le_sSup h

/-- The supremum is attained: `f(x) · Q(y | x) ≤ M(x y)` for every `y`. -/
theorem shenF_mul_le (M : BitString → ℝ≥0∞) (Q : BitString → BitString → ℝ≥0∞)
    (x y : BitString) : shenF M Q x * Q y x ≤ M (x ++ y) := by
  rw [shenF, sSup_eq_iSup', ENNReal.iSup_mul]
  exact iSup_le fun l => l.2 y

/-- `f(x) ≤ M(x)` (take `y = []`, using `Q([] | x) = 1`). -/
theorem shenF_le_root {M : BitString → ℝ≥0∞} {Q : BitString → BitString → ℝ≥0∞}
    (hQ : IsConditionalContinuousTreeSemimeasure Q) (x : BitString) :
    shenF M Q x ≤ M x := by
  have h := shenF_mul_le M Q x []
  simpa [(hQ x).1] using h

/-- `f` is finite whenever `M` is a continuous semimeasure. -/
theorem shenF_ne_top {M : BitString → ℝ≥0∞} {Q : BitString → BitString → ℝ≥0∞}
    (hM : IsContinuousTreeSemimeasure M) (hQ : IsConditionalContinuousTreeSemimeasure Q)
    (x : BitString) : shenF M Q x ≠ ⊤ := by
  have hMx : M x ≤ 1 := by
    have h := hM.antitone_of_prefix (List.nil_prefix (l := x))
    simpa [hM.1] using h
  exact ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hMx) (shenF_le_root hQ x)

end Shen
end Kolmogorov
