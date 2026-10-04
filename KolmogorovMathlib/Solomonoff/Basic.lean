/-
Copyright (c) 2024 Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author
-/
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding

/-!
# The conditional predictor of a tree semimeasure

Solomonoff induction predicts the next bit of a binary sequence from the bits seen so far by the
conditional probability `M(b | x) = M(xb) / M(x)` of the a priori probability
`M = universalContinuousSemimeasure`. This module defines the conditional `condProb a x b` of an
arbitrary tree mass function, the universal predictor `solomonoffPredictor`, and the elementary
facts about conditionals that the convergence proof uses.

### Outline

* `condProb a x b = a(xb) / a(x)`, a real number, equal to `0` when `a(x) = 0` (Lean's `t / 0 = 0`);
* for a continuous tree semimeasure the two conditionals at a node are nonnegative and sum to at
  most one (`IsContinuousTreeSemimeasure.condProb_add_le_one`), the child mass is the parent mass
  times the conditional (`IsContinuousTreeSemimeasure.toReal_mul_condProb`), and along a sequence
  the mass of a prefix is the product of the conditionals of its bits
  (`IsContinuousTreeSemimeasure.toReal_cantorPrefix_eq_prod`);
* for a probability measure on Cantor space the two conditionals sum to exactly one at every node
  of positive mass (`condProb_cantorMass_add_eq_one`);
* the a priori probability is positive everywhere (`universalContinuousSemimeasure_pos`, reused
  from `APrioriComplexity`), so the universal predictor is a genuine ratio, positive
  (`solomonoffPredictor_pos`), and a sub-probability (`solomonoffPredictor_add_le_one`).

### The semimeasure caveat

`M` is only a semimeasure, `M(x0) + M(x1) ≤ M(x)`, and the deficit is not redistributed: the
predictor used throughout this directory is the *unnormalized* one, `M(b | x) = M(xb) / M(x)`, as
in Hutter (2005) Theorem 3.19 and Li–Vitányi (3rd ed.) Theorem 5.2.1. The error of a prediction is
measured for one fixed bit `b` at a time (`predictionError`); this is legitimate for a
sub-probability predictor because Pinsker's inequality survives lowering the weight of the other
bit (`two_mul_sq_sub_le_binaryKL`). Solomonoff's normalized predictor `M(xb) / (M(x0) + M(x1))` is
not treated.

Sources: R. J. Solomonoff, *Complexity-based induction systems: comparisons and convergence
theorems*, IEEE Trans. Inform. Theory 24 (1978); M. Li and P. Vitányi, *An Introduction to
Kolmogorov Complexity and Its Applications*, 3rd ed. (2008), §4.5 and §5.2; M. Hutter,
*Universal Artificial Intelligence* (2005), §2.4 and §3.2.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-- The conditional probability `a(b | x) = a(xb) / a(x)` that the tree mass function `a` gives to
the bit `b` right after the string `x`, as a real number. It is `0` when `a(x) = 0` (Lean's
convention `t / 0 = 0`); for a semimeasure it is the unnormalized conditional, and the two
conditionals at a node may sum to less than one. Item SOL-B-COND; Li–Vitányi (3rd ed.) §5.2
(`M(b | x) = M(xb) / M(x)`), Hutter (2005) §2.4 (`ρ(x_t | x_{<t})`). -/
noncomputable def condProb (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) : ℝ :=
  (a (x ++ [b])).toReal / (a x).toReal

/-- The universal (Solomonoff) predictor `M(b | x) = M(xb) / M(x)`: the conditional of the a priori
probability `M = universalContinuousSemimeasure` on the tree. Item SOL-B-PRED; Solomonoff (1978),
Li–Vitányi (3rd ed.) §5.2, Hutter (2005) §3.2 (`ξ(x_t | x_{<t})` with `ξ = M`). -/
noncomputable def solomonoffPredictor (x : BitString) (b : Bool) : ℝ :=
  condProb universalContinuousSemimeasure x b

/-- Conditional probabilities are nonnegative. Item SOL-B-NONNEG. -/
theorem condProb_nonneg (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    0 ≤ condProb a x b := by
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- For a continuous tree semimeasure the two conditionals at a node sum to at most one; strict
inequality is allowed (the semimeasure caveat). Item SOL-B-SUBPROB; Hutter (2005) §2.4
(conditionals of a semimeasure form a semi-probability). -/
theorem IsContinuousTreeSemimeasure.condProb_add_le_one {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) :
    condProb a x false + condProb a x true ≤ 1 := by
  unfold condProb
  by_cases h : a x = 0
  · simp [h]
  · rw [← add_div]
    rw [div_le_one]
    · have h_le := ha.2 x
      have h1 :
          (a (x ++ [false])).toReal + (a (x ++ [true])).toReal =
            (a (x ++ [false]) + a (x ++ [true])).toReal := by
        rw [ENNReal.toReal_add]
        · exact ha.ne_top (x ++ [false])
        · exact ha.ne_top (x ++ [true])
      rw [h1]
      apply ENNReal.toReal_mono (ha.ne_top x) h_le
    · exact ENNReal.toReal_pos h (ha.ne_top x)

/-- For a continuous tree semimeasure the mass of a child is the mass of the node times the
conditional, `a(x) · a(b | x) = a(xb)`; this holds also when `a(x) = 0`, since then `a(xb) = 0`.
Item SOL-B-MUL. -/
theorem IsContinuousTreeSemimeasure.toReal_mul_condProb {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (x : BitString) (b : Bool) :
    (a x).toReal * condProb a x b = (a (x ++ [b])).toReal := by
  unfold condProb
  by_cases h : a x = 0
  · simp [h]
    have h1 : a (x ++ [b]) ≤ a x := by
      cases b
      · exact ha.child_false_le x
      · exact ha.child_true_le x
    have h2 : a (x ++ [b]) = 0 := le_antisymm (h ▸ h1) (bot_le)
    simp [h2]
  · rw [mul_div_cancel₀ _ (ENNReal.toReal_pos h (ha.ne_top x)).ne.symm]

/-- Chain rule for conditionals: along a sequence `w`, the mass of the length-`n` prefix is the
product of the conditionals of its bits, `a(w_{<n}) = ∏_{i<n} a(w_i | w_{<i})` (a product that
becomes `0` at the first null prefix). Item SOL-B-PROD; Hutter (2005) §2.4 (chain rule
`ρ(x_{1:n}) = ∏_t ρ(x_t | x_{<t})`). -/
theorem IsContinuousTreeSemimeasure.toReal_cantorPrefix_eq_prod {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (w : CantorSeq) (n : ℕ) :
    (a (cantorPrefix w n)).toReal =
      ∏ i ∈ Finset.range n, condProb a (cantorPrefix w i) (w i) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, cantorPrefix, List.ofFn_zero]
    rw [ha.1, ENNReal.toReal_one]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih, cantorPrefix_succ]
    exact (ha.toReal_mul_condProb (cantorPrefix w n) (w n)).symm

/-- Under a probability measure on Cantor space the two conditionals at a node of positive mass
sum to exactly one. Item SOL-B-MEAS; SUV §3.1 (`p(x) = p(x0) + p(x1)`). -/
theorem condProb_cantorMass_add_eq_one (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {x : BitString} (hx : cantorMass μ x ≠ 0) :
    condProb (cantorMass μ) x false + condProb (cantorMass μ) x true = 1 := by
  unfold condProb
  have htop : cantorMass μ x ≠ ∞ := ne_top_of_lt (measure_lt_top μ _)
  have hzero : (cantorMass μ x).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨hx, htop⟩
  rw [← add_div, ← ENNReal.toReal_add]
  · rw [← cantorMass_add μ x, div_self hzero]
  · exact ne_top_of_lt (measure_lt_top μ _)
  · exact ne_top_of_lt (measure_lt_top μ _)

/-- The a priori probability of every string is a positive real number (it is positive and at most
one). Item SOL-B-MPOS; from `universalContinuousSemimeasure_pos`. -/
theorem universalContinuousSemimeasure_toReal_pos (x : BitString) :
    0 < (universalContinuousSemimeasure x).toReal := by
  have pos := universalContinuousSemimeasure_pos x
  have ha_top :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  exact ENNReal.toReal_pos pos.ne' ha_top

/-- The universal predictor never excludes a bit: `M(b | x) > 0`. Item SOL-B-PREDPOS. -/
theorem solomonoffPredictor_pos (x : BitString) (b : Bool) : 0 < solomonoffPredictor x b := by
  unfold solomonoffPredictor condProb
  apply div_pos
  · exact universalContinuousSemimeasure_toReal_pos (x ++ [b])
  · exact universalContinuousSemimeasure_toReal_pos x

/-- The universal predictor is a sub-probability: `M(0 | x) + M(1 | x) ≤ 1`. Item SOL-B-PREDSUB;
the semimeasure caveat of Li–Vitányi (3rd ed.) §5.2 and Hutter (2005) §3.2. -/
theorem solomonoffPredictor_add_le_one (x : BitString) :
    solomonoffPredictor x false + solomonoffPredictor x true ≤ 1 := by
  exact universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
    |>.1.condProb_add_le_one _

end Kolmogorov
