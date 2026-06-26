/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CountableKraft
import KolmogorovMathlib.AlgorithmicProbability.Bounds

/-!
# The Pair-Output Marginal Semimeasure

This module isolates a small, fully-proved ingredient of the Levin–Gács lower
direction of prefix symmetry of information: the **pair-output marginal**

```
pairMarginal M x = ∑_y m_M(⟨x, y⟩ | []),
```

the total a priori probability that a `U`-program outputs an encoded pair whose
first component is `x`. The headline fact is that this marginal is itself a
(sub)semimeasure in `x`:

```
∑_x pairMarginal M x ≤ 1   (for a prefix machine M).
```

The proof is pure summation rearrangement: the double sum over `(x, y)` is a sum
over the product type, which—because `pairCode` is **injective**—is bounded by
the full output sum `∑_z m_M(z | [])`, itself `≤ 1` by the countable Kraft bound
`tsum_aprioriMeasure_le_one`. No new computability or coding content is needed
here; this is the normalization input that the (harder) marginal coding theorem
consumes to obtain `pairMarginal M x ≤× 2^{-K(x)}`.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The **pair-output marginal** of a map `M` at first component `x`: the total a
priori probability over all second components `y` of the encoded pair `⟨x, y⟩`,
taken in the empty context. -/
noncomputable def pairMarginal (M : Map) (x : BitString) : ℝ≥0∞ :=
  ∑' y : BitString, aprioriMeasure M (pairCode x y) []

/-- Unfolding lemma for `pairMarginal`. -/
theorem pairMarginal_def (M : Map) (x : BitString) :
    pairMarginal M x = ∑' y : BitString, aprioriMeasure M (pairCode x y) [] :=
  rfl

/-- **The pair marginal is a subsemimeasure.** For a prefix machine, the total
pair-output marginal over all first components is at most `1`.

The double sum over `(x, y)` collapses to a sum over the product type; injectivity
of `pairCode` bounds it by the full output sum `∑_z m_M(z | [])`, which the
countable Kraft inequality caps at `1`. -/
theorem tsum_pairMarginal_le_one (M : Map) (hM : IsPrefixMachine M) :
    (∑' x : BitString, pairMarginal M x) ≤ 1 := by
  calc
    (∑' x : BitString, pairMarginal M x)
        = ∑' p : BitString × BitString, aprioriMeasure M (pairCode p.1 p.2) [] :=
      (ENNReal.tsum_prod (f := fun x y => aprioriMeasure M (pairCode x y) [])).symm
    _ ≤ ∑' z : BitString, aprioriMeasure M z [] :=
      ENNReal.tsum_comp_le_tsum_of_injective pairCode_injective
        (fun z => aprioriMeasure M z [])
    _ ≤ 1 := tsum_aprioriMeasure_le_one M [] hM

/-- The pair marginal is finite for a prefix machine (being bounded by `1` after
summation, hence termwise bounded by the total). -/
theorem pairMarginal_ne_top (M : Map) (x : BitString) (hM : IsPrefixMachine M) :
    pairMarginal M x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (le_trans (ENNReal.le_tsum x) (tsum_pairMarginal_le_one M hM))

/-! ### The scaled section semimeasure

The Levin–Gács lower direction works with the *section semimeasure*
`y ↦ m_M(⟨x, y⟩ | []) · 2^{k}`, the a priori pair mass of `⟨x, y⟩` rescaled by
`2^{k}` (taken at `k = K(x)`). Its total mass over `y` is exactly the pair
marginal scaled by `2^{k}`, so it is a genuine (sub)semimeasure precisely when
the marginal coding bound `pairMarginal M x ≤ 2^{-k}` holds. These two facts are
the pure-summation inputs the conditional coding engine consumes. -/

/-- **Section total mass.** Summing the scaled section weights `m_M(⟨x,y⟩) · 2^{k}`
over all second components `y` gives the pair marginal scaled by `2^{k}`. Pure
`tsum` linearity. -/
theorem pairSection_tsum (M : Map) (x : BitString) (k : ℕ) :
    ∑' y : BitString, (aprioriMeasure M (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
      = pairMarginal M x * (2 : ℝ≥0∞) ^ k := by
  rw [pairMarginal_def, ENNReal.tsum_mul_right]

/-- **Constant-subnormalized section.** If the scaled marginal at `x` is bounded
by `2^d`, then the scaled section over second components has the same total-mass
bound. This is the exact pure-summation shape used by the guarded conditional
coding interface, where the marginal coding theorem supplies a uniform overhead
constant rather than a constant-free `≤ 1` bound. -/
theorem pairSection_tsum_le_of_marginal_scaled (M : Map) (x : BitString) (k d : ℕ)
    (h : pairMarginal M x * (2 : ℝ≥0∞) ^ k ≤ (2 : ℝ≥0∞) ^ d) :
    ∑' y : BitString, (aprioriMeasure M (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
      ≤ (2 : ℝ≥0∞) ^ d := by
  rw [pairSection_tsum]
  exact h

/-- **The section is a semimeasure under the marginal coding bound.** If the pair
marginal at `x` is bounded by `2^{-k}` (the marginal coding bound at `k = K(x)`),
then the scaled section `y ↦ m_M(⟨x,y⟩) · 2^{k}` has total mass `≤ 1`, i.e. it is
a conditional subsemimeasure in `y`. This is the precondition the conditional
coding theorem requires of the section. -/
theorem pairSection_tsum_le_one_of_marginal (M : Map) (x : BitString) (k : ℕ)
    (h : pairMarginal M x ≤ (2 : ℝ≥0∞)⁻¹ ^ k) :
    ∑' y : BitString, (aprioriMeasure M (pairCode x y) [] * (2 : ℝ≥0∞) ^ k) ≤ 1 := by
  rw [pairSection_tsum]
  calc pairMarginal M x * (2 : ℝ≥0∞) ^ k
      ≤ (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k := mul_le_mul_left h _
    _ = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]

end Kolmogorov
