/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.AlgorithmicProbability.Domination

/-!
# Optimal Prefix Invariance as Complexity-Weight Domination

This module is a tiny bridge: it rephrases the *additive* invariance bound of an
optimal prefix decompressor (`IsOptimalPrefixConditional.invariance`,
`KP U ≤ KP M + c`) as a *multiplicative* domination of the synthetic complexity
weight `2^{-KP}` (`complexityWeight ∘ KP`).

The algebraic core is already in `Coding`: `complexityWeight_le_of_le` (antitone
in the exponent) and `complexityWeight_add_nat` (an additive cost `c` scales the
weight by `2^{-c}`). Combining them with the invariance bound gives
`2^{-c} · 2^{-KP_M(x|y)} ≤ 2^{-KP_U(x|y)}`, packaged in the `Dominates` (`≤×`)
vocabulary.

**Scope.** This is domination of the synthetic quantity `2^{-KP}` only. It is
*not* a statement about a priori semimeasure domination: deriving
`aprioriMeasure U ≽ aprioriMeasure M` requires an explicit injective,
length-bounded translation (`aprioriMeasure_dominates_of_simulation'`), which
the abstract `KP` invariance hypothesis does not provide. No equality, no
logarithm, and no existence of an optimal prefix decompressor is claimed.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Additive-to-multiplicative bridge.** From the additive invariance bound of
an optimal prefix decompressor `U` over a prefix decompressor `M`
(`KP U x y ≤ KP M x y + c`) we obtain the multiplicative weight bound
`2^{-c} · 2^{-KP_M(x|y)} ≤ 2^{-KP_U(x|y)}`, with a single constant `c` uniform in
`x, y`. -/
theorem optimalPrefix_complexityWeight_bound
    {U M : Map} (hU : IsOptimalPrefixConditional U)
    (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ, ∀ x y,
      ((2 : ℝ≥0∞)⁻¹ ^ c) * complexityWeight (KP M x y)
        ≤ complexityWeight (KP U x y) := by
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x y
  have h := complexityWeight_le_of_le (hc x y)
  rw [complexityWeight_add_nat] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- **Realization-to-optimal transfer.** Suppose a family `μ` is *realized* by some
prefix decompressor `M` up to a constant coding loss `c₀`, in the sense that
`2^{-c₀} · μ y z ≤ 2^{-KP_M(y | z)}` everywhere. Then the optimal prefix
decompressor `U` already dominates `μ` by a (larger) constant: the optimal
invariance bound absorbs `M`'s coding overhead.

This is the reusable second half of the conditional coding theorem: it reduces
"`μ` is dominated by `2^{-KP_U}`" to the genuinely hard Kraft–Chaitin
*realization* of `μ` as a single prefix machine `M`. The realization itself is
not provided here; everything downstream of it is. -/
theorem complexityWeight_dominates_of_prefix_realization
    {U : Map} (hU : IsOptimalPrefixConditional U)
    {μ : BitString → BitString → ℝ≥0∞} {M : Map} {c₀ : ℕ}
    (hM : IsPrefixDecompressor M)
    (hreal : ∀ y z, ((2 : ℝ≥0∞)⁻¹ ^ c₀) * μ y z ≤ complexityWeight (KP M y z)) :
    ∃ c : ℕ, ∀ y z, ((2 : ℝ≥0∞)⁻¹ ^ c) * μ y z ≤ complexityWeight (KP U y z) := by
  obtain ⟨c₁, hc₁⟩ := optimalPrefix_complexityWeight_bound hU hM
  refine ⟨c₀ + c₁, fun y z => ?_⟩
  calc
    ((2 : ℝ≥0∞)⁻¹ ^ (c₀ + c₁)) * μ y z
        = ((2 : ℝ≥0∞)⁻¹ ^ c₁) * (((2 : ℝ≥0∞)⁻¹ ^ c₀) * μ y z) := by
          rw [pow_add]; ring
    _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ c₁) * complexityWeight (KP M y z) :=
        mul_le_mul_right (hreal y z) _
    _ ≤ complexityWeight (KP U y z) := hc₁ y z

/-- **Complexity-weight domination.** Restating `optimalPrefix_complexityWeight_bound`
in the `Dominates` vocabulary: the optimal prefix decompressor's complexity weight
`2^{-KP_U}` dominates any prefix decompressor's complexity weight `2^{-KP_M}` by a
constant `2^{-c}`. This is the `≤×` (multiplicative) shadow of the additive
invariance bound, over the synthetic weight only. -/
theorem optimalPrefix_complexityWeight_dominates
    {U M : Map} (hU : IsOptimalPrefixConditional U)
    (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ,
      Dominates
        (fun x y => complexityWeight (KP U x y))
        (fun x y => complexityWeight (KP M x y))
        ((2 : ℝ≥0∞)⁻¹ ^ c) := by
  obtain ⟨c, hc⟩ := optimalPrefix_complexityWeight_bound hU hM
  exact ⟨c, hc⟩

end Kolmogorov
