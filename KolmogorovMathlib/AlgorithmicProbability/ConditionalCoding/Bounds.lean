/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.ConditionalCoding.Computability
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding
import KolmogorovMathlib.AlgorithmicProbability.PairMarginal

/-!
# Conditional Coding Bounds
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Conditional Kraft–Chaitin realization of the scaled pair section** (SUV
§4.5), uniform in the subnormalization level `d`.

For every level `d`, a single prefix decompressor `M` (depending on `d`) realizes
the lower-semicomputable section family `y ↦ m_U(⟨x,y⟩) · 2^{k}` — up to a uniform
constant `c₀` (absorbing the `d`-overhead) — at every context `(x, k)` where the
section is `2^{d}`-subnormalized, i.e. where the per-context guard
`∑_y m_U(⟨x,y⟩) · 2^{k} ≤ 2^{d}` holds.

The output is a conditional program for `y` in the faithful context
`pairCode x (natCode k)` (definitionally `prefixComplexityContext x k`). The guard
is what makes the statement true: the truncated Kraft–Chaitin construction
down-scales by the fixed factor `2^{-d}` it hardcodes (yielding a genuine
subsemimeasure of mass `≤ 1`) and emits prefix codes for `y` only while the
running mass stays bounded; the `2^{-d}` down-scale costs an additive `d` in code
length, folded into `c₀`.

The proof now reduces to the abstract engine: the scaled section is l.s.c.
(`scaledSection_isLSC`); dynamic truncation (`IsLSC.truncate`) caps its global mass
at `2^{d}` while leaving it untouched wherever the guard holds; and
`kraftChaitin_realization_bound` realizes the truncated function. `scaledSection_eq`
identifies the per-context guard with the truncation's mass bound. The guard is
never dropped, so the false unguarded `∀ k` bound is never asserted. -/
theorem conditional_coding_section_realization (U : Map)
    (hU : IsOptimalPrefixConditional U) (d : ℕ) :
    ∃ M : Map, IsPrefixDecompressor M ∧ ∃ c₀ : ℕ,
      ∀ (x : BitString) (k : ℕ),
        (∑' y : BitString, aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
            ≤ (2 : ℝ≥0∞) ^ d →
        ∀ y : BitString,
          (2 : ℝ≥0∞)⁻¹ ^ c₀ * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
            ≤ complexityWeight (KP M y (pairCode x (natCode k))) := by
  -- Truncate the (globally l.s.c.) scaled section to a global `2^{d}`-mass bound,
  -- then feed it to the abstract Kraft–Chaitin engine. Where the per-context guard
  -- holds, the truncation is inert, so the realization is for the raw section.
  obtain ⟨g, hg_lsc, hg_sum, hg_agree⟩ :=
    (scaledSection_isLSC U hU.isPrefixDecompressor).truncate d
  obtain ⟨M, hM, c₀, hreal⟩ := kraftChaitin_realization_bound hg_lsc d hg_sum
  refine ⟨M, hM, c₀, fun x k hguard y => ?_⟩
  -- The guard for `(x, k)` is exactly the truncation's per-context mass bound for
  -- the section at context `pairCode x (natCode k)` (via `scaledSection_eq`).
  have hctx_sum :
      (∑' out : BitString, scaledSection U out (pairCode x (natCode k)))
        ≤ (2 : ℝ≥0∞) ^ d := by
    rw [tsum_congr (fun y => scaledSection_eq U x y k)]
    exact hguard
  have hagree := hg_agree (pairCode x (natCode k)) hctx_sum y
  rw [scaledSection_eq] at hagree
  have hM_bound := hreal y (pairCode x (natCode k))
  rwa [hagree] at hM_bound

/-- **Assembled conditional coding bound `hcode`.** Combines the marginal coding
bound and the conditional Kraft–Chaitin realization into exactly the hypothesis
consumed by `KPPair_chain_lower_of_conditional_coding`.

The proof is pure `ℝ≥0∞`/exponent algebra:

* the marginal bound puts the section mass at `≤ 2^{c₂}` at `k = K(x)` (via
  `pairSection_tsum`), discharging the realization guard at level `d = c₂`;
* the realization gives `2^{-c₀} · section ≤ 2^{-K_M(y | x,k)}`;
* `optimalPrefix_complexityWeight_bound` transfers `M`'s weight to `U`, absorbing
  the coding overhead into the constant via `pow_add`.

The guard `(k : ENat) = KP U x []` is definitionally `HasPrefixComplexityValue`,
and `pairCode x (natCode k)` is definitionally `prefixComplexityContext x k`, so
this is `defeq` to the `hcode` shape required in `Symmetry`. -/
theorem section_coding_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c₁ : ℕ, ∀ (x y : BitString) (k : ℕ), (k : ENat) = KP U x [] →
      (2 : ℝ≥0∞)⁻¹ ^ c₁ * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
        ≤ complexityWeight (KP U y (pairCode x (natCode k))) := by
  obtain ⟨c₂, hmarg⟩ := pairMarginal_coding_bound U hU
  obtain ⟨M, hM, c₀, hreal⟩ := conditional_coding_section_realization U hU c₂
  obtain ⟨c₁, hopt⟩ := optimalPrefix_complexityWeight_bound hU hM
  refine ⟨c₀ + c₁, fun x y k hk => ?_⟩
  -- The marginal coding bound puts the section mass at `≤ 2^{c₂}` at `k = K(x)`,
  -- discharging the realization guard at level `d = c₂`.
  have hsemi : (∑' y : BitString, aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
      ≤ (2 : ℝ≥0∞) ^ c₂ := by
    exact pairSection_tsum_le_of_marginal_scaled U x k c₂ (hmarg x k hk)
  have hM_bound := hreal x k hsemi y
  -- Transfer the realization from `M` to the optimal `U`, absorbing `c₀` via `pow_add`.
  calc (2 : ℝ≥0∞)⁻¹ ^ (c₀ + c₁)
          * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)
      = (2 : ℝ≥0∞)⁻¹ ^ c₁
          * ((2 : ℝ≥0∞)⁻¹ ^ c₀
            * (aprioriMeasure U (pairCode x y) [] * (2 : ℝ≥0∞) ^ k)) := by
        rw [pow_add]; ring
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KP M y (pairCode x (natCode k))) :=
        mul_le_mul_right hM_bound _
    _ ≤ complexityWeight (KP U y (pairCode x (natCode k))) :=
        hopt y (pairCode x (natCode k))

end Kolmogorov
