/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.TotalCountingBound.Computability

namespace Kolmogorov

open scoped ENNReal

/-- **Counting prefix machine for SUV Theorem 64 (upper bound).**  There is a
prefix decompressor `M` and a coding constant `c₀` such that, for every `n` and
every finite set `A` of strings of prefix complexity `≤ n`,

  `2^{-c₀} · (|A| · 2^{-n}) ≤ 2^{-KP_M(Nat.bits n)}`.

This is the genuinely hard enumeration-and-coding step of Theorem 64: it is the
Kraft–Chaitin realization (`kraftChaitin_realization_bound`) of the counting
lower-semicomputable function `countingF`, whose pointwise lower bound is
`countingF_ge_card` and whose total mass `≤ 2 = 2^1` is `countingF_tsum_le`.

The coding constant `c₀` is genuine.  A constant-free version is **false**: a
prefix machine `M` has total Kraft mass `∑_x 2^{-KP_M(x)} ≤ 1`, whereas the
required counting mass `∑_n N_n 2^{-n} = 2 ∑_x 2^{-K(x)}` can exceed `1`.  The
constant is harmlessly absorbed by the optimal-machine invariance in
`card_KPPlain_le_complexityWeight_bound`, so the downstream Theorem 64 upper bound
is unaffected. -/
theorem exists_counting_prefix_machine (U : Map) (hU : IsPrefixDecompressor U) :
    ∃ M : Map, IsPrefixDecompressor M ∧ ∃ c₀ : ℕ,
    ∀ (n : ℕ) (A : Finset BitString),
      (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) →
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n)
        ≤ complexityWeight (KP M (Nat.bits n) []) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  have hlsc : IsLSC (countingF c) := countingF_isLSC c
  have hsum : ∀ ctx : BitString, (∑' out : BitString, countingF c out ctx) ≤ (2 : ℝ≥0∞) ^ 1 := by
    intro ctx
    rw [pow_one]
    exact countingF_tsum_le U hU c hc ctx
  obtain ⟨M, hM, c₀, hreal⟩ := kraftChaitin_realization_bound hlsc 1 hsum
  refine ⟨M, hM, c₀, fun n A hA => ?_⟩
  calc
    (2 : ℝ≥0∞)⁻¹ ^ c₀ * ((A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * countingF c (Nat.bits n) [] := by
          gcongr
          exact countingF_ge_card U c hc n A hA
    _ ≤ complexityWeight (KP M (Nat.bits n) []) := hreal (Nat.bits n) []

/-- The counting weight of `n` is bounded by the complexity weight of `n` in an optimal machine. -/
theorem card_KPPlain_le_complexityWeight_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (A : Finset BitString),
    (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) →
    (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n)) := by
  obtain ⟨M, hM, c₀, hM_bound⟩ := exists_counting_prefix_machine U hU.isPrefixDecompressor
  obtain ⟨c, hc⟩ := optimalPrefix_complexityWeight_bound hU hM
  refine ⟨c + c₀, fun n A hA => ?_⟩
  have key := hM_bound n A hA
  have hopt := hc (Nat.bits n) []
  have h1 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
      ≤ (2 : ℝ≥0∞) ^ c₀ * complexityWeight (KP M (Nat.bits n) []) := by
    calc
      (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
          = (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞)⁻¹ ^ c₀ * ((A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n)) := by
            rw [← mul_assoc, ← mul_pow,
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
      _ ≤ (2 : ℝ≥0∞) ^ c₀ * complexityWeight (KP M (Nat.bits n) []) := by gcongr
  have h2 : complexityWeight (KP M (Nat.bits n) [])
      ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n)) := by
    calc
      complexityWeight (KP M (Nat.bits n) [])
          = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (KP M (Nat.bits n) [])) := by
            rw [← mul_assoc, ← mul_pow,
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
      _ ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n)) := by
            gcongr
            simpa [KPPlain] using hopt
  calc
    (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n
        ≤ (2 : ℝ≥0∞) ^ c₀ * complexityWeight (KP M (Nat.bits n) []) := h1
    _ ≤ (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (Nat.bits n))) := by
          gcongr
    _ = (2 : ℝ≥0∞) ^ (c + c₀) * complexityWeight (KPPlain U (Nat.bits n)) := by
          rw [pow_add]; ring

theorem card_KPPlain_le_upper_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
    ∀ A : Finset BitString, (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) →
    (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (n + c) * (2 : ℝ≥0∞)⁻¹ ^ kn := by
  obtain ⟨c, hc⟩ := card_KPPlain_le_complexityWeight_bound U hU
  use c
  intro n kn hkn A hA
  specialize hc n A hA
  have h_weight : complexityWeight (KPPlain U (Nat.bits n)) = (2 : ℝ≥0∞)⁻¹ ^ kn := by
    dsimp [HasPrefixComplexityValue, KPPlain] at hkn ⊢
    rw [← hkn, complexityWeight_coe]
  rw [h_weight] at hc
  have e : (A.card : ℝ≥0∞) = (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n := by
    rw [mul_assoc]
    have h_inv : (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    rw [h_inv, mul_one]
  calc
    (A.card : ℝ≥0∞) = (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n := e
    _ ≤ ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn) * (2 : ℝ≥0∞) ^ n := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (n + c) * (2 : ℝ≥0∞)⁻¹ ^ kn := by
        rw [pow_add]
        ring

/- SUV Theorem 64 (Lower Bound), historical exact statement.

There are at least `2^{n - K(n) - O(1)}` strings
with prefix complexity at most `n`.
Formulated as the existence of a finite set `A` of such strings.

This exact form (complexity `≤ n`, no additive slack) is **not** provable for
every optimal prefix machine: at `n = 0` it would require a string of complexity
`≤ 0`, which need not exist (e.g. for machines whose halting programs are all
nonempty).  The faithful, provable statement is
`card_KPPlain_le_lower_bound_faithful`, which asks for complexity `≤ n + O(1)` in
the regime `K(n) ≤ n`.

This declaration is therefore commented out: it is genuinely false for some
optimal prefix decompressors (so it cannot be proved without an additional
normalization hypothesis on `U` supplying a zero-length program), and it is not
referenced anywhere in the project.  The faithful, fully proved replacement
`card_KPPlain_le_lower_bound_faithful` above supersedes it.
-/

/-
theorem card_KPPlain_le_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
    ∃ A : Finset BitString, (∀ x ∈ A, KPPlain U x ≤ (n : ENat)) ∧
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ (kn + c) ≤ (A.card : ℝ≥0∞) :=
  -- False without additional hypotheses on U
  -- e.g. at n=0 requires complexity ≤ 0, impossible if all halting programs are nonempty
  -- Use `card_KPPlain_le_lower_bound_faithful` instead.
-/


end Kolmogorov
