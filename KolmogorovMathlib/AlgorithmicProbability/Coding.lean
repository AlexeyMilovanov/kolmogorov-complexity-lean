/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.Semimeasure

/-!
# The Easy Coding Bound `2^{-KP} ≤ m_M`

This module packages the term-level lower bound of
`KolmogorovMathlib.AlgorithmicProbability.Semimeasure` into the standard
"coding" form `2^{-KP(x | y)} ≤ m_M(x | y)`.

To raise `2⁻¹` to the conditional prefix complexity `KP M x y : ENat` we need a
convention at `⊤`: when no program produces `x` from `y`, `KP = ⊤` and the
weight is taken to be `0`. The helper `complexityWeight` encodes exactly this
`⊤ ↦ 0`, `n ↦ 2^{-n}` rule, matching the existing `progWeight` on coerced
naturals (both are `(2⁻¹) ^ n` via `Monoid.npow`, so the bridge is `rfl`).

The headline inequality `complexityWeight (KP M x y) ≤ aprioriMeasure M x y`
holds for **every** map `M`: it is the easy direction, where a single
length-minimal program witnesses the bound. No prefix-freeness, computability,
or universality is assumed. The matching upper bound (the hard half of the
coding theorem) is genuinely a strict inequality in general and is **not**
attempted here; this is an `≤`, never an equality, and uses no real logarithm.

The key structural fact is that the infimum defining `KP` is *achieved*: `ENat`
is well-ordered, so a nonempty `candidateLengths` set contains its `sInf`. That
yields an actual program of length `KP`, to which the term-level bound
`progWeight_le_aprioriMeasure` applies.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The **complexity weight** `2^{-n}` of an extended natural `n : ENat`, with the
convention `2^{-⊤} = 0`. On a coerced natural it is `(2⁻¹) ^ n`, matching
`progWeight`; at `⊤` (no program, `KP = ⊤`) it is `0`. -/
noncomputable def complexityWeight : ENat → ℝ≥0∞
  | (n : Nat) => (2 : ℝ≥0∞)⁻¹ ^ n
  | ⊤ => 0

@[simp] theorem complexityWeight_top : complexityWeight ⊤ = 0 := rfl

@[simp] theorem complexityWeight_coe (n : ℕ) :
    complexityWeight (n : ENat) = (2 : ℝ≥0∞)⁻¹ ^ n := rfl

/-- The bridge to the term-level weight: the complexity weight of a program's
length is exactly its `progWeight`. Both sides are `(2⁻¹) ^ programLength p`. -/
theorem complexityWeight_programLength (p : BitString) :
    complexityWeight (programLength p : ENat) = progWeight p := rfl

/-! ### Elementary algebra of `complexityWeight`

These are pure `ENat`/`ENNReal` facts about `complexityWeight`, with no machine,
prefix-freeness, or computability content. They are the bridge from *additive*
complexity bounds (`KP U ≤ KP M + c`) to *multiplicative* weight bounds, used
when reading an optimal-prefix inequality as a statement about `2^{-KP}`. -/

/-- The complexity weight at `0` is `1` (the empty program convention). -/
@[simp] theorem complexityWeight_zero : complexityWeight (0 : ENat) = 1 := by
  rw [← Nat.cast_zero, complexityWeight_coe, pow_zero]

/-- The complexity weight is always finite: at `⊤` it is `0`, and on a coerced
natural it is a power of the finite base `2⁻¹`. -/
theorem complexityWeight_ne_top (n : ENat) : complexityWeight n ≠ ⊤ := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k => rw [complexityWeight_coe]; exact ENNReal.pow_ne_top inv_two_ne_top

/-- The complexity weight never exceeds `1` (since `2⁻¹ ≤ 1`). -/
theorem complexityWeight_le_one (n : ENat) : complexityWeight n ≤ 1 := by
  induction n using ENat.recTopCoe with
  | top => rw [complexityWeight_top]; exact bot_le
  | coe k =>
      rw [complexityWeight_coe]
      exact pow_le_one' (ENNReal.inv_le_one.mpr one_le_two) k

/-- **Additivity in the exponent.** Adding a finite cost `c` to a complexity
`n : ENat` multiplies the weight by `2^{-c}`. This is the algebraic core that
turns an additive bound `KP U x y ≤ KP M x y + c` into a multiplicative weight
bound. The `⊤` case is absorbed: `⊤ + c = ⊤` and both sides are `0`. -/
theorem complexityWeight_add_nat (n : ENat) (c : ℕ) :
    complexityWeight (n + (c : ENat))
      = complexityWeight n * ((2 : ℝ≥0∞)⁻¹ ^ c) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
      rw [← Nat.cast_add, complexityWeight_coe, complexityWeight_coe, pow_add]

/-- **Antitone in the exponent (pointwise form).** A smaller complexity yields a
larger weight: `a ≤ b` implies `2^{-b} ≤ 2^{-a}`. The `⊤` case is handled by the
`⊤ ↦ 0` convention. -/
theorem complexityWeight_le_of_le {a b : ENat} (h : a ≤ b) :
    complexityWeight b ≤ complexityWeight a := by
  induction b using ENat.recTopCoe with
  | top => rw [complexityWeight_top]; exact bot_le
  | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at h
      | coe k =>
          rw [complexityWeight_coe, complexityWeight_coe]
          exact pow_le_pow_right_of_le_one'
            (ENNReal.inv_le_one.mpr one_le_two) (by exact_mod_cast h)

/-- **Antitonicity**, packaged as `Antitone`: longer programs (larger `KP`) carry
no more weight than shorter ones. -/
theorem complexityWeight_antitone : Antitone complexityWeight :=
  fun _ _ h => complexityWeight_le_of_le h

/-! ### From multiplicative weight bounds back to additive `K` bounds

The lemmas above turn an *additive* bound on `KP` into a *multiplicative* bound on
`complexityWeight`. The Levin–Gács lower direction needs the converse: a coding
bound `2^{-c} · 2^{-m} ≤ 2^{-n}` must be read back as the additive `n ≤ m + c`.
These are pure `ENat`/`ENNReal` facts. -/

/-- The complexity weight vanishes exactly at `⊤`: on a coerced natural it is a
nonzero power of `2⁻¹`. -/
theorem complexityWeight_eq_zero_iff (n : ENat) : complexityWeight n = 0 ↔ n = ⊤ := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
      simp only [complexityWeight_coe, ENat.coe_ne_top, iff_false]
      exact pow_ne_zero k inv_two_ne_zero

/-- The complexity weight is strictly positive exactly off `⊤`. -/
theorem complexityWeight_pos_iff (n : ENat) : 0 < complexityWeight n ↔ n ≠ ⊤ := by
  rw [pos_iff_ne_zero, ne_eq, complexityWeight_eq_zero_iff]

/-- **Strict antitonicity of `2^{-·}` in the exponent.** On coerced naturals, a
larger exponent gives a strictly smaller inverse-two power. Proved directly in
`ℝ≥0∞` (which lacks the `PosMulStrictMono` instance the generic
`pow_lt_pow_right_of_lt_one₀` needs) by splitting off the surplus factor. -/
theorem inv_two_pow_strictAnti {a b : ℕ} (hab : a < b) :
    (2 : ℝ≥0∞)⁻¹ ^ b < (2 : ℝ≥0∞)⁻¹ ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have hsurplus : (2 : ℝ≥0∞)⁻¹ ^ (k + 1) < 1 :=
    lt_of_le_of_lt
      (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (Nat.le_add_left 1 k))
      (by rw [pow_one]; exact ENNReal.inv_lt_one.mpr ENNReal.one_lt_two)
  have hmul : (2 : ℝ≥0∞)⁻¹ ^ (k + 1) * (2 : ℝ≥0∞)⁻¹ ^ a
      < 1 * (2 : ℝ≥0∞)⁻¹ ^ a :=
    ENNReal.mul_lt_mul_left (pow_ne_zero a inv_two_ne_zero)
      (ENNReal.pow_ne_top inv_two_ne_top) hsurplus
  rw [one_mul] at hmul
  calc
    (2 : ℝ≥0∞)⁻¹ ^ (a + k + 1)
        = (2 : ℝ≥0∞)⁻¹ ^ (k + 1) * (2 : ℝ≥0∞)⁻¹ ^ a := by
          rw [← pow_add]; ring_nf
    _ < (2 : ℝ≥0∞)⁻¹ ^ a := hmul

/-- A `≤` between two inverse-two powers reverses to a `≤` between the exponents.
The strict companion of `pow_le_pow_right_of_le_one'`. -/
theorem inv_two_pow_exponent_le {a b : ℕ}
    (h : (2 : ℝ≥0∞)⁻¹ ^ a ≤ (2 : ℝ≥0∞)⁻¹ ^ b) : b ≤ a := by
  by_contra hlt
  push Not at hlt
  exact absurd h (not_le.mpr (inv_two_pow_strictAnti hlt))

/-- **Multiplicative-to-additive bridge.** A coding bound
`2^{-c} · complexityWeight m ≤ complexityWeight n`, with `m` finite, forces the
additive complexity bound `n ≤ m + c`. This is the single reusable converse of
`complexityWeight_le_of_le`/`complexityWeight_add_nat`: it turns every
multiplicative coding bound `2^{-c} · 2^{-m} ≤ 2^{-n}` back into `n ≤ m + c`. -/
theorem le_add_nat_of_complexityWeight_le {m n : ENat} {c : ℕ}
    (hm : m ≠ ⊤)
    (h : (2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight m ≤ complexityWeight n) :
    n ≤ m + (c : ENat) := by
  lift m to ℕ using hm with i
  rw [complexityWeight_coe, ← pow_add] at h
  have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ (c + i) :=
    ENNReal.pow_pos (pos_iff_ne_zero.mpr inv_two_ne_zero) _
  have hn : n ≠ ⊤ := (complexityWeight_pos_iff n).mp (lt_of_lt_of_le hpos h)
  lift n to ℕ using hn with j
  rw [complexityWeight_coe] at h
  have hj : j ≤ c + i := inv_two_pow_exponent_le h
  have hcast : (j : ENat) ≤ ((i + c : ℕ) : ENat) := by exact_mod_cast (by omega : j ≤ i + c)
  rwa [Nat.cast_add] at hcast

/-- **Easy coding bound, packaged.** The complexity weight `2^{-KP(x | y)}` is a
lower bound on the a priori semimeasure `m_M(x | y)`, for an arbitrary map `M`.

When no program produces `x` from `y`, `KP = ⊤` and the left side is `0`.
Otherwise the `sInf` defining `KP` is achieved by an actual program `p` of length
`KP M x y` (because `ENat` is well-ordered), and that single program already
contributes its weight to the semimeasure. -/
theorem complexityWeight_KP_le_aprioriMeasure (M : Map) (x y : BitString) :
    complexityWeight (KP M x y) ≤ aprioriMeasure M x y := by
  rcases Set.eq_empty_or_nonempty (candidateLengths M x y) with he | hne
  · -- No program produces `x`: `KP = ⊤`, so the left side is `0`.
    have htop : KP M x y = ⊤ := by rw [KP_eq_condK, condK, he, sInf_empty]
    rw [htop, complexityWeight_top]
    exact bot_le
  · -- The infimum is achieved by a genuine program of length `KP M x y`.
    have hmem : KP M x y ∈ candidateLengths M x y := by
      rw [KP_eq_condK, condK]; exact csInf_mem hne
    obtain ⟨p, hp, hlen⟩ := hmem
    rw [← hlen, complexityWeight_programLength]
    exact progWeight_le_aprioriMeasure hp

end Kolmogorov
