/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

/-!
# A geometric deficit moment

The absolute constant is quantified before the model-complexity parameter.

Blueprint nodes: `enum:poly-moment`, `exp:geometric`.
-/

namespace Kolmogorov.MDLPrediction

/-- A geometric first moment is linear in the base parameter.
Blueprint node `exp:geometric`. -/
theorem exp_geometric :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      Summable (fun d : ℕ =>
        ((k + d + 1 : ℕ) : ℝ) * 2 ^ (-(d : ℝ) / 2)) ∧
      (∑' d : ℕ, ((k + d + 1 : ℕ) : ℝ) * 2 ^ (-(d : ℝ) / 2)) ≤
        C * (k + 1) := by
  have H : ‖(2 : ℝ) ^ (-(1 : ℝ) / 2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num)]
    left
    refine ⟨by norm_num, by norm_num⟩
  have H_pos : 0 < (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 H
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 0 H
  simp only [pow_one, pow_zero, one_mul] at h1 h2
  let sum1 := ∑' d : ℕ, (d : ℝ) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d
  let sum2 := ∑' d : ℕ, ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d
  let C := sum1 + sum2
  have hC : C = ∑' d : ℕ, ((d : ℝ) + 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d := by
    dsimp [C, sum1, sum2]
    rw [← Summable.tsum_add h1 h2]
    congr 1
    ext d
    ring
  have h3 : Summable (fun d : ℕ => ((d : ℝ) + 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d) := by
    exact h1.add h2 |>.congr (fun d => by ring)
  have H1 : 0 < C := by
    rw [hC]
    have ht : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 0 := by norm_num
    have h_nonneg : ∀ d : ℕ, (0 : ℝ) ≤ ((d : ℝ) + 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d := by
      intro d
      have : (0:ℝ) < ((d : ℝ) + 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d := by
        apply mul_pos
        · have h_cast_nonneg : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith
        · apply pow_pos H_pos
      exact this.le
    have H_sum_pos := Summable.tsum_pos h3 h_nonneg 0 ht
    exact H_sum_pos
  use C
  constructor
  · exact H1
  · intro k
    have h_pow (d : ℕ) : (2 : ℝ) ^ (-(d : ℝ) / 2) = ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have h4 : Summable (fun d : ℕ =>
      ((k : ℝ) + ((d : ℝ) + 1)) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d) := by
      have hk : Summable (fun d : ℕ => (k : ℝ) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d) := by
        exact Summable.mul_left (k : ℝ) h2
      exact hk.add h3 |>.congr (fun d : ℕ => by ring)
    have H_sum : Summable (fun d : ℕ => ((k + d + 1 : ℕ) : ℝ) * 2 ^ (-(d : ℝ) / 2)) := by
      refine Summable.congr h4 (fun d => ?_)
      rw [h_pow d]
      push_cast
      ring
    constructor
    · exact H_sum
    · have H_eq : ∑' d : ℕ, ((k + d + 1 : ℕ) : ℝ) * 2 ^ (-(d : ℝ) / 2) =
        ∑' d : ℕ, ((k : ℝ) + ((d : ℝ) + 1)) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d := by
        apply tsum_congr; intro d; rw [h_pow d]; push_cast
        ring
      rw [H_eq]
      have hk : Summable (fun d : ℕ => (k : ℝ) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d) := by
        exact Summable.mul_left (k : ℝ) h2
      have H_eq2 : ∑' d : ℕ, ((k : ℝ) + ((d : ℝ) + 1)) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d =
        ∑' d : ℕ, ((k : ℝ) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d +
          ((d : ℝ) + 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d) := by
        apply tsum_congr; intro d; ring
      rw [H_eq2, Summable.tsum_add hk h3, tsum_mul_left, ← hC]
      have h_sum2_le : ∑' d : ℕ, ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d ≤ C := by
        have H_sum2_eq : ∑' d : ℕ, ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d = sum2 := by rfl
        rw [H_sum2_eq]
        have H_sum1_pos : 0 ≤ sum1 := by
          apply tsum_nonneg; intro d
          apply mul_nonneg (Nat.cast_nonneg d) (le_of_lt (pow_pos H_pos _))
        change sum2 ≤ sum1 + sum2
        linarith
      have hk2 : (k : ℝ) * C + C = C * (k + 1) := by ring
      rw [← hk2]
      have H_calc : (k : ℝ) * ∑' (d : ℕ), ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d + C ≤
        (k : ℝ) * C + C := by
        have hk_nonneg : 0 ≤ (k : ℝ) := by exact Nat.cast_nonneg k
        have h_sum2_le' : ∑' (d : ℕ), ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ d ≤ C := h_sum2_le
        nlinarith
      exact H_calc


/-- The sum `k + d + 1` is bounded by the product of the corresponding successors. -/
private lemma add_one_le_mul_add_one
    (k d : ℕ) :
    ((k + d + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) := by
  norm_cast
  nlinarith [Nat.zero_le (k * d)]

/-- The successor product bound persists after taking a natural power. -/
private lemma add_one_pow_le_mul
    (k d e : ℕ) :
    ((k + d + 1 : ℕ) : ℝ) ^ e ≤ ((k + 1 : ℕ) : ℝ) ^ e * ((d + 1 : ℕ) : ℝ) ^ e := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact add_one_le_mul_add_one k d

/-- Geometric decay makes every shifted polynomial power summable. -/
private lemma summable_geometric_poly
    (e : ℕ) :
    Summable (fun d : ℕ => (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one e (r := (2 : ℝ)⁻¹) (by norm_num)
  have h1 := (summable_nat_add_iff 1).mpr h
  refine (h1.mul_left 2).congr fun d => ?_
  push_cast
  ring

/-- Exponential decay has every polynomial moment, uniformly after factoring
the base parameter. Blueprint node `enum:poly-moment`. -/
theorem enum_poly_moment (e : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      Summable (fun d : ℕ =>
        (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e) ∧
      (∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e) ≤
        C * ((k + 1 : ℕ) : ℝ) ^ e := by
  use (∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) + 1
  refine ⟨?_, fun k => ⟨?_, ?_⟩⟩
  · have hsum : Summable (fun d : ℕ => (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) :=
      summable_geometric_poly e
    have hsum_pos : 0 ≤ ∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e := by
      apply tsum_nonneg
      intro d
      apply mul_nonneg
      · positivity
      · positivity
    linarith
  · apply Summable.of_nonneg_of_le
    · intro b
      apply mul_nonneg
      · positivity
      · positivity
    · intro d
      calc
        (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e ≤
          (2 : ℝ)⁻¹ ^ d * (((k + 1 : ℕ) : ℝ) ^ e * ((d + 1 : ℕ) : ℝ) ^ e) := by
          gcongr
          exact add_one_pow_le_mul k d e
        _ = ((k + 1 : ℕ) : ℝ) ^ e * ((2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) := by ring
    · apply Summable.mul_left
      exact summable_geometric_poly e
  · calc
      (∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e) ≤
          ∑' d : ℕ, ((k + 1 : ℕ) : ℝ) ^ e * ((2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) := by
        apply Summable.tsum_le_tsum
        · intro d
          calc
            (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e ≤
          (2 : ℝ)⁻¹ ^ d * (((k + 1 : ℕ) : ℝ) ^ e * ((d + 1 : ℕ) : ℝ) ^ e) := by
              gcongr
              exact add_one_pow_le_mul k d e
            _ = ((k + 1 : ℕ) : ℝ) ^ e * ((2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) := by ring
        · apply Summable.of_nonneg_of_le
          · intro b
            apply mul_nonneg
            · positivity
            · positivity
          · intro d
            calc
              (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e ≤
          (2 : ℝ)⁻¹ ^ d * (((k + 1 : ℕ) : ℝ) ^ e * ((d + 1 : ℕ) : ℝ) ^ e) := by
                gcongr
                exact add_one_pow_le_mul k d e
              _ = ((k + 1 : ℕ) : ℝ) ^ e * ((2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) := by ring
          · apply Summable.mul_left
            exact summable_geometric_poly e
        · apply Summable.mul_left
          exact summable_geometric_poly e
      _ = ((k + 1 : ℕ) : ℝ) ^ e * ∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e := by
        exact tsum_mul_left
      _ ≤
        ((k + 1 : ℕ) : ℝ) ^ e * ((∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) + 1) := by
        gcongr
        linarith
      _ = ((∑' d : ℕ, (2 : ℝ)⁻¹ ^ d * ((d + 1 : ℕ) : ℝ) ^ e) + 1) * ((k + 1 : ℕ) : ℝ) ^ e := by ring

end Kolmogorov.MDLPrediction
