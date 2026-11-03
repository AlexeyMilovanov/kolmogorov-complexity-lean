/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Analysis.LogGap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Product inequalities for conditional discrepancies

Taking binary logarithms of positive finite products bounds the sum of mean gaps.
The concavity estimate then turns the gap sum into a squared-error bound.

Blueprint nodes: `exp:product`, `exp:product-logs`.
-/

namespace Kolmogorov.MDLPrediction

open scoped BigOperators

/-- A product comparison bounds the sum of logarithmic mean gaps.
Blueprint node `exp:product-logs`. -/
theorem exp_product_logs (n : ℕ) (p q : Fin n → ℝ) (c : ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (hc : 1 ≤ c)
    (hprod : (∏ i, (p i + q i) / 2) ^ 2 ≤
      c * (∏ i, p i) * (∏ i, q i)) :
    (∑ i, (Real.logb 2 ((p i + q i) / 2) -
      (Real.logb 2 (p i) + Real.logb 2 (q i)) / 2)) ≤
        Real.logb 2 c / 2 := by
  have hc_pos : 0 < c := by linarith
  have hp_prod_pos : 0 < ∏ i : Fin n, p i := Finset.prod_pos (fun i _ => hp i)
  have hq_prod_pos : 0 < ∏ i : Fin n, q i := Finset.prod_pos (fun i _ => hq i)
  have h_rhs_pos : 0 < c * (∏ i : Fin n, p i) * (∏ i : Fin n, q i) := by positivity
  have h_lhs_pos : 0 < (∏ i : Fin n, (p i + q i) / 2) ^ 2 := by
    have h_prod : 0 < ∏ i : Fin n, (p i + q i) / 2 := by
      apply Finset.prod_pos
      intro i _
      have hp_i := hp i
      have hq_i := hq i
      linarith
    positivity
  have h1 : Real.logb 2 ((∏ i, (p i + q i) / 2) ^ 2) ≤
      Real.logb 2 (c * (∏ i, p i) * (∏ i, q i)) := by
    rwa [Real.logb_le_logb (by norm_num) h_lhs_pos h_rhs_pos]
  have h2 : Real.logb 2 ((∏ i, (p i + q i) / 2) ^ 2) =
      2 * Real.logb 2 (∏ i, (p i + q i) / 2) := by
    rw [Real.logb_pow]; rfl
  have h3 : Real.logb 2 (c * (∏ i, p i) * (∏ i, q i)) =
      Real.logb 2 c + Real.logb 2 (∏ i, p i) + Real.logb 2 (∏ i, q i) := by
    rw [Real.logb_mul (by positivity) hq_prod_pos.ne', Real.logb_mul hc_pos.ne' hp_prod_pos.ne']
  have h4 : Real.logb 2 (∏ i : Fin n, p i) = ∑ i : Fin n, Real.logb 2 (p i) := by
    apply Real.logb_prod
    intro i _
    exact (hp i).ne'
  have h5 : Real.logb 2 (∏ i : Fin n, q i) = ∑ i : Fin n, Real.logb 2 (q i) := by
    apply Real.logb_prod
    intro i _
    exact (hq i).ne'
  have h6 : Real.logb 2 (∏ i : Fin n, (p i + q i) / 2) =
      ∑ i : Fin n, Real.logb 2 ((p i + q i) / 2) := by
    apply Real.logb_prod
    intro i _
    have hp_i := hp i
    have hq_i := hq i
    linarith
  rw [h2, h3, h4, h5, h6] at h1
  -- Now we need to rearrange h1 into the target form
  calc (∑ i : Fin n, (Real.logb 2 ((p i + q i) / 2) - (Real.logb 2 (p i) + Real.logb 2 (q i)) / 2))
    _ = ∑ i : Fin n, (Real.logb 2 ((p i + q i) / 2) -
        (Real.logb 2 (p i) / 2 + Real.logb 2 (q i) / 2)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin n, Real.logb 2 ((p i + q i) / 2) -
        ∑ i : Fin n, (Real.logb 2 (p i) / 2 + Real.logb 2 (q i) / 2) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ i : Fin n, Real.logb 2 ((p i + q i) / 2) -
        (∑ i : Fin n, Real.logb 2 (p i) / 2 + ∑ i : Fin n, Real.logb 2 (q i) / 2) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin n, Real.logb 2 ((p i + q i) / 2) -
        ((∑ i : Fin n, Real.logb 2 (p i)) / 2 + (∑ i : Fin n, Real.logb 2 (q i)) / 2) := by
      have hd1 : ∑ i : Fin n, Real.logb 2 (p i) / 2 = (∑ i : Fin n, Real.logb 2 (p i)) / 2 := by
        exact (Finset.sum_div (Finset.univ) (fun i => Real.logb 2 (p i)) 2).symm
      have hd2 : ∑ i : Fin n, Real.logb 2 (q i) / 2 = (∑ i : Fin n, Real.logb 2 (q i)) / 2 := by
        exact (Finset.sum_div (Finset.univ) (fun i => Real.logb 2 (q i)) 2).symm
      rw [hd1, hd2]
    _ = (2 * ∑ i : Fin n, Real.logb 2 ((p i + q i) / 2) -
        (∑ i : Fin n, Real.logb 2 (p i) + ∑ i : Fin n, Real.logb 2 (q i))) / 2 := by
      ring
    _ ≤ Real.logb 2 c / 2 := by linarith


/-- The product comparison bounds total squared discrepancy.
Blueprint node `exp:product`. -/
theorem sum_sq_le_of_mean_product (n : ℕ) (p q : Fin n → ℝ) (c : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hq : ∀ i, 0 < q i ∧ q i ≤ 1) (hc : 1 ≤ c)
    (hprod : (∏ i, (p i + q i) / 2) ^ 2 ≤
      c * (∏ i, p i) * (∏ i, q i)) :
    (∑ i, (p i - q i) ^ 2) ≤ 4 * Real.log 2 * Real.logb 2 c := by
  have H1 := exp_product_logs n p q c (fun i => (hp i).1) (fun i => (hq i).1) hc hprod
  have H2 : ∀ i, (p i - q i) ^ 2 / (8 * Real.log 2) ≤
    Real.logb 2 ((p i + q i) / 2) - (Real.logb 2 (p i) + Real.logb 2 (q i)) / 2 := by
    intro i
    exact log_mean_gap_ge_sq (hp i) (hq i)
  have H3 : ∑ i, (p i - q i) ^ 2 / (8 * Real.log 2) ≤
      ∑ i, (Real.logb 2 ((p i + q i) / 2) -
        (Real.logb 2 (p i) + Real.logb 2 (q i)) / 2) := by
    apply Finset.sum_le_sum
    intro i _
    exact H2 i
  have H4 : ∑ i, (p i - q i) ^ 2 / (8 * Real.log 2) ≤ Real.logb 2 c / 2 :=
    le_trans H3 H1
  have H5 : (∑ i, (p i - q i) ^ 2) / (8 * Real.log 2) =
      ∑ i, (p i - q i) ^ 2 / (8 * Real.log 2) := by
    exact Finset.sum_div (Finset.univ) (fun i => (p i - q i) ^ 2) (8 * Real.log 2)
  rw [← H5] at H4
  have h_pos : 0 < 8 * Real.log 2 := by
    positivity
  have H6 := (div_le_iff₀ h_pos).mp H4
  linarith

end Kolmogorov.MDLPrediction
