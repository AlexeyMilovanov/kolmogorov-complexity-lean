/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.ActualDiameterBounds

/-!
# Upper box estimates for the factorial product

Finite cylinder covers bound the covering numbers of the factorial ultrametric product.
The logarithmic cylinder count is asymptotic to the preceding factorial; bracketing arbitrary
scales between successive factorials therefore bounds the upper box dimension by one.
`ActualDiameterCounterexample` combines this bound with the Baire category lower bound for
`conf:packing-diameter-counterexample`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability

private lemma one_add_sum_factorial_le {k : ℕ} (hk : 1 ≤ k) : 1 + ∑ j ∈ Finset.Ico 1 (k + 1),
    j.factorial ≤ 3 * k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => ?_
  | succ k hk ih => ?_
  · norm_num
  · have h1 : ∑ j ∈ Finset.Ico 1 (k + 1 + 1), j.factorial = (∑ j ∈ Finset.Ico 1 (k + 1),
      j.factorial) + (k + 1).factorial := by
      apply Finset.sum_Ico_succ_top; omega
    rw [h1]
    have h2 : 1 + (∑ j ∈ Finset.Ico 1 (k + 1), j.factorial + (k + 1).factorial) = (1 + ∑ j ∈
        Finset.Ico 1 (k + 1), j.factorial) + (k + 1).factorial := by omega
    rw [h2]
    have h3 : (1 + ∑ j ∈ Finset.Ico 1 (k + 1), j.factorial) + (k + 1).factorial ≤ 3 * k.factorial +
        (k + 1).factorial := Nat.add_le_add_right ih _
    apply le_trans h3
    have h4 : (k + 1).factorial = (k + 1) * k.factorial := rfl
    have h5 : 3 * k.factorial + (k + 1).factorial = (k + 4) * k.factorial := by
      calc 3 * k.factorial + (k + 1).factorial
        _ = 3 * k.factorial + (k + 1) * k.factorial := by rw [h4]
        _ = (3 + (k + 1)) * k.factorial := by rw [← add_mul]
        _ = (k + 4) * k.factorial := by congr 1; omega
    rw [h5]
    have h7 : 3 * (k + 1).factorial = (3 * k + 3) * k.factorial := by
      calc 3 * (k + 1).factorial
        _ = 3 * ((k + 1) * k.factorial) := by rw [h4]
        _ = (3 * (k + 1)) * k.factorial := by rw [← mul_assoc]
        _ = (3 * k + 3) * k.factorial := by ring
    rw [h7]
    apply Nat.mul_le_mul_right
    omega

private lemma factorialLogCylinderCount_eq_add (n : ℕ) (hn : 3 ≤ n) : factorialLogCylinderCount n =
    (1 + ∑ j ∈ Finset.Ico 1 (n - 1), (j.factorial : ℝ)) + ((n - 1).factorial : ℝ) := by
  have h1 : factorialLogCylinderCount n = ∑ j ∈ Finset.range n, (if j = 0 then (1:ℝ) else
      (j.factorial : ℝ)) := factorialLogCylinderCount_eq_sum n
  rw [h1]
  have h_range : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
    omega
  rw [h_range]
  rw [Finset.sum_union]
  · have h2 : ∑ j ∈ {0}, (if j = 0 then (1:ℝ) else (j.factorial : ℝ)) = 1 := by simp
    rw [h2]
    have h3 : ∑ j ∈ Finset.Ico 1 n, (if j = 0 then (1:ℝ) else (j.factorial : ℝ)) = ∑ j ∈ Finset.Ico
        1 n, (j.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have : x ≠ 0 := by
        rw [Finset.mem_Ico] at hx
        omega
      simp [this]
    rw [h3]
    have h4 : Finset.Ico 1 n = Finset.Ico 1 (n - 1) ∪ {n - 1} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
      omega
    rw [h4]
    rw [Finset.sum_union]
    · have h5 : ∑ j ∈ {n - 1}, (j.factorial : ℝ) = ((n - 1).factorial : ℝ) := by simp
      rw [h5]
      abel
    · simp only [Finset.disjoint_singleton_right, Finset.mem_Ico, not_and, not_lt]
      intro h_in
      omega
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Ico, not_and, not_lt]
    intro h_in
    omega

private lemma factorialLogCylinderCount_sub_factorial_le (n : ℕ) (hn : 3 ≤ n) :
    factorialLogCylinderCount n - ((n - 1).factorial : ℝ) ≤ 3 * ((n - 2).factorial : ℝ) := by
  rw [factorialLogCylinderCount_eq_add n hn]
  have h_cancel : 1 + ∑ j ∈ Finset.Ico 1 (n - 1), (j.factorial : ℝ) + ↑(n - 1).factorial - ↑(n -
      1).factorial = 1 + ∑ j ∈ Finset.Ico 1 (n - 1), (j.factorial : ℝ) := by ring
  rw [h_cancel]
  have h_bound := one_add_sum_factorial_le (k := n - 2) (by omega)
  have h_bound_r : (1:ℝ) + ∑ j ∈ Finset.Ico 1 (n - 2 + 1), (j.factorial : ℝ) ≤ 3 * ((n -
      2).factorial : ℝ) := by
    exact_mod_cast h_bound
  have h_eq : n - 1 = n - 2 + 1 := by omega
  rw [h_eq]
  exact h_bound_r

private lemma factorial_le_factorialLogCylinderCount (n : ℕ) (hn : 2 ≤ n) : ((n - 1).factorial : ℝ)
    ≤ factorialLogCylinderCount n := by
  have h1 : factorialLogCylinderCount n = ∑ j ∈ Finset.range n, (if j = 0 then (1:ℝ) else
      (j.factorial : ℝ)) := factorialLogCylinderCount_eq_sum n
  rw [h1]
  have h_range : Finset.range n = Finset.range (n - 1) ∪ {n - 1} := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
    omega
  rw [h_range]
  rw [Finset.sum_union]
  · have h2 : ∑ j ∈ {n - 1}, (if j = 0 then (1:ℝ) else (j.factorial : ℝ)) = ((n - 1).factorial : ℝ)
      := by
      have : n - 1 ≠ 0 := by omega
      simp [this]
    rw [h2]
    have h3 : 0 ≤ ∑ j ∈ Finset.range (n - 1), (if j = 0 then (1:ℝ) else (j.factorial : ℝ)) := by
      apply Finset.sum_nonneg
      intro x _
      split_ifs
      · norm_num
      · positivity
    linarith
  · simp only [Finset.disjoint_singleton_right, Finset.mem_range, not_lt]
    omega

private lemma tendsto_three_div_nat_sub_one : Tendsto (fun n : ℕ ↦ (3 : ℝ) / ((n - 1 : ℕ) : ℝ))
    atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun x : ℝ ↦ 3 * x⁻¹) atTop (𝓝 (3 * 0)) := Tendsto.const_mul 3 h1
  have h3 : (fun x : ℝ ↦ 3 * x⁻¹) = (fun x : ℝ ↦ 3 / x) := by
    ext x
    exact div_eq_mul_inv 3 x |>.symm
  rw [h3, mul_zero] at h2
  have h4 : Tendsto (fun n : ℕ ↦ (n : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  have h5 : (fun n : ℕ ↦ (3 : ℝ) / ((n : ℝ) - 1)) =ᶠ[atTop] (fun n : ℕ ↦ (3 : ℝ) / ((n - 1 : ℕ) :
      ℝ)) := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    have h_le : 1 ≤ n := hn
    dsimp only
    rw [Nat.cast_sub h_le]
    push_cast
    rfl
  exact Tendsto.congr' h5 (Tendsto.comp h2 h4)

/-- The logarithmic cylinder count is asymptotic to the factorial of the preceding depth. -/
lemma factorialLogCylinderCount_div_factorial_tendsto : Tendsto (fun n : ℕ ↦
    factorialLogCylinderCount n / ((n - 1).factorial : ℝ)) atTop (𝓝 1) := by
  have h_bound : ∀ᶠ (n : ℕ) in atTop, |factorialLogCylinderCount n / ((n - 1).factorial : ℝ) - 1| ≤
      (3 : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    apply eventually_atTop.mpr
    use 3
    intro n hn
    have h1 : ((n - 1).factorial : ℝ) ≤ factorialLogCylinderCount n :=
        factorial_le_factorialLogCylinderCount n (by omega)
    have h2 : factorialLogCylinderCount n - ((n - 1).factorial : ℝ) ≤ 3 * ((n - 2).factorial : ℝ) :=
        factorialLogCylinderCount_sub_factorial_le n (by omega)
    have h_pos : (0:ℝ) < ((n - 1).factorial : ℝ) := by positivity
    rw [abs_le]
    constructor
    · have h_left : 0 ≤ factorialLogCylinderCount n / ((n - 1).factorial : ℝ) - 1 := by
        rw [sub_nonneg, one_le_div₀ h_pos]
        exact h1
      have h_right : 0 ≤ (3 : ℝ) / ((n - 1 : ℕ) : ℝ) := by
        apply div_nonneg (by norm_num)
        have h_n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        positivity
      linarith
    · have h3 : factorialLogCylinderCount n / ((n - 1).factorial : ℝ) - 1 =
        (factorialLogCylinderCount n - ((n - 1).factorial : ℝ)) / ((n - 1).factorial : ℝ) := by
        have : (1:ℝ) = ((n - 1).factorial : ℝ) / ((n - 1).factorial : ℝ) := (div_self (ne_of_gt
            h_pos)).symm
        rw [this, sub_div]
      rw [h3]
      apply div_le_div_of_nonneg_right h2 (le_of_lt h_pos) |>.trans
      have h4 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
        have : n - 1 = n - 2 + 1 := by omega
        calc (n - 1).factorial
          _ = (n - 2 + 1).factorial := by rw [← this]
          _ = (n - 2 + 1) * (n - 2).factorial := rfl
          _ = (n - 1) * (n - 2).factorial := by congr 1; omega
      have h4_r : ((n - 1).factorial : ℝ) = ((n - 1 : ℕ) : ℝ) * ((n - 2).factorial : ℝ) := by
          exact_mod_cast h4
      rw [h4_r]
      have h_fact_pos : (0:ℝ) < ((n - 2).factorial : ℝ) := by positivity
      rw [mul_div_mul_right 3 _ (ne_of_gt h_fact_pos)]
  have h_lim : Tendsto (fun n : ℕ ↦ factorialLogCylinderCount n / ((n - 1).factorial : ℝ) - 1) atTop
      (𝓝 0) := by
    apply squeeze_zero_norm' h_bound tendsto_three_div_nat_sub_one
  have h_res : (fun n : ℕ ↦ factorialLogCylinderCount n / ((n - 1).factorial : ℝ)) = (fun n : ℕ ↦
      factorialLogCylinderCount n / ((n - 1).factorial : ℝ) - 1 + 1) := by
    ext n; ring
  rw [h_res]
  have h_add := Tendsto.add_const 1 h_lim
  rw [zero_add] at h_add
  exact h_add

/-- For each k >= 1, choose the least n >= 2 with k < n!. -/
private lemma exists_factorial_bracketing (k : ℕ) (hk : 1 ≤ k) :
    ∃ n : ℕ, 2 ≤ n ∧ (n - 1).factorial ≤ k ∧ k < n.factorial := by
  have H : ∃ m, 2 ≤ m ∧ k < m.factorial := by
    use k + 2
    constructor
    · omega
    · have h1 : k + 2 ≤ (k + 2).factorial := Nat.self_le_factorial (k + 2)
      omega
  let n := Nat.find H
  have hn := Nat.find_spec H
  use n
  refine ⟨hn.1, ?_, hn.2⟩
  by_cases hn2 : n = 2
  · rw [hn2]
    norm_num
    exact hk
  · have hn_gt : 2 < n := by omega
    have h_min := Nat.find_min H (show n - 1 < n by omega)
    push Not at h_min
    have hn_sub : 2 ≤ n - 1 := by omega
    exact h_min hn_sub

/-- Bound the rate. -/
private lemma factorialProduct_pressureRate_le
    (m : MetricSpace FactorialProduct)
    (h_cover : ∀ n k : ℕ, 2 ≤ n → (n - 1).factorial ≤ k → k < n.factorial →
      partitionSum id (fun _ ↦ (0 : ℝ)) .centered (Set.univ : Set FactorialProduct) 1 (dyadicRadius
          k) ≤
        (factorialCylinderCount n : ℝ≥0∞))
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn1 : 2 ≤ n) (hn2 : (n - 1).factorial ≤ k) (hn3 : k < n.factorial)
        :
    (pressureRate (fun k ↦ partitionSum id (fun _ : FactorialProduct ↦ 0) .centered (Set.univ : Set
        FactorialProduct) 1 (dyadicRadius k)) k).toENNReal ≤
    ENNReal.ofReal (factorialLogCylinderCount n / ((n - 1).factorial : ℝ)) := by
  let q := fun k ↦ partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ)) .centered (Set.univ : Set
      FactorialProduct) 1 (dyadicRadius k)
  have hk0 : k ≠ 0 := by omega
  have H_Nn_pos : 1 ≤ factorialCylinderCount n := by
    unfold factorialCylinderCount
    apply Finset.one_le_prod
    intro j hj
    unfold factorialBranching
    split_ifs
    · norm_num
    · have h_pow : 1 ≤ 2 ^ j.factorial := Nat.one_le_two_pow
      exact h_pow
  have H_log_q : ENNReal.log (q k) ≤ (Real.log (factorialCylinderCount n) : EReal) := by
    have h1 : ENNReal.log (q k) ≤ ENNReal.log (factorialCylinderCount n) := by
      apply ENNReal.log_le_log
      exact h_cover n k hn1 hn2 hn3
    have h2 : ENNReal.log (factorialCylinderCount n) = (Real.log (factorialCylinderCount n) : EReal)
        := by
      apply ENNReal.log_pos_real
      · intro h_zero
        have : (1 : ℝ≥0∞) ≤ 0 := by
          calc (1 : ℝ≥0∞) ≤ (factorialCylinderCount n : ℝ≥0∞) := by
                exact_mod_cast H_Nn_pos
            _ = 0 := h_zero
        have hz : (0 : ℝ≥0∞) < 1 := by norm_num
        exact not_le.mpr hz this
      · exact ENNReal.natCast_ne_top _
    rwa [h2] at h1
  have h_rate_le : pressureRate q k ≤ ((factorialLogCylinderCount n / (k : ℝ) : ℝ) : EReal) := by
    dsimp [pressureRate, q]
    rw [ite_eq_right hk0, pressureLog]
    have h_mul1 : ENNReal.log (partitionSum id (fun _ : FactorialProduct ↦ 0) .centered Set.univ 1
        (dyadicRadius k)) * ((Real.log 2)⁻¹ : ℝ) ≤ (Real.log (factorialCylinderCount n) : EReal) *
        ((Real.log 2)⁻¹ : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact H_log_q
      · exact EReal.coe_nonneg.mpr (by positivity)
    have h_mul2 : ENNReal.log (partitionSum id (fun _ : FactorialProduct ↦ 0) .centered Set.univ 1
        (dyadicRadius k)) * ((Real.log 2)⁻¹ : ℝ) * ((k : ℝ)⁻¹ : ℝ) ≤ (Real.log
        (factorialCylinderCount n) : EReal) * ((Real.log 2)⁻¹ : ℝ) * ((k : ℝ)⁻¹ : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact h_mul1
      · exact EReal.coe_nonneg.mpr (by positivity)
    have h_eq : (Real.log (factorialCylinderCount n) : EReal) * ((Real.log 2)⁻¹ : ℝ) * ((k : ℝ)⁻¹ :
        ℝ) = ((factorialLogCylinderCount n / (k : ℝ) : ℝ) : EReal) := by
      unfold factorialLogCylinderCount
      rw [← EReal.coe_mul, ← EReal.coe_mul]
      apply congrArg (fun x : ℝ ↦ (x : EReal))
      ring
    rwa [h_eq] at h_mul2
  have h_toENNReal : (pressureRate q k).toENNReal ≤ ENNReal.ofReal (factorialLogCylinderCount n / (k
      : ℝ)) := by
    have h1 := EReal.toENNReal_le_toENNReal h_rate_le
    have h2 := EReal.real_coe_toENNReal (factorialLogCylinderCount n / (k : ℝ))
    have h1_eq : ((factorialLogCylinderCount n / (k : ℝ) : ℝ) : EReal).toENNReal = ENNReal.ofReal
        (factorialLogCylinderCount n / (k : ℝ)) := h2
    rwa [h1_eq] at h1
  apply le_trans h_toENNReal
  apply ENNReal.ofReal_le_ofReal
  have h_Ln_pos : 0 ≤ factorialLogCylinderCount n := by
    unfold factorialLogCylinderCount
    apply div_nonneg
    · apply Real.log_nonneg
      have h_cast : (1 : ℝ) ≤ (factorialCylinderCount n : ℝ) := by
        exact_mod_cast H_Nn_pos
      exact h_cast
    · apply Real.log_nonneg (by norm_num)
  apply div_le_div_of_nonneg_left h_Ln_pos
  · positivity
  · have h_fact : ((n - 1).factorial : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hn2
    exact h_fact

/-- Upper bound the limsup. -/
private lemma limsup_le_of_factorial_bracketing
    (f : ℕ → ℝ≥0∞)
    (h_bound : ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 2 ≤ n ∧ (n - 1).factorial ≤ k ∧ k < n.factorial ∧ f k ≤
        ENNReal.ofReal (factorialLogCylinderCount n / ((n - 1).factorial : ℝ))) :
    limsup f atTop ≤ 1 := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.mpr hε
  have h_ev : ∀ᶠ n : ℕ in atTop,
      factorialLogCylinderCount n / ((n - 1).factorial : ℝ) < 1 + (ε : ℝ) :=
    factorialLogCylinderCount_div_factorial_tendsto.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  apply limsup_le_of_le (by isBoundedDefault)
  rw [eventually_atTop]
  refine ⟨max 1 N.factorial, fun k hk ↦ ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hkN : N.factorial ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨n, hn2, hn3, hn4, hfk⟩ := h_bound k hk1
  have hnN : N ≤ n := by
    by_contra hlt
    have hlt' : n < N := not_le.mp hlt
    have : n.factorial ≤ N.factorial := Nat.factorial_le hlt'.le
    omega
  calc f k ≤ ENNReal.ofReal (factorialLogCylinderCount n / ((n - 1).factorial : ℝ)) := hfk
    _ ≤ ENNReal.ofReal (1 + (ε : ℝ)) := ENNReal.ofReal_le_ofReal (hN n hnN).le
    _ = 1 + ε := by
      rw [ENNReal.ofReal_add zero_le_one ε.coe_nonneg]
      simp

/-- The upper box dimension is bounded by 1, using the limits. -/
private lemma upperBoxDimension_le_of_factorial_cover
    (m : MetricSpace FactorialProduct)
    (h_cover : ∀ n k : ℕ, 2 ≤ n → (n - 1).factorial ≤ k → k < n.factorial →
      partitionSum id (fun _ ↦ (0 : ℝ)) .centered (Set.univ : Set FactorialProduct) 1 (dyadicRadius
          k) ≤
        (factorialCylinderCount n : ℝ≥0∞)) :
    upperBoxDimension (Set.univ : Set FactorialProduct) ≤ 1 := by
  dsimp [upperBoxDimension]
  let f := fun k ↦ (pressureRate (fun k' ↦ partitionSum id (fun _ : FactorialProduct ↦ 0) .centered
      Set.univ 1 (dyadicRadius k')) k).toENNReal
  apply limsup_le_of_factorial_bracketing f
  intro k hk
  rcases exists_factorial_bracketing k hk with ⟨n, hn1, hn2, hn3⟩
  use n, hn1, hn2, hn3
  exact factorialProduct_pressureRate_le m h_cover k hk n hn1 hn2 hn3

/-- The upper box dimension of the whole space `Y` is at most 1. -/
lemma factorialProduct_upperBoxDimension_le_one
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n) :
    upperBoxDimension (Set.univ : Set FactorialProduct) ≤ 1 := by
  have H1 := fun n k hn (_ : (n - 1).factorial ≤ k) hk ↦
    factorialProduct_partitionSum_le m h_dist n k hn hk
  have H3 := upperBoxDimension_le_of_factorial_cover m H1
  exact H3

end Kolmogorov.PointToSet
