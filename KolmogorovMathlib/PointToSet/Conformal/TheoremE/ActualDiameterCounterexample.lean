/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.FactorialBoxBounds

/-!
# Actual-diameter and specified-radius packing dimensions differ

The factorial product has modified upper box dimension one: finite cylinder covers give the
upper bound, while factorial-scale covering estimates and the Baire category theorem give
the lower bound. Together with the vanishing actual-diameter dimension from
`ActualDiameterBounds`, this proves the compact ultrametric counterexample re-exported by
`Conformal.TheoremE` (`conf:packing-diameter-counterexample`).
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Every nonempty open set of the factorial product contains a ball of some scale
`factorialScale q`, i.e. a cylinder. -/
private lemma exists_factorial_ball_subset_of_isOpen
    (m : MetricSpace FactorialProduct)
    (U : Set FactorialProduct) (h_open : IsOpen U) (h_ne : U.Nonempty) :
    ∃ x ∈ U, ∃ q : ℕ, Metric.ball x (factorialScale q) ⊆ U := by
  obtain ⟨x, hx⟩ := h_ne
  obtain ⟨ε, hε, h_ball⟩ := Metric.isOpen_iff.mp h_open x hx
  obtain ⟨N, hN⟩ := factorialScale_eventually_lt ε hε
  refine ⟨x, hx, N, fun y hy ↦ h_ball (Metric.mem_ball.mpr ?_)⟩
  exact lt_trans (Metric.mem_ball.mp hy) (hN N (le_refl N))

private lemma prod_factorialBranching_div_eq
    (q n : ℕ) (hn : q + 1 < n) :
    ((Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ≥0∞))) /
      (Finset.prod (Finset.range (q + 1)) (fun j ↦ (factorialBranching j : ℝ≥0∞)))) =
      ((∏ j ∈ Finset.Ico (q + 1) n, factorialBranching j : ℕ) : ℝ≥0∞) := by
  have hbn : ∀ j, (factorialBranching j : ℝ≥0∞) ≠ 0 := fun j ↦ by
    have : 0 < factorialBranching j := by
      by_cases h : j = 0 <;> simp [factorialBranching, h]
    exact_mod_cast this.ne'
  rw [← Finset.prod_range_mul_prod_Ico _ hn.le, mul_comm]
  rw [ENNReal.mul_div_cancel_right (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hbn j)
    (ENNReal.prod_ne_top fun j _ ↦ ENNReal.natCast_ne_top _)]
  push_cast
  rfl

private lemma dyadicRadius_factorial_le_scale
    (n : ℕ) (hn : 1 ≤ n - 1) :
    dyadicRadius ((n - 1).factorial) ≤ factorialScale (n - 1) := by
  have h0 : n - 1 ≠ 0 := by omega
  unfold dyadicRadius factorialScale
  simp only [h0, ↓reduceIte, one_div, le_refl]

/-- If `U` contains the ball of scale `q` around `x`, its covering number at the radius of
depth `n` is at least the number of depth-`n` cylinders inside that ball. -/
private lemma factorialProduct_partitionSum_ge
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (U : Set FactorialProduct)
    (x : FactorialProduct) (q : ℕ)
    (hq : Metric.ball x (factorialScale q) ⊆ U)
    (n : ℕ) (hn : q + 1 < n) :
    ((Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ≥0∞))) /
      (Finset.prod (Finset.range (q + 1)) (fun j ↦ (factorialBranching j : ℝ≥0∞)))) ≤
    partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ)) .centered U 1 (dyadicRadius ((n -
        1).factorial)) := by
  classical
  have hr_pos : 0 < dyadicRadius ((n - 1).factorial) := by
    unfold dyadicRadius
    positivity
  rw [packingEqModifiedUpperBox_open_covering U _ hr_pos,
    prod_factorialBranching_div_eq q n hn]
  have hρ := dyadicRadius_factorial_le_scale
    n (by omega)
  set ρ := dyadicRadius ((n - 1).factorial) with hρdef
  set I := Finset.Ico (q + 1) n with hI
  let p : (∀ j : I, Fin (factorialBranching j)) →
      FactorialProduct :=
    fun a k ↦ if h : k ∈ I then a ⟨k, h⟩ else x k
  -- every point `p a` lies in the ball `B(x, rn q)`
  have hpU : ∀ a, p a ∈ U := by
    intro a
    apply hq
    rw [Metric.mem_ball]
    by_cases hax : p a = x
    · rw [hax, dist_self]
      exact factorialScale_pos q
    · have hex : ∃ k, p a k ≠ x k := Function.ne_iff.mp hax
      have hm : ∀ k < Nat.find hex, p a k = x k := fun k hk ↦ not_not.mp (Nat.find_min hex hk)
      rw [h_dist (p a) x _ hm (Nat.find_spec hex)]
      apply factorialScale_strictAnti
      by_contra hle
      apply Nat.find_spec hex
      have hnot : Nat.find hex ∉ I := by
        rw [hI, Finset.mem_Ico]
        omega
      simp only [p, hnot, ↓reduceDIte]
  -- distinct tuples give points at distance at least `ρ`
  have hsep : ∀ a b, a ≠ b → ρ ≤ dist (p a) (p b) := by
    intro a b hab
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
    have hpj : p a j ≠ p b j := by
      simp only [p, j.2, ↓reduceDIte]
      exact hj
    have hex : ∃ k, p a k ≠ p b k := ⟨j, hpj⟩
    have hm : ∀ k < Nat.find hex, p a k = p b k := fun k hk ↦ not_not.mp (Nat.find_min hex hk)
    rw [h_dist (p a) (p b) _ hm (Nat.find_spec hex)]
    refine hρ.trans (factorialScale_antitone ?_)
    have hjI : (j : ℕ) < n := (Finset.mem_Ico.mp j.2).2
    have := Nat.find_min' hex hpj
    omega
  refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
  have hcov : ∀ a, ∃ c ∈ F, p a ∈ Metric.ball c ρ := by
    intro a
    have := hF (hpU a)
    simpa only [Set.mem_iUnion, exists_prop] using this
  choose c hcF hcb using hcov
  have hinj : Function.Injective c := by
    intro a b hab
    by_contra hne
    have h1 := hsep a b hne
    have h2 : dist (p a) (p b) < ρ := by
      calc dist (p a) (p b) ≤ max (dist (p a) (c a)) (dist (c a) (p b)) := h_ultra _ _ _
        _ < ρ := by
          apply max_lt
          · exact Metric.mem_ball.mp (hcb a)
          · rw [hab, dist_comm]
            exact Metric.mem_ball.mp (hcb b)
    linarith
  have hsub : ((Finset.univ.image c : Finset FactorialProduct) :
      Set FactorialProduct) ⊆ F := by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨a, rfl⟩ := hy
    exact hcF a
  have hcard : (Finset.univ.image c).card = ∏ j ∈ I, factorialBranching j := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact Finset.prod_coe_sort I (fun j ↦ factorialBranching j)
  have hle : (((∏ j ∈ I, factorialBranching j : ℕ)) : ℕ∞) ≤ F.encard := by
    rw [← hcard, ← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_le_encard hsub
  have := ENat.toENNReal_le.mpr hle
  simpa only [ENat.toENNReal_coe] using this

/-- Cylinder-counting lower bounds on the covering numbers of `U` at the factorial scales force
the upper box dimension of `U` to be at least one. -/
private lemma one_le_upperBoxDimension_of_factorial_lower_bound
    (m : MetricSpace FactorialProduct)
    (U : Set FactorialProduct)
    (q : ℕ)
    (h_bound : ∀ n : ℕ, q + 1 < n →
      ((Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ≥0∞))) /
        (Finset.prod (Finset.range (q + 1)) (fun j ↦ (factorialBranching j : ℝ≥0∞)))) ≤
      partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ)) .centered U 1 (dyadicRadius ((n -
          1).factorial))) :
    1 ≤ upperBoxDimension U := by
  classical
  have hbn_pos : ∀ j : ℕ, 0 < factorialBranching j := fun j ↦ by
    unfold factorialBranching
    split_ifs <;> positivity
  let f : ℕ → ℝ≥0∞ := fun k ↦ (pressureRate
    (fun k' ↦ partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ)) .centered U 1
      (dyadicRadius k')) k).toENNReal
  -- Bound the rate at the factorial scales using the cylinder covering numbers.
  have hK : ∀ n, q + 1 < n →
      ENNReal.ofReal ((factorialLogCylinderCount n -
        factorialLogCylinderCount (q + 1)) / ((n - 1).factorial : ℝ)) ≤
        f ((n - 1).factorial) := by
    intro n hn
    have hk0 : (n - 1).factorial ≠ 0 := Nat.factorial_ne_zero _
    have hP := h_bound n hn
    have hA0 : (Finset.prod (Finset.range (q + 1))
        (fun j ↦ (factorialBranching j : ℝ≥0∞))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact_mod_cast (hbn_pos j).ne'
    have hAtop : (Finset.prod (Finset.range (q + 1))
        (fun j ↦ (factorialBranching j : ℝ≥0∞))) ≠ ⊤ :=
      ENNReal.prod_ne_top (fun j _ ↦ ENNReal.natCast_ne_top _)
    have hsplit := Finset.prod_range_mul_prod_Ico
      (fun j ↦ (factorialBranching j : ℝ≥0∞)) (show q + 1 ≤ n by omega)
    have hQ : ((Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ≥0∞))) /
        (Finset.prod (Finset.range (q + 1)) (fun j ↦ (factorialBranching j : ℝ≥0∞)))) =
        ((∏ j ∈ Finset.Ico (q + 1) n, factorialBranching j : ℕ) : ℝ≥0∞) := by
      rw [← hsplit, div_eq_mul_inv, mul_comm _ (Finset.prod (Finset.Ico (q + 1) n) _), mul_assoc,
        ENNReal.mul_inv_cancel hA0 hAtop, mul_one]
      push_cast
      rfl
    rw [hQ] at hP
    set M : ℕ := ∏ j ∈ Finset.Ico (q + 1) n, factorialBranching j with hM
    have hMpos : 0 < M := Finset.prod_pos (fun j _ ↦ hbn_pos j)
    have hNpos : 0 < factorialCylinderCount (q + 1) :=
      Finset.prod_pos (fun j _ ↦ hbn_pos j)
    have hsplitN : factorialCylinderCount n =
        factorialCylinderCount (q + 1) * M := by
      unfold factorialCylinderCount
      exact (Finset.prod_range_mul_prod_Ico factorialBranching
        (show q + 1 ≤ n by omega)).symm
    have hdiff : factorialLogCylinderCount n - factorialLogCylinderCount (q + 1) =
        Real.log (M : ℝ) / Real.log 2 := by
      have h1 : (factorialCylinderCount n : ℝ) =
          (factorialCylinderCount (q + 1) : ℝ) * (M : ℝ) := by
        rw [hsplitN]; push_cast; ring
      unfold factorialLogCylinderCount
      rw [h1, Real.log_mul (by exact_mod_cast hNpos.ne') (by exact_mod_cast hMpos.ne')]
      ring
    have hlogM : ENNReal.log (M : ℝ≥0∞) = ((Real.log (M : ℝ) : ℝ) : EReal) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.log_ofReal_of_pos (by exact_mod_cast hMpos)
    have hge : ((((factorialLogCylinderCount n - factorialLogCylinderCount (q + 1)) /
          ((n - 1).factorial : ℝ) : ℝ)) : EReal) ≤
        pressureRate (fun k' ↦ partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ))
          .centered U 1 (dyadicRadius k')) ((n - 1).factorial) := by
      unfold pressureRate
      simp only [hk0, ↓reduceIte]
      unfold pressureLog
      calc ((((factorialLogCylinderCount n - factorialLogCylinderCount (q + 1)) /
              ((n - 1).factorial : ℝ) : ℝ)) : EReal)
          = ENNReal.log (M : ℝ≥0∞) * (((Real.log 2)⁻¹ : ℝ) : EReal) *
              ((((n - 1).factorial : ℝ)⁻¹ : ℝ) : EReal) := by
            rw [hlogM, ← EReal.coe_mul, ← EReal.coe_mul, hdiff]
            congr 1
        _ ≤ ENNReal.log (partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ))
              .centered U 1 (dyadicRadius ((n - 1).factorial))) * (((Real.log 2)⁻¹ : ℝ) : EReal) *
              ((((n - 1).factorial : ℝ)⁻¹ : ℝ) : EReal) := by
            gcongr
    have hcoe : ∀ r : ℝ, (r : EReal).toENNReal = ENNReal.ofReal r := fun r ↦ by
      rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]
    calc ENNReal.ofReal ((factorialLogCylinderCount n -
          factorialLogCylinderCount (q + 1)) / ((n - 1).factorial : ℝ))
        = (((((factorialLogCylinderCount n - factorialLogCylinderCount (q + 1)) /
            ((n - 1).factorial : ℝ) : ℝ)) : EReal)).toENNReal := (hcoe _).symm
      _ ≤ f ((n - 1).factorial) := EReal.toENNReal_le_toENNReal hge
  -- Removing a fixed initial cylinder does not change the limiting rate.
  have hfac : Tendsto (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n ↦ Nat.self_le_factorial (n - 1)) (tendsto_sub_atTop_nat 1))
  have hlim : Tendsto (fun n : ℕ ↦ (factorialLogCylinderCount n -
      factorialLogCylinderCount (q + 1)) / ((n - 1).factorial : ℝ)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n : ℕ ↦ factorialLogCylinderCount (q + 1) /
        ((n - 1).factorial : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hfac
    have h3 := factorialLogCylinderCount_div_factorial_tendsto.sub h2
    simpa [sub_div] using h3
  have hfac_nat : Tendsto (fun n : ℕ ↦ (n - 1).factorial) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.self_le_factorial (n - 1)) (tendsto_sub_atTop_nat 1)
  -- The factorial subsequence gives a lower bound for the full limsup.
  change 1 ≤ limsup f atTop
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨b', hbb', hb'1⟩ := exists_between hb
  have hev : ∀ᶠ n : ℕ in atTop, b' ≤ f ((n - 1).factorial) := by
    have hlimE : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((factorialLogCylinderCount n -
        factorialLogCylinderCount (q + 1)) / ((n - 1).factorial : ℝ))) atTop (𝓝 1) := by
      have := ENNReal.tendsto_ofReal hlim
      simpa using this
    filter_upwards [hlimE.eventually (lt_mem_nhds hb'1), eventually_gt_atTop (q + 1)] with n hn1 hn2
    exact hn1.le.trans (hK n hn2)
  exact lt_of_lt_of_le hbb' (Filter.le_limsup_of_frequently_le (hfac_nat.frequently hev.frequently))

/-- Any nonempty open set (e.g. cylinder) has upper box dimension at least 1. -/
private lemma one_le_upperBoxDimension_of_isOpen
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (U : Set FactorialProduct) (h_open : IsOpen U) (h_ne : U.Nonempty) :
    1 ≤ upperBoxDimension U := by
  obtain ⟨x, _, q, hq⟩ := exists_factorial_ball_subset_of_isOpen m U h_open h_ne
  have h_bound := factorialProduct_partitionSum_ge m h_ultra h_dist U x q hq
  exact one_le_upperBoxDimension_of_factorial_lower_bound m U q
      h_bound

/-- The covering number of the closure of `A` at dyadic scale `k - 1` is bounded by the
covering number of `A` at dyadic scale `k`. -/
private lemma partitionSum_closure_le_shift
    (m : MetricSpace FactorialProduct)
    (A : Set FactorialProduct) (k : ℕ) (hk : 1 ≤ k) :
    partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ)) .centered
        (closure A) 1 (dyadicRadius (k - 1)) ≤
      partitionSum id (fun _ : FactorialProduct ↦ (0 : ℝ)) .centered
        A 1 (dyadicRadius k) := by
  have h_r_pos : 0 < dyadicRadius k := by dsimp [dyadicRadius]; positivity
  have h_r'_pos : 0 < dyadicRadius (k - 1) := by dsimp [dyadicRadius]; positivity
  rw [packingEqModifiedUpperBox_open_covering A (dyadicRadius k) h_r_pos]
  rw [packingEqModifiedUpperBox_open_covering (closure A) (dyadicRadius (k - 1)) h_r'_pos]
  apply le_iInf
  intro F
  apply le_iInf
  intro hF
  by_cases h_cost : F.encard = ⊤
  · rw [h_cost]
    exact le_top
  · have h_fin : F.Finite := Set.encard_lt_top_iff.mp (lt_top_iff_ne_top.mpr h_cost)
    refine iInf_le_of_le F ?_
    refine iInf_le_of_le ?_ (le_refl _)
    have H_subset : closure A ⊆ closure (⋃ y ∈ F, Metric.ball y (dyadicRadius k)) := closure_mono hF
    have H_bound : closure (⋃ y ∈ F, Metric.ball y (dyadicRadius k)) ⊆ ⋃ y ∈ F, Metric.ball y
        (dyadicRadius (k - 1)) := by
      have h_fin_union : closure (⋃ y ∈ F, Metric.ball y (dyadicRadius k)) = ⋃ y ∈ F, closure
          (Metric.ball y (dyadicRadius k)) := by
        exact Set.Finite.closure_biUnion h_fin _
      rw [h_fin_union]
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨y, hy, h_mem⟩
      use y, hy
      have hc : closure (Metric.ball y (dyadicRadius k)) ⊆ Metric.closedBall y (dyadicRadius k) :=
          Metric.closure_ball_subset_closedBall
      have h2 : Metric.closedBall y (dyadicRadius k) ⊆ Metric.ball y (dyadicRadius (k - 1)) := by
        apply Metric.closedBall_subset_ball
        dsimp [dyadicRadius]
        apply pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
        omega
      exact h2 (hc h_mem)
    exact subset_trans H_subset H_bound

/-- For `n ≠ 0` the pressure rate of `q` at `n` is `pressureLog (q n) / n`. -/
private lemma pressureRate_eq_div_of_ne_zero (q : ℕ → ℝ≥0∞) (n : ℕ) (hn : n ≠ 0) :
    pressureRate q n = pressureLog (q n) * ((n : ℝ)⁻¹ : ℝ) := by
  dsimp [pressureRate]
  rw [ite_eq_right_iff.mpr]
  intro h
  contradiction

/-- If `q n ≤ r (n + 1)` for all `n`, the limsup of the rates of `q` is at most that of `r`. -/
private lemma limsup_pressureRate_le_of_shift_le
    (q r : ℕ → ℝ≥0∞)
    (hqr : ∀ n, q n ≤ r (n + 1)) :
    limsup (fun n ↦ (pressureRate q n).toENNReal) atTop ≤
      limsup (fun n ↦ (pressureRate r n).toENNReal) atTop := by
  let c (n : ℕ) := ((n + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)
  have H_pointwise : (fun n ↦ (pressureRate q n).toENNReal) ≤ᶠ[atTop] (fun n ↦ (pressureRate r (n +
      1)).toENNReal * c n) := by
    filter_upwards [Filter.Ici_mem_atTop 1] with n hn
    have hn_pos : 1 ≤ n := by exact hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n + 1 ≠ 0 := by omega
    have h1 : pressureRate q n = pressureLog (q n) * ((n : ℝ)⁻¹ : ℝ) :=
        pressureRate_eq_div_of_ne_zero q n hn0
    have h2 : pressureRate r (n + 1) = pressureLog (r (n + 1)) * (((n : ℝ) + 1)⁻¹ : ℝ) := by
      have h2a := pressureRate_eq_div_of_ne_zero r (n + 1) hn1
      exact Eq.trans h2a (by congr 3; push_cast; rfl)
    have H_le1 : pressureLog (q n) ≤ pressureLog (r (n + 1)) := by
      unfold pressureLog
      apply mul_le_mul_of_nonneg_right
      · exact ENNReal.log_le_log (hqr n)
      · norm_cast
        have hlog_num : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact inv_nonneg.mpr hlog_num
    have H_le2 : pressureLog (q n) * ((n : ℝ)⁻¹ : ℝ) ≤ pressureLog (r (n + 1)) * (((n : ℝ) + 1)⁻¹ :
        ℝ) * (((n : ℝ) + 1) / (n : ℝ)) := by
      have h_prod : ((((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ)) : EReal) = (((n : ℝ)⁻¹ : ℝ) :
          EReal) := by
        have h_calc : (((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ)) = ((n : ℝ)⁻¹ : ℝ) := by
          have hn_pos_real : (n : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr hn0
          have hn1_pos_real : (n : ℝ) + 1 ≠ 0 := by
            have h_ge_0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
          calc
            (((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ)) = (((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) +
                1) * ((n : ℝ)⁻¹ : ℝ)) := by rw [div_eq_mul_inv]
            _ = (((n : ℝ) + 1)⁻¹ : ℝ) * ((n : ℝ) + 1) * ((n : ℝ)⁻¹ : ℝ) := by rw [mul_assoc]
            _ = 1 * ((n : ℝ)⁻¹ : ℝ) := by rw [inv_mul_cancel₀ hn1_pos_real]
            _ = ((n : ℝ)⁻¹ : ℝ) := by rw [one_mul]
        exact congrArg (fun x : ℝ ↦ (x : EReal)) h_calc
      have h_cast2 : ((((n : ℝ) + 1)⁻¹ : ℝ) : EReal) * ((((n : ℝ) + 1) / (n : ℝ)) : EReal) = (((n :
          ℝ)⁻¹ : ℝ) : EReal) := by
        have H_tmp : ((((n : ℝ) + 1)⁻¹ : ℝ) : EReal) * ((((n : ℝ) + 1) / (n : ℝ)) : EReal) = (((((n
            : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ))) : EReal) := EReal.coe_mul (((n : ℝ) + 1)⁻¹
            : ℝ) (((n : ℝ) + 1) / (n : ℝ)) |>.symm
        rw [H_tmp]
        exact h_prod
      have h_assoc : pressureLog (r (n + 1)) * (((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ)) =
          pressureLog (r (n + 1)) * ((((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ))) := by
        have h : (a b c : EReal) → a * b * c = a * (b * c) := mul_assoc
        exact h (pressureLog (r (n + 1))) ((((n : ℝ) + 1)⁻¹ : ℝ) : EReal) ((((n : ℝ) + 1) / (n : ℝ))
            : EReal)
      rw [h_assoc]
      rw [h_cast2]
      apply mul_le_mul_of_nonneg_right
      · exact H_le1
      · have h_ge_0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h_inv : (0 : ℝ) ≤ ((n : ℝ)⁻¹ : ℝ) := inv_nonneg.mpr h_ge_0
        exact EReal.coe_nonneg.mpr h_inv
    rw [h1, h2]
    have H_le3 : (pressureLog (q n) * ((n : ℝ)⁻¹ : ℝ)).toENNReal ≤ (pressureLog (r (n + 1)) * (((n :
        ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n : ℝ))).toENNReal := by
      exact EReal.toENNReal_le_toENNReal H_le2
    have H_mul : (pressureLog (r (n + 1)) * (((n : ℝ) + 1)⁻¹ : ℝ) * (((n : ℝ) + 1) / (n :
        ℝ))).toENNReal = (pressureLog (r (n + 1)) * (((n : ℝ) + 1)⁻¹ : ℝ)).toENNReal * ((((n : ℝ) +
        1) / (n : ℝ)) : EReal).toENNReal := by
      apply EReal.toENNReal_mul'
      have h1_pos : (0 : ℝ) ≤ (n : ℝ) + 1 := by
        have h_ge_0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have h2_pos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h_div : (0 : ℝ) ≤ (((n : ℝ) + 1) / (n : ℝ)) := div_nonneg h1_pos h2_pos
      exact EReal.coe_nonneg.mpr h_div
    have H_cast : ((((n : ℝ) + 1) / (n : ℝ)) : EReal).toENNReal = c n := by
      have h_tmp : ((((n : ℝ) + 1) / (n : ℝ)) : EReal).toENNReal = ENNReal.ofReal (((n : ℝ) + 1) /
          (n : ℝ)) := EReal.real_coe_toENNReal (((n : ℝ) + 1) / (n : ℝ))
      rw [h_tmp]
      dsimp [c]
      have h_coe_n : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by exact (ENNReal.ofReal_natCast n).symm
      have h_coe_n1 : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
        have h_nat : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
        rw [← h_nat]
        exact (ENNReal.ofReal_natCast (n + 1)).symm
      rw [h_coe_n, h_coe_n1]
      have h_ofReal_div : ENNReal.ofReal (((n : ℝ) + 1) / (n : ℝ)) = ENNReal.ofReal ((n : ℝ) + 1) /
          ENNReal.ofReal (n : ℝ) := by
        have hn1_nonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by
          have h_ge_0_n : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have hn_pos_strict : (0 : ℝ) < (n : ℝ) := by exact Nat.cast_pos.mpr (by omega)
        have H_tmp2 : ENNReal.ofReal (((n : ℝ) + 1) / (n : ℝ)) = ENNReal.ofReal ((n : ℝ) + 1) /
            ENNReal.ofReal (n : ℝ) := ENNReal.ofReal_div_of_pos hn_pos_strict
        exact H_tmp2
      exact h_ofReal_div
    rw [H_mul, H_cast] at H_le3
    exact H_le3
  have H_tendsto : Filter.Tendsto c atTop (𝓝 1) := by
    dsimp [c]
    have h_eq : (fun (n : ℕ) ↦ ((n + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) =ᶠ[atTop] (fun (n : ℕ) ↦ 1 + (n :
        ℝ≥0∞)⁻¹) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by
        have h_pos : 1 ≤ n := by exact hn
        intro h
        have h_nat_eq_zero : n = 0 := by
          exact Nat.cast_eq_zero.mp h
        omega
      have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      have h_add : ((n + 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 := by push_cast; rfl
      rw [h_add]
      rw [ENNReal.add_div]
      rw [ENNReal.div_self hn0 hn_ne_top]
      have h_one_div : (1 : ℝ≥0∞) / (n : ℝ≥0∞) = (n : ℝ≥0∞)⁻¹ := by
        exact one_div (n : ℝ≥0∞)
      rw [h_one_div]
    have h_tendsto_inner : Filter.Tendsto (fun (n : ℕ) ↦ (1 : ℝ≥0∞) + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (1 +
        0)) := by
      apply Filter.Tendsto.add tendsto_const_nhds
      exact ENNReal.tendsto_inv_nat_nhds_zero
    rw [add_zero] at h_tendsto_inner
    exact Filter.Tendsto.congr' h_eq.symm h_tendsto_inner
  have h3 : limsup c atTop = 1 := Filter.Tendsto.limsup_eq H_tendsto
  have h2 : limsup (fun (n : ℕ) ↦ (pressureRate r (n + 1)).toENNReal * c n) atTop ≤ limsup (fun n ↦
      (pressureRate r (n + 1)).toENNReal) atTop * limsup c atTop := by
    apply ENNReal.limsup_mul_le' (u := fun n ↦ (pressureRate r (n + 1)).toENNReal) (v := c)
    · right
      rw [h3]
      exact ENNReal.one_ne_top
    · right
      rw [h3]
      exact one_ne_zero
  rw [h3, mul_one] at h2
  have h4 : limsup (fun n ↦ (pressureRate r (n + 1)).toENNReal) atTop ≤ limsup (fun n ↦
      (pressureRate r n).toENNReal) atTop := by
    have h : (fun n ↦ (pressureRate r (n + 1)).toENNReal) = (fun n ↦ (pressureRate r n).toENNReal) ∘
        (fun n ↦ n + 1) := by rfl
    rw [h]
    have h5 : map (fun (n : ℕ) ↦ n + 1) atTop = atTop := Filter.map_add_atTop_eq_nat 1
    rw [Filter.limsup_comp]
    rw [h5]
  exact le_trans (limsup_le_limsup H_pointwise (by isBoundedDefault) (by isBoundedDefault)) h2
      |>.trans h4

/-- Taking the closure of a set does not increase its upper box dimension. -/
private lemma upperBoxDimension_closure_le
    (m : MetricSpace FactorialProduct)
    (A : Set FactorialProduct) :
    upperBoxDimension (closure A) ≤ upperBoxDimension A := by
  by_cases hA : A = ∅
  · rw [hA, closure_empty]
  · have h1 := partitionSum_closure_le_shift m A
    dsimp [upperBoxDimension]
    apply limsup_pressureRate_le_of_shift_le
    intro n
    have hn : 1 ≤ n + 1 := by omega
    have h1a := h1 (n + 1) hn
    have H_eq : n + 1 - 1 = n := by omega
    rw [H_eq] at h1a
    exact h1a

/-- Baire's category theorem implies that in any countable cover of `Y`, the closure of some piece
contains a nonempty open set. -/
private lemma exists_open_subset_closure_of_countable_cover
    (m : MetricSpace FactorialProduct)
    (h_compact : CompactSpace FactorialProduct)
    (A : ℕ → Set FactorialProduct)
    (h_cov : Set.univ ⊆ ⋃ i, A i) :
    ∃ i, ∃ U : Set FactorialProduct, IsOpen U ∧ U.Nonempty ∧ U ⊆ closure (A i) := by
  let _ : MetricSpace FactorialProduct := m
  let _ : CompactSpace FactorialProduct := h_compact
  have hbn (n : ℕ) : 0 < factorialBranching n := by
    by_cases hn : n = 0 <;> simp [factorialBranching, hn]
  have hne : Nonempty FactorialProduct :=
    ⟨fun n ↦ ⟨0, hbn n⟩⟩
  have h_baire : BaireSpace FactorialProduct :=
    BaireSpace.of_completelyPseudoMetrizable
  have h1 := nonempty_interior_of_iUnion_of_closed (X := FactorialProduct) (ι := ℕ) (f := fun i ↦
      closure (A i)) (fun i ↦ isClosed_closure)
  have h_cov2 : ⋃ i, closure (A i) = Set.univ := by
    apply subset_antisymm (Set.subset_univ _)
    intro x _
    have hx : x ∈ ⋃ i, A i := h_cov (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
  rcases h1 h_cov2 with ⟨i, hi⟩
  use i, interior (closure (A i))
  exact ⟨isOpen_interior, hi, interior_subset⟩

/-- Monotonicity of upper box dimension. -/
private lemma upperBoxDimension_mono_on_factorialProduct
    (m : MetricSpace FactorialProduct)
    (A B : Set FactorialProduct) (h_sub : A ⊆ B) :
    upperBoxDimension A ≤ upperBoxDimension B := by
  dsimp [upperBoxDimension]
  apply Filter.limsup_le_limsup (hu := by isBoundedDefault) (hv := by isBoundedDefault)
  refine Filter.Eventually.of_forall (fun n ↦ ?_)
  apply EReal.toENNReal_le_toENNReal
  dsimp [pressureRate]
  split_ifs with hn
  · rfl
  · dsimp [pressureLog]
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · apply ENNReal.log_le_log
        dsimp [partitionSum]
        refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
        refine iInf_le_of_le F (iInf_le_of_le ⟨hF.1, Set.Subset.trans h_sub hF.2⟩ le_rfl)
      · exact EReal.coe_nonneg.mpr (by positivity)
    · exact EReal.coe_nonneg.mpr (by positivity)

private lemma factorialProduct_modifiedUpperBoxDimension
    (m : MetricSpace FactorialProduct)
    (h_compact : CompactSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n) :
    modifiedUpperBoxDimension (Set.univ : Set FactorialProduct) = 1 := by
  have h_upper := factorialProduct_upperBoxDimension_le_one m h_dist
  have h_lower : 1 ≤ modifiedUpperBoxDimension (Set.univ : Set FactorialProduct) := by
    rw [modifiedUpperBoxDimension]
    apply le_iInf
    intro Y_cov
    apply le_iInf
    intro h_cov
    obtain ⟨i, U, hU_open, hU_ne, hU_sub⟩ :=
      exists_open_subset_closure_of_countable_cover m h_compact Y_cov h_cov
    have h1 := one_le_upperBoxDimension_of_isOpen m h_ultra h_dist U hU_open hU_ne
    have h2 := upperBoxDimension_closure_le m (Y_cov i)
    have h3 := upperBoxDimension_mono_on_factorialProduct m U (closure
        (Y_cov i)) hU_sub
    have h4 : 1 ≤ upperBoxDimension (Y_cov i) := le_trans h1 (le_trans h3 h2)
    exact le_iSup_of_le i h4
  apply le_antisymm _ h_lower
  rw [modifiedUpperBoxDimension]
  have h_cov : (Set.univ : Set FactorialProduct) ⊆ ⋃ j : ℕ, if j = 0 then Set.univ else ∅ := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_ite_empty_right, Set.mem_univ, exists_eq_left]
  have h_bound : (⨆ j : ℕ, upperBoxDimension (if j = 0 then (Set.univ : Set FactorialProduct) else
      ∅)) ≤ 1 := by
    apply iSup_le
    intro j
    split_ifs
    · exact h_upper
    · have h_empty : upperBoxDimension (∅ : Set FactorialProduct) ≤ 1 := by
        have h_sub : (∅ : Set FactorialProduct) ⊆ Set.univ := Set.empty_subset Set.univ
        have h_mono := upperBoxDimension_mono_on_factorialProduct m ∅
            Set.univ h_sub
        exact le_trans h_mono h_upper
      exact h_empty
  exact iInf_le_of_le (fun j ↦ if j = 0 then Set.univ else ∅) (iInf_le_of_le h_cov h_bound)

/-- A compact separable ultrametric witness has actual-diameter packing dimension zero
and specified-radius packing dimension one. Its modified upper box dimension is also one.
Blueprint node `conf:packing-diameter-counterexample`. -/
theorem actualDiameterPackingCounterexample :
    ∃ (Y : Type) (_m : MetricSpace Y) (_P : Presentation Y), CompactSpace Y ∧
      (∀ x y z : Y, dist x z ≤ max (dist x y) (dist y z)) ∧
      actualDiameterPackingDimension (Set.univ : Set Y) = 0 ∧
      metricPackingDimension (Set.univ : Set Y) = 1 ∧
      modifiedUpperBoxDimension (Set.univ : Set Y) = 1 := by
  obtain ⟨m, P, h_compact, h_ultra, h_dist⟩ := exists_compact_factorialProduct
  use FactorialProduct, m, P, h_compact, h_ultra
  have h_actual := factorialPackingDimension_eq_zero m h_ultra h_dist
  have h_mod := factorialProduct_modifiedUpperBoxDimension m h_compact h_ultra h_dist
  refine ⟨h_actual, ?_, h_mod⟩
  let _ : TopologicalSpace.SeparableSpace FactorialProduct :=
    TopologicalSpace.SeparableSpace.of_denseRange P.ι P.dense
  rw [packingEqModifiedUpperBox (Set.univ : Set FactorialProduct)]
  exact h_mod

end Kolmogorov.PointToSet
