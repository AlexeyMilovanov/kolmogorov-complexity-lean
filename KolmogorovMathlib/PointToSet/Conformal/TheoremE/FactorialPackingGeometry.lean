/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.TheoremE.DimensionTheorem

/-!
# Balls and packing contents in the factorial ultrametric

The first-difference metric on the factorial product is compact and admits a presentation.
Its balls are cylinders, whose diameters are exactly the corresponding factorial scales.
Counting disjoint cylinders bounds actual-diameter packing contents by a factorial tail series.
`ActualDiameterBounds` proves that these series tend to zero, giving the vanishing dimension
used in `conf:packing-diameter-counterexample`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability

/-- for every `x` and `ε > 0`, points agreeing with `x` below a large enough index are `ε`-close
to `x` in the prescribed metric. -/
private lemma dist_lt_of_agree_on_initial_segment
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (x : FactorialProduct) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ y : FactorialProduct, (∀ k < N, y k = x k) → dist y x < ε := by
  obtain ⟨N, hN⟩ := factorialScale_eventually_lt ε hε
  refine ⟨N, fun y hy ↦ ?_⟩
  by_cases hxy : y = x
  · subst hxy
    simpa using hε
  · have hex : ∃ k, x k ≠ y k := Function.ne_iff.mp (Ne.symm hxy)
    classical
    have hn : x (Nat.find hex) ≠ y (Nat.find hex) := Nat.find_spec hex
    have hlt : ∀ k < Nat.find hex, x k = y k := fun k hk ↦ not_not.mp (Nat.find_min hex hk)
    have hNn : N ≤ Nat.find hex := by
      by_contra hcon
      exact hn (hy _ (not_le.mp hcon)).symm
    rw [dist_comm, h_dist x y _ hlt hn]
    exact hN _ hNn

/-- cylinders are neighbourhoods in the product topology of the finite discrete factors. -/
private lemma factorialProduct_cylinder_mem_nhds
    (x : FactorialProduct) (N : ℕ) :
    {y : FactorialProduct | ∀ k < N, y k = x k} ∈
      @nhds FactorialProduct Pi.topologicalSpace x := by
  refine Filter.mem_of_superset (set_pi_mem_nhds (Set.finite_Iio N) (s := fun k ↦ {x k}) ?_)
    (fun y hy k hk ↦ hy k hk)
  intro k _
  exact IsOpen.mem_nhds (isOpen_discrete _) rfl

private lemma compactSpace_factorialProduct
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n) :
    CompactSpace FactorialProduct := by
  have hc : @CompactSpace FactorialProduct Pi.topologicalSpace :=
    @Pi.compactSpace _ _ _ (fun i ↦ inferInstance)
  have hle : @LE.le (TopologicalSpace FactorialProduct) _
      Pi.topologicalSpace m.toUniformSpace.toTopologicalSpace := by
    refine @le_of_nhds_le_nhds FactorialProduct _ _ ?_
    intro x s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨N, hN⟩ :=
      dist_lt_of_agree_on_initial_segment m h_dist x ε hε
    exact Filter.mem_of_superset
      (factorialProduct_cylinder_mem_nhds x N)
      (fun y hy ↦ hball (Metric.mem_ball.mpr (hN y hy)))
  exact @Function.Surjective.compactSpace _ _ Pi.topologicalSpace
    m.toUniformSpace.toTopologicalSpace id (continuous_id_of_le hle) hc Function.surjective_id

/-- The factorial product admits a compact ultrametric presentation with the prescribed scales. -/
lemma exists_compact_factorialProduct :
    ∃ (_m : MetricSpace FactorialProduct)
      (_P : Presentation FactorialProduct),
      CompactSpace FactorialProduct ∧
      (∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z)) ∧
      (∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n) := by
  obtain ⟨m, h_ultra, h_dist⟩ := exists_factorialProduct_ultrametric
  have h_compact := compactSpace_factorialProduct m h_dist
  let _ := m
  let _ := h_compact
  let _ : Nonempty FactorialProduct := ⟨fun n ↦ ⟨0, by
    by_cases hn : n = 0 <;> simp [factorialBranching, hn]⟩⟩
  obtain ⟨ι, hι⟩ := TopologicalSpace.exists_dense_seq FactorialProduct
  exact ⟨m, ⟨ι, hι, inferInstance⟩, h_compact, h_ultra, h_dist⟩

/-- The factorial scales strictly decrease with their index. -/
lemma factorialScale_strictAnti :
    StrictAnti factorialScale := by
  apply strictAnti_nat_of_succ_lt
  intro n
  unfold factorialScale
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have h1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp only [hn.ne', h1, reduceIte]
    apply pow_lt_pow_right_of_lt_one₀
    · norm_num
    · norm_num
    · have h2 : n.factorial < (n + 1).factorial := by
        rw [Nat.factorial_succ]
        have h3 : 1 ≤ n.factorial := Nat.factorial_pos n
        nlinarith
      exact h2

/-- every factor has at least two values. -/
private lemma two_le_factorialBranching
    (n : ℕ) : 2 ≤ factorialBranching n := by
  unfold factorialBranching
  split_ifs
  · exact le_rfl
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n.factorial := Nat.pow_le_pow_right (by norm_num) (Nat.factorial_pos n)

/-- points of the depth-`n` cylinder around `x` are within `rn n` of `x`. -/
private lemma dist_le_factorialScale_of_agree
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (x y : FactorialProduct) (n : ℕ) (h : ∀ k < n, y k = x k) :
    dist y x ≤ factorialScale n := by
  classical
  by_cases hyx : y = x
  · rw [hyx, dist_self]
    exact (factorialScale_pos n).le
  · have hex : ∃ k, y k ≠ x k := Function.ne_iff.mp hyx
    have hm : ∀ k < Nat.find hex, y k = x k := fun k hk ↦ not_not.mp (Nat.find_min hex hk)
    rw [h_dist y x _ hm (Nat.find_spec hex)]
    refine factorialScale_antitone ?_
    by_contra hlt
    exact Nat.find_spec hex (h _ (not_le.mp hlt))

/-- the ball of radius `ρ` is the depth-`n` cylinder when `n` is the least index with `rn n < ρ`. -/
private lemma ball_eq_factorialCylinder_of_minimal_scale
    (m : MetricSpace FactorialProduct)
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (x : FactorialProduct) (ρ : ℝ) (n : ℕ)
    (hn : factorialScale n < ρ)
    (hmin : ∀ k < n, ρ ≤ factorialScale k) :
    Metric.ball x ρ = {y | ∀ k < n, y k = x k} := by
  classical
  ext y
  simp only [Metric.mem_ball, Set.mem_ofPred_eq]
  constructor
  · intro hy k hk
    by_contra hne
    have hyx : y ≠ x := fun h ↦ hne (by rw [h])
    have hex : ∃ k, y k ≠ x k := Function.ne_iff.mp hyx
    have hm : ∀ k < Nat.find hex, y k = x k := fun k hk ↦ not_not.mp (Nat.find_min hex hk)
    have hm0n : Nat.find hex < n := by
      by_contra hle
      exact hne (hm k (lt_of_lt_of_le hk (not_lt.mp hle)))
    rw [h_dist y x _ hm (Nat.find_spec hex)] at hy
    exact absurd hy (not_lt.mpr (hmin _ hm0n))
  · intro h
    exact lt_of_le_of_lt
      (dist_le_factorialScale_of_agree
        m h_dist x y n h) hn

/-- Every positive-radius ball is a cylinder, and its actual diameter is exactly the distance
threshold for that depth. -/
private lemma exists_ball_eq_factorialCylinder_ediam
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (x : FactorialProduct) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n : ℕ, Metric.ball x ρ = {y | ∀ k < n, y k = x k} ∧
             Metric.ediam (Metric.ball x ρ) = ENNReal.ofReal (factorialScale n) := by
  classical
  obtain ⟨N, hN⟩ := factorialScale_eventually_lt ρ hρ
  have hex : ∃ n, factorialScale n < ρ := ⟨N, hN N le_rfl⟩
  have hn : factorialScale (Nat.find hex) < ρ := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, ρ ≤ factorialScale k :=
    fun k hk ↦ not_lt.mp (Nat.find_min hex hk)
  have hball :=
    ball_eq_factorialCylinder_of_minimal_scale
      m h_dist x ρ _ hn hmin
  refine ⟨Nat.find hex, hball, ?_⟩
  rw [hball]
  generalize Nat.find hex = n
  apply le_antisymm
  · apply Metric.ediam_le
    intro u hu v hv
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    calc dist u v ≤ max (dist u x) (dist x v) := h_ultra u x v
      _ ≤ factorialScale n :=
        max_le
          (dist_le_factorialScale_of_agree
            m h_dist x u n hu)
          (by
            rw [dist_comm]
            exact
              dist_le_factorialScale_of_agree
                m h_dist x v n hv)
  · have : Nontrivial (Fin (factorialBranching n)) :=
      Fin.nontrivial_iff_two_le.mpr
        (two_le_factorialBranching n)
    obtain ⟨w, hw⟩ := exists_ne (x n)
    let x' : FactorialProduct := Function.update x n w
    have hx' : ∀ k < n, x' k = x k := fun k hk ↦
      Function.update_of_ne (Nat.ne_of_lt hk) w x
    have hxn : x' n = w := Function.update_self n w x
    have hd : dist x x' = factorialScale n := by
      apply h_dist x x' n (fun k hk ↦ (hx' k hk).symm)
      rw [hxn]
      exact hw.symm
    have hxmem : x ∈ {y : FactorialProduct | ∀ k < n, y k = x k} :=
      fun k _ ↦ rfl
    have hx'mem : x' ∈ {y : FactorialProduct | ∀ k < n, y k = x k} := hx'
    calc ENNReal.ofReal (factorialScale n)
        = edist x x' := by rw [edist_dist, hd]
      _ ≤ _ := Metric.edist_le_ediam_of_mem hxmem hx'mem

/-- At any depth, a disjoint family contains at most one ball for each cylinder of that depth. -/
private lemma card_disjoint_factorial_balls_le
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (F : Set (FactorialProduct × ℝ))
    (hF_disj : IsDisjointMetricBallFamily Set.univ F)
    (n : ℕ) :
    ∃ S : Finset (FactorialProduct × ℝ),
      (↑S = {a ∈ F | Metric.ediam (Metric.ball a.1 a.2) = ENNReal.ofReal (factorialScale n)}) ∧
      S.card ≤ Finset.prod (Finset.range n) (fun j ↦ factorialBranching j) := by
  classical
  have hpos : ∀ j, 0 < factorialScale j := by
    intro j
    unfold factorialScale
    split_ifs
    · exact one_pos
    · positivity
  have haux : ∀ (x : FactorialProduct) (ρ : ℝ), 0 < ρ →
      Metric.ediam (Metric.ball x ρ) = ENNReal.ofReal (factorialScale n) →
      Metric.ball x ρ = {y | ∀ k < n, y k = x k} := by
    intro x ρ hρ hn
    obtain ⟨k, hk_eq, hk_diam⟩ :=
      exists_ball_eq_factorialCylinder_ediam
        m h_ultra h_dist x ρ hρ
    rw [hn] at hk_diam
    have h1 : factorialScale k = factorialScale n :=
      ((ENNReal.ofReal_eq_ofReal_iff (hpos n).le (hpos k).le).mp hk_diam).symm
    have h2 : k = n :=
      factorialScale_strictAnti.injective h1
    rw [h2] at hk_eq
    exact hk_eq
  obtain ⟨φ, hφ⟩ : ∃ φ : FactorialProduct × ℝ →
      (∀ j : Fin n, Fin (factorialBranching j.1)),
      ∀ a j, φ a j = a.1 j.1 :=
    ⟨fun a j ↦ a.1 j.1, fun _ _ ↦ rfl⟩
  have hinj : Set.InjOn φ {a ∈ F | Metric.ediam (Metric.ball a.1 a.2) =
      ENNReal.ofReal (factorialScale n)} := by
    intro a ha b hb hab
    by_contra hne
    have hb_pos : 0 < b.2 := (hF_disj.2.1 b hb.1).2
    have hball := haux b.1 b.2 hb_pos hb.2
    have ha_in : a.1 ∈ Metric.ball b.1 b.2 := by
      rw [hball]
      intro k hk
      have := congrFun hab ⟨k, hk⟩
      simp only [hφ] at this
      exact this
    exact Set.disjoint_left.mp (hF_disj.2.2 ha.1 hb.1 hne)
      (Metric.mem_ball_self (hF_disj.2.1 a ha.1).2) ha_in
  have hfin : {a ∈ F | Metric.ediam (Metric.ball a.1 a.2) =
      ENNReal.ofReal (factorialScale n)}.Finite :=
    Set.Finite.of_injOn (Set.mapsTo_univ _ _) hinj Set.finite_univ
  refine ⟨hfin.toFinset, Set.Finite.coe_toFinset hfin, ?_⟩
  have hcard : hfin.toFinset.card ≤
      (Finset.univ : Finset (∀ j : Fin n, Fin (factorialBranching j.1))).card := by
    refine Finset.card_le_card_of_injOn φ (fun _ _ ↦ Finset.mem_univ _) ?_
    intro a ha b hb hab
    exact hinj (hfin.mem_toFinset.mp (Finset.mem_coe.mp ha))
      (hfin.mem_toFinset.mp (Finset.mem_coe.mp hb)) hab
  rw [Finset.card_univ, Fintype.card_pi] at hcard
  simp only [Fintype.card_fin] at hcard
  exact hcard.trans_eq
    (Fin.prod_univ_eq_prod_range (fun j ↦ factorialBranching j) n)

/-- By grouping masses by depth, the total mass of any admissible disjoint family is bounded by the
tail series. -/
private lemma tsum_disjoint_factorial_diameters_le
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (s : ℝ) (M : ℕ)
    (F : Set (FactorialProduct × ℝ))
    (hF_disj : IsDisjointMetricBallFamily Set.univ F)
    (hF_diam : ∀ a ∈ F, Metric.ediam (Metric.ball a.1 a.2) ≤ ENNReal.ofReal (factorialScale M)) :
    (∑' a : F, Metric.ediam (Metric.ball a.val.1 a.val.2) ^ s) ≤
      ∑' n : ℕ, if M ≤ n then
        (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
          (ENNReal.ofReal (factorialScale n) ^ s)
      else 0 := by
  have hr0 : ∀ n, 0 < factorialScale n := by
    intro n
    by_cases hn : n = 0 <;> simp [factorialScale, hn]
  have h_d : ∀ a : F, ∃ n, Metric.ediam (Metric.ball a.1.1 a.1.2) = ENNReal.ofReal (factorialScale
      n) := by
    intro a
    have hF_0 : 0 < a.1.2 := (hF_disj.2.1 a.1 a.2).2
    obtain ⟨n, hn_eq, hn_diam⟩ := exists_ball_eq_factorialCylinder_ediam m h_ultra h_dist a.1.1
        a.1.2 hF_0
    exact ⟨n, hn_diam⟩
  choose d hd using h_d
  have h_rw : (∑' a : F, Metric.ediam (Metric.ball a.val.1 a.val.2) ^ s) = ∑' a : F, ENNReal.ofReal
      (factorialScale (d a)) ^ s := by
    apply tsum_congr
    intro a
    rw [hd a]
  rw [h_rw]
  have h_fib := @ENNReal.tsum_fiberwise F ℕ (fun a ↦ ENNReal.ofReal (factorialScale (d a)) ^ s) d
  rw [← h_fib]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hMn : M ≤ n
  · simp only [hMn, reduceIte]
    have h_rw2 : (∑' (x : d ⁻¹' {n}), ENNReal.ofReal (factorialScale (d ↑x)) ^ s) = ∑' (x : d ⁻¹'
        {n}), ENNReal.ofReal (factorialScale n) ^ s := by
      apply tsum_congr
      intro x
      have hd_eq : d ↑x = n := x.property
      rw [hd_eq]
    rw [h_rw2]
    have h_const : (∑' (x : d ⁻¹' {n}), ENNReal.ofReal (factorialScale n) ^ s) = (ENat.card (d ⁻¹'
        {n})) * ENNReal.ofReal (factorialScale n) ^ s := by
      rw [ENNReal.tsum_const]
    rw [h_const]
    apply mul_le_mul'
    · obtain ⟨S, hS_eq, hS_le⟩ := card_disjoint_factorial_balls_le m h_ultra h_dist F hF_disj n
      have h_inj_map (a : d ⁻¹' {n}) : a.val.val ∈ S := by
        have h_in_S : a.val.val ∈ (S : Set (FactorialProduct × ℝ)) := by
          rw [hS_eq]
          simp only [Set.mem_ofPred_eq]
          have hd_eq : d a.val = n := a.property
          have h_diam_a : Metric.ediam (Metric.ball a.val.val.1 a.val.val.2) = ENNReal.ofReal
              (factorialScale n) := by
            have hd_val : Metric.ediam (Metric.ball a.val.val.1 a.val.val.2) = ENNReal.ofReal
                (factorialScale (d a.val)) := hd a.val
            rw [hd_eq] at hd_val
            exact hd_val
          exact ⟨a.val.property, h_diam_a⟩
        exact h_in_S
      have h_inj : Function.Injective (fun (a : d ⁻¹' {n}) ↦ (⟨a.val.val, h_inj_map a⟩ : S)) := by
        intro a b hab
        have h_val_eq : (⟨a.val.val, h_inj_map a⟩ : S).val = (⟨b.val.val, h_inj_map b⟩ : S).val :=
            congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h_val_eq)
      have h_fin : Finite (d ⁻¹' {n}) := Finite.of_injective _ h_inj
      have h_card_le : Nat.card (d ⁻¹' {n}) ≤ Nat.card S := by
        apply Nat.card_le_card_of_injective
        exact h_inj
      have h_card_S_eq : Nat.card S = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      rw [h_card_S_eq] at h_card_le
      let _ : Finite (d ⁻¹' {n}) := h_fin
      have h_ENat : (ENat.card (d ⁻¹' {n}) : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) := by
        rw [ENat.card_eq_coe_natCard]
        exact mod_cast h_card_le
      have h_prod : (S.card : ℝ≥0∞) ≤ ((Finset.prod (Finset.range n) (fun j ↦ factorialBranching j))
          : ℝ≥0∞) := by
        exact mod_cast hS_le
      have h_prod2 : ((Finset.prod (Finset.range n) (fun j ↦ factorialBranching j)) : ℝ≥0∞) =
          Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ℝ≥0∞)) := by
        exact mod_cast rfl
      have h_S_le_prod : (S.card : ℝ≥0∞) ≤ Finset.prod (Finset.range n) (fun j ↦ (factorialBranching
          j : ℝ≥0∞)) := by
        rw [← h_prod2]
        exact h_prod
      exact le_trans h_ENat h_S_le_prod
    · exact le_rfl
  · simp only [hMn, reduceIte]
    have h_emp : d ⁻¹' {n} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro a ha
      have h_diam_a := hF_diam a a.property
      rw [hd a] at h_diam_a
      have h_da_n : d a = n := ha
      rw [h_da_n] at h_diam_a
      have h_n_lt_M : n < M := not_le.mp hMn
      have h_r_M_lt_r_n : factorialScale M < factorialScale n := factorialScale_strictAnti h_n_lt_M
      have h_r_n_le_r_M : factorialScale n ≤ factorialScale M := by
        have hM_pos : 0 ≤ factorialScale M := le_of_lt (hr0 M)
        exact (ENNReal.ofReal_le_ofReal_iff hM_pos).mp h_diam_a
      have h_false := lt_irrefl _ (lt_of_lt_of_le h_r_M_lt_r_n h_r_n_le_r_M)
      exact h_false
    rw [h_emp, tsum_empty]

/-- The content is bounded by a tail series. -/
lemma factorialPackingContent_le_tsum
    (m : MetricSpace FactorialProduct)
    (h_ultra : ∀ x y z : FactorialProduct, dist x z ≤ max (dist x y) (dist y z))
    (h_dist : ∀ x y : FactorialProduct, ∀ n : ℕ,
        (∀ k < n, x k = y k) → x n ≠ y n → dist x y = factorialScale n)
    (s : ℝ) (M : ℕ) :
    actualDiameterPackingContent (Set.univ : Set FactorialProduct) s
        (factorialScale M) ≤
      ∑' n : ℕ, if M ≤ n then
        (Finset.prod (Finset.range n) (fun j ↦ (factorialBranching j : ENNReal))) *
          (ENNReal.ofReal (factorialScale n) ^ s)
      else 0 := by
  rw [actualDiameterPackingContent]
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  exact tsum_disjoint_factorial_diameters_le m h_ultra h_dist s M F hF.1 hF.2

end Kolmogorov.PointToSet
