/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Geometry.InfiniteEntropy.FiniteAlphabetSubsystems

/-!
# A conformal shift with infinite entropy and no real Bowen root

The cylinder covers and Bernoulli measure from `FiniteAlphabetSubsystems` give Hausdorff
dimension `logb 2 m` for each finite-alphabet subsystem. Letting the alphabet grow shows
that the full Baire shift has infinite pressure, entropy, Hausdorff dimension and metric
packing dimension, even though it is uniformly conformal with constant potential one.

This realizes blueprint node `geometry:infinite-entropy-conformal`: the pressure functions
have no real zero. The `InfiniteEntropy` module exports this counterexample together with
the finite-alphabet calculations.
-/

namespace Kolmogorov.PointToSet
open scoped ENNReal
open Filter Topology MeasureTheory
open scoped Topology

/-- A set of diameter zero has zero mass under the cylinder mass bound. -/
private lemma outerMeasure_inter_le_of_ediam_eq_zero [MetricSpace (ℕ → ℕ)]
    (m : ℕ) (hm : 2 ≤ m)
    (μ : MeasureTheory.OuterMeasure (ℕ → ℕ))
    (hμ_cyl : ∀ x L, μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ENNReal) ^ L)⁻¹)
    (V : Set (ℕ → ℕ)) (hD : Metric.ediam V = 0) :
    μ (V ∩ finiteAlphabetSubsystem m) ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := by
  by_cases hV : V = ∅
  · rw [hV, Set.empty_inter]
    have hz : μ ∅ = 0 := μ.empty
    rw [hz]
    exact zero_le
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hV
    have hV_sub : V ⊆ {x} := by
      intro y hy
      have h_dist : edist y x = 0 := by
        apply le_antisymm
        · rw [← hD]
          change edist y x ≤ ⨆ (y ∈ V) (x ∈ V), edist y x
          apply le_iSup_of_le y
          apply le_iSup_of_le hy
          apply le_iSup_of_le x
          apply le_iSup_of_le hx
          rfl
        · exact zero_le
      rw [Set.mem_singleton_iff]
      exact eq_of_edist_eq_zero h_dist
    have hV_cyl : ∀ L, V ⊆ PiNat.cylinder x L := by
      intro L y hy
      have hyx : y = x := hV_sub hy
      rw [hyx]
      intro n _hn
      rfl
    have h_bound : ∀ L, μ (V ∩ finiteAlphabetSubsystem m) ≤ ((m : ENNReal)⁻¹) ^ L := by
      intro L
      rw [← ENNReal.inv_pow]
      apply le_trans (μ.mono (Set.inter_subset_inter_left _ (hV_cyl L)))
      exact hμ_cyl x L
    have h_tendsto : Tendsto (fun L ↦ ((m : ENNReal)⁻¹) ^ L) atTop (𝓝 0) := by
      apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      rw [ENNReal.inv_lt_one]
      exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hm
    have hz : μ (V ∩ finiteAlphabetSubsystem m) = 0 := by
      exact le_antisymm (ge_of_tendsto h_tendsto (Eventually.of_forall h_bound)) zero_le
    rw [hz, hD]
    have h_logb_pos : 0 < Real.logb 2 m := by
      apply Real.logb_pos
      · norm_num
      · exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hm
    have h0 : (0 : ENNReal) ^ Real.logb 2 m = 0 := by
      exact ENNReal.zero_rpow_of_pos h_logb_pos
    rw [h0, mul_zero]

/-- For sets of diameter at least one, the diameter cost dominates the total mass bound. -/
private lemma outerMeasure_inter_le_of_one_le_ediam [MetricSpace (ℕ → ℕ)]
    (m : ℕ) (hm : 2 ≤ m)
    (μ : MeasureTheory.OuterMeasure (ℕ → ℕ))
    (hμ_cyl : ∀ x L, μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ENNReal) ^ L)⁻¹)
    (V : Set (ℕ → ℕ)) (hD : 1 ≤ Metric.ediam V) :
    μ (V ∩ finiteAlphabetSubsystem m) ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := by
  have hz : PiNat.cylinder (fun _ ↦ 0) 0 = Set.univ := by
    ext y
    simp
  have H := hμ_cyl (fun _ ↦ 0) 0
  rw [hz, pow_zero] at H
  have inv_one_eq : (1 : ℝ≥0∞)⁻¹ = 1 := by rw [inv_one]
  rw [inv_one_eq, Set.univ_inter] at H
  have hm_ge_1 : (1 : ℝ≥0∞) ≤ m := by exact_mod_cast le_trans (by decide : 1 ≤ 2) hm
  have hlog_pos : 0 ≤ Real.logb 2 m := by
    apply Real.logb_nonneg
    · exact_mod_cast (by decide : 1 < 2)
    · exact_mod_cast le_trans (by decide : 1 ≤ 2) hm
  have H_D : 1 ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := by
    calc (1 : ℝ≥0∞) = 1 * (1 : ℝ≥0∞) ^ Real.logb 2 m := by rw [ENNReal.one_rpow, mul_one]
    _ ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := by
      apply mul_le_mul' hm_ge_1
      exact ENNReal.rpow_le_rpow hD hlog_pos
  calc
    μ (V ∩ finiteAlphabetSubsystem m) ≤ μ (finiteAlphabetSubsystem m) :=
      μ.mono Set.inter_subset_right
    _ ≤ 1 := H
    _ ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := H_D

/-- A set of diameter strictly between zero and one lies in a cylinder at a comparable scale. -/
private lemma exists_cylinder_of_ediam_lt_one
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y →
      dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (V : Set (ℕ → ℕ))
    (hD₀ : 0 < Metric.ediam V) (hD₁ : Metric.ediam V < 1) :
    ∃ (L : ℕ) (x : ℕ → ℕ),
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (L + 1)) < Metric.ediam V ∧
      Metric.ediam V ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ L) ∧
      V ⊆ PiNat.cylinder x L := by
  classical
  have hf : Metric.ediam V ≠ ∞ :=
    ne_of_lt (hD₁.trans ENNReal.one_lt_top)
  have hp : 0 < (Metric.ediam V).toReal :=
    ENNReal.toReal_pos_iff.mpr
      ⟨hD₀, hD₁.trans ENNReal.one_lt_top⟩
  have hu : (Metric.ediam V).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono
      (by simp : (1 : ENNReal) ≠ ∞) hD₁.le
  obtain ⟨L, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one hp hu
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hlo' : ENNReal.ofReal ((1 / 2 : ℝ) ^ (L + 1)) <
      Metric.ediam V := by
    calc
      _ < ENNReal.ofReal (Metric.ediam V).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hlo
      _ = _ := ENNReal.ofReal_toReal hf
  have hhi' : Metric.ediam V ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ L) := by
    calc
      _ = ENNReal.ofReal (Metric.ediam V).toReal :=
        (ENNReal.ofReal_toReal hf).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hhi
  have hv : V.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    simp [he, Metric.ediam] at hD₀
  obtain ⟨x, hx⟩ := hv
  refine ⟨L, x, hlo', hhi', ?_⟩
  intro y hy
  have hb : edist y x ≤ Metric.ediam V := by
    unfold Metric.ediam
    exact le_iSup_of_le y (le_iSup_of_le hy
      (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))
  rw [edist_dist] at hb
  have hr : dist y x ≤ (1 / 2 : ℝ) ^ L :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hb.trans hhi')
  by_cases he : y = x
  · subst y
    intro j hj
    rfl
  · rw [hd y x he] at hr
    have hL : L ≤ PiNat.firstDiff y x :=
      (pow_le_pow_iff_right_of_lt_one₀
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mp hr
    intro j hj
    exact PiNat.apply_eq_of_lt_firstDiff (hj.trans_le hL)

/-- The mass bound of a length-`L` cylinder is at most `m` times the diameter cost. -/
private lemma inv_pow_le_mul_rpow_of_dyadic_lt
    (m : ℕ) (hm : 2 ≤ m) (L : ℕ) (D : ENNReal)
    (hD : ENNReal.ofReal ((1 / 2 : ℝ) ^ (L + 1)) < D) :
    ((m : ENNReal) ^ L)⁻¹ ≤
      (m : ENNReal) * D ^ Real.logb 2 m := by
  have hm0 : 0 ≤ Real.logb 2 m := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hm.trans' (by norm_num) : 1 ≤ m)
    exact Real.logb_nonneg (by norm_num) h1
  have h_bound : ENNReal.ofReal ((1 / 2 : ℝ) ^ (L + 1)) ^ Real.logb 2 m ≤ D ^ Real.logb 2 m := by
    apply ENNReal.rpow_le_rpow hD.le hm0
  have h_base : ENNReal.ofReal ((1 / 2 : ℝ) ^ (L + 1)) ^ Real.logb 2 m = ((m : ENNReal) ^ (L +
      1))⁻¹ := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    have h_half : ENNReal.ofReal (1 / 2) = (2 : ENNReal)⁻¹ := by
      have : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
      rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp only [ENNReal.ofReal_ofNat]
    rw [h_half]
    rw [← ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_mul]
    rw [mul_comm, ENNReal.rpow_mul]
    have h_pow_log : (2 : ENNReal) ^ Real.logb 2 m = m := by
      have : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
      rw [this]
      rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      exact ENNReal.ofReal_natCast m
    have h_inv : (2 : ENNReal)⁻¹ ^ Real.logb 2 m = ((2 : ENNReal) ^ Real.logb 2 m)⁻¹ := by
      exact ENNReal.inv_rpow 2 (Real.logb 2 m)
    rw [h_inv]
    rw [h_pow_log]
    rw [ENNReal.rpow_natCast]
    have : ((m : ENNReal) ^ (L + 1))⁻¹ = (m : ENNReal)⁻¹ ^ (L + 1) := by rw [ENNReal.inv_pow]
    exact this.symm
  have h_main : ((m : ENNReal) ^ (L + 1))⁻¹ ≤ D ^ Real.logb 2 m := by
    exact h_base.symm.trans_le h_bound
  have h_pow_L : ((m : ENNReal) ^ (L + 1))⁻¹ = ((m : ENNReal) ^ L)⁻¹ * (m : ENNReal)⁻¹ := by
    rw [pow_add, pow_one, ENNReal.mul_inv]
    · left
      have : (m : ENNReal) ^ L ≠ 0 := by
        intro h
        have hm_pos : (0 : ENNReal) < m := by exact_mod_cast lt_of_lt_of_le (by norm_num) hm
        exact (pow_ne_zero L hm_pos.ne') h
      exact this
    · left
      have : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
      exact ENNReal.pow_ne_top this
  rw [h_pow_L] at h_main
  have h_mul : ((m : ENNReal) ^ L)⁻¹ * (m : ENNReal)⁻¹ * (m : ENNReal) ≤ (D ^ Real.logb 2 m) * (m
      : ENNReal) := by
    exact mul_le_mul' h_main (le_refl _)
  have h_mul' : ((m : ENNReal) ^ L)⁻¹ * (m : ENNReal)⁻¹ * (m : ENNReal) ≤ (m : ENNReal) * D ^
      Real.logb 2 m := by
    calc
      ((m : ENNReal) ^ L)⁻¹ * (m : ENNReal)⁻¹ * (m : ENNReal) ≤ (D ^ Real.logb 2 m) * m := h_mul
      _ = (m : ENNReal) * D ^ Real.logb 2 m := mul_comm _ _
  have h_cancel : ((m : ENNReal) ^ L)⁻¹ * (m : ENNReal)⁻¹ * (m : ENNReal) = ((m : ENNReal) ^ L)⁻¹
      := by
    rw [mul_assoc]
    have h_cancel_inner : (m : ENNReal)⁻¹ * (m : ENNReal) = 1 := by
      apply ENNReal.inv_mul_cancel
      · have : (0 : ENNReal) < m := by exact_mod_cast lt_of_lt_of_le (by norm_num) hm
        exact this.ne'
      · exact ENNReal.natCast_ne_top m
    rw [h_cancel_inner, mul_one]
  rwa [h_cancel] at h_mul'

/-- The cylinder mass bound controls sets of diameter strictly between zero and one. -/
private lemma outerMeasure_inter_le_of_ediam_pos_lt_one [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m)
    (μ : MeasureTheory.OuterMeasure (ℕ → ℕ))
    (hμ_cyl : ∀ x L, μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ENNReal) ^ L)⁻¹)
    (V : Set (ℕ → ℕ)) (hD₀ : 0 < Metric.ediam V) (hD₁ : Metric.ediam V < 1) :
    μ (V ∩ finiteAlphabetSubsystem m) ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := by
  obtain ⟨L, x, hlo, _, hsub⟩ := exists_cylinder_of_ediam_lt_one hd V hD₀ hD₁
  calc
    μ (V ∩ finiteAlphabetSubsystem m) ≤ μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) :=
      MeasureTheory.OuterMeasure.mono _ (Set.inter_subset_inter_left _ hsub)
    _ ≤ ((m : ENNReal) ^ L)⁻¹ := hμ_cyl x L
    _ ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m :=
      inv_pow_le_mul_rpow_of_dyadic_lt m hm L (Metric.ediam V) hlo

/-- The Bernoulli cylinder bound implies the diameter bound needed for Hausdorff measure. -/
private lemma outerMeasure_inter_le_mul_ediam_rpow [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m)
    (μ : MeasureTheory.OuterMeasure (ℕ → ℕ))
    (hμ_cyl : ∀ x L, μ (PiNat.cylinder x L ∩ finiteAlphabetSubsystem m) ≤ ((m : ENNReal) ^ L)⁻¹)
    (V : Set (ℕ → ℕ)) :
    μ (V ∩ finiteAlphabetSubsystem m) ≤ (m : ENNReal) * Metric.ediam V ^ Real.logb 2 m := by
  by_cases hD : Metric.ediam V = 0
  · exact outerMeasure_inter_le_of_ediam_eq_zero m hm μ hμ_cyl V hD
  · by_cases hD_ge : 1 ≤ Metric.ediam V
    · exact outerMeasure_inter_le_of_one_le_ediam m hm μ hμ_cyl V hD_ge
    · have hD₀ : 0 < Metric.ediam V := pos_iff_ne_zero.mpr hD
      have hD₁ : Metric.ediam V < 1 := not_le.mp hD_ge
      exact outerMeasure_inter_le_of_ediam_pos_lt_one hd m hm μ hμ_cyl V hD₀ hD₁

/-- The Hausdorff dimension of the finite subsystem is its base-two alphabet logarithm.
Blueprint node `geometry:finite-alphabet-pressure`. -/
theorem finiteAlphabetSubsystemPressure_hausdorff [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (m : ℕ) (hm : 2 ≤ m) :
    _root_.dimH (finiteAlphabetSubsystem m) = ENNReal.ofReal (Real.logb 2 m) := by
  classical
  let _inst_uniform : UniformSpace (ℕ → ℕ) := PseudoMetricSpace.toUniformSpace
  let _inst_top : TopologicalSpace (ℕ → ℕ) := _inst_uniform.toTopologicalSpace
  let _inst_meas : MeasurableSpace (ℕ → ℕ) := @borel (ℕ → ℕ) _inst_top
  have _inst_borel : @BorelSpace (ℕ → ℕ) _inst_top _inst_meas := ⟨rfl⟩
  let _inst_emetric : EMetricSpace (ℕ → ℕ) := MetricSpace.toEMetricSpace
  have h_log_nonneg : 0 ≤ Real.logb 2 m := by
    apply Real.logb_nonneg (by norm_num)
    exact (Nat.one_le_cast.mpr (le_trans (by norm_num) hm))
  have h_toNN : (Real.toNNReal (Real.logb 2 m) : ℝ) = Real.logb 2 m := Real.coe_toNNReal _
      h_log_nonneg
  have h_ofReal : ENNReal.ofReal (Real.logb 2 m) = (Real.toNNReal (Real.logb 2 m) : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, h_toNN]
  rw [h_ofReal]
  apply le_antisymm
  · apply @dimH_le_of_hausdorffMeasure_ne_top _ _inst_emetric _inst_meas _inst_borel (d :=
      Real.toNNReal (Real.logb 2 m)) (s := finiteAlphabetSubsystem m)
    have h_meas_le : @MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ) _inst_emetric _inst_meas
        _inst_borel (Real.toNNReal (Real.logb 2 m) : ℝ) (finiteAlphabetSubsystem m) ≤ 1 := by
      rw [h_toNN]
      choose C hC_cov hC_diam hC_sum using
        (fun L ↦ exists_finite_cover_ediam_sum_le_one hd m hm L)
      have hr : Filter.Tendsto (fun L : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ L)) Filter.atTop (nhds
          0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num :
            (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
      have h_bound : @MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ) _inst_emetric _inst_meas
          _inst_borel (Real.logb 2 m) (finiteAlphabetSubsystem m) ≤ Filter.liminf (fun n ↦ ∑ i,
          Metric.ediam (C n i) ^ Real.logb 2 m) Filter.atTop := by
        apply @MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (ℕ → ℕ) _inst_emetric
            _inst_meas _inst_borel ℕ (fun L : ℕ ↦ Fin (m ^ L)) _ (Real.logb 2 m)
            (finiteAlphabetSubsystem m) Filter.atTop (fun L ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ L)) hr
            C
        · exact Filter.Eventually.of_forall hC_diam
        · exact Filter.Eventually.of_forall hC_cov
      calc
        _ ≤ Filter.liminf (fun n ↦ ∑ i, Metric.ediam (C n i) ^ Real.logb 2 m) Filter.atTop :=
            h_bound
        _ ≤ 1 := by
          apply Filter.liminf_le_of_frequently_le'
          exact Filter.Eventually.frequently (Filter.Eventually.of_forall hC_sum)
    apply ne_of_lt
    calc
      _ ≤ 1 := h_meas_le
      _ < ⊤ := ENNReal.one_lt_top
  · apply @le_dimH_of_hausdorffMeasure_ne_zero _ _inst_emetric _inst_meas _inst_borel (d :=
      Real.toNNReal (Real.logb 2 m)) (s := finiteAlphabetSubsystem m)
    intro h_zero
    obtain ⟨μ, hμ_mass, hμ_cyl⟩ := exists_outerMeasure_finiteAlphabetSubsystem m hm
    let μ_rest := MeasureTheory.OuterMeasure.restrict (finiteAlphabetSubsystem m) μ
    have h01 : (0 : ENNReal) < 1 := (by exact zero_lt_one)
    have h_le_out : (m : ENNReal)⁻¹ • μ_rest ≤ @MeasureTheory.OuterMeasure.mkMetric (ℕ → ℕ)
        _inst_emetric (fun r : ENNReal ↦ r ^ Real.logb 2 m) := by
      refine @MeasureTheory.OuterMeasure.le_mkMetric (ℕ → ℕ) _inst_emetric
        (fun r : ENNReal ↦ r ^ (Real.logb 2 m))
        ((m : ENNReal)⁻¹ • μ_rest)
        (1 : ENNReal) h01 ?_
      intro V _
      have h_bound_rest : μ_rest V ≤ (m : ENNReal) * Metric.ediam V ^ (Real.logb 2 m) := by
        calc
          μ_rest V = μ (V ∩ finiteAlphabetSubsystem m) :=
              MeasureTheory.OuterMeasure.restrict_apply _ _ _
          _ ≤ (m : ENNReal) * Metric.ediam V ^ (Real.logb 2 m) :=
              outerMeasure_inter_le_mul_ediam_rpow hd m hm μ hμ_cyl V
      calc
        ((m : ENNReal)⁻¹ • μ_rest) V = (m : ENNReal)⁻¹ * μ_rest V := rfl
        _ ≤ (m : ENNReal)⁻¹ * ((m : ENNReal) * Metric.ediam V ^ (Real.logb 2 m)) := by
          gcongr
        _ = ((m : ENNReal)⁻¹ * (m : ENNReal)) * Metric.ediam V ^ (Real.logb 2 m) := by rw
            [mul_assoc]
        _ = Metric.ediam V ^ (Real.logb 2 m) := by
          have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
          have hmt : (m : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
          rw [ENNReal.inv_mul_cancel hm0 hmt, one_mul]
    have h_le : (m : ENNReal)⁻¹ • μ_rest ≤ (@MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ)
        _inst_emetric _inst_meas _inst_borel (Real.logb 2 m)).toOuterMeasure := by
      have h_outer : (@MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ) _inst_emetric _inst_meas
          _inst_borel (Real.logb 2 m)).toOuterMeasure = @MeasureTheory.OuterMeasure.mkMetric (ℕ →
          ℕ) _inst_emetric (fun r ↦ r ^ Real.logb 2 m) := by
        exact @MeasureTheory.Measure.mkMetric_toOuterMeasure (ℕ → ℕ) _inst_emetric _inst_meas
            _inst_borel (fun r : ENNReal ↦ r ^ (Real.logb 2 m))
      rw [h_outer]
      exact h_le_out
    have h_eval : (m : ENNReal)⁻¹ * μ_rest (finiteAlphabetSubsystem m) ≤
        (@MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ) _inst_emetric _inst_meas _inst_borel
        (Real.logb 2 m)).toOuterMeasure (finiteAlphabetSubsystem m) := by
      exact h_le (finiteAlphabetSubsystem m)
    have h_rest_eval : μ_rest (finiteAlphabetSubsystem m) = 1 := by
      calc
        μ_rest (finiteAlphabetSubsystem m) = μ (finiteAlphabetSubsystem m ∩
            finiteAlphabetSubsystem m) := MeasureTheory.OuterMeasure.restrict_apply _ _ _
        _ = μ (finiteAlphabetSubsystem m) := by rw [Set.inter_self]
        _ = 1 := hμ_mass
    have h_meas_zero : (@MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ) _inst_emetric _inst_meas
        _inst_borel (Real.logb 2 m)).toOuterMeasure (finiteAlphabetSubsystem m) = 0 := by
      change @MeasureTheory.Measure.hausdorffMeasure (ℕ → ℕ) _inst_emetric _inst_meas _inst_borel
          (Real.logb 2 m) (finiteAlphabetSubsystem m) = 0
      rw [← h_toNN]
      exact h_zero
    rw [h_rest_eval, h_meas_zero, mul_one] at h_eval
    have hmt : (m : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    exact (not_le_of_gt (ENNReal.inv_pos.mpr hmt)) h_eval

/-- Baire space admits the metric given by the first differing coordinate. -/
private lemma exists_firstDiff_metric :
    ∃ (_m : MetricSpace (ℕ → ℕ)), ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff
        x y := by
  refine ⟨PiNat.metricSpaceNatNat, ?_⟩
  let _ : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  intro x y h
  exact PiNat.dist_eq_of_ne h

/-- The first-difference metric on Baire space is complete and admits a dense sequence. -/
private lemma nonempty_presentation_of_firstDiff_metric
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) :
    Nonempty (Presentation (ℕ → ℕ)) := by
  let target : MetricSpace (ℕ → ℕ) := ‹MetricSpace (ℕ → ℕ)›
  let m₀ : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  have h_dist : target.toDist = m₀.toDist := by
    ext x y
    by_cases h : x = y
    · subst h
      have h1 : @dist _ target.toDist x x = 0 := @dist_self _ target.toPseudoMetricSpace x
      have h2 : @dist _ m₀.toDist x x = 0 := @dist_self _ m₀.toPseudoMetricSpace x
      rw [h1, h2]
    · have h1 : @dist _ target.toDist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y := hd x y h
      have h2 : @dist _ m₀.toDist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
        @PiNat.dist_eq_of_ne (fun _ : ℕ ↦ ℕ) x y h
      rw [h1, h2]
  have hM : target = m₀ := by
    apply MetricSpace.ext
    exact h_dist
  have H : @Presentation (ℕ → ℕ) m₀ := by
    have h_eq : m₀ = (@PiNat.metricSpace (fun _ : ℕ ↦ ℕ) (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot
        _)) := by
      apply MetricSpace.ext
      rfl
    have h_comp : @CompleteSpace (ℕ → ℕ) m₀.toUniformSpace := by
      rw [h_eq]
      exact @PiNat.completeSpace (fun _ : ℕ ↦ ℕ) (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)
    letI : MetricSpace (ℕ → ℕ) := m₀
    exact {
      ι := TopologicalSpace.denseSeq (ℕ → ℕ)
      dense := TopologicalSpace.denseRange_denseSeq (ℕ → ℕ)
      complete := h_comp
    }
  have H' : @Presentation (ℕ → ℕ) target := by
    rw [hM]
    exact H
  exact ⟨H'⟩

/-- A first difference is characterized by its value and agreement below it. -/
private lemma firstDiff_eq_of_ne_of_forall_lt
    {x y : ℕ → ℕ} {n : ℕ} (hn : x n ≠ y n) (hlt : ∀ m < n, x m = y m) :
    PiNat.firstDiff x y = n := by
  have hne : x ≠ y := fun h ↦ hn (by rw [h])
  rcases lt_trichotomy (PiNat.firstDiff x y) n with h | h | h
  · exact absurd (hlt _ h) (PiNat.apply_firstDiff_ne hne)
  · exact h
  · exact absurd (PiNat.apply_eq_of_lt_firstDiff h) hn

/-- The shift lowers a nonzero first difference by one. -/
private lemma firstDiff_shift_add_one
    {x y : ℕ → ℕ} (hne : x ≠ y) (h0 : PiNat.firstDiff x y ≠ 0) :
    (fun j ↦ x (j + 1)) ≠ (fun j ↦ y (j + 1)) ∧
      PiNat.firstDiff (fun j ↦ x (j + 1)) (fun j ↦ y (j + 1)) + 1 =
        PiNat.firstDiff x y := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h1 : x (k + 1) ≠ y (k + 1) := by
    have := PiNat.apply_firstDiff_ne hne
    rwa [hk] at this
  refine ⟨fun h ↦ h1 (congrFun h k), ?_⟩
  have hlt : ∀ m < k, (fun j ↦ x (j + 1)) m = (fun j ↦ y (j + 1)) m := by
    intro m hm
    exact PiNat.apply_eq_of_lt_firstDiff (by rw [hk]; exact Nat.succ_lt_succ hm)
  rw [firstDiff_eq_of_ne_of_forall_lt
    (n := k) h1 hlt, hk]

/-- The Baire shift is uniformly conformal with potential one and both Birkhoff averages one. -/
private lemma exists_uniformConformalData_shift
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) :
    ∃ (C : UniformConformalData (ℕ → ℕ)),
      (∀ x j, C.T x j = x (j + 1)) ∧
      (∀ x, C.potential x = 1) ∧
      (∀ x, x ∈ conformalLocus C) ∧
      (∀ x, lowerBirkhoffAverage C.T C.potential x = 1 ∧
        upperBirkhoffAverage C.T C.potential x = 1) := by
  set T : (ℕ → ℕ) → (ℕ → ℕ) := fun x j ↦ x (j + 1) with hT
  have hle1 : ∀ z w : ℕ → ℕ, dist z w ≤ 1 := by
    intro z w
    by_cases hzw : z = w
    · simp [hzw]
    · rw [hd z w hzw]
      exact pow_le_one₀ (by norm_num) (by norm_num)
  have hloc : ∀ x y : ℕ → ℕ, dist x y < 1 → dist (T x) (T y) = 2 * dist x y := by
    intro x y hxy
    by_cases hxy' : x = y
    · subst hxy'
      simp
    have h0 : PiNat.firstDiff x y ≠ 0 := by
      intro h0
      rw [hd x y hxy', h0] at hxy
      simp at hxy
    obtain ⟨hTne, hfd⟩ :=
      firstDiff_shift_add_one hxy' h0
    rw [hd _ _ hTne, hd x y hxy', ← hfd, pow_succ]
    ring
  have hlip : ∀ x y : ℕ → ℕ, dist (T x) (T y) ≤ 2 * dist x y := by
    intro x y
    by_cases hxy : dist x y < 1
    · rw [hloc x y hxy]
    · have hxy1 : 1 ≤ dist x y := not_lt.mp hxy
      linarith [hle1 (T x) (T y)]
  let C : UniformConformalData (ℕ → ℕ) :=
    { r₀ := 1
      r₀_pos := one_pos
      T := T
      uniformContinuous_T :=
        (LipschitzWith.of_dist_le_mul (K := 2)
          (fun x y ↦ by simpa using hlip x y)).uniformContinuous
      ζ := fun _ ↦ 1
      -- Spelled out: `uniformContinuous_const` would pick the product instance on `ℕ → ℕ`.
      uniformContinuous_ζ := by
        intro s hs
        refine Filter.mem_map.2 (Filter.univ_mem' fun _ ↦ ?_)
        exact (refl_mem_uniformity hs : ((1 : ℝ), (1 : ℝ)) ∈ s)
      distance_eq := fun x y h ↦ by
        rw [Real.rpow_one]
        exact hloc x y h }
  have hpot : ∀ x, C.potential x = 1 := fun _ ↦ rfl
  have hS : ∀ (n : ℕ) (x : ℕ → ℕ), birkhoffSum C.T C.potential n x = n := by
    intro n x
    simp [birkhoffSum, hpot]
  have hev : ∀ x : ℕ → ℕ,
      (fun n : ℕ ↦ ((birkhoffSum C.T C.potential n x / n : ℝ) : EReal)) =ᶠ[Filter.atTop]
        fun _ ↦ (1 : EReal) := by
    intro x
    refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [hS, div_self hn0, EReal.coe_one]
  have hlow : ∀ x, lowerBirkhoffAverage C.T C.potential x = 1 := by
    intro x
    unfold lowerBirkhoffAverage
    rw [Filter.liminf_congr (hev x), Filter.liminf_const]
  have hup : ∀ x, upperBirkhoffAverage C.T C.potential x = 1 := by
    intro x
    unfold upperBirkhoffAverage
    rw [Filter.limsup_congr (hev x), Filter.limsup_const]
  refine ⟨C, fun _ _ ↦ rfl, hpot, fun x ↦ ?_, fun x ↦ ⟨hlow x, hup x⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hlow x]
      exact zero_lt_one
    · rw [hlow x, hup x]
    · rw [hup x]
      exact EReal.coe_lt_top 1
  · intro τ hτ
    refine ⟨0, fun n k hk ↦ ?_⟩
    rw [hS, hS]
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
    linarith
  · exact tendsto_one_div_atTop_nhds_zero_nat

/-- There is a complete separable conformal Baire shift, with every point in the conformal locus. -/
private lemma exists_conformal_baire_shift :
    ∃ (_m : MetricSpace (ℕ → ℕ)) (_P : Presentation (ℕ → ℕ))
      (C : UniformConformalData (ℕ → ℕ)),
      (∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) ∧
      (∀ x j, C.T x j = x (j + 1)) ∧ (∀ x, C.potential x = 1) ∧
      (∀ x, x ∈ conformalLocus C) ∧
      (∀ x, lowerBirkhoffAverage C.T C.potential x = 1 ∧
        upperBirkhoffAverage C.T C.potential x = 1) := by
  have hd_exist := exists_firstDiff_metric
  obtain ⟨m, hd⟩ := hd_exist
  have hP_exist := nonempty_presentation_of_firstDiff_metric hd
  have P := Classical.choice hP_exist
  have hC_exist := exists_uniformConformalData_shift hd
  obtain ⟨C, hC⟩ := hC_exist
  exact ⟨m, P, C, hd, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2⟩

private theorem lowerContentLimit_mono_set
    {X : Type*} [MetricSpace X]
    (T : X → X) (φ : X → ℝ) (w : PressureWeight) (s r : ℝ)
    {Z Y : Set X} (hZY : Z ⊆ Y) :
    lowerContentLimit T φ w Z s r ≤ lowerContentLimit T φ w Y s r := by
  unfold lowerContentLimit
  apply iSup_mono
  intro N
  apply iSup_mono'
  intro hN
  use hN
  unfold lowerContent
  apply iInf_mono
  intro C
  apply iInf_mono'
  intro hC
  use ⟨hC.1, hZY.trans hC.2⟩

private theorem lowerPressure_mono_set
    {X : Type*} [MetricSpace X]
    (T : X → X) (φ : X → ℝ) (p₀ : ℕ)
    {Z Y : Set X} (hZY : Z ⊆ Y) :
    lowerPressure T φ p₀ Z ≤ lowerPressure T φ p₀ Y := by
  unfold lowerPressure
  apply iSup_mono
  intro p
  apply iSup_mono'
  intro hp
  use hp
  unfold lowerPressureAt
  apply iInf_mono
  intro s
  apply iInf_mono'
  intro h
  use le_antisymm (le_trans (lowerContentLimit_mono_set T φ .centered s _ hZY) (le_of_eq h))
      (zero_le)

/-- Growing finite alphabets force the lower pressure of the full Baire shift to be infinite. -/
private lemma lowerPressure_baire_shift_eq_top
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (s : ℝ) :
    lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ = ⊤ := by
  apply eq_top_iff.mpr
  by_contra h_not_top
  have H : ∃ n : ℕ, 2 ≤ 2 ^ n ∧ lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0
      Set.univ < (((n : ℝ) - s : ℝ) : EReal) := by
    cases Ht : lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ
    · exfalso
      have H1 := lowerPressure_mono_set
        (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 (Set.subset_univ (finiteAlphabetSubsystem 2))
      have H2 := finiteAlphabetSubsystemPressure hd 2 (le_rfl) s
      rw [Ht] at H1
      have H3 : (⊥ : EReal) < (((Real.logb 2 (2 : ℝ)) - s : ℝ) : EReal) := EReal.bot_lt_coe _
      have H4 : (((Real.logb 2 (2 : ℝ)) - s : ℝ) : EReal) ≤ ⊥ := by
        calc
          _ = lowerPressure (fun y j ↦ y (j + 1)) (fun _ ↦ -s) 0 (finiteAlphabetSubsystem 2) :=
              H2.symm
          _ ≤ ⊥ := H1
      exact False.elim (lt_irrefl _ (lt_of_le_of_lt H4 H3))
    · rename_i t_r
      have h_arch : ∃ n : ℕ, t_r + s < (n : ℝ) := by
        exact exists_nat_gt (t_r + s)
      rcases h_arch with ⟨n, hn⟩
      let m := max n 1
      use m
      have h1 : 1 ≤ m := le_max_right _ _
      have h2 : m ≠ 0 := by linarith
      have hm2 : 2 ≤ 2 ^ m := Nat.le_self_pow h2 2
      refine ⟨hm2, ?_⟩
      have Ht_symm : (t_r : EReal) = lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0
          Set.univ := Ht.symm
      have h_lt : (t_r : EReal) < (((m : ℝ) - s : ℝ) : EReal) := by
        apply EReal.coe_lt_coe_iff.mpr
        have : t_r < (n : ℝ) - s := by linarith
        apply lt_of_lt_of_le this
        apply sub_le_sub_right
        have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (le_max_left n 1)
        exact this
      have H_eq : lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ = (t_r :
          EReal) := Ht
      exact H_eq.symm ▸ h_lt
    · exfalso
      have h_top_le_top : (⊤ : EReal) ≤ (⊤ : EReal) := le_rfl
      have h_top_le_pressure : ⊤ ≤ lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0
          Set.univ := by
        calc
          ⊤ ≤ ⊤ := h_top_le_top
          _ = lowerPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ := Ht.symm
      exact h_not_top h_top_le_pressure
  rcases H with ⟨n, hn1, hn2⟩
  have H1 := lowerPressure_mono_set
    (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 (Set.subset_univ (finiteAlphabetSubsystem (2 ^
        n)))
  have H2 := finiteAlphabetSubsystemPressure hd (2 ^ n) hn1 s
  have hn3 : (((Real.logb 2 ((2 ^ n : ℕ) : ℝ)) - s : ℝ) : EReal) = (((n : ℝ) - s : ℝ) : EReal) := by
    congr 2
    have h2 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ (n : ℕ) := by exact Nat.cast_pow 2 n
    rw [h2]
    unfold Real.logb
    have h3 : Real.log ((2 : ℝ) ^ (n : ℕ)) = n * Real.log 2 := by
      exact Real.log_pow (2:ℝ) n
    rw [h3]
    have h4 : Real.log 2 ≠ 0 := by
      intro h
      have e := Real.exp_log (by norm_num : (0 : ℝ) < 2)
      rw [h, Real.exp_zero] at e
      norm_num at e
    calc
      (n : ℝ) * Real.log 2 * (Real.log 2)⁻¹ = (n : ℝ) * (Real.log 2 * (Real.log 2)⁻¹) := by ring
      _ = (n : ℝ) * 1 := by rw [mul_inv_cancel₀ h4]
      _ = (n : ℝ) := mul_one _
  rw [hn3] at H2
  rw [H2] at H1
  have H3 := lt_of_le_of_lt H1 hn2
  exact False.elim (lt_irrefl _ H3)

private lemma modifiedUpperPressure_mono_set {X : Type*} [MetricSpace X] {T : X → X} {φ : X → ℝ}
    {w : PressureWeight} {Y Z : Set X} {r : ℝ} (h : Y ⊆ Z) :
    modifiedUpperPressure T φ w Y r ≤ modifiedUpperPressure T φ w Z r := by
  unfold modifiedUpperPressure
  refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
  refine iInf_le_of_le C (iInf_le_of_le (Set.Subset.trans h hC) le_rfl)

private lemma upperPressure_mono_set {X : Type*} [MetricSpace X] {T : X → X} {φ : X → ℝ} {p₀ : ℕ}
    {Y Z : Set X} (h : Y ⊆ Z) :
    upperPressure T φ p₀ Y ≤ upperPressure T φ p₀ Z := by
  unfold upperPressure
  refine iSup_mono fun p ↦ iSup_mono fun hp ↦ ?_
  exact modifiedUpperPressure_mono_set h

/-- Growing finite alphabets force the upper pressure of the full Baire shift to be infinite. -/
private lemma upperPressure_baire_shift_eq_top
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (s : ℝ) :
    upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ = ⊤ := by
  apply eq_top_iff.mpr
  have h_le : ∀ m : ℕ, 2 ≤ m → ((Real.logb 2 m - s : ℝ) : EReal) ≤ upperPressure (fun (y : ℕ → ℕ)
      j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ := by
    intro m hm
    have h1 := finiteAlphabetSubsystemPressure_upper hd m hm s
    have h2 : upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0
        (finiteAlphabetSubsystem m) ≤ upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0
        Set.univ :=
      upperPressure_mono_set (Set.subset_univ (finiteAlphabetSubsystem m))
    rw [← h1]
    exact h2
  by_contra h_not_top
  have h_top : upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ < ⊤ := by
    apply lt_of_not_ge
    exact h_not_top
  obtain ⟨M, hP_lt_M, hM_lt_top⟩ := EReal.lt_iff_exists_real_btwn.mp h_top
  have h_unbounded : ∃ m : ℕ, 2 ≤ m ∧ M < Real.logb 2 m - s := by
    have h_logb : Filter.Tendsto (fun (x : ℝ) ↦ Real.logb 2 x - s) Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun (x : ℝ) ↦ Real.logb 2 x) Filter.atTop Filter.atTop :=
          Real.tendsto_logb_atTop (by norm_num)
      have h2 : Filter.Tendsto (fun (x : ℝ) ↦ x - s) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id
      exact Filter.Tendsto.comp h2 h1
    have h_nat : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
    have h_comp : Filter.Tendsto (fun m : ℕ ↦ Real.logb 2 (m : ℝ) - s) Filter.atTop Filter.atTop
        := Filter.Tendsto.comp h_logb h_nat
    have h_ev := Filter.Tendsto.eventually h_comp (Filter.eventually_gt_atTop M)
    have h_ev_ge := Filter.Eventually.and h_ev (Filter.eventually_ge_atTop 2)
    have h_f : Filter.Frequently (fun m : ℕ ↦ M < Real.logb 2 m - s ∧ 2 ≤ m) Filter.atTop :=
        Filter.Eventually.frequently h_ev_ge
    obtain ⟨m, hm_gt_0, hm_cond⟩ := Filter.frequently_atTop.mp h_f 0
    exact ⟨m, hm_cond.2, hm_cond.1⟩
  obtain ⟨m, hm_ge, hm_M⟩ := h_unbounded
  have hc1 := h_le m hm_ge
  have hc2 : upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ < ((Real.logb 2
      m - s : ℝ) : EReal) := by
    calc
      upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ -s) 0 Set.univ < M := hP_lt_M
      _ < ((Real.logb 2 m - s : ℝ) : EReal) := by
        exact EReal.coe_lt_coe_iff.mpr hm_M
  exact lt_irrefl _ (lt_of_lt_of_le hc2 hc1)

private lemma nat_succ_le_dimH_baire
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y)
    (n : ℕ) :
    (n + 1 : ENNReal) ≤ _root_.dimH (Set.univ : Set (ℕ → ℕ)) := by
  let m : ℕ := 2 ^ (n + 1)
  have hm : 2 ≤ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 1 n)
  have H1 := finiteAlphabetSubsystemPressure_hausdorff hd m hm
  have H2 : _root_.dimH (finiteAlphabetSubsystem m) ≤ _root_.dimH (Set.univ : Set (ℕ → ℕ)) :=
      dimH_mono (Set.subset_univ _)
  rw [H1] at H2
  have H3 : Real.logb 2 (m : ℝ) = n + 1 := by
    have h1 : ((2 ^ (n + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (n + 1 : ℕ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    have h2 : (2 : ℝ) ^ (n + 1 : ℕ) = (2 : ℝ) ^ (n + 1 : ℝ) := by
      norm_cast
    have h3' : (m : ℝ) = (2 : ℝ) ^ (n + 1 : ℝ) := by
      calc
        (m : ℝ) = ((2 ^ (n + 1) : ℕ) : ℝ) := rfl
        _ = (2 : ℝ) ^ (n + 1 : ℕ) := h1
        _ = (2 : ℝ) ^ (n + 1 : ℝ) := h2
    rw [h3']
    have h4 : (0 : ℝ) < 2 := by norm_num
    have h5 : (2 : ℝ) ≠ 1 := by norm_num
    exact Real.logb_rpow h4 h5
  rw [H3] at H2
  have H4 : ENNReal.ofReal (n + 1) = (n + 1 : ENNReal) := by
    have : (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by norm_cast
    rw [this, ENNReal.ofReal_natCast]
    norm_cast
  rwa [H4] at H2

/-- The Hausdorff dimension of Baire space is infinite for the first-difference metric. -/
private lemma dimH_baire_eq_top
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) :
    _root_.dimH (Set.univ : Set (ℕ → ℕ)) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  obtain ⟨n, hn⟩ := exists_nat_ge r
  have h := nat_succ_le_dimH_baire hd n
  calc
    (r : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast hn
    _ ≤ (n + 1 : ENNReal) := by exact_mod_cast (Nat.le_add_right n 1)
    _ ≤ _root_.dimH (Set.univ : Set (ℕ → ℕ)) := h

/-- The point-to-set principles bound Hausdorff dimension by metric packing dimension. -/
private theorem dimH_le_metricPackingDimension
    [MetricSpace (ℕ → ℕ)]
    (P : Presentation (ℕ → ℕ)) (Z : Set (ℕ → ℕ)) :
    _root_.dimH Z ≤ metricPackingDimension Z := by
  rw [classicalPointToSet P Z, classicalPointToSet_upper P Z]
  apply iInf_mono
  intro A
  apply iSup_mono
  intro x
  apply iSup_mono
  intro _
  change (Filter.liminf _ _) ≤ (Filter.limsup _ _)
  exact Filter.liminf_le_limsup
    (Filter.isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
    (Filter.isBoundedUnder_of ⟨⊥, fun _ ↦ bot_le⟩)

/-- The shift is continuous in the first-difference metric. -/
private lemma continuous_baire_shift
    [m : MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) :
    @Continuous (ℕ → ℕ) (ℕ → ℕ) m.toUniformSpace.toTopologicalSpace
        m.toUniformSpace.toTopologicalSpace (fun (y : ℕ → ℕ) j ↦ y (j + 1)) := by
  have H : LipschitzWith 2 (fun (y : ℕ → ℕ) j ↦ y (j + 1)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    by_cases hxy : x = y
    · rw [hxy, dist_self, dist_self, mul_zero]
    by_cases hTxy : (fun j ↦ x (j + 1)) = (fun j ↦ y (j + 1))
    · rw [hTxy, dist_self]; positivity
    rw [hd x y hxy, hd _ _ hTxy]
    have h_le : PiNat.firstDiff x y ≤ PiNat.firstDiff (fun j ↦ x (j + 1)) (fun j ↦ y (j + 1)) + 1
        := by
      by_contra! H
      exact PiNat.apply_firstDiff_ne hTxy (PiNat.apply_eq_of_lt_firstDiff H)
    calc
      (1 / 2 : ℝ) ^ PiNat.firstDiff (fun j ↦ x (j + 1)) (fun j ↦ y (j + 1))
      _ = 2 * ((1 / 2 : ℝ) ^ PiNat.firstDiff (fun j ↦ x (j + 1)) (fun j ↦ y (j + 1)) * (1 / 2 :
          ℝ)) := by ring
      _ = 2 * (1 / 2 : ℝ) ^ (PiNat.firstDiff (fun j ↦ x (j + 1)) (fun j ↦ y (j + 1)) + 1) := by rw
          [pow_add, pow_one]
      _ ≤ 2 * (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) h_le) (by norm_num)
  exact LipschitzWith.continuous H

/-- The zero-potential pressure identity gives infinite lower entropy for the Baire shift. -/
private lemma lowerEntropy_baire_shift_eq_top
    [MetricSpace (ℕ → ℕ)]
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) :
    lowerEntropy (fun (y : ℕ → ℕ) j ↦ y (j + 1)) Set.univ = ⊤ := by
  have hP := nonempty_presentation_of_firstDiff_metric hd
  let P := Classical.choice hP
  have hT := continuous_baire_shift hd
  have H := entropy_eq_zeroPotentialPressure_of_nonempty P _ hT Set.univ Set.univ_nonempty
  have H2 := lowerPressure_baire_shift_eq_top hd 0
  have h_eq : (fun (_ : ℕ → ℕ) ↦ -(0 : ℝ)) = (fun _ ↦ 0) := by
    funext y
    exact neg_zero
  rw [h_eq] at H2
  rw [H2] at H
  exact EReal.coe_ennreal_eq_top_iff.mp H

/-- The zero-potential pressure identity gives infinite upper entropy for the Baire shift. -/
private lemma upperEntropy_baire_shift_eq_top
    [MetricSpace (ℕ → ℕ)]
    (P : Presentation (ℕ → ℕ))
    (hd : ∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) :
    upperEntropy P (fun (y : ℕ → ℕ) j ↦ y (j + 1)) Set.univ = ⊤ := by
  have hT := continuous_baire_shift hd
  have hcmp := entropy_eq_zeroPotentialPressure_of_nonempty_upper P (fun (y : ℕ → ℕ) j ↦ y (j +
      1)) hT Set.univ Set.univ_nonempty
  have hp : upperPressure (fun (y : ℕ → ℕ) j ↦ y (j + 1)) (fun _ ↦ 0) 0 Set.univ = ⊤ := by
    simpa using (upperPressure_baire_shift_eq_top hd 0)
  apply EReal.coe_ennreal_eq_top_iff.mp
  exact hcmp.trans hp

/-- The complete separable Baire shift is uniformly conformal with potential one, but has
infinite pressures, entropies and classical dimensions, and neither real Bowen root.
The single witness lies throughout the three conformal loci and has both averages one.
Blueprint node `geometry:infinite-entropy-conformal`. -/
theorem infiniteEntropyConformalNoBowenRoot :
    ∃ (_m : MetricSpace (ℕ → ℕ)) (P : Presentation (ℕ → ℕ))
      (C : UniformConformalData (ℕ → ℕ)),
      (∀ x y : ℕ → ℕ, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y) ∧
      (∀ x j, C.T x j = x (j + 1)) ∧ (∀ x, C.potential x = 1) ∧
      (∀ x, x ∈ conformalLocus C) ∧
      (∀ x, lowerBirkhoffAverage C.T C.potential x = 1 ∧
        upperBirkhoffAverage C.T C.potential x = 1) ∧
      (∀ s : ℝ, lowerPressure C.T (fun y => -s * C.potential y) 0 Set.univ = ⊤ ∧
        upperPressure C.T (fun y => -s * C.potential y) 0 Set.univ = ⊤) ∧
      lowerEntropy C.T Set.univ = ⊤ ∧ upperEntropy P C.T Set.univ = ⊤ ∧
      _root_.dimH (Set.univ : Set (ℕ → ℕ)) = ⊤ ∧
      metricPackingDimension (Set.univ : Set (ℕ → ℕ)) = ⊤ ∧
      (∀ s : ℝ, lowerPressure C.T (fun y => -s * C.potential y) 0 Set.univ ≠ 0 ∧
        upperPressure C.T (fun y => -s * C.potential y) 0 Set.univ ≠ 0) := by
  obtain ⟨m_inst, P, C, hd, hT, hphi, hlocus, havg⟩ := exists_conformal_baire_shift
  have hT_eq : C.T = (fun y j ↦ y (j + 1)) := funext fun y ↦ funext (hT y)
  have hphi_eq (s : ℝ) : (fun y ↦ -s * C.potential y) = (fun _ ↦ -s) := by
    funext y
    rw [hphi, mul_one]
  have hpressure (s : ℝ) :
      lowerPressure C.T (fun y ↦ -s * C.potential y) 0 Set.univ = ⊤ ∧
      upperPressure C.T (fun y ↦ -s * C.potential y) 0 Set.univ = ⊤ := by
    rw [hT_eq, hphi_eq]
    exact ⟨lowerPressure_baire_shift_eq_top hd s, upperPressure_baire_shift_eq_top hd s⟩
  refine ⟨m_inst, P, C, hd, hT, hphi, hlocus, havg, hpressure, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT_eq]
    exact lowerEntropy_baire_shift_eq_top hd
  · rw [hT_eq]
    exact upperEntropy_baire_shift_eq_top P hd
  · exact dimH_baire_eq_top hd
  · have h := dimH_le_metricPackingDimension P Set.univ
    rw [dimH_baire_eq_top hd] at h
    exact eq_top_iff.mpr h
  · intro s
    rw [(hpressure s).1, (hpressure s).2]
    exact ⟨EReal.top_ne_zero, EReal.top_ne_zero⟩

end Kolmogorov.PointToSet
