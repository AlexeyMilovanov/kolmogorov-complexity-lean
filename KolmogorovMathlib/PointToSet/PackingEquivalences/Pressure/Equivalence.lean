/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.ModifiedSeparated

/-!
# Equivalence of upper pressure definitions

The spanning--separated comparisons and packing bounds identify packing pressure with
modified separated pressure and modified covering pressure at scale zero
(blueprint node `pack:pressure-equivalence`):

* `pressureEquivalence` : packing pressure equals modified separated pressure;
* `pressureEquivalence_covering` : modified separated pressure is the `limsup` of the sup-weight
  covering modifications as the radius tends to `0`;
* `pressureEquivalence_separated_limit` : the radius `limsup` of the separated modification is a
  genuine limit, also at the infinite endpoints;
* `pressureEquivalence_upper` and `pressureEquivalence_covering_limit` : the covering limit
  agrees with the centered dyadic upper pressure `upperPressure T f 0 Z` of the main chapter.

The squeeze between the centered and the sup-weight conventions (they differ by at most the
potential variation at the radius) and the scale-invariance of `limsup` under `r ↦ 2 * r` are
proved here for `EReal`-valued functions on the right neighbourhood filter `𝓝[>] 0`.  These
equalities connect the appendix constructions to the upper point-to-set principle.
-/

namespace Kolmogorov.PointToSet

open Filter TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-- Multiplication by a positive constant maps the filter `𝓝[>] 0` to itself. -/
private theorem map_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    map (c * ·) (𝓝[>] (0 : ℝ)) = 𝓝[>] 0 := by
  rw [Filter.map_eq_comap_of_inverse (n := (c⁻¹ * ·))
    (funext (mul_inv_cancel_left₀ hc.ne')) (funext (inv_mul_cancel_left₀ hc.ne'))]
  exact comap_mulLeft_nhdsGT_zero (inv_pos.mpr hc)

/-- Multiplication by a positive constant tends to `0` from the right as the argument does. -/
private theorem tendsto_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (c * ·) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) :=
  (map_const_mul_nhdsGT_zero hc).le

/-- The `limsup` as the radius tends to `0` does not change when the radius is doubled. -/
private theorem limsup_comp_two_mul (g : ℝ → EReal) :
    limsup (fun r ↦ g (2 * r)) (𝓝[>] 0) = limsup g (𝓝[>] 0) := by
  rw [show (fun r ↦ g (2 * r)) = g ∘ (2 * ·) from rfl, limsup_comp,
    map_const_mul_nhdsGT_zero two_pos]

/-- Adding an error term that tends to `0` does not increase the `limsup`. -/
private theorem limsup_add_le_of_tendsto_zero (g w : ℝ → EReal)
    (hw : Tendsto w (𝓝[>] 0) (𝓝 0)) :
    limsup (fun r ↦ g r + w r) (𝓝[>] 0) ≤ limsup g (𝓝[>] 0) := by
  have h := EReal.limsup_add_le (u := g) (v := w) (f := 𝓝[>] 0)
    (Or.inr (by rw [hw.limsup_eq]; exact EReal.zero_ne_top))
    (Or.inr (by rw [hw.limsup_eq]; exact EReal.zero_ne_bot))
  rwa [hw.limsup_eq, add_zero] at h

/-- Adding an error term that tends to `0` does not change a limit in `EReal`. -/
private theorem tendsto_add_of_tendsto_zero {α : Type*} {l : Filter α} {u w : α → EReal}
    {a : EReal} (hu : Tendsto u l (𝓝 a)) (hw : Tendsto w l (𝓝 0)) :
    Tendsto (fun x ↦ u x + w x) l (𝓝 a) := by
  have h := (EReal.continuousAt_add (p := (a, 0)) (Or.inr EReal.zero_ne_bot)
    (Or.inr EReal.zero_ne_top)).tendsto.comp (hu.prodMk_nhds hw)
  simpa only [Function.comp_def, add_zero] using h

/-- The potential variation at doubled radii tends to `0` with the radius. -/
private theorem tendsto_potentialVariation_two_mul_toReal (f : X → ℝ)
    (hf : UniformContinuous f) :
    Tendsto (fun r : ℝ ↦ ((potentialVariation f (2 * r)).toReal : EReal))
      (𝓝[>] 0) (𝓝 0) :=
  (tendsto_potentialVariation_toReal hf).comp (tendsto_const_mul_nhdsGT_zero two_pos)

/-- The potential variation at doubled radii is finite at small radii. -/
private theorem eventually_potentialVariation_two_mul_lt_top (f : X → ℝ)
    (hf : UniformContinuous f) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, potentialVariation f (2 * r) < ⊤ :=
  (tendsto_const_mul_nhdsGT_zero two_pos).eventually (eventually_potentialVariation_lt_top hf)

/-- Packing and modified separated pressure have the same scale-zero value.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence [SeparableSpace X] (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (hf : UniformContinuous f) (Z : Set X) :
    packingPressure T f Z = modifiedSeparatedPressure T f Z := by
  apply le_antisymm
  · refine limsup_le_limsup ?_
    filter_upwards [eventually_potentialVariation_lt_top hf, self_mem_nhdsWithin]
      with r hr_fin hr_pos
    exact modifiedSeparatedBoundsPackPressure T hT f Z r hr_pos hr_fin
  · dsimp [packingPressure, modifiedSeparatedPressure]
    rw [← limsup_comp_two_mul (modifiedSeparatedPressureAt T f Z)]
    have H_ineq : ∀ᶠ r in 𝓝[>] (0 : ℝ), modifiedSeparatedPressureAt T f Z (2 * r) ≤
        packingPressureAt T f Z r + ((potentialVariation f (2 * r)).toReal : EReal) := by
      filter_upwards [eventually_potentialVariation_two_mul_lt_top f hf, self_mem_nhdsWithin]
        with r hr_fin hr_pos
      exact packBoundsModifiedSeparatedPressure T hT f Z r hr_pos hr_fin
    exact (limsup_le_limsup H_ineq).trans (limsup_add_le_of_tendsto_zero _ _
      (tendsto_potentialVariation_two_mul_toReal f hf))

/-- The separated scale-zero value equals the limit of existing sup-weight modifications.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_covering [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (f : X → ℝ) (hf : UniformContinuous f) (Z : Set X) :
    modifiedSeparatedPressure T f Z =
      limsup (modifiedUpperPressure T f .supremum Z) (𝓝[Set.Ioi 0] 0) := by
  have H_finite := eventually_potentialVariation_two_mul_lt_top f hf
  have H_pos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  apply le_antisymm
  · dsimp [modifiedSeparatedPressure]
    rw [← limsup_comp_two_mul (modifiedSeparatedPressureAt T f Z)]
    have H_ineq : ∀ᶠ r in 𝓝[>] (0 : ℝ), modifiedSeparatedPressureAt T f Z (2 * r) ≤
        modifiedUpperPressure T f .supremum Z r +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
      filter_upwards [H_finite, H_pos] with r hr_fin hr_pos
      exact pressureEquivalence_modified_upper T hT f Z r hr_pos hr_fin
    exact (limsup_le_limsup H_ineq).trans (limsup_add_le_of_tendsto_zero _ _
      (tendsto_potentialVariation_two_mul_toReal f hf))
  · dsimp [modifiedSeparatedPressure]
    rw [← limsup_comp_two_mul (modifiedUpperPressure T f .supremum Z),
      ← limsup_comp_two_mul (modifiedSeparatedPressureAt T f Z)]
    have H_ineq : ∀ᶠ r in 𝓝[>] (0 : ℝ), modifiedUpperPressure T f .supremum Z (2 * r) ≤
        modifiedSeparatedPressureAt T f Z (2 * r) := by
      filter_upwards [H_finite, H_pos] with r hr_fin hr_pos
      exact pressureEquivalence_modified_lower T hT f Z r hr_pos hr_fin
    exact limsup_le_limsup H_ineq
      (isCoboundedUnder_le_of_le _ fun _ ↦ bot_le) (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)

/-- Centered partition sums decrease when the radius increases. -/
private lemma partitionSum_centered_le_of_le (T : X → X) (f : X → ℝ) (Z : Set X) (n : ℕ)
    {r R : ℝ} (h : r ≤ R) :
    partitionSum T f .centered Z n R ≤ partitionSum T f .centered Z n r := by
  refine iInf_mono fun F ↦ iInf_mono' fun hF ↦ ⟨⟨hF.1, ?_⟩, le_rfl⟩
  exact hF.2.trans (Set.iUnion_mono fun y ↦ Set.iUnion_mono fun _ ↦
    bowenBall_subset_of_le T n y h)

/-- The countable modification of centered upper pressure decreases when the radius increases. -/
private lemma modifiedUpperPressure_centered_antitoneOn (T : X → X) (f : X → ℝ) (Z : Set X) :
    AntitoneOn (modifiedUpperPressure T f .centered Z) (Set.Ioi 0) := by
  intro R _ r _ hrR
  refine iInf_mono fun Y ↦ iInf_mono fun _ ↦ iSup_mono fun k ↦ ?_
  refine limsup_le_limsup (Eventually.of_forall fun n ↦ pressureRate_le_of_le _ _ n ?_)
    (isCoboundedUnder_le_of_le atTop fun _ ↦ bot_le) (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
  exact partitionSum_centered_le_of_le T f (Y k) n hrR

/-- Along the radius tending to `0`, the countable modification of centered upper pressure
converges to the centered dyadic upper pressure, including the infinite endpoints. -/
private lemma tendsto_modifiedUpperPressure_centered (T : X → X) (f : X → ℝ) (Z : Set X) :
    Tendsto (modifiedUpperPressure T f .centered Z)
      (𝓝[>] 0) (𝓝 (upperPressure T f 0 Z)) := by
  have hf := modifiedUpperPressure_centered_antitoneOn T f Z
  have H : Tendsto (modifiedUpperPressure T f .centered Z) (𝓝[>] 0) (𝓝 (sSup
      ((modifiedUpperPressure T f .centered Z) '' Set.Ioi 0))) :=
    AntitoneOn.tendsto_nhdsGT hf (OrderTop.bddAbove _)
  have hr_pos : ∀ n, dyadicRadius n ∈ Set.Ioi 0 := fun n ↦
    Set.mem_Ioi.mpr (by unfold dyadicRadius; positivity)
  have H2 : Tendsto (fun n ↦ modifiedUpperPressure T f .centered Z (dyadicRadius n)) atTop
      (𝓝 (sSup ((modifiedUpperPressure T f .centered Z) '' Set.Ioi 0))) :=
    H.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (Eventually.of_forall hr_pos))
  have h_mono : Monotone (fun p ↦ modifiedUpperPressure T f .centered Z (dyadicRadius p)) :=
    fun p q hpq ↦ hf (hr_pos q) (hr_pos p) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq)
  have heq1 : sSup ((modifiedUpperPressure T f .centered Z) '' Set.Ioi 0) =
      ⨆ p, modifiedUpperPressure T f .centered Z (dyadicRadius p) :=
    tendsto_nhds_unique H2 (tendsto_atTop_iSup h_mono)
  have heq2 : upperPressure T f 0 Z =
      ⨆ p, modifiedUpperPressure T f .centered Z (dyadicRadius p) := by
    unfold upperPressure
    rw [iSup_ge_eq_iSup_nat_add, h_mono.iSup_nat_add]
  rwa [heq1, ← heq2] at H

/-- Finite potential variation at radius `r` multiplies the partition sum by at most
`2 ^ (n * ω_f(r))` when passing from centered to supremum weights. -/
private lemma partitionSum_supremum_le_mul_centered (T : X → X) (f : X → ℝ) (Z : Set X)
    (n : ℕ) (r : ℝ) (hω : potentialVariation f r < ⊤) :
    partitionSum T f .supremum Z n r ≤
      partitionSum T f .centered Z n r *
        (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f r).toReal) := by
  have hzero : (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f r).toReal) ≠ 0 := by positivity
  have htop : (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f r).toReal) ≠ ⊤ := by finiteness
  unfold partitionSum
  rw [ENNReal.iInf_mul_of_ne hzero htop]
  refine iInf_mono fun F ↦ ?_
  rw [ENNReal.iInf_mul_of_ne hzero htop]
  refine iInf_mono fun _ ↦ ?_
  unfold partitionCoverCost
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun y ↦ ?_
  dsimp [pressureBallWeight]
  refine iSup₂_le fun z hz ↦ ?_
  rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdist := abs_birkhoffSum_sub_le_mul_variation T f n y z r hω hz
  linarith [(abs_le.mp hdist).2]

/-- The centered upper capacity of a set is bounded by the supremum-weight one. -/
private lemma upperCapacity_centered_le_supremum (T : X → X) (f : X → ℝ) (Y : Set X)
    {r : ℝ} (hr : 0 < r) :
    upperCapacity T f .centered Y r ≤ upperCapacity T f .supremum Y r := by
  unfold upperCapacity
  refine limsup_le_limsup (Eventually.of_forall fun n ↦ pressureRate_le_of_le _ _ n
    (partitionSum_centered_le_supremum T f Y n hr)) ?_ ?_
  · isBoundedDefault
  · isBoundedDefault

/-- At a radius with finite potential variation, the supremum-weight upper capacity of a set
exceeds the centered one by at most the variation. -/
private lemma upperCapacity_supremum_le_centered_add (T : X → X) (f : X → ℝ) (Y : Set X)
    (r : ℝ) (hω : potentialVariation f r < ⊤) :
    upperCapacity T f .supremum Y r ≤
      upperCapacity T f .centered Y r + ((potentialVariation f r).toReal : EReal) := by
  unfold upperCapacity
  have hr_rate : ∀ᶠ n : ℕ in atTop,
      pressureRate (fun n ↦ partitionSum T f .supremum Y n r) n ≤
        pressureRate (fun n ↦ partitionSum T f .centered Y n r) n +
          ((potentialVariation f r).toReal : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pressureRate_le_add_of_le_mul _ _ ((potentialVariation f r).toReal) n hn
      (partitionSum_supremum_le_mul_centered T f Y n r hω)
  refine (limsup_le_limsup hr_rate).trans ?_
  have hlim := EReal.limsup_add_le
    (u := pressureRate (fun n ↦ partitionSum T f .centered Y n r))
    (v := fun _ : ℕ ↦ ((potentialVariation f r).toReal : EReal)) (f := atTop)
    (Or.inr (by simp)) (Or.inr (by simp))
  simpa only [Pi.add_def, limsup_const] using hlim

/-- The centered countable modification is bounded by the supremum-weight one. -/
private lemma modifiedUpperPressure_centered_le_supremum (T : X → X) (f : X → ℝ) (Z : Set X)
    {r : ℝ} (hr : 0 < r) :
    modifiedUpperPressure T f .centered Z r ≤ modifiedUpperPressure T f .supremum Z r :=
  iInf_mono fun Y ↦ iInf_mono fun _ ↦ iSup_mono fun k ↦
    upperCapacity_centered_le_supremum T f (Y k) hr

/-- The supremum-weight countable modification exceeds the centered one by at most the potential
variation, at every radius where the variation is finite. -/
private lemma modifiedUpperPressure_supremum_le_centered_add (T : X → X) (f : X → ℝ)
    (Z : Set X) (r : ℝ) (hω : potentialVariation f r < ⊤) :
    modifiedUpperPressure T f .supremum Z r ≤
      modifiedUpperPressure T f .centered Z r + ((potentialVariation f r).toReal : EReal) := by
  unfold modifiedUpperPressure
  refine le_trans (iInf_mono fun Y ↦ iInf_mono fun _ ↦ ?_)
    ((iInf_mono fun Y ↦ EReal.iInf_add_coe_le _ _).trans (EReal.iInf_add_coe_le _ _))
  exact (iSup_mono fun k ↦ upperCapacity_supremum_le_centered_add T f (Y k) r hω).trans
    (EReal.iSup_add_coe_le _ _)

/-- The sup-weight covering modifications converge along all positive radii to the centered
upper pressure, without any assumption on the separated or packing pressures. -/
private lemma tendsto_modifiedUpperPressure_supremum (T : X → X) (f : X → ℝ)
    (hf : UniformContinuous f) (Z : Set X) :
    Tendsto (modifiedUpperPressure T f .supremum Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (upperPressure T f 0 Z)) := by
  have h_centered := tendsto_modifiedUpperPressure_centered T f Z
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_centered
    (tendsto_add_of_tendsto_zero h_centered (tendsto_potentialVariation_toReal hf)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact modifiedUpperPressure_centered_le_supremum T f Z hr
  · filter_upwards [eventually_potentialVariation_lt_top hf] with r hr
    exact modifiedUpperPressure_supremum_le_centered_add T f Z r hr

/-- All three scale-zero values agree with the frozen centered dyadic upper pressure.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_upper [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (f : X → ℝ) (hf : UniformContinuous f) (Z : Set X) :
    packingPressure T f Z = upperPressure T f 0 Z := by
  rw [pressureEquivalence T hT f hf Z, pressureEquivalence_covering T hT f hf Z]
  exact Tendsto.limsup_eq (tendsto_modifiedUpperPressure_supremum T f hf Z)

/-- The separated radius limsup is a genuine limit, including infinite endpoints.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_separated_limit [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (f : X → ℝ) (hf : UniformContinuous f) (Z : Set X) :
    Tendsto (modifiedSeparatedPressureAt T f Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (modifiedSeparatedPressure T f Z)) := by
  rw [← pressureEquivalence T hT f hf Z]
  have hg : Tendsto (packingPressureAt T f Z) (𝓝[>] 0) (𝓝 (packingPressure T f Z)) :=
    pressureDichotomyScaleLimit_limit T hT f hf Z
  have h_half : Tendsto (fun r : ℝ ↦ r / 2) (𝓝[>] 0) (𝓝[>] 0) :=
    (tendsto_const_mul_nhdsGT_zero (inv_pos.mpr two_pos)).congr fun r ↦ by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg
    (tendsto_add_of_tendsto_zero (hg.comp h_half) (tendsto_potentialVariation_toReal hf))
    ?_ ?_
  · filter_upwards [eventually_potentialVariation_lt_top hf, self_mem_nhdsWithin]
      with r hr_fin hr_pos
    exact modifiedSeparatedBoundsPackPressure T hT f Z r hr_pos hr_fin
  · filter_upwards [eventually_potentialVariation_lt_top hf, self_mem_nhdsWithin]
      with r hr_fin hr_pos
    have h2 : 2 * (r / 2) = r := mul_div_cancel₀ r two_ne_zero
    simpa only [Function.comp_apply, h2] using packBoundsModifiedSeparatedPressure T hT f Z
      (r / 2) (half_pos hr_pos) (by rwa [h2])

/-- The sup-weight covering modifications converge along all positive radii.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_covering_limit [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (f : X → ℝ) (hf : UniformContinuous f) (Z : Set X) :
    Tendsto (modifiedUpperPressure T f .supremum Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (upperPressure T f 0 Z)) := by
  have h_sep := pressureEquivalence_separated_limit T hT f hf Z
  have h_lower_lim : Tendsto (fun r : ℝ ↦ modifiedSeparatedPressureAt T f Z (2 * r) -
      ((potentialVariation f (2 * r)).toReal : EReal)) (𝓝[>] 0)
      (𝓝 (modifiedSeparatedPressure T f Z)) :=
    tendsto_add_of_tendsto_zero (h_sep.comp (tendsto_const_mul_nhdsGT_zero two_pos))
      (by simpa only [neg_zero] using (tendsto_potentialVariation_two_mul_toReal f hf).neg)
  have h_lower : ∀ᶠ r : ℝ in 𝓝[>] 0, modifiedSeparatedPressureAt T f Z (2 * r) -
      ((potentialVariation f (2 * r)).toReal : EReal) ≤
        modifiedUpperPressure T f .supremum Z r := by
    filter_upwards [eventually_potentialVariation_two_mul_lt_top f hf, self_mem_nhdsWithin]
      with r hr_fin hr_pos
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr
      (pressureEquivalence_modified_upper T hT f Z r hr_pos hr_fin)
  have h_upper : ∀ᶠ r : ℝ in 𝓝[>] 0,
      modifiedUpperPressure T f .supremum Z r ≤ modifiedSeparatedPressureAt T f Z r := by
    filter_upwards [eventually_potentialVariation_lt_top hf, self_mem_nhdsWithin]
      with r hr_fin hr_pos
    have h2 : 2 * (r / 2) = r := mul_div_cancel₀ r two_ne_zero
    simpa only [h2] using pressureEquivalence_modified_lower T hT f Z (r / 2) (half_pos hr_pos)
      (by rwa [h2])
  have h_eq : modifiedSeparatedPressure T f Z = upperPressure T f 0 Z :=
    (pressureEquivalence T hT f hf Z).symm.trans (pressureEquivalence_upper T hT f hf Z)
  rw [← h_eq]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_lim h_sep h_lower h_upper

end Kolmogorov.PointToSet
