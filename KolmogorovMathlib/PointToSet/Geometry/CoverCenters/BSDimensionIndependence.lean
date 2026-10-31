/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Geometry.CoverCenters.PressureIndependence

/-!
# BS dimension independence of cover centers

The relocation inequalities compare lower BS masses and fixed-order partition sums
without a variation penalty for nonnegative exponents. Their critical values therefore
agree at scale zero for ambient and self-centered covers, including countable
modifications and unrestricted pieces (blueprint node `geometry:bs-centers`). This module
also completes the comparison of unrestricted self-centered upper pressure with the
usual upper pressure from `geometry:pressure-centers`.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X]
section Pressure
variable [SeparableSpace X] (T : X → X) (hT : Continuous T) (f : X → ℝ)
  (hf : UniformContinuous f) (E : Set X)
include hT hf

omit [SeparableSpace X] hT in
/-- The variation error of a uniformly continuous potential at radius `2 * r` vanishes as
`r → 0⁺`. -/
private lemma tendsto_potentialVariation_two_mul :
    Tendsto (fun r : ℝ => ((potentialVariation f (2 * r)).toReal : EReal))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  have H1 : Tendsto (fun r : ℝ => (potentialVariation f (2 * r))) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hne_top : ε = ⊤
    · rw [hne_top]
      filter_upwards with r
      exact le_top
    have he : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hne_top
    rcases Metric.uniformContinuous_iff.mp hf ε.toReal he with ⟨δ, hδ, hdist⟩
    have h1 : Set.Iio (δ / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by linarith : (0 : ℝ) < δ / 2)
    have h2 : Set.Ioi (0 : ℝ) ∩ Set.Iio (δ / 2) ∈ 𝓝[Set.Ioi 0] (0 : ℝ) := inter_mem_nhdsWithin _ h1
    filter_upwards [h2] with r hr
    have hr' : r < δ / 2 := hr.2
    have hr'' : 2 * r < δ := by linarith
    unfold potentialVariation
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    apply iSup_le
    intro hxy
    have hxy_lt : dist x y < δ := lt_of_le_of_lt hxy hr''
    have hfxy : dist (f x) (f y) < ε.toReal := hdist hxy_lt
    have H2 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal
      (le_of_lt hfxy)
    rw [ENNReal.ofReal_toReal hne_top] at H2
    exact H2
  have H3 : Tendsto (fun r : ℝ => (potentialVariation f (2 * r)).toReal) (𝓝[Set.Ioi 0] 0) (𝓝 0) :=
    by
    have h_cont : ContinuousAt ENNReal.toReal 0 := ENNReal.continuousAt_toReal ENNReal.zero_ne_top
    have H4 := Tendsto.comp h_cont H1
    simp only [ENNReal.toReal_zero] at H4
    exact H4
  have h_cont : ContinuousAt (fun x : ℝ => (x : EReal)) (0 : ℝ) := by
    exact continuous_coe_real_ereal.continuousAt
  have H6 := Tendsto.comp h_cont H3
  simp only [EReal.coe_zero] at H6
  exact H6

/-- The modified self-centered upper pressure at radius `2 * r`, corrected by the variation
error, tends to the upper pressure. -/
private lemma tendsto_modifiedUpperPressure_self_sub_variation :
    Tendsto
      (fun r : ℝ => modifiedUpperPressureWithCenters .self T f E (2 * r) -
        ((potentialVariation f (2 * r)).toReal : EReal))
      (𝓝[Set.Ioi 0] 0) (𝓝 (upperPressure T f 0 E)) := by
  have hd : Tendsto (fun r : ℝ => 2 * r)
      (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
    have hc : Continuous (fun r : ℝ => 2 * r) := continuous_const.mul continuous_id
    have hzero : Tendsto (fun r : ℝ => 2 * r)
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h_tendsto := hc.tendsto 0
      exact (by simpa using h_tendsto)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hzero.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 0 < r := hr
      exact mul_pos (by norm_num : (0 : ℝ) < 2) hr'
  have hp : Tendsto
      (fun r : ℝ => modifiedUpperPressureWithCenters .self T f E (2 * r))
      (𝓝[Set.Ioi 0] 0) (𝓝 (upperPressure T f 0 E)) := by
    have H := pressureIndependentOfCoverCenters_limit T hT f hf E .self .upper
    dsimp [LimitSide.choose] at H
    have H_comp := Tendsto.comp H hd
    have H_eq : ((fun r : ℝ => modifiedUpperPressureWithCenters CoverCenterPolicy.self T f E r) ∘
      fun r : ℝ => 2 * r) = (fun r : ℝ => modifiedUpperPressureWithCenters CoverCenterPolicy.self
      T f E (2 * r)) := by funext x; simp
    rwa [H_eq] at H_comp
  have he :=
    tendsto_potentialVariation_two_mul f hf
  have hn : Tendsto
      (fun r : ℝ => -((potentialVariation f (2 * r)).toReal : EReal))
      (𝓝[Set.Ioi 0] 0) (𝓝 (0 : EReal)) := by
    have hc_neg : Continuous (fun x : EReal => -x) := continuous_neg
    have H2 := hc_neg.tendsto 0
    have H3 := Tendsto.comp H2 he
    have H_eq : ((fun x : EReal => -x) ∘ fun r : ℝ => ↑(potentialVariation f (2 * r)).toReal) =
      (fun r : ℝ => -↑(potentialVariation f (2 * r)).toReal) := by funext x; simp
    rwa [H_eq, neg_zero] at H3
  have hc : ContinuousAt
      (fun p : EReal × EReal => p.1 + p.2)
      (upperPressure T f 0 E, (0 : EReal)) :=
    EReal.continuousAt_add
      (Or.inr EReal.zero_ne_bot) (Or.inr EReal.zero_ne_top)
  have H3 := hc.tendsto.comp (hp.prodMk_nhds hn)
  have H_eq : ((fun p : EReal × EReal => p.1 + p.2) ∘ fun c : ℝ =>
    (modifiedUpperPressureWithCenters CoverCenterPolicy.self T f E (2 * c), -↑(potentialVariation
    f (2 * c)).toReal)) = (fun r : ℝ => modifiedUpperPressureWithCenters CoverCenterPolicy.self T
    f E (2 * r) - ↑(potentialVariation f (2 * r)).toReal) := by
    funext x
    simp only [Function.comp_apply, sub_eq_add_neg]
  have H_eq2 : (upperPressure T f 0 E + 0 : EReal) = upperPressure T f 0 E := by simp
  rwa [H_eq, H_eq2] at H3


/-- For small `r`, the variation-corrected modified self-centered upper pressure at radius
`2 * r` lies below the unrestricted self-centered upper pressure at radius `r`. -/
private lemma eventually_modifiedUpperPressure_self_sub_variation_le :
    ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      modifiedUpperPressureWithCenters .self T f E (2 * r) -
        ((potentialVariation f (2 * r)).toReal : EReal) ≤
      unrestrictedSelfUpperPressure T f E r := by
  have Hfin : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0, potentialVariation f (2 * r) < ⊤ := by
    have h1 := tendsto_potentialVariation_zero f hf
    have hm : Tendsto (fun r : ℝ => 2 * r) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
      have hc : Continuous (fun r : ℝ => 2 * r) := continuous_const.mul continuous_id
      have h_mul : Tendsto (fun r : ℝ => 2 * r) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
        have h_tendsto := hc.tendsto 0
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using h_tendsto)
      have hpos : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0, 2 * r ∈ Set.Ioi 0 := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos (by positivity : (0 : ℝ) < 2) hr
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_mul hpos
    have h2 := h1.comp hm
    exact h2.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))
  filter_upwards [Hfin, self_mem_nhdsWithin] with r hr hpos
  have hsandwich := pressureIndependentOfCoverCenters_unrestricted_sandwich T hT f hf E r hpos hr
  have h2 := hsandwich.2
  apply (EReal.sub_le_iff_le_add _ _).mpr h2
  · left
    exact EReal.coe_ne_bot (potentialVariation f (2 * r)).toReal
  · left
    exact EReal.coe_ne_top (potentialVariation f (2 * r)).toReal

omit [SeparableSpace X] hT hf in
/-- The unrestricted self-centered upper pressure lies below the modified one, since restricted
decompositions are special unrestricted ones. -/
private lemma eventually_unrestrictedSelfUpperPressure_le_modified :
    ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      unrestrictedSelfUpperPressure T f E r ≤
        modifiedUpperPressureWithCenters .self T f E r := by
  filter_upwards [self_mem_nhdsWithin] with r _hr
  unfold unrestrictedSelfUpperPressure modifiedUpperPressureWithCenters
  refine le_iInf (fun Y => le_iInf (fun hY => ?_))
  exact iInf_le_of_le Y (iInf_le_of_le hY.2 (le_refl _))

/-- Unrestricted self pieces have the same upper pressure limit as restricted pieces.
Blueprint node `geometry:pressure-centers`. -/
theorem pressureIndependentOfCoverCenters_unrestricted :
    Tendsto (unrestrictedSelfUpperPressure T f E) (𝓝[Set.Ioi 0] 0)
      (𝓝 (upperPressure T f 0 E)) := by
  have hl_lower := tendsto_modifiedUpperPressure_self_sub_variation T hT f hf E
  have hl_upper : Tendsto (fun r => modifiedUpperPressureWithCenters .self T f E r) (𝓝[Set.Ioi 0]
    0) (𝓝 (upperPressure T f 0 E)) := by
    have h_lim := pressureIndependentOfCoverCenters_limit T hT f hf E .self .upper
    dsimp [LimitSide.choose] at h_lim
    exact h_lim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl_lower hl_upper
  · exact eventually_modifiedUpperPressure_self_sub_variation_le T hT f hf E
  · exact eventually_unrestrictedSelfUpperPressure_le_modified T f E
end Pressure

section BS

variable [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (E : Set X) (hpos : ∀ x ∈ E, 0 < lowerBirkhoffAverage T u x)

include hT hu hpos

section RelocatedFamily

omit [TopologicalSpace.SeparableSpace X] hT hu hpos

/-- The Bowen cover family obtained from `C` by discarding the balls that miss `E` and
moving each remaining ball to a chosen center in its intersection with `E`. -/
private noncomputable def relocatedBowenCoverFamily
    (T : X → X) (E : Set X) (r : ℝ) (C : BowenCoverFamily X) : BowenCoverFamily X where
  index := {k : ℕ | ∃ (hk : k ∈ C.index), (E ∩ bowenBall T (C.order ⟨k, hk⟩) (C.center ⟨k, hk⟩)
    r).Nonempty}
  center := fun j => Classical.choose j.2.2
  order := fun j => C.order ⟨j.1, j.2.1⟩

/-- Relocating the balls of a Bowen cover of `E` at radius `r` gives a Bowen cover of `E` at
radius `2 * r` whose centers lie in `E`. -/
private lemma isBowenCover_relocatedBowenCoverFamily
    (T : X → X) (E : Set X) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (C : BowenCoverFamily X)
    (hC : IsBowenCover T E r N C) :
    IsBowenCover T E (2 * r) N (relocatedBowenCoverFamily T E r C) ∧
      ∀ j, (relocatedBowenCoverFamily T E r C).center j ∈ E := by
  constructor
  · constructor
    · intro j
      dsimp [relocatedBowenCoverFamily]
      exact hC.1 ⟨j.1, j.2.1⟩
    · intro x hx
      have hx' := hC.2 hx
      simp only [Set.mem_iUnion] at hx' ⊢
      rcases hx' with ⟨j, hj⟩
      have Hnonempty : (E ∩ bowenBall T (C.order j) (C.center j) r).Nonempty := ⟨x, hx, hj⟩
      let j' : {k : ℕ | ∃ (hk : k ∈ C.index), (E ∩ bowenBall T (C.order ⟨k, hk⟩) (C.center ⟨k,
        hk⟩) r).Nonempty} :=
        ⟨j.1, j.2, Hnonempty⟩
      use j'
      dsimp [relocatedBowenCoverFamily]
      have hz : Classical.choose j'.2.2 ∈ E ∩ bowenBall T (C.order j) (C.center j) r :=
        Classical.choose_spec j'.2.2
      exact relocateCoverBall T E (C.order j) (C.center j) (Classical.choose j'.2.2) r hr hz hj
  · intro j
    dsimp [relocatedBowenCoverFamily]
    have hz : Classical.choose j.2.2 ∈ E ∩ bowenBall T (C.order ⟨j.1, j.2.1⟩) (C.center ⟨j.1,
      j.2.1⟩) r := Classical.choose_spec j.2.2
    exact hz.1

/-- Relocating the balls of a cover to centers in `E`, at doubled radius, does not increase the
BS cost for nonnegative exponents. -/
private lemma bsCoverCost_relocatedBowenCoverFamily_le
    (T : X → X) (u : X → ℝ) (E : Set X)
    (a : ℝ) (ha : 0 ≤ a) (r : ℝ) (hr : 0 < r)
    (C : BowenCoverFamily X) :
    bsCoverCost T u a (2 * r) (relocatedBowenCoverFamily T E r C) ≤
      bsCoverCost T u a r C := by
  dsimp [bsCoverCost]
  let R := relocatedBowenCoverFamily T E r C
  let f : R.index → C.index := fun j => ⟨j.val, j.property.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h1 : (f x).val = (f y).val := by rw [hxy]
    exact h1
  apply le_trans _ (ENNReal.tsum_comp_le_tsum_of_injective hf (fun j => bsBallWeight T u a
    (C.order j) (C.center j) r))
  apply ENNReal.tsum_le_tsum
  intro j
  dsimp [f, relocatedBowenCoverFamily, bsBallWeight]
  apply ENNReal.antitone_rpow_of_nonpos (-a) (neg_nonpos.mpr ha)
  dsimp only [pressureBallWeight]
  apply iSup_mono
  intro w
  apply iSup_mono'
  intro hw
  have hz : Classical.choose j.property.2 ∈ E ∩ bowenBall T (C.order ⟨j.val, j.property.1⟩)
    (C.center ⟨j.val, j.property.1⟩) r := Classical.choose_spec j.property.2
  have h_incl := relocateCoverBall T E (C.order ⟨j.val, j.property.1⟩) (C.center ⟨j.val,
    j.property.1⟩) (Classical.choose j.property.2) r hr hz
  use h_incl hw

end RelocatedFamily

/-- Lower BS cutoff masses compare without a variation error for nonnegative exponents.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_content (a : ℝ) (ha : 0 ≤ a)
    (r : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N) :
    lowerBSMass T u E a (2 * r) N ≤ lowerBSMassWithCenters .self T u E a (2 * r) N ∧
      lowerBSMassWithCenters .self T u E a (2 * r) N ≤ lowerBSMass T u E a r N := by
  have _ := hT
  have _ := hu
  have _ := hpos
  have _ := (inferInstance : SeparableSpace X)
  have _ := hN
  classical
  constructor
  · change
      (⨅ C : BowenCoverFamily X,
        ⨅ (_ : IsBowenCover T E (2 * r) N C),
          bsCoverCost T u a (2 * r) C) ≤
      (⨅ C : BowenCoverFamily X,
        ⨅ (_ : IsBowenCover T E (2 * r) N C ∧
          ∀ j, C.center j ∈ E),
          bsCoverCost T u a (2 * r) C)
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    have hamb : IsBowenCover T E (2 * r) N C := hC.1
    exact iInf_le_of_le C
      (iInf_le (fun _ : IsBowenCover T E (2 * r) N C =>
        bsCoverCost T u a (2 * r) C) hamb)
  · unfold lowerBSMass lowerBSMassWithCenters
    refine le_iInf (fun C => le_iInf (fun hC => ?_))
    refine iInf_le_of_le (relocatedBowenCoverFamily T E r C) ?_
    refine iInf_le_of_le (isBowenCover_relocatedBowenCoverFamily T E r hr N C hC) ?_
    exact bsCoverCost_relocatedBowenCoverFamily_le T u E a ha r hr C

/-- Fixed-order BS partition infima compare with no finite-to-zero threshold conversion.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_partition (a : ℝ) (ha : 0 ≤ a)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 1 ≤ n) :
    bsPartitionSum T u E a (2 * r) n ≤ bsPartitionSumWithCenters .self T u E a (2 * r) n ∧
      bsPartitionSumWithCenters .self T u E a (2 * r) n ≤ bsPartitionSum T u E a r n := by
  have _ := hT
  have _ := hu
  have _ := hpos
  have _ := (inferInstance : SeparableSpace X)
  have _ := hn
  classical
  constructor
  · unfold bsPartitionSum bsPartitionSumWithCenters
    refine le_iInf fun F => le_iInf fun hF => ?_
    exact iInf_le_of_le F (iInf_le_of_le ⟨hF.1, hF.2.2⟩ le_rfl)
  · unfold bsPartitionSum
    refine le_iInf fun F => le_iInf fun hF => ?_
    -- Keep the useful balls and choose each new center in its intersection with E.
    let I := {y : F // (E ∩ bowenBall T n y r).Nonempty}
    let z : I → X := fun y => Classical.choose y.property
    have hz (y : I) : z y ∈ E ∩ bowenBall T n y.val r :=
      Classical.choose_spec y.property
    let G : Set X := Set.range z
    have hGcount : G.Countable := by
      let : Countable F := hF.1.to_subtype
      exact Set.countable_range z
    have hGE : G ⊆ E := by
      rintro x ⟨y, rfl⟩
      exact (hz y).1
    have hGcover : E ⊆ ⋃ y ∈ G, bowenBall T n y (2 * r) := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ : ∃ y ∈ F, x ∈ bowenBall T n y r := by
        simpa only [Set.mem_iUnion, exists_prop] using hF.2 hx
      let i : I := ⟨⟨y, hy⟩, ⟨x, hx, hxy⟩⟩
      have hball : x ∈ bowenBall T n (z i) (2 * r) :=
        relocateCoverBall T E n y (z i) r hr (hz i) hxy
      exact Set.mem_iUnion.mpr ⟨z i,
        Set.mem_iUnion.mpr ⟨Set.mem_range_self i, hball⟩⟩
    have hcost : bsPartitionCoverCost T u a (2 * r) n G ≤
        bsPartitionCoverCost T u a r n F := by
      let g : I → G := fun y => ⟨z y, Set.mem_range_self y⟩
      have hg : Function.Surjective g := by
        rintro ⟨x, y, hxy⟩
        exact ⟨y, Subtype.ext hxy⟩
      unfold bsPartitionCoverCost
      calc
        -- Passing to the range deletes repeated centers without increasing the sum.
        (∑' y : G, bsBallWeight T u a n y (2 * r)) ≤
            ∑' y : I, bsBallWeight T u a n (z y) (2 * r) :=
          ENNReal.tsum_le_tsum_comp_of_surjective hg _
        _ ≤ ∑' y : I, bsBallWeight T u a n y.val r := by
          apply ENNReal.tsum_le_tsum
          intro y
          unfold bsBallWeight
          apply ENNReal.antitone_rpow_of_nonpos (-a) (neg_nonpos.mpr ha)
          dsimp only [pressureBallWeight]
          apply iSup₂_le
          intro w hw
          exact le_iSup₂_of_le w
            (relocateCoverBall T E n y.val (z y) r hr (hz y) hw) le_rfl
        _ ≤ ∑' y : F, bsBallWeight T u a n y r :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun y : I => y.val) Subtype.val_injective
            (fun y : F => bsBallWeight T u a n y r)
    unfold bsPartitionSumWithCenters
    exact iInf_le_of_le G (iInf_le_of_le ⟨hGcount, hGE, hGcover⟩ hcost)

/-- Lower BS zero thresholds inherit the radius-doubled sandwich.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_lower (r : ℝ) (hr : 0 < r) :
    lowerBSDimensionAt T u E (2 * r) ≤ lowerBSDimensionAtWithCenters .self T u E (2 * r) ∧
      lowerBSDimensionAtWithCenters .self T u E (2 * r) ≤ lowerBSDimensionAt T u E r := by
  have H (a : ℝ) (ha : 0 ≤ a) (r' : ℝ) (hr' : 0 < r') :
    lowerBSMassLimit T u E a (2 * r') ≤ lowerBSMassLimitWithCenters .self T u E a (2 * r') ∧
    lowerBSMassLimitWithCenters .self T u E a (2 * r') ≤ lowerBSMassLimit T u E a r' := by
    constructor
    · apply iSup_mono; intro N
      apply iSup_mono; intro hN
      exact (bsDimensionIndependentOfCoverCenters_content T hT u hu E hpos a ha r' hr' N hN).1
    · apply iSup_mono; intro N
      apply iSup_mono; intro hN
      exact (bsDimensionIndependentOfCoverCenters_content T hT u hu E hpos a ha r' hr' N hN).2
  constructor
  · apply iInf_mono; intro s
    apply iInf_mono; intro hs
    apply iInf_mono'; intro h_zero
    refine ⟨?_, le_rfl⟩
    have H_lower := (H s hs r hr).1
    rw [h_zero] at H_lower
    exact le_antisymm H_lower (by exact bot_le)
  · apply iInf_mono; intro s
    apply iInf_mono; intro hs
    apply iInf_mono'; intro h_zero
    refine ⟨?_, le_rfl⟩
    have H_upper := (H s hs r hr).2
    rw [h_zero] at H_upper
    exact le_antisymm H_upper (by exact bot_le)

/-- Raw upper capacities compare using the finite threshold on both sides.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_capacity (r : ℝ) (hr : 0 < r) :
    upperBSCapacityAt T u E (2 * r) ≤ upperBSCapacityAtWithCenters .self T u E (2 * r) ∧
      upperBSCapacityAtWithCenters .self T u E (2 * r) ≤ upperBSCapacityAt T u E r := by
  unfold upperBSCapacityAt upperBSCapacityAtWithCenters
  constructor
  · refine iInf_mono (fun s => iInf_mono (fun hs => ?_))
    refine le_iInf (fun h => iInf_le_of_le ?_ (le_refl _))
    have hs_ineq := bsDimensionIndependentOfCoverCenters_partition T hT u hu E hpos s hs r hr
    have H : ∀ᶠ n in atTop, bsPartitionSum T u E s (2 * r) n ≤ bsPartitionSumWithCenters .self T u
      E s (2 * r) n := by
      apply eventually_atTop.mpr ⟨1, fun n hn => (hs_ineq n hn).1⟩
    apply lt_of_le_of_lt (limsup_le_limsup H) h
  · refine iInf_mono (fun s => iInf_mono (fun hs => ?_))
    refine le_iInf (fun h => iInf_le_of_le ?_ (le_refl _))
    have hs_ineq := bsDimensionIndependentOfCoverCenters_partition T hT u hu E hpos s hs r hr
    have H : ∀ᶠ n in atTop, bsPartitionSumWithCenters .self T u E s (2 * r) n ≤ bsPartitionSum T u
      E s r n := by
      apply eventually_atTop.mpr ⟨1, fun n hn => (hs_ineq n hn).2⟩
    apply lt_of_le_of_lt (limsup_le_limsup H) h

/-- Modified upper BS capacities relocate to centers in each target piece separately.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_modified (r : ℝ) (hr : 0 < r) :
    modifiedUpperBSDimension T u E (2 * r) ≤
        modifiedUpperBSDimensionWithCenters .self T u E (2 * r) ∧
      modifiedUpperBSDimensionWithCenters .self T u E (2 * r) ≤
        modifiedUpperBSDimension T u E r := by
  constructor
  · apply iInf_mono
    intro Y
    apply iInf_mono
    intro hY
    apply iSup_mono
    intro j
    have := bsDimensionIndependentOfCoverCenters_capacity T hT u hu (Y j) (fun x hx => hpos x
      (hY.1 j hx)) r hr
    exact this.1
  · apply iInf_mono
    intro Y
    apply iInf_mono
    intro hY
    apply iSup_mono
    intro j
    have := bsDimensionIndependentOfCoverCenters_capacity T hT u hu (Y j) (fun x hx => hpos x
      (hY.1 j hx)) r hr
    exact this.2

/-- The two BS center policies give the frozen lower or modified upper dimension.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters (policy : CoverCenterPolicy) (σ : LimitSide) :
    coverCenterBSDimension policy σ T u E =
      σ.choose (lowerBSDimension T u E, upperBSDimension T u E) := by
  have hsup (A S : ℝ → ℝ≥0∞)
      (h : ∀ r, 0 < r → A (2 * r) ≤ S (2 * r) ∧ S (2 * r) ≤ A r) :
      (⨆ p : ℕ, S (dyadicRadius p)) = ⨆ p : ℕ, A (dyadicRadius p) := by
    have hd (p : ℕ) : 2 * dyadicRadius (p + 1) = dyadicRadius p := by
      unfold dyadicRadius
      rw [pow_succ]
      ring
    have hp (p : ℕ) := h (dyadicRadius (p + 1)) (by unfold dyadicRadius; positivity)
    simp only [hd] at hp
    exact le_antisymm
      (iSup_le fun p ↦ (hp p).2.trans (le_iSup (fun q ↦ A (dyadicRadius q)) (p + 1)))
      (iSup_le fun p ↦ (hp p).1.trans (le_iSup (fun q ↦ S (dyadicRadius q)) p))
  cases policy with
  | ambient => cases σ <;> rfl
  | self =>
    cases σ with
    | lower =>
      exact hsup _ _ (bsDimensionIndependentOfCoverCenters_lower T hT u hu E hpos)
    | upper =>
      exact hsup _ _ (bsDimensionIndependentOfCoverCenters_modified T hT u hu E hpos)

/-- The self-centered lower BS dimension at scale `r` converges to the lower BS dimension as
`r → 0⁺`. -/
private theorem tendsto_lowerBSDimensionAtWithCenters_self :
    Tendsto (fun r : ℝ => lowerBSDimensionAtWithCenters .self T u E r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (lowerBSDimension T u E)) := by
  have h1 : Tendsto (fun r => lowerBSDimensionAt T u E r) (𝓝[Set.Ioi 0] 0) (𝓝 (lowerBSDimension T
    u E)) := lowerBSMass_scale_limit T u E
  have h_domain : Tendsto (fun r : ℝ => r / 2) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
    have h_div : Tendsto (fun r : ℝ => r / 2) (𝓝 0) (𝓝 (0 / 2)) := (@tendsto_id ℝ _).div_const 2
    have h_div' : Tendsto (fun r : ℝ => r / 2) (𝓝 0) (𝓝 0) := by simpa using h_div
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Tendsto.mono_left h_div' nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 0 < r := hr
      exact half_pos hr'
  have h3 : Tendsto (fun r => lowerBSDimensionAt T u E (r / 2)) (𝓝[Set.Ioi 0] 0) (𝓝
    (lowerBSDimension T u E)) := h1.comp h_domain
  have h12 : ∀ᶠ (r : ℝ) in 𝓝[Set.Ioi 0] 0, lowerBSDimensionAt T u E r ≤
    lowerBSDimensionAtWithCenters .self T u E r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    have hr_half : 0 < r / 2 := half_pos hr'
    have H := bsDimensionIndependentOfCoverCenters_lower T hT u hu E hpos (r / 2) hr_half
    have H_mul : 2 * (r / 2) = r := by ring
    rw [H_mul] at H
    exact H.1
  have h23 : ∀ᶠ (r : ℝ) in 𝓝[Set.Ioi 0] 0, lowerBSDimensionAtWithCenters .self T u E r ≤
    lowerBSDimensionAt T u E (r / 2) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    have hr_half : 0 < r / 2 := half_pos hr'
    have H := bsDimensionIndependentOfCoverCenters_lower T hT u hu E hpos (r / 2) hr_half
    have H_mul : 2 * (r / 2) = r := by ring
    rw [H_mul] at H
    exact H.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h3 h12 h23

/-- The self-centered modified upper BS dimension at scale `r` converges to the upper BS
dimension as `r → 0⁺`. -/
private theorem tendsto_modifiedUpperBSDimensionWithCenters_self :
    Tendsto (fun r : ℝ => modifiedUpperBSDimensionWithCenters .self T u E r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (upperBSDimension T u E)) := by
  have h1 : Tendsto (fun r => modifiedUpperBSDimension T u E r) (𝓝[Set.Ioi 0] 0) (𝓝
    (upperBSDimension T u E)) := upperBSDimension_radius_limit T u E
  have h_domain : Tendsto (fun r : ℝ => r / 2) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
    have h_div : Tendsto (fun r : ℝ => r / 2) (𝓝 0) (𝓝 (0 / 2)) := (@tendsto_id ℝ _).div_const 2
    have h_div' : Tendsto (fun r : ℝ => r / 2) (𝓝 0) (𝓝 0) := by simpa using h_div
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Tendsto.mono_left h_div' nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 0 < r := hr
      exact half_pos hr'
  have h3 : Tendsto (fun r => modifiedUpperBSDimension T u E (r / 2)) (𝓝[Set.Ioi 0] 0) (𝓝
    (upperBSDimension T u E)) := h1.comp h_domain
  have h12 : ∀ᶠ (r : ℝ) in 𝓝[Set.Ioi 0] 0, modifiedUpperBSDimension T u E r ≤
    modifiedUpperBSDimensionWithCenters .self T u E r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    have hr_half : 0 < r / 2 := half_pos hr'
    have H := bsDimensionIndependentOfCoverCenters_modified T hT u hu E hpos (r / 2) hr_half
    have H_mul : 2 * (r / 2) = r := by ring
    rw [H_mul] at H
    exact H.1
  have h23 : ∀ᶠ (r : ℝ) in 𝓝[Set.Ioi 0] 0, modifiedUpperBSDimensionWithCenters .self T u E r ≤
    modifiedUpperBSDimension T u E (r / 2) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    have hr_half : 0 < r / 2 := half_pos hr'
    have H := bsDimensionIndependentOfCoverCenters_modified T hT u hu E hpos (r / 2) hr_half
    have H_mul : 2 * (r / 2) = r := by ring
    rw [H_mul] at H
    exact H.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h3 h12 h23

/-- Both center policies converge to the existing dimensions along all positive radii.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_limit (policy : CoverCenterPolicy) (σ : LimitSide) :
    Tendsto (fun r => σ.choose (lowerBSDimensionAtWithCenters policy T u E r,
      modifiedUpperBSDimensionWithCenters policy T u E r)) (𝓝[Set.Ioi 0] 0)
        (𝓝 (σ.choose (lowerBSDimension T u E, upperBSDimension T u E))) := by
  cases policy
  · cases σ
    · dsimp [LimitSide.choose]
      have H : (fun r => lowerBSDimensionAtWithCenters CoverCenterPolicy.ambient T u E r) = (fun r
        => lowerBSDimensionAt T u E r) := by ext r; rfl
      rw [H]
      exact lowerBSMass_scale_limit T u E
    · dsimp [LimitSide.choose]
      have H : (fun r => modifiedUpperBSDimensionWithCenters CoverCenterPolicy.ambient T u E r) =
        (fun r => modifiedUpperBSDimension T u E r) := by ext r; rfl
      rw [H]
      exact upperBSDimension_radius_limit T u E
  · cases σ
    · dsimp [LimitSide.choose]
      exact tendsto_lowerBSDimensionAtWithCenters_self T hT u hu E hpos
    · dsimp [LimitSide.choose]
      exact tendsto_modifiedUpperBSDimensionWithCenters_self T hT u hu E hpos

omit [SeparableSpace X] hT hu hpos in
/-- Fixed-order self-centered BS partition sums of `Y ∩ E` at radius `2 * r` are bounded by those
of `Y` at radius `r`, for nonnegative exponents. -/
private lemma bsPartitionSumWithCenters_self_inter_le
    (Y : Set X) (a : ℝ) (ha : 0 ≤ a) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    bsPartitionSumWithCenters .self T u (Y ∩ E) a (2 * r) n ≤
      bsPartitionSumWithCenters .self T u Y a r n := by
  classical
  unfold bsPartitionSumWithCenters
  refine le_iInf fun F => le_iInf fun hF => ?_
  -- Retain useful balls and select a center in each intersection with the target.
  let I := {y : F // ((Y ∩ E) ∩ bowenBall T n y r).Nonempty}
  let z : I → X := fun y => Classical.choose y.property
  have hz (y : I) : z y ∈ (Y ∩ E) ∩ bowenBall T n y.val r :=
    Classical.choose_spec y.property
  let G : Set X := Set.range z
  have hGcount : G.Countable := by
    let : Countable F := hF.1.to_subtype
    exact Set.countable_range z
  have hGE : G ⊆ Y ∩ E := by
    rintro x ⟨y, rfl⟩
    exact (hz y).1
  have hGcover : Y ∩ E ⊆ ⋃ y ∈ G, bowenBall T n y (2 * r) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ F, x ∈ bowenBall T n y r := by
      simpa only [Set.mem_iUnion, exists_prop] using hF.2.2 hx.1
    let i : I := ⟨⟨y, hy⟩, ⟨x, hx, hxy⟩⟩
    have hball : x ∈ bowenBall T n (z i) (2 * r) :=
      relocateCoverBall T (Y ∩ E) n y (z i) r hr (hz i) hxy
    exact Set.mem_iUnion.mpr ⟨z i,
      Set.mem_iUnion.mpr ⟨Set.mem_range_self i, hball⟩⟩
  have hcost : bsPartitionCoverCost T u a (2 * r) n G ≤
      bsPartitionCoverCost T u a r n F := by
    let g : I → G := fun y => ⟨z y, Set.mem_range_self y⟩
    have hg : Function.Surjective g := by
      rintro ⟨x, y, hxy⟩
      exact ⟨y, Subtype.ext hxy⟩
    unfold bsPartitionCoverCost
    calc
      (∑' y : G, bsBallWeight T u a n y (2 * r)) ≤
          ∑' y : I, bsBallWeight T u a n (z y) (2 * r) :=
        ENNReal.tsum_le_tsum_comp_of_surjective hg _
      _ ≤ ∑' y : I, bsBallWeight T u a n y.val r := by
        apply ENNReal.tsum_le_tsum
        intro y
        dsimp only [bsBallWeight]
        apply ENNReal.antitone_rpow_of_nonpos (-a) (neg_nonpos.mpr ha)
        dsimp only [pressureBallWeight]
        apply iSup_mono
        intro w
        apply iSup_mono'
        intro hw
        use relocateCoverBall T (Y ∩ E) n y.val (z y) r hr (hz y) hw
      _ ≤ ∑' y : F, bsBallWeight T u a n y r :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun y : I => y.val) Subtype.val_injective
          (fun y : F => bsBallWeight T u a n y r)
  exact iInf_le_of_le G (iInf_le_of_le ⟨hGcount, hGE, hGcover⟩ hcost)

omit [SeparableSpace X] hT hu hpos in
/-- The self-centered upper BS capacity of `Y ∩ E` at radius `2 * r` is bounded by that of `Y`
at radius `r`: covers of `Y` relocate to centers in the intersection at doubled radius. -/
private lemma upperBSCapacityAtWithCenters_self_inter_le
    (Y : Set X) (r : ℝ) (hr : 0 < r) :
    upperBSCapacityAtWithCenters .self T u (Y ∩ E) (2 * r) ≤
      upperBSCapacityAtWithCenters .self T u Y r := by
  unfold upperBSCapacityAtWithCenters
  refine iInf_mono (fun s => iInf_mono (fun hs => ?_))
  refine le_iInf (fun h => iInf_le_of_le ?_ (le_refl _))
  have H : ∀ᶠ n in atTop, bsPartitionSumWithCenters .self T u (Y ∩ E) s (2 * r) n ≤
    bsPartitionSumWithCenters .self T u Y s r n := by
    apply eventually_atTop.mpr
      ⟨1, fun n _ => bsPartitionSumWithCenters_self_inter_le T u E Y s hs r hr n⟩
  apply lt_of_le_of_lt (limsup_le_limsup H) h

omit [SeparableSpace X] hT hu hpos in
/-- The modified self-centered upper BS dimension at radius `2 * r` is bounded by the
unrestricted self-centered one at radius `r`: intersect each unrestricted piece with `E`. -/
private lemma modifiedUpperBSDimensionWithCenters_self_two_mul_le
    (r : ℝ) (hr : 0 < r) :
    modifiedUpperBSDimensionWithCenters .self T u E (2 * r) ≤
      unrestrictedSelfUpperBSDimension T u E r := by
  unfold modifiedUpperBSDimensionWithCenters unrestrictedSelfUpperBSDimension
  refine le_iInf (fun Y => le_iInf (fun hY => ?_))
  let Y' := fun j => Y j ∩ E
  have hY' : (∀ j, Y' j ⊆ E) ∧ E ⊆ ⋃ j, Y' j := by
    constructor
    · intro j x hx; exact hx.2
    · intro x hx
      have hx' := hY hx
      simp only [Set.mem_iUnion] at hx' ⊢
      rcases hx' with ⟨j, hj⟩
      exact ⟨j, hj, hx⟩
  refine iInf_le_of_le Y' (iInf_le_of_le hY' (iSup_mono (fun j => ?_)))
  exact upperBSCapacityAtWithCenters_self_inter_le T u E (Y j) r hr

omit [SeparableSpace X] hT hu hpos in
/-- The unrestricted self-centered upper BS dimension is bounded by the modified one, since
restricted decompositions are special unrestricted ones. -/
private lemma unrestrictedSelfUpperBSDimension_le_modified
    (r : ℝ) :
    unrestrictedSelfUpperBSDimension T u E r ≤
      modifiedUpperBSDimensionWithCenters .self T u E r := by
  unfold unrestrictedSelfUpperBSDimension modifiedUpperBSDimensionWithCenters
  refine le_iInf (fun Y => le_iInf (fun hY => ?_))
  refine iInf_le_of_le Y (iInf_le_of_le hY.2 (le_refl _))

/-- Relocation compares unrestricted self pieces to their intersections with the target.
No positivity is required on the discarded points outside the target.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_unrestricted_sandwich (r : ℝ) (hr : 0 < r) :
    unrestrictedSelfUpperBSDimension T u E r ≤
        modifiedUpperBSDimensionWithCenters .self T u E r ∧
      modifiedUpperBSDimensionWithCenters .self T u E (2 * r) ≤
        unrestrictedSelfUpperBSDimension T u E r := by
  have _ := hT
  have _ := hu
  have _ := hpos
  have _ := (inferInstance : SeparableSpace X)
  exact ⟨unrestrictedSelfUpperBSDimension_le_modified T u E r,
         modifiedUpperBSDimensionWithCenters_self_two_mul_le T u E r hr⟩

/-- Unrestricted self BS pieces give the same scale-zero modified upper dimension.
Blueprint node `geometry:bs-centers`. -/
theorem bsDimensionIndependentOfCoverCenters_unrestricted :
    Tendsto (unrestrictedSelfUpperBSDimension T u E) (𝓝[Set.Ioi 0] 0)
      (𝓝 (upperBSDimension T u E)) := by
  have h1 : Tendsto (fun r => modifiedUpperBSDimensionWithCenters .self T u E r) (𝓝[Set.Ioi 0] 0)
    (𝓝 (upperBSDimension T u E)) :=
    bsDimensionIndependentOfCoverCenters_limit T hT u hu E hpos .self .upper
  have h_map : Tendsto (fun r : ℝ => 2 * r) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
    have ht1 : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 (2 * 0)) := (tendsto_id : Tendsto (fun r : ℝ
      => r) (𝓝 0) (𝓝 0)).const_mul (2:ℝ)
    have ht2 : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
      have h0 : (2 * 0 : ℝ) = 0 := by ring
      rwa [h0] at ht1
    apply tendsto_inf.mpr
    constructor
    · exact ht2.mono_left nhdsWithin_le_nhds
    · apply tendsto_principal.mpr
      apply eventually_of_mem self_mem_nhdsWithin
      intro r hr
      have h2_pos : (0:ℝ) < 2 := by linarith
      exact mul_pos h2_pos hr
  have h2 : Tendsto (fun r => modifiedUpperBSDimensionWithCenters .self T u E (2 * r)) (𝓝[Set.Ioi
    0] 0) (𝓝 (upperBSDimension T u E)) :=
    h1.comp h_map
  have H1 : (fun x => modifiedUpperBSDimensionWithCenters .self T u E (2 * x)) ≤ᶠ[𝓝[Set.Ioi 0] 0]
    unrestrictedSelfUpperBSDimension T u E := by
    refine eventually_of_mem self_mem_nhdsWithin (fun r hr => ?_)
    exact (bsDimensionIndependentOfCoverCenters_unrestricted_sandwich T hT u hu E hpos r hr).2
  have H2 : unrestrictedSelfUpperBSDimension T u E ≤ᶠ[𝓝[Set.Ioi 0] 0] (fun x =>
    modifiedUpperBSDimensionWithCenters .self T u E x) := by
    refine eventually_of_mem self_mem_nhdsWithin (fun r hr => ?_)
    exact (bsDimensionIndependentOfCoverCenters_unrestricted_sandwich T hT u hu E hpos r hr).1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 H1 H2

end BS

end Kolmogorov.PointToSet
