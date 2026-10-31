/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Defs
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension
import KolmogorovMathlib.PointToSet.PackingEquivalences.Defs
import KolmogorovMathlib.PointToSet.Pressure.Defs
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Upper

/-!
# Cover centers and relocation

This module defines ambient and self-centered covering policies for pressure and
Barreira–Schmeling dimension (blueprint node `geometry:center-policies`). Modified upper
quantities use countable decompositions into subsets of the target, with centers chosen
separately for each piece.

Relocating a useful Bowen ball to a point of the target doubles its radius. The resulting
supremum weights incur a potential-variation error for pressure and no error for
nonnegative BS exponents (blueprint node `geometry:center-relocation`). The pressure and
BS dimension independence modules use these comparisons, together with the vanishing of
variation for uniformly continuous potentials, to identify the scale-zero quantities.
-/

namespace Kolmogorov.PointToSet

open Filter TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-- The permitted centers of a cover, relative to the set being covered.
Blueprint node `geometry:center-policies`. -/
inductive CoverCenterPolicy where
  /-- Any point of the ambient metric space may be a center. -/
  | ambient
  /-- Every center must belong to the particular set being covered. -/
  | self

/-- Lower sup-weight pressure content with the selected center restriction.
Blueprint node `geometry:center-policies`. -/
noncomputable def lowerContentWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (f : X → ℝ) (E : Set X) (s r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  match policy with
  | .ambient => lowerContent T f .supremum E s r N
  | .self => ⨅ C : BowenCoverFamily X,
      ⨅ (_ : IsBowenCover T E r N C ∧ ∀ j, C.center j ∈ E),
        bowenCoverCost T f .supremum s r C

/-- The lower content limit retains the existing positive-cutoff convention.
Blueprint node `geometry:center-policies`. -/
noncomputable def lowerContentLimitWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (f : X → ℝ) (E : Set X) (s r : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), lowerContentWithCenters policy T f E s r N

/-- The signed lower critical pressure for the chosen policy at one radius.
Blueprint node `geometry:center-policies`. -/
noncomputable def lowerPressureAtWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (f : X → ℝ) (E : Set X) (r : ℝ) : EReal :=
  ⨅ s : ℝ, ⨅ (_ : lowerContentLimitWithCenters policy T f E s r = 0), (s : EReal)

/-- The fixed-order sup-weight partition infimum with the selected centers.
Countable sets of centers suffice after deleting repeated terms.
Blueprint node `geometry:center-policies`. -/
noncomputable def partitionSumWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (f : X → ℝ) (E : Set X) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  match policy with
  | .ambient => partitionSum T f .supremum E n r
  | .self => ⨅ F : Set X,
      ⨅ (_ : F.Countable ∧ F ⊆ E ∧ E ⊆ ⋃ y ∈ F, bowenBall T n y r),
        partitionCoverCost T f .supremum F n r

/-- Upper pressure capacity uses the logarithmic rate of the policy partition sums.
Blueprint node `geometry:center-policies`. -/
noncomputable def upperCapacityWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (f : X → ℝ) (E : Set X) (r : ℝ) : EReal :=
  limsup (pressureRate (fun n ↦ partitionSumWithCenters policy T f E n r)) atTop

/-- Countable pressure modification with pieces inside the target; self centers lie in
each piece separately. Blueprint node `geometry:center-policies`. -/
noncomputable def modifiedUpperPressureWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (f : X → ℝ) (E : Set X) (r : ℝ) : EReal :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ E) ∧ E ⊆ ⋃ j, Y j),
    ⨆ j, upperCapacityWithCenters policy T f (Y j) r

/-- The separate variant with unrestricted pieces and centers in each such piece.
No same-radius equality with the restricted self modification is built into this definition.
Blueprint node `geometry:center-policies`. -/
noncomputable def unrestrictedSelfUpperPressure (T : X → X) (f : X → ℝ)
    (E : Set X) (r : ℝ) : EReal :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : E ⊆ ⋃ j, Y j),
    ⨆ j, upperCapacityWithCenters .self T f (Y j) r

/-- Scale-zero pressure for either the lower or countably modified upper policy quantity.
Blueprint node `geometry:center-policies`. -/
noncomputable def coverCenterPressure (policy : CoverCenterPolicy) (σ : LimitSide)
    (T : X → X) (f : X → ℝ) (E : Set X) : EReal :=
  limsup (fun r ↦ σ.choose (lowerPressureAtWithCenters policy T f E r,
    modifiedUpperPressureWithCenters policy T f E r)) (𝓝[Set.Ioi 0] 0)

/-- Lower BS cutoff mass restricts the existing cover class and uses its unchanged BS cost.
Blueprint node `geometry:center-policies`. -/
noncomputable def lowerBSMassWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (u : X → ℝ) (E : Set X) (s r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  match policy with
  | .ambient => lowerBSMass T u E s r N
  | .self => ⨅ C : BowenCoverFamily X,
      ⨅ (_ : IsBowenCover T E r N C ∧ ∀ j, C.center j ∈ E), bsCoverCost T u s r C

/-- The lower BS mass limit takes the supremum over positive order cutoffs.
Blueprint node `geometry:center-policies`. -/
noncomputable def lowerBSMassLimitWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (u : X → ℝ) (E : Set X) (s r : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), lowerBSMassWithCenters policy T u E s r N

/-- Lower BS dimension is the nonnegative zero threshold of the policy mass limit.
Blueprint node `geometry:center-policies`. -/
noncomputable def lowerBSDimensionAtWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (u : X → ℝ) (E : Set X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : lowerBSMassLimitWithCenters policy T u E s r = 0), ENNReal.ofReal s

/-- Fixed-order BS covering infima keep the global sup-weight at the specified radius.
Blueprint node `geometry:center-policies`. -/
noncomputable def bsPartitionSumWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (u : X → ℝ) (E : Set X) (s r : ℝ) (n : ℕ) : ℝ≥0∞ :=
  match policy with
  | .ambient => bsPartitionSum T u E s r n
  | .self => ⨅ F : Set X,
      ⨅ (_ : F.Countable ∧ F ⊆ E ∧ E ⊆ ⋃ y ∈ F, bowenBall T n y r),
        bsPartitionCoverCost T u s r n F

/-- Upper BS capacity retains the finite upper-mass threshold for both center policies.
Blueprint node `geometry:center-policies`. -/
noncomputable def upperBSCapacityAtWithCenters (policy : CoverCenterPolicy) (T : X → X)
    (u : X → ℝ) (E : Set X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
    ⨅ (_ : limsup (bsPartitionSumWithCenters policy T u E s r) atTop < ⊤), ENNReal.ofReal s

/-- Modified upper BS dimension restricts pieces to the target and centers to each piece
when the self policy is selected. Blueprint node `geometry:center-policies`. -/
noncomputable def modifiedUpperBSDimensionWithCenters (policy : CoverCenterPolicy)
    (T : X → X) (u : X → ℝ) (E : Set X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ E) ∧ E ⊆ ⋃ j, Y j),
    ⨆ j, upperBSCapacityAtWithCenters policy T u (Y j) r

/-- Unrestricted self BS pieces may contain points outside the positive-average target.
Their capacities still use the finite threshold. Blueprint node `geometry:center-policies`. -/
noncomputable def unrestrictedSelfUpperBSDimension (T : X → X) (u : X → ℝ)
    (E : Set X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : E ⊆ ⋃ j, Y j),
    ⨆ j, upperBSCapacityAtWithCenters .self T u (Y j) r

/-- The scale-zero BS quantity takes the dyadic supremum after any countable modification.
Blueprint node `geometry:center-policies`. -/
noncomputable def coverCenterBSDimension (policy : CoverCenterPolicy) (σ : LimitSide)
    (T : X → X) (u : X → ℝ) (E : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, σ.choose (lowerBSDimensionAtWithCenters policy T u E (dyadicRadius p),
    modifiedUpperBSDimensionWithCenters policy T u E (dyadicRadius p))

/-- Ambient upper pressure capacity is monotone in the covered set. -/
lemma upperCapacity_supremum_mono_set (T : X → X) (f : X → ℝ) (r : ℝ)
    {Y Y' : Set X} (h : Y' ⊆ Y) :
    upperCapacity T f .supremum Y' r ≤ upperCapacity T f .supremum Y r := by
  exact limsup_le_limsup (Eventually.of_forall fun n ↦
    pressureRate_le_of_le _ _ n (partitionSum_mono_set T f .supremum h n r))

/-- Ambient pressure pieces may be intersected with the target without changing the
existing modified pressure at the same radius. Blueprint node `geometry:center-policies`. -/
theorem modifiedUpperPressureWithCenters_ambient (T : X → X) (f : X → ℝ)
    (E : Set X) (r : ℝ) :
    modifiedUpperPressureWithCenters .ambient T f E r =
      modifiedUpperPressure T f .supremum E r := by
  unfold modifiedUpperPressureWithCenters modifiedUpperPressure
  unfold upperCapacityWithCenters
  dsimp only [partitionSumWithCenters]
  apply le_antisymm
  · refine le_iInf fun Y ↦ le_iInf fun h ↦ ?_
    let Y' := fun j ↦ Y j ∩ E
    have hY' : (∀ j, Y' j ⊆ E) ∧ E ⊆ ⋃ j, Y' j := by
      refine ⟨fun _ _ hx ↦ hx.2, fun x hx ↦ ?_⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h hx)
      exact Set.mem_iUnion.mpr ⟨j, hj, hx⟩
    refine iInf_le_of_le Y' (iInf_le_of_le hY' (iSup_mono fun j ↦ ?_))
    exact upperCapacity_supremum_mono_set T f r Set.inter_subset_left
  · refine iInf_mono fun Y ↦ le_iInf fun h ↦ ?_
    exact iInf_le_of_le h.2 le_rfl

/-- Relocating a useful ball to a point of the target doubles its radius and contains it.
Blueprint node `geometry:center-relocation`. -/
theorem relocateCoverBall (T : X → X) (E : Set X) (n : ℕ) (y z : X) (r : ℝ)
    (hr : 0 < r) (hz : z ∈ E ∩ bowenBall T n y r) :
    bowenBall T n y r ⊆ bowenBall T n z (2 * r) := by
  have _ := hr
  intro w hw
  rw [bowenBall] at hw hz ⊢
  simp only [Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at hw hz ⊢
  intro k hk
  calc
    dist (T^[k] z) (T^[k] w) ≤
        dist (T^[k] z) (T^[k] y) + dist (T^[k] y) (T^[k] w) := dist_triangle _ _ _
    _ < r + r := add_lt_add (by simpa only [dist_comm] using hz.2 k hk) (hw k hk)
    _ = 2 * r := (two_mul r).symm

/-- The relocated global potential supremum is bounded by the original one plus finite
variation at twice the radius. Blueprint node `geometry:center-relocation`. -/
theorem relocateCoverBall_sup (T : X → X) (f : X → ℝ) (E : Set X) (n : ℕ)
    (y z : X) (r : ℝ) (hr : 0 < r) (hz : z ∈ E ∩ bowenBall T n y r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    bowenPotentialSup T f n y r ≤ bowenPotentialSup T f n z (2 * r) ∧
      bowenPotentialSup T f n z (2 * r) ≤ bowenPotentialSup T f n y r +
        ((n * (potentialVariation f (2 * r)).toReal : ℝ) : EReal) := by
  constructor
  · exact iSup₂_le fun w hw ↦
      le_iSup₂_of_le w (relocateCoverBall T E n y z r hr hz hw) le_rfl
  · refine iSup₂_le fun w hw ↦ ?_
    have hdiff := abs_birkhoffSum_sub_le_mul_variation T f n z w (2 * r) hvar hw
    have hsum : birkhoffSum T f n w ≤
        birkhoffSum T f n z + n * (potentialVariation f (2 * r)).toReal := by
      linarith [(abs_le.mp hdiff).2]
    calc
      ((birkhoffSum T f n w : ℝ) : EReal) ≤
          ((birkhoffSum T f n z + n * (potentialVariation f (2 * r)).toReal : ℝ) :
            EReal) := EReal.coe_le_coe_iff.mpr hsum
      _ = ((birkhoffSum T f n z : ℝ) : EReal) +
          ((n * (potentialVariation f (2 * r)).toReal : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ bowenPotentialSup T f n y r +
          ((n * (potentialVariation f (2 * r)).toReal : ℝ) : EReal) :=
        add_le_add (by exact le_iSup₂_of_le z hz.2 le_rfl) le_rfl

private lemma pressureBallWeight_supremum_le_centered_mul (T : X → X) (f : X → ℝ)
    (n : ℕ) (y : X) (r : ℝ) (hvar : potentialVariation f r < ⊤) :
    pressureBallWeight T f .supremum n y r ≤
      (2 : ℝ≥0∞) ^ (n * (potentialVariation f r).toReal) *
        pressureBallWeight T f .centered n y r := by
  refine iSup₂_le fun z hz ↦ ?_
  have hdiff := abs_birkhoffSum_sub_le_mul_variation T f n y z r hvar hz
  have hsum : birkhoffSum T f n z ≤
      n * (potentialVariation f r).toReal + birkhoffSum T f n y := by
    linarith [(abs_le.mp hdiff).2]
  calc
    (2 : ℝ≥0∞) ^ birkhoffSum T f n z ≤
        (2 : ℝ≥0∞) ^ (n * (potentialVariation f r).toReal + birkhoffSum T f n y) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hsum
    _ = _ := ENNReal.rpow_add _ _ (by norm_num) (by norm_num)

/-- Pressure relocation shifts the real time exponent by the finite variation error.
Blueprint node `geometry:center-relocation`. -/
theorem relocateCoverBall_pressure (T : X → X) (f : X → ℝ) (E : Set X) (n : ℕ)
    (y z : X) (r : ℝ) (hr : 0 < r) (hz : z ∈ E ∩ bowenBall T n y r)
    (hvar : potentialVariation f (2 * r) < ⊤) (t : ℝ) :
    (2 : ℝ≥0∞) ^ (-t * n) * pressureBallWeight T f .supremum n z (2 * r) ≤
      (2 : ℝ≥0∞) ^ (-(t - (potentialVariation f (2 * r)).toReal) * n) *
        pressureBallWeight T f .supremum n y r := by
  have _ := hr
  let c := (potentialVariation f (2 * r)).toReal
  have hweight : pressureBallWeight T f .supremum n z (2 * r) ≤
      (2 : ℝ≥0∞) ^ (n * c) * pressureBallWeight T f .supremum n y r := by
    refine (pressureBallWeight_supremum_le_centered_mul T f n z (2 * r) hvar).trans ?_
    dsimp only [pressureBallWeight]
    exact mul_le_mul' le_rfl (le_iSup₂_of_le z hz.2 le_rfl)
  calc
    (2 : ℝ≥0∞) ^ (-t * n) * pressureBallWeight T f .supremum n z (2 * r) ≤
        (2 : ℝ≥0∞) ^ (-t * n) *
          ((2 : ℝ≥0∞) ^ (n * c) * pressureBallWeight T f .supremum n y r) :=
      mul_le_mul' le_rfl hweight
    _ = (2 : ℝ≥0∞) ^ (-(t - c) * n) *
        pressureBallWeight T f .supremum n y r := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 2
      ring

/-- A nonnegative BS exponent reverses the supremum inequality, so relocation has no
variation penalty. Blueprint node `geometry:center-relocation`. -/
theorem relocateCoverBall_bs (T : X → X) (u : X → ℝ) (E : Set X) (n : ℕ)
    (y z : X) (r : ℝ) (hr : 0 < r) (hz : z ∈ E ∩ bowenBall T n y r)
    (hvar : potentialVariation u (2 * r) < ⊤) (a : ℝ) (ha : 0 ≤ a) :
    bsBallWeight T u a n z (2 * r) ≤ bsBallWeight T u a n y r := by
  have _ := hvar
  apply ENNReal.antitone_rpow_of_nonpos (-a) (neg_nonpos.mpr ha)
  exact iSup₂_le fun w hw ↦
    le_iSup₂_of_le w (relocateCoverBall T E n y z r hr hz hw) le_rfl

section Pressure

variable (T : X → X) (f : X → ℝ) (E : Set X)

/-- Uniform continuity makes the potential variation tend to zero at positive radii. -/
lemma tendsto_potentialVariation_zero (hf : UniformContinuous f) :
    Tendsto (fun r ↦ potentialVariation f r) (𝓝[Set.Ioi 0] 0)
      (𝓝 (0 : ℝ≥0∞)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ (not_lt_bot ha).elim, fun a ha ↦ ?_⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp ha with ⟨ε_nn, h0, h_a⟩
  have h_pos : (0 : ℝ) < ε_nn := ENNReal.coe_pos.mp h0
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp hf ε_nn h_pos
  have Hmem : {r | r < δ} ∈ 𝓝 0 := Iio_mem_nhds hδ_pos
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds Hmem] with r _hr hr_lt
  have H : ∀ x y : X, dist x y ≤ r → ENNReal.ofReal |f x - f y| ≤ ε_nn := by
    intro x y h_dist
    have h_dist' : dist x y < δ := h_dist.trans_lt hr_lt
    have hf_dist := hδ h_dist'
    rw [Real.dist_eq] at hf_dist
    exact (ENNReal.ofReal_le_ofReal hf_dist.le).trans_eq ENNReal.ofReal_coe_nnreal
  unfold potentialVariation
  refine lt_of_le_of_lt ?_ h_a
  refine iSup_le (fun x ↦ iSup_le (fun y ↦ iSup_le (fun h_dist ↦ ?_)))
  exact H x y h_dist

private lemma lowerPressureAt_centered_antitone_radius
    (r R : ℝ) (hrR : r ≤ R) :
    lowerPressureAt T f .centered E R ≤ lowerPressureAt T f .centered E r := by
  have hcontent (s : ℝ) (N : ℕ) :
      lowerContent T f .centered E s R N ≤
        lowerContent T f .centered E s r N := by
    unfold lowerContent
    refine iInf_mono fun C ↦ le_iInf fun hC ↦ ?_
    have hCR : IsBowenCover T E R N C := by
      refine ⟨hC.1, ?_⟩
      intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hC.2 hx)
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at hj ⊢
      intro k hk
      exact lt_of_lt_of_le (hj k hk) hrR
    exact iInf_le_of_le hCR le_rfl
  have hlimit (s : ℝ) :
      lowerContentLimit T f .centered E s R ≤
        lowerContentLimit T f .centered E s r := by
    unfold lowerContentLimit
    exact iSup_mono fun N ↦ iSup_mono fun _ ↦ hcontent s N
  unfold lowerPressureAt
  refine iInf_mono fun s ↦ le_iInf fun hs ↦ ?_
  have hsR : lowerContentLimit T f .centered E s R = 0 :=
    le_antisymm ((hlimit s).trans_eq hs) zero_le
  exact iInf_le_of_le hsR le_rfl

private lemma tendsto_lowerPressureAt_centered :
    Tendsto (fun r ↦ lowerPressureAt T f .centered E r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (lowerPressure T f 0 E)) := by
  have hanti := lowerPressureAt_centered_antitone_radius T f E
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    change a < ⨆ p, ⨆ (_ : 0 ≤ p), lowerPressureAt T f .centered E (dyadicRadius p) at ha
    obtain ⟨p, hp⟩ := lt_iSup_iff.mp ha
    obtain ⟨_, hp⟩ := lt_iSup_iff.mp hp
    have hpos : (0 : ℝ) < dyadicRadius p := by
      unfold dyadicRadius
      positivity
    filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds hpos)] with r hr
    exact hp.trans_le (hanti r (dyadicRadius p) hr)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr_pos : 0 < r := hr
    obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one hr_pos (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hle : lowerPressureAt T f .centered E (dyadicRadius p) ≤ lowerPressure T f 0 E :=
      le_iSup_of_le p (le_iSup_of_le (Nat.zero_le p) le_rfl)
    exact (hanti (dyadicRadius p) r hp.le).trans_lt (hle.trans_lt ha)

private lemma lowerPressureAt_centered_le_supremum (r : ℝ) (hr : 0 < r) :
    lowerPressureAt T f .centered E r ≤ lowerPressureAt T f .supremum E r := by
  refine le_iInf₂ fun s hs ↦ ?_
  have hz : lowerContentLimit T f .centered E s r = 0 :=
    le_antisymm ((lowerContentLimit_centered_le_supremum T f E s _ hr).trans_eq hs) bot_le
  exact iInf₂_le s hz

private lemma bowenCoverCost_supremum_le_centered_shift (r : ℝ)
    (hvar : potentialVariation f r < ⊤) (s : ℝ) (C : BowenCoverFamily X) :
    bowenCoverCost T f .supremum s r C ≤
      bowenCoverCost T f .centered (s - (potentialVariation f r).toReal) r C := by
  unfold bowenCoverCost
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  let n := C.order j
  let y := C.center j
  let c := (potentialVariation f r).toReal
  calc
    (2 : ℝ≥0∞) ^ (-s * n) * pressureBallWeight T f .supremum n y r ≤
        (2 : ℝ≥0∞) ^ (-s * n) *
          ((2 : ℝ≥0∞) ^ (n * c) * pressureBallWeight T f .centered n y r) :=
      mul_le_mul' le_rfl (pressureBallWeight_supremum_le_centered_mul T f n y r hvar)
    _ = (2 : ℝ≥0∞) ^ (-(s - c) * n) * pressureBallWeight T f .centered n y r := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 2
      ring

private lemma lowerContentLimit_supremum_le_centered_shift (r : ℝ)
    (hvar : potentialVariation f r < ⊤) (s : ℝ) :
    lowerContentLimit T f .supremum E s r ≤
      lowerContentLimit T f .centered E (s - (potentialVariation f r).toReal) r := by
  unfold lowerContentLimit lowerContent
  refine iSup_mono fun N ↦ iSup_mono fun _ ↦ iInf_mono fun C ↦ iInf_mono fun _ ↦ ?_
  exact bowenCoverCost_supremum_le_centered_shift T f r hvar s C

private lemma lowerPressureAt_supremum_le_centered_add (r : ℝ)
    (hvar : potentialVariation f r < ⊤) :
    lowerPressureAt T f .supremum E r ≤
      lowerPressureAt T f .centered E r + ((potentialVariation f r).toReal : EReal) := by
  let c := (potentialVariation f r).toReal
  have shift (a b : EReal) : a - (c : EReal) ≤ b ↔ a ≤ b + (c : EReal) :=
    EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
  rw [← shift]
  unfold lowerPressureAt
  simp only [le_iInf_iff]
  intro t ht
  rw [shift]
  have hz : lowerContentLimit T f .supremum E (t + c) r = 0 := by
    have h := lowerContentLimit_supremum_le_centered_shift T f E r hvar (t + c)
    change lowerContentLimit T f .supremum E (t + c) r ≤
      lowerContentLimit T f .centered E (t + c - c) r at h
    rw [add_sub_cancel_right, ht] at h
    exact le_antisymm h bot_le
  have hb : (⨅ s : ℝ, ⨅ (_ : lowerContentLimit T f .supremum E s r = 0), (s : EReal)) ≤
      ((t + c : ℝ) : EReal) := iInf_le_of_le (t + c) (iInf_le_of_le hz le_rfl)
  simpa only [EReal.coe_add] using hb

/-- Ambient lower sup-weight pressure converges to lower pressure along positive radii. -/
lemma tendsto_lowerPressureAt_supremum (hf : UniformContinuous f) :
    Tendsto (fun r ↦ lowerPressureAt T f .supremum E r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (lowerPressure T f 0 E)) := by
  have hc := tendsto_lowerPressureAt_centered T f E
  have hv := tendsto_potentialVariation_zero f hf
  have he : Tendsto
      (fun r ↦ ((potentialVariation f r).toReal : EReal))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hv
    exact EReal.tendsto_coe.mpr hreal
  have hadd : Tendsto
      (fun r ↦ lowerPressureAt T f .centered E r +
        ((potentialVariation f r).toReal : EReal))
      (𝓝[Set.Ioi 0] 0) (𝓝 (lowerPressure T f 0 E)) := by
    have ha : ContinuousAt
        (fun p : EReal × EReal ↦ p.1 + p.2)
        (lowerPressure T f 0 E, (0 : EReal)) :=
      EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
    simpa only [Function.comp_def, add_zero] using
      ha.tendsto.comp (hc.prodMk_nhds he)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hc hadd ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact lowerPressureAt_centered_le_supremum T f E r hr
  · have hfin : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
        potentialVariation f r < ⊤ :=
      hv.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))
    filter_upwards [hfin] with r hvar
    exact lowerPressureAt_supremum_le_centered_add T f E r hvar

/-- Ambient modified upper sup-weight pressure converges to upper pressure at scale zero. -/
lemma tendsto_modifiedUpperPressure_supremum [SeparableSpace X]
    (hT : Continuous T) (hf : UniformContinuous f) :
    Tendsto (fun r ↦ modifiedUpperPressure T f .supremum E r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (upperPressure T f 0 E)) := by
  exact pressureEquivalence_covering_limit
    (X := X) (T := T) (hT := hT) (f := f) (hf := hf) (Z := E)

private lemma lowerContentLimit_le_self (r t : ℝ) :
    lowerContentLimit T f .supremum E t r ≤
      lowerContentLimitWithCenters .self T f E t r := by
  unfold lowerContentLimit lowerContentLimitWithCenters lowerContentWithCenters lowerContent
  refine iSup_mono fun N ↦ iSup_mono fun _ ↦ iInf_mono fun C ↦ le_iInf fun h ↦ ?_
  exact iInf_le_of_le h.1 le_rfl

/-- Recentering a cover at points of `E` costs at most a shift of the exponent by the
potential variation at twice the radius. -/
theorem lowerContentLimit_self_le_shift (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) (t : ℝ) :
    lowerContentLimitWithCenters .self T f E t (2 * r) ≤
      lowerContentLimit T f .supremum E (t - (potentialVariation f (2 * r)).toReal) r := by
  classical
  unfold lowerContentLimitWithCenters lowerContentLimit
  refine iSup_mono fun N ↦ ?_
  refine iSup_mono fun _ ↦ ?_
  unfold lowerContentWithCenters lowerContent
  refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
  let S : Set ℕ := {n | ∃ hn : n ∈ C.index,
    (E ∩ bowenBall T (C.order ⟨n, hn⟩)
      (C.center ⟨n, hn⟩) r).Nonempty}
  let p : S → C.index := fun j ↦
    ⟨j.val, Classical.choose j.property⟩
  let z : S → X := fun j ↦
    Classical.choose (Classical.choose_spec j.property)
  have hz (j : S) :
      z j ∈ E ∩ bowenBall T (C.order (p j)) (C.center (p j)) r :=
    Classical.choose_spec (Classical.choose_spec j.property)
  let D : BowenCoverFamily X :=
    { index := S, center := z, order := fun j ↦ C.order (p j) }
  have hD : IsBowenCover T E (2 * r) N D := by
    constructor
    · intro j
      exact hC.1 (p j)
    · intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hC.2 hx)
      let k : S := ⟨j.val, ⟨j.property, ⟨x, hx, hj⟩⟩⟩
      have hp : p k = j := Subtype.ext rfl
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      apply relocateCoverBall T E (C.order (p k))
        (C.center (p k)) (z k) r hr (hz k)
      simpa only [hp] using hj
  refine iInf_le_of_le D
    (iInf_le_of_le ⟨hD, fun j ↦ (hz j).1⟩ ?_)
  let g : C.index → ℝ≥0∞ := fun j ↦
    (2 : ℝ≥0∞) ^
      (-(t - (potentialVariation f (2 * r)).toReal) * (C.order j : ℝ)) *
      pressureBallWeight T f .supremum (C.order j) (C.center j) r
  have hterm (j : S) :
      (2 : ℝ≥0∞) ^ (-t * (D.order j : ℝ)) *
        pressureBallWeight T f .supremum (D.order j) (D.center j) (2 * r)
        ≤ g (p j) :=
    relocateCoverBall_pressure T f E (C.order (p j))
      (C.center (p j)) (z j) r hr (hz j) hvar t
  have hp : Function.Injective p := fun a b hab ↦
    Subtype.ext (congrArg (fun (x : C.index) ↦ x.val) hab)
  exact (ENNReal.tsum_le_tsum hterm).trans
    (ENNReal.tsum_comp_le_tsum_of_injective hp g)

private lemma lowerPressureAt_le_self (r : ℝ) :
    lowerPressureAt T f .supremum E r ≤ lowerPressureAtWithCenters .self T f E r := by
  refine le_iInf₂ fun t ht ↦ ?_
  have hz : lowerContentLimit T f .supremum E t r = 0 :=
    le_antisymm ((lowerContentLimit_le_self T f E r t).trans_eq ht) bot_le
  exact iInf₂_le t hz

/-- The lower pressure with centers in `E` at radius `2 r` exceeds the supremum-weight lower
pressure at radius `r` by at most the potential variation at `2 r`. -/
theorem lowerPressureAt_self_le_add_variation (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    lowerPressureAtWithCenters .self T f E (2 * r) ≤
      lowerPressureAt T f .supremum E r + ((potentialVariation f (2 * r)).toReal : EReal) := by
  let c : ℝ := (potentialVariation f (2 * r)).toReal
  change lowerPressureAtWithCenters .self T f E (2 * r) ≤
    lowerPressureAt T f .supremum E r + (c : EReal)
  apply (EReal.sub_le_iff_le_add
    (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c))).mp
  unfold lowerPressureAt
  refine le_iInf (fun t ↦ le_iInf (fun ht ↦ ?_))
  have hz : lowerContentLimitWithCenters .self T f E (t + c) (2 * r) = 0 := by
    have h := lowerContentLimit_self_le_shift T f E r hr hvar (t + c)
    have heq : t + c - (potentialVariation f (2 * r)).toReal = t := by
      dsimp [c]
      ring
    rw [heq, ht] at h
    exact le_antisymm h bot_le
  have hb : lowerPressureAtWithCenters .self T f E (2 * r) ≤
      ((t + c : ℝ) : EReal) := by
    unfold lowerPressureAtWithCenters
    exact iInf_le_of_le (t + c) (iInf_le _ hz)
  exact EReal.sub_le_of_le_add
    (by simpa only [EReal.coe_add] using hb)

/-- Self-centered lower pressure lies between ambient pressure at twice the radius and
ambient pressure at the original radius plus its variation error.
Blueprint node `geometry:center-relocation`. -/
lemma lowerPressureAt_self_bounds (r : ℝ) (hr : 0 < r)
    (hvar : potentialVariation f (2 * r) < ⊤) :
    lowerPressureAt T f .supremum E (2 * r) ≤
        lowerPressureAtWithCenters .self T f E (2 * r) ∧
      lowerPressureAtWithCenters .self T f E (2 * r) ≤
        lowerPressureAt T f .supremum E r +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
  exact ⟨lowerPressureAt_le_self T f E (2 * r),
    lowerPressureAt_self_le_add_variation T f E r hr hvar⟩

end Pressure

end Kolmogorov.PointToSet
