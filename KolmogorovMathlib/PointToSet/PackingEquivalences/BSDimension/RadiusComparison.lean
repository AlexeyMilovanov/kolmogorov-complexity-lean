/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.PackingSeparatedDefs

/-!
# Radius comparison for Barreira–Schmeling packing and separated sums

This module proves the radius monotonicity and scale limits of BS packing content
and separated capacity, including their values on the empty set and the divergence
of packing content at negative exponents (blueprint node `pack:bs-definitions`).
On sets with a uniform positive lower bound for Birkhoff averages, increasing the
exponent turns finite limiting upper mass into zero mass, for both separated sums
and covering sums (`pack:bs-finite-zero`). `CoveringComparison` uses these estimates
to compare covering and separated thresholds after refinement into positive pieces.
-/

namespace Kolmogorov.PointToSet

open Filter TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

private lemma bsPackingSum_antitone_radius (T : X → X) (u : X → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (F : Set (X × ℕ)) :
    Antitone (fun r ↦ bsPackingSum T u a r F) := by
  intro r₁ r₂ hr
  exact ENNReal.tsum_le_tsum fun p ↦
    bsBallWeight_le_of_radius_le T u a ha p.val.2 p.val.1 hr

private lemma IsBowenPacking.mono_radius (T : X → X) (Z : Set X)
    (N : ℕ) (F : Set (X × ℕ)) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (hF : IsBowenPacking T Z r₂ N F) : IsBowenPacking T Z r₁ N F := by
  refine ⟨hF.1, hF.2.1, ?_⟩
  intro a ha b hb hab
  exact (hF.2.2 ha hb hab).mono
    (bowenBall_subset_of_le T a.2 a.1 hr) (bowenBall_subset_of_le T b.2 b.1 hr)

private lemma bsPackingContent_antitone_radius (T : X → X) (u : X → ℝ)
    (Z : Set X) (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    Antitone (fun r ↦ bsPackingContent T u Z a r N) := by
  intro r₁ r₂ hr
  exact iSup_mono fun F ↦ iSup_mono' fun hF ↦
    ⟨IsBowenPacking.mono_radius T Z N F hr hF, bsPackingSum_antitone_radius T u a ha F hr⟩

private lemma bsPackingPrecontent_antitone_radius (T : X → X) (u : X → ℝ)
    (Z : Set X) (a : ℝ) (ha : 0 ≤ a) :
    Antitone (bsPackingPrecontent T u Z a) := by
  intro r₁ r₂ hr
  exact iInf_mono fun N ↦ iInf_mono fun _ ↦
    bsPackingContent_antitone_radius T u Z a ha N hr

/-- Smaller positive radii increase the outer BS content at nonnegative exponents.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_content_radius (T : X → X) (u : X → ℝ)
    (Z : Set X) (a : ℝ) (ha : 0 ≤ a) :
    AntitoneOn (bsPackingOuterEnvelope T u Z a) (Set.Ioi 0) := by
  intro r₁ _ r₂ _ hr
  exact iInf_mono fun Y ↦ iInf_mono fun _ ↦ ENNReal.tsum_le_tsum fun j ↦
    bsPackingPrecontent_antitone_radius T u (Y j) a ha hr

/-- Packing BS thresholds increase as the positive radius decreases.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_radius (T : X → X) (u : X → ℝ) (Z : Set X) :
    AntitoneOn (packingBSDimensionAt T u Z) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ hr
  refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hzero ↦ ?_
  have hzero₂ : bsPackingOuterEnvelope T u Z a r₂ = 0 :=
    nonpos_iff_eq_zero.mp ((bsPackingSeparatedDefinitions_content_radius
      T u Z a ha hr₁ hr₂ hr).trans_eq hzero)
  exact iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le hzero₂ le_rfl))

private lemma bsPartitionCoverCost_le_of_radius_le (T : X → X) (u : X → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (F : Set X) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    bsPartitionCoverCost T u a r₂ n F ≤ bsPartitionCoverCost T u a r₁ n F := by
  exact ENNReal.tsum_le_tsum fun y ↦ bsBallWeight_le_of_radius_le T u a ha n y hr

/-- Both the available separated sets and their BS weights increase at smaller radii.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_sum_radius (T : X → X) (u : X → ℝ)
    (Z : Set X) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n) :
    AntitoneOn (fun r => separatedBSSum T u Z a r n) (Set.Ioi 0) := by
  have _ := hn
  intro r₁ _ r₂ _ hr
  refine iSup_mono fun F ↦ iSup_mono' fun hF ↦ ?_
  refine ⟨⟨hF.1, fun x hx y hy hxy ↦ hr.trans (hF.2 hx hy hxy)⟩, ?_⟩
  exact bsPartitionCoverCost_le_of_radius_le T u a ha n F hr

private lemma separatedBSZeroCapacityAt_antitone_radius
    (T : X → X) (u : X → ℝ) (Z : Set X) :
    AntitoneOn (separatedBSZeroCapacityAt T u Z) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ hr
  refine iInf_mono fun a ↦ iInf_mono' fun ha ↦ ⟨ha, ?_⟩
  refine iInf_mono' fun hzero ↦ ⟨?_, le_rfl⟩
  apply nonpos_iff_eq_zero.mp
  apply le_trans (limsup_le_limsup ?_) (le_of_eq hzero)
  exact eventually_atTop.mpr ⟨1, fun n hn ↦
    bsPackingSeparatedDefinitions_sum_radius T u Z a ha n hn hr₁ hr₂ hr⟩

/-- Modified separated zero thresholds increase as the positive radius decreases.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_separated_radius (T : X → X)
    (u : X → ℝ) (Z : Set X) :
    AntitoneOn (modifiedSeparatedBSDimension T u Z) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ hr
  exact iInf_mono fun Y ↦ iInf_mono fun _ ↦ iSup_mono fun j ↦
    separatedBSZeroCapacityAt_antitone_radius T u (Y j) hr₁ hr₂ hr

/-- Dyadic radii compute the supremum of an antitone function on positive radii. -/
private lemma sSup_image_Ioi_eq_iSup_dyadicRadius (f : ℝ → ℝ≥0∞)
    (hf : AntitoneOn f (Set.Ioi 0)) :
    sSup (f '' Set.Ioi 0) = ⨆ p, f (dyadicRadius p) := by
  have hpos (p : ℕ) : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  refine le_antisymm (sSup_le ?_) (iSup_le fun p ↦ le_sSup ⟨_, hpos p, rfl⟩)
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact (hf (hpos p) hr hp.le).trans (le_iSup (fun q ↦ f (dyadicRadius q)) p)

/-- The packing dyadic scale supremum equals the limit over all positive real radii.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_scale_limit (T : X → X) (u : X → ℝ)
    (Z : Set X) :
    Tendsto (packingBSDimensionAt T u Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (packingBSDimension T u Z)) := by
  change Tendsto _ _ (𝓝 (⨆ p, packingBSDimensionAt T u Z (dyadicRadius p)))
  rw [← sSup_image_Ioi_eq_iSup_dyadicRadius _ (bsPackingSeparatedDefinitions_radius T u Z)]
  exact (bsPackingSeparatedDefinitions_radius T u Z).tendsto_nhdsGT (OrderTop.bddAbove _)

/-- The separated scale supremum is a limit after countable modification.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_separated_scale_limit (T : X → X)
    (u : X → ℝ) (Z : Set X) :
    Tendsto (modifiedSeparatedBSDimension T u Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (separatedBSDimension T u Z)) := by
  change Tendsto _ _ (𝓝 (⨆ p, modifiedSeparatedBSDimension T u Z (dyadicRadius p)))
  rw [← sSup_image_Ioi_eq_iSup_dyadicRadius _
    (bsPackingSeparatedDefinitions_separated_radius T u Z)]
  exact (bsPackingSeparatedDefinitions_separated_radius T u Z).tendsto_nhdsGT
    (OrderTop.bddAbove _)

/-- A point with positive lower average forces infinite packing content at negative exponents. -/
private lemma bsPackingContent_eq_top_of_neg
    (T : X → X) (u : X → ℝ) (Z : Set X) (x : X) (hx : x ∈ Z)
    (havg : 0 < lowerBirkhoffAverage T u x) (a r : ℝ) (ha : a < 0) (hr : 0 < r)
    (N : ℕ) : bsPackingContent T u Z a r N = ⊤ := by
  obtain ⟨q, hq, hqx⟩ := EReal.exists_rat_btwn_of_lt havg
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum : ∀ᶠ n in atTop, (q : ℝ) * n ≤ birkhoffSum T u n x := by
    filter_upwards [eventually_lt_of_lt_liminf hqx, eventually_gt_atTop 0] with n hn hnpos
    have hdiv : (q : ℝ) < birkhoffSum T u n x / n := EReal.coe_lt_coe_iff.mp hn
    exact ((lt_div_iff₀ (Nat.cast_pos.mpr hnpos)).mp hdiv).le
  have hpack (n : ℕ) (hn : max 1 N ≤ n) : IsBowenPacking T Z r N {(x, n)} := by
    refine ⟨Set.countable_singleton _, ?_, ?_⟩
    · rintro p (rfl : p = (x, n))
      exact ⟨hx, hn⟩
    · rintro p (rfl : p = (x, n)) p' (rfl : p' = (x, n)) hne
      exact (hne rfl).elim
  have hweight (n : ℕ) (hn : (q : ℝ) * n ≤ birkhoffSum T u n x) :
      (2 : ENNReal) ^ (-a * (q : ℝ) * n) ≤ bsPackingSum T u a r {(x, n)} := by
    have hbase : (2 : ENNReal) ^ ((q : ℝ) * n) ≤
        pressureBallWeight T u .supremum n x r :=
      (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hn).trans
        (le_iSup_of_le x (le_iSup_of_le (self_mem_bowenBall T n x r hr) le_rfl))
    have hpow := ENNReal.rpow_le_rpow hbase (neg_nonneg.mpr ha.le)
    rw [← ENNReal.rpow_mul] at hpow
    have hexp : (q : ℝ) * n * -a = -a * (q : ℝ) * n := by ring
    rw [hexp] at hpow
    exact hpow.trans (ENNReal.le_tsum
      (f := fun p : ({(x, n)} : Set (X × ℕ)) ↦ bsBallWeight T u a p.val.2 p.val.1 r)
      ⟨(x, n), rfl⟩)
  have ht : Tendsto (fun n : ℕ ↦ (2 : ENNReal) ^ (-a * (q : ℝ) * n)) atTop (𝓝 ⊤) :=
    (ENNReal.tendsto_rpow_atTop_of_one_lt_base ENNReal.one_lt_two).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos (neg_pos.mpr ha) hqpos))
  apply eq_top_iff.mpr
  apply le_of_tendsto ht
  filter_upwards [hsum, eventually_ge_atTop (max 1 N)] with n hn hnN
  exact (hweight n hn).trans
    (le_iSup_of_le {(x, n)} (le_iSup_of_le (hpack n hnN) le_rfl))

private lemma bsPackingPrecontent_eq_top_of_neg
    (T : X → X) (u : X → ℝ) (Z : Set X) (x : X) (hx : x ∈ Z)
    (havg : 0 < lowerBirkhoffAverage T u x) (a r : ℝ) (ha : a < 0) (hr : 0 < r) :
    bsPackingPrecontent T u Z a r = ⊤ := by
  exact eq_top_iff.mpr (le_iInf fun N ↦ le_iInf fun _ ↦
    (bsPackingContent_eq_top_of_neg T u Z x hx havg a r ha hr N).ge)

/-- Negative parameters have infinite packing outer content on nonempty positive loci.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_negative (T : X → X) (u : X → ℝ)
    (Z : Set X) (hne : Z.Nonempty) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (a r : ℝ) (ha : a < 0) (hr : 0 < r) : bsPackingOuterEnvelope T u Z a r = ⊤ := by
  refine eq_top_iff.mpr (le_iInf fun Y ↦ le_iInf fun hY ↦ ?_)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (hY.2 hx)
  calc
    ⊤ = bsPackingPrecontent T u (Y k) a r :=
      (bsPackingPrecontent_eq_top_of_neg T u (Y k) x hxk (hZ x hx) a r ha hr).symm
    _ ≤ ∑' j, bsPackingPrecontent T u (Y j) a r :=
      ENNReal.le_tsum (f := fun j ↦ bsPackingPrecontent T u (Y j) a r) k

private lemma bsPackingPrecontent_empty (T : X → X) (u : X → ℝ) (a r : ℝ) :
    bsPackingPrecontent T u ∅ a r = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine iInf_le_of_le 1 (iInf_le_of_le le_rfl (iSup_le fun F ↦ iSup_le fun hF ↦ ?_))
  have hempty : F = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact fun p hp ↦ (hF.2.1 p hp).1
  simp [bsPackingSum, hempty]

private lemma bsPackingOuterEnvelope_empty (T : X → X) (u : X → ℝ) (a r : ℝ) :
    bsPackingOuterEnvelope T u ∅ a r = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine iInf_le_of_le (fun _ ↦ ∅)
    (iInf_le_of_le ⟨fun _ ↦ Set.Subset.refl _, Set.empty_subset _⟩ ?_)
  simp [bsPackingPrecontent_empty]

/-- The packing BS dimension of the empty set is zero.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_empty (T : X → X) (u : X → ℝ) :
    packingBSDimension T u ∅ = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine iSup_le fun p ↦ iInf_le_of_le 0 (iInf_le_of_le le_rfl ?_)
  exact iInf_le_of_le (bsPackingOuterEnvelope_empty T u 0 (dyadicRadius p))
    (le_of_eq ENNReal.ofReal_zero)

/-- The modified separated BS dimension of the empty set is zero.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_empty_separated (T : X → X) (u : X → ℝ) :
    separatedBSDimension T u ∅ = 0 := by
  have hsum (r : ℝ) : separatedBSSum T u ∅ 0 r = fun _ ↦ 0 := by
    funext n
    apply nonpos_iff_eq_zero.mp
    refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
    have hempty : F = ∅ := Set.subset_empty_iff.mp hF.1
    simp [bsPartitionCoverCost, hempty]
  apply nonpos_iff_eq_zero.mp
  refine iSup_le fun p ↦ iInf_le_of_le (fun _ ↦ ∅)
    (iInf_le_of_le ⟨fun _ ↦ Set.Subset.refl _, Set.empty_subset _⟩ (iSup_le fun _ ↦ ?_))
  refine iInf_le_of_le 0 (iInf_le_of_le le_rfl (iInf_le_of_le ?_ ?_))
  · rw [hsum]
    exact limsup_const _
  · exact le_of_eq ENNReal.ofReal_zero

/-- A lower Birkhoff sum at one point of a ball controls the change in its BS weight. -/
private lemma bsBallWeight_le_mul_of_mem
    (T : X → X) (u : X → ℝ) {a b L r : ℝ} {n : ℕ} {y z : X}
    (ha : 0 ≤ a) (hab : a < b) (hz : z ∈ bowenBall T n y r)
    (hsum : L ≤ birkhoffSum T u n z) :
    bsBallWeight T u b n y r ≤ bsBallWeight T u a n y r * (2 : ℝ≥0∞) ^ (-(b - a) * L) := by
  let S := pressureBallWeight T u .supremum n y r
  have hbase : (2 : ℝ≥0∞) ^ L ≤ S :=
    (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hsum).trans
      (le_iSup_of_le z (le_iSup_of_le hz le_rfl))
  change S ^ (-b) ≤ S ^ (-a) * (2 : ℝ≥0∞) ^ (-(b - a) * L)
  by_cases htop : S = ⊤
  · rw [htop, ENNReal.top_rpow_of_neg (by linarith : -b < 0)]
    exact bot_le
  have hzero : S ≠ 0 := ne_of_gt
    ((ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 2) (by norm_num)).trans_le hbase)
  have hgap : S ^ (-(b - a)) ≤ (2 : ℝ≥0∞) ^ (-(b - a) * L) := by
    calc
      S ^ (-(b - a)) ≤ ((2 : ℝ≥0∞) ^ L) ^ (-(b - a)) :=
        ENNReal.antitone_rpow_of_nonpos _ (by linarith) hbase
      _ = _ := by rw [← ENNReal.rpow_mul, mul_comm L]
  calc
    S ^ (-b) = S ^ (-a + -(b - a)) := by congr 1; ring
    _ = S ^ (-a) * S ^ (-(b - a)) := ENNReal.rpow_add _ _ hzero htop
    _ ≤ S ^ (-a) * (2 : ℝ≥0∞) ^ (-(b - a) * L) := mul_le_mul_right hgap _

/-- A uniform lower bound for Birkhoff sums gives a multiplicative separated-sum bound. -/
private lemma separatedBSSum_le_mul_of_le_birkhoffSum
    (T : X → X) (u : X → ℝ) (C : Set X) {a b L r : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hC : ∀ x ∈ C, L ≤ birkhoffSum T u n x) :
    separatedBSSum T u C b r n ≤ separatedBSSum T u C a r n *
      (2 : ℝ≥0∞) ^ (-(b - a) * L) := by
  unfold separatedBSSum
  simp_rw [ENNReal.iSup_mul]
  refine iSup_mono fun F ↦ iSup_mono fun hF ↦ ?_
  unfold bsPartitionCoverCost
  rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun y ↦ bsBallWeight_le_mul_of_mem T u ha hab
    (self_mem_bowenBall T n y r hr) (hC y (hF.1 y.2))

/-- Finite upper mass multiplied by an exponentially decaying factor tends to zero. -/
private lemma tendsto_zero_of_le_mul_two_rpow
    (f g : ℕ → ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hfg : ∀ᶠ n in atTop, f n ≤ g n * (2 : ℝ≥0∞) ^ (-c * (n : ℝ)))
    (hfinite : limsup g atTop < ⊤) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨M, hM, hMtop⟩ := exists_between hfinite
  have hbound : ∀ᶠ n in atTop, f n ≤ M * (2 : ℝ≥0∞) ^ (-c * (n : ℝ)) := by
    filter_upwards [hfg, eventually_lt_of_limsup_lt hM] with n hn hgn
    exact hn.trans (mul_le_mul_left hgn.le _)
  have hexp : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-c * (n : ℝ))) atTop (𝓝 0) :=
    (ENNReal.tendsto_rpow_atBot_of_one_lt_base ENNReal.one_lt_two).comp
      (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hc) tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ ↦ M * (2 : ℝ≥0∞) ^ (-c * (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hexp (Or.inr hMtop.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) hbound

/-- On a uniform positive-average piece, finite separated upper mass becomes zero.
Blueprint node `pack:bs-finite-zero`. -/
theorem bsFiniteZeroUniformPiece (T : X → X) (u : X → ℝ) (C : Set X)
    (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 < ρ)
    (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hfinite : limsup (separatedBSSum T u C a r) atTop < ⊤) :
    limsup (separatedBSSum T u C b r) atTop = 0 := by
  have _ := hN
  apply Tendsto.limsup_eq
  apply tendsto_zero_of_le_mul_two_rpow _ _ ((b - a) * ρ)
    (mul_pos (sub_pos.mpr hab) hρ) ?_ hfinite
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [neg_mul, mul_assoc] using
    separatedBSSum_le_mul_of_le_birkhoffSum T u C ha hab hr (fun x hx ↦ hC x hx n hn)

/-- Discarding balls that miss the set yields the same multiplicative bound for covers. -/
private lemma bsPartitionSum_le_mul_of_le_birkhoffSum
    (T : X → X) (u : X → ℝ) (C : Set X) {a b L r : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hab : a < b) (hC : ∀ x ∈ C, L ≤ birkhoffSum T u n x) :
    bsPartitionSum T u C b r n ≤ bsPartitionSum T u C a r n *
      (2 : ℝ≥0∞) ^ (-(b - a) * L) := by
  let q := (2 : ℝ≥0∞) ^ (-(b - a) * L)
  have hq0 : q ≠ 0 := by simp [q, ENNReal.rpow_eq_zero_iff]
  have hqtop : q ≠ ⊤ := by simp [q, ENNReal.rpow_eq_top_iff]
  have hcover (F : Set X) (hF : F.Countable ∧ C ⊆ ⋃ y ∈ F, bowenBall T n y r) :
      bsPartitionSum T u C b r n ≤ bsPartitionCoverCost T u a r n F * q := by
    let G := {y ∈ F | (bowenBall T n y r ∩ C).Nonempty}
    have hGcount : G.Countable := hF.1.mono fun _ hy ↦ hy.1
    have hGcover : C ⊆ ⋃ y ∈ G, bowenBall T n y r := by
      intro x hx
      obtain ⟨y, hyF, hxy⟩ : ∃ y ∈ F, x ∈ bowenBall T n y r := by
        simpa only [Set.mem_iUnion, exists_prop] using hF.2 hx
      exact Set.mem_iUnion₂.mpr ⟨y, ⟨hyF, ⟨x, hxy, hx⟩⟩, hxy⟩
    calc
      bsPartitionSum T u C b r n ≤ bsPartitionCoverCost T u b r n G :=
        iInf_le_of_le G (iInf_le_of_le ⟨hGcount, hGcover⟩ le_rfl)
      _ ≤ bsPartitionCoverCost T u a r n G * q := by
        unfold bsPartitionCoverCost
        rw [← ENNReal.tsum_mul_right]
        apply ENNReal.tsum_le_tsum
        intro y
        obtain ⟨z, hzy, hzC⟩ := y.2.2
        exact bsBallWeight_le_mul_of_mem T u ha hab hzy (hC z hzC)
      _ ≤ bsPartitionCoverCost T u a r n F * q :=
        mul_le_mul_left (ENNReal.tsum_mono_subtype
          (fun y ↦ bsBallWeight T u a n y r) (fun _ hy ↦ hy.1)) q
  have hle : bsPartitionSum T u C b r n * q⁻¹ ≤ bsPartitionSum T u C a r n := by
    refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
    have h := mul_le_mul_left (hcover F hF) q⁻¹
    rwa [mul_assoc, ENNReal.mul_inv_cancel hq0 hqtop, mul_one] at h
  have h := mul_le_mul_left hle q
  rwa [mul_assoc, ENNReal.inv_mul_cancel hq0 hqtop, mul_one] at h

/-- On a uniform positive-average piece, finite covering upper mass becomes zero
at every larger exponent. Balls missing the piece can be discarded.
Blueprint node `pack:bs-finite-zero`. -/
theorem bsFiniteZeroUniformPiece_covering (T : X → X) (u : X → ℝ) (C : Set X)
    (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 < ρ)
    (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hfinite : limsup (bsPartitionSum T u C a r) atTop < ⊤) :
    limsup (bsPartitionSum T u C b r) atTop = 0 := by
  have _ := hN
  have _ := hr
  apply Tendsto.limsup_eq
  apply tendsto_zero_of_le_mul_two_rpow _ _ ((b - a) * ρ)
    (mul_pos (sub_pos.mpr hab) hρ) ?_ hfinite
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [neg_mul, mul_assoc] using
    bsPartitionSum_le_mul_of_le_birkhoffSum T u C ha hab (fun x hx ↦ hC x hx n hn)

/-- If finite values become zero at every larger nonnegative parameter, the infimum
of finite parameters equals the infimum of zero parameters. -/
lemma _root_.ENNReal.iInf_ofReal_lt_top_eq_iInf_ofReal_eq_zero
    (f : ℝ → ℝ≥0∞)
    (h : ∀ a b, 0 ≤ a → a < b → f a < ⊤ → f b = 0) :
    (⨅ a, ⨅ (_ : 0 ≤ a), ⨅ (_ : f a < ⊤), ENNReal.ofReal a) =
      ⨅ a, ⨅ (_ : 0 ≤ a), ⨅ (_ : f a = 0), ENNReal.ofReal a := by
  apply le_antisymm
  · refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hzero ↦ ?_
    exact iInf_le_of_le a (iInf_le_of_le ha
      (iInf_le_of_le (hzero.trans_lt ENNReal.zero_lt_top) le_rfl))
  · refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hfinite ↦ ?_
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hpos : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    calc
      _ ≤ ENNReal.ofReal (a + ε) := iInf_le_of_le (a + ε)
        (iInf_le_of_le (add_nonneg ha ε.coe_nonneg)
          (iInf_le_of_le (h a (a + ε) ha (by linarith) hfinite) le_rfl))
      _ = ENNReal.ofReal a + ε := by rw [ENNReal.ofReal_add ha ε.coe_nonneg]; simp

/-- Finite and zero raw separated thresholds agree on a uniform positive-average piece.
Blueprint node `pack:bs-finite-zero`. -/
theorem bsFiniteZeroUniformPiece_separated_threshold (T : X → X) (u : X → ℝ)
    (C : Set X) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 < ρ)
    (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (r : ℝ) (hr : 0 < r) :
    separatedBSFiniteCapacityAt T u C r = separatedBSZeroCapacityAt T u C r := by
  apply ENNReal.iInf_ofReal_lt_top_eq_iInf_ofReal_eq_zero
  intro a b ha hab hfinite
  exact bsFiniteZeroUniformPiece T u C N hN ρ hρ hC a b r ha hab hr hfinite

end Kolmogorov.PointToSet
