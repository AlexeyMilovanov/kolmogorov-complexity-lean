/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Lower
import KolmogorovMathlib.Oracle.Joins
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Scale limits and positive refinement for upper Barreira–Schmeling dimension

The upper BS capacity and its countable modification are monotone in the covered set
and antitone in the radius. The dyadic supremum defining `upperBSDimension` is also the
limit over all positive radii tending to zero (blueprint node `bs:upper-capacity`).

On pieces with a uniform positive lower bound for Birkhoff averages, an increase in the
exponent gives exponential decay of partition sums. Refining countable covers by these
pieces identifies the modified finite and zero capacity thresholds
(`bs:upper-refinement`). Finally, uniform BS nets bound the upper dimension
(`bs:net-lower`). These results supply the scale and covering estimates used by the
uniform-net construction and the upper BS point-to-set principle.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

private lemma bsPartitionSum_mono (T : X → X) (u : X → ℝ) (s r : ℝ) (n : ℕ) :
    Monotone (fun Z ↦ bsPartitionSum T u Z s r n) := by
  intro Z₁ Z₂ hZ
  unfold bsPartitionSum
  refine iInf_mono fun F ↦ iInf_mono' fun hF ↦ ?_
  exact ⟨⟨hF.1, hZ.trans hF.2⟩, le_rfl⟩

/-- Upper capacity is monotone in the covered set.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_mono_capacity (T : X → X) (u : X → ℝ) (r : ℝ) :
    Monotone (fun Z => upperBSCapacityAt T u Z r) := by
  intro Z₁ Z₂ hZ
  unfold upperBSCapacityAt
  refine iInf_mono fun s ↦ iInf_mono fun _ ↦ iInf_mono' fun hlimsup ↦ ?_
  refine ⟨lt_of_le_of_lt ?_ hlimsup, le_rfl⟩
  exact limsup_le_limsup (Eventually.of_forall fun n ↦ bsPartitionSum_mono T u s r n hZ)

/-- Intersecting cover pieces with the original set leaves the modified dimension unchanged.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_restrict_pieces (T : X → X) (u : X → ℝ) (Z : Set X) (r : ℝ) :
    modifiedUpperBSDimension T u Z r =
      ⨅ Y : ℕ → Set X, ⨅ (_ : Z ⊆ ⋃ k, Y k), ⨆ k, upperBSCapacityAt T u (Y k) r := by
  unfold modifiedUpperBSDimension
  refine le_antisymm (le_iInf₂ fun Y hY ↦ ?_) (le_iInf₂ fun Y hY ↦ ?_)
  · have hcover : Z ⊆ ⋃ k, Y k ∩ Z := by
      intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hY hx)
      exact Set.mem_iUnion.mpr ⟨k, hk, hx⟩
    refine iInf₂_le_of_le (fun k ↦ Y k ∩ Z) ⟨fun _ ↦ Set.inter_subset_right, hcover⟩ ?_
    exact iSup_mono fun _ ↦ upperBSDimension_mono_capacity T u r Set.inter_subset_left
  · exact iInf₂_le_of_le Y hY.2 le_rfl

private lemma modifiedUpperBSDimension_mono (T : X → X) (u : X → ℝ) (r : ℝ) :
    Monotone (fun Z ↦ modifiedUpperBSDimension T u Z r) := by
  intro Z₁ Z₂ hZ
  dsimp only
  rw [upperBSDimension_restrict_pieces, upperBSDimension_restrict_pieces]
  exact iInf_mono fun Y ↦ iInf_mono' fun hY ↦ ⟨hZ.trans hY, le_rfl⟩

/-- The upper BS dimension is monotone in the covered set.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_mono (T : X → X) (u : X → ℝ) :
    Monotone (upperBSDimension T u) := by
  intro Z₁ Z₂ hZ
  dsimp [upperBSDimension]
  exact iSup_mono (fun p ↦ modifiedUpperBSDimension_mono T u (dyadicRadius p) hZ)

/-- At a nonnegative exponent, enlarging a Bowen ball decreases its BS weight. -/
lemma bsBallWeight_le_of_radius_le
    (T : X → X) (u : X → ℝ) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (y : X)
    {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    bsBallWeight T u s n y ε₂ ≤ bsBallWeight T u s n y ε₁ := by
  apply ENNReal.antitone_rpow_of_nonpos (-s) (neg_nonpos.mpr hs)
  exact iSup_mono fun z ↦ iSup_mono' fun hz ↦
    ⟨bowenBall_subset_of_le T n y h hz, le_rfl⟩

private lemma bsPartitionCoverCost_antitone_radius (T : X → X) (u : X → ℝ)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (F : Set X) :
    AntitoneOn (fun r ↦ bsPartitionCoverCost T u s r n F) (Set.Ioi 0) := by
  intro r₁ _ r₂ _ h
  dsimp [bsPartitionCoverCost]
  apply ENNReal.tsum_le_tsum
  intro y
  exact bsBallWeight_le_of_radius_le T u s hs n y h

private lemma bsPartitionSum_antitone_radius (T : X → X) (u : X → ℝ) (s : ℝ)
    (hs : 0 ≤ s) (n : ℕ) (Z : Set X) :
    AntitoneOn (fun r ↦ bsPartitionSum T u Z s r n) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ h
  dsimp [bsPartitionSum]
  apply iInf_mono
  intro F
  apply iInf_mono'
  intro hF
  refine ⟨⟨hF.1, ?_⟩, ?_⟩
  · exact hF.2.trans (Set.iUnion₂_mono fun y _ ↦ bowenBall_subset_of_le T n y h)
  · exact bsPartitionCoverCost_antitone_radius T u s hs n F hr₁ hr₂ h

/-- Smaller radii increase the upper capacity threshold.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_antitone_capacity_radius (T : X → X) (u : X → ℝ) (Z : Set X) :
    AntitoneOn (upperBSCapacityAt T u Z) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ h
  dsimp [upperBSCapacityAt]
  apply iInf_mono
  intro s
  apply iInf_mono
  intro hs
  apply iInf_mono'
  intro h_lim
  refine ⟨?_, le_rfl⟩
  apply lt_of_le_of_lt _ h_lim
  exact limsup_le_limsup (Eventually.of_forall fun n ↦
    bsPartitionSum_antitone_radius T u s hs n Z hr₁ hr₂ h)

/-- Smaller radii increase the modified upper critical dimension.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_antitone_radius (T : X → X) (u : X → ℝ) (Z : Set X) :
    AntitoneOn (modifiedUpperBSDimension T u Z) (Set.Ioi 0) := by
  intro r₁ hr₁ r₂ hr₂ hr
  dsimp [modifiedUpperBSDimension]
  apply iInf_mono
  intro Y
  apply iInf_mono
  intro hY
  apply iSup_mono
  intro k
  apply upperBSDimension_antitone_capacity_radius T u (Y k) hr₁ hr₂ hr

private lemma modifiedUpperBSDimension_mono_dyadic (T : X → X) (u : X → ℝ) (Z : Set X) :
    Monotone (fun p ↦ modifiedUpperBSDimension T u Z (dyadicRadius p)) := by
  intro a b hab
  apply upperBSDimension_antitone_radius T u Z
  · rw [Set.mem_Ioi]
    dsimp [dyadicRadius]
    positivity
  · rw [Set.mem_Ioi]
    dsimp [dyadicRadius]
    positivity
  · exact dyadicRadius_antitone hab

/-- The dyadic supremum is the upper dimension's scale-zero limit.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_scale_limit (T : X → X) (u : X → ℝ) (Z : Set X) :
    Tendsto (fun p => modifiedUpperBSDimension T u Z (dyadicRadius p)) atTop
      (𝓝 (upperBSDimension T u Z)) := by
  exact tendsto_atTop_iSup (modifiedUpperBSDimension_mono_dyadic T u Z)

/-- The same upper dimension is the limit along all positive radii tending to zero.
Blueprint node `bs:upper-capacity`. -/
theorem upperBSDimension_radius_limit (T : X → X) (u : X → ℝ) (Z : Set X) :
    Tendsto (modifiedUpperBSDimension T u Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (upperBSDimension T u Z)) := by
  let f := modifiedUpperBSDimension T u Z
  let L := upperBSDimension T u Z
  let r := fun (p : ℕ) ↦ dyadicRadius p
  have hf : AntitoneOn f (Set.Ioi 0) := upperBSDimension_antitone_radius T u Z
  have hr_pos : ∀ n, 0 < r n := by
    intro n
    dsimp [r, dyadicRadius]
    positivity
  have hr_tendsto : Tendsto r atTop (𝓝 0) := by
    dsimp [r, dyadicRadius]
    apply _root_.tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have hl : Tendsto (fun n ↦ f (r n)) atTop (𝓝 L) := by
    apply upperBSDimension_scale_limit
  have hsup : Tendsto f (𝓝[>] 0) (𝓝 (sSup (f '' Set.Ioi 0))) := by
    apply AntitoneOn.tendsto_nhdsGT hf
    exact OrderTop.bddAbove _
  have h_r_in : ∀ᶠ n in atTop, r n ∈ Set.Ioi 0 := Eventually.of_forall hr_pos
  have h2 : Tendsto (fun n ↦ f (r n)) atTop (𝓝 (sSup (f '' Set.Ioi 0))) := by
    apply Tendsto.comp hsup
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hr_tendsto h_r_in
  have hL : L = sSup (f '' Set.Ioi 0) := tendsto_nhds_unique hl h2
  change Tendsto f (𝓝[>] 0) (𝓝 L)
  rw [hL]
  exact hsup

/-- On a positive-average piece, the ball sup-weight is bounded by the exponent-gap factor
times the base weight. -/
private lemma bsBallWeight_le_gap_mul_of_positiveAveragePiece
    (T : X → X) (u : X → ℝ) (Z C : Set X)
    (N₀ : ℕ) (ρ : ℚ) (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ)
    (s t r : ℝ) (hs : 0 ≤ s) (hst : s < t) (n : ℕ) (hn : N₀ ≤ n)
    (y : X) (hy : (bowenBall T n y r ∩ C).Nonempty) :
    bsBallWeight T u t n y r ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (ρ : ℝ) * n) * bsBallWeight T u s n y r := by
  dsimp [bsBallWeight]
  rcases hy with ⟨z, hz, hzC⟩
  let S : ℝ≥0∞ := pressureBallWeight T u .supremum n y r
  have hbase : (2 : ℝ≥0∞) ^ ((ρ : ℝ) * n) ≤ S := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ birkhoffSum T u n z :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          ((hC hzC).2 n hn)
      _ ≤ S := by
        change _ ≤ ⨆ w ∈ bowenBall T n y r,
          (2 : ℝ≥0∞) ^ birkhoffSum T u n w
        exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  change S ^ (-t) ≤
    (2 : ℝ≥0∞) ^ (-(t - s) * (ρ : ℝ) * n) * S ^ (-s)
  by_cases htop : S = ⊤
  · rw [htop, ENNReal.top_rpow_of_neg (by linarith : -t < 0)]
    exact zero_le
  have hpos : 0 < (2 : ℝ≥0∞) ^ ((ρ : ℝ) * n) :=
    ENNReal.rpow_pos (by norm_num) (by norm_num)
  have hzero : S ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos hbase)
  have hgap : S ^ (-(t - s)) ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (ρ : ℝ) * n) := by
    have h := ENNReal.antitone_rpow_of_nonpos (-(t - s)) (by linarith) hbase
    dsimp only at h
    rw [← ENNReal.rpow_mul] at h
    have he : ((ρ : ℝ) * (n : ℝ)) * (-(t - s)) =
        -(t - s) * (ρ : ℝ) * n := by ring
    rw [he] at h
    exact h
  calc
    S ^ (-t) = S ^ (-(t - s) + (-s)) := by congr 1; ring
    _ = S ^ (-(t - s)) * S ^ (-s) :=
      ENNReal.rpow_add _ _ hzero htop
    _ ≤ _ := by gcongr

/-- Any countable cover can be refined (by dropping balls missing `C`) into one where every
ball meets `C`, without increasing the cover cost. -/
private lemma exists_cover_meeting_set
    (T : X → X) (u : X → ℝ) (C : Set X) (s r : ℝ) (n : ℕ)
    (F : Set X) (hF : F.Countable ∧ C ⊆ ⋃ y ∈ F, bowenBall T n y r) :
    ∃ F' : Set X, F' ⊆ F ∧ F'.Countable ∧
      (C ⊆ ⋃ y ∈ F', bowenBall T n y r) ∧
      (∀ y ∈ F', (bowenBall T n y r ∩ C).Nonempty) ∧
      bsPartitionCoverCost T u s r n F' ≤ bsPartitionCoverCost T u s r n F := by
  classical
  let F' : Set X := {y ∈ F | (bowenBall T n y r ∩ C).Nonempty}
  have hsub : F' ⊆ F := fun y hy ↦ hy.1
  refine ⟨F', hsub, hF.1.mono hsub, ?_, ?_, ?_⟩
  · intro x hx
    have hcov := hF.2 hx
    simp only [Set.mem_iUnion] at hcov ⊢
    rcases hcov with ⟨y, hy, hxy⟩
    exact ⟨y, ⟨hy, ⟨x, hxy, hx⟩⟩, hxy⟩
  · intro y hy
    exact hy.2
  · exact ENNReal.tsum_mono_subtype
      (fun y ↦ bsBallWeight T u s n y r) hsub

/-- On one uniform positive-average piece an exponent gap gives an exponential mass bound.
Blueprint node `bs:upper-refinement`. -/
theorem upperCapacityPositiveRefinement (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z C : Set X)
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (ρ : ℚ) (hρ : 0 < ρ)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ) (s t r : ℝ)
    (hs : 0 ≤ s) (hst : s < t) (hr : 0 < r) (n : ℕ) (hn : N₀ ≤ n) :
    bsPartitionSum T u C t r n ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (ρ : ℝ) * n) * bsPartitionSum T u C s r n := by
  -- These parameters are retained in the public statement; the estimate is purely order-theoretic.
  have _ := P
  have _ := hT
  have _ := hu
  have _ := hN₀
  have _ := hρ
  have _ := hr
  let a : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-(t - s) * (ρ : ℝ) * n)
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have hatop : a ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  change bsPartitionSum T u C t r n ≤ a * bsPartitionSum T u C s r n
  unfold bsPartitionSum
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine le_iInf fun F ↦ ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine le_iInf fun hF ↦ ?_
  obtain ⟨F', _, hcount, hcover, hmeet, hcost⟩ :=
    exists_cover_meeting_set T u C s r n F hF
  refine (iInf₂_le_of_le F' ⟨hcount, hcover⟩ ?_).trans (mul_le_mul_right hcost a)
  unfold bsPartitionCoverCost
  calc
    _ ≤ ∑' y : F', a * bsBallWeight T u s n y r :=
      ENNReal.tsum_le_tsum fun y ↦
        bsBallWeight_le_gap_mul_of_positiveAveragePiece T u Z C N₀ ρ hC s t r hs hst n hn
          y (hmeet y y.2)
    _ = _ := ENNReal.tsum_mul_left

/-- A sequence dominated by an exponentially decaying factor times a sequence with finite
limsup tends to zero. -/
private theorem tendsto_zero_of_le_geometric_mul_of_limsup_lt_top
    (f g : ℕ → ℝ≥0∞) (a : ℝ) (ha : 0 < a)
    (hfg : ∀ᶠ n in atTop, f n ≤ (2 : ℝ≥0∞) ^ (-a * n) * g n)
    (hfinite : limsup g atTop < ⊤) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨c, hc, hctop⟩ := exists_between hfinite
  have hbound : ∀ᶠ n in atTop, f n ≤ (2 : ℝ≥0∞) ^ (-a * n) * c := by
    filter_upwards [hfg, eventually_lt_of_limsup_lt hc] with n hn hnc
    exact hn.trans (mul_le_mul_right hnc.le _)
  have hexponent : Tendsto (fun n : ℕ ↦ -a * (n : ℝ)) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr ha) tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * n)) atTop (𝓝 0) :=
    (ENNReal.tendsto_rpow_atBot_of_one_lt_base (by norm_num)).comp hexponent
  have hdecay : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * n) * c) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hpow (Or.inr hctop.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
    (Eventually.of_forall fun _ ↦ zero_le) hbound

/-- Finite upper mass limit becomes convergence to zero on a uniform positive piece.
Blueprint node `bs:upper-refinement`. -/
theorem upperCapacityPositiveRefinement_tendsto (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z C : Set X)
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (ρ : ℚ) (hρ : 0 < ρ)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ) (s t r : ℝ)
    (hs : 0 ≤ s) (hst : s < t) (hr : 0 < r)
    (hfinite : limsup (bsPartitionSum T u C s r) atTop < ⊤) :
    Tendsto (bsPartitionSum T u C t r) atTop (𝓝 0) := by
  let f := bsPartitionSum T u C t r
  let g := bsPartitionSum T u C s r
  let a := (t - s) * (ρ : ℝ)
  have ha : 0 < a := mul_pos (sub_pos.mpr hst) (Rat.cast_pos.mpr hρ)
  have hfg : ∀ᶠ n in atTop, f n ≤ (2 : ℝ≥0∞) ^ (-a * (n : ℝ)) * g n := by
    apply eventually_atTop.mpr
    use N₀
    intro n hn
    have h_refine :=
      upperCapacityPositiveRefinement P T hT u hu Z C N₀ hN₀ ρ hρ hC s t r hs hst hr n hn
    have h_eq : -(t - s) * (ρ : ℝ) * n = -a * n := by
      dsimp [a]
      ring
    rwa [h_eq] at h_refine
  exact tendsto_zero_of_le_geometric_mul_of_limsup_lt_top f g a ha hfg hfinite

/-- The finite capacity threshold is at most the zero capacity threshold. -/
private lemma upperBSCapacityAt_le_zeroCapacityAt
    (T : X → X) (u : X → ℝ) (C : Set X) (r : ℝ) :
    upperBSCapacityAt T u C r ≤ upperBSZeroCapacityAt T u C r := by
  unfold upperBSZeroCapacityAt
  refine le_iInf₂ fun s hs ↦ le_iInf fun hzero ↦ ?_
  unfold upperBSCapacityAt
  apply iInf_le_of_le s
  apply iInf_le_of_le hs
  exact iInf_le_of_le (hzero.trans_lt ENNReal.zero_lt_top) le_rfl

/-- On a uniform positive-average piece, the zero threshold is at most the finite threshold.
Increase each finite-limsup exponent by an arbitrarily small positive amount and use
`upperCapacityPositiveRefinement_tendsto`. -/
private lemma upperBSZeroCapacityAt_le_capacityAt_of_positiveAveragePiece
    (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z C : Set X)
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (ρ : ℚ) (hρ : 0 < ρ)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ)
    (r : ℝ) (hr : 0 < r) :
    upperBSZeroCapacityAt T u C r ≤ upperBSCapacityAt T u C r := by
  unfold upperBSCapacityAt
  refine le_iInf₂ fun s hs ↦ le_iInf fun hfinite ↦ ?_
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : 0 < (ε : ℝ) := NNReal.coe_pos.mpr hε
  have hzero : limsup (bsPartitionSum T u C (s + ε) r) atTop = 0 :=
    (upperCapacityPositiveRefinement_tendsto P T hT u hu Z C N₀ hN₀ ρ hρ hC
      s (s + ε) r hs (by linarith) hr hfinite).limsup_eq
  calc
    upperBSZeroCapacityAt T u C r ≤ ENNReal.ofReal (s + ε) := by
      unfold upperBSZeroCapacityAt
      apply iInf_le_of_le (s + ε)
      apply iInf_le_of_le (show 0 ≤ s + (ε : ℝ) by positivity)
      exact iInf_le_of_le hzero le_rfl
    _ = ENNReal.ofReal s + (ε : ℝ≥0∞) := by
      rw [ENNReal.ofReal_add hs ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- Intersect every piece of an admissible cover with all the positive-average exhaustion
pieces, enumerate the resulting countable family, and bound its zero capacities by
the original finite capacities. The enumeration includes only positive slopes and
cutoffs at least one. -/
private lemma exists_cover_zeroCapacity_le_capacity
    (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) (hr : 0 < r)
    (Y : ℕ → Set X) (hY_sub : ∀ k, Y k ⊆ Z) (hY_cov : Z ⊆ ⋃ k, Y k) :
    ∃ W : ℕ → Set X, ((∀ j, W j ⊆ Z) ∧ Z ⊆ ⋃ j, W j) ∧
      (⨆ j, upperBSZeroCapacityAt T u (W j) r) ≤
        ⨆ k, upperBSCapacityAt T u (Y k) r := by
  classical
  let I := ℕ × {N : ℕ // 1 ≤ N} × {ρ : ℚ // 0 < ρ}
  have hI : Nonempty I := ⟨⟨0, ⟨1, le_rfl⟩, ⟨1, by norm_num⟩⟩⟩
  obtain ⟨e, he⟩ := @exists_surjective_nat I hI inferInstance
  let W : ℕ → Set X := fun j ↦ Y (e j).1 ∩
    positiveAveragePiece T u Z (e j).2.1.1 (e j).2.2.1
  have hW_sub : ∀ j, W j ⊆ Z := fun j ↦
    Set.Subset.trans Set.inter_subset_left (hY_sub (e j).1)
  have hW_cov : Z ⊆ ⋃ j, W j := by
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hY_cov hx)
    have hx' := hx
    rw [positiveAverageExhaustion P T hT u hu Z hZ] at hx'
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨N, hN, ρ, hρ, hxpiece⟩ := hx'
    obtain ⟨j, hj⟩ := he ⟨k, ⟨N, hN⟩, ⟨ρ, hρ⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    dsimp [W]
    rw [hj]
    exact ⟨hk, hxpiece⟩
  refine ⟨W, ⟨hW_sub, hW_cov⟩, iSup_le fun j ↦ ?_⟩
  calc
    upperBSZeroCapacityAt T u (W j) r ≤ upperBSCapacityAt T u (W j) r :=
      upperBSZeroCapacityAt_le_capacityAt_of_positiveAveragePiece P T hT u hu Z (W j)
        (e j).2.1.1 (e j).2.1.2 (e j).2.2.1 (e j).2.2.2 Set.inter_subset_right r hr
    _ ≤ upperBSCapacityAt T u (Y (e j).1) r :=
      upperBSDimension_mono_capacity T u r Set.inter_subset_left
    _ ≤ ⨆ k, upperBSCapacityAt T u (Y k) r :=
      le_iSup (fun k ↦ upperBSCapacityAt T u (Y k) r) (e j).1

/-- After countable positive refinement, the modified finite and zero thresholds agree.
Blueprint node `bs:upper-refinement`. -/
theorem upperCapacityPositiveRefinement_modified (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) (hr : 0 < r) :
    modifiedUpperBSDimension T u Z r = modifiedUpperBSZeroDimension T u Z r := by
  apply le_antisymm
  · unfold modifiedUpperBSDimension modifiedUpperBSZeroDimension
    apply iInf_mono
    intro Y
    apply iInf_mono
    intro hY
    exact iSup_mono fun k ↦ upperBSCapacityAt_le_zeroCapacityAt T u (Y k) r
  · unfold modifiedUpperBSDimension
    refine le_iInf₂ fun Y hY ↦ ?_
    obtain ⟨W, hW, hbound⟩ :=
      exists_cover_zeroCapacity_le_capacity P T hT u hu Z hZ r hr
        Y hY.1 hY.2
    unfold modifiedUpperBSZeroDimension
    exact iInf_le_of_le W (iInf_le_of_le hW hbound)

/-- Points of `Z` covered by every positive-order slice at fixed scale and piece index. -/
private def uniformBSNetPiece
    (P : Presentation X) (T : X → X) (Z : Set X) (p k : ℕ) (E : Set (ℕ × ℕ × ℕ × ℕ)) :
    Set X :=
  Z ∩ ⋂ n ≥ 1, ⋃ (i : ℕ) (_ : (i, n, p, k) ∈ E), bowenBall T n (P.ι i) (dyadicRadius p)

/-- Every point of `Z` belongs to a uniform-net piece at each scale. -/
private lemma subset_iUnion_uniformBSNetPiece
    (P : Presentation X) (T : X → X) (u : X → ℝ) (Z : Set X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (hE : IsUniformBSNet P T u Z s E) (p : ℕ) :
    Z ⊆ ⋃ k, uniformBSNetPiece P T Z p k E := by
  intro x hx
  obtain ⟨k, hk⟩ := hE.2 p x hx
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  dsimp [uniformBSNetPiece]
  refine ⟨hx, ?_⟩
  simp only [Set.mem_iInter, Set.mem_iUnion]
  intro n hn
  obtain ⟨i, hi, hx2⟩ := hk n hn
  exact ⟨i, hi, hx2⟩

/-- Each positive-order slice of a uniform net covers its associated piece. -/
private lemma uniformBSNetPiece_subset_slice
    (P : Presentation X) (T : X → X) (Z : Set X) (p k : ℕ)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (n : ℕ) (hn : 1 ≤ n) :
    uniformBSNetPiece P T Z p k E ⊆
      ⋃ (i : ℕ) (_ : (i, n, p, k) ∈ E), bowenBall T n (P.ι i) (dyadicRadius p) := by
  intro x hx
  unfold uniformBSNetPiece at hx
  rcases hx with ⟨_, hx2⟩
  simp_rw [Set.mem_iInter] at hx2
  exact hx2 n hn

/-- An indexed countable cover bounds the partition sum by the sum of its ball weights,
even when its centers are not distinct. -/
private lemma bsPartitionSum_le_tsum_of_cover {ι : Type*} [Countable ι]
    (T : X → X) (u : X → ℝ) (Z : Set X) (s r : ℝ) (n : ℕ) (c : ι → X)
    (hcover : Z ⊆ ⋃ i, bowenBall T n (c i) r) :
    bsPartitionSum T u Z s r n ≤ ∑' i, bsBallWeight T u s n (c i) r := by
  have hcov : Z ⊆ ⋃ y ∈ Set.range c, bowenBall T n y r := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion₂.mpr ⟨c i, ⟨i, rfl⟩, hi⟩
  unfold bsPartitionSum
  refine (iInf₂_le_of_le (Set.range c) ⟨Set.countable_range c, hcov⟩ le_rfl).trans ?_
  exact ENNReal.tsum_le_tsum_comp_of_surjective Set.rangeFactorization_surjective
    (fun y : Set.range c ↦ bsBallWeight T u s n y r)

/-- For nonnegative exponents the sup-weight of a ball is at most its center weight. -/
private lemma bsBallWeight_le_center_weight (T : X → X) (u : X → ℝ)
    (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr : 0 < r) (n : ℕ) (y : X) :
    bsBallWeight T u s n y r ≤ (2 : ℝ≥0∞) ^ birkhoffSum T (fun z ↦ -s * u z) n y := by
  have hsum : birkhoffSum T (fun z ↦ -s * u z) n y = birkhoffSum T u n y * (-s) := by
    simp only [birkhoffSum, Finset.sum_mul, mul_comm (-s)]
  rw [hsum, ENNReal.rpow_mul]
  apply ENNReal.antitone_rpow_of_nonpos (-s) (neg_nonpos.mpr hs)
  have hmem : y ∈ bowenBall T n y r :=
    mem_bowenBall_iff.mpr fun _ _ ↦ by simpa using hr
  exact le_iSup₂ (α := ℝ≥0∞) (f := fun z _ ↦ 2 ^ birkhoffSum T u n z) y hmem

/-- Finite upper slice mass limits bound the capacity of each uniform-net piece. -/
private lemma upperBSCapacityAt_uniformBSNetPiece_le
    (P : Presentation X) (T : X → X) (u : X → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (Z : Set X) (p k : ℕ) (E : Set (ℕ × ℕ × ℕ × ℕ)) (hE : IsUniformBSNet P T u Z s E) :
    upperBSCapacityAt T u (uniformBSNetPiece P T Z p k E) (dyadicRadius p) ≤
      ENNReal.ofReal s := by
  have hbound : ∀ᶠ n in atTop,
      bsPartitionSum T u (uniformBSNetPiece P T Z p k E) s (dyadicRadius p) n ≤
        uniformBSSum P T u s E n p k := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let I := {i : ℕ // (i, n, p, k) ∈ E}
    have hcover : uniformBSNetPiece P T Z p k E ⊆
        ⋃ i : I, bowenBall T n (P.ι i) (dyadicRadius p) := by
      simpa only [I, Set.iUnion_subtype] using
        uniformBSNetPiece_subset_slice P T Z p k E n hn
    refine (bsPartitionSum_le_tsum_of_cover T u _ s (dyadicRadius p) n
      (fun i : I ↦ P.ι i) hcover).trans ?_
    exact ENNReal.tsum_le_tsum fun i ↦
      bsBallWeight_le_center_weight T u s hs (dyadicRadius p)
        (by unfold dyadicRadius; positivity) n (P.ι i)
  unfold upperBSCapacityAt
  exact iInf_le_of_le s (iInf_le_of_le hs
    (iInf_le_of_le ((limsup_le_limsup hbound).trans_lt (hE.1 p k)) le_rfl))

/-- A uniform net bounds the upper BS dimension; positive Birkhoff averages are not needed.
Blueprint node `bs:net-lower`. -/
theorem uniformNetBoundsUpperBS (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (Z : Set X) (s : ℝ) (hs : 0 ≤ s) (E : Set (ℕ × ℕ × ℕ × ℕ))
    (hE : IsUniformBSNet P T u Z s E) :
    upperBSDimension T u Z ≤ ENNReal.ofReal s := by
  -- The covering argument does not require continuity.
  have _ := hT
  have _ := hu
  dsimp [upperBSDimension]
  apply iSup_le
  intro p
  dsimp [modifiedUpperBSDimension]
  apply iInf_le_of_le (fun k ↦ uniformBSNetPiece P T Z p k E)
  apply iInf_le_of_le
    ⟨fun _ ↦ Set.inter_subset_left, subset_iUnion_uniformBSNetPiece P T u Z s E hE p⟩
  apply iSup_le
  intro k
  exact upperBSCapacityAt_uniformBSNetPiece_le P T u s hs Z p k E hE

end Kolmogorov.PointToSet
