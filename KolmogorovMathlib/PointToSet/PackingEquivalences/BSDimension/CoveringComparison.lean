/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension.RadiusComparison

/-!
# Comparing BS covering, separated, and packing thresholds

This file compares the three Barreira–Schmeling definitions of the upper BS dimension of a
set `Z` for a potential `u` with positive lower Birkhoff averages on `Z`: the covering
definition, the separated-set definition and the packing definition.

Maximal separated nets and injective assignments of separated points to covering centers
compare the BS covering and separated sums (`bsSpanSepModified*`, blueprint node
`pack:bs-span-sep`). Refining countable covers into uniform positive-average pieces identifies
the finite and zero separated thresholds (`bsSpanSepModified_refinement`). Order slices of
Bowen packings then show that the packing BS dimension is bounded by, and bounds, the modified
separated dimension (`bsPackBoundsSeparated`, `bsSeparatedBoundsPack`; blueprint nodes
`pack:bs-pack-to-sep` and `pack:bs-sep-to-pack`). Together these give the equivalence of the
three definitions and the convergence of the modified covering dimensions
(`bsEquivalence*`; blueprint node `pack:bs-equivalence`).

The equivalence is used by `RawThresholdCounterexample` and by the module
`KolmogorovMathlib.PointToSet.PackingEquivalences.BSDimension` that assembles the packing
equivalences for the BS dimension.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X]

/-- The existing finite and zero raw covering thresholds agree on uniform positive pieces.
Blueprint node `pack:bs-finite-zero`. -/
theorem bsFiniteZeroUniformPiece_covering_threshold (T : X → X) (u : X → ℝ) (C : Set X) (N : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (r : ℝ) :
    upperBSCapacityAt T u C r = upperBSZeroCapacityAt T u C r := by
  apply ENNReal.iInf_ofReal_lt_top_eq_iInf_ofReal_eq_zero
  intro a b ha hab hfinite
  exact bsFiniteZeroUniformPiece_covering T u C N ρ hρ hC a b r ha hab hfinite

/-- A maximal separated net bounds the covering BS sum, without a positivity assumption.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) (hr : 0 < r)
    (n : ℕ) (hn : 1 ≤ n) :
    bsPartitionSum T u Z a (2 * r) n ≤ separatedBSSum T u Z a (2 * r) n := by
  have hr' : 0 < 2 * r := mul_pos zero_lt_two hr
  rcases countableSeparatedMaximalNet T hT Z n hn (2 * r) hr' with ⟨F, hsub, hsep, hcount, _,
    hcover⟩
  calc
    bsPartitionSum T u Z a (2 * r) n ≤ bsPartitionCoverCost T u a (2 * r) n F :=
      iInf_le_of_le F (iInf_le_of_le ⟨hcount, hcover⟩ le_rfl)
    _ ≤ separatedBSSum T u Z a (2 * r) n :=
      le_iSup_of_le F (le_iSup_of_le ⟨hsub, hsep⟩ le_rfl)

/-- A `2r`-separated set maps injectively to the centers of any family of radius-`r` Bowen balls
covering it, each point landing in the ball of its image. -/
private lemma exists_injective_bowenBall_center (T : X → X) (n : ℕ) (r : ℝ) (F C : Set X)
    (hn : 1 ≤ n) (hF_sep : IsBowenSeparated T n (2 * r) F)
    (hC : F ⊆ ⋃ y ∈ C, bowenBall T n y r) :
    ∃ π : F → C, Function.Injective π ∧
      ∀ x : F, x.1 ∈ bowenBall T n (π x).1 r := by
  have H : ∀ x : F, ∃ c : C, x.1 ∈ bowenBall T n c.1 r := by
    intro x
    have h1 := hC x.2
    simp only [Set.mem_iUnion, exists_prop] at h1
    rcases h1 with ⟨y, hyC, hxy⟩
    use ⟨y, hyC⟩
  choose π hπ using H
  use π
  constructor
  · intro x y hxy
    by_contra hneq
    have hneq_val : x.1 ≠ y.1 := fun h ↦ hneq (Subtype.ext h)
    have hsep := hF_sep x.2 y.2 hneq_val
    have h1 := hπ x
    have h2 := hπ y
    rw [hxy] at h1
    rw [bowen_ball_dense_iff T n hn _ _ _] at h1
    rw [bowen_ball_dense_iff T n hn _ _ _] at h2
    have h3 := bowen_ball_dense_triangle T n x.1 (π y).1 y.1
    have h4 := bowen_dist_comm T n x.1 (π y).1
    have h5 := bowen_dist_comm T n (π y).1 y.1
    rw [h4] at h3
    linarith
  · exact hπ

/-- Moving the center inside a Bowen ball and doubling its radius decreases the BS weight. -/
private lemma bsBallWeight_le_of_mem_bowenBall
    (T : X → X) (u : X → ℝ) {a r : ℝ} (ha : 0 ≤ a) (n : ℕ) (x y : X)
    (hxy : x ∈ bowenBall T n y r) :
    bsBallWeight T u a n x (2 * r) ≤ bsBallWeight T u a n y r := by
  apply ENNReal.antitone_rpow_of_nonpos (-a) (neg_nonpos.mpr ha)
  refine iSup_mono fun z ↦ iSup_mono' fun hz ↦ ⟨?_, le_rfl⟩
  dsimp [bowenBall] at hxy hz ⊢
  rw [Dynamics.mem_dynEntourage] at hxy hz ⊢
  intro k hk
  calc
    dist (T^[k] x) (T^[k] z) ≤ dist (T^[k] x) (T^[k] y) + dist (T^[k] y) (T^[k] z) :=
      dist_triangle _ _ _
    _ = dist (T^[k] y) (T^[k] x) + dist (T^[k] y) (T^[k] z) := by rw [dist_comm]
    _ < r + r := add_lt_add (hxy k hk) (hz k hk)
    _ = 2 * r := by ring

/-- If the weights at radius `2r` of the points of `F` are dominated by the weights at radius `r`
of their images under an injective map to `C`, the cost of `F` at radius `2r` is at most the
cost of `C` at radius `r`. -/
private lemma bsPartitionCoverCost_le_of_injective
    (T : X → X) (u : X → ℝ) (a r : ℝ) (n : ℕ) (F C : Set X)
    (π : F → C) (hπ : Function.Injective π)
    (hweight : ∀ x : F,
      bsBallWeight T u a n x.1 (2 * r) ≤ bsBallWeight T u a n (π x).1 r) :
    bsPartitionCoverCost T u a (2 * r) n F ≤ bsPartitionCoverCost T u a r n C :=
  (ENNReal.tsum_le_tsum hweight).trans
    (ENNReal.summable.tsum_le_tsum_of_inj (g := fun c : C ↦ bsBallWeight T u a n c.val r) π
      hπ (fun _ _ ↦ bot_le) (fun _ ↦ le_rfl) ENNReal.summable)

/-- Separated BS sums at twice the radius are bounded by covering BS sums.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified_upper (T : X → X) (u : X → ℝ) (Z : Set X) (a r : ℝ) (ha : 0 ≤ a)
    (n : ℕ) (hn : 1 ≤ n) :
    separatedBSSum T u Z a (2 * r) n ≤ bsPartitionSum T u Z a r n := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  have hC' : F ⊆ ⋃ y ∈ C, bowenBall T n y r := Set.Subset.trans hF.1 hC.2
  have ⟨π, hπ_inj, hπ_ball⟩ := exists_injective_bowenBall_center T n r F C hn hF.2 hC'
  have hweight : ∀ x : F, bsBallWeight T u a n x.1 (2 * r) ≤ bsBallWeight T u a n (π x).1 r :=
    fun x ↦ bsBallWeight_le_of_mem_bowenBall T u ha n x (π x) (hπ_ball x)
  exact bsPartitionCoverCost_le_of_injective T u a r n F C π hπ_inj hweight

/-- The raw sum comparison compares finite covering and finite separated thresholds.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified_finite_lower [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (Z : Set X) (r : ℝ) (hr : 0 < r) :
    upperBSCapacityAt T u Z (2 * r) ≤ separatedBSFiniteCapacityAt T u Z (2 * r) := by
  dsimp [separatedBSFiniteCapacityAt, upperBSCapacityAt]
  apply le_iInf; intro a
  apply le_iInf; intro ha
  apply le_iInf; intro h_limsup
  have H : limsup (bsPartitionSum T u Z a (2 * r)) atTop ≤ limsup (separatedBSSum T u Z a (2 * r))
    atTop := by
    apply limsup_le_limsup (hu := isCoboundedUnder_le_of_le atTop (fun (x : ℕ) ↦ (bot_le : ⊥ ≤
      bsPartitionSum T u Z a (2 * r) x))) (hv := isBoundedUnder_of ⟨⊤, fun (x : ℕ) ↦ (le_top :
      separatedBSSum T u Z a (2 * r) x ≤ ⊤)⟩)
    filter_upwards [Ici_mem_atTop 1] with n hn
    exact bsSpanSepModified T hT u Z a r hr n hn
  have h_limsup2 : limsup (bsPartitionSum T u Z a (2 * r)) atTop < ⊤ := H.trans_lt h_limsup
  apply iInf_le_of_le a
  apply iInf_le_of_le ha
  apply iInf_le_of_le h_limsup2
  rfl

/-- The reverse raw comparison still uses finite thresholds on both sides.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified_finite_upper (T : X → X)
    (u : X → ℝ) (Z : Set X) (r : ℝ) :
    separatedBSFiniteCapacityAt T u Z (2 * r) ≤ upperBSCapacityAt T u Z r := by
  dsimp [separatedBSFiniteCapacityAt, upperBSCapacityAt]
  apply le_iInf; intro a
  apply le_iInf; intro ha
  apply le_iInf; intro h_limsup
  have H : limsup (separatedBSSum T u Z a (2 * r)) atTop ≤ limsup (bsPartitionSum T u Z a r) atTop
    := by
    apply limsup_le_limsup (hu := isCoboundedUnder_le_of_le atTop (fun (x : ℕ) ↦ (bot_le : ⊥ ≤
      separatedBSSum T u Z a (2 * r) x))) (hv := isBoundedUnder_of ⟨⊤, fun (x : ℕ) ↦ (le_top :
      bsPartitionSum T u Z a r x ≤ ⊤)⟩)
    filter_upwards [Ici_mem_atTop 1] with n hn
    exact bsSpanSepModified_upper T u Z a r ha n hn
  have h_limsup2 : limsup (separatedBSSum T u Z a (2 * r)) atTop < ⊤ := H.trans_lt h_limsup
  apply iInf_le_of_le a
  apply iInf_le_of_le ha
  apply iInf_le_of_le h_limsup2
  rfl

/-- The finite separated threshold is at most the zero separated threshold, since a vanishing
upper mass limit is in particular finite. -/
private lemma separatedBSFiniteCapacityAt_le_separatedBSZeroCapacityAt
    (T : X → X) (u : X → ℝ) (C : Set X) (r : ℝ) :
    separatedBSFiniteCapacityAt T u C r ≤ separatedBSZeroCapacityAt T u C r := by
  unfold separatedBSFiniteCapacityAt separatedBSZeroCapacityAt
  refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hzero ↦ ?_
  have hfinite : limsup (separatedBSSum T u C a r) atTop < ⊤ := by
    rw [hzero]
    exact ENNReal.zero_lt_top
  exact iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le hfinite le_rfl))

/-- Restricting the underlying set decreases separated sums. -/
private lemma separatedBSSum_mono (T : X → X) (u : X → ℝ) (a r : ℝ) (n : ℕ) {C D : Set X}
    (hCD : C ⊆ D) : separatedBSSum T u C a r n ≤ separatedBSSum T u D a r n := by
  unfold separatedBSSum
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  exact le_iSup_of_le F (le_iSup_of_le ⟨hF.1.trans hCD, hF.2⟩ le_rfl)

/-- Restricting the underlying set decreases separated sums and hence their finite threshold. -/
private lemma monotone_separatedBSFiniteCapacityAt
    (T : X → X) (u : X → ℝ) (r : ℝ) :
    Monotone (fun C : Set X ↦ separatedBSFiniteCapacityAt T u C r) := by
  intro C D hCD
  unfold separatedBSFiniteCapacityAt
  refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hfinite ↦ ?_
  have hlim : limsup (separatedBSSum T u C a r) atTop ≤
      limsup (separatedBSSum T u D a r) atTop :=
    limsup_le_limsup (Eventually.of_forall fun n ↦ separatedBSSum_mono T u a r n hCD)
  exact iInf_le_of_le a
    (iInf_le_of_le ha (iInf_le_of_le (hlim.trans_lt hfinite) le_rfl))

omit [MetricSpace X] in
/-- A countable cover of `Z` is refined by countably many intersections of its members with the
uniform positive-average pieces of `Z`: the refinement is indexed by a sequence of triples
`(k, N, ρ)` with `1 ≤ N` and `0 < ρ`, selecting the member `Y k` and the piece with cutoff `N`
and slope `ρ`. -/
private lemma exists_cover_inter_positiveAveragePiece (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (Y : ℕ → Set X) (hY : Z ⊆ ⋃ j, Y j) :
    ∃ e : ℕ → ℕ × ℕ × ℚ, (∀ j, 1 ≤ (e j).2.1 ∧ 0 < (e j).2.2) ∧
      Z ⊆ ⋃ j, Y (e j).1 ∩ positiveAveragePiece T u Z (e j).2.1 (e j).2.2 := by
  classical
  let I := ℕ × {N : ℕ // 1 ≤ N} × {ρ : ℚ // 0 < ρ}
  have hI : Nonempty I := ⟨⟨0, ⟨1, le_rfl⟩, ⟨1, by norm_num⟩⟩⟩
  obtain ⟨e, he⟩ := @exists_surjective_nat I hI inferInstance
  refine ⟨fun j ↦ ((e j).1, (e j).2.1.1, (e j).2.2.1), fun j ↦ ⟨(e j).2.1.2, (e j).2.2.2⟩, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hY hx)
  have hxpiece := hx
  rw [uniformPositivePieces T u Z hZ] at hxpiece
  simp only [Set.mem_iUnion] at hxpiece
  obtain ⟨N, hN, ρ, hρ, hxpiece⟩ := hxpiece
  obtain ⟨j, hj⟩ := he ⟨k, ⟨N, hN⟩, ⟨ρ, hρ⟩⟩
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  simp only [hj]
  exact ⟨hk, hxpiece⟩

/-- Every countable cover of `Z` has a refinement into countably many sets, each contained in a
member of the cover and in a uniform positive-average piece, whose separated zero thresholds are
bounded by the finite separated thresholds of the original members. -/
private lemma exists_refinement_separatedBSZeroCapacityAt_le
    (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) (hr : 0 < r)
    (Y : ℕ → Set X) (hY_sub : ∀ j, Y j ⊆ Z) (hY_cov : Z ⊆ ⋃ j, Y j) :
    ∃ W : ℕ → Set X, ((∀ j, W j ⊆ Z) ∧ Z ⊆ ⋃ j, W j) ∧
      (⨆ j, separatedBSZeroCapacityAt T u (W j) r) ≤
        ⨆ j, separatedBSFiniteCapacityAt T u (Y j) r := by
  obtain ⟨e, he, hcov⟩ := exists_cover_inter_positiveAveragePiece T u Z hZ Y hY_cov
  refine ⟨fun j ↦ Y (e j).1 ∩ positiveAveragePiece T u Z (e j).2.1 (e j).2.2,
    ⟨fun j ↦ Set.inter_subset_left.trans (hY_sub (e j).1), hcov⟩, iSup_le fun j ↦ ?_⟩
  rw [← bsFiniteZeroUniformPiece_separated_threshold T u _ (e j).2.1
    ((e j).2.2 : ℝ) (Rat.cast_pos.mpr (he j).2) (fun x hx n hn ↦ hx.2.2 n hn) r hr]
  exact (monotone_separatedBSFiniteCapacityAt T u r Set.inter_subset_left).trans
    (le_iSup (fun k ↦ separatedBSFiniteCapacityAt T u (Y k) r) (e j).1)

/-- Refinement by positive-average pieces identifies the two modified separated thresholds.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified_refinement (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) (hr : 0 < r) :
    modifiedSeparatedBSDimension T u Z r =
      ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
        ⨆ j, separatedBSFiniteCapacityAt T u (Y j) r := by
  apply le_antisymm
  · refine le_iInf fun Y ↦ le_iInf fun hY ↦ ?_
    obtain ⟨W, hW, hbound⟩ := exists_refinement_separatedBSZeroCapacityAt_le
      T u Z hZ r hr Y hY.1 hY.2
    exact iInf_le_of_le W (iInf_le_of_le hW hbound)
  · unfold modifiedSeparatedBSDimension
    apply iInf_mono
    intro Y
    apply iInf_mono
    intro hY
    exact iSup_mono fun j ↦ separatedBSFiniteCapacityAt_le_separatedBSZeroCapacityAt T u (Y j) r

/-- After countable modification the covering finite threshold bounds the separated zero one.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified_modified_lower [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) (hr : 0 < r) :
    modifiedUpperBSDimension T u Z (2 * r) ≤
      modifiedSeparatedBSDimension T u Z (2 * r) := by
  have H := bsSpanSepModified_refinement T u Z hZ (2 * r) (mul_pos zero_lt_two hr)
  rw [H]
  dsimp [modifiedUpperBSDimension]
  apply iInf_mono; intro Y
  apply iInf_mono; intro hY
  apply iSup_mono; intro k
  exact bsSpanSepModified_finite_lower T hT u (Y k) r hr

/-- The reverse modified comparison uses uniform-positive refinement before changing thresholds.
Blueprint node `pack:bs-span-sep`. -/
theorem bsSpanSepModified_modified_upper (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) (hr : 0 < r) :
    modifiedSeparatedBSDimension T u Z (2 * r) ≤ modifiedUpperBSDimension T u Z r := by
  have hr2 : 0 < 2 * r := by positivity
  rw [bsSpanSepModified_refinement T u Z hZ (2 * r) hr2]
  dsimp [modifiedUpperBSDimension]
  apply le_iInf; intro Y
  apply le_iInf; intro hY
  apply iInf_le_of_le Y
  apply iInf_le_of_le hY
  apply iSup_mono; intro j
  apply bsSpanSepModified_finite_upper T u (Y j) r

/-- An order-`n`, `2r`-separated set gives a radius-`r` packing above any cutoff at most `n`,
and increasing the weight radius to `2r` decreases its cost; hence separated sums at radius
`2r` are bounded by packing contents at radius `r`. -/
private lemma separatedBSSum_le_bsPackingContent [SeparableSpace X]
    (T : X → X) (hT : Continuous T) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) (N n : ℕ) (hn : max 1 N ≤ n) :
    separatedBSSum T u Z a (2 * r) n ≤ bsPackingContent T u Z a r N := by
  classical
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  unfold separatedBSSum
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  let G : Set (X × ℕ) := (fun x ↦ (x, n)) '' F
  have hG : IsBowenPacking T Z r N G := by
    refine ⟨?_, ?_, ?_⟩
    · exact (countableSeparatedMaximalNet_countable T hT n hn1 (2 * r)
        (mul_pos zero_lt_two hr) F hF.2).image (fun x ↦ (x, n))
    · rintro p ⟨x, hx, rfl⟩
      exact ⟨hF.1 hx, hn⟩
    · rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hpq
      apply Set.disjoint_left.mpr
      intro z hzx hzy
      have hxy : x ≠ y := fun h ↦ hpq (by rw [h])
      have hsep := hF.2 hx hy hxy
      have hxz := (bowen_ball_dense_iff T n hn1 x z r).mp hzx
      have hyz := (bowen_ball_dense_iff T n hn1 y z r).mp hzy
      have htri := bowen_ball_dense_triangle T n x z y
      rw [bowen_dist_comm T n z y] at htri
      linarith
  let f : F → G := fun x ↦ ⟨(x.val, n), ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun p : G ↦ p.val.1) h)
  calc
    bsPartitionCoverCost T u a (2 * r) n F ≤
        ∑' x : F, bsBallWeight T u a n x.val r := by
      apply ENNReal.tsum_le_tsum
      intro x
      exact bsBallWeight_le_of_radius_le T u a ha n x.val
        (by linarith : r ≤ 2 * r)
    _ ≤ bsPackingSum T u a r G :=
      ENNReal.tsum_comp_le_tsum_of_injective hf
        (fun p : G ↦ bsBallWeight T u a p.val.2 p.val.1 r)
    _ ≤ bsPackingContent T u Z a r N :=
      le_iSup_of_le G (le_iSup_of_le hG le_rfl)

/-- Finite packing precontent supplies a cutoff with finite content, which eventually bounds the
separated sums at the doubled radius. -/
private lemma limsup_separatedBSSum_lt_top_of_bsPackingPrecontent_lt_top [SeparableSpace X]
    (T : X → X) (hT : Continuous T) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r)
    (hfinite : bsPackingPrecontent T u Z a r < ⊤) :
    limsup (separatedBSSum T u Z a (2 * r)) atTop < ⊤ := by
  simp only [bsPackingPrecontent, iInf_lt_iff] at hfinite
  obtain ⟨N, hN, hcontent⟩ := hfinite
  apply lt_of_le_of_lt _ hcontent
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ ↦ bot_le))
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  exact separatedBSSum_le_bsPackingContent T hT u Z a r ha hr N n hn

/-- A finite packing outer envelope at exponent `a` gives a countable cover with finite
precontents, whose pieces have finite separated upper mass limits; positive-average refinement
then bounds the modified separated dimension at the doubled radius by `a`. -/
private lemma modifiedSeparatedBSDimension_le_of_bsPackingOuterEnvelope_lt_top [SeparableSpace X]
    (T : X → X) (hT : Continuous T) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r)
    (hfinite : bsPackingOuterEnvelope T u Z a r < ⊤) :
    modifiedSeparatedBSDimension T u Z (2 * r) ≤ ENNReal.ofReal a := by
  simp only [bsPackingOuterEnvelope, iInf_lt_iff] at hfinite
  obtain ⟨Y, hY, hsum⟩ := hfinite
  rw [bsSpanSepModified_refinement T u Z hZ (2 * r) (mul_pos zero_lt_two hr)]
  refine iInf_le_of_le Y (iInf_le_of_le hY (iSup_le fun j ↦ ?_))
  have hpiece : bsPackingPrecontent T u (Y j) a r < ⊤ :=
    (ENNReal.le_tsum j).trans_lt hsum
  have hlim := limsup_separatedBSSum_lt_top_of_bsPackingPrecontent_lt_top T hT u (Y j) a r ha hr
    hpiece
  unfold separatedBSFiniteCapacityAt
  exact iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le hlim le_rfl))

/-- Packing BS dimension bounds the separated modification on the positive-average locus.
Blueprint node `pack:bs-pack-to-sep`. -/
theorem bsPackBoundsSeparated [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    separatedBSDimension T u Z ≤ packingBSDimension T u Z := by
  unfold separatedBSDimension
  refine iSup_le fun p ↦ ?_
  have hr : 0 < dyadicRadius (p + 1) := by unfold dyadicRadius; positivity
  have hscale : 2 * dyadicRadius (p + 1) = dyadicRadius p := by
    unfold dyadicRadius
    rw [pow_succ]
    ring
  have hbound : modifiedSeparatedBSDimension T u Z (2 * dyadicRadius (p + 1)) ≤
      packingBSDimensionAt T u Z (dyadicRadius (p + 1)) := by
    unfold packingBSDimensionAt
    refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun hzero ↦ ?_
    apply modifiedSeparatedBSDimension_le_of_bsPackingOuterEnvelope_lt_top T hT u Z hZ a _ ha hr
    rw [hzero]
    exact ENNReal.zero_lt_top
  rw [hscale] at hbound
  exact hbound.trans (le_iSup (fun q ↦ packingBSDimensionAt T u Z (dyadicRadius q))
    (p + 1))

/-- The centers in one order slice of a radius-`r` packing are `r`-separated, so their cost is
bounded by the separated sum at that same radius. -/
private lemma bsPartitionCoverCost_slice_le_separatedBSSum (T : X → X) (u : X → ℝ)
    (C : Set X) (r : ℝ) (hr : 0 < r) (L k : ℕ)
    (F : Set (X × ℕ)) (hF : IsBowenPacking T C r L F) (a : ℝ) :
    bsPartitionCoverCost T u a r k {x | (x, k) ∈ F} ≤
      separatedBSSum T u C a r k := by
  have hsub : {x | (x, k) ∈ F} ⊆ C := fun x hx ↦ (hF.2.1 (x, k) hx).1
  have hsep : IsBowenSeparated T k r {x | (x, k) ∈ F} := by
    intro x hx y hy hxy
    have hk : 1 ≤ k := (le_max_left 1 L).trans (hF.2.1 (x, k) hx).2
    have hdisj := hF.2.2 hx hy (by simpa using hxy)
    apply le_of_not_gt
    intro hclose
    have hyx : y ∈ bowenBall T k x r :=
      (bowen_ball_dense_iff T k hk x y r).mpr hclose
    have hyy : y ∈ bowenBall T k y r := by
      simp only [bowenBall, Set.mem_ofPred_eq, Dynamics.mem_dynEntourage, dist_self]
      exact fun _ _ ↦ hr
    exact Set.disjoint_left.mp hdisj hyx hyy
  exact le_iSup_of_le {x | (x, k) ∈ F} (le_iSup_of_le ⟨hsub, hsep⟩ le_rfl)

/-- A decorated family supported above `L` is regrouped into its order slices, retaining each
center once: its packing sum is the sum of the slice costs. -/
private lemma bsPackingSum_eq_tsum_slices (T : X → X) (u : X → ℝ)
    (a r : ℝ) (L : ℕ) (F : Set (X × ℕ))
    (hF : ∀ p ∈ F, L ≤ p.2) :
    bsPackingSum T u a r F = ∑' k : {k : ℕ // L ≤ k},
      bsPartitionCoverCost T u a r k.val {x | (x, k.val) ∈ F} := by
  let e : F ≃ (Σ k : {k : ℕ // L ≤ k}, {x : X // (x, k.val) ∈ F}) :=
    { toFun := fun p ↦ ⟨⟨p.val.2, hF p.val p.property⟩, ⟨p.val.1, p.property⟩⟩
      invFun := fun p ↦ ⟨(p.2.val, p.1.val), p.2.property⟩
      left_inv := fun p ↦ by cases p; rfl
      right_inv := fun p ↦ by rcases p with ⟨⟨k, hk⟩, ⟨x, hx⟩⟩; rfl }
  calc
    bsPackingSum T u a r F =
        ∑' p : (Σ k : {k : ℕ // L ≤ k}, {x : X // (x, k.val) ∈ F}),
          bsBallWeight T u a p.1.val p.2.val r :=
      e.tsum_eq (fun p ↦ bsBallWeight T u a p.1.val p.2.val r)
    _ = _ := ENNReal.tsum_sigma' _

/-- A uniform lower Birkhoff bound `ρ * n` supplies an exponential factor when the BS exponent
increases from `t` to `s`. This includes the case of an infinite potential supremum. -/
private lemma bsBallWeight_le_two_rpow_mul_of_le_birkhoffSum (T : X → X) (u : X → ℝ)
    (C : Set X) (N : ℕ) (ρ : ℝ)
    (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (t s r : ℝ) (ht : 0 ≤ t) (hts : t < s) (hr : 0 < r)
    (k : ℕ) (hk : N ≤ k) (x : X) (hx : x ∈ C) :
    bsBallWeight T u s k x r ≤
      (2 : ℝ≥0∞) ^ (-((s - t) * ρ) * (k : ℝ)) * bsBallWeight T u t k x r := by
  let S := pressureBallWeight T u .supremum k x r
  have hbase : (2 : ℝ≥0∞) ^ (ρ * k) ≤ S := by
    have hxx : x ∈ bowenBall T k x r := by
      simp only [bowenBall, Set.mem_ofPred_eq, Dynamics.mem_dynEntourage, dist_self]
      exact fun _ _ ↦ hr
    exact (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (hC x hx k hk)).trans
      (le_iSup_of_le x (le_iSup_of_le hxx le_rfl))
  change S ^ (-s) ≤ (2 : ℝ≥0∞) ^ (-((s - t) * ρ) * (k : ℝ)) * S ^ (-t)
  by_cases htop : S = ⊤
  · rw [htop, ENNReal.top_rpow_of_neg (by linarith : -s < 0)]
    exact bot_le
  have hzero : S ≠ 0 := ne_of_gt
    ((ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 2) (by norm_num)).trans_le hbase)
  have hgap : S ^ (-(s - t)) ≤ (2 : ℝ≥0∞) ^ (-((s - t) * ρ) * (k : ℝ)) := by
    have h := ENNReal.antitone_rpow_of_nonpos
      (-(s - t)) (by linarith) hbase
    calc
      S ^ (-(s - t)) ≤ ((2 : ℝ≥0∞) ^ (ρ * k)) ^ (-(s - t)) := h
      _ = _ := by rw [← ENNReal.rpow_mul]; congr 1; ring
  calc
    S ^ (-s) = S ^ (-(s - t) + (-t)) := by congr 1; ring
    _ = S ^ (-(s - t)) * S ^ (-t) := ENNReal.rpow_add _ _ hzero htop
    _ ≤ _ := by gcongr

/-- Regrouping by order and comparing weights bounds any mixed-order packing by a geometrically
weighted tail of the separated sums on its uniform positive piece. -/
private lemma bsPackingSum_le_tsum_two_rpow_mul_separatedBSSum (T : X → X) (u : X → ℝ)
    (C : Set X) (N : ℕ) (ρ : ℝ)
    (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (t s r : ℝ) (ht : 0 ≤ t) (hts : t < s) (hr : 0 < r)
    (L : ℕ) (hL : N ≤ L) (F : Set (X × ℕ))
    (hF : IsBowenPacking T C r L F) :
    bsPackingSum T u s r F ≤ ∑' k : {k : ℕ // L ≤ k},
      (2 : ℝ≥0∞) ^ (-((s - t) * ρ) * (k.val : ℝ)) *
        separatedBSSum T u C t r k.val := by
  rw [bsPackingSum_eq_tsum_slices T u s r L F
    (fun p hp ↦ (le_max_right 1 L).trans (hF.2.1 p hp).2)]
  apply ENNReal.tsum_le_tsum
  intro k
  calc
    bsPartitionCoverCost T u s r k.val {x | (x, k.val) ∈ F} ≤
        ∑' x : {x | (x, k.val) ∈ F},
          (2 : ℝ≥0∞) ^ (-((s - t) * ρ) * (k.val : ℝ)) *
            bsBallWeight T u t k.val x.val r := by
      exact ENNReal.tsum_le_tsum fun x ↦ bsBallWeight_le_two_rpow_mul_of_le_birkhoffSum
        T u C N ρ hC t s r ht hts hr k.val (hL.trans k.property) x.val
        (hF.2.1 (x.val, k.val) x.property).1
    _ = (2 : ℝ≥0∞) ^ (-((s - t) * ρ) * (k.val : ℝ)) *
        bsPartitionCoverCost T u t r k.val {x | (x, k.val) ∈ F} :=
      ENNReal.tsum_mul_left
    _ ≤ _ := by
      gcongr
      exact bsPartitionCoverCost_slice_le_separatedBSSum T u C r hr L k.val F hF t

/-- On a uniform positive-average piece, a vanishing separated limsup at `t` forces zero packing
precontent at every larger exponent `s`. Positive precontent would, by mixed-order extraction,
force a fixed positive separated mass arbitrarily late. -/
private lemma bsPackingPrecontent_eq_zero_of_limsup_separatedBSSum_eq_zero (T : X → X)
    (u : X → ℝ)
    (C : Set X) (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hC : ∀ x ∈ C, ∀ n ≥ N, ρ * n ≤ birkhoffSum T u n x)
    (t s r : ℝ) (ht : 0 ≤ t) (hts : t < s) (hr : 0 < r)
    (hb : limsup (separatedBSSum T u C t r) atTop = 0) :
    bsPackingPrecontent T u C s r = 0 := by
  by_contra hnonzero
  have hpos : 0 < bsPackingPrecontent T u C s r := bot_lt_iff_ne_bot.mpr hnonzero
  obtain ⟨a, _, hapos, hapre⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have ha : 0 < a := ENNReal.ofReal_pos.mp hapos
  let d := (s - t) * ρ
  have hd : 0 < d := mul_pos (sub_pos.mpr hts) hρ
  have hcpos : 0 < ENNReal.ofReal ((1 - (2 : ℝ) ^ (-d)) * a) := by
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (neg_neg_of_pos hd))) ha
  have hfrequent : ∃ᶠ k in atTop,
      ENNReal.ofReal ((1 - (2 : ℝ) ^ (-d)) * a) ≤ separatedBSSum T u C t r k := by
    apply frequently_atTop.mpr
    intro M
    let L := max N (max 1 M)
    have hLN : N ≤ L := le_max_left _ _
    have hL1 : 1 ≤ L := (le_max_left 1 M).trans (le_max_right N (max 1 M))
    have hLM : M ≤ L := (le_max_right 1 M).trans (le_max_right N (max 1 M))
    have hcontent : ENNReal.ofReal a < bsPackingContent T u C s r L :=
      hapre.trans_le (iInf_le_of_le L (iInf_le_of_le hL1 le_rfl))
    obtain ⟨F, hF⟩ := lt_iSup_iff.mp hcontent
    obtain ⟨hpacking, hsum⟩ := lt_iSup_iff.mp hF
    have hmass : ENNReal.ofReal a ≤ ∑' k : {k : ℕ // L ≤ k},
        (2 : ℝ≥0∞) ^ (-(d - 0) * (k.val : ℝ)) * separatedBSSum T u C t r k.val := by
      simpa only [sub_zero] using hsum.le.trans
        (bsPackingSum_le_tsum_two_rpow_mul_separatedBSSum T u C N ρ hC t s r ht hts hr
          L hLN F hpacking)
    obtain ⟨k, hk, hmassk⟩ := extractOrder d 0 a hd ha
      (separatedBSSum T u C t r) L hL1 hmass
    exact ⟨k, hLM.trans hk, by simpa only [sub_zero] using hmassk⟩
  have hle := le_limsup_of_frequently_le hfrequent
  rw [hb] at hle
  exact (not_le_of_gt hcpos) hle

/-- Refining a countable cover into positive pieces bounds the packing threshold
by the supremum of the separated zero thresholds of its members. -/
private lemma packingBSDimensionAt_le_modifiedSeparatedBSDimension (T : X → X) (u : X → ℝ)
    (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (r : ℝ) (hr : 0 < r) :
    packingBSDimensionAt T u Z r ≤ modifiedSeparatedBSDimension T u Z r := by
  unfold modifiedSeparatedBSDimension
  refine le_iInf fun Y ↦ le_iInf fun hY ↦ ?_
  apply le_of_not_gt
  intro hlt
  obtain ⟨s, hs, hbelow, habove⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hzero : bsPackingOuterEnvelope T u Z s r = 0 := by
    have hcap (j : ℕ) : separatedBSZeroCapacityAt T u (Y j) r < ENNReal.ofReal s :=
      (le_iSup (fun k ↦ separatedBSZeroCapacityAt T u (Y k) r) j).trans_lt hbelow
    have hpieces : ∀ j N, 1 ≤ N → ∀ ρ : ℚ, 0 < ρ →
        bsPackingPrecontent T u (Y j ∩ positiveAveragePiece T u Z N ρ) s r = 0 := by
      intro j N hN ρ hρ
      have hexp := hcap j
      simp only [separatedBSZeroCapacityAt, iInf_lt_iff] at hexp
      obtain ⟨t, ht, hzero, hts⟩ := hexp
      have htsReal : t < s := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp hts
      have hlim : limsup
          (separatedBSSum T u (Y j ∩ positiveAveragePiece T u Z N ρ) t r) atTop ≤
          limsup (separatedBSSum T u (Y j) t r) atTop := by
        exact limsup_le_limsup (Eventually.of_forall fun n ↦
          separatedBSSum_mono T u t r n Set.inter_subset_left)
      apply bsPackingPrecontent_eq_zero_of_limsup_separatedBSSum_eq_zero T u
        (Y j ∩ positiveAveragePiece T u Z N ρ) N (ρ : ℝ) (Rat.cast_pos.mpr hρ)
        (fun x hx n hn ↦ hx.2.2 n hn) t s r ht htsReal hr
      exact le_antisymm (hlim.trans_eq hzero) bot_le
    obtain ⟨e, he, hcov⟩ := exists_cover_inter_positiveAveragePiece T u Z hZ Y hY.2
    apply le_antisymm _ bot_le
    unfold bsPackingOuterEnvelope
    refine iInf_le_of_le (fun j ↦ Y (e j).1 ∩ positiveAveragePiece T u Z (e j).2.1 (e j).2.2)
      (iInf_le_of_le ⟨fun j ↦ Set.inter_subset_left.trans (hY.1 (e j).1), hcov⟩ ?_)
    exact (ENNReal.tsum_eq_zero.mpr fun j ↦ hpieces _ _ (he j).1 _ (he j).2).le
  have hbound : packingBSDimensionAt T u Z r ≤ ENNReal.ofReal s :=
    iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le hzero le_rfl))
  exact not_lt_of_ge hbound habove

/-- Separated modification bounds packing BS dimension after uniform-positive localization.
Blueprint node `pack:bs-sep-to-pack`. -/
theorem bsSeparatedBoundsPack (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    packingBSDimension T u Z ≤ separatedBSDimension T u Z := by
  unfold packingBSDimension separatedBSDimension
  exact iSup_mono fun p ↦ packingBSDimensionAt_le_modifiedSeparatedBSDimension T u Z hZ
    (dyadicRadius p) (by unfold dyadicRadius; positivity)

/-- Packing and modified separated BS dimensions agree on the positive-average locus.
Blueprint node `pack:bs-equivalence`. -/
theorem bsEquivalence [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    packingBSDimension T u Z = separatedBSDimension T u Z := by
  exact le_antisymm
    (bsSeparatedBoundsPack T u Z hZ)
    (bsPackBoundsSeparated T hT u Z hZ)

/-- Doubling the radius maps small positive radii to small positive radii. -/
private lemma tendsto_two_mul_nhdsWithin_Ioi_zero :
    Tendsto (fun r ↦ 2 * r) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝[Set.Ioi 0] 0) := by
  have H1 : Tendsto (fun r ↦ 2 * (r : ℝ)) (𝓝 0) (𝓝 (2 * 0)) := tendsto_const_nhds.mul tendsto_id
  have H1' : Tendsto (fun r ↦ 2 * (r : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using H1
  have H2 : ∀ᶠ r in 𝓝[Set.Ioi 0] (0 : ℝ), 0 < 2 * r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos zero_lt_two hr
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (Tendsto.mono_left H1'
    inf_le_left) H2

/-- The separated scale-zero dimension equals the existing modified covering BS dimension.
Blueprint node `pack:bs-equivalence`. -/
theorem bsEquivalence_covering [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    separatedBSDimension T u Z = upperBSDimension T u Z := by
  have hsep : Tendsto (fun r ↦ modifiedSeparatedBSDimension T u Z (2 * r))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (separatedBSDimension T u Z)) :=
    (bsPackingSeparatedDefinitions_separated_scale_limit T u Z).comp
      tendsto_two_mul_nhdsWithin_Ioi_zero
  apply le_antisymm
  · refine le_of_tendsto_of_tendsto hsep (upperBSDimension_radius_limit T u Z) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact bsSpanSepModified_modified_upper T u Z hZ r hr
  · have hupper : Tendsto (fun r ↦ modifiedUpperBSDimension T u Z (2 * r))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (upperBSDimension T u Z)) :=
      (upperBSDimension_radius_limit T u Z).comp tendsto_two_mul_nhdsWithin_Ioi_zero
    refine le_of_tendsto_of_tendsto hupper hsep ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact bsSpanSepModified_modified_lower T hT u Z hZ r hr

/-- Packing BS dimension equals the frozen upper BS dimension from the point-to-set theorem.
Blueprint node `pack:bs-equivalence`. -/
theorem bsEquivalence_upper [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    packingBSDimension T u Z = upperBSDimension T u Z := by
  exact (bsEquivalence T hT u Z hZ).trans (bsEquivalence_covering T hT u Z hZ)

/-- The existing modified covering thresholds converge to the common dimension.
Blueprint node `pack:bs-equivalence`. -/
theorem bsEquivalence_covering_limit [SeparableSpace X] (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    Tendsto (modifiedUpperBSDimension T u Z) (𝓝[Set.Ioi 0] 0)
      (𝓝 (packingBSDimension T u Z)) := by
  rw [bsEquivalence_upper T hT u Z hZ]
  exact upperBSDimension_radius_limit T u Z

end Kolmogorov.PointToSet
