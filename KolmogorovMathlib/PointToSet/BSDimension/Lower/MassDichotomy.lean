/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Lower.Realizers

/-!
# Mass dichotomy for the lower Barreira-Schmeling dimension

This module proves the structural properties of the lower covering mass
`lowerBSMass` / `lowerBSMassLimit` that turn it into a dimension:

* `lowerBSMass_scale_limit`: the dyadic definition `lowerBSDimension` is the limit of
  `lowerBSDimensionAt` as the radius tends to zero through all positive reals
  (blueprint node `bs:lower-mass`);
* `lowerBSMassCountableSubadditive` and `lowerBSMassCountableSubadditive_limit`: the
  cutoff masses and their limit are countably subadditive, the cover for a union being
  assembled from near-optimal covers of the pieces (blueprint node `bs:subadditivity`);
* `lowerBSDichotomy`, `lowerBSDichotomy_top`, `lowerBSDichotomy_zero`: on a set where the
  lower Birkhoff average is positive, finite mass at an exponent `s` forces zero mass at
  every larger exponent, so the mass is `⊤` below and `0` above the critical exponent
  `lowerBSDimensionAt` (blueprint node `bs:lower-dichotomy`);
* `recenterNearBirkhoffSupremum`: a Bowen ball can be recentered at an ideal point of the
  presentation that nearly attains the supremum of the Birkhoff sum, at the price of
  doubling the radius (blueprint node `bs:recenter`).

The dichotomy is the key step in the lower point-to-set principle for the
Barreira-Schmeling dimension; the recentering lemma is used by `NullCovers` to replace
arbitrary covers by covers centered at ideal points.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### Scale limit -/

/-- The supremum of `lowerBSDimensionAt` over all positive radii is its supremum over the
dyadic radii, that is the lower BS dimension. -/
private lemma sSup_image_lowerBSDimensionAt (T : X → X) (u : X → ℝ) (Z : Set X) :
    sSup (lowerBSDimensionAt T u Z '' Set.Ioi 0) = lowerBSDimension T u Z := by
  have hpos (p : ℕ) : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  refine le_antisymm (sSup_le ?_) (iSup_le fun p ↦ le_sSup ⟨dyadicRadius p, hpos p, rfl⟩)
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one (Set.mem_Ioi.1 hr) (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact (lowerBSMass_antitone_radius_dimension T u Z (hpos p) hr hp.le).trans
    (le_iSup (fun q ↦ lowerBSDimensionAt T u Z (dyadicRadius q)) p)

/-- The dyadic definition equals the limit over all positive radii tending to zero.
Blueprint node `bs:lower-mass`. -/
theorem lowerBSMass_scale_limit (T : X → X) (u : X → ℝ) (Z : Set X) :
    Tendsto (lowerBSDimensionAt T u Z) (𝓝[Set.Ioi 0] 0) (𝓝 (lowerBSDimension T u Z)) := by
  rw [← sSup_image_lowerBSDimensionAt]
  exact (lowerBSMass_antitone_radius_dimension T u Z).tendsto_nhdsGT ⟨⊤, fun _ _ ↦ le_top⟩

/-! ### Countable subadditivity -/

/-- The union of a sequence of Bowen cover families, with the pair `(j, k)` coded as
`Nat.pair j k`. -/
private def unionCoverFamily (C : ℕ → BowenCoverFamily X) : BowenCoverFamily X where
  index := {n | (Nat.unpair n).2 ∈ (C (Nat.unpair n).1).index}
  center n := (C (Nat.unpair n.1).1).center ⟨(Nat.unpair n.1).2, n.2⟩
  order n := (C (Nat.unpair n.1).1).order ⟨(Nat.unpair n.1).2, n.2⟩

omit [MetricSpace X] in
/-- At the index `Nat.pair j k` the union family has the order and center of the `k`-th ball
of the `j`-th family. -/
private lemma unionCoverFamily_pair (C : ℕ → BowenCoverFamily X) (j : ℕ) (k : (C j).index)
    (h : Nat.pair j k ∈ (unionCoverFamily C).index) :
    (unionCoverFamily C).order ⟨Nat.pair j k, h⟩ = (C j).order k ∧
      (unionCoverFamily C).center ⟨Nat.pair j k, h⟩ = (C j).center k := by
  obtain ⟨k, hk⟩ := k
  have key : ∀ a : ℕ × ℕ, a = (j, k) → ∀ ha : a.2 ∈ (C a.1).index,
      (C a.1).order ⟨a.2, ha⟩ = (C j).order ⟨k, hk⟩ ∧
        (C a.1).center ⟨a.2, ha⟩ = (C j).center ⟨k, hk⟩ := by
    rintro a rfl ha
    exact ⟨rfl, rfl⟩
  exact key _ (Nat.unpair_pair j k) _

/-- The indices of the union family are in bijection with the sigma type of the indices of
the summands. -/
private noncomputable def unionCoverFamilyEquiv (C : ℕ → BowenCoverFamily X) :
    (Σ j, (C j).index) ≃ (unionCoverFamily C).index :=
  Equiv.ofBijective
    (fun p ↦ ⟨Nat.pair p.1 p.2.1, by
      change (Nat.unpair (Nat.pair p.1 p.2.1)).2 ∈ (C (Nat.unpair (Nat.pair p.1 p.2.1)).1).index
      rw [Nat.unpair_pair]
      exact p.2.2⟩)
    ⟨by
      rintro ⟨j, k, hk⟩ ⟨j', k', hk'⟩ h
      simp only [Subtype.mk.injEq, Nat.pair_eq_pair] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl,
    fun n ↦ ⟨⟨(Nat.unpair n.1).1, (Nat.unpair n.1).2, n.2⟩, Subtype.ext (Nat.pair_unpair n.1)⟩⟩

/-- The union family covers the union of the sets covered by the summands. -/
private lemma isBowenCover_unionCoverFamily {T : X → X} {Z : ℕ → Set X} {r : ℝ} {N : ℕ}
    {C : ℕ → BowenCoverFamily X} (hC : ∀ j, IsBowenCover T (Z j) r N (C j)) :
    IsBowenCover T (⋃ j, Z j) r N (unionCoverFamily C) := by
  refine ⟨fun n ↦ (hC _).1 _, fun x hx ↦ ?_⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ((hC j).2 hj)
  have hmem : Nat.pair j k ∈ (unionCoverFamily C).index := by
    change (Nat.unpair (Nat.pair j k)).2 ∈ (C (Nat.unpair (Nat.pair j k)).1).index
    rw [Nat.unpair_pair]
    exact k.2
  refine Set.mem_iUnion.2 ⟨⟨Nat.pair j k, hmem⟩, ?_⟩
  obtain ⟨h_order, h_center⟩ := unionCoverFamily_pair C j k hmem
  rw [h_order, h_center]
  exact hk

/-- The cost of the union family is the sum of the costs of the summands. -/
private lemma bsCoverCost_unionCoverFamily (T : X → X) (u : X → ℝ) (s r : ℝ)
    (C : ℕ → BowenCoverFamily X) :
    bsCoverCost T u s r (unionCoverFamily C) = ∑' j, bsCoverCost T u s r (C j) := by
  rw [bsCoverCost, ← (unionCoverFamilyEquiv C).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun j ↦ tsum_congr fun k ↦ ?_
  obtain ⟨h_order, h_center⟩ := unionCoverFamily_pair C j k ((unionCoverFamilyEquiv C ⟨j, k⟩).2)
  exact congrArg₂ (bsBallWeight T u s · · r) h_order h_center

/-- A cover of cost below `c` exists whenever the covering infimum is below `c`. -/
private lemma exists_isBowenCover_bsCoverCost_lt {T : X → X} {u : X → ℝ} {Z : Set X}
    {s r : ℝ} {N : ℕ} {c : ℝ≥0∞} (h : lowerBSMass T u Z s r N < c) :
    ∃ C, IsBowenCover T Z r N C ∧ bsCoverCost T u s r C < c := by
  unfold lowerBSMass at h
  simp only [iInf_lt_iff] at h
  obtain ⟨C, hC, hcost⟩ := h
  exact ⟨C, hC, hcost⟩

/-- Lower BS cutoff masses are countably subadditive.
The hypotheses `P`, `hT`, `hu`, `hs`, `hr` and `hN` are not needed by the argument.
Blueprint node `bs:subadditivity`. -/
theorem lowerBSMassCountableSubadditive (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : ℕ → Set X)
    (s r : ℝ) (hs : 0 ≤ s) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N) :
    lowerBSMass T u (⋃ j, Z j) s r N ≤ ∑' j, lowerBSMass T u (Z j) s r N := by
  have _ := P
  have _ := And.intro hT (And.intro hu (And.intro hs (And.intro hr hN)))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hsum ↦ ?_
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hε.ne') ℕ
  have hex (j : ℕ) : ∃ C, IsBowenCover T (Z j) r N C ∧
      bsCoverCost T u s r C < lowerBSMass T u (Z j) s r N + δ j :=
    exists_isBowenCover_bsCoverCost_lt <|
      ENNReal.lt_add_right ((ENNReal.le_tsum j).trans_lt hsum).ne (by simpa using (hδ j).ne')
  choose C hCcov hCcost using hex
  calc lowerBSMass T u (⋃ j, Z j) s r N
      ≤ bsCoverCost T u s r (unionCoverFamily C) :=
        iInf₂_le _ (isBowenCover_unionCoverFamily hCcov)
    _ = ∑' j, bsCoverCost T u s r (C j) := bsCoverCost_unionCoverFamily T u s r C
    _ ≤ ∑' j, (lowerBSMass T u (Z j) s r N + δ j) :=
        ENNReal.tsum_le_tsum fun j ↦ (hCcost j).le
    _ = ∑' j, lowerBSMass T u (Z j) s r N + ∑' j, (δ j : ℝ≥0∞) := ENNReal.tsum_add
    _ ≤ ∑' j, lowerBSMass T u (Z j) s r N + ε := by gcongr

/-- The order-limit masses are countably subadditive without exchanging a limit and sum.
Blueprint node `bs:subadditivity`. -/
theorem lowerBSMassCountableSubadditive_limit (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (Z : ℕ → Set X) (s r : ℝ) (hs : 0 ≤ s) (hr : 0 < r) :
    lowerBSMassLimit T u (⋃ j, Z j) s r ≤ ∑' j, lowerBSMassLimit T u (Z j) s r := by
  refine iSup₂_le fun N hN ↦
    (lowerBSMassCountableSubadditive P T hT u hu Z s r hs hr N hN).trans ?_
  exact ENNReal.tsum_le_tsum fun j ↦ le_iSup₂_of_le N hN le_rfl

/-! ### Dichotomy -/

/-- The limit mass is monotone in the set. -/
private lemma lowerBSMassLimit_mono (T : X → X) (u : X → ℝ) (s r : ℝ) {Z₁ Z₂ : Set X}
    (h : Z₁ ⊆ Z₂) : lowerBSMassLimit T u Z₁ s r ≤ lowerBSMassLimit T u Z₂ s r :=
  iSup₂_mono fun _ _ ↦ iInf₂_mono' fun C hC ↦ ⟨C, ⟨hC.1, h.trans hC.2⟩, le_rfl⟩

/-- If a point of a Bowen ball has Birkhoff sum at least `m`, the ball has sup-weight at
least `2 ^ m`, so raising the exponent from `s` to `t` shrinks its cost by `2 ^ (-(t - s) m)`. -/
private lemma bsBallWeight_le_rpow_mul_bsBallWeight (T : X → X) (u : X → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) {m : ℝ} {n : ℕ} {y z : X} {r : ℝ}
    (hz : m ≤ birkhoffSum T u n z) (hzb : z ∈ bowenBall T n y r) :
    bsBallWeight T u t n y r ≤ (2 : ℝ≥0∞) ^ (-(t - s) * m) * bsBallWeight T u s n y r := by
  unfold bsBallWeight
  set w := pressureBallWeight T u .supremum n y r with hw_def
  have hw : (2 : ℝ≥0∞) ^ m ≤ w :=
    calc (2 : ℝ≥0∞) ^ m ≤ (2 : ℝ≥0∞) ^ birkhoffSum T u n z :=
          ENNReal.rpow_le_rpow_of_exponent_le one_le_two hz
      _ ≤ w := le_iSup₂ (α := ℝ≥0∞) (f := fun x _ ↦ (2 : ℝ≥0∞) ^ birkhoffSum T u n x) z hzb
  have hw0 : 0 < w := (ENNReal.rpow_pos (by norm_num) (by norm_num)).trans_le hw
  rcases eq_or_ne w ⊤ with hw_top | hw_top
  · rw [hw_top, ENNReal.top_rpow_of_neg (by linarith)]
    exact bot_le
  · calc w ^ (-t) = w ^ (-(t - s)) * w ^ (-s) := by
          rw [← ENNReal.rpow_add _ _ hw0.ne' hw_top]
          congr 1
          ring
      _ ≤ ((2 : ℝ≥0∞) ^ m) ^ (-(t - s)) * w ^ (-s) :=
          mul_le_mul' (by
            rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
            exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hw (by linarith))) le_rfl
      _ = (2 : ℝ≥0∞) ^ (-(t - s) * m) * w ^ (-s) := by
          rw [← ENNReal.rpow_mul, mul_comm m]

/-- The sub-family of a Bowen cover consisting of the balls that meet `S`. -/
private def restrictBowenCover (T : X → X) (r : ℝ) (S : Set X) (C : BowenCoverFamily X) :
    BowenCoverFamily X where
  index := {j | ∃ hj : j ∈ C.index,
    ∃ z ∈ S, z ∈ bowenBall T (C.order ⟨j, hj⟩) (C.center ⟨j, hj⟩) r}
  center j := C.center ⟨j.1, j.2.1⟩
  order j := C.order ⟨j.1, j.2.1⟩

/-- A cover of a set covers each of its subsets by the balls that meet the subset. -/
private lemma isBowenCover_restrictBowenCover {T : X → X} {Z S : Set X} {r : ℝ} {N : ℕ}
    {C : BowenCoverFamily X} (hC : IsBowenCover T Z r N C) (hS : S ⊆ Z) :
    IsBowenCover T S r N (restrictBowenCover T r S C) := by
  refine ⟨fun j ↦ hC.1 ⟨j.1, j.2.1⟩, fun z hz ↦ ?_⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hC.2 (hS hz))
  exact Set.mem_iUnion.2 ⟨⟨j.1, j.2, z, hz, hj⟩, hj⟩

/-- If every ball meeting `S` has its `t`-cost bounded by `c` times its `s`-cost, the same
holds for the total cost of the restricted cover. -/
private lemma bsCoverCost_restrictBowenCover_le (T : X → X) (u : X → ℝ) (r s t : ℝ)
    (S : Set X) (c : ℝ≥0∞) (C : BowenCoverFamily X)
    (hS : ∀ i : C.index, (∃ z ∈ S, z ∈ bowenBall T (C.order i) (C.center i) r) →
      bsBallWeight T u t (C.order i) (C.center i) r ≤
        c * bsBallWeight T u s (C.order i) (C.center i) r) :
    bsCoverCost T u t r (restrictBowenCover T r S C) ≤ c * bsCoverCost T u s r C := by
  let g : (restrictBowenCover T r S C).index → C.index := fun j ↦ ⟨j.1, j.2.1⟩
  have hg : Function.Injective g := fun j₁ j₂ h ↦ Subtype.ext (Subtype.mk.inj h)
  calc bsCoverCost T u t r (restrictBowenCover T r S C)
      ≤ ∑' j, c * bsBallWeight T u s (C.order (g j)) (C.center (g j)) r :=
        ENNReal.tsum_le_tsum fun j ↦ hS (g j) (by simpa using j.2.2)
    _ = c * ∑' j, bsBallWeight T u s (C.order (g j)) (C.center (g j)) r :=
        ENNReal.tsum_mul_left
    _ ≤ c * bsCoverCost T u s r C :=
        mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hg
          fun i ↦ bsBallWeight T u s (C.order i) (C.center i) r)

/-- Passing to the points whose Birkhoff sums grow linearly from time `N` and raising the
exponent from `s` to `t` multiplies the cutoff mass (cutoff `N' ≥ N`) by at most
`2 ^ (-(t - s) ρ N')`. -/
private lemma lowerBSMass_positiveAveragePiece_le (T : X → X) (u : X → ℝ) (Z : Set X)
    {N N' : ℕ} (hN' : N ≤ N') {ρ : ℚ} (hρ : 0 < ρ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (r : ℝ) :
    lowerBSMass T u (positiveAveragePiece T u Z N ρ) t r N' ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * ((ρ : ℝ) * N')) * lowerBSMass T u Z s r N' := by
  have hne_zero : (2 : ℝ≥0∞) ^ (-(t - s) * ((ρ : ℝ) * N')) ≠ 0 :=
    (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have hne_top : (2 : ℝ≥0∞) ^ (-(t - s) * ((ρ : ℝ) * N')) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  unfold lowerBSMass
  rw [ENNReal.mul_iInf_of_ne hne_zero hne_top]
  refine le_iInf fun C ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hne_zero hne_top]
  refine le_iInf fun hC ↦ ?_
  refine (iInf₂_le (restrictBowenCover T r (positiveAveragePiece T u Z N ρ) C)
    (isBowenCover_restrictBowenCover hC fun z hz ↦ hz.1)).trans ?_
  refine bsCoverCost_restrictBowenCover_le T u r s t _ _ C ?_
  rintro i ⟨z, hz, hzb⟩
  refine bsBallWeight_le_rpow_mul_bsBallWeight T u hs hst ?_ hzb
  have hn : N' ≤ C.order i := (le_max_right _ _).trans (hC.1 i)
  calc (ρ : ℝ) * N' ≤ ρ * (C.order i) := by gcongr
    _ ≤ birkhoffSum T u (C.order i) z := hz.2 _ (hN'.trans hn)

/-- Finite limit mass at the exponent `s` forces zero limit mass at every larger exponent `t`
on the set of points whose Birkhoff sums grow at least linearly with rate `ρ` from time `N`. -/
private lemma lowerBSMassLimit_positiveAveragePiece_eq_zero (T : X → X) (u : X → ℝ) (Z : Set X)
    (N : ℕ) {ρ : ℚ} (hρ : 0 < ρ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (r : ℝ)
    (hmass : lowerBSMassLimit T u Z s r < ⊤) :
    lowerBSMassLimit T u (positiveAveragePiece T u Z N ρ) t r = 0 := by
  refine le_antisymm (iSup₂_le fun K _ ↦ ?_) bot_le
  have hc : 0 < (t - s) * (ρ : ℝ) := mul_pos (sub_pos.2 hst) (by exact_mod_cast hρ)
  have hexp : Tendsto (fun L : ℕ ↦ -(t - s) * ((ρ : ℝ) * L)) atTop atBot := by
    have := tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
      (show -((t - s) * (ρ : ℝ)) < 0 by linarith)
    simpa only [neg_mul, mul_assoc] using this
  have hlim : Tendsto (fun L : ℕ ↦ (2 : ℝ≥0∞) ^ (-(t - s) * ((ρ : ℝ) * L)) *
      lowerBSMassLimit T u Z s r) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const
      ((ENNReal.tendsto_rpow_atBot_of_one_lt_base (b := (2 : ℝ≥0∞))
        (by norm_num)).comp hexp) (Or.inr hmass.ne)
    simpa only [Function.comp_apply, zero_mul] using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop N,
    eventually_ge_atTop 1] with L hKL hNL hL
  exact (lowerBSMass_mono_cutoff T u _ t r hKL).trans
    ((lowerBSMass_positiveAveragePiece_le T u Z hNL hρ hs hst r).trans
      (mul_le_mul' le_rfl (le_iSup₂_of_le L hL le_rfl)))

omit [MetricSpace X] in
/-- A set exhausted by a family indexed by positive integers and positive rationals is
covered by a sequence of members of the family with positive rational parameter. -/
private lemma exists_seq_subset_iUnion_of_eq_iUnion {Z : Set X} {S : ℕ → ℚ → Set X}
    (h : Z = ⋃ N : ℕ, ⋃ (_ : 1 ≤ N), ⋃ ρ : ℚ, ⋃ (_ : 0 < ρ), S N ρ) :
    ∃ (f : ℕ → ℕ) (g : ℕ → ℚ), (∀ j, 0 < g j) ∧ Z ⊆ ⋃ j, S (f j) (g j) := by
  let I := {p : ℕ × ℚ // 1 ≤ p.1 ∧ 0 < p.2}
  have : Nonempty I := ⟨⟨(1, 1), by norm_num⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat I
  refine ⟨fun j ↦ (e j).1.1, fun j ↦ (e j).1.2, fun j ↦ (e j).2.2, fun x hx ↦ ?_⟩
  rw [h] at hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨N, hN, ρ, hρ, hx⟩ := hx
  obtain ⟨j, hj⟩ := he ⟨(N, ρ), hN, hρ⟩
  exact ⟨j, by rw [hj]; exact hx⟩

/-- Finite lower mass becomes zero after a strict exponent increase on the positive locus.
Blueprint node `bs:lower-dichotomy`. -/
theorem lowerBSDichotomy (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s t r : ℝ)
    (hs : 0 ≤ s) (hst : s < t) (hr : 0 < r)
    (hmass : lowerBSMassLimit T u Z s r < ⊤) :
    lowerBSMassLimit T u Z t r = 0 := by
  obtain ⟨f, g, hg, hcover⟩ :=
    exists_seq_subset_iUnion_of_eq_iUnion (positiveAverageExhaustion P T hT u hu Z hZ)
  refine le_antisymm ?_ bot_le
  calc lowerBSMassLimit T u Z t r
      ≤ lowerBSMassLimit T u (⋃ j, positiveAveragePiece T u Z (f j) (g j)) t r :=
        lowerBSMassLimit_mono T u t r hcover
    _ ≤ ∑' j, lowerBSMassLimit T u (positiveAveragePiece T u Z (f j) (g j)) t r :=
        lowerBSMassCountableSubadditive_limit P T hT u hu _ t r (hs.trans hst.le) hr
    _ = 0 := by
        simp only [lowerBSMassLimit_positiveAveragePiece_eq_zero T u Z _ (hg _) hs hst r hmass,
          tsum_zero]

/-- Below the nonnegative critical parameter the lower mass is infinite.
Blueprint node `bs:lower-dichotomy`. -/
theorem lowerBSDichotomy_top (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s r : ℝ)
    (hs : 0 ≤ s) (hr : 0 < r) (hbelow : ENNReal.ofReal s < lowerBSDimensionAt T u Z r) :
    lowerBSMassLimit T u Z s r = ⊤ := by
  by_contra h_not_top
  obtain ⟨t, ht0, hst, htd⟩ := ENNReal.lt_iff_exists_real_btwn.1 hbelow
  have hst' : s < t := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).1 hst
  have hzero : lowerBSMassLimit T u Z t r = 0 :=
    lowerBSDichotomy P T hT u hu Z hZ s t r hs hst' hr (lt_top_iff_ne_top.2 h_not_top)
  exact htd.not_ge ((iInf₂_le t ht0).trans (iInf_le _ hzero))

/-- Above the nonnegative critical parameter the lower mass vanishes.
The hypothesis `hs` is not needed by the argument.
Blueprint node `bs:lower-dichotomy`. -/
theorem lowerBSDichotomy_zero (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s r : ℝ)
    (hs : 0 ≤ s) (hr : 0 < r) (habove : lowerBSDimensionAt T u Z r < ENNReal.ofReal s) :
    lowerBSMassLimit T u Z s r = 0 := by
  have _ := hs
  unfold lowerBSDimensionAt at habove
  simp only [iInf_lt_iff] at habove
  obtain ⟨s', hs', hmass, hlt⟩ := habove
  have hlt' : s' < s := by
    by_contra h
    exact (hlt.trans_le (ENNReal.ofReal_le_ofReal (not_lt.1 h))).false
  exact lowerBSDichotomy P T hT u hu Z hZ s' s r hs' hlt' hr (hmass ▸ ENNReal.zero_lt_top)

/-! ### Recentering -/

/-- If the supremum of the Birkhoff sums over a Bowen ball is the real number `w`, some point
of the ball has Birkhoff sum above `w - a / 2`. -/
private lemma exists_mem_bowenBall_lt_birkhoffSum (T : X → X) (u : X → ℝ) (n : ℕ) (y : X)
    (r w : ℝ) (hw : bowenPotentialSup T u n y r = (w : EReal)) {a : ℝ} (ha : 0 < a) :
    ∃ z ∈ bowenBall T n y r, w - a / 2 < birkhoffSum T u n z := by
  have h : ((w - a / 2 : ℝ) : EReal) < bowenPotentialSup T u n y r := by
    rw [hw, EReal.coe_lt_coe_iff]
    linarith
  unfold bowenPotentialSup at h
  simp_rw [lt_iSup_iff] at h
  obtain ⟨z, hz, hlt⟩ := h
  exact ⟨z, hz, EReal.coe_lt_coe_iff.1 hlt⟩

/-- Finite Birkhoff sums of a uniformly continuous potential are continuous for continuous
dynamics. -/
private lemma continuous_birkhoffSum (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (hu : UniformContinuous u) (n : ℕ) : Continuous (birkhoffSum T u n) :=
  continuous_finsetSum _ fun i _ ↦ hu.continuous.comp (hT.iterate i)

/-- A Bowen ball is contained in the Bowen ball of twice the radius around any of its
points. -/
private lemma bowenBall_subset_bowenBall_two_mul (T : X → X) (n : ℕ) {y z : X} {r : ℝ}
    (hz : z ∈ bowenBall T n y r) : bowenBall T n y r ⊆ bowenBall T n z (2 * r) := by
  intro x hx
  unfold bowenBall at hz hx ⊢
  simp only [Set.mem_ofPred_eq, Dynamics.mem_dynEntourage] at hz hx ⊢
  intro k hk
  have hd := dist_triangle (T^[k] z) (T^[k] y) (T^[k] x)
  rw [dist_comm (T^[k] z) (T^[k] y)] at hd
  linarith [hz k hk, hx k hk]

/-- If `W` is the (finite) supremum of the Birkhoff sums over a Bowen ball, an ideal point of
the ball has Birkhoff sum above `W - a`, and the doubled Bowen ball around it contains the
original ball.  The hypothesis `hn` is not needed by the argument.
Blueprint node `bs:recenter`. -/
theorem recenterNearBirkhoffSupremum (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (n : ℕ) (hn : 1 ≤ n)
    (y : X) (r : ℝ) (hr : 0 < r) (w : ℝ)
    (hw : bowenPotentialSup T u n y r = (w : EReal)) (a : ℝ) (ha : 0 < a) :
    ∃ i, P.ι i ∈ bowenBall T n y r ∧ w - a < birkhoffSum T u n (P.ι i) ∧
      bowenBall T n y r ⊆ bowenBall T n (P.ι i) (2 * r) := by
  have _ := And.intro hn hr
  obtain ⟨z, hz, hz'⟩ := exists_mem_bowenBall_lt_birkhoffSum T u n y r w hw ha
  have hopen : IsOpen (bowenBall T n y r ∩ {x | w - a < birkhoffSum T u n x}) :=
    (bowen_ball_dense_open T hT n y r).inter
      (isOpen_lt continuous_const (continuous_birkhoffSum T hT u hu n))
  obtain ⟨i, hi⟩ := P.dense.exists_mem_open hopen
    ⟨z, hz, lt_trans (by linarith : w - a < w - a / 2) hz'⟩
  exact ⟨i, hi.1, hi.2, bowenBall_subset_bowenBall_two_mul T n hi.1⟩

end Kolmogorov.PointToSet
