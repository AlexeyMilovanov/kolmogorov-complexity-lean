/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyZeroPotential

/-!
# Entropy characterization for the lower pressure

This module proves two statements about the lower entropy of a set `Z`, the nonnegative
critical value of the zero-potential Bowen content.

* `bowenEntropy_eq_lowerPressure_zero` (blueprint node `pressure:entropy-content`): the
  entropy defined through the residence time `n_r(U)` of open sets, with cost
  `2 ^ (-n_r(U))`, equals `lowerEntropy`. One inequality covers `Z` by the open Bowen balls of
  radius `r / 2`, whose images under the first `n` iterates have diameter at most `r`; the
  other turns an open cover into a Bowen cover of radius `2 * r`, charging the sets of
  infinite residence time an arbitrarily small extra cost. The nonempty case is then
  identified with the signed zero-potential lower pressure.
* `entropy_effectiveCharacterization_allOracles` (blueprint node `pressure:entropy-pts`): for
  every oracle `A` and without any admissibility hypothesis, the effective lower entropy
  relative to `A` is the supremum of the lower orbit complexities of the points of `Z`.
  The inequality `≤` enumerates the triples whose oracle complexity is below `s * n` and
  bounds their total mass by Kraft's inequality; the inequality `≥` codes a recursively
  enumerable null cover with relative Kraft–Chaitin coding.

The second theorem is the lower-entropy half of the point-to-set principle assembled in
`KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- A finite order `n` is at most the residence time of `U` exactly when the images of `U`
under the first `n` iterates have diameter at most `r`. -/
private lemma natCast_le_residenceTime_iff (T : X → X) (r : ℝ)
    (U : Set X) (n : ℕ) :
    (n : ENat) ≤ residenceTime T r U ↔
      ∀ j < n, Metric.ediam (T^[j] '' U) ≤ ENNReal.ofReal r := by
  constructor
  · intro hn j hj
    by_contra hdiam
    have hb : residenceTime T r U ≤ (j : ENat) := by
      unfold residenceTime
      refine iSup_le fun k => iSup_le fun hk => ?_
      exact_mod_cast (show k ≤ j from by
        by_contra hkj
        exact hdiam (hk j (by omega)))
    exact (not_le_of_gt (ENat.natCast_lt_natCast.mpr hj)) (hn.trans hb)
  · intro hn
    exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

/-- Residence sizes are at most one, so increasing the exponent decreases every cover cost. -/
private lemma residenceSize_le_one (T : X → X) (r : ℝ) (U : Set X) :
    residenceSize T r U ≤ 1 := by
  unfold residenceSize
  split_ifs
  · exact zero_le
  · calc
      (2 : ℝ≥0∞) ^ (-(residenceTime T r U).toNat : ℝ) ≤ (2 : ℝ≥0∞) ^ (0 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = 1 := ENNReal.rpow_zero

/-- The explicit convention `0 ^ 0 = 1` for the exponent zero agrees with the extended
nonnegative real power. -/
private lemma ite_exponent_zero_eq_rpow (a : ℝ≥0∞) (s : ℝ) :
    (if s = 0 then 1 else a ^ s) = a ^ s := by
  split_ifs with h
  · simp [h]
  · rfl

/-- The residence content limit is antitone in the exponent, including exponent zero. -/
private lemma antitone_residenceContentLimit (T : X → X) (Z : Set X) (r : ℝ) :
    Antitone (fun s : ℝ => ⨆ δ : ℝ≥0∞, ⨆ (_ : 0 < δ), residenceContent T Z s r δ) := by
  intro s t hst
  refine iSup_mono fun δ => iSup_mono fun _ => ?_
  unfold residenceContent
  refine iInf_mono fun J => iInf_mono fun U => iInf_mono fun _ => ?_
  apply ENNReal.tsum_le_tsum
  intro j
  simp only [ite_exponent_zero_eq_rpow]
  exact ENNReal.rpow_le_rpow_of_exponent_ge (residenceSize_le_one T r (U j)) hst

/-- The zero-potential Bowen content limit is antitone in the exponent. -/
private lemma antitone_lowerContentLimit_zero_potential (T : X → X) (Z : Set X) (r : ℝ) :
    Antitone (fun s : ℝ => lowerContentLimit T (fun _ => 0) .centered Z s r) := by
  intro s t hst
  unfold lowerContentLimit
  refine iSup_mono fun N => iSup_mono fun _ => ?_
  unfold lowerContent
  refine iInf_mono fun C => iInf_mono fun _ => ?_
  unfold bowenCoverCost
  apply ENNReal.tsum_le_tsum
  intro j
  apply mul_le_mul_left
  exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    (by nlinarith [(Nat.cast_nonneg (C.order j) : (0 : ℝ) ≤ _)])

/-- For a positive exponent `s`, the costs `2 ^ (-s * n)` become arbitrarily small along
orders `n` that stay above any prescribed cutoff. -/
private lemma exists_large_order_two_rpow_le
    (s : ℝ) (hs : 0 < s) (ε : ℝ≥0∞) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, max 1 N ≤ n ∧ (2 : ℝ≥0∞) ^ (-s * n) ≤ ε := by
  have hb : (2 : ℝ≥0∞) ^ (-s) < 1 := by
    calc
      (2 : ℝ≥0∞) ^ (-s) < (2 : ℝ≥0∞) ^ (0 : ℝ) :=
        ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) (by linarith)
      _ = 1 := ENNReal.rpow_zero
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb
  have he : ∀ᶠ n : ℕ in atTop, ((2 : ℝ≥0∞) ^ (-s)) ^ n < ε :=
    ht.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn, hne⟩ := (eventually_ge_atTop (max 1 N)).and he |>.exists
  refine ⟨n, hn, ?_⟩
  simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] using hne.le

/-- A dyadic size cutoff `2⁻ⁿ` on the residence size is equivalent to the lower bound `n`
on the residence time. -/
private lemma residenceSize_le_two_rpow_neg_iff (T : X → X) (r : ℝ)
    (U : Set X) (n : ℕ) :
    residenceSize T r U ≤ (2 : ℝ≥0∞) ^ (-(n : ℝ)) ↔
      (n : ENat) ≤ residenceTime T r U := by
  by_cases ht : residenceTime T r U = ⊤
  · simp [residenceSize, ht]
  have hm : StrictMono (fun a : ℝ => (2 : ℝ≥0∞) ^ a) :=
    fun a b hab => ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) hab
  rw [residenceSize, ite_eq_right ht, hm.le_iff_le, neg_le_neg_iff]
  have hc := ENat.natCast_toNat ht
  constructor
  · intro h
    exact (ENat.natCast_le_natCast.mpr (by exact_mod_cast h)).trans_eq hc
  · intro h
    have hn : (n : ENat) ≤ ((residenceTime T r U).toNat : ENat) := by rwa [hc]
    exact_mod_cast ENat.natCast_le_natCast.mp hn

/-- For continuous `T`, each Bowen ball of radius `r / 2` is open and has residence size at
most `2⁻ⁿ` at scale `r`. -/
private lemma isOpen_bowenBall_and_residenceSize_le
    (T : X → X) (hT : Continuous T) (r : ℝ) (n : ℕ) (y : X) :
    IsOpen (bowenBall T n y (r / 2)) ∧
      residenceSize T r (bowenBall T n y (r / 2)) ≤ (2 : ℝ≥0∞) ^ (-(n : ℝ)) := by
  constructor
  · have ho : IsOpen {z : X × X | dist z.1 z.2 < r / 2} :=
      isOpen_lt continuous_dist continuous_const
    exact (isOpen.dynEntourage hT ho n).preimage (Continuous.prodMk_right y)
  · rw [residenceSize_le_two_rpow_neg_iff, natCast_le_residenceTime_iff]
    intro j hj
    rw [Metric.ediam_image_le_iff]
    intro a ha b hb
    simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at ha hb
    have ha' : dist (T^[j] y) (T^[j] a) < r / 2 := ha j hj
    have hb' : dist (T^[j] y) (T^[j] b) < r / 2 := hb j hj
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have htri := dist_triangle (T^[j] a) (T^[j] y) (T^[j] b)
    rw [dist_comm (T^[j] a) (T^[j] y)] at htri
    linarith

/-- Continuous Bowen balls of radius `r / 2` turn every large-order cover into an open cover
of residence size at most `2⁻ᴺ`, with no increase in cost for a nonnegative exponent. -/
private lemma residenceContent_le_lowerContent
    (T : X → X) (hT : Continuous T) (Z : Set X) (s r : ℝ)
    (δ : ℝ≥0∞) (N : ℕ)
    (hδ : (2 : ℝ≥0∞) ^ (-(N : ℝ)) ≤ δ) (hs : 0 ≤ s) :
    residenceContent T Z s r δ ≤
      lowerContent T (fun _ => 0) .centered Z s (r / 2) N := by
  unfold lowerContent
  refine le_iInf fun C => le_iInf fun hC => ?_
  let U : C.index → Set X := fun j => bowenBall T (C.order j) (C.center j) (r / 2)
  have hU : (∀ j, IsOpen (U j) ∧ residenceSize T r (U j) ≤ δ) ∧
      Z ⊆ ⋃ j, U j := by
    refine ⟨fun j => ?_, hC.2⟩
    have hb := isOpen_bowenBall_and_residenceSize_le T hT r (C.order j) (C.center j)
    refine ⟨hb.1, hb.2.trans ?_⟩
    apply le_trans _ hδ
    apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    have hn : N ≤ C.order j := (le_max_right 1 N).trans (hC.1 j)
    exact neg_le_neg (by exact_mod_cast hn)
  calc
    residenceContent T Z s r δ ≤
        ∑' j, if s = 0 then 1 else residenceSize T r (U j) ^ s :=
      iInf_le_of_le C.index (iInf_le_of_le U (iInf_le_of_le hU le_rfl))
    _ ≤ bowenCoverCost T (fun _ => 0) .centered s (r / 2) C := by
      unfold bowenCoverCost
      apply ENNReal.tsum_le_tsum
      intro j
      simp only [ite_exponent_zero_eq_rpow,
        pressureBallWeight, birkhoffSum, Finset.sum_const_zero, ENNReal.rpow_zero, mul_one]
      calc
        residenceSize T r (U j) ^ s ≤ ((2 : ℝ≥0∞) ^ (-(C.order j : ℝ))) ^ s :=
          ENNReal.rpow_le_rpow
            (isOpen_bowenBall_and_residenceSize_le T hT r _ _).2 hs
        _ = (2 : ℝ≥0∞) ^ (-s * C.order j) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring

/-- A set with residence time at least `n` lies in the radius-`2 * r` Bowen ball of order `n`
about each of its points. -/
private lemma subset_bowenBall_of_le_residenceTime
    (T : X → X) (r : ℝ) (hr : 0 < r) (U : Set X) (y : X) (hy : y ∈ U)
    (n : ℕ) (hn : (n : ENat) ≤ residenceTime T r U) :
    U ⊆ bowenBall T n y (2 * r) := by
  intro z hz
  simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq]
  intro j hj
  have hd := (natCast_le_residenceTime_iff T r U n).mp hn j hj
  have he := Metric.edist_le_ediam_of_mem
    (Set.mem_image_of_mem (T^[j]) hy) (Set.mem_image_of_mem (T^[j]) hz)
  have hdist : dist (T^[j] y) (T^[j] z) ≤ r := (edist_le_ofReal hr.le).mp (he.trans hd)
  linarith

/-- A countable open cover of residence size at most `2⁻ᴺ` converts to a Bowen cover at
radius `2 * r` and order cutoff `N`, for a positive exponent. Sets of infinite residence time
are assigned finite orders with an arbitrarily small positive total extra cost `η`. -/
private lemma lowerContent_le_residenceContent_add
    (x₀ : X) (T : X → X) (Z : Set X) (s r : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (η : ℝ≥0∞) (hη : 0 < η) (hs : 0 < s) (hr : 0 < r) :
    lowerContent T (fun _ => 0) .centered Z s (2 * r) N ≤
      residenceContent T Z s r ((2 : ℝ≥0∞) ^ (-(N : ℝ))) + η := by
  classical
  unfold residenceContent
  simp only [ENNReal.iInf_add]
  refine le_iInf fun J => le_iInf fun U => le_iInf fun hU => ?_
  let ε : J → ℝ≥0∞ := fun j => η * (2⁻¹ : ℝ≥0∞) ^ ((j : ℕ) + 1)
  have hε : ∀ j, 0 < ε j := by
    intro j
    dsimp [ε]
    exact ENNReal.mul_pos hη.ne' (pow_ne_zero _ (by simp))
  -- Each set is replaced by a Bowen ball of finite order, using the fallback point `x₀`
  -- only for the empty set.
  have hex : ∀ j : J, ∃ y : X, ∃ n : ℕ,
      max 1 N ≤ n ∧ U j ⊆ bowenBall T n y (2 * r) ∧
        (2 : ℝ≥0∞) ^ (-s * n) ≤ residenceSize T r (U j) ^ s + ε j := by
    intro j
    by_cases hne : (U j).Nonempty
    · obtain ⟨y, hy⟩ := hne
      by_cases ht : residenceTime T r (U j) = ⊤
      · obtain ⟨n, hn, hc⟩ := exists_large_order_two_rpow_le s hs (ε j) (hε j) N
        refine ⟨y, n, hn, ?_, hc.trans (le_add_of_nonneg_left zero_le)⟩
        apply subset_bowenBall_of_le_residenceTime T r hr (U j) y hy n
        rw [ht]
        exact le_top
      · let n := (residenceTime T r (U j)).toNat
        have he : (n : ENat) = residenceTime T r (U j) := ENat.natCast_toNat ht
        have hn : N ≤ n := by
          have h := (residenceSize_le_two_rpow_neg_iff T r (U j) N).mp (hU.1 j).2
          rw [← he] at h
          exact_mod_cast h
        refine ⟨y, n, max_le (hN.trans hn) hn,
          subset_bowenBall_of_le_residenceTime T r hr (U j) y hy n he.le, ?_⟩
        have hc : (2 : ℝ≥0∞) ^ (-s * n) = residenceSize T r (U j) ^ s := by
          rw [residenceSize, ite_eq_right ht, ← ENNReal.rpow_mul]
          congr 1
          dsimp [n]
          ring
        rw [hc]
        exact le_self_add
    · obtain ⟨n, hn, hc⟩ := exists_large_order_two_rpow_le s hs (ε j) (hε j) N
      refine ⟨x₀, n, hn, ?_, hc.trans (le_add_of_nonneg_left zero_le)⟩
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.empty_subset _
  choose y n hn hsub hc using hex
  let C : BowenCoverFamily X := ⟨J, y, n⟩
  have hC : IsBowenCover T Z (2 * r) N C := by
    refine ⟨hn, ?_⟩
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hU.2 hz)
    exact Set.mem_iUnion.mpr ⟨j, hsub j hj⟩
  have hbudget : ∑' j : J, ε j ≤ η := by
    calc
      ∑' j : J, ε j ≤ ∑' k : ℕ, η * (2⁻¹ : ℝ≥0∞) ^ (k + 1) :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun j : J => (j : ℕ)) Subtype.val_injective
          (fun k : ℕ => η * (2⁻¹ : ℝ≥0∞) ^ (k + 1))
      _ = η := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
        norm_num
        rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  calc
    lowerContent T (fun _ => 0) .centered Z s (2 * r) N ≤
        bowenCoverCost T (fun _ => 0) .centered s (2 * r) C :=
      iInf_le_of_le C (iInf_le_of_le hC le_rfl)
    _ ≤ ∑' j : J, (residenceSize T r (U j) ^ s + ε j) := by
      unfold bowenCoverCost
      simp only [pressureBallWeight, birkhoffSum, Finset.sum_const_zero,
        ENNReal.rpow_zero, mul_one]
      exact ENNReal.tsum_le_tsum hc
    _ = (∑' j : J, if s = 0 then 1 else residenceSize T r (U j) ^ s) + ∑' j : J, ε j := by
      simp only [ite_exponent_zero_eq_rpow, ENNReal.tsum_add]
    _ ≤ (∑' j : J, if s = 0 then 1 else residenceSize T r (U j) ^ s) + η :=
      add_le_add le_rfl hbudget

/-- Vanishing Bowen content at radius `r / 2` implies vanishing residence content at
radius `r`. -/
private lemma residenceContentLimit_eq_zero_of_lowerContentLimit_eq_zero
    (T : X → X) (hT : Continuous T) (Z : Set X) (s r : ℝ) (hs : 0 < s)
    (h : lowerContentLimit T (fun _ => 0) .centered Z s (r / 2) = 0) :
    (⨆ δ : ℝ≥0∞, ⨆ (_ : 0 < δ), residenceContent T Z s r δ) = 0 := by
  apply le_antisymm _ zero_le
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  obtain ⟨N, hN, hNd⟩ := exists_large_order_two_rpow_le 1 zero_lt_one δ hδ 1
  have hN' : 1 ≤ N := by simpa using hN
  have hc := residenceContent_le_lowerContent T hT Z s r δ N (by simpa using hNd) hs.le
  apply hc.trans
  rw [← h]
  exact le_iSup_of_le N (le_iSup_of_le hN' le_rfl)

/-- Vanishing residence content implies vanishing Bowen content at doubled radius for a
positive exponent, by letting the extra cost of infinite-residence sets tend to zero. -/
private lemma lowerContentLimit_eq_zero_of_residenceContentLimit_eq_zero
    (x₀ : X) (T : X → X) (Z : Set X) (s r : ℝ) (hs : 0 < s) (hr : 0 < r)
    (h : (⨆ δ : ℝ≥0∞, ⨆ (_ : 0 < δ), residenceContent T Z s r δ) = 0) :
    lowerContentLimit T (fun _ => 0) .centered Z s (2 * r) = 0 := by
  apply le_antisymm _ zero_le
  unfold lowerContentLimit
  refine iSup_le fun N => iSup_le fun hN => ?_
  have hδ : 0 < (2 : ℝ≥0∞) ^ (-(N : ℝ)) := by positivity
  have hz : residenceContent T Z s r ((2 : ℝ≥0∞) ^ (-(N : ℝ))) = 0 := by
    apply le_antisymm _ zero_le
    rw [← h]
    exact le_iSup_of_le ((2 : ℝ≥0∞) ^ (-(N : ℝ))) (le_iSup_of_le hδ le_rfl)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  simpa only [hz, zero_add] using
    lowerContent_le_residenceContent_add x₀ T Z s r N hN ε (by exact_mod_cast hε) hs hr

/-- An implication between positive-exponent zero sets compares their nonnegative critical
infima, provided the source content is antitone. This includes the critical value zero. -/
private lemma criticalValue_le_of_zero_set_implication
    (f g : ℝ → ℝ≥0∞) (hf : Antitone f)
    (hfg : ∀ s : ℝ, 0 < s → f s = 0 → g s = 0) :
    (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : g s = 0), ENNReal.ofReal s) ≤
      ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : f s = 0), ENNReal.ofReal s := by
  refine le_iInf fun s => le_iInf fun hs => le_iInf fun hfs => ?_
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have ht : 0 < s + (ε : ℝ) := add_pos_of_nonneg_of_pos hs hε
  have hft : f (s + ε) = 0 :=
    le_antisymm ((hf (le_add_of_nonneg_right ε.coe_nonneg)).trans_eq hfs) zero_le
  have hgt := hfg (s + ε) ht hft
  calc
    (⨅ t : ℝ, ⨅ (_ : 0 ≤ t), ⨅ (_ : g t = 0), ENNReal.ofReal t) ≤
        ENNReal.ofReal (s + ε) := iInf_le_of_le (s + ε)
          (iInf_le_of_le ht.le (iInf_le_of_le hgt le_rfl))
    _ = ENNReal.ofReal s + ε := by rw [ENNReal.ofReal_add hs ε.coe_nonneg]; simp

/-- The open-set residence-time construction agrees with lower entropy, also on empty sets.
Blueprint node `pressure:entropy-content`. -/
theorem bowenEntropy_eq_lowerPressure_zero (P : Presentation X) (T : X → X)
    (hT : Continuous T) (Z : Set X) : residenceEntropy T Z = lowerEntropy T Z := by
  apply le_antisymm
  · unfold residenceEntropy lowerEntropy
    apply iSup_le
    intro p
    apply le_trans ?_ (le_iSup _ (p + 1))
    have he : dyadicRadius (p + 1) = dyadicRadius p / 2 := by
      unfold dyadicRadius
      rw [pow_succ]
      ring
    rw [he]
    exact criticalValue_le_of_zero_set_implication _ _
      (antitone_lowerContentLimit_zero_potential T Z _)
      (fun s hs h ↦ residenceContentLimit_eq_zero_of_lowerContentLimit_eq_zero T hT Z s _ hs h)
  · unfold residenceEntropy lowerEntropy
    apply iSup_le
    intro p
    apply le_trans ?_ (le_iSup _ (p + 1))
    have hr : 0 < dyadicRadius (p + 1) := by unfold dyadicRadius; positivity
    have he : dyadicRadius p = 2 * dyadicRadius (p + 1) := by
      unfold dyadicRadius
      rw [pow_succ]
      ring
    rw [he]
    exact criticalValue_le_of_zero_set_implication _ _
      (antitone_residenceContentLimit T Z _)
      (fun s hs h ↦
        lowerContentLimit_eq_zero_of_residenceContentLimit_eq_zero (P.ι 0) T Z s _ hs hr h)

/-- On nonempty sets residence entropy embeds as the signed zero-potential lower pressure.
Blueprint node `pressure:entropy-content`. -/
theorem bowenEntropy_eq_lowerPressure_zero_nonempty (P : Presentation X) (T : X → X)
    (hT : Continuous T) (Z : Set X) (hZ : Z.Nonempty) :
    (residenceEntropy T Z : EReal) = lowerPressure T (fun _ => 0) 0 Z := by
  rw [bowenEntropy_eq_lowerPressure_zero P T hT Z]
  rw [entropy_eq_zeroPotentialPressure_of_nonempty T Z hZ]

/-- Rational linear costs `t * n` on an enumerable domain of pair codes `(i, n)` are upper
semicomputable relative to every oracle. -/
private lemma isUpperSemicomputableOnIn_ratMul_decodeBits
    (A : Set ℕ) (t : ℚ) (F : BitString → Prop) (hF : IsREIn A F) :
    IsUpperSemicomputableOnIn A F
      (fun w => (t : ℝ) * decodeBits (decodeSecond w.val)) := by
  let J : BitString → ℕ := fun w => decodeBits (decodeSecond w)
  let g : BitString → ℝ := fun w => (t : ℝ) * J w
  have hJ : Computable J :=
    (primrec_decodeBits.comp CodedFiniteDistribution.decodeSecond_primrec).to_comp
  have hg : IsComputableRealFamilyIn A g := by
    refine ⟨fun wp => t * (J wp.1 : ℚ), ?_, ?_⟩
    · exact (computable₂_ratMul.comp (Computable.const t)
        (computable_nat_to_rat.comp (hJ.comp Computable.fst))).computableIn
    · intro w m
      simp only [g, Rat.cast_mul, Rat.cast_natCast, sub_self, abs_zero]
      positivity
  have hcut := birkhoff_computableIn_lt A g hg
  have hdom : IsREIn A (fun wq : BitString × ℚ => F wq.1) := by
    obtain ⟨f, hf, hfd⟩ := hF
    exact ⟨fun wq => f wq.1, hf.comp ComputableIn.fst, fun wq => hfd wq.1⟩
  refine ⟨fun wq => F wq.1 ∧ g wq.1 < (wq.2 : ℝ),
    IsREIn.and hdom hcut, ?_, ?_⟩
  · intro w q h
    exact ⟨h.1, h.2⟩
  · intro w ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g w.val) hε)
    exact ⟨q, ⟨w.property, hq1⟩, hq2⟩

/-- An enumerable set of triples `(i, n, p)` with finite mass at exponent `a` has oracle
complexity of `i` at most `t * n + c` for every rational `t ≥ a`. Choosing one triple for each
pair code `(i, n)` injects the projected pair domain into the original finite-mass set. -/
private lemma oracleNatComplexity_le_of_finiteMass_cover
    (P : Presentation X) (T : X → X) (A : Set ℕ) (a : ℝ)
    (E : Set (ℕ × ℕ × ℕ))
    (hmass : nullPressureMass P T (fun _ => 0) a E < ⊤)
    (hRE : IsREIn A E) (t : ℚ) (ht : a ≤ (t : ℝ)) :
    ∃ c : ℕ, ∀ z ∈ E,
      (oracleNatComplexity A z.1 : ℝ) ≤ (t : ℝ) * z.2.1 + c := by
  classical
  let F : BitString → Prop := fun w => ∃ i n p : ℕ,
    w = pairCode (natBits i) (natBits n) ∧ (i, n, p) ∈ E
  let g : BitString → ℝ := fun w => (t : ℝ) * decodeBits (decodeSecond w)
  have hF : IsREIn A F :=
    isREIn_pairCode_image A E hRE
  have hg : IsUpperSemicomputableOnIn A F (fun w => g w.val) :=
    isUpperSemicomputableOnIn_ratMul_decodeBits A t F hF
  have hgeval (i n : ℕ) : g (pairCode (natBits i) (natBits n)) = (t : ℝ) * n := by
    simp only [g, decodeSecond_pairCode, natBits, decodeBits_natBits]
  choose i n p hw he using (fun w : Subtype F => w.property)
  let f : Subtype F → E := fun w => ⟨(i w, n w, p w), he w⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hi : i u = i v := congrArg (fun z : E => z.val.1) huv
    have hn : n u = n v := congrArg (fun z : E => z.val.2.1) huv
    apply Subtype.ext
    rw [hw u, hw v, hi, hn]
  have hterm (w : Subtype F) : (2 : ℝ≥0∞) ^ (-g w.val) ≤
      (2 : ℝ≥0∞) ^ (-a * (f w).val.2.1) := by
    rw [hw w, hgeval]
    dsimp only [f]
    apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    have hn : (0 : ℝ) ≤ n w := Nat.cast_nonneg _
    nlinarith
  have hbound : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) ≤
      nullPressureMass P T (fun _ => 0) a E := by
    calc
      (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) ≤
          ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-a * (f w).val.2.1) :=
        ENNReal.tsum_le_tsum hterm
      _ ≤ ∑' z : E, (2 : ℝ≥0∞) ^ (-a * z.val.2.1) :=
        ENNReal.tsum_comp_le_tsum_of_injective hf
          (fun z : E => (2 : ℝ≥0∞) ^ (-a * z.val.2.1))
      _ = nullPressureMass P T (fun _ => 0) a E := by
        simp only [nullPressureMass, birkhoffSum, Finset.sum_const_zero, add_zero]
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F (fun w => g w.val) hg
    (nullPressureMass P T (fun _ => 0) a E) hbound hmass
  obtain ⟨d, hd⟩ := oracle_tuple_bounds A
  refine ⟨c + d, ?_⟩
  intro z hz
  have hzF : F (pairCode (natBits z.1) (natBits z.2.1)) :=
    ⟨z.1, z.2.1, z.2.2, rfl, hz⟩
  have hcode := hc ⟨pairCode (natBits z.1) (natBits z.2.1), hzF⟩
  change (oracleComplexity A (pairCode (natBits z.1) (natBits z.2.1)) : ℝ) ≤
    g (pairCode (natBits z.1) (natBits z.2.1)) + c at hcode
  rw [hgeval] at hcode
  have hproj : (oracleNatComplexity A z.1 : ℝ) ≤
      (oracleComplexity A (pairCode (natBits z.1) (natBits z.2.1)) : ℝ) + d := by
    exact_mod_cast hd z.1 z.2.1
  push_cast
  linarith

/-- If a point is covered at arbitrarily large orders by Bowen balls around ideal points
whose oracle complexity is at most `t * n + c`, then at that scale its liminf of the
potential-one finite-scale costs is at most `t`. Symmetry of the Bowen ball and the coding
bound give a frequent upper bound by `t + c / n`, whose limit is `t`. -/
private lemma liminf_finiteScaleBSCost_le_of_coded_cover
    (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X) (p : ℕ)
    (t : ℝ) (c : ℕ) (E : Set (ℕ × ℕ × ℕ))
    (hcode : ∀ z ∈ E, (oracleNatComplexity A z.1 : ℝ) ≤ t * z.2.1 + c)
    (hcover : ∀ N ≥ 1, ∃ i n, N ≤ n ∧ (i, n, p) ∈ E ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p)) :
    liminf (fun n => finiteScaleBSCost P T (fun _ => 1) A x n (dyadicRadius p))
      atTop ≤ ENNReal.ofReal t := by
  have hcov : ∃ᶠ n in atTop, 1 ≤ n ∧ ∃ i, (i, n, p) ∈ E ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨i, n, hn, hi, hx⟩ := hcover (max 1 N) (le_max_left 1 N)
    exact ⟨n, (le_max_right 1 N).trans hn, (le_max_left 1 N).trans hn, i, hi, hx⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (t + (c : ℝ) / n))
      atTop (𝓝 (ENNReal.ofReal t)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using
      (tendsto_const_nhds (x := t)).add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  have hfreq : ∃ᶠ n in atTop,
      finiteScaleBSCost P T (fun _ => 1) A x n (dyadicRadius p) ≤
        ENNReal.ofReal (t + (c : ℝ) / n) := by
    apply hcov.mono
    rintro n ⟨hn, i, hi, hx⟩
    have hn0 : n ≠ 0 := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsymm : P.ι i ∈ bowenBall T n x (dyadicRadius p) := by
      simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at hx ⊢
      intro k hk
      rw [dist_comm]
      exact hx k hk
    have hcost : finiteScaleBSCost P T (fun _ => 1) A x n (dyadicRadius p) ≤
        (oracleNatComplexity A i : ℝ≥0∞) / n := by
      rw [finiteScaleBSCost, ite_eq_right hn0]
      apply iInf_le_of_le i
      apply iInf_le_of_le hsymm
      have hsum : birkhoffSum T (fun _ => (1 : ℝ)) n (P.ι i) = n := by
        simp [birkhoffSum]
      rw [hsum]
      exact iInf_le_of_le hnR (by rw [ENNReal.ofReal_natCast])
    have hreal : (oracleNatComplexity A i : ℝ) / n ≤ t + (c : ℝ) / n := by
      calc
        _ ≤ (t * n + c) / n :=
          div_le_div_of_nonneg_right (hcode (i, n, p) hi) hnR.le
        _ = t + (c : ℝ) / n := by rw [add_div, mul_div_cancel_right₀ _ hnR.ne']
    calc
      finiteScaleBSCost P T (fun _ => 1) A x n (dyadicRadius p) ≤
          (oracleNatComplexity A i : ℝ≥0∞) / n := hcost
      _ = ENNReal.ofReal ((oracleNatComplexity A i : ℝ) / n) := by
        rw [ENNReal.ofReal_div_of_pos hnR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (t + (c : ℝ) / n) := ENNReal.ofReal_le_ofReal hreal
  exact (liminf_le_limsup_of_frequently_le hfreq).trans_eq hlim.limsup_eq

/-- An enumerable null cover of nonnegative exponent `a` bounds the lower orbit complexity
of each covered point by `a`. -/
private theorem orbitComplexities_fst_le_of_isNullPressureCover
    (P : Presentation X) (T : X → X)
    (A : Set ℕ) (Z : Set X) (a : ℝ) (ha : 0 ≤ a)
    (E : Set (ℕ × ℕ × ℕ))
    (hE : IsNullPressureCover P T (fun _ => 0) 0 Z a E)
    (hRE : IsREIn A E) (x : X) (hx : x ∈ Z) :
    (orbitComplexities P T A x).1 ≤ ENNReal.ofReal a := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨t, hat, hta⟩ := exists_rat_btwn (lt_add_of_pos_right a hεR)
  obtain ⟨c, hc⟩ :=
    oracleNatComplexity_le_of_finiteMass_cover P T A a E hE.2.1 hRE t hat.le
  have hrate : (orbitComplexities P T A x).1 ≤ ENNReal.ofReal (t : ℝ) := by
    change (⨆ p : ℕ, liminf (fun n =>
      finiteScaleBSCost P T (fun _ => 1) A x n (dyadicRadius p)) atTop) ≤ _
    apply iSup_le
    intro p
    apply liminf_finiteScaleBSCost_le_of_coded_cover P T A x p (t : ℝ) c E hc
    intro N hN
    exact hE.2.2 p (Nat.zero_le p) N hN x hx
  calc
    (orbitComplexities P T A x).1 ≤ ENNReal.ofReal (t : ℝ) := hrate
    _ ≤ ENNReal.ofReal (a + ε) := ENNReal.ofReal_le_ofReal hta.le
    _ = ENNReal.ofReal a + ε := by
      rw [ENNReal.ofReal_add ha ε.coe_nonneg]
      simp

/-- The zero-potential triple threshold `{(i, n, p) | K^A(i, n, p) < s * n}` is enumerable
relative to every oracle, using only rational arithmetic and the enumerable strict
complexity cut. -/
private lemma isREIn_lowerPressureThreshold_zero_potential
    (P : Presentation X) (T : X → X) (A : Set ℕ) (s : ℚ) :
    IsREIn A (lowerPressureThreshold P T (fun _ => 0) 0 A s) := by
  have hE : lowerPressureThreshold P T (fun _ => 0) 0 A s =
      {t : ℕ × ℕ × ℕ | 1 ≤ t.2.1 ∧
        (oracleComplexity A (pairCode (natBits t.1)
          (pairCode (natBits t.2.1) (natBits t.2.2))) : ℝ) < (s : ℝ) * t.2.1} := by
    ext t
    simp [lowerPressureThreshold, birkhoffSum]
  rw [hE]
  have hvalid : IsREIn A (fun t : ℕ × ℕ × ℕ => 1 ≤ t.2.1) :=
    isREIn_of_computableIn_decide A _
      ((Primrec.nat_le.decide.to_comp.comp (Computable.const 1)
        (Computable.fst.comp Computable.snd)).computableIn)
  have hargs : Computable (fun t : ℕ × ℕ × ℕ =>
      (pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2)),
        s * (t.2.1 : ℚ))) :=
    computable_tripleCode.pair
      (computable₂_ratMul.comp (Computable.const s)
        (computable_nat_to_rat.comp (Computable.fst.comp Computable.snd)))
  obtain ⟨f, hf, hdom⟩ := isREIn_oracleComplexity_lt A
  have hcut : IsREIn A (fun t : ℕ × ℕ × ℕ =>
      (oracleComplexity A (pairCode (natBits t.1)
        (pairCode (natBits t.2.1) (natBits t.2.2))) : ℝ) < (s : ℝ) * t.2.1) := by
    refine ⟨fun t => f (pairCode (natBits t.1)
      (pairCode (natBits t.2.1) (natBits t.2.2)), s * (t.2.1 : ℚ)),
      hf.comp hargs.computableIn, ?_⟩
    intro t
    simpa only [Rat.cast_mul, Rat.cast_natCast] using
      hdom (pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2)),
        s * (t.2.1 : ℚ))
  exact IsREIn.and hvalid hcut

/-- Injective triple coding and the prefix-machine Kraft bound give the zero-potential
threshold total mass at most one, without any assumption on the oracle or on the
geometry. -/
private lemma nullPressureMass_lowerPressureThreshold_le_one
    (P : Presentation X) (T : X → X) (A : Set ℕ) (s : ℚ) :
    nullPressureMass P T (fun _ => 0) (s : ℝ)
      (lowerPressureThreshold P T (fun _ => 0) 0 A s) ≤ 1 := by
  let e : ℕ × ℕ × ℕ → BitString := fun t =>
    pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2))
  have he : Function.Injective e := by
    intro a b hab
    have h₁ := @pairCode_injective
      (natBits a.1, pairCode (natBits a.2.1) (natBits a.2.2))
      (natBits b.1, pairCode (natBits b.2.1) (natBits b.2.2)) hab
    have hi := natBits_injective (Prod.ext_iff.mp h₁).1
    have h₂ := @pairCode_injective (natBits a.2.1, natBits a.2.2)
      (natBits b.2.1, natBits b.2.2) (Prod.ext_iff.mp h₁).2
    exact Prod.ext hi (Prod.ext
      (natBits_injective (Prod.ext_iff.mp h₂).1)
      (natBits_injective (Prod.ext_iff.mp h₂).2))
  have hkraft : (∑' w : BitString,
      ((2 : ℝ≥0∞)⁻¹) ^ (oracleComplexity A w : ℝ)) ≤ 1 := by
    let U := optimalOraclePrefix A
    have hU := exists_optimalOraclePrefix_spec A
    have hk : (∑' w : BitString, complexityWeight (KP U w [])) ≤ 1 :=
      (ENNReal.tsum_le_tsum fun w => complexityWeight_KP_le_aprioriMeasure U w []).trans
        (tsum_aprioriMeasure_le_one U [] hU.2.1)
    have hw (w : BitString) :
        ((2 : ℝ≥0∞)⁻¹) ^ (oracleComplexity A w : ℝ) =
          complexityWeight (KP U w []) := by
      change ((2 : ℝ≥0∞)⁻¹) ^ ((KP U w []).toNat : ℝ) = _
      rw [ENNReal.rpow_natCast, ← complexityWeight_coe,
        ENat.natCast_toNat (exists_optimalOraclePrefix_finite A w [])]
    simpa only [hw] using hk
  unfold nullPressureMass
  simp only [birkhoffSum, Finset.sum_const_zero, add_zero]
  calc
    (∑' t : lowerPressureThreshold P T (fun _ => 0) 0 A s,
        (2 : ℝ≥0∞) ^ (-(s : ℝ) * t.val.2.1)) ≤
        ∑' t : lowerPressureThreshold P T (fun _ => 0) 0 A s,
          ((2 : ℝ≥0∞)⁻¹) ^ (oracleComplexity A (e t.val) : ℝ) := by
      apply ENNReal.tsum_le_tsum
      intro t
      have ht : (oracleComplexity A (e t.val) : ℝ) < (s : ℝ) * t.val.2.1 := by
        simpa only [lowerPressureThreshold, Set.mem_ofPred_eq, birkhoffSum,
          Finset.sum_const_zero, sub_zero] using t.property.2.2
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ ∑' w : BitString, ((2 : ℝ≥0∞)⁻¹) ^ (oracleComplexity A w : ℝ) :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun t : lowerPressureThreshold P T (fun _ => 0) 0 A s => e t.val)
        (he.comp Subtype.val_injective)
        (fun w => ((2 : ℝ≥0∞)⁻¹) ^ (oracleComplexity A w : ℝ))
    _ ≤ 1 := hkraft

/-- A strict scale-wise liminf bound for the potential-one Bowen–Schmeling cost supplies
arbitrarily large positive orders with an ideal Bowen-ball realizer of complexity below
`b * n`. The strict infimum inequality already supplies a realizer; no effective geometric
information is required. -/
private lemma exists_large_order_realizer_of_liminf_lt
    (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X) (p : ℕ) (b : ℝ)
    (hb : liminf (fun n => finiteScaleBSCost P T (fun _ => 1) A x n
      (dyadicRadius p)) atTop < ENNReal.ofReal b) (N : ℕ) :
    ∃ n i : ℕ, N ≤ n ∧ 1 ≤ n ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) ∧
      (oracleNatComplexity A i : ℝ) < b * n := by
  have hfreq : ∃ᶠ n in atTop, finiteScaleBSCost P T (fun _ => 1) A x n
      (dyadicRadius p) < ENNReal.ofReal b :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hb
  obtain ⟨n, hn, hcost⟩ :=
    ((eventually_ge_atTop (max N 1)).and_frequently hfreq).exists
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [finiteScaleBSCost, ite_eq_right hn0] at hcost
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp hcost
  obtain ⟨hball, hi⟩ := iInf_lt_iff.mp hi
  obtain ⟨hdenom, hi⟩ := iInf_lt_iff.mp hi
  have hsum : birkhoffSum T (fun _ => (1 : ℝ)) n (P.ι i) = n := by
    simp [birkhoffSum]
  rw [hsum] at hi
  have hi' : ENNReal.ofReal ((oracleNatComplexity A i : ℝ) / n) <
      ENNReal.ofReal b := by
    simpa only [ENNReal.ofReal_div_of_pos hnR, ENNReal.ofReal_natCast] using hi
  have hreal : (oracleNatComplexity A i : ℝ) / n < b :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hi'
  refine ⟨n, i, (le_max_left N 1).trans hn, hn1, ?_, (div_lt_iff₀ hnR).mp hreal⟩
  simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at hball ⊢
  intro k hk
  rw [dist_comm]
  exact hball k hk

/-- A rational threshold above the pointwise lower orbit-complexity supremum admits an
enumerable null cover of that exponent, without oracle admissibility assumptions. -/
private theorem exists_isREIn_isNullPressureCover_of_lt
    (P : Presentation X) (T : X → X)
    (A : Set ℕ) (Z : Set X) (s : ℚ)
    (hbound : (⨆ x ∈ Z, (orbitComplexities P T A x).1) <
      ENNReal.ofReal (s : ℝ)) :
    ∃ E : Set (ℕ × ℕ × ℕ),
      IsNullPressureCover P T (fun _ => 0) 0 Z (s : ℝ) E ∧
      IsREIn A E := by
  refine ⟨lowerPressureThreshold P T (fun _ => 0) 0 A s, ⟨?_, ?_, ?_⟩,
    isREIn_lowerPressureThreshold_zero_potential P T A s⟩
  · intro t ht
    exact ⟨ht.1, ht.2.1⟩
  · exact (nullPressureMass_lowerPressureThreshold_le_one P T A s).trans_lt
      ENNReal.one_lt_top
  · intro p hp N hN x hx
    have hxrate : (orbitComplexities P T A x).1 < ENNReal.ofReal (s : ℝ) :=
      (le_iSup₂ (f := fun x (_ : x ∈ Z) => (orbitComplexities P T A x).1) x hx).trans_lt
        hbound
    have hlim : liminf (fun n => finiteScaleBSCost P T (fun _ => 1) A x n
        (dyadicRadius p)) atTop < ENNReal.ofReal (s : ℝ) :=
      (le_iSup (fun p => liminf (fun n =>
        finiteScaleBSCost P T (fun _ => 1) A x n (dyadicRadius p)) atTop) p).trans_lt
          hxrate
    obtain ⟨b, hlow, hbs⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hlim)
    have hb : liminf (fun n => finiteScaleBSCost P T (fun _ => 1) A x n
        (dyadicRadius p)) atTop < ENNReal.ofReal b :=
      (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hlim)).mpr hlow
    obtain ⟨c, hc⟩ := oracle_triple_complexity_le A p
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      (eventually_logarithmic_overhead_lt_linear (s : ℝ) b c hbs)
    obtain ⟨n, i, hn, hn1, hball, hcost⟩ :=
      exists_large_order_realizer_of_liminf_lt P T A x p b hb (max N M)
    refine ⟨i, n, (le_max_left N M).trans hn, ?_, hball⟩
    refine ⟨hn1, hp, ?_⟩
    simp only [birkhoffSum, Finset.sum_const_zero, sub_zero]
    have ht := hc i n
    have ho := hM n ((le_max_right N M).trans hn)
    nlinarith

/-- Effective lower entropy is the pointwise lower orbit-complexity supremum for every oracle.
Blueprint node `pressure:entropy-pts`. -/
theorem entropy_effectiveCharacterization_allOracles (P : Presentation X) (T : X → X)
    (A : Set ℕ) (Z : Set X) :
    effectiveLowerEntropy P T A Z = ⨆ x ∈ Z, (orbitComplexities P T A x).1 := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε hS ↦ ?_
    set S := ⨆ x ∈ Z, (orbitComplexities P T A x).1 with hSdef
    obtain ⟨q, hq1, hq2⟩ :=
      exists_rat_btwn (lt_add_of_pos_right S.toReal (NNReal.coe_pos.mpr hε))
    have hq : 0 < (q : ℝ) := lt_of_le_of_lt ENNReal.toReal_nonneg hq1
    obtain ⟨E, hcover, hRE⟩ := exists_isREIn_isNullPressureCover_of_lt P T A Z q
      ((ENNReal.lt_ofReal_iff_toReal_lt hS.ne).mpr hq1)
    calc
      effectiveLowerEntropy P T A Z ≤ ENNReal.ofReal (q : ℝ) :=
        iInf_le_of_le (q : ℝ) (iInf_le_of_le hq.le
          (iInf_le_of_le E (iInf_le_of_le ⟨hcover, hRE⟩ le_rfl)))
      _ ≤ ENNReal.ofReal (S.toReal + ε) := ENNReal.ofReal_le_ofReal hq2.le
      _ = S + ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg,
          ENNReal.ofReal_toReal hS.ne]
        simp
  · rw [effectiveLowerEntropy]
    refine le_iInf₂ fun s hs ↦ le_iInf fun E ↦ le_iInf fun ⟨hcover, hRE⟩ ↦ ?_
    exact iSup₂_le fun x hx ↦
      orbitComplexities_fst_le_of_isNullPressureCover P T A Z s hs E hcover hRE x hx

end Kolmogorov.PointToSet
