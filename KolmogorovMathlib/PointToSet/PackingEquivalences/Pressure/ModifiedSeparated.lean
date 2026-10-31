/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.ScaleDichotomy

/-!
# The countable separated modification of upper pressure

This module compares the separated upper capacity pressure `separatedUpperPressureAt` and its
countable modification `modifiedSeparatedPressureAt` with the packing pressure and with the
covering capacity pressures `upperCapacity` and `modifiedUpperPressure`.

* `modifiedSeparatedBoundsPackPressure` (blueprint node `pack:sep-to-pack`): the packing
  pressure at radius `r` is at most the separated modification at the same radius. A packing is
  grouped by order, the slices are separated sets, and mixed-order extraction produces
  arbitrarily large orders at which the separated sum is exponentially large.
* `pressureEquivalence_capacity_lower`, `pressureEquivalence_capacity_upper`: covering capacity
  and separated capacity are comparable at radii `r` and `2 * r`, up to the potential variation
  error.
* `pressureEquivalence_restrict_pieces`, `pressureEquivalence_modified_lower`,
  `pressureEquivalence_modified_upper`: the same comparisons for the countable modifications,
  where the cover pieces may be assumed to lie in the target set.

These are the inequalities between the three upper pressure definitions that are combined in
`KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.Equivalence` to prove
`pack:pressure-equivalence`.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X]

/-- If the packing outer envelope is infinite, then every countable cover has a piece of positive
pre-content. -/
private lemma exists_pos_precontent_of_pressureOuterEnvelope_eq_top (T : X → X) (f : X → ℝ)
    (Z : Set X) (r s : ℝ) (Y : ℕ → Set X) (hY_sub : ∀ j, Y j ⊆ Z) (hY_cov : Z ⊆ ⋃ j, Y j)
    (h_env : pressureOuterEnvelope T f Z s r = ⊤) :
    ∃ j, 0 < packingPressurePrecontent T f (Y j) s r := by
  by_contra h
  push Not at h
  have h_zero (j : ℕ) : packingPressurePrecontent T f (Y j) s r = 0 := le_antisymm (h j) zero_le
  have h_le : pressureOuterEnvelope T f Z s r ≤ ∑' j, packingPressurePrecontent T f (Y j) s r :=
    iInf₂_le_of_le Y ⟨hY_sub, hY_cov⟩ le_rfl
  simp only [h_zero, tsum_zero, h_env, nonpos_iff_eq_zero, ENNReal.top_ne_zero] at h_le

/-- A real number strictly below the packing pressure threshold has infinite packing outer
envelope. -/
private lemma pressureOuterEnvelope_eq_top_of_lt_packingPressureAt (T : X → X) (f : X → ℝ)
    (Z : Set X) (r : ℝ) {s : ℝ}
    (hs : (s : EReal) < packingPressureAt T f Z r) : pressureOuterEnvelope T f Z s r = ⊤ := by
  by_contra h_ne
  refine absurd hs (not_lt.mpr ?_)
  rw [pressureDichotomyScaleLimit_threshold T f Z r]
  refine iSup₂_le fun t ht ↦ ?_
  by_contra h_lt
  have hst : s < t := EReal.coe_lt_coe_iff.mp (not_le.mp h_lt)
  have h_mono : pressureOuterEnvelope T f Z t r ≤ pressureOuterEnvelope T f Z s r :=
    pressureOuterEnvelope_antitone_exponent T f Z r hst.le
  rw [ht] at h_mono
  exact h_ne (top_le_iff.mp h_mono)

/-- A set with packing pre-content greater than `ofReal a` admits, above every cutoff `N`, a
Bowen packing of weighted sum at least `ofReal a`. -/
private lemma exists_isBowenPacking_of_lt_precontent (T : X → X) (f : X → ℝ) (Y : Set X)
    (r s a : ℝ) (ha_lt : ENNReal.ofReal a < packingPressurePrecontent T f Y s r) {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ F : Set (X × ℕ), IsBowenPacking T Y r N F ∧
      ENNReal.ofReal a ≤ packingPressureSum T f s r F := by
  have h_pre : packingPressurePrecontent T f Y s r ≤ packingPressureContent T f Y s r N :=
    iInf₂_le_of_le N hN le_rfl
  obtain ⟨F, hF⟩ := lt_iSup_iff.mp (ha_lt.trans_le h_pre)
  obtain ⟨hF_pack, hF_sum⟩ := lt_iSup_iff.mp hF
  exact ⟨F, hF_pack, hF_sum.le⟩

/-- The centers of a Bowen packing that have one given order form a separated set. -/
private lemma isBowenSeparated_of_isBowenPacking (T : X → X) {Y : Set X} {r : ℝ} (hr : 0 < r)
    {N : ℕ} {F : Set (X × ℕ)} (hF : IsBowenPacking T Y r N F) {k : ℕ} (hk : 1 ≤ k) :
    IsBowenSeparated T k r {x | (x, k) ∈ F} := by
  intro x hx y hy hxy
  by_contra h
  have hdisj := hF.2.2 hx hy fun e ↦ hxy (congr_arg Prod.fst e)
  have hyx : y ∈ bowenBall T k x r := (bowen_ball_dense_iff T k hk x y r).mpr (not_le.mp h)
  have hyy : y ∈ bowenBall T k y r := by
    have hne : (Finset.range k).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
    have h0 : bowenDist T k y y = 0 := by simp [bowenDist, Finset.sup_const hne]
    exact (bowen_ball_dense_iff T k hk y y r).mpr (h0 ▸ hr)
  exact Set.disjoint_left.mp hdisj hyx hyy

/-- The weighted sum of a decorated family is the sum over orders `k` of `2 ^ (-s * k)` times the
weight of the centers of order `k`. -/
private lemma packingPressureSum_eq_tsum_orders (T : X → X) (f : X → ℝ) (s r : ℝ)
    (F : Set (X × ℕ)) :
    packingPressureSum T f s r F = ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-s * (k : ℝ)) *
      ∑' x : {x | (x, k) ∈ F}, pressureBallWeight T f .supremum k x r := by
  let e : (Σ k : ℕ, {x | (x, k) ∈ F}) ≃ F :=
    { toFun := fun p ↦ ⟨(p.2.1, p.1), p.2.2⟩
      invFun := fun a ↦ ⟨a.1.2, a.1.1, a.2⟩
      left_inv := fun p ↦ rfl
      right_inv := fun a ↦ rfl }
  unfold packingPressureSum
  rw [← e.tsum_eq, ENNReal.tsum_sigma']
  exact tsum_congr fun k ↦ ENNReal.tsum_mul_left (a := (2 : ℝ≥0∞) ^ (-s * (k : ℝ)))
    (f := fun x : {x | (x, k) ∈ F} ↦ pressureBallWeight T f .supremum k x r)

/-- Mixed-order extraction for a packing: if a Bowen packing of orders at least `N` has weighted
sum at least `ofReal a` at exponent `s`, then for every `t < s` some order `k ≥ N` has
`2 ^ (-t * k)` times the separated sum at least a fixed positive constant. -/
private lemma exists_order_lower_bound_separatedPressureSum (T : X → X) (f : X → ℝ) (Y : Set X)
    (r s t : ℝ) (hr : 0 < r) (hts : t < s) (a : ℝ) (ha_pos : 0 < a) {N : ℕ} (hN : 1 ≤ N)
    {F : Set (X × ℕ)} (hF_pack : IsBowenPacking T Y r N F)
    (hF_sum : ENNReal.ofReal a ≤ packingPressureSum T f s r F) :
    ∃ k : ℕ, k ≥ N ∧ ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(s - t))) * a) ≤
      (2 : ℝ≥0∞) ^ (-t * (k : ℝ)) * separatedPressureSum T f Y k r := by
  let b (k : ℕ) : ℝ≥0∞ := ∑' x : {x | (x, k) ∈ F}, pressureBallWeight T f .supremum k x r
  have hb_le (k : ℕ) (hk : N ≤ k) : b k ≤ separatedPressureSum T f Y k r :=
    le_iSup₂_of_le {x | (x, k) ∈ F} ⟨fun x hx ↦ (hF_pack.2.1 (x, k) hx).1,
      isBowenSeparated_of_isBowenPacking T hr hF_pack (hN.trans hk)⟩ le_rfl
  have hb_zero (k : ℕ) (hk : k < N) : b k = 0 := by
    have : IsEmpty {x | (x, k) ∈ F} :=
      ⟨fun x ↦ absurd (le_max_right 1 N |>.trans (hF_pack.2.1 (x.1, k) x.2).2) (by omega)⟩
    exact tsum_empty
  have hpow (k : ℝ) : (2 : ℝ≥0∞) ^ (-s * k) = 2 ^ (-(s - t) * k) * 2 ^ (-t * k) := by
    rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    congr 1
    ring
  have h_support : Function.support (fun k : ℕ ↦ (2 : ℝ≥0∞) ^ (-s * (k : ℝ)) * b k) ⊆
      {k | N ≤ k} := fun k hk ↦ by
    by_contra h
    exact hk (by simp only [hb_zero k (not_le.mp h), mul_zero])
  have hmass : ENNReal.ofReal a ≤ ∑' k : {k : ℕ // N ≤ k},
      (2 : ℝ≥0∞) ^ (-(s - t) * (k.val : ℝ)) *
        ((2 : ℝ≥0∞) ^ (-t * (k.val : ℝ)) * separatedPressureSum T f Y k.val r) :=
    calc ENNReal.ofReal a
        ≤ ∑' k : ℕ, (2 : ℝ≥0∞) ^ (-s * (k : ℝ)) * b k := by
          exact hF_sum.trans_eq (packingPressureSum_eq_tsum_orders T f s r F)
      _ = ∑' k : {k : ℕ // N ≤ k}, (2 : ℝ≥0∞) ^ (-s * (k.val : ℝ)) * b k.val :=
          (tsum_subtype_eq_of_support_subset h_support).symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun k ↦ by
          rw [hpow, mul_assoc]
          gcongr
          exact hb_le k.val k.2
  exact extractOrder s t a hts ha_pos
    (fun k ↦ (2 : ℝ≥0∞) ^ (-t * (k : ℝ)) * separatedPressureSum T f Y k r) N hN hmass

/-- A lower bound for the modified separated pressure follows from a lower bound on some piece
of every countable cover. -/
private lemma le_modifiedSeparatedPressureAt_of_forall_cover (T : X → X) (f : X → ℝ) (Z : Set X)
    (r : ℝ) (e : EReal)
    (h : ∀ Y : ℕ → Set X, (∀ j, Y j ⊆ Z) → Z ⊆ ⋃ j, Y j →
      ∃ j, e ≤ separatedUpperPressureAt T f (Y j) r) :
    e ≤ modifiedSeparatedPressureAt T f Z r :=
  le_iInf₂ fun Y hY ↦ (h Y hY.1 hY.2).elim fun j hj ↦
    hj.trans (le_iSup (fun k ↦ separatedUpperPressureAt T f (Y k) r) j)

/-- The extended logarithm of the natural number `2` is the real logarithm. -/
private lemma log_two_eq : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
  simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)

/-- An exponential lower bound `c ≤ 2 ^ (-t * k) * q k` for the partition sums gives the
logarithmic rate bound `t + log₂ c / k ≤ pressureRate q k`. -/
private lemma coe_add_logb_div_le_pressureRate (q : ℕ → ℝ≥0∞) {c : ℝ} (t : ℝ) (hc : 0 < c)
    {k : ℕ} (hk : k ≠ 0) (h : ENNReal.ofReal c ≤ (2 : ℝ≥0∞) ^ (-t * (k : ℝ)) * q k) :
    ((t + Real.logb 2 c / (k : ℝ) : ℝ) : EReal) ≤ pressureRate q k := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ : 0 ≤ (((Real.log 2)⁻¹ * (k : ℝ)⁻¹ : ℝ) : EReal) :=
    EReal.coe_nonneg.mpr (by positivity)
  have hlog := ENNReal.log_le_log h
  rw [ENNReal.log_mul_add, ENNReal.log_rpow, log_two_eq, ENNReal.log_ofReal_of_pos hc] at hlog
  have hm := mul_le_mul_of_nonneg_right hlog hκ
  rw [EReal.right_distrib_of_nonneg_of_ne_top hκ (EReal.coe_ne_top _),
    ← pressureRate_eq_log_mul q hk] at hm
  have h₁ : ((Real.log c : ℝ) : EReal) * (((Real.log 2)⁻¹ * (k : ℝ)⁻¹ : ℝ) : EReal) =
      ((Real.logb 2 c / k : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    rw [Real.logb]
    ring
  have h₂ : ((-t * k : ℝ) : EReal) * (Real.log 2 : ℝ) *
      (((Real.log 2)⁻¹ * (k : ℝ)⁻¹ : ℝ) : EReal) = ((-t : ℝ) : EReal) := by
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    congr 1
    field_simp
  rw [h₁, h₂] at hm
  calc ((t + Real.logb 2 c / k : ℝ) : EReal)
      = (t : EReal) + ((Real.logb 2 c / k : ℝ) : EReal) := EReal.coe_add _ _
    _ ≤ (t : EReal) + (((-t : ℝ) : EReal) + pressureRate q k) := add_le_add le_rfl hm
    _ = pressureRate q k := by
      rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]

/-- If for every `N ≥ 1` there is an order `k ≥ N` with `t + d / k ≤ u k`, then
`t ≤ limsup u`. -/
private lemma coe_le_limsup_of_forall_exists_add_div_le (u : ℕ → EReal) (t d : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → ∃ k : ℕ, k ≥ N ∧ ((t + d / (k : ℝ) : ℝ) : EReal) ≤ u k) :
    (t : EReal) ≤ limsup u atTop := by
  refine le_of_forall_lt fun x hx ↦ ?_
  obtain ⟨y, hxy, hyt⟩ := EReal.exists_between_coe_real hx
  refine hxy.trans_le (le_limsup_of_frequently_le ?_)
  have h_event : ∀ᶠ k : ℕ in atTop, y ≤ t + d / k := by
    have h_lim := (tendsto_const_div_atTop_nhds_zero_nat d).const_add t
    rw [add_zero] at h_lim
    exact h_lim.eventually (Ici_mem_nhds (EReal.coe_lt_coe_iff.mp hyt))
  obtain ⟨M, hM⟩ := eventually_atTop.mp h_event
  refine Filter.frequently_atTop.mpr fun N ↦ ?_
  obtain ⟨k, hk, hk_le⟩ := h (max (max N M) 1) (le_max_right _ _)
  exact ⟨k, (le_max_left N M).trans ((le_max_left _ 1).trans hk), (EReal.coe_le_coe_iff.mpr
    (hM k ((le_max_right N M).trans ((le_max_left _ 1).trans hk)))).trans hk_le⟩

/-- If the separated sums are, for arbitrarily large orders `k`, at least `c / 2 ^ (-t * k)`
with `c > 0`, then the separated upper capacity pressure is at least `t`. -/
private lemma coe_le_separatedUpperPressureAt_of_exists_large (T : X → X) (f : X → ℝ) (Y : Set X)
    (r t : ℝ) {c : ℝ} (hc : 0 < c)
    (h : ∀ N : ℕ, 1 ≤ N → ∃ k : ℕ, k ≥ N ∧
      ENNReal.ofReal c ≤ (2 : ℝ≥0∞) ^ (-t * (k : ℝ)) * separatedPressureSum T f Y k r) :
    (t : EReal) ≤ separatedUpperPressureAt T f Y r := by
  refine coe_le_limsup_of_forall_exists_add_div_le _ t (Real.logb 2 c) fun N hN ↦ ?_
  obtain ⟨k, hk, hk_le⟩ := h N hN
  exact ⟨k, hk, coe_add_logb_div_le_pressureRate _ t hc (by omega) hk_le⟩

/-- Separated modification bounds packing at the same radius for all signed pressures.
Blueprint node `pack:sep-to-pack`. -/
theorem modifiedSeparatedBoundsPackPressure (T : X → X) (f : X → ℝ) (Z : Set X) (r : ℝ) (hr : 0 < r)
    :
    packingPressureAt T f Z r ≤ modifiedSeparatedPressureAt T f Z r := by
  refine le_of_forall_lt fun x hx ↦ ?_
  obtain ⟨s, hxs, hs⟩ := EReal.exists_between_coe_real hx
  refine hxs.trans_le (le_modifiedSeparatedPressureAt_of_forall_cover T f Z r s ?_)
  intro Y hY_sub hY_cov
  have h_top := pressureOuterEnvelope_eq_top_of_lt_packingPressureAt T f Z r hs
  obtain ⟨j, hj_pos⟩ :=
    exists_pos_precontent_of_pressureOuterEnvelope_eq_top T f Z r s Y hY_sub hY_cov h_top
  obtain ⟨a, -, ha_pos', ha_lt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hj_pos
  have ha_pos : 0 < a := ENNReal.ofReal_pos.mp ha_pos'
  refine ⟨j, EReal.ge_of_forall_gt_iff_ge.mp fun t ht ↦ ?_⟩
  have hts : t < s := EReal.coe_lt_coe_iff.mp ht
  refine coe_le_separatedUpperPressureAt_of_exists_large T f (Y j) r t
    (c := (1 - (2 : ℝ) ^ (-(s - t))) * a) ?_ fun N hN ↦ ?_
  · exact mul_pos (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)))
      ha_pos
  · obtain ⟨F, hF_pack, hF_sum⟩ := exists_isBowenPacking_of_lt_precontent T f (Y j) r s a ha_lt hN
    exact exists_order_lower_bound_separatedPressureSum T f (Y j) r s t hr hts a ha_pos hN
      hF_pack hF_sum

/-- The covering upper capacity is bounded by separated capacity at the doubled radius.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_capacity_lower [SeparableSpace X] (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (Z : Set X) (r : ℝ) (hr : 0 < r) :
    upperCapacity T f .supremum Z (2 * r) ≤ separatedUpperPressureAt T f Z (2 * r) := by
  refine limsup_le_limsup ?_ (isCoboundedUnder_le_of_le atTop fun _ ↦ bot_le)
    (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact pressureRate_le_of_le _ _ n (pressureSpanSep T hT f Z n hn r hr)

/-- The separated capacity at the doubled radius is bounded by the covering capacity at radius `r`
plus the finite potential variation at radius `2 * r`.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_capacity_upper (T : X → X) (f : X → ℝ) (Z : Set X) (r : ℝ)
    (hω : potentialVariation f (2 * r) < ⊤) :
    separatedUpperPressureAt T f Z (2 * r) ≤
      upperCapacity T f .supremum Z r + ((potentialVariation f (2 * r)).toReal : EReal) := by
  unfold separatedUpperPressureAt upperCapacity
  have h_eventual : ∀ᶠ n in atTop,
      pressureRate (fun n ↦ separatedPressureSum T f Z n (2 * r)) n ≤
        pressureRate (fun n ↦ partitionSum T f .supremum Z n r) n +
          ((potentialVariation f (2 * r)).toReal : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine pressureRate_le_add_of_le_mul _ _ _ _ (by omega) ?_
    simpa only [mul_comm] using pressureSpanSep_upper T f Z n hn r hω
  have h_add := EReal.limsup_add_le (u := pressureRate fun n ↦ partitionSum T f .supremum Z n r)
    (v := fun _ : ℕ ↦ ((potentialVariation f (2 * r)).toReal : EReal)) (f := atTop)
    (Or.inr (by simp)) (Or.inr (by simp))
  simpa only [Pi.add_def, limsup_const] using (limsup_le_limsup h_eventual).trans h_add

/-- The countable modification of the supremum-weight covering capacity may be computed with
covers whose pieces lie in the target set: it is the infimum over countable covers of the
supremum of the pieces' upper capacities.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_restrict_pieces (T : X → X) (f : X → ℝ)
    (Z : Set X) (r : ℝ) :
    modifiedUpperPressure T f .supremum Z r =
      ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
        ⨆ j, upperCapacity T f .supremum (Y j) r := by
  unfold modifiedUpperPressure
  refine le_antisymm (le_iInf₂ fun Y hY ↦ iInf₂_le_of_le Y hY.2 le_rfl) (le_iInf₂ fun Y hY ↦ ?_)
  have h : (∀ j, Y j ∩ Z ⊆ Z) ∧ Z ⊆ ⋃ j, Y j ∩ Z :=
    ⟨fun j ↦ Set.inter_subset_right, fun x hx ↦ by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hY hx)
      exact Set.mem_iUnion.2 ⟨j, hj, hx⟩⟩
  exact iInf₂_le_of_le (fun j ↦ Y j ∩ Z) h
    (iSup_mono fun j ↦ upperCapacity_mono_set T f .supremum Set.inter_subset_left r)

/-- The covering-to-separated comparison passes to countable modifications.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_modified_lower [SeparableSpace X] (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (Z : Set X) (r : ℝ) (hr : 0 < r) :
    modifiedUpperPressure T f .supremum Z (2 * r) ≤
      modifiedSeparatedPressureAt T f Z (2 * r) := by
  unfold modifiedUpperPressure modifiedSeparatedPressureAt
  refine le_iInf₂ fun Y hY ↦ iInf₂_le_of_le Y hY.2 (iSup_mono fun j ↦ ?_)
  exact pressureEquivalence_capacity_lower T hT f (Y j) r hr

/-- The reverse modified comparison retains the radius and error from the sum comparison.
Blueprint node `pack:pressure-equivalence`. -/
theorem pressureEquivalence_modified_upper (T : X → X) (f : X → ℝ) (Z : Set X) (r : ℝ)
    (hω : potentialVariation f (2 * r) < ⊤) :
    modifiedSeparatedPressureAt T f Z (2 * r) ≤
      modifiedUpperPressure T f .supremum Z r +
        ((potentialVariation f (2 * r)).toReal : EReal) := by
  rw [pressureEquivalence_restrict_pieces T f Z r]
  refine le_trans (le_iInf₂ fun Y hY ↦ ?_ :
    _ ≤ ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
      (⨆ j, upperCapacity T f .supremum (Y j) r) +
        ((potentialVariation f (2 * r)).toReal : EReal))
    ((iInf_mono fun Y ↦ EReal.iInf_add_coe_le _ _).trans (EReal.iInf_add_coe_le _ _))
  refine (iInf₂_le_of_le Y hY le_rfl).trans
    ((iSup_mono fun j ↦ ?_).trans (EReal.iSup_add_coe_le _ _))
  exact pressureEquivalence_capacity_upper T f (Y j) r hω

end Kolmogorov.PointToSet
