/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Classical.HausdorffCovers

/-!
# Hausdorff dimension and static point dimensions

This module relates the Hausdorff dimension of a set `Z` in a presented metric space to the lower
static point dimensions `(staticPointDimensions P A x).1` of its points relative to an oracle `A`,
in the two directions of the point-to-set principle for Hausdorff dimension.

* `hausdorffLeSupPointDimension` (blueprint node `conf:hausdorff-any-oracle`): for every oracle `A`,
  `dimH Z ≤ ⨆ x ∈ Z, dim^A x`.  The proof builds from Kraft's inequality an ideal dyadic cover in
  which every point of `Z` occurs infinitely often, and bounds its cost by a geometric tail.
* `hausdorffAchievingOracle` (blueprint node `conf:hausdorff-achieving`): some oracle gives the
  reverse inequality `⨆ x ∈ Z, dim^A x ≤ dimH Z`.  The index–precision pairs of arbitrarily fine
  covers of small cost are coded in an oracle with the oracle coding theorem, and the oracles
  obtained for a sequence of exponents decreasing to `dimH Z` are joined.
* `hausdorffAchievingOracle_stable`: the inequality persists for every oracle above an achieving
  one.

The lemmas `normalizedPrecisionComplexity_dyadicRadius_eq_ofReal_div` and
`precisionComplexityNat_le_of_oracleNatComplexity_le` are shared with
`KolmogorovMathlib.PointToSet.Conformal.Classical.PointToSetPrinciple`, which proves the
corresponding statements for packing dimension.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace MeasureTheory Measure
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- The dyadic radii `2⁻ʳ` tend to zero through positive values. -/
private lemma tendsto_dyadicRadius_nhdsGT : Tendsto dyadicRadius atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall fun n ↦ Set.mem_Ioi.mpr (by unfold dyadicRadius; positivity)⟩

/-- The lower static point dimension is the lower limit of the normalized precision complexity
along the dyadic radii `2⁻ʳ`. -/
private lemma staticPointDimensions_fst_eq_liminf_dyadicRadius
    (P : Presentation X) (A : Set ℕ) (x : X) :
    (staticPointDimensions P A x).1 =
      liminf (fun r : ℕ ↦ normalizedPrecisionComplexity P A x (dyadicRadius r)) atTop :=
  dimension_along_scales P A x dyadicRadius
    (fun m ↦ by unfold dyadicRadius; positivity)
    (tendsto_nhdsWithin_iff.mp tendsto_dyadicRadius_nhdsGT).1
    tendsto_log_dyadicRadius_succ_div

/-- At a positive dyadic precision `2⁻ʳ`, the normalized precision complexity is the precision
complexity divided by the integer exponent `r`. -/
lemma normalizedPrecisionComplexity_dyadicRadius_eq_ofReal_div
    (P : Presentation X) (A : Set ℕ) (x : X) (r : ℕ) (hr : 1 ≤ r) :
    normalizedPrecisionComplexity P A x (dyadicRadius r) =
      ENNReal.ofReal ((precisionComplexityNat P A x (dyadicRadius r) : ℝ) / (r : ℝ)) := by
  have hpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : -Real.logb 2 (dyadicRadius r) = (r : ℝ) := by
    rw [dyadicRadius, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [normalizedPrecisionComplexity, hlog]
  simp only [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast]

/-- The precision complexity at radius `δ` is attained by an ideal point within `δ` of `x`, and
its natural-number value is the oracle complexity of that index. -/
private lemma exists_ideal_point_attaining_precisionComplexityNat
    (P : Presentation X) (A : Set ℕ) (x : X) (δ : ℝ) (hδ : 0 < δ) :
    ∃ i : ℕ, dist (P.ι i) x < δ ∧
      precisionComplexityNat P A x δ = oracleNatComplexity A i := by
  obtain ⟨i, hi, heq⟩ := staticPointDimensions_attained P A x δ hδ
  refine ⟨i, hi, ?_⟩
  unfold precisionComplexityNat
  rw [heq]
  exact ENat.toNat_natCast _

/-- A point whose lower static dimension is below `s` is, for arbitrarily large dyadic
precisions `r`, within `2⁻ʳ` of an ideal point of oracle complexity below `s * r`. -/
private lemma exists_ideal_point_near_of_staticPointDimensions_lt
    (P : Presentation X) (A : Set ℕ) (x : X) (s : ℝ)
    (hs : (staticPointDimensions P A x).1 < ENNReal.ofReal s) :
    ∀ M : ℕ, ∃ r : ℕ, M ≤ r ∧ ∃ i : ℕ,
      dist (P.ι i) x < dyadicRadius r ∧ (oracleNatComplexity A i : ℝ) < s * r := by
  have hspos : 0 < s := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hs)
  rw [staticPointDimensions_fst_eq_liminf_dyadicRadius P A x] at hs
  have H : ∃ᶠ r : ℕ in atTop,
      normalizedPrecisionComplexity P A x (dyadicRadius r) < ENNReal.ofReal s :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hs
  intro M
  obtain ⟨r, hsmall, hM, hr⟩ :=
    (H.and_eventually ((eventually_ge_atTop M).and (eventually_ge_atTop 1))).exists
  rw [normalizedPrecisionComplexity_dyadicRadius_eq_ofReal_div P A x r hr] at hsmall
  have hpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hcost : (precisionComplexityNat P A x (dyadicRadius r) : ℝ) < s * r :=
    (div_lt_iff₀ hpos).mp ((ENNReal.ofReal_lt_ofReal_iff hspos).mp hsmall)
  obtain ⟨i, hi, hnat⟩ := exists_ideal_point_attaining_precisionComplexityNat P A x
    (dyadicRadius r) (by unfold dyadicRadius; positivity)
  exact ⟨r, hM, i, hi, by simpa only [hnat] using hcost⟩

/-- Kraft counting: at most `2 ^ a` indices have oracle complexity below `a ≥ 0`. -/
private lemma tsum_ite_oracleNatComplexity_lt_le (A : Set ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∑' i : ℕ, (if (oracleNatComplexity A i : ℝ) < a then (1 : ℝ≥0∞) else 0) ≤ 2 ^ a := by
  have hterm : ∀ i : ℕ, (if (oracleNatComplexity A i : ℝ) < a then (1 : ℝ≥0∞) else 0) ≤
      2 ^ a * 2⁻¹ ^ oracleNatComplexity A i := by
    intro i
    split_ifs with h
    · have h1 : (2⁻¹ : ℝ≥0∞) ^ a ≤ 2⁻¹ ^ (oracleNatComplexity A i : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num) h.le
      rw [ENNReal.rpow_natCast] at h1
      calc (1 : ℝ≥0∞) = 2 ^ a * 2⁻¹ ^ a := by
            rw [ENNReal.inv_rpow, ENNReal.mul_inv_cancel
              (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
              (ENNReal.rpow_ne_top_of_nonneg ha (by norm_num))]
        _ ≤ _ := by gcongr
    · exact bot_le
  calc
    _ ≤ ∑' i, 2 ^ a * 2⁻¹ ^ oracleNatComplexity A i := ENNReal.tsum_le_tsum hterm
    _ = 2 ^ a * ∑' i, 2⁻¹ ^ oracleNatComplexity A i := ENNReal.tsum_mul_left
    _ ≤ 2 ^ a * 1 := by gcongr; exact oracle_kraft A
    _ = 2 ^ a := mul_one _

/-- The `t`-cost of the ideal dyadic cover of all pairs `(i, r)` with `r ≥ M` and
`K^A(i) < s * r` is at most a geometric tail of ratio `2 ^ (s - t)`. -/
private lemma idealDyadicCoverCost_oracleNatComplexity_lt_le (A : Set ℕ) {s : ℝ} (hs : 0 ≤ s)
    (t : ℝ) (M : ℕ) :
    idealDyadicCoverCost t
        {a : ℕ × ℕ | M ≤ a.2 ∧ (oracleNatComplexity A a.1 : ℝ) < s * a.2} ≤
      ∑' r : ℕ, if M ≤ r then ((2 : ℝ≥0∞) ^ (s - t)) ^ r else 0 := by
  rw [idealDyadicCoverCost, tsum_subtype _ (fun a : ℕ × ℕ ↦ (2 : ℝ≥0∞) ^ (-t * (a.2 : ℝ))),
    ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun r ↦ ?_
  by_cases hM : M ≤ r
  · have hterm : ∀ i : ℕ, Set.indicator
        {a : ℕ × ℕ | M ≤ a.2 ∧ (oracleNatComplexity A a.1 : ℝ) < s * a.2}
        (fun a ↦ (2 : ℝ≥0∞) ^ (-t * (a.2 : ℝ))) (i, r) =
        (if (oracleNatComplexity A i : ℝ) < s * r then 1 else 0) * 2 ^ (-t * (r : ℝ)) := by
      intro i
      by_cases h : (oracleNatComplexity A i : ℝ) < s * r <;>
        simp [Set.indicator, hM, h]
    rw [tsum_congr hterm, ENNReal.tsum_mul_right]
    simp only [hM, ↓reduceIte]
    calc
      _ ≤ 2 ^ (s * (r : ℝ)) * 2 ^ (-t * (r : ℝ)) := by
        gcongr
        exact tsum_ite_oracleNatComplexity_lt_le A (mul_nonneg hs (Nat.cast_nonneg r))
      _ = ((2 : ℝ≥0∞) ^ (s - t)) ^ r := by
        rw [← ENNReal.rpow_add _ _ (by simp) (by simp), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        congr 1
        ring
  · have hterm : ∀ i : ℕ, Set.indicator
        {a : ℕ × ℕ | M ≤ a.2 ∧ (oracleNatComplexity A a.1 : ℝ) < s * a.2}
        (fun a ↦ (2 : ℝ≥0∞) ^ (-t * (a.2 : ℝ))) (i, r) = 0 := by
      intro i
      simp [Set.indicator, hM]
    rw [tsum_congr hterm, tsum_zero]
    exact bot_le

/-- A geometric tail `∑_{r ≥ M} q ^ r` with ratio `q < 1` tends to zero as `M → ∞`. -/
private lemma tendsto_tsum_ite_pow_atTop {q : ℝ≥0∞} (hq : q < 1) :
    Tendsto (fun M : ℕ ↦ ∑' r : ℕ, if M ≤ r then q ^ r else 0) atTop (𝓝 0) := by
  have hsum : ∑' r : ℕ, q ^ r ≠ ∞ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hq).ne'
  refine ((ENNReal.tendsto_sum_nat_add (fun r ↦ q ^ r) hsum).comp tendsto_id).congr fun M ↦ ?_
  have hinj : Function.Injective fun k : ℕ ↦ k + M := add_left_injective M
  rw [← hinj.tsum_eq (f := fun r ↦ if M ≤ r then q ^ r else 0)]
  · simp
  · intro r hr
    exact ⟨r - M, Nat.sub_add_cancel (by by_contra h; exact hr (by simp [h]))⟩

/-- If every point of `Z` has lower static dimension below `s < t`, then `Z` has ideal dyadic
covers of arbitrarily high precision and arbitrarily small `t`-cost. -/
private lemma exists_idealDyadicCover_of_staticPointDimensions_lt
    (P : Presentation X) (Z : Set X) (A : Set ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (hdim : ∀ x ∈ Z, (staticPointDimensions P A x).1 < ENNReal.ofReal s)
    (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Set (ℕ × ℕ),
      IsIdealDyadicCover P Z M E ∧ idealDyadicCoverCost t E < ENNReal.ofReal ε := by
  have hq : (2 : ℝ≥0∞) ^ (s - t) < 1 :=
    ENNReal.rpow_lt_one_of_one_lt_of_neg ENNReal.one_lt_two (sub_neg.mpr hst)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp (tendsto_tsum_ite_pow_atTop hq)).2 _ (ENNReal.ofReal_pos.mpr hε))
  refine ⟨{a | max M N ≤ a.2 ∧ (oracleNatComplexity A a.1 : ℝ) < s * a.2},
    ⟨fun a ha ↦ (le_max_left _ _).trans ha.1, fun x hx ↦ ?_⟩, ?_⟩
  · obtain ⟨r, hr, i, hi, hK⟩ := exists_ideal_point_near_of_staticPointDimensions_lt P A x s
      (hdim x hx) (max M N)
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop]
    exact ⟨(i, r), ⟨hr, hK⟩, by rwa [dist_comm]⟩
  · exact (idealDyadicCoverCost_oracleNatComplexity_lt_le A hs t _).trans_lt
      (hN _ (le_max_right _ _))

/-- Every oracle bounds the Hausdorff dimension by the supremum of its lower point dimensions.
Blueprint node `conf:hausdorff-any-oracle`. -/
theorem hausdorffLeSupPointDimension (P : Presentation X) (Z : Set X) (A : Set ℕ) :
    _root_.dimH Z ≤ ⨆ x ∈ Z, (staticPointDimensions P A x).1 := by
  by_contra h
  obtain ⟨t', hsup, ht'⟩ := exists_between (not_le.mp h)
  obtain ⟨s', hsup', hs't'⟩ := exists_between hsup
  have ht'top : t' ≠ ⊤ := (ht'.trans_le le_top).ne
  have hs'top : s' ≠ ⊤ := (hs't'.trans (lt_top_iff_ne_top.mpr ht'top)).ne
  have hst : s'.toReal < t'.toReal := (ENNReal.toReal_lt_toReal hs'top ht'top).mpr hs't'
  have hbound : _root_.dimH Z ≤ ENNReal.ofReal t'.toReal := by
    refine hausdorffDyadicIdealCover_converse P Z t'.toReal ENNReal.toReal_nonneg ?_
    refine exists_idealDyadicCover_of_staticPointDimensions_lt P Z A
      ENNReal.toReal_nonneg hst fun x hx ↦ ?_
    rw [ENNReal.ofReal_toReal hs'top]
    exact (le_iSup₂ (f := fun x (_ : x ∈ Z) ↦ (staticPointDimensions P A x).1) x hx).trans_lt
      hsup'
  rw [ENNReal.ofReal_toReal ht'top] at hbound
  exact not_le.mpr ht' hbound

/-- Passing from an oracle `A` to an oracle `B` that satisfies `K^B(i) ≤ K^A(i) + c` for all
indices `i` increases the precision complexity at every positive radius by at most `c`. -/
lemma precisionComplexityNat_le_of_oracleNatComplexity_le
    (P : Presentation X) (A B : Set ℕ) (c : ℕ)
    (hc : ∀ i : ℕ, oracleNatComplexity B i ≤ oracleNatComplexity A i + c)
    (x : X) (δ : ℝ) (hδ : 0 < δ) :
    precisionComplexityNat P B x δ ≤ precisionComplexityNat P A x δ + c := by
  obtain ⟨i, hi, hA⟩ := exists_ideal_point_attaining_precisionComplexityNat P A x δ hδ
  have hB : precisionComplexity P B x δ ≤ oracleNatComplexity B i :=
    iInf_le_of_le i (iInf_le_of_le hi le_rfl)
  have hBnat : precisionComplexityNat P B x δ ≤ oracleNatComplexity B i := by
    have h := ENat.toNat_le_toNat hB (by simp)
    rwa [ENat.toNat_natCast] at h
  calc precisionComplexityNat P B x δ
    _ ≤ oracleNatComplexity B i := hBnat
    _ ≤ oracleNatComplexity A i + c := hc i
    _ = precisionComplexityNat P A x δ + c := by rw [hA]

/-- A fixed additive cost `c` disappears in the lower limit of the complexities `g δ`
normalized by `-log₂ δ` as `δ → 0⁺`. -/
private lemma liminf_div_logb_le_of_le_add (f g : ℝ → ℕ) (c : ℕ)
    (hfg : ∀ δ : ℝ, 0 < δ → g δ ≤ f δ + c) :
    liminf (fun δ ↦ (g δ : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 δ)) (𝓝[>] (0 : ℝ)) ≤
      liminf (fun δ ↦ (f δ : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 δ)) (𝓝[>] (0 : ℝ)) := by
  let L := 𝓝[>] (0 : ℝ)
  let t (δ : ℝ) := -Real.logb 2 δ
  have ht : Tendsto t L atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num))
  let e (δ : ℝ) := ENNReal.ofReal ((c : ℝ) / t δ)
  have he_zero : Tendsto e L (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (Tendsto.const_div_atTop ht (c : ℝ))
    exact (ENNReal.ofReal_zero).symm ▸ this
  have h_bound : ∀ᶠ δ in L, (g δ : ℝ≥0∞) / ENNReal.ofReal (t δ) ≤
      (f δ : ℝ≥0∞) / ENNReal.ofReal (t δ) + e δ := by
    filter_upwards [self_mem_nhdsWithin, ht.eventually (eventually_gt_atTop 0)]
    intro δ hδ ht_pos
    have h_div : (g δ : ℝ≥0∞) / ENNReal.ofReal (t δ) ≤
        ((f δ : ℝ≥0∞) + (c : ℝ≥0∞)) / ENNReal.ofReal (t δ) := by
      apply ENNReal.div_le_div_right
      exact_mod_cast hfg δ hδ
    have h_c_div : (c : ℝ≥0∞) / ENNReal.ofReal (t δ) = e δ := by
      unfold e
      rw [ENNReal.ofReal_div_of_pos ht_pos, ENNReal.ofReal_natCast]
    rwa [ENNReal.add_div, h_c_div] at h_div
  have h_le := Filter.liminf_le_liminf h_bound
  have h_add_lim := ENNReal.liminf_add_of_right_tendsto_zero he_zero
    (fun δ ↦ (f δ : ℝ≥0∞) / ENNReal.ofReal (t δ))
  exact h_le.trans_eq h_add_lim

/-- If `dimH Z < s`, there are ideal dyadic covers `E M` of `Z` of arbitrarily high precision
whose `s`-costs have total sum at most one. -/
private lemma exists_idealDyadicCovers_with_summable_cost (P : Presentation X) (Z : Set X) (s : ℝ)
    (h_dim : _root_.dimH Z < ENNReal.ofReal s) :
    ∃ E : ℕ → Set (ℕ × ℕ),
      (∀ M, IsIdealDyadicCover P Z M (E M)) ∧
      (∑' M : ℕ, idealDyadicCoverCost s (E M)) ≤ 1 := by
  choose E hE using fun M ↦ hausdorffDyadicIdealCover P Z s h_dim M
    ((2 : ℝ)⁻¹ ^ (M + 1)) (by positivity)
  refine ⟨E, fun M ↦ (hE M).1, ?_⟩
  calc
    (∑' M : ℕ, idealDyadicCoverCost s (E M)) ≤
        ∑' M : ℕ, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (M + 1)) :=
      ENNReal.tsum_le_tsum fun M ↦ (hE M).2.le
    _ = ∑' M : ℕ, (2⁻¹ : ℝ≥0∞) ^ (M + 1) := by
      congr 1
      ext M
      rw [ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    _ = 1 := by
      rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- All index–precision pairs of a family of ideal dyadic covers of total cost at most one can
be coded in one oracle `A`, with one additive constant `c`: the oracle complexity of an index `i`
occurring with precision `r` is at most `s * r + c`. -/
private lemma exists_oracle_bounding_cover_complexity
    (s : ℝ) (hs : 0 ≤ s) (E : ℕ → Set (ℕ × ℕ))
    (hcost : (∑' M : ℕ, idealDyadicCoverCost s (E M)) ≤ 1) :
    ∃ A : Set ℕ, ∃ c : ℝ, ∀ M : ℕ, ∀ a ∈ E M,
      (oracleNatComplexity A a.1 : ℝ) ≤ s * (a.2 : ℝ) + c := by
  classical
  let e : ℕ × (ℕ × ℕ) ≃ ℕ :=
    (Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv).trans Nat.pairEquiv
  let R : ℕ × (ℕ × ℕ) → Option (BitString × ℕ) := fun p ↦
    if p.2 ∈ E p.1 then some (natBits p.2.1, ⌈s * (p.2.2 : ℝ)⌉₊) else none
  let req : ℕ → Option (BitString × ℕ) := fun n ↦ R (e.symm n)
  have hmass : oracleRequestMass req ≤ 1 := by
    apply le_trans ?_ hcost
    unfold oracleRequestMass
    rw [← e.tsum_eq]
    simp only [req, Equiv.symm_apply_apply]
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro M
    unfold idealDyadicCoverCost
    rw [tsum_subtype (E M) (fun a : ℕ × ℕ ↦ (2 : ℝ≥0∞) ^ (-s * (a.2 : ℝ)))]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases ha : a ∈ E M
    · simp only [R, ha, ↓reduceIte, Option.elim_some, Set.indicator_of_mem ha]
      calc
        (2⁻¹ : ℝ≥0∞) ^ ⌈s * (a.2 : ℝ)⌉₊ =
            (2 : ℝ≥0∞) ^ (-((⌈s * (a.2 : ℝ)⌉₊ : ℕ) : ℝ)) := by
          rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
        _ ≤ (2 : ℝ≥0∞) ^ (-s * (a.2 : ℝ)) := by
          apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
          linarith [Nat.le_ceil (s * (a.2 : ℝ))]
    · simp [R, ha]
  let v : ℕ → ℕ → ℤ := fun n _ ↦ (Encodable.encode (req n) : ℤ)
  obtain ⟨A, _, _, hv⟩ := oracle_joins_tables ∅ (fun _ ↦ ∅) v
  have hcode : ComputableIn {charOracle A} (fun n ↦ Encodable.encode (req n)) := by
    have h := (ComputableReals.primrec_intToNat.to_comp.computableIn).comp
      (hv.comp (Computable.id.pair (Computable.const 0)).computableIn)
    simpa only [v, Int.toNat_natCast, id_eq] using h
  have hreq : ComputableIn {charOracle A} req := by
    have hd : Computable (fun n : ℕ ↦
        (Encodable.decode (α := Option (BitString × ℕ)) n).getD none) :=
      Computable.option_getD Computable.decode (Computable.const none)
    exact (hd.computableIn.comp hcode).of_eq fun n ↦ by simp
  obtain ⟨c, hc⟩ := oracle_kraftChaitin_bound A req hreq hmass
  refine ⟨A, (c : ℝ) + 1, ?_⟩
  intro M a ha
  have hreqval : req (e (M, a)) = some (natBits a.1, ⌈s * (a.2 : ℝ)⌉₊) := by
    simp [req, R, ha]
  have hb := hc _ _ _ hreqval
  have hbr : (oracleNatComplexity A a.1 : ℝ) ≤ (⌈s * (a.2 : ℝ)⌉₊ : ℕ) + (c : ℝ) := by
    exact_mod_cast hb
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hs (Nat.cast_nonneg a.2))
  linarith

/-- A point covered at unbounded precisions by balls whose centers have oracle complexity at
most linear in the precision, with slope `s`, has lower static dimension at most `s`. -/
private lemma iSup_staticPointDimensions_fst_le_of_cover_complexity
    (P : Presentation X) (Z : Set X) (s : ℝ)
    (E : ℕ → Set (ℕ × ℕ)) (hcov : ∀ M, IsIdealDyadicCover P Z M (E M))
    (A : Set ℕ) (c : ℝ)
    (hcomp : ∀ M : ℕ, ∀ a ∈ E M, (oracleNatComplexity A a.1 : ℝ) ≤ s * (a.2 : ℝ) + c) :
    (⨆ x ∈ Z, (staticPointDimensions P A x).1) ≤ ENNReal.ofReal s := by
  classical
  apply iSup₂_le
  intro x hx
  have hex : ∀ M : ℕ, ∃ a ∈ E M, dist (P.ι a.1) x < dyadicRadius a.2 := by
    intro M
    obtain ⟨a, ha, hax⟩ := Set.mem_iUnion₂.mp ((hcov M).2 hx)
    exact ⟨a, ha, by simpa only [Metric.mem_ball, dist_comm] using hax⟩
  choose a ha hax using hex
  have hr : Tendsto (fun M ↦ (a M).2) atTop atTop :=
    tendsto_atTop_mono (fun M ↦ (hcov M).1 _ (ha M)) tendsto_id
  have hscale := tendsto_dyadicRadius_nhdsGT.comp hr
  have hrealr : Tendsto (fun M ↦ ((a M).2 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  have hlim : Tendsto (fun M ↦ ENNReal.ofReal (s + c / ((a M).2 : ℝ)))
      atTop (𝓝 (ENNReal.ofReal s)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using
      tendsto_const_nhds.add (Tendsto.const_div_atTop hrealr c)
  have hnorm : ∀ᶠ M in atTop,
      normalizedPrecisionComplexity P A x (dyadicRadius (a M).2) ≤
        ENNReal.ofReal (s + c / ((a M).2 : ℝ)) := by
    filter_upwards [hr.eventually (eventually_ge_atTop 1)] with M hM
    have hpos : (0 : ℝ) < (a M).2 := by exact_mod_cast hM
    have hprec : precisionComplexityNat P A x (dyadicRadius (a M).2) ≤
        oracleNatComplexity A (a M).1 := by
      have hb : precisionComplexity P A x (dyadicRadius (a M).2) ≤
          (oracleNatComplexity A (a M).1 : ℕ∞) :=
        iInf_le_of_le _ (iInf_le_of_le (hax M) le_rfl)
      exact (ENat.toNat_le_toNat hb (ENat.natCast_ne_top _)).trans_eq
        (ENat.toNat_natCast _)
    have hcost : (precisionComplexityNat P A x (dyadicRadius (a M).2) : ℝ) ≤
        s * (a M).2 + c := by
      have hcast : (precisionComplexityNat P A x (dyadicRadius (a M).2) : ℝ) ≤
          (oracleNatComplexity A (a M).1 : ℝ) := by exact_mod_cast hprec
      exact hcast.trans (hcomp M _ (ha M))
    rw [normalizedPrecisionComplexity_dyadicRadius_eq_ofReal_div P A x _ hM]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (s * ((a M).2 : ℝ) + c) / ((a M).2 : ℝ) :=
        div_le_div_of_nonneg_right hcost hpos.le
      _ = s + c / ((a M).2 : ℝ) := by field_simp
  change liminf (normalizedPrecisionComplexity P A x) (𝓝[>] (0 : ℝ)) ≤ _
  calc
    _ ≤ liminf (fun M ↦ normalizedPrecisionComplexity P A x (dyadicRadius (a M).2))
        atTop := hscale.liminf_le_liminf_comp
    _ ≤ liminf (fun M ↦ ENNReal.ofReal (s + c / ((a M).2 : ℝ))) atTop :=
      liminf_le_liminf hnorm
    _ = ENNReal.ofReal s := hlim.liminf_eq

/-- If for every rational-like exponent `s > dimH Z` some oracle has point dimensions on `Z`
bounded by `s`, then one oracle has them bounded by `dimH Z`: join the oracles for `s = dimH Z +
1 / (n + 1)`. -/
private lemma exists_oracle_iSup_le_dimH_of_forall_gt (P : Presentation X) (Z : Set X)
    (h_bound : ∀ s : ℝ, 0 ≤ s → _root_.dimH Z < ENNReal.ofReal s →
      ∃ A : Set ℕ, (⨆ x ∈ Z, (staticPointDimensions P A x).1) ≤ ENNReal.ofReal s) :
    ∃ A : Set ℕ, (⨆ x ∈ Z, (staticPointDimensions P A x).1) ≤ _root_.dimH Z := by
  classical
  by_cases htop : dimH Z = ⊤
  · exact ⟨∅, htop ▸ le_top⟩
  let s : ℕ → ℝ := fun n ↦ (dimH Z).toReal + 1 / (n + 1 : ℝ)
  have hs : ∀ n, 0 ≤ s n := fun n ↦ by dsimp [s]; positivity
  have hgt : ∀ n, dimH Z < ENNReal.ofReal (s n) := by
    intro n
    rw [← ENNReal.ofReal_toReal htop]
    apply (ENNReal.ofReal_lt_ofReal_iff (by dsimp [s]; positivity)).mpr
    dsimp [s]
    linarith [show 0 < 1 / (n + 1 : ℝ) by positivity]
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (s n)) atTop (𝓝 (dimH Z)) := by
    rw [← ENNReal.ofReal_toReal htop]
    apply ENNReal.tendsto_ofReal
    dsimp [s]
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (dimH Z).toReal)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0))
  choose A hA using fun n ↦ h_bound (s n) (hs n) (hgt n)
  refine ⟨oracleCountableJoin A, ?_⟩
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  obtain ⟨c, hc⟩ := oracle_monotonicity (A n) (oracleCountableJoin A)
    (oracle_joins_countable A n)
  apply le_trans (iSup₂_mono fun x _ ↦ ?_) (hA n)
  change liminf (normalizedPrecisionComplexity P (oracleCountableJoin A) x) (𝓝[>] (0 : ℝ)) ≤
    liminf (normalizedPrecisionComplexity P (A n) x) (𝓝[>] (0 : ℝ))
  apply liminf_div_logb_le_of_le_add (precisionComplexityNat P (A n) x)
    (precisionComplexityNat P (oracleCountableJoin A) x) c
  exact precisionComplexityNat_le_of_oracleNatComplexity_le P (A n) (oracleCountableJoin A) c
    (fun i ↦ hc (natBits i)) x

/-- An oracle achieves the upper bound by Hausdorff dimension in the fixed presentation.
Blueprint node `conf:hausdorff-achieving`. -/
theorem hausdorffAchievingOracle (P : Presentation X) (Z : Set X) :
    ∃ A : Set ℕ, (⨆ x ∈ Z, (staticPointDimensions P A x).1) ≤ _root_.dimH Z := by
  apply exists_oracle_iSup_le_dimH_of_forall_gt P Z
  intro s hs h_dim
  obtain ⟨E, hcov, hcost⟩ := exists_idealDyadicCovers_with_summable_cost P Z s h_dim
  obtain ⟨A, c, hcomp⟩ := exists_oracle_bounding_cover_complexity s hs E hcost
  exact ⟨A, iSup_staticPointDimensions_fst_le_of_cover_complexity P Z s E hcov A c hcomp⟩

/-- The Hausdorff achieving bound remains valid above any oracle satisfying it.
Blueprint node `conf:hausdorff-achieving`. -/
theorem hausdorffAchievingOracle_stable (P : Presentation X) (Z : Set X) (A B : Set ℕ)
    (hA : (⨆ x ∈ Z, (staticPointDimensions P A x).1) ≤ _root_.dimH Z)
    (hAB : charOracle A ≤ᵀ charOracle B) :
    (⨆ x ∈ Z, (staticPointDimensions P B x).1) ≤ _root_.dimH Z := by
  obtain ⟨c, hc⟩ := oracle_monotonicity A B hAB
  have h_c_nat : ∀ i, oracleNatComplexity B i ≤ oracleNatComplexity A i + c :=
    fun i ↦ hc (natBits i)
  have h_pt : ∀ x ∈ Z, (staticPointDimensions P B x).1 ≤ (staticPointDimensions P A x).1 := by
    intro x _
    exact liminf_div_logb_le_of_le_add (precisionComplexityNat P A x)
      (precisionComplexityNat P B x) c
      (precisionComplexityNat_le_of_oracleNatComplexity_le P A B c h_c_nat x)
  exact (iSup₂_mono h_pt).trans hA

end Kolmogorov.PointToSet
