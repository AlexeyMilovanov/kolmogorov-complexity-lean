/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.BowenGeometry

/-!
# Null covers and lower topological pressure

A null cover of a set `Z` at exponent `s` is a set `E` of triples `(i, n, p)` of finite
`nullPressureMass` that covers `Z` by Bowen balls around ideal points at every small scale
`p` and arbitrarily large orders `n`.  This module compares such discrete covers with the
classical lower pressure `lowerPressure` defined through lower contents of countable Bowen
covers.

* `lowerPressure_le_of_nullCover` (blueprint node `pressure:null-to-lower`): a null
  `s`-cover bounds the lower pressure by `s`.
* `exists_nullCover_of_lowerPressure_lt` (blueprint node `pressure:lower-to-null`): every
  real exponent strictly above the lower pressure admits a null cover.
* `lowerPressure_eq_iInf_nullCover` (blueprint node `pressure:lower-discrete`): the lower
  pressure is the infimum of the exponents admitting a null cover.
* `effectiveLowerPressure_ge`, `effectiveLowerPressure_mono`,
  `effectiveLowerPressure_mono_oracle`, `effectiveLowerPressure_exists_cover` (blueprint node
  `pressure:effective-lower`): the effective lower pressure dominates the classical one, is
  monotone in the set, is antitone in the oracle, and is attained by effective null covers
  above its value.

These facts are the classical half of the point-to-set principle for lower pressure.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### A null cover bounds the lower pressure -/

/-- The Bowen family indexed by the triples `(i, n, p)` of `E` at scale `p` with order at least
`N`, centered at the ideal points `ι i`; the triples are coded by `Encodable.encode`. -/
private noncomputable def nullCoverSlice (D : PressureData X) (E : Set (ℕ × ℕ × ℕ))
    (p N : ℕ) : BowenCoverFamily X where
  index := Encodable.encode '' { t ∈ E | t.2.2 = p ∧ N ≤ t.2.1 }
  center j :=
    match (Encodable.decode j.val : Option (ℕ × ℕ × ℕ)) with
    | some t => D.presentation.ι t.1
    | none => D.presentation.ι 0
  order j :=
    match (Encodable.decode j.val : Option (ℕ × ℕ × ℕ)) with
    | some t => t.2.1
    | none => 1

private lemma nullCoverSlice_order (D : PressureData X) (E : Set (ℕ × ℕ × ℕ)) (p N : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ { t ∈ E | t.2.2 = p ∧ N ≤ t.2.1 }) :
    (nullCoverSlice D E p N).order ⟨Encodable.encode t, Set.mem_image_of_mem _ ht⟩ = t.2.1 := by
  simp only [nullCoverSlice, Encodable.encodek]

private lemma nullCoverSlice_center (D : PressureData X) (E : Set (ℕ × ℕ × ℕ)) (p N : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ { t ∈ E | t.2.2 = p ∧ N ≤ t.2.1 }) :
    (nullCoverSlice D E p N).center ⟨Encodable.encode t, Set.mem_image_of_mem _ ht⟩ =
      D.presentation.ι t.1 := by
  simp only [nullCoverSlice, Encodable.encodek]

/-- The slice of a null cover at scale `p` and order cutoff `N ≥ 1` is a Bowen cover of `Z`. -/
private lemma isBowenCover_nullCoverSlice (D : PressureData X) (Z : Set X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E)
    (p : ℕ) (hp : D.p₀ ≤ p) (N : ℕ) (hN : 1 ≤ N) :
    IsBowenCover D.T Z (dyadicRadius p) N (nullCoverSlice D E p N) := by
  constructor
  · rintro ⟨_, t, ht, rfl⟩
    rw [nullCoverSlice_order D E p N t ht]
    exact max_le (hN.trans ht.2.2) ht.2.2
  · intro x hx
    obtain ⟨i, n, hn, htE, hx_ball⟩ := hE.2.2 p hp N hN x hx
    refine Set.mem_iUnion.mpr ⟨⟨Encodable.encode (i, n, p),
      Set.mem_image_of_mem _ ⟨htE, rfl, hn⟩⟩, ?_⟩
    rw [nullCoverSlice_center D E p N _ ⟨htE, rfl, hn⟩,
      nullCoverSlice_order D E p N _ ⟨htE, rfl, hn⟩]
    exact hx_ball

/-- The cost of the slice of a null cover at exponent `t > s` is at most
`2 ^ (-(t - s) N)` times the mass of the cover. -/
private lemma bowenCoverCost_nullCoverSlice_le (D : PressureData X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ)) (p N : ℕ) (t : ℝ) (hst : s < t) :
    bowenCoverCost D.T D.φ .centered t (dyadicRadius p) (nullCoverSlice D E p N) ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) * nullPressureMass D.presentation D.T D.φ s E := by
  let F : Set (ℕ × ℕ × ℕ) := { x ∈ E | x.2.2 = p ∧ N ≤ x.2.1 }
  let e : F ≃ (nullCoverSlice D E p N).index :=
    Equiv.Set.image Encodable.encode F Encodable.encode_injective
  have hcost : bowenCoverCost D.T D.φ .centered t (dyadicRadius p) (nullCoverSlice D E p N) =
      ∑' x : F, (2 : ℝ≥0∞) ^ (-t * (x.val.2.1 : ℝ)) *
        (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ x.val.2.1 (D.presentation.ι x.val.1) := by
    rw [bowenCoverCost, ← e.tsum_eq]
    refine tsum_congr fun x ↦ ?_
    rw [show (nullCoverSlice D E p N).order (e x) = x.val.2.1 from
      nullCoverSlice_order D E p N x.val x.property,
      show (nullCoverSlice D E p N).center (e x) = D.presentation.ι x.val.1 from
      nullCoverSlice_center D E p N x.val x.property]
    rfl
  have hterm (x : F) : (2 : ℝ≥0∞) ^ (-t * (x.val.2.1 : ℝ)) *
        (2 : ℝ≥0∞) ^ birkhoffSum D.T D.φ x.val.2.1 (D.presentation.ι x.val.1) ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) *
        (2 : ℝ≥0∞) ^ (-s * (x.val.2.1 : ℝ) +
          birkhoffSum D.T D.φ x.val.2.1 (D.presentation.ι x.val.1)) := by
    have hN : (N : ℝ) ≤ x.val.2.1 := Nat.cast_le.mpr x.property.2.2
    have hexp : -(t - s) * (x.val.2.1 : ℝ) ≤ -(t - s) * (N : ℝ) := by nlinarith
    calc _ = (2 : ℝ≥0∞) ^ (-(t - s) * (x.val.2.1 : ℝ)) *
            (2 : ℝ≥0∞) ^ (-s * (x.val.2.1 : ℝ) +
              birkhoffSum D.T D.φ x.val.2.1 (D.presentation.ι x.val.1)) := by
          rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
            ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
          congr 1
          ring
      _ ≤ _ := by gcongr; norm_num
  rw [hcost]
  calc _ ≤ ∑' x : F, (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) *
          (2 : ℝ≥0∞) ^ (-s * (x.val.2.1 : ℝ) +
            birkhoffSum D.T D.φ x.val.2.1 (D.presentation.ι x.val.1)) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_left]
        exact mul_le_mul' le_rfl (ENNReal.tsum_mono_subtype
          (fun x : ℕ × ℕ × ℕ ↦ (2 : ℝ≥0∞) ^
            (-s * (x.2.1 : ℝ) + birkhoffSum D.T D.φ x.2.1 (D.presentation.ι x.1)))
          (fun x hx ↦ hx.1))

/-- For `a > 0` and finite `c`, the sequence `2 ^ (-a M) * c` tends to `0` as `M → ∞`. -/
private lemma tendsto_two_rpow_neg_mul_mul_const (c : ℝ≥0∞) (hc : c < ⊤) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun M : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * (M : ℝ)) * c) atTop (𝓝 0) := by
  have hreal : Tendsto (fun M : ℕ ↦ ((2 : ℝ) ^ (-a)) ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr ha))
  have hmul : Tendsto (fun M : ℕ ↦ (2 : ℝ≥0∞) ^ (-a * (M : ℝ))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_zero] at h
    refine h.congr fun M ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
      ← ENNReal.ofReal_rpow_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  simpa using ENNReal.Tendsto.mul_const hmul (Or.inr hc.ne)

/-- The lower content of a set with a null `s`-cover vanishes at every exponent `t > s`, every
scale `p ≥ p₀` and every cutoff `N ≥ 1`. -/
private lemma lowerContent_centered_eq_zero_of_nullCover (D : PressureData X) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ))
    (hE : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E)
    (p : ℕ) (hp : D.p₀ ≤ p) (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (hst : s < t) :
    lowerContent D.T D.φ .centered Z t (dyadicRadius p) N = 0 := by
  have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  have hbound (M : ℕ) (hM : N ≤ M) : lowerContent D.T D.φ .centered Z t (dyadicRadius p) N ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (M : ℝ)) * nullPressureMass D.presentation D.T D.φ s E := by
    have hM1 : 1 ≤ M := hN.trans hM
    calc _ ≤ lowerContent D.T D.φ .centered Z t (dyadicRadius p) M :=
          lowerContent_critical_mono_cutoff D .centered Z (dyadicRadius p) hr (D.ω p)
            (D.oscillation p hp) t N M hN hM
      _ ≤ bowenCoverCost D.T D.φ .centered t (dyadicRadius p) (nullCoverSlice D E p M) :=
          iInf₂_le _ (isBowenCover_nullCoverSlice D Z s E hE p hp M hM1)
      _ ≤ _ := bowenCoverCost_nullCoverSlice_le D s E p M t hst
  have hlim := tendsto_two_rpow_neg_mul_mul_const _ hE.2.1 (t - s) (sub_pos.mpr hst)
  exact le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨N, hbound⟩)) bot_le

/-- If a set has a null `s`-cover, its centered lower content limit vanishes at every exponent
`t > s` and every scale `p ≥ p₀`.  Blueprint node `pressure:null-to-lower`. -/
lemma lowerContentLimit_centered_eq_zero_of_nullCover (D : PressureData X) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ))
    (hE : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E)
    (p : ℕ) (hp : D.p₀ ≤ p) (t : ℝ) (hst : s < t) :
    lowerContentLimit D.T D.φ .centered Z t (dyadicRadius p) = 0 :=
  le_antisymm (iSup₂_le fun N hN ↦
    (lowerContent_centered_eq_zero_of_nullCover D Z s E hE p hp N hN t hst).le) bot_le

/-- A null `s`-cover bounds the centered critical value at every scale `p ≥ p₀` by `s`. -/
private lemma lowerPressureAt_centered_le_of_nullCover (D : PressureData X) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ))
    (hE : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E)
    (p : ℕ) (hp : D.p₀ ≤ p) :
    lowerPressureAt D.T D.φ .centered Z (dyadicRadius p) ≤ (s : EReal) := by
  by_contra hlt
  obtain ⟨t, hst, hta⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
  have hle : lowerPressureAt D.T D.φ .centered Z (dyadicRadius p) ≤ (t : EReal) :=
    iInf₂_le t (lowerContentLimit_centered_eq_zero_of_nullCover D Z s E hE p hp t
      (EReal.coe_lt_coe_iff.mp hst))
  exact absurd hta (not_lt.mpr hle)

/-- A discrete null cover bounds classical lower pressure.
Blueprint node `pressure:null-to-lower`. -/
theorem lowerPressure_le_of_nullCover (D : PressureData X) (Z : Set X) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ))
    (hE : IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E) :
    lowerPressure D.T D.φ D.p₀ Z ≤ (s : EReal) :=
  iSup₂_le fun p hp ↦ lowerPressureAt_centered_le_of_nullCover D Z s E hE p hp

/-! ### A null cover above the lower pressure -/

/-- Along a sequence of scales `q p ≥ p + 1` beyond `p₀`, the oscillation bound of the potential
stays below `s - a` once `a < s`. -/
private lemma exists_scale_seq_omega_lt (D : PressureData X) (a s : ℝ) (has : a < s) :
    ∃ q : ℕ → ℕ, ∀ p, p + 1 ≤ q p ∧ D.p₀ ≤ q p ∧ D.ω (q p) < s - a := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp D.ω_tendsto).2 (s - a)
    (sub_pos.mpr has))
  exact ⟨fun p ↦ max (p + 1) (max D.p₀ M), fun p ↦ ⟨le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),
    hM _ ((le_max_right _ _).trans (le_max_right _ _))⟩⟩

/-- If the lower pressure is below `a`, then for every scale sequence `q` beyond `p₀` and every
`p, k` there is a Bowen cover at radius `dyadicRadius (q p)` with orders at least `k + 1` whose
centered `a`-cost is below `2 ^ (-p - k - 2)`. -/
private lemma exists_bowenCover_cost_lt (D : PressureData X) (Z : Set X) (a : ℝ)
    (ha : lowerPressure D.T D.φ D.p₀ Z < (a : EReal)) (q : ℕ → ℕ) (hq : ∀ p, D.p₀ ≤ q p) :
    ∃ C : ℕ → ℕ → BowenCoverFamily X, ∀ p k,
      IsBowenCover D.T Z (dyadicRadius (q p)) (k + 1) (C p k) ∧
        bowenCoverCost D.T D.φ .centered a (dyadicRadius (q p)) (C p k) <
          (2 : ℝ≥0∞) ^ (-(p : ℝ) - k - 2) := by
  have hchoose (p k : ℕ) : ∃ C : BowenCoverFamily X,
      IsBowenCover D.T Z (dyadicRadius (q p)) (k + 1) C ∧
        bowenCoverCost D.T D.φ .centered a (dyadicRadius (q p)) C <
          (2 : ℝ≥0∞) ^ (-(p : ℝ) - k - 2) := by
    have hr : 0 < dyadicRadius (q p) := by unfold dyadicRadius; positivity
    have hscale : lowerPressureAt D.T D.φ .centered Z (dyadicRadius (q p)) ≤
        lowerPressure D.T D.φ D.p₀ Z :=
      le_iSup₂_of_le (q p) (hq p) le_rfl
    have hω : ∀ x y, dist x y < dyadicRadius (q p) → |D.φ x - D.φ y| ≤ D.ω (q p) :=
      fun x y hxy ↦ D.oscillation (q p) (hq p) x y hxy
    have hzero := lowerContent_critical_zero D .centered Z _ hr _ hω a (hscale.trans_lt ha)
    exact lowerContent_critical_cover D .centered Z _ hr _ hω a hzero (k + 1) (by omega) _
      (by positivity)
  choose C hC using hchoose
  exact ⟨C, hC⟩

/-- Dyadic radii: `2 * dyadicRadius q ≤ dyadicRadius p` as soon as `p + 1 ≤ q`. -/
private lemma two_mul_dyadicRadius_le {p q : ℕ} (h : p + 1 ≤ q) :
    2 * dyadicRadius q ≤ dyadicRadius p := by
  have hpow : (2 : ℝ)⁻¹ ^ q ≤ (2 : ℝ)⁻¹ ^ (p + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  calc 2 * dyadicRadius q ≤ 2 * (2 : ℝ)⁻¹ ^ (p + 1) := by unfold dyadicRadius; gcongr
    _ = dyadicRadius p := by unfold dyadicRadius; rw [pow_succ]; field_simp

/-- The triples `(i p k j, order j, p)` with `p ≥ p₀` read off from recentered Bowen families
`C p k`. -/
private def recenteredTriples (C : ℕ → ℕ → BowenCoverFamily X)
    (i : (p k : ℕ) → (C p k).index → ℕ) (p₀ : ℕ) : Set (ℕ × ℕ × ℕ) :=
  { t | ∃ (p : ℕ) (_ : p₀ ≤ p) (k : ℕ) (j : (C p k).index),
    t = (i p k j, (C p k).order j, p) }

/-- Recentering a Bowen ball of order `n ≥ 1` at an ideal point within the dyadic radius
`dyadicRadius q`, where `ω q < s - a`, does not increase the `s`-weight beyond the `a`-weight
at the original center. -/
private lemma two_rpow_neg_mul_add_birkhoffSum_le (D : PressureData X) (a s : ℝ) (q : ℕ)
    (hq : D.p₀ ≤ q) (h_omega : D.ω q < s - a) (n : ℕ) (hn : 1 ≤ n) (y : X) (i : ℕ)
    (h_dist : bowenDist D.T n y (D.presentation.ι i) < dyadicRadius q) :
    (2 : ℝ≥0∞) ^ (-s * (n : ℝ) + birkhoffSum D.T D.φ n (D.presentation.ι i)) ≤
      (2 : ℝ≥0∞) ^ (-a * (n : ℝ) + birkhoffSum D.T D.φ n y) := by
  have hz : D.presentation.ι i ∈ bowenBall D.T n y (dyadicRadius q) :=
    (bowen_ball_dense_iff D.T n hn y _ _).mpr h_dist
  have hsum := (abs_le.mp (recenter_bowen_cover_distortion D q hq n hn y _ hz)).2
  have hmul := mul_lt_mul_of_pos_left h_omega (by exact_mod_cast hn : (0 : ℝ) < n)
  exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- The mass of the recentered triples is at most the sum of the centered `a`-costs of the
families `C p k`, taken at the radii `dyadicRadius (q p)`. -/
private lemma nullPressureMass_recenteredTriples_le (D : PressureData X)
    (C : ℕ → ℕ → BowenCoverFamily X) (i : (p k : ℕ) → (C p k).index → ℕ)
    (a s : ℝ) (q : ℕ → ℕ) (hq1 : ∀ p, D.p₀ ≤ q p) (hq2 : ∀ p, D.ω (q p) < s - a)
    (hC_order : ∀ p k j, 1 ≤ (C p k).order j)
    (h_dist : ∀ p k j, bowenDist D.T ((C p k).order j) ((C p k).center j)
      (D.presentation.ι (i p k j)) < dyadicRadius (q p)) :
    nullPressureMass D.presentation D.T D.φ s (recenteredTriples C i D.p₀) ≤
      ∑' (p : ℕ) (k : ℕ), bowenCoverCost D.T D.φ .centered a (dyadicRadius (q p)) (C p k) := by
  let f : (Σ p : {p : ℕ // D.p₀ ≤ p}, Σ k : ℕ, (C p.1 k).index) →
      recenteredTriples C i D.p₀ := fun w ↦
    ⟨(i w.1.1 w.2.1 w.2.2, (C w.1.1 w.2.1).order w.2.2, w.1.1),
      ⟨w.1.1, w.1.2, w.2.1, w.2.2, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨_, p, hp, k, j, rfl⟩
    exact ⟨⟨⟨p, hp⟩, ⟨k, j⟩⟩, rfl⟩
  let g : recenteredTriples C i D.p₀ → ℝ≥0∞ := fun t ↦ (2 : ℝ≥0∞) ^
    (-s * (t.val.2.1 : ℝ) + birkhoffSum D.T D.φ t.val.2.1 (D.presentation.ι t.val.1))
  have hcost (p : {p : ℕ // D.p₀ ≤ p}) (k : ℕ) :
      ∑' j : (C p.1 k).index, g (f ⟨p, k, j⟩) ≤
        bowenCoverCost D.T D.φ .centered a (dyadicRadius (q p.1)) (C p.1 k) := by
    refine ENNReal.tsum_le_tsum fun j ↦ ?_
    refine (two_rpow_neg_mul_add_birkhoffSum_le D a s (q p.1) (hq1 p.1) (hq2 p.1) _
      (hC_order p.1 k j) _ _ (h_dist p.1 k j)).trans_eq ?_
    simp only [pressureBallWeight]
    rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  calc nullPressureMass D.presentation D.T D.φ s (recenteredTriples C i D.p₀)
      = ∑' t : recenteredTriples C i D.p₀, g t := rfl
    _ ≤ ∑' w, g (f w) := ENNReal.tsum_le_tsum_comp_of_surjective hsurj g
    _ = ∑' (p : {p : ℕ // D.p₀ ≤ p}) (k : ℕ), ∑' j : (C p.1 k).index, g (f ⟨p, k, j⟩) := by
        simp only [ENNReal.tsum_sigma']
    _ ≤ ∑' (p : {p : ℕ // D.p₀ ≤ p}) (k : ℕ),
          bowenCoverCost D.T D.φ .centered a (dyadicRadius (q p.1)) (C p.1 k) :=
        ENNReal.tsum_le_tsum fun p ↦ ENNReal.tsum_le_tsum (hcost p)
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (f := Subtype.val) Subtype.val_injective
        (fun p ↦ ∑' k : ℕ, bowenCoverCost D.T D.φ .centered a (dyadicRadius (q p)) (C p k))

/-- The double geometric series `∑ₚ ∑ₖ 2 ^ (-p - k - 2)` is finite. -/
private lemma tsum_tsum_two_rpow_neg_lt_top :
    (∑' (p : ℕ) (k : ℕ), (2 : ℝ≥0∞) ^ (-(p : ℝ) - k - 2)) < ⊤ := by
  have hterm (p k : ℕ) : (2 : ℝ≥0∞) ^ (-(p : ℝ) - k - 2) =
      (2 : ℝ≥0∞)⁻¹ ^ p * (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞)⁻¹ ^ 2 := by
    have he : -(p : ℝ) - k - 2 = -((p + k + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [he, ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow, pow_add, pow_add]
  simp_rw [hterm, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric_two]
  finiteness

/-- The recentered triples cover `Z` at every scale `p ≥ p₀` and every cutoff `N ≥ 1`: the
family `C p N` covers `Z`, and its recentered balls of radius `2 * dyadicRadius (q p)` lie in
the balls of radius `dyadicRadius p`. -/
private lemma exists_mem_recenteredTriples_of_mem (D : PressureData X) (Z : Set X)
    (C : ℕ → ℕ → BowenCoverFamily X) (i : (p k : ℕ) → (C p k).index → ℕ) (q : ℕ → ℕ)
    (hq : ∀ p, p + 1 ≤ q p)
    (hC_cover : ∀ p k, IsBowenCover D.T Z (dyadicRadius (q p)) (k + 1) (C p k))
    (h_subset : ∀ p k j, bowenBall D.T ((C p k).order j) ((C p k).center j) (dyadicRadius (q p)) ⊆
      bowenBall D.T ((C p k).order j) (D.presentation.ι (i p k j)) (2 * dyadicRadius (q p))) :
    ∀ p ≥ D.p₀, ∀ N ≥ 1, ∀ x ∈ Z, ∃ idx n, N ≤ n ∧ (idx, n, p) ∈ recenteredTriples C i D.p₀ ∧
      x ∈ bowenBall D.T n (D.presentation.ι idx) (dyadicRadius p) := by
  intro p hp N _ x hx
  obtain ⟨h_order, h_cover⟩ := hC_cover p N
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h_cover hx)
  exact ⟨i p N j, (C p N).order j,
    (Nat.le_succ N).trans ((le_max_right _ _).trans (h_order j)), ⟨p, hp, N, j, rfl⟩,
    bowenBall_subset_of_le _ _ _ (two_mul_dyadicRadius_le (hq p)) (h_subset p N j hj)⟩

/-- Every real exponent strictly above classical lower pressure has a null cover.
Blueprint node `pressure:lower-to-null`. -/
theorem exists_nullCover_of_lowerPressure_lt (D : PressureData X) (Z : Set X) (s : ℝ)
    (hs : lowerPressure D.T D.φ D.p₀ Z < (s : EReal)) :
    ∃ E, IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E := by
  obtain ⟨a, ha, has⟩ := EReal.lt_iff_exists_real_btwn.mp hs
  have has : a < s := EReal.coe_lt_coe_iff.mp has
  obtain ⟨q, hq⟩ := exists_scale_seq_omega_lt D a s has
  obtain ⟨C, hC⟩ := exists_bowenCover_cost_lt D Z a ha q fun p ↦ (hq p).2.1
  have hC_order (p k j) : 1 ≤ (C p k).order j :=
    (le_max_left 1 (k + 1)).trans ((hC p k).1.1 j)
  have hrecenter (p k : ℕ) := recenter_bowen_cover D (C p k) (hC_order p k)
    (dyadicRadius (q p)) (by unfold dyadicRadius; positivity)
  choose i hi using hrecenter
  refine ⟨recenteredTriples C i D.p₀, ?_, ?_, ?_⟩
  · rintro t ⟨p, hp0, k, j, rfl⟩
    exact ⟨hC_order p k j, hp0⟩
  · refine lt_of_le_of_lt
      (nullPressureMass_recenteredTriples_le D C i a s q (fun p ↦ (hq p).2.1)
        (fun p ↦ (hq p).2.2) hC_order fun p k j ↦ (hi p k j).1) ?_
    exact (ENNReal.tsum_le_tsum fun p ↦ ENNReal.tsum_le_tsum fun k ↦ (hC p k).2.le).trans_lt
      tsum_tsum_two_rpow_neg_lt_top
  · exact exists_mem_recenteredTriples_of_mem D Z C i q (fun p ↦ (hq p).1)
      (fun p k ↦ (hC p k).1) fun p k j ↦ (hi p k j).2

/-- Discrete null covers recover the signed lower pressure, including infinite endpoints.
Blueprint node `pressure:lower-discrete`. -/
theorem lowerPressure_eq_iInf_nullCover (D : PressureData X) (Z : Set X) :
    lowerPressure D.T D.φ D.p₀ Z =
      ⨅ s : ℝ, ⨅ (_ : ∃ E, IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E),
        (s : EReal) := by
  refine le_antisymm (le_iInf₂ fun s hE ↦ ?_) ?_
  · obtain ⟨E, hE⟩ := hE
    exact lowerPressure_le_of_nullCover D Z s E hE
  · by_contra hlt
    obtain ⟨s, hs, hsR⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
    exact absurd hsR (not_lt.mpr (iInf₂_le s (exists_nullCover_of_lowerPressure_lt D Z s hs)))

/-! ### Effective lower pressure -/

/-- Restricting null covers to an oracle's enumerable sets increases the critical value.
Blueprint node `pressure:effective-lower`. -/
theorem effectiveLowerPressure_ge (D : PressureData X) (A : Set ℕ) (Z : Set X) :
    lowerPressure D.T D.φ D.p₀ Z ≤
      effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z := by
  rw [lowerPressure_eq_iInf_nullCover, effectiveLowerPressure]
  refine iInf_mono fun s ↦ le_iInf₂ fun E h ↦ ?_
  exact iInf_le_of_le ⟨E, h.1⟩ le_rfl

/-- Effective lower pressure is monotone in the covered set.
Blueprint node `pressure:effective-lower`. -/
theorem effectiveLowerPressure_mono (D : PressureData X) (A : Set ℕ)
    (Z Y : Set X) (hZY : Z ⊆ Y) :
    effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z ≤
      effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Y := by
  refine iInf_mono fun s ↦ iInf_mono fun E ↦ le_iInf fun h ↦ ?_
  obtain ⟨⟨h1, h2, h3⟩, hRE⟩ := h
  exact iInf_le_of_le ⟨⟨h1, h2, fun p hp N hN x hx ↦ h3 p hp N hN x (hZY hx)⟩, hRE⟩ le_rfl

/-- Strengthening the oracle decreases effective lower pressure.
Blueprint node `pressure:effective-lower`. -/
theorem effectiveLowerPressure_mono_oracle (D : PressureData X) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (Z : Set X) :
    effectiveLowerPressure D.presentation D.T D.φ D.p₀ B Z ≤
      effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z := by
  refine le_iInf fun s ↦ le_iInf fun E ↦ le_iInf fun hA ↦ ?_
  exact (iInf_le _ s).trans ((iInf_le _ E).trans
    (iInf_le _ ⟨hA.1, hA.2.mono_oracle hAB⟩))

/-- Every exponent above the effective infimum has an actual effective null cover.
Blueprint node `pressure:effective-lower`. -/
theorem effectiveLowerPressure_exists_cover (D : PressureData X) (A : Set ℕ)
    (Z : Set X) (s : ℝ)
    (hs : effectiveLowerPressure D.presentation D.T D.φ D.p₀ A Z < (s : EReal)) :
    ∃ E, IsNullPressureCover D.presentation D.T D.φ D.p₀ Z s E ∧ IsREIn A E := by
  obtain ⟨s', hs'⟩ := iInf_lt_iff.mp hs
  obtain ⟨E, hE⟩ := iInf_lt_iff.mp hs'
  obtain ⟨⟨h_cov, h_RE⟩, hs'_lt_s⟩ := iInf_lt_iff.mp hE
  refine ⟨E, ⟨h_cov.1, ?_, h_cov.2.2⟩, h_RE⟩
  have hs_lt : s' < s := EReal.coe_lt_coe_iff.mp hs'_lt_s
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun t ↦ ?_) h_cov.2.1
  refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
  have h1 : 1 ≤ (t.val.2.1 : ℝ) := by exact_mod_cast (h_cov.1 t.val t.property).1
  nlinarith

end Kolmogorov.PointToSet
