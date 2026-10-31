/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyPointToSet

/-!
# Orbit complexity of isometries and of the symbolic shift

This module evaluates the pointwise orbit complexities `orbitComplexities` in two model
situations.

* For an isometry every point of the space is shadowed by a single ideal point at all times,
  so the orbit complexity rates vanish and `lowerEntropy_isometry` shows that the lower
  entropy of the whole space is zero (blueprint node `pressure:isometry`, a corollary of the
  effective characterization of lower entropy by pointwise orbit complexities).
* For the one-sided shift on `ℕ → α` with the geometric first-difference metric
  `dist x y = β ^ firstDiff x y`, the strict Bowen ball of order `n` and radius `β ^ k` is the
  ball of radius `β ^ (n + k - 1)` (`symbolic_orbitComplexity`).  Consequently the lower and
  upper orbit complexities are `-log₂ β` times the lower and upper static point dimensions
  (`symbolic_orbitComplexity_lower`, `symbolic_orbitComplexity_upper`).  The proof compares
  the dyadic scales defining the orbit complexities with the geometric scales `β ^ k` and
  uses the sampling invariance `dimension_along_scales` of the static dimensions
  (blueprint node `pressure:symbolic`).
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### Finite scale costs with the constant potential one -/

/-- With the constant potential one, the Birkhoff sum of order `n` is `n`. -/
private lemma birkhoffSum_const_one {Y : Type*} (T : Y → Y) (n : ℕ) (y : Y) :
    birkhoffSum T (fun _ ↦ (1 : ℝ)) n y = n := by
  simp only [birkhoffSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- At a positive order, the finite scale cost with the constant potential one is the infimum
of the oracle complexities of the ideal points in the Bowen ball, divided by the order. -/
private lemma finiteScaleBSCost_one_eq (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)
    {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    finiteScaleBSCost P T (fun _ ↦ 1) A x n r =
      ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x r), (oracleNatComplexity A i : ℝ≥0∞) / n := by
  have hn0 : n ≠ 0 := by omega
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [finiteScaleBSCost, hn0, ↓reduceIte, birkhoffSum_const_one, hpos, iInf_pos,
    ENNReal.ofReal_natCast]

/-- For an antitone function of the radius, the supremum over the dyadic radii equals the
supremum over the powers of any `β ∈ (0, 1)`. -/
private lemma iSup_dyadicRadius_eq_iSup_pow {F : ℝ → ℝ≥0∞} (hF : Antitone F) {β : ℝ}
    (hβ : 0 < β) (hβ₁ : β < 1) : ⨆ p : ℕ, F (dyadicRadius p) = ⨆ k : ℕ, F (β ^ k) := by
  refine le_antisymm (iSup_le fun p ↦ ?_) (iSup_le fun k ↦ ?_)
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) p) hβ₁
    exact (hF hk.le).trans (le_iSup (fun k ↦ F (β ^ k)) k)
  · obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one (pow_pos hβ k) (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact (hF hp.le).trans (le_iSup (fun p ↦ F (dyadicRadius p)) p)

/-! ### Isometries -/

/-- Iterates of an isometry are isometries. -/
private lemma isometry_iterate {Y : Type*} [PseudoEMetricSpace Y] {T : Y → Y}
    (hT : Isometry T) (k : ℕ) : Isometry T^[k] := by
  induction k with
  | zero => exact isometry_id
  | succ k ih =>
    rw [Function.iterate_succ]
    exact ih.comp hT

/-- If `T` is an isometry, one ideal point close to `x` stays equally close along the whole
orbit, so the finite scale cost at a fixed dyadic scale is at most a constant divided by the
order. -/
private lemma exists_finiteScaleBSCost_le_div_of_isometry (P : Presentation X) (T : X → X)
    (hT : Isometry T) (A : Set ℕ) (x : X) (p : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n →
      finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) ≤ (c : ℝ≥0∞) / n := by
  obtain ⟨i, hi⟩ := P.dense.exists_dist_lt x (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) p)
  refine ⟨oracleNatComplexity A i, fun n hn ↦ ?_⟩
  rw [finiteScaleBSCost_one_eq P T A x hn]
  refine iInf₂_le_of_le i ?_ le_rfl
  rw [bowenBall, Set.mem_ofPred_eq, Dynamics.mem_dynEntourage]
  intro k _
  rw [Set.mem_ofPred_eq, (isometry_iterate hT k).dist_eq]
  exact hi

/-- A sequence of extended nonnegative reals bounded by `c / n` has lower limit zero. -/
private lemma liminf_eq_zero_of_le_div (u : ℕ → ℝ≥0∞) (c : ℕ)
    (hu : ∀ n : ℕ, 1 ≤ n → u n ≤ (c : ℝ≥0∞) / n) : liminf u atTop = 0 := by
  have hlim : Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (ENNReal.natCast_ne_top c))
  refine le_antisymm ?_ bot_le
  calc liminf u atTop ≤ liminf (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop :=
        liminf_le_liminf (eventually_atTop.2 ⟨1, hu⟩)
    _ = 0 := hlim.liminf_eq

/-- For an isometry, the lower orbit complexity rate of every point vanishes for every
oracle. -/
private lemma orbitComplexities_fst_eq_zero_of_isometry (P : Presentation X) (T : X → X)
    (hT : Isometry T) (A : Set ℕ) (x : X) : (orbitComplexities P T A x).1 = 0 := by
  refine le_antisymm (iSup_le fun p ↦ ?_) bot_le
  obtain ⟨c, hc⟩ := exists_finiteScaleBSCost_le_div_of_isometry P T hT A x p
  exact (liminf_eq_zero_of_le_div _ c hc).le

/-- An isometry has zero lower entropy on the nonempty presented space.
Blueprint node `pressure:isometry`. -/
theorem lowerEntropy_isometry (P : Presentation X) (T : X → X) (hT : Isometry T) :
    lowerEntropy T Set.univ = 0 := by
  have : Nonempty X := ⟨P.ι 0⟩
  rw [entropy_effectiveCharacterization_allOracles_pointToSet P T hT.continuous Set.univ]
  simp only [Set.mem_univ, iSup_pos, orbitComplexities_fst_eq_zero_of_isometry P T hT,
    iSup_const, ciInf_const]

/-! ### Strict Bowen balls of the shift -/

/-- Iterating the one-sided shift `j` times drops the first `j` coordinates. -/
private lemma shift_iterate_apply {α : Type*} (x : ℕ → α) (j : ℕ) :
    (fun (y : ℕ → α) i ↦ y (i + 1))^[j] x = fun i ↦ x (i + j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext i
    exact congrArg x (by omega)

/-- In the geometric first-difference metric, two sequences are at distance less than
`β ^ m` exactly when they agree at all positions up to `m`. -/
private lemma dist_lt_pow_iff {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ} (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (x y : ℕ → α) (m : ℕ) : dist x y < β ^ m ↔ ∀ i ≤ m, x i = y i := by
  by_cases hxy : x = y
  · subst hxy
    simpa only [dist_self, implies_true, iff_true] using pow_pos hβ m
  · rw [hd x y hxy, pow_lt_pow_iff_right_of_lt_one₀ hβ hβ₁]
    refine ⟨fun h i hi ↦ PiNat.apply_eq_of_lt_firstDiff (hi.trans_lt h), fun h ↦ ?_⟩
    by_contra hle
    exact PiNat.apply_firstDiff_ne hxy (h _ (not_lt.mp hle))

/-- A point lies in the strict Bowen ball of the shift of order `n ≥ 1` and radius `β ^ k`
exactly when it agrees with the center at all positions up to `n + k - 1`. -/
private lemma mem_bowenBall_shift_iff {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ}
    (hβ : 0 < β) (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (x y : ℕ → α) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    y ∈ bowenBall (fun (y : ℕ → α) j ↦ y (j + 1)) n x (β ^ k) ↔
      ∀ i ≤ n + k - 1, x i = y i := by
  rw [bowenBall, Set.mem_ofPred_eq, Dynamics.mem_dynEntourage]
  simp only [Set.mem_ofPred_eq, shift_iterate_apply, dist_lt_pow_iff hβ hβ₁ hd]
  refine ⟨fun H i hi ↦ ?_, fun H j hj i hi ↦ H (i + j) (by omega)⟩
  by_cases hin : i < n
  · simpa using H i hin 0 k.zero_le
  · have := H (n - 1) (by omega) (i - (n - 1)) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this

/-- Strict symbolic Bowen balls observe `n - 1` transitions, giving exponent `n + k - 1`.
The distance hypothesis specifies exactly the geometric first-difference metric.
Blueprint node `pressure:symbolic`. -/
theorem symbolic_orbitComplexity {α : Type*} [MetricSpace (ℕ → α)] (β : ℝ) (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (x : ℕ → α) (n k : ℕ) (hn : 1 ≤ n) :
    bowenBall (fun y j => y (j + 1)) n x (β ^ k) = Metric.ball x (β ^ (n + k - 1)) := by
  ext y
  rw [mem_bowenBall_shift_iff hβ hβ₁ hd x y hn k, Metric.mem_ball, dist_comm,
    dist_lt_pow_iff hβ hβ₁ hd]

/-- Under the shift, the finite scale cost at scale `β ^ k` and order `n ≥ 1` is the precision
complexity at scale `β ^ (n + k - 1)` divided by `n`. -/
private lemma finiteScaleBSCost_shift_eq {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ} (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ) (x : ℕ → α) (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    finiteScaleBSCost P (fun y j ↦ y (j + 1)) (fun _ ↦ 1) A x n (β ^ k) =
      (precisionComplexityNat P A x (β ^ (n + k - 1)) : ℝ≥0∞) / n := by
  rw [finiteScaleBSCost_one_eq P _ A x hn, symbolic_orbitComplexity β hβ hβ₁ hd x n k hn]
  obtain ⟨i, hi, hprec⟩ := staticPointDimensions_attained P A x _ (pow_pos hβ (n + k - 1))
  have hK : precisionComplexityNat P A x (β ^ (n + k - 1)) = oracleNatComplexity A i := by
    rw [precisionComplexityNat, hprec, ENat.toNat_natCast]
  rw [hK]
  refine le_antisymm (iInf₂_le_of_le i hi le_rfl) (le_iInf₂ fun j hj ↦
    ENNReal.div_le_div_right ?_ _)
  have hle : precisionComplexity P A x (β ^ (n + k - 1)) ≤ oracleNatComplexity A j :=
    iInf₂_le_of_le j hj le_rfl
  rw [hprec] at hle
  exact_mod_cast hle

/-! ### Extended real arithmetic for the normalization by `-log₂ β` -/

/-- The normalizing constant `-log₂ β` is positive for `β ∈ (0, 1)`. -/
private lemma ofReal_neg_logb_ne_zero {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    ENNReal.ofReal (-Real.logb 2 β) ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le, neg_pos]
  exact Real.logb_neg one_lt_two hβ hβ₁

/-- The normalizing denominator at the `m`-th power of `β` is `m` times the one at `β`. -/
private lemma ofReal_neg_logb_pow (β : ℝ) (m : ℕ) :
    ENNReal.ofReal (-Real.logb 2 (β ^ m)) = ENNReal.ofReal (-Real.logb 2 β) * m := by
  have h : -Real.logb 2 (β ^ m) = m * -Real.logb 2 β := by
    rw [Real.logb, Real.logb, Real.log_pow]
    ring
  rw [h, ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast, mul_comm]

/-- The constant `-log₂ β` times the normalized precision complexity at `β ^ m` is the
precision complexity divided by `m`. -/
private lemma const_mul_normalizedPrecisionComplexity_pow {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1)
    (P : Presentation X) (A : Set ℕ) (x : X) (m : ℕ) :
    ENNReal.ofReal (-Real.logb 2 β) * normalizedPrecisionComplexity P A x (β ^ m) =
      (precisionComplexityNat P A x (β ^ m) : ℝ≥0∞) / m := by
  rw [normalizedPrecisionComplexity, ofReal_neg_logb_pow, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ofReal_neg_logb_ne_zero hβ hβ₁) ENNReal.ofReal_ne_top]

/-- Dividing by `n` rather than by `m ≠ 0` multiplies by `m / n`. -/
private lemma div_eq_natCast_div_mul_div (K : ℝ≥0∞) {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    K / n = (m : ℝ≥0∞) / n * (K / m) := by
  have h0 : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc K * (n : ℝ≥0∞)⁻¹
      = K * (n : ℝ≥0∞)⁻¹ * (m * (m : ℝ≥0∞)⁻¹) := by
        rw [ENNReal.mul_inv_cancel h0 (ENNReal.natCast_ne_top m), mul_one]
    _ = (m : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * (K * (m : ℝ≥0∞)⁻¹) := by ring

/-- The ratio `(n + k - 1) / n` of natural numbers tends to one in `ℝ≥0∞`. -/
private lemma tendsto_natCast_add_sub_one_div (k : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n + k - 1 : ℕ) : ℝ≥0∞) / n) atTop (𝓝 1) := by
  have hreal : Tendsto (fun n : ℕ ↦ ((n + k - 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ ↦ 1 + ((k : ℝ) - 1) / n) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have h := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- Multiplying a sequence by a factor tending to one does not change its lower limit. -/
private lemma liminf_mul_of_tendsto_one {u a : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 1)) :
    liminf (fun n ↦ a n * u n) atTop = liminf u atTop := by
  refine le_antisymm ?_ ?_
  · have h := ENNReal.liminf_mul_le (u := a) (v := u) (f := atTop)
      (Or.inl (by rw [ha.limsup_eq]; exact one_ne_zero))
      (Or.inl (by rw [ha.limsup_eq]; exact ENNReal.one_ne_top))
    rwa [ha.limsup_eq, one_mul] at h
  · have h := ENNReal.le_liminf_mul (u := a) (v := u) (f := atTop)
    rwa [ha.liminf_eq, one_mul] at h

/-- Multiplying a sequence by a factor tending to one does not change its upper limit. -/
private lemma limsup_mul_of_tendsto_one {u a : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 1)) :
    limsup (fun n ↦ a n * u n) atTop = limsup u atTop := by
  refine le_antisymm ?_ ?_
  · have h := ENNReal.limsup_mul_le' (u := a) (v := u) (f := atTop)
      (Or.inl (by rw [ha.limsup_eq]; exact one_ne_zero))
      (Or.inl (by rw [ha.limsup_eq]; exact ENNReal.one_ne_top))
    rwa [ha.limsup_eq, one_mul] at h
  · have h := ENNReal.le_limsup_mul (u := u) (v := a) (f := atTop)
    rw [ha.liminf_eq, mul_one] at h
    exact h.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ mul_comm (u n) (a n)))

/-- The map `n ↦ n + k - 1` sends `atTop` to `atTop`. -/
private lemma map_add_sub_one_atTop (k : ℕ) : map (fun n : ℕ ↦ n + k - 1) atTop = atTop := by
  have h : (fun n : ℕ ↦ n + k - 1) = (fun n ↦ n - 1) ∘ (fun n ↦ n + k) := rfl
  rw [h, ← Filter.map_map, map_add_atTop_eq_nat, map_sub_atTop_eq_nat]

/-- The lower limit of `K (n + k - 1) / n` equals the lower limit of `K m / m`. -/
private lemma liminf_div_add_sub_one (K : ℕ → ℝ≥0∞) (k : ℕ) :
    liminf (fun n : ℕ ↦ K (n + k - 1) / n) atTop = liminf (fun m : ℕ ↦ K m / m) atTop := by
  have h : (fun n : ℕ ↦ K (n + k - 1) / n) =ᶠ[atTop]
      fun n ↦ ((n + k - 1 : ℕ) : ℝ≥0∞) / n * (K (n + k - 1) / ((n + k - 1 : ℕ) : ℝ≥0∞)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_eq_natCast_div_mul_div _ (by omega) n
  rw [liminf_congr h, liminf_mul_of_tendsto_one (tendsto_natCast_add_sub_one_div k)]
  exact (Filter.liminf_comp (fun m : ℕ ↦ K m / m) (fun n ↦ n + k - 1) atTop).trans
    (by rw [map_add_sub_one_atTop])

/-- The upper limit of `K (n + k - 1) / n` equals the upper limit of `K m / m`. -/
private lemma limsup_div_add_sub_one (K : ℕ → ℝ≥0∞) (k : ℕ) :
    limsup (fun n : ℕ ↦ K (n + k - 1) / n) atTop = limsup (fun m : ℕ ↦ K m / m) atTop := by
  have h : (fun n : ℕ ↦ K (n + k - 1) / n) =ᶠ[atTop]
      fun n ↦ ((n + k - 1 : ℕ) : ℝ≥0∞) / n * (K (n + k - 1) / ((n + k - 1 : ℕ) : ℝ≥0∞)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_eq_natCast_div_mul_div _ (by omega) n
  rw [limsup_congr h, limsup_mul_of_tendsto_one (tendsto_natCast_add_sub_one_div k)]
  exact (Filter.limsup_comp (fun m : ℕ ↦ K m / m) (fun n ↦ n + k - 1) atTop).trans
    (by rw [map_add_sub_one_atTop])

/-! ### Orbit rates of the shift -/

/-- The lower limit of the finite scale costs of the shift at scale `β ^ k` is `-log₂ β` times
the lower limit of the normalized precision complexities at the scales `β ^ (m + 1)`. -/
private lemma liminf_finiteScaleBSCost_shift {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ} (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ) (x : ℕ → α) (k : ℕ) :
    liminf (fun n ↦ finiteScaleBSCost P (fun y j ↦ y (j + 1)) (fun _ ↦ 1) A x n (β ^ k))
        atTop =
      ENNReal.ofReal (-Real.logb 2 β) *
        liminf (fun m ↦ normalizedPrecisionComplexity P A x (β ^ (m + 1))) atTop := by
  have hcost := liminf_congr (f := atTop) (eventually_atTop.2
    ⟨1, fun n hn ↦ finiteScaleBSCost_shift_eq hβ hβ₁ hd P A x k hn⟩)
  rw [hcost, liminf_div_add_sub_one
    (fun m ↦ (precisionComplexityNat P A x (β ^ m) : ℝ≥0∞)) k,
    liminf_nat_add (fun m ↦ normalizedPrecisionComplexity P A x (β ^ m)) 1,
    ← ENNReal.liminf_const_mul_of_ne_zero_of_ne_top (ofReal_neg_logb_ne_zero hβ hβ₁)
      ENNReal.ofReal_ne_top]
  exact liminf_congr (Eventually.of_forall fun m ↦
    (const_mul_normalizedPrecisionComplexity_pow hβ hβ₁ P A x m).symm)

/-- The upper limit of the finite scale costs of the shift at scale `β ^ k` is `-log₂ β` times
the upper limit of the normalized precision complexities at the scales `β ^ m`. -/
private lemma limsup_finiteScaleBSCost_shift {α : Type*} [MetricSpace (ℕ → α)] {β : ℝ} (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ) (x : ℕ → α) (k : ℕ) :
    limsup (fun n ↦ finiteScaleBSCost P (fun y j ↦ y (j + 1)) (fun _ ↦ 1) A x n (β ^ k))
        atTop =
      ENNReal.ofReal (-Real.logb 2 β) *
        limsup (fun m ↦ normalizedPrecisionComplexity P A x (β ^ m)) atTop := by
  have hcost := limsup_congr (f := atTop) (eventually_atTop.2
    ⟨1, fun n hn ↦ finiteScaleBSCost_shift_eq hβ hβ₁ hd P A x k hn⟩)
  rw [hcost, limsup_div_add_sub_one
    (fun m ↦ (precisionComplexityNat P A x (β ^ m) : ℝ≥0∞)) k,
    ← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  exact limsup_congr (Eventually.of_forall fun m ↦
    (const_mul_normalizedPrecisionComplexity_pow hβ hβ₁ P A x m).symm)

/-- Symbolic lower orbit complexity is static lower dimension times the logarithmic metric
scale, using the same fixed dense sequence. Blueprint node `pressure:symbolic`. -/
theorem symbolic_orbitComplexity_lower {α : Type*} [MetricSpace (ℕ → α)] (β : ℝ) (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ) (x : ℕ → α) :
    (orbitComplexities P (fun y j => y (j + 1)) A x).1 =
      ENNReal.ofReal (-Real.logb 2 β) * (staticPointDimensions P A x).1 := by
  have hpos : ∀ m : ℕ, 0 < β ^ (m + 1) := fun m ↦ pow_pos hβ _
  have hzero : Tendsto (fun m : ℕ ↦ β ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ₁).comp (tendsto_add_atTop_nat 1)
  have hratio := (Real.tendsto_log_pow_succ_div_log_pow hβ hβ₁).comp (tendsto_add_atTop_nat 1)
  rw [dimension_along_scales P A x (fun m ↦ β ^ (m + 1)) hpos hzero hratio]
  refine (iSup_dyadicRadius_eq_iSup_pow
    (F := fun r ↦ liminf (fun n ↦ finiteScaleBSCost P (fun y j ↦ y (j + 1)) (fun _ ↦ 1) A x n r)
      atTop) (fun r₁ r₂ hr ↦ liminf_le_liminf (Eventually.of_forall fun n ↦
        pointwiseBSDimension_antitone_radius P _ _ A x n hr)) hβ hβ₁).trans ?_
  simp only [liminf_finiteScaleBSCost_shift hβ hβ₁ hd P A x, iSup_const]

/-- Symbolic upper orbit complexity has the corresponding static upper-dimension formula.
Blueprint node `pressure:symbolic`. -/
theorem symbolic_orbitComplexity_upper {α : Type*} [MetricSpace (ℕ → α)] (β : ℝ) (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ) (x : ℕ → α) :
    (orbitComplexities P (fun y j => y (j + 1)) A x).2 =
      ENNReal.ofReal (-Real.logb 2 β) * (staticPointDimensions P A x).2 := by
  rw [dimension_along_scales_upper P A x (fun m ↦ β ^ m) (fun m ↦ pow_pos hβ m)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ₁)
    (Real.tendsto_log_pow_succ_div_log_pow hβ hβ₁)]
  refine (iSup_dyadicRadius_eq_iSup_pow
    (F := fun r ↦ limsup (fun n ↦ finiteScaleBSCost P (fun y j ↦ y (j + 1)) (fun _ ↦ 1) A x n r)
      atTop) (fun r₁ r₂ hr ↦ limsup_le_limsup (Eventually.of_forall fun n ↦
        pointwiseBSDimension_antitone_radius P _ _ A x n hr)) hβ hβ₁).trans ?_
  simp only [limsup_finiteScaleBSCost_shift hβ hβ₁ hd P A x, iSup_const]

end Kolmogorov.PointToSet
