/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Defs
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.PointToSet.Order
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Bowen geometry and the scale-zero lower pressure

This module collects the metric and calculus facts about Bowen balls on which the lower
topological pressure rests, for a `PressureData` (a continuous map `T`, a potential `φ` and a
fixed dense presentation).

* `bowen_geometry` and its companions: for positive order the Bowen distance is a metric
  inducing the original topology, Bowen balls are open, ball membership is symmetric, the
  triangle inequality moves a ball to another center, and the ideal points are dense for
  every Bowen distance (blueprint node `pressure:bowen`).
* `recenter_bowen_cover` and the `recenter_bowen_cover_*` lemmas: countable families of
  Bowen balls can be recentered on ideal points at twice the radius, and Birkhoff sums
  oscillate by at most `n * ω p` on a ball of radius `2⁻ᵖ`, so the supremum weight is finite
  and squeezed between the centered weight and the centered weight plus `n * ω p`
  (blueprint node `pressure:recenter`).
* `lowerContent_critical` and its companions: the critical-value calculus of the
  order-cutoff lower content, namely monotonicity in the cutoff and in the exponent, the
  exponential decay estimate, vanishing above the critical value, divergence below it, and
  the extraction of covers of small cost from vanishing content (blueprint node
  `pressure:critical`).
* `lowerPressure_eq_centered_radius`, `lowerPressure_eq_centered_bounds` and
  `lowerPressure_eq_centered`: the centered critical value is antitone in the radius, the
  supremum-weight critical value differs from it by at most the oscillation error, and hence
  the supremum-weight critical values at the dyadic radii converge to the scale-zero lower
  pressure (blueprint node `pressure:lower-scale`).

These facts feed the point-to-set principle for the lower pressure and the comparison
modules of `KolmogorovMathlib.PointToSet.Pressure.Lower`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Positive-order Bowen distance is a metric inducing the original topology.
Blueprint node `pressure:bowen`. -/
theorem bowen_geometry (D : PressureData X) (n : ℕ) (hn : 1 ≤ n) :
    let d := bowenDist D.T n
    let τ := (inferInstance : TopologicalSpace X)
    ∃ m : MetricSpace X, (∀ x y, m.dist x y = d x y) ∧
      m.toUniformSpace.toTopologicalSpace = τ := by
  exact bowen_ball_dense_metric D.T D.continuous_T n hn

/-- Bowen balls are open in the original topology. Blueprint node `pressure:bowen`. -/
theorem bowen_geometry_open (D : PressureData X) (n : ℕ) (hn : 1 ≤ n) (x : X) (r : ℝ) :
    IsOpen (bowenBall D.T n x r) := by
  have _ := hn
  exact bowen_ball_dense_open D.T D.continuous_T n x r

/-- Membership in a Bowen ball is symmetric in the two points.
Blueprint node `pressure:bowen`. -/
theorem bowen_geometry_symm (D : PressureData X) (n : ℕ) (hn : 1 ≤ n)
    (x y : X) (r : ℝ) : y ∈ bowenBall D.T n x r ↔ x ∈ bowenBall D.T n y r := by
  rw [bowen_ball_dense_iff D.T n hn, bowen_ball_dense_iff D.T n hn, bowen_dist_comm]

/-- The triangle inequality enlarges a ball after changing its center: the Bowen ball of
radius `b` around `x` lies in the ball of radius `a + b` around every `y` within Bowen
distance `a` of `x`. Blueprint node `pressure:bowen`. -/
theorem bowen_geometry_subset (D : PressureData X) (n : ℕ) (hn : 1 ≤ n)
    (x y : X) (a b : ℝ) (hxy : bowenDist D.T n x y < a) :
    bowenBall D.T n x b ⊆ bowenBall D.T n y (a + b) := by
  intro z hz
  rw [bowen_ball_dense_iff D.T n hn] at hz ⊢
  have htri := bowen_ball_dense_triangle D.T n y x z
  rw [bowen_dist_comm D.T n y x] at htri
  linarith

/-- The fixed ideal sequence meets every positive-radius Bowen ball.
Blueprint node `pressure:bowen`. -/
theorem bowen_geometry_dense (D : PressureData X) (n : ℕ) (hn : 1 ≤ n)
    (x : X) (r : ℝ) (hr : 0 < r) :
    ∃ i, bowenDist D.T n x (D.presentation.ι i) < r := by
  obtain ⟨i, hi⟩ := bowen_ball_dense D.presentation D.T D.continuous_T x n hn r hr
  exact ⟨i, (bowen_ball_dense_iff D.T n hn x _ r).mp hi⟩

/-- A countable family can be recentered on ideal points with twice its radius.
Blueprint node `pressure:recenter`. -/
theorem recenter_bowen_cover (D : PressureData X) (C : BowenCoverFamily X)
    (hC : ∀ j, 1 ≤ C.order j) (a : ℝ) (ha : 0 < a) :
    ∃ i : C.index → ℕ, ∀ j,
      bowenDist D.T (C.order j) (C.center j) (D.presentation.ι (i j)) < a ∧
      bowenBall D.T (C.order j) (C.center j) a ⊆
        bowenBall D.T (C.order j) (D.presentation.ι (i j)) (2 * a) := by
  choose i hi using fun j : C.index ↦
    bowen_geometry_dense D (C.order j) (hC j) (C.center j) a ha
  refine ⟨i, fun j ↦ ⟨hi j, ?_⟩⟩
  rw [two_mul]
  exact bowen_geometry_subset D (C.order j) (hC j) _ _ a a (hi j)

/-- Oscillation adds over the observed times, using the frozen Birkhoff sum.
Blueprint node `pressure:recenter`. -/
theorem recenter_bowen_cover_distortion (D : PressureData X) (p : ℕ) (hp : D.p₀ ≤ p)
    (n : ℕ) (hn : 1 ≤ n) (y z : X) (hz : z ∈ bowenBall D.T n y (dyadicRadius p)) :
    |birkhoffSum D.T D.φ n z - birkhoffSum D.T D.φ n y| ≤ n * D.ω p := by
  have _ := hn
  have hbound : ∀ k ∈ Finset.range n, |D.φ (D.T^[k] z) - D.φ (D.T^[k] y)| ≤ D.ω p := by
    intro k hk
    refine D.oscillation p hp _ _ ?_
    rw [dist_comm]
    exact Dynamics.mem_dynEntourage.mp hz k (Finset.mem_range.mp hk)
  rw [birkhoffSum, birkhoffSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n, |D.φ (D.T^[i] z) - D.φ (D.T^[i] y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, D.ω p := Finset.sum_le_sum hbound
    _ = n * D.ω p := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The supremum potential lies between the center value and its oscillation bound.
Blueprint node `pressure:recenter`. -/
theorem recenter_bowen_cover_sup_bounds (D : PressureData X) (p : ℕ) (hp : D.p₀ ≤ p)
    (n : ℕ) (hn : 1 ≤ n) (y : X) :
    ((birkhoffSum D.T D.φ n y : ℝ) : EReal) ≤
      bowenPotentialSup D.T D.φ n y (dyadicRadius p) ∧
    bowenPotentialSup D.T D.φ n y (dyadicRadius p) ≤
      ((birkhoffSum D.T D.φ n y + n * D.ω p : ℝ) : EReal) := by
  refine ⟨le_iSup₂_of_le y (self_mem_bowenBall D.T n y _ (dyadicRadius_pos p)) le_rfl,
    iSup₂_le fun z hz ↦ EReal.coe_le_coe_iff.mpr ?_⟩
  have hd := (abs_le.mp (recenter_bowen_cover_distortion D p hp n hn y z hz)).2
  linarith

/-- The supremum potential on a valid small-scale ball is a finite real number.
Blueprint node `pressure:recenter`. -/
theorem recenter_bowen_cover_sup_finite (D : PressureData X) (p : ℕ) (hp : D.p₀ ≤ p)
    (n : ℕ) (hn : 1 ≤ n) (y : X) :
    ∃ w : ℝ, bowenPotentialSup D.T D.φ n y (dyadicRadius p) = (w : EReal) := by
  obtain ⟨hlo, hhi⟩ := recenter_bowen_cover_sup_bounds D p hp n hn y
  exact ⟨_, (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)).symm⟩

/-- Increasing the exponent bounds cutoff content by the explicit exponential factor.
Blueprint node `pressure:critical`. -/
theorem lowerContent_critical (D : PressureData X) (w : PressureWeight) (Z : Set X)
    (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω)
    (N : ℕ) (hN : 1 ≤ N) (s t : ℝ) (hst : s < t) :
    lowerContent D.T D.φ w Z t r N ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * N) * lowerContent D.T D.φ w Z s r N := by
  have _ := And.intro hr (And.intro hω hN)
  let a : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ))
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have haT : a ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hcost (C : BowenCoverFamily X) (hC : IsBowenCover D.T Z r N C) :
      bowenCoverCost D.T D.φ w t r C ≤ a * bowenCoverCost D.T D.φ w s r C := by
    unfold bowenCoverCost
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j ↦ ?_
    have hjR : (N : ℝ) ≤ (C.order j : ℝ) := by
      exact_mod_cast (le_max_right 1 N).trans (hC.1 j)
    have hp : 0 ≤ (t - s) * ((C.order j : ℝ) - (N : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hst.le) (sub_nonneg.mpr hjR)
    have he : -t * (C.order j : ℝ) ≤ -(t - s) * (N : ℝ) + -s * (C.order j : ℝ) := by
      nlinarith [hp]
    have hw : (2 : ℝ≥0∞) ^ (-t * (C.order j : ℝ)) ≤ a * (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ)) :=
      calc
        _ ≤ (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ) + -s * (C.order j : ℝ)) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) he
        _ = _ := ENNReal.rpow_add _ _ (by norm_num) (by norm_num)
    calc
      _ ≤ (a * (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ))) *
          pressureBallWeight D.T D.φ w (C.order j) (C.center j) r := by gcongr
      _ = _ := mul_assoc _ _ _
  change lowerContent D.T D.φ w Z t r N ≤ a * lowerContent D.T D.φ w Z s r N
  unfold lowerContent
  simp_rw [ENNReal.mul_iInf_of_ne ha0 haT]
  exact iInf_mono fun C ↦ iInf_mono fun hC ↦ hcost C hC

/-- Raising the positive order cutoff can only increase content.
Blueprint node `pressure:critical`. -/
theorem lowerContent_critical_mono_cutoff (D : PressureData X) (w : PressureWeight)
    (Z : Set X) (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω) (s : ℝ) (N M : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M) :
    lowerContent D.T D.φ w Z s r N ≤ lowerContent D.T D.φ w Z s r M := by
  have _ := And.intro hr (And.intro hω hN)
  unfold lowerContent
  refine iInf_mono fun C ↦ iInf_mono' fun hC ↦ ⟨⟨fun j ↦ ?_, hC.2⟩, le_rfl⟩
  exact (max_le_max le_rfl hNM).trans (hC.1 j)

/-- Increasing the exponent can only decrease cutoff content.
Blueprint node `pressure:critical`. -/
theorem lowerContent_critical_antitone (D : PressureData X) (w : PressureWeight)
    (Z : Set X) (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω) (N : ℕ) (hN : 1 ≤ N) :
    Antitone (fun s => lowerContent D.T D.φ w Z s r N) := by
  have _ := And.intro hr (And.intro hω hN)
  intro s t hst
  unfold lowerContent
  refine iInf_mono fun C ↦ iInf_mono fun _ ↦ ENNReal.tsum_le_tsum fun j ↦ ?_
  gcongr ?_ * _
  refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
  have h_le : s * (C.order j : ℝ) ≤ t * (C.order j : ℝ) :=
    mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg _)
  linarith

/-- A cutoff content is at most the content limit. -/
private lemma lowerContent_le_lowerContentLimit (T : X → X) (φ : X → ℝ) (w : PressureWeight)
    (Z : Set X) (s r : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    lowerContent T φ w Z s r N ≤ lowerContentLimit T φ w Z s r :=
  le_iSup₂_of_le N hN le_rfl

/-- Content vanishes strictly above its extended critical value.
Blueprint node `pressure:critical`. -/
theorem lowerContent_critical_zero (D : PressureData X) (w : PressureWeight)
    (Z : Set X) (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω) (s : ℝ)
    (hs : lowerPressureAt D.T D.φ w Z r < (s : EReal)) :
    lowerContentLimit D.T D.φ w Z s r = 0 := by
  unfold lowerPressureAt at hs
  obtain ⟨s', hs'⟩ := iInf_lt_iff.mp hs
  obtain ⟨h_zero, hs's⟩ := iInf_lt_iff.mp hs'
  have hss : s' ≤ s := (EReal.coe_lt_coe_iff.mp hs's).le
  refine iSup_eq_bot.mpr fun N ↦ iSup_eq_bot.mpr fun hN ↦ le_antisymm ?_ zero_le
  calc
    _ ≤ lowerContent D.T D.φ w Z s' r N :=
      lowerContent_critical_antitone D w Z r hr ω hω N hN hss
    _ ≤ lowerContentLimit D.T D.φ w Z s' r := lowerContent_le_lowerContentLimit _ _ _ _ _ _ hN
    _ = 0 := h_zero

/-- If the content limit at the exponent `s` is finite, it vanishes at every larger exponent
`t`: the exponential factor of `lowerContent_critical` tends to zero with the cutoff. -/
private lemma lowerContentLimit_eq_zero_of_lt (D : PressureData X) (w : PressureWeight)
    (Z : Set X) (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω) (s t : ℝ) (hst : s < t)
    (h_fin : lowerContentLimit D.T D.φ w Z s r < ⊤) :
    lowerContentLimit D.T D.φ w Z t r = 0 := by
  have H (N : ℕ) (hN : 1 ≤ N) : lowerContent D.T D.φ w Z t r N ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * N) * lowerContentLimit D.T D.φ w Z s r :=
    (lowerContent_critical D w Z r hr ω hω N hN s t hst).trans
      (mul_le_mul_right (lowerContent_le_lowerContentLimit _ _ _ _ _ _ hN) _)
  have h_lt_one : (2 : ℝ≥0∞) ^ (-(t - s)) < 1 := by
    rw [← ENNReal.rpow_zero (x := (2 : ℝ≥0∞))]
    exact ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) (by linarith)
  have H_lim : Tendsto (fun N : ℕ ↦
      (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) * lowerContentLimit D.T D.φ w Z s r) atTop (𝓝 0) := by
    have h_pow : ∀ N : ℕ, (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) =
        ((2 : ℝ≥0∞) ^ (-(t - s))) ^ N := fun N ↦ by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    simp_rw [h_pow]
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h_lt_one)
        (Or.inr h_fin.ne)
  refine iSup_eq_bot.mpr fun N ↦ iSup_eq_bot.mpr fun hN ↦ le_antisymm ?_ zero_le
  refine ge_of_tendsto H_lim ?_
  filter_upwards [Ici_mem_atTop N] with M hM
  exact (lowerContent_critical_mono_cutoff D w Z r hr ω hω t N M hN hM).trans
    (H M (hN.trans hM))

/-- Content is infinite strictly below its extended critical value.
Blueprint node `pressure:critical`. -/
theorem lowerContent_critical_top (D : PressureData X) (w : PressureWeight)
    (Z : Set X) (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω) (s : ℝ)
    (hs : (s : EReal) < lowerPressureAt D.T D.φ w Z r) :
    lowerContentLimit D.T D.φ w Z s r = ⊤ := by
  by_contra h
  obtain ⟨t, hst, ht⟩ := EReal.lt_iff_exists_real_btwn.mp hs
  have h_zero := lowerContentLimit_eq_zero_of_lt D w Z r hr ω hω s t
    (EReal.coe_lt_coe_iff.mp hst) (lt_top_iff_ne_top.mpr h)
  exact (not_le.mpr ht) (iInf₂_le t h_zero)

/-- Vanishing content supplies an actual cover below every positive tolerance.
Blueprint node `pressure:critical`. -/
theorem lowerContent_critical_cover (D : PressureData X) (w : PressureWeight)
    (Z : Set X) (r : ℝ) (hr : 0 < r) (ω : ℝ)
    (hω : ∀ x y, dist x y < r → |D.φ x - D.φ y| ≤ ω) (s : ℝ)
    (hs : lowerContentLimit D.T D.φ w Z s r = 0)
    (N : ℕ) (hN : 1 ≤ N) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ C : BowenCoverFamily X, IsBowenCover D.T Z r N C ∧
      bowenCoverCost D.T D.φ w s r C < ε := by
  have _ := And.intro hr hω
  have h1 : lowerContent D.T D.φ w Z s r N = 0 :=
    le_antisymm
      ((lowerContent_le_lowerContentLimit D.T D.φ w Z s r hN).trans_eq hs) zero_le
  have h2 : lowerContent D.T D.φ w Z s r N < ε := by
    rw [h1]
    exact hε
  unfold lowerContent at h2
  obtain ⟨C, hC⟩ := iInf_lt_iff.mp h2
  obtain ⟨hCov, hcost⟩ := iInf_lt_iff.mp hC
  exact ⟨C, hCov, hcost⟩

/-- Centered critical values are antitone in the positive radius: a cover by balls of radius
`r` is also a cover by balls of radius `R ≥ r` at the same centered cost.
Blueprint node `pressure:lower-scale`. -/
theorem lowerPressure_eq_centered_radius (D : PressureData X) (Z : Set X)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    lowerPressureAt D.T D.φ .centered Z R ≤ lowerPressureAt D.T D.φ .centered Z r := by
  have _ := hr
  have hcontent (s : ℝ) (N : ℕ) :
      lowerContent D.T D.φ .centered Z s R N ≤ lowerContent D.T D.φ .centered Z s r N := by
    unfold lowerContent
    refine iInf_mono fun C ↦ le_iInf fun hC ↦ ?_
    have hCR : IsBowenCover D.T Z R N C := by
      refine ⟨hC.1, fun x hx ↦ ?_⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hC.2 hx)
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at hj ⊢
      exact fun k hk ↦ (hj k hk).trans_le hrR
    exact iInf_le_of_le hCR le_rfl
  have hlimit (s : ℝ) :
      lowerContentLimit D.T D.φ .centered Z s R ≤ lowerContentLimit D.T D.φ .centered Z s r :=
    iSup_mono fun N ↦ iSup_mono fun _ ↦ hcontent s N
  unfold lowerPressureAt
  refine iInf_mono fun s ↦ le_iInf fun hs ↦ ?_
  have hsR : lowerContentLimit D.T D.φ .centered Z s R = 0 :=
    le_antisymm ((hlimit s).trans_eq hs) zero_le
  exact iInf_le_of_le hsR le_rfl

/-- On a valid small-scale ball the supremum weight exceeds the centered weight by at most
the factor `2 ^ (n * ω p)`, so shifting the exponent by `ω p` compares the two costs of a
cover. -/
private lemma bowenCoverCost_supremum_le_centered (D : PressureData X) (p : ℕ) (hp : D.p₀ ≤ p)
    (s : ℝ) (C : BowenCoverFamily X) (hC : ∀ j, 1 ≤ C.order j) :
    bowenCoverCost D.T D.φ .supremum s (dyadicRadius p) C ≤
      bowenCoverCost D.T D.φ .centered (s - D.ω p) (dyadicRadius p) C := by
  unfold bowenCoverCost
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  dsimp only [pressureBallWeight]
  have hsup : (⨆ z ∈ bowenBall D.T (C.order j) (C.center j) (dyadicRadius p),
      (2 : ℝ≥0∞) ^ (birkhoffSum D.T D.φ (C.order j) z : ℝ)) ≤
      (2 : ℝ≥0∞) ^ (birkhoffSum D.T D.φ (C.order j) (C.center j) +
        (C.order j : ℝ) * D.ω p) := by
    refine iSup₂_le fun z hz ↦ ?_
    refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) ?_
    have hd := recenter_bowen_cover_distortion D p hp (C.order j) (hC j) (C.center j) z hz
    linarith [(abs_le.mp hd).2]
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ)) *
        (2 : ℝ≥0∞) ^ (birkhoffSum D.T D.φ (C.order j) (C.center j) +
          (C.order j : ℝ) * D.ω p) := by gcongr
    _ = (2 : ℝ≥0∞) ^ (-(s - D.ω p) * (C.order j : ℝ) +
        (birkhoffSum D.T D.φ (C.order j) (C.center j) : ℝ)) := by
      rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      ring
    _ = _ := ENNReal.rpow_add _ _ (by norm_num) (by norm_num)

/-- The supremum-weight content limit at exponent `s` is at most the centered one at the
exponent `s - ω p`, at a valid small scale. -/
private lemma lowerContentLimit_supremum_le_centered (D : PressureData X) (Z : Set X) (p : ℕ)
    (hp : D.p₀ ≤ p) (s : ℝ) :
    lowerContentLimit D.T D.φ .supremum Z s (dyadicRadius p) ≤
      lowerContentLimit D.T D.φ .centered Z (s - D.ω p) (dyadicRadius p) := by
  unfold lowerContentLimit lowerContent
  refine iSup_mono fun N ↦ iSup_mono fun _ ↦ iInf_mono fun C ↦ iInf_mono fun hC ↦ ?_
  exact bowenCoverCost_supremum_le_centered D p hp s C fun j ↦ (le_max_left 1 N).trans (hC.1 j)

/-- The two fixed-scale critical values differ by at most the finite oscillation error.
Blueprint node `pressure:lower-scale`. -/
theorem lowerPressure_eq_centered_bounds (D : PressureData X) (Z : Set X)
    (p : ℕ) (hp : D.p₀ ≤ p) :
    lowerPressureAt D.T D.φ .centered Z (dyadicRadius p) ≤
      lowerPressureAt D.T D.φ .supremum Z (dyadicRadius p) ∧
    lowerPressureAt D.T D.φ .supremum Z (dyadicRadius p) ≤
      lowerPressureAt D.T D.φ .centered Z (dyadicRadius p) + (D.ω p : EReal) := by
  constructor
  · unfold lowerPressureAt
    refine le_iInf fun s ↦ le_iInf fun hs ↦ ?_
    have hs0 : lowerContentLimit D.T D.φ .centered Z s (dyadicRadius p) = 0 :=
      le_antisymm
        ((lowerContentLimit_centered_le_supremum D.T D.φ Z s _ (dyadicRadius_pos p)).trans_eq hs)
        zero_le
    exact iInf₂_le s hs0
  · have shift (a b : EReal) : a - (D.ω p : EReal) ≤ b ↔ a ≤ b + (D.ω p : EReal) :=
      EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot (D.ω p)))
        (Or.inl (EReal.coe_ne_top (D.ω p)))
    rw [← shift]
    unfold lowerPressureAt
    simp only [le_iInf_iff]
    intro t ht
    rw [shift]
    have hz : lowerContentLimit D.T D.φ .supremum Z (t + D.ω p) (dyadicRadius p) = 0 := by
      have h := lowerContentLimit_supremum_le_centered D Z p hp (t + D.ω p)
      rw [add_sub_cancel_right, ht] at h
      exact le_antisymm h zero_le
    have hb : (⨅ s : ℝ, ⨅ (_ : lowerContentLimit D.T D.φ .supremum Z s (dyadicRadius p) = 0),
        (s : EReal)) ≤ ((t + D.ω p : ℝ) : EReal) :=
      iInf_le_of_le (t + D.ω p) (iInf_le_of_le hz le_rfl)
    simpa only [EReal.coe_add] using hb

/-- Centered critical values converge to their small-scale supremum.
Blueprint node `pressure:lower-scale`. -/
theorem lowerPressure_eq_centered_limit (D : PressureData X) (Z : Set X) :
    Tendsto (fun p => lowerPressureAt D.T D.φ .centered Z (dyadicRadius p)) atTop
      (𝓝 (lowerPressure D.T D.φ D.p₀ Z)) := by
  let f := fun p ↦ lowerPressureAt D.T D.φ .centered Z (dyadicRadius p)
  have hmono : Monotone f := by
    intro p q hpq
    apply lowerPressure_eq_centered_radius
    · change 0 < (2 : ℝ)⁻¹ ^ q
      exact pow_pos (by norm_num) q
    · change (2 : ℝ)⁻¹ ^ q ≤ (2 : ℝ)⁻¹ ^ p
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq
  have hsup : ⨆ p, f p = lowerPressure D.T D.φ D.p₀ Z := by
    unfold lowerPressure
    apply le_antisymm
    · apply iSup_le
      intro p
      by_cases hp : D.p₀ ≤ p
      · exact le_iSup_of_le p (le_iSup (fun _ ↦ f p) hp)
      · push Not at hp
        have hle : f p ≤ f D.p₀ := hmono (le_of_lt hp)
        have h_p0 : f D.p₀ ≤ ⨆ p ≥ D.p₀, f p :=
          le_iSup_of_le D.p₀ (le_iSup (fun _ ↦ f D.p₀) le_rfl)
        exact le_trans hle h_p0
    · apply iSup_le
      intro p
      apply iSup_le
      intro _
      exact le_iSup f p
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

/-- The supremum-weight small-scale limit exists and is the centered lower pressure: the
fixed-scale critical values with supremum weight converge to `lowerPressure`.
Blueprint node `pressure:lower-scale`. -/
theorem lowerPressure_eq_centered (D : PressureData X) (Z : Set X) :
    Tendsto (fun p => lowerPressureAt D.T D.φ .supremum Z (dyadicRadius p)) atTop
      (𝓝 (lowerPressure D.T D.φ D.p₀ Z)) := by
  have hc := lowerPressure_eq_centered_limit D Z
  have hw : Tendsto (fun p ↦ (D.ω p : EReal)) atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr D.ω_tendsto
  have hr : Tendsto (fun p ↦ lowerPressureAt D.T D.φ .centered Z (dyadicRadius p) +
      (D.ω p : EReal)) atTop (𝓝 (lowerPressure D.T D.φ D.p₀ Z)) := by
    have h := (EReal.continuousAt_add (p := (lowerPressure D.T D.φ D.p₀ Z, (0 : EReal)))
      (Or.inr (by simp)) (Or.inr (by simp))).tendsto.comp (hc.prodMk_nhds hw)
    simpa only [Function.comp_def, add_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hc hr ?_ ?_
  · filter_upwards [eventually_ge_atTop D.p₀] with p hp
    exact (lowerPressure_eq_centered_bounds D Z p hp).1
  · filter_upwards [eventually_ge_atTop D.p₀] with p hp
    exact (lowerPressure_eq_centered_bounds D Z p hp).2

end Kolmogorov.PointToSet
