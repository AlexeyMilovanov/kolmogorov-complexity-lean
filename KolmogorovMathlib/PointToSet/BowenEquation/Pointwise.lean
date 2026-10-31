/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation.SlopeBounds

/-!
# Slope bounds and finiteness for pointwise Bowen equations

At a fixed radius with positive, bounded realizer averages and finite zero-potential pressure,
the time limit of the BS cost is the unique real pressure zero. The pressure lies between
the two affine bounds through that zero
(blueprint node `bs:finite-scale-root`). For positive lower and finite upper Birkhoff averages,
these slope bounds pass to scale zero, where they imply strict decrease at finite pressures
(blueprint node `bs:affine-slope`). Finite zero-potential pressure also forces finite pointwise
BS dimension (blueprint node `bs:pointwise-root`).

`PointwiseCriticalValue` uses these estimates and finiteness to establish the scale-zero
pointwise Bowen equation and its strict sign on either side of the root.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

/-- Subtraction of a convergent real family preserves convergence of extended reals. -/
private lemma tendsto_sub_coe {α : Type*} {l : Filter α} {f : α → EReal} {g : α → ℝ}
    {a : EReal} {b : ℝ} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun i ↦ f i - (g i : EReal)) l (𝓝 (a - (b : EReal))) := by
  simpa only [Function.comp_def, sub_eq_add_neg, ← EReal.coe_neg] using
    (EReal.continuousAt_add (p := (a, ((-b : ℝ) : EReal)))
      (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).tendsto.comp
      (hf.prodMk_nhds (EReal.tendsto_coe.mpr hg.neg))

/-- Two affine bounds with arbitrarily small positive slack imply the bounds without slack. -/
private lemma sub_coe_sandwich_of_pos_slack {z w : EReal} {a b c : ℝ} (ha : 0 < a)
    (h : ∀ η : ℝ, 0 < η → η < a →
      z - (c * (b + η) : ℝ) ≤ w ∧ w ≤ z - (c * (a - η) : ℝ)) :
    z - (c * b : ℝ) ≤ w ∧ w ≤ z - (c * a : ℝ) := by
  have hevent : ∀ᶠ η : ℝ in 𝓝[>] 0,
      z - (c * (b + η) : ℝ) ≤ w ∧ w ≤ z - (c * (a - η) : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds ha)] with η hη hηa
    exact h η hη hηa
  have hid : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlower : Tendsto (fun η : ℝ ↦ c * (b + η)) (𝓝[>] 0) (𝓝 (c * b)) := by
    simpa only [add_zero] using (hid.const_add b).const_mul c
  have hupper : Tendsto (fun η : ℝ ↦ c * (a - η)) (𝓝[>] 0) (𝓝 (c * a)) := by
    simpa only [sub_zero] using (hid.const_sub a).const_mul c
  exact ⟨le_of_tendsto (tendsto_sub_coe tendsto_const_nhds hlower)
      (hevent.mono fun _ hη ↦ hη.1),
    ge_of_tendsto (tendsto_sub_coe tendsto_const_nhds hupper)
      (hevent.mono fun _ hη ↦ hη.2)⟩

variable {X : Type*} [MetricSpace X]

section FixedRadius

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (a b : ℝ) (ha : 0 < a) (A : Set ℕ) (x : X) (r : ℝ) (hr : 0 < r)
  (hbounds : ∀ᶠ n in atTop, ∀ i, P.ι i ∈ bowenBall T n x r →
    a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)
include hT hu ha hr hbounds
variable (σ : LimitSide)
  (hfinite : σ.timeLimit (fun n => finiteScalePressureRate P T (fun _ => 0) A x n r) < ⊤)
include hfinite

omit hu in
/-- The fixed-radius pressure has no other real zero.
Blueprint node `bs:finite-scale-root`. -/
theorem finiteScalePointwiseBowenEquation_unique (s : ℝ) :
    σ.timeLimit (fun n => finiteScalePressureRate P T (fun y => -s * u y) A x n r) = 0 ↔
      s = (σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r)).toReal := by
  let d := (σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n r)).toReal
  let f := fun s : ℝ ↦
    σ.timeLimit (fun n ↦ finiteScalePressureRate P T (fun y ↦ -s * u y) A x n r)
  have hd : f d = 0 :=
    finiteScalePointwiseBowenEquation P T hT u a b ha A x r hr hbounds σ hfinite
  change f s = 0 ↔ s = d
  constructor
  · intro hs
    rcases lt_trichotomy s d with h | h | h
    · have hle := (pointwisePressureSlopeBounds_time
        P T u a b A x r hbounds σ s d h).2
      change f d ≤ f s - (((d - s) * a : ℝ) : EReal) at hle
      rw [hd, hs, zero_sub] at hle
      have hpos : (0 : EReal) < (((d - s) * a : ℝ) : EReal) :=
        EReal.coe_pos.mpr (mul_pos (sub_pos.mpr h) ha)
      exact False.elim ((EReal.neg_lt_zero.mpr hpos).not_ge hle)
    · exact h
    · have hle := (pointwisePressureSlopeBounds_time
        P T u a b A x r hbounds σ d s h).2
      change f s ≤ f d - (((s - d) * a : ℝ) : EReal) at hle
      rw [hd, hs, zero_sub] at hle
      have hpos : (0 : EReal) < (((s - d) * a : ℝ) : EReal) :=
        EReal.coe_pos.mpr (mul_pos (sub_pos.mpr h) ha)
      exact False.elim ((EReal.neg_lt_zero.mpr hpos).not_ge hle)
  · rintro rfl
    exact hd

omit hu in
/-- The pressure at every real parameter is trapped between the two slopes through its root.
Blueprint node `bs:finite-scale-root`. -/
theorem finiteScalePointwiseBowenEquation_sandwich (s : ℝ) :
    let d := (σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r)).toReal
    let f := σ.timeLimit (fun n =>
      finiteScalePressureRate P T (fun y => -s * u y) A x n r)
    ((min (a * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ f ∧
      f ≤ ((max (a * (d - s)) (b * (d - s)) : ℝ) : EReal) := by
  intro d f
  let F : ℝ → EReal := fun t ↦ σ.timeLimit (fun n ↦
    finiteScalePressureRate P T (fun y ↦ -t * u y) A x n r)
  have hd : F d = 0 :=
    finiteScalePointwiseBowenEquation P T hT u a b ha A x r hr
      hbounds σ hfinite
  change ((min (a * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ F s ∧
    F s ≤ ((max (a * (d - s)) (b * (d - s)) : ℝ) : EReal)
  rcases lt_trichotomy s d with hs | hs | hs
  · have H := pointwisePressureSlopeBounds_time
      P T u a b A x r hbounds σ s d hs
    change F s - (((d - s) * b : ℝ) : EReal) ≤ F d ∧
      F d ≤ F s - (((d - s) * a : ℝ) : EReal) at H
    rw [hd] at H
    have upper := EReal.sub_nonpos.mp H.1
    have lower : (((d - s) * a : ℝ) : EReal) ≤ F s := by
      simpa only [zero_add] using EReal.add_le_of_le_sub H.2
    rw [mul_comm (d - s) a] at lower
    rw [mul_comm (d - s) b] at upper
    exact ⟨(EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans lower,
      upper.trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))⟩
  · rw [hs, hd]
    simp
  · have H := pointwisePressureSlopeBounds_time
      P T u a b A x r hbounds σ d s hs
    change F d - (((s - d) * b : ℝ) : EReal) ≤ F s ∧
      F s ≤ F d - (((s - d) * a : ℝ) : EReal) at H
    rw [hd] at H
    change (((0 - (s - d) * b : ℝ) : EReal) ≤ F s ∧
      F s ≤ ((0 - (s - d) * a : ℝ) : EReal)) at H
    have eb : 0 - (s - d) * b = b * (d - s) := by ring
    have ea : 0 - (s - d) * a = a * (d - s) := by ring
    rw [eb, ea] at H
    exact ⟨(EReal.coe_le_coe_iff.mpr (min_le_right _ _)).trans H.1,
      H.2.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))⟩

end FixedRadius

section Pointwise

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (A : Set ℕ) (x : X)
  (hpos : 0 < lowerBirkhoffAverage T u x) (hupper : upperBirkhoffAverage T u x < ⊤)

include hT hu hpos hupper

omit [MetricSpace X] hT hu in
/-- Positive lower and finite upper averages have positive, ordered real representatives. -/
private lemma birkhoffAverage_toReal_bounds :
    let ℓ := (lowerBirkhoffAverage T u x).toReal
    let b := (upperBirkhoffAverage T u x).toReal
    0 < ℓ ∧ ℓ ≤ b ∧
      lowerBirkhoffAverage T u x = (ℓ : EReal) ∧
      upperBirkhoffAverage T u x = (b : EReal) := by
  have hle : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := liminf_le_limsup
  have hlower := EReal.coe_toReal (hle.trans_lt hupper).ne hpos.ne_bot
  have hupper' := EReal.coe_toReal hupper.ne (hpos.trans_le hle).ne_bot
  refine ⟨EReal.toReal_pos hpos (hle.trans_lt hupper).ne, ?_, hlower.symm, hupper'.symm⟩
  rw [← hlower, ← hupper'] at hle
  exact EReal.coe_le_coe_iff.mp hle

omit hT in
/-- The time-limit slope bounds hold at all sufficiently small positive radii,
with any positive slack smaller than the lower average. -/
private lemma pressure_slope_bounds_small_radius (σ : LimitSide) (s t η : ℝ) (hst : s < t)
    (hη : 0 < η) :
    let ℓ := (lowerBirkhoffAverage T u x).toReal
    let b := (upperBirkhoffAverage T u x).toReal
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      let f := fun v : ℝ ↦
        σ.timeLimit (fun n ↦ finiteScalePressureRate P T (fun y ↦ -v * u y) A x n r)
      f s - ((t - s) * (b + η) : ℝ) ≤ f t ∧
        f t ≤ f s - ((t - s) * (ℓ - η) : ℝ) := by
  obtain ⟨hℓ, hℓb, hlower, hupper'⟩ := birkhoffAverage_toReal_bounds T u x hpos hupper
  obtain ⟨r₀, hr₀, hbounds⟩ := birkhoffRealizerBounds P T u hu x
    (lowerBirkhoffAverage T u x).toReal (upperBirkhoffAverage T u x).toReal
    hlower hupper' η hη
  refine ⟨r₀, hr₀, fun r hr hrle ↦ ?_⟩
  obtain ⟨N, -, hN⟩ := hbounds r hr hrle
  exact pointwisePressureSlopeBounds_time P T u
    ((lowerBirkhoffAverage T u x).toReal - η) ((upperBirkhoffAverage T u x).toReal + η)
    A x r (eventually_atTop.mpr ⟨N, hN⟩) σ s t hst

omit hT hu hpos hupper in
/-- The time-limit pressure increases as the dyadic radius decreases. -/
lemma timeLimit_pressureRate_monotone_scale (σ : LimitSide) (v : ℝ) :
    Monotone (fun p ↦ σ.timeLimit (fun n ↦
      finiteScalePressureRate P T (fun y ↦ -v * u y) A x n (dyadicRadius p))) := by
  intro p q hpq
  have hrate (n : ℕ) :
      finiteScalePressureRate P T (fun y ↦ -v * u y) A x n (dyadicRadius p) ≤
        finiteScalePressureRate P T (fun y ↦ -v * u y) A x n (dyadicRadius q) := by
    unfold finiteScalePressureRate
    split_ifs
    · exact le_rfl
    · refine iInf_mono fun i ↦ iInf_mono' fun hi ↦ ⟨?_, le_rfl⟩
      exact bowenBall_subset_of_le T n x (dyadicRadius_antitone hpq) hi
  cases σ
  · exact liminf_le_liminf (Eventually.of_forall hrate)
  · exact limsup_le_limsup (Eventually.of_forall hrate)

omit hT in
/-- At scale zero the lower and upper Birkhoff averages give the two affine slopes.
Blueprint node `bs:affine-slope`. -/
theorem pointwisePressureSlopeBounds_scale (σ : LimitSide) (s t : ℝ) (hst : s < t) :
    let ℓ := (lowerBirkhoffAverage T u x).toReal
    let b := (upperBirkhoffAverage T u x).toReal
    let f := fun v : ℝ => σ.choose (pointwisePressure P T (fun y => -v * u y) A x)
    f s - ((t - s) * b : ℝ) ≤ f t ∧ f t ≤ f s - ((t - s) * ℓ : ℝ) := by
  intro ℓ b f
  have hℓ := (birkhoffAverage_toReal_bounds T u x hpos hupper).1
  let F := fun v p ↦ σ.timeLimit (fun n ↦
    finiteScalePressureRate P T (fun y ↦ -v * u y) A x n (dyadicRadius p))
  have hlimit (v : ℝ) : Tendsto (F v) atTop (𝓝 (f v)) := by
    have heq : f v = ⨆ p, F v p := by cases σ <;> rfl
    rw [heq]
    exact tendsto_atTop_iSup (timeLimit_pressureRate_monotone_scale P T u A x σ v)
  apply sub_coe_sandwich_of_pos_slack hℓ
  intro η hη hηℓ
  obtain ⟨r₀, hr₀, hbounds⟩ :=
    pressure_slope_bounds_small_radius P T u hu A x hpos hupper σ s t η hst hη
  have hradius : ∀ᶠ p in atTop, dyadicRadius p ≤ r₀ := by
    have hzero : Tendsto dyadicRadius atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact (hzero.eventually (gt_mem_nhds hr₀)).mono fun _ hp ↦ hp.le
  have hslopes : ∀ᶠ p in atTop,
      F s p - ((t - s) * (b + η) : ℝ) ≤ F t p ∧
        F t p ≤ F s p - ((t - s) * (ℓ - η) : ℝ) := by
    filter_upwards [hradius] with p hp
    exact hbounds (dyadicRadius p) (by unfold dyadicRadius; positivity) hp
  exact ⟨le_of_tendsto_of_tendsto (tendsto_sub_coe (hlimit s) tendsto_const_nhds)
      (hlimit t) (hslopes.mono fun _ hp ↦ hp.1),
    le_of_tendsto_of_tendsto (hlimit t) (tendsto_sub_coe (hlimit s) tendsto_const_nhds)
      (hslopes.mono fun _ hp ↦ hp.2)⟩

omit hT in
/-- Positive lower and finite upper averages prevent pressure from being negative infinity. -/
private lemma pointwisePressure_ne_bot
    (σ : LimitSide) (s : ℝ) :
    σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x) ≠ ⊥ := by
  obtain ⟨hℓ, hℓb, hlower, hupper'⟩ :=
    birkhoffAverage_toReal_bounds T u x hpos hupper
  let ℓ := (lowerBirkhoffAverage T u x).toReal
  let b := (upperBirkhoffAverage T u x).toReal
  obtain ⟨r₀, hr₀, hrealizer⟩ :=
    birkhoffRealizerBounds P T u hu x ℓ b hlower hupper'
      (ℓ / 2) (half_pos hℓ)
  obtain ⟨p, hp⟩ : ∃ p : ℕ, dyadicRadius p ≤ r₀ := by
    obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨p, hp.le⟩
  have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  obtain ⟨N, hN, hbounds⟩ := hrealizer (dyadicRadius p) hr hp
  let a := ℓ - ℓ / 2
  let d := b + ℓ / 2
  let c := min (-s * a) (-s * d)
  have hcost : ∀ᶠ n in atTop, (c : EReal) ≤
      finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius p) := by
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
    have hn0 : n ≠ 0 := by omega
    simp only [finiteScalePressureRate, hn0, ↓reduceIte]
    refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    apply EReal.coe_le_coe_iff.mpr
    have hb := hbounds n hn i hi
    have hlinear : c ≤ -s * (birkhoffSum T u n (P.ι i) / n) := by
      rcases le_total 0 s with hs | hs
      · exact (min_le_right _ _).trans
          (mul_le_mul_of_nonpos_left hb.2 (neg_nonpos.mpr hs))
      · exact (min_le_left _ _).trans
          (mul_le_mul_of_nonneg_left hb.1 (neg_nonneg.mpr hs))
    have hsum : birkhoffSum T (fun y ↦ -s * u y) n (P.ι i) =
        -s * birkhoffSum T u n (P.ι i) := by
      simp only [birkhoffSum, Finset.mul_sum]
    rw [hsum, add_div, mul_div_assoc]
    exact hlinear.trans (le_add_of_nonneg_left
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)))
  have hlow : (c : EReal) ≤ liminf (fun n ↦
      finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius p))
      atTop := le_liminf_of_le (by isBoundedDefault) hcost
  have hupp : (c : EReal) ≤ limsup (fun n ↦
      finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius p))
      atTop := hlow.trans liminf_le_limsup
  apply ne_bot_of_gt
  cases σ with
  | lower =>
      change (⊥ : EReal) < ⨆ q, liminf (fun n ↦
        finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius q)) atTop
      exact (EReal.bot_lt_coe c).trans_le (le_iSup_of_le p hlow)
  | upper =>
      change (⊥ : EReal) < ⨆ q, limsup (fun n ↦
        finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius q)) atTop
      exact (EReal.bot_lt_coe c).trans_le (le_iSup_of_le p hupp)

omit hT in
/-- Strict decrease is asserted only when the right-hand pressure is finite.
Blueprint node `bs:affine-slope`. -/
theorem pointwisePressureSlopeBounds_strict (σ : LimitSide) (s t : ℝ) (hst : s < t)
    (hfinite : σ.choose (pointwisePressure P T (fun y => -s * u y) A x) < ⊤) :
    σ.choose (pointwisePressure P T (fun y => -t * u y) A x) <
      σ.choose (pointwisePressure P T (fun y => -s * u y) A x) := by
  let ℓ := (lowerBirkhoffAverage T u x).toReal
  let f := fun v : ℝ ↦ σ.choose (pointwisePressure P T (fun y ↦ -v * u y) A x)
  have hℓ : 0 < ℓ := (birkhoffAverage_toReal_bounds T u x hpos hupper).1
  have hbot : f s ≠ ⊥ := pointwisePressure_ne_bot P T u hu A x hpos hupper σ s
  have hreal : ((f s).toReal : EReal) = f s := EReal.coe_toReal hfinite.ne hbot
  have hbound := (pointwisePressureSlopeBounds_scale
    P T u hu A x hpos hupper σ s t hst).2
  change f t ≤ f s - (((t - s) * ℓ : ℝ) : EReal) at hbound
  change f t < f s
  rw [← hreal] at hbound ⊢
  rw [← EReal.coe_sub] at hbound
  exact hbound.trans_lt (EReal.coe_lt_coe_iff.mpr
    (sub_lt_self _ (mul_pos (sub_pos.mpr hst) hℓ)))

omit hT hu hpos hupper in
/-- A positive linear lower bound on every realizer denominator bounds the BS cost,
multiplied by that slope, by the zero-potential pressure at the same order and radius. -/
private lemma mul_finiteScaleBSCost_le_pressureRate_zero
    (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) (r : ℝ)
    (hb : ∀ i, P.ι i ∈ bowenBall T n x r →
      a * n ≤ birkhoffSum T u n (P.ι i)) :
    ((ENNReal.ofReal a * finiteScaleBSCost P T u A x n r : ℝ≥0∞) : EReal) ≤
      finiteScalePressureRate P T (fun _ ↦ 0) A x n r := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold finiteScalePressureRate
  rw [ite_eq_right hn0]
  refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
  have hUlower := hb i hi
  have hU : 0 < birkhoffSum T u n (P.ι i) := (mul_pos ha hnpos).trans_le hUlower
  have hcost : finiteScaleBSCost P T u A x n r ≤
      (oracleNatComplexity A i : ℝ≥0∞) /
        ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
    unfold finiteScaleBSCost
    rw [ite_eq_right hn0]
    exact iInf_le_of_le i (iInf_le_of_le hi (iInf_le_of_le hU le_rfl))
  have hratio : a * ((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i)) ≤
      (oracleNatComplexity A i : ℝ) / n := by
    apply (le_div_iff₀ hnpos).mpr
    calc
      _ = (a * n) * ((oracleNatComplexity A i : ℝ) /
          birkhoffSum T u n (P.ι i)) := by ring
      _ ≤ birkhoffSum T u n (P.ι i) * ((oracleNatComplexity A i : ℝ) /
          birkhoffSum T u n (P.ι i)) :=
        mul_le_mul_of_nonneg_right hUlower (by positivity)
      _ = (oracleNatComplexity A i : ℝ) := by field_simp
  have hle : ((ENNReal.ofReal a * finiteScaleBSCost P T u A x n r : ℝ≥0∞) : EReal) ≤
      (((oracleNatComplexity A i : ℝ) / n : ℝ) : EReal) := by
    calc
      _ ≤ ((ENNReal.ofReal a * ((oracleNatComplexity A i : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i))) : ℝ≥0∞) : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.mpr (mul_le_mul_right hcost _)
      _ = ((ENNReal.ofReal (a * ((oracleNatComplexity A i : ℝ) /
          birkhoffSum T u n (P.ι i))) : ℝ≥0∞) : EReal) := by
        rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_div_of_pos hU,
          ENNReal.ofReal_natCast]
      _ = ((a * ((oracleNatComplexity A i : ℝ) /
          birkhoffSum T u n (P.ι i)) : ℝ) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
      _ ≤ _ := EReal.coe_le_coe_iff.mpr hratio
  simpa only [birkhoffSum, Finset.sum_const_zero, add_zero] using hle

omit [MetricSpace X] hT hu hpos hupper in
/-- An eventual comparison by a fixed finite slope passes through either time limit
and the scale supremum. Monotonicity of the costs recovers the discarded coarse scales. -/
private lemma mul_iSup_timeLimit_le_of_eventually_le
    (σ : LimitSide) (f : ℕ → ℕ → EReal) (g : ℕ → ℕ → ℝ≥0∞)
    (a : ℝ) (hg : ∀ n, Monotone (fun p ↦ g p n)) (p₀ : ℕ)
    (hfg : ∀ p ≥ p₀, ∀ᶠ n in atTop,
      ((ENNReal.ofReal a * g p n : ℝ≥0∞) : EReal) ≤ f p n) :
    ENNReal.ofReal a * (⨆ p, σ.timeLimit (g p)) ≤
      (⨆ p, σ.timeLimit (f p)).toENNReal := by
  let φ : ℝ≥0∞ → EReal := fun t ↦ ((ENNReal.ofReal a * t : ℝ≥0∞) : EReal)
  have hφmono : Monotone φ := by
    intro c d hcd
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (mul_le_mul_right hcd _)
  have hφcont : Continuous φ :=
    continuous_coe_ennreal_ereal.comp (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top)
  have htime (p : ℕ) (hp : p₀ ≤ p) :
      φ (σ.timeLimit (g p)) ≤ σ.timeLimit (f p) := by
    cases σ with
    | lower =>
      exact (hφmono.map_liminf_of_continuousAt (g p) hφcont.continuousAt).trans_le
        (liminf_le_liminf (hfg p hp))
    | upper =>
      exact (hφmono.map_limsup_of_continuousAt (g p) hφcont.continuousAt).trans_le
        (limsup_le_limsup (hfg p hp))
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p ↦ ?_
  have hmono : σ.timeLimit (g p) ≤ σ.timeLimit (g (max p p₀)) := by
    cases σ with
    | lower => exact liminf_le_liminf (Eventually.of_forall fun n ↦ hg n (le_max_left _ _))
    | upper => exact limsup_le_limsup (Eventually.of_forall fun n ↦ hg n (le_max_left _ _))
  have htime' : ENNReal.ofReal a * σ.timeLimit (g (max p p₀)) ≤
      (σ.timeLimit (f (max p p₀))).toENNReal := by
    simpa only [φ, EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal (htime (max p p₀) (le_max_right _ _))
  exact (mul_le_mul_right hmono _).trans
    (htime'.trans (EReal.toENNReal_le_toENNReal
      (le_iSup (fun q ↦ σ.timeLimit (f q)) (max p p₀))))

omit hT in
/-- Finite relevant orbit complexity implies finite scale-zero pointwise BS dimension.
Blueprint node `bs:pointwise-root`. -/
theorem pointwiseBowenEquation_finite (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ => 0) A x) < ⊤) :
    σ.choose (pointwiseBSDimension P T u A x) < ⊤ := by
  let ℓ := (lowerBirkhoffAverage T u x).toReal
  let b := (upperBirkhoffAverage T u x).toReal
  obtain ⟨hℓ, hℓb, hlow, hupp⟩ := birkhoffAverage_toReal_bounds T u x hpos hupper
  obtain ⟨r₀, hr₀, htail⟩ :=
    birkhoffRealizerBounds P T u hu x ℓ b hlow hupp (ℓ / 2) (by positivity)
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℕ, dyadicRadius p₀ ≤ r₀ := by
    obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨p₀, hp₀.le⟩
  let a := ℓ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hbounds : ∀ p ≥ p₀, ∀ᶠ n in atTop, 1 ≤ n ∧
      ∀ i, P.ι i ∈ bowenBall T n x (dyadicRadius p) →
        a * n ≤ birkhoffSum T u n (P.ι i) := by
    intro p hp
    have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
    have hrle : dyadicRadius p ≤ r₀ := (dyadicRadius_antitone hp).trans hp₀
    obtain ⟨N, hN, hbound⟩ := htail (dyadicRadius p) hr hrle
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn ↦ ⟨hN.trans hn, fun i hi ↦ ?_⟩⟩
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (hN.trans hn)
    apply (le_div_iff₀ hnpos).mp
    have := (hbound n hn i hi).1
    dsimp [a]
    linarith
  have hfg : ∀ p ≥ p₀, ∀ᶠ n in atTop,
      ((ENNReal.ofReal a * finiteScaleBSCost P T u A x n (dyadicRadius p) :
        ℝ≥0∞) : EReal) ≤
        finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p) := by
    intro p hp
    filter_upwards [hbounds p hp] with n hn
    exact mul_finiteScaleBSCost_le_pressureRate_zero P T u A x a ha n hn.1
      (dyadicRadius p) hn.2
  have hmono (n : ℕ) :
      Monotone (fun p ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    intro p q hpq
    exact pointwiseBSDimension_antitone_radius P T u A x n (dyadicRadius_antitone hpq)
  have hbound := mul_iSup_timeLimit_le_of_eventually_le σ
    (fun p n ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p))
    (fun p n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) a hmono p₀ hfg
  have hpressure : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n
        (dyadicRadius p)) := by cases σ <;> rfl
  have hdimension : σ.choose (pointwiseBSDimension P T u A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [← hpressure, ← hdimension] at hbound
  have hproduct : ENNReal.ofReal a * σ.choose (pointwiseBSDimension P T u A x) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.toENNReal_ne_top_iff.mpr hfinite.ne) hbound
  apply lt_top_iff_ne_top.mpr
  intro hdim
  apply hproduct
  rw [hdim, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha).ne']

end Pointwise
end Kolmogorov.PointToSet
