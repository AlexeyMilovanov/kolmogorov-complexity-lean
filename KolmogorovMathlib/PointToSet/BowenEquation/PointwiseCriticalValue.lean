/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation.Pointwise

/-!
# Pointwise Bowen equations and critical values

Under positive lower and finite upper Birkhoff averages, the effective BS dimension is
characterized by the pressure of the potentials `-s u`. When the zero-potential pressure is
finite, the dimension is the unique real zero and gives two affine bounds on the pressure
(blueprint node `bs:pointwise-root`). When it is infinite, both the dimension and all these
pressures are infinite. The positive and nonpositive pressure thresholds therefore recover
the dimension in both cases (blueprint node `bs:pointwise-critical`).

These pointwise characterizations supply the critical values used in the set-level Bowen
equations exported by `KolmogorovMathlib.PointToSet.BowenEquation`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]
section Pointwise
variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (A : Set ℕ) (x : X)
  (hpos : 0 < lowerBirkhoffAverage T u x) (hupper : upperBirkhoffAverage T u x < ⊤)
include hT hu hpos hupper

omit hT in
/-- Extract fixed positive finite bounds valid at every sufficiently small radius. -/
private lemma exists_eventually_realizer_bounds :
    ∃ a b : ℝ, 0 < a ∧
      ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          ∀ᶠ n in atTop, ∀ i, P.ι i ∈ bowenBall T n x r →
            a ≤ birkhoffSum T u n (P.ι i) / n ∧
              birkhoffSum T u n (P.ι i) / n ≤ b := by
  have havg : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x :=
    liminf_le_limsup
  let ℓ := (lowerBirkhoffAverage T u x).toReal
  let b := (upperBirkhoffAverage T u x).toReal
  have hℓtop : lowerBirkhoffAverage T u x ≠ ⊤ := (havg.trans_lt hupper).ne
  have hℓ : 0 < ℓ := EReal.toReal_pos hpos hℓtop
  have hlow : lowerBirkhoffAverage T u x = (ℓ : EReal) :=
    (EReal.coe_toReal hℓtop hpos.ne_bot).symm
  have hupp : upperBirkhoffAverage T u x = (b : EReal) :=
    (EReal.coe_toReal hupper.ne (hpos.trans_le havg).ne_bot).symm
  have hℓb : ℓ ≤ b := by
    rw [hlow, hupp] at havg
    exact EReal.coe_le_coe_iff.mp havg
  obtain ⟨r₀, hr₀, htail⟩ :=
    birkhoffRealizerBounds P T u hu x ℓ b hlow hupp (ℓ / 2) (by positivity)
  refine ⟨ℓ / 2, b + ℓ / 2, by positivity, r₀, hr₀, ?_⟩
  intro r hr hrle
  obtain ⟨N, -, hbound⟩ := htail r hr hrle
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn i hi ↦ ?_⟩
  have hb := hbound n hn i hi
  refine ⟨?_, hb.2⟩
  linarith [hb.1]

omit hT hu hpos hupper in
/-- The zero-potential finite-scale pressure rate time-limit is finite. -/
private lemma timeLimit_pressureRate_zero_lt_top
    (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤) (p : ℕ) :
    σ.timeLimit (fun n ↦
      finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p)) < ⊤ := by
  cases σ
  · exact (le_iSup (fun q ↦ liminf (fun n ↦
      finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius q)) atTop) p).trans_lt hfinite
  · exact (le_iSup (fun q ↦ limsup (fun n ↦
      finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius q)) atTop) p).trans_lt hfinite

omit hT hu hpos hupper in
/-- The finite-scale BS cost limits to the chosen BS dimension. -/
private lemma tendsto_timeLimit_bsCost (σ : LimitSide) :
    Tendsto (fun p ↦ σ.timeLimit (fun n ↦
      finiteScaleBSCost P T u A x n (dyadicRadius p))) atTop
      (𝓝 (σ.choose (pointwiseBSDimension P T u A x))) := by
  have heq : σ.choose (pointwiseBSDimension P T u A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [heq]
  apply tendsto_atTop_iSup
  intro p q hpq
  have hcost (n : ℕ) :=
    pointwiseBSDimension_antitone_radius P T u A x n (dyadicRadius_antitone hpq)
  cases σ
  · exact liminf_le_liminf (Eventually.of_forall hcost)
  · exact limsup_le_limsup (Eventually.of_forall hcost)

omit hT hu hpos hupper in
/-- The finite-scale pressure rate limits to the chosen pressure. -/
private lemma tendsto_timeLimit_pressureRate (σ : LimitSide) (s : ℝ) :
    Tendsto (fun p ↦ σ.timeLimit (fun n ↦
      finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius p))) atTop
      (𝓝 (σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x))) := by
  have heq : σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x) =
      ⨆ p, σ.timeLimit (fun n ↦
        finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [heq]
  exact tendsto_atTop_iSup (timeLimit_pressureRate_monotone_scale P T u A x σ s)

omit hpos hupper hu in
/-- Pass the fixed-radius sandwiches to scale zero with fixed slopes,
assuming dimension finiteness and uniform tail bounds. -/
private lemma pressure_sandwich_of_eventually_realizer_bounds
    (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤)
    (hdim : σ.choose (pointwiseBSDimension P T u A x) < ⊤)
    (a b : ℝ) (ha : 0 < a)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hbounds : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ᶠ n in atTop, ∀ i, P.ι i ∈ bowenBall T n x r →
        a ≤ birkhoffSum T u n (P.ι i) / n ∧
          birkhoffSum T u n (P.ι i) / n ≤ b)
    (s : ℝ) :
    let d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
    let f := σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x)
    ((min (a * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ f ∧
      f ≤ ((max (a * (d - s)) (b * (d - s)) : ℝ) : EReal) := by
  intro d f
  let D := fun p ↦
    (σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))).toReal
  let F := fun p ↦ σ.timeLimit (fun n ↦
    finiteScalePressureRate P T (fun y ↦ -s * u y) A x n (dyadicRadius p))
  have hradius : ∀ᶠ p in atTop, dyadicRadius p ≤ r₀ := by
    have hzero : Tendsto dyadicRadius atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact (hzero.eventually (gt_mem_nhds hr₀)).mono fun _ hp ↦ hp.le
  have hD : Tendsto D atTop (𝓝 d) :=
    (ENNReal.tendsto_toReal hdim.ne).comp (tendsto_timeLimit_bsCost P T u A x σ)
  have hF : Tendsto F atTop (𝓝 f) := tendsto_timeLimit_pressureRate P T u A x σ s
  have hlower : Tendsto (fun p ↦ ((min (a * (D p - s)) (b * (D p - s)) : ℝ) : EReal))
      atTop (𝓝 ((min (a * (d - s)) (b * (d - s)) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr
      ((tendsto_const_nhds.mul (hD.sub_const s)).min
        (tendsto_const_nhds.mul (hD.sub_const s)))
  have hupper : Tendsto (fun p ↦ ((max (a * (D p - s)) (b * (D p - s)) : ℝ) : EReal))
      atTop (𝓝 ((max (a * (d - s)) (b * (d - s)) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr
      ((tendsto_const_nhds.mul (hD.sub_const s)).max
        (tendsto_const_nhds.mul (hD.sub_const s)))
  have hsand : ∀ᶠ p in atTop,
      ((min (a * (D p - s)) (b * (D p - s)) : ℝ) : EReal) ≤ F p ∧
        F p ≤ ((max (a * (D p - s)) (b * (D p - s)) : ℝ) : EReal) := by
    filter_upwards [hradius] with p hp
    have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
    exact finiteScalePointwiseBowenEquation_sandwich P T hT u a b ha A x
      (dyadicRadius p) hr (hbounds _ hr hp) σ
      (timeLimit_pressureRate_zero_lt_top P T A x σ hfinite p) s
  exact ⟨le_of_tendsto_of_tendsto hlower hF (hsand.mono fun _ hp ↦ hp.1),
    le_of_tendsto_of_tendsto hF hupper (hsand.mono fun _ hp ↦ hp.2)⟩

/-- Main C: the finite pointwise BS dimension solves its scale-zero Bowen equation.
Blueprint node `bs:pointwise-root`. -/
theorem pointwiseBowenEquation (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ => 0) A x) < ⊤) :
    let d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
    σ.choose (pointwisePressure P T (fun y => -d * u y) A x) = 0 := by
  intro d
  have hdim := pointwiseBowenEquation_finite P T u hu A x hpos hupper σ hfinite
  obtain ⟨a, b, ha, r₀, hr₀, hbounds⟩ := exists_eventually_realizer_bounds P T u hu x hpos hupper
  have hsand := pressure_sandwich_of_eventually_realizer_bounds P T hT u A x σ hfinite hdim
    a b ha r₀ hr₀ hbounds d
  simp only [d, sub_self, mul_zero, min_self, max_self, EReal.coe_zero] at hsand
  exact le_antisymm hsand.2 hsand.1

/-- The scale-zero pressure sandwich uses the actual lower and upper averages.
Blueprint node `bs:pointwise-root`. -/
theorem pointwiseBowenEquation_sandwich (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ => 0) A x) < ⊤) (s : ℝ) :
    let d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
    let ℓ := (lowerBirkhoffAverage T u x).toReal
    let b := (upperBirkhoffAverage T u x).toReal
    let f := σ.choose (pointwisePressure P T (fun y => -s * u y) A x)
    ((min (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ f ∧
      f ≤ ((max (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) := by
  intro d ℓ b f
  let F : ℝ → EReal := fun t ↦
    σ.choose (pointwisePressure P T (fun y ↦ -t * u y) A x)
  have hd : F d = 0 :=
    pointwiseBowenEquation P T hT u hu A x hpos hupper σ hfinite
  change ((min (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ F s ∧
    F s ≤ ((max (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal)
  rcases lt_trichotomy s d with hs | hs | hs
  · have H := pointwisePressureSlopeBounds_scale
      P T u hu A x hpos hupper σ s d hs
    change F s - (((d - s) * b : ℝ) : EReal) ≤ F d ∧
      F d ≤ F s - (((d - s) * ℓ : ℝ) : EReal) at H
    rw [hd] at H
    have upper := EReal.sub_nonpos.mp H.1
    have lower : (((d - s) * ℓ : ℝ) : EReal) ≤ F s := by
      simpa only [zero_add] using EReal.add_le_of_le_sub H.2
    rw [mul_comm (d - s) ℓ] at lower
    rw [mul_comm (d - s) b] at upper
    exact ⟨(EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans lower,
      upper.trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))⟩
  · rw [hs, hd]
    simp
  · have H := pointwisePressureSlopeBounds_scale
      P T u hu A x hpos hupper σ d s hs
    change F d - (((s - d) * b : ℝ) : EReal) ≤ F s ∧
      F s ≤ F d - (((s - d) * ℓ : ℝ) : EReal) at H
    rw [hd] at H
    change (((0 - (s - d) * b : ℝ) : EReal) ≤ F s ∧
      F s ≤ ((0 - (s - d) * ℓ : ℝ) : EReal)) at H
    have eb : 0 - (s - d) * b = b * (d - s) := by ring
    have eℓ : 0 - (s - d) * ℓ = ℓ * (d - s) := by ring
    rw [eb, eℓ] at H
    exact ⟨(EReal.coe_le_coe_iff.mpr (min_le_right _ _)).trans H.1,
      H.2.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))⟩

/-- The finite pointwise dimension is the unique real pressure zero.
Blueprint node `bs:pointwise-root`. -/
theorem pointwiseBowenEquation_unique (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ => 0) A x) < ⊤) (s : ℝ) :
    σ.choose (pointwisePressure P T (fun y => -s * u y) A x) = 0 ↔
      s = (σ.choose (pointwiseBSDimension P T u A x)).toReal := by
  let d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
  let f := fun s ↦ σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x)
  have hd : f d = 0 := pointwiseBowenEquation P T hT u hu A x hpos hupper σ hfinite
  change f s = 0 ↔ s = d
  constructor
  · intro hs
    rcases lt_trichotomy s d with h | h | h
    · have hfin : f s < ⊤ := by rw [hs]; exact EReal.zero_lt_top
      have hlt := pointwisePressureSlopeBounds_strict P T u hu A x hpos hupper σ s d h hfin
      change f d < f s at hlt
      rw [hd, hs] at hlt
      exact False.elim (lt_irrefl _ hlt)
    · exact h
    · have hfin : f d < ⊤ := by rw [hd]; exact EReal.zero_lt_top
      have hlt := pointwisePressureSlopeBounds_strict P T u hu A x hpos hupper σ d s h hfin
      change f s < f d at hlt
      rw [hd, hs] at hlt
      exact False.elim (lt_irrefl _ hlt)
  · rintro rfl
    exact hd

omit hT in
/-- At every sufficiently fine dyadic scale, the positive realizer averages have one
common finite positive upper bound on an eventual tail of positive orders. -/
private lemma exists_eventually_pos_realizer_average_le :
    ∃ B : ℝ, 0 < B ∧ ∃ p₀ : ℕ, ∀ p ≥ p₀,
      ∀ᶠ n in atTop, 1 ≤ n ∧
        ∀ i, P.ι i ∈ bowenBall T n x (dyadicRadius p) →
          0 < birkhoffSum T u n (P.ι i) ∧
          birkhoffSum T u n (P.ι i) / n ≤ B := by
  have havg : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x :=
    liminf_le_limsup
  let ℓ := (lowerBirkhoffAverage T u x).toReal
  let b := (upperBirkhoffAverage T u x).toReal
  have hℓtop : lowerBirkhoffAverage T u x ≠ ⊤ := (havg.trans_lt hupper).ne
  have hℓ : 0 < ℓ := EReal.toReal_pos hpos hℓtop
  have hlow : lowerBirkhoffAverage T u x = (ℓ : EReal) :=
    (EReal.coe_toReal hℓtop hpos.ne_bot).symm
  have hupp : upperBirkhoffAverage T u x = (b : EReal) :=
    (EReal.coe_toReal hupper.ne (hpos.trans_le havg).ne_bot).symm
  have hℓb : ℓ ≤ b := by
    rw [hlow, hupp] at havg
    exact EReal.coe_le_coe_iff.mp havg
  obtain ⟨r₀, hr₀, htail⟩ :=
    birkhoffRealizerBounds P T u hu x ℓ b hlow hupp (ℓ / 2) (by positivity)
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℕ, dyadicRadius p₀ ≤ r₀ := by
    obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨p₀, hp₀.le⟩
  refine ⟨b + ℓ / 2, by linarith, p₀, ?_⟩
  intro p hp
  have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  have hrle : dyadicRadius p ≤ r₀ := (dyadicRadius_antitone hp).trans hp₀
  obtain ⟨N, hN, hbound⟩ := htail (dyadicRadius p) hr hrle
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn ↦ ⟨hN.trans hn, fun i hi ↦ ?_⟩⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (hN.trans hn)
  have hb := hbound n hn i hi
  refine ⟨?_, hb.2⟩
  have hratio : 0 < birkhoffSum T u n (P.ι i) / n := by linarith [hb.1]
  exact (div_pos_iff_of_pos_right hnpos).mp hratio

omit hT hu hpos hupper in
/-- At a positive order, an upper bound `B` on realizer averages bounds zero-potential
pressure by `B` times the positive-denominator ratio infimum. -/
private lemma pressureRate_zero_le_mul_finiteScaleBSCost
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 1 ≤ n) (r : ℝ)
    (hb : ∀ i, P.ι i ∈ bowenBall T n x r →
      birkhoffSum T u n (P.ι i) / n ≤ B) :
    finiteScalePressureRate P T (fun _ ↦ 0) A x n r ≤
      ((ENNReal.ofReal B * finiteScaleBSCost P T u A x n r : ℝ≥0∞) : EReal) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hB0 : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hB).ne'
  have hle : (finiteScalePressureRate P T (fun _ ↦ 0) A x n r).toENNReal ≤
      ENNReal.ofReal B * finiteScaleBSCost P T u A x n r := by
    unfold finiteScaleBSCost
    rw [ite_eq_right hn0]
    simp_rw [ENNReal.mul_iInf_of_ne hB0 ENNReal.ofReal_ne_top]
    refine le_iInf fun i ↦ le_iInf fun hi ↦ le_iInf fun hU ↦ ?_
    have hrate : finiteScalePressureRate P T (fun _ ↦ 0) A x n r ≤
        (((oracleNatComplexity A i : ℝ) / n : ℝ) : EReal) := by
      unfold finiteScalePressureRate
      rw [ite_eq_right hn0]
      simpa only [birkhoffSum, Finset.sum_const_zero, add_zero] using
        (iInf_le_of_le i (iInf_le_of_le hi le_rfl))
    have hUupper : birkhoffSum T u n (P.ι i) ≤ B * n :=
      (div_le_iff₀ hnpos).mp (hb i hi)
    have hratio : (oracleNatComplexity A i : ℝ) / n ≤
        B * ((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hU).mpr
      calc
        (oracleNatComplexity A i : ℝ) / n * birkhoffSum T u n (P.ι i) ≤
            (oracleNatComplexity A i : ℝ) / n * (B * n) :=
          mul_le_mul_of_nonneg_left hUupper (by positivity)
        _ = B * (oracleNatComplexity A i : ℝ) := by field_simp
    calc
      (finiteScalePressureRate P T (fun _ ↦ 0) A x n r).toENNReal ≤
          ENNReal.ofReal ((oracleNatComplexity A i : ℝ) / n) :=
        EReal.toENNReal_le_toENNReal hrate
      _ ≤ ENNReal.ofReal (B * ((oracleNatComplexity A i : ℝ) /
          birkhoffSum T u n (P.ι i))) := ENNReal.ofReal_le_ofReal hratio
      _ = ENNReal.ofReal B * ((oracleNatComplexity A i : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i))) := by
        rw [ENNReal.ofReal_mul hB.le, ENNReal.ofReal_div_of_pos hU,
          ENNReal.ofReal_natCast]
  calc
    finiteScalePressureRate P T (fun _ ↦ 0) A x n r ≤
        ((finiteScalePressureRate P T (fun _ ↦ 0) A x n r).toENNReal : EReal) := by
      rw [EReal.coe_toENNReal_eq_max]
      exact le_max_right _ _
    _ ≤ ((ENNReal.ofReal B * finiteScaleBSCost P T u A x n r : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle

omit [MetricSpace X] hT hu hpos hupper in
/-- An eventual comparison by a fixed finite nonnegative factor passes to either time
limit and then to the scale supremum, using monotonicity only for the left side. -/
private lemma iSup_timeLimit_le_mul_of_eventually_le
    (σ : LimitSide) (f : ℕ → ℕ → EReal) (g : ℕ → ℕ → ℝ≥0∞)
    (B : ℝ) (hf : ∀ n, Monotone (fun p ↦ f p n)) (p₀ : ℕ)
    (hfg : ∀ p ≥ p₀, ∀ᶠ n in atTop,
      f p n ≤ ((ENNReal.ofReal B * g p n : ℝ≥0∞) : EReal)) :
    (⨆ p, σ.timeLimit (f p)) ≤
      ((ENNReal.ofReal B * (⨆ p, σ.timeLimit (g p)) : ℝ≥0∞) : EReal) := by
  let φ : ℝ≥0∞ → EReal := fun t ↦ ((ENNReal.ofReal B * t : ℝ≥0∞) : EReal)
  have hφmono : Monotone φ := by
    intro a b hab
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    gcongr
  have hφcont : Continuous φ :=
    continuous_coe_ennreal_ereal.comp (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top)
  have htime (p : ℕ) (hp : p₀ ≤ p) :
      σ.timeLimit (f p) ≤ φ (σ.timeLimit (g p)) := by
    cases σ with
    | lower =>
      exact (liminf_le_liminf (hfg p hp)).trans_eq
        (hφmono.map_liminf_of_continuousAt (g p) hφcont.continuousAt).symm
    | upper =>
      exact (limsup_le_limsup (hfg p hp)).trans_eq
        (hφmono.map_limsup_of_continuousAt (g p) hφcont.continuousAt).symm
  apply iSup_le
  intro p
  have hmono : σ.timeLimit (f p) ≤ σ.timeLimit (f (max p p₀)) := by
    cases σ with
    | lower => exact liminf_le_liminf (Eventually.of_forall fun n ↦ hf n (le_max_left _ _))
    | upper => exact limsup_le_limsup (Eventually.of_forall fun n ↦ hf n (le_max_left _ _))
  exact hmono.trans ((htime (max p p₀) (le_max_right _ _)).trans
    (hφmono (le_iSup (fun q ↦ σ.timeLimit (g q)) (max p p₀))))

omit hT in
/-- Infinite orbit complexity forces infinite pointwise BS dimension.
Blueprint node `bs:pointwise-critical`. -/
theorem pointwiseBowenCriticalValue_infinite (σ : LimitSide)
    (hinfinite : σ.choose (pointwisePressure P T (fun _ => 0) A x) = ⊤) :
    σ.choose (pointwiseBSDimension P T u A x) = ⊤ := by
  obtain ⟨B, hB, p₀, htail⟩ :=
    exists_eventually_pos_realizer_average_le P T u hu x hpos hupper
  have hfg : ∀ p ≥ p₀, ∀ᶠ n in atTop,
      finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p) ≤
        ((ENNReal.ofReal B * finiteScaleBSCost P T u A x n (dyadicRadius p) : ℝ≥0∞) :
          EReal) := by
    intro p hp
    filter_upwards [htail p hp] with n hn
    exact pressureRate_zero_le_mul_finiteScaleBSCost P T u A x B hB n hn.1
      (dyadicRadius p) (fun i hi ↦ (hn.2 i hi).2)
  have hmono (n : ℕ) :
      Monotone (fun p ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p)) := by
    intro p q hpq
    unfold finiteScalePressureRate
    split_ifs
    · exact le_rfl
    · refine iInf_mono fun i ↦ le_iInf fun hi ↦ ?_
      have hrad : dyadicRadius q ≤ dyadicRadius p := dyadicRadius_antitone hpq
      have hi' : P.ι i ∈ bowenBall T n x (dyadicRadius p) := by
        simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq] at hi ⊢
        intro k hk
        exact (hi k hk).trans_le hrad
      exact iInf_le_of_le hi' le_rfl
  have hbound := iSup_timeLimit_le_mul_of_eventually_le σ
    (fun p n ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p))
    (fun p n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) B hmono p₀ hfg
  have hpressure : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n
        (dyadicRadius p)) := by cases σ <;> rfl
  have hdimension : σ.choose (pointwiseBSDimension P T u A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [← hpressure, ← hdimension, hinfinite] at hbound
  have htop : ENNReal.ofReal B * σ.choose (pointwiseBSDimension P T u A x) = ⊤ :=
    EReal.coe_ennreal_eq_top_iff.mp (top_le_iff.mp hbound)
  exact (ENNReal.mul_eq_top.mp htop).resolve_right (fun h ↦ ENNReal.ofReal_ne_top h.1) |>.2

omit hT in
/-- Infinite orbit complexity forces infinite pressure at every real parameter.
Blueprint node `bs:pointwise-critical`. -/
theorem pointwiseBowenCriticalValue_infinite_pressure (σ : LimitSide)
    (hinfinite : σ.choose (pointwisePressure P T (fun _ => 0) A x) = ⊤) (s : ℝ) :
    σ.choose (pointwisePressure P T (fun y => -s * u y) A x) = ⊤ := by
  let f := fun v : ℝ ↦ σ.choose (pointwisePressure P T (fun y ↦ -v * u y) A x)
  have hf0 : f 0 = ⊤ := by simpa only [f, neg_zero, zero_mul] using hinfinite
  change f s = ⊤
  rcases lt_trichotomy s 0 with h | rfl | h
  · have hbound := (pointwisePressureSlopeBounds_scale
      P T u hu A x hpos hupper σ s 0 h).2
    change f 0 ≤ f s - ((0 - s) * (lowerBirkhoffAverage T u x).toReal : ℝ) at hbound
    rw [hf0] at hbound
    apply top_le_iff.mp
    simpa only [EReal.top_add_coe] using EReal.add_le_of_le_sub hbound
  · exact hf0
  · have hbound := (pointwisePressureSlopeBounds_scale
      P T u hu A x hpos hupper σ 0 s h).1
    change f 0 - ((s - 0) * (upperBirkhoffAverage T u x).toReal : ℝ) ≤ f s at hbound
    rw [hf0, EReal.top_sub_coe] at hbound
    exact top_le_iff.mp hbound

omit [MetricSpace X] P T hT u hu A x hpos hupper in
/-- If a function is positive for all nonnegative inputs, its positive threshold is infinity. -/
private lemma positivePressureThreshold_eq_top_of_pos
    (f : ℝ → EReal) (hf_pos : ∀ s, 0 ≤ s → 0 < f s) :
    positivePressureThreshold f = ⊤ := by
  unfold positivePressureThreshold
  apply le_antisymm le_top
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r _ _
  have ⟨s, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ (r : ℝ) < s := by
    use (r : ℝ) + 1
    have h1 : 0 ≤ (r : ℝ) + 1 := by exact add_nonneg (NNReal.coe_nonneg r) zero_le_one
    refine ⟨h1, by linarith⟩
  have hr_lt_s : (r : ℝ≥0∞) < ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg r)).mpr hs.2
  apply le_trans hr_lt_s.le
  apply le_iSup_of_le s
  apply le_iSup_of_le hs.1
  apply le_iSup_of_le (hf_pos s hs.1)
  exact le_rfl

omit [MetricSpace X] P T hT u hu A x hpos hupper in
/-- If a function is positive exactly below a threshold, its positive threshold is that value. -/
private lemma positivePressureThreshold_eq_of_pos_iff
    (f : ℝ → EReal) (d : ℝ)
    (hiff : ∀ s, 0 ≤ s → (0 < f s ↔ s < d)) :
    positivePressureThreshold f = ENNReal.ofReal d := by
  unfold positivePressureThreshold
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    apply iSup_le
    intro hfs
    have h_lt : s < d := (hiff s hs).mp hfs
    exact ENNReal.ofReal_le_ofReal h_lt.le
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r _ hr_lt
    have h_lt_d : (r : ℝ) < d := by
      have h1 : (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by exact ENNReal.ofReal_coe_nnreal.symm
      rw [h1] at hr_lt
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg r)).mp hr_lt
    have ⟨s, hs1, hs2⟩ := exists_between h_lt_d
    have hs_nonneg : 0 ≤ s := le_trans (NNReal.coe_nonneg r) (le_of_lt hs1)
    have hfs : 0 < f s := (hiff s hs_nonneg).mpr hs2
    have hr_lt_s : (r : ℝ≥0∞) < ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg r)).mpr hs1
    apply le_trans hr_lt_s.le
    apply le_iSup_of_le s
    apply le_iSup_of_le hs_nonneg
    apply le_iSup_of_le hfs
    exact le_rfl

omit [MetricSpace X] P T hT u hu A x hpos hupper in
/-- If a function is sandwiched by slopes, its positive values are bounded by the root. -/
private lemma pos_iff_lt_of_affine_sandwich
    (f : ℝ → EReal)
    (d ℓ b : ℝ)
    (h_sand : ∀ s : ℝ,
    ((min (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ f s ∧
      f s ≤ ((max (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal))
    (hl_pos : 0 < ℓ)
    (hb_pos : 0 < b)
    (s : ℝ) :
    0 < f s ↔ s < d := by
  constructor
  · intro h0
    have h_upper_bound := (h_sand s).2
    have hm : (0 : EReal) < ((max (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) := lt_of_lt_of_le h0
      h_upper_bound
    rw [EReal.coe_pos] at hm
    rw [lt_max_iff] at hm
    rcases hm with hm_l | hm_b
    · exact sub_pos.mp (pos_of_mul_pos_right hm_l (le_of_lt hl_pos))
    · exact sub_pos.mp (pos_of_mul_pos_right hm_b (le_of_lt hb_pos))
  · intro hlt
    have h_lower_bound := (h_sand s).1
    have hs_pos : 0 < d - s := sub_pos.mpr hlt
    have hl_mul : 0 < ℓ * (d - s) := mul_pos hl_pos hs_pos
    have hb_mul : 0 < b * (d - s) := mul_pos hb_pos hs_pos
    have hm : 0 < min (ℓ * (d - s)) (b * (d - s)) := lt_min hl_mul hb_mul
    have hm_ereal : (0 : EReal) < ((min (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) := by
      exact EReal.coe_pos.mpr hm
    exact lt_of_lt_of_le hm_ereal h_lower_bound

omit [MetricSpace X] P T hT u hu A x hpos hupper in
/-- If a function is nonpositive exactly above a threshold, its nonpositive threshold is that
value. -/
private lemma nonpositivePressureThreshold_eq_of_nonpos_iff
    (f : ℝ → EReal) (d : ℝ) (hd : 0 ≤ d)
    (hiff : ∀ s, 0 ≤ s → (f s ≤ 0 ↔ d ≤ s)) :
    nonpositivePressureThreshold f = ENNReal.ofReal d := by
  unfold nonpositivePressureThreshold
  apply le_antisymm
  · apply iInf_le_of_le d
    apply iInf_le_of_le hd
    have hfd : f d ≤ 0 := (hiff d hd).mpr le_rfl
    apply iInf_le_of_le hfd
    exact le_rfl
  · apply le_iInf
    intro s
    apply le_iInf
    intro hs
    apply le_iInf
    intro hfs
    have h_le : d ≤ s := (hiff s hs).mp hfs
    exact ENNReal.ofReal_le_ofReal h_le

omit [MetricSpace X] P T hT u hu A x hpos hupper in
/-- If a function is sandwiched by slopes, its nonpositive values are bounded by the root. -/
private lemma nonpos_iff_le_of_affine_sandwich
    (f : ℝ → EReal)
    (d ℓ b : ℝ)
    (h_sand : ∀ s : ℝ,
    ((min (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ f s ∧
      f s ≤ ((max (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal))
    (hl_pos : 0 < ℓ)
    (hb_pos : 0 < b)
    (s : ℝ) :
    f s ≤ 0 ↔ d ≤ s := by
  simpa only [not_lt] using
    (not_congr (pos_iff_lt_of_affine_sandwich f d ℓ b h_sand hl_pos hb_pos s))

omit [MetricSpace X] P T hT u hu A x hpos hupper in
/-- If a function is strictly positive for all nonnegative inputs, its nonpositive threshold is
infinity. -/
private lemma nonpositivePressureThreshold_eq_top_of_pos
    (f : ℝ → EReal) (hf : ∀ s, 0 ≤ s → ¬ (f s ≤ 0)) :
    nonpositivePressureThreshold f = ⊤ := by
  unfold nonpositivePressureThreshold
  apply le_antisymm le_top
  apply le_iInf
  intro s
  apply le_iInf
  intro hs
  apply le_iInf
  intro hfs
  exfalso
  exact hf s hs hfs

/-- The pointwise dimension is the nonnegative positive-pressure threshold, including infinity.
Blueprint node `bs:pointwise-critical`. -/
theorem pointwiseBowenCriticalValue (σ : LimitSide) :
    σ.choose (pointwiseBSDimension P T u A x) = positivePressureThreshold
      (fun s => σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) := by
  let f := fun s ↦ σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x)
  by_cases hinf : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) = ⊤
  · have hdim_inf := pointwiseBowenCriticalValue_infinite P T u hu A x hpos hupper σ hinf
    rw [hdim_inf]
    have hf_pos : ∀ s : ℝ, 0 ≤ s → 0 < f s := by
      intro s _
      have hp := pointwiseBowenCriticalValue_infinite_pressure P T u hu A x hpos hupper σ hinf s
      have h1 : f s = ⊤ := hp
      rw [h1]
      exact EReal.zero_lt_top
    exact Eq.symm (positivePressureThreshold_eq_top_of_pos f hf_pos)
  · have hfin : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤ := lt_top_iff_ne_top.mpr hinf
    have hdim_fin := pointwiseBowenEquation_finite P T u hu A x hpos hupper σ hfin
    have hd_eq : σ.choose (pointwiseBSDimension P T u A x) =
        ENNReal.ofReal (σ.choose (pointwiseBSDimension P T u A x)).toReal :=
      (ENNReal.ofReal_toReal hdim_fin.ne).symm
    rw [hd_eq]
    let d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
    have h_le : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := liminf_le_limsup
    have h_lt_top : lowerBirkhoffAverage T u x < ⊤ := lt_of_le_of_lt h_le hupper
    have hl_pos : 0 < (lowerBirkhoffAverage T u x).toReal :=
      EReal.toReal_pos hpos h_lt_top.ne
    have hb_pos : 0 < (upperBirkhoffAverage T u x).toReal :=
      EReal.toReal_pos (hpos.trans_le h_le) hupper.ne
    have hiff : ∀ s, 0 ≤ s → (0 < f s ↔ s < d) := fun s _ ↦ pos_iff_lt_of_affine_sandwich f d
      ((lowerBirkhoffAverage T u x).toReal) ((upperBirkhoffAverage T u x).toReal)
      (pointwiseBowenEquation_sandwich P T hT u hu A x hpos hupper σ hfin) hl_pos hb_pos s
    exact Eq.symm (positivePressureThreshold_eq_of_pos_iff f d hiff)

/-- The same pointwise dimension is the nonpositive-pressure threshold.
Blueprint node `bs:pointwise-critical`. -/
theorem pointwiseBowenCriticalValue_nonpositive (σ : LimitSide) :
    σ.choose (pointwiseBSDimension P T u A x) = nonpositivePressureThreshold
      (fun s => σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) := by
  let f := fun s ↦ σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x)
  by_cases hinf : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) = ⊤
  · have hdim_inf := pointwiseBowenCriticalValue_infinite P T u hu A x hpos hupper σ hinf
    rw [hdim_inf]
    have hf_pos : ∀ s : ℝ, 0 ≤ s → ¬ (f s ≤ 0) := by
      intro s _
      have hp := pointwiseBowenCriticalValue_infinite_pressure P T u hu A x hpos hupper σ hinf s
      have h1 : f s = ⊤ := hp
      rw [h1]
      exact not_le.mpr EReal.zero_lt_top
    exact Eq.symm (nonpositivePressureThreshold_eq_top_of_pos f hf_pos)
  · have hfin : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤ := lt_top_iff_ne_top.mpr hinf
    have hdim_fin := pointwiseBowenEquation_finite P T u hu A x hpos hupper σ hfin
    have hd_eq : σ.choose (pointwiseBSDimension P T u A x) =
        ENNReal.ofReal (σ.choose (pointwiseBSDimension P T u A x)).toReal :=
      (ENNReal.ofReal_toReal hdim_fin.ne).symm
    rw [hd_eq]
    let d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
    have hd_nonneg : 0 ≤ d := ENNReal.toReal_nonneg
    have h_le : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := liminf_le_limsup
    have h_lt_top : lowerBirkhoffAverage T u x < ⊤ := lt_of_le_of_lt h_le hupper
    have hl_pos : 0 < (lowerBirkhoffAverage T u x).toReal :=
      EReal.toReal_pos hpos h_lt_top.ne
    have hb_pos : 0 < (upperBirkhoffAverage T u x).toReal :=
      EReal.toReal_pos (hpos.trans_le h_le) hupper.ne
    have hiff : ∀ s, 0 ≤ s → (f s ≤ 0 ↔ d ≤ s) := fun s _ ↦ nonpos_iff_le_of_affine_sandwich f d
      ((lowerBirkhoffAverage T u x).toReal) ((upperBirkhoffAverage T u x).toReal)
      (pointwiseBowenEquation_sandwich P T hT u hu A x hpos hupper σ hfin) hl_pos hb_pos s
    exact Eq.symm (nonpositivePressureThreshold_eq_of_nonpos_iff f d hd_nonneg hiff)

/-- For a finite dimension the positive-pressure ray ends exactly at that dimension.
Blueprint node `bs:pointwise-critical`. -/
theorem pointwiseBowenCriticalValue_positive_iff (σ : LimitSide)
    (hfinite : σ.choose (pointwiseBSDimension P T u A x) < ⊤) (s : ℝ) :
    0 < σ.choose (pointwisePressure P T (fun y => -s * u y) A x) ↔
      s < (σ.choose (pointwiseBSDimension P T u A x)).toReal := by
  have hcomp : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤ := by
    by_contra h
    push Not at h
    have h' := pointwiseBowenCriticalValue_infinite P T u hu A x hpos hupper σ (top_le_iff.mp h)
    rw [h'] at hfinite
    exact not_top_lt hfinite
  have h_le : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := liminf_le_limsup
  have hl_pos : 0 < (lowerBirkhoffAverage T u x).toReal :=
    EReal.toReal_pos hpos (h_le.trans_lt hupper).ne
  have hb_pos : 0 < (upperBirkhoffAverage T u x).toReal :=
    EReal.toReal_pos (hpos.trans_le h_le) hupper.ne
  exact pos_iff_lt_of_affine_sandwich
    (fun s ↦ σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x))
    (σ.choose (pointwiseBSDimension P T u A x)).toReal
    (lowerBirkhoffAverage T u x).toReal (upperBirkhoffAverage T u x).toReal
    (pointwiseBowenEquation_sandwich P T hT u hu A x hpos hupper σ hcomp) hl_pos hb_pos s

end Pointwise
end Kolmogorov.PointToSet
