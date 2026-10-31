/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation.PointwiseCriticalValue

/-!
# Critical values of the classical Bowen pressure of a set

For a set `Z` of points with positive and finite Birkhoff averages, this file identifies the
classical lower and upper Barreira–Schmeling dimension of `Z` with the two critical values of the
set pressure `s ↦ P^Z_σ(s)` (the pressure of the potential `-s * u`): the supremum of the
parameters with positive pressure and the infimum of the parameters with nonpositive pressure
(blueprint nodes `bs:set-critical`, `bs:supremum-critical`, `bs:set-slope-join` and
`bs:dense-threshold`).

* `monotoneDenseAgreementCriticalValue`: two nonincreasing maps which agree on the nonnegative
  rationals have the same positive threshold.
* `supPointwiseBSDimensionCriticalValue` and its variants: for each oracle `A`, the supremum of the
  pointwise dimensions is both critical value of the supremum of the pointwise pressures.
* `setPressureSlopeAndRationalAttainment` and its variants: the classical set pressure is
  nonincreasing in the parameter, with a quantitative slope under a uniform lower bound on the
  Birkhoff averages, and a single oracle (together with every oracle above it) attains the
  dimension and the pressure minima at all nonnegative rational parameters.
* `setBowenCriticalValue` and its variants: the critical values of the classical pressure equal the
  classical dimension, and also the minimum over oracles of the pointwise critical values.

These results feed the root-existence and uniqueness statements of
`KolmogorovMathlib.PointToSet.BowenEquation.SetRoot` and the conformal dimension theorem.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability

section Thresholds

/-- The positive threshold commutes with a supremum of maps over an index set. -/
private lemma positivePressureThreshold_biSup {ι : Type*} {s : Set ι} {f : ι → ℝ → EReal} :
    positivePressureThreshold (fun t : ℝ ↦ ⨆ x ∈ s, f x t) =
      ⨆ x ∈ s, positivePressureThreshold (f x) := by
  unfold positivePressureThreshold
  refine le_antisymm (iSup_le fun t ↦ iSup_le fun ht ↦ iSup_le fun hpos ↦ ?_)
    (iSup₂_le fun x hx ↦ iSup_le fun t ↦ iSup_le fun ht ↦ iSup_le fun hpos ↦ ?_)
  · obtain ⟨x, hx, hxpos⟩ : ∃ x ∈ s, 0 < f x t := by
      simpa only [lt_iSup_iff, exists_prop] using hpos
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le t ht (le_iSup_of_le hxpos le_rfl))
  · have hpos' : 0 < ⨆ x ∈ s, f x t := hpos.trans_le (le_iSup₂_of_le x hx le_rfl)
    exact le_iSup₂_of_le t ht (le_iSup_of_le hpos' le_rfl)

/-- One half of `monotoneDenseAgreementCriticalValue`: if `f` is nonincreasing and agrees with `g`
on the nonnegative rationals, the positive threshold of `f` is at most that of `g`. -/
private lemma positivePressureThreshold_le_of_rat_eq {f g : ℝ → EReal}
    (hf : AntitoneOn f (Set.Ici 0)) (hagree : ∀ q : ℚ, 0 ≤ q → f q = g q) :
    positivePressureThreshold f ≤ positivePressureThreshold g := by
  by_contra hnot
  obtain ⟨q, hq, hgq, hqf⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (lt_of_not_ge hnot)
  have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  change positivePressureThreshold g < ENNReal.ofReal (q : ℝ) at hgq
  change ENNReal.ofReal (q : ℝ) < positivePressureThreshold f at hqf
  unfold positivePressureThreshold at hqf
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hqf
  obtain ⟨ht0, ht⟩ := lt_iSup_iff.mp ht
  obtain ⟨hft, hqt⟩ := lt_iSup_iff.mp ht
  have hqt' : (q : ℝ) ≤ t := ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq0).mp hqt).le
  have hgq_pos : 0 < g q := by
    rw [← hagree q hq]
    exact hft.trans_le (hf hq0 ht0 hqt')
  exact hgq.not_ge (le_iSup_of_le (q : ℝ)
    (le_iSup_of_le hq0 (le_iSup_of_le hgq_pos le_rfl)))

/-- Two nonincreasing maps on `[0, ∞)` which agree on the nonnegative rationals have the same
positive threshold. No continuity is needed. Blueprint node `bs:dense-threshold`. -/
theorem monotoneDenseAgreementCriticalValue (f g : ℝ → EReal)
    (hf : AntitoneOn f (Set.Ici 0)) (hg : AntitoneOn g (Set.Ici 0))
    (hagree : ∀ q : ℚ, 0 ≤ q → f q = g q) :
    positivePressureThreshold f = positivePressureThreshold g :=
  le_antisymm (positivePressureThreshold_le_of_rat_eq hf hagree)
    (positivePressureThreshold_le_of_rat_eq hg fun q hq ↦ (hagree q hq).symm)

/-- One half of `nonpositivePressureThreshold_eq_of_rat_eq`: if `g` is nonincreasing and agrees
with `f` on the nonnegative rationals, the nonpositive threshold of `f` is at most that of `g`. -/
theorem nonpositivePressureThreshold_le_of_rat_eq {f g : ℝ → EReal}
    (hg : AntitoneOn g (Set.Ici 0)) (hagree : ∀ q : ℚ, 0 ≤ q → f q = g q) :
    nonpositivePressureThreshold f ≤ nonpositivePressureThreshold g := by
  by_contra h
  obtain ⟨q, hq, hgq, hqf⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (lt_of_not_ge h)
  have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  change nonpositivePressureThreshold g < ENNReal.ofReal (q : ℝ) at hgq
  change ENNReal.ofReal (q : ℝ) < nonpositivePressureThreshold f at hqf
  unfold nonpositivePressureThreshold at hgq
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp hgq
  obtain ⟨hs0, hs⟩ := iInf_lt_iff.mp hs
  obtain ⟨hgs, hsq⟩ := iInf_lt_iff.mp hs
  have hsq' : s ≤ (q : ℝ) := ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs0).mp hsq).le
  have hfq : f q ≤ 0 := by
    rw [hagree q hq]
    exact (hg hs0 hq0 hsq').trans hgs
  have hle : nonpositivePressureThreshold f ≤ ENNReal.ofReal (q : ℝ) :=
    iInf_le_of_le (q : ℝ) (iInf_le_of_le hq0 (iInf_le_of_le hfq le_rfl))
  exact hqf.not_ge hle

/-- Two nonincreasing maps on `[0, ∞)` which agree on the nonnegative rationals have the same
nonpositive threshold, including thresholds equal to zero or infinity. Blueprint node
`bs:dense-threshold`. -/
private lemma nonpositivePressureThreshold_eq_of_rat_eq {f g : ℝ → EReal}
    (hf : AntitoneOn f (Set.Ici 0)) (hg : AntitoneOn g (Set.Ici 0))
    (hagree : ∀ q : ℚ, 0 ≤ q → f q = g q) :
    nonpositivePressureThreshold f = nonpositivePressureThreshold g :=
  le_antisymm (nonpositivePressureThreshold_le_of_rat_eq hg hagree)
    (nonpositivePressureThreshold_le_of_rat_eq hf fun q hq ↦ (hagree q hq).symm)

end Thresholds

variable {X : Type*} [MetricSpace X]

section Pointwise

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (A : Set ℕ) (x : X)
  (hpos : 0 < lowerBirkhoffAverage T u x) (hupper : upperBirkhoffAverage T u x < ⊤)
include hT hu hpos hupper

/-- For a finite dimension the nonpositive-pressure ray starts exactly at that dimension.
Blueprint node `bs:pointwise-critical`. -/
theorem pointwiseBowenCriticalValue_nonpositive_iff (σ : LimitSide)
    (hfinite : σ.choose (pointwiseBSDimension P T u A x) < ⊤) (s : ℝ) :
    σ.choose (pointwisePressure P T (fun y => -s * u y) A x) ≤ 0 ↔
      (σ.choose (pointwiseBSDimension P T u A x)).toReal ≤ s := by
  have hcomp : σ.choose (pointwisePressure P T (fun _ => 0) A x) < ⊤ := by
    by_contra h
    push Not at h
    have h' := pointwiseBowenCriticalValue_infinite P T u hu A x hpos hupper σ
      (top_le_iff.mp h)
    rw [h'] at hfinite
    exact not_top_lt hfinite
  set d := (σ.choose (pointwiseBSDimension P T u A x)).toReal
  set ℓ := (lowerBirkhoffAverage T u x).toReal
  set b := (upperBirkhoffAverage T u x).toReal
  have h_sand := pointwiseBowenEquation_sandwich P T hT u hu A x hpos hupper σ hcomp s
  have h_le : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := by
    apply Filter.liminf_le_limsup
    · exact Filter.isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
    · exact Filter.isBoundedUnder_of ⟨⊥, fun _ => bot_le⟩
  have h_lt_top : lowerBirkhoffAverage T u x < ⊤ := lt_of_le_of_lt h_le hupper
  have hl_pos : 0 < ℓ := EReal.toReal_pos hpos (ne_of_lt h_lt_top)
  have hb_pos : 0 < b := EReal.toReal_pos (lt_of_lt_of_le hpos h_le) (ne_of_lt hupper)
  constructor
  · intro h0
    rcases h_sand with ⟨h_lower_bound, _⟩
    have hm : ((min (ℓ * (d - s)) (b * (d - s)) : ℝ) : EReal) ≤ 0 := le_trans h_lower_bound h0
    rw [EReal.coe_nonpos] at hm
    rw [min_le_iff] at hm
    rcases hm with hm_l | hm_b
    · exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hm_l hl_pos)
    · exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hm_b hb_pos)
  · intro hle
    rcases h_sand with ⟨_, h_upper_bound⟩
    have hs_nonpos : d - s ≤ 0 := sub_nonpos.mpr hle
    have hl_mul : ℓ * (d - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hl_pos) hs_nonpos
    have hb_mul : b * (d - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb_pos) hs_nonpos
    have hm : max (ℓ * (d - s)) (b * (d - s)) ≤ 0 := max_le hl_mul hb_mul
    exact le_trans h_upper_bound (EReal.coe_nonpos.mpr hm)

omit hT in
/-- A lower bound `α` on the lower Birkhoff average makes the pointwise pressure decrease at least
linearly with slope `α` in the Bowen parameter. -/
theorem pointwisePressure_le_sub_mul_of_le_lowerBirkhoffAverage (σ : LimitSide) (α : ℝ)
    (hα : (α : EReal) ≤ lowerBirkhoffAverage T u x) (s t : ℝ) (hst : s < t) :
    σ.choose (pointwisePressure P T (fun y => -t * u y) A x) ≤
      σ.choose (pointwisePressure P T (fun y => -s * u y) A x) - ((t - s) * α : ℝ) := by
  have havg : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := liminf_le_limsup
  have hℓ : lowerBirkhoffAverage T u x ≠ ⊤ := (havg.trans_lt hupper).ne
  have hαℓ : α ≤ (lowerBirkhoffAverage T u x).toReal :=
    EReal.coe_le_coe_iff.mp (hα.trans (EReal.le_coe_toReal hℓ))
  have hmul : (((t - s) * α : ℝ) : EReal) ≤
      (((t - s) * (lowerBirkhoffAverage T u x).toReal : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hαℓ (sub_nonneg.mpr hst.le))
  exact (pointwisePressureSlopeBounds_scale P T u hu A x hpos hupper σ s t hst).2.trans
    (EReal.sub_le_sub le_rfl hmul)

end Pointwise

section PressureData

/-- Every Bowen potential `-v * u` with `u` uniformly continuous is the potential of some
`PressureData` over the given presentation and map. -/
private lemma exists_pressureData_of_bowenPotential (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (v : ℝ) :
    ∃ D : PressureData X, D.presentation = P ∧ D.T = T ∧ D.φ = (fun y => -v * u y) := by
  let φ : X → ℝ := fun y => -v * u y
  have hφ : UniformContinuous φ := UniformContinuous.const_smul hu (-v)
  obtain ⟨ω, hω_pos, hω_tendsto, p₀, h_osc⟩ := small_scale_oscillation φ hφ
  refine ⟨{
    presentation := P
    T := T
    continuous_T := hT
    φ := φ
    uniformContinuous_φ := hφ
    p₀ := p₀
    ω := ω
    ω_pos := fun p _ => hω_pos p
    ω_tendsto := hω_tendsto
    oscillation := ?_ }, rfl, rfl, rfl⟩
  intro p hp x y hxy
  refine h_osc p hp x y (hxy.trans_le ?_)
  have hr : 0 < dyadicRadius p := by
    dsimp only [dyadicRadius]
    positivity
  linarith

/-- The lower pressure does not depend on the initial scale `0` versus the cutoff `p₀`. -/
private lemma lowerPressure_zero_eq_lowerPressure_p₀ (D : PressureData X) (Z : Set X) :
    lowerPressure D.T D.φ 0 Z = lowerPressure D.T D.φ D.p₀ Z := by
  have hrad : ∀ p : ℕ, dyadicRadius (max p D.p₀) ≤ dyadicRadius p := fun p => by
    change (2 : ℝ)⁻¹ ^ max p D.p₀ ≤ (2 : ℝ)⁻¹ ^ p
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left p D.p₀)
  unfold lowerPressure
  refine le_antisymm (iSup_mono' fun p ↦ ⟨max p D.p₀, iSup_mono' fun _ ↦
    ⟨le_max_right p D.p₀, ?_⟩⟩) (iSup_le fun p ↦ iSup_le fun hp ↦
    le_iSup_of_le p (le_iSup_of_le (by omega) le_rfl))
  exact lowerPressure_eq_centered_radius (D := D) (Z := Z)
    (r := dyadicRadius (max p D.p₀)) (R := dyadicRadius p)
    (hrad p)

/-- The upper pressure does not depend on the initial scale `0` versus the cutoff `p₀`. -/
private lemma upperPressure_zero_eq_upperPressure_p₀ (D : PressureData X) (Z : Set X) :
    upperPressure D.T D.φ 0 Z = upperPressure D.T D.φ D.p₀ Z := by
  have hrad : ∀ p : ℕ, dyadicRadius (max p D.p₀) ≤ dyadicRadius p := fun p => by
    change (2 : ℝ)⁻¹ ^ max p D.p₀ ≤ (2 : ℝ)⁻¹ ^ p
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left p D.p₀)
  unfold upperPressure
  refine le_antisymm (iSup_mono' fun p ↦ ⟨max p D.p₀, iSup_mono' fun _ ↦
    ⟨le_max_right p D.p₀, ?_⟩⟩) (iSup_le fun p ↦ iSup_le fun hp ↦
    le_iSup_of_le p (le_iSup_of_le (by omega) le_rfl))
  exact upperPressure_scale_comparison_modified_radius (D := D) (Z := Z)
    (r := dyadicRadius (max p D.p₀)) (R := dyadicRadius p)
    (hrad p)

end PressureData

section Sets

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (Z : Set X)
  (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x < ⊤)

include P hT hu hZ

/-- The supremum of pointwise dimensions is the positive threshold of the pressure supremum.
Blueprint node `bs:supremum-critical`. -/
theorem supPointwiseBSDimensionCriticalValue (A : Set ℕ) (σ : LimitSide) :
    (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) =
      positivePressureThreshold (fun s =>
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) := by
  rw [positivePressureThreshold_biSup (f := fun x t ↦
    σ.choose (pointwisePressure P T (fun y => -t * u y) A x))]
  exact iSup_congr fun x ↦ iSup_congr fun hx ↦
    pointwiseBowenCriticalValue P T hT u hu A x (hZ x hx).1 (hZ x hx).2 σ

/-- The same dimension supremum is the nonpositive threshold, even on the empty set.
Blueprint node `bs:supremum-critical`. -/
theorem supPointwiseBSDimensionCriticalValue_nonpositive (A : Set ℕ) (σ : LimitSide) :
    (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) =
      nonpositivePressureThreshold (fun s =>
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) := by
  let D := ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)
  change D = _
  apply le_antisymm
  · unfold nonpositivePressureThreshold
    refine le_iInf fun s => le_iInf fun hs => le_iInf fun hpressure => ?_
    refine iSup_le fun x => iSup_le fun hx => ?_
    rw [pointwiseBowenCriticalValue_nonpositive P T hT u hu A x
      (hZ x hx).1 (hZ x hx).2 σ]
    have hxpressure : σ.choose (pointwisePressure P T (fun y => -s * u y) A x) ≤ 0 :=
      (le_iSup₂_of_le x hx le_rfl).trans hpressure
    unfold nonpositivePressureThreshold
    exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le hxpressure le_rfl))
  · by_cases htop : D = ⊤
    · rw [htop]
      exact le_top
    · have hpressure :
          (⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -D.toReal * u y) A x)) ≤
            0 := by
        refine iSup_le fun x => iSup_le fun hx => ?_
        have hdim : σ.choose (pointwiseBSDimension P T u A x) ≤ D :=
          le_iSup₂_of_le x hx le_rfl
        have hfinite : σ.choose (pointwiseBSDimension P T u A x) < ⊤ :=
          hdim.trans_lt (lt_top_iff_ne_top.mpr htop)
        apply (pointwiseBowenCriticalValue_nonpositive_iff P T hT u hu A x
          (hZ x hx).1 (hZ x hx).2 σ hfinite D.toReal).mpr
        exact ENNReal.toReal_mono htop hdim
      calc
        nonpositivePressureThreshold (fun s =>
            ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) ≤
            ENNReal.ofReal D.toReal := by
          unfold nonpositivePressureThreshold
          exact iInf_le_of_le D.toReal (iInf_le_of_le ENNReal.toReal_nonneg
            (iInf_le_of_le hpressure le_rfl))
        _ = D := ENNReal.ofReal_toReal htop

/-- At a finite supremum of dimensions the pressure supremum is nonpositive.
Blueprint node `bs:supremum-critical`. -/
theorem supPointwiseBSDimensionCriticalValue_at_dimension (A : Set ℕ) (σ : LimitSide)
    (hfinite : (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) < ⊤) :
    let d := (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)).toReal
    (⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -d * u y) A x)) ≤ 0 := by
  intro d
  refine iSup₂_le fun x hx ↦ ?_
  have hle : σ.choose (pointwiseBSDimension P T u A x) ≤
      ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x) := le_iSup₂_of_le x hx le_rfl
  exact (pointwiseBowenCriticalValue_nonpositive_iff P T hT u hu A x (hZ x hx).1 (hZ x hx).2 σ
    (hle.trans_lt hfinite) d).mpr (ENNReal.toReal_mono hfinite.ne hle)

omit hT in
/-- The pointwise pressure of every point of `Z` is nonincreasing in the Bowen parameter. -/
private lemma pointwisePressure_anti (A : Set ℕ) (σ : LimitSide) {x : X} (hx : x ∈ Z)
    {s t : ℝ} (hst : s < t) :
    σ.choose (pointwisePressure P T (fun y => -t * u y) A x) ≤
      σ.choose (pointwisePressure P T (fun y => -s * u y) A x) := by
  have h := pointwisePressure_le_sub_mul_of_le_lowerBirkhoffAverage P T u hu A x
    (hZ x hx).1 (hZ x hx).2 σ 0 (EReal.coe_zero.le.trans (hZ x hx).1.le) s t hst
  simpa using h

omit hT in
/-- The supremum over `Z` of the pointwise pressures is nonincreasing in the Bowen parameter. -/
private lemma iSup_pointwisePressure_anti (A : Set ℕ) (σ : LimitSide) {s t : ℝ} (hst : s < t) :
    (⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -t * u y) A x)) ≤
      ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x) :=
  iSup₂_mono fun _ hx ↦ pointwisePressure_anti P T u hu Z hZ A σ hx hst

omit hZ in
/-- The classical set pressure at a Bowen parameter is the infimum over oracles of the supremum of
the pointwise pressures. Blueprint node `bs:set-slope-join`. -/
theorem setPressure_eq_iInf_iSup_pointwisePressure (σ : LimitSide) (v : ℝ) :
    σ.choose (lowerPressure T (fun y => -v * u y) 0 Z, upperPressure T (fun y => -v * u y) 0 Z) =
      ⨅ A : Set ℕ, ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -v * u y) A x) := by
  obtain ⟨D, hP, hTeq, hφ⟩ := exists_pressureData_of_bowenPotential P T hT u hu v
  cases σ with
  | lower =>
    simpa only [hP, hTeq, hφ, LimitSide.choose] using
      (lowerPressure_zero_eq_lowerPressure_p₀ D Z).trans (lowerPressure_pointToSet D Z)
  | upper =>
    simpa only [hP, hTeq, hφ, LimitSide.choose] using
      (upperPressure_zero_eq_upperPressure_p₀ D Z).trans (upperPressure_pointToSet D Z)

/-- Classical pressure is nonincreasing in the real Bowen parameter.
Blueprint node `bs:set-slope-join`. -/
theorem setPressureSlopeAndRationalAttainment (σ : LimitSide) (s t : ℝ) (hst : s < t) :
    σ.choose (lowerPressure T (fun y => -t * u y) 0 Z,
      upperPressure T (fun y => -t * u y) 0 Z) ≤
    σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
      upperPressure T (fun y => -s * u y) 0 Z) := by
  rw [setPressure_eq_iInf_iSup_pointwisePressure P T hT u hu Z σ t,
    setPressure_eq_iInf_iSup_pointwisePressure P T hT u hu Z σ s]
  exact iInf_mono fun A ↦ iSup_pointwisePressure_anti P T u hu Z hZ A σ hst

/-- A uniform positive lower average gives an extended-real quantitative slope bound. (The
positivity of `α` is part of the blueprint statement but the argument does not use it.)
Blueprint node `bs:set-slope-join`. -/
theorem setPressureSlopeAndRationalAttainment_slope (σ : LimitSide) (α : ℝ)
    (hlower : ∀ x ∈ Z, (α : EReal) ≤ lowerBirkhoffAverage T u x)
    (s t : ℝ) (hst : s < t) :
    σ.choose (lowerPressure T (fun y => -t * u y) 0 Z,
      upperPressure T (fun y => -t * u y) 0 Z) ≤
    σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
      upperPressure T (fun y => -s * u y) 0 Z) - ((t - s) * α : ℝ) := by
  rw [setPressure_eq_iInf_iSup_pointwisePressure P T hT u hu Z σ t,
    setPressure_eq_iInf_iSup_pointwisePressure P T hT u hu Z σ s]
  have hc_ne_top : (((t - s) * α : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hc_ne_bot : (((t - s) * α : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  rw [EReal.le_sub_iff_add_le (Or.inl hc_ne_bot) (Or.inl hc_ne_top)]
  refine le_iInf fun A ↦ ?_
  rw [← EReal.le_sub_iff_add_le (Or.inl hc_ne_bot) (Or.inl hc_ne_top)]
  refine (iInf_le _ A).trans (iSup₂_le fun x hx ↦ ?_)
  exact (pointwisePressure_le_sub_mul_of_le_lowerBirkhoffAverage P T u hu A x (hZ x hx).1
    (hZ x hx).2 σ α (hlower x hx) s t hst).trans
    (EReal.sub_le_sub (le_iSup₂_of_le x hx le_rfl) le_rfl)

/-- One admissible upper cone attains both BS minima and both pressure minima at every
nonnegative rational parameter. Blueprint node `bs:set-slope-join`. -/
theorem setPressureSlopeAndRationalAttainment_attainment :
    ∃ A₀ : Set ℕ, ∀ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A →
      IsAdmissible P T (fun _ : Fin 1 => u) A ∧
      (∀ σ : LimitSide, σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
        ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) ∧
      ∀ q : ℚ, 0 ≤ q → ∀ σ : LimitSide,
        σ.choose (lowerPressure T (fun y => -(q : ℝ) * u y) 0 Z,
          upperPressure T (fun y => -(q : ℝ) * u y) 0 Z) =
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -(q : ℝ) * u y) A x) := by
  obtain ⟨A_BS, hA_BS⟩ := bsPointToSet_cone P T hT u hu Z (fun x hx => (hZ x hx).1)
  let φ : ℕ → X → ℝ := fun j y => -(((Encodable.decode (α := ℚ) j).getD 0 : ℝ)) * u y
  have hφ : ∀ j, UniformContinuous (φ j) := fun j =>
    UniformContinuous.const_smul hu (-(((Encodable.decode (α := ℚ) j).getD 0 : ℝ)))
  obtain ⟨B_press, hB_press⟩ :=
    upperEntropy_pointToSet_simultaneous P T hT φ hφ (fun _ => 0) Z
  refine ⟨oracleJoin A_BS B_press, fun A hA ↦ ?_⟩
  obtain ⟨h_adm, h_BS⟩ := hA_BS A (TuringReducible.trans (oracle_joins A_BS B_press) hA)
  obtain ⟨_, _, h_press⟩ :=
    hB_press A (TuringReducible.trans (oracle_joins_right A_BS B_press) hA)
  refine ⟨h_adm, h_BS, fun q _ σ ↦ ?_⟩
  have hj : φ (Encodable.encode q) = fun y => -(q : ℝ) * u y := by
    simp only [φ, Encodable.encodek, Option.getD_some]
  have hj_eval := h_press (Encodable.encode q)
  rw [hj] at hj_eval
  cases σ with
  | lower => exact hj_eval.1
  | upper => exact hj_eval.2

/-- An attaining oracle for which the dimension is the supremum of the pointwise dimensions and
the classical pressure agrees with the pointwise pressure supremum at nonnegative rationals. -/
private lemma exists_oracle_dimension_eq_pressure_agreement (σ : LimitSide) :
    ∃ A₀ : Set ℕ,
      σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
        ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A₀ x) ∧
      (∀ q : ℚ, 0 ≤ q →
        σ.choose (lowerPressure T (fun y => -(q : ℝ) * u y) 0 Z,
          upperPressure T (fun y => -(q : ℝ) * u y) 0 Z) =
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -(q : ℝ) * u y) A₀ x)) := by
  obtain ⟨A₀, hA₀⟩ := setPressureSlopeAndRationalAttainment_attainment P T hT u hu Z hZ
  obtain ⟨_, hd, hq⟩ := hA₀ A₀ (TuringReducible.refl _)
  exact ⟨A₀, hd σ, fun q hq0 ↦ hq q hq0 σ⟩

/-- The classical set pressure is nonincreasing on `[0, ∞)`. -/
private lemma setPressure_antitoneOn (σ : LimitSide) :
    AntitoneOn (fun s : ℝ => σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
      upperPressure T (fun y => -s * u y) 0 Z)) (Set.Ici 0) :=
  antitoneOn_iff_forall_lt.2 fun _ _ _ _ hst ↦
    setPressureSlopeAndRationalAttainment P T hT u hu Z hZ σ _ _ hst

/-- Main D's critical-value part: the classical dimension is the positive-pressure threshold.
Blueprint node `bs:set-critical`. -/
theorem setBowenCriticalValue (σ : LimitSide) :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
      positivePressureThreshold (fun s =>
        σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
          upperPressure T (fun y => -s * u y) 0 Z)) := by
  obtain ⟨A₀, hd, hq⟩ := exists_oracle_dimension_eq_pressure_agreement P T hT u hu Z hZ σ
  rw [hd, supPointwiseBSDimensionCriticalValue P T hT u hu Z hZ A₀ σ]
  exact (monotoneDenseAgreementCriticalValue _ _ (setPressure_antitoneOn P T hT u hu Z hZ σ)
    (antitoneOn_iff_forall_lt.2 fun _ _ _ _ hst ↦
      iSup_pointwisePressure_anti P T u hu Z hZ A₀ σ hst) hq).symm

/-- The same classical dimension is the nonpositive-pressure threshold.
Blueprint node `bs:set-critical`. -/
theorem setBowenCriticalValue_nonpositive (σ : LimitSide) :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
      nonpositivePressureThreshold (fun s =>
        σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
          upperPressure T (fun y => -s * u y) 0 Z)) := by
  obtain ⟨A₀, hd, hq⟩ := exists_oracle_dimension_eq_pressure_agreement P T hT u hu Z hZ σ
  rw [hd, supPointwiseBSDimensionCriticalValue_nonpositive P T hT u hu Z hZ A₀ σ]
  exact (nonpositivePressureThreshold_eq_of_rat_eq (setPressure_antitoneOn P T hT u hu Z hZ σ)
    (antitoneOn_iff_forall_lt.2 fun _ _ _ _ hst ↦
      iSup_pointwisePressure_anti P T u hu Z hZ A₀ σ hst) hq).symm

/-- Both critical-parameter oracle minima are attained on one admissible upper cone.
Blueprint node `bs:set-critical`. -/
theorem setBowenCriticalValue_cone :
    ∃ A₀ : Set ℕ, ∀ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A →
      IsAdmissible P T (fun _ : Fin 1 => u) A ∧ ∀ σ : LimitSide,
        let d := σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z)
        let f := fun s : ℝ =>
          ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x)
        d = positivePressureThreshold f ∧ d = nonpositivePressureThreshold f := by
  obtain ⟨A₀, hA₀⟩ := setPressureSlopeAndRationalAttainment_attainment P T hT u hu Z hZ
  refine ⟨A₀, fun A hA ↦ ?_⟩
  obtain ⟨hAdm, hd, -⟩ := hA₀ A hA
  refine ⟨hAdm, fun σ ↦ ?_⟩
  dsimp only
  rw [hd σ]
  exact ⟨supPointwiseBSDimensionCriticalValue P T hT u hu Z hZ A σ,
    supPointwiseBSDimensionCriticalValue_nonpositive P T hT u hu Z hZ A σ⟩

/-- The positive critical parameter is the infimum of its all-oracle counterparts.
Blueprint node `bs:set-critical`. -/
theorem setBowenCriticalValue_oracles (σ : LimitSide) :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
      ⨅ A : Set ℕ, positivePressureThreshold (fun s =>
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) := by
  obtain ⟨A₀, hA₀⟩ := setBowenCriticalValue_cone P T hT u hu Z hZ
  refine le_antisymm (le_iInf fun A ↦ ?_)
    (iInf_le_of_le A₀ ((hA₀ A₀ (TuringReducible.refl _)).2 σ).1.ge)
  rw [← supPointwiseBSDimensionCriticalValue P T hT u hu Z hZ A σ]
  exact bsPointToSet_all_oracles P T hT u hu Z (fun x hx => (hZ x hx).1) A σ

/-- The nonpositive critical parameter has the analogous all-oracle infimum.
Blueprint node `bs:set-critical`. -/
theorem setBowenCriticalValue_oracles_nonpositive (σ : LimitSide) :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
      ⨅ A : Set ℕ, nonpositivePressureThreshold (fun s =>
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y => -s * u y) A x)) := by
  obtain ⟨A₀, hA₀⟩ := setBowenCriticalValue_cone P T hT u hu Z hZ
  refine le_antisymm (le_iInf fun A ↦ ?_)
    (iInf_le_of_le A₀ ((hA₀ A₀ (TuringReducible.refl _)).2 σ).2.ge)
  rw [← supPointwiseBSDimensionCriticalValue_nonpositive P T hT u hu Z hZ A σ]
  exact bsPointToSet_all_oracles P T hT u hu Z (fun x hx => (hZ x hx).1) A σ

end Sets

end Kolmogorov.PointToSet
