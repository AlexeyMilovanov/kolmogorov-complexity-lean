/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation.SetCriticalValue

/-!
# Roots of the classical Bowen pressure of a set

For a set `Z` and a potential `-s * u`, the classical Bowen pressure `s ↦ P^Z_σ(s)` (with `σ` one
of the two `LimitSide`s, i.e. lower or upper) is compared with the Barreira–Schmeling dimension of
`Z`. This file proves the existence and uniqueness of its zero under the hypotheses of the
repaired set-level theorems of the blueprint.

* `monotoneDenseAgreementCriticalValue_nonpositive`: two nonincreasing maps which agree on the
  nonnegative rationals have the same nonpositive threshold (blueprint node `bs:dense-threshold`).
* `setBowenRootOfFiniteBSDimension`: if the relevant Barreira–Schmeling dimension of a nonempty
  set is finite and the upper Birkhoff averages are uniformly bounded, the pressure vanishes at
  the dimension (blueprint node `bs:set-root-repaired`).
* `setBowenRootUniqueness` and its variants `setBowenRootUniqueness_real`,
  `setBowenRootUniqueness_strict`, `setBowenRootUniqueness_dimension_le` and
  `setBowenRootUniqueness_dimension_finite`: under a uniform positive lower bound on the Birkhoff
  averages and finite entropy, the pressure is real-valued and strictly decreasing on
  `[0, ∞)`, so it has at most one real zero, and the dimension is at most the entropy divided by
  the lower bound (blueprint node `bs:set-root-unique`).

The existence and uniqueness statements are combined in
`KolmogorovMathlib.PointToSet.BowenEquation.NonuniformCounterexample` and in the conformal
dimension theorem.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

section DenseAgreement

/-- The same dense agreement preserves the nonpositive-set infimum.
Blueprint node `bs:dense-threshold`. -/
theorem monotoneDenseAgreementCriticalValue_nonpositive (f g : ℝ → EReal)
    (hf : AntitoneOn f (Set.Ici 0)) (hg : AntitoneOn g (Set.Ici 0))
    (hagree : ∀ q : ℚ, 0 ≤ q → f q = g q) :
    nonpositivePressureThreshold f = nonpositivePressureThreshold g :=
  le_antisymm (nonpositivePressureThreshold_le_of_rat_eq hg hagree)
    (nonpositivePressureThreshold_le_of_rat_eq hf fun q hq ↦ (hagree q hq).symm)

end DenseAgreement

section FiniteDimension

omit [MetricSpace X] in
/-- The real values of the lower and upper Birkhoff averages at a point with positive lower average
and upper average at most `β` satisfy `0 < ℓ ≤ b ≤ β`. -/
private lemma birkhoffAverage_toReal_bounds (T : X → X) (u : X → ℝ) {x : X} {β : ℝ}
    (hpos : 0 < lowerBirkhoffAverage T u x) (hup : upperBirkhoffAverage T u x ≤ (β : EReal)) :
    0 < (lowerBirkhoffAverage T u x).toReal ∧
      (lowerBirkhoffAverage T u x).toReal ≤ (upperBirkhoffAverage T u x).toReal ∧
      (upperBirkhoffAverage T u x).toReal ≤ β := by
  have havg : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x := liminf_le_limsup
  have hupper : upperBirkhoffAverage T u x ≠ ⊤ := (hup.trans_lt (EReal.coe_lt_top β)).ne
  refine ⟨EReal.toReal_pos hpos (havg.trans_lt (hup.trans_lt (EReal.coe_lt_top β))).ne,
    EReal.toReal_le_toReal havg hpos.ne_bot hupper, ?_⟩
  simpa only [EReal.toReal_coe] using
    EReal.toReal_le_toReal hup (hpos.trans_le havg).ne_bot (EReal.coe_ne_top β)

/-- Some oracle simultaneously attains the relevant Barreira–Schmeling dimension of `Z` and the
relevant classical pressure of `Z` for the potential `-s * u`, both as suprema of the pointwise
quantities. -/
private lemma exists_oracle_attaining_dimension_and_pressure
    (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (Z : Set X) (hpos : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (σ : LimitSide) (s : ℝ) :
    ∃ A : Set ℕ,
      σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) =
        ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x) ∧
      σ.choose (lowerPressure T (fun y ↦ -s * u y) 0 Z,
        upperPressure T (fun y ↦ -s * u y) 0 Z) =
        ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x) := by
  obtain ⟨A₀, hA₀⟩ := bsPointToSet_cone P T hT u hu Z hpos
  obtain ⟨B, hB⟩ := upperEntropy_pointToSet_simultaneous P T hT
    (fun _ y ↦ -s * u y) (fun _ ↦ UniformContinuous.const_smul hu (-s)) (fun _ ↦ 0) Z
  refine ⟨oracleJoin A₀ B, (hA₀ _ (oracle_joins A₀ B)).2 σ, ?_⟩
  obtain ⟨-, -, hpressure⟩ := hB _ (oracle_joins_right A₀ B)
  cases σ with
  | lower => exact (hpressure 0).1
  | upper => exact (hpressure 0).2

/-- If the supremum of the pointwise dimensions over `Z` is finite, the zero-potential pointwise
pressure is finite at every point of `Z`. -/
private lemma pointwisePressure_zero_lt_top_of_iSup_lt_top
    (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x < ⊤)
    (σ : LimitSide) (A : Set ℕ)
    (hfinite : (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) < ⊤) :
    ∀ x ∈ Z, σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤ := by
  intro x hx
  refine lt_top_iff_ne_top.2 fun htop ↦ ?_
  have hdim := pointwiseBowenCriticalValue_infinite P T hT u hu A x (hZ x hx).1 (hZ x hx).2 σ htop
  have hle : σ.choose (pointwiseBSDimension P T u A x) ≤
      ⨆ y ∈ Z, σ.choose (pointwiseBSDimension P T u A y) := le_iSup₂_of_le x hx le_rfl
  rw [hdim] at hle
  exact hfinite.not_ge hle

/-- A finite supremum of extended nonnegative reals is approached, in real value, by one of its
terms. -/
private lemma exists_mem_sub_lt_toReal_iSup {ι : Type*} {S : Set ι} (hne : S.Nonempty)
    {f : ι → ℝ≥0∞} (hfin : (⨆ i ∈ S, f i) < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ i ∈ S, (⨆ j ∈ S, f j).toReal - δ < (f i).toReal := by
  by_contra! h
  obtain ⟨i₀, hi₀⟩ := hne
  have h0 : 0 ≤ (⨆ j ∈ S, f j).toReal - δ := ENNReal.toReal_nonneg.trans (h i₀ hi₀)
  have hle : (⨆ j ∈ S, f j) ≤ ENNReal.ofReal ((⨆ j ∈ S, f j).toReal - δ) := by
    refine iSup₂_le fun i hi ↦ ?_
    have hfi : f i ≠ ⊤ := ((le_iSup₂_of_le i hi le_rfl).trans_lt hfin).ne
    rw [← ENNReal.ofReal_toReal hfi]
    exact ENNReal.ofReal_le_ofReal (h i hi)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal h0] at this
  linarith

/-- For a point whose pointwise dimension is at most `s`, the pointwise pressure of the potential
`-s * u` is bounded below by `β * (dim - s)`, where `β` bounds the upper Birkhoff average. -/
private lemma mul_dimension_sub_le_pointwisePressure
    (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (A : Set ℕ) (x : X) {β : ℝ} (hpos : 0 < lowerBirkhoffAverage T u x)
    (hup : upperBirkhoffAverage T u x ≤ (β : EReal)) (σ : LimitSide)
    (hfinite : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤) {s : ℝ}
    (hs : (σ.choose (pointwiseBSDimension P T u A x)).toReal ≤ s) :
    ((β * ((σ.choose (pointwiseBSDimension P T u A x)).toReal - s) : ℝ) : EReal) ≤
      σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x) := by
  obtain ⟨-, hℓb, hbβ⟩ := birkhoffAverage_toReal_bounds T u hpos hup
  have hsand := (pointwiseBowenEquation_sandwich P T hT u hu A x hpos
    (hup.trans_lt (EReal.coe_lt_top β)) σ hfinite s).1
  refine le_trans (EReal.coe_le_coe_iff.2 (le_min ?_ ?_)) hsand
  · exact mul_le_mul_of_nonpos_right (hℓb.trans hbβ) (sub_nonpos.2 hs)
  · exact mul_le_mul_of_nonpos_right hbβ (sub_nonpos.2 hs)

/-- If the relevant dimension of `Z` is approached by the pointwise dimensions of an oracle, the
supremum of the pointwise pressures at that dimension is nonnegative. -/
private lemma zero_le_iSup_pointwisePressure
    (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (Z : Set X) (hne : Z.Nonempty) {β : ℝ}
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x ≤ (β : EReal))
    (σ : LimitSide) (A : Set ℕ)
    (hfinite : (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) < ⊤) :
    let d := (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)).toReal
    0 ≤ ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y ↦ -d * u y) A x) := by
  intro d
  have hZ' : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x < ⊤ :=
    fun x hx ↦ ⟨(hZ x hx).1, (hZ x hx).2.trans_lt (EReal.coe_lt_top β)⟩
  have hPointFinite :=
    pointwisePressure_zero_lt_top_of_iSup_lt_top P T hT u hu Z hZ' σ A hfinite
  obtain ⟨x₀, hx₀⟩ := hne
  have hβ : 0 < β := by
    obtain ⟨hℓ, hℓb, hbβ⟩ := birkhoffAverage_toReal_bounds T u (hZ x₀ hx₀).1 (hZ x₀ hx₀).2
    linarith
  have key : ∀ η : ℝ, 0 < η →
      ((-η : ℝ) : EReal) < ⨆ x ∈ Z, σ.choose (pointwisePressure P T (fun y ↦ -d * u y) A x) := by
    intro η hη
    obtain ⟨x, hx, hxd⟩ := exists_mem_sub_lt_toReal_iSup ⟨x₀, hx₀⟩ hfinite (div_pos hη hβ)
    have hxle : (σ.choose (pointwiseBSDimension P T u A x)).toReal ≤ d :=
      ENNReal.toReal_mono hfinite.ne (le_iSup₂_of_le x hx le_rfl)
    have hlt : -η < β * ((σ.choose (pointwiseBSDimension P T u A x)).toReal - d) := by
      calc -η = β * (-(η / β)) := by field_simp
        _ < _ := mul_lt_mul_of_pos_left (by linarith) hβ
    exact (EReal.coe_lt_coe_iff.2 hlt).trans_le <|
      (mul_dimension_sub_le_pointwisePressure P T hT u hu A x (hZ x hx).1 (hZ x hx).2 σ
        (hPointFinite x hx) hxle).trans (le_iSup₂_of_le x hx le_rfl)
  by_contra! hlt
  obtain ⟨e, hse, he⟩ := EReal.exists_between_coe_real hlt
  have he0 : e < 0 := by exact_mod_cast he
  have := key (-e) (neg_pos.2 he0)
  rw [neg_neg] at this
  exact lt_asymm hse this

/-- Finite relevant Barreira–Schmeling dimension, nonemptiness, and a common finite bound on the
upper Birkhoff averages give a set-level pressure zero at the dimension.
Blueprint node `bs:set-root-repaired`. -/
theorem setBowenRootOfFiniteBSDimension (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hne : Z.Nonempty) (β : ℝ)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧
      upperBirkhoffAverage T u x ≤ (β : EReal)) (σ : LimitSide)
    (hfinite : σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) < ⊤) :
    let d := (σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z)).toReal
    σ.choose (lowerPressure T (fun y => -d * u y) 0 Z,
      upperPressure T (fun y => -d * u y) 0 Z) = 0 := by
  intro d
  obtain ⟨A, hDim, hPressure⟩ :=
    exists_oracle_attaining_dimension_and_pressure P T hT u hu Z (fun x hx ↦ (hZ x hx).1) σ d
  have hfinite' : (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) < ⊤ := hDim ▸ hfinite
  have hlower := zero_le_iSup_pointwisePressure P T hT u hu Z hne hZ σ A hfinite'
  have hupper := supPointwiseBSDimensionCriticalValue_at_dimension P T hT u hu Z
    (fun x hx ↦ ⟨(hZ x hx).1, (hZ x hx).2.trans_lt (EReal.coe_lt_top β)⟩) A σ hfinite'
  have hd : (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)).toReal = d := by
    rw [← hDim]
  rw [hd] at hupper hlower
  rw [hPressure]
  exact le_antisymm hupper hlower

end FiniteDimension

section ZeroPotential

/-- The pointwise pressure of the zero potential is nonnegative, for both limit sides: the
finite-scale rate is `+∞` at order zero and a quotient `K^A(i) / n ≥ 0` otherwise. No continuity
is needed. -/
private lemma zero_le_pointwisePressure_zero (Q : Presentation X) (F : X → X) (A : Set ℕ) (x : X)
    (τ : LimitSide) : (0 : EReal) ≤ τ.choose (pointwisePressure Q F (fun _ ↦ 0) A x) := by
  have hrate (n : ℕ) (ε : ℝ) : (0 : EReal) ≤ finiteScalePressureRate Q F (fun _ ↦ 0) A x n ε := by
    unfold finiteScalePressureRate
    split_ifs with hn
    · exact le_top
    · refine le_iInf fun i ↦ le_iInf fun _ ↦
        EReal.coe_nonneg.mpr (div_nonneg ?_ (Nat.cast_nonneg _))
      simpa only [birkhoffSum, Finset.sum_const_zero, add_zero] using Nat.cast_nonneg _
  have hge (n : ℕ) : (0 : EReal) ≤
      finiteScalePressureRate Q F (fun _ ↦ 0) A x n (dyadicRadius 0) := hrate n _
  unfold pointwisePressure LimitSide.choose
  cases τ
  · refine le_iSup_of_le 0 ?_
    have h : liminf (fun _ : ℕ ↦ (0 : EReal)) atTop ≤
        liminf (fun n ↦ finiteScalePressureRate Q F (fun _ ↦ 0) A x n (dyadicRadius 0)) atTop :=
      liminf_le_liminf (Eventually.of_forall hge) (by isBoundedDefault) (by isBoundedDefault)
    rwa [liminf_const] at h
  · refine le_iSup_of_le 0 ?_
    have h : limsup (fun _ : ℕ ↦ (0 : EReal)) atTop ≤
        limsup (fun n ↦ finiteScalePressureRate Q F (fun _ ↦ 0) A x n (dyadicRadius 0)) atTop :=
      limsup_le_limsup (Eventually.of_forall hge) (by isBoundedDefault) (by isBoundedDefault)
    rwa [limsup_const] at h

/-- The zero-potential pointwise pressure is bounded by the orbit complexity rate, by comparing
the same candidates before taking time limits and suprema over scales. -/
private lemma pointwisePressure_zero_le_orbitComplexities (P : Presentation X) (T : X → X)
    (σ : LimitSide) (A : Set ℕ) (x : X) :
    σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) ≤
      ((σ.choose (orbitComplexities P T A x) : ℝ≥0∞) : EReal) := by
  have horder (n : ℕ) (r : ℝ) :
      finiteScalePressureRate P T (fun _ ↦ 0) A x n r ≤
        (finiteScaleBSCost P T (fun _ ↦ 1) A x n r : EReal) := by
    have hle : (finiteScalePressureRate P T (fun _ ↦ 0) A x n r).toENNReal ≤
        finiteScaleBSCost P T (fun _ ↦ 1) A x n r := by
      unfold finiteScaleBSCost
      split_ifs with hn
      · exact le_top
      · simp only [birkhoffSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        refine le_iInf fun i ↦ le_iInf fun hi ↦ le_iInf fun _ ↦ ?_
        have hr : finiteScalePressureRate P T (fun _ ↦ 0) A x n r ≤
            (((oracleNatComplexity A i : ℝ) / n : ℝ) : EReal) := by
          simp only [finiteScalePressureRate, hn, ↓reduceIte, birkhoffSum,
            Finset.sum_const_zero, add_zero]
          exact iInf_le_of_le i (iInf_le_of_le hi le_rfl)
        have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        simpa only [EReal.real_coe_toENNReal, ENNReal.ofReal_div_of_pos hnpos,
          ENNReal.ofReal_natCast] using EReal.toENNReal_le_toENNReal hr
    calc
      _ ≤ ((finiteScalePressureRate P T (fun _ ↦ 0) A x n r).toENNReal : EReal) := by
        rw [EReal.coe_toENNReal_eq_max]
        exact le_max_right _ _
      _ ≤ _ := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle
  have htime (p : ℕ) :
      σ.timeLimit (fun n ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n (dyadicRadius p)) ≤
      ((σ.timeLimit (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p)) :
        ℝ≥0∞) : EReal) := by
    cases σ with
    | lower =>
      exact (liminf_le_liminf (Eventually.of_forall fun n ↦ horder n _)).trans_eq
        (EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt
          (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p))
          continuous_coe_ennreal_ereal.continuousAt).symm
    | upper =>
      exact (limsup_le_limsup (Eventually.of_forall fun n ↦ horder n _)).trans_eq
        (EReal.coe_ennreal_strictMono.monotone.map_limsup_of_continuousAt
          (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p))
          continuous_coe_ennreal_ereal.continuousAt).symm
  have hpressure : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScalePressureRate P T (fun _ ↦ 0) A x n
        (dyadicRadius p)) := by cases σ <;> rfl
  have hcomplexity : σ.choose (orbitComplexities P T A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n
        (dyadicRadius p)) := by cases σ <;> rfl
  rw [hpressure, hcomplexity]
  exact iSup_le fun p ↦ (htime p).trans
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup
      (fun q ↦ (σ.timeLimit (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n
        (dyadicRadius q)) : ℝ≥0∞)) p))

/-- A pointwise pressure of the potential `-s * u`, at a point with positive lower and finite upper
Birkhoff average and nonnegative `s`, is at least `-s * b`, where `b` is the upper average. -/
private lemma neg_mul_le_pointwisePressure
    (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u)
    (A : Set ℕ) (x : X) (hpos : 0 < lowerBirkhoffAverage T u x)
    (hupper : upperBirkhoffAverage T u x < ⊤) (σ : LimitSide) {s : ℝ} (hs : 0 ≤ s) :
    ((-s * (upperBirkhoffAverage T u x).toReal : ℝ) : EReal) ≤
      σ.choose (pointwisePressure P T (fun y ↦ -s * u y) A x) := by
  have hzero := zero_le_pointwisePressure_zero P T A x σ
  rcases hs.eq_or_lt with rfl | hspos
  · simpa only [neg_zero, zero_mul, EReal.coe_zero] using hzero
  · have hslope := (pointwisePressureSlopeBounds_scale P T hT u hu A x hpos hupper σ 0 s hspos).1
    simp only [neg_zero, zero_mul, sub_zero] at hslope
    calc ((-s * (upperBirkhoffAverage T u x).toReal : ℝ) : EReal)
        = (0 : EReal) - ((s * (upperBirkhoffAverage T u x).toReal : ℝ) : EReal) := by
          rw [zero_sub, neg_mul, EReal.coe_neg]
      _ ≤ _ := EReal.sub_le_sub hzero le_rfl
      _ ≤ _ := hslope

omit [MetricSpace X] in
/-- A uniform positive lower bound on the lower Birkhoff averages makes them positive. -/
private lemma birkhoffAverage_pos_of_lower_bound (T : X → X) (u : X → ℝ) {Z : Set X} {α : ℝ}
    (hα : 0 < α)
    (hZ : ∀ x ∈ Z, (α : EReal) ≤ lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x < ⊤) :
    ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x < ⊤ :=
  fun x hx ↦ ⟨(EReal.coe_pos.mpr hα).trans_le (hZ x hx).1, (hZ x hx).2⟩

end ZeroPotential

section UniformLower

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (Z : Set X) (hne : Z.Nonempty) (α : ℝ) (hα : 0 < α)
  (hZ : ∀ x ∈ Z, (α : EReal) ≤ lowerBirkhoffAverage T u x ∧
    upperBirkhoffAverage T u x < ⊤) (σ : LimitSide)
  (hfinite : σ.choose (lowerEntropy T Z, upperEntropy P T Z) < ⊤)

include hT hu hne hα hZ hfinite

/-- Under the uniform lower bound and finite entropy there is at most one real root.
Blueprint node `bs:set-root-unique`. -/
theorem setBowenRootUniqueness (s t : ℝ)
    (hs : σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
      upperPressure T (fun y => -s * u y) 0 Z) = 0)
    (ht : σ.choose (lowerPressure T (fun y => -t * u y) 0 Z,
      upperPressure T (fun y => -t * u y) 0 Z) = 0) : s = t := by
  -- The public interface retains `hne` and `hfinite`; the slope estimate does not need them.
  have _ := hne
  have _ := hfinite
  have hpos := birkhoffAverage_pos_of_lower_bound T u hα hZ
  have hlower : ∀ x ∈ Z, (α : EReal) ≤ lowerBirkhoffAverage T u x := fun x hx ↦ (hZ x hx).1
  rcases lt_trichotomy s t with hst | hst | hts
  · have h := setPressureSlopeAndRationalAttainment_slope
      P T hT u hu Z hpos σ α hα hlower s t hst
    rw [hs, ht, zero_sub, ← EReal.coe_neg] at h
    have hnonneg := EReal.coe_nonneg.mp h
    have hprod := mul_pos (sub_pos.mpr hst) hα
    linarith
  · exact hst
  · have h := setPressureSlopeAndRationalAttainment_slope
      P T hT u hu Z hpos σ α hα hlower t s hts
    rw [hs, ht, zero_sub, ← EReal.coe_neg] at h
    have hnonneg := EReal.coe_nonneg.mp h
    have hprod := mul_pos (sub_pos.mpr hts) hα
    linarith

/-- Under the uniform lower bound and finite entropy, the set pressure is finite at every
nonnegative parameter. -/
private lemma setPressure_lt_top (s : ℝ) (hs : 0 ≤ s) :
    σ.choose (lowerPressure T (fun y ↦ -s * u y) 0 Z,
      upperPressure T (fun y ↦ -s * u y) 0 Z) < ⊤ := by
  have hpos := birkhoffAverage_pos_of_lower_bound T u hα hZ
  have hzero : σ.choose (lowerPressure T (fun _ ↦ 0) 0 Z, upperPressure T (fun _ ↦ 0) 0 Z) < ⊤ := by
    have hent : σ.choose (lowerPressure T (fun _ ↦ 0) 0 Z, upperPressure T (fun _ ↦ 0) 0 Z) =
        ((σ.choose (lowerEntropy T Z, upperEntropy P T Z) : ℝ≥0∞) : EReal) := by
      cases σ with
      | lower => exact (entropy_eq_zeroPotentialPressure_of_nonempty P T hT Z hne).symm
      | upper => exact (entropy_eq_zeroPotentialPressure_of_nonempty_upper P T hT Z hne).symm
    rw [hent]
    exact lt_top_iff_ne_top.2 fun h ↦ hfinite.ne (EReal.coe_ennreal_eq_top_iff.1 h)
  rcases hs.eq_or_lt with rfl | hspos
  · simpa only [neg_zero, zero_mul] using hzero
  · have hslope := setPressureSlopeAndRationalAttainment_slope P T hT u hu Z hpos σ α hα
      (fun x hx ↦ (hZ x hx).1) 0 s hspos
    simp only [neg_zero, zero_mul] at hslope
    calc _ ≤ _ := hslope
      _ = σ.choose (lowerPressure T (fun _ ↦ 0) 0 Z, upperPressure T (fun _ ↦ 0) 0 Z) +
          (-((s - 0) * α : ℝ) : ℝ) := by rw [sub_eq_add_neg, EReal.coe_neg]
      _ < ⊤ := EReal.add_lt_top hzero.ne (EReal.coe_ne_top _)

omit hfinite in
include P in
/-- Under the uniform lower bound, the set pressure at a nonnegative parameter is not `-∞`: a
point of the nonempty set bounds every pointwise pressure from below. -/
private lemma bot_lt_setPressure (s : ℝ) (hs : 0 ≤ s) :
    ⊥ < σ.choose (lowerPressure T (fun y ↦ -s * u y) 0 Z,
      upperPressure T (fun y ↦ -s * u y) 0 Z) := by
  have hpos := birkhoffAverage_pos_of_lower_bound T u hα hZ
  obtain ⟨x, hx⟩ := hne
  rw [setPressure_eq_iInf_iSup_pointwisePressure P T hT u hu Z σ s]
  exact (EReal.bot_lt_coe (-s * (upperBirkhoffAverage T u x).toReal)).trans_le
    (le_iInf fun A ↦ le_iSup₂_of_le x hx
      (neg_mul_le_pointwisePressure P T hT u hu A x (hpos x hx).1 (hpos x hx).2 σ hs))

/-- On nonnegative parameters the pressure is real-valued under these hypotheses.
Blueprint node `bs:set-root-unique`. -/
theorem setBowenRootUniqueness_real (s : ℝ) (hs : 0 ≤ s) :
    ∃ v : ℝ, σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
      upperPressure T (fun y => -s * u y) 0 Z) = (v : EReal) :=
  ⟨_, (EReal.coe_toReal (setPressure_lt_top P T hT u hu Z hne α hα hZ σ hfinite s hs).ne
    (bot_lt_setPressure P T hT u hu Z hne α hα hZ σ s hs).ne').symm⟩

/-- Strict decrease holds on the nonnegative parameter region; no global finiteness is assumed.
Blueprint node `bs:set-root-unique`. -/
theorem setBowenRootUniqueness_strict :
    StrictAntiOn (fun s : ℝ => σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
      upperPressure T (fun y => -s * u y) 0 Z)) (Set.Ici 0) := by
  intro s hs t _ hst
  have hpos := birkhoffAverage_pos_of_lower_bound T u hα hZ
  have hslope := setPressureSlopeAndRationalAttainment_slope P T hT u hu Z hpos σ α hα
    (fun x hx ↦ (hZ x hx).1) s t hst
  obtain ⟨v, hv⟩ := setBowenRootUniqueness_real P T hT u hu Z hne α hα hZ σ hfinite s hs
  dsimp only
  rw [hv] at hslope ⊢
  rw [← EReal.coe_sub] at hslope
  exact hslope.trans_lt (EReal.coe_lt_coe_iff.2 (sub_lt_self v (mul_pos (sub_pos.2 hst) hα)))

omit hfinite hne in
/-- At a point of `Z`, the pointwise dimension is at most the orbit complexity rate divided by the
uniform lower bound on the Birkhoff averages. -/
private lemma pointwiseBSDimension_le_orbitComplexities_div
    (A : Set ℕ) (x : X) (hx : x ∈ Z) :
    σ.choose (pointwiseBSDimension P T u A x) ≤
      σ.choose (orbitComplexities P T A x) / ENNReal.ofReal α := by
  by_cases hk : σ.choose (orbitComplexities P T A x) = ⊤
  · rw [hk, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top
  have hzero := pointwisePressure_zero_le_orbitComplexities P T σ A x
  have hzero_finite : σ.choose (pointwisePressure P T (fun _ ↦ 0) A x) < ⊤ :=
    hzero.trans_lt (lt_top_iff_ne_top.mpr fun h ↦ hk (EReal.coe_ennreal_eq_top_iff.mp h))
  have hpos : 0 < lowerBirkhoffAverage T u x :=
    (EReal.coe_pos.mpr hα).trans_le (hZ x hx).1
  have hupper := (hZ x hx).2
  have hdim := pointwiseBowenEquation_finite P T hT u hu A x hpos hupper σ hzero_finite
  have havg : lowerBirkhoffAverage T u x ≤ upperBirkhoffAverage T u x :=
    liminf_le_limsup
  have hℓtop : lowerBirkhoffAverage T u x ≠ ⊤ := (havg.trans_lt hupper).ne
  have hαℓ : α ≤ (lowerBirkhoffAverage T u x).toReal :=
    EReal.coe_le_coe_iff.mp ((hZ x hx).1.trans (EReal.le_coe_toReal hℓtop))
  have hℓb : (lowerBirkhoffAverage T u x).toReal ≤
      (upperBirkhoffAverage T u x).toReal :=
    EReal.toReal_le_toReal havg hpos.ne_bot hupper.ne
  have hsand := (pointwiseBowenEquation_sandwich P T hT u hu A x hpos hupper
    σ hzero_finite 0).1
  simp only [sub_zero, neg_zero, zero_mul] at hsand
  rw [min_eq_left (mul_le_mul_of_nonneg_right hℓb ENNReal.toReal_nonneg)] at hsand
  have hmul : (lowerBirkhoffAverage T u x).toReal *
      (σ.choose (pointwiseBSDimension P T u A x)).toReal ≤
        (σ.choose (orbitComplexities P T A x)).toReal := by
    apply EReal.coe_le_coe_iff.mp
    exact (hsand.trans hzero).trans_eq (EReal.coe_ennreal_toReal hk).symm
  have hreal : (σ.choose (pointwiseBSDimension P T u A x)).toReal ≤
      (σ.choose (orbitComplexities P T A x)).toReal / α := by
    apply (le_div_iff₀ hα).mpr
    calc
      _ = α * (σ.choose (pointwiseBSDimension P T u A x)).toReal := mul_comm _ _
      _ ≤ (lowerBirkhoffAverage T u x).toReal *
          (σ.choose (pointwiseBSDimension P T u A x)).toReal :=
        mul_le_mul_of_nonneg_right hαℓ ENNReal.toReal_nonneg
      _ ≤ _ := hmul
  calc
    _ = ENNReal.ofReal (σ.choose (pointwiseBSDimension P T u A x)).toReal :=
      (ENNReal.ofReal_toReal hdim.ne).symm
    _ ≤ ENNReal.ofReal ((σ.choose (orbitComplexities P T A x)).toReal / α) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_div_of_pos hα, ENNReal.ofReal_toReal hk]

/-- Entropy divided by the uniform lower average bounds the relevant BS dimension.
Blueprint node `bs:set-root-unique`. -/
theorem setBowenRootUniqueness_dimension_le :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) ≤
      σ.choose (lowerEntropy T Z, upperEntropy P T Z) / ENNReal.ofReal α := by
  -- The public interface retains `hne`; the oracle argument does not need it.
  have _ := hne
  obtain ⟨A, hA⟩ := upperEntropy_pointToSet_simultaneous P T hT (fun _ _ ↦ 0)
    (fun _ ↦ uniformContinuous_const) (fun _ ↦ 0) Z
  have hentropy : σ.choose (lowerEntropy T Z, upperEntropy P T Z) =
      ⨆ x ∈ Z, σ.choose (orbitComplexities P T A x) := by
    cases σ with
    | lower => exact (hA A (TuringReducible.refl _)).1
    | upper => exact (hA A (TuringReducible.refl _)).2.1
  have hdim := bsPointToSet_all_oracles P T hT u hu Z
    (fun x hx ↦ (EReal.coe_pos.mpr hα).trans_le (hZ x hx).1) A σ
  have hsup : (⨆ x ∈ Z, σ.choose (pointwiseBSDimension P T u A x)) ≤
      (⨆ x ∈ Z, σ.choose (orbitComplexities P T A x)) / ENNReal.ofReal α := by
    calc
      _ ≤ ⨆ x ∈ Z, σ.choose (orbitComplexities P T A x) / ENNReal.ofReal α :=
        iSup₂_mono fun x hx ↦
          pointwiseBSDimension_le_orbitComplexities_div P T hT u hu Z α hα hZ σ A x hx
      _ = _ := by simp only [div_eq_mul_inv, ENNReal.iSup_mul]
  rw [hentropy]
  exact hdim.trans hsup

/-- In particular the relevant BS dimension is finite.
Blueprint node `bs:set-root-unique`. -/
theorem setBowenRootUniqueness_dimension_finite :
    σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) < ⊤ :=
  (setBowenRootUniqueness_dimension_le P T hT u hu Z hne α hα hZ σ hfinite).trans_lt
    (ENNReal.div_lt_top hfinite.ne (by simpa using hα))

end UniformLower

end Kolmogorov.PointToSet
