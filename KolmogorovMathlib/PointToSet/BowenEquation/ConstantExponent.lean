/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Upper
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Upper

/-!
# BS dimension at a constant asymptotic exponent

If both Birkhoff averages of a uniformly continuous potential equal the same positive
constant on a set, its lower and upper Barreira–Schmeling dimensions are the corresponding
entropies divided by that constant. This proves blueprint node `bs:constant-exponent`,
including infinite entropy and the empty set, for the Bowen equation results.

Realizer bounds first compare finite-scale costs with those of the constant potential one.
The comparisons pass through time limits and dyadic scale suprema, and letting the positive
slack tend to zero gives the pointwise identities. The entropy and BS point-to-set principles
then give the set identities. `BowenEquation` re-exports these conclusions.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- Linear bounds on realizer sums bound the BS cost by rescaled unit-potential costs. -/
private lemma finite_scale_bs_cost_bounds (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (r : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ i, P.ι i ∈ bowenBall T n x r →
      a * n ≤ birkhoffSum T u n (P.ι i) ∧ birkhoffSum T u n (P.ι i) ≤ b * n) :
    finiteScaleBSCost P T (fun _ ↦ 1) A x n r / ENNReal.ofReal b ≤
        finiteScaleBSCost P T u A x n r ∧
      finiteScaleBSCost P T u A x n r ≤
        finiteScaleBSCost P T (fun _ ↦ 1) A x n r / ENNReal.ofReal a := by
  have hn0 : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hone (y : X) : birkhoffSum T (fun _ ↦ (1 : ℝ)) n y = n := by
    simp [birkhoffSum]
  have hpos (i : ℕ) (hi : P.ι i ∈ bowenBall T n x r) :
      0 < birkhoffSum T u n (P.ι i) := (mul_pos ha hn_pos).trans_le (h i hi).1
  have hdiv (c : ℝ) (hc : 0 < c) (k : ℝ≥0∞) :
      k / ENNReal.ofReal (n : ℝ) / ENNReal.ofReal c =
        k / ENNReal.ofReal (c * n) := by
    rw [ENNReal.ofReal_mul hc.le, div_eq_mul_inv, div_eq_mul_inv,
      div_eq_mul_inv, ENNReal.mul_inv]
    · ac_rfl
    · exact Or.inr ENNReal.ofReal_ne_top
    · exact Or.inl ENNReal.ofReal_ne_top
  simp only [finiteScaleBSCost, hn0, ↓reduceIte, hone, hn_pos, iInf_pos]
  constructor
  · simp only [ENNReal.iInf_div_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hb))
      ENNReal.ofReal_ne_top]
    refine le_iInf fun i ↦ le_iInf fun hi ↦ le_iInf fun _ ↦ ?_
    refine (iInf_le_of_le i (iInf_le_of_le hi le_rfl)).trans ?_
    rw [hdiv b hb]
    exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (h i hi).2) _
  · simp only [ENNReal.iInf_div_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
      ENNReal.ofReal_ne_top]
    refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    refine (iInf_le_of_le i (iInf_le_of_le hi (iInf_le_of_le (hpos i hi) le_rfl))).trans ?_
    rw [hdiv a ha]
    exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (h i hi).1) _

/-- A constant positive Birkhoff average gives cost bounds at all sufficiently fine scales
and, at each such scale, all sufficiently large times. -/
private lemma eventually_bs_cost_bounds (P : Presentation X) (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (A : Set ℕ) (x : X) (α : ℝ)
    (hx : lowerBirkhoffAverage T u x = (α : EReal) ∧
      upperBirkhoffAverage T u x = (α : EReal)) (η : ℝ) (hη : 0 < η) (hηα : η < α) :
    ∀ᶠ p in atTop, ∀ᶠ n in atTop,
      finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) / ENNReal.ofReal (α + η) ≤
          finiteScaleBSCost P T u A x n (dyadicRadius p) ∧
        finiteScaleBSCost P T u A x n (dyadicRadius p) ≤
          finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) / ENNReal.ofReal (α - η) := by
  obtain ⟨r₀, hr₀, hbounds⟩ :=
    birkhoffRealizerBounds P T u hu x α α hx.1 hx.2 η hη
  obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2⁻¹ : ℝ) < 1)
  refine eventually_atTop.mpr ⟨p₀, fun p hp ↦ ?_⟩
  have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  obtain ⟨N, hN, hbounds⟩ := hbounds (dyadicRadius p) hr
    ((dyadicRadius_antitone hp).trans hp₀.le)
  refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hN.trans hn))
  apply finite_scale_bs_cost_bounds P T u A x (α - η) (α + η)
    (sub_pos.mpr hηα) (by linarith) _ n (hN.trans hn)
  intro i hi
  obtain ⟨hl, hu⟩ := hbounds n hn i hi
  exact ⟨(le_div_iff₀ hn_pos).mp hl, (div_le_iff₀ hn_pos).mp hu⟩

/-- Eventual quotient bounds pass through both lower and upper time limits. -/
private lemma time_limits_div_bounds (f g : ℕ → ℝ≥0∞) (a b : ℝ≥0∞)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ᶠ n in atTop, f n / b ≤ g n ∧ g n ≤ f n / a) :
    (liminf f atTop / b ≤ liminf g atTop ∧ liminf g atTop ≤ liminf f atTop / a) ∧
      (limsup f atTop / b ≤ limsup g atTop ∧ limsup g atTop ≤ limsup f atTop / a) := by
  have ha' : a⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr ha
  have hb' : b⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hb
  have hl := h.mono fun _ hn ↦ hn.1
  have hu := h.mono fun _ hn ↦ hn.2
  simp only [ENNReal.div_eq_inv_mul] at hl hu ⊢
  constructor
  · constructor
    · simpa only [ENNReal.liminf_const_mul_of_ne_top hb'] using liminf_le_liminf hl
    · simpa only [ENNReal.liminf_const_mul_of_ne_top ha'] using liminf_le_liminf hu
  · constructor
    · simpa only [ENNReal.limsup_const_mul_of_ne_top hb'] using limsup_le_limsup hl
    · simpa only [ENNReal.limsup_const_mul_of_ne_top ha'] using limsup_le_limsup hu

/-- Eventual quotient bounds for monotone sequences pass to their suprema. -/
private lemma iSup_div_bounds (f g : ℕ → ℝ≥0∞) (hf : Monotone f) (hg : Monotone g)
    (a b : ℝ≥0∞) (h : ∀ᶠ p in atTop, f p / b ≤ g p ∧ g p ≤ f p / a) :
    (⨆ p, f p) / b ≤ ⨆ p, g p ∧ (⨆ p, g p) ≤ (⨆ p, f p) / a := by
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp h
  rw [← hf.iSup_nat_add p₀, ← hg.iSup_nat_add p₀]
  simp only [ENNReal.iSup_div]
  exact ⟨iSup_mono fun p ↦ (hp₀ (p + p₀) (Nat.le_add_left _ _)).1,
    iSup_mono fun p ↦ (hp₀ (p + p₀) (Nat.le_add_left _ _)).2⟩

/-- Quotient bounds with arbitrarily small positive slack determine an extended nonnegative
value, even when the numerator is infinite. -/
private lemma eq_div_of_slack_bounds (K D : ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h : ∀ η : ℝ, 0 < η → η < α →
      K / ENNReal.ofReal (α + η) ≤ D ∧ D ≤ K / ENNReal.ofReal (α - η)) :
    D = K / ENNReal.ofReal α := by
  have hzero : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hadd : Tendsto (fun η : ℝ ↦ α + η) (𝓝[>] 0) (𝓝 α) := by
    simpa using tendsto_const_nhds.add hzero
  have hsub : Tendsto (fun η : ℝ ↦ α - η) (𝓝[>] 0) (𝓝 α) := by
    simpa using tendsto_const_nhds.sub hzero
  have hleft := ENNReal.Tendsto.const_div
    ((ENNReal.continuous_ofReal.tendsto α).comp hadd) (a := K) (Or.inl ENNReal.ofReal_ne_top)
  have hright := ENNReal.Tendsto.const_div
    ((ENNReal.continuous_ofReal.tendsto α).comp hsub) (a := K) (Or.inl ENNReal.ofReal_ne_top)
  have hevent : ∀ᶠ η in 𝓝[>] 0,
      K / ENNReal.ofReal (α + η) ≤ D ∧ D ≤ K / ENNReal.ofReal (α - η) := by
    filter_upwards [Ioo_mem_nhdsGT hα] with η hη
    exact h η hη.1 hη.2
  exact le_antisymm (ge_of_tendsto hright (hevent.mono fun _ hη ↦ hη.2))
    (le_of_tendsto hleft (hevent.mono fun _ hη ↦ hη.1))

/-- At a point with constant positive Birkhoff average, both effective BS dimensions are
obtained by dividing the orbit complexities by that average. -/
private lemma pointwise_bs_dimension_eq_div (P : Presentation X) (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (A : Set ℕ) (x : X) (α : ℝ) (hα : 0 < α)
    (hx : lowerBirkhoffAverage T u x = (α : EReal) ∧
      upperBirkhoffAverage T u x = (α : EReal)) :
    (pointwiseBSDimension P T u A x).1 = (orbitComplexities P T A x).1 / ENNReal.ofReal α ∧
      (pointwiseBSDimension P T u A x).2 = (orbitComplexities P T A x).2 / ENNReal.ofReal α := by
  let C (v : X → ℝ) (p n : ℕ) := finiteScaleBSCost P T v A x n (dyadicRadius p)
  have hmono (v : X → ℝ) (n : ℕ) : Monotone (fun p ↦ C v p n) := by
    intro p q hpq
    exact pointwiseBSDimension_antitone_radius P T v A x n (dyadicRadius_antitone hpq)
  have hinf (v : X → ℝ) : Monotone (fun p ↦ liminf (C v p) atTop) := by
    intro p q hpq
    exact liminf_le_liminf (Eventually.of_forall fun n ↦ hmono v n hpq)
  have hsup (v : X → ℝ) : Monotone (fun p ↦ limsup (C v p) atTop) := by
    intro p q hpq
    exact limsup_le_limsup (Eventually.of_forall fun n ↦ hmono v n hpq)
  have hbounds (η : ℝ) (hη : 0 < η) (hηα : η < α) :
      ((orbitComplexities P T A x).1 / ENNReal.ofReal (α + η) ≤
          (pointwiseBSDimension P T u A x).1 ∧
        (pointwiseBSDimension P T u A x).1 ≤
          (orbitComplexities P T A x).1 / ENNReal.ofReal (α - η)) ∧
      ((orbitComplexities P T A x).2 / ENNReal.ofReal (α + η) ≤
          (pointwiseBSDimension P T u A x).2 ∧
        (pointwiseBSDimension P T u A x).2 ≤
          (orbitComplexities P T A x).2 / ENNReal.ofReal (α - η)) := by
    have ha : ENNReal.ofReal (α - η) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hηα))
    have hb : ENNReal.ofReal (α + η) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    have htime := (eventually_bs_cost_bounds P T u hu A x α hx η hη hηα).mono
      fun p hp ↦ time_limits_div_bounds (C (fun _ ↦ 1) p) (C u p) _ _ ha hb hp
    exact ⟨iSup_div_bounds _ _ (hinf (fun _ ↦ 1)) (hinf u) _ _ (htime.mono fun _ h ↦ h.1),
      iSup_div_bounds _ _ (hsup (fun _ ↦ 1)) (hsup u) _ _ (htime.mono fun _ h ↦ h.2)⟩
  exact ⟨eq_div_of_slack_bounds _ _ α hα (fun η hη hηα ↦ (hbounds η hη hηα).1),
    eq_div_of_slack_bounds _ _ α hα (fun η hη hηα ↦ (hbounds η hη hηα).2)⟩

/-- A common positive asymptotic exponent divides lower entropy, including infinite entropy
and the empty set. Blueprint node `bs:constant-exponent`. -/
theorem bsDimensionConstantExponent (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X) (α : ℝ) (hα : 0 < α)
    (hZ : ∀ x ∈ Z, lowerBirkhoffAverage T u x = (α : EReal) ∧
      upperBirkhoffAverage T u x = (α : EReal)) :
    lowerBSDimension T u Z = lowerEntropy T Z / ENNReal.ofReal α := by
  have hZ_pos : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x := by
    intro x hx
    rw [(hZ x hx).1]
    exact_mod_cast hα
  rw [bsPointToSet P T hT u hu Z hZ_pos,
    entropy_effectiveCharacterization_allOracles_pointToSet P T hT Z,
    ENNReal.iInf_div_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hα)) ENNReal.ofReal_ne_top]
  congr 1
  funext A
  simp only [ENNReal.iSup_div]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  exact (pointwise_bs_dimension_eq_div P T u hu A x α hα (hZ x hx)).1

/-- The same constant exponent divides upper entropy without a finiteness hypothesis.
Blueprint node `bs:constant-exponent`. -/
theorem bsDimensionConstantExponent_upper (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (α : ℝ) (hα : 0 < α)
    (hZ : ∀ x ∈ Z, lowerBirkhoffAverage T u x = (α : EReal) ∧
      upperBirkhoffAverage T u x = (α : EReal)) :
    upperBSDimension T u Z = upperEntropy P T Z / ENNReal.ofReal α := by
  have hZ_pos : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x := by
    intro x hx
    rw [(hZ x hx).1]
    exact_mod_cast hα
  rw [bsPointToSet_upper P T hT u hu Z hZ_pos, upperEntropy_pointToSet P T hT Z,
    ENNReal.iInf_div_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hα)) ENNReal.ofReal_ne_top]
  congr 1
  funext A
  simp only [ENNReal.iSup_div]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  exact (pointwise_bs_dimension_eq_div P T u hu A x α hα (hZ x hx)).2

end Kolmogorov.PointToSet
