/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics
import KolmogorovMathlib.Oracle.Joins
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing normalized coding overhead

A fixed additive description cost vanishes when divided by an eventually positive linear
quantity; logarithmic coding costs also vanish after division by time. These estimates
implement blueprint node `order:slack`. They transfer oracle monotonicity of complexity
through the finite-scale infima and time limits defining pointwise pressure and
Barreira–Schmeling dimension. For the latter, a positive lower Birkhoff average and uniform
continuity give a linear denominator bound throughout sufficiently small Bowen balls.

The `Order` module exports these comparisons for the oracle minima in the point-to-set
principles for pressure and Barreira–Schmeling dimension.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

/-- A fixed description overhead divided by an eventually positive linear denominator
tends to zero. Blueprint node `order:slack`. -/
theorem normalized_additive_slack (a : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (ha : ∀ᶠ n in atTop, c * n ≤ a n) (d : ℕ) :
    Tendsto (fun n => (d : ℝ) / a n) atTop (𝓝 0) := by
  have hlinear : Tendsto (fun n : ℕ ↦ (d : ℝ) / (c * n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_inv, mul_assoc, mul_zero] using
      tendsto_inv_atTop_nhds_zero_nat.const_mul ((d : ℝ) / c)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlinear
  · filter_upwards [ha] with n hn
    exact div_nonneg (Nat.cast_nonneg d)
      ((mul_nonneg hc.le (Nat.cast_nonneg n)).trans hn)
  · filter_upwards [ha, eventually_gt_atTop 0] with n hn hnpos
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg d)
      (mul_pos hc (Nat.cast_pos.mpr hnpos)) hn

/-- Logarithmic coding overhead divided by time tends to zero.
Blueprint node `order:slack`. -/
theorem normalized_additive_slack_log :
    Tendsto (fun n : ℕ => Real.log (n + 1) / n) atTop (𝓝 0) := by
  have hlog := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
    hlog.comp hshift

/-- The binary length is bounded by a logarithm, up to one extra bit. -/
private lemma nat_size_le_log (n : ℕ) (hn : 0 < n) :
    (Nat.size n : ℝ) ≤ Real.log (n + 1) / Real.log 2 + 1 := by
  have hpow : 2 ^ (Nat.size n - 1) ≤ n :=
    Nat.lt_size.mp (Nat.sub_lt (Nat.size_pos.mpr hn) zero_lt_one)
  have hpow_real : (2 : ℝ) ^ (Nat.size n - 1) ≤ n := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpow_real
  rw [Real.log_pow, Nat.cast_sub (Nat.size_pos.mpr hn), Nat.cast_one] at hlog
  have hsize : (Nat.size n : ℝ) - 1 ≤ Real.log n / Real.log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog
  have hmono : Real.log (n : ℝ) ≤ Real.log (n + 1) :=
    Real.log_le_log (Nat.cast_pos.mpr hn) (by linarith)
  have : Real.log (n : ℝ) / Real.log 2 ≤ Real.log (n + 1) / Real.log 2 :=
    div_le_div_of_nonneg_right hmono (Real.log_nonneg (by norm_num))
  linarith

/-- The library's explicit logarithmic slack also vanishes after normalization.
Blueprint node `order:slack`. -/
theorem normalized_additive_slack_logSlack (c : ℕ) :
    Tendsto (fun n : ℕ => (logSlack c n : ℝ) / n) atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun n : ℕ ↦ (Real.log (n + 1) / Real.log 2 + 1) / n) atTop (𝓝 0) := by
    have h := (normalized_additive_slack_log.div_const (Real.log 2)).add
      tendsto_inv_atTop_nhds_zero_nat
    simp only [zero_div, zero_add] at h
    convert h using 1
    ext n
    ring
  have hbits : Tendsto (fun n : ℕ ↦ ((Nat.bits n).length : ℝ) / n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    · exact Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Nat.size_eq_bits_len]
      exact div_le_div_of_nonneg_right (nat_size_le_log n hn) (Nat.cast_nonneg n)
  have h := (hbits.const_mul (c : ℝ)).add
    (tendsto_inv_atTop_nhds_zero_nat.const_mul (c : ℝ))
  simpa only [logSlack, Nat.cast_add, Nat.cast_mul, div_eq_mul_inv, add_mul,
    mul_assoc, mul_zero, add_zero] using h

/-- A vanishing real additive error preserves the order of lower extended-real limits. -/
private lemma ereal_liminf_le_of_le_add (f g : ℕ → EReal) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    liminf f atTop ≤ liminf g atTop := by
  have he' : Tendsto (fun n ↦ (e n : EReal)) atTop (𝓝 0) :=
    (continuous_coe_real_ereal.tendsto 0).comp he
  have hsum := EReal.liminf_add_le (u := fun n ↦ (e n : EReal)) (v := g)
    (.inl (he'.limsup_eq.trans_ne EReal.zero_ne_bot))
    (.inl (he'.limsup_eq.trans_ne EReal.zero_ne_top))
  have hcomm : (fun n ↦ (e n : EReal)) + g = fun n ↦ g n + (e n : EReal) := by
    exact funext fun n ↦ add_comm (e n : EReal) (g n)
  rw [hcomm, he'.limsup_eq, zero_add] at hsum
  exact (liminf_le_liminf h).trans hsum

/-- A vanishing real additive error preserves the order of upper extended-real limits. -/
private lemma ereal_limsup_le_of_le_add (f g : ℕ → EReal) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    limsup f atTop ≤ limsup g atTop := by
  have he' : Tendsto (fun n ↦ (e n : EReal)) atTop (𝓝 0) :=
    (continuous_coe_real_ereal.tendsto 0).comp he
  have hsum := EReal.limsup_add_le (u := g) (v := fun n ↦ (e n : EReal))
    (.inr (he'.limsup_eq.trans_ne EReal.zero_ne_top))
    (.inr (he'.limsup_eq.trans_ne EReal.zero_ne_bot))
  simpa only [he'.limsup_eq, add_zero] using (limsup_le_limsup h).trans hsum

variable {X : Type*} [MetricSpace X]

/-- Under an oracle reduction, the target pressure rate is at most the source rate plus
`c / n`, with a constant independent of the point and radius. -/
private lemma finiteScalePressureRate_le_add_of_reducible
    (P : Presentation X) (T : X → X) (φ : X → ℝ) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) :
    ∃ c : ℕ, ∀ x n ε, finiteScalePressureRate P T φ B x n ε ≤
      finiteScalePressureRate P T φ A x n ε + (((c : ℝ) / n : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ := oracle_monotonicity A B hAB
  refine ⟨c, fun x n ε ↦ ?_⟩
  by_cases hn : n = 0
  · simp [finiteScalePressureRate, hn]
  simp only [finiteScalePressureRate, hn, ite_false]
  refine le_trans (iInf_mono fun i ↦ ?_) (EReal.iInf_add_coe_le _ _)
  refine le_trans (iInf_mono fun _ ↦ ?_) (EReal.iInf_add_coe_le _ _)
  have hcomplexity : (oracleNatComplexity B i : ℝ) ≤ oracleNatComplexity A i + c := by
    exact_mod_cast hc (natBits i)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-- Oracle monotonicity passes to lower pointwise pressure for the same presentation.
Blueprint node `order:slack`. -/
theorem normalized_additive_slack_pressure (P : Presentation X) (T : X → X)
    (φ : X → ℝ) (A B : Set ℕ) (hAB : charOracle A ≤ᵀ charOracle B) (x : X) :
    (pointwisePressure P T φ B x).1 ≤ (pointwisePressure P T φ A x).1 := by
  obtain ⟨c, hc⟩ := finiteScalePressureRate_le_add_of_reducible P T φ A B hAB
  apply iSup_mono
  intro p
  exact ereal_liminf_le_of_le_add _ _ _ (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
    (Eventually.of_forall fun n ↦ hc x n (dyadicRadius p))

/-- Oracle monotonicity passes to upper pointwise pressure.
Blueprint node `order:slack`. -/
theorem normalized_additive_slack_pressure_upper (P : Presentation X) (T : X → X)
    (φ : X → ℝ) (A B : Set ℕ) (hAB : charOracle A ≤ᵀ charOracle B) (x : X) :
    (pointwisePressure P T φ B x).2 ≤ (pointwisePressure P T φ A x).2 := by
  obtain ⟨c, hc⟩ := finiteScalePressureRate_le_add_of_reducible P T φ A B hAB
  apply iSup_mono
  intro p
  exact ereal_limsup_le_of_le_add _ _ _ (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
    (Eventually.of_forall fun n ↦ hc x n (dyadicRadius p))

/-- Positive lower average gives an eventual linear lower bound throughout small Bowen balls. -/
private lemma exists_birkhoffSum_lower_bound (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ p₀ : ℕ, ∃ ρ > (0 : ℝ), ∀ p ≥ p₀, ∀ᶠ n in atTop,
      ∀ y ∈ bowenBall T n x (dyadicRadius p), ρ * (n : ℝ) ≤ birkhoffSum T u n y := by
  obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
  have hrpos : 0 < r := EReal.coe_pos.mp hr
  obtain ⟨ω, _, hωzero, pω, hω⟩ := small_scale_oscillation u hu
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp
    (hωzero.eventually (gt_mem_nhds (half_pos hrpos)))
  refine ⟨max pω p₁, r / 2, half_pos hrpos, fun p hp ↦ ?_⟩
  filter_upwards [eventually_lt_of_lt_liminf hrx, eventually_gt_atTop 0] with n hn hnpos
  intro y hy
  have hnpos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hbase : r * (n : ℝ) < birkhoffSum T u n x :=
    (lt_div_iff₀ hnpos_real).mp (EReal.coe_lt_coe_iff.mp hn)
  have hosc := small_scale_oscillation_birkhoff T u p (ω p)
    (hω p (by omega)) n x y hy
  have hsmall := hp₁ p (by omega)
  have hdiff := (abs_le.mp hosc).1
  nlinarith

/-- A uniform complexity overhead and a denominator bound control the BS cost infimum. -/
private lemma finiteScaleBSCost_le_add_of_complexity_le
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A B : Set ℕ) (x : X) (n : ℕ) (ε : ℝ)
    (c : ℕ) (hc : ∀ i, oracleNatComplexity B i ≤ oracleNatComplexity A i + c) (a : ℝ)
    (ha : ∀ i, P.ι i ∈ bowenBall T n x ε → a ≤ birkhoffSum T u n (P.ι i)) :
    finiteScaleBSCost P T u B x n ε ≤
      finiteScaleBSCost P T u A x n ε + (c : ℝ≥0∞) / ENNReal.ofReal a := by
  unfold finiteScaleBSCost
  split_ifs
  · exact le_top
  refine le_trans (iInf_mono fun i ↦ ?_) (le_of_eq ENNReal.iInf_add.symm)
  refine le_trans (iInf_mono fun hi ↦ ?_) (le_of_eq ENNReal.iInf_add.symm)
  refine le_trans (iInf_mono fun _ ↦ ?_) (le_of_eq ENNReal.iInf_add.symm)
  calc
    (oracleNatComplexity B i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i))
      ≤ (oracleNatComplexity A i + c : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
        gcongr
        exact_mod_cast hc i
    _ = (oracleNatComplexity A i : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i)) +
          (c : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := ENNReal.add_div
    _ ≤ (oracleNatComplexity A i : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i)) +
          (c : ℝ≥0∞) / ENNReal.ofReal a := by
        exact add_le_add le_rfl (mul_le_mul' le_rfl
          (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (ha i hi))))

/-- Division by a positive linear denominator makes a finite `ENNReal` overhead vanish. -/
private lemma tendsto_ennreal_div_linear (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / ENNReal.ofReal (ρ * n)) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal (normalized_additive_slack
    (fun n ↦ ρ * n) ρ hρ (Eventually.of_forall fun _ ↦ le_rfl) c)
  simp only [ENNReal.ofReal_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [ENNReal.ofReal_div_of_pos (mul_pos hρ (Nat.cast_pos.mpr hn)), ENNReal.ofReal_natCast]

/-- Shrinking a dyadic Bowen ball can only increase its finite-scale BS cost. -/
private lemma monotone_finiteScaleBSCost (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (x : X) (n : ℕ) :
    Monotone (fun p ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) := by
  intro p q hpq
  have hradius : dyadicRadius q ≤ dyadicRadius p :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq
  unfold finiteScaleBSCost
  split_ifs
  · exact le_rfl
  apply iInf_mono
  intro i
  apply iInf_mono'
  intro hi
  refine ⟨?_, le_rfl⟩
  dsimp [bowenBall] at hi ⊢
  rw [Dynamics.mem_dynEntourage] at hi ⊢
  simp only [Set.mem_ofPred_eq] at hi ⊢
  exact fun k hk ↦ (hi k hk).trans_le hradius

/-- Oracle monotonicity passes to lower BS dimension on the positive-average locus of a
uniformly continuous potential. Blueprint node `order:slack`. -/
theorem normalized_additive_slack_bs (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    (pointwiseBSDimension P T u B x).1 ≤ (pointwiseBSDimension P T u A x).1 := by
  -- Continuity of the dynamics is retained in the interface but is not needed here.
  have _ := hT
  dsimp only [pointwiseBSDimension]
  obtain ⟨c, hc⟩ := oracle_monotonicity A B hAB
  obtain ⟨p₀, ρ, hρ, hbound⟩ := exists_birkhoffSum_lower_bound T u hu x hx
  have hslack := tendsto_ennreal_div_linear c ρ hρ
  have hscale (p : ℕ) (hp : p₀ ≤ p) :
      liminf (fun n ↦ finiteScaleBSCost P T u B x n (dyadicRadius p)) atTop ≤
        liminf (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop := by
    rw [← ENNReal.liminf_add_of_right_tendsto_zero hslack
      (f := fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))]
    refine liminf_le_liminf ?_
    filter_upwards [hbound p hp] with n hn
    exact finiteScaleBSCost_le_add_of_complexity_le P T u A B x n (dyadicRadius p)
      c (fun i ↦ hc (natBits i)) (ρ * n) (fun i hi ↦ hn (P.ι i) hi)
  apply iSup_le
  intro p
  have hmono :
      liminf (fun n ↦ finiteScaleBSCost P T u B x n (dyadicRadius p)) atTop ≤
        liminf (fun n ↦ finiteScaleBSCost P T u B x n (dyadicRadius (max p p₀))) atTop :=
    liminf_le_liminf (Eventually.of_forall fun n ↦
      monotone_finiteScaleBSCost P T u B x n (le_max_left _ _))
  refine hmono.trans ((hscale (max p p₀) (le_max_right _ _)).trans ?_)
  exact le_iSup
    (fun q ↦ liminf (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius q)) atTop) (max p p₀)

/-- Oracle monotonicity passes to upper BS dimension on the positive-average locus of a
uniformly continuous potential. Blueprint node `order:slack`. -/
theorem normalized_additive_slack_bs_upper (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    (pointwiseBSDimension P T u B x).2 ≤ (pointwiseBSDimension P T u A x).2 := by
  -- Continuity of the dynamics is retained in the interface but is not needed here.
  have _ := hT
  dsimp only [pointwiseBSDimension]
  obtain ⟨c, hc⟩ := oracle_monotonicity A B hAB
  obtain ⟨p₀, ρ, hρ, hbound⟩ := exists_birkhoffSum_lower_bound T u hu x hx
  have hslack := tendsto_ennreal_div_linear c ρ hρ
  have hscale (p : ℕ) (hp : p₀ ≤ p) :
      limsup (fun n ↦ finiteScaleBSCost P T u B x n (dyadicRadius p)) atTop ≤
        limsup (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop := by
    rw [← ENNReal.limsup_add_of_right_tendsto_zero hslack
      (f := fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))]
    refine limsup_le_limsup ?_
    filter_upwards [hbound p hp] with n hn
    exact finiteScaleBSCost_le_add_of_complexity_le P T u A B x n (dyadicRadius p)
      c (fun i ↦ hc (natBits i)) (ρ * n) (fun i hi ↦ hn (P.ι i) hi)
  apply iSup_le
  intro p
  have hmono :
      limsup (fun n ↦ finiteScaleBSCost P T u B x n (dyadicRadius p)) atTop ≤
        limsup (fun n ↦ finiteScaleBSCost P T u B x n (dyadicRadius (max p p₀))) atTop :=
    limsup_le_limsup (Eventually.of_forall fun n ↦
      monotone_finiteScaleBSCost P T u B x n (le_max_left _ _))
  refine hmono.trans ((hscale (max p p₀) (le_max_right _ _)).trans ?_)
  exact le_iSup
    (fun q ↦ limsup (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius q)) atTop) (max p p₀)

end Kolmogorov.PointToSet
