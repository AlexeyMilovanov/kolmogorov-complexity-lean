/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Distortion.DistortionModuli

/-!
# Pointwise conformal comparison of static and Barreira–Schmeling dimensions

For a point `x` in the conformal locus (positive finite lower Birkhoff average, tempered
contraction and sublinear orbit growth), the lower and upper static point dimensions of `x`
relative to any oracle `A` coincide with the lower and upper pointwise Barreira–Schmeling
dimensions of `x` for `(T, u)`. This is the blueprint theorem `conf:pointwise`, in the two
forms `pointwiseDimensionEqBS` and `pointwiseDimensionEqBS_upper`.

The proof compares, at order `n + 1`, the Bowen ball with the metric balls of the radii
`r_n^-` and `r_n^+` of `DistortionModuli`; the numerical estimate of these radii against the
Birkhoff sums on the Bowen ball is `orbitScaleDenominators_bounds` (blueprint node
`conf:denominators`). The finite-scale BS cost is squeezed between the normalized precision
complexities at the two radii, nonmonotone scale sampling turns the radius sequences into the
static limits, and the multiplicative error is removed by letting the Bowen-ball radius and the
slack parameters tend to zero. Lower and upper limits are treated simultaneously through
`LimitSide`.

The module is used by `KolmogorovMathlib.PointToSet.Conformal.TheoremE.DimensionTheorem` to
identify the point-to-set dimensions of the conformal locus with the Bowen-equation quantities.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- Along the orbit of `x`, the logarithmic orbit precision stays within `n * τ + K` of the
Birkhoff sum `S_n u (x)`, where `K` depends only on `η` and `δ`. Blueprint node
`conf:denominators`. -/
private lemma exists_abs_conformalOrbitPrecision_sub_birkhoffSum_le
    (C : UniformConformalData X) (x : X) (τ η δ : ℝ) (hτ : 0 < τ) (hη : 0 < η) (hδ : 0 < δ)
    (σ : LimitSide) :
    ∃ K : ℝ, ∀ n : ℕ,
      |conformalOrbitPrecision C σ x η δ τ n - birkhoffSum C.T C.potential n x| ≤
        (n : ℝ) * τ + K := by
  refine ⟨|Real.logb 2 (η * δ)| + |Real.logb 2 δ|, fun n ↦ ?_⟩
  have hn : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.le
  unfold conformalOrbitPrecision conformalOrbitRadius
  cases σ
  · dsimp only [LimitSide.choose]
    rw [Real.logb_mul (mul_pos hη hδ).ne' (by positivity),
      Real.logb_rpow (by norm_num) (by norm_num)]
    have h1 := neg_abs_le (Real.logb 2 (η * δ))
    have h2 := le_abs_self (Real.logb 2 (η * δ))
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (Real.logb 2 δ)]
  · dsimp only [LimitSide.choose]
    rw [Real.logb_mul hδ.ne' (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
    have h1 := neg_abs_le (Real.logb 2 δ)
    have h2 := le_abs_self (Real.logb 2 δ)
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (Real.logb 2 (η * δ))]

/-- Numerical core of `orbitScaleDenominators_bounds`: if `t n` stays within `n * τ + K` of
`s n ≥ a * n` eventually, and `v n / n → 0`, then the error `(n + 1) * ω + |v n| + n * τ + K`
is eventually at most `c * t n`, whenever `(τ + ω) / (a - τ) < c`. -/
private lemma eventually_pos_and_error_le_mul (s t v : ℕ → ℝ) (a τ ω K c : ℝ)
    (hτ : 0 ≤ τ) (hω : 0 ≤ ω) (hta : τ < a) (hc : (τ + ω) / (a - τ) < c)
    (hs : ∀ᶠ n : ℕ in atTop, a * (n : ℝ) ≤ s n)
    (ht : ∀ n : ℕ, |t n - s n| ≤ (n : ℝ) * τ + K)
    (hv : Tendsto (fun n : ℕ ↦ v n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, 0 < t n ∧
      ((n : ℝ) + 1) * ω + |v n| + (n : ℝ) * τ + K ≤ c * t n := by
  have hat : 0 < a - τ := sub_pos.mpr hta
  have hcd : τ + ω < c * (a - τ) := (div_lt_iff₀ hat).mp hc
  have hd : 0 < c * (a - τ) - (τ + ω) := sub_pos.mpr hcd
  have hcpos : 0 < c := by
    have : 0 ≤ (τ + ω) / (a - τ) := div_nonneg (add_nonneg hτ hω) hat.le
    linarith
  have ht_lower : ∀ᶠ n : ℕ in atTop, (a - τ) * (n : ℝ) - K ≤ t n := by
    filter_upwards [hs] with n hn
    have H := abs_le.mp (ht n)
    linarith [H.1]
  have hlim : Tendsto (fun n : ℕ ↦ (|v n| + (ω + (1 + c) * K)) / (n : ℝ)) atTop (𝓝 0) := by
    have h := hv.abs.add (tendsto_const_div_atTop_nhds_zero_nat (ω + (1 + c) * K))
    simpa only [abs_div, Nat.abs_cast, abs_zero, add_zero, add_div] using h
  have hbound : ∀ᶠ n : ℕ in atTop,
      |v n| + ω + (1 + c) * K ≤ (c * (a - τ) - (τ + ω)) * (n : ℝ) := by
    filter_upwards [hlim.eventually (gt_mem_nhds hd), eventually_gt_atTop 0] with n hn hn0
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hn0)] at hn
    linarith
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (a - τ) * (n : ℝ) - K := by
    filter_upwards [eventually_gt_atTop ⌈K / (a - τ)⌉₊] with n hn
    have h1 : K / (a - τ) < (n : ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    have h2 : K < (n : ℝ) * (a - τ) := (div_lt_iff₀ hat).mp h1
    linarith
  filter_upwards [ht_lower, hbound, hpos] with n ht_low hv_bd htn
  refine ⟨by linarith, ?_⟩
  calc ((n : ℝ) + 1) * ω + |v n| + (n : ℝ) * τ + K
    _ = |v n| + ω + (1 + c) * K - c * K + (τ + ω) * (n : ℝ) := by ring
    _ ≤ (c * (a - τ) - (τ + ω)) * (n : ℝ) - c * K + (τ + ω) * (n : ℝ) := by linarith
    _ = c * ((a - τ) * (n : ℝ) - K) := by ring
    _ ≤ c * t n := mul_le_mul_of_nonneg_left ht_low hcpos.le

section OrbitScales
variable (C : UniformConformalData X) (x : X)
  (hx : x ∈ positiveFiniteAverageLocus C.T C.potential)
  (hgrowth : HasSublinearOrbitGrowth C.T C.potential x)
  (α τ η δ : ℝ) (hα : lowerBirkhoffAverage C.T C.potential x = (α : EReal))
  (hτ : 0 < τ) (hτα : τ < α / 4) (hη : 0 < η) (hηone : η ≤ 1) (hδ : 0 < δ)
  (hvar : potentialVariation C.potential δ < ⊤)
include hx hgrowth hα hτ hτα hη hηone hδ hvar

/-- The eventual two-sided denominator bound is uniform over every point in the Bowen ball.
Blueprint node `conf:denominators`. -/
theorem orbitScaleDenominators_bounds (a c : ℝ) (hta : τ < a) (haα : a < α)
    (hc : (τ + (potentialVariation C.potential δ).toReal) / (a - τ) < c)
    (σ : LimitSide) :
    ∀ᶠ n in atTop, ∀ y ∈ bowenBall C.T (n + 1) x δ,
      1 - c ≤ birkhoffSum C.T C.potential (n + 1) y /
        conformalOrbitPrecision C σ x η δ τ n ∧
      birkhoffSum C.T C.potential (n + 1) y /
        conformalOrbitPrecision C σ x η δ τ n ≤ 1 + c := by
  obtain ⟨K, hK⟩ :=
    exists_abs_conformalOrbitPrecision_sub_birkhoffSum_le C x τ η δ hτ hη hδ σ
  have hbudget := eventually_pos_and_error_le_mul
    (fun n ↦ birkhoffSum C.T C.potential n x) (fun n ↦ conformalOrbitPrecision C σ x η δ τ n)
    (fun n ↦ C.potential (C.T^[n] x)) a τ (potentialVariation C.potential δ).toReal K c
    hτ.le ENNReal.toReal_nonneg hta hc (eventually_mul_le_birkhoffSum hα haα) hK hgrowth
  filter_upwards [hbudget] with n hn y hy
  have H_var := orbitScaleDenominators_variation C x hx hgrowth α τ η δ hα hτ hτα hη hηone hδ hvar
    n y hy
  have H_diff : |birkhoffSum C.T C.potential (n + 1) y -
      conformalOrbitPrecision C σ x η δ τ n| ≤
      ((n : ℝ) + 1) * (potentialVariation C.potential δ).toReal +
        |C.potential (C.T^[n] x)| + (n : ℝ) * τ + K := by
    calc _ ≤ |birkhoffSum C.T C.potential (n + 1) y - birkhoffSum C.T C.potential n x| +
          |birkhoffSum C.T C.potential n x - conformalOrbitPrecision C σ x η δ τ n| :=
        abs_sub_le _ _ _
      _ = |birkhoffSum C.T C.potential (n + 1) y - birkhoffSum C.T C.potential n x| +
          |conformalOrbitPrecision C σ x η δ τ n - birkhoffSum C.T C.potential n x| := by
        rw [abs_sub_comm (birkhoffSum C.T C.potential n x)]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (potentialVariation C.potential δ).toReal +
          |C.potential (C.T^[n] x)| + ((n : ℝ) * τ + K) := add_le_add H_var (hK n)
      _ = _ := by push_cast; abel
  have H_abs := abs_le.mp (H_diff.trans hn.2)
  constructor
  · rw [le_div_iff₀ hn.1]
    linarith
  · rw [div_le_iff₀ hn.1]
    linarith

end OrbitScales

/-- Shifting the time index by one preserves the lower and the upper time limit of the
finite-scale BS cost. Blueprint node `conf:pointwise`. -/
theorem pointwiseDimensionEqBS_order_shift (P : Presentation X) (C : UniformConformalData X)
    (A : Set ℕ) (x : X) (δ : ℝ) (σ : LimitSide) :
    σ.timeLimit (fun n => finiteScaleBSCost P C.T C.potential A x (n + 1) δ) =
      σ.timeLimit (fun n => finiteScaleBSCost P C.T C.potential A x n δ) := by
  cases σ
  · exact liminf_nat_add (fun n ↦ finiteScaleBSCost P C.T C.potential A x n δ) 1
  · exact limsup_nat_add (fun n ↦ finiteScaleBSCost P C.T C.potential A x n δ) 1

/-- The time limit selected by `σ` commutes with multiplication by a finite constant. -/
private lemma timeLimit_const_mul (σ : LimitSide) {a : ℝ≥0∞} (ha : a ≠ ⊤) (f : ℕ → ℝ≥0∞) :
    σ.timeLimit (fun n ↦ a * f n) = a * σ.timeLimit f := by
  cases σ
  · exact ENNReal.liminf_const_mul_of_ne_top ha
  · exact ENNReal.limsup_const_mul_of_ne_top ha

/-- The finite-scale BS cost of positive order is the infimum of the complexity-to-Birkhoff-sum
ratios over the ideal points of the Bowen ball with positive Birkhoff sum. -/
private lemma finiteScaleBSCost_succ (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    (x : X) (n : ℕ) (δ : ℝ) :
    finiteScaleBSCost P T u A x (n + 1) δ =
      ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T (n + 1) x δ),
        ⨅ (_ : 0 < birkhoffSum T u (n + 1) (P.ι i)),
          (oracleNatComplexity A i : ℝ≥0∞) /
            ENNReal.ofReal (birkhoffSum T u (n + 1) (P.ι i)) := by
  simp only [finiteScaleBSCost, Nat.add_one_ne_zero, ↓reduceIte]

/-- If the Bowen ball of order `n + 1` lies in the metric ball of radius `r`, and its Birkhoff
sums are at most `(1 + c) * (-log₂ r)`, then the normalized precision complexity at radius `r`
is at most `1 + c` times the finite-scale BS cost. -/
private lemma normalizedPrecisionComplexity_le_mul_finiteScaleBSCost
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) (δ r c : ℝ)
    (hc : 0 ≤ c) (hr : 0 < -Real.logb 2 r)
    (hout : bowenBall T (n + 1) x δ ⊆ Metric.ball x r)
    (hden : ∀ y ∈ bowenBall T (n + 1) x δ, birkhoffSum T u (n + 1) y ≤ (1 + c) * (-Real.logb 2 r)) :
    normalizedPrecisionComplexity P A x r ≤
      ENNReal.ofReal (1 + c) * finiteScaleBSCost P T u A x (n + 1) δ := by
  have hplus : 0 < 1 + c := by linarith
  rw [finiteScaleBSCost_succ, ENNReal.mul_iInf_of_ne (by positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun i ↦ ?_
  rw [ENNReal.mul_iInf_of_ne (by positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun hi ↦ ?_
  rw [ENNReal.mul_iInf_of_ne (by positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun hsi ↦ ?_
  have hK : precisionComplexityNat P A x r ≤ oracleNatComplexity A i := by
    have hle : precisionComplexity P A x r ≤ (oracleNatComplexity A i : ENat) :=
      iInf_le_of_le i (iInf_le_of_le (hout hi) le_rfl)
    exact (ENat.toNat_le_toNat hle (ENat.natCast_ne_top _)).trans_eq (ENat.toNat_natCast _)
  have hratio : (precisionComplexityNat P A x r : ℝ) / (-Real.logb 2 r) ≤
      (1 + c) * ((oracleNatComplexity A i : ℝ) / birkhoffSum T u (n + 1) (P.ι i)) := by
    calc
      _ ≤ (oracleNatComplexity A i : ℝ) / (-Real.logb 2 r) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hK) hr.le
      _ ≤ _ := by
        rw [← mul_div_assoc, div_le_div_iff₀ hr hsi]
        nlinarith [mul_le_mul_of_nonneg_left (hden (P.ι i) hi)
          (Nat.cast_nonneg (oracleNatComplexity A i) : (0 : ℝ) ≤ _)]
  simpa only [normalizedPrecisionComplexity, ENNReal.ofReal_div_of_pos hr,
    ENNReal.ofReal_mul hplus.le, ENNReal.ofReal_div_of_pos hsi, ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal hratio

/-- If the metric ball of radius `r` lies in the Bowen ball of order `n + 1`, and the Birkhoff
sums on the Bowen ball are at least `(1 - c) * (-log₂ r)`, then `1 - c` times the finite-scale BS
cost is at most the normalized precision complexity at radius `r`. -/
private lemma mul_finiteScaleBSCost_le_normalizedPrecisionComplexity
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) (δ r c : ℝ)
    (hr : 0 < r) (hlog : 0 < -Real.logb 2 r) (hc1 : c < 1)
    (hin : Metric.ball x r ⊆ bowenBall T (n + 1) x δ)
    (hden : ∀ y ∈ bowenBall T (n + 1) x δ, (1 - c) * (-Real.logb 2 r) ≤ birkhoffSum T u (n + 1) y) :
    ENNReal.ofReal (1 - c) * finiteScaleBSCost P T u A x (n + 1) δ ≤
      normalizedPrecisionComplexity P A x r := by
  have hminus : 0 < 1 - c := sub_pos.mpr hc1
  obtain ⟨i, hi, hKi⟩ := staticPointDimensions_attained P A x r hr
  have hiball : P.ι i ∈ bowenBall T (n + 1) x δ := hin hi
  have hsi : 0 < birkhoffSum T u (n + 1) (P.ι i) :=
    (mul_pos hminus hlog).trans_le (hden _ hiball)
  have hKnat : precisionComplexityNat P A x r = oracleNatComplexity A i := by
    simp only [precisionComplexityNat, hKi, ENat.toNat_natCast]
  have hcost : finiteScaleBSCost P T u A x (n + 1) δ ≤
      (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u (n + 1) (P.ι i)) := by
    rw [finiteScaleBSCost_succ]
    exact iInf_le_of_le i (iInf_le_of_le hiball (iInf_le_of_le hsi le_rfl))
  refine (mul_le_mul' le_rfl hcost).trans ?_
  have hratio : (1 - c) * ((oracleNatComplexity A i : ℝ) / birkhoffSum T u (n + 1) (P.ι i)) ≤
      (oracleNatComplexity A i : ℝ) / (-Real.logb 2 r) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hsi hlog]
    nlinarith [mul_le_mul_of_nonneg_left (hden _ hiball)
      (Nat.cast_nonneg (oracleNatComplexity A i) : (0 : ℝ) ≤ _)]
  simpa only [normalizedPrecisionComplexity, hKnat, ENNReal.ofReal_mul hminus.le,
    ENNReal.ofReal_div_of_pos hsi, ENNReal.ofReal_div_of_pos hlog, ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal hratio

/-- If the logarithmic precision `-log₂ (r n)` of positive radii tends to infinity with adjacent
ratio tending to one, then the static lower (upper) dimension is the lower (upper) limit of the
normalized precision complexity along the radii `r n`. This is nonmonotone scale sampling. -/
private lemma choose_staticPointDimensions_eq_timeLimit
    (σ : LimitSide) (P : Presentation X) (A : Set ℕ) (x : X) (r : ℕ → ℝ)
    (hpos : ∀ n, 0 < r n)
    (ht : Tendsto (fun n ↦ -Real.logb 2 (r n)) atTop atTop)
    (hratio : Tendsto (fun n ↦ (-Real.logb 2 (r (n + 1))) / (-Real.logb 2 (r n))) atTop (𝓝 1)) :
    σ.choose (staticPointDimensions P A x) =
      σ.timeLimit (fun n ↦ normalizedPrecisionComplexity P A x (r n)) := by
  cases σ
  · let R : ℝ → ℝ := fun t ↦ (2 : ℝ) ^ (-t)
    let F : ℝ → ℝ≥0∞ := fun t ↦ (precisionComplexityNat P A x (R t) : ℝ≥0∞)
    have hRpos (t : ℝ) : 0 < R t := by dsimp [R]; positivity
    have hR : Tendsto R atTop (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hRpos⟩
      exact (_root_.tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
        tendsto_neg_atTop_atBot
    have hprec : Tendsto (fun s : ℝ ↦ -Real.logb 2 s) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num))
    have hRprec (s : ℝ) (hs : 0 < s) : R (-Real.logb 2 s) = s := by
      dsimp [R]
      rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hs]
    have hden (t : ℝ) : -Real.logb 2 (R t) = t := by
      dsimp [R]
      rw [Real.logb_rpow (by norm_num) (by norm_num), neg_neg]
    have hF : MonotoneOn F (Set.Ici 0) := by
      intro s hs t ht hst
      have hr : R t ≤ R s := Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hst)
      have hK := staticPointDimensions_antitone P A x hr
      obtain ⟨i, _, hi⟩ := staticPointDimensions_attained P A x (R t) (hRpos t)
      have hnat := ENat.toNat_le_toNat hK (by rw [hi]; exact ENat.natCast_ne_top _)
      dsimp only [F, precisionComplexityNat]
      exact_mod_cast hnat
    have hnorm (t : ℝ) : F t / ENNReal.ofReal t = normalizedPrecisionComplexity P A x (R t) := by
      rw [normalizedPrecisionComplexity, hden]
    have hstatic : (staticPointDimensions P A x).1 =
        liminf (fun t ↦ F t / ENNReal.ofReal t) atTop := by
      apply le_antisymm
      · have h := hR.liminf_le_liminf_comp (u := normalizedPrecisionComplexity P A x)
        simpa only [staticPointDimensions, Function.comp_def, ← hnorm] using h
      · have h := hprec.liminf_le_liminf_comp (u := fun t ↦ F t / ENNReal.ofReal t)
        have heq : ((fun t ↦ F t / ENNReal.ofReal t) ∘ (fun s : ℝ ↦ -Real.logb 2 s)) =ᶠ[𝓝[>] 0]
            normalizedPrecisionComplexity P A x := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [Function.comp_def, hnorm, hRprec s hs]
        rwa [liminf_congr heq] at h
    refine (hstatic.trans ?_).trans (by rfl)
    rw [nonmonotoneScaleSampling F 0 hF _ ht (ht.eventually (eventually_gt_atTop 0)) hratio]
    congr 1
    funext n
    rw [hnorm, hRprec _ (hpos n)]
  · have hzero : Tendsto r atTop (𝓝 0) := by
      have h := (_root_.tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
        (tendsto_neg_atTop_atBot.comp ht)
      convert h using 1
      funext n
      simp only [neg_neg, Function.comp_def]
      exact (Real.rpow_logb (by norm_num) (by norm_num) (hpos n)).symm
    have hlog : Tendsto (fun n ↦ Real.log (r (n + 1)) / Real.log (r n)) atTop (𝓝 1) := by
      convert hratio using 1
      funext n
      rw [neg_div_neg_eq, Real.logb, Real.logb,
        div_div_div_cancel_right₀ (by positivity : Real.log 2 ≠ 0)]
    exact dimension_along_scales_upper P A x r hpos hzero hlog

/-- Time-limit form of the squeeze: if the Bowen balls of order `n + 1` lie between the metric
balls of radii `rlo n` and `rhi n`, with Birkhoff sums squeezed by `1 ± c` times the logarithmic
precisions, and the static dimension is the sampled limit along both radius sequences, then the
static dimension is squeezed by `1 ± c` times the time limit of the finite-scale BS cost. -/
private lemma choose_staticPointDimensions_squeeze_timeLimit
    (σ : LimitSide) (P : Presentation X) (C : UniformConformalData X) (A : Set ℕ) (x : X)
    (δ c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) (rlo rhi : ℕ → ℝ) (hrlo : ∀ n, 0 < rlo n)
    (htlo : ∀ᶠ n in atTop, 0 < -Real.logb 2 (rlo n))
    (hthi : ∀ᶠ n in atTop, 0 < -Real.logb 2 (rhi n))
    (hslo : σ.choose (staticPointDimensions P A x) =
      σ.timeLimit (fun n ↦ normalizedPrecisionComplexity P A x (rlo n)))
    (hshi : σ.choose (staticPointDimensions P A x) =
      σ.timeLimit (fun n ↦ normalizedPrecisionComplexity P A x (rhi n)))
    (hballs : ∀ n, Metric.ball x (rlo n) ⊆ bowenBall C.T (n + 1) x δ ∧
      bowenBall C.T (n + 1) x δ ⊆ Metric.ball x (rhi n))
    (hden : ∀ᶠ n in atTop, ∀ y ∈ bowenBall C.T (n + 1) x δ,
      (1 - c) * (-Real.logb 2 (rlo n)) ≤ birkhoffSum C.T C.potential (n + 1) y ∧
      birkhoffSum C.T C.potential (n + 1) y ≤ (1 + c) * (-Real.logb 2 (rhi n))) :
    σ.choose (staticPointDimensions P A x) ≤ ENNReal.ofReal (1 + c) *
        σ.timeLimit (fun n ↦ finiteScaleBSCost P C.T C.potential A x n δ) ∧
      ENNReal.ofReal (1 - c) * σ.timeLimit (fun n ↦ finiteScaleBSCost P C.T C.potential A x n δ) ≤
        σ.choose (staticPointDimensions P A x) := by
  have hevent : ∀ᶠ n in atTop,
      normalizedPrecisionComplexity P A x (rhi n) ≤ ENNReal.ofReal (1 + c) *
          finiteScaleBSCost P C.T C.potential A x (n + 1) δ ∧
        ENNReal.ofReal (1 - c) * finiteScaleBSCost P C.T C.potential A x (n + 1) δ ≤
          normalizedPrecisionComplexity P A x (rlo n) := by
    filter_upwards [htlo, hthi, hden] with n hnlo hnhi hnd
    exact ⟨normalizedPrecisionComplexity_le_mul_finiteScaleBSCost P C.T C.potential A x n δ _ c hc
        hnhi (hballs n).2 fun y hy ↦ (hnd y hy).2,
      mul_finiteScaleBSCost_le_normalizedPrecisionComplexity P C.T C.potential A x n δ _ c
        (hrlo n) hnlo hc1 (hballs n).1 fun y hy ↦ (hnd y hy).1⟩
  have hshift := pointwiseDimensionEqBS_order_shift P C A x δ σ
  constructor
  · rw [hshi]
    have h := σ.timeLimit_mono (hevent.mono fun _ hn ↦ hn.1)
    rwa [timeLimit_const_mul σ ENNReal.ofReal_ne_top, hshift] at h
  · rw [hslo]
    have h := σ.timeLimit_mono (hevent.mono fun _ hn ↦ hn.2)
    rwa [timeLimit_const_mul σ ENNReal.ofReal_ne_top, hshift] at h

/-- Uniform continuity of `u` makes the variation `potentialVariation u δ` finite and smaller
than `ε` for all sufficiently small positive radii `δ`. -/
private lemma exists_potentialVariation_toReal_lt (u : X → ℝ) (hu : UniformContinuous u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      potentialVariation u δ < ⊤ ∧ (potentialVariation u δ).toReal < ε := by
  obtain ⟨δ₀, hδ₀, huc⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (by positivity)
  refine ⟨δ₀, hδ₀, fun δ hδ hsmall ↦ ?_⟩
  have hbound : potentialVariation u δ ≤ ENNReal.ofReal (ε / 2) := by
    refine iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun hxy ↦ ?_
    exact ENNReal.ofReal_le_ofReal (huc (hxy.trans_lt hsmall)).le
  refine ⟨hbound.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  linarith

/-- For a point with tempered contraction and every error `0 < c < 1`, there are a time slack
`τ` and a ball constant `η` such that, for all small radii `δ`, the potential variation is
finite, the denominator error `(τ + ω_u(δ)) / (α / 2 - τ)` is below `c`, and the Bowen ball of
order `n + 1` lies between the metric balls of the orbit radii `r_n^-` and `r_n^+`. -/
private lemma exists_orbit_scale_parameters
    (C : UniformConformalData X) (x : X) (hx : HasTemperedContraction C.T C.potential x)
    (α c : ℝ) (hα : 0 < α) (hc : 0 < c) (hc1 : c < 1) :
    ∃ τ η δ₀ : ℝ, 0 < τ ∧ τ < α / 4 ∧ 0 < η ∧ η ≤ 1 ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        potentialVariation C.potential δ < ⊤ ∧
        (τ + (potentialVariation C.potential δ).toReal) / (α / 2 - τ) < c ∧
        ∀ n : ℕ,
          Metric.ball x (conformalOrbitRadius C .lower x η δ τ n) ⊆ bowenBall C.T (n + 1) x δ ∧
          bowenBall C.T (n + 1) x δ ⊆ Metric.ball x (conformalOrbitRadius C .upper x η δ τ n) := by
  let τ : ℝ := c * α / 16
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτα : τ < α / 16 := by
    dsimp [τ]
    nlinarith [mul_lt_mul_of_pos_right hc1 hα]
  obtain ⟨δb, η, hδb, hη, hηone, hball⟩ := ballInclusion C x hx τ hτ
  obtain ⟨δv, hδv, hvar⟩ :=
    exists_potentialVariation_toReal_lt C.potential (distortionModuli C) τ hτ
  refine ⟨τ, η, min δb δv, hτ, by linarith, hη, hηone, lt_min hδb hδv, fun δ hδ hsmall ↦ ?_⟩
  have hv := hvar δ hδ (hsmall.trans_le (min_le_right _ _))
  refine ⟨hv.1, ?_, hball δ hδ (hsmall.trans_le (min_le_left _ _))⟩
  apply (div_lt_iff₀ (by linarith : 0 < α / 2 - τ)).mpr
  have hct := mul_lt_mul_of_pos_left hτα hc
  dsimp [τ] at *
  nlinarith

/-- The time limit of the finite-scale BS cost is monotone in the dyadic scale index. -/
private lemma monotone_timeLimit_finiteScaleBSCost (σ : LimitSide) (P : Presentation X)
    (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) :
    Monotone (fun p ↦ σ.timeLimit (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p))) :=
  fun _ _ hpq ↦ σ.timeLimit_mono (Eventually.of_forall fun n ↦
    pointwiseBSDimension_antitone_radius P T u A x n (dyadicRadius_antitone hpq))

/-- A fixed multiplicative squeeze of `d` by an eventually monotone sequence passes to its
supremum. -/
private lemma squeeze_iSup_of_monotone (f : ℕ → ℝ≥0∞) (hf : Monotone f) (d : ℝ≥0∞) (c : ℝ)
    (hbound : ∀ᶠ p in atTop,
      d ≤ ENNReal.ofReal (1 + c) * f p ∧ ENNReal.ofReal (1 - c) * f p ≤ d) :
    d ≤ ENNReal.ofReal (1 + c) * ⨆ p, f p ∧ ENNReal.ofReal (1 - c) * ⨆ p, f p ≤ d := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp⟩ := hbound.exists
    exact hp.1.trans (mul_le_mul' le_rfl (le_iSup f p))
  · have hlim := ENNReal.Tendsto.const_mul (tendsto_atTop_iSup hf)
      (a := ENNReal.ofReal (1 - c)) (Or.inr ENNReal.ofReal_ne_top)
    exact le_of_tendsto hlim (hbound.mono fun _ hp ↦ hp.2)

/-- If `d` is squeezed between `(1 - c) * b` and `(1 + c) * b` for every `c ∈ (0, 1)`, then
`d = b`; this includes the cases `b = 0` and `b = ∞`. -/
private lemma eq_of_forall_mul_ofReal_squeeze (d b : ℝ≥0∞)
    (h : ∀ c : ℝ, 0 < c → c < 1 →
      d ≤ ENNReal.ofReal (1 + c) * b ∧ ENNReal.ofReal (1 - c) * b ≤ d) :
    d = b := by
  have hid : Tendsto (fun c : ℝ ↦ c) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
  have hplus : Tendsto (fun c : ℝ ↦ ENNReal.ofReal (1 + c)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero, ENNReal.ofReal_one] using
      ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).add hid)
  have hminus : Tendsto (fun c : ℝ ↦ ENNReal.ofReal (1 - c)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [sub_zero, ENNReal.ofReal_one] using
      ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).sub hid)
  have hp := ENNReal.Tendsto.mul_const (b := b) hplus (Or.inl one_ne_zero)
  have hm := ENNReal.Tendsto.mul_const (b := b) hminus (Or.inl one_ne_zero)
  have hevent : ∀ᶠ c : ℝ in 𝓝[>] 0,
      d ≤ ENNReal.ofReal (1 + c) * b ∧ ENNReal.ofReal (1 - c) * b ≤ d := by
    filter_upwards [self_mem_nhdsWithin,
      hid.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with c hc hc1
    exact h c hc hc1
  apply le_antisymm
  · simpa only [one_mul] using
      le_of_tendsto_of_tendsto tendsto_const_nhds hp (hevent.mono fun _ hc ↦ hc.1)
  · simpa only [one_mul] using le_of_tendsto hm (hevent.mono fun _ hc ↦ hc.2)

/-- On the conformal locus, the lower (upper) static point dimension agrees with the lower
(upper) pointwise BS dimension. Blueprint node `conf:pointwise`. -/
private lemma choose_staticPointDimensions_eq_choose_pointwiseBSDimension
    (σ : LimitSide) (P : Presentation X) (C : UniformConformalData X) (A : Set ℕ) (x : X)
    (hx : x ∈ conformalLocus C) :
    σ.choose (staticPointDimensions P A x) =
      σ.choose (pointwiseBSDimension P C.T C.potential A x) := by
  have havg : x ∈ positiveFiniteAverageLocus C.T C.potential := hx.1.1
  have htemp : HasTemperedContraction C.T C.potential x := hx.1.2
  have hgrowth : HasSublinearOrbitGrowth C.T C.potential x := hx.2
  have hfinite : lowerBirkhoffAverage C.T C.potential x ≠ ⊤ :=
    ne_top_of_lt (havg.2.1.trans_lt havg.2.2)
  have hbot : lowerBirkhoffAverage C.T C.potential x ≠ ⊥ := ne_bot_of_gt havg.1
  let α := (lowerBirkhoffAverage C.T C.potential x).toReal
  have hα : lowerBirkhoffAverage C.T C.potential x = (α : EReal) :=
    (EReal.coe_toReal hfinite hbot).symm
  have hαpos : 0 < α := EReal.coe_pos.mp (hα ▸ havg.1)
  have hbs : σ.choose (pointwiseBSDimension P C.T C.potential A x) =
      ⨆ p, σ.timeLimit (fun n ↦ finiteScaleBSCost P C.T C.potential A x n (dyadicRadius p)) := by
    cases σ <;> rfl
  rw [hbs]
  refine eq_of_forall_mul_ofReal_squeeze _ _ fun c hc hc1 ↦ ?_
  obtain ⟨τ, η, δ₀, hτ, hτα, hη, hηone, hδ₀, hspec⟩ :=
    exists_orbit_scale_parameters C x htemp α c hαpos hc hc1
  refine squeeze_iSup_of_monotone _ (monotone_timeLimit_finiteScaleBSCost σ P C.T C.potential A x)
    _ c ?_
  have hd : Tendsto dyadicRadius atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hd.eventually (gt_mem_nhds hδ₀)] with p hp
  have hδ : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  obtain ⟨hvar, herror, hballs⟩ := hspec (dyadicRadius p) hδ hp
  have hrpos (side : LimitSide) (n : ℕ) :
      0 < conformalOrbitRadius C side x η (dyadicRadius p) τ n := by
    cases side <;> dsimp [conformalOrbitRadius, LimitSide.choose] <;> positivity
  have ht (side : LimitSide) := orbitScaleDenominators C x havg hgrowth α τ η (dyadicRadius p)
    hα hτ hτα hη hηone hδ hvar side
  have hpos (side : LimitSide) :
      ∀ᶠ n in atTop, 0 < conformalOrbitPrecision C side x η (dyadicRadius p) τ n :=
    (ht side).eventually (eventually_gt_atTop 0)
  have hsample (side : LimitSide) := choose_staticPointDimensions_eq_timeLimit σ P A x
    (conformalOrbitRadius C side x η (dyadicRadius p) τ) (hrpos side) (ht side)
    (orbitScaleDenominators_ratio C x havg hgrowth α τ η (dyadicRadius p)
      hα hτ hτα hη hηone hδ hvar side)
  refine choose_staticPointDimensions_squeeze_timeLimit σ P C A x (dyadicRadius p) c hc.le hc1
    (conformalOrbitRadius C .lower x η (dyadicRadius p) τ)
    (conformalOrbitRadius C .upper x η (dyadicRadius p) τ) (hrpos .lower) (hpos .lower)
    (hpos .upper) (hsample .lower) (hsample .upper) hballs ?_
  have hd (side : LimitSide) := orbitScaleDenominators_bounds C x havg hgrowth α τ η
    (dyadicRadius p) hα hτ hτα hη hηone hδ hvar (α / 2) c (by linarith) (by linarith) herror side
  filter_upwards [hpos .lower, hpos .upper, hd .lower, hd .upper] with n hnlo hnhi hdlo hdhi y hy
  exact ⟨(le_div_iff₀ hnlo).mp (hdlo y hy).1, (div_le_iff₀ hnhi).mp (hdhi y hy).2⟩

/-- Lower static and BS point dimensions agree for every oracle in the fixed presentation.
No oracle admissibility is required. Blueprint node `conf:pointwise`. -/
theorem pointwiseDimensionEqBS (P : Presentation X) (C : UniformConformalData X)
    (A : Set ℕ) (x : X) (hx : x ∈ conformalLocus C) :
    (staticPointDimensions P A x).1 = (pointwiseBSDimension P C.T C.potential A x).1 :=
  choose_staticPointDimensions_eq_choose_pointwiseBSDimension .lower P C A x hx

/-- Upper static and BS point dimensions agree on the same three-locus intersection.
Blueprint node `conf:pointwise`. -/
theorem pointwiseDimensionEqBS_upper (P : Presentation X) (C : UniformConformalData X)
    (A : Set ℕ) (x : X) (hx : x ∈ conformalLocus C) :
    (staticPointDimensions P A x).2 = (pointwiseBSDimension P C.T C.potential A x).2 :=
  choose_staticPointDimensions_eq_choose_pointwiseBSDimension .upper P C A x hx

end Kolmogorov.PointToSet
