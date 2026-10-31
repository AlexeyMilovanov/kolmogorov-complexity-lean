/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Defs
import KolmogorovMathlib.PointToSet.BSDimension.Lower.Realizers
import KolmogorovMathlib.PointToSet.ComputableMetric
import KolmogorovMathlib.PointToSet.Dynamics
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Distortion moduli and orbit scales of uniformly conformal dynamics

For uniform conformal data `C` (a map `T` with the local distance law
`d(Tx, Ty) = 2 ^ ζ(x, y) * d(x, y)` and diagonal potential `u(x) = ζ(x, x)`) this module proves
the quantitative estimates of the conformal dimension theorem (blueprint nodes `conf:moduli`,
`conf:tempered-constant`, `conf:iterate-distance`, `conf:ball-inclusion`,
`conf:nonmonotone-scales` and `conf:denominators`).

* The potential is uniformly continuous, the ratio distortion `conformalDistortion C δ` is finite
  and tends to zero with the radius, and it controls the variation of the potential
  (`potentialVariation C.potential δ ≤ 2 * conformalDistortion C δ`) and the Birkhoff sums along
  Bowen balls.
* Along orbits with tempered contraction, the finite-orbit estimates `iterateDistance` and
  `iterateDistance_small_initial` compare `d(x, y)` with `d(Tⁿx, Tⁿy)`, and `ballInclusion`
  sandwiches the Bowen ball of order `n + 1` between two metric balls with radii
  `2 ^ (-Sₙu(x) ± nτ)`.
* `nonmonotoneScaleSampling` and `nonmonotoneScaleSampling_upper` show that the lower and upper
  limits of `F(t) / t` for nondecreasing `F` may be computed along any sequence of scales
  `tₙ → ∞` with `tₙ₊₁ / tₙ → 1`; `orbitScaleDenominators` and its companions verify these
  hypotheses for the logarithmic orbit precisions.

The module is used by `KolmogorovMathlib.PointToSet.Conformal.Distortion.PointwiseDimension`
to compare pointwise Barreira–Schmeling dimensions with effective dimensions, and by the
dimension theorem through `distortionModuli`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- The diagonal pair `(x, x)` as an element of the domain of the distance ratio `C.ζ`. -/
private def diagPair (C : UniformConformalData X) (x : X) :
    {p : X × X // dist p.1 p.2 < C.r₀} :=
  ⟨(x, x), by simpa using C.r₀_pos⟩

/-- The pair `(x, y)` is as far from the diagonal pair `(x, x)` as `x` is from `y`. -/
private lemma dist_pair_diagPair (C : UniformConformalData X) (x y : X) (h : dist x y < C.r₀) :
    dist (⟨(x, y), h⟩ : {p : X × X // dist p.1 p.2 < C.r₀}) (diagPair C x) = dist x y := by
  rw [Subtype.dist_eq, diagPair, Prod.dist_eq]
  simp [dist_comm]

/-- If `ζ` moves by less than `ε` on pairs of pairs at distance less than `δ`, then at a pair
`(x, y)` with `d(x, y) < δ` it differs from the potential at `x` by less than `ε`. -/
private lemma abs_zeta_sub_potential_lt (C : UniformConformalData X) {ε δ : ℝ}
    (hδ : ∀ ⦃a b : {p : X × X // dist p.1 p.2 < C.r₀}⦄,
      dist a b < δ → dist (C.ζ a) (C.ζ b) < ε)
    {x y : X} (h : dist x y < C.r₀) (hxy : dist x y < δ) :
    |C.ζ ⟨(x, y), h⟩ - C.potential x| < ε := by
  have := hδ (a := ⟨(x, y), h⟩) (b := diagPair C x) (by rwa [dist_pair_diagPair])
  rw [Real.dist_eq] at this
  exact this

/-- The diagonal potential is uniformly continuous. Blueprint node `conf:moduli`. -/
theorem distortionModuli (C : UniformConformalData X) :
    UniformContinuous C.potential :=
  C.uniformContinuous_ζ.comp
    ((uniformContinuous_id.prodMk uniformContinuous_id).subtype_mk fun x ↦ diagPair C x |>.2)

/-- Every positive error has a uniform one-step distance bound at a smaller radius.
Blueprint node `conf:moduli`. -/
theorem distortionModuli_distance (C : UniformConformalData X) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < C.r₀ ∧ HasConformalDistortionBound C τ δ₀ := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuous_iff.mp C.uniformContinuous_ζ (τ / 2) (by positivity)
  have hr₀ := C.r₀_pos
  have hmin : min δ (C.r₀ / 2) ≤ C.r₀ / 2 := min_le_right _ _
  refine ⟨min δ (C.r₀ / 2), lt_min hδ_pos (by linarith), by linarith, ?_⟩
  intro x y hxy
  have hxy_lt : dist x y < C.r₀ := by linarith
  have hζ := abs_lt.mp
    (abs_zeta_sub_potential_lt C hδ hxy_lt (hxy.trans_le (min_le_left _ _)))
  rw [C.distance_eq x y hxy_lt]
  exact ⟨mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) dist_nonneg,
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) dist_nonneg⟩

/-- The ratio distortion is finite on a whole sufficiently small positive-radius tail.
Blueprint node `conf:moduli`. -/
theorem distortionModuli_finite (C : UniformConformalData X) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < C.r₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → conformalDistortion C δ < ⊤ := by
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    Metric.uniformContinuous_iff.mp C.uniformContinuous_ζ 1 one_pos
  have hr₀ := C.r₀_pos
  refine ⟨min δ₀ (C.r₀ / 2), lt_min hδ₀_pos (by linarith), ?_, ?_⟩
  · linarith [min_le_right δ₀ (C.r₀ / 2)]
  intro δ _ hδ_lt
  refine lt_of_le_of_lt (b := 1) ?_ ENNReal.one_lt_top
  unfold conformalDistortion
  refine iSup_le fun p ↦ iSup_le fun hp ↦ ?_
  have hlt : dist p.val.1 p.val.2 < δ₀ := (hp.2.trans_lt hδ_lt).trans_le (min_le_left _ _)
  exact ENNReal.ofReal_le_one.mpr (abs_zeta_sub_potential_lt C hδ₀ p.property hlt).le

/-- The extended ratio distortion tends to zero along positive radii.
Blueprint node `conf:moduli`. -/
theorem distortionModuli_tendsto (C : UniformConformalData X) :
    Tendsto (conformalDistortion C) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε' hε'
  obtain ⟨ε, hε, hεε'⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ ε' := by
    rcases eq_or_ne ε' ⊤ with rfl | he
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε'.toReal, ENNReal.toReal_pos hε'.ne' he, (ENNReal.ofReal_toReal he).le⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp C.uniformContinuous_ζ ε hε
  filter_upwards [Ico_mem_nhdsGT hδ] with r hr
  refine le_trans ?_ hεε'
  unfold conformalDistortion
  refine iSup_le fun p ↦ iSup_le fun hp ↦ ?_
  have hlt : dist p.val.1 p.val.2 < δ := hp.2.trans_lt hr.2
  exact ENNReal.ofReal_le_ofReal (abs_zeta_sub_potential_lt C hδ' p.property hlt).le

/-- The distance ratio is symmetric: `ζ(x, y) = ζ(y, x)` for distinct nearby points. -/
private lemma zeta_swap (C : UniformConformalData X) {x y : X} (h : dist x y < C.r₀)
    (hxy : 0 < dist x y) :
    C.ζ ⟨(x, y), h⟩ = C.ζ ⟨(y, x), by rwa [dist_comm]⟩ := by
  have h3 : (2 : ℝ) ^ C.ζ ⟨(x, y), h⟩ * dist x y =
      (2 : ℝ) ^ C.ζ ⟨(y, x), by rwa [dist_comm]⟩ * dist x y :=
    calc _ = dist (C.T x) (C.T y) := (C.distance_eq x y h).symm
      _ = dist (C.T y) (C.T x) := dist_comm _ _
      _ = _ := C.distance_eq y x (by rwa [dist_comm])
      _ = _ := congrArg _ (dist_comm y x)
  have h3 := mul_right_cancel₀ hxy.ne' h3
  exact le_antisymm ((Real.rpow_le_rpow_left_iff one_lt_two).mp h3.le)
    ((Real.rpow_le_rpow_left_iff one_lt_two).mp h3.ge)

/-- A pair `(x, y)` at distance at most `δ` contributes to the ratio distortion at radius `δ`. -/
private lemma ofReal_abs_zeta_sub_potential_le (C : UniformConformalData X) {δ : ℝ} {x y : X}
    (h : dist x y < C.r₀) (hpos : 0 < dist x y) (hδ : dist x y ≤ δ) :
    ENNReal.ofReal |C.ζ ⟨(x, y), h⟩ - C.potential x| ≤ conformalDistortion C δ := by
  unfold conformalDistortion
  exact le_iSup₂_of_le (⟨(x, y), h⟩ : {p : X × X // dist p.1 p.2 < C.r₀}) ⟨hpos, hδ⟩ le_rfl

/-- The potential differs at two points at distance at most `δ` by at most twice the ratio
distortion at radius `δ`, because `ζ(x, y) = ζ(y, x)` lies close to both `u(x)` and `u(y)`. -/
private lemma ofReal_abs_potential_sub_le (C : UniformConformalData X) {δ : ℝ} (hδr : δ < C.r₀)
    {x y : X} (h : dist x y ≤ δ) :
    ENNReal.ofReal |C.potential x - C.potential y| ≤ 2 * conformalDistortion C δ := by
  rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with h0 | hpos
  · rw [dist_eq_zero.mp h0.symm, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hxy : dist x y < C.r₀ := h.trans_lt hδr
  have hyx : dist y x < C.r₀ := by rwa [dist_comm]
  have h1 := ofReal_abs_zeta_sub_potential_le C hxy hpos h
  have h2 := ofReal_abs_zeta_sub_potential_le C (δ := δ) hyx (by rwa [dist_comm])
    ((dist_comm y x).le.trans h)
  rw [← zeta_swap C hxy hpos] at h2
  have key : ∀ a b c : ℝ, |a - c| ≤ |b - a| + |b - c| := fun a b c ↦ by
    rw [abs_sub_comm b a]
    exact abs_sub_le a b c
  calc ENNReal.ofReal |C.potential x - C.potential y|
      ≤ ENNReal.ofReal (|C.ζ ⟨(x, y), hxy⟩ - C.potential x| +
          |C.ζ ⟨(x, y), hxy⟩ - C.potential y|) := ENNReal.ofReal_le_ofReal (key _ _ _)
    _ ≤ _ := ENNReal.ofReal_add_le
    _ ≤ conformalDistortion C δ + conformalDistortion C δ := add_le_add h1 h2
    _ = 2 * conformalDistortion C δ := (two_mul _).symm

/-- Potential variation is bounded by twice the ratio-to-diagonal distortion.
Blueprint node `conf:moduli`. -/
theorem distortionModuli_potential (C : UniformConformalData X) (δ : ℝ)
    (hδ : 0 < δ) (hδr : δ < C.r₀) :
    potentialVariation C.potential δ ≤ 2 * conformalDistortion C δ := by
  have _ := hδ
  unfold potentialVariation
  exact iSup_le fun x ↦ iSup_le fun y ↦ iSup_le fun h ↦ ofReal_abs_potential_sub_le C hδr h

/-- Birkhoff sums at two points of a Bowen ball of order `n` differ by at most `n` times the
potential variation at the radius of the ball. -/
private lemma ofReal_abs_birkhoffSum_sub_le (C : UniformConformalData X) (δ : ℝ) (n : ℕ)
    (x y : X) (hy : y ∈ bowenBall C.T n x δ) :
    ENNReal.ofReal |birkhoffSum C.T C.potential n y - birkhoffSum C.T C.potential n x| ≤
      n * potentialVariation C.potential δ := by
  rw [birkhoffSum, birkhoffSum, ← Finset.sum_sub_distrib]
  calc ENNReal.ofReal |∑ i ∈ Finset.range n, (C.potential (C.T^[i] y) - C.potential (C.T^[i] x))|
      ≤ ENNReal.ofReal
          (∑ i ∈ Finset.range n, |C.potential (C.T^[i] y) - C.potential (C.T^[i] x)|) :=
        ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i ∈ Finset.range n,
          ENNReal.ofReal |C.potential (C.T^[i] y) - C.potential (C.T^[i] x)| :=
        ENNReal.ofReal_sum_of_nonneg fun i _ ↦ abs_nonneg _
    _ ≤ ∑ _i ∈ Finset.range n, potentialVariation C.potential δ := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have h_dist : dist (C.T^[i] y) (C.T^[i] x) ≤ δ := by
          rw [dist_comm]
          exact (mem_bowenBall_iff.1 hy i (Finset.mem_range.1 hi)).le
        unfold potentialVariation
        exact le_iSup₂_of_le (C.T^[i] y) (C.T^[i] x) (le_iSup_of_le h_dist le_rfl)
    _ = n * potentialVariation C.potential δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The corrected accumulated Birkhoff error has the factor two, in the extended domain.
Blueprint node `conf:moduli`. -/
theorem distortionModuli_birkhoff (C : UniformConformalData X) (δ : ℝ)
    (hδ : 0 < δ) (hδr : δ < C.r₀) (n : ℕ) (x y : X)
    (hy : y ∈ bowenBall C.T n x δ) :
    ENNReal.ofReal |birkhoffSum C.T C.potential n y - birkhoffSum C.T C.potential n x| ≤
      2 * n * conformalDistortion C δ := by
  calc ENNReal.ofReal |birkhoffSum C.T C.potential n y - birkhoffSum C.T C.potential n x|
      ≤ (n : ℝ≥0∞) * potentialVariation C.potential δ :=
        ofReal_abs_birkhoffSum_sub_le C δ n x y hy
    _ ≤ (n : ℝ≥0∞) * (2 * conformalDistortion C δ) :=
        by gcongr; exact distortionModuli_potential C δ hδ hδr
    _ = 2 * (n : ℝ≥0∞) * conformalDistortion C δ := by
        rw [← mul_assoc, mul_comm (n : ℝ≥0∞) 2]

/-- A single positive tempered constant gives both the logarithmic bound and the radius bound.
The constant is chosen before both time indices. Blueprint node `conf:tempered-constant`. -/
theorem temperedConstant (C : UniformConformalData X) (x : X)
    (hx : HasTemperedContraction C.T C.potential x) (τ : ℝ) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ n k : ℕ, k ≤ n →
      Real.logb 2 η ≤
        birkhoffSum C.T C.potential n x - birkhoffSum C.T C.potential k x + n * τ / 2 ∧
      η * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x - n * τ) ≤
        (2 : ℝ) ^ (-birkhoffSum C.T C.potential k x - k * τ / 2) := by
  obtain ⟨c, hc⟩ := hx (τ / 2) (by positivity)
  refine ⟨(2 : ℝ) ^ min c 0, by positivity,
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (min_le_right c 0), fun n k hkn ↦ ?_⟩
  have hck := hc n k hkn
  have hmin := min_le_left c 0
  refine ⟨?_, ?_⟩
  · rw [Real.logb_rpow two_pos (by norm_num)]
    linarith
  · rw [← Real.rpow_add two_pos]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    nlinarith [mul_nonneg (sub_nonneg.2 hkn') hτ.le]

/-- Multiplying the local lower bounds controls the initial distance by the final one.
Blueprint node `conf:iterate-distance`. -/
theorem iterateDistance (C : UniformConformalData X) (τ δ₀ δ : ℝ)
    (hτ : 0 < τ) (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ < C.r₀)
    (hbound : HasConformalDistortionBound C τ δ₀) (hδ : 0 < δ) (hδδ₀ : δ < δ₀)
    (x y : X) (n : ℕ) (hclose : ∀ k ≤ n, dist (C.T^[k] x) (C.T^[k] y) < δ) :
    dist x y ≤ dist (C.T^[n] x) (C.T^[n] y) *
      (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ / 2) := by
  have _ : _ ∧ _ ∧ _ ∧ _ := ⟨hτ, hδ₀, hδ₀r, hδ⟩
  induction n with
  | zero => simp [birkhoffSum]
  | succ n ih =>
    have ih' := ih fun k hk ↦ hclose k (Nat.le_succ_of_le hk)
    have hn : dist (C.T^[n] x) (C.T^[n] y) < δ₀ := (hclose n n.le_succ).trans hδδ₀
    have hstep := (hbound _ _ hn).1
    have hprod : (2 : ℝ) ^ (C.potential (C.T^[n] x) - τ / 2) *
        (2 : ℝ) ^ (-C.potential (C.T^[n] x) + τ / 2) = 1 := by
      rw [← Real.rpow_add two_pos]
      simp
    have h2 : dist (C.T^[n] x) (C.T^[n] y) ≤
        dist (C.T (C.T^[n] x)) (C.T (C.T^[n] y)) * (2 : ℝ) ^ (-C.potential (C.T^[n] x) + τ / 2) :=
      calc dist (C.T^[n] x) (C.T^[n] y)
          = (2 : ℝ) ^ (C.potential (C.T^[n] x) - τ / 2) * dist (C.T^[n] x) (C.T^[n] y) *
            (2 : ℝ) ^ (-C.potential (C.T^[n] x) + τ / 2) := by
            linear_combination (-dist (C.T^[n] x) (C.T^[n] y)) * hprod
        _ ≤ _ := mul_le_mul_of_nonneg_right hstep (by positivity)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', birkhoffSum_succ_apply]
    calc dist x y ≤ dist (C.T^[n] x) (C.T^[n] y) *
          (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ / 2) := ih'
      _ ≤ dist (C.T (C.T^[n] x)) (C.T (C.T^[n] y)) *
          (2 : ℝ) ^ (-C.potential (C.T^[n] x) + τ / 2) *
          (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ / 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add two_pos]
        congr 2
        push_cast
        ring

/-- If the first `n` orbit distances stay below the radius where the local bounds hold, the
distance after `n` steps is at most the initial distance times the accumulated upper
distortion factor. -/
private lemma dist_iterate_le_of_forall_lt (C : UniformConformalData X) (τ δ₀ δ : ℝ)
    (hbound : HasConformalDistortionBound C τ δ₀) (hδδ₀ : δ < δ₀)
    (x y : X) (n : ℕ) (hclose : ∀ k < n, dist (C.T^[k] x) (C.T^[k] y) < δ) :
    dist (C.T^[n] x) (C.T^[n] y) ≤ dist x y *
      (2 : ℝ) ^ (birkhoffSum C.T C.potential n x + (n : ℝ) * τ / 2) := by
  induction n with
  | zero => simp [birkhoffSum]
  | succ n ih =>
    have ih' := ih fun k hk ↦ hclose k (hk.trans n.lt_succ_self)
    have hn : dist (C.T^[n] x) (C.T^[n] y) < δ₀ := (hclose n n.lt_succ_self).trans hδδ₀
    have hstep := (hbound _ _ hn).2
    calc dist (C.T^[n + 1] x) (C.T^[n + 1] y)
        = dist (C.T (C.T^[n] x)) (C.T (C.T^[n] y)) := by
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      _ ≤ (2 : ℝ) ^ (C.potential (C.T^[n] x) + τ / 2) * dist (C.T^[n] x) (C.T^[n] y) := hstep
      _ ≤ (2 : ℝ) ^ (C.potential (C.T^[n] x) + τ / 2) *
          (dist x y * (2 : ℝ) ^ (birkhoffSum C.T C.potential n x + (n : ℝ) * τ / 2)) :=
        mul_le_mul_of_nonneg_left ih' (by positivity)
      _ = dist x y * (2 : ℝ) ^ (birkhoffSum C.T C.potential n x + (n : ℝ) * τ / 2 +
          (C.potential (C.T^[n] x) + τ / 2)) := by
        rw [Real.rpow_add two_pos (birkhoffSum C.T C.potential n x + (n : ℝ) * τ / 2)
          (C.potential (C.T^[n] x) + τ / 2)]
        ring
      _ = _ := by
        congr 2
        rw [birkhoffSum_succ_apply]
        push_cast
        ring

/-- A finite infimum of the required initial radii ensures all intermediate orbit bounds.
Blueprint node `conf:iterate-distance`. -/
theorem iterateDistance_small_initial (C : UniformConformalData X) (τ δ₀ δ : ℝ)
    (hτ : 0 < τ) (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ < C.r₀)
    (hbound : HasConformalDistortionBound C τ δ₀) (hδ : 0 < δ) (hδδ₀ : δ < δ₀)
    (x y : X) (n : ℕ)
    (hsmall : dist x y < δ * ⨅ k : Fin (n + 1),
      (2 : ℝ) ^ (-birkhoffSum C.T C.potential k.val x - k.val * τ / 2)) :
    ∀ k ≤ n, dist (C.T^[k] x) (C.T^[k] y) < δ := by
  have _ : _ ∧ _ ∧ _ := ⟨hτ, hδ₀, hδ₀r⟩
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hinf : (⨅ m : Fin (n + 1),
          (2 : ℝ) ^ (-birkhoffSum C.T C.potential m.val x - (m.val : ℝ) * τ / 2)) ≤
        (2 : ℝ) ^ (-birkhoffSum C.T C.potential k x - (k : ℝ) * τ / 2) :=
      ciInf_le (Set.finite_range _).bddBelow (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1))
    have hupper := dist_iterate_le_of_forall_lt C τ δ₀ δ hbound hδδ₀ x y k
      fun j hj ↦ ih j hj (hj.le.trans hk)
    have hxy : dist x y <
        δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential k x - (k : ℝ) * τ / 2) :=
      hsmall.trans_le (mul_le_mul_of_nonneg_left hinf hδ.le)
    have h0 : -birkhoffSum C.T C.potential k x - (k : ℝ) * τ / 2 +
        (birkhoffSum C.T C.potential k x + (k : ℝ) * τ / 2) = 0 := by ring
    calc dist (C.T^[k] x) (C.T^[k] y)
        ≤ dist x y * (2 : ℝ) ^ (birkhoffSum C.T C.potential k x + (k : ℝ) * τ / 2) := hupper
      _ < δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential k x - (k : ℝ) * τ / 2) *
          (2 : ℝ) ^ (birkhoffSum C.T C.potential k x + (k : ℝ) * τ / 2) :=
        mul_lt_mul_of_pos_right hxy (by positivity)
      _ = δ := by rw [mul_assoc, ← Real.rpow_add two_pos, h0, Real.rpow_zero, mul_one]

/-- The inner and outer metric balls compare with order `n + 1`, including `n = 0`.
The same two constants work for every sufficiently small radius and every order.
Blueprint node `conf:ball-inclusion`. -/
theorem ballInclusion (C : UniformConformalData X) (x : X)
    (hx : HasTemperedContraction C.T C.potential x) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ₀ η : ℝ, 0 < δ₀ ∧ 0 < η ∧ η ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ n : ℕ,
        Metric.ball x (conformalOrbitRadius C .lower x η δ τ n) ⊆
          bowenBall C.T (n + 1) x δ ∧
        bowenBall C.T (n + 1) x δ ⊆
          Metric.ball x (conformalOrbitRadius C .upper x η δ τ n) := by
  obtain ⟨η, hη, hη₁, hηtemp⟩ := temperedConstant C x hx τ hτ
  obtain ⟨δ₀, hδ₀, hδ₀r, hbound⟩ := distortionModuli_distance C τ hτ
  refine ⟨δ₀, η, hδ₀, hη, hη₁, fun δ hδ hδδ₀ n ↦ ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩⟩
  · rw [Metric.mem_ball] at hy
    dsimp only [conformalOrbitRadius, LimitSide.choose] at hy
    have hinf : η * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x - n * τ) ≤ ⨅ k : Fin (n + 1),
        (2 : ℝ) ^ (-birkhoffSum C.T C.potential k.val x - k.val * τ / 2) :=
      le_ciInf fun k ↦ (hηtemp n k.val (Nat.lt_succ_iff.mp k.isLt)).2
    have hsmall : dist x y < δ * ⨅ k : Fin (n + 1),
        (2 : ℝ) ^ (-birkhoffSum C.T C.potential k.val x - k.val * τ / 2) :=
      calc dist x y = dist y x := dist_comm x y
        _ < η * δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x - n * τ) := hy
        _ = δ * (η * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x - n * τ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinf hδ.le
    exact mem_bowenBall_iff.2 fun k hk ↦
      iterateDistance_small_initial C τ δ₀ δ hτ hδ₀ hδ₀r hbound hδ hδδ₀ x y n hsmall k
        (Nat.lt_succ_iff.mp hk)
  · have hclose : ∀ k ≤ n, dist (C.T^[k] x) (C.T^[k] y) < δ := fun k hk ↦
      mem_bowenBall_iff.1 hy k (Nat.lt_succ_of_le hk)
    have hd := iterateDistance C τ δ₀ δ hτ hδ₀ hδ₀r hbound hδ hδδ₀ x y n hclose
    have hnτ : 0 ≤ (n : ℝ) * τ := by positivity
    rw [Metric.mem_ball]
    calc dist y x = dist x y := dist_comm y x
      _ ≤ dist (C.T^[n] x) (C.T^[n] y) *
          (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ / 2) := hd
      _ < δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ / 2) :=
        mul_lt_mul_of_pos_right (hclose n le_rfl) (by positivity)
      _ ≤ δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x + n * τ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) hδ.le

/-- For a sequence of scales `t n → ∞`, the first index with `r ≤ t n` brackets `r`: its
predecessor `p r` satisfies `t (p r) < r ≤ t (p r + 1)` for large `r`, and `p r → ∞`. -/
private lemma exists_index_bracketing (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ p : ℝ → ℕ, Tendsto p atTop atTop ∧
      ∀ᶠ r in atTop, t (p r) < r ∧ r ≤ t (p r + 1) := by
  have H (r : ℝ) : ∃ n, r ≤ t n := (tendsto_atTop.1 ht r).exists
  let n (r : ℝ) := Nat.find (H r)
  have hn_spec (r : ℝ) : r ≤ t (n r) := Nat.find_spec (H r)
  have hn_min (r : ℝ) (m : ℕ) (hm : m < n r) : t m < r := not_le.mp (Nat.find_min (H r) hm)
  refine ⟨fun r ↦ n r - 1, ?_, ?_⟩
  · refine tendsto_atTop_atTop.mpr fun m ↦ ?_
    obtain ⟨M, hM⟩ : ∃ M, ∀ k ≤ m + 1, t k ≤ M :=
      ⟨(Finset.range (m + 2)).sup' (by simp) t, fun k hk ↦
        Finset.le_sup' t (Finset.mem_range.2 (by omega))⟩
    refine ⟨M + 1, fun r hr ↦ ?_⟩
    have : m + 1 < n r := by
      by_contra hc
      linarith [hM (n r) (not_lt.1 hc), hn_spec r]
    omega
  · filter_upwards [eventually_gt_atTop (t 0)] with r hr
    have hpos : 0 < n r := by
      by_contra hc
      have h0 : n r = 0 := by omega
      have := hn_spec r
      rw [h0] at this
      linarith
    have h1 : n r - 1 + 1 = n r := by omega
    exact ⟨hn_min r _ (by omega), by rw [h1]; exact hn_spec r⟩

/-- Along a bracketing index function, the lower scale divided by the argument tends to one. -/
private lemma tendsto_div_of_bracketing
    (t : ℕ → ℝ) (hpos : ∀ᶠ n in atTop, 0 < t n)
    (hratio : Tendsto (fun n ↦ t (n + 1) / t n) atTop (𝓝 1))
    (p : ℝ → ℕ) (hp : Tendsto p atTop atTop)
    (hb : ∀ᶠ r in atTop, t (p r) < r ∧ r ≤ t (p r + 1)) :
    Tendsto (fun r ↦ t (p r) / r) atTop (𝓝 1) := by
  have H3 : Tendsto (fun r ↦ t (p r) / t (p r + 1)) atTop (𝓝 1) := by
    have := (hratio.comp hp).inv₀ one_ne_zero
    simpa only [Function.comp_apply, inv_div, inv_one] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' H3 tendsto_const_nhds ?_ ?_
  · filter_upwards [hp.eventually hpos, hb] with r hr ⟨h_lt, h_le⟩
    rw [div_le_div_iff₀ (hr.trans (h_lt.trans_le h_le)) (hr.trans h_lt)]
    exact mul_le_mul_of_nonneg_left h_le hr.le
  · filter_upwards [hb, hp.eventually hpos] with r ⟨h_lt, _⟩ hr
    exact (div_le_one₀ (hr.trans h_lt)).2 h_lt.le

/-- For nondecreasing `F`, the normalized value `F r / r` dominates the normalized value at an
earlier scale `a`, discounted by the factor `a / r`. -/
private lemma ofReal_div_mul_div_le (F : ℝ → ℝ≥0∞) (t₀ : ℝ)
    (hF : MonotoneOn F (Set.Ici t₀)) (a r : ℝ) (ha : 0 < a) (hbase : t₀ ≤ a) (har : a ≤ r) :
    ENNReal.ofReal (a / r) * (F a / ENNReal.ofReal a) ≤ F r / ENNReal.ofReal r := by
  rw [ENNReal.ofReal_div_of_pos (ha.trans_le har), mul_comm,
    ENNReal.div_mul_div_cancel (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top]
  exact ENNReal.div_le_div_right (hF hbase (hbase.trans har) har) _

/-- A nondecreasing extended function has the same lower normalized limit along
any asymptotically dense precision sequence, without monotonicity of that sequence.
Values below the initial threshold are irrelevant. Blueprint node `conf:nonmonotone-scales`. -/
theorem nonmonotoneScaleSampling (F : ℝ → ℝ≥0∞) (t₀ : ℝ)
    (hF : MonotoneOn F (Set.Ici t₀)) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hpos : ∀ᶠ n in atTop, 0 < t n)
    (hratio : Tendsto (fun n => t (n + 1) / t n) atTop (𝓝 1)) :
    liminf (fun r => F r / ENNReal.ofReal r) atTop =
      liminf (fun n => F (t n) / ENNReal.ofReal (t n)) atTop := by
  refine le_antisymm (ht.liminf_le_liminf_comp (u := fun r ↦ F r / ENNReal.ofReal r)) ?_
  obtain ⟨p, hp, hb⟩ := exists_index_bracketing t ht
  have hlower := tendsto_div_of_bracketing t hpos hratio p hp hb
  let G : ℝ → ℝ≥0∞ := fun r ↦ F r / ENNReal.ofReal r
  let B : ℝ → ℝ≥0∞ := fun r ↦ G (t (p r))
  let A : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal (t (p r) / r)
  have hA : Tendsto A atTop (𝓝 1) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hlower
  have hbound : ∀ᶠ r in atTop, A r * B r ≤ G r := by
    filter_upwards [hb, hp.eventually hpos, (ht.comp hp).eventually (eventually_ge_atTop t₀)]
      with r ⟨h_lt, _⟩ h_pos h_base
    exact ofReal_div_mul_div_le F t₀ hF (t (p r)) r h_pos h_base h_lt.le
  calc liminf (fun n ↦ F (t n) / ENNReal.ofReal (t n)) atTop ≤ liminf B atTop :=
        hp.liminf_le_liminf_comp (u := fun n ↦ G (t n))
    _ = 1 * liminf B atTop := (one_mul _).symm
    _ ≤ liminf (fun r ↦ A r * B r) atTop := by
        rw [← hA.liminf_eq]
        exact ENNReal.le_liminf_mul
    _ ≤ liminf G atTop := liminf_le_liminf hbound

/-- The same nonmonotone precision sampling preserves the upper normalized limit.
Blueprint node `conf:nonmonotone-scales`. -/
theorem nonmonotoneScaleSampling_upper (F : ℝ → ℝ≥0∞) (t₀ : ℝ)
    (hF : MonotoneOn F (Set.Ici t₀)) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hpos : ∀ᶠ n in atTop, 0 < t n)
    (hratio : Tendsto (fun n => t (n + 1) / t n) atTop (𝓝 1)) :
    limsup (fun r => F r / ENNReal.ofReal r) atTop =
      limsup (fun n => F (t n) / ENNReal.ofReal (t n)) atTop := by
  refine le_antisymm ?_ (ht.limsup_comp_le_limsup (u := fun r ↦ F r / ENNReal.ofReal r))
  obtain ⟨p, hp, hb⟩ := exists_index_bracketing t ht
  have hlower := tendsto_div_of_bracketing t hpos hratio p hp hb
  have hupper : Tendsto (fun r ↦ t (p r + 1) / r) atTop (𝓝 1) := by
    have h := (hratio.comp hp).mul hlower
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hp.eventually hpos] with r hr
    exact div_mul_div_cancel₀ hr.ne'
  let G : ℝ → ℝ≥0∞ := fun r ↦ F r / ENNReal.ofReal r
  let B : ℝ → ℝ≥0∞ := fun r ↦ G (t (p r + 1))
  let A : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal (t (p r + 1) / r)
  have hA : Tendsto A atTop (𝓝 1) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hupper
  have hlimA : limsup A atTop = 1 := hA.limsup_eq
  have hbound : ∀ᶠ r in atTop, G r ≤ B r * A r := by
    filter_upwards [hb, eventually_gt_atTop (max t₀ 0)] with r hbr hr
    have hrpos : 0 < r := (le_max_right t₀ 0).trans_lt hr
    have htpos : 0 < t (p r + 1) := hrpos.trans_le hbr.2
    have hrbase : t₀ ≤ r := (le_max_left t₀ 0).trans hr.le
    dsimp only [G, B, A]
    rw [ENNReal.ofReal_div_of_pos hrpos,
      ENNReal.div_mul_div_cancel (by positivity) ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right (hF hrbase (hrbase.trans hbr.2) hbr.2) _
  calc limsup G atTop ≤ limsup (fun r ↦ B r * A r) atTop := limsup_le_limsup hbound
    _ ≤ limsup B atTop * limsup A atTop :=
      ENNReal.limsup_mul_le' (Or.inr (by rw [hlimA]; simp)) (Or.inr (by rw [hlimA]; simp))
    _ = limsup B atTop := by rw [hlimA, mul_one]
    _ ≤ limsup (fun n ↦ G (t n)) atTop :=
      ((tendsto_add_atTop_nat 1).comp hp).limsup_comp_le_limsup (u := fun n ↦ G (t n))

omit [MetricSpace X] in
/-- If the lower Birkhoff average of `u` at `x` equals `α`, then `S_n u(x) ≥ a * n` for all large
`n`, for every `a < α`. -/
lemma eventually_mul_le_birkhoffSum {T : X → X} {u : X → ℝ} {x : X} {α a : ℝ}
    (hα : lowerBirkhoffAverage T u x = (α : EReal)) (ha : a < α) :
    ∀ᶠ n : ℕ in atTop, a * n ≤ birkhoffSum T u n x := by
  have H : ((a : ℝ) : EReal) < lowerBirkhoffAverage T u x := by
    rw [hα]
    exact EReal.coe_lt_coe_iff.mpr ha
  filter_upwards [eventually_lt_of_lt_liminf H, eventually_gt_atTop 0] with n hn hn_pos
  exact ((lt_div_iff₀ (Nat.cast_pos.mpr hn_pos)).mp (EReal.coe_lt_coe_iff.mp hn)).le

/-- The logarithmic orbit precision is `S_n u(x) + n * s - k`, where `s = ±τ` and `k` is the
logarithm of the constant factor of the radius (`η δ` for the inner radius, `δ` for the
outer one). -/
private lemma conformalOrbitPrecision_eq (C : UniformConformalData X) (σ : LimitSide) (x : X)
    {η δ τ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (n : ℕ) :
    conformalOrbitPrecision C σ x η δ τ n = birkhoffSum C.T C.potential n x +
      n * σ.choose (τ, -τ) - σ.choose (Real.logb 2 (η * δ), Real.logb 2 δ) := by
  cases σ <;> dsimp only [conformalOrbitPrecision, conformalOrbitRadius, LimitSide.choose]
  · rw [Real.logb_mul (mul_pos hη hδ).ne' (Real.rpow_pos_of_pos two_pos _).ne',
      Real.logb_rpow two_pos (by norm_num)]
    ring
  · rw [Real.logb_mul hδ.ne' (Real.rpow_pos_of_pos two_pos _).ne',
      Real.logb_rpow two_pos (by norm_num)]
    ring

/-- Points of a Bowen ball of positive radius `δ` have Bowen distance less than `δ` from the
center. -/
private lemma bowenDist_lt_of_mem_bowenBall {T : X → X} {n : ℕ} {x y : X} {δ : ℝ} (hδ : 0 < δ)
    (hy : y ∈ bowenBall T n x δ) : bowenDist T n x y < δ := by
  have hδ' : (δ.toNNReal : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  rw [← hδ', bowenDist, NNReal.coe_lt_coe, Finset.sup_lt_iff (Real.toNNReal_pos.2 hδ)]
  intro k hk
  rw [← NNReal.coe_lt_coe, hδ']
  exact mem_bowenBall_iff.1 hy k (Finset.mem_range.1 hk)

section OrbitScales

variable (C : UniformConformalData X) (x : X)
  (hx : x ∈ positiveFiniteAverageLocus C.T C.potential)
  (hgrowth : HasSublinearOrbitGrowth C.T C.potential x)
  (α τ η δ : ℝ) (hα : lowerBirkhoffAverage C.T C.potential x = (α : EReal))
  (hτ : 0 < τ) (hτα : τ < α / 4) (hη : 0 < η) (hηone : η ≤ 1) (hδ : 0 < δ)
  (hvar : potentialVariation C.potential δ < ⊤)

include hx hgrowth hα hτ hτα hη hηone hδ hvar

/-- Both logarithmic orbit precisions tend to infinity, without tempered contraction.
Blueprint node `conf:denominators`. -/
theorem orbitScaleDenominators (σ : LimitSide) :
    Tendsto (conformalOrbitPrecision C σ x η δ τ) atTop atTop := by
  have _ : _ ∧ _ ∧ _ ∧ _ := ⟨hx, hgrowth, hηone, hvar⟩
  have hsum := eventually_mul_le_birkhoffSum hα (a := 2 * τ) (by linarith)
  have hs : -τ ≤ σ.choose (τ, -τ) := by
    cases σ <;> dsimp only [LimitSide.choose] <;> linarith
  have hlow : Tendsto (fun n : ℕ ↦ τ * n + -σ.choose (Real.logb 2 (η * δ), Real.logb 2 δ))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop hτ)
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [hsum] with n hn
  rw [conformalOrbitPrecision_eq C σ x hη hδ n]
  nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- Adjacent logarithmic orbit precisions have ratio tending to one.
Blueprint node `conf:denominators`. -/
theorem orbitScaleDenominators_ratio (σ : LimitSide) :
    Tendsto (fun n => conformalOrbitPrecision C σ x η δ τ (n + 1) /
      conformalOrbitPrecision C σ x η δ τ n) atTop (𝓝 1) := by
  have _ : _ ∧ _ ∧ _ := ⟨hx, hηone, hvar⟩
  let t := conformalOrbitPrecision C σ x η δ τ
  let s : ℝ := σ.choose (τ, -τ)
  let k : ℝ := σ.choose (Real.logb 2 (η * δ), Real.logb 2 δ)
  have hval (n : ℕ) : t n = birkhoffSum C.T C.potential n x + n * s - k :=
    conformalOrbitPrecision_eq C σ x hη hδ n
  have hdiff (n : ℕ) : t (n + 1) - t n = C.potential (C.T^[n] x) + s := by
    rw [hval, hval, birkhoffSum_succ_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hinc : Tendsto (fun n : ℕ ↦ (t (n + 1) - t n) / n) atTop (𝓝 0) := by
    simp_rw [hdiff, add_div]
    simpa only [add_zero] using hgrowth.add
      ((tendsto_const_nhds (x := s)).div_atTop tendsto_natCast_atTop_atTop)
  have hsum : ∀ᶠ n : ℕ in atTop, (2 * τ) * (n : ℝ) ≤ birkhoffSum C.T C.potential n x :=
    eventually_mul_le_birkhoffSum hα (by linarith)
  have hs : -τ ≤ s := by
    cases σ <;> dsimp only [s, LimitSide.choose] <;> linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, k / (τ / 2) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hbound : ∀ᶠ n : ℕ in atTop, (τ / 2) * (n : ℝ) ≤ t n := by
    filter_upwards [hsum, hlarge] with n hn hlarge
    have hk : k ≤ (n : ℝ) * (τ / 2) := (div_le_iff₀ (half_pos hτ)).mp hlarge
    have hslack := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [hval]
    nlinarith
  have hnO : Asymptotics.IsBigO atTop (fun n : ℕ ↦ (n : ℝ)) t := by
    apply Asymptotics.IsBigO.of_bound (1 / (τ / 2))
    filter_upwards [hbound] with n hn
    have ht : 0 ≤ t n := (mul_nonneg (half_pos hτ).le (Nat.cast_nonneg n)).trans hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg n), Real.norm_of_nonneg ht]
    calc (n : ℝ) ≤ t n / (τ / 2) := (le_div_iff₀ (half_pos hτ)).mpr (by nlinarith)
      _ = 1 / (τ / 2) * t n := by ring
  have hsmall : Asymptotics.IsLittleO atTop (fun n ↦ t (n + 1) - t n) (fun n : ℕ ↦ (n : ℝ)) := by
    apply Asymptotics.isLittleO_of_tendsto' _ hinc
    filter_upwards [eventually_gt_atTop 0] with n hn hzero
    exact ((Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne' hzero).elim
  have hquot := (hsmall.trans_isBigO hnO).tendsto_div_nhds_zero
  have hfinal : Tendsto (fun n ↦ 1 + (t (n + 1) - t n) / t n) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hquot
  refine hfinal.congr' ?_
  filter_upwards [hbound, eventually_gt_atTop 0] with n hn hnpos
  have ht : 0 < t n := (mul_pos (half_pos hτ) (Nat.cast_pos.mpr hnpos)).trans_le hn
  change 1 + (t (n + 1) - t n) / t n = t (n + 1) / t n
  field_simp [ht.ne']
  ring

/-- Uniformly on the correctly indexed ball, the denominator differs by potential
variation and the last term at the reference point. Blueprint node `conf:denominators`. -/
theorem orbitScaleDenominators_variation (n : ℕ) (y : X)
    (hy : y ∈ bowenBall C.T (n + 1) x δ) :
    |birkhoffSum C.T C.potential (n + 1) y - birkhoffSum C.T C.potential n x| ≤
      (n + 1 : ℕ) * (potentialVariation C.potential δ).toReal +
        |C.potential (C.T^[n] x)| := by
  have _ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := ⟨hx, hgrowth, hα, hτ, hτα, hη, hηone⟩
  have hdist : bowenDist C.T (n + 1) x y < δ := bowenDist_lt_of_mem_bowenBall hδ hy
  have h1 := supWeightBounds_birkhoff C.T C.potential (n + 1) x y δ hvar hdist
  have hS := birkhoffSum_succ_apply C.T C.potential n x
  calc |birkhoffSum C.T C.potential (n + 1) y - birkhoffSum C.T C.potential n x|
      = |(birkhoffSum C.T C.potential (n + 1) y - birkhoffSum C.T C.potential (n + 1) x) +
          C.potential (C.T^[n] x)| := by
        congr 1
        linarith
    _ ≤ |birkhoffSum C.T C.potential (n + 1) y - birkhoffSum C.T C.potential (n + 1) x| +
          |C.potential (C.T^[n] x)| := abs_add_le _ _
    _ = |birkhoffSum C.T C.potential (n + 1) x - birkhoffSum C.T C.potential (n + 1) y| +
          |C.potential (C.T^[n] x)| := by rw [abs_sub_comm]
    _ ≤ _ := add_le_add h1 le_rfl

end OrbitScales

end Kolmogorov.PointToSet
