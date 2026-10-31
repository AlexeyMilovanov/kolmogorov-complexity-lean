/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Conformal.Distortion

/-!
# Counterexamples to uncorrected ball comparisons

A doubling map shows that an order-`n` Bowen ball uses only `n - 1` iterates, so its
radius need not satisfy the unshifted outer estimate. A discrete conformal system with
a square-root coboundary has tempered contraction but unbounded negative suffix sums
at zero slack. These witnesses justify the indexing and positive slack in the corrected
ball comparison (`conf:ball-counterexamples`) and are re-exported by `Conformal.TheoremE`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

private lemma conformalDistortion_eq_zero_of_doubling (C : UniformConformalData ℝ)
    (hT : ∀ x, C.T x = 2 * x) (hPot : ∀ x, C.potential x = 1) (δ : ℝ) :
    conformalDistortion C δ = 0 := by
  apply le_antisymm _ zero_le
  refine iSup_le fun p ↦ iSup_le fun hp ↦ ?_
  have hd := C.distance_eq p.1.1 p.1.2 p.2
  have hd₂ : dist (C.T p.1.1) (C.T p.1.2) = 2 * dist p.1.1 p.1.2 := by
    rw [hT, hT, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos zero_lt_two]
  rw [hd₂] at hd
  have hpow : (2 : ℝ) ^ C.ζ p = 2 := mul_right_cancel₀ hp.1.ne' hd.symm
  have hζ : C.ζ p = 1 := by
    apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp
    simpa using hpow
  simp only [hζ, hPot, sub_self, abs_zero, ENNReal.ofReal_zero, le_refl]

private lemma dist_iterate_doubling (T : ℝ → ℝ) (hT : ∀ x, T x = 2 * x)
    (n : ℕ) (x y : ℝ) : dist (T^[n] x) (T^[n] y) = 2 ^ n * dist x y := by
  have hiterate (z : ℝ) : T^[n] z = 2 ^ n * z := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', hT, ih, pow_succ]; ring
  rw [hiterate, hiterate, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
    abs_of_nonneg (pow_nonneg zero_le_two n)]

private lemma bowenBall_doubling (T : ℝ → ℝ) (hT : ∀ x, T x = 2 * x)
    (n : ℕ) (hn : 1 ≤ n) (x δ : ℝ) :
    bowenBall T n x δ = Metric.ball x (δ * (2 : ℝ) ^ (-((n : ℝ) - 1))) := by
  have hradius : δ * (2 : ℝ) ^ (-((n : ℝ) - 1)) = δ / (2 : ℝ) ^ (n - 1) := by
    rw [Real.rpow_neg zero_le_two, div_eq_mul_inv, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn,
        Real.rpow_natCast]
  rw [hradius]
  ext y
  simp only [bowenBall, Dynamics.dynEntourage, Set.mem_ofPred_eq, Set.mem_iInter,
    Set.mem_preimage, Prod.map_iterate, Prod.map_apply, Metric.mem_ball]
  constructor
  · intro h
    have hlast := h (n - 1) (by omega)
    change dist (T^[n - 1] x) (T^[n - 1] y) < δ at hlast
    rw [dist_iterate_doubling T hT, mul_comm, ← lt_div_iff₀ (by positivity),
      dist_comm] at hlast
    exact hlast
  · intro h k hk
    change dist (T^[k] x) (T^[k] y) < δ
    rw [dist_iterate_doubling T hT]
    have hlast : (2 : ℝ) ^ (n - 1) * dist x y < δ := by
      rwa [dist_comm, lt_div_iff₀ (by positivity), mul_comm] at h
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k ≤ n - 1))
      dist_nonneg).trans_lt hlast

private lemma ball_doubling_radius_not_subset (x δ : ℝ) (n : ℕ) (hδ : 0 < δ) :
    ¬Metric.ball x (δ * (2 : ℝ) ^ (-((n : ℝ) - 1))) ⊆
      Metric.ball x (δ * (2 : ℝ) ^ (-(n : ℝ))) := by
  have hradius : δ * (2 : ℝ) ^ (-((n : ℝ) - 1)) =
      2 * (δ * (2 : ℝ) ^ (-(n : ℝ))) := by
    rw [neg_sub, sub_eq_neg_add, Real.rpow_add zero_lt_two, Real.rpow_one]
    ring
  rw [hradius]
  let r := δ * (2 : ℝ) ^ (-(n : ℝ))
  have hr : 0 < r := mul_pos hδ (Real.rpow_pos_of_pos zero_lt_two _)
  intro h
  have hmem : x + r ∈ Metric.ball x (2 * r) := by
    simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hr]
    linarith
  have hout := h hmem
  change x + r ∈ Metric.ball x r at hout
  simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hr,
    lt_self_iff_false] at hout

/-- A doubling system on the real line has zero distortion, yet its order-`n` Bowen ball
has radius `δ * 2⁻⁽ⁿ⁻¹⁾` and violates the unshifted outer bound at every positive order.
Blueprint node `conf:ball-counterexamples`. -/
theorem ballComparisonRegression :
    ∃ C : UniformConformalData ℝ,
      (∀ x, C.T x = 2 * x) ∧ (∀ x, C.potential x = 1) ∧
      (∀ δ : ℝ, 0 < δ → δ < C.r₀ → conformalDistortion C δ = 0) ∧
      ∀ (x δ : ℝ), 0 < δ → ∀ n : ℕ, 1 ≤ n →
        bowenBall C.T n x δ = Metric.ball x (δ * (2 : ℝ) ^ (-((n : ℝ) - 1))) ∧
        ¬bowenBall C.T n x δ ⊆
          Metric.ball x (δ * (2 : ℝ) ^ (-birkhoffSum C.T C.potential n x)) := by
  let T : ℝ → ℝ := fun x ↦ 2 * x
  have hT : UniformContinuous T := Real.uniformContinuous_const_mul
  have h_dist : ∀ (x y : ℝ) (_ : dist x y < 1),
      dist (T x) (T y) = (2 : ℝ) ^ (1 : ℝ) * dist x y := by
    intro x y _
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos zero_lt_two,
      Real.rpow_one]
  let C : UniformConformalData ℝ := {
    r₀ := 1
    r₀_pos := by positivity
    T := T
    uniformContinuous_T := hT
    ζ := fun _ ↦ 1
    uniformContinuous_ζ := uniformContinuous_const
    distance_eq := h_dist
  }
  use C
  have hC_T : ∀ x, C.T x = 2 * x := fun _ ↦ rfl
  have hC_pot : ∀ x, C.potential x = 1 := fun _ ↦ rfl
  refine ⟨hC_T, hC_pot, ?_, ?_⟩
  · intro δ _ _
    exact conformalDistortion_eq_zero_of_doubling C hC_T hC_pot δ
  · intro x δ hδ n hn
    constructor
    · exact bowenBall_doubling C.T hC_T n hn x δ
    · rw [bowenBall_doubling C.T hC_T n hn x δ]
      have H_birkhoff : birkhoffSum C.T C.potential n x = (n : ℝ) := by
        simp [birkhoffSum, hC_pot]
      rw [H_birkhoff]
      exact ball_doubling_radius_not_subset x δ n hδ

/-- On the discrete natural numbers, every potential defines local conformal data:
the radius-one distance law only compares equal points. -/
private noncomputable def discreteConformalData (v : ℕ → ℝ) :
    UniformConformalData ℕ where
  r₀ := 1
  r₀_pos := zero_lt_one
  T := Nat.succ
  uniformContinuous_T := DiscreteUniformity.uniformContinuous ℕ _
  ζ := fun p ↦ v p.val.1
  uniformContinuous_ζ := (DiscreteUniformity.uniformContinuous ℕ v).comp
    (uniformContinuous_fst.comp uniformContinuous_subtype_val)
  distance_eq := by
    intro x y h
    have hxy : x = y := by
      by_contra hne
      exact (not_le_of_gt h) (Nat.pairwise_one_le_dist hne)
    subst y
    simp

/-- A nonnegative square-root oscillation, zero at odd times. -/
private noncomputable def sqrtOscillation (n : ℕ) : ℝ :=
  if n % 2 = 0 then Real.sqrt n else 0

/-- A coboundary perturbation of one, with unbounded negative one-step increments. -/
private noncomputable def sqrtCoboundaryPotential (n : ℕ) : ℝ :=
  1 + sqrtOscillation (n + 1) -
    sqrtOscillation n

private lemma iterate_succ_zero (n : ℕ) :
    Nat.succ^[n] 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]

private lemma birkhoffSum_sqrtCoboundaryPotential (n : ℕ) :
    birkhoffSum Nat.succ sqrtCoboundaryPotential n 0 =
      n + sqrtOscillation n := by
  induction n with
  | zero => simp [sqrtOscillation]
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ih, iterate_succ_zero]
    simp only [sqrtCoboundaryPotential, Nat.cast_succ]
    ring

private lemma sqrtOscillation_bounds (n : ℕ) :
    0 ≤ sqrtOscillation n ∧
      sqrtOscillation n ≤ Real.sqrt n := by
  unfold sqrtOscillation
  split_ifs <;> simp [Real.sqrt_nonneg]

private lemma sqrtOscillation_sublinear :
    Tendsto (fun n : ℕ ↦ sqrtOscillation n / n)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt n / n) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
  · intro n
    exact div_nonneg (sqrtOscillation_bounds n).1 (Nat.cast_nonneg n)
  · intro n
    exact div_le_div_of_nonneg_right
      (sqrtOscillation_bounds n).2 (Nat.cast_nonneg n)

private lemma sqrtCoboundaryPotential_average_tendsto :
    Tendsto (fun n : ℕ ↦
      birkhoffSum Nat.succ sqrtCoboundaryPotential n 0 / n)
      atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add
    sqrtOscillation_sublinear
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [birkhoffSum_sqrtCoboundaryPotential, add_div,
    div_self (by exact_mod_cast (show n ≠ 0 by omega))]

private lemma sqrtCoboundaryPotential_sublinear_growth :
    HasSublinearOrbitGrowth Nat.succ sqrtCoboundaryPotential 0 := by
  have hi : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hr : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add hi
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [add_div, div_self (by exact_mod_cast (show n ≠ 0 by omega))]
  have he : Tendsto (fun n : ℕ ↦ sqrtOscillation (n + 1) / n)
      atTop (𝓝 0) := by
    have h := (sqrtOscillation_sublinear.comp
      (tendsto_add_atTop_nat 1)).mul hr
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [] with n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [div_mul_div_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)]
  have h := (hi.add he).sub sqrtOscillation_sublinear
  simpa only [HasSublinearOrbitGrowth, iterate_succ_zero,
    sqrtCoboundaryPotential, sub_div, add_div, add_zero, sub_zero]
    using h

/-- Every suffix is bounded below by minus the square root of its ending time.
Completing the square absorbs this loss with any positive linear slack. -/
private lemma sqrtCoboundaryPotential_tempered_contraction :
    HasTemperedContraction Nat.succ sqrtCoboundaryPotential 0 := by
  intro τ hτ
  refine ⟨-(1 / τ), ?_⟩
  intro n k hkn
  rw [birkhoffSum_sqrtCoboundaryPotential, birkhoffSum_sqrtCoboundaryPotential]
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have he0 := (sqrtOscillation_bounds n).1
  have hek := (sqrtOscillation_bounds k).2
  have hsqrt : Real.sqrt k ≤ Real.sqrt n := Real.sqrt_le_sqrt hkn'
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpos := mul_nonneg hτ.le (sq_nonneg (Real.sqrt n - 1 / τ))
  have heq : τ * (Real.sqrt n - 1 / τ) ^ 2 =
      τ * (n : ℝ) - 2 * Real.sqrt n + 1 / τ := by
    calc
      τ * (Real.sqrt n - 1 / τ) ^ 2 =
          τ * (Real.sqrt n) ^ 2 - 2 * Real.sqrt n + 1 / τ := by
        field_simp [hτ.ne']
        ring
      _ = _ := by rw [hsq]
  rw [heq] at hpos
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- The suffix from the even time `2 * m^2` to the next odd time tends to minus infinity. -/
private lemma sqrtCoboundaryPotential_suffix_unbounded (c : ℝ) :
    ∃ n k : ℕ, k ≤ n ∧
      birkhoffSum Nat.succ sqrtCoboundaryPotential n 0 -
      birkhoffSum Nat.succ sqrtCoboundaryPotential k 0 < c := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 - c)
  refine ⟨2 * m ^ 2 + 1, 2 * m ^ 2, by omega, ?_⟩
  rw [birkhoffSum_sqrtCoboundaryPotential, birkhoffSum_sqrtCoboundaryPotential]
  have hbound : (m : ℝ) ≤ Real.sqrt (2 * m ^ 2 : ℕ) := by
    apply Real.le_sqrt_of_sq_le
    push_cast
    nlinarith [sq_nonneg (m : ℝ)]
  have heven : (2 * m ^ 2) % 2 = 0 := by omega
  have hodd : (2 * m ^ 2 + 1) % 2 ≠ 0 := by omega
  simp only [sqrtOscillation, heven, hodd, ↓reduceIte,
    Nat.cast_add, Nat.cast_one]
  linarith

private lemma zero_mem_sqrtCoboundary_conformalLocus :
    0 ∈ conformalLocus (discreteConformalData
      sqrtCoboundaryPotential) := by
  change (0 ∈ positiveFiniteAverageLocus Nat.succ sqrtCoboundaryPotential ∧
    HasTemperedContraction Nat.succ sqrtCoboundaryPotential 0) ∧
    HasSublinearOrbitGrowth Nat.succ sqrtCoboundaryPotential 0
  refine ⟨⟨?_, sqrtCoboundaryPotential_tempered_contraction⟩,
    sqrtCoboundaryPotential_sublinear_growth⟩
  have he : Tendsto (fun n : ℕ ↦
      ((birkhoffSum Nat.succ sqrtCoboundaryPotential n 0 / n : ℝ) : EReal))
      atTop (𝓝 (1 : EReal)) := by
    exact EReal.tendsto_coe.mpr sqrtCoboundaryPotential_average_tendsto
  change 0 < liminf _ atTop ∧ liminf _ atTop ≤ limsup _ atTop ∧ limsup _ atTop < ⊤
  rw [he.liminf_eq, he.limsup_eq]
  exact ⟨by norm_num, le_rfl, EReal.coe_lt_top 1⟩

private lemma conformalDistortion_discreteConformalData (v : ℕ → ℝ) (δ : ℝ) :
    conformalDistortion (discreteConformalData v) δ = 0 := by
  simp [conformalDistortion, discreteConformalData,
    UniformConformalData.potential]

/-- A complete separable conformal system has zero local distortion and a point in all three
loci whose suffix sums have no finite lower bound at zero slack. Its averages tend to one.
The witness uses the successor map on the natural numbers and a square-root coboundary.
Blueprint node `conf:ball-counterexamples`. -/
theorem ballComparisonRegression_tempered :
    ∃ (Y : Type) (_m : MetricSpace Y) (_P : Presentation Y) (C : UniformConformalData Y)
      (x : Y), x ∈ conformalLocus C ∧
      (∀ δ : ℝ, 0 < δ → δ < C.r₀ → conformalDistortion C δ = 0) ∧
      Tendsto (fun n : ℕ => birkhoffSum C.T C.potential n x / n) atTop (𝓝 1) ∧
      ∀ c : ℝ, ∃ n k : ℕ, k ≤ n ∧
        birkhoffSum C.T C.potential n x - birkhoffSum C.T C.potential k x < c := by
  refine ⟨ℕ, inferInstance, ⟨id, denseRange_id, inferInstance⟩,
    discreteConformalData sqrtCoboundaryPotential,
    0, zero_mem_sqrtCoboundary_conformalLocus, ?_,
    sqrtCoboundaryPotential_average_tendsto, sqrtCoboundaryPotential_suffix_unbounded⟩
  intro δ _ _
  exact conformalDistortion_discreteConformalData _ δ

end Kolmogorov.PointToSet
