/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.Convergence
import KolmogorovMathlib.Solomonoff.Domination

/-!
# Solomonoff's theorem

The universal predictor `M(b | x) = M(xb) / M(x)` of the a priori probability
`M = universalContinuousSemimeasure` learns every computable probability measure `μ` on Cantor
space: its total expected squared prediction error is finite, bounded by `(ln 2 / 2) (K(μ) + C)`
with a universal constant `C`, and its predictions converge to the true conditionals
`μ(b | x_{<n})` with `μ`-probability one.

### Outline

* `solomonoff_tsum_stepKL_le_log` (target KL-TOTAL for `M`): under `c · μ ≤ M`, the expected
  one-step divergences `E_n[KL(μ(· | x) ‖ M(· | x))]` have partial sums at most `ln(1/c)` at every
  horizon, are summable, and sum to at most `ln(1/c)`; `solomonoff_tsum_stepKL_le_complexity` is the
  complexity form `ln 2 · (K(μ) + C)`;
* `solomonoff_tsum_predictionError_le_log` (target SOLOMONOFF, `ln(1/c) / 2` form): under
  `c · μ ≤ M`, `Σ_n E_n[(M(b | x) − μ(b | x))²] ≤ ln(1/c) / 2` for either bit `b`;
* `solomonoff_tsum_predictionError_le_complexity` (target SOLOMONOFF, main form): a universal
  constant `C`, quantified before `μ`, with
  `Σ_n E_n[(M(b | x) − μ(b | x))²] ≤ (ln 2 / 2) (K(μ) + C)` for every computable probability
  measure `μ` and either bit `b`;
* `solomonoff_tsum_sum_predictionError_le_log`: the Euclidean form of Hutter (2005) Theorem 3.19,
  errors of both bits summed, bound `ln(1/c)`;
* `solomonoff_ae_tendsto` (target CONV): `M(b | w_{<n}) − μ(b | w_{<n}) → 0` for `μ`-almost every
  `w`.

All statements use the unnormalized predictor and measure the error bit by bit; see the module
`Solomonoff.Basic` for the semimeasure caveat.

Sources: R. J. Solomonoff (1978); Li–Vitányi (3rd ed.) Theorem 5.2.1; Hutter (2005)
Theorem 3.19.
-/

namespace Kolmogorov

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **KL-TOTAL for the universal predictor.** If `c · μ(Ω_x) ≤ M(x)` for all `x` with `c > 0`,
then the expected one-step divergences `E_{x ∼ μ, |x| = n} KL(μ(· | x) ‖ M(· | x))` have partial
sums at most `ln(1/c)` at every horizon `N`, hence are summable with sum at most `ln(1/c)`.
Item SOL-M-KL (target KL-TOTAL); Hutter (2005) Theorem 3.19 (`D_∞ ≤ ln w_μ^{-1}`),
Li–Vitányi (3rd ed.) §5.2. -/
theorem solomonoff_tsum_stepKL_le_log (μ : Measure CantorSeq) [IsProbabilityMeasure μ] {c : ℝ}
    (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ universalContinuousSemimeasure x) :
    (∀ N, ∑ n ∈ Finset.range N,
        prefixExpectation μ n (stepKL μ universalContinuousSemimeasure) ≤ Real.log c⁻¹) ∧
      Summable (fun n => prefixExpectation μ n (stepKL μ universalContinuousSemimeasure)) ∧
      ∑' n, prefixExpectation μ n (stepKL μ universalContinuousSemimeasure) ≤
        Real.log c⁻¹ := by
  have hN : ∀ N, ∑ n ∈ Finset.range N,
      prefixExpectation μ n (stepKL μ universalContinuousSemimeasure) ≤ Real.log c⁻¹ :=
    sum_prefixExpectation_stepKL_le μ
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
      hc hdom
  have h_nonneg : ∀ n, 0 ≤ prefixExpectation μ n (stepKL μ universalContinuousSemimeasure) := by
    intro n
    unfold prefixExpectation
    apply Finset.sum_nonneg
    intro x _
    by_cases hx : cantorMass μ x = 0
    · rw [hx, ENNReal.toReal_zero, zero_mul]
    · apply mul_nonneg
      · exact ENNReal.toReal_nonneg
      · refine stepKL_nonneg μ
          universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 ?_ hx
        intro y _ hy_uni
        have hpos := universalContinuousSemimeasure_toReal_pos y
        rw [hy_uni, ENNReal.toReal_zero] at hpos
        exact lt_irrefl _ hpos
  have h_sum_le : ∀ s : Finset ℕ, ∑ i ∈ s,
      prefixExpectation μ i (stepKL μ universalContinuousSemimeasure) ≤ Real.log c⁻¹ := by
    intro s
    obtain ⟨N, hN_le⟩ := Finset.exists_nat_subset_range s
    calc
      ∑ i ∈ s, prefixExpectation μ i (stepKL μ universalContinuousSemimeasure)
        ≤ ∑ i ∈ Finset.range N, prefixExpectation μ i (stepKL μ universalContinuousSemimeasure) :=
          Finset.sum_le_sum_of_subset_of_nonneg hN_le (fun i _ _ => h_nonneg i)
      _ ≤ Real.log c⁻¹ := hN N
  have h_summable : Summable
      (fun n => prefixExpectation μ n (stepKL μ universalContinuousSemimeasure)) :=
    summable_of_sum_le h_nonneg h_sum_le
  have h_tsum : ∑' n, prefixExpectation μ n (stepKL μ universalContinuousSemimeasure) ≤
      Real.log c⁻¹ :=
    Real.tsum_le_of_sum_le h_nonneg h_sum_le
  exact ⟨hN, h_summable, h_tsum⟩

/-- **KL-TOTAL, complexity form.** There is a constant `C`, quantified before the measure, such
that for every computable probability measure `μ` the expected one-step divergences of `M` are
summable with `Σ_n E_n[KL(μ(· | x) ‖ M(· | x))] ≤ ln 2 · (K(μ) + C)`, where
`K(μ) = computableMeasureComplexity U μ`. Item SOL-M-KL-K; Li–Vitányi (3rd ed.) §5.2,
Hutter (2005) Theorem 3.19 with `w_μ = 2^{-K(μ)}`. -/
theorem solomonoff_tsum_stepKL_le_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (μ : Measure CantorSeq) [IsProbabilityMeasure μ], IsComputableMeasure μ →
      Summable (fun n => prefixExpectation μ n (stepKL μ universalContinuousSemimeasure)) ∧
        ∑' n, prefixExpectation μ n (stepKL μ universalContinuousSemimeasure) ≤
          Real.log 2 * (((computableMeasureComplexity U μ).toNat + C : ℕ) : ℝ) := by
  obtain ⟨C, hC⟩ := exists_const_two_pow_complexity_mul_cantorMass_le_universal U hU
  use C
  intro μ _ hμ
  have hdom := hC μ hμ
  set c : ℝ := (2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U μ).toNat + C)
  have hc : 0 < c := by
    apply pow_pos
    norm_num
  have hdom_real : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ universalContinuousSemimeasure x := by
    intro x
    have h_c_eq : ENNReal.ofReal c =
        (2 : ℝ≥0∞)⁻¹ ^ ((computableMeasureComplexity U μ).toNat + C) := by
      unfold c
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
      rw [ENNReal.ofReal_ofNat]
    rw [h_c_eq]
    exact hdom x
  obtain ⟨_, h_summable, h_tsum⟩ := solomonoff_tsum_stepKL_le_log μ hc hdom_real
  refine ⟨h_summable, le_trans h_tsum ?_⟩
  unfold c
  rw [inv_pow, inv_inv, Real.log_pow, mul_comm]

/-- **Solomonoff's theorem, `ln(1/c) / 2` form.** If `c · μ(Ω_x) ≤ M(x)` for all `x` with
`c > 0`, then for either bit `b` the prediction errors of the universal predictor are summable and
`Σ_n E_{x ∼ μ, |x| = n} (M(b | x) − μ(b | x))² ≤ ln(1/c) / 2`. Item SOL-M-MAIN-C (target
SOLOMONOFF, `ln(1/c)/2` version); Hutter (2005) Theorem 3.19, Li–Vitányi (3rd ed.)
Theorem 5.2.1. -/
theorem solomonoff_tsum_predictionError_le_log (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ universalContinuousSemimeasure x)
    (b : Bool) :
    Summable (predictionError μ universalContinuousSemimeasure b) ∧
      ∑' n, predictionError μ universalContinuousSemimeasure b n ≤ Real.log c⁻¹ / 2 :=
  tsum_predictionError_le μ
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 hc hdom b

/-- **Solomonoff's theorem.** There is a constant `C`, quantified before the measure, such that
for every computable probability measure `μ` on Cantor space and either bit `b` the prediction
errors of the universal predictor are summable and
`Σ_n E_{x ∼ μ, |x| = n} (M(b | x) − μ(b | x))² ≤ (ln 2 / 2) · (K(μ) + C)`, where
`K(μ) = computableMeasureComplexity U μ` is the prefix complexity of `μ`. With `b = true` this is
the error of the prediction of a one. Item SOL-M-MAIN (target SOLOMONOFF); Solomonoff (1978),
Li–Vitányi (3rd ed.) Theorem 5.2.1, Hutter (2005) Theorem 3.19. -/
theorem solomonoff_tsum_predictionError_le_complexity (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (μ : Measure CantorSeq) [IsProbabilityMeasure μ], IsComputableMeasure μ →
      ∀ b : Bool, Summable (predictionError μ universalContinuousSemimeasure b) ∧
        ∑' n, predictionError μ universalContinuousSemimeasure b n ≤
          Real.log 2 / 2 * (((computableMeasureComplexity U μ).toNat + C : ℕ) : ℝ) := by
  obtain ⟨C, hC⟩ := exists_const_two_pow_complexity_mul_cantorMass_le_universal U hU
  use C; intro μ _ hμ b
  have hc : 0 < (2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U μ).toNat + C) := by positivity
  have hdom : ∀ x, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U μ).toNat + C)) *
      cantorMass μ x ≤ universalContinuousSemimeasure x := by
    intro x; have := hC μ hμ x
    rwa [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_ofNat]
  have h := solomonoff_tsum_predictionError_le_log μ hc hdom b
  have h_eq : Real.log ((2 : ℝ)⁻¹ ^ ((computableMeasureComplexity U μ).toNat + C))⁻¹ / 2 =
      Real.log 2 / 2 * (((computableMeasureComplexity U μ).toNat + C : ℕ) : ℝ) := by
    rw [inv_pow, inv_inv, Real.log_pow]
    ring
  rwa [h_eq] at h

/-- **Solomonoff's theorem, Euclidean form.** If `c · μ(Ω_x) ≤ M(x)` for all `x` with `c > 0`,
the errors of both bits together are summable with
`Σ_n E_{x ∼ μ, |x| = n} Σ_b (M(b | x) − μ(b | x))² ≤ ln(1/c)`: the form of Hutter (2005)
Theorem 3.19(i) (`Σ_t E[s_t] ≤ ln w_μ^{-1}`) for the binary alphabet. Item SOL-M-EUCLID. -/
theorem solomonoff_tsum_sum_predictionError_le_log (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ universalContinuousSemimeasure x) :
    Summable (fun n => ∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) ∧
      ∑' n, ∑ b : Bool, predictionError μ universalContinuousSemimeasure b n ≤
        Real.log c⁻¹ := by
  have hF := solomonoff_tsum_predictionError_le_log μ hc hdom false
  have hT := solomonoff_tsum_predictionError_le_log μ hc hdom true
  have hSummable : Summable
      (fun n => ∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) := by
    have h_eq : (fun n => ∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) =
        (fun n => predictionError μ universalContinuousSemimeasure false n +
        predictionError μ universalContinuousSemimeasure true n) := by
      ext n
      have : (∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) =
          predictionError μ universalContinuousSemimeasure true n +
          predictionError μ universalContinuousSemimeasure false n :=
        Fintype.sum_bool (predictionError μ universalContinuousSemimeasure · n)
      rw [this]
      ring
    rw [h_eq]
    exact Summable.add hF.1 hT.1
  refine ⟨hSummable, ?_⟩
  have h_add : (∑' n, ∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) =
               (∑' n, predictionError μ universalContinuousSemimeasure false n) +
               (∑' n, predictionError μ universalContinuousSemimeasure true n) := by
    have h_eq : (fun n => ∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) =
                (fun n => predictionError μ universalContinuousSemimeasure false n +
                predictionError μ universalContinuousSemimeasure true n) := by
      ext n
      have : (∑ b : Bool, predictionError μ universalContinuousSemimeasure b n) =
          predictionError μ universalContinuousSemimeasure true n +
          predictionError μ universalContinuousSemimeasure false n :=
        Fintype.sum_bool (predictionError μ universalContinuousSemimeasure · n)
      rw [this]
      ring
    rw [h_eq]
    exact Summable.tsum_add hF.1 hT.1
  rw [h_add]
  have h_bound : (Real.log c⁻¹ / 2) + (Real.log c⁻¹ / 2) = Real.log c⁻¹ := by ring
  linarith [hF.2, hT.2, h_bound]

/-- **Convergence of the universal predictor.** For every computable probability measure `μ` on
Cantor space and either bit `b`, `M(b | w_{<n}) − μ(b | w_{<n}) → 0` as `n → ∞` for `μ`-almost
every sequence `w`. Item SOL-M-CONV (target CONV); Solomonoff (1978), Li–Vitányi (3rd ed.) §5.2
(convergence with `μ`-probability one), Hutter (2005) Theorem 3.19. -/
theorem solomonoff_ae_tendsto (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) (b : Bool) :
    ∀ᵐ w ∂μ, Tendsto (fun n => solomonoffPredictor (cantorPrefix w n) b -
      condProb (cantorMass μ) (cantorPrefix w n) b) atTop (𝓝 0) := by
  have h_dom := exists_pos_mul_cantorMass_le_universal μ hμ
  obtain ⟨c, hc_pos, hc_le⟩ := h_dom
  have h_lsc := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have h_ae := ae_tendsto_condProb_sub_of_dominates μ h_lsc hc_pos hc_le b
  unfold solomonoffPredictor
  exact h_ae

end Kolmogorov
