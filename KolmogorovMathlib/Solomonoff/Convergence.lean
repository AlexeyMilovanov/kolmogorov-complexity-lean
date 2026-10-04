/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.KL

/-!
# Total prediction error and almost sure convergence for a dominating semimeasure

From the Kullback–Leibler bound to the two conclusions of Solomonoff's theorem, for an arbitrary
continuous tree semimeasure `a` that dominates the probability measure `μ` with a constant `c > 0`
(the universal instance `a = M` is in `Main`):

* the total expected squared error of the prediction of either bit is at most `ln(1/c) / 2`, at
  every horizon (`sum_predictionError_le`) and in the limit (`tsum_predictionError_le`, which also
  gives summability): Pinsker at each node (`two_mul_sq_condProb_sub_le_stepKL`) followed by
  KL-TOTAL (`sum_prefixExpectation_stepKL_le`);
* a general measure-theoretic step: when the expected squares `E_n[g_n²]` have bounded partial
  sums, `g_n(w_{<n}) → 0` for `μ`-almost every sequence `w`
  (`ae_tendsto_zero_of_sum_prefixExpectation_sq_le`, monotone convergence), whence
  `a(b | w_{<n}) − μ(b | w_{<n}) → 0` almost surely (`ae_tendsto_condProb_sub_of_dominates`).

Sources: Hutter (2005) Theorem 3.19 (convergence with `μ`-probability one),
Li–Vitányi (3rd ed.) Theorem 5.2.1 and the discussion after it, Solomonoff (1978).
-/

namespace Kolmogorov

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Total error at every horizon.** If `c · μ ≤ a` with `c > 0`, then for either bit `b` and
every `N`, `Σ_{n<N} E_{x ∼ μ, |x| = n} (a(b | x) − μ(b | x))² ≤ ln(1/c) / 2`. Item SOL-C-ERRSUM;
Hutter (2005) Theorem 3.19, Li–Vitányi (3rd ed.) Theorem 5.2.1 (for `a = M`). -/
theorem sum_predictionError_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (b : Bool) (N : ℕ) :
    ∑ n ∈ Finset.range N, predictionError μ a b n ≤ Real.log c⁻¹ / 2 := by
  have hac : ∀ y, cantorMass μ y ≠ 0 → a y ≠ 0 := by
    intro y hy h_a
    have h1 := hdom y
    rw [h_a] at h1
    have h2 : ENNReal.ofReal c * cantorMass μ y = 0 := by
      apply le_antisymm h1 zero_le
    cases mul_eq_zero.mp h2 with
    | inl hl =>
      have hc_enn : ENNReal.ofReal c ≠ 0 := by
        intro hc_eq
        have h_c_le_0 : c ≤ 0 := ENNReal.ofReal_eq_zero.mp hc_eq
        linarith
      exact hc_enn hl
    | inr hr => exact hy hr
  have h_bound : ∀ n, predictionError μ a b n ≤ prefixExpectation μ n (stepKL μ a) / 2 := by
    intro n
    unfold predictionError
    have h_div2 : prefixExpectation μ n (stepKL μ a) / 2 =
        prefixExpectation μ n (fun x ↦ stepKL μ a x / 2) := by
      unfold prefixExpectation
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [h_div2]
    apply prefixExpectation_mono
    intro x hx
    have h_pinsker := two_mul_sq_condProb_sub_le_stepKL μ ha hac hx b
    linarith
  have h_sum_bound : ∑ n ∈ Finset.range N, predictionError μ a b n ≤
      (∑ n ∈ Finset.range N, prefixExpectation μ n (stepKL μ a)) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro n _
    exact h_bound n
  have h_kl_total := sum_prefixExpectation_stepKL_le μ ha hc hdom N
  linarith

/-- **Finite total error.** If `c · μ ≤ a` with `c > 0`, then for either bit `b` the prediction
errors are summable and `Σ_n E_{x ∼ μ, |x| = n} (a(b | x) − μ(b | x))² ≤ ln(1/c) / 2`.
Item SOL-C-ERRTSUM; Hutter (2005) Theorem 3.19. -/
theorem tsum_predictionError_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (b : Bool) :
    Summable (predictionError μ a b) ∧ ∑' n, predictionError μ a b n ≤ Real.log c⁻¹ / 2 := by
  have h_sum_le := sum_predictionError_le μ ha hc hdom b
  have h_nonneg : ∀ n, 0 ≤ predictionError μ a b n := predictionError_nonneg μ a b
  have h_summable : Summable (predictionError μ a b) := by
    apply summable_of_sum_range_le h_nonneg h_sum_le
  refine ⟨h_summable, ?_⟩
  exact Real.tsum_le_of_sum_range_le h_nonneg h_sum_le

private theorem ennreal_ofReal_sq_cantorPrefix_eq_sum_indicator (g : ℕ → BitString → ℝ) (n : ℕ) :
    (fun w => ENNReal.ofReal (g n (cantorPrefix w n) ^ 2)) =
      fun w => ∑ x ∈ levelFinset n,
        (cantorCylinder x).indicator (fun _ => ENNReal.ofReal (g n x ^ 2)) w := by
  funext w
  have hmem := mem_cantorCylinder_cantorPrefix w n
  rw [Finset.sum_eq_single (cantorPrefix w n)]
  · simp [Set.indicator_of_mem hmem]
  · intro x hx hnx
    have hlen : x.length = n := mem_levelFinset.1 hx
    have hnot : w ∉ cantorCylinder x := by
      intro hw
      have : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hw
      rw [hlen] at this
      exact hnx this.symm
    simp [Set.indicator_of_notMem hnot]
  · intro hnot
    exact absurd (mem_levelFinset.2 (by simp)) hnot

private theorem lintegral_ennreal_ofReal_sq_cantorPrefix_eq_prefixExpectation
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (g : ℕ → BitString → ℝ) (n : ℕ) :
    ∫⁻ w, ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2) ∂μ =
      ENNReal.ofReal (prefixExpectation μ n (fun x => g n x ^ 2)) := by
  rw [ennreal_ofReal_sq_cantorPrefix_eq_sum_indicator g n]
  rw [lintegral_finsetSum _ (fun x _ =>
    (measurable_const.indicator (measurableSet_cantorCylinder x)))]
  have h1 : ∑ x ∈ levelFinset n, ∫⁻ w, (cantorCylinder x).indicator
      (fun _ => ENNReal.ofReal (g n x ^ 2)) w ∂μ =
      ∑ x ∈ levelFinset n, ENNReal.ofReal (g n x ^ 2) * (cantorMass μ x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [lintegral_indicator_const (measurableSet_cantorCylinder x)]
    rfl
  rw [h1]
  rw [prefixExpectation]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro x _
    have hcantor : cantorMass μ x = ENNReal.ofReal (cantorMass μ x).toReal := by
      rw [ENNReal.ofReal_toReal]
      exact measure_ne_top μ (cantorCylinder x)
    rw [hcantor]
    rw [← ENNReal.ofReal_mul]
    · congr 1
      have hc_re : (ENNReal.ofReal (cantorMass μ x).toReal).toReal =
        (cantorMass μ x).toReal := by
        rw [ENNReal.toReal_ofReal]
        exact ENNReal.toReal_nonneg
      rw [hc_re]
      ring
    · positivity
  · intro x _
    positivity

private theorem measurable_ennreal_ofReal_sq_cantorPrefix (g : ℕ → BitString → ℝ) (n : ℕ) :
    Measurable (fun w => ENNReal.ofReal (g n (cantorPrefix w n) ^ 2)) := by
  rw [ennreal_ofReal_sq_cantorPrefix_eq_sum_indicator g n]
  exact Finset.measurable_sum _ fun x _ =>
    measurable_const.indicator (measurableSet_cantorCylinder x)

/-- If the expected squares `E_{x ∼ μ, |x| = n} g_n(x)²` of a family of functions of the prefixes
have bounded partial sums, then `g_n(w_{<n}) → 0` for `μ`-almost every sequence `w`.
Item SOL-C-AE; the step "finite expected sum ⇒ almost surely finite sum ⇒ terms tend to zero" of
Hutter (2005) §3.2 and Li–Vitányi (3rd ed.) §5.2. -/
theorem ae_tendsto_zero_of_sum_prefixExpectation_sq_le (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (g : ℕ → BitString → ℝ) {B : ℝ}
    (h : ∀ N, ∑ n ∈ Finset.range N, prefixExpectation μ n (fun x => g n x ^ 2) ≤ B) :
    ∀ᵐ w ∂μ, Tendsto (fun n => g n (cantorPrefix w n)) atTop (𝓝 0) := by
  have h_meas_comp : ∀ n, Measurable (fun w => ENNReal.ofReal (g n (cantorPrefix w n) ^ 2)) :=
    measurable_ennreal_ofReal_sq_cantorPrefix g
  have h_bound : (∫⁻ w, ∑' n, ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2) ∂μ) < ⊤ := by
    have h_lintegral_tsum : (∫⁻ w, ∑' n, ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2) ∂μ) =
           ∑' n, ∫⁻ w, ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2) ∂μ := by
      apply lintegral_tsum
      intro n
      exact (h_meas_comp n).aemeasurable
    rw [h_lintegral_tsum]
    have h_int2 : (∑' (n : ℕ), ∫⁻ (w : CantorSeq),
        ENNReal.ofReal (g n (cantorPrefix w n) ^ 2) ∂μ) =
        ∑' n, ENNReal.ofReal (prefixExpectation μ n (fun x => g n x ^ 2)) := by
      apply tsum_congr
      intro n
      exact lintegral_ennreal_ofReal_sq_cantorPrefix_eq_prefixExpectation μ g n
    rw [h_int2]
    have hb : ∀ N, ∑ n ∈ Finset.range N, ENNReal.ofReal (prefixExpectation μ n
        (fun x => g n x ^ 2)) ≤ ENNReal.ofReal B := by
      intro N
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal (h N)
      · intro i _
        exact prefixExpectation_nonneg μ i (fun _ => by positivity)
    have h_bound_ineq := ENNReal.tsum_le_of_sum_range_le hb
    exact lt_of_le_of_lt h_bound_ineq ENNReal.ofReal_lt_top
  have h_meas : Measurable (fun w : CantorSeq =>
      ∑' n, ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2)) :=
    Measurable.tsum h_meas_comp
  have h_ae_lt_top : ∀ᵐ w ∂μ, (∑' n, ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2)) < ⊤ := by
    apply ae_lt_top' h_meas.aemeasurable h_bound.ne
  filter_upwards [h_ae_lt_top] with w hw
  have hz : Tendsto (fun n => ENNReal.ofReal ((g n (cantorPrefix w n)) ^ 2)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hw.ne
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hz
  rcases hz (ENNReal.ofReal (ε ^ 2 / 2)) (by positivity) with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  rw [Real.dist_eq, sub_zero]
  have h_le2 : ENNReal.ofReal (g n (cantorPrefix w n) ^ 2) ≤ ENNReal.ofReal (ε ^ 2 / 2) := hN
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h_le2
  have h_sq : g n (cantorPrefix w n) ^ 2 < ε ^ 2 := by
    have h_pos_sq : 0 < ε ^ 2 := by positivity
    have h_lt : ε ^ 2 / 2 < ε ^ 2 := by linarith [h_pos_sq]
    exact lt_of_le_of_lt h_le2 h_lt
  rw [← sq_abs] at h_sq
  have h_sqrt := Real.sqrt_lt_sqrt (by positivity) h_sq
  rw [Real.sqrt_sq (by positivity), Real.sqrt_sq hε.le] at h_sqrt
  exact h_sqrt

/-- **Almost sure convergence for a dominating semimeasure.** If `c · μ ≤ a` with `c > 0`, then
for either bit `b`, `a(b | w_{<n}) − μ(b | w_{<n}) → 0` as `n → ∞` for `μ`-almost every sequence
`w`. Item SOL-C-AE-DOM; Hutter (2005) Theorem 3.19 (convergence with `μ`-probability one). -/
theorem ae_tendsto_condProb_sub_of_dominates (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (b : Bool) :
    ∀ᵐ w ∂μ, Tendsto (fun n => condProb a (cantorPrefix w n) b -
      condProb (cantorMass μ) (cantorPrefix w n) b) atTop (𝓝 0) := by
  have : ∀ N, ∑ n ∈ Finset.range N, prefixExpectation μ n (fun x =>
      (condProb a x b - condProb (cantorMass μ) x b) ^ 2) ≤ Real.log c⁻¹ / 2 := by
    intro N
    have h1 : ∑ n ∈ Finset.range N, predictionError μ a b n = ∑ n ∈ Finset.range N,
        prefixExpectation μ n (fun x => (condProb a x b - condProb (cantorMass μ) x b) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rfl
    rw [← h1]
    exact sum_predictionError_le μ ha hc hdom b N
  exact ae_tendsto_zero_of_sum_prefixExpectation_sq_le μ
    (fun n x => condProb a x b - condProb (cantorMass μ) x b) this

end Kolmogorov
