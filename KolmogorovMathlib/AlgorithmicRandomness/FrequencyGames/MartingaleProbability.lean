/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Martingale
import KolmogorovMathlib.AlgorithmicRandomness.StrongLaw

import KolmogorovMathlib.AlgorithmicRandomness.BlockMap
import KolmogorovMathlib.Entropy.Coding


/-!
# A digression: martingales in probability theory (SUV Section 9.6, pp. 275-277)

The technical half of this section is the martingale proof of the Strong Law of Large Numbers: the
ratio `B_q / B_p` of two Bernoulli measures is a `B_p`-martingale, unbounded on the sequences whose
frequency of ones exceeds `q > p` infinitely often.  The second half, the "market" reading of
randomness on pp. 276-277, has no mathematical statement and is recorded as omitted in
`docs/suv_chapters_08_09.md`.

The non-effective law itself is the library's `strongLaw_bernoulli`.
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology

/-- The ratio `B_q(Ω_x) / B_p(Ω_x)` of two Bernoulli measures.  For `0 < p < 1` the denominator
never vanishes. -/
noncomputable def bernoulliRatio (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1) (x : BitString) : ℝ :=
  massR (bernoulliMeasure q hq) x / massR (bernoulliMeasure p hp) x

/-- **SUV p. 276.**  `B_q / B_p` is a `B_p`-martingale, for `0 < p < 1`. -/
theorem isMartingale_bernoulliRatio {p q : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq : q ≤ 1) :
    IsMartingale (bernoulliMeasure p hp1.le) (bernoulliRatio p q hp1.le hq) := by
  have : IsProbabilityMeasure (bernoulliMeasure p hp1.le) := inferInstance
  rw [isMartingale_iff_exists_measure]
  constructor
  · intro x
    unfold bernoulliRatio
    apply div_nonneg
    · exact ENNReal.toReal_nonneg
    · exact ENNReal.toReal_nonneg
  · use bernoulliMeasure q hq
    constructor
    · exact inferInstance
    · intro x
      unfold bernoulliRatio
      have h1 : massR (bernoulliMeasure p hp1.le) x ≠ 0 := by
        unfold massR
        have h_prod := cantorMass_bernoulliMeasure p hp1.le x
        rw [h_prod]
        clear h_prod
        rw [ENNReal.toReal_prod]
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hi' : i < List.length x := Finset.mem_Iio.mp hi
        split_ifs with hc
        · intro hp0_eq
          have ht : ENNReal.toReal p = (p : ℝ) := ENNReal.coe_toReal p
          rw [ht] at hp0_eq
          have : (p : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hp0.ne'
          contradiction
        · intro hp1_eq
          have ht : ENNReal.toReal (1 - p) = 1 - (p : ℝ) := by
            have h_eq : ENNReal.toReal (1 - p) = ENNReal.toReal 1 - ENNReal.toReal p := by
              apply ENNReal.toReal_sub_of_le
              · exact (ENNReal.coe_le_one_iff (r := p)).mpr hp1.le
              · exact ENNReal.one_ne_top
            rw [h_eq, ENNReal.toReal_one, ENNReal.coe_toReal]
          rw [ht] at hp1_eq
          have : 1 - (p : ℝ) ≠ 0 := by
            intro h
            have : (p:ℝ) = 1 := by linarith
            have : p = 1 := NNReal.coe_inj.mp this
            linarith
          contradiction
      exact div_mul_cancel₀ _ h1





/-- Step 1 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
the mass of a prefix under Bernoulli measure is p^k (1-p)^{n-k}. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_mass
    {p : NNReal} (hp : p ≤ 1) (x : BitString) :
  massR (bernoulliMeasure p hp) x =
      (p : ℝ) ^ x.count true * (1 - (p : ℝ)) ^ x.count false := by
  unfold massR
  rw [cantorMass_bernoulliMeasure_prod]
  rw [prod_map_ite_bool]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.coe_toReal]
  have h1 : (1 - (p : ENNReal)).toReal = 1 - (p : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · rfl
    · exact ENNReal.coe_mono hp
    · exact ENNReal.coe_ne_top
  rw [h1]

/-- Step 2 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
the log of the ratio B_q(x)/B_p(x) is a linear combination. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_logb
    {p q : NNReal} (hp0 : 0 < p) (hpq : p < q) (hq1 : q < 1) (x : BitString) :
  Real.logb 2 (bernoulliRatio p q (hpq.trans hq1).le hq1.le x) =
    (x.count true : ℝ) * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
    (x.count false : ℝ) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ))) := by
  unfold bernoulliRatio
  rw [wins_bernoulliRatio_of_frequently_freq_gt_mass hq1.le x]
  rw [wins_bernoulliRatio_of_frequently_freq_gt_mass (hpq.trans hq1).le x]
  have hq0 : 0 < q := hp0.trans hpq
  have hp_pos : 0 < (p : ℝ) := NNReal.coe_pos.mpr hp0
  have hq_pos : 0 < (q : ℝ) := NNReal.coe_pos.mpr hq0
  have hq_lt1 : (q : ℝ) < 1 := hq1
  have hp_lt1 : (p : ℝ) < 1 := hpq.trans hq1
  have hp1_pos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp_lt1
  have hq1_pos : 0 < 1 - (q : ℝ) := sub_pos.mpr hq_lt1
  have H_rewrite : 
    ((q : ℝ) ^ x.count true * (1 - (q : ℝ)) ^ x.count false) /
    ((p : ℝ) ^ x.count true * (1 - (p : ℝ)) ^ x.count false) =
    ((q : ℝ) / (p : ℝ)) ^ x.count true * ((1 - (q : ℝ)) / (1 - (p : ℝ))) ^ x.count false := by
    rw [div_mul_eq_div_div, div_pow, div_pow]; ring
  rw [H_rewrite, Real.logb_mul]
  · rw [Real.logb_pow, Real.logb_pow]
  · exact (pow_pos (div_pos hq_pos hp_pos) _).ne'
  · exact (pow_pos (div_pos hq1_pos hp1_pos) _).ne'

/-- Step 3 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
express the log ratio using the frequency of ones. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_logb_freq
    {p q : NNReal} (hp0 : 0 < p) (hpq : p < q) (hq1 : q < 1) (w : CantorSeq) (n : ℕ) (hn : 0 < n) :
  Real.logb 2 (bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n)) =
    n * ((freqOne w n : ℝ) * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
         (1 - (freqOne w n : ℝ)) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ)))) := by
  have h2 := wins_bernoulliRatio_of_frequently_freq_gt_logb hp0 hpq hq1 (cantorPrefix w n)
  rw [h2]
  have h_len : ((cantorPrefix w n).count true : ℝ) + ((cantorPrefix w n).count false : ℝ) = n := by
    have h1 : (cantorPrefix w n).count true + (cantorPrefix w n).count false = (cantorPrefix w
        n).length := by
      exact count_true_add_count_false (cantorPrefix w n)
    have h2_len : (cantorPrefix w n).length = n := cantorPrefix_length w n
    rw [h2_len] at h1
    exact_mod_cast h1
  have h_freq : (freqOne w n : ℝ) = ((cantorPrefix w n).count true : ℝ) / n := by
    unfold freqOne
    push_cast
    rfl
  rw [h_freq]
  have h_n : (n : ℝ) ≠ 0 := by positivity
  have h_false : ((cantorPrefix w n).count false : ℝ) = n - ((cantorPrefix w n).count true : ℝ) :=
      by linarith
  rw [h_false]
  have h_div : (((cantorPrefix w n).count true : ℝ) / n) * n = ((cantorPrefix w n).count true : ℝ)
      := div_mul_cancel₀ _ h_n
  calc
    ((cantorPrefix w n).count true : ℝ) * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
        (↑n - ((cantorPrefix w n).count true : ℝ)) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ)))
      = (((cantorPrefix w n).count true : ℝ) / n) * n * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
        (↑n - (((cantorPrefix w n).count true : ℝ) / n) * n) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p
            : ℝ))) := by rw [h_div]
    _ = (((cantorPrefix w n).count true : ℝ) / n) * n * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
        (1 - (((cantorPrefix w n).count true : ℝ) / n)) * n * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p :
            ℝ))) := by ring
    _ = ↑n * ((((cantorPrefix w n).count true : ℝ) / ↑n) * Real.logb 2 (↑q / ↑p) +
        (1 - (((cantorPrefix w n).count true : ℝ) / ↑n)) * Real.logb 2 ((1 - ↑q) / (1 - ↑p))) := by
            ring

/-- Step 4 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
the KL divergence is positive. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_klDiv_pos
    {p q : NNReal} (hp0 : 0 < p) (hpq : p < q) (hq1 : q < 1) :
    0 < klDiv (fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ))
      (fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ)) := by
  let P : Bool → ℝ := fun b => if b then (q : ℝ) else 1 - (q : ℝ)
  let P' : Bool → ℝ := fun b => if b then (p : ℝ) else 1 - (p : ℝ)
  have hP_nonneg : ∀ a, 0 ≤ P a := by
    intro a
    cases a
    · dsimp [P]; have : (q : ℝ) < 1 := hq1; linarith
    · dsimp [P]; positivity
  have hP_sum : ∑ a : Bool, P a = 1 := by
    rw [Fintype.sum_bool]
    dsimp [P]
    ring
  have hP'_pos : ∀ a, 0 < P' a := by
    intro a
    cases a
    · dsimp [P']; have : (p : ℝ) < 1 := (NNReal.coe_lt_coe.mpr hpq).trans (NNReal.coe_lt_coe.mpr
        hq1); linarith
    · dsimp [P']; exact NNReal.coe_pos.mpr hp0
  have hP'_sum : ∑ a : Bool, P' a = 1 := by
    rw [Fintype.sum_bool]
    dsimp [P']
    ring
  have h_nonneg := klDiv_nonneg hP_nonneg hP_sum hP'_pos hP'_sum
  apply lt_of_le_of_ne h_nonneg
  intro h_eq_zero
  have h_eq := (klDiv_eq_zero_iff hP_nonneg hP_sum hP'_pos hP'_sum).mp h_eq_zero.symm
  have h_eq_true := h_eq true
  dsimp [P, P'] at h_eq_true
  have hpq_real : (p : ℝ) < (q : ℝ) := NNReal.coe_lt_coe.mpr hpq
  linarith

/-- Step 5 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
a specific logarithmic term is strictly positive. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_logb_pos
    {p q : NNReal} (hp0 : 0 < p) (hpq : p < q) (hq1 : q < 1) :
  0 < Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) := by
  have hp0' : (0 : ℝ) < p := by exact NNReal.coe_pos.mpr hp0
  have hpq' : (p : ℝ) < q := by exact NNReal.coe_lt_coe.mpr hpq
  have hq1' : (q : ℝ) < 1 := by exact NNReal.coe_lt_coe.mpr hq1
  apply Real.logb_pos
  · norm_num
  · have hq : (0 : ℝ) < 1 - q := sub_pos.mpr hq1'
    have hp1' : (p : ℝ) < 1 := hpq'.trans hq1'
    have hp : (0 : ℝ) < 1 - p := sub_pos.mpr hp1'
    have H : (0 : ℝ) < p * (1 - q) := mul_pos hp0' hq
    rw [one_lt_div H]
    nlinarith

/-- Step 6 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
linear expansion of the log term involving KL divergence. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_linear
    {p q : NNReal} (hp0 : 0 < p) (hpq : p < q) (hq1 : q < 1) (x : ℝ) :
  x * Real.logb 2 ((q : ℝ) / (p : ℝ)) + (1 - x) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ))) =
  (x - (q : ℝ)) * Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) +
  klDiv (fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ))
    (fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ)) := by
  unfold klDiv
  rw [Fintype.sum_bool]
  dsimp only
  simp only [ite_true, ite_false, Bool.false_eq_true]
  have hq_pos : (0 : ℝ) < q := NNReal.coe_pos.mpr (hp0.trans hpq)
  have hp_pos : (0 : ℝ) < p := NNReal.coe_pos.mpr hp0
  have h1_sub_p_pos : (0 : ℝ) < 1 - p := by
    have h : (p : ℝ) < 1 := NNReal.coe_lt_coe.mpr (hpq.trans hq1)
    linarith
  have h1_sub_q_pos : (0 : ℝ) < 1 - q := by
    have h : (q : ℝ) < 1 := NNReal.coe_lt_coe.mpr hq1
    linarith
  have h_inner : ((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ))) = ((q : ℝ) / (p : ℝ)) / ((1 -
      (q : ℝ)) / (1 - (p : ℝ))) := by
    calc ((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))
      _ = ((q : ℝ) * (1 - (p : ℝ))) * ((p : ℝ) * (1 - (q : ℝ)))⁻¹ := rfl
      _ = ((q : ℝ) * (1 - (p : ℝ))) * ((p : ℝ)⁻¹ * (1 - (q : ℝ))⁻¹) := by rw [mul_inv_rev] ; ring
      _ = ((q : ℝ) * (p : ℝ)⁻¹) * ((1 - (q : ℝ))⁻¹ * (1 - (p : ℝ))) := by ring
      _ = ((q : ℝ) / (p : ℝ)) * ((1 - (q : ℝ))⁻¹ * (1 - (p : ℝ))) := rfl
      _ = ((q : ℝ) / (p : ℝ)) * ((1 - (q : ℝ)) / (1 - (p : ℝ)))⁻¹ := by
        congr 1
        have : ((1 - (q : ℝ)) / (1 - (p : ℝ)))⁻¹ = ((1 - (q : ℝ)) * (1 - (p : ℝ))⁻¹)⁻¹ := rfl
        rw [this, mul_inv_rev, inv_inv]
        ring
      _ = ((q : ℝ) / (p : ℝ)) / ((1 - (q : ℝ)) / (1 - (p : ℝ))) := rfl
  have h_logb : Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) = 
    Real.logb 2 ((q : ℝ) / (p : ℝ)) - Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ))) := by
    rw [h_inner]
    have h1 : (q : ℝ) / (p : ℝ) ≠ 0 := ne_of_gt (div_pos hq_pos hp_pos)
    have h2 : (1 - (q : ℝ)) / (1 - (p : ℝ)) ≠ 0 := ne_of_gt (div_pos h1_sub_q_pos h1_sub_p_pos)
    exact Real.logb_div h1 h2
  
  rw [h_logb]
  ring

/-- Step 7 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
uniform positive lower bound. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_uniform_bound
    {p q : NNReal} (hp0 : 0 < p) (hpq : p < q) (hq1 : q < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ freq : ℝ, (q : ℝ) < freq →
      c ≤ freq * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
      (1 - freq) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ))) := by
  let D := klDiv (fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ))
    (fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ))
  use D
  constructor
  · exact wins_bernoulliRatio_of_frequently_freq_gt_klDiv_pos hp0 hpq hq1
  · intro freq h_freq
    rw [wins_bernoulliRatio_of_frequently_freq_gt_linear hp0 hpq hq1 freq]
    have hL : 0 < Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) :=
      wins_bernoulliRatio_of_frequently_freq_gt_logb_pos hp0 hpq hq1
    have h_sub : 0 < freq - (q : ℝ) := sub_pos.mpr h_freq
    have h_mul_nonneg : 0 ≤ (freq - (q : ℝ)) * Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) *
        (1 - (q : ℝ)))) :=
      mul_nonneg h_sub.le hL.le
    linarith

/-- Step 8 of the proof of wins_bernoulliRatio_of_frequently_freq_gt:
bridge between lower bound and unboundedness. -/
private lemma wins_bernoulliRatio_of_frequently_freq_gt_unbounded_of_log_bound
    {p q : NNReal} (hpq : p < q) (hq1 : q < 1)
    {w : CantorSeq} (hw : ∃ᶠ n in atTop, (q : ℝ) < (freqOne w n : ℝ))
    {c : ℝ} (hc : 0 < c)
    (hlog : ∀ n, 0 < n → (q : ℝ) < (freqOne w n : ℝ) →
      n * c ≤ Real.logb 2
        (bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n))) :
    Wins (bernoulliRatio p q (hpq.trans hq1).le hq1.le) w := by
  intro hbnd
  rcases hbnd with ⟨M, hM⟩
  have h_exists_N : ∃ N : ℕ, Real.logb 2 M / c < N := exists_nat_gt (Real.logb 2 M / c)
  rcases h_exists_N with ⟨N, hN⟩
  have hw_frequent : ∃ n, max N 1 ≤ n ∧ (q : ℝ) < (freqOne w n : ℝ) := by
    have hw_atTop := frequently_atTop.mp hw (max N 1)
    rcases hw_atTop with ⟨n, hn_le, hn_freq⟩
    exact ⟨n, hn_le, hn_freq⟩
  rcases hw_frequent with ⟨n, hn_le, hn_freq⟩
  have hn_pos : 0 < n := by
    have h1 : 1 ≤ max N 1 := le_max_right N 1
    linarith
  have hlog_n : (n : ℝ) * c ≤ Real.logb 2 (bernoulliRatio p q (hpq.trans hq1).le hq1.le
      (cantorPrefix w n)) := by
    apply hlog n hn_pos hn_freq
  have hr_nonneg : 0 ≤ bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n) := by
    unfold bernoulliRatio
    apply div_nonneg
    · exact ENNReal.toReal_nonneg
    · exact ENNReal.toReal_nonneg
  have hR_le_M : bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n) ≤ M := by
    apply hM
    simp only [Set.mem_range, exists_apply_eq_apply]
  have hr_pos : 0 < bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n) := by
    by_contra! h_not_pos
    have hr_zero : bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n) = 0 :=
        le_antisymm h_not_pos hr_nonneg
    have hlog_zero : Real.logb 2 (bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n)) =
        0 := by
      rw [hr_zero, Real.logb, Real.log_zero]
      simp
    rw [hlog_zero] at hlog_n
    have hnc_pos : 0 < (n : ℝ) * c := mul_pos (Nat.cast_pos.mpr hn_pos) hc
    linarith
  have hlogM_le : Real.logb 2 (bernoulliRatio p q (hpq.trans hq1).le hq1.le (cantorPrefix w n)) ≤
      Real.logb 2 M := by
    apply Real.logb_le_logb_of_le (by norm_num) hr_pos hR_le_M
  have hnc_le_logM : (n : ℝ) * c ≤ Real.logb 2 M := hlog_n.trans hlogM_le
  have hN_le_n : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_trans (le_max_left N 1) hn_le)
  have hNc_le_nc : (N : ℝ) * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right hN_le_n hc.le
  have hNc_le_logM : (N : ℝ) * c ≤ Real.logb 2 M := hNc_le_nc.trans hnc_le_logM
  have hlogM_lt_Nc : Real.logb 2 M < (N : ℝ) * c := (div_lt_iff₀ hc).mp hN
  linarith

/-- **SUV p. 276.**  For `0 < p < q < 1`, the martingale `B_q / B_p` is unbounded on the sequences
where the frequency of ones exceeds `q` infinitely often.  This is where Gibbs' inequality is
used. -/
theorem wins_bernoulliRatio_of_frequently_freq_gt {p q : NNReal} (hp0 : 0 < p) (hpq : p < q)
    (hq1 : q < 1) {w : CantorSeq} (hw : ∃ᶠ n in atTop, (q : ℝ) < (freqOne w n : ℝ)) :
    Wins (bernoulliRatio p q (hpq.trans hq1).le hq1.le) w := by
  rcases wins_bernoulliRatio_of_frequently_freq_gt_uniform_bound
      hp0 hpq hq1 with ⟨c, hc_pos, hc_bound⟩
  apply wins_bernoulliRatio_of_frequently_freq_gt_unbounded_of_log_bound
      hpq hq1 hw hc_pos
  intro n hn h_freq_gt
  have h3 := wins_bernoulliRatio_of_frequently_freq_gt_logb_freq hp0 hpq hq1 w n hn
  rw [h3]
  have h_bnd := hc_bound (freqOne w n : ℝ) h_freq_gt
  exact mul_le_mul_of_nonneg_left h_bnd (by positivity)




/-- Step 3 of the proof of wins_bernoulliRatio_of_frequently_freq_lt: ... -/
private lemma wins_bernoulliRatio_of_frequently_freq_lt_logb_freq
    {p q : NNReal} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (w : CantorSeq) (n : ℕ) (hn : 0 < n) :
  Real.logb 2 (bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n)) =
    (n : ℝ) * ((freqOne w n : ℝ) * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
         (1 - (freqOne w n : ℝ)) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ)))) := by
  unfold bernoulliRatio
  rw [wins_bernoulliRatio_of_frequently_freq_gt_mass (hqp.trans hp1).le (cantorPrefix w n)]
  rw [wins_bernoulliRatio_of_frequently_freq_gt_mass hp1.le (cantorPrefix w n)]
  have hp0 : 0 < p := hq0.trans hqp
  have hq1 : q < 1 := hqp.trans hp1
  have hp_pos : 0 < (p : ℝ) := NNReal.coe_pos.mpr hp0
  have hq_pos : 0 < (q : ℝ) := NNReal.coe_pos.mpr hq0
  have hp1_pos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hq1_pos : 0 < 1 - (q : ℝ) := sub_pos.mpr hq1
  have H_rewrite :
             ((q : ℝ) ^ (cantorPrefix w n).count true * (1 - (q : ℝ)) ^ (cantorPrefix w n).count
                 false) /
             ((p : ℝ) ^ (cantorPrefix w n).count true * (1 - (p : ℝ)) ^ (cantorPrefix w n).count
                 false) =
             ((q : ℝ) / (p : ℝ)) ^ (cantorPrefix w n).count true * ((1 - (q : ℝ)) / (1 - (p : ℝ))) ^
                 (cantorPrefix w n).count false := by
    rw [div_mul_eq_div_div, div_pow, div_pow]; ring
  rw [H_rewrite, Real.logb_mul]
  · rw [Real.logb_pow, Real.logb_pow]
    have h_len : ((cantorPrefix w n).count true : ℝ) + ((cantorPrefix w n).count false : ℝ) = n :=
        by
               have h1 : (cantorPrefix w n).count true + (cantorPrefix w n).count false =
                   (cantorPrefix w n).length := count_true_add_count_false (cantorPrefix w n)
               have h2_len : (cantorPrefix w n).length = n := cantorPrefix_length w n
               rw [h2_len] at h1
               exact_mod_cast h1
    have h_freq : (freqOne w n : ℝ) = ((cantorPrefix w n).count true : ℝ) / n := by
               unfold freqOne
               push_cast
               rfl
    rw [h_freq]
    have h_n : (n : ℝ) ≠ 0 := by positivity
    have h_false : ((cantorPrefix w n).count false : ℝ) = n - ((cantorPrefix w n).count true : ℝ) :=
        by linarith
    rw [h_false]
    calc
      ((cantorPrefix w n).count true : ℝ) * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
          (↑n - ((cantorPrefix w n).count true : ℝ)) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ)))
        = (((cantorPrefix w n).count true : ℝ) / n) * n * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
            (↑n - (((cantorPrefix w n).count true : ℝ) / n) * n) * Real.logb 2 ((1 - (q : ℝ)) / (1 -
                (p : ℝ))) := by
          rw [div_mul_cancel₀ _ h_n]
      _ = ↑n * (((cantorPrefix w n).count true : ℝ) / ↑n * Real.logb 2 (↑q / ↑p) +
            (1 - ((cantorPrefix w n).count true : ℝ) / ↑n) * Real.logb 2 ((1 - ↑q) / (1 - ↑p))) :=
                by ring
  · exact (pow_pos (div_pos hq_pos hp_pos) _).ne'
  · exact (pow_pos (div_pos hq1_pos hp1_pos) _).ne'

/-- Step 4 of the proof of wins_bernoulliRatio_of_frequently_freq_lt: ... -/
private lemma wins_bernoulliRatio_of_frequently_freq_lt_klDiv_pos
    {p q : NNReal} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    0 < klDiv (fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ))
      (fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ)) := by
  let D1 : Bool → ℝ := fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ)
  let D2 : Bool → ℝ := fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ)
  have hq_pos : (0 : ℝ) < q := NNReal.coe_pos.mpr hq0
  have hp_lt_one : (p : ℝ) < 1 := NNReal.coe_lt_one.mpr hp1
  have hq_lt_p : (q : ℝ) < p := NNReal.coe_lt_coe.mpr hqp
  have hp_pos : (0 : ℝ) < p := lt_trans hq_pos hq_lt_p
  have hq_lt_one : (q : ℝ) < 1 := lt_trans hq_lt_p hp_lt_one
  have hp_nonneg : ∀ a : Bool, 0 ≤ D1 a := by
    intro a
    cases a <;> dsimp [D1]
    · linarith
    · positivity
  have hp_sum : ∑ a : Bool, D1 a = 1 := by
    rw [Fintype.sum_bool]
    dsimp [D1]
    ring
  have hq_pos_fun : ∀ a : Bool, 0 < D2 a := by
    intro a
    cases a <;> dsimp [D2]
    · linarith
    · positivity
  have hq_sum_fun : ∑ a : Bool, D2 a = 1 := by
    rw [Fintype.sum_bool]
    dsimp [D2]
    ring
  have hk_nonneg := Kolmogorov.klDiv_nonneg hp_nonneg hp_sum hq_pos_fun hq_sum_fun
  have hk_ne_zero : klDiv D1 D2 ≠ 0 := by
    intro h_eq
    have hk_eq := (Kolmogorov.klDiv_eq_zero_iff hp_nonneg hp_sum hq_pos_fun hq_sum_fun).mp h_eq
    have h_eval : D1 true = D2 true := by rw [hk_eq]
    dsimp [D1, D2] at h_eval
    linarith
  exact lt_of_le_of_ne hk_nonneg hk_ne_zero.symm

/-- Step 5 of the proof of wins_bernoulliRatio_of_frequently_freq_lt: ... -/
private lemma wins_bernoulliRatio_of_frequently_freq_lt_logb_pos
    {p q : NNReal} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
  0 > Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) := by
  have hq0' : 0 < (q : ℝ) := NNReal.coe_pos.mpr hq0
  have hp0' : 0 < (p : ℝ) := hq0'.trans (NNReal.coe_lt_coe.mpr hqp)
  have hp1' : (p : ℝ) < 1 := hp1
  have hq1' : (q : ℝ) < 1 := (NNReal.coe_lt_coe.mpr hqp).trans hp1'
  have h_num : 0 < (q : ℝ) * (1 - (p : ℝ)) := mul_pos hq0' (sub_pos.mpr hp1')
  have h_den : 0 < (p : ℝ) * (1 - (q : ℝ)) := mul_pos hp0' (sub_pos.mpr hq1')
  have h_div_pos : 0 < (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) := div_pos h_num
      h_den
  have h_num_lt_den : (q : ℝ) * (1 - (p : ℝ)) < (p : ℝ) * (1 - (q : ℝ)) := by
    calc (q : ℝ) * (1 - (p : ℝ)) = (q : ℝ) - (q : ℝ) * (p : ℝ) := by ring
      _ < (p : ℝ) - (q : ℝ) * (p : ℝ) := sub_lt_sub_right (NNReal.coe_lt_coe.mpr hqp) ((q : ℝ) * (p
          : ℝ))
      _ = (p : ℝ) * (1 - (q : ℝ)) := by ring
  have h_div_lt_one : (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) < 1 := (div_lt_one
      h_den).mpr h_num_lt_den
  exact Real.logb_neg (by norm_num) h_div_pos h_div_lt_one

/-- Step 6 of the proof of wins_bernoulliRatio_of_frequently_freq_lt: ... -/
private lemma wins_bernoulliRatio_of_frequently_freq_lt_linear
    {p q : NNReal} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (x : ℝ) :
  x * Real.logb 2 ((q : ℝ) / (p : ℝ)) + (1 - x) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ))) =
  (x - (q : ℝ)) * Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 - (q : ℝ)))) +
  klDiv (fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ))
    (fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ)) := by
  classical
  have hq_pos : (0 : ℝ) < (q : ℝ) :=
    NNReal.coe_pos.mpr hq0
  have hp_pos : (0 : ℝ) < (p : ℝ) :=
    NNReal.coe_pos.mpr (hq0.trans hqp)
  have hp_lt : (p : ℝ) < 1 :=
    NNReal.coe_lt_coe.mpr hp1
  have hq_lt : (q : ℝ) < 1 :=
    NNReal.coe_lt_coe.mpr (hqp.trans hp1)
  have hlog :
      Real.logb 2
        (((q : ℝ) * (1 - (p : ℝ))) /
          ((p : ℝ) * (1 - (q : ℝ)))) =
      Real.logb 2 ((q : ℝ) / (p : ℝ)) -
        Real.logb 2
          ((1 - (q : ℝ)) / (1 - (p : ℝ))) := by
    calc
      _ = Real.logb 2
          (((q : ℝ) / (p : ℝ)) /
            ((1 - (q : ℝ)) / (1 - (p : ℝ)))) :=
        congrArg (Real.logb 2)
          (div_div_div_eq (q : ℝ) (p : ℝ)
            (1 - (q : ℝ)) (1 - (p : ℝ))).symm
      _ = _ := Real.logb_div
        (div_pos hq_pos hp_pos).ne'
        (div_pos (sub_pos.mpr hq_lt)
          (sub_pos.mpr hp_lt)).ne'
  simpa only [klDiv, Fintype.sum_bool,
    Bool.false_eq_true, ite_true, ite_false, hlog] using
    (show
      x * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
          (1 - x) * Real.logb 2
            ((1 - (q : ℝ)) / (1 - (p : ℝ))) =
      (x - (q : ℝ)) *
          (Real.logb 2 ((q : ℝ) / (p : ℝ)) -
            Real.logb 2
              ((1 - (q : ℝ)) / (1 - (p : ℝ)))) +
        ((q : ℝ) * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
          (1 - (q : ℝ)) * Real.logb 2
            ((1 - (q : ℝ)) / (1 - (p : ℝ)))) from by
      ring)

/-- Step 7 of the proof of wins_bernoulliRatio_of_frequently_freq_lt: ... -/
private lemma wins_bernoulliRatio_of_frequently_freq_lt_uniform_bound
    {p q : NNReal} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ freq : ℝ, freq < (q : ℝ) →
      c ≤ freq * Real.logb 2 ((q : ℝ) / (p : ℝ)) +
      (1 - freq) * Real.logb 2 ((1 - (q : ℝ)) / (1 - (p : ℝ))) := by
  use klDiv (fun b : Bool => if b then (q : ℝ) else 1 - (q : ℝ))
    (fun b : Bool => if b then (p : ℝ) else 1 - (p : ℝ))
  refine ⟨wins_bernoulliRatio_of_frequently_freq_lt_klDiv_pos hq0 hqp hp1, ?_⟩
  intro freq hfreq
  rw [wins_bernoulliRatio_of_frequently_freq_lt_linear hq0 hqp hp1 freq]
  have hA := wins_bernoulliRatio_of_frequently_freq_lt_logb_pos hq0 hqp hp1
  have h_sub : freq - (q : ℝ) < 0 := sub_neg.mpr hfreq
  have h_mul_pos : 0 ≤ (freq - (q : ℝ)) * Real.logb 2 (((q : ℝ) * (1 - (p : ℝ))) / ((p : ℝ) * (1 -
      (q : ℝ)))) :=
    mul_nonneg_of_nonpos_of_nonpos h_sub.le hA.le
  linarith

/-- Step 8 of the proof of wins_bernoulliRatio_of_frequently_freq_lt: ... -/
private lemma wins_bernoulliRatio_of_frequently_freq_lt_unbounded_of_log_bound
    {p q : NNReal} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1)
    {w : CantorSeq} (hw : ∃ᶠ n in atTop, (freqOne w n : ℝ) < (q : ℝ))
    {c : ℝ} (hc : 0 < c)
    (hlog : ∀ n, 0 < n → (freqOne w n : ℝ) < (q : ℝ) →
      (n : ℝ) * c ≤ Real.logb 2
        (bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n))) :
    Wins (bernoulliRatio p q hp1.le (hqp.trans hp1).le) w := by
  intro hbnd
  rcases hbnd with ⟨B, hB⟩
  have hB_le : ∀ n, bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n) ≤ B := by
    intro n
    apply hB
    exact Set.mem_range_self n
  have h_freq : ∃ n, ⌈Real.logb 2 B / c⌉₊ + 1 ≤ n ∧ (freqOne w n : ℝ) < (q : ℝ) := by
    obtain ⟨n, hn1, hn2⟩ := frequently_atTop.mp hw (⌈Real.logb 2 B / c⌉₊ + 1)
    exact ⟨n, hn1, hn2⟩
  rcases h_freq with ⟨n, hn_le, hn_lt⟩
  have hn_pos : 0 < n := by omega
  have h1 : (n : ℝ) * c ≤ Real.logb 2 (bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w
      n)) :=
    hlog n hn_pos hn_lt
  
  have h_r_nonneg : 0 ≤ bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n) := by
    unfold bernoulliRatio
    apply div_nonneg <;> exact ENNReal.toReal_nonneg
    
  have h_r_pos : 0 < bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n) := by
    by_contra h_contra
    push Not at h_contra
    have h_r_eq_0 : bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n) = 0 :=
      le_antisymm h_contra h_r_nonneg
    rw [h_r_eq_0] at h1
    have h_log_0 : Real.logb 2 0 = 0 := by simp
    rw [h_log_0] at h1
    have h_nc_pos : 0 < (n : ℝ) * c := mul_pos (Nat.cast_pos.mpr hn_pos) hc
    linarith
  have h_B_pos : 0 < B := h_r_pos.trans_le (hB_le n)
  have h_logb_le : Real.logb 2 (bernoulliRatio p q hp1.le (hqp.trans hp1).le (cantorPrefix w n)) ≤
      Real.logb 2 B := by
    apply (Real.logb_le_logb (by norm_num) h_r_pos h_B_pos).mpr (hB_le n)
    
  have h2 : (n : ℝ) * c ≤ Real.logb 2 B := h1.trans h_logb_le
  have h3 : (n : ℝ) ≤ Real.logb 2 B / c := (le_div_iff₀ hc).mpr h2
  
  have h4 : (⌈Real.logb 2 B / c⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn_le
  have h5 : Real.logb 2 B / c ≤ (⌈Real.logb 2 B / c⌉₊ : ℝ) := Nat.le_ceil _
  linarith


/-- **SUV p. 276.**  The symmetric case: for `0 < q < p < 1`, the martingale `B_q / B_p` is
unbounded on the sequences where the frequency of ones falls below `q` infinitely often. -/
theorem wins_bernoulliRatio_of_frequently_freq_lt {p q : NNReal} (hq0 : 0 < q) (hqp : q < p)
    (hp1 : p < 1) {w : CantorSeq} (hw : ∃ᶠ n in atTop, (freqOne w n : ℝ) < (q : ℝ)) :
    Wins (bernoulliRatio p q hp1.le (hqp.trans hp1).le) w := by
  rcases wins_bernoulliRatio_of_frequently_freq_lt_uniform_bound
      hq0 hqp hp1 with ⟨c, hc_pos, hc_bound⟩
  apply wins_bernoulliRatio_of_frequently_freq_lt_unbounded_of_log_bound
      hq0 hqp hp1 hw hc_pos
  intro n hn h_freq_lt
  have h3 := wins_bernoulliRatio_of_frequently_freq_lt_logb_freq hq0 hqp hp1 w n hn
  rw [h3]
  have h_bnd := hc_bound (freqOne w n : ℝ) h_freq_lt
  exact mul_le_mul_of_nonneg_left h_bnd (by positivity)

end Kolmogorov.FrequencyGames





