/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.IndependentTrials

/-!
# Frequency Deviation

A law of large numbers for a sequence with variable conditional probabilities: the number of ones
among the first `n` terms deviates from the sum `condSum` of the conditional probabilities of `1`
by a quantity of lower order than `n`.

Main declarations:
* `measure_abs_ones_sub_condSum_gt_le`: an exponential tail bound for the deviation;
* `ae_tendsto_ones_sub_condSum`: almost surely the normalized deviation tends to `0`
  (Theorem 199 of Shen, Uspensky, Vereshchagin);
* `selectedPositions`, `selectedOnes`, `selectedCondSum`, `measure_selected_abs_sub_gt_le`: the
  analogous statements along the positions selected by a set of strings `R`
  (used in Theorems 201 and 202 of the book).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### The law of large numbers for variable probabilities -/

/-- The number of ones among the first `n` terms, as a real. -/
noncomputable def onesR (w : CantorSeq) (n : ℕ) : ℝ := ((cantorPrefix w n).count true : ℝ)

/-- The sum of the conditional probabilities of `1` at the first `n` positions. -/
noncomputable def condSum (μ : Measure CantorSeq) (w : CantorSeq) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, condOne μ (cantorPrefix w i)

/-- Step 1 of the proof of `measure_abs_ones_sub_condSum_gt_le`: bounds of `condOne`. -/
private lemma measure_abs_ones_sub_condSum_gt_le_condOne_mem_Icc
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (x : List Bool) :
    0 ≤ condOne μ x ∧ condOne μ x ≤ 1 := by
  have h1 : 0 ≤ massR μ (x ++ [true]) := ENNReal.toReal_nonneg
  have h0 : 0 ≤ massR μ (x ++ [false]) := ENNReal.toReal_nonneg
  have hx : massR μ x = massR μ (x ++ [false]) + massR μ (x ++ [true]) := massR_add x
  have hc : condOne μ x = massR μ (x ++ [true]) / massR μ x := rfl
  rw [hc]
  refine ⟨div_nonneg h1 (by linarith), ?_⟩
  rcases (show 0 ≤ massR μ x by linarith).eq_or_lt with h | h
  · rw [← h]; simp
  · exact (div_le_one h).2 (by linarith)

/-- The tilted martingale used in the proof of `measure_abs_ones_sub_condSum_gt_le`. -/
private noncomputable def measure_abs_ones_sub_condSum_gt_le_tilt_M (μ : Measure CantorSeq) (t : ℝ)
    (x : List Bool) : ℝ :=
  ∏ i ∈ Finset.range x.length, (1 + t * ((if x.getD i false then 1 else 0) - condOne μ (x.take i)))

private lemma measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale_aux_cond
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (x : List Bool) :
    0 ≤ condOne μ x ∧ condOne μ x ≤ 1 ∧
      condOne μ x * massR μ x = massR μ (x ++ [true]) ∧
      (1 - condOne μ x) * massR μ x = massR μ (x ++ [false]) := by
  have h0 : 0 ≤ massR μ x := ENNReal.toReal_nonneg
  have h1 : 0 ≤ massR μ (x ++ [true]) := ENNReal.toReal_nonneg
  have h2 : 0 ≤ massR μ (x ++ [false]) := ENNReal.toReal_nonneg
  have hadd := massR_add (π := μ) x
  have hc : condOne μ x = massR μ (x ++ [true]) / massR μ x := rfl
  by_cases hz : massR μ x = 0
  · have e1 : massR μ (x ++ [true]) = 0 := by linarith
    have e2 : massR μ (x ++ [false]) = 0 := by linarith
    have : condOne μ x = 0 := by rw [hc, hz]; simp
    refine ⟨by rw [this], by rw [this]; norm_num, ?_, ?_⟩
    · rw [hz, e1]; simp
    · rw [hz, e2]; simp
  · have hpos : 0 < massR μ x := lt_of_le_of_ne h0 (Ne.symm hz)
    refine ⟨by rw [hc]; positivity, ?_, ?_, ?_⟩
    · rw [hc, div_le_one hpos]; linarith
    · rw [hc]; field_simp
    · rw [hc]; field_simp; linarith

private lemma measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale_aux_step
    (μ : Measure CantorSeq) (t : ℝ) (x : List Bool) (b : Bool) :
    measure_abs_ones_sub_condSum_gt_le_tilt_M μ t (x ++ [b]) =
      measure_abs_ones_sub_condSum_gt_le_tilt_M μ t x *
        (1 + t * ((if b then 1 else 0) - condOne μ x)) := by
  unfold measure_abs_ones_sub_condSum_gt_le_tilt_M
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < x.length := Finset.mem_range.mp hi
    rw [List.getD_append _ _ _ _ hi', List.take_append_of_le_length hi'.le]
  · simp

/-- Step 2 of the proof of `measure_abs_ones_sub_condSum_gt_le`: tilt is a martingale. -/
private lemma measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : |t| ≤ 1) :
    IsMartingale μ (measure_abs_ones_sub_condSum_gt_le_tilt_M μ t) := by
  have ht' := abs_le.mp ht
  have hfac : ∀ x : List Bool, ∀ b : Bool,
      0 ≤ 1 + t * ((if b then (1:ℝ) else 0) - condOne μ x) := by
    intro x b
    obtain ⟨hp0, hp1, -, -⟩ :=
      measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale_aux_cond μ x
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      nlinarith [ht'.1, ht'.2]
    · simp only [ite_true]
      nlinarith [ht'.1, ht'.2]
  have hnn : ∀ x : List Bool, 0 ≤ measure_abs_ones_sub_condSum_gt_le_tilt_M μ t x := by
    intro x
    unfold measure_abs_ones_sub_condSum_gt_le_tilt_M
    refine Finset.prod_nonneg fun i _ => ?_
    exact hfac _ _
  refine ⟨⟨hnn, ?_⟩, ?_⟩
  · intro x
    obtain ⟨-, -, e1, e0⟩ :=
      measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale_aux_cond μ x
    rw [measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale_aux_step,
      measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale_aux_step,
      ← e1, ← e0]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    ring
  · simp [measure_abs_ones_sub_condSum_gt_le_tilt_M]

/-- Step 3 of the proof of `measure_abs_ones_sub_condSum_gt_le`: exponential bound on the
increment. -/
private lemma measure_abs_ones_sub_condSum_gt_le_exp_sub_sq_le_one_add
    (h : ℝ) (h_bound : |h| ≤ 1 / 2) :
    Real.exp (h - h^2) ≤ 1 + h := by
  have hb := abs_le.mp h_bound
  rcases le_or_gt 0 h with h0 | h0
  · have hpos : 0 < 1 - h + h^2 := by nlinarith [sq_nonneg h]
    have h1 : 1 - h + h^2 ≤ Real.exp (-(h - h^2)) := by
      have := Real.add_one_le_exp (-(h - h^2)); linarith
    have h2 : Real.exp (h - h^2) * Real.exp (-(h - h^2)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : Real.exp (h - h^2) * (1 - h + h^2) ≤ 1 := by
      calc Real.exp (h - h^2) * (1 - h + h^2) ≤ Real.exp (h - h^2) * Real.exp (-(h - h^2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    have h4 : 1 ≤ (1 + h) * (1 - h + h^2) := by nlinarith [pow_nonneg h0 3]
    exact le_of_mul_le_mul_right (h3.trans h4) hpos
  · obtain ⟨s, rfl⟩ : ∃ s, h = -s := ⟨-h, by ring⟩
    have hs0 : 0 ≤ s := by linarith
    have hs1 : s ≤ 1/2 := by linarith
    have hy : 0 ≤ s + s^2 := by positivity
    have h1 := Real.quadratic_le_exp_of_nonneg hy
    have h2 : Real.exp (-(s + s^2)) * Real.exp (s + s^2) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : 1 ≤ (1 - s) * (1 + (s + s^2) + (s + s^2)^2 / 2) := by
      have a1 : s^2 ≤ 1/4 := by nlinarith
      have a2 : s^3 ≤ 1/8 := by nlinarith [sq_nonneg s]
      have a3 : 0 ≤ s^2 / 2 * (1 - s - s^2 - s^3) := by
        apply mul_nonneg (by positivity); nlinarith [sq_nonneg s]
      nlinarith [a3, pow_nonneg hs0 3, pow_nonneg hs0 4, pow_nonneg hs0 5]
    have h6 : (1 - s) * (1 + (s + s^2) + (s + s^2)^2 / 2) ≤ (1 - s) * Real.exp (s + s^2) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h7 : 1 ≤ (1 - s) * Real.exp (s + s^2) := h5.trans h6
    have e : -s - (-s)^2 = -(s + s^2) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h7 (Real.exp_pos (-(s + s^2))).le
    calc Real.exp (-(s + s^2)) = Real.exp (-(s + s^2)) * 1 := by ring
      _ ≤ Real.exp (-(s + s^2)) * ((1 - s) * Real.exp (s + s^2)) := this
      _ = (1 - s) * (Real.exp (-(s + s^2)) * Real.exp (s + s^2)) := by ring
      _ = 1 + -s := by rw [h2]; ring

/-- Step 4 of the proof of `measure_abs_ones_sub_condSum_gt_le`: exponential bound on the
tilt. -/
private lemma measure_abs_ones_sub_condSum_gt_le_exp_le_tilt
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : |t| ≤ 1 / 2) (x : List Bool) :
    Real.exp (t * (x.count true - ∑ i ∈ Finset.range x.length, condOne μ (x.take i)) - x.length *
        t^2) ≤ measure_abs_ones_sub_condSum_gt_le_tilt_M μ t x := by
  induction x using List.reverseRecOn with
  | nil => simp [measure_abs_ones_sub_condSum_gt_le_tilt_M]
  | append_singleton y β ih =>
    have hlen : (y ++ [β]).length = y.length + 1 := by simp
    have hsum : ∑ i ∈ Finset.range (y ++ [β]).length, condOne μ ((y ++ [β]).take i) =
        ∑ i ∈ Finset.range y.length, condOne μ (y.take i) + condOne μ y := by
      rw [hlen, Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ y.length := (Finset.mem_range.mp hi).le
        rw [List.take_append_of_le_length hi']
      · rw [List.take_append_of_le_length le_rfl]
        simp
    have hprod : measure_abs_ones_sub_condSum_gt_le_tilt_M μ t (y ++ [β]) =
        measure_abs_ones_sub_condSum_gt_le_tilt_M μ t y *
          (1 + t * ((if β then 1 else 0) - condOne μ y)) := by
      unfold measure_abs_ones_sub_condSum_gt_le_tilt_M
      rw [hlen, Finset.prod_range_succ]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        have hi1 : i < y.length := Finset.mem_range.mp hi
        have hi' : i ≤ y.length := hi1.le
        rw [List.take_append_of_le_length hi', List.getD_append _ _ _ _ hi1]
      · rw [List.take_append_of_le_length le_rfl]
        simp
    have hcount : ((y ++ [β]).count true : ℝ) = (y.count true : ℝ) + (if β then 1 else 0) := by
      rw [List.count_append]
      cases β <;> simp
    obtain ⟨hp0, hp1⟩ := measure_abs_ones_sub_condSum_gt_le_condOne_mem_Icc μ y
    set p := condOne μ y with hp
    set b : ℝ := if β then 1 else 0 with hb
    have hb01 : 0 ≤ b ∧ b ≤ 1 := by
      rw [hb]; split_ifs <;> norm_num
    have hbp : |b - p| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hb01.1, hb01.2]
    have hh : |t * (b - p)| ≤ 1/2 := by
      rw [abs_mul]
      calc |t| * |b - p| ≤ (1/2) * 1 := mul_le_mul ht hbp (abs_nonneg _) (by norm_num)
        _ = 1/2 := by norm_num
    have hh2 : (t * (b - p))^2 ≤ t^2 := by
      rw [mul_pow]
      have : (b - p)^2 ≤ 1 := (sq_le_one_iff_abs_le_one (b - p)).mpr hbp
      nlinarith [sq_nonneg t]
    have hstep := measure_abs_ones_sub_condSum_gt_le_exp_sub_sq_le_one_add (t * (b - p)) hh
    have hsplit : t * (((y ++ [β]).count true : ℝ) - ∑ i ∈ Finset.range (y ++ [β]).length,
        condOne μ ((y ++ [β]).take i)) - ((y ++ [β]).length : ℝ) * t^2 =
        (t * ((y.count true : ℝ) - ∑ i ∈ Finset.range y.length, condOne μ (y.take i)) -
            (y.length : ℝ) * t^2) + (t * (b - p) - t^2) := by
      rw [hsum, hcount, hlen]
      push_cast
      ring
    rw [hsplit, Real.exp_add, hprod]
    have h1 : Real.exp (t * (b - p) - t^2) ≤ 1 + t * (b - p) :=
      le_trans (Real.exp_le_exp.mpr (by linarith)) hstep
    exact mul_le_mul ih h1 (Real.exp_pos _).le
      (le_trans (Real.exp_pos _).le ih)

/-- Step 5 of the proof of `measure_abs_ones_sub_condSum_gt_le`: assemble the one-sided
bounds. -/
private lemma measure_abs_ones_sub_condSum_gt_le_assemble
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {d : ℝ} (hd : 0 ≤ d) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    μ {w | d < s * (onesR w n - condSum μ w n)} ≤ ENNReal.ofReal (Real.exp (-d ^ 2 / (4 * n))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs1 : s ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  have habs : |s| = 1 := by rcases hs with h | h <;> simp [h]
  by_cases hdn : d ≤ n
  · set τ : ℝ := d / (2 * n) with hτ
    have hτ0 : 0 ≤ τ := by positivity
    have hτ1 : τ ≤ 1 / 2 := by
      rw [hτ, div_le_iff₀ (by positivity)]; linarith
    have ht : |s * τ| ≤ 1 / 2 := by
      rw [abs_mul, habs, abs_of_nonneg hτ0, one_mul]; exact hτ1
    have hM := measure_abs_ones_sub_condSum_gt_le_tilt_isMartingale μ (s * τ)
      (le_trans ht (by norm_num))
    have hc : 0 < Real.exp (d ^ 2 / (4 * n)) := Real.exp_pos _
    have hV := measure_exists_ge_le hM.toIsFairCapital hc
    rw [hM.init] at hV
    have e : 1 / Real.exp (d ^ 2 / (4 * n)) = Real.exp (-d ^ 2 / (4 * n)) := by
      rw [one_div, ← Real.exp_neg]; congr 1; ring
    rw [e] at hV
    refine le_trans (measure_mono ?_) hV
    intro w hw
    have hw' : d < s * (onesR w n - condSum μ w n) := hw
    refine ⟨n, ?_⟩
    have h4 := measure_abs_ones_sub_condSum_gt_le_exp_le_tilt μ (s * τ) ht
      (cantorPrefix w n)
    have hlen : (cantorPrefix w n).length = n := cantorPrefix_length w n
    have hsum : ∑ i ∈ Finset.range (cantorPrefix w n).length,
        condOne μ ((cantorPrefix w n).take i) = condSum μ w n := by
      rw [hlen, condSum]
      exact Finset.sum_congr rfl fun i hi =>
        by rw [cantorPrefix_take w i n (Finset.mem_range.mp hi).le]
    rw [hsum, hlen] at h4
    have hcnt : (((cantorPrefix w n).count true : ℕ) : ℝ) = onesR w n := rfl
    rw [hcnt] at h4
    refine le_trans (Real.exp_le_exp.mpr ?_) h4
    have h1 : τ * d ≤ τ * (s * (onesR w n - condSum μ w n)) :=
      mul_le_mul_of_nonneg_left hw'.le hτ0
    have h2 : (n : ℝ) * (s * τ) ^ 2 = d ^ 2 / (4 * n) := by
      have : (s * τ) ^ 2 = τ ^ 2 := by rw [mul_pow, hs1, one_mul]
      rw [this, hτ]; field_simp; ring
    have h3 : τ * d = d ^ 2 / (2 * n) := by rw [hτ]; field_simp
    have h5 : s * τ * (onesR w n - condSum μ w n) = τ * (s * (onesR w n - condSum μ w n)) := by ring
    have h6 : d ^ 2 / (2 * n) = 2 * (d ^ 2 / (4 * n)) := by field_simp; ring
    change d ^ 2 / (4 * n) ≤ s * τ * (onesR w n - condSum μ w n) - n * (s * τ) ^ 2
    rw [h2, h5]
    linarith
  · push Not at hdn
    have hempty : {w | d < s * (onesR w n - condSum μ w n)} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : 0 ≤ onesR w n := Nat.cast_nonneg _
      have h2 : onesR w n ≤ n := by
        have := List.count_le_length (a := true) (l := cantorPrefix w n)
        rw [cantorPrefix_length] at this
        unfold onesR
        exact_mod_cast this
      have h3 : 0 ≤ condSum μ w n :=
        Finset.sum_nonneg fun i _ => (measure_abs_ones_sub_condSum_gt_le_condOne_mem_Icc μ
                                       _).1
      have h4 : condSum μ w n ≤ n := by
        calc condSum μ w n ≤ ∑ i ∈ Finset.range n, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => (measure_abs_ones_sub_condSum_gt_le_condOne_mem_Icc
                                             μ _).2
          _ = n := by simp
      have h5 : |onesR w n - condSum μ w n| ≤ n := by
        rw [abs_le]; constructor <;> linarith
      calc s * (onesR w n - condSum μ w n) ≤ |s * (onesR w n - condSum μ w n)| := le_abs_self _
        _ = |onesR w n - condSum μ w n| := by rw [abs_mul, habs, one_mul]
        _ ≤ n := h5
        _ ≤ d := hdn.le
    rw [hempty]; simp

/-- **SUV Theorem 198, p. 302.**  For an arbitrary probability measure `μ` on `Ω` (so, for an
arbitrary distribution on `n`-bit strings), `d ≥ 0` and `n ≥ 1`,

`Pr[ |m - (p_0 + … + p_{n-1})| > d ] ≤ 2 e^{-d² / 4n}`.

The hypothesis `0 ≤ d` is implicit in the book: for `d < 0` the event is certain and the bound can
fall below `1`. -/
theorem measure_abs_ones_sub_condSum_gt_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {d : ℝ} (hd : 0 ≤ d) :
    μ {w | d < |onesR w n - condSum μ w n|} ≤
      ENNReal.ofReal (2 * Real.exp (-d ^ 2 / (4 * n))) := by
  have H : {w | d < |onesR w n - condSum μ w n|} =
      {w | d < onesR w n - condSum μ w n} ∪ {w | d < -(onesR w n - condSum μ w n)} := by
    ext w
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    exact lt_abs (a := d) (b := onesR w n - condSum μ w n)
  rw [H]
  calc μ ({w | d < onesR w n - condSum μ w n} ∪ {w | d < -(onesR w n - condSum μ w n)})
    _ ≤ μ {w | d < onesR w n - condSum μ w n} + μ {w | d < -(onesR w n - condSum μ w n)} :=
        measure_union_le _ _
    _ = μ {w | d < 1 * (onesR w n - condSum μ w n)} + μ {w | d < -1 * (onesR w n - condSum μ w n)}
        := by
      congr 2
      · ext w
        simp only [one_mul, Set.mem_ofPred_eq]
      · ext w
        simp only [neg_mul, one_mul, Set.mem_ofPred_eq]
    _ ≤ ENNReal.ofReal (Real.exp (-d ^ 2 / (4 * n))) + ENNReal.ofReal (Real.exp (-d ^ 2 / (4 * n)))
        := by
      have h_gt := measure_abs_ones_sub_condSum_gt_le_assemble μ hn hd 1 (Or.inl rfl)
      have h_lt := measure_abs_ones_sub_condSum_gt_le_assemble μ hn hd (-1) (Or.inr rfl)
      exact add_le_add h_gt h_lt
    _ = ENNReal.ofReal (2 * Real.exp (-d ^ 2 / (4 * n))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

/-- Step 1 of the proof of `ae_tendsto_ones_sub_condSum`: bounding tail sums. -/
private lemma ae_tendsto_ones_sub_condSum_summable_exp (ε : ℝ) (hε : 0 < ε) :
    (∑' n : ℕ, ENNReal.ofReal (2 * Real.exp (- (ε * (n : ℝ)) ^ 2 / (4 * n)))) ≠ ⊤ := by
  set r : ℝ := Real.exp (-(ε ^ 2 / 4)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have : 0 < ε ^ 2 / 4 := by positivity
    linarith
  have heq : ∀ n : ℕ, 2 * Real.exp (- (ε * (n : ℝ)) ^ 2 / (4 * n)) = 2 * r ^ n := by
    intro n
    congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hr, ← Real.exp_nat_mul]
      congr 1
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hs : Summable (fun n : ℕ => 2 * r ^ n) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left 2
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
  exact ENNReal.ofReal_ne_top

/-- Step 2 of the proof of `ae_tendsto_ones_sub_condSum`: probability of limsup is zero.
-/
private lemma ae_tendsto_ones_sub_condSum_limsup (μ : Measure CantorSeq) [IsProbabilityMeasure
    μ]
    (ε : ℝ) (hε : 0 < ε) :
    μ (limsup (fun n => {w | ε * n < |onesR w n - condSum μ w n|}) atTop) = 0 := by
  have H : (∑' n : ℕ, ENNReal.ofReal (2 * Real.exp (- (ε * (n : ℝ)) ^ 2 / (4 * n)))) ≠ ⊤ :=
      ae_tendsto_ones_sub_condSum_summable_exp ε hε
  have h1 : ∀ n : ℕ, 0 < n → μ {w | ε * n < |onesR w n - condSum μ w n|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε * n) ^ 2 / (4 * n))) := by
    intro n hn
    have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
    exact measure_abs_ones_sub_condSum_gt_le μ hn (by positivity : 0 ≤ ε * (n : ℝ))
  have h2 : ∀ n : ℕ, μ {w | ε * n < |onesR w n - condSum μ w n|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε * n) ^ 2 / (4 * n))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · calc μ {w | ε * ((0 : ℕ) : ℝ) < |onesR w 0 - condSum μ w 0|} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(ε * ((0 : ℕ) : ℝ)) ^ 2 / (4 * ((0 : ℕ) : ℝ)))) := by
          simp only [Nat.cast_zero, mul_zero, neg_zero, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, zero_pow, zero_div, Real.exp_zero, mul_one]
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
          norm_num
    · exact h1 n hn
  refine measure_limsup_atTop_eq_zero ?_
  exact ne_top_of_le_ne_top H (ENNReal.tsum_le_tsum h2)

/-- Step 3 of the proof of `ae_tendsto_ones_sub_condSum`: almost everywhere eventually
bounded. -/
private lemma ae_tendsto_ones_sub_condSum_eventually (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ w ∂μ, ∀ᶠ n in atTop, |onesR w n - condSum μ w n| ≤ ε * n := by
  have H : μ (limsup (fun n => {w | ε * n < |onesR w n - condSum μ w n|}) atTop) = 0 :=
      ae_tendsto_ones_sub_condSum_limsup μ ε hε
  rw [ae_iff]
  refine measure_mono_null ?_ H
  intro w hw
  have hw' : ∃ᶠ n in atTop, ε * n < |onesR w n - condSum μ w n| := by
    have hw2 : ¬ ∀ᶠ n in atTop, |onesR w n - condSum μ w n| ≤ ε * n := hw
    simpa only [Filter.not_eventually, not_le] using hw2
  exact Filter.mem_limsup_iff_frequently_mem.mpr hw'

/-- Step 4 of the proof of `ae_tendsto_ones_sub_condSum`: difference tends to zero with
division. -/
private lemma ae_tendsto_ones_sub_condSum_step4 (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ w ∂μ, ∀ᶠ n in atTop, |onesR w n / n - condSum μ w n / n| < ε := by
  have h := ae_tendsto_ones_sub_condSum_eventually μ (ε / 2) (by linarith)
  filter_upwards [h] with w hw
  obtain ⟨N, hN⟩ := eventually_atTop.mp hw
  apply eventually_atTop.mpr
  use N + 1
  intro n hn
  have hn_pos : 0 < n := by omega
  have h_le := hN n (by omega)
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_div : |onesR w n / n - condSum μ w n / n| = |onesR w n - condSum μ w n| / n := by
    rw [← sub_div, abs_div, abs_of_pos hn_real_pos]
  rw [h_div]
  have h_lt : ε / 2 * n / n < ε := by
    rw [mul_div_cancel_right₀ _ (by positivity)]
    linarith
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right h_le (by positivity)) h_lt

/-- **SUV Theorem 199, p. 303.**  For a sequence with distribution `μ`, with probability `1` the
difference of the frequency of ones and the average conditional probability tends to `0`. -/
theorem ae_tendsto_ones_sub_condSum (μ : Measure CantorSeq) [IsProbabilityMeasure μ] :
    ∀ᵐ w ∂μ, Tendsto (fun n : ℕ => onesR w n / n - condSum μ w n / n) atTop (𝓝 0) := by
  have h1 : ∀ ε : ℚ, 0 < ε → ∀ᵐ w ∂μ, ∀ᶠ n in atTop, |onesR w n / n - condSum μ w n / n| <
      (ε : ℝ) :=
    fun ε hε => ae_tendsto_ones_sub_condSum_step4 μ (ε : ℝ) (by exact_mod_cast hε)
  have h2 : ∀ᵐ w ∂μ, ∀ ε : ℚ, 0 < ε → ∀ᶠ n in atTop, |onesR w n / n - condSum μ w n / n| <
      (ε : ℝ) := by
    rw [ae_all_iff]
    intro ε
    by_cases hε : 0 < ε
    · filter_upwards [h1 ε hε] with w hw h_eps
      exact hw
    · filter_upwards [] with w h_eps
      contradiction
  filter_upwards [h2] with w hw
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hε
  have hq0 : 0 < q := by exact_mod_cast hq1
  have h3 := hw q hq0
  obtain ⟨N, hN⟩ := eventually_atTop.mp h3
  exact ⟨N, fun n hn => by
    rw [dist_zero_right]
    exact lt_trans (hN n hn) hq2⟩

/-! ### The law of large numbers for subsequences -/

open Classical in
/-- The positions below `T` selected by `R` from `ω`. -/
noncomputable def selectedPositions (R : Set BitString) (w : CantorSeq) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter fun i => cantorPrefix w i ∈ R

/-- The number of ones among the terms at the positions selected below `T`. -/
noncomputable def selectedOnes (R : Set BitString) (w : CantorSeq) (T : ℕ) : ℝ :=
  ∑ i ∈ selectedPositions R w T, bitVal (w i)

/-- The sum of the conditional probabilities of `1` at the positions selected below `T`. -/
noncomputable def selectedCondSum (μ : Measure CantorSeq) (R : Set BitString) (w : CantorSeq)
    (T : ℕ) : ℝ :=
  ∑ i ∈ selectedPositions R w T, condOne μ (cantorPrefix w i)

/-- `condOne` is a probability. -/
private lemma measure_selected_abs_sub_gt_le_condOne_mem_Icc (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (x : BitString) :
    0 ≤ condOne μ x ∧ condOne μ x ≤ 1 := by
  have hnn : ∀ y, 0 ≤ massR μ y := fun y => ENNReal.toReal_nonneg
  have hadd := massR_add (π := μ) x
  have hdef : condOne μ x = massR μ (x ++ [true]) / massR μ x := rfl
  rw [hdef]
  refine ⟨div_nonneg (hnn _) (hnn _), ?_⟩
  rcases (hnn x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · rw [div_le_one hpos]
    linarith [hnn (x ++ [false])]

/-- The child `x1` carries the conditional share of the mass of `x`. -/
private lemma measure_selected_abs_sub_gt_le_condOne_mul_massR (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (x : BitString) :
    condOne μ x * massR μ x = massR μ (x ++ [true]) := by
  have hnn : ∀ y, 0 ≤ massR μ y := fun y => ENNReal.toReal_nonneg
  have hadd := massR_add (π := μ) x
  have hdef : condOne μ x = massR μ (x ++ [true]) / massR μ x := rfl
  rcases (hnn x).eq_or_lt with h0 | hpos
  · have h1 : massR μ (x ++ [true]) = 0 := by
      linarith [hnn (x ++ [false]), hnn (x ++ [true])]
    rw [← h0, h1, mul_zero]
  · rw [hdef]; exact div_mul_cancel₀ _ hpos.ne'

/-- The child `x0` carries the complementary share. -/
private lemma measure_selected_abs_sub_gt_le_one_sub_condOne_mul_massR (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (x : BitString) :
    (1 - condOne μ x) * massR μ x = massR μ (x ++ [false]) := by
  have h1 := measure_selected_abs_sub_gt_le_condOne_mul_massR μ x
  have hadd := massR_add (π := μ) x
  rw [sub_mul, one_mul, h1]
  linarith

/-- A single weighted factor is nonnegative. -/
private lemma measure_selected_abs_sub_gt_le_one_add_mul_sub_nonneg {u p : ℝ} (hu : |u| ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ 1 + u * ((if b then (1 : ℝ) else 0) - p) := by
  obtain ⟨hu0, hu1⟩ := abs_le.mp hu
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    nlinarith
  · simp only [ite_true]
    nlinarith

/-- The weighted tilted product on `x ++ [b]` is the product on `x` times one more factor. -/
private lemma measure_selected_abs_sub_gt_le_tilt_prod_append (μ : Measure CantorSeq)
    (s : BitString → ℝ) (t : ℝ) (x : BitString) (b : Bool) :
    ∏ i ∈ Finset.range (x ++ [b]).length,
        (1 + t * s ((x ++ [b]).take i) * ((if (x ++ [b]).getD i false then (1 : ℝ) else 0) -
          condOne μ ((x ++ [b]).take i))) =
      (∏ i ∈ Finset.range x.length,
        (1 + t * s (x.take i) * ((if x.getD i false then (1 : ℝ) else 0) - condOne μ (x.take i)))) *
        (1 + t * s x * ((if b then (1 : ℝ) else 0) - condOne μ x)) := by
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < x.length := Finset.mem_range.mp hi
    rw [List.getD_append _ _ _ _ hi', List.take_append_of_le_length hi'.le]
  · have h1 : (x ++ [b]).getD x.length false = b := by simp
    have h2 : (x ++ [b]).take x.length = x := by simp
    rw [h1, h2]

/-- Step 1 of the proof of `measure_selected_abs_sub_gt_le`: for predictable weights `s`
with values in `[0, 1]` and `|t| ≤ 1`, the tilted product
`∏ i < |x|, (1 + t * s(x↾i) * (x_i - condOne μ (x↾i)))` is a `μ`-martingale. -/
private lemma measure_selected_abs_sub_gt_le_martingale (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (s : BitString → ℝ) (hs : ∀ y, 0 ≤ s y ∧ s y ≤ 1) {t : ℝ}
    (ht : |t| ≤ 1) :
    IsMartingale μ (fun x : BitString => ∏ i ∈ Finset.range x.length,
      (1 + t * s (x.take i) * ((if x.getD i false then (1 : ℝ) else 0) - condOne μ (x.take i)))) :=
          by
  have hfac : ∀ (x : BitString) (b : Bool),
      0 ≤ 1 + t * s x * ((if b then (1 : ℝ) else 0) - condOne μ x) := by
    intro x b
    obtain ⟨h0, h1⟩ := measure_selected_abs_sub_gt_le_condOne_mem_Icc μ x
    obtain ⟨hs0, hs1⟩ := hs x
    have hu : |t * s x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hs0]
      calc |t| * s x ≤ 1 * 1 := mul_le_mul ht hs1 hs0 (by norm_num)
        _ = 1 := by norm_num
    exact measure_selected_abs_sub_gt_le_one_add_mul_sub_nonneg hu h0 h1 b
  refine ⟨⟨fun x => ?_, fun x => ?_⟩, ?_⟩
  · exact Finset.prod_nonneg fun i _ => hfac (x.take i) (x.getD i false)
  · show (∏ i ∈ Finset.range x.length,
        (1 + t * s (x.take i) * ((if x.getD i false then (1 : ℝ) else 0) - condOne μ (x.take i)))) *
        massR μ x =
      (∏ i ∈ Finset.range (x ++ [false]).length,
        (1 + t * s ((x ++ [false]).take i) * ((if (x ++ [false]).getD i false then (1 : ℝ) else 0) -
          condOne μ ((x ++ [false]).take i)))) * massR μ (x ++ [false]) +
      (∏ i ∈ Finset.range (x ++ [true]).length,
        (1 + t * s ((x ++ [true]).take i) * ((if (x ++ [true]).getD i false then (1 : ℝ) else 0) -
          condOne μ ((x ++ [true]).take i)))) * massR μ (x ++ [true])
    rw [measure_selected_abs_sub_gt_le_tilt_prod_append μ s t x false,
      measure_selected_abs_sub_gt_le_tilt_prod_append μ s t x true,
      ← measure_selected_abs_sub_gt_le_one_sub_condOne_mul_massR μ x,
      ← measure_selected_abs_sub_gt_le_condOne_mul_massR μ x]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    ring
  · show ∏ i ∈ Finset.range ([] : BitString).length,
        (1 + t * s (([] : BitString).take i) * ((if ([] : BitString).getD i false then (1 : ℝ) else
          0) -
          condOne μ (([] : BitString).take i))) = 1
    simp

/-- One-term inequality: `exp (h - h²) ≤ 1 + h` for `|h| ≤ 1/2`. -/
private lemma measure_selected_abs_sub_gt_le_exp_sub_sq_le_one_add {h : ℝ} (hh : |h| ≤ 1 / 2) :
    Real.exp (h - h ^ 2) ≤ 1 + h := by
  have hh' := abs_le.mp hh
  rcases le_total 0 h with h0 | h0
  · have hpos : 0 < 1 - h + h ^ 2 := by nlinarith
    have h1 : 1 - h + h ^ 2 ≤ Real.exp (-(h - h ^ 2)) := by
      have := Real.add_one_le_exp (-(h - h ^ 2))
      linarith
    have h2 : Real.exp (h - h ^ 2) * Real.exp (-(h - h ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 1 ≤ (1 + h) * (1 - h + h ^ 2) := by
      have h3 : (1 + h) * (1 - h + h ^ 2) = 1 + h ^ 3 := by ring
      rw [h3]; nlinarith [pow_nonneg h0 3]
    have h5 : Real.exp (h - h ^ 2) * (1 - h + h ^ 2) ≤ (1 + h) * (1 - h + h ^ 2) := by
      calc Real.exp (h - h ^ 2) * (1 - h + h ^ 2)
          ≤ Real.exp (h - h ^ 2) * Real.exp (-(h - h ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
        _ ≤ (1 + h) * (1 - h + h ^ 2) := h4
    exact le_of_mul_le_mul_right h5 hpos
  · obtain ⟨s, rfl⟩ : ∃ s, h = -s := ⟨-h, by ring⟩
    have hs0 : 0 ≤ s := by linarith
    have hs1 : s ≤ 1 / 2 := by linarith
    have hy0 : 0 ≤ s + s ^ 2 := by positivity
    have h1 : 1 + (s + s ^ 2) + (s + s ^ 2) ^ 2 / 2 ≤ Real.exp (s + s ^ 2) :=
      Real.quadratic_le_exp_of_nonneg hy0
    have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
    have hs3 : s ^ 3 ≤ 1 / 8 := by nlinarith [sq_nonneg s]
    have h4 : 1 ≤ (1 - s) * (1 + (s + s ^ 2) + (s + s ^ 2) ^ 2 / 2) := by
      have h5 : 0 ≤ s ^ 2 / 2 * (1 - s - s ^ 2 - s ^ 3) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [h5]
    have h2 : Real.exp (-(s + s ^ 2)) * Real.exp (s + s ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : Real.exp (-(s + s ^ 2)) * Real.exp (s + s ^ 2) ≤ (1 - s) * Real.exp (s + s ^ 2) :=
      calc Real.exp (-(s + s ^ 2)) * Real.exp (s + s ^ 2) = 1 := h2
        _ ≤ (1 - s) * (1 + (s + s ^ 2) + (s + s ^ 2) ^ 2 / 2) := h4
        _ ≤ (1 - s) * Real.exp (s + s ^ 2) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h6 : Real.exp (-(s + s ^ 2)) ≤ 1 - s := le_of_mul_le_mul_right h5 (Real.exp_pos _)
    have e1 : -s - (-s) ^ 2 = -(s + s ^ 2) := by ring
    rw [e1]
    linarith

/-- Step 2 of the proof of `measure_selected_abs_sub_gt_le`: for predictable weights `s`
with values in `[0, 1]` and `|t| ≤ 1/2`, the tilted product dominates
`exp (t * ∑ s_i (x_i - p_i) - t^2 * ∑ s_i)`. -/
private lemma measure_selected_abs_sub_gt_le_exp_le (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (s : BitString → ℝ) (hs : ∀ y, 0 ≤ s y ∧ s y ≤ 1) {t : ℝ}
    (ht : |t| ≤ 1 / 2) (x : BitString) :
    Real.exp (t * ∑ i ∈ Finset.range x.length, s (x.take i) *
          ((if x.getD i false then (1 : ℝ) else 0) - condOne μ (x.take i)) -
        t ^ 2 * ∑ i ∈ Finset.range x.length, s (x.take i)) ≤
      ∏ i ∈ Finset.range x.length,
        (1 + t * s (x.take i) * ((if x.getD i false then (1 : ℝ) else 0) - condOne μ (x.take i))) :=
            by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton y b ih =>
    obtain ⟨hp0, hp1⟩ := measure_selected_abs_sub_gt_le_condOne_mem_Icc μ y
    obtain ⟨hσ0, hσ1⟩ := hs y
    have hlen : (y ++ [b]).length = y.length + 1 := by simp
    have hsum1 : ∑ i ∈ Finset.range (y ++ [b]).length, s ((y ++ [b]).take i) *
          ((if (y ++ [b]).getD i false then (1 : ℝ) else 0) - condOne μ ((y ++ [b]).take i)) =
        ∑ i ∈ Finset.range y.length, s (y.take i) *
          ((if y.getD i false then (1 : ℝ) else 0) - condOne μ (y.take i)) +
        s y * ((if b then (1 : ℝ) else 0) - condOne μ y) := by
      rw [hlen, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < y.length := Finset.mem_range.mp hi
        rw [List.getD_append _ _ _ _ hi', List.take_append_of_le_length hi'.le]
      · have h1 : (y ++ [b]).getD y.length false = b := by simp
        have h2 : (y ++ [b]).take y.length = y := by simp
        rw [h1, h2]
    have hsum2 : ∑ i ∈ Finset.range (y ++ [b]).length, s ((y ++ [b]).take i) =
        ∑ i ∈ Finset.range y.length, s (y.take i) + s y := by
      rw [hlen, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [List.take_append_of_le_length (Finset.mem_range.mp hi).le]
      · have h2 : (y ++ [b]).take y.length = y := by simp
        rw [h2]
    have hprod : ∏ i ∈ Finset.range (y ++ [b]).length,
        (1 + t * s ((y ++ [b]).take i) * ((if (y ++ [b]).getD i false then (1 : ℝ) else 0) -
          condOne μ ((y ++ [b]).take i))) =
        (∏ i ∈ Finset.range y.length,
          (1 + t * s (y.take i) * ((if y.getD i false then (1 : ℝ) else 0) -
            condOne μ (y.take i)))) *
        (1 + t * s y * ((if b then (1 : ℝ) else 0) - condOne μ y)) :=
      measure_selected_abs_sub_gt_le_tilt_prod_append μ s t y b
    rw [hsum1, hsum2, hprod]
    -- abstract the pieces
    generalize hP : (∏ i ∈ Finset.range y.length,
        (1 + t * s (y.take i) * ((if y.getD i false then (1 : ℝ) else 0) -
          condOne μ (y.take i)))) = P at ih ⊢
    generalize hS1 : (∑ i ∈ Finset.range y.length, s (y.take i) *
        ((if y.getD i false then (1 : ℝ) else 0) - condOne μ (y.take i))) = S1 at ih ⊢
    generalize hS2 : (∑ i ∈ Finset.range y.length, s (y.take i)) = S2 at ih ⊢
    generalize hp : condOne μ y = p at hp0 hp1 ⊢
    generalize hσ : s y = σ at hσ0 hσ1 ⊢
    generalize hβ : (if b then (1 : ℝ) else 0) = β
    have hβ0 : 0 ≤ β := by rw [← hβ]; split_ifs <;> norm_num
    have hβ1 : β ≤ 1 := by rw [← hβ]; split_ifs <;> norm_num
    have habs : |β - p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hsq : (β - p) ^ 2 ≤ 1 := by nlinarith
    have hσ2 : σ ^ 2 ≤ σ := by nlinarith
    have hh : |t * σ * (β - p)| ≤ 1 / 2 := by
      have hσabs : |σ| ≤ 1 := by rw [abs_of_nonneg hσ0]; exact hσ1
      rw [abs_mul, abs_mul]
      calc |t| * |σ| * |β - p| ≤ 1 / 2 * 1 * 1 :=
            mul_le_mul (mul_le_mul ht hσabs (abs_nonneg _) (by norm_num)) habs (abs_nonneg _)
              (by norm_num)
        _ = 1 / 2 := by norm_num
    have hh2 : (t * σ * (β - p)) ^ 2 ≤ t ^ 2 * σ := by
      have h1 : (t * σ * (β - p)) ^ 2 = t ^ 2 * (σ ^ 2 * (β - p) ^ 2) := by ring
      have h2 : σ ^ 2 * (β - p) ^ 2 ≤ σ := by
        calc σ ^ 2 * (β - p) ^ 2 ≤ σ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hsq (sq_nonneg σ)
          _ = σ ^ 2 := by ring
          _ ≤ σ := hσ2
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg t)
    have hB1 := measure_selected_abs_sub_gt_le_exp_sub_sq_le_one_add hh
    have hexp : Real.exp (t * σ * (β - p) - t ^ 2 * σ) ≤ 1 + t * σ * (β - p) :=
      (Real.exp_le_exp.mpr (by linarith)).trans hB1
    have hsplit : t * (S1 + σ * (β - p)) - t ^ 2 * (S2 + σ) =
        (t * S1 - t ^ 2 * S2) + (t * σ * (β - p) - t ^ 2 * σ) := by
      ring
    rw [hsplit, Real.exp_add]
    exact mul_le_mul ih hexp (Real.exp_pos _).le ((Real.exp_pos _).le.trans ih)

open Classical in
/-- Step 3 of the proof of `measure_selected_abs_sub_gt_le`: the weights `s` select
exactly the first `n` selected positions. -/
private lemma measure_selected_abs_sub_gt_le_weights (R : Set BitString) {n : ℕ}
    (s : BitString → ℝ)
    (hs : ∀ y, s y = if y ∈ R ∧ ((Finset.range y.length).filter (fun j => y.take j ∈ R)).card < n
      then 1 else 0)
    (w : CantorSeq) {T : ℕ} (hT : (selectedPositions R w T).card = n) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range T, s (cantorPrefix w i) * f i = ∑ i ∈ selectedPositions R w T, f i := by
  unfold selectedPositions at hT ⊢
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiT : i < T := Finset.mem_range.mp hi
  rw [hs]
  simp only [cantorPrefix_length]
  by_cases hR : cantorPrefix w i ∈ R
  · have hlt : ((Finset.range i).filter (fun j => (cantorPrefix w i).take j ∈ R)).card < n := by
      have hsub : insert i ((Finset.range i).filter (fun j => cantorPrefix w j ∈ R)) ⊆
          (Finset.range T).filter (fun j => cantorPrefix w j ∈ R) := by
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Finset.mem_filter.mpr ⟨hi, hR⟩
        · obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hj1) hiT), hj2⟩
      have hnot : i ∉ (Finset.range i).filter (fun j => cantorPrefix w j ∈ R) := by simp
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hcard
      have heq : (Finset.range i).filter (fun j => (cantorPrefix w i).take j ∈ R) =
          (Finset.range i).filter (fun j => cantorPrefix w j ∈ R) := by
        refine Finset.filter_congr fun j hj => ?_
        rw [cantorPrefix_take w j i (Finset.mem_range.mp hj).le]
      rw [heq]
      omega
    rw [ite_eq_left ⟨hR, hlt⟩, ite_eq_left hR, one_mul]
  · rw [ite_eq_right (fun h => hR h.1), ite_eq_right hR, zero_mul]

open Classical in
/-- The signed one-sided bound (assembly of Steps 1-3 with Ville's inequality). -/
private lemma measure_selected_abs_sub_gt_le_signed_gt_le (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (R : Set BitString) {n : ℕ} (hn : 0 < n) {d : ℝ} (hd : 0 ≤ d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    μ {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < σ * (selectedOnes R w T - selectedCondSum μ R w T)} ≤
      ENNReal.ofReal (Real.exp (-d ^ 2 / (4 * n))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨s, hs_def⟩ : ∃ s : BitString → ℝ, ∀ y, s y =
      if y ∈ R ∧ ((Finset.range y.length).filter (fun j => y.take j ∈ R)).card < n
      then 1 else 0 := ⟨_, fun _ => rfl⟩
  have hs : ∀ y, 0 ≤ s y ∧ s y ≤ 1 := fun y => by
    rw [hs_def]; split_ifs <;> norm_num
  by_cases hdn : d ≤ n
  · have ht0 : 0 ≤ d / (2 * n) := by positivity
    have ht : |σ * (d / (2 * n))| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg ht0, hσ1, one_mul, div_le_iff₀ (by positivity)]
      linarith
    have hM := measure_selected_abs_sub_gt_le_martingale μ s hs
      (t := σ * (d / (2 * n))) (le_trans ht (by norm_num))
    have hc : 0 < Real.exp (d ^ 2 / (4 * n)) := Real.exp_pos _
    have hV := measure_exists_ge_le hM.toIsFairCapital hc
    rw [hM.init] at hV
    have e : 1 / Real.exp (d ^ 2 / (4 * n)) = Real.exp (-d ^ 2 / (4 * n)) := by
      rw [one_div, ← Real.exp_neg]; congr 1; ring
    rw [e] at hV
    refine le_trans (measure_mono ?_) hV
    rintro w ⟨T, hT, hw⟩
    refine ⟨T, ?_⟩
    have h2 := measure_selected_abs_sub_gt_le_exp_le μ s hs ht (cantorPrefix w T)
    have hlen : (cantorPrefix w T).length = T := cantorPrefix_length w T
    have htake : ∀ i ∈ Finset.range T, (cantorPrefix w T).take i = cantorPrefix w i :=
      fun i hi => cantorPrefix_take w i T (Finset.mem_range.mp hi).le
    have hget : ∀ i ∈ Finset.range T, (cantorPrefix w T).getD i false = w i := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact Finset.mem_range.mp hi),
        cantorPrefix_getElem]
    have hA : ∑ i ∈ Finset.range T, s (cantorPrefix w i) *
        ((if w i then (1 : ℝ) else 0) - condOne μ (cantorPrefix w i)) =
        selectedOnes R w T - selectedCondSum μ R w T := by
      rw [measure_selected_abs_sub_gt_le_weights R s hs_def w hT
        (fun i => (if w i then (1 : ℝ) else 0) - condOne μ (cantorPrefix w i))]
      unfold selectedOnes selectedCondSum bitVal
      rw [Finset.sum_sub_distrib]
    have hB : ∑ i ∈ Finset.range T, s (cantorPrefix w i) = n := by
      have := measure_selected_abs_sub_gt_le_weights R s hs_def w hT (fun _ => (1 : ℝ))
      simpa [hT] using this
    have e1 : ∑ i ∈ Finset.range T, s ((cantorPrefix w T).take i) *
        ((if (cantorPrefix w T).getD i false then (1 : ℝ) else 0) -
          condOne μ ((cantorPrefix w T).take i)) =
        ∑ i ∈ Finset.range T, s (cantorPrefix w i) *
        ((if w i then (1 : ℝ) else 0) - condOne μ (cantorPrefix w i)) :=
      Finset.sum_congr rfl fun i hi => by rw [htake i hi, hget i hi]
    have e2 : ∑ i ∈ Finset.range T, s ((cantorPrefix w T).take i) =
        ∑ i ∈ Finset.range T, s (cantorPrefix w i) :=
      Finset.sum_congr rfl fun i hi => by rw [htake i hi]
    rw [hlen] at h2 ⊢
    rw [e1, e2, hA, hB] at h2
    refine le_trans ?_ h2
    apply Real.exp_le_exp.mpr
    have hw' : d < σ * (selectedOnes R w T - selectedCondSum μ R w T) := hw
    have h1 : σ * (d / (2 * n)) * (selectedOnes R w T - selectedCondSum μ R w T) =
        d / (2 * n) * (σ * (selectedOnes R w T - selectedCondSum μ R w T)) := by ring
    have h2' : d / (2 * n) * d ≤
        d / (2 * n) * (σ * (selectedOnes R w T - selectedCondSum μ R w T)) :=
      mul_le_mul_of_nonneg_left hw'.le ht0
    have h3 : (σ * (d / (2 * n))) ^ 2 * (n : ℝ) = d ^ 2 / (4 * n) := by
      have : (σ * (d / (2 * n))) ^ 2 * (n : ℝ) = σ ^ 2 * (n * (d / (2 * n)) ^ 2) := by ring
      rw [this, hσ2]; field_simp; ring
    have h4 : d / (2 * n) * d = d ^ 2 / (2 * n) := by ring
    have h5 : d ^ 2 / (2 * n) = d ^ 2 / (4 * n) + d ^ 2 / (4 * n) := by field_simp; ring
    linarith
  · push Not at hdn
    have hempty : {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < σ * (selectedOnes R w T - selectedCondSum μ R w T)} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_lt]
      intro T hT
      have hon : ∀ i ∈ selectedPositions R w T, 0 ≤ bitVal (w i) ∧ bitVal (w i) ≤ 1 := fun i _ => by
        unfold bitVal; split_ifs <;> norm_num
      have hco : ∀ i ∈ selectedPositions R w T,
          0 ≤ condOne μ (cantorPrefix w i) ∧ condOne μ (cantorPrefix w i) ≤ 1 :=
        fun i _ => measure_selected_abs_sub_gt_le_condOne_mem_Icc μ _
      have h1 : selectedOnes R w T ≤ n := by
        calc selectedOnes R w T ≤ ∑ i ∈ selectedPositions R w T, (1 : ℝ) :=
              Finset.sum_le_sum fun i hi => (hon i hi).2
          _ = n := by simp [hT]
      have h2 : 0 ≤ selectedOnes R w T := Finset.sum_nonneg fun i hi => (hon i hi).1
      have h3 : 0 ≤ selectedCondSum μ R w T := Finset.sum_nonneg fun i hi => (hco i hi).1
      have h4 : selectedCondSum μ R w T ≤ n := by
        calc selectedCondSum μ R w T ≤ ∑ i ∈ selectedPositions R w T, (1 : ℝ) :=
              Finset.sum_le_sum fun i hi => (hco i hi).2
          _ = n := by simp [hT]
      rcases hσ with rfl | rfl <;> linarith
    rw [hempty]; simp

/-- **SUV Theorem 200, p. 304.**  For an arbitrary measure `μ` and an arbitrary set `R`, the set of
`ω` such that `S_R(ω)` has at least `n` terms and, for its first `n` selected positions, the number
of ones and the sum of conditional probabilities differ by more than `d`, has measure at most
`2 e^{-d² / 4n}`.

The first `n` selected positions are those below any `T` with exactly `n` selected positions below
it; the sums do not depend on the choice of such `T`.  The published display writes `i_n` for the
last position, which is `i_{n-1}`: the list is said to have `n` terms. -/
theorem measure_selected_abs_sub_gt_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    (R : Set BitString) {n : ℕ} (hn : 0 < n) {d : ℝ} (hd : 0 ≤ d) :
    μ {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < |selectedOnes R w T - selectedCondSum μ R w T|} ≤
      ENNReal.ofReal (2 * Real.exp (-d ^ 2 / (4 * n))) := by
  have hset : {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < |selectedOnes R w T - selectedCondSum μ R w T|} =
      {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < 1 * (selectedOnes R w T - selectedCondSum μ R w T)} ∪
      {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < (-1) * (selectedOnes R w T - selectedCondSum μ R w T)} := by
    ext w
    simp only [Set.mem_union, Set.mem_ofPred_eq, one_mul, neg_mul]
    constructor
    · rintro ⟨T, hT, h⟩
      rcases lt_abs.mp h with h | h
      · exact Or.inl ⟨T, hT, h⟩
      · exact Or.inr ⟨T, hT, h⟩
    · rintro (⟨T, hT, h⟩ | ⟨T, hT, h⟩)
      · exact ⟨T, hT, lt_abs.mpr (Or.inl h)⟩
      · exact ⟨T, hT, lt_abs.mpr (Or.inr h)⟩
  rw [hset]
  calc _ ≤ μ {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < 1 * (selectedOnes R w T - selectedCondSum μ R w T)} +
      μ {w | ∃ T, (selectedPositions R w T).card = n ∧
        d < (-1) * (selectedOnes R w T - selectedCondSum μ R w T)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-d ^ 2 / (4 * n))) +
          ENNReal.ofReal (Real.exp (-d ^ 2 / (4 * n))) :=
        add_le_add (measure_selected_abs_sub_gt_le_signed_gt_le μ R hn hd (Or.inl rfl))
          (measure_selected_abs_sub_gt_le_signed_gt_le μ R hn hd (Or.inr rfl))
    _ = ENNReal.ofReal (2 * Real.exp (-d ^ 2 / (4 * n))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-- The effective convergence hypothesis of Theorems 201 and 202, p. 304: a uniformly computable
sequence of nonnegative reals with a computable convergence rate to `q`.  The bounds `p_i ≤ 1` and
`q ∈ (0, 1)` are separate hypotheses of those theorems, not fields of this structure. -/
structure ConvergesComputably (p : ℕ → NNReal) (q : ℝ) : Prop where
  computable : IsComputableProbSeq p
  rate : ∃ N : ℚ → ℕ, Computable N ∧ ∀ ε : ℚ, 0 < ε → ∀ i, N ε ≤ i → |(p i : ℝ) - q| < ε

end Kolmogorov.FrequencyGames
