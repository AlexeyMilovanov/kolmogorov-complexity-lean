/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Path
import KolmogorovMathlib.MDLPrediction.Expectation.Layers
import KolmogorovMathlib.MDLPrediction.Expectation.Tonelli
import KolmogorovMathlib.MDLPrediction.Analysis.Series

/-!
# Expected squared error for an effective class

The least-budget layer includes both a budget and minimality among smaller natural
budgets. The measure of paths with no budget is zero. The class predictor uses the
same class minimizer choice at every cylinder throughout the expectation.
Blueprint nodes: `enum:class-layers`, `enum:theorem10`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-! ## Least-budget layers -/

/-- Genuine least-budget layer; no default selector value enters its membership.
Blueprint node `enum:class-layers`. -/
def classBudgetLayer (P : Measure CantorSeq) (d : ℕ) : Set CantorSeq :=
  {w | PathBudget P w d ∧ ∀ j < d, ¬ PathBudget P w j}

/-- The pathwise polynomial bound applies on each genuine layer; those layers
cover almost every path and have geometric mass. Blueprint node `enum:class-layers`. -/
private theorem classBudgetLayer_eq_leastBudget (P : Measure CantorSeq) (d : ℕ) :
    classBudgetLayer P d = {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d} := by
  ext w
  simp only [classBudgetLayer, Set.mem_ofPred_eq]
  unfold leastBudget
  classical
  constructor
  · rintro ⟨h1, h2⟩
    have h : ∃ D, PathBudget P w D := ⟨d, h1⟩
    refine ⟨h, ?_⟩
    split_ifs
    · rw [Nat.find_eq_iff]
      exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    split_ifs at h2
    · rw [Nat.find_eq_iff] at h2
      exact h2

/-- Almost every path belongs to a least-budget layer. -/
private theorem ae_mem_classBudgetLayer (P : Measure CantorSeq) [IsProbabilityMeasure P] :
    ∀ᵐ w ∂P, ∃ d : ℕ, w ∈ classBudgetLayer P d := by
  have h_ae := ae_exists_budget P
  filter_upwards [h_ae] with w h_ex
  use leastBudget P w
  rw [classBudgetLayer_eq_leastBudget]
  exact ⟨h_ex, rfl⟩

/-- A positive least-budget layer has geometric mass. -/
private theorem classBudgetLayer_measure_le (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d) :
    P (classBudgetLayer P d) ≤ (2 : ℝ≥0∞)⁻¹ ^ (d - 1) := by
  rw [classBudgetLayer_eq_leastBudget]
  exact exp_budget_layers P d hd
/-- Least-budget layers cover almost every path, have geometric mass, and inherit
the pathwise polynomial error bound. Blueprint node `enum:class-layers`. -/
theorem enum_class_layers (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (P : Measure CantorSeq)
    [IsProbabilityMeasure P]
    (choose : BitString → Measure CantorSeq)
    (C : ℝ) (e : ℕ)
    (h9 : ∀ w D, PathBudget P w D →
      classPathError U hU A P choose w false ≤
        C * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) ^ e) :
    (∀ᵐ w ∂P, ∃ d : ℕ, w ∈ classBudgetLayer P d) ∧
      (∀ d ≥ 1, P (classBudgetLayer P d) ≤ (2 : ℝ≥0∞)⁻¹ ^ (d - 1)) ∧
      ∀ d w, w ∈ classBudgetLayer P d →
        classPathError U hU A P choose w false ≤
          C * ((classComplexity U hU A P + d + 1 : ℕ) : ℝ) ^ e := by
  refine ⟨ae_mem_classBudgetLayer P, classBudgetLayer_measure_le P, ?_⟩
  intro d w hw
  exact h9 w d hw.1

/-! ## Expected squared error -/

/-- A path budget is a countable intersection of prefix conditions, hence measurable. -/
private theorem measurableSet_pathBudget (P : Measure CantorSeq)
    (D : ℕ) : MeasurableSet {w | PathBudget P w D} := by
  have hset : {w | PathBudget P w D} = ⋂ n, {w | universalContinuousSemimeasure
      (cantorPrefix w n) ≤ (2 : ℝ≥0∞) ^ D * cantorMass P (cantorPrefix w n)} := by
    ext w
    simp [PathBudget]
  rw [hset]
  exact MeasurableSet.iInter fun n =>
    measurableSet_le (measurable_comp_cantorPrefix n _)
      (measurable_comp_cantorPrefix n (fun x => (2 : ℝ≥0∞) ^ D * cantorMass P x))

/-- The least-budget layers are measurable. -/
private theorem measurableSet_classBudgetLayer (P : Measure CantorSeq)
    (d : ℕ) : MeasurableSet (classBudgetLayer P d) := by
  have hset : classBudgetLayer P d =
      {w | PathBudget P w d} ∩ ⋂ j ∈ Finset.range d, {w | PathBudget P w j}ᶜ := by
    ext w
    simp [classBudgetLayer]
  rw [hset]
  exact (measurableSet_pathBudget P d).inter
    (Finset.measurableSet_biInter _ fun j _ =>
      (measurableSet_pathBudget P j).compl)

/-- Corrected Theorem 10: weighted bit-zero class prediction error is summable
and bounded by a polynomial in relative complexity. Blueprint node `enum:theorem10`. -/
theorem class_expected_sq_polynomial (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ (C : ℝ) (e : ℕ), 0 < C ∧
      ∀ (P : Measure CantorSeq) (choose : BitString → Measure CantorSeq),
        P ∈ A.carrier → IsClassChoice U hU A choose →
          Summable (fun x : BitString => (cantorMass P x).toReal *
            (classPredictor U hU A choose x false -
              condProb (cantorMass P) x false) ^ 2) ∧
          (∑' x : BitString, (cantorMass P x).toReal *
            (classPredictor U hU A choose x false -
              condProb (cantorMass P) x false) ^ 2) ≤
            C * ((classComplexity U hU A P + 1 : ℕ) : ℝ) ^ e := by
  obtain ⟨C, e, hC, h9⟩ := class_pathwise_sq_polynomial U hU A
  obtain ⟨Ce, hCe, hmom⟩ := enum_poly_moment e
  refine ⟨2 * C * Ce, e, by positivity, ?_⟩
  intro P choose hP hchoose
  have : IsProbabilityMeasure P := by
    obtain ⟨i, hi⟩ := hP
    rw [← hi]
    exact (A.A i).probability
  set k := classComplexity U hU A P with hk
  set sq : BitString → ℝ := fun x =>
    (classPredictor U hU A choose x false - condProb (cantorMass P) x false) ^ 2 with hsq
  -- Tonelli for the ENNReal path sum
  obtain ⟨hT, -⟩ := integral_path_error_eq_tsum P
    (fun x => classPredictor U hU A choose x false)
  -- pathwise bound in ENNReal, using the summability conjunct of Theorem 9
  have hpath : ∀ w D, PathBudget P w D →
      ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ≤
        ENNReal.ofReal (C * ((k + D + 1 : ℕ) : ℝ) ^ e) := by
    intro w D hw
    obtain ⟨hs, hb⟩ := h9 P w D choose hP hw hchoose
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hb
  obtain ⟨hcover, hlayer, -⟩ := enum_class_layers U hU A P choose C e
    (fun w D hw => (h9 P w D choose hP hw hchoose).2)
  let c : ℕ → ℝ≥0∞ := fun d => ENNReal.ofReal (C * ((k + d + 1 : ℕ) : ℝ) ^ e)
  have hae : ∀ᵐ w ∂P, ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ≤
      ∑' d, (classBudgetLayer P d).indicator (fun _ => c d) w := by
    filter_upwards [hcover] with w hw
    obtain ⟨d, hd⟩ := hw
    calc ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ≤ c d := hpath w d hd.1
      _ = (classBudgetLayer P d).indicator (fun _ => c d) w :=
          (Set.indicator_of_mem hd (fun _ => c d)).symm
      _ ≤ ∑' d, (classBudgetLayer P d).indicator (fun _ => c d) w :=
          ENNReal.le_tsum (f := fun d => (classBudgetLayer P d).indicator (fun _ => c d) w) d
  have hPL : ∀ d, P (classBudgetLayer P d) ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ d := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [pow_zero, mul_one]
      exact prob_le_one.trans (by norm_num)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
      calc P (classBudgetLayer P (1 + m)) ≤ (2 : ℝ≥0∞)⁻¹ ^ (1 + m - 1) := hlayer _ hd
        _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ (1 + m) := by
          rw [Nat.add_sub_cancel_left, pow_add, pow_one, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hint : (∫⁻ w, ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ∂P) ≤
      ∑' d, c d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) := by
    calc (∫⁻ w, ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ∂P)
        ≤ ∫⁻ w, ∑' d, (classBudgetLayer P d).indicator (fun _ => c d) w ∂P :=
          lintegral_mono_ae hae
      _ = ∑' d, ∫⁻ w, (classBudgetLayer P d).indicator (fun _ => c d) w ∂P :=
          lintegral_tsum fun d => (measurable_const.indicator
            (measurableSet_classBudgetLayer P d)).aemeasurable
      _ = ∑' d, c d * P (classBudgetLayer P d) := by
          congr 1
          ext d
          exact lintegral_indicator_const (measurableSet_classBudgetLayer P d) _
      _ ≤ ∑' d, c d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) := ENNReal.tsum_le_tsum fun d => by
          gcongr
          exact hPL d
  have hser : ∑' d, c d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) ≤
      ENNReal.ofReal (2 * C * Ce * ((k + 1 : ℕ) : ℝ) ^ e) := by
    have hterm : ∀ d, c d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) =
        ENNReal.ofReal (2 * C * ((2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e)) := by
      intro d
      have h2 : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ d = ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ d) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      rw [h2, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun d => by positivity)
      (((hmom k).1).mul_left (2 * C))]
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_mul_left]
    calc 2 * C * ∑' d, (2 : ℝ)⁻¹ ^ d * ((k + d + 1 : ℕ) : ℝ) ^ e
        ≤ 2 * C * (Ce * ((k + 1 : ℕ) : ℝ) ^ e) := by
          gcongr
          exact (hmom k).2
      _ = 2 * C * Ce * ((k + 1 : ℕ) : ℝ) ^ e := by ring
  have hbound : (∑' x, cantorMass P x * ENNReal.ofReal (sq x)) ≤
      ENNReal.ofReal (2 * C * Ce * ((k + 1 : ℕ) : ℝ) ^ e) := by
    rw [← hT]
    exact hint.trans hser
  -- back to real numbers
  have hfin : ∀ x, cantorMass P x * ENNReal.ofReal (sq x) ≠ ⊤ := fun x =>
    ENNReal.mul_ne_top (measure_ne_top P _) ENNReal.ofReal_ne_top
  have hreal : (fun x => (cantorMass P x).toReal * sq x) =
      fun x => (cantorMass P x * ENNReal.ofReal (sq x)).toReal := by
    ext x
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hne : (∑' x, cantorMass P x * ENNReal.ofReal (sq x)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  refine ⟨?_, ?_⟩
  · change Summable (fun x => (cantorMass P x).toReal * sq x)
    rw [hreal]
    exact ENNReal.summable_toReal hne
  · change (∑' x, (cantorMass P x).toReal * sq x) ≤ _
    rw [hreal, ← ENNReal.tsum_toReal_eq hfin]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
end Kolmogorov.MDLPrediction
