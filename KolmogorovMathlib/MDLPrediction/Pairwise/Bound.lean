/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Pairwise.Product
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding

/-!
# Pairwise squared discrepancy on a positive cylinder

The finite sum ranges over positions strictly before the endpoint string. The
conditional after the endpoint is charged separately in selected-time arguments.
Blueprint nodes: `exp:pairwise`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal BigOperators

/-! ## Conditional products and their square budget -/

/-- The pairwise bit-zero square sum through a finite prefix.
Blueprint node `exp:pairwise`. -/
noncomputable def pairwiseError (P Q : Measure CantorSeq) (x : BitString) : ℝ :=
  ∑ i : Fin x.length,
    (condProb (cantorMass P) (x.take i.val) false -
      condProb (cantorMass Q) (x.take i.val) false) ^ 2

/-- Cylinder mass is the product of its realized conditional probabilities. -/
private lemma cantorMass_toReal_eq_condProb_prod (μ : MeasureTheory.Measure CantorSeq)
    [MeasureTheory.IsProbabilityMeasure μ] (x : Kolmogorov.BitString) :
    (Kolmogorov.cantorMass μ x).toReal = ∏ i : Fin x.length, Kolmogorov.condProb
        (Kolmogorov.cantorMass μ) (x.take i.val) (x[i.val]'i.isLt) := by
  induction x using List.reverseRecOn with
  | nil =>
    simp [(Kolmogorov.isContinuousTreeSemimeasure_cantorMass μ).1]
  | append_singleton y b ih =>
    rw [← Fin.prod_congr' _ (by simp : y.length + 1 = (y ++ [b]).length)]
    rw [Fin.prod_univ_castSucc]
    rw [← (Kolmogorov.isContinuousTreeSemimeasure_cantorMass μ).toReal_mul_condProb y b, ih]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      simp [List.take_append_of_le_length (Nat.le_of_lt i.isLt), List.getElem_append_left i.isLt]
    · simp

/-- A conditional along a positive cylinder lies in the interval (0, 1]. -/
private lemma condProb_pos_le_one_of_mass_pos (μ : MeasureTheory.Measure CantorSeq)
    [MeasureTheory.IsProbabilityMeasure μ]
    (x : Kolmogorov.BitString) (h : 0 < Kolmogorov.cantorMass μ x) (i : Fin x.length) :
    0 < Kolmogorov.condProb (Kolmogorov.cantorMass μ) (x.take i.val) (x[i.val]'i.isLt) ∧
    Kolmogorov.condProb (Kolmogorov.cantorMass μ) (x.take i.val) (x[i.val]'i.isLt) ≤ 1 := by
  have h_append : x.take i.val ++ [x[i.val]'i.isLt] = x.take (i.val + 1) := by
    rw [List.take_add_one, List.getElem?_eq_getElem i.isLt, Option.toList_some]
  have h_le1 : Kolmogorov.cantorMass μ (x.take (i.val + 1)) ≤ Kolmogorov.cantorMass μ
      (x.take i.val) := by
    rw [← h_append]
    apply MeasureTheory.measure_mono
    exact cantorCylinder_subset_of_prefix (List.prefix_append _ _)
  have h_pos1 : 0 < Kolmogorov.cantorMass μ (x.take (i.val + 1)) := by
    apply lt_of_lt_of_le h
    apply MeasureTheory.measure_mono
    exact cantorCylinder_subset_of_prefix (List.take_prefix _ _)
  have h_pos2 : 0 < Kolmogorov.cantorMass μ (x.take i.val) := by
    apply lt_of_lt_of_le h_pos1 h_le1
  constructor
  · unfold Kolmogorov.condProb
    rw [h_append]
    apply div_pos
    · exact ENNReal.toReal_pos h_pos1.ne' (MeasureTheory.measure_ne_top μ _)
    · exact ENNReal.toReal_pos h_pos2.ne' (MeasureTheory.measure_ne_top μ _)
  · unfold Kolmogorov.condProb
    rw [h_append]
    apply div_le_one_of_le₀
    · apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ _) h_le1
    · exact ENNReal.toReal_nonneg

/-- Positive endpoint masses and two budgets give a uniform pairwise square bound.
Blueprint node `exp:pairwise`. -/
theorem pairwise_prefix_sq_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Measure CantorSeq)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      IsComputableMeasure P → IsComputableMeasure Q →
        ∀ x : BitString, 0 < cantorMass P x → 0 < cantorMass Q x →
        ∀ D : ℕ,
          universalContinuousSemimeasure x ≤
            (2 : ℝ≥0∞) ^ D * cantorMass P x →
          universalContinuousSemimeasure x ≤
            (2 : ℝ≥0∞) ^ D * cantorMass Q x →
          pairwiseError P Q x ≤ C *
            ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + D + 1) := by
  obtain ⟨c, hc⟩ := meanTree_uniform_domination U hU
  use 8 * Real.log 2 * (c + 1 : ℝ)
  refine ⟨by positivity, ?_⟩
  intro P Q _ _ hPc hQc x hP hQ D hDP hDQ
  let kP := (computableMeasureComplexity U P).toNat
  let kQ := (computableMeasureComplexity U Q).toNat
  have hprod := exp_pair_product U c hc P Q hPc hQc x hP hQ D hDP hDQ
  have hA_P := cantorMass_toReal_eq_condProb_prod P x
  have hA_Q := cantorMass_toReal_eq_condProb_prod Q x
  simp only [hA_P, hA_Q] at hprod
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * (kP + kQ + c + D)) := one_le_pow₀ (by norm_num)
  have hsq := sum_sq_le_of_mean_product x.length
    (fun i => condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt))
    (fun i => condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt))
    ((2 : ℝ) ^ (2 * (kP + kQ + c + D)))
    (condProb_pos_le_one_of_mass_pos P x hP)
    (condProb_pos_le_one_of_mass_pos Q x hQ)
    hc1
    (by simpa [kP, kQ] using hprod)
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hsq
  push_cast at hsq
  unfold pairwiseError
  have hsum_eq : ∑ i : Fin x.length,
      (condProb (cantorMass P) (x.take ↑i) false -
        condProb (cantorMass Q) (x.take ↑i) false) ^ 2 =
      ∑ i : Fin x.length,
      (condProb (cantorMass P) (x.take ↑i) x[↑i] -
        condProb (cantorMass Q) (x.take ↑i) x[↑i]) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h_posP : 0 < cantorMass P (x.take i.val) := by
      apply lt_of_lt_of_le hP
      apply measure_mono
      exact cantorCylinder_subset_of_prefix (List.take_prefix _ _)
    have h_posQ : 0 < cantorMass Q (x.take i.val) := by
      apply lt_of_lt_of_le hQ
      apply measure_mono
      exact cantorCylinder_subset_of_prefix (List.take_prefix _ _)
    exact exp_zero_one P Q (x.take i.val) (x[i.val]'i.isLt) h_posP h_posQ
  rw [hsum_eq]
  refine hsq.trans ?_
  have hlog : 0 < Real.log 2 := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hs0 : (0 : ℝ) ≤ kP + kQ + D := by positivity
  nlinarith [mul_nonneg hlog.le (mul_nonneg hc0 hs0), mul_nonneg hlog.le hc0, mul_nonneg
      hlog.le hs0]

/-! ## Realized-bit conditionals -/

/-- The realized-bit square sum equals the bit-zero pairwise error. -/
private theorem realized_sq_sum_eq_pairwiseError
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (x : BitString)
    (hP : 0 < cantorMass P x) (hQ : 0 < cantorMass Q x) :
    (∑ i : Fin x.length,
      (condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) -
        condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) ^ 2) =
    pairwiseError P Q x := by
  unfold pairwiseError
  apply Finset.sum_congr rfl
  intro i _
  have hi_P : 0 < cantorMass P (x.take i.val) := by
    apply lt_of_lt_of_le hP
    apply measure_mono
    exact cantorCylinder_subset_of_prefix (List.take_prefix i.val x)
  have hi_Q : 0 < cantorMass Q (x.take i.val) := by
    apply lt_of_lt_of_le hQ
    apply measure_mono
    exact cantorCylinder_subset_of_prefix (List.take_prefix i.val x)
  exact (exp_zero_one P Q (x.take i.val) (x[i.val]'i.isLt) hi_P hi_Q).symm

/-- The same pairwise bound holds for realized-bit conditionals.
Blueprint node `exp:pairwise`. -/
theorem pairwise_realized_sq_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Measure CantorSeq)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      IsComputableMeasure P → IsComputableMeasure Q →
        ∀ x : BitString, 0 < cantorMass P x → 0 < cantorMass Q x →
        ∀ D : ℕ,
          universalContinuousSemimeasure x ≤
            (2 : ℝ≥0∞) ^ D * cantorMass P x →
          universalContinuousSemimeasure x ≤
            (2 : ℝ≥0∞) ^ D * cantorMass Q x →
          (∑ i : Fin x.length,
            (condProb (cantorMass P) (x.take i.val) (x[i.val]'i.isLt) -
              condProb (cantorMass Q) (x.take i.val) (x[i.val]'i.isLt)) ^ 2) ≤
            C * ((computableMeasureComplexity U P).toNat +
              (computableMeasureComplexity U Q).toNat + D + 1) := by
  obtain ⟨C, hC_pos, hC⟩ := pairwise_prefix_sq_bound U hU
  use C, hC_pos
  intro P Q _ _ hP_comp hQ_comp x hPx hQx D hDP hDQ
  rw [realized_sq_sum_eq_pairwiseError P Q x hPx hQx]
  exact hC P Q hP_comp hQ_comp x hPx hQx D hDP hDQ

end Kolmogorov.MDLPrediction
