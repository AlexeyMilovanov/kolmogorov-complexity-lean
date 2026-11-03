/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Pairwise.Bound
import KolmogorovMathlib.MDLPrediction.Random.Criteria
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Merging on paths random for two computable measures

Two random-path budgets and the pairwise bound give square summability, hence
convergence for both bit conditionals.

Blueprint nodes: `rand:vovk`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- Pairwise error on a path prefix is the finite sum of conditional discrepancies. -/
private lemma pairwiseError_prefix_eq_sum_range (P Q : Measure CantorSeq) (w : CantorSeq) (N : ℕ) :
  pairwiseError P Q (cantorPrefix w N) = ∑ i ∈ Finset.range N,
    (condProb (cantorMass P) (cantorPrefix w i) false -
      condProb (cantorMass Q) (cantorPrefix w i) false) ^ 2 := by
  unfold pairwiseError
  have H := Fin.sum_univ_eq_sum_range (fun (i:ℕ) => (condProb (cantorMass P)
      ((cantorPrefix w N).take i) false -
      condProb (cantorMass Q) ((cantorPrefix w N).take i) false) ^ 2) (cantorPrefix w N).length
  rw [H]
  have hl : (cantorPrefix w N).length = N := cantorPrefix_length w N
  rw [hl]
  apply Finset.sum_congr rfl
  intro i hi
  have H2 : (cantorPrefix w N).take i = cantorPrefix w i := by
    rw [Finset.mem_range] at hi
    exact cantorPrefix_take w i N hi.le
  rw [H2]

/-- Two common natural budgets quantitatively bound the pairwise square series.
Blueprint node `rand:vovk`. -/
theorem vovk_merging_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Measure CantorSeq)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
        IsComputableMeasure P → IsComputableMeasure Q →
          ∀ (w : CantorSeq) (D : ℕ),
            PathBudget P w D → PathBudget Q w D →
              Summable (fun n : ℕ =>
                (condProb (cantorMass P) (cantorPrefix w n) false -
                  condProb (cantorMass Q) (cantorPrefix w n) false) ^ 2) ∧
              (∑' n : ℕ,
                (condProb (cantorMass P) (cantorPrefix w n) false -
                  condProb (cantorMass Q) (cantorPrefix w n) false) ^ 2) ≤
                C * ((computableMeasureComplexity U P).toNat +
                  (computableMeasureComplexity U Q).toNat + D + 1) := by
  obtain ⟨C, hC_pos, hC⟩ := pairwise_prefix_sq_bound U hU
  use C, hC_pos
  intro P Q _ _ hPc hQc w D hDP hDQ
  let f : ℕ → ℝ := fun n => (condProb (cantorMass P) (cantorPrefix w n) false -
    condProb (cantorMass Q) (cantorPrefix w n) false) ^ 2
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    exact sq_nonneg _
  let B := C * ((computableMeasureComplexity U P).toNat +
    (computableMeasureComplexity U Q).toNat + D + 1)
  have hB : ∀ N, ∑ i ∈ Finset.range N, f i ≤ B := by
    intro N
    have H : ∑ i ∈ Finset.range N, f i = pairwiseError P Q (cantorPrefix w N) :=
      (pairwiseError_prefix_eq_sum_range P Q w N).symm
    rw [H]
    apply hC P Q hPc hQc (cantorPrefix w N)
    · exact base_budget_positive P w D N hDP
    · exact base_budget_positive Q w D N hDQ
    · exact hDP N
    · exact hDQ N
  have hs : Summable f := summable_of_sum_range_le hf hB
  exact ⟨hs, Real.tsum_le_of_sum_range_le hf hB⟩


/-- Two random path budgets can be enlarged to a common budget. -/
private lemma exists_common_budget (U : Map) (hU : IsOptimalPrefixConditional U)
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPc : IsComputableMeasure P) (hQc : IsComputableMeasure Q)
    (w : CantorSeq) (hP : IsMartinLofRandom P w)
    (hQ : IsMartinLofRandom Q w) :
    ∃ D : ℕ, PathBudget P w D ∧ PathBudget Q w D := by
  have ⟨DP, hDP⟩ := (random_iff_exists_budget U hU P w hPc).mp hP
  have ⟨DQ, hDQ⟩ := (random_iff_exists_budget U hU Q w hQc).mp hQ
  use max DP DQ
  constructor
  · intro n
    have h : (2 : ℝ≥0∞) ^ DP ≤ (2 : ℝ≥0∞) ^ (max DP DQ) := by
      have : (1 : ℝ≥0∞) ≤ 2 := by norm_num
      gcongr
      exact le_max_left DP DQ
    have h' : (2 : ℝ≥0∞) ^ DP * cantorMass P (cantorPrefix w n) ≤
        (2 : ℝ≥0∞) ^ (max DP DQ) * cantorMass P (cantorPrefix w n) := by
      gcongr
    exact (hDP n).trans h'
  · intro n
    have h : (2 : ℝ≥0∞) ^ DQ ≤ (2 : ℝ≥0∞) ^ (max DP DQ) := by
      have : (1 : ℝ≥0∞) ≤ 2 := by norm_num
      gcongr
      exact le_max_right DP DQ
    have h' : (2 : ℝ≥0∞) ^ DQ * cantorMass Q (cantorPrefix w n) ≤
        (2 : ℝ≥0∞) ^ (max DP DQ) * cantorMass Q (cantorPrefix w n) := by
      gcongr
    exact (hDQ n).trans h'

/-- The pairwise bit-zero discrepancies are square summable on a path random
for both proper computable measures. Blueprint node `rand:vovk`. -/
theorem vovk_merging_summable (U : Map) (hU : IsOptimalPrefixConditional U)
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPc : IsComputableMeasure P) (hQc : IsComputableMeasure Q)
    (w : CantorSeq) (hP : IsMartinLofRandom P w)
    (hQ : IsMartinLofRandom Q w) :
    Summable (fun n : ℕ =>
      (condProb (cantorMass P) (cantorPrefix w n) false -
        condProb (cantorMass Q) (cantorPrefix w n) false) ^ 2) := by
  have ⟨D, hDP, hDQ⟩ := exists_common_budget U hU P Q hPc hQc w hP hQ
  obtain ⟨C, _, hC⟩ := vovk_merging_bound U hU
  exact (hC P Q hPc hQc w D hDP hDQ).1

/-- Vovk merging for bit zero, derived from the square-sum bound.
Blueprint node `rand:vovk`. -/
theorem vovk_merging (U : Map) (hU : IsOptimalPrefixConditional U)
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPc : IsComputableMeasure P) (hQc : IsComputableMeasure Q)
    (w : CantorSeq) (hP : IsMartinLofRandom P w)
    (hQ : IsMartinLofRandom Q w) :
    Filter.Tendsto (fun n =>
      condProb (cantorMass P) (cantorPrefix w n) false -
        condProb (cantorMass Q) (cantorPrefix w n) false)
      Filter.atTop (nhds 0) := by
  have h := vovk_merging_summable U hU P Q hPc hQc w hP hQ
  have h2 := h.tendsto_atTop_zero
  have h3 : Filter.Tendsto (fun n => Real.sqrt ((condProb (cantorMass P) (cantorPrefix w n) false -
        condProb (cantorMass Q) (cantorPrefix w n) false) ^ 2)) Filter.atTop (nhds (Real.sqrt 0)) :=
    Filter.Tendsto.comp (Continuous.tendsto Real.continuous_sqrt 0) h2
  rw [Real.sqrt_zero] at h3
  have h4 : Filter.Tendsto (fun n => |condProb (cantorMass P) (cantorPrefix w n) false -
        condProb (cantorMass Q) (cantorPrefix w n) false|) Filter.atTop (nhds 0) := by
    simp_rw [← Real.sqrt_sq_eq_abs]
    exact h3
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h4

/-- Vovk merging also holds for bit one. Blueprint node `rand:vovk`. -/
theorem vovk_merging_true (U : Map) (hU : IsOptimalPrefixConditional U)
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPc : IsComputableMeasure P) (hQc : IsComputableMeasure Q)
    (w : CantorSeq) (hP : IsMartinLofRandom P w)
    (hQ : IsMartinLofRandom Q w) :
    Filter.Tendsto (fun n =>
      condProb (cantorMass P) (cantorPrefix w n) true -
        condProb (cantorMass Q) (cantorPrefix w n) true)
      Filter.atTop (nhds 0) := by
  have H := vovk_merging U hU P Q hPc hQc w hP hQ
  have H_P_add : ∀ n, condProb (cantorMass P) (cantorPrefix w n) false +
      condProb (cantorMass P) (cantorPrefix w n) true = 1 := by
    intro n
    exact condProb_cantorMass_add_eq_one P (by
      have hpos := random_prefix_mass_pos U hU P hPc w hP n
      exact hpos.ne')
  have H_Q_add : ∀ n, condProb (cantorMass Q) (cantorPrefix w n) false +
      condProb (cantorMass Q) (cantorPrefix w n) true = 1 := by
    intro n
    exact condProb_cantorMass_add_eq_one Q (by
      have hpos := random_prefix_mass_pos U hU Q hQc w hQ n
      exact hpos.ne')
  have H_eq : (fun n => condProb (cantorMass P) (cantorPrefix w n) true -
      condProb (cantorMass Q) (cantorPrefix w n) true) =
    (fun n => - (condProb (cantorMass P) (cantorPrefix w n) false -
      condProb (cantorMass Q) (cantorPrefix w n) false)) := by
    ext n
    have hPn := H_P_add n
    have hQn := H_Q_add n
    linarith
  rw [H_eq]
  have H_nhds : (nhds (0 : ℝ)) = nhds (- (0 : ℝ)) := by rw [neg_zero]
  rw [H_nhds]
  exact Filter.Tendsto.neg H

end Kolmogorov.MDLPrediction
