/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Path.Winners
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pathwise squared-error bound for the global predictor

Each selected model has bounded charge; the finite winner family bounds how many
such charges occur. The predictor choice may change at every time.

Blueprint node: `exp:theorem7`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- The squared bit-zero error of the global predictor at time `n` is the sum of the
charges `selectedCharge` over any finite family containing every chosen measure:
only the measure chosen at `w_{<n}` is charged at time `n`. -/
private lemma pathwise_sq_bound_sq_eq (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) (w : CantorSeq) (choose : BitString → Measure CantorSeq)
    (F : Finset (Measure CantorSeq)) (hF : ∀ n, choose (cantorPrefix w n) ∈ F) (n : ℕ) :
    (predictor U hU choose (cantorPrefix w n) false -
      condProb (cantorMass P) (cantorPrefix w n) false) ^ 2 =
    ∑ Q ∈ F, selectedCharge choose P Q w n := by
  rw [Finset.sum_eq_single (choose (cantorPrefix w n))]
  · unfold selectedCharge selectedError predictor
    rw [ite_eq_left rfl]
  · intro Q _ hQ
    unfold selectedCharge
    exact ite_eq_right (Ne.symm hQ)
  · intro h
    exact absurd (hF n) h

/-- The winner-count factor: `2 ^ (⌊M / 2⌋ + 1) ≤ 2 * 2 ^ (M / 2)`. -/
private lemma pathwise_sq_bound_pow_le (M : ℕ) :
    (2 : ℝ) ^ (M / 2 + 1) ≤ 2 * (2 : ℝ) ^ ((M : ℝ) / 2) := by
  have hdiv : ((M / 2 : ℕ) : ℝ) ≤ (M : ℝ) / 2 := by
    have h := Nat.cast_div_le (α := ℝ) (m := M) (n := 2)
    simpa using h
  have hrpow : (2 : ℝ) ^ (M / 2) ≤ (2 : ℝ) ^ ((M : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv
  rw [pow_succ]
  linarith

/-- Paper Theorem 7: a natural path budget gives a finite, explicit global
predictor square-sum bound. Blueprint node `exp:theorem7`. -/
theorem pathwise_sq_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ (c : ℕ) (C : ℝ), 0 < C ∧
      ∀ (P : Measure CantorSeq) [IsProbabilityMeasure P],
        IsComputableMeasure P → ∀ (w : CantorSeq) (D : ℕ),
          PathBudget P w D →
            ∀ (choose : BitString → Measure CantorSeq),
              IsGlobalChoice U hU choose →
                Summable (fun n : ℕ =>
                  (predictor U hU choose (cantorPrefix w n) false -
                    condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ∧
                (∑' n : ℕ,
                  (predictor U hU choose (cantorPrefix w n) false -
                    condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ≤
                  C * ((computableMeasureComplexity U P).toNat + D + 1) *
                    (2 : ℝ) ^ (((3 * (computableMeasureComplexity U P).toNat +
                      D + c : ℕ) : ℝ) / 2) := by
  obtain ⟨c, hc⟩ := exp_finite_winner_count U hU
  obtain ⟨C, hC_pos, hC⟩ := charge_selected_measure U hU
  refine ⟨c, 2 * C, by positivity, ?_⟩
  intro P _ hP_comp w D hbudget choose hchoose
  obtain ⟨F_set, hF_fin, hF_card, _, hF_choose⟩ :=
    hc P hP_comp w D hbudget choose hchoose
  set k := (computableMeasureComplexity U P).toNat with hk
  set F := hF_fin.toFinset with hF
  have hF_mem : ∀ n, choose (cantorPrefix w n) ∈ F := fun n =>
    hF_fin.mem_toFinset.mpr (hF_choose n)
  have hB_nonneg : (0 : ℝ) ≤ C * ((k : ℝ) + D + 1) := by positivity
  -- Each measure of the family has bounded charge (zero if it is never chosen).
  have h_charge : ∀ Q ∈ F, Summable (fun n : ℕ => selectedCharge choose P Q w n) ∧
      (∑' n : ℕ, selectedCharge choose P Q w n) ≤ C * ((k : ℝ) + D + 1) := by
    intro Q _
    by_cases h_sel : ∃ n, choose (cantorPrefix w n) = Q
    · exact hC P hP_comp w D hbudget choose hchoose Q h_sel
    · simp only [not_exists] at h_sel
      have h_zero : (fun n : ℕ => selectedCharge choose P Q w n) = fun _ => 0 := by
        funext n
        unfold selectedCharge
        exact ite_eq_right (h_sel n)
      rw [h_zero, tsum_zero]
      exact ⟨summable_zero, hB_nonneg⟩
  have h_summ : ∀ Q ∈ F, Summable (fun n : ℕ => selectedCharge choose P Q w n) :=
    fun Q hQ => (h_charge Q hQ).1
  have h_eq : (fun n : ℕ => (predictor U hU choose (cantorPrefix w n) false -
      condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) =
      fun n => ∑ Q ∈ F, selectedCharge choose P Q w n :=
    funext (pathwise_sq_bound_sq_eq U hU P w choose F hF_mem)
  -- The family has at most `2 ^ (⌊(3k + D + c) / 2⌋ + 1)` members.
  have hcard : (F.card : ℝ) ≤ 2 * (2 : ℝ) ^ (((3 * k + D + c : ℕ) : ℝ) / 2) := by
    have h1 : F.card ≤ 2 ^ ((3 * k + D + c) / 2 + 1) := by
      rw [hF, ← Set.ncard_eq_toFinset_card F_set hF_fin]
      exact hF_card
    have h2 : (F.card : ℝ) ≤ (2 : ℝ) ^ ((3 * k + D + c) / 2 + 1) := by
      exact_mod_cast h1
    exact h2.trans (pathwise_sq_bound_pow_le (3 * k + D + c))
  rw [h_eq]
  refine ⟨summable_sum h_summ, ?_⟩
  rw [Summable.tsum_finsetSum h_summ]
  calc ∑ Q ∈ F, ∑' n, selectedCharge choose P Q w n
      ≤ ∑ _Q ∈ F, C * ((k : ℝ) + D + 1) :=
        Finset.sum_le_sum fun Q hQ => (h_charge Q hQ).2
    _ = F.card * (C * ((k : ℝ) + D + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (2 : ℝ) ^ (((3 * k + D + c : ℕ) : ℝ) / 2)) * (C * ((k : ℝ) + D + 1)) :=
        mul_le_mul_of_nonneg_right hcard hB_nonneg
    _ = 2 * C * ((k : ℝ) + D + 1) * (2 : ℝ) ^ (((3 * k + D + c : ℕ) : ℝ) / 2) := by ring

end Kolmogorov.MDLPrediction
