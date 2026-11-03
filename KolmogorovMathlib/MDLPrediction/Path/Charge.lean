/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Pairwise.Bound
import KolmogorovMathlib.MDLPrediction.Core.Winner
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Charge at selected times for one model

The last selected time is charged separately because the pairwise bound at its
prefix covers only earlier positions. The uniform constant precedes the measures.

Blueprint nodes: `exp:charge-finite`, `exp:charge`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped BigOperators

/-! ## Error charged at selected times -/

/-- The squared bit-zero discrepancy at one path time.
Blueprint node `exp:charge-finite`. -/
noncomputable def selectedError (P Q : Measure CantorSeq) (w : CantorSeq)
    (n : ℕ) : ℝ :=
  (condProb (cantorMass Q) (cantorPrefix w n) false -
    condProb (cantorMass P) (cantorPrefix w n) false) ^ 2

/-- The discrepancy charged to `Q` exactly when it is selected.
Blueprint node `exp:charge`. -/
noncomputable def selectedCharge (choose : BitString → Measure CantorSeq)
    (P Q : Measure CantorSeq) (w : CantorSeq) (n : ℕ) : ℝ := by
  classical
  exact if choose (cantorPrefix w n) = Q then selectedError P Q w n else 0

/-! ## Uniform finite charge -/

/-- A uniform pairwise error bound for a winner along a budgeted path. -/
private lemma pairwiseError_le_pathBudget (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Measure CantorSeq)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      IsComputableMeasure P → IsComputableMeasure Q →
        ∀ (w : CantorSeq) (D m : ℕ), PathBudget P w D →
          IsGlobalWinner U hU Q (cantorPrefix w m) →
            pairwiseError P Q (cantorPrefix w m) ≤
              C * ((computableMeasureComplexity U P).toNat + D + 1) - 1 := by
  obtain ⟨c, hc⟩ := KA_le_measure_code U hU
  obtain ⟨C0, hC0, hpair⟩ := pairwise_prefix_sq_bound U hU
  refine ⟨C0 * (7 + c) + 1, by positivity, ?_⟩
  intro P Q _ _ hP_comp hQ_comp w D m hbudget hwin
  let k := (computableMeasureComplexity U P).toNat
  have hPpos := base_budget_positive P w D m hbudget
  have hQpos := hwin.2.2.1
  let x := cantorPrefix w m
  let n := 3 * k + D
  have hMQ : universalContinuousSemimeasure x ≤ (2 : ENNReal) ^ n * cantorMass Q x := by
    have hw := winner_bounds U hU c hc P hP_comp w D m hbudget Q hwin
    have hcancel : (2 : ENNReal) ^ n * (2 : ENNReal)⁻¹ ^ n = 1 := by
      rw [← ENNReal.inv_pow]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      universalContinuousSemimeasure x =
          ((2 : ENNReal) ^ n * (2 : ENNReal)⁻¹ ^ n) *
            universalContinuousSemimeasure x := by rw [hcancel, one_mul]
      _ = (2 : ENNReal) ^ n *
            ((2 : ENNReal)⁻¹ ^ n * universalContinuousSemimeasure x) := by rw [mul_assoc]
      _ ≤ (2 : ENNReal) ^ n * cantorMass Q x := by gcongr
  have hMP : universalContinuousSemimeasure x ≤ (2 : ENNReal) ^ n * cantorMass P x := by
    calc
      universalContinuousSemimeasure x ≤ (2 : ENNReal) ^ D * cantorMass P x := hbudget m
      _ ≤ (2 : ENNReal) ^ n * cantorMass P x := by
        have h1 : (2 : ENNReal) ^ D ≤ (2 : ENNReal) ^ n := by
          apply pow_le_pow_right₀
          · norm_num
          · omega
        exact mul_le_mul' h1 (le_refl _)
  have hkQ := winner_bounds_complexity U hU c hc P hP_comp w D m hbudget Q hwin
  have h := hpair P Q hP_comp hQ_comp x hPpos hQpos n hMP hMQ
  have hkQ_real :
      (2 : ℝ) * ((computableMeasureComplexity U Q).toNat : ℝ) ≤
        (3 : ℝ) * (k : ℝ) + (D : ℝ) + (c : ℝ) := by
    exact_mod_cast hkQ
  have hS :
      (k : ℝ) + ((computableMeasureComplexity U Q).toNat : ℝ) + (n : ℝ) + 1 ≤
        ((7 + c : ℕ) : ℝ) * ((k : ℝ) + (D : ℝ) + 1) := by
    have hn : (n : ℝ) = (3 : ℝ) * (k : ℝ) + (D : ℝ) := by
      unfold n
      push_cast
      ring
    rw [hn]
    have h_c_nonneg : 0 ≤ (c : ℝ) := Nat.cast_nonneg _
    have h_k_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have h_D_nonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
    have h_kQ_nonneg : 0 ≤ ((computableMeasureComplexity U Q).toNat : ℝ) := Nat.cast_nonneg _
    have hs1 :
        2 * (k : ℝ) + 2 * ((computableMeasureComplexity U Q).toNat : ℝ) +
          2 * ((3 : ℝ) * (k : ℝ) + (D : ℝ)) + 2 ≤
        2 * (k : ℝ) + (3 * (k : ℝ) + (D : ℝ) + (c : ℝ)) +
          2 * ((3 : ℝ) * (k : ℝ) + (D : ℝ)) + 2 := by linarith
    have hs2 :
        2 * (k : ℝ) + (3 * (k : ℝ) + (D : ℝ) + (c : ℝ)) +
          2 * ((3 : ℝ) * (k : ℝ) + (D : ℝ)) + 2 =
        11 * (k : ℝ) + 3 * (D : ℝ) + (c : ℝ) + 2 := by ring
    have hs3 : 11 * (k : ℝ) + 3 * (D : ℝ) + (c : ℝ) + 2 ≤
               2 * (((7 + c : ℕ) : ℝ) * ((k : ℝ) + (D : ℝ) + 1)) := by
      push_cast
      nlinarith
    linarith
  have hCS :
      C0 * ((k : ℝ) + ((computableMeasureComplexity U Q).toNat : ℝ) + (n : ℝ) + 1) ≤
        C0 * (((7 + c : ℕ) : ℝ) * ((k : ℝ) + (D : ℝ) + 1)) := by
    exact mul_le_mul_of_nonneg_left hS hC0.le
  calc
    pairwiseError P Q x ≤
        C0 * ((k : ℝ) + ((computableMeasureComplexity U Q).toNat : ℝ) + (n : ℝ) + 1) := h
    _ ≤ C0 * (((7 + c : ℕ) : ℝ) * ((k : ℝ) + (D : ℝ) + 1)) := hCS
    _ = (C0 * ((7 + (c : ℝ)))) * ((k : ℝ) + (D : ℝ) + 1) := by
      push_cast
      ring
    _ ≤ (C0 * ((7 + (c : ℝ))) + 1) * ((k : ℝ) + (D : ℝ) + 1) - 1 := by
      have h1 :
          (C0 * (7 + (c : ℝ))) * ((k : ℝ) + (D : ℝ) + 1) +
            ((k : ℝ) + (D : ℝ)) + 1 =
          (C0 * (7 + (c : ℝ)) + 1) * ((k : ℝ) + (D : ℝ) + 1) := by
        ring
      have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      have hD_nonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
      linarith

/-- The conditional probability of the zero successor is at most one. -/
private lemma condProb_cantorMass_le_one (mu : Measure CantorSeq) (x : BitString) :
    condProb (cantorMass mu) x false ≤ 1 := by
  unfold condProb
  have hsub : cantorMass mu (x ++ [false]) ≤ cantorMass mu x :=
    measure_mono (cantorCylinder_subset_of_prefix (List.prefix_append x [false]))
  by_cases htop : cantorMass mu x = ⊤
  · simp [htop]
  · exact div_le_one_of_le₀ (ENNReal.toReal_mono htop hsub) ENNReal.toReal_nonneg

/-- Selected errors through time `m` are bounded by the preceding pairwise error
and the error at `m`, which is at most one. -/
private lemma sum_selectedError_le_pairwiseError_add_one (P Q : Measure CantorSeq) (w : CantorSeq)
    (T : Finset ℕ) (m : ℕ) (hm : ∀ n ∈ T, n ≤ m) :
    (∑ n ∈ T, selectedError P Q w n) ≤ pairwiseError P Q (cantorPrefix w m) + 1 := by
  have hTm : T ⊆ Finset.range (m + 1) := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hm n hn))
  have hpe : ∑ i ∈ Finset.range m, selectedError P Q w i =
      pairwiseError P Q (cantorPrefix w m) := by
    unfold pairwiseError selectedError
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (condProb (cantorMass P) ((cantorPrefix w m).take i) false -
      condProb (cantorMass Q) ((cantorPrefix w m).take i) false) ^ 2), cantorPrefix_length]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [cantorPrefix_take w i m (Finset.mem_range.mp hi).le]
    ring
  have hlast : selectedError P Q w m ≤ 1 := by
    unfold selectedError
    have hcond_P := condProb_cantorMass_le_one P (cantorPrefix w m)
    have hcond_Q := condProb_cantorMass_le_one Q (cantorPrefix w m)
    have hnonneg_P := condProb_nonneg (cantorMass P) (cantorPrefix w m) false
    have hnonneg_Q := condProb_nonneg (cantorMass Q) (cantorPrefix w m) false
    nlinarith
  calc (∑ n ∈ T, selectedError P Q w n)
    _ ≤ ∑ n ∈ Finset.range (m + 1), selectedError P Q w n :=
        Finset.sum_le_sum_of_subset_of_nonneg hTm (fun i _ _ => by
          unfold selectedError; exact sq_nonneg _)
    _ = (∑ n ∈ Finset.range m, selectedError P Q w n) + selectedError P Q w m :=
        Finset.sum_range_succ _ m
    _ = pairwiseError P Q (cantorPrefix w m) + selectedError P Q w m := by rw [hpe]
    _ ≤ pairwiseError P Q (cantorPrefix w m) + 1 := by linarith

/-- Every finite set of times selecting the same model has uniformly bounded charge.
Blueprint node `exp:charge-finite`. -/
theorem exp_charge_finite (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Measure CantorSeq)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      IsComputableMeasure P → IsComputableMeasure Q →
        ∀ (w : CantorSeq) (D : ℕ), PathBudget P w D →
          ∀ T : Finset ℕ,
            (∀ n ∈ T, IsGlobalWinner U hU Q (cantorPrefix w n)) →
              (∑ n ∈ T, selectedError P Q w n) ≤
                C * ((computableMeasureComplexity U P).toNat + D + 1) := by
  obtain ⟨C, hC_pos, hC⟩ := pairwiseError_le_pathBudget U hU
  use C, hC_pos
  intro P Q _ _ hP_comp hQ_comp w D hBudget T hT
  obtain h_empty | h_nonempty := T.eq_empty_or_nonempty
  · rw [h_empty, Finset.sum_empty]
    have : (0 : ℝ) ≤ (computableMeasureComplexity U P).toNat + D + 1 := by positivity
    exact mul_nonneg hC_pos.le this
  · let m := T.max' h_nonempty
    have hm_mem : m ∈ T := Finset.max'_mem T h_nonempty
    have hm_le : ∀ n ∈ T, n ≤ m := fun n hn => Finset.le_max' T n hn
    have h_winner_m := hT m hm_mem
    have h_pair := hC P Q hP_comp hQ_comp w D m hBudget h_winner_m
    have h_sum_le := sum_selectedError_le_pairwiseError_add_one P Q w T m hm_le
    calc (∑ n ∈ T, selectedError P Q w n)
      _ ≤ pairwiseError P Q (cantorPrefix w m) + 1 := h_sum_le
      _ ≤ C * ((computableMeasureComplexity U P).toNat + D + 1) - 1 + 1 := by linarith
      _ = C * ((computableMeasureComplexity U P).toNat + D + 1) := by ring


/-- Uniform bound on finite initial sums of charges for one selected model. -/
private lemma sum_selectedCharge_range_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure CantorSeq) [IsProbabilityMeasure P],
      IsComputableMeasure P → ∀ (w : CantorSeq) (D : ℕ),
        PathBudget P w D →
          ∀ (choose : BitString → Measure CantorSeq),
            IsGlobalChoice U hU choose → ∀ Q : Measure CantorSeq,
              (∃ n, choose (cantorPrefix w n) = Q) →
              ∀ (N : ℕ), (∑ n ∈ Finset.range N, selectedCharge choose P Q w n) ≤
                  C * ((computableMeasureComplexity U P).toNat + D + 1) := by
  obtain ⟨C, hC_pos, hC⟩ := exp_charge_finite U hU
  use C, hC_pos
  intro P _ hP w D hBudget choose hChoose Q hQ N
  obtain ⟨n0, hn0⟩ := hQ
  have hQ_winner := hChoose (cantorPrefix w n0)
  rw [hn0] at hQ_winner
  have : IsProbabilityMeasure Q := hQ_winner.1
  have hQ_comp : IsComputableMeasure Q := hQ_winner.2.1
  classical
  let T : Finset ℕ := (Finset.range N).filter (fun n => choose (cantorPrefix w n) = Q)
  have h_sum : (∑ n ∈ Finset.range N, selectedCharge choose P Q w n) =
      ∑ n ∈ T, selectedError P Q w n := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun n => choose (cantorPrefix w n) = Q)]
    have h1 : ∑ n ∈ (Finset.range N).filter (fun n => choose (cantorPrefix w n) = Q),
        selectedCharge choose P Q w n =
        ∑ n ∈ (Finset.range N).filter (fun n => choose (cantorPrefix w n) = Q),
        selectedError P Q w n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : choose (cantorPrefix w n) = Q := (Finset.mem_filter.mp hn).2
      unfold selectedCharge
      simp only [hn', ite_true]
    have h2 : ∑ n ∈ (Finset.range N).filter (fun n => ¬ choose (cantorPrefix w n) = Q),
        selectedCharge choose P Q w n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hn' : choose (cantorPrefix w n) ≠ Q := (Finset.mem_filter.mp hn).2
      unfold selectedCharge
      simp only [hn', ite_false]
    rw [h1, h2, add_zero]
  rw [h_sum]
  have hT : ∀ n ∈ T, IsGlobalWinner U hU Q (cantorPrefix w n) := by
    intro n hn
    have hn' : choose (cantorPrefix w n) = Q := (Finset.mem_filter.mp hn).2
    have h_winner := hChoose (cantorPrefix w n)
    rw [hn'] at h_winner
    exact h_winner
  exact hC P Q hP hQ_comp w D hBudget T hT

/-- The full series of charges from one selected measure is bounded, even if
that measure is selected intermittently. Blueprint node `exp:charge`. -/
theorem charge_selected_measure (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure CantorSeq) [IsProbabilityMeasure P],
      IsComputableMeasure P → ∀ (w : CantorSeq) (D : ℕ),
        PathBudget P w D →
          ∀ (choose : BitString → Measure CantorSeq),
            IsGlobalChoice U hU choose → ∀ Q : Measure CantorSeq,
              (∃ n, choose (cantorPrefix w n) = Q) →
                Summable (fun n : ℕ => selectedCharge choose P Q w n) ∧
                (∑' n : ℕ, selectedCharge choose P Q w n) ≤
                  C * ((computableMeasureComplexity U P).toNat + D + 1) := by
  obtain ⟨C, hC_pos, hC⟩ := sum_selectedCharge_range_le U hU
  use C, hC_pos
  intro P _ hP w D hBudget choose hChoose Q hQ
  have h_bound : ∀ N : ℕ, (∑ n ∈ Finset.range N, selectedCharge choose P Q w n) ≤
      C * ((computableMeasureComplexity U P).toNat + D + 1) := by
    exact hC P hP w D hBudget choose hChoose Q hQ
  have h_nonneg : ∀ n, 0 ≤ selectedCharge choose P Q w n := by
    intro n
    unfold selectedCharge
    split_ifs
    · exact sq_nonneg _
    · exact le_refl _
  have h_summable : Summable (fun n : ℕ => selectedCharge choose P Q w n) := by
    exact summable_of_sum_range_le h_nonneg h_bound
  refine ⟨h_summable, ?_⟩
  exact Real.tsum_le_of_sum_range_le h_nonneg h_bound

end Kolmogorov.MDLPrediction
