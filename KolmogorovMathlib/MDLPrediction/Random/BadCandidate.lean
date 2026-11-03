/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.FinitePrograms
import KolmogorovMathlib.MDLPrediction.Core.Winner
import KolmogorovMathlib.MDLPrediction.Random.Criteria

/-!
# Finite winners and eventual exclusion of nonrandom candidates

On a budgeted path every winner belongs to one finite complexity sublevel. For each
candidate relative to which the path is nonrandom, the score eventually loses against
the source model. A finite maximum excludes all such candidates under any tie choice.

Blueprint nodes: `rand:bad`, `rand:bad-one`, `rand:finite-candidates`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- One finite family contains every global winner on a budgeted path, with the
explicit complexity-sublevel cardinal bound. Blueprint node `rand:finite-candidates`. -/
theorem rand_finite_candidates (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : ℕ)
    (hc : ∀ R : Measure CantorSeq, IsProbabilityMeasure R →
      IsComputableMeasure R → ∀ x : BitString, 0 < cantorMass R x →
        KA x ≤ (computableMeasureComplexity U R).toNat -
          Real.logb 2 (cantorMass R x).toReal + c)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (hP : IsComputableMeasure P)
    (w : CantorSeq) (D : ℕ) (hbudget : PathBudget P w D) :
    ∃ F : Set (Measure CantorSeq), F.Finite ∧
      F.ncard ≤ 2 ^ ((3 * (computableMeasureComplexity U P).toNat + D + c) / 2 + 1) ∧
      (∀ Q ∈ F, IsProbabilityMeasure Q ∧ IsComputableMeasure Q) ∧
      ∀ n Q, IsGlobalWinner U hU Q (cantorPrefix w n) → Q ∈ F := by
  let bound := (3 * (computableMeasureComplexity U P).toNat + D + c) / 2
  let F : Set (Measure CantorSeq) := { Q | IsProbabilityMeasure Q ∧ IsComputableMeasure Q ∧
    (computableMeasureComplexity U Q).toNat ≤ bound }
  use F
  have hF : F.Finite ∧ F.ncard < 2 ^ (bound + 1) := finite_models_complexity_le U hU bound
  rcases hF with ⟨hF_fin, hF_card⟩
  refine ⟨hF_fin, le_of_lt hF_card, ?_, ?_⟩
  · intro Q hQ
    exact ⟨hQ.1, hQ.2.1⟩
  · intro n Q hQ_win
    have h_comp := winner_bounds_complexity U hU c hc P hP w D n hbudget Q hQ_win
    have h_comp2 : (computableMeasureComplexity U Q).toNat ≤ bound := by omega
    exact ⟨hQ_win.1, hQ_win.2.1, h_comp2⟩

/-- Each computable nonrandom candidate eventually has zero mass or loses to the
budgeted source model. Blueprint node `rand:bad-one`. -/
theorem rand_bad_one (U : Map) (hU : IsOptimalPrefixConditional U)
    (P Q : Measure CantorSeq) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : IsComputableMeasure Q)
    (w : CantorSeq) (D : ℕ) (hbudget : PathBudget P w D)
    (hnot : ¬ IsMartinLofRandom Q w) :
    ∃ N : ℕ, ∀ n ≥ N,
      cantorMass Q (cantorPrefix w n) = 0 ∨
        score U hU P (cantorPrefix w n) < score U hU Q (cantorPrefix w n) := by
  let B : ℝ := 3 * ((computableMeasureComplexity U P).toNat : ℝ) + D -
    3 * ((computableMeasureComplexity U Q).toNat : ℝ)
  obtain ⟨N, hN⟩ := apriori_deficiency_tendsto_of_not_random U hU Q w hQ hnot B
  use N
  intro n hn
  have h_cases := hN n hn
  by_cases hQ_zero : cantorMass Q (cantorPrefix w n) = 0
  · exact Or.inl hQ_zero
  · apply Or.inr
    have h_ineq := h_cases.resolve_left hQ_zero
    have hP_pos : 0 < cantorMass P (cantorPrefix w n) := base_budget_positive P w D n hbudget
    have h_score_P : score U hU P (cantorPrefix w n) =
        ((3 * ((computableMeasureComplexity U P).toNat : ℝ) -
          Real.logb 2 (cantorMass P (cantorPrefix w n)).toReal : ℝ) : EReal) := by
      unfold score
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hP_pos.ne' h))]
    have h_score_Q : score U hU Q (cantorPrefix w n) =
        ((3 * ((computableMeasureComplexity U Q).toNat : ℝ) -
          Real.logb 2 (cantorMass Q (cantorPrefix w n)).toReal : ℝ) : EReal) := by
      unfold score
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hQ_zero h))]
    rw [h_score_P, h_score_Q, EReal.coe_lt_coe_iff]
    have hbudget_log := (base_budget_log P (cantorPrefix w n) D hP_pos).mp (hbudget n)
    linarith


open Classical in
/-- A finite set of eventual bounds has one common threshold. -/
private lemma eventually_forall_finite
    (F : Set (Measure CantorSeq)) (hF : F.Finite)
    (U : Map) (hU : IsOptimalPrefixConditional U) (P : Measure CantorSeq)
    (w : CantorSeq)
    (H : ∀ Q ∈ F, ¬ IsMartinLofRandom Q w → ∃ N : ℕ, ∀ n ≥ N,
      cantorMass Q (cantorPrefix w n) = 0 ∨
      score U hU P (cantorPrefix w n) < score U hU Q (cantorPrefix w n)) :
    ∃ N_max : ℕ, ∀ Q ∈ F, ¬ IsMartinLofRandom Q w → ∀ n ≥ N_max,
      cantorMass Q (cantorPrefix w n) = 0 ∨
      score U hU P (cantorPrefix w n) < score U hU Q (cantorPrefix w n) := by
  let f : Measure CantorSeq → ℕ := fun Q =>
    if h : Q ∈ F ∧ ¬ IsMartinLofRandom Q w then Classical.choose (H Q h.1 h.2) else 0
  use hF.toFinset.sup f
  intro Q hQ hnQ n hn
  have h_in : Q ∈ F ∧ ¬ IsMartinLofRandom Q w := ⟨hQ, hnQ⟩
  have hf_eq : f Q = Classical.choose (H Q hQ hnQ) := dite_eq_left h_in
  have hn' : Classical.choose (H Q hQ hnQ) ≤ n := by
    rw [← hf_eq]
    exact le_trans (Finset.le_sup (Set.Finite.mem_toFinset hF |>.mpr hQ)) hn
  exact Classical.choose_spec (H Q hQ hnQ) n hn'

/-- Every choice of global winners eventually avoids all candidates for which
the path is nonrandom. Blueprint node `rand:bad`. -/
theorem eventually_no_bad_winner (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (hP : IsComputableMeasure P)
    (w : CantorSeq) (hPw : IsMartinLofRandom P w)
    (choose : BitString → Measure CantorSeq) (hchoose : IsGlobalChoice U hU choose) :
    ∃ F : Set (Measure CantorSeq), F.Finite ∧
      (∀ Q ∈ F, IsProbabilityMeasure Q ∧ IsComputableMeasure Q) ∧
      (∀ n, choose (cantorPrefix w n) ∈ F) ∧
      ∃ N : ℕ, ∀ Q ∈ F, ¬ IsMartinLofRandom Q w →
        ∀ n ≥ N, choose (cantorPrefix w n) ≠ Q := by
  obtain ⟨D, hD⟩ := (random_iff_exists_budget U hU P w hP).mp hPw
  obtain ⟨c, hc⟩ := KA_le_measure_code U hU
  obtain ⟨F, hF_fin, _, hF_models, hF_winners⟩ := rand_finite_candidates U hU c hc P hP w D hD
  use F, hF_fin, hF_models
  have h_choose_in_F : ∀ n, choose (cantorPrefix w n) ∈ F := by
    intro n
    apply hF_winners
    exact hchoose (cantorPrefix w n)
  use h_choose_in_F
  have H : ∀ Q ∈ F, ¬ IsMartinLofRandom Q w → ∃ N : ℕ, ∀ n ≥ N,
      cantorMass Q (cantorPrefix w n) = 0 ∨
      score U hU P (cantorPrefix w n) < score U hU Q (cantorPrefix w n) := by
    intro Q hQ hQ_not_rand
    have h_prob : IsProbabilityMeasure Q := (hF_models Q hQ).1
    have h_comp : IsComputableMeasure Q := (hF_models Q hQ).2
    exact rand_bad_one U hU P Q h_comp w D hD hQ_not_rand
  obtain ⟨N, hN⟩ := eventually_forall_finite F hF_fin U hU P w H
  use N
  intro Q hQ hQ_not_rand n hn h_eq
  have h_bad := hN Q hQ hQ_not_rand n hn
  cases h_bad with
  | inl h0 =>
    have h_winner := hchoose (cantorPrefix w n)
    rw [h_eq] at h_winner
    have h_pos := h_winner.2.2.1
    rw [h0] at h_pos
    exact False.elim (lt_irrefl 0 h_pos)
  | inr h_lt =>
    have h_winner := hchoose (cantorPrefix w n)
    have h_P_winner := h_winner.2.2.2 P inferInstance hP (random_prefix_mass_pos U hU P hP w hPw n)
    rw [h_eq] at h_winner h_P_winner
    exact False.elim (not_le.mpr h_lt h_P_winner)


end Kolmogorov.MDLPrediction
