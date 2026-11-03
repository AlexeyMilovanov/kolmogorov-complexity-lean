/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Path.Charge
import KolmogorovMathlib.MDLPrediction.Core.FinitePrograms

/-!
# Finite family of winners on a budgeted path

The coding constant precedes the source measure and budget. Extensional measures
selected along the path fit inside one finite complexity sublevel.

Blueprint node: `exp:finite-winner-count`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- Every winner has bounded complexity and the entire path uses only a finite
family of proper computable measures. Blueprint node `exp:finite-winner-count`. -/
theorem exp_finite_winner_count (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : Measure CantorSeq) [IsProbabilityMeasure P],
      IsComputableMeasure P → ∀ (w : CantorSeq) (D : ℕ),
        PathBudget P w D → ∀ (choose : BitString → Measure CantorSeq),
          IsGlobalChoice U hU choose →
            ∃ F : Set (Measure CantorSeq), F.Finite ∧
              F.ncard ≤ 2 ^ ((3 * (computableMeasureComplexity U P).toNat +
                D + c) / 2 + 1) ∧
              (∀ Q ∈ F, IsProbabilityMeasure Q ∧ IsComputableMeasure Q ∧
                2 * (computableMeasureComplexity U Q).toNat ≤
                  3 * (computableMeasureComplexity U P).toNat + D + c) ∧
              (∀ n, choose (cantorPrefix w n) ∈ F) := by
  obtain ⟨c, hc⟩ := KA_le_measure_code U hU
  use c
  intro P hP_prob hP_comp w D hbudget choose hchoose
  let a := (3 * (computableMeasureComplexity U P).toNat + D + c) / 2
  have Hfin := finite_models_complexity_le U hU a
  let F := {Q : Measure CantorSeq | IsProbabilityMeasure Q ∧
      IsComputableMeasure Q ∧ (computableMeasureComplexity U Q).toNat ≤ a}
  use F
  refine ⟨Hfin.1, ?_, ?_, ?_⟩
  · exact le_of_lt Hfin.2
  · intro Q hQ
    rcases hQ with ⟨hQ_prob, hQ_comp, hQ_le⟩
    refine ⟨hQ_prob, hQ_comp, ?_⟩
    omega
  · intro n
    have h_win := hchoose (cantorPrefix w n)
    unfold IsGlobalWinner at h_win
    rcases h_win with ⟨hQ_prob, hQ_comp, hQ_pos, hQ_min⟩
    have h_bound := winner_bounds_complexity U hU c hc P hP_comp w D n hbudget
      (choose (cantorPrefix w n)) (hchoose (cantorPrefix w n))
    dsimp [F]
    refine ⟨hQ_prob, hQ_comp, ?_⟩
    omega


end Kolmogorov.MDLPrediction
