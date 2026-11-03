/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.ArgminGeneric
import KolmogorovMathlib.MDLPrediction.Core.FinitePrograms
import KolmogorovMathlib.MDLPrediction.Core.UniformModel

/-!
# Global score minimizers and their predictors

Every finite string has an eligible uniform-measure competitor. A minimizer is chosen
classically, while later statements accept every choice function satisfying minimality.
The conditional at a zero-mass node is zero; a chosen winner always has positive mass.

Blueprint nodes: `base:argmin`, `base:predictor`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

open scoped ENNReal

/-- Proper computable measures assigning positive mass to a string. -/
private def eligible (x : BitString) : Type :=
  {P : Measure CantorSeq // IsProbabilityMeasure P ∧ IsComputableMeasure P ∧ 0 < cantorMass P x}

/-- The uniform measure witnesses nonemptiness of eligible measures. -/
private noncomputable def eligible_uniform (x : BitString) : eligible x :=
  ⟨uniformMeasure, (base_uniform_positive x).1, (base_uniform_positive x).2.1,
    (base_uniform_positive x).2.2.2⟩

/-- The natural valued complexity of a measure. -/
private noncomputable def candidateComplexity (U : Map) (P : Measure CantorSeq) : ℕ :=
  (computableMeasureComplexity U P).toNat
/-- The real cylinder mass of an eligible measure. -/
private noncomputable def candidateMass (x : BitString) (P : eligible x) : ℝ :=
    (cantorMass P.val x).toReal

/-- Eligible cylinder mass lies in the interval `(0, 1]`. -/
private lemma candidateMass_bounds (x : BitString) (P : eligible x) : 0 < candidateMass
    x P ∧ candidateMass x P ≤ 1 := by
  dsimp [candidateMass]
  have hP1 : IsProbabilityMeasure P.val := P.property.1
  have hne : cantorMass P.val x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one (μ := P.val))
  constructor
  · rw [ENNReal.toReal_pos_iff]
    exact ⟨P.property.2.2, lt_top_iff_ne_top.mpr hne⟩
  · have hone : (1 : ℝ) = (1 : ℝ≥0∞).toReal := by simp
    rw [hone, ENNReal.toReal_le_toReal hne ENNReal.one_ne_top]
    exact prob_le_one

/-- On eligible measures the score has its finite real formula. -/
private lemma score_eq (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString)
    (P : eligible x) :
    score U hU P.val x = ((3 * (candidateComplexity U P.val : ℝ) - Real.logb 2
        (candidateMass x P)) : ℝ) := by
  dsimp [score, candidateComplexity, candidateMass]
  have hne : cantorMass P.val x ≠ 0 := P.property.2.2.ne'
  simp only [hne, ↓reduceIte]

/-- Eligible measures of bounded complexity form a finite set. -/
private lemma finite_level (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) (a : ℕ) :
    Set.Finite {q : eligible x | candidateComplexity U q.val ≤ a} := by
  have H := (finite_models_complexity_le U hU a).1
  let f : eligible x → Measure CantorSeq := fun q => q.val
  have hf : Set.InjOn f {q : eligible x | candidateComplexity U q.val ≤ a} := by
    intro q1 _ q2 _ hq
    exact Subtype.ext hq
  have hmaps : Set.MapsTo f {q : eligible x | candidateComplexity U q.val ≤ a}
    {P | IsProbabilityMeasure P ∧ IsComputableMeasure P ∧ candidateComplexity U P ≤ a} := by
    intro q hq
    exact ⟨q.property.1, q.property.2.1, hq⟩
  exact Set.Finite.of_injOn hmaps hf H

/-- The generic minimum principle gives an eligible score minimizer. -/
private lemma exists_argmin_from_generic (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) :
    ∃ Q : eligible x, ∀ R : eligible x,
      score U hU Q.val x ≤ score U hU R.val x := by
  let k_fun (P : eligible x) := candidateComplexity U P.val
  have _inst : Nonempty (eligible x) := ⟨eligible_uniform x⟩
  have H := base_argmin_generic k_fun (candidateMass x) (candidateMass_bounds x)
      (finite_level U hU x)
  rcases H with ⟨Q, hQ⟩
  use Q
  intro R
  have hsQ := score_eq U hU x Q
  have hsR := score_eq U hU x R
  rw [hsQ, hsR]
  exact EReal.coe_le_coe_iff.mpr (hQ R)

/-- At every string, the global MDL score has an eligible minimizer.
Blueprint node `base:argmin`. -/
theorem exists_argmin (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) : ∃ Q : Measure CantorSeq, IsGlobalWinner U hU Q x := by
  have h := exists_argmin_from_generic U hU x
  rcases h with ⟨Q, hQ⟩
  use Q.val
  dsimp [IsGlobalWinner]
  refine ⟨Q.property.1, Q.property.2.1, Q.property.2.2, ?_⟩
  intro R hR hC hpos
  exact hQ ⟨R, hR, hC, hpos⟩

/-- A choice function selects a global winner at every string.
Blueprint node `base:predictor`. -/
def IsGlobalChoice (U : Map) (hU : IsOptimalPrefixConditional U)
    (choose : BitString → Measure CantorSeq) : Prop :=
  ∀ x, IsGlobalWinner U hU (choose x) x

/-- One classical global minimizer choice, with no computability claim.
Blueprint node `base:predictor`. -/
noncomputable def globalChoice (U : Map) (hU : IsOptimalPrefixConditional U) :
    BitString → Measure CantorSeq :=
  fun x => Classical.choose (exists_argmin U hU x)

/-- The classical choice satisfies global score minimality at every string.
Blueprint node `base:predictor`. -/
theorem globalChoice_spec (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsGlobalChoice U hU (globalChoice U hU) := by
  intro x
  exact Classical.choose_spec (exists_argmin U hU x)

/-- The conditional predictor associated to any global minimizer choice.
Blueprint node `base:predictor`. -/
noncomputable def predictor (U : Map) (_hU : IsOptimalPrefixConditional U)
    (choose : BitString → Measure CantorSeq) (x : BitString) (b : Bool) : ℝ :=
  condProb (cantorMass (choose x)) x b

/-- The two predictions sum to one for every valid winner choice.
Blueprint node `base:predictor`. -/
theorem predictor_add_eq_one (U : Map) (hU : IsOptimalPrefixConditional U)
    (choose : BitString → Measure CantorSeq) (hchoose : IsGlobalChoice U hU choose)
    (x : BitString) :
    predictor U hU choose x false + predictor U hU choose x true = 1 := by
  have h_winner := hchoose x
  unfold IsGlobalWinner at h_winner
  obtain ⟨h_prob, _h_comp, h_pos, _h_min⟩ := h_winner
  unfold predictor
  have : IsProbabilityMeasure (choose x) := h_prob
  have h_pos_ne_zero : cantorMass (choose x) x ≠ 0 := ne_of_gt h_pos
  exact condProb_cantorMass_add_eq_one (choose x) h_pos_ne_zero

end Kolmogorov.MDLPrediction
