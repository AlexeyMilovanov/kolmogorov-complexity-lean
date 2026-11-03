/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Presentation
import KolmogorovMathlib.MDLPrediction.Core.ArgminGeneric
import KolmogorovMathlib.MDLPrediction.Core.FinitePrograms
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctionDyadic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Relative complexity, class score, and minimizers

Relative complexity minimizes numeric index complexity over every presentation index
of the same measure. The score is infinite at zero cylinder mass. The classical
predictor uses the fixed value `1 / 2` if every class member has zero mass.
Blueprint nodes: `enum:argmin`, `enum:relative-attained`, `enum:relative-finite`, `enum:score`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- Minimum prefix complexity among indices representing a class measure.
Blueprint node `enum:score`. -/
noncomputable def classComplexityENat (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq) : ENat :=
  ⨅ i : {i : ℕ // A.model i = Q}, KPNat U i.1

/-- The natural relative complexity, finite on the class carrier.
Blueprint node `enum:score`. -/
noncomputable def classComplexity (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq) : ℕ :=
  (classComplexityENat U hU A Q).toNat

/-- A represented class measure has an index attaining its finite relative complexity.
Blueprint node `enum:relative-attained`. -/
theorem enum_relative_attained (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq) (hQ : Q ∈ A.carrier) :
    classComplexityENat U hU A Q ≠ ⊤ ∧
      ∃ i : ℕ, A.model i = Q ∧ KPNat U i = classComplexityENat U hU A Q := by
  rcases hQ with ⟨j, hj⟩
  let S := {i : ℕ // A.model i = Q}
  have : Nonempty S := ⟨⟨j, hj⟩⟩
  have hle : classComplexityENat U hU A Q ≤ KPNat U j := by
    dsimp [classComplexityENat]
    exact iInf_le (fun i : S => KPNat U i.1) ⟨j, hj⟩
  have hfinite : classComplexityENat U hU A Q ≠ ⊤ :=
    ne_top_of_le_ne_top (KPNat_ne_top hU j) hle
  obtain ⟨i, hi⟩ := ENat.exists_eq_iInf (fun i : S => KPNat U i.1)
  refine ⟨hfinite, ⟨i.1, i.2, ?_⟩⟩
  simpa [classComplexityENat] using hi

/-- A relative-complexity sublevel contains at most `2^(a+1)` measures.
Blueprint node `enum:relative-finite`. -/
theorem enum_relative_finite (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (a : ℕ) :
    (Set.Finite {Q : Measure CantorSeq | Q ∈ A.carrier ∧
      classComplexity U hU A Q ≤ a}) ∧
      Set.ncard {Q : Measure CantorSeq | Q ∈ A.carrier ∧
        classComplexity U hU A Q ≤ a} ≤ 2 ^ (a + 1) := by
  have H_base := base_program_count U a
  let I := {i : ℕ | KPNat U i ≤ a}
  have hI_fin : I.Finite := H_base.1
  have hI_card : I.ncard < 2 ^ (a + 1) := H_base.2
  let S := {Q : Measure CantorSeq | Q ∈ A.carrier ∧ classComplexity U hU A Q ≤ a}
  have H_subset : S ⊆ A.model '' I := by
    intro Q hQ
    have hQ_c : Q ∈ A.carrier := hQ.1
    have hQ_le : classComplexity U hU A Q ≤ a := hQ.2
    have H_att := enum_relative_attained U hU A Q hQ_c
    rcases H_att with ⟨h_ne_top, ⟨i, hi_mod, hi_KPNat⟩⟩
    use i
    constructor
    · dsimp [I]
      have H_eq : classComplexityENat U hU A Q = (classComplexity U hU A Q : ENat) := by
        exact ENat.natCast_toNat h_ne_top |>.symm
      rw [hi_KPNat, H_eq]
      exact ENat.natCast_le_natCast.mpr hQ_le
    · exact hi_mod
  have hS_fin : S.Finite := Set.Finite.subset (Set.Finite.image A.model hI_fin) H_subset
  have hS_card : S.ncard ≤ 2 ^ (a + 1) := by
    have h1 : S.ncard ≤ (A.model '' I).ncard :=
      Set.ncard_le_ncard H_subset (Set.Finite.image A.model hI_fin)
    have h2 : (A.model '' I).ncard ≤ I.ncard := Set.ncard_image_le hI_fin
    have h3 : I.ncard ≤ 2 ^ (a + 1) := le_of_lt hI_card
    exact le_trans h1 (le_trans h2 h3)
  exact ⟨hS_fin, hS_card⟩

/-- Relative class score, with infinite score at zero mass.
Blueprint node `enum:score`. -/
noncomputable def classScore (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq) (x : BitString) : EReal :=
  if cantorMass Q x = 0 then ⊤
  else (3 * (classComplexity U hU A Q : ℝ) -
    Real.logb 2 (cantorMass Q x).toReal : ℝ)

/-- At positive mass, the class score is at least three times relative complexity.
Blueprint node `enum:score`. -/
theorem classScore_ge_complexity (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq)
    (hQ : Q ∈ A.carrier) (x : BitString) (hx : 0 < cantorMass Q x) :
    ((3 * (classComplexity U hU A Q : ℝ) : ℝ) : EReal) ≤
      classScore U hU A Q x := by
  dsimp [classScore]
  have hm : cantorMass Q x ≠ 0 := ne_of_gt hx
  rw [ite_eq_right (by exact fun h => (hm h).elim)]
  norm_cast
  have h_le_1 : (cantorMass Q x).toReal ≤ 1 := by
    rcases hQ with ⟨i, hi⟩
    have h2 : cantorMass Q x ≤ 1 := by
      have : IsProbabilityMeasure Q := by
        rw [← hi]
        exact (A.A i).probability
      exact prob_le_one
    have h1 : (1 : ENNReal).toReal = 1 := ENNReal.toReal_one
    rw [← h1]
    apply (ENNReal.toReal_le_toReal
      (ne_of_lt (lt_of_le_of_lt h2 ENNReal.one_lt_top)) ENNReal.one_ne_top).mpr h2
  have h_log : Real.log (cantorMass Q x).toReal ≤ 0 :=
    Real.log_nonpos ENNReal.toReal_nonneg h_le_1
  have h_log2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_logb : Real.logb 2 (cantorMass Q x).toReal ≤ 0 := by
    rw [Real.logb]
    exact div_nonpos_of_nonpos_of_nonneg h_log (le_of_lt h_log2)
  linarith

/-- The score of every proper class model is nonnegative.
Blueprint node `enum:score`. -/
theorem classScore_nonneg (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq)
    (hQ : Q ∈ A.carrier) (x : BitString) :
    (0 : EReal) ≤ classScore U hU A Q x := by
  dsimp [classScore]
  split_ifs with h
  · exact le_top
  · norm_cast
    have hc : (0 : ℝ) ≤ 3 * (classComplexity U hU A Q : ℝ) := by positivity
    obtain ⟨i, hi⟩ := hQ
    have h_prob : IsProbabilityMeasure Q := by
      rw [←hi]
      exact (A.A i).probability
    have hm : (cantorMass Q x).toReal ≤ 1 := by
      have : IsProbabilityMeasure Q := h_prob
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)
    have hm0 : 0 ≤ (cantorMass Q x).toReal := ENNReal.toReal_nonneg
    have hl : Real.logb 2 (cantorMass Q x).toReal ≤ 0 := by
      rw [Real.logb]
      apply div_nonpos_of_nonpos_of_nonneg
      · exact Real.log_nonpos hm0 hm
      · exact Real.log_nonneg (by norm_num)
    linarith

/-- Eligible class minimizers have positive mass and least relative score.
Blueprint node `enum:argmin`. -/
def IsClassWinner (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (Q : Measure CantorSeq) (x : BitString) : Prop :=
  Q ∈ A.carrier ∧ 0 < cantorMass Q x ∧
    ∀ R ∈ A.carrier, 0 < cantorMass R x →
      classScore U hU A Q x ≤ classScore U hU A R x

/-- A class score has a minimizer whenever an eligible candidate exists.
Blueprint node `enum:argmin`. -/
theorem enum_argmin (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (x : BitString)
    (hx : ∃ Q ∈ A.carrier, 0 < cantorMass Q x) :
    ∃ Q : Measure CantorSeq, IsClassWinner U hU A Q x := by
  let E := { Q : Measure CantorSeq // Q ∈ A.carrier ∧ 0 < cantorMass Q x }
  have hE : Nonempty E := by
    rcases hx with ⟨Q, hQ, hQpos⟩
    exact ⟨⟨Q, hQ, hQpos⟩⟩
  let k (q : E) : ℕ := classComplexity U hU A q.1
  let m (q : E) : ℝ := (cantorMass q.1 x).toReal
  have hm : ∀ q : E, 0 < m q ∧ m q ≤ 1 := by
    intro q
    have h1 : 0 < cantorMass q.1 x := q.2.2
    have h2 : cantorMass q.1 x ≤ 1 := by
      rcases q.2.1 with ⟨i, hi⟩
      have hp : IsProbabilityMeasure (A.model i) := (A.A i).probability
      rw [← hi]
      exact prob_le_one
    constructor
    · have htop : cantorMass q.1 x ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h2
      exact (ENNReal.toReal_pos h1.ne' htop)
    · apply ENNReal.toReal_le_of_le_ofReal zero_le_one
      rw [ENNReal.ofReal_one]
      exact h2
  have hfin : ∀ a, Set.Finite {q : E | k q ≤ a} := by
    intro a
    let S := {Q : Measure CantorSeq | Q ∈ A.carrier ∧ classComplexity U hU A Q ≤ a}
    have hS : Set.Finite S := (enum_relative_finite U hU A a).1
    have hsub : (fun (q : E) => q.1) '' {q : E | k q ≤ a} ⊆ S := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q.2.1, hq⟩
    have hinj : Set.InjOn (fun (q : E) => q.1) {q : E | k q ≤ a} := by
      intro x hx y hy hxy
      exact Subtype.ext hxy
    exact Set.Finite.of_finite_image (Set.Finite.subset hS hsub) hinj
  have ⟨q_min, hq_min⟩ := @base_argmin_generic E k m hm hfin hE
  use q_min.1
  constructor
  · exact q_min.2.1
  · constructor
    · exact q_min.2.2
    · intro R hR hRpos
      have hR_E : R ∈ A.carrier ∧ 0 < cantorMass R x := ⟨hR, hRpos⟩
      let r : E := ⟨R, hR_E⟩
      have hq := hq_min r
      unfold classScore
      dsimp [k, m] at hq
      have h1 : cantorMass (q_min.1) x ≠ 0 := q_min.2.2.ne'
      have h2 : cantorMass R x ≠ 0 := hRpos.ne'
      rw [ite_eq_right_iff.mpr (fun h => False.elim (h1 h)),
          ite_eq_right_iff.mpr (fun h => False.elim (h2 h))]
      simp only [EReal.coe_le_coe_iff]
      exact hq

/-- A class choice selects minimizers at each string with a positive candidate.
Blueprint node `enum:argmin`. -/
def IsClassChoice (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (choose : BitString → Measure CantorSeq) : Prop :=
  ∀ x, (∃ Q ∈ A.carrier, 0 < cantorMass Q x) →
    IsClassWinner U hU A (choose x) x

/-- Classical class minimizer choice, using the first class member at all-zero strings.
Blueprint node `enum:argmin`. -/
noncomputable def classChoice (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (x : BitString) : Measure CantorSeq := by
  classical
  exact if hx : ∃ Q ∈ A.carrier, 0 < cantorMass Q x then
    Classical.choose (enum_argmin U hU A x hx)
  else A.model 0

/-- The classical choice selects an eligible minimizer whenever one exists.
Blueprint node `enum:argmin`. -/
theorem classChoice_spec (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    IsClassChoice U hU A (classChoice U hU A) := by
  intro x hx
  simp only [classChoice, dite_eq_left hx]
  exact Classical.choose_spec (enum_argmin U hU A x hx)

/-- Conditional prediction from any class minimizer choice.
Blueprint node `enum:argmin`. -/
noncomputable def classPredictor (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (choose : BitString → Measure CantorSeq)
    (x : BitString) (b : Bool) : ℝ := by
  classical
  exact if ∃ Q ∈ A.carrier, 0 < cantorMass Q x then
    condProb (cantorMass (choose x)) x b
  else 1 / 2

/-- At an all-zero class cylinder the predictor uses the fixed half-half default.
Blueprint node `enum:argmin`. -/
theorem classPredictor_default (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (choose : BitString → Measure CantorSeq)
    (x : BitString) (hx : ¬ ∃ Q ∈ A.carrier, 0 < cantorMass Q x) (b : Bool) :
    classPredictor U hU A choose x b = 1 / 2 := by
  simp [classPredictor, hx]
end Kolmogorov.MDLPrediction
