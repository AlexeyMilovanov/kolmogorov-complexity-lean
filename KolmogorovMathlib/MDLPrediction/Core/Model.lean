/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.Basic
import KolmogorovMathlib.Solomonoff.MeasureIndex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.EReal.Basic

/-!
# Computable probability models and MDL scores

The model is a computable proper measure on Cantor space. Its probability and computability
fields are propositions, so equality of models is determined by equality of measures.
Scores use `EReal` to give zero-mass cylinders infinite score. All real logarithms below
are used only with explicit positive-mass hypotheses. Complexity uses the unrounded `KA`.

The source-audit remarks `audit:notation` and `audit:scope` fix the bit argument, the
global proper-measure domain, and classical minimizer ties. `audit:pair` treats the
pairwise intermediate object as a continuous tree semimeasure under two-sided dyadic
measure representations. `audit:deficiency` uses natural multiplicative budgets and
the unrounded a priori complexity; no real log is interpreted at zero mass.

Blueprint nodes: `base:model`, `base:score`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- A computable probability measure regarded as an MDL model.
Blueprint node `base:model`. -/
structure Model (U : Map) (hU : IsOptimalPrefixConditional U) where
  measure : Measure CantorSeq
  probability : IsProbabilityMeasure measure
  computable : IsComputableMeasure measure

/-- The finite prefix complexity of a computable probability model.
Blueprint node `base:model`. -/
noncomputable def Model.k {U : Map} {hU : IsOptimalPrefixConditional U}
    (P : Model U hU) : ℕ := (computableMeasureComplexity U P.measure).toNat

/-- The conditional probability of a model, with value zero at a zero-mass node.
Blueprint node `base:model`. -/
noncomputable def Model.conditional {U : Map} {hU : IsOptimalPrefixConditional U}
    (P : Model U hU) (x : BitString) (b : Bool) : ℝ :=
  condProb (cantorMass P.measure) x b

/-- Model conditionals lie in the unit interval, including the zero-mass convention.
Blueprint node `base:model`. -/
theorem Model.conditional_bounds {U : Map} {hU : IsOptimalPrefixConditional U}
    (P : Model U hU) (x : BitString) (b : Bool) :
    0 ≤ P.conditional x b ∧ P.conditional x b ≤ 1 := by
  have : IsProbabilityMeasure P.measure := P.probability
  constructor
  · apply condProb_nonneg
  · by_cases h : cantorMass P.measure x = 0
    · unfold Model.conditional condProb
      simp [h]
    · have h1 : condProb (cantorMass P.measure) x false +
          condProb (cantorMass P.measure) x true = 1 := by
        exact condProb_cantorMass_add_eq_one P.measure h
      unfold Model.conditional
      cases b
      · have h2 : 0 ≤ condProb (cantorMass P.measure) x true := condProb_nonneg _ _ _
        linarith
      · have h2 : 0 ≤ condProb (cantorMass P.measure) x false := condProb_nonneg _ _ _
        linarith

/-- Model equality is extensional equality of the underlying measures.
Blueprint node `base:model`. -/
@[ext] theorem Model.ext {U : Map} {hU : IsOptimalPrefixConditional U}
    {P Q : Model U hU} (h : P.measure = Q.measure) : P = Q := by
  cases P with
  | mk μ hp hc =>
    cases Q with
    | mk ν hq hd =>
      cases h
      rfl

/-- The global MDL score, infinite when the candidate assigns zero cylinder mass.
Blueprint node `base:score`. -/
noncomputable def score (U : Map) (_hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) (x : BitString) : EReal :=
  if cantorMass P x = 0 then ⊤
  else (3 * ((computableMeasureComplexity U P).toNat : ℝ) -
    Real.logb 2 (cantorMass P x).toReal : ℝ)

/-- On a positive cylinder, the score dominates three times model complexity.
Blueprint node `base:score`. -/
theorem score_ge_complexity (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (x : BitString)
    (hpos : 0 < cantorMass P x) :
    ((3 * ((computableMeasureComplexity U P).toNat : ℝ) : ℝ) : EReal) ≤
      score U hU P x := by
  unfold score
  have hne : cantorMass P x ≠ 0 := hpos.ne'
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hne h))]
  simp only [EReal.coe_le_coe_iff]
  have ht : cantorMass P x ≤ 1 := prob_le_one
  have htop : cantorMass P x ≠ ⊤ := measure_ne_top P _
  have hl : Real.logb 2 (cantorMass P x).toReal ≤ 0 := by
    apply Real.logb_nonpos
    · norm_num
    · exact (ENNReal.toReal_pos hne htop).le
    · apply ENNReal.toReal_le_of_le_ofReal zero_le_one
      rw [ENNReal.ofReal_one]
      exact ht
  linarith

/-- The global score is nonnegative for every proper model.
Blueprint node `base:score`. -/
theorem score_nonneg (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (x : BitString) :
    (0 : EReal) ≤ score U hU P x := by
  rw [score]
  split_ifs with h
  · exact le_top
  · refine EReal.coe_nonneg.mpr ?_
    have h1 : 0 ≤ (cantorMass P x).toReal := ENNReal.toReal_nonneg
    have h2 : cantorMass P x ≤ 1 := prob_le_one
    have h3 : (cantorMass P x).toReal ≤ 1 := by
      have : (cantorMass P x).toReal ≤ (1 : ℝ≥0∞).toReal := by
        apply (ENNReal.toReal_le_toReal _ _).mpr
        · exact h2
        · exact ne_top_of_le_ne_top (by norm_num) h2
        · exact ENNReal.one_ne_top
      exact this
    have h4 : Real.logb 2 (cantorMass P x).toReal ≤ 0 := by
      have h4a : Real.logb 2 (cantorMass P x).toReal =
          Real.log (cantorMass P x).toReal / Real.log 2 := by
        rfl
      rw [h4a, div_le_iff₀]
      · rw [zero_mul]
        exact Real.log_nonpos h1 h3
      · refine Real.log_pos ?_
        norm_num
    have h5 : 0 ≤ (3 : ℝ) * ((computableMeasureComplexity U P).toNat : ℝ) := by
      apply mul_nonneg
      · norm_num
      · exact Nat.cast_nonneg _
    linarith

/-- Eligibility and minimality of a global score winner.
Blueprint node `base:score`. -/
def IsGlobalWinner (U : Map) (hU : IsOptimalPrefixConditional U)
    (Q : Measure CantorSeq) (x : BitString) : Prop :=
  IsProbabilityMeasure Q ∧ IsComputableMeasure Q ∧ 0 < cantorMass Q x ∧
    ∀ R : Measure CantorSeq, IsProbabilityMeasure R → IsComputableMeasure R →
      0 < cantorMass R x → score U hU Q x ≤ score U hU R x

end Kolmogorov.MDLPrediction
