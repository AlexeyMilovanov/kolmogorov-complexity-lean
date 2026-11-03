/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Budget
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria

/-!
# Random paths and a priori deficiency

The Levin--Schnorr criterion is expressed with a natural multiplicative path budget.
For a nonrandom path, positive-mass real deficiencies eventually exceed every real bound;
at a zero-mass prefix the disjunction records the undefined log interpretation.

Blueprint nodes: `rand:diverges`, `rand:levin`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- Martin--Löf randomness is equivalent to an a priori path budget.
Blueprint node `rand:levin`. -/
theorem random_iff_exists_budget (U : Map) (_hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) (w : CantorSeq) [IsProbabilityMeasure P]
    (hP : IsComputableMeasure P) :
    IsMartinLofRandom P w ↔ ∃ D : ℕ, PathBudget P w D := by
  exact Kolmogorov.isMartinLofRandom_iff_boundedAPrioriDeficiency hP w

/-- Every prefix of a random path has positive mass under its computable proper measure.
Blueprint node `rand:levin`. -/
theorem random_prefix_mass_pos (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P] (hP : IsComputableMeasure P)
    (w : CantorSeq) (hw : IsMartinLofRandom P w) (n : ℕ) :
    0 < cantorMass P (cantorPrefix w n) := by
  obtain ⟨D, hD⟩ := (random_iff_exists_budget U hU P w hP).mp hw
  exact base_budget_positive P w D n hD

/-- A nonrandom path has eventually unbounded a priori deficiency wherever its cylinder
mass remains positive. Blueprint node `rand:diverges`. -/
theorem apriori_deficiency_tendsto_of_not_random (U : Map)
    (_hU : IsOptimalPrefixConditional U) (Q : Measure CantorSeq) (w : CantorSeq)
    [IsProbabilityMeasure Q] (hQ : IsComputableMeasure Q)
    (hnot : ¬ IsMartinLofRandom Q w) :
    ∀ B : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      cantorMass Q (cantorPrefix w n) = 0 ∨
        B < -Real.logb 2 (cantorMass Q (cantorPrefix w n)).toReal -
          KA (cantorPrefix w n) := by
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  obtain ⟨c, hc⟩ := exists_const_KA_le_KMOf hD
  intro B
  obtain ⟨k, hk⟩ : ∃ k : ℕ, B + c < (k : ℝ) := exists_nat_gt (B + c)
  obtain ⟨N, hN⟩ := tendsto_monotoneDeficiency_of_not_isMartinLofRandom hQ hD hnot k
  refine ⟨N, fun n hn => ?_⟩
  rcases eq_or_ne (cantorMass Q (cantorPrefix w n)) 0 with hzero | hpos
  · exact Or.inl hzero
  right
  have hfin : KMOf D (cantorPrefix w n) ≠ ⊤ := KMOf_ne_top_of_isOptimal hD _
  have hle : (2 : ENNReal) ^ k * cantorMass Q (cantorPrefix w n) ≤
      (2 : ENNReal)⁻¹ ^ (KMOf D (cantorPrefix w n)).toNat := by
    have h := hN n hn
    rwa [← ENat.natCast_toNat hfin, complexityWeight_coe] at h
  have hq : 0 < (cantorMass Q (cantorPrefix w n)).toReal :=
    ENNReal.toReal_pos hpos (measure_ne_top Q _)
  have hreal : (2 : ℝ) ^ k * (cantorMass Q (cantorPrefix w n)).toReal ≤
      (2 : ℝ)⁻¹ ^ (KMOf D (cantorPrefix w n)).toNat := by
    have h := ENNReal.toReal_mono (by simp) hle
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv] using h
  have hlog := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) hreal
  rw [Real.logb_mul (by positivity) hq.ne', Real.logb_pow, Real.logb_pow, Real.logb_inv,
    Real.logb_self_eq_one one_lt_two] at hlog
  have hKA := hc (cantorPrefix w n)
  linarith

/-- Once a path has a zero-mass prefix, all later prefixes also have zero mass.
Blueprint node `rand:diverges`. -/
theorem zero_mass_persists (Q : Measure CantorSeq) (w : CantorSeq)
    (n : ℕ) (hzero : cantorMass Q (cantorPrefix w n) = 0) :
    ∀ m ≥ n, cantorMass Q (cantorPrefix w m) = 0 := by
  intro m hmn
  have H : cantorCylinder (cantorPrefix w m) ⊆ cantorCylinder (cantorPrefix w n) :=
    cantorCylinder_subset_of_prefix (cantorPrefix_mono w hmn)
  have H2 : Q (cantorCylinder (cantorPrefix w m)) ≤ Q (cantorCylinder (cantorPrefix w n)) :=
    measure_mono H
  unfold cantorMass at hzero ⊢
  rw [hzero] at H2
  exact nonpos_iff_eq_zero.mp H2

end Kolmogorov.MDLPrediction
