/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CubeStochasticity
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyValue

/-!
# The mass of the non-stochastic strings under a weaker hypothesis

The two-sided bound on `nonStochasticMass` holds already when
`alpha + beta < n - O(log n)`, rather than under the stronger gap hypothesis of
`nonStochasticMass_bounds`.

SUV Exercise 365, p. 501.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution

/-- The upper bound on the non-stochastic mass under the weaker hypothesis. -/
private theorem nonStochasticMass_upper_bound_weak (U : Map) (C_imp : ℕ) (c : ℕ)
    (hc_imp : C_imp ≤ c)
    (hC_imp : ∀ (n alpha : ℕ),
      (2 : ℝ≥0∞)⁻¹ ^ (logSlack C_imp n) *
        nonStochasticAprioriMass U n alpha (logSlack C_imp n) ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha)
    (n alpha beta : ℕ)
    (hgap2 : alpha + logSlack c n < beta) :
    nonStochasticMass U n alpha beta ≤ (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ alpha := by
  have hS_imp : logSlack C_imp n ≤ logSlack c n := logSlack_mono_left hc_imp n
  have h_beta_gt : logSlack C_imp n < beta := by
    have h1 : logSlack C_imp n ≤ logSlack c n := hS_imp
    omega
  have h_stoch_imp : ∀ x, IsStochastic U x alpha (logSlack C_imp n) →
      IsStochastic U x alpha beta := fun x h => h.mono_beta (by omega)
  have h_mass_le : nonStochasticMass U n alpha beta ≤
      nonStochasticAprioriMass U n alpha (logSlack C_imp n) := by
    unfold nonStochasticMass nonStochasticAprioriMass
    refine ENNReal.tsum_le_tsum (fun x => ?_)
    by_cases hcond : x.length = n ∧ IsNonStochastic U x alpha beta
    · rw [if_pos hcond]
      have hcond2 : x.length = n ∧ ¬ IsStochastic U x alpha (logSlack C_imp n) := by
        refine ⟨hcond.1, fun hst => hcond.2 (h_stoch_imp x hst)⟩
      rw [if_pos hcond2]
      exact complexityWeight_KP_le_aprioriMeasure U x []
    · rw [if_neg hcond]
      exact zero_le
  have h_apriori_bound := hC_imp n alpha
  have h2_inv_le : (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) ≤ (2 : ℝ≥0∞)⁻¹ ^ (logSlack C_imp n) :=
    pow_le_pow_right_of_le_one' (by norm_num) hS_imp
  have h_prod_le : (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) * nonStochasticMass U n alpha beta ≤
      (2 : ℝ≥0∞)⁻¹ ^ alpha := by
    calc (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) * nonStochasticMass U n alpha beta
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (logSlack C_imp n) *
          nonStochasticAprioriMass U n alpha (logSlack C_imp n) :=
          mul_le_mul' h2_inv_le h_mass_le
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ alpha := h_apriori_bound
  have h2_cancel : (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  calc nonStochasticMass U n alpha beta
      = 1 * nonStochasticMass U n alpha beta := (one_mul _).symm
    _ = ((2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ (logSlack c n)) *
          nonStochasticMass U n alpha beta := by rw [h2_cancel]
    _ = (2 : ℝ≥0∞) ^ (logSlack c n) *
          ((2 : ℝ≥0∞)⁻¹ ^ (logSlack c n) * nonStochasticMass U n alpha beta) := by ring
    _ ≤ (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ alpha := by gcongr

/-- **Exercise 365.** Theorem 251 holds already under the weaker hypothesis
`alpha + beta < n - O(log n)`. -/
theorem nonStochasticMass_bounds_weak (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n alpha beta : ℕ),
      alpha + beta + logSlack c n < n →
      alpha + logSlack c n < beta →
      (2 : ℝ≥0∞)⁻¹ ^ (alpha + logSlack c n) ≤ nonStochasticMass U n alpha beta ∧
        nonStochasticMass U n alpha beta ≤ (2 : ℝ≥0∞) ^ (logSlack c n) * (2 : ℝ≥0∞)⁻¹ ^ alpha := by
  classical
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨c_code, hc_code⟩ : ∃ c : Code, IsCodeFor c V := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨C_imp, hC_imp⟩ := prop_nonstochastic_counting_improved V U hV hU c_code hc_code
  obtain ⟨c_anti, h_anti⟩ := exists_antistochastic U hU
  obtain ⟨cOpt, hOpt⟩ := stochasticity_to_optimal_set_thm U hU
  obtain ⟨cProf, hProf⟩ := isOptimalSetStochastic_imp_profile U hU
  obtain ⟨cFoldOpt, hFoldOpt⟩ := logSlack_linear_bound cOpt 3 0
  obtain ⟨cFoldProf, hFoldProf⟩ := logSlack_linear_bound cProf 6 0
  set c := C_imp + 3 * c_anti + 2 * cFoldOpt + 2 * cFoldProf + 10
  refine ⟨c, fun n alpha beta hgap1 hgap2 => ?_⟩
  have hc_imp : C_imp ≤ c := by dsimp [c]; omega
  constructor
  · -- Lower bound
    have hM1 : n + alpha + beta ≤ 3 * n := by
      have : alpha < n := by unfold logSlack at hgap1; omega
      have : beta < n := by unfold logSlack at hgap1; omega
      omega
    set S1 := logSlack cOpt (n + alpha + beta)
    have hS1_le : S1 ≤ logSlack cFoldOpt n := by
      calc S1 = logSlack cOpt (n + alpha + beta) := rfl
        _ ≤ logSlack cOpt (3 * n) := logSlack_mono_right cOpt hM1
        _ ≤ logSlack cFoldOpt n := hFoldOpt n
    set alpha' := alpha + S1
    set beta' := beta + S1
    set S2_bound := logSlack cFoldProf n
    set k := alpha' + S2_bound + logSlack c_anti n + 1
    have hk_le : k ≤ n := by
      calc k = alpha + S1 + logSlack cFoldProf n + logSlack c_anti n + 1 := rfl
        _ ≤ alpha + logSlack cFoldOpt n + logSlack cFoldProf n + logSlack c_anti n + 1 := by omega
        _ ≤ alpha + logSlack c n := by
          dsimp [c]
          unfold logSlack
          nlinarith
        _ ≤ n := by omega
    obtain ⟨x, hx_len, hx_KP_ub, hx_KP_lb, hx_anti⟩ := h_anti n k hk_le
    have hnstoch : IsNonStochastic U x alpha beta := by
      intro hstoch
      have hOpt_spec := hOpt x n alpha beta hx_len hstoch
      obtain ⟨kx, hkx⟩ : ∃ kx : ℕ, KPPlain U x = (kx : ℕ∞) := by
        obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp (KPPlain_ne_top_of_optimal U hU x)
        exact ⟨p, hp.symm⟩
      have hkx_ub : kx ≤ k + logSlack c_anti n := by
        rw [hkx] at hx_KP_ub
        exact (Nat.cast_le (α := ENat)).mp hx_KP_ub
      have hkx_lb : k ≤ kx + logSlack c_anti n := by
        rw [hkx] at hx_KP_lb
        exact (Nat.cast_le (α := ENat)).mp hx_KP_lb
      set j := kx + beta' - alpha'
      have h_arith : KPPlain U x + (beta' : ENat) ≤ (alpha' : ENat) + (j : ENat) := by
        rw [hkx]
        norm_cast
        dsimp [j, alpha', beta', S1]
        omega
      have hProf_spec := hProf x alpha' beta' j hOpt_spec h_arith
      set M2 := alpha' + beta' + j
      have hM2 : M2 ≤ 6 * n := by
        dsimp [M2, j, alpha', beta', S1, k, S2_bound, c] at *
        unfold logSlack at *
        have : S1 ≤ cFoldOpt * n.bits.length + cFoldOpt := hS1_le
        omega
      set S2 := logSlack cProf M2
      have hS2_le : S2 ≤ S2_bound := by
        calc S2 = logSlack cProf M2 := rfl
          _ ≤ logSlack cProf (6 * n) := logSlack_mono_right cProf hM2
          _ ≤ logSlack cFoldProf n := hFoldProf n
      have hProf_spec' : InDescriptionProfile U x (alpha' + S2) (j + 1) := hProf_spec
      have h_cond_i : alpha' + S2 + logSlack c_anti n < k := by
        dsimp [k, alpha', S2_bound]
        have : S2 ≤ S2_bound := hS2_le
        omega
      have hanti_spec := hx_anti (alpha' + S2) (j + 1) h_cond_i hProf_spec'
      have h_alpha_le_kx : alpha' ≤ kx := by
        dsimp [alpha', k] at hkx_lb
        omega
      have h1 : n ≤ alpha' + S2 + (j + 1) + logSlack c_anti n := hanti_spec
      have h2 : alpha' + S2 + (j + 1) + logSlack c_anti n =
          kx + beta' + S2 + logSlack c_anti n + 1 := by
        dsimp [j]
        omega
      have h3 : kx + beta' + S2 + logSlack c_anti n + 1 ≤
          (k + logSlack c_anti n) + (beta + S1) + S2 + logSlack c_anti n + 1 := by
        dsimp [beta']
        omega
      have h4 : (k + logSlack c_anti n) + (beta + S1) + S2 + logSlack c_anti n + 1 =
          alpha + beta + 2 * S1 + S2 + S2_bound + 3 * logSlack c_anti n + 2 := by
        dsimp [k, alpha']
        ring
      have h_anti_ub : n ≤ alpha + beta + 2 * S1 + S2 + S2_bound + 3 * logSlack c_anti n + 2 := by
        linarith
      have h_anti_ub2 : 2 * S1 + S2 + S2_bound + 3 * logSlack c_anti n + 2 ≤ logSlack c n := by
        have hS1 : S1 ≤ cFoldOpt * n.bits.length + cFoldOpt := hS1_le
        have hS2 : S2 ≤ cFoldProf * n.bits.length + cFoldProf := hS2_le
        dsimp [c, S2_bound]
        unfold logSlack
        nlinarith
      have h_contra : n < n := by linarith
      exact lt_irrefl n h_contra
    have h_mem_sum : (if x.length = n ∧ IsNonStochastic U x alpha beta
        then complexityWeight (KPPlain U x) else 0) ≤ nonStochasticMass U n alpha beta :=
      ENNReal.le_tsum x
    rw [if_pos ⟨hx_len, hnstoch⟩] at h_mem_sum
    have h_KPPlain_le_ENat : KPPlain U x ≤ ((alpha + logSlack c n : ℕ) : ENat) := by
      refine hx_KP_ub.trans ?_
      norm_cast
      have h1 : S1 ≤ cFoldOpt * n.bits.length + cFoldOpt := hS1_le
      dsimp [k, alpha', S2_bound, c]
      unfold logSlack
      nlinarith
    have h_weight_le : (2 : ℝ≥0∞)⁻¹ ^ (alpha + logSlack c n) ≤ complexityWeight (KPPlain U x) := by
      have h_cw := complexityWeight_le_of_le h_KPPlain_le_ENat
      rw [complexityWeight_coe] at h_cw
      exact h_cw
    exact h_weight_le.trans h_mem_sum
  · -- Upper bound
    exact nonStochasticMass_upper_bound_weak U C_imp c hc_imp hC_imp n alpha beta hgap2

end Kolmogorov
