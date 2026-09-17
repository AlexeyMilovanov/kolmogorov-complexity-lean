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
import KolmogorovMathlib.AlgorithmicStatistics.StochasticityProfile
import KolmogorovMathlib.AlgorithmicStatistics.DescriptionProfileInvariance
import KolmogorovMathlib.Restricted.DescriptionProfileGap

/-!
# Arithmetic of the slacks in the restricted-description bounds

Natural-number inequalities that fold the several logarithmic slacks of the
restricted-description estimates into a single one.

SUV Chapter 14, Section 14.5.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
open ENat

/-- The parameter `n + i_A + j_A` is at most `4 (n + alpha + gamma + d)` up to an additive
constant. -/
lemma upper_bound_M2_le {n alpha gamma d i_A j_A kx c_plain c_len : ℕ}
    (hi_A : i_A ≤ alpha)
    (hj_A : j_A ≤ kx + c_plain + d + 1)
    (hkx : kx ≤ 3 * n + c_len) :
    n + i_A + j_A ≤ 4 * (n + alpha + gamma + d) + (c_len + c_plain + 1) := by
  omega

/-- Two logarithmic slack terms add up to one logarithmic slack term with the larger constant. -/
lemma lower_upper_slack_add {c_lb c_ub bits_n bits_M : ℕ}
    (h_bits : bits_n ≤ bits_M) :
    (c_lb * bits_n + c_lb) + (c_ub * bits_M + c_ub) ≤
      (c_lb + c_ub + 10) * bits_M + (c_lb + c_ub + 10) := by
  zify at *
  nlinarith

/-- A bound `kx ≤ n + 2 |bits n| + c` gives `kx ≤ 3 n + c`. -/
lemma kx_le_3n_add_clen {n c_len bits_n kx : ℕ}
    (h_bits : bits_n ≤ n)
    (h_len : kx ≤ n + 2 * bits_n + c_len) :
    kx ≤ 3 * n + c_len := by
  omega

/-- The gap left after improving by `k₀` is at most `d + slack + c + 1`. -/
lemma delta_sub_k0_le_full
    (delta_A d gamma slack1 c_plain i_A j_A kx k_max k_0 : ℕ)
    (h_sum : i_A + j_A = kx + delta_A)
    (h_jA : j_A ≤ kx + d + slack1 + c_plain + 1)
    (h_dg_le : d + gamma ≤ delta_A)
    (h_delta_ub : delta_A ≤ d + gamma + 1)
    (hk_max : k_max = delta_A - d - slack1)
    (hk_0 : k_0 = min (min gamma i_A) k_max) :
    delta_A - k_0 ≤ d + slack1 + c_plain + 1 := by
  subst hk_max hk_0
  rcases le_total gamma i_A with hgi | hig
  · rw [min_eq_left hgi]
    rcases le_total gamma (delta_A - d - slack1) with hgk | hkg
    · rw [min_eq_left hgk]
      omega
    · rw [min_eq_right hkg]
      omega
  · rw [min_eq_right hig]
    rcases le_total i_A (delta_A - d - slack1) with hik | hki
    · rw [min_eq_left hik]
      omega
    · rw [min_eq_right hki]
      omega


/-! ### Exercise 367 -/

open ENat

/-- If the infimum of a set of naturals viewed in `ℕ∞` equals `d`, then `d` satisfies the
defining predicate. -/
lemma ENat_sInf_mem {P : ℕ → Prop} {d : ℕ}
    (h : sInf {b : ℕ∞ | ∃ beta : ℕ, (beta : ℕ∞) = b ∧ P beta} = (d : ℕ∞)) :
    P d := by
  classical
  by_contra hPd
  have h_ex : ∃ beta, P beta := by
    by_contra h_none
    have h_empty : {b : ℕ∞ | ∃ beta : ℕ, (beta : ℕ∞) = b ∧ P beta} = ∅ := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨beta, rfl, hPbeta⟩
      exact h_none ⟨beta, hPbeta⟩
    rw [h_empty, sInf_empty] at h
    contradiction
  set m := Nat.find h_ex
  have hPm : P m := Nat.find_spec h_ex
  have h_Inf_eq : sInf {b : ℕ∞ | ∃ beta : ℕ, (beta : ℕ∞) = b ∧ P beta} = (m : ℕ∞) := by
    apply le_antisymm
    · exact sInf_le ⟨m, rfl, hPm⟩
    · apply le_sInf
      rintro b ⟨beta, rfl, hPbeta⟩
      have : m ≤ beta := Nat.find_le hPbeta
      exact_mod_cast this
  rw [h_Inf_eq] at h
  have : m = d := by exact_mod_cast h
  subst this
  exact hPd hPm

/-- A deficiency value equal to `d` gives the bound `DeficiencyLe … d`. -/
lemma DeficiencyLe_of_deficiencyValue_eq {U : Map} {A : Finset BitString}
    {hA : A.Nonempty} {x : BitString} {d : ℕ}
    (hdef : deficiencyValue U A hA x = (d : ℕ∞)) :
    DeficiencyLe U (codedUniformOn A hA) x d :=
  ENat_sInf_mem hdef

/-- An optimality deficiency value equal to `beta` gives the bound
`SetOptimalityDeficiencyLe … beta`. -/
lemma SetOptimalityDeficiencyLe_of_optimalityDeficiencyValue_eq {U : Map}
    {A : Finset BitString} {hA : A.Nonempty} {x : BitString} {beta : ℕ}
    (hopt : optimalityDeficiencyValue U A hA x = (beta : ℕ∞)) :
    SetOptimalityDeficiencyLe U A hA x beta :=
  ENat_sInf_mem hopt

/-- The accumulated slack of the profile argument is again of the form `C |bits M| + C`. -/
lemma upper_bound_slack_sum_le {C_gap_fold C_imp_fold c_por c_plain slack1 S bits_M : ℕ}
    (h_s1 : slack1 ≤ C_gap_fold * bits_M + C_gap_fold)
    (h_S : S ≤ C_imp_fold * bits_M + C_imp_fold) :
    slack1 + 2 * S + 2 * bits_M + c_por + c_plain + 2 ≤
      (C_gap_fold + 2 * C_imp_fold + c_por + c_plain + 100) * bits_M +
      (C_gap_fold + 2 * C_imp_fold + c_por + c_plain + 100) := by
  zify at *
  nlinarith

/-- The parameter `n + (i_A + j_A - kx) + d` is at most `4 (n + alpha + gamma + d)` up to an
additive constant. -/
lemma upper_bound_M1_le {n alpha gamma d i_A j_A kx c_plain c_len : ℕ}
    (hi_A : i_A ≤ alpha)
    (hj_A : j_A ≤ kx + c_plain + d + 1) :
    n + (i_A + j_A - kx) + d ≤ 4 * (n + alpha + gamma + d) + (c_len + c_plain + 1) := by
  omega

end Kolmogorov
