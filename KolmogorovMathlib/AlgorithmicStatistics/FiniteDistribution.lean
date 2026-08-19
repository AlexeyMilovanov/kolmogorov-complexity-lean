import KolmogorovMathlib.AlgorithmicStatistics.Basic
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import KolmogorovMathlib.Prefix.Encoding
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Finite Probability Models

This module defines finite coded probability distributions over bitstrings.
These form the statistical models for algorithmic statistics.
-/

namespace Kolmogorov

open scoped ENNReal BigOperators

/-- A probability distribution over `BitString` with finite support and a code.
This is the basic model type for algorithmic statistics. -/
structure FiniteDistribution where
  mass : BitString → ℝ≥0∞
  support : Finset BitString
  code : BitString
  mass_eq_zero_of_not_mem_support : ∀ x, x ∉ support → mass x = 0
  sum_mass : ∑ x ∈ support, mass x = 1

namespace FiniteDistribution

variable (P : FiniteDistribution)

@[simp] theorem mass_eq_zero (x : BitString) (hx : x ∉ P.support) : P.mass x = 0 :=
  P.mass_eq_zero_of_not_mem_support x hx

/-- The total sum of probabilities over all strings is 1. -/
theorem tsum_mass : ∑' x, P.mass x = 1 := by
  rw [← P.sum_mass]
  apply tsum_eq_sum
  intro x hx
  exact P.mass_eq_zero_of_not_mem_support x hx

/-- The probability of any string is bounded by 1. -/
theorem mass_le_one (x : BitString) : P.mass x ≤ 1 := by
  by_cases hx : x ∈ P.support
  · rw [← P.sum_mass]
    exact Finset.single_le_sum (fun _ _ => zero_le) hx
  · rw [P.mass_eq_zero x hx]
    exact zero_le

end FiniteDistribution

/-! ### Dirac (Singleton) Distribution -/

/-- The Dirac distribution concentrated at `x`. -/
noncomputable def dirac (x : BitString) : FiniteDistribution where
  mass y := if y = x then 1 else 0
  support := {x}
  code := pairCode (natCode 1) x
  mass_eq_zero_of_not_mem_support y hy := by
    simp only [Finset.mem_singleton] at hy
    simp only [ite_eq_right_iff]
    intro h
    exact (hy h).elim
  sum_mass := by
    simp only [Finset.sum_singleton, ite_true]

@[simp] theorem dirac_mass_self (x : BitString) : (dirac x).mass x = 1 := by
  simp [dirac]

@[simp] theorem dirac_mass_ne (x y : BitString) (h : y ≠ x) : (dirac x).mass y = 0 := by
  simp [dirac, h]

/-! ### Uniform Distribution on a Finite Set -/

/-- The uniform distribution on a nonempty finite set. -/
noncomputable def uniformOn (S : Finset BitString) (hS : S.Nonempty) (code : BitString) :
    FiniteDistribution where
  mass y := if y ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0
  support := S
  code := code
  mass_eq_zero_of_not_mem_support y hy := by
    simp [hy]
  sum_mass := by
    have hcard : (S.card : ℝ≥0∞) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Finset.Nonempty.card_pos hS |>.ne'
    have h_eq : ∑ x ∈ S, (if x ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0) = ∑ x ∈ S, (S.card : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact if_pos hx
    rw [h_eq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _)

@[simp] theorem uniformOn_mass_of_mem (S : Finset BitString) (hS : S.Nonempty) (code : BitString)
    (x : BitString) (hx : x ∈ S) :
    (uniformOn S hS code).mass x = (S.card : ℝ≥0∞)⁻¹ := by
  dsimp [uniformOn]
  rw [if_pos hx]

@[simp] theorem uniformOn_mass_of_not_mem (S : Finset BitString) (hS : S.Nonempty)
    (code : BitString) (x : BitString) (hx : x ∉ S) :
    (uniformOn S hS code).mass x = 0 := by
  dsimp [uniformOn]
  rw [if_neg hx]

/-! ### Uniform Distribution on Strings of a Fixed Length -/

theorem stringsOfLength_nonempty (n : ℕ) : (stringsOfLength n).Nonempty := by
  rw [Finset.card_pos.symm, cardStringsOfLength]
  exact pow_pos (by decide) n

/-- The uniform distribution on all strings of length `n`. -/
noncomputable def lengthUniform (n : ℕ) : FiniteDistribution :=
  uniformOn (stringsOfLength n) (stringsOfLength_nonempty n) (natCode n)

theorem lengthUniform_mass_of_mem (n : ℕ) (x : BitString) (hx : x.length = n) :
    (lengthUniform n).mass x = (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hmem : x ∈ stringsOfLength n := (memStringsOfLength n x).mpr hx
  rw [lengthUniform, uniformOn_mass_of_mem _ _ _ _ hmem, cardStringsOfLength]
  rw [Nat.cast_pow, Nat.cast_two, ENNReal.inv_pow]

theorem lengthUniform_mass_of_not_mem (n : ℕ) (x : BitString) (hx : x.length ≠ n) :
    (lengthUniform n).mass x = 0 := by
  have hnotmem : x ∉ stringsOfLength n := mt (memStringsOfLength n x).mp hx
  rw [lengthUniform, uniformOn_mass_of_not_mem _ _ _ _ hnotmem]

end Kolmogorov
