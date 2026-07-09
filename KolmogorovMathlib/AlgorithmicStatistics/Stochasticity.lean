/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Deficiency
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Prefix.Properties

/-!
# Stochasticity

This module defines `(alpha, beta)`-stochasticity. A string `x` is stochastic
if there exists a "simple" probability model `P` (complexity $\le \alpha$) that
is a "good fit" for `x` (deficiency $\le \beta$).
-/

namespace Kolmogorov

open scoped ENNReal

/-- A string `x` is `(alpha, beta)`-stochastic with respect to a universal machine `U`
if there is a finite probability distribution `P` such that its plain complexity
is bounded by `alpha` and the randomness deficiency of `x` with respect to `P`
is bounded by `beta`. -/
noncomputable def IsStochastic (U : Map) (x : BitString) (alpha beta : ℕ) : Prop :=
  ∃ P : CodedFiniteDistribution,
    P.IsProbability ∧ P.complexity U ≤ (alpha : ENat) ∧ DeficiencyLe U P x beta

/-- Non-stochasticity is the negation of stochasticity. -/
def IsNonStochastic (U : Map) (x : BitString) (alpha beta : ℕ) : Prop :=
  ¬ IsStochastic U x alpha beta

/-- Stochasticity is monotonic in `alpha`. -/
theorem IsStochastic.mono_alpha {U : Map} {x : BitString} {alpha alpha' beta : ℕ}
    (h : alpha ≤ alpha') (hstoch : IsStochastic U x alpha beta) :
    IsStochastic U x alpha' beta := by
  obtain ⟨P, hP_prob, hP_comp, hP_def⟩ := hstoch
  exact ⟨P, hP_prob, le_trans hP_comp (by exact_mod_cast h), hP_def⟩

/-- Stochasticity is monotonic in `beta`. -/
theorem IsStochastic.mono_beta {U : Map} {x : BitString} {alpha beta beta' : ℕ}
    (h : beta ≤ beta') (hstoch : IsStochastic U x alpha beta) :
    IsStochastic U x alpha beta' := by
  obtain ⟨P, hP_prob, hP_comp, hP_def⟩ := hstoch
  exact ⟨P, hP_prob, hP_comp, hP_def.mono_beta h⟩

/-- Joint monotonicity. -/
theorem isStochastic_mono {U : Map} {x : BitString} {alpha alpha' beta beta' : ℕ}
    (ha : alpha ≤ alpha') (hb : beta ≤ beta') (hstoch : IsStochastic U x alpha beta) :
    IsStochastic U x alpha' beta' :=
  (hstoch.mono_alpha ha).mono_beta hb

/-- Any explicit model that fits `x` witnesses its stochasticity. -/
theorem isStochastic_of_model (U : Map) (x : BitString) (P : CodedFiniteDistribution) (alpha beta : ℕ)
    (hprob : P.IsProbability)
    (hcomp : P.complexity U ≤ (alpha : ENat)) (hdef : DeficiencyLe U P x beta) :
    IsStochastic U x alpha beta :=
  ⟨P, hprob, hcomp, hdef⟩

/-- A singleton (Dirac) model for `x` has zero deficiency. -/
theorem isStochastic_dirac_of_KPPlain_le (U : Map) (x : BitString) (alpha : ℕ)
    (hcomp : (codedDirac x).complexity U ≤ (alpha : ENat)) :
    IsStochastic U x alpha 0 :=
  isStochastic_of_model U x _ alpha 0 (codedDirac_isProbability x) hcomp
    (deficiencyLe_zero_of_mass_one U _ x (codedDirac_mass_self x))

/-- Every string is weakly stochastic under its own Dirac model. -/
theorem isStochastic_dirac_self (U : Map) (x : BitString) (alpha : ℕ)
    (h : (codedDirac x).complexity U = (alpha : ENat)) :
    IsStochastic U x alpha 0 := by
  apply isStochastic_dirac_of_KPPlain_le
  exact le_of_eq h

/-- Every string of length `n` is weakly stochastic under the length-uniform model. -/
theorem isStochastic_lengthUniform (U : Map) (x : BitString) (n : ℕ) (_ : x.length = n) (alpha beta : ℕ)
    (hcomp : (codedLengthUniform n).complexity U ≤ (alpha : ENat))
    (hdef : DeficiencyLe U (codedLengthUniform n) x beta) :
    IsStochastic U x alpha beta :=
  isStochastic_of_model U x _ alpha beta (codedLengthUniform_isProbability n) hcomp hdef

/-- The code mapping from a unary length code to the canonical length-uniform
distribution code.  The remaining computability obligation is exactly the fact
that this canonical `Finset.toList` enumeration can be generated effectively. -/
def lengthUniformCode (w : BitString) : BitString :=
  (codedLengthUniform (w.takeWhile id).length).code

theorem lengthUniformCode_eq (n : ℕ) :
    lengthUniformCode (natCode n) = (codedLengthUniform n).code := by
  have h : ((natCode n).takeWhile id).length = n := by
    simp [natCode]
  rw [lengthUniformCode, h]

theorem lengthUniformCode_computable : Computable lengthUniformCode :=
  (CodedFiniteDistribution.codedLengthUniform_code_primrec.to_comp.comp
    (((Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
      (fun z ↦ (takeWhile_id_length_eq_findIdx z).symm)).to_comp)).of_eq (fun _ ↦ rfl)

/-- Every string is stochastic under the length-uniform model with complexity bounded logarithmically in its length. -/
theorem isStochastic_lengthUniform_log (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, ∀ beta : ℕ,
      DeficiencyLe U (codedLengthUniform x.length) x beta →
      IsStochastic U x (2 * (Nat.bits x.length).length + c) beta := by
  obtain ⟨c1, hc1⟩ := KPPlain_map_le U hU lengthUniformCode lengthUniformCode_computable
  obtain ⟨c2, hc2⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c1 + c2, ?_⟩
  intro x beta hdef
  apply isStochastic_lengthUniform U x x.length rfl
  have h_comp : (codedLengthUniform x.length).complexity U ≤
      (2 * (Nat.bits x.length).length + (c1 + c2) : ENat) := by
    have hmap := hc1 (natCode x.length)
    rw [lengthUniformCode_eq x.length] at hmap
    unfold CodedFiniteDistribution.complexity
    calc
      KPPlain U (codedLengthUniform x.length).code
          ≤ KPPlain U (natCode x.length) + (c1 : ENat) := hmap
      _ ≤ (2 * (Nat.bits x.length).length + (c2 : ENat)) + (c1 : ENat) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (hc2 x.length) (c1 : ENat)
      _ = (2 * (Nat.bits x.length).length + (c1 + c2 : Nat) : ENat) := by
          rw [Nat.cast_add]
          simp [add_comm, add_assoc]
  exact h_comp
  exact hdef

end Kolmogorov
