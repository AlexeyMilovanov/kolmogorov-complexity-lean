/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Counterexample.Atomic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Deficiency drop along the atomic branch

The log is used only at positive cylinder mass. Equal masses at `1` and `1z`
cancel, leaving the a priori complexity difference.

Blueprint nodes: `audit:drop`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- Positive-mass a priori deficiency. Blueprint node `audit:drop`. -/
noncomputable def positiveDeficiency (Q : Measure CantorSeq) (x : BitString)
    (_hpos : 0 < cantorMass Q x) : ℝ :=
  -Real.logb 2 (cantorMass Q x).toReal - KA x

/-- One absolute constant gives a linear deficiency drop on the explicit
atomic branch for every positive length. Blueprint node `audit:drop`. -/
theorem audit_drop :
    ∃ c : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ z : BitString,
      z.length = k ∧
      (k : ℝ) - c ≤ KA (true :: z) ∧
      KA (true :: z) ≤ (k : ℝ) + c + 1 ∧
      IsProbabilityMeasure (atomicWitness k z) ∧
      IsComputableMeasure (atomicWitness k z) ∧
      ∃ hs : 0 < cantorMass (atomicWitness k z) [true],
        ∃ hh : 0 < cantorMass (atomicWitness k z) (true :: z),
          positiveDeficiency (atomicWitness k z) [true] hs -
            positiveDeficiency (atomicWitness k z) (true :: z) hh ≥ (k : ℝ) - c := by
  rcases audit_incompressible with ⟨c, hc1, hc2⟩
  use c + |KA [true]|
  intro k hk
  rcases hc1 k hk with ⟨z, hz1, hz2, hz3⟩
  use z
  refine ⟨hz1, ?_, ?_, ?_, ?_, ?_⟩
  · have h_pos : 0 ≤ |KA [true]| := abs_nonneg _
    linarith
  · have h_pos : 0 ≤ |KA [true]| := abs_nonneg _
    linarith
  · exact (audit_atomic k z).1
  · exact (audit_atomic k z).2.1
  · have hm1 := (audit_atomic k z).2.2.1
    have hm2 := (audit_atomic k z).2.2.2
    have hz_pow : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ (2 * k) := by
      exact ENNReal.pow_pos
        (pos_iff_ne_zero.mpr Kolmogorov.inv_two_ne_zero) (2 * k)
    have h1 : 0 < cantorMass (atomicWitness k z) [true] := by
      rw [hm1]
      exact hz_pow
    use h1
    have h2 : 0 < cantorMass (atomicWitness k z) (true :: z) := by
      rw [hm2]
      exact hz_pow
    use h2
    unfold positiveDeficiency
    rw [hm1, hm2]
    have hz_bound : k - c ≤ KA (true :: z) := hz2
    have h_abs : KA [true] ≤ |KA [true]| := le_abs_self _
    linarith

end Kolmogorov.MDLPrediction
