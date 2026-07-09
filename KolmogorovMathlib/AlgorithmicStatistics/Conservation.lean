/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity

/-!
# Conservation of Coded Stochasticity

The old file built `pushForward P f code` with a caller-provided code.  That is
not a valid model-complexity foundation.  This replacement states conservation
for an explicitly supplied coded image model `Q`; its complexity is measured by
`Q.code`, the canonical code of its finite rational data.
-/

namespace Kolmogorov

open scoped ENNReal

/-- Deficiency is conserved under a mapped coded model once the image model has
enough mass at `f x` and the conditional-complexity transfer bound is known. -/
theorem deficiency_conserved (U : Map) (P Q : CodedFiniteDistribution)
    (f : BitString -> BitString) (x : BitString)
    (c d : Nat)
    (h_mass : P.mass x <= Q.mass (f x))
    (h_weight :
      complexityWeight (KP U (f x) Q.code) <=
        (2 : ENNReal) ^ c * complexityWeight (KP U x P.code)) :
    DeficiencyLe U P x d -> DeficiencyLe U Q (f x) (d + c) := by
  intro h_def
  unfold DeficiencyLe at *
  unfold CodedFiniteDistribution.DeficiencyLe at *
  calc
    complexityWeight (KP U (f x) Q.code)
        <= (2 : ENNReal) ^ c * complexityWeight (KP U x P.code) := h_weight
    _ <= (2 : ENNReal) ^ c * ((2 : ENNReal) ^ d * P.mass x) := by
      exact mul_le_mul_right h_def _
    _ = (2 : ENNReal) ^ (d + c) * P.mass x := by
      rw [pow_add]
      ac_rfl
    _ <= (2 : ENNReal) ^ (d + c) * Q.mass (f x) := by
      exact mul_le_mul_right h_mass _

/-- A coded witness-level conservation statement.  The image model `Q` must be
constructed elsewhere as finite rational data; no arbitrary code label is used. -/
theorem isStochastic_map_of_model (U : Map) (P Q : CodedFiniteDistribution)
    (f : BitString -> BitString) (x : BitString)
    (alpha beta c_comp c_def : Nat)
    (h_probQ : Q.IsProbability)
    (h_compQ : Q.complexity U <= P.complexity U + c_comp)
    (h_mass : P.mass x <= Q.mass (f x))
    (h_weight :
      complexityWeight (KP U (f x) Q.code) <=
        (2 : ENNReal) ^ c_def * complexityWeight (KP U x P.code))
    (h_comp : P.complexity U <= (alpha : ENat))
    (h_def : DeficiencyLe U P x beta) :
    IsStochastic U (f x) (alpha + c_comp) (beta + c_def) := by
  apply isStochastic_of_model U (f x) Q (alpha + c_comp) (beta + c_def)
  · exact h_probQ
  · calc
      Q.complexity U <= P.complexity U + c_comp := h_compQ
      _ <= (alpha : ENat) + c_comp := by
        simpa [add_comm] using add_le_add_left h_comp (c_comp : ENat)
      _ = ((alpha + c_comp : Nat) : ENat) := by
        rw [Nat.cast_add]
  · exact deficiency_conserved U P Q f x c_def beta h_mass h_weight h_def

/-- Conservation for an existential stochasticity witness, parameterized by a
canonical coded image model assignment and the structural bounds it satisfies. -/
theorem IsStochastic.map (U : Map) (f : BitString -> BitString)
    (imageModel : CodedFiniteDistribution -> CodedFiniteDistribution) (x : BitString)
    (alpha beta c_comp c_def : Nat)
    (h_prob : ∀ P, (imageModel P).IsProbability)
    (h_comp : ∀ P, (imageModel P).complexity U <= P.complexity U + c_comp)
    (h_mass : ∀ P, P.mass x <= (imageModel P).mass (f x))
    (h_weight : ∀ P,
      complexityWeight (KP U (f x) (imageModel P).code) <=
        (2 : ENNReal) ^ c_def * complexityWeight (KP U x P.code))
    (h_stoch : IsStochastic U x alpha beta) :
    IsStochastic U (f x) (alpha + c_comp) (beta + c_def) := by
  obtain ⟨P, _h_probP, h_compP, h_defP⟩ := h_stoch
  exact isStochastic_map_of_model U P (imageModel P) f x alpha beta c_comp c_def
    (h_prob P) (h_comp P) (h_mass P) (h_weight P) h_compP h_defP

end Kolmogorov
