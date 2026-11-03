/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Core.Model
import Mathlib.Computability.Partrec

/-!
# Effective indexed classes of computable measures

The presentation lists models by natural number. Its total computable maps turn class
indices into dyadic measure indices and nonempty lists into uniform mixtures. Repeated
indices remain in the list and therefore receive repeated mixture weight.
Blueprint nodes: `enum:class`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- An effective class closed under finite uniform mixtures, including lists with
repeated indices. Blueprint node `enum:class`. -/
structure EffectiveMixtureClass (U : Map) (hU : IsOptimalPrefixConditional U) where
  A : ℕ → Model U hU
  toIndex : ℕ → ℕ
  toIndex_computable : Computable toIndex
  toIndex_spec : ∀ i, IsComputableMeasureIndex (A i).measure (toIndex i)
  mix : List ℕ → ℕ
  mix_computable : Computable mix
  mix_eq : ∀ G : List ℕ, G ≠ [] →
    (A (mix G)).measure = (G.length : ℝ≥0∞)⁻¹ •
      (G.map fun i => (A i).measure).sum

/-- The proper measure at a presented class index. Blueprint node `enum:class`. -/
def EffectiveMixtureClass.model {U : Map} {hU : IsOptimalPrefixConditional U}
    (A : EffectiveMixtureClass U hU) (i : ℕ) : Measure CantorSeq :=
  (A.A i).measure

/-- The extensional image of a presentation. Blueprint node `enum:class`. -/
def EffectiveMixtureClass.carrier {U : Map} {hU : IsOptimalPrefixConditional U}
    (A : EffectiveMixtureClass U hU) : Set (Measure CantorSeq) :=
  Set.range A.model
end Kolmogorov.MDLPrediction
