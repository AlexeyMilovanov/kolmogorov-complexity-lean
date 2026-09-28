/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.StreamGapFill
import KolmogorovMathlib.MonotoneComplexity.StreamRelationSanitizer

/-!
# Enumeration of computable stream maps

This file assembles the results of `StreamRelationSanitizer` to prove SUV Theorem 83:
there exists a uniformly enumerable family of lower graphs of computable stream maps
that contains all lower graphs of computable stream maps.
-/

namespace Kolmogorov

/-- **SUV Theorem 83**: There exists a uniformly enumerable sequence of lower graphs of computable
stream maps such that every lower graph of a computable stream map appears in the sequence. -/
theorem exists_universal_computableStreamMap_lowerGraphs :
    ∃ U : ℕ → BitString → BitString → Prop,
      IsRE (fun p : ℕ × (BitString × BitString) => U p.1 p.2.1 p.2.2) ∧
      (∀ i, IsStreamLowerGraph (U i)) ∧
      ∀ f, IsComputableStreamMap f → ∃ i, ∀ x y, U i x y ↔ streamLowerGraph f x y := by
  use fun i => streamGapFill (sanitizedUniversalStreamRel i)
  refine ⟨?_, ?_, ?_⟩
  · exact streamGapFill_isRE_uniform sanitizedUniversalStreamRel_isRE_uniform
  · intro i
    exact streamGapFill_isStreamLowerGraph (sanitizedUniversalStreamRel_isConsistent i)
  · intro f hf
    have hcons :=
      (continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1.1).isConsistentStreamRelation
    have hre := hf.2
    obtain ⟨i, hi⟩ := sanitizedUniversalStreamRel_complete hcons hre
    refine ⟨i, fun x y => ?_⟩
    have h_self :=
      streamGapFill_eq_self (continuousStreamMap_lowerGraph_isStreamLowerGraph hf.1.1) x y
    rw [← h_self]
    apply streamGapFill_congr
    intro x' y'
    exact hi x' y'

end Kolmogorov
