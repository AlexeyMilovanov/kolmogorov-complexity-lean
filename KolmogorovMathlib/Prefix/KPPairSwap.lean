/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Symmetry of the Prefix Complexity of Pairs

This module records that the prefix complexity of a pair is symmetric in its two
components up to an additive constant: `KPPair U y x ≤ KPPair U x y + O(1)`. The
bound follows from the computable map that swaps the two components of a pair code
together with the map-invariance of plain prefix complexity, so no new coding
infrastructure is needed beyond `KolmogorovMathlib.Prefix.Symmetry`.
-/

namespace Kolmogorov
open scoped ENNReal

theorem KPPair_swap_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y : BitString, KPPair U y x ≤ KPPair U x y + (c : ENat) := by
  let f : BitString → BitString := fun z ↦ pairCode (decodeSecond z) (decodeFirst z)
  have h : f = (fun p : BitString × BitString ↦ pairCode p.1 p.2) ∘
      (fun p : BitString ↦ (decodeSecond p, decodeFirst p)) := by
    ext p; rfl
  have hf : Computable f := by
    rw [h]
    exact pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU f hf
  use c
  intro x y
  have hw : f (pairCode x y) = pairCode y x := by
    simp [f, decodeSecond_pairCode, decodeFirst_pairCode]
  have h_bound := hc (pairCode x y)
  rw [hw] at h_bound
  exact h_bound

end Kolmogorov
