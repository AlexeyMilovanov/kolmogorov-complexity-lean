import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Properties

namespace Kolmogorov
open scoped ENNReal

theorem KPPair_swap_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y : BitString, KPPair U y x ≤ KPPair U x y + (c : ENat) := by
  let f : BitString → BitString := fun z => pairCode (decodeSecond z) (decodeFirst z)
  have h : f = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun p : BitString => (decodeSecond p, decodeFirst p)) := by
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
