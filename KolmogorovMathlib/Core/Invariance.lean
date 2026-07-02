import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Encoding
import Mathlib.Data.List.Basic
import Mathlib.Data.ENat.Lattice
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Core.UniversalDecompressor

/-!
# The Invariance Theorem

This module formalizes the Kolmogorov-Solomonoff-Chaitin Invariance Theorem.
It proves the existence of an optimal conditional decompressor (a universal decompressor).
This fundamental result ensures that Algorithmic Complexity is well-defined
up to an additive constant, making it independent of the specific decompressor chosen.
-/

namespace Kolmogorov

/-! ### Helper Lemmas -/

/-- Every computable conditional decompressor D has a numerical code. -/
lemma existsCodeOfIsDecompressor (D : Map) (hD : isDecompressor D) :
    ∃ code : Nat.Partrec.Code, ∀ p y,
      (code.eval (Encodable.encode (p, y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) = D (p, y) := by
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hD
  exact ⟨code, fun p y => by
    ext out
    rw [hc]
    simp [Encodable.encodek]⟩

/-- If set S₁ has a solution that is at most `c` worse than any solution in S₂,
    then `sInf S₁ ≤ sInf S₂ + c`. -/
lemma sInfLeSInfAdd {S₁ S₂ : Set ENat} {c : ℕ}
    (h : ∀ s₂ ∈ S₂, ∃ s₁ ∈ S₁, s₁ ≤ s₂ + (c : ENat)) :
    sInf S₁ ≤ sInf S₂ + (c : ENat) := by
  rw [← tsub_le_iff_right]
  exact le_sInf fun s₂ hs₂ ↦
    let ⟨s₁, hs₁, hle⟩ := h s₂ hs₂
    tsub_le_iff_right.mpr (le_trans (sInf_le hs₁) hle)

/-! ### The Main Theorem (Kolmogorov's Theorem) -/

/-- Kolmogorov's Theorem: An optimal conditional decompressor exists.
    We prove this by showing that our `universalDecompressor` satisfies the
    optimality predicate. -/
theorem existsIsOptimalConditional : ∃ U : Map, isOptimalConditional U := by
  refine ⟨universalDecompressor, isDecompressorUniversalDecompressor, fun D hD => ?_⟩
  obtain ⟨code, hc⟩ := existsCodeOfIsDecompressor D hD
  refine ⟨(unaryPrefix (Encodable.encode code)).length, fun x y => ?_⟩
  apply sInfLeSInfAdd
  rintro len_p ⟨p, hp_out, rfl⟩
  refine ⟨(programLength (unaryPrefix (Encodable.encode code) ++ p) : ENat), ?_, ?_⟩
  · refine ⟨unaryPrefix (Encodable.encode code) ++ p, ?_, rfl⟩
    change x ∈ universalDecompressor _
    rw [universalSimulation, hc]
    exact hp_out
  · dsimp [programLength]
    rw [List.length_append]
    push_cast
    rw [add_comm]

end Kolmogorov
