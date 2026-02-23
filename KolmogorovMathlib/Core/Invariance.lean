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

-- ==========================================================
-- BLOCK 1: Helper Lemmas for Computability and Sets
-- ==========================================================

/-- Every computable conditional decompressor D has a numerical code in our system. -/
lemma exists_code_of_isDecompressor (D : Map) (hD : isDecompressor D) :
    ∃ code : Nat.Partrec.Code, ∀ p y,
      (code.eval (Encodable.encode (p, y))).map
        (fun r => (Encodable.decode r : Option BitString).getD []) = D (p, y) := by
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hD
  use code
  intro p y
  have h_fun : ((fun r ↦ (Encodable.decode r : Option BitString).getD []) ∘
      Encodable.encode) = (id : BitString → BitString) := by
    funext a; simp
  rw [hc]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_map, h_fun]
  rfl

/-- If set S1 has a solution that is at most c worse than any solution in S2,
    then sInf S1 <= sInf S2 + c. -/
lemma sInf_le_sInf_add {S1 S2 : Set ENat} {c : ℕ}
    (h : ∀ s2 ∈ S2, ∃ s1 ∈ S1, s1 ≤ s2 + (c : ENat)) :
    sInf S1 ≤ sInf S2 + (c : ENat) := by
  have h1 : ∀ s2 ∈ S2, sInf S1 ≤ s2 + (c : ENat) := by
    intro s2 hs2
    obtain ⟨s1, hs1_in, hs1_le⟩ := h s2 hs2
    exact le_trans (sInf_le hs1_in) hs1_le
  have h2 : ∀ s2 ∈ S2, sInf S1 - (c : ENat) ≤ s2 := fun s2 hs2 =>
    tsub_le_iff_right.mpr (h1 s2 hs2)
  exact tsub_le_iff_right.mp (le_sInf h2)

-- ==========================================================
-- BLOCK 2: The Main Theorem (Kolmogorov's Theorem)
-- ==========================================================

/-- Kolmogorov's Theorem: An optimal conditional decompressor exists.
    We prove this by showing that our `universalDecompressor` satisfies the optimality predicate. -/
theorem exists_isOptimalConditional : ∃ U : Map, isOptimalConditional U := by
  use universalDecompressor
  constructor
  · exact isDecompressor_universalDecompressor
  · intro D hD
    obtain ⟨code, hc⟩ := exists_code_of_isDecompressor D hD
    let pref_bits := unaryPrefix (Encodable.encode code)
    use pref_bits.length
    intro x y
    apply sInf_le_sInf_add
    intro len_p h_len
    -- h_len means: ∃ p, x ∈ D (p, y) ∧ p.length = len_p
    obtain ⟨p, hp_out, rfl⟩ := h_len
    -- Construct the universal program by prepending the code prefix directly
    use (programLength (pref_bits ++ p) : ENat)
    constructor
    · use pref_bits ++ p
      constructor
      · -- Goal: x ∈ universalDecompressor (pref_bits ++ p, y)
        change x ∈ universalDecompressor (pref_bits ++ p, y)
        rw [universalSimulation, hc]
        exact hp_out
      · rfl
    · -- Prove length bound accurately by applying rules in the exact correct order
      dsimp [programLength]
      rw [List.length_append, add_comm]
      push_cast
      exact le_rfl
end Kolmogorov
