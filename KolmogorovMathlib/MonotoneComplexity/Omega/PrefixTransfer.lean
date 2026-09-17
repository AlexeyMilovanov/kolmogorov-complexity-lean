/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.MonotoneComplexity.SharedCoding

/-!
# Prefix complexity under a *partial* computable map

`Prefix/Properties.lean` has `KP_map_le`: a **total** computable `f : BitString → BitString`
raises prefix complexity by at most `O(1)`.  Several arguments of SUV Chapter 5 need the
same statement for a **partial** computable map — most notably the proof of Theorem 100
(p. 157), where "from the first `n` bits of `Ω`, compute the list and then the least
integer outside it" is only defined on the prefixes of `Ω` (on other strings the search
"generate lower bounds until the sum exceeds `Ωₙ − 2⁻ⁿ`" diverges).

The proof is the source's own: the machine `p ↦ g (U p)` is again a prefix decompressor,
because its domain is a subset of `U`'s and a subset of a prefix-free set is prefix-free;
optimality of `U` then supplies the constant.  This is exactly the construction the
docstring of the C11b leaf `exists_const_KPPlain_code_invariant` describes as missing.

Everything here is proved; the module renders no statement of the source.
-/

namespace Kolmogorov

/-- **Partial computable maps do not increase conditional prefix complexity by more than
`O(1)`.**  If `z` is the value of the partial computable `g` at `x`, then
`KP U z y ≤ KP U x y + O(1)`, with a constant independent of `x`, `y` and `z`. -/
theorem KP_partial_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (g : BitString →. BitString) (hg : Partrec g) :
    ∃ c : ℕ, ∀ x y z, z ∈ g x → KP U z y ≤ KP U x y + (c : ENat) := by
  let D : Map := fun pair => (U pair).bind g
  have hD_decomp : isDecompressor D :=
    Partrec.bind hU.isDecompressor (hg.comp Computable.snd)
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    have hp' : (U (p, y)).Dom := by
      have h := hp
      simp only [D] at h
      exact h.fst
    have hq' : (U (q, y)).Dom := by
      have h := hq
      simp only [D] at h
      exact h.fst
    exact hU.isPrefixMachine y hp' hq' hpre
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD
  refine ⟨c, fun x y z hz => ?_⟩
  refine le_trans (hc z y) ?_
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
  refine ⟨p, ?_, rfl⟩
  change z ∈ (U (p, y)).bind g
  exact Part.mem_bind_iff.mpr ⟨x, h_eq ▸ Part.get_mem h_dom, hz⟩

/-- The plain (unconditional) form of `KP_partial_map_le`. -/
theorem KPPlain_partial_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (g : BitString →. BitString) (hg : Partrec g) :
    ∃ c : ℕ, ∀ x z, z ∈ g x → KPPlain U z ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := KP_partial_map_le U hU g hg
  exact ⟨c, fun x z hz => hc x [] z hz⟩

/-- The form needed by SUV p. 157: a partial computable map from strings to *numbers*
raises the shared `KPNat` by at most `O(1)` over `KPPlain` of the input. -/
theorem KPNat_partial_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (g : BitString →. ℕ) (hg : Partrec g) :
    ∃ c : ℕ, ∀ x n, n ∈ g x → KPNat U n ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_partial_map_le U hU
    (fun x => (g x).map natToBitString)
    (Partrec.map hg (computable_natToBitString.comp Computable.snd))
  refine ⟨c, fun x n hn => ?_⟩
  have hmem : natToBitString n ∈ (fun x => (g x).map natToBitString) x :=
    Part.mem_map _ hn
  simpa [KPNat] using hc x (natToBitString n) hmem

end Kolmogorov
