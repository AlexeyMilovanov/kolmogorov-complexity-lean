import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Complexity of list codes

The two basic "KP of the code vs the components" facts for `listCode`:

* `KPPlain_listCode_le` — the code of a list is no more complex than the sum
  of the components' complexities plus `O(1)` per element (the per-element
  constant is the pair-coding overhead; it cannot be avoided in this
  generality);
* `KP_component_listCode_le` — each component is `O(1)`-decodable from the
  list code and its index (packaged as `pairCode (listCode l) (natCode i)`,
  the standard context convention).

Chapters needing finer bounds (e.g. `K(listCode l)` against
`Σ K(xᵢ | x₁…xᵢ₋₁)`) should derive them from these plus the staged symmetry
of information, not re-derive coding from scratch.
-/

namespace Kolmogorov

open CodedFiniteDistribution

/-- The complexity of a list code is at most the sum of the components'
complexities plus a constant per element. -/
theorem KPPlain_listCode_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ l : List BitString,
      KPPlain U (listCode l) ≤
        (l.map fun x => KPPlain U x).sum + ((c * (l.length + 1) : ℕ) : ENat) := by
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨c₁, hc₁⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨c₀ + c₁, fun l => ?_⟩
  induction l with
  | nil =>
    have h := hc₀ []
    simp only [listCode_nil, List.map_nil, List.sum_nil, List.length_nil, zero_add,
      mul_one]
    calc KPPlain U [] ≤ 2 * ([] : BitString).length + (c₀ : ENat) := h
      _ = (c₀ : ENat) := by simp
      _ ≤ ((c₀ + c₁ : ℕ) : ENat) := by exact_mod_cast Nat.le_add_right c₀ c₁
  | cons x t ih =>
    have hpair : KPPlain U (listCode (x :: t)) = KPPair U x (listCode t) := rfl
    calc KPPlain U (listCode (x :: t))
        = KPPair U x (listCode t) := hpair
      _ ≤ KPPlain U x + KPPlain U (listCode t) + (c₁ : ENat) := hc₁ x (listCode t)
      _ ≤ KPPlain U x +
            ((t.map fun y => KPPlain U y).sum +
              (((c₀ + c₁) * (t.length + 1) : ℕ) : ENat)) + (c₁ : ENat) := by
          gcongr
      _ = ((x :: t).map fun y => KPPlain U y).sum +
            ((((c₀ + c₁) * (t.length + 1) : ℕ) : ENat) + (c₁ : ENat)) := by
          simp only [List.map_cons, List.sum_cons]
          ring
      _ ≤ ((x :: t).map fun y => KPPlain U y).sum +
            (((c₀ + c₁) * ((x :: t).length + 1) : ℕ) : ENat) := by
          gcongr
          have hnat : (c₀ + c₁) * (t.length + 1) + c₁ ≤ (c₀ + c₁) * (t.length + 2) := by
            nlinarith
          calc (((c₀ + c₁) * (t.length + 1) : ℕ) : ENat) + (c₁ : ENat)
              = (((c₀ + c₁) * (t.length + 1) + c₁ : ℕ) : ENat) := by push_cast; ring
            _ ≤ (((c₀ + c₁) * (t.length + 2) : ℕ) : ENat) := by exact_mod_cast hnat
            _ = (((c₀ + c₁) * ((x :: t).length + 1) : ℕ) : ENat) := by
                push_cast [List.length_cons]
                ring

/-- Each component of a coded list is `O(1)`-decodable from the pair
(list code, index): `KP U (l[i]) (pairCode (listCode l) (natCode i)) ≤ O(1)`. -/
theorem KP_component_listCode_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (l : List BitString) (i : ℕ),
      KP U (l.getD i []) (pairCode (listCode l) (natCode i)) ≤ (c : ENat) := by
  have hprim : Primrec (fun w : BitString =>
      (decodeListCode (decodeFirst w)).getD (decodeNatCode (decodeSecond w))
        ([] : BitString)) := by
    have h := (Primrec.list_getD ([] : BitString)).comp
      (decodeListCode_primrec.comp decodeFirst_primrec')
      (decodeNatCode_primrec.comp decodeSecond_primrec')
    exact h
  obtain ⟨c, hc⟩ := KP_map_self_le U hU _ hprim.to_comp
  refine ⟨c, fun l i => ?_⟩
  have h := hc (pairCode (listCode l) (natCode i))
  simpa [decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode,
    decodeListCode_listCode] using h

end Kolmogorov
