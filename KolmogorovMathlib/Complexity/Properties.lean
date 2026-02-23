import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic
import Mathlib.Data.ENat.Lattice
import KolmogorovMathlib.Core.Basic

/-!
# Basic Properties of Kolmogorov Complexity

This module establishes the foundational inequalities of algorithmic information theory
using an optimal universal decompressor `U`. It proves that:
* `plainK(x) ≤ |x| + c` (strings can be compressed no worse than their literal length).
* `condK(x|x) ≤ c` (knowing the answer gives constant complexity).
* `condK(x|y) ≤ plainK(x) + c` (conditioning only reduces complexity).
* `condK(f(x)|y) ≤ condK(x|y) + c` (computable functions do not add information).
-/

namespace Kolmogorov

-- ==========================================================
-- 1. Boundary API
-- ==========================================================

/-- The conditional complexity is infinite (⊤) if and only if
    there is no program that produces `x` given context `y` on map `D`. -/
lemma condK_eq_top_iff (D : Map) (x y : BitString) :
    condK D x y = ⊤ ↔ ¬ ∃ p, x ∈ D (p, y) := by
  constructor
  · intro h ⟨p, hp⟩
    have h_mem : (programLength p : ENat) ∈ candidateLengths D x y := ⟨p, hp, rfl⟩
    have h_le : condK D x y ≤ (programLength p : ENat) := sInf_le h_mem
    rw [h] at h_le
    have h_not_top : ¬ (⊤ ≤ (programLength p : ENat)) := by simp
    exact h_not_top h_le
  · intro h_none
    have h_empty : candidateLengths D x y = ∅ := by
      ext n; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨p', hp', rfl⟩
      exact h_none ⟨p', hp'⟩
    change sInf (candidateLengths D x y) = ⊤
    rw [h_empty]
    exact sInf_empty

-- ==========================================================
-- 2. Fundamental Inequalities
-- ==========================================================

/-- Plain complexity of a string is bounded by its length plus a constant.
    `K(x) ≤ |x| + c` -/
theorem plainK_le_length (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, plainK U x ≤ (programLength x : ENat) + c := by
  let id_decompressor : Map := fun (p, _) => Part.some p
  obtain ⟨c, hc⟩ := hU.2 id_decompressor (Computable.partrec Computable.fst)
  use c; intro x
  apply le_trans (hc x [])
  gcongr
  apply sInf_le
  exact ⟨x, ⟨trivial, rfl⟩, rfl⟩

/-- The conditional complexity of a string given itself is bounded by a constant.
    `K(x|x) ≤ c` -/
theorem condK_self (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, condK U x x ≤ (c : ENat) := by
  let ctx_decompressor : Map := fun (_, y) => Part.some y
  obtain ⟨c, hc⟩ := hU.2 ctx_decompressor (Computable.partrec Computable.snd)
  use c; intro x
  calc
    condK U x x ≤ condK ctx_decompressor x x + c := hc x x
    _           ≤ 0 + c                          := by
      gcongr
      apply sInf_le
      exact ⟨[], ⟨trivial, rfl⟩, rfl⟩
    _           = c                              := zero_add _

/-- Conditioning only reduces complexity.
    `K(x|y) ≤ K(x) + c` -/
theorem condK_le_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y, condK U x y ≤ plainK U x + (c : ENat) := by
  let D : Map := fun p => U (p.1, [])
  have hD : isDecompressor D :=
    Partrec.comp hU.1 (Computable.pair Computable.fst (Computable.const []))
  obtain ⟨c, hc⟩ := hU.2 D hD
  use c; intro x y
  exact le_trans (hc x y) le_rfl

/-- The conditional complexity of f(x) given x is bounded by a constant.
    `K(f(x)|x) ≤ c_f` -/
theorem condK_comp (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, condK U (f x) x ≤ (c : ENat) := by
  let f_decompressor : Map := fun (_, y) => Part.some (f y)
  have hF : isDecompressor f_decompressor :=
    Computable.partrec (Computable.comp hf Computable.snd)
  obtain ⟨c, hc⟩ := hU.2 f_decompressor hF
  use c; intro x
  calc
    condK U (f x) x ≤ condK f_decompressor (f x) x + c := hc (f x) x
    _               ≤ 0 + c                            := by
      gcongr
      apply sInf_le
      exact ⟨[], ⟨trivial, rfl⟩, rfl⟩
    _               = c                                := zero_add _

/-- Applying a computable function does not increase conditional complexity.
    `K(f(x)|y) ≤ K(x|y) + c_f` -/
theorem condK_map_le (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, condK U (f x) y ≤ condK U x y + (c : ENat) := by
  let D : Map := fun pair => (U pair).map f
  have hD : isDecompressor D := Partrec.map hU.1 (Computable.comp hf Computable.snd)
  obtain ⟨c, hc⟩ := hU.2 D hD
  use c; intro x y
  apply le_trans (hc (f x) y)
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
  exact ⟨p, ⟨h_dom, congrArg f h_eq⟩, rfl⟩

/-- Applying a computable function does not increase plain complexity.
    `K(f(x)) ≤ K(x) + c_f` -/
theorem plainK_map_le (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, plainK U (f x) ≤ plainK U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_map_le U hU f hf
  exact ⟨c, fun x => hc x []⟩

end Kolmogorov
