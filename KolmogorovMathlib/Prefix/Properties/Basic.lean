/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.Prefix.CountableKraft
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Prefix.CountingBound

/-!
# Properties of Prefix Complexity

This module establishes the first layer of easy theorems about prefix complexity
and its relationship to ordinary/plain Kolmogorov complexity, mirroring SUV Chapter 4.
-/

namespace Kolmogorov
open scoped ENNReal
/-- Ordinary optimal conditional complexity is bounded by conditional prefix complexity.
    `condK V x y <= KP U x y + O(1)` -/
theorem condK_le_KP (V U : Map) (hV : isOptimalConditional V) (hU : IsPrefixDecompressor U) :
    ∃ c : ℕ, ∀ x y, condK V x y ≤ KP U x y + (c : ENat) := by
  have hU_decomp : isDecompressor U := hU.isDecompressor
  obtain ⟨c, hc⟩ := hV.2 U hU_decomp
  use c
  intro x y
  exact hc x y

/-- Ordinary plain complexity is bounded by plain prefix complexity.
    `plainK V x <= KPPlain U x + O(1)` -/
theorem plainK_le_KPPlain (V U : Map) (hV : isOptimalConditional V) (hU : IsPrefixDecompressor U) :
    ∃ c : ℕ, ∀ x, plainK V x ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_le_KP V U hV hU
  use c
  intro x
  exact hc x []

/-- Conditioning only reduces prefix complexity.
    `KP U x y <= KPPlain U x + O(1)` -/
theorem KP_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KP U x y ≤ KPPlain U x + (c : ENat) := by
  let D : Map := fun p => U (p.1, [])
  have hD_decomp : isDecompressor D :=
    Partrec.comp hU.isDecompressor (Computable.pair Computable.fst (Computable.const []))
  have hD_prefix : IsPrefixMachine D := by
    intro y
    exact hU.isPrefixMachine []
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD
  use c; intro x y
  exact le_trans (hc x y) le_rfl

/-- Computable maps do not increase conditional prefix complexity by more than O(1).
    `KP U (f x) y <= KP U x y + O(1)` -/
theorem KP_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, KP U (f x) y ≤ KP U x y + (c : ENat) := by
  let D : Map := fun pair => (U pair).map f
  have hD_decomp : isDecompressor D :=
    Partrec.map hU.isDecompressor (Computable.comp hf Computable.snd)
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    have hp' : (U (p, y)).Dom := by
      have hp_map : (Part.map f (U (p, y))).Dom := by simpa [domainAt, D] using hp
      obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hp_map
      obtain ⟨w, hw, _⟩ := Part.mem_map_iff f |>.mp hz
      exact Part.dom_iff_mem.mpr ⟨w, hw⟩
    have hq' : (U (q, y)).Dom := by
      have hq_map : (Part.map f (U (q, y))).Dom := by simpa [domainAt, D] using hq
      obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hq_map
      obtain ⟨w, hw, _⟩ := Part.mem_map_iff f |>.mp hz
      exact Part.dom_iff_mem.mpr ⟨w, hw⟩
    exact hU.isPrefixMachine y hp' hq' hpre
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD
  use c; intro x y
  apply le_trans (hc (f x) y)
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
  exact ⟨p, ⟨h_dom, congrArg f h_eq⟩, rfl⟩

/-- Computable maps do not increase plain prefix complexity by more than O(1).
    `KPPlain U (f x) ≤ KPPlain U x + O(1)` -/
theorem KPPlain_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, KPPlain U (f x) ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := KP_map_le U hU f hf
  use c
  intro x
  exact hc x []

/-- SUV-style alias for the plain prefix form of computable monotonicity. -/
theorem prefix_plain_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, KPPlain U (f x) ≤ KPPlain U x + (c : ENat) :=
  KPPlain_map_le U hU f hf

/-- The prefix complexity of a string given itself is bounded by a constant.
    `KP U x x <= O(1)` -/
theorem KP_self_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, KP U x x ≤ (c : ENat) := by
  let selfDecompressor : Map := fun pr =>
    if pr.1.length = 0 then Part.some pr.2 else Part.none
  have hSelf_decomp : isDecompressor selfDecompressor := by
    have hopt : Computable (fun pr : BitString × BitString =>
        bif decide (pr.1.length = 0) then some pr.2 else none) := by
      have hEqZero : Computable (fun n : ℕ => decide (n = 0)) := by
        have hLeZero : Computable (fun n : ℕ => decide (n ≤ 0)) := by
          have hLe : Computable (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
            obtain ⟨_, h⟩ := Primrec.nat_le
            exact Computable.of_eq h.to_comp (fun p => by congr)
          exact hLe.comp (Computable.id.pair (Computable.const 0))
        exact Computable.of_eq hLeZero (fun n => by simp)
      have hguard : Computable (fun pr : BitString × BitString => decide (pr.1.length = 0)) :=
        hEqZero.comp (Computable.list_length.comp Computable.fst)
      exact Computable.cond hguard
        (Computable.option_some.comp Computable.snd)
        (Computable.const none)
    exact (Computable.ofOption hopt).of_eq fun pr => by
      by_cases hp : pr.1.length = 0
      · have hnil : pr.1 = [] := List.eq_nil_of_length_eq_zero hp
        simp [selfDecompressor, hnil]
      · have hnil : pr.1 ≠ [] := by
          intro h
          exact hp (by simp [h])
        simp [selfDecompressor, hp, hnil]
  have hSelf_prefix : IsPrefixMachine selfDecompressor := by
    intro y
    refine (isPrefixFree_singleton ([] : BitString)).mono ?_
    intro p hp
    change (selfDecompressor (p, y)).Dom at hp
    by_cases h : p.length = 0
    · simp [List.eq_nil_of_length_eq_zero h]
    · have hnil : p ≠ [] := by
        intro hp_nil
        exact h (by simp [hp_nil])
      simp [selfDecompressor, hnil] at hp
  have hSelf : IsPrefixDecompressor selfDecompressor := ⟨hSelf_decomp, hSelf_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hSelf
  use c
  intro x
  calc
    KP U x x ≤ KP selfDecompressor x x + (c : ENat) := hc x x
    _        ≤ (0 : ENat) + c := by
      gcongr
      exact KP_le_programLength_of_produces (M := selfDecompressor) (p := []) (x := x) (y := x) (by
        change x ∈ (if ([] : BitString) = [] then Part.some x else Part.none)
        simp)
    _        = c := zero_add _

/-- The prefix complexity of `f(x)` given `x` is bounded by a constant.
    `KP U (f x) x <= O(1)` -/
theorem KP_map_self_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, KP U (f x) x ≤ (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := KP_map_le U hU f hf
  obtain ⟨c₂, hc₂⟩ := KP_self_le U hU
  use c₁ + c₂
  intro x
  calc
    KP U (f x) x ≤ KP U x x + c₁ := hc₁ x x
    _            ≤ (c₂ : ENat) + c₁ := by
      gcongr
      exact hc₂ x
    _            = ((c₂ + c₁ : ℕ) : ENat) := by rw [Nat.cast_add]
    _            = ((c₁ + c₂ : ℕ) : ENat) := by rw [add_comm c₂ c₁]

/-- An explicit SUV Theorem 60-style corollary:
    `KPPair U x y <= KPPlain U x + KPPlain U y + O(1)` -/
theorem KPPair_le_KPPlain_add_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KPPair U x y ≤ KPPlain U x + KPPlain U y + (c : ENat) := by
  obtain ⟨c_weak, h_weak⟩ := KPPair_chain_upper_weak U hU
  obtain ⟨c_drop, h_drop⟩ := KP_le_KPPlain U hU
  use c_weak + c_drop
  intro x y
  calc
    KPPair U x y ≤ KPPlain U x + KP U y x + c_weak := h_weak x y
    _            ≤ KPPlain U x + (KPPlain U y + c_drop) + c_weak := by
      gcongr
      exact h_drop y x
    _            = KPPlain U x + KPPlain U y + (c_drop + c_weak : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl
    _            = KPPlain U x + KPPlain U y + (c_weak + c_drop : ℕ) := by
      rw [add_comm c_weak c_drop]

/-- Weak chain upper bound in the shorter pair-complexity notation:
    `KPPair U x y <= KPPlain U x + KP U y x + O(1)`. -/
theorem KPPair_le_KPPlain_add_KP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KPPair U x y ≤ KPPlain U x + KP U y x + (c : ENat) :=
  KPPair_chain_upper_weak U hU


end Kolmogorov
