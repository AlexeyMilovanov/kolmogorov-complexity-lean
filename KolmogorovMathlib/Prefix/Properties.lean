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

/-! ### Projection Bounds for Encoded Pairs -/

/-- The first component of an encoded pair has complexity bounded by the pair. -/
theorem KPPlain_left_le_KPPair (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KPPlain U x ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU decodeFirst decodeFirst_computable
  use c
  intro x y
  simpa [KPPair, KPPlain, decodeFirst_pairCode] using hc (pairCode x y)

/-- The second component of an encoded pair has complexity bounded by the pair. -/
theorem KPPlain_right_le_KPPair (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KPPlain U y ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU decodeSecond decodeSecond_computable
  use c
  intro x y
  simpa [KPPair, KPPlain, decodeSecond_pairCode] using hc (pairCode x y)

/-! ### Ordinary Plain Corollaries for Encoded Pairs -/

/-- Ordinary conditional complexity is bounded by plain prefix complexity. -/
theorem condK_le_KPPlain (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, condK V x y ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c_cond, h_cond⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨c_plain, h_plain⟩ := KP_le_KPPlain U hU
  use c_plain + c_cond
  intro x y
  calc
    condK V x y ≤ KP U x y + c_cond := h_cond x y
    _           ≤ (KPPlain U x + c_plain) + c_cond := by
      gcongr
      exact h_plain x y
    _           = KPPlain U x + (c_plain + c_cond : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl

/-- Ordinary conditional complexity of a computable image is bounded by prefix complexity. -/
theorem condK_map_le_KP (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, condK V (f x) y ≤ KP U x y + (c : ENat) := by
  obtain ⟨c_cond, h_cond⟩ := condK_le_KP V U hV hU.isPrefixDecompressor
  obtain ⟨c_map, h_map⟩ := KP_map_le U hU f hf
  use c_map + c_cond
  intro x y
  calc
    condK V (f x) y ≤ KP U (f x) y + c_cond := h_cond (f x) y
    _               ≤ (KP U x y + c_map) + c_cond := by
      gcongr
      exact h_map x y
    _               = KP U x y + (c_map + c_cond : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl

/-- Ordinary plain complexity of a computable image is bounded by plain prefix complexity. -/
theorem plainK_map_le_KPPlain (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, plainK V (f x) ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c_plain, h_plain⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨c_map, h_map⟩ := KPPlain_map_le U hU f hf
  use c_map + c_plain
  intro x
  calc
    plainK V (f x) ≤ KPPlain U (f x) + c_plain := h_plain (f x)
    _              ≤ (KPPlain U x + c_map) + c_plain := by
      gcongr
      exact h_map x
    _              = KPPlain U x + (c_map + c_plain : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl

/-- Ordinary plain complexity of the encoded pair is bounded by prefix pair complexity. -/
theorem plainK_pair_le_KPPair (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, plainK V (pairCode x y) ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  use c
  intro x y
  simpa [KPPair, KPPlain] using hc (pairCode x y)

/-- Ordinary plain complexity of the first component is bounded by prefix pair complexity. -/
theorem plainK_left_le_KPPair (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, plainK V x ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨c_plain, h_plain⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨c_proj, h_proj⟩ := KPPlain_left_le_KPPair U hU
  use c_plain + c_proj
  intro x y
  calc
    plainK V x ≤ KPPlain U x + c_plain := h_plain x
    _          ≤ (KPPair U x y + c_proj) + c_plain := by
      gcongr
      exact h_proj x y
    _          = KPPair U x y + (c_proj + c_plain : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl
    _          = KPPair U x y + (c_plain + c_proj : ℕ) := by
      rw [add_comm c_proj c_plain]

/-- Ordinary plain complexity of the second component is bounded by prefix pair complexity. -/
theorem plainK_right_le_KPPair (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, plainK V y ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨c_plain, h_plain⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨c_proj, h_proj⟩ := KPPlain_right_le_KPPair U hU
  use c_plain + c_proj
  intro x y
  calc
    plainK V y ≤ KPPlain U y + c_plain := h_plain y
    _          ≤ (KPPair U x y + c_proj) + c_plain := by
      gcongr
      exact h_proj x y
    _          = KPPair U x y + (c_proj + c_plain : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl
    _          = KPPair U x y + (c_plain + c_proj : ℕ) := by
      rw [add_comm c_proj c_plain]

/-- Ordinary plain complexity of an encoded pair is bounded by the sum of
plain prefix complexities. -/
theorem plainK_pair_le_KPPlain_add_KPPlain (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y,
      plainK V (pairCode x y) ≤ KPPlain U x + KPPlain U y + (c : ENat) := by
  obtain ⟨c_pair, h_pair⟩ := plainK_pair_le_KPPair V U hV hU
  obtain ⟨c_upper, h_upper⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  use c_upper + c_pair
  intro x y
  calc
    plainK V (pairCode x y) ≤ KPPair U x y + c_pair := h_pair x y
    _                         ≤ (KPPlain U x + KPPlain U y + c_upper) + c_pair := by
      gcongr
      exact h_upper x y
    _                         = KPPlain U x + KPPlain U y + (c_upper + c_pair : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl

/-! ### Stable Aliases for SUV Theorem Statements -/

/-- SUV Theorem 57-style alias for `plainK_le_KPPlain`. -/
theorem plain_le_prefix (V U : Map) (hV : isOptimalConditional V) (hU : IsPrefixDecompressor U) :
    ∃ c : ℕ, ∀ x, plainK V x ≤ KPPlain U x + (c : ENat) :=
  plainK_le_KPPlain V U hV hU

/-- SUV-style alias for `KP_le_KPPlain`. -/
theorem prefix_conditioning_le_plain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KP U x y ≤ KPPlain U x + (c : ENat) :=
  KP_le_KPPlain U hU

/-- SUV-style alias for `KP_self_le`. -/
theorem prefix_self_le_const (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, KP U x x ≤ (c : ENat) :=
  KP_self_le U hU

/-- The symmetry of pair prefix complexity.
    `KPPair U x y <= KPPair U y x + O(1)` -/
theorem KPPair_symm (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KPPair U x y ≤ KPPair U y x + (c : ENat) := by
  let swapPair : BitString → BitString := fun p => pairCode (decodeSecond p) (decodeFirst p)
  have h_swap : Computable swapPair := by
    have h : swapPair = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun p : BitString => (decodeSecond p, decodeFirst p)) := by
      funext p; rfl
    rw [h]
    exact pairCode_computable.comp (decodeSecond_computable.pair decodeFirst_computable)
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU swapPair h_swap
  use c
  intro x y
  have h_eq : swapPair (pairCode y x) = pairCode x y := by
    simp [swapPair, decodeFirst_pairCode, decodeSecond_pairCode]
  calc
    KPPair U x y = KPPlain U (pairCode x y) := rfl
    _            = KPPlain U (swapPair (pairCode y x)) := by rw [h_eq]
    _            ≤ KPPlain U (pairCode y x) + c := hc (pairCode y x)
    _            = KPPair U y x + c := rfl

/-- Prefix subadditivity: `KP(x) <= KP(y) + KP(x|y) + O(1)`. -/
theorem KPPlain_le_KPPlain_add_KP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, KPPlain U x ≤ KPPlain U y + KP U x y + (c : ENat) := by
  obtain ⟨c_symm, h_symm⟩ := KPPair_symm U hU
  obtain ⟨c_left, h_left⟩ := KPPlain_left_le_KPPair U hU
  obtain ⟨c_weak, h_weak⟩ := KPPair_chain_upper_weak U hU
  use c_left + c_symm + c_weak
  intro x y
  calc
    KPPlain U x ≤ KPPair U x y + c_left := h_left x y
    _           ≤ (KPPair U y x + c_symm) + c_left := by
      gcongr
      exact h_symm x y
    _           ≤ (KPPlain U y + KP U x y + c_weak) + c_symm + c_left := by
      gcongr
      exact h_weak y x
    _           = KPPlain U y + KP U x y + (c_left + c_symm + c_weak : ℕ) := by
      rw [add_assoc (KPPlain U y + KP U x y), add_assoc (KPPlain U y + KP U x y)]
      congr 1
      rw [← Nat.cast_add, ← Nat.cast_add]
      congr 1
      omega

/-- Applying a computable function to the left component of a pair does not increase complexity. -/
theorem KPPair_map_left_le_KPPair (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, KPPair U (f x) y ≤ KPPair U x y + (c : ENat) := by
  let mapLeft : BitString → BitString := fun p => pairCode (f (decodeFirst p)) (decodeSecond p)
  have h_map : Computable mapLeft := by
    have h : mapLeft = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun p : BitString => (f (decodeFirst p), decodeSecond p)) := by
      funext p; rfl
    rw [h]
    exact pairCode_computable.comp ((hf.comp decodeFirst_computable).pair decodeSecond_computable)
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU mapLeft h_map
  use c
  intro x y
  have h_eq : mapLeft (pairCode x y) = pairCode (f x) y := by
    simp [mapLeft, decodeFirst_pairCode, decodeSecond_pairCode]
  calc
    KPPair U (f x) y = KPPlain U (pairCode (f x) y) := rfl
    _                = KPPlain U (mapLeft (pairCode x y)) := by rw [h_eq]
    _                ≤ KPPlain U (pairCode x y) + c := hc (pairCode x y)
    _                = KPPair U x y + c := rfl

/-- Applying a computable function to the right component of a pair does not increase complexity. -/
theorem KPPair_map_right_le_KPPair (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, KPPair U x (f y) ≤ KPPair U x y + (c : ENat) := by
  let mapRight : BitString → BitString := fun p => pairCode (decodeFirst p) (f (decodeSecond p))
  have h_map : Computable mapRight := by
    have h : mapRight = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun p : BitString => (decodeFirst p, f (decodeSecond p))) := by
      funext p; rfl
    rw [h]
    exact pairCode_computable.comp (decodeFirst_computable.pair (hf.comp decodeSecond_computable))
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU mapRight h_map
  use c
  intro x y
  have h_eq : mapRight (pairCode x y) = pairCode x (f y) := by
    simp [mapRight, decodeFirst_pairCode, decodeSecond_pairCode]
  calc
    KPPair U x (f y) = KPPlain U (pairCode x (f y)) := rfl
    _                = KPPlain U (mapRight (pairCode x y)) := by rw [h_eq]
    _                ≤ KPPlain U (pairCode x y) + c := hc (pairCode x y)
    _                = KPPair U x y + c := rfl

/-- Applying computable functions to both components of a pair does not increase complexity. -/
theorem KPPair_map_le_map (U : Map) (hU : IsOptimalPrefixConditional U)
    (f g : BitString → BitString) (hf : Computable f) (hg : Computable g) :
    ∃ c : ℕ, ∀ x y, KPPair U (f x) (g y) ≤ KPPair U x y + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := KPPair_map_left_le_KPPair U hU f hf
  obtain ⟨c₂, hc₂⟩ := KPPair_map_right_le_KPPair U hU g hg
  use c₁ + c₂
  intro x y
  calc
    KPPair U (f x) (g y) ≤ KPPair U x (g y) + c₁ := hc₁ x (g y)
    _                    ≤ (KPPair U x y + c₂) + c₁ := by
      gcongr
      exact hc₂ x y
    _                    = KPPair U x y + (c₂ + c₁ : ℕ) := by
      rw [Nat.cast_add]
      ac_rfl
    _                    = KPPair U x y + (c₁ + c₂ : ℕ) := by
      rw [add_comm c₁ c₂]

/-- The pair complexity of `(x, x)` is bounded by the plain complexity of `x`. -/
theorem KPPair_self_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, KPPair U x x ≤ KPPlain U x + (c : ENat) := by
  let dup : BitString → BitString := fun x => pairCode x x
  have h_dup : Computable dup := by
    have h : dup = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun x : BitString => (x, x)) := by
      funext x; rfl
    rw [h]
    exact pairCode_computable.comp (Computable.id.pair Computable.id)
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU dup h_dup
  use c
  intro x
  exact hc x

/-- The pair complexity of `(x, f(x))` is bounded by the plain complexity of `x`. -/
theorem KPPair_map_right_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, KPPair U x (f x) ≤ KPPlain U x + (c : ENat) := by
  let dupMap : BitString → BitString := fun x => pairCode x (f x)
  have h_dupMap : Computable dupMap := by
    have h : dupMap = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun x : BitString => (x, f x)) := by
      funext x; rfl
    rw [h]
    exact pairCode_computable.comp (Computable.id.pair hf)
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU dupMap h_dupMap
  use c
  intro x
  exact hc x

/-- The pair complexity of `(f(x), x)` is bounded by the plain complexity of `x`. -/
theorem KPPair_map_left_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, KPPair U (f x) x ≤ KPPlain U x + (c : ENat) := by
  let dupMap : BitString → BitString := fun x => pairCode (f x) x
  have h_dupMap : Computable dupMap := by
    have h : dupMap = (fun p : BitString × BitString => pairCode p.1 p.2) ∘
      (fun x : BitString => (f x, x)) := by
      funext x; rfl
    rw [h]
    exact pairCode_computable.comp (hf.pair Computable.id)
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU dupMap h_dupMap
  use c
  intro x
  exact hc x

/-- Conditioning on more information (via a computable function) does not increase complexity.
    `KP U x y <= KP U x (f y) + O(1)` -/
theorem KP_cond_map_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, KP U x y ≤ KP U x (f y) + (c : ENat) := by
  let D : Map := fun p => U (p.1, f p.2)
  have hD_decomp : isDecompressor D :=
    Partrec.comp hU.isDecompressor (Computable.fst.pair (Computable.comp hf Computable.snd))
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpre
    have hp' : (U (p, f y)).Dom := by
      change (D (p, y)).Dom at hp
      simpa [D] using hp
    have hq' : (U (q, f y)).Dom := by
      change (D (q, y)).Dom at hq
      simpa [D] using hq
    exact hU.isPrefixMachine (f y) hp' hq' hpre
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c, hc⟩ := hU.invariance hD
  use c; intro x y
  calc
    KP U x y ≤ KP D x y + c := hc x y
    _        ≤ KP U x (f y) + c := by
      gcongr
      apply sInf_le_sInf
      rintro n ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩

/-- Dropping the right component of a condition does not increase complexity. -/
theorem KP_cond_drop_right_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z, KP U x (pairCode y z) ≤ KP U x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := KP_cond_map_le U hU decodeFirst decodeFirst_computable
  use c
  intro x y z
  have : decodeFirst (pairCode y z) = y := decodeFirst_pairCode y z
  calc
    KP U x (pairCode y z) ≤ KP U x (decodeFirst (pairCode y z)) + c := hc x (pairCode y z)
    _                     = KP U x y + c := by rw [this]

/-- Dropping the left component of a condition does not increase complexity. -/
theorem KP_cond_drop_left_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z, KP U x (pairCode y z) ≤ KP U x z + (c : ENat) := by
  obtain ⟨c, hc⟩ := KP_cond_map_le U hU decodeSecond decodeSecond_computable
  use c
  intro x y z
  have : decodeSecond (pairCode y z) = z := decodeSecond_pairCode y z
  calc
    KP U x (pairCode y z) ≤ KP U x (decodeSecond (pairCode y z)) + c := hc x (pairCode y z)
    _                     = KP U x z + c := by rw [this]



/-- Optional implementation of a simple length decompressor. -/
def simpleLenDecompressorOpt (p : List Bool) : Option (List Bool) :=
  bif (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1) then some (p.drop ((p.takeWhile id).length + 1)) else none

/-- A simple length decompressor. -/
def simpleLenDecompressor : Map := fun pr => Part.ofOption (simpleLenDecompressorOpt pr.1)

lemma simpleLenDecompressor_computable : isDecompressor simpleLenDecompressor := by
  have h_opt : Computable simpleLenDecompressorOpt := by
    have h_n : Computable (fun p : List Bool => (p.takeWhile id).length) :=
      ((Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
        (fun z => (takeWhile_id_length_eq_findIdx z).symm)).to_comp
    have h_n_plus_1 : Computable (fun p : List Bool => (p.takeWhile id).length + 1) :=
      Computable.succ.comp h_n
    have h_q : Computable (fun p : List Bool => p.drop ((p.takeWhile id).length + 1)) :=
      primrec_list_drop.to_comp.comp Computable.id h_n_plus_1
    have h_len : Computable (fun p : List Bool => p.length) :=
      Computable.list_length
    have h_add : Computable₂ (fun (x y : Nat) => x + y) := Primrec.nat_add.to_comp
    have h_2n : Computable (fun p : List Bool => (p.takeWhile id).length + (p.takeWhile id).length) :=
      h_add.comp h_n h_n
    have h_2n1 : Computable (fun p : List Bool => (p.takeWhile id).length + (p.takeWhile id).length + 1) :=
      Computable.succ.comp h_2n
    have h_beq : Computable (fun p : List Bool => (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1)) := by
      have h1 := (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_2n1)
      exact h1.of_eq (fun p => rfl)
    have h_none : Computable (fun (p : List Bool) => (none : Option (List Bool))) :=
      Computable.const (α := List Bool) (σ := Option (List Bool)) none
    have h_cond := Computable.cond h_beq (Computable.option_some.comp h_q) h_none
    exact h_cond.of_eq (fun p => by
      unfold simpleLenDecompressorOpt
      cases h : (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1)
      · rfl
      · rfl)
  have h_fst : Computable (fun (pr : List Bool × List Bool) => pr.1) := Computable.fst
  have h_pr := Computable.ofOption (h_opt.comp h_fst)
  exact h_pr

lemma takeWhile_length_eq_of_prefix {p q : List Bool} (hpre : p <+: q)
    (h_bounds : (p.takeWhile id).length < p.length) :
    (p.takeWhile id).length = (q.takeWhile id).length := by
  induction p generalizing q
  · exact absurd h_bounds (by simp)
  · rename_i a p ih
    rcases hpre with ⟨t, rfl⟩
    cases h_a : a
    · -- a = false
      rfl
    · -- a = true
      subst h_a
      have h1 : (List.takeWhile id (true :: p)).length = (List.takeWhile id p).length + 1 := rfl
      have h2 : (List.takeWhile id (true :: p ++ t)).length = (List.takeWhile id (p ++ t)).length + 1 := rfl
      have h_bounds_p : (List.takeWhile id p).length < p.length := by
        rw [h1] at h_bounds
        have h3 : (true :: p).length = p.length + 1 := rfl
        omega
      have h_ih := ih (List.prefix_append p t) h_bounds_p
      rw [h1, h_ih, h2]

lemma simpleLenDecompressor_isPrefixMachine : IsPrefixMachine simpleLenDecompressor := by
  intro y p hp q hq hpre
  unfold simpleLenDecompressor at hp hq
  have hp' : simpleLenDecompressorOpt p ≠ none := by
    intro h
    change (Part.ofOption (simpleLenDecompressorOpt p)).Dom at hp
    rw [h] at hp
    exact hp
  have hq' : simpleLenDecompressorOpt q ≠ none := by
    intro h
    change (Part.ofOption (simpleLenDecompressorOpt q)).Dom at hq
    rw [h] at hq
    exact hq
  unfold simpleLenDecompressorOpt at hp' hq'
  cases h1 : (p.length == (p.takeWhile id).length + (p.takeWhile id).length + 1) <;> rw [h1] at hp'
  · contradiction
  cases h2 : (q.length == (q.takeWhile id).length + (q.takeWhile id).length + 1) <;> rw [h2] at hq'
  · contradiction
  have h1_eq := beq_iff_eq.mp h1
  have h2_eq := beq_iff_eq.mp h2
  have h_bounds : (p.takeWhile id).length < p.length := by omega
  have h_n_eq : (p.takeWhile id).length = (q.takeWhile id).length :=
    takeWhile_length_eq_of_prefix hpre h_bounds
  have h_len_eq : p.length = q.length := by
    rw [h1_eq, h2_eq, h_n_eq]
  rcases hpre with ⟨t, rfl⟩
  have ht : t = [] := by
    have h_len2 : p.length = (p ++ t).length := h_len_eq
    simp only [List.length_append] at h_len2
    cases t
    · rfl
    · simp at h_len2
  subst ht
  exact (List.append_nil p).symm

lemma simpleLenDecompressor_produces (p y : List Bool) (h : p.length = (p.takeWhile id).length + (p.takeWhile id).length + 1) :
    produces simpleLenDecompressor p y (p.drop ((p.takeWhile id).length + 1)) := by
  unfold produces simpleLenDecompressor
  have heq : simpleLenDecompressorOpt p = some (p.drop ((p.takeWhile id).length + 1)) := by
    unfold simpleLenDecompressorOpt
    rw [beq_iff_eq.mpr h]
    rfl
  change _ ∈ Part.ofOption (simpleLenDecompressorOpt p)
  rw [heq]
  exact ⟨trivial, rfl⟩

/-- Kraft sum for prefix complexity. -/
theorem KPPlain_kraft_sum_le_one (U : Map) (hU : IsPrefixDecompressor U) :
    (∑' x : BitString, complexityWeight (KPPlain U x)) ≤ 1 := by
  have h := tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine
  have h_le : ∀ x, complexityWeight (KPPlain U x) ≤ aprioriMeasure U x [] := fun x =>
    complexityWeight_KP_le_aprioriMeasure U x []
  exact le_trans (ENNReal.tsum_le_tsum h_le) h

lemma drop_replicate_append (n : Nat) (x : List Bool) :
  List.drop (n + 1) (List.replicate n true ++ false :: x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Simple length bound: `KPPlain U x ≤ 2 * x.length + O(1)`. -/
theorem KPPlain_le_two_mul_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U x ≤ 2 * x.length + (c : ENat) := by
  have hM : IsPrefixDecompressor simpleLenDecompressor := ⟨simpleLenDecompressor_computable, simpleLenDecompressor_isPrefixMachine⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  use c + 1
  intro x
  let p : List Bool := List.replicate x.length true ++ (false :: x)
  have h_p_take : (p.takeWhile id).length = x.length := by
    simp [p]
  have h_p_len : p.length = 2 * x.length + 1 := by
    simp [p]
    omega
  have h_p_eq : p.length = (p.takeWhile id).length + (p.takeWhile id).length + 1 := by
    rw [h_p_take, h_p_len]
    omega
  have h_prod := simpleLenDecompressor_produces p [] h_p_eq
  have h_drop : p.drop ((p.takeWhile id).length + 1) = x := by
    rw [h_p_take]
    exact drop_replicate_append x.length x
  rw [h_drop] at h_prod
  have h_KP := KP_le_programLength_of_produces h_prod
  calc
    KPPlain U x = KP U x [] := rfl
    _           ≤ KP simpleLenDecompressor x [] + c := hc x []
    _           ≤ p.length + c := by gcongr
    _           = ((2 * x.length + 1 : ℕ) : ENat) + c := by rw [h_p_len]
    _           = (2 * x.length + (c + 1) : ℕ) := by norm_cast; omega

/-- Conditional decompressor that accepts exactly programs whose length is the
length encoded in the context and returns the program literally. For each fixed
context, all halting programs have the same length, hence form a prefix-free
domain. -/
def exactLengthContextDecompressorOpt (pr : BitString × BitString) : Option BitString :=
  bif (pr.1.length == decodeBits pr.2) then some pr.1 else none

/-- Decompressor for `exactLengthContextDecompressorOpt`. -/
def exactLengthContextDecompressor : Map := fun pr =>
  Part.ofOption (exactLengthContextDecompressorOpt pr)

lemma exactLengthContextDecompressor_computable :
    isDecompressor exactLengthContextDecompressor := by
  have h_opt : Computable exactLengthContextDecompressorOpt := by
    have h_len : Computable (fun pr : BitString × BitString => pr.1.length) :=
      Computable.list_length.comp Computable.fst
    have h_dec : Computable (fun pr : BitString × BitString => decodeBits pr.2) :=
      decodeBitsComputable.comp Computable.snd
    have h_beq : Computable (fun pr : BitString × BitString =>
        (pr.1.length == decodeBits pr.2)) := by
      exact (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_dec)
    have h_none : Computable (fun (_ : BitString × BitString) => (none : Option BitString)) :=
      Computable.const (α := BitString × BitString) (σ := Option BitString) none
    exact (Computable.cond h_beq (Computable.option_some.comp Computable.fst) h_none).of_eq
      (fun pr => by
        unfold exactLengthContextDecompressorOpt
        cases h : (pr.1.length == decodeBits pr.2) <;> rfl)
  exact Computable.ofOption h_opt

lemma exactLengthContextDecompressor_isPrefixMachine :
    IsPrefixMachine exactLengthContextDecompressor := by
  intro y p hp q hq hpre
  unfold exactLengthContextDecompressor at hp hq
  have hp' : exactLengthContextDecompressorOpt (p, y) ≠ none := by
    intro h
    change (Part.ofOption (exactLengthContextDecompressorOpt (p, y))).Dom at hp
    rw [h] at hp
    exact hp
  have hq' : exactLengthContextDecompressorOpt (q, y) ≠ none := by
    intro h
    change (Part.ofOption (exactLengthContextDecompressorOpt (q, y))).Dom at hq
    rw [h] at hq
    exact hq
  unfold exactLengthContextDecompressorOpt at hp' hq'
  cases hp_eq : (p.length == decodeBits y) <;> rw [hp_eq] at hp'
  · contradiction
  cases hq_eq : (q.length == decodeBits y) <;> rw [hq_eq] at hq'
  · contradiction
  have hplen : p.length = decodeBits y := beq_iff_eq.mp hp_eq
  have hqlen : q.length = decodeBits y := beq_iff_eq.mp hq_eq
  exact hpre.eq_of_length (by rw [hplen, hqlen])

lemma exactLengthContextDecompressor_produces
    (x y : BitString) (h : x.length = decodeBits y) :
    produces exactLengthContextDecompressor x y x := by
  unfold produces exactLengthContextDecompressor exactLengthContextDecompressorOpt
  rw [beq_iff_eq.mpr h]
  exact ⟨trivial, rfl⟩

/-- Given a binary encoding of `x.length` as condition, a prefix program can be
the literal string `x` up to the universal-machine overhead. -/
theorem KP_le_length_given_natBits_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KP U x (Nat.bits x.length) ≤ x.length + (c : ENat) := by
  have hM : IsPrefixDecompressor exactLengthContextDecompressor :=
    ⟨exactLengthContextDecompressor_computable, exactLengthContextDecompressor_isPrefixMachine⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x
  have hprod : produces exactLengthContextDecompressor x (Nat.bits x.length) x :=
    exactLengthContextDecompressor_produces x (Nat.bits x.length) (by simp [decodeBits_natBits])
  calc
    KP U x (Nat.bits x.length)
        ≤ KP exactLengthContextDecompressor x (Nat.bits x.length) + (c : ENat) := hc x (Nat.bits x.length)
    _ ≤ (x.length : ENat) + (c : ENat) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (KP_le_programLength_of_produces hprod) (c : ENat)

/-- Sharper self-delimiting length bound: `KPPlain U x ≤ x.length + 2 * log x.length + O(1)`. -/
theorem KPPlain_le_length_add_log (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U x ≤ x.length + 2 * (Nat.bits x.length).length + (c : ENat) := by
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_cond, h_cond⟩ := KP_le_length_given_natBits_length U hU
  obtain ⟨c_nat, h_nat⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_cond + c_nat + c_sub, ?_⟩
  intro x
  calc
    KPPlain U x
        ≤ KPPlain U (Nat.bits x.length) + KP U x (Nat.bits x.length)
            + (c_sub : ENat) := h_sub x (Nat.bits x.length)
    _ ≤ (2 * (Nat.bits x.length).length + (c_nat : ENat))
          + (x.length + (c_cond : ENat)) + (c_sub : ENat) := by
        gcongr
        · exact h_nat (Nat.bits x.length)
        · exact h_cond x
    _ = x.length + 2 * (Nat.bits x.length).length
          + ((c_cond + c_nat + c_sub : ℕ) : ENat) := by
        rw [Nat.cast_add, Nat.cast_add]
        simp [add_comm, add_left_comm, add_assoc]


/-- Natural-number prefix complexity bound: `KPPlain U (natCode n) ≤ 2 * log n + O(1)`. -/
theorem KPPlain_natCode_le_log (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, KPPlain U (natCode n) ≤ 2 * (Nat.bits n).length + (c : ENat) := by
  let bitsToNatCode : BitString → BitString := fun bs => natCode (decodeBits bs)
  have h_bitsToNatCode : Computable bitsToNatCode :=
    natCode_computable.comp decodeBitsComputable
  obtain ⟨c_map, h_map⟩ := KPPlain_map_le U hU bitsToNatCode h_bitsToNatCode
  obtain ⟨c_len, h_len⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c_len + c_map, ?_⟩
  intro n
  calc
    KPPlain U (natCode n)
        = KPPlain U (bitsToNatCode (Nat.bits n)) := by
            simp [bitsToNatCode, decodeBits_natBits]
    _ ≤ KPPlain U (Nat.bits n) + (c_map : ENat) := h_map (Nat.bits n)
    _ ≤ (2 * (Nat.bits n).length + (c_len : ENat)) + (c_map : ENat) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (h_len (Nat.bits n)) (c_map : ENat)
    _ = 2 * (Nat.bits n).length + ((c_len + c_map : ℕ) : ENat) := by
        rw [Nat.cast_add]
        ac_rfl

/-- SUV Theorem 61: `K(x, K(x)) = K(x) + O(1)`. -/
theorem KPPair_self_complexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x kx, HasPrefixComplexityValue U x kx → KPPair U x (natCode kx) ≤ kx + (c : ENat) := by
  obtain ⟨c_chain, h_chain⟩ := KPPair_chain_upper U hU
  obtain ⟨c_cond, h_cond⟩ := KP_map_self_le U hU decodeSecond decodeSecond_computable
  refine ⟨c_cond + c_chain, ?_⟩
  intro x kx hkx
  have hdec : decodeSecond (prefixComplexityContext x kx) = natCode kx := by
    exact decodeSecond_pairCode x (natCode kx)
  have h_cond' : KP U (natCode kx) (prefixComplexityContext x kx) ≤ (c_cond : ENat) := by
    simpa [prefixComplexityContext, decodeSecond_pairCode] using
      h_cond (prefixComplexityContext x kx)
  calc
    KPPair U x (natCode kx)
        ≤ KPPlain U x + KP U (natCode kx) (prefixComplexityContext x kx)
            + (c_chain : ENat) := h_chain x (natCode kx) kx hkx
    _ ≤ (kx : ENat) + (c_cond : ENat) + (c_chain : ENat) := by
        rw [← hkx]
        gcongr
    _ = (kx : ENat) + ((c_cond + c_chain : ℕ) : ENat) := by
        rw [Nat.cast_add]
        simp [add_assoc, add_comm]

theorem KPPlain_le_KPPair_self_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x kx, HasPrefixComplexityValue U x kx → (kx : ENat) ≤ KPPair U x (natCode kx) + (c : ENat) := by
  obtain ⟨c, h_left⟩ := KPPlain_left_le_KPPair U hU
  refine ⟨c, ?_⟩
  intro x kx hkx
  rw [hkx]
  exact h_left x (natCode kx)

/-- SUV Theorem 63(a): `K(x) ≤ |x| + K(|x|) + O(1)`. -/
theorem KPPlain_le_length_add_KPPlain_length (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, KPPlain U x ≤ x.length + KPPlain U (Nat.bits x.length) + (c : ENat) := by
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_cond, h_cond⟩ := KP_le_length_given_natBits_length U hU
  refine ⟨c_cond + c_sub, ?_⟩
  intro x
  calc
    KPPlain U x
        ≤ KPPlain U (Nat.bits x.length) + KP U x (Nat.bits x.length)
            + (c_sub : ENat) := h_sub x (Nat.bits x.length)
    _ ≤ KPPlain U (Nat.bits x.length) + (x.length + (c_cond : ENat))
            + (c_sub : ENat) := by
        gcongr
        exact h_cond x
    _ = x.length + KPPlain U (Nat.bits x.length) + ((c_cond + c_sub : ℕ) : ENat) := by
        rw [Nat.cast_add]
        simp [add_comm, add_left_comm, add_assoc]

/-- Run a plain decompressor only on programs whose length is encoded in the
condition. The fixed-length guard is what makes the domain prefix-free in every
condition. -/
def plainProgramLengthContextDecompressor (V : Map) : Map := fun pr =>
  bif (pr.1.length == decodeBits pr.2) then V (pr.1, []) else Part.none

lemma plainProgramLengthContextDecompressor_computable (V : Map) (hV : isDecompressor V) :
    isDecompressor (plainProgramLengthContextDecompressor V) := by
  have h_len : Computable (fun pr : BitString × BitString => pr.1.length) :=
    Computable.list_length.comp Computable.fst
  have h_dec : Computable (fun pr : BitString × BitString => decodeBits pr.2) :=
    decodeBitsComputable.comp Computable.snd
  have h_guard : Computable (fun pr : BitString × BitString =>
      (pr.1.length == decodeBits pr.2)) :=
    (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_dec)
  have h_call : Partrec (fun pr : BitString × BitString => V (pr.1, [])) :=
    Partrec.comp hV (Computable.fst.pair (Computable.const []))
  exact (Partrec.cond h_guard h_call Partrec.none).of_eq (fun pr => by
    unfold plainProgramLengthContextDecompressor
    cases h : (pr.1.length == decodeBits pr.2) <;> rfl)

lemma plainProgramLengthContextDecompressor_isPrefixMachine (V : Map) :
    IsPrefixMachine (plainProgramLengthContextDecompressor V) := by
  intro y p hp q hq hpre
  change (plainProgramLengthContextDecompressor V (p, y)).Dom at hp
  change (plainProgramLengthContextDecompressor V (q, y)).Dom at hq
  unfold plainProgramLengthContextDecompressor at hp hq
  cases hp_eq : (p.length == decodeBits y) <;> rw [hp_eq] at hp
  · exact False.elim hp
  cases hq_eq : (q.length == decodeBits y) <;> rw [hq_eq] at hq
  · exact False.elim hq
  have hplen : p.length = decodeBits y := beq_iff_eq.mp hp_eq
  have hqlen : q.length = decodeBits y := beq_iff_eq.mp hq_eq
  exact hpre.eq_of_length (by rw [hplen, hqlen])

lemma plainProgramLengthContextDecompressor_produces
    {V : Map} {p x y : BitString} (hprod : produces V p [] x)
    (hlen : p.length = decodeBits y) :
    produces (plainProgramLengthContextDecompressor V) p y x := by
  unfold produces plainProgramLengthContextDecompressor
  rw [beq_iff_eq.mpr hlen]
  exact hprod

/-- If `kC` is the exact plain complexity of `x`, then `x` has conditional prefix
complexity at most `kC + O(1)` given the binary code of `kC`. -/
theorem KP_le_plainK_value_given_value_code (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kC : ℕ), plainK V x = (kC : ENat) →
      KP U x (Nat.bits kC) ≤ (kC : ENat) + (c : ENat) := by
  have hM : IsPrefixDecompressor (plainProgramLengthContextDecompressor V) :=
    ⟨plainProgramLengthContextDecompressor_computable V hV.1,
      plainProgramLengthContextDecompressor_isPrefixMachine V⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, ?_⟩
  intro x kC hfin
  have hK_ne_top : KP V x [] ≠ ⊤ := by
    change plainK V x ≠ ⊤
    rw [hfin]
    exact ENat.coe_ne_top kC
  obtain ⟨p, hp, hplen⟩ := exists_program_of_KP_ne_top (M := V) (x := x) (y := []) hK_ne_top
  have hp_len_nat : p.length = kC := by
    have : (p.length : ENat) = (kC : ENat) := by
      rw [hplen]
      exact hfin
    exact_mod_cast this
  have hprod : produces (plainProgramLengthContextDecompressor V) p (Nat.bits kC) x :=
    plainProgramLengthContextDecompressor_produces hp (by simp [hp_len_nat, decodeBits_natBits])
  calc
    KP U x (Nat.bits kC)
        ≤ KP (plainProgramLengthContextDecompressor V) x (Nat.bits kC) + (c : ENat) :=
          hc x (Nat.bits kC)
    _ ≤ (kC : ENat) + (c : ENat) := by
        have hp_bound := KP_le_programLength_of_produces hprod
        simpa [programLength, hp_len_nat, add_comm, add_left_comm, add_assoc] using
          add_le_add_right hp_bound (c : ENat)

/-- SUV Theorem 63(b): counting bound. Among the strings of length `n`, the number
whose prefix complexity is below `n + K(n) - c - d` is at most `2^{n-d}`.

The proof is a Kraft/coding argument: each string in the bad set carries
complexity weight at least `2^{-(n+K(n)-c-d)}`, while the total weight of all
length-`n` strings is at most `2^{c}·2^{-K(n)}` by the length-marginal coding
bound `sum_complexityWeight_stringsOfLength_le`. -/
theorem card_KPPlain_lt_length_add_KPPlain_sub_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n d kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
    (Finset.filter (fun x : BitString =>
        KPPlain U x + (d : ENat) < (n : ENat) + (kn : ENat) - (c : ENat))
      (stringsOfLength n)).card ≤ (2 : ℕ) ^ (n - d) := by
  obtain ⟨c, hc⟩ := sum_complexityWeight_stringsOfLength_le U hU
  refine ⟨c, fun n d kn hkn => ?_⟩
  set A := Finset.filter
    (fun x : BitString => KPPlain U x + (d : ENat) < (n : ENat) + (kn : ENat) - (c : ENat))
    (stringsOfLength n) with hA
  -- The total weight of length-`n` strings, from the crux lemma.
  have htot : (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x))
        ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := hc n kn hkn
  -- The threshold, as a (truncated) natural exponent.
  set T : ℕ := (n + kn) - c with hT
  -- `(n:ENat)+(kn:ENat)-(c:ENat) = (T : ENat)`
  have hTcast : (n : ENat) + (kn : ENat) - (c : ENat) = (T : ENat) := by
    rw [hT]; push_cast; rfl
  by_cases hcase : n + kn ≤ c
  · -- The threshold is `0`, so the bad set is empty.
    have hT0 : T = 0 := by rw [hT]; omega
    have hempty : A = ∅ := by
      rw [hA]
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      rw [hTcast, hT0, Nat.cast_zero]
      exact not_lt_bot
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · -- The interesting case: `c < n + kn`.
    have hcle : c ≤ n + kn := (not_le.mp hcase).le
    -- Key pointwise lower bound: each `x ∈ A` has weight `≥ 2^{-T}·2^{d}`.
    have hpt : ∀ x ∈ A, (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d
        ≤ complexityWeight (KPPlain U x) := by
      intro x hx
      rw [hA, Finset.mem_filter] at hx
      have hlt := hx.2
      rw [hTcast] at hlt
      have hle : KPPlain U x + (d : ENat) ≤ (T : ENat) := le_of_lt hlt
      have hmono := complexityWeight_le_of_le hle
      rw [complexityWeight_add_nat, complexityWeight_coe] at hmono
      -- hmono : (2⁻¹)^T ≤ complexityWeight (KPPlain U x) * (2⁻¹)^d
      have hdd : (2 : ℝ≥0∞)⁻¹ ^ d * (2 : ℝ≥0∞) ^ d = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
      calc
        (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d
            ≤ (complexityWeight (KPPlain U x) * (2 : ℝ≥0∞)⁻¹ ^ d) * (2 : ℝ≥0∞) ^ d := by
              gcongr
        _ = complexityWeight (KPPlain U x) * ((2 : ℝ≥0∞)⁻¹ ^ d * (2 : ℝ≥0∞) ^ d) := by ring
        _ = complexityWeight (KPPlain U x) := by rw [hdd, mul_one]
    -- The cardinality times the per-element weight bounds the total weight.
    have hcard : (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d)
        ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := by
      have hsub : A ⊆ stringsOfLength n := Finset.filter_subset _ _
      calc
        (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d)
            = ∑ _x ∈ A, ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ A, complexityWeight (KPPlain U x) := Finset.sum_le_sum hpt
        _ ≤ ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) :=
              Finset.sum_le_sum_of_subset hsub
        _ ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := htot
    -- Cancel the per-element weight to get `card ≤ 2^n · 2^{-d}`.
    have hfin : (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d := by
      have hstep := mul_le_mul_left hcard ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
      have hcancel : (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d *
          ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d) = 1 := by
        have e1 : (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ T = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
        have e2 : (2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d = 1 := by
          rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
        calc
          (2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ d * ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
              = ((2 : ℝ≥0∞)⁻¹ ^ T * (2 : ℝ≥0∞) ^ T) * ((2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d) := by ring
          _ = 1 := by rw [e1, e2, one_mul]
      have hRHS : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn * ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
          = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d := by
        have hcT : c + T = n + kn := by rw [hT]; omega
        have e3 : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ T = (2 : ℝ≥0∞) ^ (n + kn) := by
          rw [← pow_add, hcT]
        have e4 : (2 : ℝ≥0∞) ^ (n + kn) * (2 : ℝ≥0∞)⁻¹ ^ kn = (2 : ℝ≥0∞) ^ n := by
          rw [pow_add, mul_assoc,
            show (2 : ℝ≥0∞) ^ kn * (2 : ℝ≥0∞)⁻¹ ^ kn = 1 from by
              rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow],
            mul_one]
        calc
          (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn * ((2 : ℝ≥0∞) ^ T * (2 : ℝ≥0∞)⁻¹ ^ d)
              = ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ T) * (2 : ℝ≥0∞)⁻¹ ^ kn * (2 : ℝ≥0∞)⁻¹ ^ d := by ring
          _ = (2 : ℝ≥0∞) ^ (n + kn) * (2 : ℝ≥0∞)⁻¹ ^ kn * (2 : ℝ≥0∞)⁻¹ ^ d := by rw [e3]
          _ = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d := by rw [e4]
      rw [mul_assoc, hcancel, mul_one, hRHS] at hstep
      exact hstep
    -- Convert the `ℝ≥0∞` bound to the `ℕ` cardinality bound.
    have hcast : (A.card : ℝ≥0∞) ≤ ((2 ^ (n - d) : ℕ) : ℝ≥0∞) :=
      le_trans hfin (two_pow_mul_inv_pow_le_cast_pow_sub n d)
    exact_mod_cast hcast

/-- SUV Theorem 65: `K(x) ≤ C(x) + K(C(x)) + O(1)`. -/
theorem KPPlain_le_plainK_add_KPPlain_plainK (U V : Map)
    (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (kC : ℕ), plainK V x = (kC : ENat) →
      KPPlain U x ≤ (kC : ENat) + KPPlain U (Nat.bits kC) + (c : ENat) := by
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_cond, h_cond⟩ := KP_le_plainK_value_given_value_code U V hU hV
  refine ⟨c_cond + c_sub, ?_⟩
  intro x kC hfin
  calc
    KPPlain U x
        ≤ KPPlain U (Nat.bits kC) + KP U x (Nat.bits kC) + (c_sub : ENat) :=
          h_sub x (Nat.bits kC)
    _ ≤ KPPlain U (Nat.bits kC) + ((kC : ENat) + (c_cond : ENat)) + (c_sub : ENat) := by
        gcongr
        exact h_cond x kC hfin
    _ = (kC : ENat) + KPPlain U (Nat.bits kC) + ((c_cond + c_sub : ℕ) : ENat) := by
        rw [Nat.cast_add]
        simp [add_comm, add_left_comm, add_assoc]

end Kolmogorov
