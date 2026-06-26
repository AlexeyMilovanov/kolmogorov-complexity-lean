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
import KolmogorovMathlib.Prefix.Properties.Basic

/-!
# Pair Properties of Prefix Complexity

This module collects projection and subadditivity bounds for encoded pairs.
-/

namespace Kolmogorov
open scoped ENNReal

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



end Kolmogorov
