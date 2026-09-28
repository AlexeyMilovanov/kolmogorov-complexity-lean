import Mathlib.Algebra.Order.BigOperators.Group.Finset
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.CommonInformation.Definitions

/-!
# Counting the pairs with a common witness

The counting behind the non-extractability of common information: the pairs that do admit a
short common witness are too few to cover a positive fraction of all pairs.

`commonWitnessPairsLe` is the set of pairs `(x, y)` with a witness `z` satisfying
`K(z) ≤ α`, `K(x|z) ≤ β`, `K(y|z) ≤ γ`, characterised by
`mem_commonWitnessPairsLe_iff` and bounded by `card_commonWitnessPairsLe_lt`: fewer than
`2 ^ (α + β + γ + 3)`.  `card_conditionallyCompressiblePairs_lt` is the companion bound for
pairs with two conditionally compressible components, and the three
`card_fixedLengthPairs_*_lt` lemmas count, among pairs of length-`L` strings, those with a
simple left component, a simple right component, or a simple pair.
-/

namespace Kolmogorov

/-- There are fewer than `2^{β+γ+2}` pairs both of whose components are conditionally compressible
below the respective thresholds. -/
theorem card_conditionallyCompressiblePairs_lt
    (V : Map) (z : BitString) (β γ : Nat) :
  ((compressibleWords V z β).product
    (compressibleWords V z γ)).card <
      2 ^ ((β + 1) + (γ + 1)) := by
  change ((compressibleWords V z β ×ˢ compressibleWords V z γ).card <
    2 ^ ((β + 1) + (γ + 1)))
  rw [Finset.card_product, pow_add]
  have hβ := card_compressibleWordsLt V z β
  have hγ := card_compressibleWordsLt V z γ
  calc
    (compressibleWords V z β).card * (compressibleWords V z γ).card
        ≤ (compressibleWords V z β).card * 2 ^ (γ + 1) :=
      Nat.mul_le_mul_left _ hγ.le
    _ < 2 ^ (β + 1) * 2 ^ (γ + 1) :=
      Nat.mul_lt_mul_of_pos_right hβ (Nat.pow_pos (by norm_num))

/-- The pairs `(x, y)` admitting a common witness `z` with `K(z) ≤ α`, `K(x|z) ≤ β` and
`K(y|z) ≤ γ`. -/
noncomputable def commonWitnessPairsLe
    (V : Map) (α β γ : Nat) :
    Finset (BitString × BitString) :=
  (compressibleWords V [] α).biUnion fun z =>
    (compressibleWords V z β).product
      (compressibleWords V z γ)

/-- Exact semantic membership in `compressibleWords`: a string lies in the
`k`-bounded compressible set for condition `y` iff its conditional complexity
given `y` is at most `k`. -/
theorem mem_compressibleWords_iff
    (V : Map) (y x : BitString) (k : Nat) :
  x ∈ compressibleWords V y k ↔ condK V x y ≤ (k : ENat) := by
  rw [compressibleWords, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hx
    refine ⟨?_, hx⟩
    obtain ⟨p, hpLen, hp⟩ := (condK_le_iff V x y k).mp hx
    rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, mem_programsLe k p hpLen, progToOut_eq_some.mpr hp⟩

/-- Exact semantic membership in `commonWitnessPairsLe`: a pair lies in the
three-parameter common-witness set iff there is a common witness `z` with the
three non-strict complexity bounds. -/
theorem mem_commonWitnessPairsLe_iff
    (V : Map) (α β γ : Nat) (x y : BitString) :
  (x, y) ∈ commonWitnessPairsLe V α β γ ↔
    ∃ z, plainK V z ≤ (α : ENat) ∧
      condK V x z ≤ (β : ENat) ∧
      condK V y z ≤ (γ : ENat) := by
  rw [commonWitnessPairsLe, Finset.mem_biUnion]
  constructor
  · rintro ⟨z, hz, hxy⟩
    change (x, y) ∈
      compressibleWords V z β ×ˢ compressibleWords V z γ at hxy
    rw [Finset.mem_product] at hxy
    exact ⟨z, (mem_compressibleWords_iff V [] z α).mp hz,
      (mem_compressibleWords_iff V z x β).mp hxy.1,
      (mem_compressibleWords_iff V z y γ).mp hxy.2⟩
  · rintro ⟨z, hz, hx, hy⟩
    refine ⟨z, (mem_compressibleWords_iff V [] z α).mpr hz, ?_⟩
    change (x, y) ∈
      compressibleWords V z β ×ˢ compressibleWords V z γ
    rw [Finset.mem_product]
    exact ⟨(mem_compressibleWords_iff V z x β).mpr hx,
      (mem_compressibleWords_iff V z y γ).mpr hy⟩

/-- Fewer than `2^{α+β+γ+3}` pairs admit a common witness within the given thresholds. -/
theorem card_commonWitnessPairsLe_lt
    (V : Map) (α β γ : Nat) :
  (commonWitnessPairsLe V α β γ).card <
    2 ^ ((α + 1) + (β + 1) + (γ + 1)) := by
  unfold commonWitnessPairsLe
  have hα := card_compressibleWordsLt V [] α
  have hEach :
      ∀ z ∈ compressibleWords V [] α,
        ((compressibleWords V z β).product
          (compressibleWords V z γ)).card ≤
            2 ^ ((β + 1) + (γ + 1)) := by
    intro z _
    exact (card_conditionallyCompressiblePairs_lt V z β γ).le
  calc
    ((compressibleWords V [] α).biUnion fun z =>
        (compressibleWords V z β).product
          (compressibleWords V z γ)).card
        ≤ ∑ z ∈ compressibleWords V [] α,
            ((compressibleWords V z β).product
              (compressibleWords V z γ)).card :=
      Finset.card_biUnion_le
    _ ≤ (compressibleWords V [] α).card *
          2 ^ ((β + 1) + (γ + 1)) :=
      Finset.sum_le_card_nsmul _ _ _ hEach
    _ < 2 ^ (α + 1) * 2 ^ ((β + 1) + (γ + 1)) :=
      Nat.mul_lt_mul_of_pos_right hα (Nat.pow_pos (by norm_num))
    _ = 2 ^ ((α + 1) + (β + 1) + (γ + 1)) := by
      rw [← pow_add]
      congr 1
      omega

/-- Among the pairs of length-`L` strings, fewer than `2^{L+t+1}` have a left component of
complexity at most `t`. -/
theorem card_fixedLengthPairs_lowLeft_lt
    (V : Map) (L t : Nat) :
  (((stringsOfLength L).product (stringsOfLength L)).filter
      fun p => plainK V p.1 ≤ (t : ENat)).card <
    2 ^ (L + t + 1) := by
  have hsub :
      ((stringsOfLength L).product (stringsOfLength L)).filter
          (fun p => plainK V p.1 ≤ (t : ENat)) ⊆
        (compressibleWords V [] t).product (stringsOfLength L) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    change p ∈ stringsOfLength L ×ˢ stringsOfLength L ∧
      plainK V p.1 ≤ (t : ENat) at hp
    rw [Finset.mem_product] at hp
    change p ∈ compressibleWords V [] t ×ˢ stringsOfLength L
    rw [Finset.mem_product]
    refine ⟨?_, hp.1.2⟩
    rw [compressibleWords, Finset.mem_filter]
    refine ⟨?_, hp.2⟩
    obtain ⟨q, hqLen, hq⟩ :=
      (condK_le_iff V p.1 [] t).mp hp.2
    rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨q, mem_programsLe t q hqLen, progToOut_eq_some.mpr hq⟩
  have hcomp := card_compressibleWordsLt V [] t
  calc
    (((stringsOfLength L).product (stringsOfLength L)).filter
        fun p => plainK V p.1 ≤ (t : ENat)).card
        ≤ ((compressibleWords V [] t).product
          (stringsOfLength L)).card :=
      Finset.card_le_card hsub
    _ = (compressibleWords V [] t).card * 2 ^ L := by
      change (compressibleWords V [] t ×ˢ stringsOfLength L).card =
        (compressibleWords V [] t).card * 2 ^ L
      rw [Finset.card_product, card_stringsOfLength]
    _ < 2 ^ (t + 1) * 2 ^ L :=
      Nat.mul_lt_mul_of_pos_right hcomp (Nat.pow_pos (by norm_num))
    _ = 2 ^ (L + t + 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- Among the pairs of length-`L` strings, fewer than `2^{L+t+1}` have a right component of
complexity at most `t`. -/
theorem card_fixedLengthPairs_lowRight_lt
    (V : Map) (L t : Nat) :
  (((stringsOfLength L).product (stringsOfLength L)).filter
      fun p => plainK V p.2 ≤ (t : ENat)).card <
    2 ^ (L + t + 1) := by
  have hsub :
      ((stringsOfLength L).product (stringsOfLength L)).filter
          (fun p => plainK V p.2 ≤ (t : ENat)) ⊆
        (stringsOfLength L).product (compressibleWords V [] t) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    change p ∈ stringsOfLength L ×ˢ stringsOfLength L ∧
      plainK V p.2 ≤ (t : ENat) at hp
    rw [Finset.mem_product] at hp
    change p ∈ stringsOfLength L ×ˢ compressibleWords V [] t
    rw [Finset.mem_product]
    refine ⟨hp.1.1, ?_⟩
    rw [compressibleWords, Finset.mem_filter]
    refine ⟨?_, hp.2⟩
    obtain ⟨q, hqLen, hq⟩ :=
      (condK_le_iff V p.2 [] t).mp hp.2
    rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨q, mem_programsLe t q hqLen, progToOut_eq_some.mpr hq⟩
  have hcomp := card_compressibleWordsLt V [] t
  calc
    (((stringsOfLength L).product (stringsOfLength L)).filter
        fun p => plainK V p.2 ≤ (t : ENat)).card
        ≤ ((stringsOfLength L).product
          (compressibleWords V [] t)).card :=
      Finset.card_le_card hsub
    _ = 2 ^ L * (compressibleWords V [] t).card := by
      change (stringsOfLength L ×ˢ compressibleWords V [] t).card =
        2 ^ L * (compressibleWords V [] t).card
      rw [Finset.card_product, card_stringsOfLength]
    _ < 2 ^ L * 2 ^ (t + 1) :=
      Nat.mul_lt_mul_of_pos_left hcomp (Nat.pow_pos (by norm_num))
    _ = 2 ^ (L + t + 1) := by
      rw [← pow_add]
      congr 1

/-- Among the pairs of length-`L` strings, fewer than `2^{t+1}` have pair complexity at
most `t`. -/
theorem card_fixedLengthPairs_lowPair_lt
    (V : Map) (L t : Nat) :
  (((stringsOfLength L).product (stringsOfLength L)).filter
      fun p => pairPlainK V p.1 p.2 ≤ (t : ENat)).card <
    2 ^ (t + 1) := by
  let bad :=
    ((stringsOfLength L).product (stringsOfLength L)).filter
      fun p => pairPlainK V p.1 p.2 ≤ (t : ENat)
  let encodePair : BitString × BitString → BitString :=
    fun p => pairCode p.1 p.2
  have hsub : bad.image encodePair ⊆ compressibleWords V [] t := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    have hpComplex : pairPlainK V p.1 p.2 ≤ (t : ENat) := by
      dsimp [bad] at hp
      rw [Finset.mem_filter] at hp
      exact hp.2
    rw [compressibleWords, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hqLen, hq⟩ :=
        (condK_le_iff V (pairCode p.1 p.2) [] t).mp hpComplex
      rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨q, mem_programsLe t q hqLen, progToOut_eq_some.mpr hq⟩
    · exact hpComplex
  have hcardImage : (bad.image encodePair).card = bad.card :=
    Finset.card_image_of_injective bad pairCode_injective
  calc
    (((stringsOfLength L).product (stringsOfLength L)).filter
        fun p => pairPlainK V p.1 p.2 ≤ (t : ENat)).card
        = bad.card := rfl
    _ = (bad.image encodePair).card := hcardImage.symm
    _ ≤ (compressibleWords V [] t).card := Finset.card_le_card hsub
    _ < 2 ^ (t + 1) := card_compressibleWordsLt V [] t

end Kolmogorov
