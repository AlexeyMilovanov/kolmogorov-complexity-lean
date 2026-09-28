/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# Restriction of a sequence to a finite index set: the event `ω(F) = Z`

SUV p. 149 (Problems 144 and 145) uses `ω(F)`, the string of the bits `ω i` for `i ∈ F` read
in increasing order of `i`, and `p_{F,Z} = μ{ω : ω(F) = Z}`.

This module supplies the measure-theoretic half of what those problems need: the event
`ω(F) = Z` is a **finite disjoint union of cylinders** of any level `N` above `F`, so `p_{F,Z}`
is a finite sum of cylinder masses.  In particular `p_{F,Z}` is a finite sum of quantities
that the computability of `μ` approximates from both sides, which is exactly the shape the
enumerability of the deficiency set of Problem 144 needs.

## The `Finset ℕ` computability that this rests on

Mathlib's `Primcodable (Finset ℕ)` instance is `Primcodable.ofDenumerable`, i.e. the code of
`F` is its **rank** in the `Encodable` enumeration and not the `Encodable` code itself:
`encode (Finset.range 2) = 2` and `encode (Finset.range 3) = 5`, while the `Finset.encodable`
codes of the same sets are `10` and `2602`.  Consequently neither
`Computable fun F : Finset ℕ => F.sort (· ≤ ·)` nor `Computable fun i : ℕ => Finset.range i`
is available off the shelf, and both are needed: the first to evaluate `restrictStr` inside an
r.e. predicate (Problem 144), the second to make Problem 145's hypothesis `Computable F` usable.

Both are supplied by `LevinSchnorr/FinsetComputable.lean`.  The rank indirection is harmless
because Mathlib's `Denumerable (Finset ℕ)` instance is *itself* built from the sorted list,
through the `lower'`/`raise'` pair:
`(ofNat (Finset ℕ) n).sort (· ≤ ·) = raise' (ofNat (List ℕ) n) 0`, and `raise'` is a plain
`List.foldr`.

## Main results

* `restrictStr` — the string version of `restrictSeq`, and `restrictSeq_eq_restrictStr`;
* `setOf_restrictSeq_eq_biUnion`, `finsetEventMass_eq_sum` —
  `p_{F,Z} = ∑ {μ(Ω_x) : |x| = N, x(F) = Z}` for any `N` above `F`.
-/

namespace Kolmogorov

open MeasureTheory

open scoped ENNReal

/-! ### The string version of the restriction -/

/-- SUV p. 149: `x(F)`, the restriction of the *string* `x` to the finite index set `F`.
Coincides with `restrictSeq F w` whenever `x` is a long enough prefix of `w`. -/
def restrictStr (F : Finset ℕ) (x : BitString) : BitString :=
  (F.sort (· ≤ ·)).map (fun i => x.getD i false)

/-- Restricting a sequence to coordinates below `n` is the same as restricting its length-`n`
prefix. -/
lemma restrictSeq_eq_restrictStr {F : Finset ℕ} {w : CantorSeq} {n : ℕ}
    (hF : ∀ i ∈ F, i < n) : restrictSeq F w = restrictStr F (cantorPrefix w n) := by
  rw [restrictSeq, restrictStr]
  refine List.map_congr_left fun i hi => ?_
  have hin : i < n := hF i ((Finset.mem_sort (· ≤ ·)).mp hi)
  have hlen : i < (cantorPrefix w n).length := by rw [cantorPrefix_length]; exact hin
  rw [List.getD_eq_getElem _ _ hlen, cantorPrefix_getElem]

/-- Restricting a string to a finite set of coordinates gives a string of that set's cardinality. -/
@[simp] lemma length_restrictStr (F : Finset ℕ) (x : BitString) :
    (restrictStr F x).length = F.card := by
  simp [restrictStr]

/-! ### The event `ω(F) = Z` as a finite disjoint union of cylinders -/

open scoped Classical in
/-- The strings of length `N` that restrict to `Z` on `F`. -/
noncomputable def restrictSlice (F : Finset ℕ) (Z : BitString) (N : ℕ) : Finset BitString :=
  (levelFinset N).filter fun x => restrictStr F x = Z

/-- Cylinders over distinct strings of a common length are pairwise disjoint. -/
lemma cantorCylinder_pairwiseDisjoint (N : ℕ) (S : Finset BitString)
    (hS : ∀ x ∈ S, x.length = N) : (S : Set BitString).PairwiseDisjoint cantorCylinder := by
  intro x hx y hy hxy
  refine Set.disjoint_left.mpr fun w hwx hwy => ?_
  have h1 : cantorPrefix w N = x := by
    rw [← hS x hx]
    exact (isCantorPrefix_iff_cantorPrefix_eq x w).1 hwx
  have h2 : cantorPrefix w N = y := by
    rw [← hS y hy]
    exact (isCantorPrefix_iff_cantorPrefix_eq y w).1 hwy
  exact hxy (h1 ▸ h2 ▸ rfl)

/-- The event that the coordinates in `F` read `Z` is the union of the cylinders of the length-`N`
strings with that restriction. -/
lemma setOf_restrictSeq_eq_biUnion {F : Finset ℕ} {N : ℕ} (hF : ∀ i ∈ F, i < N)
    (Z : BitString) :
    {w : CantorSeq | restrictSeq F w = Z}
      = ⋃ x ∈ restrictSlice F Z N, cantorCylinder x := by
  classical
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, restrictSlice,
    Finset.mem_filter, mem_levelFinset]
  constructor
  · intro hw
    refine ⟨cantorPrefix w N, ⟨cantorPrefix_length w N, ?_⟩, ?_⟩
    · rw [← restrictSeq_eq_restrictStr hF]
      exact hw
    · exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 (by rw [cantorPrefix_length])
  · rintro ⟨x, ⟨hxlen, hxZ⟩, hwx⟩
    have hx : cantorPrefix w N = x := by
      rw [← hxlen]
      exact (isCantorPrefix_iff_cantorPrefix_eq x w).1 hwx
    rw [restrictSeq_eq_restrictStr hF, hx]
    exact hxZ

/-- SUV p. 149: `p_{F,Z}` is the sum of the masses of the cylinders of any level `N` above
`F` that restrict to `Z`. -/
theorem finsetEventMass_eq_sum (μ : Measure CantorSeq) {F : Finset ℕ} {N : ℕ}
    (hF : ∀ i ∈ F, i < N) (Z : BitString) :
    finsetEventMass μ F Z = ∑ x ∈ restrictSlice F Z N, cantorMass μ x := by
  classical
  rw [finsetEventMass, setOf_restrictSeq_eq_biUnion hF Z]
  refine measure_biUnion_finset ?_ (fun x _ => measurableSet_cantorCylinder x)
  refine cantorCylinder_pairwiseDisjoint N _ fun x hx => ?_
  rw [restrictSlice, Finset.mem_filter, mem_levelFinset] at hx
  exact hx.1

end Kolmogorov
