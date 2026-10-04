/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Encoding.Tuples
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange

/-!
# Complexity of tuples of bit strings

SUV Sections 10.1 and 12.1, pp. 313–318 and pp. 367–369.  Chapters 10 and 12 work with an
`n`-tuple `x = (x_1, …, x_n)` of bit strings and with the complexities `C(x_I)` and
`C(x_J | x_I)` of its subtuples, indexed by subsets `I, J ⊆ {1, …, n}`.

A subtuple is turned into a single bit string by `listCode`, applied to the components in
increasing order of index, so that `x_I` is a definite string.  All the complexities below are
therefore plain complexities of definite strings and take values in `ℕ∞`; which decompressor
is meant is the explicit argument `D`, and the chapter statements quantify it with
`isOptimalConditional`.  A different self-delimiting packing changes every quantity by at most
an additive constant, which the `O(log N)` terms of the chapter absorb.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-- The code of a whole tuple of bit strings: the self-delimiting code of the list of its
components.  SUV Section 10.1, p. 313. -/
def tupleCode (x : Fin n → BitString) : BitString := listCode (List.ofFn x)

/-- The code of the subtuple `x_I`: the components with index in `I`, in increasing order of
index, packed by `listCode`.  SUV Section 10.1, p. 314. -/
def subtupleCode (x : Fin n → BitString) (I : Finset (Fin n)) : BitString :=
  listCode ((I.sort (· ≤ ·)).map x)

/-- The empty subtuple is coded by the empty string. -/
@[simp] theorem subtupleCode_empty (x : Fin n → BitString) : subtupleCode x ∅ = [] := by
  simp [subtupleCode]

/-- The subtuple over all indices is the whole tuple. -/
theorem subtupleCode_univ (x : Fin n → BitString) :
    subtupleCode x Finset.univ = tupleCode x := by
  simp [subtupleCode, tupleCode, Fin.sort_univ, List.ofFn_eq_map]

/-- The plain complexity `C(x_I)` of a subtuple, with respect to the decompressor `D`.
SUV Section 10.1, p. 314. -/
noncomputable def tuplePlainK (D : Map) (x : Fin n → BitString) (I : Finset (Fin n)) : ℕ∞ :=
  plainK D (subtupleCode x I)

/-- The conditional plain complexity `C(x_J | x_I)` of one subtuple given another, with
respect to the decompressor `D`.  SUV Section 10.1, p. 314. -/
noncomputable def tupleCondK (D : Map) (x : Fin n → BitString)
    (J I : Finset (Fin n)) : ℕ∞ :=
  condK D (subtupleCode x J) (subtupleCode x I)

/-- For an optimal decompressor the complexity of a subtuple is finite: every string is
described by a program of length `|x| + O(1)`.  Statements that cast a complexity to `ℕ` with
`ENat.toNat` need this, since `ENat.toNat ⊤ = 0` would silently turn an infinite complexity
into zero.  SUV Section 10.1, p. 314. -/
theorem tuplePlainK_ne_top (D : Map) (hD : isOptimalConditional D) (x : Fin n → BitString)
    (I : Finset (Fin n)) : tuplePlainK D x I ≠ ⊤ := by
  obtain ⟨c, hc⟩ := plainK_le_length D hD
  exact ne_top_of_le_natCast_add (hc (subtupleCode x I))

/-- For an optimal decompressor the conditional complexity of a subtuple given another is
finite: it is at most the unconditional one, up to an additive constant.  SUV Section 10.1,
p. 314. -/
theorem tupleCondK_ne_top (D : Map) (hD : isOptimalConditional D) (x : Fin n → BitString)
    (J I : Finset (Fin n)) : tupleCondK D x J I ≠ ⊤ := by
  obtain ⟨c, hc⟩ := condK_le_plainK D hD
  obtain ⟨d, hd⟩ := plainK_le_length D hD
  refine ne_top_of_le_natCast
    (n := programLength (subtupleCode x J) + d + c) ?_
  calc tupleCondK D x J I ≤ plainK D (subtupleCode x J) + (c : ℕ∞) := hc _ _
    _ ≤ ((programLength (subtupleCode x J) : ℕ∞) + (d : ℕ∞)) + (c : ℕ∞) := by
        gcongr
        exact hd _
    _ = ((programLength (subtupleCode x J) + d + c : ℕ) : ℕ∞) := by push_cast; ring

/-- The complexity vector `κ(x)` of a tuple: the family of the complexities of all its
subtuples, the point of `ℕ∞ ^ (2 ^ n)` that Chapter 10 compares with entropy vectors.
SUV Section 10.1, p. 314. -/
noncomputable def complexityVector (D : Map) (x : Fin n → BitString) :
    Finset (Fin n) → ℕ∞ :=
  fun I => tuplePlainK D x I

/-- The length of the longest component of a tuple.  This is the `N` of the `O(log N)` terms
in the inequalities of SUV Section 10.1, p. 315, where the strings have length at most `N`. -/
def tupleMaxLength (x : Fin n → BitString) : ℕ := Finset.univ.sup fun i => (x i).length

/-- Every component of a tuple is at most as long as the longest one. -/
theorem length_le_tupleMaxLength (x : Fin n → BitString) (i : Fin n) :
    (x i).length ≤ tupleMaxLength x :=
  Finset.le_sup (f := fun j => (x j).length) (Finset.mem_univ i)

end Kolmogorov
