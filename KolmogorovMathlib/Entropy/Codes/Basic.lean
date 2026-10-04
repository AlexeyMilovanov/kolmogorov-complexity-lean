/-
Copyright (c) 2024 The KolmogorovMathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Contributors
-/
import KolmogorovMathlib.Core.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

/-!
# Codes over a finite alphabet

SUV Section 7.1, pp. 213–217.  A code assigns a binary codeword to every letter of an
alphabet `α`; a word over `α` is encoded by concatenating the codewords of its letters.

The two decodability notions of the section are `Code.IsPrefixFree` (no codeword is empty and no
codeword is a prefix of another one) and `Code.IsUniquelyDecodable` (the encoding of words is
injective), and the two numerical quantities are the average codeword length `Code.avgLength`
(Theorem 138 is stated for a distribution, so the average is taken against a weight function) and
the Kraft sum `Code.kraftSum` of Kraft's inequality and the McMillan inequality.

The non-emptiness of the codewords is *not* part of the book's definition of a prefix code
(p. 213 defines it as "a code where no codeword is a prefix of another codeword", and the Kraft
lemma of p. 214 is printed for non-negative lengths); it is a **repair** that this library
adopts, because Theorem 137 is false for the printed definition on a one-letter alphabet.  See
the docstring of `Code.IsPrefixFree` and the deviation table of Chapter 7.

Mathlib's `InformationTheory.IsPrefixFree` and `IsUniquelyDecodable`, which live on
`Set (List β)`, do not exist at this toolchain pin; the names below are the library's own and
a later Mathlib bump can add bridges.
-/

namespace Kolmogorov

open Finset

/-- A code over the alphabet `α`: a binary codeword for every letter.  This is an `abbrev`,
so that the instances of the underlying function type (`DecidableEq`, `Fintype` when the
codewords are restricted, the pointwise algebraic structure) apply to codes directly.
SUV Section 7.1.1, p. 213. -/
abbrev Code (α : Type*) := α → BitString

namespace Code

variable {α : Type*}

/-- The encoding of a word: the codewords of its letters, concatenated without separators.
SUV Section 7.1.1, p. 213. -/
def encodeWord (c : Code α) (w : List α) : BitString := (w.map c).flatten

/-- The empty word is encoded by the empty string.  SUV Section 7.1.1, p. 213. -/
@[simp] theorem encodeWord_nil (c : Code α) : c.encodeWord [] = [] := rfl

/-- Encoding a word letter by letter: the head's codeword, then the encoding of the tail.
SUV Section 7.1.1, p. 213. -/
@[simp] theorem encodeWord_cons (c : Code α) (a : α) (w : List α) :
    c.encodeWord (a :: w) = c a ++ c.encodeWord w := rfl

/-- A code is prefix-free when no codeword is empty and no codeword is a prefix of the codeword
of another letter.

The second conjunct is the book's condition "no codeword is a prefix of another codeword"; it
already forces distinct letters to get distinct codewords (`Code.IsPrefixFree.injective`), since
a string is a prefix of itself.

The first conjunct is **not** the book's, tacitly or otherwise: the definition of a code on
p. 213 admits every binary string as a codeword, and the Kraft lemma on p. 214 explicitly ranges
over non-negative lengths `n_i`, so the empty codeword is allowed there.  It is a **repair**
adopted by this library, because the printed definition makes Theorem 137 false: the code
`a ↦ ε` of a one-letter alphabet satisfies the printed condition vacuously and is not uniquely
decodable, since `ε` encodes every word.  For an alphabet with at least two letters the first
conjunct follows from the second (an empty codeword is a prefix of every other codeword), so the
repair changes nothing there; its only visible trace in the chapter is the conjunct `0 < n a` in
`Code.exists_isPrefixFree_lengths_iff_kraft`.  SUV Section 7.1.1, p. 213. -/
def IsPrefixFree (c : Code α) : Prop :=
  (∀ a : α, c a ≠ []) ∧ ∀ a b : α, a ≠ b → ¬ (c a <+: c b)

/-- No codeword of a prefix code is empty.  SUV Section 7.1.1, p. 213. -/
theorem IsPrefixFree.ne_nil {c : Code α} (h : c.IsPrefixFree) (a : α) : c a ≠ [] := h.1 a

/-- A prefix code is injective: distinct letters have distinct codewords, because a codeword is
a prefix of itself.  SUV Section 7.1.1, p. 213. -/
theorem IsPrefixFree.injective {c : Code α} (h : c.IsPrefixFree) : Function.Injective c := by
  intro a b hab
  by_contra hne
  exact h.2 a b hne ⟨[], by rw [List.append_nil, hab]⟩

/-- A code is uniquely decodable when distinct words get distinct encodings.
SUV Section 7.1.1, p. 213. -/
def IsUniquelyDecodable (c : Code α) : Prop := Function.Injective c.encodeWord

/-- The average codeword length of a code against a distribution on the alphabet,
`∑ a, p a · |c a|`.  Theorem 138 bounds this quantity from below by the entropy of `p`.
SUV Section 7.1, p. 214. -/
def avgLength [Fintype α] (c : Code α) (p : α → ℝ) : ℝ := ∑ a, p a * (c a).length

/-- The Kraft sum `∑ a, 2^(-|c a|)` of a code, the quantity bounded by one in Kraft's
inequality and in the McMillan inequality.  SUV Section 7.1.2, p. 214. -/
noncomputable def kraftSum [Fintype α] (c : Code α) : ℝ := ∑ a, (2 : ℝ)⁻¹ ^ (c a).length

/-- The Kraft sum is non-negative.  SUV Section 7.1.1, pp. 213–214. -/
theorem kraftSum_nonneg [Fintype α] (c : Code α) : 0 ≤ c.kraftSum :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (by norm_num) _

end Code

end Kolmogorov
