/-
Copyright (c) 2024 The KolmogorovMathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Contributors
-/
import KolmogorovMathlib.Entropy.Codes.Basic
import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Log

/-!
# A fixed binary encoding of words over a finite alphabet

SUV Sections 7.1 and 7.3, pp. 213 and 226–229.  The book measures the Kolmogorov complexity
of a word over a `k`-letter alphabet by fixing, once and for all, some computable injective
encoding of such words by bit strings; all choices agree up to an additive constant, so the
choice is immaterial for the statements.  This module makes one choice and names it, so that
`plainK D (wordBits w)` is a definite quantity.

The choice: each letter is written in a block of `alphabetWidth α = ⌊log₂ |α|⌋ + 1` bits
holding its rank `alphabetIndex α a` in the order that `Encodable.encode` induces on `α`
(`natBitsFixed` writes a number in a fixed number of bits, least significant bit first).
Since `|α| < 2 ^ alphabetWidth α`, distinct letters get distinct blocks, and because all
blocks have the same length the resulting code is prefix-free
(`alphabetCode_isPrefixFree`), hence the word encoding `wordBits` is injective.
-/

namespace Kolmogorov

open Finset

/-- The `w` low bits of `k`, least significant bit first. -/
def natBitsFixed (w k : ℕ) : BitString := List.ofFn fun i : Fin w => Nat.testBit k i

/-- A fixed-width block has exactly the prescribed length. -/
@[simp] theorem length_natBitsFixed (w k : ℕ) : (natBitsFixed w k).length = w := by
  simp [natBitsFixed]

/-- Numbers below `2 ^ w` are determined by their `w` low bits. -/
theorem natBitsFixed_inj {w k m : ℕ} (hk : k < 2 ^ w) (hm : m < 2 ^ w)
    (h : natBitsFixed w k = natBitsFixed w m) : k = m := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < w
  · exact congrFun (List.ofFn_inj.1 h) ⟨i, hi⟩
  · have hle : (2 : ℕ) ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_eq_false_of_lt (hk.trans_le hle),
      Nat.testBit_eq_false_of_lt (hm.trans_le hle)]

variable (α : Type*) [Fintype α] [Encodable α]

/-- The block width used for one letter of `α`: `⌊log₂ |α|⌋ + 1` bits, enough to hold every
rank below `|α|`.  SUV Section 7.1.1, p. 213. -/
def alphabetWidth : ℕ := Nat.log 2 (Fintype.card α) + 1

/-- The rank of a letter in the order that `Encodable.encode` induces on `α`: the number of
letters whose code is smaller.  This is a bijection onto `{0, …, |α| - 1}`, which
`Encodable.encode` itself need not be.  SUV Section 7.1.1, p. 213. -/
def alphabetIndex (a : α) : ℕ :=
  (Finset.univ.filter fun b : α => Encodable.encode b < Encodable.encode a).card

variable {α}

/-- A letter of smaller code has a smaller rank. -/
theorem alphabetIndex_lt_alphabetIndex {a b : α}
    (h : Encodable.encode a < Encodable.encode b) : alphabetIndex α a < alphabetIndex α b := by
  have hsub : (Finset.univ.filter fun c : α => Encodable.encode c < Encodable.encode a) ⊆
      Finset.univ.filter fun c : α => Encodable.encode c < Encodable.encode b := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans h
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨a, ?_, ?_⟩) <;> simp [h]

/-- Distinct letters have distinct ranks. -/
theorem alphabetIndex_injective : Function.Injective (alphabetIndex α) := by
  intro a b hab
  by_contra hne
  have hne' : Encodable.encode a ≠ Encodable.encode b := fun h =>
    hne (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact absurd hab (Nat.ne_of_lt (alphabetIndex_lt_alphabetIndex h))
  · exact absurd hab.symm (Nat.ne_of_lt (alphabetIndex_lt_alphabetIndex h))

/-- Ranks are smaller than the size of the alphabet. -/
theorem alphabetIndex_lt_card (a : α) : alphabetIndex α a < Fintype.card α := by
  have hsub : (Finset.univ.filter fun b : α => Encodable.encode b < Encodable.encode a) ⊂
      (Finset.univ : Finset α) :=
    (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2 ⟨a, Finset.mem_univ a, by simp⟩
  simpa [alphabetIndex] using Finset.card_lt_card hsub

/-- A rank fits into a block of `alphabetWidth α` bits. -/
theorem alphabetIndex_lt_two_pow (a : α) : alphabetIndex α a < 2 ^ alphabetWidth α :=
  (alphabetIndex_lt_card a).trans (Nat.lt_pow_succ_log_self (by norm_num) _)

variable (α)

/-- The fixed binary code of the alphabet `α`: the rank of a letter, written in a block of
`alphabetWidth α` bits.  This is the library's definitional choice for "the binary encoding of
a `k`-letter alphabet" of SUV Section 7.1.1, p. 213; the book allows any fixed computable
encoding, and all of them agree up to an additive constant. -/
def alphabetCode : Code α := fun a => natBitsFixed (alphabetWidth α) (alphabetIndex α a)

variable {α}

/-- Every codeword of the fixed alphabet code has length `alphabetWidth α`. -/
@[simp] theorem length_alphabetCode (a : α) :
    (alphabetCode α a).length = alphabetWidth α := length_natBitsFixed _ _

/-- The fixed alphabet code is prefix-free: its codewords are non-empty, distinct and all of the
same length. -/
theorem alphabetCode_isPrefixFree : (alphabetCode α).IsPrefixFree := by
  have hinj : Function.Injective (alphabetCode α) := by
    intro a b hab
    exact alphabetIndex_injective
      (natBitsFixed_inj (alphabetIndex_lt_two_pow a) (alphabetIndex_lt_two_pow b) hab)
  refine ⟨fun a hnil => ?_, fun a b hne hpre => hne (hinj ?_)⟩
  · have h := length_alphabetCode (α := α) a
    rw [hnil] at h
    simp only [List.length_nil, alphabetWidth] at h
    omega
  · exact hpre.eq_of_length (by simp)

variable (α)

/-- The bit string that codes a word over `α`: the fixed-width blocks of its letters,
concatenated.  The plain complexity of an `α`-word is `plainK D (wordBits w)`.
SUV Sections 7.1 and 7.3, pp. 213 and 226. -/
def wordBits (w : List α) : BitString := (alphabetCode α).encodeWord w

variable {α}

/-- The code of a word has `alphabetWidth α` bits per letter. -/
@[simp] theorem length_wordBits (w : List α) :
    (wordBits α w).length = w.length * alphabetWidth α := by
  induction w with
  | nil => simp [wordBits]
  | cons a w ih =>
    simp only [wordBits, Code.encodeWord_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih, length_alphabetCode]
    exact (Nat.add_comm _ _).trans (Nat.succ_mul _ _).symm

/-- The code of a word determines the word: all blocks have the same positive length, so the
encoding can be cut back into blocks and each block decoded.  This is what makes
`plainK D (wordBits α w)` a faithful measure of the complexity of an `α`-word.
SUV Sections 7.1 and 7.3, pp. 213 and 226. -/
theorem wordBits_injective : Function.Injective (wordBits α) := by
  have hw : 0 < alphabetWidth α := Nat.succ_pos _
  intro u
  induction u with
  | nil =>
    intro v hv
    cases v with
    | nil => rfl
    | cons b v =>
      have hlen := congrArg List.length hv
      rw [length_wordBits, length_wordBits] at hlen
      simp only [List.length_nil, Nat.zero_mul, List.length_cons] at hlen
      exact absurd hlen.symm (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos _) hw))
  | cons a u ih =>
    intro v hv
    cases v with
    | nil =>
      have hlen := congrArg List.length hv
      rw [length_wordBits, length_wordBits] at hlen
      simp only [List.length_nil, Nat.zero_mul, List.length_cons] at hlen
      exact absurd hlen (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos _) hw))
    | cons b v =>
      have hblock : (alphabetCode α a).length = (alphabetCode α b).length := by
        rw [length_alphabetCode, length_alphabetCode]
      have hsplit : alphabetCode α a ++ wordBits α u = alphabetCode α b ++ wordBits α v := hv
      obtain ⟨hab, huv⟩ := List.append_inj hsplit hblock
      rw [alphabetCode_isPrefixFree.injective hab, ih huv]

end Kolmogorov
