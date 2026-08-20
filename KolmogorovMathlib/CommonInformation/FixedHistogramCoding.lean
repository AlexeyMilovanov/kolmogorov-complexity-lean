import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.CommonInformation.FixedHistogram
import Mathlib.Tactic.FinCases

/-!
# Fixed-histogram pairs of bit strings and their incompressibility

Exercise 316 of SUV concerns a *pair* `(x, y)` of bit strings with prescribed
joint letter frequencies.  Such a pair is the same thing as a single word over
the four-letter alphabet `Fin 4`: the letter at position `t` records the pair
`(x t, y t)`.  This module makes that dictionary explicit and transports the
counting (lower) half of the fixed-frequency bridge from
`KolmogorovMathlib.CommonInformation.FixedFrequency` to the four-letter case.

* `wordFirst` / `wordSecond` split a four-letter word into its two bit-string
  components, and `word_eq_of_components` shows the pair determines the word;
* `count_true_wordFirst` / `count_true_wordSecond` identify the *marginal*
  frequencies of the two components in terms of the joint histogram;
* `fourWordPairCode` codes the pair as a single bit string, injectively;
* `exists_fixedHistogram_condK_gt` and `exists_fixedHistogram_plainK_gt` are
  the multinomial versions of `exists_fixedWeight_condK_gt` and
  `exists_fixedWeight_plainK_gt`: whenever the multinomial coefficient of the
  histogram `f` exceeds `2 ^ (m + 1)`, some pair with exactly that joint
  histogram has complexity greater than `m`.
-/

namespace Kolmogorov

open Finset

/-! ### Four-letter words as pairs of bit strings -/

/-- The first component bit of a four-letter alphabet symbol. -/
def letterFirst (i : Fin 4) : Bool := decide (2 ≤ i.val)

/-- The second component bit of a four-letter alphabet symbol. -/
def letterSecond (i : Fin 4) : Bool := decide (i.val % 2 = 1)

/-- A four-letter symbol is determined by its two component bits. -/
theorem letter_eq_of_bits {i j : Fin 4} (h1 : letterFirst i = letterFirst j)
    (h2 : letterSecond i = letterSecond j) : i = j := by
  revert h1 h2; revert i j; decide

/-- The first bit-string component of a four-letter word. -/
def wordFirst (w : List (Fin 4)) : BitString := w.map letterFirst

/-- The second bit-string component of a four-letter word. -/
def wordSecond (w : List (Fin 4)) : BitString := w.map letterSecond

@[simp]
theorem length_wordFirst (w : List (Fin 4)) : (wordFirst w).length = w.length := by
  simp [wordFirst]

@[simp]
theorem length_wordSecond (w : List (Fin 4)) : (wordSecond w).length = w.length := by
  simp [wordSecond]

/-- A four-letter word is determined by its two bit-string components. -/
theorem word_eq_of_components : ∀ (w w' : List (Fin 4)), wordFirst w = wordFirst w' →
    wordSecond w = wordSecond w' → w = w' := by
  intro w
  induction w with
  | nil =>
    intro w' h1 _
    cases w' with
    | nil => rfl
    | cons b w' => simp [wordFirst] at h1
  | cons a w ih =>
    intro w' h1 h2
    cases w' with
    | nil => simp [wordFirst] at h1
    | cons b w' =>
      simp only [wordFirst, wordSecond, List.map_cons, List.cons.injEq] at h1 h2
      have hab : a = b := letter_eq_of_bits h1.1 h2.1
      subst hab
      rw [ih w' h1.2 h2.2]

/-- The weight of the first component is the corresponding marginal of the
joint histogram. -/
theorem count_true_wordFirst (w : List (Fin 4)) :
    (wordFirst w).count true = w.count 2 + w.count 3 := by
  induction w with
  | nil => simp [wordFirst]
  | cons a w ih =>
    rw [wordFirst, List.map_cons] at *
    fin_cases a <;> simp [letterFirst] at ih ⊢ <;> omega

/-- The weight of the second component is the corresponding marginal of the
joint histogram. -/
theorem count_true_wordSecond (w : List (Fin 4)) :
    (wordSecond w).count true = w.count 1 + w.count 3 := by
  induction w with
  | nil => simp [wordSecond]
  | cons a w ih =>
    rw [wordSecond, List.map_cons] at *
    fin_cases a <;> simp [letterSecond] at ih ⊢ <;> omega

/-- A four-letter word coded as a single bit string: the pair code of its two
components. -/
def fourWordPairCode (w : List (Fin 4)) : BitString :=
  pairCode (wordFirst w) (wordSecond w)

theorem fourWordPairCode_injective : Function.Injective fourWordPairCode := by
  intro w w' h
  refine word_eq_of_components w w' ?_ ?_
  · have hd := congrArg decodeFirst h
    rwa [fourWordPairCode, fourWordPairCode, decodeFirst_pairCode, decodeFirst_pairCode] at hd
  · have hd := congrArg decodeSecond h
    rwa [fourWordPairCode, fourWordPairCode, decodeSecond_pairCode, decodeSecond_pairCode] at hd

/-! ### Fixed-histogram incompressibility -/

/-- **Fixed-histogram incompressibility (conditional form).**  If the
multinomial coefficient of the joint histogram `f` is at least `2 ^ (m + 1)`,
then some pair of bit strings with exactly that joint histogram has conditional
complexity greater than `m`.  This is the multinomial generalization of
`exists_fixedWeight_condK_gt`. -/
theorem exists_fixedHistogram_condK_gt (D : Map) (y : BitString) (f : Fin 4 → ℕ) (m : ℕ)
    (hcard : 2 ^ (m + 1) ≤ Nat.multinomial univ f) :
    ∃ w : List (Fin 4), (∀ i, w.count i = f i) ∧
      (m : ENat) < condK D (fourWordPairCode w) y := by
  have hnodup : ((fixedHistogramWords f).map fourWordPairCode).Nodup :=
    (fixedHistogramWords_nodup f).map fourWordPairCode_injective
  have hcardS : (((fixedHistogramWords f).map fourWordPairCode).toFinset).card =
      Nat.multinomial univ f := by
    rw [List.toFinset_card_of_nodup hnodup, List.length_map, length_fixedHistogramWords]
  obtain ⟨s, hs, hK⟩ :=
    exists_mem_condK_gt_of_card_le D y m
      ((fixedHistogramWords f).map fourWordPairCode).toFinset (by rw [hcardS]; exact hcard)
  rw [List.mem_toFinset, List.mem_map] at hs
  obtain ⟨w, hw, rfl⟩ := hs
  exact ⟨w, ((mem_fixedHistogramWords f w).mp hw).2, hK⟩

/-- **Fixed-histogram incompressibility (unconditional form).** -/
theorem exists_fixedHistogram_plainK_gt (D : Map) (f : Fin 4 → ℕ) (m : ℕ)
    (hcard : 2 ^ (m + 1) ≤ Nat.multinomial univ f) :
    ∃ w : List (Fin 4), (∀ i, w.count i = f i) ∧
      (m : ENat) < plainK D (fourWordPairCode w) :=
  exists_fixedHistogram_condK_gt D [] f m hcard

end Kolmogorov
