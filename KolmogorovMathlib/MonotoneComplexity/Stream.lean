/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.Cantor

/-!
# Finite-or-infinite streams

This module defines `BitStream`, representing SUV's `E = Σ ∪ Ω`
(the space of finite and infinite binary sequences).

We define a partial order on streams: finite streams are ordered by prefix,
infinite streams by equality, and a finite stream is less than an infinite stream
if it is a prefix of it.

## Conflation guard
Cylinder mass `p(x) = p(x0) + p(x1)` (equality, §3.1) ≠ tree semimeasure
`a(x) ≥ a(x0) + a(x1)` (inequality, Thm 75) ≠ the existing discrete
`aprioriMeasure`. No identification without a proved bridge.
-/

namespace Kolmogorov

/--
`BitStream` represents the set `E = Σ ∪ Ω` from SUV,
consisting of all finite and infinite binary sequences.
-/
inductive BitStream
  | finite   : BitString → BitStream
  | infinite : CantorSeq → BitStream

namespace BitStream

/-- The prefix ordering on `BitStream`. -/
protected def le : BitStream → BitStream → Prop
  | .finite x,   .finite y   => x <+: y
  | .finite x,   .infinite w => IsCantorPrefix x w
  | .infinite w, .infinite s => w = s
  | .infinite _, .finite _   => False

/-- A prefix of a prefix of a sequence is again a prefix of that sequence. -/
lemma IsCantorPrefix.of_prefix {x y : BitString} {w : CantorSeq} (h1 : x <+: y)
    (h2 : IsCantorPrefix y w) : IsCantorPrefix x w := by
  intro i hi
  have hlen : i < y.length := lt_of_lt_of_le hi h1.length_le
  rw [h2 i hlen]
  obtain ⟨l, hl⟩ := h1
  subst hl
  simp [hi]

/-- One finite stream approximates another exactly when the underlying strings are in the prefix
relation. -/
@[simp]
lemma finite_le_finite_iff {x y : BitString} : BitStream.le (.finite x) (.finite y) ↔ x <+: y :=
  Iff.rfl

/-- A finite stream approximates an infinite one exactly when its string is a prefix of the
sequence. -/
@[simp]
lemma finite_le_infinite_iff {x : BitString} {w : CantorSeq} :
    BitStream.le (.finite x) (.infinite w) ↔ IsCantorPrefix x w :=
  Iff.rfl

/-- Infinite streams are comparable only when they are equal. -/
@[simp]
lemma infinite_le_infinite_iff {w s : CantorSeq} :
    BitStream.le (.infinite w) (.infinite s) ↔ w = s :=
  Iff.rfl

/-- An infinite stream never approximates a finite one. -/
@[simp]
lemma not_infinite_le_finite {w : CantorSeq} {x : BitString} :
    ¬ BitStream.le (.infinite w) (.finite x) :=
  fun h => h

instance : PartialOrder BitStream where
  le := BitStream.le
  le_refl := by
    intro s
    cases s <;> simp [BitStream.le]
  le_trans := by
    intro a b c hab hbc
    cases a with
    | finite x =>
      cases b with
      | finite y =>
        cases c with
        | finite z => exact List.IsPrefix.trans hab hbc
        | infinite w => exact IsCantorPrefix.of_prefix hab hbc
      | infinite w =>
        cases c with
        | finite z => exact False.elim hbc
        | infinite s => rwa [← hbc]
    | infinite w =>
      cases b with
      | finite y => exact False.elim hab
      | infinite s =>
        cases c with
        | finite z => exact False.elim hbc
        | infinite v => exact Eq.trans hab hbc
  le_antisymm := by
    intro a b hab hba
    cases a with
    | finite x =>
      cases b with
      | finite y => exact congrArg _ (hab.eq_of_length (le_antisymm hab.length_le hba.length_le))
      | infinite w => exact False.elim hba
    | infinite w =>
      cases b with
      | finite y => exact False.elim hab
      | infinite s => exact congrArg _ hab

/-- Prepends a finite string to a stream. -/
def prepend (x : BitString) : BitStream → BitStream
  | .finite y => .finite (x ++ y)
  | .infinite w => .infinite (prependCantor x w)

/-- Prepending a fixed string is monotone for the approximation order on streams. -/
lemma prepend_mono (x : BitString) {s t : BitStream} (h : s ≤ t) : prepend x s ≤ prepend x t := by
  cases s with
  | finite y1 =>
    cases t with
    | finite y2 =>
      obtain ⟨l, hl⟩ := h
      subst hl
      change x ++ y1 <+: x ++ (y1 ++ l)
      rw [← List.append_assoc]
      exact ⟨l, rfl⟩
    | infinite w =>
      intro i hi
      simp only [List.length_append] at hi
      simp only [prependCantor]
      split_ifs with h_lt
      · rw [List.getElem_append_left]
      · have h_i : i - x.length < y1.length := by omega
        have h_w := h (i - x.length) h_i
        rw [h_w]
        rw [List.getElem_append_right (by omega)]
  | infinite w1 =>
    cases t with
    | finite y2 => exact False.elim h
    | infinite w2 =>
      change w1 = w2 at h
      subst h
      rfl

/-- Prepending the empty string leaves a stream unchanged. -/
@[simp] lemma prepend_nil (s : BitStream) : prepend [] s = s := by
  cases s <;> simp [prepend]

/-- Prepending is associative with respect to string concatenation. -/
lemma prepend_append (x y : BitString) (s : BitStream) :
    prepend x (prepend y s) = prepend (x ++ y) s := by
  cases s <;> simp [prepend, prependCantor_append, List.append_assoc]

/-- A prepended prefix is below the resulting stream. -/
lemma finite_le_prepend (x : BitString) (s : BitStream) :
    BitStream.finite x ≤ prepend x s := by
  cases s with
  | finite y => exact ⟨y, rfl⟩
  | infinite w => exact isCantorPrefix_prepend x w

/-- The empty finite stream is the least element of `BitStream`. -/
@[simp] lemma nil_le (s : BitStream) : BitStream.finite [] ≤ s := by
  cases s with
  | finite y => exact List.nil_prefix
  | infinite w => intro i hi; simp at hi

end BitStream

end Kolmogorov
