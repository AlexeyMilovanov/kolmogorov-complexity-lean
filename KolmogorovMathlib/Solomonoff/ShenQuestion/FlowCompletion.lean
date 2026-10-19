/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.ShenQuestion.Sanitize

/-!
# A2. Finite exact flow completion

Given a finite ℕ-valued *snapshot* `A : BitString → ℕ` on the cone of a node (indexed by
the suffix `w`), coherent (`A (w0) + A (w1) ≤ A w`) and with root budget `q0 ≥ A []`, we
complete it to an **exact flow** `flowVal A q0`:

* `flowVal A q0 [] = q0`,
* `flowVal A q0 (w ++ [false]) + flowVal A q0 (w ++ [true]) = flowVal A q0 w` (exact split),
* `A w ≤ flowVal A q0 w` (domination),
* the level sums are constant: `∑_{|w| = d} flowVal A q0 w = q0`.

The completion is the deterministic "give the remainder to the `0`-child" rule of
blueprint A2.2:

  `P(w1) := A(w1)`,   `P(w0) := P(w) − A(w1)`.

It is defined by structural recursion on the *reversed* suffix, hence genuinely
computable (no `Classical.choice`, no well-founded recursion).
-/

namespace Kolmogorov
namespace Shen

/-- All bit strings of a given length (in a fixed computable order). -/
def binStrings : ℕ → List BitString
  | 0 => [[]]
  | d + 1 => (binStrings d).flatMap (fun w => [w ++ [false], w ++ [true]])

/-- All bit strings of length `≤ d`. -/
def binStringsUpTo (d : ℕ) : List BitString :=
  (List.range (d + 1)).flatMap binStrings

/-- Every element of `binStrings d` has length `d`.  Difficulty **E**. -/
theorem length_of_mem_binStrings : ∀ (d : ℕ) (w : BitString), w ∈ binStrings d → w.length = d := by
  intro d
  induction d with
  | zero => intro w hw; simp [binStrings] at hw; simp [hw]
  | succ d ih =>
      intro w hw
      simp only [binStrings, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hw
      obtain ⟨v, hv, hw⟩ := hw
      rcases hw with rfl | rfl <;> simp [ih v hv]

/-- Membership in `binStrings`: every string of length `d` occurs.  Difficulty **E**,
~15 lines (induction on `d`, splitting `w` at its last bit). -/
theorem mem_binStrings (w : BitString) : w ∈ binStrings w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [binStrings]
  | append_singleton v b ih =>
      have hlen : (v ++ [b]).length = v.length + 1 := by simp
      rw [hlen]
      simp only [binStrings, List.mem_flatMap]
      exact ⟨v, ih, by cases b <;> simp⟩

/-- The flow value, as a function of the *reversed* suffix.  Structural recursion. -/
def flowValR (A : BitString → ℕ) (q0 : ℕ) : BitString → ℕ
  | [] => q0
  | true :: r => A (r.reverse ++ [true])
  | false :: r => flowValR A q0 r - A (r.reverse ++ [true])

/-- **A2.1/A2.2.** The exact flow completing the snapshot `A` with root mass `q0`. -/
def flowVal (A : BitString → ℕ) (q0 : ℕ) (w : BitString) : ℕ := flowValR A q0 w.reverse

/-- The flow value at the root is the root value `q0`. -/
@[simp] theorem flowVal_nil (A : BitString → ℕ) (q0 : ℕ) : flowVal A q0 [] = q0 := rfl

/-- At a `1`-child the flow takes the value of the snapshot. -/
@[simp] theorem flowVal_true (A : BitString → ℕ) (q0 : ℕ) (w : BitString) :
    flowVal A q0 (w ++ [true]) = A (w ++ [true]) := by
  simp [flowVal, flowValR]

/-- At a `0`-child the flow takes the remainder of the parent after the `1`-child. -/
@[simp] theorem flowVal_false (A : BitString → ℕ) (q0 : ℕ) (w : BitString) :
    flowVal A q0 (w ++ [false]) = flowVal A q0 w - A (w ++ [true]) := by
  simp [flowVal, flowValR]

section
variable {A : BitString → ℕ} {q0 : ℕ}

/-- **A2.2 (domination).** The completion dominates the snapshot.

Proof sketch: induction on `|w|` (peeling the last bit).  At `[]`: `A [] ≤ q0` is `hroot`.
Step: `A (w ++ [true]) = flowVal .. ` by `flowVal_true`; and
`A (w ++ [false]) ≤ flowVal A q0 w − A (w ++ [true])` follows from the induction hypothesis
`A w ≤ flowVal A q0 w` together with `hcoh w : A (w0) + A (w1) ≤ A w` and ℕ-subtraction
(`Nat.le_sub_of_add_le`).  Difficulty **M**, ~40 lines. -/
theorem flowVal_ge (hcoh : ∀ w, A (w ++ [false]) + A (w ++ [true]) ≤ A w)
    (hroot : A [] ≤ q0) (w : BitString) : A w ≤ flowVal A q0 w := by
  induction w using List.reverseRecOn with
  | nil => simpa using hroot
  | append_singleton v b ih =>
      cases b
      · have h1 : A (v ++ [false]) + A (v ++ [true]) ≤ flowVal A q0 v :=
          le_trans (hcoh v) ih
        rw [flowVal_false]
        exact Nat.le_sub_of_add_le h1
      · rw [flowVal_true]

/-- **A2.2 (exact split).**  Difficulty **M**, ~25 lines: unfold both children and use
`Nat.sub_add_cancel` with `A (w ++ [true]) ≤ flowVal A q0 w`, which follows from
`flowVal_ge` and `hcoh`. -/
theorem flowVal_split (hcoh : ∀ w, A (w ++ [false]) + A (w ++ [true]) ≤ A w)
    (hroot : A [] ≤ q0) (w : BitString) :
    flowVal A q0 (w ++ [false]) + flowVal A q0 (w ++ [true]) = flowVal A q0 w := by
  have hA : A (w ++ [true]) ≤ flowVal A q0 w :=
    le_trans (le_trans le_add_self (hcoh w)) (flowVal_ge hcoh hroot w)
  rw [flowVal_false, flowVal_true, Nat.sub_add_cancel hA]

/-- **A2.3 (leaf sum).** Every level of the completed flow carries exactly the mass `q0`.

Proof sketch: induction on `d`; `binStrings (d+1)` is `binStrings d` expanded by the two
children, so `List.sum_flatMap` plus `flowVal_split` telescopes.  Difficulty **M**,
~40 lines. -/
theorem flowVal_level_sum (hcoh : ∀ w, A (w ++ [false]) + A (w ++ [true]) ≤ A w)
    (hroot : A [] ≤ q0) (d : ℕ) :
    ((binStrings d).map (flowVal A q0)).sum = q0 := by
  have key : ∀ l : List BitString,
      ((l.flatMap (fun w => [w ++ [false], w ++ [true]])).map (flowVal A q0)).sum
        = (l.map (flowVal A q0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a t iht =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero, iht]
        rw [flowVal_split hcoh hroot a]
  induction d with
  | zero => simp [binStrings]
  | succ d ih =>
      rw [show binStrings (d + 1)
            = (binStrings d).flatMap (fun w => [w ++ [false], w ++ [true]]) from rfl,
        key, ih]

/-- Beyond the snapshot's support the flow only splits; in particular the flow value is
`0` exactly where the whole subtree is unused.  Difficulty **E**, ~10 lines
(`flowVal_split` and `Nat.le_of_add_le_left`). -/
theorem flowVal_child_le (hcoh : ∀ w, A (w ++ [false]) + A (w ++ [true]) ≤ A w)
    (hroot : A [] ≤ q0) (w : BitString) (b : Bool) :
    flowVal A q0 (w ++ [b]) ≤ flowVal A q0 w := by
  cases b
  · exact le_trans le_self_add (le_of_eq (flowVal_split hcoh hroot w))
  · exact le_trans le_add_self (le_of_eq (flowVal_split hcoh hroot w))

end

end Shen
end Kolmogorov
