/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.Prefix.Encoding
import Mathlib.Data.List.TakeWhile

/-!
# Combining a Family of Prefix Machines into One

This module builds the combinatorial heart of a *universal* prefix machine: a
self-delimiting **tagged union** of a countable family of maps. Given a family
`M : ℕ → Map`, the map `taggedUnion M` reads a unary tag `natCode i` (the
self-delimiting code `1ⁱ0` of `Prefix.Encoding`) off the front of its program and
then runs machine `M i` on the remaining bits.

The key structural fact is `taggedUnion_isPrefixMachine`: if every `M i` is a
prefix machine, then so is `taggedUnion M`. This is exactly the gluing lemma a
universal prefix machine construction needs — the prefix-freeness of the unary
tags (`isPrefixFree_range_natCode`) combines with the prefix-freeness of each
`M i`'s domain to keep the glued domain prefix-free.

We deliberately stay purely combinatorial here. We do **not** claim
`Partrec (taggedUnion M)`, nor do we build an actual universal machine or assert
any coding-theorem equality; those require the `Nat.Partrec.Code` machinery and
belong in a later slot. The conditional prefix complexity bound recorded here,
`taggedUnion_KP_le_of_produces`, is the elementary per-program coding bound: the
tagged program is only `i + 1` bits longer than the original.

No real numbers, no logarithms, and no unproved gaps.
-/

namespace Kolmogorov

open List

/-! ### Length and drop bookkeeping for a tagged program -/

/-- Reading the unary tag back: the leading run of `true`s in `natCode n ++ p`
has length exactly `n` (the trailing `false` of `natCode n` stops the run). -/
@[simp] theorem length_takeWhile_natCode_append (n : ℕ) (p : BitString) :
    ((natCode n ++ p).takeWhile id).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((natCode n ++ p).takeWhile id).length + 1 = n + 1
    omega

/-- Dropping the unary tag: discarding the first `n + 1` bits of `natCode n ++ p`
(the `n` ones plus the terminating `false`) recovers the tail `p`. -/
theorem drop_natCode_append (n : ℕ) (p : BitString) :
    (natCode n ++ p).drop (n + 1) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (natCode n ++ p).drop (n + 1) = p
    exact ih

/-! ### The tagged union of a family of maps -/

/-- The **tagged union** of a family `M : ℕ → Map`. On program `p` in context
`y`, it reads the index `i` as the length of the leading run of `true`s, then runs
`M i` on the bits after the unary tag `1ⁱ0`. The guard `i < p.length` ensures the
tag is actually terminated by a `false`: an all-`true` program (`replicate n true`,
which is `natCode n` without its trailing `0`) never halts. That guard is what
keeps the construction prefix-free. -/
def taggedUnion (M : ℕ → Map) : Map := fun pr =>
  if (pr.1.takeWhile id).length < pr.1.length then
    M ((pr.1.takeWhile id).length) (pr.1.drop ((pr.1.takeWhile id).length + 1), pr.2)
  else Part.none

/-! ### Parsing a halting tagged program -/

/-- If the leading `true`-run of `p` is strictly shorter than `p` (so `p` is not
all-`true`), then `p` splits as the unary tag for that run length followed by the
remaining bits. This is the combinatorial inverse of the unary tagging. -/
theorem eq_natCode_append_drop {p : BitString}
    (hlt : (p.takeWhile id).length < p.length) :
    p = natCode (p.takeWhile id).length ++ p.drop ((p.takeWhile id).length + 1) := by
  set i := (p.takeWhile id).length with hi
  have happ : p.takeWhile id ++ p.dropWhile id = p := takeWhile_append_dropWhile
  -- The leading run is a block of `true`s.
  have htw : p.takeWhile id = List.replicate i true := by
    rw [List.eq_replicate_iff]
    refine ⟨hi.symm, ?_⟩
    intro b hb
    have := List.mem_takeWhile_imp hb
    simpa using this
  -- The remaining bits are nonempty, and their head fails the predicate, i.e. is `false`.
  have hlen : i + (p.dropWhile id).length = p.length := by
    rw [hi, ← List.length_append, happ]
  have hdpos : 0 < (p.dropWhile id).length := by omega
  have hne : p.dropWhile id ≠ [] := List.ne_nil_of_length_pos hdpos
  have hhead : (p.dropWhile id).head hne = false := by
    have := List.head_dropWhile_not id hne
    simpa using this
  have hcons : p.dropWhile id = false :: (p.dropWhile id).tail := by
    conv_lhs => rw [← List.cons_head_tail hne]
    rw [hhead]
  -- Reassemble `p = natCode i ++ tail`.
  have hp_eq : p = natCode i ++ (p.dropWhile id).tail := by
    conv_lhs => rw [← happ, htw, hcons]
    simp [natCode, List.append_assoc]
  -- And the explicit drop recovers that same tail.
  have hdrop : p.drop (i + 1) = (p.dropWhile id).tail := by
    conv_lhs => rw [hp_eq]
    rw [drop_natCode_append]
  rw [hdrop]
  exact hp_eq

/-- If `taggedUnion M` halts on `p` in context `y`, then `p` parses as a unary tag
`natCode i` followed by a tail `q` on which the `i`-th machine `M i` halts. -/
theorem taggedUnion_dom_decompose {M : ℕ → Map} {p y : BitString}
    (h : (taggedUnion M (p, y)).Dom) :
    ∃ i q, p = natCode i ++ q ∧ (M i (q, y)).Dom := by
  by_cases hlt : (p.takeWhile id).length < p.length
  · refine ⟨(p.takeWhile id).length, p.drop ((p.takeWhile id).length + 1),
      eq_natCode_append_drop hlt, ?_⟩
    have heq : taggedUnion M (p, y)
        = M ((p.takeWhile id).length) (p.drop ((p.takeWhile id).length + 1), y) := by
      simp only [taggedUnion]
      rw [if_pos hlt]
    rwa [heq] at h
  · exfalso
    have heq : taggedUnion M (p, y) = Part.none := by
      simp only [taggedUnion]
      rw [if_neg hlt]
    rw [heq] at h
    exact h

/-! ### The tagged union is a prefix machine -/

/-- **Gluing lemma.** If every `M i` is a prefix machine, then the tagged union
`taggedUnion M` is a prefix machine. Two halting tagged programs in a prefix
relation must carry comparable unary tags, hence (by prefix-freeness of the unary
code) the *same* tag `i`; cancelling the common tag reduces the prefix relation to
one between halting programs of `M i`, which prefix-freeness of `M i`'s domain
forces to be equal. -/
theorem taggedUnion_isPrefixMachine {M : ℕ → Map}
    (hM : ∀ i, IsPrefixMachine (M i)) :
    IsPrefixMachine (taggedUnion M) := by
  intro y p hp q hq hpre
  obtain ⟨i, a, hpa, hai⟩ := taggedUnion_dom_decompose hp
  obtain ⟨j, b, hqb, hbj⟩ := taggedUnion_dom_decompose hq
  subst hpa
  subst hqb
  -- The two unary tags are both prefixes of the longer program, hence comparable,
  -- hence equal by prefix-freeness of the unary code.
  have hi_pre : natCode i <+: natCode j ++ b :=
    (List.prefix_append (natCode i) a).trans hpre
  have hij : i = j := by
    rcases List.prefix_or_prefix_of_prefix hi_pre (List.prefix_append (natCode j) b) with hc | hc
    · exact natCode_prefix_iff.mp hc
    · exact (natCode_prefix_iff.mp hc).symm
  subst hij
  -- Cancel the common tag and apply prefix-freeness of `M i`'s domain.
  have hab : a <+: b := (List.prefix_append_right_inj (natCode i)).mp hpre
  have : a = b := hM i y hai hbj hab
  rw [this]

/-! ### Simulation and the elementary coding bound -/

/-- **Simulation.** Prepending the unary tag `natCode i` makes `taggedUnion M`
reproduce the behaviour of `M i`: whatever `M i` produces from `q`, the tagged
program `natCode i ++ q` produces under `taggedUnion M`. -/
theorem taggedUnion_produces_natCode {M : ℕ → Map} {i : ℕ} {q y x : BitString}
    (h : produces (M i) q y x) :
    produces (taggedUnion M) (natCode i ++ q) y x := by
  have hlt : i < (natCode i ++ q).length := by
    simp only [List.length_append, length_natCode]; omega
  have heq : taggedUnion M (natCode i ++ q, y) = M i (q, y) := by
    simp only [taggedUnion, length_takeWhile_natCode_append, drop_natCode_append]
    rw [if_pos hlt]
  change x ∈ taggedUnion M (natCode i ++ q, y)
  rw [heq]
  exact h

/-- **Elementary coding bound.** A program `q` of `M i` producing `x` from `y`
yields, after tagging, a `taggedUnion M`-program of length `i + 1 + q.length`,
bounding the conditional prefix complexity in the tagged union. This is the only
quantitative consequence we record; it carries no logarithms and no exact coding
equality. -/
theorem taggedUnion_KP_le_of_produces {M : ℕ → Map} {i : ℕ} {q x y : BitString}
    (h : produces (M i) q y x) :
    KP (taggedUnion M) x y ≤ ((i + 1 + q.length : ℕ) : ENat) := by
  have hle := KP_le_programLength_of_produces (taggedUnion_produces_natCode (M := M) h)
  have hlen : programLength (natCode i ++ q) = i + 1 + q.length := by
    simp [programLength, List.length_append, length_natCode]
  rwa [hlen] at hle

end Kolmogorov
