/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Core.Basic
import Mathlib.Data.List.Infix

/-!
# Prefix-Free Sets of BitStrings

This module establishes the elementary combinatorics of *prefix-free* sets of
bitstrings. A set `S` of bitstrings is prefix-free when no element of `S` is a
prefix of a distinct element of `S`. Such sets are the domains of prefix
machines, and they are the foundation on which prefix Kolmogorov complexity and
a priori semimeasures are later built.

We reuse Mathlib's `List.IsPrefix` relation (notation `<+:`) on
`BitString = List Bool`, rather than reinventing a prefix predicate. Only the
set-level `IsPrefixFree` notion and its basic closure properties are new here.

This file deliberately contains *only* combinatorics: no machines, no
complexity measures, and no measures or semimeasures. Those are developed in
later modules that import this one.
-/

namespace Kolmogorov

/-- A set of bitstrings `S` is **prefix-free** when, whenever one element of `S`
is a prefix of another element of `S`, the two elements are in fact equal.
Equivalently, no element of `S` is a *proper* prefix of another element. -/
def IsPrefixFree (S : Set BitString) : Prop :=
  ∀ ⦃p : BitString⦄, p ∈ S → ∀ ⦃q : BitString⦄, q ∈ S → p <+: q → p = q

/-- A bitstring `p` is a **strict prefix** of `q` when it is a prefix of `q` and
the two are distinct. This is the relation that prefix-free sets forbid between
distinct elements. -/
def IsStrictPrefix (p q : BitString) : Prop :=
  p <+: q ∧ p ≠ q

/-! ### Basic facts about strict prefixes -/

/-- A strict prefix is strictly shorter. -/
theorem IsStrictPrefix.length_lt {p q : BitString} (h : IsStrictPrefix p q) :
    p.length < q.length := by
  rcases h with ⟨hpre, hne⟩
  rcases lt_or_eq_of_le hpre.length_le with hlt | heq
  · exact hlt
  · exact absurd (hpre.eq_of_length heq) hne

/-- No bitstring is a strict prefix of itself. -/
theorem not_isStrictPrefix_self (p : BitString) : ¬ IsStrictPrefix p p :=
  fun h => h.2 rfl

/-! ### Basic facts about prefix-free sets -/

/-- The empty set is prefix-free (vacuously). -/
theorem isPrefixFree_empty : IsPrefixFree (∅ : Set BitString) := by
  intro p hp
  exact absurd hp (Set.notMem_empty p)

/-- Every singleton set is prefix-free. -/
theorem isPrefixFree_singleton (p : BitString) : IsPrefixFree {p} := by
  intro a ha b hb _
  rw [Set.mem_singleton_iff] at ha hb
  rw [ha, hb]

/-- A subset of a prefix-free set is prefix-free. This closure property is used
pervasively: any sub-collection of a prefix code is again a prefix code. -/
theorem IsPrefixFree.mono {S T : Set BitString} (hS : IsPrefixFree S)
    (hTS : T ⊆ S) : IsPrefixFree T :=
  fun _ hp _ hq hpre => hS (hTS hp) (hTS hq) hpre

/-- A prefix-free set contains no strict-prefix pair: if `p` and `q` are both in
`S`, then `p` is not a strict prefix of `q`. -/
theorem IsPrefixFree.not_isStrictPrefix {S : Set BitString} (hS : IsPrefixFree S)
    {p q : BitString} (hp : p ∈ S) (hq : q ∈ S) : ¬ IsStrictPrefix p q :=
  fun h => h.2 (hS hp hq h.1)

/-- Characterisation of prefix-freeness via strict prefixes: `S` is prefix-free
iff no element of `S` is a strict prefix of another element of `S`. -/
theorem isPrefixFree_iff_forall_not_isStrictPrefix (S : Set BitString) :
    IsPrefixFree S ↔
      ∀ ⦃p : BitString⦄, p ∈ S → ∀ ⦃q : BitString⦄, q ∈ S → ¬ IsStrictPrefix p q := by
  constructor
  · intro hS p hp q hq
    exact hS.not_isStrictPrefix hp hq
  · intro h p hp q hq hpre
    by_contra hne
    exact h hp hq ⟨hpre, hne⟩

end Kolmogorov
