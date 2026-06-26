/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Prefix.Basic

/-!
# Prefix Machines and Conditional Prefix Complexity

This module introduces *prefix machines*: maps whose halting set, in every
context `y`, is a prefix-free set of programs (see `KolmogorovMathlib.Prefix.Basic`).
Prefix-freeness of the domain is precisely the structural condition that makes
the Kraft inequality and a priori semimeasures available later.

We deliberately keep prefix-freeness *separate* from computability: a
`Map` may or may not be a decompressor (`isDecompressor`), and that property is
orthogonal to whether its domain is prefix-free. Bundling computability in here
would force a `Partrec` obligation on every toy example, so we resist it.

The conditional prefix complexity `KP` is defined to be *definitionally equal*
to the ordinary conditional complexity `condK`; the prefix content of the theory
lives in the `IsPrefixMachine` hypotheses carried by the lemmas, not in the
infimum itself. This `rfl`-bridge lets every existing `condK` fact transfer for
free.

This file contains only definitions and elementary structural lemmas: no
measures, no Kraft inequality, no coding theorem.
-/

namespace Kolmogorov

/-! ### The halting domain in a context -/

/-- The **domain** of a map `M` in context `y`: the set of programs `p` for which
the computation `M (p, y)` halts. This is the natural object on which
prefix-freeness is imposed. -/
def domainAt (M : Map) (y : BitString) : Set BitString :=
  {p | (M (p, y)).Dom}

/-- If `M` produces some output from `p` in context `y`, then `p` lies in the
domain of `M` at `y`. -/
theorem produces_mem_domainAt {M : Map} {p y x : BitString}
    (h : produces M p y x) : p ∈ domainAt M y :=
  Part.dom_iff_mem.mpr ⟨x, h⟩

/-! ### Prefix machines -/

/-- A map `M` is a **prefix machine** when, in every context `y`, its halting
domain is prefix-free. Equivalently, no halting program is a strict prefix of
another halting program in the same context. -/
def IsPrefixMachine (M : Map) : Prop :=
  ∀ y, IsPrefixFree (domainAt M y)

/-- The defining property of a prefix machine, unfolded: two halting programs in
the same context that are in a prefix relation must be equal. This is the only
bridge from `produces` to the prefix-free combinatorics of `Prefix.Basic`. -/
theorem IsPrefixMachine.eq_of_prefix {M : Map} (hM : IsPrefixMachine M)
    {p q y a b : BitString} (hp : produces M p y a) (hq : produces M q y b)
    (hpre : p <+: q) : p = q :=
  hM y (produces_mem_domainAt hp) (produces_mem_domainAt hq) hpre

/-! ### Conditional prefix complexity -/

/-- **Conditional prefix complexity** `KP M x y`. It is defined to coincide with
`condK M x y`; what makes it "prefix" complexity is that the intended maps `M`
satisfy `IsPrefixMachine`. Keeping it definitionally equal to `condK` means the
entire `condK` API applies verbatim. -/
noncomputable def KP (M : Map) (x y : BitString) : ENat :=
  condK M x y

/-- `KP` is, by definition, the ordinary conditional complexity. This `rfl`
bridge transfers every `condK` lemma to `KP`. -/
theorem KP_eq_condK (M : Map) (x y : BitString) : KP M x y = condK M x y :=
  rfl

/-- The easy "coding" direction: any program that produces `x` from `y` bounds
the conditional prefix complexity by its length. -/
theorem KP_le_programLength_of_produces {M : Map} {p x y : BitString}
    (h : produces M p y x) : KP M x y ≤ (programLength p : ENat) := by
  rw [KP_eq_condK]
  exact sInf_le ⟨p, h, rfl⟩

/-- If no program produces `x` from `y`, the conditional prefix complexity is
`⊤`. The converse also holds since `sInf ∅ = ⊤`. -/
theorem KP_eq_top_of_no_program {M : Map} {x y : BitString}
    (h : ∀ p, ¬ produces M p y x) : KP M x y = ⊤ := by
  rw [KP_eq_condK, condK]
  have hempty : candidateLengths M x y = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro n ⟨p, hp, _⟩
    exact h p hp
  rw [hempty, sInf_empty]

/-! ### The witness behind a finite `KP`

When `KP M x y` is finite, the infimum defining it is actually *achieved*:
because `ENat` is well-ordered, a nonempty set of program lengths contains its
own infimum. These lemmas package that fact into a reusable witness API so that
downstream files need not repeat the `candidateLengths` / `csInf_mem` unfolding. -/

/-- If `KP M x y` is finite, the infimum defining it is achieved: the value
`KP M x y` itself is the length of an actual producing program. -/
theorem KP_mem_candidateLengths_of_ne_top {M : Map} {x y : BitString}
    (h : KP M x y ≠ ⊤) : KP M x y ∈ candidateLengths M x y := by
  rcases Set.eq_empty_or_nonempty (candidateLengths M x y) with he | hne
  · exact absurd (by rw [KP_eq_condK, condK, he, sInf_empty]) h
  · rw [KP_eq_condK, condK]; exact csInf_mem hne

/-- If `KP M x y` is finite there is a program of length exactly `KP M x y` that
produces `x` from `y`. This is the existence form of the witness lemma. -/
theorem exists_program_of_KP_ne_top {M : Map} {x y : BitString}
    (h : KP M x y ≠ ⊤) :
    ∃ p, produces M p y x ∧ (programLength p : ENat) = KP M x y :=
  KP_mem_candidateLengths_of_ne_top h

/-- `KP M x y` is finite **iff** some program produces `x` from `y`. -/
theorem KP_ne_top_iff_exists_program {M : Map} {x y : BitString} :
    KP M x y ≠ ⊤ ↔ ∃ p, produces M p y x := by
  constructor
  · intro h
    obtain ⟨p, hp, _⟩ := exists_program_of_KP_ne_top h
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩ htop
    have hle := KP_le_programLength_of_produces hp
    rw [htop, top_le_iff] at hle
    exact absurd hle (by simp)

/-- `KP M x y = ⊤` **iff** no program produces `x` from `y`. This packages the
one-way `KP_eq_top_of_no_program` together with the witness API. -/
theorem KP_eq_top_iff_no_program {M : Map} {x y : BitString} :
    KP M x y = ⊤ ↔ ∀ p, ¬ produces M p y x := by
  rw [← not_iff_not, not_forall_not]
  exact KP_ne_top_iff_exists_program

end Kolmogorov
