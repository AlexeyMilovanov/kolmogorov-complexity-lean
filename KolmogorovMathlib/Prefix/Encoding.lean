/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Basic
import Mathlib.Data.List.Basic

/-!
# A Concrete Self-Delimiting Code on `BitString`

This module provides a concrete, prefix-free encoding of the natural numbers as
bitstrings. We use the elementary **unary** self-delimiting code: the number `n`
is encoded as `n` copies of `true` followed by a single `false`, i.e. `1ⁿ0`.

The point of this code is structural: it is *prefix-free as a set*
(`isPrefixFree_range_natCode`), it is *injective* (`natCode_injective`), and it
is *uniquely decodable as a leading block* (`natCode_append_inj`). These three
facts are exactly what a later "machine mixture" construction needs in order to
glue a family of prefix machines into a single prefix machine: prepend `natCode i`
to address machine `i`, and the prefix-freeness of the codes plus the
prefix-freeness of each machine's domain combine into prefix-freeness of the
union.

This file is deliberately pure list combinatorics: it mentions no machines, no
complexity measures, no semimeasures, no real numbers, and no logarithms. The
length bookkeeping (`length_natCode`) records that the code of `n` has length
`n + 1`, the only quantitative fact downstream weight calculations require.
-/

namespace Kolmogorov

/-- The unary self-delimiting code of `n`: `n` copies of `true` then one `false`
(written `1ⁿ0`). This is the simplest prefix-free encoding of `ℕ` into
`BitString`. -/
def natCode (n : ℕ) : BitString := List.replicate n true ++ [false]

/-- The unary code of `n` has length `n + 1`. -/
@[simp] theorem length_natCode (n : ℕ) : (natCode n).length = n + 1 := by
  simp [natCode]

/-- The unary code is injective: the length already determines the number. -/
theorem natCode_injective : Function.Injective natCode := by
  intro m n h
  have hlen := congrArg List.length h
  rw [length_natCode, length_natCode] at hlen
  omega

/-- One unary code is a prefix of another exactly when they are equal. This is
the heart of the prefix-freeness argument: a shorter code `1ᵐ0` cannot sit at the
front of a longer code `1ⁿ0`, because the trailing `0` of the shorter code lands
on a `1` of the longer one. -/
theorem natCode_prefix_iff {m n : ℕ} : natCode m <+: natCode n ↔ m = n := by
  constructor
  · intro h
    have hle : m ≤ n := by
      have hlen := h.length_le
      rw [length_natCode, length_natCode] at hlen
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    suffices hk : k = 0 by omega
    by_contra hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp only [natCode, List.replicate_add, List.append_assoc,
      List.prefix_append_right_inj] at h
    -- `h : [false] <+: replicate (j + 1) true ++ [false]`
    obtain ⟨t, ht⟩ := h
    rw [List.replicate_succ] at ht
    simp at ht
  · rintro rfl
    exact List.prefix_refl _

/-- The set of all unary codes is prefix-free. This is the property a machine
mixture relies on to keep its glued domain prefix-free. -/
theorem isPrefixFree_range_natCode : IsPrefixFree (Set.range natCode) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hpre
  rw [natCode_prefix_iff] at hpre
  rw [hpre]

/-- Unique decodability of the unary code as a leading block: if two strings of
the form `natCode m ++ a` and `natCode n ++ b` are equal, then both the codes and
the suffixes agree. This is the lemma a future combine/mixture construction
consumes to split an input program into "which machine" and "argument". -/
theorem natCode_append_inj {m n : ℕ} {a b : BitString}
    (h : natCode m ++ a = natCode n ++ b) : m = n ∧ a = b := by
  have hpm : natCode m <+: natCode n ++ b := ⟨a, h⟩
  have hpn : natCode n <+: natCode n ++ b := List.prefix_append _ _
  have hmn : m = n := by
    rcases List.prefix_or_prefix_of_prefix hpm hpn with hc | hc
    · exact natCode_prefix_iff.mp hc
    · exact (natCode_prefix_iff.mp hc).symm
  subst hmn
  exact ⟨rfl, List.append_cancel_left h⟩

end Kolmogorov
