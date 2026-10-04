/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The group form of an information inequality

SUV Section 10.4, p. 324.

The dictionary of Theorem 209 (Chan and Yeung) sends a tuple of random variables to a finite
group `G` with subgroups `G_1, …, G_n`, replacing the entropy `H(ξ_I)` by
`log₂ (|G| / |G_I|)`, where `G_I` is the intersection of the `G_i` with `i ∈ I`.  The book
prints the dictionary on p. 323: for the orbit `U` of a point under an action of `G` on
`X_1 × ⋯ × X_n`, the size of the projection of `U` on the indices `{i₁, i₂, …}` is the ratio
`|G| / |S_{i₁} ∩ S_{i₂} ∩ ⋯|`, where `S_j` is the stabiliser of the `j`-th coordinate; and
every subgroup of `G` is such a stabiliser.  The two examples on p. 324 use it:
`m(1,2) ≤ m(1) · m(2)` becomes `|G| / |H₁ ∩ H₂| ≤ (|G| / |H₁|) · (|G| / |H₂|)`, and
`m(1,2,3)² ≤ m(1,2) m(1,3) m(2,3)` becomes
`|H₁ ∩ H₂ ∩ H₃|² ≥ |H₁ ∩ H₂| · |H₁ ∩ H₃| · |H₂ ∩ H₃| / |G|`.

The convention `m(∅) = 1` comes out right: `subgroupMeet H ∅ = ⊤`, so the empty set
contributes `log₂ (|G| / |G|) = 0`.

The printed statement of Theorem 209 says "linear equality"; that is a misprint for "linear
inequality", as the examples on the same page show.  The equivalence that the theorem asserts
is a statement of the chapter skeleton: `HoldsForEntropies f ↔ HoldsForGroups f`.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-- The subgroup `G_I = ⋂_{i ∈ I} G_i` of the group dictionary.  For `I = ∅` this is the whole
group.  SUV Section 10.4, p. 323. -/
def subgroupMeet {G : Type*} [Group G] (H : Fin n → Subgroup G) (I : Finset (Fin n)) :
    Subgroup G :=
  ⨅ i ∈ I, H i

/-- The intersection over no indices is the whole group, so `|G| / |G_∅| = 1`. -/
@[simp] theorem subgroupMeet_empty {G : Type*} [Group G] (H : Fin n → Subgroup G) :
    subgroupMeet H ∅ = ⊤ := by
  simp [subgroupMeet]

/-- The value of a linear form in the group dictionary printed on p. 323:
`∑_{I ≠ ∅} λ_I · log₂ (|G| / |G_I|)`.  SUV Section 10.4, pp. 323–324. -/
noncomputable def LinearForm.evalGroupIndex (f : LinearForm n) {G : Type*} [Group G]
    (H : Fin n → Subgroup G) : ℝ :=
  ∑ I ∈ nonemptyParts n,
    f I * Real.logb 2 ((Nat.card G : ℝ) / (Nat.card (subgroupMeet H I) : ℝ))

/-- The form holds for groups: `∑_{I ≠ ∅} λ_I · log₂ (|G| / |G_I|) ≤ 0` for every finite group
`G` and all subgroups `G_1, …, G_n`.  Theorem 209 states that this is equivalent to
`HoldsForEntropies f`.  The group ranges over `Type`, i.e. over universe `0`: every object of
the book's statements is finite, so nothing is lost, and the chapter statements are written
with `Type` throughout.  SUV Section 10.4, p. 324. -/
def HoldsForGroups (f : LinearForm n) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Fin n → Subgroup G), f.evalGroupIndex H ≤ 0

end Kolmogorov
