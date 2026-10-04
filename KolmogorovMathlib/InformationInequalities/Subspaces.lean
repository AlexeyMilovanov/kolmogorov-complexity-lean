/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The subspace form of an information inequality

SUV Section 10.11, pp. 339–340.

Theorem 216: every inequality that is true for the entropies of random variables and their
tuples is also true for the dimensions of finite-dimensional subspaces of a vector space over
a finite field, when the entropy of a tuple is replaced by the dimension of the sum of the
corresponding subspaces (p. 340).  The dictionary behind it: for a subspace `Y` of a
finite-dimensional space `X` over a finite field `F`, the restriction to `Y` of a uniformly
random linear functional on `X` is a random variable with entropy `dim Y · log |F|`, and the
pair of the restrictions to `Y` and to `Z` determines and is determined by the restriction to
`Y + Z` (p. 339).

So the entropy `H(ξ_I)` corresponds to `dim (∑_{i ∈ I} V_i)`, which is `subspaceSum`.  The
convention `H(ξ_∅) = 0` comes out right: the sum over no indices is the zero subspace.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-- The subspace `∑_{i ∈ I} V_i` of the dimension dictionary.  For `I = ∅` this is the zero
subspace, of dimension zero.  SUV Section 10.11, p. 340. -/
def subspaceSum {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (W : Fin n → Submodule F V) (I : Finset (Fin n)) : Submodule F V :=
  ⨆ i ∈ I, W i

/-- The sum over no indices is the zero subspace. -/
@[simp] theorem subspaceSum_empty {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (W : Fin n → Submodule F V) : subspaceSum W ∅ = ⊥ := by
  simp [subspaceSum]

/-- The value of a linear form in the dimension dictionary:
`∑_{I ≠ ∅} λ_I · dim (∑_{i ∈ I} V_i)`.  SUV Section 10.11, p. 340. -/
noncomputable def LinearForm.evalDim (f : LinearForm n) {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (W : Fin n → Submodule F V) : ℝ :=
  ∑ I ∈ nonemptyParts n, f I * (Module.finrank F (subspaceSum W I) : ℝ)

/-- The form holds for subspaces: `∑_{I ≠ ∅} λ_I · dim (∑_{i ∈ I} V_i) ≤ 0` for every finite
field, every vector space over it and all *finite-dimensional* subspaces `V_1, …, V_n`.  The
book's Theorem 216 restricts the subspaces, not the ambient space: finite-dimensionality of
each `V_i` is what makes every `subspaceSum W I` finitely generated and hence `finrank` the
honest dimension, while the ambient space is arbitrary.  Theorem 216 states that
`HoldsForEntropies f` implies this.  The field and the space range over `Type`, i.e. over
universe `0`: every object of the book's statements is finite-dimensional over a finite field,
so nothing is lost, and the chapter statements are written with `Type` throughout.
SUV Section 10.11, p. 340. -/
def HoldsForSubspaces (f : LinearForm n) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    (W : Fin n → Submodule F V) [∀ i, Module.Finite F (W i)], f.evalDim W ≤ 0

end Kolmogorov
