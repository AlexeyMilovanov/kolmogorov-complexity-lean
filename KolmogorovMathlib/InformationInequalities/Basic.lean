/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Subtuples
import KolmogorovMathlib.Complexity.Tuples.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Linear information inequalities as objects

SUV Chapter 10, Sections 10.1 and 10.11, pp. 313–318 and pp. 337–339.

Chapter 10 compares one and the same family of linear inequalities in five guises: for
entropies of tuples of random variables, for Kolmogorov complexities of tuples of strings,
for log-sizes of projections of uniform sets, for sizes of subgroups of a finite group, and
for dimensions of subspaces.  To state that comparison one needs the inequality itself as an
object, and that object is a `LinearForm n`: a coefficient `λ_I` for every `I ⊆ {1, …, n}`.

Two conventions are fixed here and used by every module of this directory.

* **Sign.**  A form is read as the assertion `∑_I λ_I · (quantity of I) ≤ 0`.  An inequality
  printed in the book as `LHS ≤ RHS` is therefore encoded as `LHS − RHS`.
* **The empty set.**  Every evaluation sums over the *non-empty* `I` only
  (`nonemptyParts`), so the coefficient `λ_∅` is ignored; `evalEntropy_congr` and its kin
  record this.  This matches the book, which indexes the coordinates of its space by the
  `2^n − 1` non-empty subsets (p. 338).

`HoldsForEntropies` quantifies over `ℕ`-valued random variables.  This is no loss: a random
variable with a finite range on a finite space is carried to an `ℕ`-valued one by any
injection of its range into `ℕ`, and entropy only depends on the distribution.  It avoids
quantifying over the alphabet as well as over the space.
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-- The non-empty subsets of `Fin n`: the index set over which every evaluation of a linear
form is taken.  SUV Section 10.11, p. 338. -/
def nonemptyParts (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun I => I.Nonempty

/-- A set of indices is summed over exactly when it is non-empty. -/
@[simp] theorem mem_nonemptyParts {I : Finset (Fin n)} :
    I ∈ nonemptyParts n ↔ I.Nonempty := by
  simp [nonemptyParts]

/-- A linear form in the `2^n` quantities attached to the subsets of `{1, …, n}`: the
coefficients `λ_I` of an information inequality `∑_I λ_I · (quantity of I) ≤ 0`.  This is an
`abbrev` so that the pointwise structure of the function type is available on forms: `f + g`,
`c • f` and the `Module ℝ` structure are the ones the book uses when it takes non-negative
combinations of inequalities.  SUV Section 10.1, p. 314. -/
abbrev LinearForm (n : ℕ) := Finset (Fin n) → ℝ

namespace LinearForm

/-- The form with the listed coefficients: `ofTable t I` is the sum of the entries of `t`
whose set is `I`, and `0` for a set that `t` does not list.  This is how the concrete forms of
Chapter 10 are written down.  A table evaluates at a concrete set by
`simp +decide [ingletonForm, LinearForm.ofTable]` (the `+decide` settles the equalities
between the explicit `Finset`s of the table).  SUV Section 10.1, p. 314. -/
def ofTable (t : List (Finset (Fin n) × ℝ)) : LinearForm n :=
  fun S => ((t.filter fun e => e.1 = S).map Prod.snd).sum

/-! ### Evaluation on entropies -/

/-- The value of a form on the entropies of the subtuples of `X`:
`∑_{I ≠ ∅} λ_I · H(ξ_I)`.  SUV Section 10.1, p. 314. -/
noncomputable def evalEntropy (f : LinearForm n) {Ω : Type*} [Fintype Ω] {α : Type*}
    [DecidableEq α] (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) : ℝ :=
  ∑ I ∈ nonemptyParts n, f I * entropySub μ X I

/-- Only the coefficients at non-empty sets matter for the entropy evaluation. -/
theorem evalEntropy_congr {f g : LinearForm n} {Ω : Type*} [Fintype Ω] {α : Type*}
    [DecidableEq α] (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (h : ∀ I : Finset (Fin n), I.Nonempty → f I = g I) :
    f.evalEntropy μ X = g.evalEntropy μ X :=
  Finset.sum_congr rfl fun I hI => by rw [h I (mem_nonemptyParts.1 hI)]

/-! ### Evaluation on complexities -/

/-- The value of a form on the plain complexities of the subtuples of a tuple of strings:
`∑_{I ≠ ∅} λ_I · C(x_I)`.  The complexities are `ℕ∞`-valued and are cast through `ENat.toNat`;
for an optimal decompressor they are finite (`tuplePlainK_ne_top`), so the cast loses nothing.

Optimality is not optional: `ENat.toNat ⊤ = 0`, so for a decompressor that describes nothing
this reads every complexity as `0`.  Every theorem about `evalComplexity` must carry the
hypothesis `isOptimalConditional D`.  SUV Section 10.1, p. 314. -/
noncomputable def evalComplexity (f : LinearForm n) (D : Map) (x : Fin n → BitString) : ℝ :=
  ∑ I ∈ nonemptyParts n, f I * ((tuplePlainK D x I).toNat : ℝ)

/-- Only the coefficients at non-empty sets matter for the complexity evaluation. -/
theorem evalComplexity_congr {f g : LinearForm n} (D : Map) (x : Fin n → BitString)
    (h : ∀ I : Finset (Fin n), I.Nonempty → f I = g I) :
    f.evalComplexity D x = g.evalComplexity D x :=
  Finset.sum_congr rfl fun I hI => by rw [h I (mem_nonemptyParts.1 hI)]

end LinearForm

/-! ### Validity for entropies -/

/-- The entropy vector of a tuple of random variables: the family `I ↦ H(ξ_I)`, a point of
the set `E` of SUV Section 10.11, p. 338. -/
noncomputable def entropyVector {Ω : Type*} [Fintype Ω] {α : Type*} [DecidableEq α]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) : Finset (Fin n) → ℝ :=
  fun I => entropySub μ X I

/-- The entropy region `E`: the set of entropy vectors of `n`-tuples of random variables.
The outcome space is taken to be `Fin m`, which is no loss of generality and avoids
quantifying over an arbitrary finite type.  SUV Section 10.11, p. 338. -/
def entropyRegion (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {v | ∃ (m : ℕ) (μ : FiniteProbSpace (Fin m)) (X : Fin n → Fin m → ℕ),
      v = entropyVector μ X}

/-- The polyhedral cone cut out by the basic inequalities: `H(ξ_∅) = 0`, `H(ξ_I) ≥ 0`,
`H(ξ_I) ≤ H(ξ_J)` for `I ⊆ J`, and `H(ξ_{I∩J}) + H(ξ_{I∪J}) ≤ H(ξ_I) + H(ξ_J)`.  The entropy
region is contained in it; for `n = 2` the two coincide, for `n = 3` the cone is the closure
of the region, and for `n = 4` it is strictly larger than that closure.
SUV Section 10.11, p. 338. -/
def basicCone (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {v | v ∅ = 0 ∧ (∀ I, 0 ≤ v I) ∧ (∀ I J, I ⊆ J → v I ≤ v J) ∧
    ∀ I J, v (I ∩ J) + v (I ∪ J) ≤ v I + v J}

/-- The form holds for entropies: `∑_{I ≠ ∅} λ_I · H(ξ_I) ≤ 0` for every `n`-tuple of random
variables on every finite probability space.  The outcome space ranges over `Type`, i.e. over
universe `0`: every object of the book's statements is finite, so nothing is lost, and the
chapter statements are written with `Type` throughout.  SUV Section 10.1, p. 314. -/
def HoldsForEntropies (f : LinearForm n) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ),
    f.evalEntropy μ X ≤ 0

/-! ### Validity for complexities -/

/-- The form holds for complexities of strings of bounded length: there is a constant `c`
such that for every `N` and every tuple of strings of length at most `N`, the value of the
form on the complexities is at most `logSlack c N`.  This is the form the inequalities of
SUV Section 10.1 take (`O(log N)` precision for strings of length at most `N`).

For a `D` that is not optimal the predicate is trivially true — all complexities are then `⊤`,
which `evalComplexity` reads as `0` — so every theorem that uses it must assume
`isOptimalConditional D`.  SUV Section 10.1, p. 314. -/
def HoldsForComplexitiesLen (f : LinearForm n) (D : Map) : Prop :=
  ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), tupleMaxLength x ≤ N →
    f.evalComplexity D x ≤ (logSlack c N : ℝ)

/-- The form holds for complexities of strings of bounded complexity: the same statement with
the hypothesis `C(x_i) ≤ N` in place of `|x_i| ≤ N`.  This is the form of the equivalence of
Theorem 212.

For a `D` that is not optimal the predicate is trivially true — the hypothesis `C(x_i) ≤ N` is
then never satisfied — so every theorem that uses it must assume `isOptimalConditional D`.
SUV Theorem 212, p. 327. -/
def HoldsForComplexitiesCplx (f : LinearForm n) (D : Map) : Prop :=
  ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
    f.evalComplexity D x ≤ (logSlack c N : ℝ)

/-! ### Shannon-type forms -/

/-- The basic inequality `H(ξ_{I ∪ K}) + H(ξ_{J ∪ K}) ≥ H(ξ_{I ∪ J ∪ K}) + H(ξ_K)` as a
linear form, in the sign convention `eval ≤ 0`.  The book prints it as
`H(ξ_{I ∩ J}) + H(ξ_{I ∪ J}) ≤ H(ξ_I) + H(ξ_J)` (p. 338); with `I, J, K` disjoint the two
readings are the same statement for the sets `I ∪ K` and `J ∪ K`, whose intersection is `K`.
The form is the sum of four indicator coefficients, so repetitions among the four sets add up
correctly.  SUV Section 10.11, p. 338. -/
def basicInequality (n : ℕ) (I J K : Finset (Fin n)) : LinearForm n := fun S =>
  (if S = I ∪ J ∪ K then 1 else 0) + (if S = K then 1 else 0)
    - (if S = I ∪ K then 1 else 0) - (if S = J ∪ K then 1 else 0)

/-- The monotonicity form `H(ξ_I) − H(ξ_{I ∪ J}) ≤ 0`, the second family of basic
inequalities of SUV Section 10.11, p. 338. -/
def monotonicityForm (n : ℕ) (I J : Finset (Fin n)) : LinearForm n := fun S =>
  (if S = I then 1 else 0) - (if S = I ∪ J then 1 else 0)

/-- The generators of the Shannon cone: the basic inequalities and the monotonicity forms.
SUV Section 10.11, p. 338. -/
def shannonGenerators (n : ℕ) : Set (LinearForm n) :=
  {f | (∃ I J K, f = basicInequality n I J K) ∨ ∃ I J, f = monotonicityForm n I J}

/-- A form is of Shannon type when it is a non-negative real combination of the generators of
the Shannon cone, the coefficients at the empty set being disregarded.  The content of
Chapter 10 is that some true inequalities for entropies are *not* of Shannon type
(Theorem 218).  SUV Section 10.11, p. 338. -/
def IsShannonType (f : LinearForm n) : Prop :=
  ∃ (m : ℕ) (g : Fin m → LinearForm n) (c : Fin m → ℝ),
    (∀ k, 0 ≤ c k) ∧ (∀ k, g k ∈ shannonGenerators n) ∧
      ∀ I : Finset (Fin n), I.Nonempty → f I = ∑ k, c k * g k I

end Kolmogorov
