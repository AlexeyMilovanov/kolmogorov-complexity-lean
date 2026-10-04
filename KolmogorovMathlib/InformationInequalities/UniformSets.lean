/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Projections, sections and uniform sets

SUV Sections 10.2 and 10.5, pp. 318–319 and p. 324.

For a subset `A ⊆ X_1 × ⋯ × X_n` of a product of finite sets the book writes `m_A(I)` for the
size of the projection of `A` onto the coordinates in `I`, and `m_A(J | I)`, for disjoint `I`
and `J`, for the **maximal** size of a section: fix a point of `∏_{i ∈ I} X_i` and count the
`J`-coordinates of the points of `A` with those `I`-coordinates; `m_A(J | I)` is the largest
such count (p. 318).  The maximum is taken over the whole product `∏_{i ∈ I} X_i`, exactly as
printed; points outside the projection give empty sections and do not affect it.

The conventions `m(∅) = 1`, `m(∅ | J) = 1` and `m(I | ∅) = m(I)` of p. 319 are facts here, not
stipulations: `projCard_empty` and `maxSection_empty`.

For every set `A` and every permutation `k_1, …, k_n` of the coordinates the chain inequality
`m(k_1, …, k_n) ≤ m(k_1) · m(k_2 | k_1) ⋯ m(k_n | k_1, …, k_{n-1})` holds, with
`m(k_1, …, k_n) = |A|` on the left (p. 319).  `A` is **uniform** when all `n!` of these
inequalities are equalities (p. 319), and **`c`-uniform** when the ratio of the two sides is
at most `c` for every permutation (p. 324); `1`-uniform is uniform.  `chainBound A σ` is the
right-hand side for the permutation `σ`.
-/

namespace Kolmogorov

open Finset

section Restrict

variable {n : ℕ} {X : Fin n → Type*}

/-- The restriction of a point of `∏_i X_i` to the coordinates in `I`. -/
def restrictTo (I : Finset (Fin n)) (a : ∀ i, X i) : (i : I) → X i.val := fun i => a i.val

/-- The restriction to all coordinates loses nothing. -/
theorem restrictTo_univ_injective :
    Function.Injective (restrictTo (X := X) Finset.univ) := by
  intro a b h
  funext i
  exact congrFun h ⟨i, Finset.mem_univ i⟩

end Restrict

section Projections

variable {n : ℕ} {X : Fin n → Type*} [∀ i, DecidableEq (X i)]

/-- The projection of `A` onto the coordinates in `I`.  SUV Section 10.2, p. 318. -/
def proj (A : Finset (∀ i, X i)) (I : Finset (Fin n)) : Finset ((i : I) → X i.val) :=
  A.image (restrictTo I)

/-- The size `m_A(I)` of the projection of `A` onto the coordinates in `I`.
SUV Section 10.2, p. 318. -/
def projCard (A : Finset (∀ i, X i)) (I : Finset (Fin n)) : ℕ := (proj A I).card

/-- `m_A(∅) = 1` for a non-empty `A`: the projection onto no coordinates is a single point.
SUV Section 10.2, p. 319. -/
theorem projCard_empty {A : Finset (∀ i, X i)} (hA : A.Nonempty) : projCard A ∅ = 1 := by
  refine Finset.card_eq_one.2 ⟨restrictTo ∅ hA.choose, ?_⟩
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · exact Finset.mem_image_of_mem _ hA.choose_spec
  · intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hp
    funext i
    exact (Finset.notMem_empty i.val i.2).elim

/-- `m_A({1, …, n}) = |A|`: the projection onto all coordinates is `A` itself.
SUV Section 10.2, p. 319. -/
theorem projCard_univ (A : Finset (∀ i, X i)) : projCard A Finset.univ = A.card :=
  Finset.card_image_of_injective _ restrictTo_univ_injective

/-- The `J`-section of `A` over the point `p` of `∏_{i ∈ I} X_i`: the `J`-coordinates of the
points of `A` whose `I`-coordinates are `p`.  SUV Section 10.2, p. 318. -/
def sectionOver (A : Finset (∀ i, X i)) (J I : Finset (Fin n)) (p : (i : I) → X i.val) :
    Finset ((j : J) → X j.val) :=
  (A.filter fun a => restrictTo I a = p).image (restrictTo J)

/-- The value of a linear form on the log-sizes of the projections of `A`:
`∑_{I ≠ ∅} λ_I · log₂ m_A(I)`.  SUV Theorem 206, p. 321. -/
noncomputable def LinearForm.evalLogSize (f : LinearForm n) (A : Finset (∀ i, X i)) : ℝ :=
  ∑ I ∈ nonemptyParts n, f I * Real.logb 2 (projCard A I)

/-- Only the coefficients at non-empty sets matter for the log-size evaluation. -/
theorem LinearForm.evalLogSize_congr {f g : LinearForm n} (A : Finset (∀ i, X i))
    (h : ∀ I : Finset (Fin n), I.Nonempty → f I = g I) :
    f.evalLogSize A = g.evalLogSize A :=
  Finset.sum_congr rfl fun I hI => by rw [h I (mem_nonemptyParts.1 hI)]

end Projections

section Uniformity

variable {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The maximal size `m_A(J | I)` of a `J`-section of `A` over a point of `∏_{i ∈ I} X_i`.
SUV Section 10.2, p. 318. -/
def maxSection (A : Finset (∀ i, X i)) (J I : Finset (Fin n)) : ℕ :=
  Finset.univ.sup fun p : (i : I) → X i.val => (sectionOver A J I p).card

/-- The maximum defining `m_A(J | I)` is attained on the projection of `A`: a point of
`∏_{i ∈ I} X_i` outside `proj A I` has an empty `J`-section and contributes nothing, so taking
the maximum over the whole product — as the book prints it — is the same as taking it over the
`I`-projection of `A`.  SUV Section 10.2, p. 318. -/
theorem maxSection_eq_sup_proj (A : Finset (∀ i, X i)) (J I : Finset (Fin n)) :
    maxSection A J I = (proj A I).sup fun p => (sectionOver A J I p).card := by
  simp only [maxSection]
  apply le_antisymm
  · refine Finset.sup_le fun p _ => ?_
    by_cases hp : p ∈ proj A I
    · exact Finset.le_sup (f := fun q => (sectionOver A J I q).card) hp
    · have hempty : sectionOver A J I p = ∅ := by
        refine Finset.image_eq_empty.2 (Finset.filter_eq_empty_iff.2 fun {a} ha h => ?_)
        exact hp (Finset.mem_image.2 ⟨a, ha, h⟩)
      simp [hempty]
  · exact Finset.sup_mono (f := fun q => (sectionOver A J I q).card)
      (Finset.subset_univ _)

/-- `m_A(J | ∅) = m_A(J)`: conditioning on no coordinates is the plain projection.
SUV Section 10.2, p. 319. -/
theorem maxSection_empty (A : Finset (∀ i, X i)) (J : Finset (Fin n)) :
    maxSection A J ∅ = projCard A J := by
  have hall : ∀ p : (i : (∅ : Finset (Fin n))) → X i.val,
      sectionOver A J ∅ p = proj A J := by
    intro p
    have hfilter : (A.filter fun a => restrictTo ∅ a = p) = A := by
      refine Finset.filter_true_of_mem fun a _ => ?_
      funext i
      exact (Finset.notMem_empty i.val i.2).elim
    rw [sectionOver, hfilter, proj]
  have hcard : ∀ p : (i : (∅ : Finset (Fin n))) → X i.val,
      (sectionOver A J ∅ p).card = projCard A J := fun p => by rw [hall p, projCard]
  refine le_antisymm (Finset.sup_le fun p _ => (hcard p).le) ?_
  rw [← hcard fun i => (Finset.notMem_empty i.val i.2).elim]
  exact Finset.le_sup (f := fun p : (i : (∅ : Finset (Fin n))) → X i.val =>
    (sectionOver A J ∅ p).card) (Finset.mem_univ _)

/-- The indices that precede `k` in the ordering that `σ` imposes on the coordinates. -/
def earlierIndices (σ : Equiv.Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun j => j < k).image σ

/-- The right-hand side `m(k_1) · m(k_2 | k_1) ⋯ m(k_n | k_1, …, k_{n-1})` of the chain
inequality for the ordering `σ` of the coordinates.  SUV Section 10.2, p. 319. -/
def chainBound (A : Finset (∀ i, X i)) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∏ k : Fin n, maxSection A {σ k} (earlierIndices σ k)

/-- `A` is uniform when the chain inequality is an equality for every ordering of the
coordinates; the left-hand side `m(k_1, …, k_n)` is `|A|`.  SUV Section 10.2, p. 319.

The predicate does not require `A` to be non-empty, although the book always fixes a non-empty
`A` (p. 318): every statement about uniformity must therefore carry `A.Nonempty` itself, or it
becomes false at `A = ∅`. -/def IsUniform (A : Finset (∀ i, X i)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), chainBound A σ = A.card

/-- `A` is `c`-uniform when the two sides of the chain inequality differ by a factor at most
`c`, for every ordering of the coordinates.  A `1`-uniform set is a uniform set.
SUV Section 10.5, p. 324.

The predicate does not require `A` to be non-empty, although the book always fixes a non-empty
`A` (p. 318): every statement about uniformity must therefore carry `A.Nonempty` itself, or it
becomes false at `A = ∅`. -/def IsCUniform (c : ℝ) (A : Finset (∀ i, X i)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), (chainBound A σ : ℝ) ≤ c * A.card

end Uniformity

/-! ### The uniform distribution on a finite set -/

/-- The uniform distribution on a non-empty finite set: every element has probability
`1 / |A|`.  This is the distribution that SUV Section 10.2, p. 320 attaches to a uniform
set in order to read its projection sizes off as entropies. -/
noncomputable def uniformProbOn {α : Type*} (A : Finset α) (hA : A.Nonempty) :
    FiniteProbSpace {a // a ∈ A} where
  prob := fun _ => (A.card : ℝ)⁻¹
  prob_nonneg := fun _ => by positivity
  sum_prob := by
    have hcard : (Finset.univ : Finset {a // a ∈ A}).card = A.card := by simp
    have hpos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 hA
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp

/-- The `i`-th coordinate of a point chosen uniformly at random in `A`: the random variables
`ξ_1, …, ξ_n` of SUV Section 10.2, p. 320.  The coordinates are taken in one and the same
value type, which is how the entropy layer indexes a tuple of random variables. -/
def uniformCoords {n : ℕ} {α : Type*} (A : Finset (Fin n → α)) :
    Fin n → ({a // a ∈ A} → α) := fun i a => a.val i

/-- A random variable is uniformly distributed on its range when all the values it takes are
equiprobable.  This is the property that SUV Theorem 205, p. 321 asks of every subtuple
`ξ_I`. -/
def IsUniformlyDistributed {Ω : Type*} [Fintype Ω] {α : Type*} [DecidableEq α]
    (μ : FiniteProbSpace Ω) (X : Ω → α) : Prop :=
  ∀ a ∈ rangeFinset X, μ.dist X a = ((rangeFinset X).card : ℝ)⁻¹

/-- The form holds for uniform sets: `∑_{I ≠ ∅} λ_I · log₂ m_A(I) ≤ 0` for every non-empty
uniform subset of a product of finite sets.  The coordinate types range over `Type`, i.e. over
universe `0`: every object of the book's statements is finite, so nothing is lost, and the
chapter statements are written with `Type` throughout.  SUV Theorem 206, p. 321. -/
def HoldsForUniformSets {n : ℕ} (f : LinearForm n) : Prop :=
  ∀ (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (A : Finset (∀ i, Y i)), A.Nonempty → IsUniform A → f.evalLogSize A ≤ 0

end Kolmogorov
