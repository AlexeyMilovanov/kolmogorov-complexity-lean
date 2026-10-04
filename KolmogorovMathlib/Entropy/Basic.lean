/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Shannon entropy on a finite probability space

SUV Section 7.1–7.2, pp. 213–221.  The book works with random variables that have a finite
range and are defined on a common finite probability space; this module fixes that model.

A `FiniteProbSpace Ω` is a finite type `Ω` carrying non-negative weights that sum to one.
A random variable is an arbitrary function `X : Ω → α`; its distribution is
`FiniteProbSpace.dist`, and its entropy is the base-two sum `∑ a, -p a * log₂ (p a)` taken over
the (finite) range of `X`.

Two conventions are fixed here and used everywhere below.

* **Base two.**  All entropies are measured in bits, as in the book: the summand is
  `negMulLog2 x = -x·log₂ x`, obtained from Mathlib's natural-logarithm `Real.negMulLog` by
  dividing by `Real.log 2`.
* **`0 log 0 = 0`.**  This is already Mathlib's convention for `Real.negMulLog`, and it is the
  book's convention for zero-probability values.

The range of a random variable is taken as a `Finset` (`rangeFinset`) rather than requiring the
value type to be a `Fintype`.  This is a deliberate departure from a naive `∑ a : α` definition:
`Finset (Fin n) → α`-valued subtuples and `ℕ`-valued variables (used for the entropy region of
Chapter 10) are then covered by the same definition.  For a `Fintype` value type the two agree,
which is `entropy_eq_entropyDist`.
-/

namespace Kolmogorov

open Finset

/-! ### The entropy summand -/

/-- `negMulLog2 x = -x · log₂ x`, the summand of a base-two entropy, with the convention
`0 log 0 = 0` inherited from `Real.negMulLog`. -/
noncomputable def negMulLog2 (x : ℝ) : ℝ := Real.negMulLog x / Real.log 2

/-- The entropy summand vanishes at zero: `0 log 0 = 0`. -/
@[simp] theorem negMulLog2_zero : negMulLog2 0 = 0 := by
  simp [negMulLog2]

/-- The entropy summand is non-negative on the probability range `[0, 1]`. -/
theorem negMulLog2_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ negMulLog2 x :=
  div_nonneg (Real.negMulLog_nonneg h0 h1) (Real.log_nonneg (by norm_num))

/-! ### Finite probability spaces -/

/-- A finite probability space: a finite type of outcomes with non-negative weights summing
to one.  SUV Section 7.2, p. 217. -/
structure FiniteProbSpace (Ω : Type*) [Fintype Ω] where
  /-- The weight of an outcome. -/
  prob : Ω → ℝ
  /-- Weights are non-negative. -/
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  /-- The weights sum to one. -/
  sum_prob : ∑ ω, prob ω = 1

variable {Ω : Type*} [Fintype Ω] {α : Type*} [DecidableEq α]

/-- The range of a random variable on a finite space, as a `Finset`.  Every entropy below is a
sum over this `Finset`, so the value type need not be a `Fintype`.
SUV Section 7.2, p. 217. -/
def rangeFinset (X : Ω → α) : Finset α := Finset.image X Finset.univ

/-- A value taken by a random variable lies in its range. -/
@[simp] theorem mem_rangeFinset {X : Ω → α} {a : α} : a ∈ rangeFinset X ↔ ∃ ω, X ω = a := by
  simp [rangeFinset]

namespace FiniteProbSpace

/-- The probability of an event, i.e. the total weight of a set of outcomes.
SUV Section 7.2, p. 217. -/
def probOf (μ : FiniteProbSpace Ω) (E : Finset Ω) : ℝ := ∑ ω ∈ E, μ.prob ω

/-- The probability of an event is non-negative. -/
theorem probOf_nonneg (μ : FiniteProbSpace Ω) (E : Finset Ω) : 0 ≤ μ.probOf E :=
  Finset.sum_nonneg fun ω _ => μ.prob_nonneg ω

/-- The probability of the whole space is one. -/
@[simp] theorem probOf_univ (μ : FiniteProbSpace Ω) : μ.probOf Finset.univ = 1 := μ.sum_prob

/-- The distribution of a random variable: `dist μ X a = Pr[X = a]`.
SUV Section 7.2, p. 217. -/
def dist (μ : FiniteProbSpace Ω) (X : Ω → α) (a : α) : ℝ :=
  μ.probOf (Finset.univ.filter fun ω => X ω = a)

/-- A distribution takes non-negative values. -/
theorem dist_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) (a : α) : 0 ≤ μ.dist X a :=
  μ.probOf_nonneg _

/-- A value outside the range of a random variable has probability zero. -/
theorem dist_eq_zero_of_not_mem_range (μ : FiniteProbSpace Ω) {X : Ω → α} {a : α}
    (ha : a ∉ rangeFinset X) : μ.dist X a = 0 := by
  have hempty : (Finset.univ.filter fun ω => X ω = a) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 ?_
    intro ω _
    exact fun h => ha (mem_rangeFinset.2 ⟨ω, h⟩)
  simp [dist, probOf, hempty]

/-- The distribution of a random variable sums to one over its range. -/
theorem sum_dist_eq_one (μ : FiniteProbSpace Ω) (X : Ω → α) :
    ∑ a ∈ rangeFinset X, μ.dist X a = 1 := by
  have hmaps : ∀ ω ∈ (Finset.univ : Finset Ω), X ω ∈ rangeFinset X := by
    intro ω _
    exact mem_rangeFinset.2 ⟨ω, rfl⟩
  have := Finset.sum_fiberwise_of_maps_to hmaps μ.prob
  simpa [dist, probOf] using this.trans μ.sum_prob

/-- The expectation of a real-valued function on a finite probability space. -/
def expect (μ : FiniteProbSpace Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.prob ω * f ω

/-- The `N`-fold product of a finite probability space: `N` independent copies of `μ`, the
model for the i.i.d. sequences of Section 7.3.  The i.i.d. sequence of copies of a random
variable `X : Ω → α` is `fun i ω => X (ω i)`.  SUV Section 7.3, p. 226. -/
def power (μ : FiniteProbSpace Ω) (N : ℕ) : FiniteProbSpace (Fin N → Ω) where
  prob ω := ∏ i, μ.prob (ω i)
  prob_nonneg _ := Finset.prod_nonneg fun i _ => μ.prob_nonneg _
  sum_prob := by
    have h := Finset.prod_univ_sum (κ := fun _ : Fin N => Ω) (fun _ => Finset.univ)
      (fun _ o => μ.prob o)
    simp only [Fintype.piFinset_univ, μ.sum_prob, Finset.prod_const_one] at h
    simpa using h.symm

end FiniteProbSpace

/-! ### Entropy -/

/-- The base-two entropy of a distribution given as a weight function on a finite type:
`H(p) = ∑ a -p a · log₂ (p a)`.  Theorems 138 and 139 speak about distributions rather than
random variables, and this is the form they use.  SUV Section 7.1, pp. 214–216. -/
noncomputable def entropyDist {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, negMulLog2 (p a)

/-- The base-two Shannon entropy `H(ξ)` of a random variable with a finite range:
the sum of `-p·log₂ p` over the values actually taken.  SUV Section 7.2, p. 217. -/
noncomputable def entropy (μ : FiniteProbSpace Ω) (X : Ω → α) : ℝ :=
  ∑ a ∈ rangeFinset X, negMulLog2 (μ.dist X a)

/-- For a random variable whose value type is a `Fintype`, the entropy is the entropy of its
distribution: the values outside the range contribute `negMulLog2 0 = 0`. -/
theorem entropy_eq_entropyDist [Fintype α] (μ : FiniteProbSpace Ω) (X : Ω → α) :
    entropy μ X = entropyDist (μ.dist X) := by
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro a _ ha
  rw [μ.dist_eq_zero_of_not_mem_range ha, negMulLog2_zero]

/-- The entropy of a random variable is non-negative: every summand is. -/
theorem entropy_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) : 0 ≤ entropy μ X := by
  refine Finset.sum_nonneg fun a ha => negMulLog2_nonneg (μ.dist_nonneg X a) ?_
  rw [← μ.sum_dist_eq_one X]
  exact Finset.single_le_sum (f := fun b => μ.dist X b) (fun b _ => μ.dist_nonneg X b) ha

/-- Recoding the values of a random variable along an injective map does not change its
entropy: `H(f(ξ)) = H(ξ)` when `f` is injective.  Entropy depends on the distribution only,
and an injective recoding carries the distribution over bijectively; this is what lets a
subtuple be repacked into any other faithful encoding of the same data.
SUV Section 7.2, p. 217. -/
theorem entropy_comp_of_injective {β : Type*} [DecidableEq β] (μ : FiniteProbSpace Ω)
    (X : Ω → α) {f : α → β} (hf : Function.Injective f) :
    entropy μ (f ∘ X) = entropy μ X := by
  have hrange : rangeFinset (f ∘ X) = (rangeFinset X).image f := by
    simp [rangeFinset, Finset.image_image]
  have hdist : ∀ a : α, μ.dist (f ∘ X) (f a) = μ.dist X a := by
    intro a
    have hfil : (Finset.univ.filter fun ω => (f ∘ X) ω = f a)
        = Finset.univ.filter fun ω => X ω = a := by
      ext ω
      simp [hf.eq_iff]
    simp only [FiniteProbSpace.dist, hfil]
  simp only [entropy, hrange]
  rw [Finset.sum_image fun a _ b _ h => hf h]
  exact Finset.sum_congr rfl fun a _ => by rw [hdist a]

end Kolmogorov
