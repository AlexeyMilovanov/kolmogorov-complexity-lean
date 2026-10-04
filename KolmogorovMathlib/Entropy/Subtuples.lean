/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Conditional

/-!
# Subtuples of random variables, and empirical frequencies

SUV Sections 7.3 and 10.1, pp. 226–229 and pp. 314–318.

Chapters 10 and 12 speak about an `n`-tuple `ξ_1, …, ξ_n` of random variables and about the
entropies `H(ξ_I)` of its subtuples, indexed by `I ⊆ {1, …, n}`.  `subtuple X I` is the
subtuple as a single random variable with values in `I → α` (that is, `{i // i ∈ I} → α`), and
`entropySub`/`condEntropySub` are the corresponding entropies.

The second half of the file fixes the combinatorial vocabulary of Section 7.3: the empirical
frequency of a letter in a word and the set of words with prescribed frequencies (the "type
class" of information theory — nothing to do with Lean's type classes).  Exact multinomial
arithmetic for these sets is already available in `CommonInformation/TypeBounds.lean`.
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α : Type*} [DecidableEq α] {n : ℕ}

/-! ### Subtuples -/

/-- The subtuple `ξ_I` of an `n`-tuple of random variables, as a single random variable with
values in `I → α`.  SUV Section 10.1, p. 314. -/
def subtuple (X : Fin n → Ω → α) (I : Finset (Fin n)) : Ω → (I → α) :=
  fun ω i => X i.val ω

/-- The entropy `H(ξ_I)` of a subtuple.  SUV Section 10.1, p. 314. -/
noncomputable def entropySub (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (I : Finset (Fin n)) : ℝ :=
  entropy μ (subtuple X I)

/-- The conditional entropy `H(ξ_J | ξ_I)` of one subtuple given another.
SUV Section 10.1, p. 314. -/
noncomputable def condEntropySub (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (J I : Finset (Fin n)) : ℝ :=
  condEntropy μ (subtuple X J) (subtuple X I)

/-- The entropy of a subtuple is non-negative. -/
theorem entropySub_nonneg (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (I : Finset (Fin n)) :
    0 ≤ entropySub μ X I :=
  entropy_nonneg _ _

/-- The empty subtuple carries no information: `H(ξ_∅) = 0`.  This is the normalisation the
book fixes for the coordinate of the empty set.  SUV Section 10.1, p. 314. -/
@[simp] theorem entropySub_empty (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) :
    entropySub μ X ∅ = 0 := by
  simp only [entropySub, entropy]
  refine Finset.sum_eq_zero fun a _ => ?_
  have hfil : (Finset.univ.filter fun ω => subtuple X ∅ ω = a) = Finset.univ := by
    refine Finset.filter_true_of_mem fun ω _ => ?_
    funext i
    exact (Finset.notMem_empty i.val i.2).elim
  have h1 : μ.dist (subtuple X ∅) a = 1 := by
    simp only [FiniteProbSpace.dist, hfil]
    exact μ.probOf_univ
  rw [h1]
  simp [negMulLog2, Real.negMulLog]

/-- `H(ξ_{I ∪ J}) = H(ξ_I, ξ_J)`: the subtuple over a union and the pair of the two subtuples
determine each other, so by `entropy_comp_of_injective` they have the same entropy.
SUV Section 10.1, p. 314. -/
theorem entropySub_union (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (I J : Finset (Fin n)) :
    entropySub μ X (I ∪ J) = entropy μ (pairRV (subtuple X I) (subtuple X J)) := by
  set g : (↥(I ∪ J) → α) → (↥I → α) × (↥J → α) :=
    fun h => (fun i : ↥I => h ⟨i.1, Finset.mem_union_left J i.2⟩,
      fun j : ↥J => h ⟨j.1, Finset.mem_union_right I j.2⟩) with hg_def
  have hg : Function.Injective g := by
    intro h₁ h₂ hh
    funext i
    rcases Finset.mem_union.1 i.2 with hi | hi
    · exact congrFun (congrArg Prod.fst hh) ⟨i.1, hi⟩
    · exact congrFun (congrArg Prod.snd hh) ⟨i.1, hi⟩
  have hcomp : pairRV (subtuple X I) (subtuple X J) = g ∘ subtuple X (I ∪ J) := rfl
  rw [entropySub, hcomp, entropy_comp_of_injective μ (subtuple X (I ∪ J)) hg]

/-! ### Empirical frequencies -/

/-- The number of positions of the word `w` that carry the letter `a`.
SUV Section 7.3, p. 226. -/
def freq {N : ℕ} (w : Fin N → α) (a : α) : ℕ := (Finset.univ.filter fun i => w i = a).card

/-- The frequencies of a word of length `N` sum to `N`. -/
theorem sum_freq [Fintype α] {N : ℕ} (w : Fin N → α) : ∑ a, freq w a = N := by
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin N)), w i ∈ (Finset.univ : Finset α) :=
    fun _ _ => Finset.mem_univ _
  simpa [freq] using Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℕ))

/-- The empirical frequency of the letter `a` in the word `w` of length `N`: the fraction
`freq w a / N` of the positions that carry `a`.  These are the frequencies `p_1, …, p_k` of
Theorem 146 — fractions with denominator `N` and integer numerators — whose Shannon entropy
the theorem compares with `C(w)/N`.  For `N = 0` the value is `0`, by the Lean convention
that division by zero gives zero.  SUV Section 7.3, p. 226. -/
noncomputable def freqRat {N : ℕ} (w : Fin N → α) (a : α) : ℝ := (freq w a : ℝ) / N

/-- The type class of a frequency vector: the words of length `N` over `α` in which every
letter `a` occurs exactly `c a` times.  ("Type class" is the information-theoretic term; these
are the sets whose sizes are the multinomial coefficients of Section 7.3.)
SUV Section 7.3, p. 226. -/
def typeClass (N : ℕ) [Fintype α] (c : α → ℕ) : Finset (Fin N → α) :=
  Finset.univ.filter fun w => ∀ a, freq w a = c a

/-- Membership in a type class is exactly the prescription of all the frequencies. -/
@[simp] theorem mem_typeClass {N : ℕ} [Fintype α] {c : α → ℕ} {w : Fin N → α} :
    w ∈ typeClass N c ↔ ∀ a, freq w a = c a := by
  simp [typeClass]

end Kolmogorov
