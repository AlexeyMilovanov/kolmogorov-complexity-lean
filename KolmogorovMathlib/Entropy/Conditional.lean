/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Basic

/-!
# Conditional entropy, independence, mutual information

SUV Sections 7.2.2–7.2.4, pp. 219–224.

The definitions here follow the printed text, not the identities that the book derives from
them; those identities (Theorem 142, `H(ξ|η) = H(ξ,η) − H(η)`, and Theorem 144) are statements
of the chapter skeleton and must not be used as definitions.

* `condDist μ X E` is the conditional distribution of `X` given the event `E`, i.e.
  `Pr[X = a and E] / Pr[E]` (p. 219).  Lean's `x / 0 = 0` gives the book's convention that the
  conditional distribution is the zero function when `Pr[E] = 0`.
* `condEntropy μ X Y` is `H(ξ|η) = ∑_b Pr[η = b] · H(ξ | η = b)`, the displayed formula on
  p. 219.
* `mutualInfo μ X Y` is `I(ξ:η) = H(ξ) + H(η) − H(⟨ξ,η⟩)`, the definition on p. 222.  The
  book records `I(ξ:η) = H(ξ) − H(ξ|η)` as a *consequence* of Theorem 142, so it is not used
  here.
* `condMutualInfo μ X Y Z` is `I(α:β|γ) = H(α|γ) + H(β|γ) − H(⟨α,β⟩|γ)`, the definition on
  p. 223.
* `tripleInfo μ X Y Z` is the central region `I(α:β:γ)` of Figure 21, given on p. 224 by
  `H(α)+H(β)+H(γ) − H(α,β) − H(α,γ) − H(β,γ) + H(α,β,γ)`.  It may be negative.
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Conditioning on an event -/

namespace FiniteProbSpace

/-- The conditional distribution of `X` given the event `E`: `Pr[(X = a) and E] / Pr[E]`.
When `Pr[E] = 0` this is the zero function, by Lean's convention `x / 0 = 0`.
SUV Section 7.2.2, p. 219. -/
noncomputable def condDist (μ : FiniteProbSpace Ω) (X : Ω → α) (E : Finset Ω) (a : α) : ℝ :=
  μ.probOf (E.filter fun ω => X ω = a) / μ.probOf E

/-- A conditional distribution takes non-negative values. -/
theorem condDist_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) (E : Finset Ω) (a : α) :
    0 ≤ μ.condDist X E a :=
  div_nonneg (μ.probOf_nonneg _) (μ.probOf_nonneg _)

/-- Conditioning on the whole space changes nothing. -/
@[simp] theorem condDist_univ (μ : FiniteProbSpace Ω) (X : Ω → α) (a : α) :
    μ.condDist X Finset.univ a = μ.dist X a := by
  simp [condDist, dist, μ.probOf_univ]

end FiniteProbSpace

/-- The entropy of the conditional distribution of `X` given the event `E`, written `H(ξ|A)`
in the book.  SUV Section 7.2.2, p. 219. -/
noncomputable def condEntropyGiven (μ : FiniteProbSpace Ω) (X : Ω → α) (E : Finset Ω) : ℝ :=
  ∑ a ∈ rangeFinset X, negMulLog2 (μ.condDist X E a)

/-- The conditional entropy `H(ξ|η) = ∑_b Pr[η = b] · H(ξ | η = b)`, the average of the
entropies of the conditional distributions of `ξ` given the values of `η`.  This is the book's
definition; `H(ξ|η) = H(ξ,η) − H(η)` is Theorem 142(d), a statement, not a definition.
SUV Section 7.2.2, p. 219. -/
noncomputable def condEntropy (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  ∑ b ∈ rangeFinset Y,
    μ.dist Y b * condEntropyGiven μ X (Finset.univ.filter fun ω => Y ω = b)

/-! ### Pairs and independence -/

/-- The pair `⟨ξ, η⟩` of two random variables on the same space. -/
def pairRV (X : Ω → α) (Y : Ω → β) : Ω → α × β := fun ω => (X ω, Y ω)

/-- Two random variables are independent when the distribution of the pair is the product of the
distributions: `p_{ij} = p_{i*} p_{*j}`.  SUV Section 7.2.3, p. 221. -/
def Independent (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  ∀ a b, μ.dist (pairRV X Y) (a, b) = μ.dist X a * μ.dist Y b

/-- A finite family of random variables is (mutually) independent when the distribution of the
tuple is the product of the distributions of its members.  This is the notion used in
Problem 222, p. 222. -/
def IndependentFamily {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : FiniteProbSpace Ω)
    (X : ι → Ω → α) : Prop :=
  ∀ a : ι → α, μ.dist (fun ω i => X i ω) a = ∏ i, μ.dist (X i) (a i)

/-! ### Mutual information -/

/-- The mutual information `I(ξ:η) = H(ξ) + H(η) − H(⟨ξ,η⟩)`, the book's definition on p. 222
(the form `H(ξ) − H(ξ|η)` is derived there from Theorem 142). -/
noncomputable def mutualInfo (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  entropy μ X + entropy μ Y - entropy μ (pairRV X Y)

/-- The conditional mutual information
`I(α:β|γ) = H(α|γ) + H(β|γ) − H(⟨α,β⟩|γ)`.  SUV Section 7.2.4, p. 223. -/
noncomputable def condMutualInfo (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : ℝ :=
  condEntropy μ X Z + condEntropy μ Y Z - condEntropy μ (pairRV X Y) Z

/-- The central region `I(α:β:γ)` of the diagram for three variables, expressed in
unconditional entropies as
`H(α)+H(β)+H(γ) − H(α,β) − H(α,γ) − H(β,γ) + H(α,β,γ)`.  Unlike the other six regions it can
be negative.  SUV Section 7.2.4, p. 224. -/
noncomputable def tripleInfo (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : ℝ :=
  entropy μ X + entropy μ Y + entropy μ Z
    - entropy μ (pairRV X Y) - entropy μ (pairRV X Z) - entropy μ (pairRV Y Z)
    + entropy μ (pairRV X (pairRV Y Z))

end Kolmogorov
