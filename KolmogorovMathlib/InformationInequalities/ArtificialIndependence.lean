import KolmogorovMathlib.InformationInequalities.Ingleton
import KolmogorovMathlib.Entropy.Inequalities

/-!
# Artificial independence and Theorem 218

SUV Section 10.13, pp. 343–347.

This module holds the first half of the section on non-Shannon inequalities: the quantity
`W(α, β, γ) = I(α:β|γ) + I(α:γ|β) + I(β:γ|α)` (`pairwiseCondInfoSum`), the recoding and
basic-inequality helpers used throughout the section, the resampling construction
(`coupling`: two independent copies of the space glued along a variable `Z`, so that the
variables read off the two coordinates are independent given `Z`), and the proof of
**Theorem 218** (Makarychev, Makarychev, Romashchenko and Vereshchagin) by artificial
independence:
`I(α:β) ≤ I(α:β|γ) + I(α:β|δ) + I(γ:δ) + I(α:β|ε) + I(α:ε|β) + I(β:ε|α)`.
The inequality with three extra terms is a sum of eight basic inequalities; resampling so that
`⟨γ, δ⟩` and `ε` are independent given `⟨α, β⟩` leaves every term unchanged and kills the
first extra term, which bounds the other two.

The consequences of Theorem 218 (the special extreme ray outside the closure of the entropy
region, the deduction rule, Theorem 219, Problem 303 and the steps of the second proof) are in
`KolmogorovMathlib.InformationInequalities.NonShannonTheorems`, which imports this module.
The book's proof of Theorem 218 is announced as "we will prove Theorem 208 in the general
case" (p. 346), a misprint for Theorem 218.
-/

namespace Kolmogorov

open Finset

section Variables

variable {Ω : Type} [Fintype Ω] {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The quantity `W(α, β, γ) = I(α:β|γ) + I(α:γ|β) + I(β:γ|α)`, the sum of the three
conditional mutual informations of a triple (Figure 34).  SUV Section 10.13, p. 344. -/
noncomputable def pairwiseCondInfoSum (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : ℝ :=
  condMutualInfo μ X Y Z + condMutualInfo μ X Z Y + condMutualInfo μ Y Z X

end Variables

/-! ### Recoding tuples and the chain rule

Every term of the section is a combination of entropies of nested pairs of the variables.  The
helpers below identify the entropies of two nestings of the same variables (entropy is invariant
under an injective recoding, `entropy_comp_of_injective`) and record the two consequences of
the basic inequality that the book uses: conditioning on more does not increase the entropy,
and the conditional form of Problem 296. -/

section Helpers

variable {Ω : Type} [Fintype Ω] {α β γ δ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [DecidableEq δ]

/-- Entropy is invariant under an injective recoding, stated pointwise. -/
theorem entropy_eq_of_comp (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (f : α → β) (hf : Function.Injective f) (h : ∀ ω, Y ω = f (X ω)) :
    entropy μ Y = entropy μ X := by
  have : Y = f ∘ X := funext h
  rw [this, entropy_comp_of_injective μ X hf]

/-- `H((η, ζ), ξ) = H((ξ, η), ζ)`. -/
theorem entropy_pair_rotate (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    entropy μ (pairRV (pairRV Y Z) X) = entropy μ (pairRV (pairRV X Y) Z) := by
  rw [entropy_pairRV_comm, entropy_pairRV_assoc]

/-- `H(η, (ξ, ζ)) = H(ξ, (η, ζ))`. -/
private theorem entropy_pair_swap_mid (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    entropy μ (pairRV Y (pairRV X Z)) = entropy μ (pairRV X (pairRV Y Z)) := by
  rw [← entropy_pairRV_assoc, entropy_pairRV_swap_right, entropy_pairRV_comm]

/-- `I(ξ : η | ζ) = H(ξ, ζ) + H(η, ζ) − H(ζ) − H((ξ, η), ζ)`. -/
theorem condMutualInfo_eq (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    condMutualInfo μ X Y Z = entropy μ (pairRV X Z) + entropy μ (pairRV Y Z) - entropy μ Z
      - entropy μ (pairRV (pairRV X Y) Z) := by
  unfold condMutualInfo
  rw [condEntropy_eq_sub, condEntropy_eq_sub, condEntropy_eq_sub]
  ring

/-- The basic inequality `I(ξ : η | ζ) ≥ 0`, expanded into entropies. -/
private theorem basic_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    entropy μ (pairRV (pairRV X Y) Z) + entropy μ Z
      ≤ entropy μ (pairRV X Z) + entropy μ (pairRV Y Z) := by
  linarith [condMutualInfo_nonneg μ X Y Z, condMutualInfo_eq μ X Y Z]

/-- Conditioning on more does not increase the entropy: `H(ξ | η, ζ) ≤ H(ξ | η)`.  It is the
basic inequality `I(ξ : ζ | η) ≥ 0` rewritten through the chain rule. -/
theorem condEntropy_pairRV_le_condEntropy (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) : condEntropy μ X (pairRV Y Z) ≤ condEntropy μ X Y := by
  rw [condEntropy_eq_sub, condEntropy_eq_sub]
  linarith [basic_nonneg μ X Z Y, entropy_pairRV_assoc μ X Y Z, entropy_pairRV_swap_right μ X Y Z,
    entropy_pairRV_comm μ Y Z]

/-- **Problem 296, conditional form**: `H(ξ | ζ) ≤ H(ξ | η, ζ) + H(ξ | θ, ζ) + I(η : θ | ζ)`.
It is the sum of the two basic inequalities `H(ξ | η, θ, ζ) ≥ 0` and `I(η : θ | ξ, ζ) ≥ 0`,
through the identity `H(ξ|ζ) + H(ξ|η,θ,ζ) + I(η:θ|ξ,ζ) = H(ξ|η,ζ) + H(ξ|θ,ζ) + I(η:θ|ζ)`.
SUV Section 10.13, p. 348. -/
theorem condEntropy_le_condEntropy_pairRV_add (μ : FiniteProbSpace Ω) (X : Ω → α)
    (G : Ω → β) (D : Ω → γ) (Z : Ω → δ) :
    condEntropy μ X Z
      ≤ condEntropy μ X (pairRV G Z) + condEntropy μ X (pairRV D Z) + condMutualInfo μ G D Z := by
  simp only [condEntropy_eq_sub, condMutualInfo_eq]
  linarith [condEntropy_nonneg μ X (pairRV (pairRV G D) Z),
    condEntropy_eq_sub μ X (pairRV (pairRV G D) Z), basic_nonneg μ G D (pairRV X Z),
    entropy_pair_swap_mid μ X G Z, entropy_pair_swap_mid μ X D Z,
    entropy_pair_swap_mid μ X (pairRV G D) Z]

end Helpers

/-! ### Theorem 218: artificial independence

The book's proof (pp. 346–347) has three steps: the inequality with the three extra terms
`I(⟨γ,δ⟩:ε|⟨α,β⟩) + I(γ:ε|⟨α,β⟩) + I(δ:ε|⟨α,β⟩)` on the right is a sum of eight basic
inequalities; resampling `⟨γ,δ⟩` and `ε` independently given `⟨α,β⟩` leaves every term of
Theorem 218 unchanged and makes the first extra term vanish; and the other two extra terms are
bounded by the first. -/

section ArtificialIndependence

variable {Ω : Type} [Fintype Ω] {α β γ δ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  [DecidableEq δ]

/-- `H((η, ξ), ζ) = H((ξ, η), ζ)`. -/
private theorem entropy_pair_swap_left (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    entropy μ (pairRV (pairRV Y X) Z) = entropy μ (pairRV (pairRV X Y) Z) :=
  entropy_eq_of_comp μ _ _ (fun p => ((p.1.2, p.1.1), p.2))
    (by rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h; simp only [Prod.mk.injEq] at h ⊢; tauto)
    fun _ => rfl

/-- `H((ζ, η), ξ) = H(ξ, (η, ζ))`. -/
private theorem entropy_pair_rev (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    entropy μ (pairRV (pairRV Z Y) X) = entropy μ (pairRV X (pairRV Y Z)) :=
  entropy_eq_of_comp μ _ _ (fun p => ((p.2.2, p.2.1), p.1))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; simp only [Prod.mk.injEq] at h ⊢; tauto)
    fun _ => rfl

/-- `H((η, ζ), ξ) = H((ξ, ζ), η)`. -/
private theorem entropy_pair_swap_outer (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    entropy μ (pairRV (pairRV Y Z) X) = entropy μ (pairRV (pairRV X Z) Y) :=
  entropy_eq_of_comp μ _ _ (fun p => ((p.2, p.1.2), p.1.1))
    (by rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h; simp only [Prod.mk.injEq] at h ⊢; tauto)
    fun _ => rfl

/-- Conditional mutual information grows with the first argument:
`I(ξ : ε | ζ) ≤ I(⟨ξ, η⟩ : ε | ζ)`, the basic inequality `I(η : ε | ξ, ζ) ≥ 0` in disguise.
SUV Section 10.13, p. 346. -/
theorem condMutualInfo_le_condMutualInfo_pairRV_left (μ : FiniteProbSpace Ω)
    (X : Ω → α) (Y : Ω → β) (E : Ω → γ) (Z : Ω → δ) :
    condMutualInfo μ X E Z ≤ condMutualInfo μ (pairRV X Y) E Z := by
  simp only [condMutualInfo_eq]
  have e3 : entropy μ (pairRV (pairRV Y E) (pairRV X Z))
      = entropy μ (pairRV (pairRV (pairRV X Y) E) Z) :=
    entropy_eq_of_comp μ _ _ (fun p => ((p.1.1.2, p.1.2), (p.1.1.1, p.2)))
      (by rintro ⟨⟨⟨a, b⟩, c⟩, d⟩ ⟨⟨⟨a', b'⟩, c'⟩, d'⟩ h; simp only [Prod.mk.injEq] at h ⊢; tauto)
      fun _ => rfl
  linarith [basic_nonneg μ Y E (pairRV X Z), entropy_pairRV_assoc μ Y X Z,
    entropy_pair_swap_left μ X Y Z, entropy_pairRV_assoc μ E X Z, entropy_pair_swap_left μ X E Z]

/-- The inequality of Theorem 218 with the three extra terms
`I(⟨γ,δ⟩:ε|⟨α,β⟩) + I(γ:ε|⟨α,β⟩) + I(δ:ε|⟨α,β⟩)` on the right.  It is the sum of the eight
basic inequalities `I(⟨α,β⟩:ε|γ,δ)`, `I(α:β|ε,γ)`, `I(α:β|ε,δ)`, `I(γ:δ|ε)`, `I(γ:ε|α)`,
`I(γ:ε|β)`, `I(δ:ε|α)`, `I(δ:ε|β)` `≥ 0`, expanded into entropies of tuples.
SUV Section 10.13, pp. 346–347. -/
private theorem mutualInfo_le_nonShannon_add_three_condMutualInfo (μ : FiniteProbSpace Ω)
    (A B C D E : Ω → ℕ) :
    mutualInfo μ A B
      ≤ condMutualInfo μ A B C + condMutualInfo μ A B D + mutualInfo μ C D
        + pairwiseCondInfoSum μ A B E
        + condMutualInfo μ (pairRV C D) E (pairRV A B)
        + condMutualInfo μ C E (pairRV A B) + condMutualInfo μ D E (pairRV A B) := by
  simp only [condMutualInfo_eq, mutualInfo, pairwiseCondInfoSum]
  linarith [basic_nonneg μ (pairRV A B) E (pairRV C D), basic_nonneg μ A B (pairRV E C),
    basic_nonneg μ A B (pairRV E D), basic_nonneg μ C D E, basic_nonneg μ C E A,
    basic_nonneg μ C E B, basic_nonneg μ D E A, basic_nonneg μ D E B,
    entropy_pairRV_comm μ A B, entropy_pairRV_comm μ A C, entropy_pairRV_comm μ B C,
    entropy_pairRV_comm μ A D, entropy_pairRV_comm μ B D, entropy_pairRV_comm μ A E,
    entropy_pairRV_comm μ B E, entropy_pairRV_comm μ C E, entropy_pairRV_comm μ D E,
    entropy_pairRV_comm μ (pairRV A B) C, entropy_pairRV_comm μ (pairRV A B) D,
    entropy_pairRV_comm μ (pairRV A B) E, entropy_pairRV_swap_right μ A B E,
    entropy_pair_rotate μ A B E, entropy_pair_rev μ A E C, entropy_pair_rev μ B E C,
    entropy_pair_rev μ A E D, entropy_pair_rev μ B E D, entropy_pairRV_comm μ (pairRV C D) E,
    entropy_pairRV_comm μ (pairRV A B) (pairRV C D), entropy_pair_rev μ (pairRV A B) E C,
    entropy_pair_rev μ (pairRV A B) E D, entropy_pair_swap_outer μ (pairRV A B) (pairRV C D) E]

/-- Entropy depends on the distribution only: two random variables, possibly on different
spaces, with the same distribution have the same entropy. -/
private theorem entropy_eq_of_dist_eq {Ω' : Type} [Fintype Ω'] (μ : FiniteProbSpace Ω)
    (μ' : FiniteProbSpace Ω') (X : Ω → α) (X' : Ω' → α) (h : ∀ a, μ.dist X a = μ'.dist X' a) :
    entropy μ X = entropy μ' X' := by
  unfold entropy
  have h1 : ∑ a ∈ rangeFinset X, negMulLog2 (μ.dist X a)
      = ∑ a ∈ rangeFinset X ∪ rangeFinset X', negMulLog2 (μ.dist X a) :=
    Finset.sum_subset Finset.subset_union_left fun a _ ha => by
      rw [μ.dist_eq_zero_of_not_mem_range ha, negMulLog2_zero]
  have h2 : ∑ a ∈ rangeFinset X', negMulLog2 (μ'.dist X' a)
      = ∑ a ∈ rangeFinset X ∪ rangeFinset X', negMulLog2 (μ'.dist X' a) :=
    Finset.sum_subset Finset.subset_union_right fun a _ ha => by
      rw [μ'.dist_eq_zero_of_not_mem_range ha, negMulLog2_zero]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

/-- Two random variables that agree on every outcome of non-zero weight have the same
distribution. -/
private theorem dist_eq_of_eq_on_support (μ : FiniteProbSpace Ω) (X Y : Ω → α)
    (h : ∀ ω, μ.prob ω ≠ 0 → X ω = Y ω) (a : α) : μ.dist X a = μ.dist Y a := by
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : μ.prob ω = 0
  · simp [hω]
  · rw [h ω hω]

/-- The weight of a pair `(ω₁, ω₂)` in the coupling of `μ` with itself along `Z`:
`Pr[ω₁] · Pr[ω₂] / Pr[Z = Z(ω₁)]` when `Z(ω₁) = Z(ω₂)`, and `0` otherwise. -/
private noncomputable def couplingWeight (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω : Ω × Ω) :
    ℝ :=
  if Z ω.1 = Z ω.2 then μ.prob ω.1 * μ.prob ω.2 / μ.dist Z (Z ω.1) else 0

/-- The weight of an outcome is at most the probability of the value of `Z` it takes. -/
private theorem prob_le_dist (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω : Ω) :
    μ.prob ω ≤ μ.dist Z (Z ω) := by
  unfold FiniteProbSpace.dist FiniteProbSpace.probOf
  exact Finset.single_le_sum (f := μ.prob) (fun ω' _ => μ.prob_nonneg ω') (by simp)

/-- The event `{Z = Z(ω₁)}` has probability `Pr[Z = Z(ω₁)]`, in the form of a sum over all
outcomes. -/
private theorem sum_ite_eq_dist (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω₁ : Ω) :
    ∑ ω₂, (if Z ω₁ = Z ω₂ then μ.prob ω₂ else 0) = μ.dist Z (Z ω₁) := by
  unfold FiniteProbSpace.dist FiniteProbSpace.probOf
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : Z ω = Z ω₁
  · simp [h]
  · simp [h, Ne.symm h]

/-- The weight of a positive-probability fibre, divided by itself, is one; the case of
probability zero is absorbed because the outcome then has weight zero. -/
private theorem prob_div_dist_mul (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω : Ω) :
    μ.prob ω / μ.dist Z (Z ω) * μ.dist Z (Z ω) = μ.prob ω := by
  rcases (μ.dist_nonneg Z (Z ω)).lt_or_eq with h | h
  · exact div_mul_cancel₀ _ h.ne'
  · rw [← h, mul_zero]
    have := prob_le_dist μ Z ω
    rw [← h] at this
    exact (le_antisymm this (μ.prob_nonneg ω)).symm

/-- Summing the coupling weight over the second coordinate gives back the weight of the
first. -/
private theorem sum_couplingWeight_snd (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω₁ : Ω) :
    ∑ ω₂, couplingWeight μ Z (ω₁, ω₂) = μ.prob ω₁ := by
  have h : ∀ ω₂, couplingWeight μ Z (ω₁, ω₂)
      = μ.prob ω₁ / μ.dist Z (Z ω₁) * (if Z ω₁ = Z ω₂ then μ.prob ω₂ else 0) := by
    intro ω₂
    unfold couplingWeight
    split_ifs <;> ring
  simp_rw [h, ← Finset.mul_sum, sum_ite_eq_dist]
  exact prob_div_dist_mul μ Z ω₁

/-- Summing the coupling weight over the first coordinate gives back the weight of the
second. -/
private theorem sum_couplingWeight_fst (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω₂ : Ω) :
    ∑ ω₁, couplingWeight μ Z (ω₁, ω₂) = μ.prob ω₂ := by
  have h : ∀ ω₁, couplingWeight μ Z (ω₁, ω₂)
      = μ.prob ω₂ / μ.dist Z (Z ω₂) * (if Z ω₂ = Z ω₁ then μ.prob ω₁ else 0) := by
    intro ω₁
    unfold couplingWeight
    by_cases h : Z ω₁ = Z ω₂
    · simp only [h, ite_true]
      ring
    · simp [h, Ne.symm h]
  simp_rw [h, ← Finset.mul_sum, sum_ite_eq_dist]
  exact prob_div_dist_mul μ Z ω₂

/-- The coupling of `μ` with itself along `Z`: two outcomes drawn independently from the
conditional distributions given a common value of `Z`, that value drawn from the
distribution of `Z`. -/
noncomputable def coupling (μ : FiniteProbSpace Ω) (Z : Ω → γ) :
    FiniteProbSpace (Ω × Ω) where
  prob := couplingWeight μ Z
  prob_nonneg ω := by
    unfold couplingWeight
    split_ifs
    · exact div_nonneg (mul_nonneg (μ.prob_nonneg _) (μ.prob_nonneg _)) (μ.dist_nonneg _ _)
    · exact le_rfl
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp only [sum_couplingWeight_snd, μ.sum_prob]

/-- A pair of positive weight in the coupling has a common value of `Z`. -/
private theorem coupling_eq_of_prob_ne_zero (μ : FiniteProbSpace Ω) (Z : Ω → γ) (ω : Ω × Ω)
    (h : (coupling μ Z).prob ω ≠ 0) : Z ω.1 = Z ω.2 := by
  by_contra hne
  change couplingWeight μ Z ω ≠ 0 at h
  unfold couplingWeight at h
  rw [ite_eq_right hne] at h
  exact h rfl

/-- The first coordinate of the coupling is distributed as `μ`. -/
private theorem dist_coupling_fst (μ : FiniteProbSpace Ω) (Z : Ω → γ) (X : Ω → α) (a : α) :
    (coupling μ Z).dist (fun ω => X ω.1) a = μ.dist X a := by
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω₁ _ => ?_
  by_cases h : X ω₁ = a
  · simp only [h, ite_true]
    exact sum_couplingWeight_snd μ Z ω₁
  · simp [h]

/-- The second coordinate of the coupling is distributed as `μ`. -/
private theorem dist_coupling_snd (μ : FiniteProbSpace Ω) (Z : Ω → γ) (X : Ω → α) (a : α) :
    (coupling μ Z).dist (fun ω => X ω.2) a = μ.dist X a := by
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun ω₂ _ => ?_
  by_cases h : X ω₂ = a
  · simp only [h, ite_true]
    exact sum_couplingWeight_fst μ Z ω₂
  · simp [h]

/-- A variable on the coupling that agrees on the support with a function of the first
coordinate has the entropy of that function under `μ`. -/
theorem entropy_coupling_of_eq_fst (μ : FiniteProbSpace Ω) (Z : Ω → γ)
    (V : Ω × Ω → α) (V₁ : Ω → α) (h : ∀ ω : Ω × Ω, Z ω.1 = Z ω.2 → V ω = V₁ ω.1) :
    entropy (coupling μ Z) V = entropy μ V₁ := by
  rw [entropy_eq_of_dist_eq (coupling μ Z) (coupling μ Z) V (fun ω => V₁ ω.1)
    (dist_eq_of_eq_on_support _ _ _ fun ω hω => h ω (coupling_eq_of_prob_ne_zero μ Z ω hω))]
  exact entropy_eq_of_dist_eq _ _ _ _ (dist_coupling_fst μ Z V₁)

/-- A variable on the coupling that agrees on the support with a function of the second
coordinate has the entropy of that function under `μ`. -/
theorem entropy_coupling_of_eq_snd (μ : FiniteProbSpace Ω) (Z : Ω → γ)
    (V : Ω × Ω → α) (V₂ : Ω → α) (h : ∀ ω : Ω × Ω, Z ω.1 = Z ω.2 → V ω = V₂ ω.2) :
    entropy (coupling μ Z) V = entropy μ V₂ := by
  rw [entropy_eq_of_dist_eq (coupling μ Z) (coupling μ Z) V (fun ω => V₂ ω.2)
    (dist_eq_of_eq_on_support _ _ _ fun ω hω => h ω (coupling_eq_of_prob_ne_zero μ Z ω hω))]
  exact entropy_eq_of_dist_eq _ _ _ _ (dist_coupling_snd μ Z V₂)

/-- The product formula of the coupling: given `Z = c`, a function of the first coordinate
and a function of the second are independent. -/
private theorem dist_coupling_prod (μ : FiniteProbSpace Ω) (Z : Ω → γ) (X : Ω → α)
    (Y : Ω → β) (c : γ) (a : α) (b : β) :
    (coupling μ Z).dist (fun ω => (Z ω.1, (X ω.1, Y ω.2))) (c, (a, b))
      = μ.dist (pairRV Z X) (c, a) * μ.dist (pairRV Z Y) (c, b) / μ.dist Z c := by
  have key : ∀ ω₁ ω₂ : Ω,
      (if (Z ω₁, (X ω₁, Y ω₂)) = (c, (a, b)) then (coupling μ Z).prob (ω₁, ω₂) else 0)
        = (if (Z ω₁, X ω₁) = (c, a) then μ.prob ω₁ else 0)
          * (if (Z ω₂, Y ω₂) = (c, b) then μ.prob ω₂ else 0) / μ.dist Z c := by
    intro ω₁ ω₂
    change (if _ then couplingWeight μ Z (ω₁, ω₂) else 0) = _
    unfold couplingWeight
    by_cases h1 : Z ω₁ = c
    · subst h1
      by_cases h2 : Z ω₂ = Z ω₁
      · by_cases h3 : X ω₁ = a <;> by_cases h4 : Y ω₂ = b <;> simp [h2, h3, h4]
      · by_cases h3 : X ω₁ = a <;> by_cases h4 : Y ω₂ = b <;> simp [h2, Ne.symm h2, h3, h4]
    · simp [h1]
  have hX : ∑ ω, (if (Z ω, X ω) = (c, a) then μ.prob ω else 0) = μ.dist (pairRV Z X) (c, a) := by
    unfold FiniteProbSpace.dist FiniteProbSpace.probOf
    rw [Finset.sum_filter]
    rfl
  have hY : ∑ ω, (if (Z ω, Y ω) = (c, b) then μ.prob ω else 0) = μ.dist (pairRV Z Y) (c, b) := by
    unfold FiniteProbSpace.dist FiniteProbSpace.probOf
    rw [Finset.sum_filter]
    rfl
  rw [← hX, ← hY]
  conv_lhs => unfold FiniteProbSpace.dist FiniteProbSpace.probOf
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => key ω₁ ω₂).trans ?_
  simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Given a value of `Z`, a function of the first coordinate of the coupling and a function
of the second are conditionally independent: the conditional distribution of the pair is the
product of the conditional distributions. -/
private theorem condDist_coupling_mul (μ : FiniteProbSpace Ω) (Z : Ω → γ) (X : Ω → α)
    (Y : Ω → β) (c : γ) (a : α) (b : β) :
    (coupling μ Z).condDist (pairRV (fun ω => X ω.1) (fun ω => Y ω.2))
        (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c) (a, b)
      = (coupling μ Z).condDist (fun ω => X ω.1)
          (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c) a
        * (coupling μ Z).condDist (fun ω => Y ω.2)
          (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c) b := by
  have h1 : (coupling μ Z).probOf (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c)
      = μ.dist Z c := dist_coupling_fst μ Z Z c
  have h2 : (coupling μ Z).probOf ((Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c).filter
      fun ω => X ω.1 = a) = μ.dist (pairRV Z X) (c, a) := by
    rw [← dist_coupling_fst μ Z (pairRV Z X) (c, a)]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp [pairRV]
  have h3 : (coupling μ Z).probOf ((Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c).filter
      fun ω => Y ω.2 = b) = μ.dist (pairRV Z Y) (c, b) := by
    rw [← dist_coupling_snd μ Z (pairRV Z Y) (c, b),
      ← dist_eq_of_eq_on_support (coupling μ Z) (fun ω => (Z ω.1, Y ω.2))
        (fun ω => pairRV Z Y ω.2)
        (fun ω hω => by
          change (Z ω.1, Y ω.2) = (Z ω.2, Y ω.2)
          rw [coupling_eq_of_prob_ne_zero μ Z ω hω]) (c, b)]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp
  have h4 : (coupling μ Z).probOf ((Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c).filter
      fun ω => pairRV (fun ω => X ω.1) (fun ω => Y ω.2) ω = (a, b))
      = μ.dist (pairRV Z X) (c, a) * μ.dist (pairRV Z Y) (c, b) / μ.dist Z c := by
    rw [← dist_coupling_prod μ Z X Y c a b]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp [pairRV]
  unfold FiniteProbSpace.condDist
  rw [h4, h2, h3, h1]
  ring

/-- In the coupling along `Z`, a function of the first coordinate and a function of the
second are independent given `Z` (read off the first coordinate): `I(X : Y | Z) = 0`. -/
theorem condMutualInfo_coupling_eq_zero (μ : FiniteProbSpace Ω) (Z : Ω → γ)
    (X : Ω → α) (Y : Ω → β) :
    condMutualInfo (coupling μ Z) (fun ω => X ω.1) (fun ω => Y ω.2) (fun ω => Z ω.1) = 0 := by
  have hsum : condMutualInfo (coupling μ Z) (fun ω => X ω.1) (fun ω => Y ω.2) (fun ω => Z ω.1)
      = ∑ c ∈ rangeFinset (fun ω : Ω × Ω => Z ω.1),
          (coupling μ Z).dist (fun ω => Z ω.1) c *
          (condEntropyGiven (coupling μ Z) (fun ω => X ω.1)
              (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c)
            + condEntropyGiven (coupling μ Z) (fun ω => Y ω.2)
              (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c)
            - condEntropyGiven (coupling μ Z) (pairRV (fun ω => X ω.1) (fun ω => Y ω.2))
              (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c)) := by
    simp only [condMutualInfo, condEntropy, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  rw [hsum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases ((coupling μ Z).dist_nonneg (fun ω => Z ω.1) c).lt_or_eq with hc | hc
  · have hE : 0 < (coupling μ Z).probOf (Finset.univ.filter fun ω : Ω × Ω => Z ω.1 = c) := hc
    rw [← (coupling μ Z).entropy_condSpace hE, ← (coupling μ Z).entropy_condSpace hE,
      ← (coupling μ Z).entropy_condSpace hE]
    have hind : Independent ((coupling μ Z).condSpace _ hE) (fun ω => X ω.1)
        (fun ω => Y ω.2) := by
      intro a b
      rw [(coupling μ Z).dist_condSpace, (coupling μ Z).dist_condSpace,
        (coupling μ Z).dist_condSpace]
      exact condDist_coupling_mul μ Z X Y c a b
    rw [(independent_iff_entropy_pairRV_eq_add _ _ _).1 hind]
    ring
  · rw [← hc, zero_mul]

/-- **Artificial independence.**  Resampling `⟨γ,δ⟩` and `ε` independently according to
their conditional distributions given `⟨α,β⟩` — on the space `Ω × Ω` with the weight
`Pr[ω₁] · Pr[ω₂] / Pr[⟨α,β⟩ = ⟨α,β⟩(ω₁)]` on the pairs with `⟨α,β⟩(ω₁) = ⟨α,β⟩(ω₂)`, the
variables `α, β, γ, δ` read off `ω₁` and `ε` off `ω₂` — keeps the joint distributions of
`(α,β,γ,δ)` and of `(α,β,ε)`, hence every term of Theorem 218, and makes `⟨γ,δ⟩` and `ε`
independent given `⟨α,β⟩`.  SUV Section 10.13, p. 346. -/
private theorem exists_artificially_independent (μ : FiniteProbSpace Ω) (A B C D E : Ω → ℕ) :
    ∃ (Ω' : Type) (_ : Fintype Ω') (μ' : FiniteProbSpace Ω') (A' B' C' D' E' : Ω' → ℕ),
      mutualInfo μ' A' B' = mutualInfo μ A B ∧
      condMutualInfo μ' A' B' C' = condMutualInfo μ A B C ∧
      condMutualInfo μ' A' B' D' = condMutualInfo μ A B D ∧
      mutualInfo μ' C' D' = mutualInfo μ C D ∧
      pairwiseCondInfoSum μ' A' B' E' = pairwiseCondInfoSum μ A B E ∧
      condMutualInfo μ' (pairRV C' D') E' (pairRV A' B') = 0 ∧
      condMutualInfo μ' (pairRV D' C') E' (pairRV A' B') = 0 := by
  let μ' := coupling μ (pairRV A B)
  let A' : Ω × Ω → ℕ := fun ω => A ω.1
  let B' : Ω × Ω → ℕ := fun ω => B ω.1
  let C' : Ω × Ω → ℕ := fun ω => C ω.1
  let D' : Ω × Ω → ℕ := fun ω => D ω.1
  let E' : Ω × Ω → ℕ := fun ω => E ω.2
  have hf : ∀ {κ : Type} [DecidableEq κ] (V : Ω → κ) (V' : Ω × Ω → κ),
      (∀ ω, V' ω = V ω.1) → entropy μ' V' = entropy μ V :=
    fun V V' h => entropy_coupling_of_eq_fst μ _ V' V fun ω _ => h ω
  have hs : ∀ {κ : Type} [DecidableEq κ] (V : Ω → κ) (V' : Ω × Ω → κ),
      (∀ ω : Ω × Ω, A ω.1 = A ω.2 → B ω.1 = B ω.2 → V' ω = V ω.2) →
        entropy μ' V' = entropy μ V :=
    fun V V' h => entropy_coupling_of_eq_snd μ _ V' V fun ω hω => by
      simp only [pairRV, Prod.mk.injEq] at hω
      exact h ω hω.1 hω.2
  refine ⟨Ω × Ω, inferInstance, μ', A', B', C', D', E', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold mutualInfo
    linarith [hf A A' fun _ => rfl, hf B B' fun _ => rfl,
      hf (pairRV A B) (pairRV A' B') fun _ => rfl]
  · simp only [condMutualInfo_eq]
    linarith [hf (pairRV A C) (pairRV A' C') fun _ => rfl,
      hf (pairRV B C) (pairRV B' C') fun _ => rfl, hf C C' fun _ => rfl,
      hf (pairRV (pairRV A B) C) (pairRV (pairRV A' B') C') fun _ => rfl]
  · simp only [condMutualInfo_eq]
    linarith [hf (pairRV A D) (pairRV A' D') fun _ => rfl,
      hf (pairRV B D) (pairRV B' D') fun _ => rfl, hf D D' fun _ => rfl,
      hf (pairRV (pairRV A B) D) (pairRV (pairRV A' B') D') fun _ => rfl]
  · unfold mutualInfo
    linarith [hf C C' fun _ => rfl, hf D D' fun _ => rfl,
      hf (pairRV C D) (pairRV C' D') fun _ => rfl]
  · simp only [pairwiseCondInfoSum, condMutualInfo_eq]
    linarith [hs A A' fun _ hA _ => hA, hs B B' fun _ _ hB => hB, hs E E' fun _ _ _ => rfl,
      hs (pairRV A E) (pairRV A' E') fun _ hA _ => Prod.ext hA rfl,
      hs (pairRV B E) (pairRV B' E') fun _ _ hB => Prod.ext hB rfl,
      hs (pairRV A B) (pairRV A' B') fun _ hA hB => Prod.ext hA hB,
      hs (pairRV B A) (pairRV B' A') fun _ hA hB => Prod.ext hB hA,
      hs (pairRV E B) (pairRV E' B') fun _ _ hB => Prod.ext rfl hB,
      hs (pairRV E A) (pairRV E' A') fun _ hA _ => Prod.ext rfl hA,
      hs (pairRV (pairRV A B) E) (pairRV (pairRV A' B') E') fun _ hA hB =>
        Prod.ext (Prod.ext hA hB) rfl,
      hs (pairRV (pairRV A E) B) (pairRV (pairRV A' E') B') fun _ hA hB =>
        Prod.ext (Prod.ext hA rfl) hB,
      hs (pairRV (pairRV B E) A) (pairRV (pairRV B' E') A') fun _ hA hB =>
        Prod.ext (Prod.ext hB rfl) hA]
  · exact condMutualInfo_coupling_eq_zero μ (pairRV A B) (pairRV C D) E
  · exact condMutualInfo_coupling_eq_zero μ (pairRV A B) (pairRV D C) E

end ArtificialIndependence

/-! ### Theorem 218 -/

/-- **Theorem 218.**  For every quintuple of random variables `α, β, γ, δ, ε`:
`I(α:β) ≤ I(α:β|γ) + I(α:β|δ) + I(γ:δ) + I(α:β|ε) + I(α:ε|β) + I(β:ε|α)`.
SUV Theorem 218, p. 344. -/
theorem mutualInfo_le_nonShannon {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (A B C D E : Ω → ℕ) :
    mutualInfo μ A B
      ≤ condMutualInfo μ A B C + condMutualInfo μ A B D + mutualInfo μ C D
        + condMutualInfo μ A B E + condMutualInfo μ A E B + condMutualInfo μ B E A := by
  obtain ⟨Ω', _, μ', A', B', C', D', E', h1, h2, h3, h4, h5, h0, h0'⟩ :=
    exists_artificially_independent μ A B C D E
  have hweak := mutualInfo_le_nonShannon_add_three_condMutualInfo μ' A' B' C' D' E'
  have hC := condMutualInfo_le_condMutualInfo_pairRV_left μ' C' D' E' (pairRV A' B')
  have hD := condMutualInfo_le_condMutualInfo_pairRV_left μ' D' C' E' (pairRV A' B')
  have hCn := condMutualInfo_nonneg μ' C' E' (pairRV A' B')
  have hDn := condMutualInfo_nonneg μ' D' E' (pairRV A' B')
  unfold pairwiseCondInfoSum at h5 hweak
  linarith

end Kolmogorov
