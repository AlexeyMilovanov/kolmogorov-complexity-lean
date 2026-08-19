import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Conditionally independent uniform bits (SUV Exercise 314)

SUV Theorem 217 (p. 342) produces two random variables `α, β`, both uniformly
distributed in `{0,1}`, that are *conditionally independent* — meaning that
there are two **independent** random variables `γ, δ` such that `α` and `β` are
independent given `γ` and independent given `δ` — while
`Pr[α = β] = 5/8`, so that `α` and `β` are not independent.

**Exercise 314** asks to show that `5/8` may be replaced by an arbitrary
`c ∈ [3/8, 5/8]`.  This file proves exactly that, over an explicit finite
probability space: the four variables take Boolean values, so a joint
distribution is a nonnegative weight function on `Bool × Bool × Bool × Bool`
of total mass `1` (`Kolmogorov.QuadDist`).

## Main definitions

* `Kolmogorov.QuadDist` — a joint distribution of four Boolean random
  variables `α, β, γ, δ`.
* `Kolmogorov.QuadDist.pr` — the probability of a Boolean-valued event,
  together with the marginal abbreviations `prAlpha`, `prBeta`, `prGamma`,
  `prDelta`, `prAlphaBeta`, `prGammaDelta`, … and the agreement probability
  `prAgree = Pr[α = β]`.
* `Kolmogorov.QuadDist.CondIndepGivenGamma` / `CondIndepGivenDelta` —
  conditional independence of `α` and `β` in the division-free form
  `Pr[α = a, β = b, γ = g] · Pr[γ = g] = Pr[α = a, γ = g] · Pr[β = b, γ = g]`.
* `Kolmogorov.QuadDist.GammaDeltaIndep` — independence of `γ` and `δ`.

## Main results

* `Kolmogorov.exercise_314_conditionally_independent_uniform_pair`: for every
  `c ∈ [3/8, 5/8]` there is a distribution with uniform `α`, uniform `β`,
  independent `γ, δ`, conditional independence of `α, β` given `γ` and given
  `δ`, and `Pr[α = β] = c`; moreover the joint law of `(α, β)` is the symmetric
  one with `Pr[α = β = a] = c/2`.
* `Kolmogorov.exercise_314_not_independent`: for `c ≠ 1/2` such a pair is not
  independent, so the mutual information of `α` and `β` is nonzero — this is
  the point of the exercise.

## Construction

Write `A_g` for the joint law of `(α, β)` conditioned on `γ = g` and `B_d` for
the one conditioned on `δ = d`; conditional independence says each of these is
a product measure.  We take `γ, δ` uniform and independent and put
`N_{gd}(a,b) = Pr[α = a, β = b, γ = g, δ = d]`, so that `N` must have Boolean
"row sums" `A_g/2` and "column sums" `B_d/2`, each block having total mass
`1/4`.  With a parameter `p ∈ [1/2, 3/4]` we use

* for `c = 1 - 2p(1-p) ∈ [1/2, 5/8]`: `A_0 = B_0 = (p, 1-p) ⊗ (p, 1-p)`, the
  laws for `γ = 1`, `δ = 1` being the bit-flips of these
  (`Kolmogorov.highWeight`);
* for `c = 2p(1-p) ∈ [3/8, 1/2]`: `A_0 = (p, 1-p) ⊗ (1-p, p)` and
  `B_0 = A_0ᵀ` (`Kolmogorov.lowWeight`).

In both cases the required nonnegative coupling `N` is written down explicitly,
and `p = (1 + √|2c-1|)/2` realizes the prescribed value of `c`.
-/

open Finset

namespace Kolmogorov

/-- A joint distribution of four Boolean random variables `α, β, γ, δ`, given by
its weight function `w a b g d = Pr[α = a, β = b, γ = g, δ = d]`. -/
structure QuadDist where
  /-- The elementary probabilities `Pr[α = a, β = b, γ = g, δ = d]`. -/
  w : Bool → Bool → Bool → Bool → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a b g d, 0 ≤ w a b g d
  /-- The total mass is one. -/
  total : ∑ a : Bool, ∑ b : Bool, ∑ g : Bool, ∑ d : Bool, w a b g d = 1

namespace QuadDist

variable (D : QuadDist)

/-- The probability of the event described by the Boolean predicate `S`. -/
def pr (S : Bool → Bool → Bool → Bool → Bool) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, ∑ g : Bool, ∑ d : Bool, if S a b g d then D.w a b g d else 0

/-- `Pr[α = a]`. -/
def prAlpha (a : Bool) : ℝ := D.pr fun a' _ _ _ => a' == a

/-- `Pr[β = b]`. -/
def prBeta (b : Bool) : ℝ := D.pr fun _ b' _ _ => b' == b

/-- `Pr[γ = g]`. -/
def prGamma (g : Bool) : ℝ := D.pr fun _ _ g' _ => g' == g

/-- `Pr[δ = d]`. -/
def prDelta (d : Bool) : ℝ := D.pr fun _ _ _ d' => d' == d

/-- `Pr[α = a, β = b]`. -/
def prAlphaBeta (a b : Bool) : ℝ := D.pr fun a' b' _ _ => (a' == a) && (b' == b)

/-- `Pr[γ = g, δ = d]`. -/
def prGammaDelta (g d : Bool) : ℝ := D.pr fun _ _ g' d' => (g' == g) && (d' == d)

/-- `Pr[α = a, γ = g]`. -/
def prAlphaGamma (a g : Bool) : ℝ := D.pr fun a' _ g' _ => (a' == a) && (g' == g)

/-- `Pr[β = b, γ = g]`. -/
def prBetaGamma (b g : Bool) : ℝ := D.pr fun _ b' g' _ => (b' == b) && (g' == g)

/-- `Pr[α = a, δ = d]`. -/
def prAlphaDelta (a d : Bool) : ℝ := D.pr fun a' _ _ d' => (a' == a) && (d' == d)

/-- `Pr[β = b, δ = d]`. -/
def prBetaDelta (b d : Bool) : ℝ := D.pr fun _ b' _ d' => (b' == b) && (d' == d)

/-- `Pr[α = a, β = b, γ = g]`. -/
def prAlphaBetaGamma (a b g : Bool) : ℝ :=
  D.pr fun a' b' g' _ => (a' == a) && (b' == b) && (g' == g)

/-- `Pr[α = a, β = b, δ = d]`. -/
def prAlphaBetaDelta (a b d : Bool) : ℝ :=
  D.pr fun a' b' _ d' => (a' == a) && (b' == b) && (d' == d)

/-- `Pr[α = β]`. -/
def prAgree : ℝ := D.pr fun a b _ _ => a == b

/-- `α` and `β` are independent given `γ`, in division-free form. -/
def CondIndepGivenGamma : Prop :=
  ∀ a b g, D.prAlphaBetaGamma a b g * D.prGamma g = D.prAlphaGamma a g * D.prBetaGamma b g

/-- `α` and `β` are independent given `δ`, in division-free form. -/
def CondIndepGivenDelta : Prop :=
  ∀ a b d, D.prAlphaBetaDelta a b d * D.prDelta d = D.prAlphaDelta a d * D.prBetaDelta b d

/-- `γ` and `δ` are independent. -/
def GammaDeltaIndep : Prop := ∀ g d, D.prGammaDelta g d = D.prGamma g * D.prDelta d

/-- `α` and `β` are independent. -/
def AlphaBetaIndep : Prop := ∀ a b, D.prAlphaBeta a b = D.prAlpha a * D.prBeta b

end QuadDist

/-- The weight function of the high-correlation family: with `p ∈ [1/2, 3/4]`
it realizes `Pr[α = β] = 1 - 2p(1-p) ∈ [1/2, 5/8]`. -/
noncomputable def highWeight (p : ℝ) : Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => p - 1 / 2
  | false, true, false, false => 3 / 8 - p / 2
  | true, false, false, false => 3 / 8 - p / 2
  | true, true, false, false => 0
  | false, false, true, true => 0
  | false, true, true, true => 3 / 8 - p / 2
  | true, false, true, true => 3 / 8 - p / 2
  | true, true, true, true => p - 1 / 2
  | false, false, _, _ => (1 - p) ^ 2 / 2
  | false, true, _, _ => p * (1 - p) / 2 + p / 2 - 3 / 8
  | true, false, _, _ => p * (1 - p) / 2 + p / 2 - 3 / 8
  | true, true, _, _ => (1 - p) ^ 2 / 2

/-- The weight function of the low-correlation family: with `p ∈ [1/2, 3/4]`
it realizes `Pr[α = β] = 2p(1-p) ∈ [3/8, 1/2]`. -/
noncomputable def lowWeight (p : ℝ) : Bool → Bool → Bool → Bool → ℝ
  | false, false, false, false => p / 8
  | false, true, false, false => (1 - p) / 8
  | true, false, false, false => (1 - p) / 8
  | true, true, false, false => p / 8
  | false, false, true, true => p / 8
  | false, true, true, true => (1 - p) / 8
  | true, false, true, true => (1 - p) / 8
  | true, true, true, true => p / 8
  | false, false, false, true => p * (1 - p) / 2 - p / 8
  | false, true, false, true => p ^ 2 / 2 - (1 - p) / 8
  | true, false, false, true => (1 - p) ^ 2 / 2 - (1 - p) / 8
  | true, true, false, true => p * (1 - p) / 2 - p / 8
  | false, false, true, false => p * (1 - p) / 2 - p / 8
  | false, true, true, false => (1 - p) ^ 2 / 2 - (1 - p) / 8
  | true, false, true, false => p ^ 2 / 2 - (1 - p) / 8
  | true, true, true, false => p * (1 - p) / 2 - p / 8

/-- The high-correlation distribution attached to `p ∈ [1/2, 3/4]`. -/
noncomputable def highDist (p : ℝ) (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) : QuadDist where
  w := highWeight p
  nonneg := by
    intro a b g d
    cases a <;> cases b <;> cases g <;> cases d <;> simp [highWeight] <;> nlinarith
  total := by simp [highWeight]; ring

/-- The low-correlation distribution attached to `p ∈ [1/2, 3/4]`. -/
noncomputable def lowDist (p : ℝ) (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) : QuadDist where
  w := lowWeight p
  nonneg := by
    intro a b g d
    cases a <;> cases b <;> cases g <;> cases d <;> simp [lowWeight] <;> nlinarith
  total := by simp [lowWeight]; ring

section Verification

variable {p : ℝ}

open QuadDist

theorem highDist_prAlpha (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) (a : Bool) :
    (highDist p h₁ h₂).prAlpha a = 1 / 2 := by
  cases a <;> simp [prAlpha, pr, highDist, highWeight] <;> ring

theorem highDist_prBeta (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) (b : Bool) :
    (highDist p h₁ h₂).prBeta b = 1 / 2 := by
  cases b <;> simp [prBeta, pr, highDist, highWeight] <;> ring

theorem highDist_gammaDeltaIndep (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (highDist p h₁ h₂).GammaDeltaIndep := by
  intro g d
  cases g <;> cases d <;>
    simp [prGammaDelta, prGamma, prDelta, pr, highDist, highWeight] <;> ring

theorem highDist_condIndepGivenGamma (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (highDist p h₁ h₂).CondIndepGivenGamma := by
  intro a b g
  cases a <;> cases b <;> cases g <;>
    simp [prAlphaBetaGamma, prGamma, prAlphaGamma, prBetaGamma, pr, highDist, highWeight] <;> ring

theorem highDist_condIndepGivenDelta (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (highDist p h₁ h₂).CondIndepGivenDelta := by
  intro a b d
  cases a <;> cases b <;> cases d <;>
    simp [prAlphaBetaDelta, prDelta, prAlphaDelta, prBetaDelta, pr, highDist, highWeight] <;> ring

theorem highDist_prAlphaBeta (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) (a b : Bool) :
    (highDist p h₁ h₂).prAlphaBeta a b =
      if a = b then (1 - 2 * p * (1 - p)) / 2 else (2 * p * (1 - p)) / 2 := by
  cases a <;> cases b <;> simp [prAlphaBeta, pr, highDist, highWeight] <;> ring

theorem highDist_prAgree (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (highDist p h₁ h₂).prAgree = 1 - 2 * p * (1 - p) := by
  simp [prAgree, pr, highDist, highWeight]; ring

theorem lowDist_prAlpha (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) (a : Bool) :
    (lowDist p h₁ h₂).prAlpha a = 1 / 2 := by
  cases a <;> simp [prAlpha, pr, lowDist, lowWeight] <;> ring

theorem lowDist_prBeta (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) (b : Bool) :
    (lowDist p h₁ h₂).prBeta b = 1 / 2 := by
  cases b <;> simp [prBeta, pr, lowDist, lowWeight] <;> ring

theorem lowDist_gammaDeltaIndep (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (lowDist p h₁ h₂).GammaDeltaIndep := by
  intro g d
  cases g <;> cases d <;>
    simp [prGammaDelta, prGamma, prDelta, pr, lowDist, lowWeight] <;> ring

theorem lowDist_condIndepGivenGamma (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (lowDist p h₁ h₂).CondIndepGivenGamma := by
  intro a b g
  cases a <;> cases b <;> cases g <;>
    simp [prAlphaBetaGamma, prGamma, prAlphaGamma, prBetaGamma, pr, lowDist, lowWeight] <;> ring

theorem lowDist_condIndepGivenDelta (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (lowDist p h₁ h₂).CondIndepGivenDelta := by
  intro a b d
  cases a <;> cases b <;> cases d <;>
    simp [prAlphaBetaDelta, prDelta, prAlphaDelta, prBetaDelta, pr, lowDist, lowWeight] <;> ring

theorem lowDist_prAlphaBeta (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) (a b : Bool) :
    (lowDist p h₁ h₂).prAlphaBeta a b =
      if a = b then (2 * p * (1 - p)) / 2 else (1 - 2 * p * (1 - p)) / 2 := by
  cases a <;> cases b <;> simp [prAlphaBeta, pr, lowDist, lowWeight] <;> ring

theorem lowDist_prAgree (h₁ : 1 / 2 ≤ p) (h₂ : p ≤ 3 / 4) :
    (lowDist p h₁ h₂).prAgree = 2 * p * (1 - p) := by
  simp [prAgree, pr, lowDist, lowWeight]; ring

end Verification

/-- **SUV Exercise 314.**  For every `c ∈ [3/8, 5/8]` there are four Boolean
random variables `α, β, γ, δ` on a common (finite) probability space such that

* `α` and `β` are uniformly distributed in `{0,1}`;
* `γ` and `δ` are independent;
* `α` and `β` are independent given `γ`, and also given `δ`;
* `Pr[α = β] = c`, the joint law of `(α, β)` being the symmetric one.

For `c = 5/8` this is SUV Theorem 217. -/
theorem exercise_314_conditionally_independent_uniform_pair (c : ℝ)
    (hc₀ : 3 / 8 ≤ c) (hc₁ : c ≤ 5 / 8) :
    ∃ D : QuadDist,
      (∀ a, D.prAlpha a = 1 / 2) ∧ (∀ b, D.prBeta b = 1 / 2) ∧
        D.GammaDeltaIndep ∧ D.CondIndepGivenGamma ∧ D.CondIndepGivenDelta ∧
          D.prAgree = c ∧
            ∀ a b, D.prAlphaBeta a b = if a = b then c / 2 else (1 - c) / 2 := by
  rcases le_total (1 / 2 : ℝ) c with hhalf | hhalf
  · -- high-correlation branch: `c = 1 - 2p(1-p)` with `p = (1 + √(2c-1))/2`
    set r : ℝ := Real.sqrt (2 * c - 1) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = 2 * c - 1 := by
      rw [hr, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * c - 1)]
    have hr1 : r ≤ 1 / 2 := by nlinarith
    set p : ℝ := (1 + r) / 2 with hp
    have h₁ : 1 / 2 ≤ p := by rw [hp]; linarith
    have h₂ : p ≤ 3 / 4 := by rw [hp]; linarith
    have hcp : 1 - 2 * p * (1 - p) = c := by rw [hp]; nlinarith
    refine ⟨highDist p h₁ h₂, highDist_prAlpha h₁ h₂, highDist_prBeta h₁ h₂,
      highDist_gammaDeltaIndep h₁ h₂, highDist_condIndepGivenGamma h₁ h₂,
      highDist_condIndepGivenDelta h₁ h₂, ?_, ?_⟩
    · rw [highDist_prAgree h₁ h₂, hcp]
    · intro a b
      rw [highDist_prAlphaBeta h₁ h₂]
      by_cases hab : a = b
      · simp [hab, hcp]
      · simp only [hab, if_false]
        nlinarith [hcp]
  · -- low-correlation branch: `c = 2p(1-p)` with `p = (1 + √(1-2c))/2`
    set r : ℝ := Real.sqrt (1 - 2 * c) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = 1 - 2 * c := by
      rw [hr, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - 2 * c)]
    have hr1 : r ≤ 1 / 2 := by nlinarith
    set p : ℝ := (1 + r) / 2 with hp
    have h₁ : 1 / 2 ≤ p := by rw [hp]; linarith
    have h₂ : p ≤ 3 / 4 := by rw [hp]; linarith
    have hcp : 2 * p * (1 - p) = c := by rw [hp]; nlinarith
    refine ⟨lowDist p h₁ h₂, lowDist_prAlpha h₁ h₂, lowDist_prBeta h₁ h₂,
      lowDist_gammaDeltaIndep h₁ h₂, lowDist_condIndepGivenGamma h₁ h₂,
      lowDist_condIndepGivenDelta h₁ h₂, ?_, ?_⟩
    · rw [lowDist_prAgree h₁ h₂, hcp]
    · intro a b
      rw [lowDist_prAlphaBeta h₁ h₂]
      by_cases hab : a = b
      · simp [hab, hcp]
      · simp only [hab, if_false]
        nlinarith [hcp]

/-- The pairs produced by `exercise_314_conditionally_independent_uniform_pair`
are **not** independent unless `c = 1/2`: their mutual information is nonzero,
which is what makes the statement interesting. -/
theorem exercise_314_not_independent {D : QuadDist} {c : ℝ} (hc : c ≠ 1 / 2)
    (hα : ∀ a, D.prAlpha a = 1 / 2) (hβ : ∀ b, D.prBeta b = 1 / 2)
    (hjoint : ∀ a b, D.prAlphaBeta a b = if a = b then c / 2 else (1 - c) / 2) :
    ¬ D.AlphaBetaIndep := by
  intro h
  have h00 := h false false
  rw [hjoint false false, hα false, hβ false, if_pos rfl] at h00
  exact hc (by linarith)

/-- **SUV Theorem 217** (p. 342), the case `c = 5/8` of Exercise 314: there are
two uniformly distributed, conditionally independent but *dependent* Boolean
random variables `α, β` with `Pr[α = β] = 5/8`. -/
theorem theorem_217_conditionally_independent_not_independent :
    ∃ D : QuadDist,
      (∀ a, D.prAlpha a = 1 / 2) ∧ (∀ b, D.prBeta b = 1 / 2) ∧
        D.GammaDeltaIndep ∧ D.CondIndepGivenGamma ∧ D.CondIndepGivenDelta ∧
          D.prAgree = 5 / 8 ∧ ¬ D.AlphaBetaIndep := by
  obtain ⟨D, hα, hβ, hγδ, hcg, hcd, hagree, hjoint⟩ :=
    exercise_314_conditionally_independent_uniform_pair (5 / 8) (by norm_num) le_rfl
  exact ⟨D, hα, hβ, hγδ, hcg, hcd, hagree,
    exercise_314_not_independent (by norm_num) hα hβ hjoint⟩

end Kolmogorov
