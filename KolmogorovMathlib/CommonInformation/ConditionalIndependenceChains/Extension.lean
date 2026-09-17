import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import KolmogorovMathlib.CommonInformation.FiniteQuadruple
import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains.ChainDist

/-!
# Extending a conditional-independence chain

The construction step behind SUV Exercise 315: `extend_independence_chain` prepends two new
coordinates to a chain, keeping uniform marginals and the conditional independences
(`extendChainDist_prAlpha`, `extendChainDist_prBeta`, `extendChainDist_condIndep_old`,
`extendChainDist_indep_old`, `extendChainDist_isChain`) and sending the agreement probability
`c` to `(c² + 1) / 2` (`extendChainDist_prAgree`).  `iterate_reaches` shows that iterating
this map from a starting value in `(1/2, 5/8]` reaches every `c ∈ (1/2, 1)`.

The marginal computations the step needs — `ChainDist.prAt_eq_sum_prAt2_left` and its right
form, `ChainDist.uniform_pair_joint`, `extendChainDist_prAt3_old`,
`extendChainDist_prAt3_new_givenAlpha` — make up most of the module.
-/

namespace Kolmogorov
open Finset
open ChainDist QuadDist

/-- A three-coordinate marginal at old coordinates is unchanged by the extension. -/
theorem extendChainDist_prAt3_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ j₃ : Fin (2 * k + 2))
    (x₁ x₂ x₃ : Bool) :
    (extendChainDist D c hc0 hc1).prAt3 (oldCoordInNew j₁) (oldCoordInNew j₂)
        (oldCoordInNew j₃) x₁ x₂ x₃ = D.prAt3 j₁ j₂ j₃ x₁ x₂ x₃ := by
  unfold ChainDist.prAt3
  have hevent :
      (fun w => (w (oldCoordInNew j₁) == x₁) && (w (oldCoordInNew j₂) == x₂) &&
        (w (oldCoordInNew j₃) == x₃)) =
      (fun v => ((extensionEquiv k v).1 j₁ == x₁) &&
        ((extensionEquiv k v).1 j₂ == x₂) &&
        ((extensionEquiv k v).1 j₃ == x₃)) := by
    funext v
    rw [extensionEquiv_old_apply, extensionEquiv_old_apply,
      extensionEquiv_old_apply]
  rw [hevent]
  exact extendChainDist_pr_old D c hc0 hc1
    (fun old => (old j₁ == x₁) && (old j₂ == x₂) && (old j₃ == x₃))

/-- A one-coordinate marginal is the sum of a two-coordinate marginal over the
second coordinate. -/
theorem ChainDist.prAt_eq_sum_prAt2_right {k : ℕ} (D : ChainDist k)
    (j₁ j₂ : Fin (2 * k + 2)) (x : Bool) :
    D.prAt j₁ x = ∑ y : Bool, D.prAt2 j₁ j₂ x y := by
  unfold ChainDist.prAt ChainDist.prAt2 ChainDist.pr
  simp only [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v j₁ = false ∨ v j₁ = true := by cases v j₁ <;> simp
  have h₂ : v j₂ = false ∨ v j₂ = true := by cases v j₂ <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    cases x <;> simp [h₁, h₂]

/-- A one-coordinate marginal is the sum of a two-coordinate marginal over the first
coordinate. -/
theorem ChainDist.prAt_eq_sum_prAt2_left {k : ℕ} (D : ChainDist k)
    (j₁ j₂ : Fin (2 * k + 2)) (y : Bool) :
    D.prAt j₂ y = ∑ x : Bool, D.prAt2 j₁ j₂ x y := by
  unfold ChainDist.prAt ChainDist.prAt2 ChainDist.pr
  simp only [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v j₁ = false ∨ v j₁ = true := by cases v j₁ <;> simp
  have h₂ : v j₂ = false ∨ v j₂ = true := by cases v j₂ <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    cases y <;> simp [h₁, h₂]

/-- The agreement probability of the two initial coordinates is the sum of the two
diagonal entries of their joint law. -/
theorem ChainDist.prAgree01_eq_diag {k : ℕ} (D : ChainDist k) :
    D.prAgree01 = D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) false false +
      D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) true true := by
  unfold ChainDist.prAgree01 ChainDist.prAt2 ChainDist.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v (chainAlphaIdx 0) = false ∨ v (chainAlphaIdx 0) = true := by
    cases v (chainAlphaIdx 0) <;> simp
  have h₂ : v (chainBetaIdx 0) = false ∨ v (chainBetaIdx 0) = true := by
    cases v (chainBetaIdx 0) <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

/-- With uniform initial coordinates and agreement probability `c`, the joint law of
the two initial coordinates is `c / 2` on the diagonal and `(1 - c) / 2` off it. -/
theorem ChainDist.uniform_pair_joint {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (a b : Bool) :
    D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) a b =
      if a = b then c / 2 else (1 - c) / 2 := by
  have hr0 := D.prAt_eq_sum_prAt2_right (chainAlphaIdx 0) (chainBetaIdx 0) false
  have hr1 := D.prAt_eq_sum_prAt2_right (chainAlphaIdx 0) (chainBetaIdx 0) true
  have hc0 := D.prAt_eq_sum_prAt2_left (chainAlphaIdx 0) (chainBetaIdx 0) false
  have hd := D.prAgree01_eq_diag
  simp only [Fintype.sum_bool] at hr0 hr1 hc0
  rw [hα false] at hr0
  rw [hα true] at hr1
  rw [hβ false] at hc0
  rw [hagree] at hd
  cases a <;> cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte] <;> linarith

/-- The expectation of a function of the two initial coordinates only depends on
their joint law. -/
theorem ChainDist.sum_weight_mul_pair {k : ℕ} (D : ChainDist k)
    (F : Bool → Bool → ℝ) :
    ∑ v, D.w v * F (v (chainAlphaIdx 0)) (v (chainBetaIdx 0)) =
      ∑ g : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d * F g d := by
  simp only [Fintype.sum_bool]
  unfold ChainDist.prAt2 ChainDist.pr
  simp_rw [Finset.sum_mul]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v (chainAlphaIdx 0) = false ∨ v (chainAlphaIdx 0) = true := by
    cases v (chainAlphaIdx 0) <;> simp
  have h₂ : v (chainBetaIdx 0) = false ∨ v (chainBetaIdx 0) = true := by
    cases v (chainBetaIdx 0) <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

/-- Probability, under the extended chain, of an event depending on the two new and
the two old initial coordinates, as a sum over the old pair weighted by the step
kernel. -/
theorem extendChainDist_pr_pair_sum {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (S : Bool → Bool → Bool → Bool → Bool) :
    (extendChainDist D c hc0 hc1).pr (fun v =>
        S (v (chainAlphaIdx 0)) (v (chainBetaIdx 0))
          (v (chainAlphaIdx (Fin.succ 0))) (v (chainBetaIdx (Fin.succ 0)))) =
      ∑ g : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d *
          (∑ a : Bool, ∑ b : Bool,
            if S a b g d then chainStepKernel c a b g d else 0) := by
  have hevent :
      (fun v : Fin (2 * (k + 1) + 2) → Bool =>
        S (v (chainAlphaIdx 0)) (v (chainBetaIdx 0))
          (v (chainAlphaIdx (Fin.succ 0))) (v (chainBetaIdx (Fin.succ 0)))) =
      (fun v => S (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
        ((extensionEquiv k v).1 (chainAlphaIdx 0))
        ((extensionEquiv k v).1 (chainBetaIdx 0))) := by
    funext v
    rw [extensionEquiv_newAlpha, extensionEquiv_newBeta,
      extensionEquiv_oldAlpha, extensionEquiv_oldBeta]
  rw [hevent]
  rw [extendChainDist_pr_eq D c hc0 hc1
    (fun a b old => S a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)))]
  calc
    (∑ old, ∑ a : Bool, ∑ b : Bool,
        if S a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) then
          D.w old * chainStepKernel c a b
            (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) else 0) =
        ∑ old, D.w old *
          (∑ a : Bool, ∑ b : Bool,
            if S a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) then
              chainStepKernel c a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0))
            else 0) := by
      apply Finset.sum_congr rfl
      intro old _
      simp only [Fintype.sum_bool]
      by_cases hTT : S true true (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        by_cases hTF : S true false (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        by_cases hFT : S false true (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        by_cases hFF : S false false (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        simp [hTT, hTF, hFT, hFF] <;> ring
    _ = _ := D.sum_weight_mul_pair (fun g d =>
      ∑ a : Bool, ∑ b : Bool,
        if S a b g d then chainStepKernel c a b g d else 0)

/-- The new coordinate `α₀` of the extended chain is uniform. -/
theorem extendChainDist_prAlpha {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (a : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainAlphaIdx 0) a = 1 / 2 := by
  unfold ChainDist.prAt
  rw [extendChainDist_pr_pair_sum D c hc0 hc1 (fun a' _ _ _ => a' == a)]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases a <;> simp only [Fintype.sum_bool] <;> simp [chainStepKernel] <;> ring

/-- The new coordinate `β₀` of the extended chain is uniform. -/
theorem extendChainDist_prBeta {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (b : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainBetaIdx 0) b = 1 / 2 := by
  unfold ChainDist.prAt
  rw [extendChainDist_pr_pair_sum D c hc0 hc1 (fun _ b' _ _ => b' == b)]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases b <;> simp only [Fintype.sum_bool] <;> simp [chainStepKernel] <;> ring

/-- One extension step sends the agreement probability `c` to `(c ^ 2 + 1) / 2`. -/
theorem extendChainDist_prAgree {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) :
    (extendChainDist D c hc0 hc1).prAgree01 = (c ^ 2 + 1) / 2 := by
  unfold ChainDist.prAgree01
  rw [extendChainDist_pr_pair_sum D c hc0 hc1 (fun a b _ _ => a == b)]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  simp only [Fintype.sum_bool]
  simp [chainStepKernel]
  ring

/-- The joint law of the two new coordinates and the old `α₀`, expanded over the old
pair and the step kernel. -/
theorem extendChainDist_prAt3_new_givenAlpha {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b g : Bool) :
    (extendChainDist D c hc0 hc1).prAt3 (chainAlphaIdx 0) (chainBetaIdx 0)
        (chainAlphaIdx (Fin.succ 0)) a b g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (b' == b) && (g' == g) then
              chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt3] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' b' g' _ => (a' == a) && (b' == b) && (g' == g))

/-- The marginal of the old `α₀` inside the extended chain, expanded over the old
pair and the step kernel. -/
theorem extendChainDist_prAt_newAlphaNext {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (g : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainAlphaIdx (Fin.succ 0)) g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if g' == g then chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ _ g' _ => g' == g)

/-- The joint law of the new `α₀` and the old `α₀`, expanded over the old pair and
the step kernel. -/
theorem extendChainDist_prAt2_newAlpha_alphaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a g : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainAlphaIdx 0)
        (chainAlphaIdx (Fin.succ 0)) a g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (g' == g) then chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' _ g' _ => (a' == a) && (g' == g))

/-- The joint law of the new `β₀` and the old `α₀`, expanded over the old pair and
the step kernel. -/
theorem extendChainDist_prAt2_newBeta_alphaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (b g : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainBetaIdx 0)
        (chainAlphaIdx (Fin.succ 0)) b g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if (b' == b) && (g' == g) then chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ b' g' _ => (b' == b) && (g' == g))

/-- In the extended chain the two new coordinates are conditionally independent
given the old `α₀`. -/
theorem extendChainDist_condIndepGivenAlphaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) :
    (extendChainDist D c hc0 hc1).CondIndepCoords
      (chainAlphaIdx 0) (chainBetaIdx 0) (chainAlphaIdx (Fin.succ 0)) := by
  intro a b g
  rw [extendChainDist_prAt3_new_givenAlpha,
    extendChainDist_prAt_newAlphaNext,
    extendChainDist_prAt2_newAlpha_alphaNext,
    extendChainDist_prAt2_newBeta_alphaNext]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases a <;> cases b <;> cases g <;> simp only [Fintype.sum_bool] <;>
    simp [chainStepKernel] <;> ring

/-- The joint law of the two new coordinates and the old `β₀`, expanded over the old
pair and the step kernel. -/
theorem extendChainDist_prAt3_new_givenBeta {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b d : Bool) :
    (extendChainDist D c hc0 hc1).prAt3 (chainAlphaIdx 0) (chainBetaIdx 0)
        (chainBetaIdx (Fin.succ 0)) a b d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (b' == b) && (d' == d) then
              chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt3] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' b' _ d' => (a' == a) && (b' == b) && (d' == d))

/-- The marginal of the old `β₀` inside the extended chain, expanded over the old
pair and the step kernel. -/
theorem extendChainDist_prAt_newBetaNext {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (d : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainBetaIdx (Fin.succ 0)) d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if d' == d then chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ _ _ d' => d' == d)

/-- The joint law of the new `α₀` and the old `β₀`, expanded over the old pair and
the step kernel. -/
theorem extendChainDist_prAt2_newAlpha_betaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a d : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainAlphaIdx 0)
        (chainBetaIdx (Fin.succ 0)) a d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (d' == d) then chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' _ _ d' => (a' == a) && (d' == d))

/-- The joint law of the new `β₀` and the old `β₀`, expanded over the old pair and
the step kernel. -/
theorem extendChainDist_prAt2_newBeta_betaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (b d : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainBetaIdx 0)
        (chainBetaIdx (Fin.succ 0)) b d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if (b' == b) && (d' == d) then chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ b' _ d' => (b' == b) && (d' == d))

/-- In the extended chain the two new coordinates are conditionally independent
given the old `β₀`. -/
theorem extendChainDist_condIndepGivenBetaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) :
    (extendChainDist D c hc0 hc1).CondIndepCoords
      (chainAlphaIdx 0) (chainBetaIdx 0) (chainBetaIdx (Fin.succ 0)) := by
  intro a b d
  rw [extendChainDist_prAt3_new_givenBeta,
    extendChainDist_prAt_newBetaNext,
    extendChainDist_prAt2_newAlpha_betaNext,
    extendChainDist_prAt2_newBeta_betaNext]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases a <;> cases b <;> cases d <;> simp only [Fintype.sum_bool] <;>
    simp [chainStepKernel] <;> ring

/-- Conditional independence of old coordinates survives the extension. -/
theorem extendChainDist_condIndep_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ j₃ : Fin (2 * k + 2))
    (h : D.CondIndepCoords j₁ j₂ j₃) :
    (extendChainDist D c hc0 hc1).CondIndepCoords
      (oldCoordInNew j₁) (oldCoordInNew j₂) (oldCoordInNew j₃) := by
  intro x₁ x₂ x₃
  rw [extendChainDist_prAt3_old, extendChainDist_prAt_old,
    extendChainDist_prAt2_old, extendChainDist_prAt2_old]
  exact h x₁ x₂ x₃

/-- Independence of old coordinates survives the extension. -/
theorem extendChainDist_indep_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ : Fin (2 * k + 2))
    (h : D.IndepCoords j₁ j₂) :
    (extendChainDist D c hc0 hc1).IndepCoords
      (oldCoordInNew j₁) (oldCoordInNew j₂) := by
  intro x₁ x₂
  rw [extendChainDist_prAt2_old, extendChainDist_prAt_old,
    extendChainDist_prAt_old]
  exact h x₁ x₂

/-- Extending a chain with uniform initial coordinates and agreement probability `c`
again yields a chain with the required independence pattern. -/
theorem extendChainDist_isChain {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) :
    (extendChainDist D c hc0 hc1).IsIndep315Chain := by
  rcases hchain with ⟨hchainα, hchainβ, htop⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact extendChainDist_condIndepGivenAlphaNext D c hc0 hc1 hα hβ hagree
    · have h := extendChainDist_condIndep_old D c hc0 hc1
        (chainAlphaIdx j.castSucc) (chainBetaIdx j.castSucc) (chainAlphaIdx j.succ)
        (hchainα j)
      have h_eq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
      simp only [oldCoordInNew_alpha, oldCoordInNew_beta] at h
      rw [h_eq] at h
      exact h
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact extendChainDist_condIndepGivenBetaNext D c hc0 hc1 hα hβ hagree
    · have h := extendChainDist_condIndep_old D c hc0 hc1
        (chainAlphaIdx j.castSucc) (chainBetaIdx j.castSucc) (chainBetaIdx j.succ)
        (hchainβ j)
      have h_eq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
      simp only [oldCoordInNew_alpha, oldCoordInNew_beta] at h
      rw [h_eq] at h
      exact h
  · have h := extendChainDist_indep_old D c hc0 hc1
      (chainAlphaIdx (Fin.last k)) (chainBetaIdx (Fin.last k)) htop
    have h_eq : (Fin.last k).succ = Fin.last (k + 1) := Fin.ext rfl
    simp only [oldCoordInNew_alpha, oldCoordInNew_beta] at h
    rw [h_eq] at h
    exact h

/-- The exact construction step from the hint to SUV Exercise 315.  A chain
realizing `c` can be extended by one link to realize `(c²+1)/2`.  The new
bottom pair is conditionally independent given either coordinate of the old
bottom pair; all old links are shifted up unchanged. -/
theorem extend_independence_chain {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) :
    ∃ D' : ChainDist (k + 1),
      (∀ a, D'.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D'.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D'.prAgree01 = (c ^ 2 + 1) / 2 ∧ D'.IsIndep315Chain := by
  refine ⟨extendChainDist D c hc0 hc1, ?_, ?_, ?_, ?_⟩
  · exact extendChainDist_prAlpha D c hc0 hc1 hα hβ hagree
  · exact extendChainDist_prBeta D c hc0 hc1 hα hβ hagree
  · exact extendChainDist_prAgree D c hc0 hc1 hα hβ hagree
  · exact extendChainDist_isChain D c hc0 hc1 hα hβ hagree hchain

/-- Every agreement probability `c` in `(1/2, 1)` is reached from some starting
value in `(1/2, 5/8]` by finitely many iterations of `x ↦ (x ^ 2 + 1) / 2`. -/
theorem iterate_reaches (c : ℝ) (h1 : 1 / 2 < c) (h2 : c < 1) :
    ∃ (n : ℕ) (c₀ : ℝ), 1 / 2 < c₀ ∧ c₀ ≤ 5 / 8 ∧
      (fun x => (x ^ 2 + 1) / 2)^[n] c₀ = c := by
  let f : ℝ → ℝ := fun x => (x ^ 2 + 1) / 2
  let a : ℕ → ℝ := fun n => f^[n] (1 / 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have ha_succ (n : ℕ) : a (n + 1) = f (a n) := by
    simp only [a, Function.iterate_succ_apply']
  have ha_bounds : ∀ n, 1 / 2 ≤ a n ∧ a n ≤ 1 := by
    intro n
    induction n with
    | zero => norm_num [a]
    | succ n ih =>
        rw [show n + 1 = n.succ from rfl, ha_succ]
        dsimp [f]
        constructor <;> nlinarith [sq_nonneg (a n), sq_nonneg (a n - 1)]
  have ha_step (n : ℕ) : a n ≤ a (n + 1) := by
    rw [ha_succ]
    dsimp [f]
    nlinarith [sq_nonneg (a n - 1)]
  have ha_mono : Monotone a := monotone_nat_of_le_succ ha_step
  have ha_bdd : BddAbove (Set.range a) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (ha_bounds n).2
  let l : ℝ := ⨆ n, a n
  have hl : Filter.Tendsto a Filter.atTop (nhds l) :=
    tendsto_atTop_ciSup ha_mono ha_bdd
  have hl_shift : Filter.Tendsto (fun n => a (n + 1)) Filter.atTop (nhds l) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hl
  have hl_map : Filter.Tendsto (fun n => f (a n)) Filter.atTop (nhds (f l)) :=
    hf.continuousAt.tendsto.comp hl
  have hfix : f l = l := by
    apply tendsto_nhds_unique hl_map
    convert hl_shift using 1
    ext n
    exact (ha_succ n).symm
  have hl_one : l = 1 := by
    dsimp [f] at hfix
    nlinarith [sq_nonneg (l - 1)]
  rw [hl_one] at hl
  have hex : ∃ n, c ≤ a n := by
    have hev : ∀ᶠ n in Filter.atTop, c < a n := (tendsto_order.1 hl).1 c h2
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    exact ⟨N, (hN N le_rfl).le⟩
  let N := Nat.find hex
  have hN : c ≤ a N := Nat.find_spec hex
  have hN_ne : N ≠ 0 := by
    intro hzero
    have hN' := hN
    rw [hzero] at hN'
    norm_num [a] at hN'
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN_ne
  have hn_lt : a n < c := by
    have hnot : ¬ c ≤ a n := by
      apply Nat.find_min hex
      omega
    exact lt_of_not_ge hnot
  have hc_mem : c ∈ Set.Icc ((f^[n]) (1 / 2)) ((f^[n]) (5 / 8)) := by
    have hfive : (5 / 8 : ℝ) = f (1 / 2) := by
      dsimp [f]
      norm_num
    have hlo : (f^[n]) (1 / 2) = a n := rfl
    have hhi : (f^[n]) (5 / 8) = a N := by
      rw [hfive]
      change f^[n] (f (1 / 2)) = f^[N] (1 / 2)
      rw [hn, Function.iterate_succ_apply]
    rw [hlo, hhi]
    exact ⟨hn_lt.le, hN⟩
  obtain ⟨c₀, hc₀, hc₀eq⟩ :=
    intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 5 / 8)
      (hf.iterate n).continuousOn hc_mem
  refine ⟨n, c₀, ?_, hc₀.2, ?_⟩
  · apply lt_of_le_of_ne hc₀.1
    intro heq
    have hc₀half : c₀ = 1 / 2 := heq.symm
    rw [hc₀half] at hc₀eq
    change a n = c at hc₀eq
    linarith
  · exact hc₀eq

end Kolmogorov
