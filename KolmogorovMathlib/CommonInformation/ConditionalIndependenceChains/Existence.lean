import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import KolmogorovMathlib.CommonInformation.FiniteQuadruple
import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains.ChainDist
import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains.Extension

/-!
# Conditional-independence chains exist at every agreement probability

`exists_indepChain`: for every `c ∈ (0, 1)` there is a finite chain of Boolean random
variables `α₀, …, α_k, β₀, …, β_k` with uniform marginals, the prescribed conditional
independences, and agreement probability `c` — SUV Exercise 315.

`base_chain` settles the base range `c ∈ [3/8, 5/8]` with a chain of length one;
`extend_independence_chain_iterate` iterates the extension step of
`ConditionalIndependenceChains/Extension`, which maps the agreement probability `c` to
`(c² + 1) / 2`, and `exists_indepChain_of_three_eighths_le` covers `[3/8, 1)` by iterating
backwards.  The remaining range follows by symmetry.
-/

namespace Kolmogorov
open Finset
open ChainDist QuadDist

/-- Iterating `extend_independence_chain` realizes every finite forward iterate
of the agreement transformation. -/
theorem extend_independence_chain_iterate {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) (n : ℕ) :
    ∃ (k' : ℕ) (D' : ChainDist k'),
      (∀ a, D'.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D'.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D'.prAgree01 = (fun x => (x ^ 2 + 1) / 2)^[n] c ∧
      D'.IsIndep315Chain := by
  let f : ℝ → ℝ := fun x => (x ^ 2 + 1) / 2
  have hiter_bounds : ∀ m, 0 ≤ f^[m] c ∧ f^[m] c ≤ 1 := by
    intro m
    induction m with
    | zero => simpa [f] using And.intro hc0 hc1
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        dsimp [f]
        constructor <;> nlinarith [sq_nonneg (f^[m] c), sq_nonneg (f^[m] c - 1)]
  induction n with
  | zero =>
      exact ⟨k, D, hα, hβ, by simpa [f] using hagree, hchain⟩
  | succ n ih =>
      obtain ⟨k', D', hα', hβ', hagree', hchain'⟩ := ih
      obtain ⟨D'', hα'', hβ'', hagree'', hchain''⟩ :=
        extend_independence_chain D' (hiter_bounds n).1 (hiter_bounds n).2
          hα' hβ' hagree' hchain'
      refine ⟨k' + 1, D'', hα'', hβ'', ?_, hchain''⟩
      rw [Function.iterate_succ_apply']
      exact hagree''


/-! ### Exercise 315 -/

/-- **Exercise 315, base range.**  For every `c ∈ [3/8, 5/8]` there is a
length-`1` conditional-independence chain with `Pr[α₀ = β₀] = c` and uniform
`α₀, β₀`.  This is the Exercise-314 quadruple reread as a chain, and it
discharges the base of the general statement below. -/
theorem base_chain (c : ℝ) (hc0 : 3 / 8 ≤ c) (hc1 : c ≤ 5 / 8) :
    ∃ D : ChainDist 1,
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D.prAgree01 = c ∧
      D.IsIndep315Chain := by
  obtain ⟨Q, hα, hβ, hγδ, hcg, hcd, hagree, _hjoint⟩ :=
    exists_quadDist_condIndep_uniform_pair c hc0 hc1
  refine ⟨chainOfQuad Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [show (0 : Fin (1 + 1)) = (0 : Fin 2) from rfl, chainOfQuad.idxA0,
      chainOfQuad.prAt0]
    exact hα a
  · intro b
    rw [show (0 : Fin (1 + 1)) = (0 : Fin 2) from rfl, chainOfQuad.idxB0,
      chainOfQuad.prAt2c]
    exact hβ b
  · rw [chainOfQuad.prAgree01_eq]; exact hagree
  · -- `αᵢ ⫫ βᵢ | α_{i+1}` at the single link `i = 0`, i.e. `α₀ ⫫ β₀ | α₁`.
    refine Fin.forall_fin_one.mpr ?_
    change (chainOfQuad Q).CondIndepCoords (0 : Fin 4) (2 : Fin 4) (1 : Fin 4)
    intro v₁ v₂ v₃
    rw [chainOfQuad.prAt3_021, chainOfQuad.prAt1, chainOfQuad.prAt2_01,
      chainOfQuad.prAt2_21]
    exact hcg v₁ v₂ v₃
  · -- `αᵢ ⫫ βᵢ | β_{i+1}` at the single link `i = 0`, i.e. `α₀ ⫫ β₀ | β₁`.
    refine Fin.forall_fin_one.mpr ?_
    change (chainOfQuad Q).CondIndepCoords (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
    intro v₁ v₂ v₃
    rw [chainOfQuad.prAt3_023, chainOfQuad.prAt3c, chainOfQuad.prAt2_03,
      chainOfQuad.prAt2_23]
    exact hcd v₁ v₂ v₃
  · -- Top relation `α₁ ⫫ β₁`.
    change (chainOfQuad Q).IndepCoords (1 : Fin 4) (3 : Fin 4)
    intro v₁ v₂
    rw [chainOfQuad.prAt2_13, chainOfQuad.prAt1, chainOfQuad.prAt3c]
    exact hγδ v₁ v₂


/-- For every agreement probability `c` in `[3/8, 1)` there is a chain distribution with uniform
marginals, that agreement probability, and the conditional independence pattern of the chain. -/
theorem exists_indepChain_of_three_eighths_le (c : ℝ) (hc0 : 3 / 8 ≤ c) (hc1 : c < 1) :
    ∃ (k : ℕ) (D : ChainDist k),
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D.prAgree01 = c ∧
      D.IsIndep315Chain := by
  by_cases hhi : c ≤ 5 / 8
  · -- Base range `c ∈ [3/8, 5/8]`: the Exercise-314 quadruple as a chain.
    obtain ⟨D, h1, h2, h3, h4⟩ := base_chain c hc0 hhi
    exact ⟨1, D, h1, h2, h3, h4⟩
  · -- `c ∈ (5/8, 1)`: pull `c` back to the base interval and extend the
    -- resulting chain by the required number of source construction steps.
    have hc_half : 1 / 2 < c := by
      have : 5 / 8 < c := lt_of_not_ge hhi
      norm_num at this ⊢
      linarith
    obtain ⟨n, c₀, hc₀half, hc₀base, hciterate⟩ := iterate_reaches c hc_half hc1
    have hc₀low : 3 / 8 ≤ c₀ := by linarith
    obtain ⟨D, hα, hβ, hagree, hchain⟩ := base_chain c₀ hc₀low hc₀base
    obtain ⟨k', D', hα', hβ', hagree', hchain'⟩ :=
      extend_independence_chain_iterate D (by linarith : 0 ≤ c₀) (by linarith : c₀ ≤ 1)
        hα hβ hagree hchain n
    rw [hciterate] at hagree'
    exact ⟨k', D', hα', hβ', hagree', hchain'⟩

/-- For every `c ∈ (0, 1)` there is a finite chain `α₀,…,α_k, β₀,…,β_k` of Boolean random
variables with uniform `α₀, β₀`, `Pr[α₀ = β₀] = c`, and the full chain of
conditional-independence relations `IsIndep315Chain`. The base range `c ∈ [3/8, 5/8]` is
proved (via `base_chain`, i.e. Theorem 217 / Exercise 314), the high range by iterating
`extend_independence_chain`, and the low range by the proved `α₀`-inversion construction.
SUV Exercise 315. -/
theorem exists_indepChain (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ (k : ℕ) (D : ChainDist k),
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D.prAgree01 = c ∧
      D.IsIndep315Chain := by
  by_cases hlo : 3 / 8 ≤ c
  · exact exists_indepChain_of_three_eighths_le c hlo hc1
  · have hc_1 : 3 / 8 ≤ 1 - c := by linarith
    have hc_2 : 1 - c < 1 := by linarith
    obtain ⟨k, D, h1, h2, h3, h4⟩ := exists_indepChain_of_three_eighths_le (1 - c) hc_1 hc_2
    obtain ⟨D', h1', h2', h3', h4'⟩ := invert_chain D h1 h2 h3 h4
    rw [sub_sub_cancel] at h3'
    exact ⟨k, D', h1', h2', h3', h4'⟩

end Kolmogorov
