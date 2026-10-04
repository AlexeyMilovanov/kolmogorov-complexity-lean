/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.ArtificialIndependence
import KolmogorovMathlib.InformationInequalities.ConditionallyIndependent
import KolmogorovMathlib.InformationInequalities.Ingleton
import KolmogorovMathlib.Entropy.Inequalities

/-!
# Non-Shannon inequalities

SUV Section 10.13, pp. 343–349.

Theorem 218 (Makarychev, Makarychev, Romashchenko and Vereshchagin) is an entropy inequality
for five variables that is not a consequence of the basic inequalities:
`I(α:β) ≤ I(α:β|γ) + I(α:β|δ) + I(γ:δ) + I(α:β|ε) + I(α:ε|β) + I(β:ε|α)`.
The first three terms on the right are Ingleton's; the last three form
`W(α, β, ε) = I(α:β|ε) + I(α:ε|β) + I(β:ε|α)` (`pairwiseCondInfoSum`).  Specialising and
conditioning it shows that the special extreme ray of Section 10.11 lies outside the closure of
the entropy region, so for four variables the basic inequalities do not describe that closure.

The section proves Theorem 218 by "artificial independence" — resample so that `⟨γ, δ⟩` and
`ε` are independent given `⟨α, β⟩`, which leaves every term unchanged — and extracts from it a
general deduction rule.  The resampling construction, the helpers and Theorem 218 itself are
in `KolmogorovMathlib.InformationInequalities.ArtificialIndependence`; this module holds the
consequences.  A second proof uses the Ahlswede–Körner theorem (Theorem 220), which
the book states **without proof**; only the steps of that proof that do not use it are here.
Theorem 219 and Problem 303 are about extracting common information when `W = 0`.

Three results of the section are archived, with their statements, in
`docs/ARCHIVED_TARGETS.md`: Theorem 220, Problem 304 (its two-variable case, which was derived
from it) and the Kolmogorov-complexity analogue of Theorem 219, which the book only cites.

Sign convention of `LinearForm`: `∑_I λ_I · (quantity of I) ≤ 0`; `nonShannonForm` is the
right-hand side of Theorem 218 subtracted from its left-hand side, expanded into entropies
(`α, β, γ, δ, ε` are the indices `0, …, 4`).  The book's proof of Theorem 218 is announced as
"we will prove Theorem 208 in the general case" (p. 346), a misprint for Theorem 218.
-/

namespace Kolmogorov

open Finset

/-! ### Subtuple entropies of small index sets, and the table sum -/

section Subtuples

variable {Ω : Type} [Fintype Ω] {α : Type} [DecidableEq α] {n : ℕ}

/-- `H(ξ_{I ∪ J ∪ K}) = H((ξ_I, ξ_J), ξ_K)`. -/
private theorem entropySub_union_union (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (I J K : Finset (Fin n)) :
    entropySub μ X (I ∪ J ∪ K)
      = entropy μ (pairRV (pairRV (subtuple X I) (subtuple X J)) (subtuple X K)) := by
  rw [entropySub_union]
  set g : (↥(I ∪ J) → α) → (↥I → α) × (↥J → α) :=
    fun h => (fun i : ↥I => h ⟨i.1, Finset.mem_union_left J i.2⟩,
      fun j : ↥J => h ⟨j.1, Finset.mem_union_right I j.2⟩) with hg_def
  have hg : Function.Injective g := by
    intro h₁ h₂ hh
    funext i
    rcases Finset.mem_union.1 i.2 with hi | hi
    · exact congrFun (congrArg Prod.fst hh) ⟨i.1, hi⟩
    · exact congrFun (congrArg Prod.snd hh) ⟨i.1, hi⟩
  symm
  exact entropy_eq_of_comp μ (pairRV (subtuple X (I ∪ J)) (subtuple X K))
    (pairRV (pairRV (subtuple X I) (subtuple X J)) (subtuple X K)) (Prod.map g id)
    (hg.prodMap Function.injective_id) fun _ => rfl

omit [DecidableEq α] in
/-- Reading the value at `i` off a function on `{i}` is injective. -/
private theorem eval_singleton_injective (i : Fin n) :
    Function.Injective fun h : ↥({i} : Finset (Fin n)) → α =>
      h ⟨i, Finset.mem_singleton_self i⟩ := by
  intro h₁ h₂ hh
  funext ⟨k, hk⟩
  obtain rfl := Finset.mem_singleton.1 hk
  exact hh

/-- `H(ξ_{\{i\}}) = H(ξ_i)`. -/
private theorem entropySub_singleton (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (i : Fin n) :
    entropySub μ X {i} = entropy μ (X i) :=
  (entropy_eq_of_comp μ (subtuple X {i}) (X i) _ (eval_singleton_injective i) fun _ => rfl).symm

/-- `H(ξ_{\{i, j\}}) = H(ξ_i, ξ_j)`; `i = j` is allowed. -/
private theorem entropySub_pair (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (i j : Fin n) :
    entropySub μ X {i, j} = entropy μ (pairRV (X i) (X j)) := by
  rw [Finset.insert_eq, entropySub_union]
  symm
  exact entropy_eq_of_comp μ (pairRV (subtuple X {i}) (subtuple X {j})) (pairRV (X i) (X j)) _
    ((eval_singleton_injective i).prodMap (eval_singleton_injective j)) fun _ => rfl

/-- `H(ξ_{\{i, j, k\}}) = H((ξ_i, ξ_j), ξ_k)`; coincidences among `i, j, k` are allowed. -/
private theorem entropySub_triple (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (i j k : Fin n) :
    entropySub μ X {i, j, k} = entropy μ (pairRV (pairRV (X i) (X j)) (X k)) := by
  rw [Finset.insert_eq, Finset.insert_eq, ← Finset.union_assoc, entropySub_union_union]
  symm
  exact entropy_eq_of_comp μ
    (pairRV (pairRV (subtuple X {i}) (subtuple X {j})) (subtuple X {k}))
    (pairRV (pairRV (X i) (X j)) (X k)) _
    (((eval_singleton_injective i).prodMap (eval_singleton_injective j)).prodMap
      (eval_singleton_injective k)) fun _ => rfl

/-- Theorem 218 for the subtuples `ξ_a, ξ_b, ξ_c, ξ_d, ξ_e` of a tuple, every term expanded
into subtuple entropies (the index sets are the ones whose entropies `entropySub_pair` and
`entropySub_triple` identify with nested pairs). -/
private theorem nonShannon_entropySub (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ)
    (a b c d e : Fin n) :
    entropySub μ X {a} + entropySub μ X {b} - entropySub μ X {a, b}
      ≤ (entropySub μ X {a, c} + entropySub μ X {b, c} - entropySub μ X {c}
            - entropySub μ X {a, b, c})
        + (entropySub μ X {a, d} + entropySub μ X {b, d} - entropySub μ X {d}
            - entropySub μ X {a, b, d})
        + (entropySub μ X {c} + entropySub μ X {d} - entropySub μ X {c, d})
        + (entropySub μ X {a, e} + entropySub μ X {b, e} - entropySub μ X {e}
            - entropySub μ X {a, b, e})
        + (entropySub μ X {a, b} + entropySub μ X {b, e} - entropySub μ X {b}
            - entropySub μ X {a, b, e})
        + (entropySub μ X {a, b} + entropySub μ X {a, e} - entropySub μ X {a}
            - entropySub μ X {a, b, e}) := by
  simp only [entropySub_singleton, entropySub_pair, entropySub_triple]
  have h := mutualInfo_le_nonShannon μ (X a) (X b) (X c) (X d) (X e)
  simp only [condMutualInfo_eq, mutualInfo] at h
  linarith [entropy_pairRV_comm μ (X b) (X e), entropy_pairRV_comm μ (X a) (X b),
    entropy_pairRV_comm μ (X a) (X e), entropy_pairRV_swap_right μ (X a) (X b) (X e),
    entropy_pair_rotate μ (X a) (X b) (X e)]

end Subtuples

/-- **Theorem 218**, as a linear form: the non-Shannon inequality, expanded into entropies of
subtuples of `(α, β, γ, δ, ε)`, is valid for entropies.  SUV Theorem 218, p. 344. -/
theorem holdsForEntropies_nonShannonForm : HoldsForEntropies nonShannonForm := by
  intro Ω _ μ X
  unfold LinearForm.evalEntropy nonShannonForm
  rw [LinearForm.sum_ofTable_mul _ _ (by decide)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h := nonShannon_entropySub μ X 0 1 2 3 4
  linarith

/-! ### Consequences of Theorem 218 -/

/-- **The conditional Ingleton inequality.**  If `W(α, β, ε) = 0` for some `ε`, then
`I(α:β) ≤ I(α:β|γ) + I(α:β|δ) + I(γ:δ)` for all `γ, δ`.  (Taking `α = β = ε = ξ` gives
`H(ξ) ≤ H(ξ|γ) + H(ξ|δ) + I(γ:δ)`, which is Problem 296.)
SUV Section 10.13, p. 344 (unnumbered). -/
theorem mutualInfo_le_ingleton_of_pairwiseCondInfoSum_eq_zero {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (A B E : Ω → ℕ) (hW : pairwiseCondInfoSum μ A B E = 0)
    (C D : Ω → ℕ) :
    mutualInfo μ A B ≤ condMutualInfo μ A B C + condMutualInfo μ A B D + mutualInfo μ C D := by
  have h := mutualInfo_le_nonShannon μ A B C D E
  unfold pairwiseCondInfoSum at hW
  linarith

/-- No point of the special ray other than the origin lies in the closure of the entropy region
for four variables: apply the conditional Ingleton inequality with `α = ξ₃`, `β = ξ₄`,
`γ = ε = ξ₁`, `δ = ξ₂`.  SUV Section 10.13, p. 344 (unnumbered). -/
theorem smul_specialRay_not_mem_closure_entropyRegion {t : ℝ} (ht : 0 < t) :
    t • specialRay ∉ closure (entropyRegion 4) := by
  -- the four-variable inequality obtained from Theorem 218 with `α = ξ₃, β = ξ₄, γ = ε = ξ₁,
  -- δ = ξ₂`, as a continuous linear functional that is `≤ 0` on the entropy region
  set φ : (Finset (Fin 4) → ℝ) → ℝ := fun v =>
    v {2} + v {3} - v {2, 3}
      - ((v {2, 0} + v {3, 0} - v {0} - v {2, 3, 0})
        + (v {2, 1} + v {3, 1} - v {1} - v {2, 3, 1})
        + (v {0} + v {1} - v {0, 1})
        + (v {2, 0} + v {3, 0} - v {0} - v {2, 3, 0})
        + (v {2, 3} + v {3, 0} - v {3} - v {2, 3, 0})
        + (v {2, 3} + v {2, 0} - v {2} - v {2, 3, 0})) with hφ
  have hcont : Continuous φ := by
    simp only [hφ]
    fun_prop
  have hclosed : IsClosed {v | φ v ≤ 0} := isClosed_le hcont continuous_const
  have hsub : entropyRegion 4 ⊆ {v | φ v ≤ 0} := by
    rintro v ⟨m, μ, X, rfl⟩
    have h := nonShannon_entropySub μ X 2 3 0 1 0
    simp only [Set.mem_ofPred_eq, hφ, entropyVector]
    linarith
  intro hmem
  have hle : φ (t • specialRay) ≤ 0 := closure_minimal hsub hclosed hmem
  simp +decide [hφ, specialRay, LinearForm.ofTable] at hle
  linarith

/-- For four variables the closure of the entropy region is strictly smaller than the cone of
basic inequalities: the special ray lies in the cone but not in the closure.  The basic cone is
an upper bound for the closure that is not exact.
SUV Section 10.11, p. 338, and Section 10.13, p. 344 (unnumbered). -/
theorem closure_entropyRegion_four_ne_basicCone : closure (entropyRegion 4) ≠ basicCone 4 := by
  intro h
  have h1 := smul_specialRay_not_mem_closure_entropyRegion (t := 1) one_pos
  rw [one_smul, h] at h1
  exact h1 specialRay_mem_basicCone

/-! ### The cone of basic inequalities and the lifted special ray -/

section Cone

variable {n : ℕ}

/-- Every generator of the Shannon cone is non-positive at every point of the cone of basic
inequalities (the sum runs over the non-empty index sets, and `v ∅ = 0` in the cone).
SUV Section 10.11, p. 338. -/
private theorem sum_generator_mul_nonpos {v : Finset (Fin n) → ℝ} (hv : v ∈ basicCone n)
    {g : LinearForm n} (hg : g ∈ shannonGenerators n) :
    ∑ I ∈ nonemptyParts n, g I * v I ≤ 0 := by
  obtain ⟨h0, -, hmono, hsub⟩ := hv
  have hv0 : ∀ T : Finset (Fin n), (if T.Nonempty then v T else 0) = v T := by
    intro T
    split_ifs with h
    · rfl
    · rw [Finset.not_nonempty_iff_eq_empty.1 h, h0]
  rcases hg with ⟨I, J, K, rfl⟩ | ⟨I, J, rfl⟩
  · simp only [basicInequality, add_mul, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_nonemptyParts,
      hv0]
    have h1 := hmono K ((I ∪ K) ∩ (J ∪ K)) fun x hx => by simp [hx]
    have h2 := hsub (I ∪ K) (J ∪ K)
    have h3 : (I ∪ K) ∪ (J ∪ K) = I ∪ J ∪ K := by
      ext x
      simp only [Finset.mem_union]
      tauto
    rw [h3] at h2
    linarith
  · simp only [monotonicityForm, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', mem_nonemptyParts, hv0]
    have := hmono I (I ∪ J) Finset.subset_union_left
    linarith

/-- The special ray as a point of the five-variable cone: the variables `α, β, γ, δ, ε` of
Theorem 218 (indices `0, …, 4`) are read as `ξ₃, ξ₄, ξ₁, ξ₂, ξ₁` (indices `2, 3, 0, 1, 0` of
the ray), so that `ε = γ`. -/
private def liftedSpecialRay : Finset (Fin 5) → ℝ :=
  fun I => specialRay (I.image ![2, 3, 0, 1, 0])

/-- The lifted special ray satisfies all basic inequalities for five variables. -/
private theorem liftedSpecialRay_mem_basicCone : liftedSpecialRay ∈ basicCone 5 := by
  obtain ⟨h0, hnn, hmono, hsub⟩ := specialRay_mem_basicCone
  refine ⟨?_, fun I => hnn _, fun I J hIJ => hmono _ _ (Finset.image_subset_image hIJ),
    fun I J => ?_⟩
  · simp [liftedSpecialRay, h0]
  · unfold liftedSpecialRay
    rw [Finset.image_union]
    have h1 := hmono _ _ (Finset.image_inter_subset ![2, 3, 0, 1, 0] I J)
    have h2 := hsub (I.image ![2, 3, 0, 1, 0]) (J.image ![2, 3, 0, 1, 0])
    linarith

/-- The non-Shannon form takes the value `1 > 0` at the lifted special ray. -/
private theorem sum_nonShannonForm_mul_liftedSpecialRay :
    ∑ I ∈ nonemptyParts 5, nonShannonForm I * liftedSpecialRay I = 1 := by
  unfold nonShannonForm
  rw [LinearForm.sum_ofTable_mul _ _ (by decide)]
  simp +decide [liftedSpecialRay, specialRay, LinearForm.ofTable, Finset.image_insert,
    Finset.image_singleton]
  norm_num

end Cone

/-- The inequality of Theorem 218 is not a consequence of the basic inequalities: it is not of
Shannon type.  The special ray satisfies all basic inequalities but violates it.
SUV Section 10.13, p. 344 (unnumbered). -/
theorem not_isShannonType_nonShannonForm : ¬ IsShannonType nonShannonForm := by
  rintro ⟨m, g, c, hc, hg, hf⟩
  have h1 := sum_nonShannonForm_mul_liftedSpecialRay
  have h2 : ∑ I ∈ nonemptyParts 5, nonShannonForm I * liftedSpecialRay I
      = ∑ k, c k * ∑ I ∈ nonemptyParts 5, g k I * liftedSpecialRay I := by
    rw [Finset.sum_congr rfl fun I hI => by rw [hf I (mem_nonemptyParts.1 hI)]]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have h3 : ∑ k, c k * ∑ I ∈ nonemptyParts 5, g k I * liftedSpecialRay I ≤ 0 :=
    Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hc k)
      (sum_generator_mul_nonpos liftedSpecialRay_mem_basicCone (hg k))
  linarith

/-! ### Theorem 219 and Problem 303 -/

section CommonInformation

variable {Ω : Type} [Fintype Ω]

/-- `W(α, β, γ) = 0` forces each of its three non-negative summands to vanish. -/
private theorem condMutualInfo_eq_zero_of_pairwiseCondInfoSum_eq_zero (μ : FiniteProbSpace Ω)
    (A B C : Ω → ℕ) (hW : pairwiseCondInfoSum μ A B C = 0) :
    condMutualInfo μ A B C = 0 ∧ condMutualInfo μ A C B = 0 ∧ condMutualInfo μ B C A = 0 := by
  unfold pairwiseCondInfoSum at hW
  have h1 := condMutualInfo_nonneg μ A B C
  have h2 := condMutualInfo_nonneg μ A C B
  have h3 := condMutualInfo_nonneg μ B C A
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A variable determined by `α` and by `β` is determined by `γ` as soon as `I(α:β|γ) = 0`:
the conditional Problem 296 bounds `H(ξ|γ)` by `H(ξ|α,γ) + H(ξ|β,γ) + I(α:β|γ)`, and all
three terms vanish.  SUV Problem 303(b), hint, pp. 345–346. -/
private theorem condEntropy_eq_zero_of_condMutualInfo_eq_zero (μ : FiniteProbSpace Ω)
    (X A B C : Ω → ℕ) (hA : condEntropy μ X A = 0) (hB : condEntropy μ X B = 0)
    (hAB : condMutualInfo μ A B C = 0) : condEntropy μ X C = 0 := by
  have h := condEntropy_le_condEntropy_pairRV_add μ X A B C
  have h1 := condEntropy_pairRV_left_le μ X A C
  have h2 := condEntropy_pairRV_left_le μ X B C
  have h0 := condEntropy_nonneg μ X C
  linarith

/-- If `⟨α, β⟩` is independent of `γ` given `ξ`, then so are `α` and `β` separately:
`I(α:γ|ξ) ≤ I(⟨α,β⟩:γ|ξ)` and `I(β:γ|ξ) ≤ I(⟨β,α⟩:γ|ξ) = I(⟨α,β⟩:γ|ξ)`.
SUV Problem 303(b), hint, pp. 345–346. -/
private theorem condMutualInfo_eq_zero_of_pairRV_eq_zero (μ : FiniteProbSpace Ω)
    (A B C X : Ω → ℕ) (h : condMutualInfo μ (pairRV A B) C X = 0) :
    condMutualInfo μ A C X = 0 ∧ condMutualInfo μ B C X = 0 := by
  have hA := condMutualInfo_le_condMutualInfo_pairRV_left μ A B C X
  have hB := condMutualInfo_le_condMutualInfo_pairRV_left μ B A C X
  have hBA : condMutualInfo μ (pairRV B A) C X = condMutualInfo μ (pairRV A B) C X := by
    simp only [condMutualInfo_eq]
    have e1 : entropy μ (pairRV (pairRV B A) X) = entropy μ (pairRV (pairRV A B) X) :=
      entropy_eq_of_comp μ _ _ (fun p => ((p.1.2, p.1.1), p.2))
        (by rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h; simp only [Prod.mk.injEq] at h ⊢; tauto)
        fun _ => rfl
    have e2 : entropy μ (pairRV (pairRV (pairRV B A) C) X)
        = entropy μ (pairRV (pairRV (pairRV A B) C) X) :=
      entropy_eq_of_comp μ _ _ (fun p => (((p.1.1.2, p.1.1.1), p.1.2), p.2))
        (by rintro ⟨⟨⟨a, b⟩, c⟩, d⟩ ⟨⟨⟨a', b'⟩, c'⟩, d'⟩ h
            simp only [Prod.mk.injEq] at h ⊢; tauto)
        fun _ => rfl
    linarith
  exact ⟨le_antisymm (by linarith) (condMutualInfo_nonneg μ A C X),
    le_antisymm (by linarith) (condMutualInfo_nonneg μ B C X)⟩

/-- The core of Problem 303(b).  If `ξ` is determined by `α` and by `β`, the pair `⟨α, β⟩` is
independent of `γ` given `ξ`, and `W(α, β, γ) = 0`, then `α` and `β` are independent given
`ξ`.  The chain of the hint: `I(α:β) − I(α:β|ξ) = I(⟨α,β⟩:ξ) ≥ I(⟨α,β⟩:γ) = I(α:β)`, where
the first equality uses `H(ξ|α) = H(ξ|β) = 0`, the inequality uses `I(⟨α,β⟩:γ|ξ) = 0`, and
the last equality uses `W = 0`.  SUV Problem 303(b), hint, pp. 345–346. -/
private theorem condMutualInfo_eq_zero_of_double_markov (μ : FiniteProbSpace Ω)
    (A B C X : Ω → ℕ) (hA : condEntropy μ X A = 0) (hB : condEntropy μ X B = 0)
    (hC : condMutualInfo μ (pairRV A B) C X = 0) (hABC : condMutualInfo μ A B C = 0)
    (hACB : condMutualInfo μ A C B = 0) (hBCA : condMutualInfo μ B C A = 0) :
    condMutualInfo μ A B X = 0 := by
  have h1 := mutualInfo_le_mutualInfo_of_condMutualInfo_eq_zero μ (pairRV A B) X C hC
  have h2 := mutualInfo_pairRV_eq_add_condMutualInfo μ A B X
  have h3 := mutualInfo_pairRV_eq_add_condMutualInfo μ A B C
  have h4 := condMutualInfo_nonneg μ A B X
  have h5 := condMutualInfo_nonneg μ B X A
  have h6 := condMutualInfo_nonneg μ A X B
  have e1 := entropy_le_entropy_pairRV_left μ (pairRV A B) X
  have e2 := entropy_pair_rotate μ A B X
  have e3 := entropy_pair_rotate μ A B C
  have e4 := entropy_pairRV_swap_right μ A X B
  have e5 := entropy_pairRV_swap_right μ A C B
  have e6 := entropy_pairRV_comm μ A X
  have e7 := entropy_pairRV_comm μ B X
  have e8 := entropy_pairRV_comm μ A B
  have e9 := entropy_pairRV_comm μ A C
  have e10 := entropy_pairRV_comm μ B C
  have e11 := entropy_pairRV_comm μ C X
  simp only [mutualInfo, condMutualInfo_eq, condEntropy_eq_sub] at *
  linarith

end CommonInformation

section DoubleMarkov

variable {Ω : Type} [Fintype Ω]

/-- Two values of `α` are *adjacent* when they share a value of `β` of positive joint
probability: an edge of the bipartite support graph of the pair `(α, β)`.  The connected
components of this graph are the blocks of the block-diagonal structure of the proof of
Theorem 219.  SUV p. 345. -/
private def adjacent (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (a a' : ℕ) : Prop :=
  ∃ b, 0 < μ.dist (pairRV A B) (a, b) ∧ 0 < μ.dist (pairRV A B) (a', b)

open Classical in
/-- The least element of the connected component of `a` in the support graph of `(α, β)`. -/
private noncomputable def componentOf (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (a : ℕ) : ℕ :=
  Nat.find (⟨a, Relation.EqvGen.refl _⟩ : ∃ a', Relation.EqvGen (adjacent μ A B) a a')

/-- The block number `ξ = componentOf (α)`: the common-information variable of Problem 303. -/
private noncomputable def blockRV (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (ω : Ω) : ℕ :=
  componentOf μ A B (A ω)

private theorem eqvGen_adjacent_symm (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (a a' : ℕ)
    (h : Relation.EqvGen (adjacent μ A B) a a') : Relation.EqvGen (adjacent μ A B) a' a :=
  Relation.EqvGen.symm a a' h

private theorem componentOf_eq (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (a a' : ℕ)
    (h : Relation.EqvGen (adjacent μ A B) a a') :
    componentOf μ A B a = componentOf μ A B a' := by
  have H1 : ∀ x, Relation.EqvGen (adjacent μ A B) a x ↔ Relation.EqvGen (adjacent μ A B) a' x := by
    intro x
    constructor
    · intro hx
      exact Relation.EqvGen.trans _ _ _ (eqvGen_adjacent_symm μ A B a a' h) hx
    · intro hx
      exact Relation.EqvGen.trans _ _ _ h hx
  unfold componentOf
  congr 1
  ext x
  exact H1 x

open Classical in
private noncomputable def componentByB (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (b : ℕ) : ℕ :=
  if h : ∃ ω, B ω = b ∧ 0 < μ.prob ω
  then componentOf μ A B (A h.choose)
  else 0

/-- On the support, the block number is also a function of `β`: `A ω` and any `a` with
`(a, B ω)` of positive probability are adjacent, so they have the same component. -/
private theorem condEntropy_blockRV_right (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) :
    condEntropy μ (blockRV μ A B) B = 0 := by
  rw [condEntropy_eq_zero_iff]
  use componentByB μ A B
  rw [FiniteProbSpace.probOf_eq_one_iff]
  intro ω hprob
  have hmem : blockRV μ A B ω = componentByB μ A B (B ω) := by
    unfold blockRV componentByB
    have hex : ∃ ω', B ω' = B ω ∧ 0 < μ.prob ω' := ⟨ω, rfl, hprob⟩
    rw [dite_eq_left hex]
    apply componentOf_eq
    apply Relation.EqvGen.rel
    use B ω
    constructor
    · rw [FiniteProbSpace.dist_pos_iff]
      use ω
      exact ⟨rfl, hprob⟩
    · rw [FiniteProbSpace.dist_pos_iff]
      use hex.choose
      exact ⟨by change (A hex.choose, B hex.choose) = (A hex.choose, B ω); rw [hex.choose_spec.1],
        hex.choose_spec.2⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hmem⟩

/-- The two ways of conditioning a joint value `(a, b, c)` differ only by the probability of
the conditioning fibre. -/
private theorem condDist_pair_mul_dist_eq (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (a b c : ℕ) (ha : 0 < μ.dist A a) (hb : 0 < μ.dist B b) :
    μ.condDist (pairRV B C) (valueEvent A a) (b, c) * μ.dist A a =
      μ.condDist (pairRV A C) (valueEvent B b) (a, c) * μ.dist B b := by
  have hevent :
      ((valueEvent A a).filter fun ω => pairRV B C ω = (b, c)) =
        ((valueEvent B b).filter fun ω => pairRV A C ω = (a, c)) := by
    ext ω
    simp only [valueEvent, Finset.mem_filter, Finset.mem_univ, true_and, pairRV,
      Prod.mk.injEq]
    tauto
  unfold FiniteProbSpace.condDist
  rw [hevent]
  change μ.probOf _ / μ.dist A a * μ.dist A a =
    μ.probOf _ / μ.dist B b * μ.dist B b
  rw [div_mul_cancel₀ _ ha.ne', div_mul_cancel₀ _ hb.ne']

/-- Multiplying a conditional probability by the probability of its conditioning fibre gives
the corresponding joint probability. -/
private theorem condDist_mul_dist_eq_dist_pair (μ : FiniteProbSpace Ω) (A B : Ω → ℕ)
    (a b : ℕ) (ha : 0 < μ.dist A a) :
    μ.condDist B (valueEvent A a) b * μ.dist A a = μ.dist (pairRV A B) (a, b) := by
  have hevent : ((valueEvent A a).filter fun ω => B ω = b) =
      Finset.univ.filter fun ω => pairRV A B ω = (a, b) := by
    ext ω
    simp only [valueEvent, Finset.mem_filter, Finset.mem_univ, true_and, pairRV,
      Prod.mk.injEq]
  unfold FiniteProbSpace.condDist FiniteProbSpace.dist
  rw [hevent]
  change μ.probOf _ / μ.dist A a * μ.dist A a = _
  exact div_mul_cancel₀ _ ha.ne'

/-- Under the two Markov assumptions, the conditional law of `C` computed from either endpoint
of a positive support edge `(a, b)` is the same. -/
private theorem condDist_eq_on_support_edge (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (hBC : condMutualInfo μ B C A = 0) (hAC : condMutualInfo μ A C B = 0)
    (a b : ℕ) (hab : 0 < μ.dist (pairRV A B) (a, b)) (c : ℕ) :
    μ.condDist C (valueEvent A a) c = μ.condDist C (valueEvent B b) c := by
  obtain ⟨ω, hω, hp⟩ := (μ.dist_pos_iff (pairRV A B) (a, b)).mp hab
  have hAa : 0 < μ.dist A a :=
    (μ.dist_pos_iff A a).mpr ⟨ω, congrArg Prod.fst hω, hp⟩
  have hBb : 0 < μ.dist B b :=
    (μ.dist_pos_iff B b).mpr ⟨ω, congrArg Prod.snd hω, hp⟩
  have h1 := (condMutualInfo_eq_zero_iff μ B C A).mp hBC a hAa b c
  have h2 := (condMutualInfo_eq_zero_iff μ A C B).mp hAC b hBb a c
  have h3 := condDist_pair_mul_dist_eq μ A B C a b c hAa hBb
  have h4 := condDist_mul_dist_eq_dist_pair μ A B a b hAa
  have h5 := condDist_mul_dist_eq_dist_pair μ B A b a hBb
  have hswap : μ.dist (pairRV B A) (b, a) = μ.dist (pairRV A B) (a, b) := by
    rw [μ.dist_pairRV, μ.dist_pairRV]
    congr 1
    ext x
    simp [and_comm]
  rw [hswap] at h5
  rw [h1, h2] at h3
  have h3' : μ.dist (pairRV A B) (a, b) * μ.condDist C (valueEvent A a) c =
      μ.dist (pairRV A B) (a, b) * μ.condDist C (valueEvent B b) c := by
    calc
      _ = (μ.condDist B (valueEvent A a) b * μ.dist A a) *
          μ.condDist C (valueEvent A a) c := by rw [h4]
      _ = μ.condDist B (valueEvent A a) b * μ.condDist C (valueEvent A a) c *
          μ.dist A a := by ring
      _ = μ.condDist A (valueEvent B b) a * μ.condDist C (valueEvent B b) c *
          μ.dist B b := h3
      _ = (μ.condDist A (valueEvent B b) a * μ.dist B b) *
          μ.condDist C (valueEvent B b) c := by ring
      _ = _ := by rw [h5]
  exact mul_left_cancel₀ hab.ne' h3'

/-- Every value belongs to the equivalence class whose least representative is `componentOf`. -/
private theorem eqvGen_componentOf (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (a : ℕ) :
    Relation.EqvGen (adjacent μ A B) a (componentOf μ A B a) := by
  classical
  unfold componentOf
  exact Nat.find_spec (⟨a, Relation.EqvGen.refl _⟩ :
    ∃ a', Relation.EqvGen (adjacent μ A B) a a')

/-- Values with the same component number are connected in the support graph. -/
private theorem eqvGen_of_componentOf_eq (μ : FiniteProbSpace Ω) (A B : Ω → ℕ)
    (a a' : ℕ) (h : componentOf μ A B a = componentOf μ A B a') :
    Relation.EqvGen (adjacent μ A B) a a' := by
  exact Relation.EqvGen.trans _ (componentOf μ A B a) _ (eqvGen_componentOf μ A B a)
    (h ▸ eqvGen_adjacent_symm μ A B a' (componentOf μ A B a')
      (eqvGen_componentOf μ A B a'))

/-- The conditional law of `C` is constant on every connected component of the support graph. -/
private theorem condDist_eq_of_eqvGen (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (hBC : condMutualInfo μ B C A = 0) (hAC : condMutualInfo μ A C B = 0)
    (a a' : ℕ) (h : Relation.EqvGen (adjacent μ A B) a a') (c : ℕ) :
    μ.condDist C (valueEvent A a) c = μ.condDist C (valueEvent A a') c := by
  induction h with
  | rel x y hxy =>
      obtain ⟨b, hxb, hyb⟩ := hxy
      exact (condDist_eq_on_support_edge μ A B C hBC hAC x b hxb c).trans
        (condDist_eq_on_support_edge μ A B C hBC hAC y b hyb c).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The joint distribution of the block number and `A` is supported on the graph of
`componentOf`. -/
private theorem dist_blockRV_pair (μ : FiniteProbSpace Ω) (A B : Ω → ℕ) (x a : ℕ) :
    μ.dist (pairRV (blockRV μ A B) A) (x, a) =
      if componentOf μ A B a = x then μ.dist A a else 0 := by
  by_cases h : componentOf μ A B a = x
  · rw [ite_eq_left h]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairRV, blockRV,
      Prod.mk.injEq]
    constructor
    · exact fun hω => hω.2
    · intro hω
      exact ⟨hω ▸ h, hω⟩
  · rw [ite_eq_right h]
    unfold FiniteProbSpace.dist
    have hempty : (Finset.univ.filter fun ω =>
        pairRV (blockRV μ A B) A ω = (x, a)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ω _ hω
      apply h
      simp only [pairRV, Prod.mk.injEq] at hω
      have hparts := hω
      exact hparts.2 ▸ hparts.1
    rw [hempty]
    simp [FiniteProbSpace.probOf]

/-- Adding `C` to the preceding graph-supported pair preserves the same support condition. -/
private theorem dist_C_blockRV_pair (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (c x a : ℕ) :
    μ.dist (pairRV (pairRV C (blockRV μ A B)) A) ((c, x), a) =
      if componentOf μ A B a = x then μ.dist (pairRV C A) (c, a) else 0 := by
  by_cases h : componentOf μ A B a = x
  · rw [ite_eq_left h]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairRV, blockRV,
      Prod.mk.injEq]
    constructor
    · exact fun hω => ⟨hω.1.1, hω.2⟩
    · rintro ⟨hC, hA⟩
      exact ⟨⟨hC, hA ▸ h⟩, hA⟩
  · rw [ite_eq_right h]
    unfold FiniteProbSpace.dist
    have hempty : (Finset.univ.filter fun ω =>
        pairRV (pairRV C (blockRV μ A B)) A ω = ((c, x), a)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ω _ hω
      apply h
      simp only [pairRV, Prod.mk.injEq] at hω
      exact hω.2 ▸ hω.1.2
    rw [hempty]
    simp [FiniteProbSpace.probOf]

/-- On a positive block, the conditional law of `C` is the law conditioned on any
positive-probability value of `A` in that block. -/
private theorem condDist_blockRV_eq_condDist_A (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (hBC : condMutualInfo μ B C A = 0) (hAC : condMutualInfo μ A C B = 0)
    (x a : ℕ) (hx : 0 < μ.dist (blockRV μ A B) x)
    (hax : componentOf μ A B a = x) (c : ℕ) :
    μ.condDist C (valueEvent (blockRV μ A B) x) c =
      μ.condDist C (valueEvent A a) c := by
  let q := μ.condDist C (valueEvent A a) c
  have hden : μ.dist (blockRV μ A B) x =
      ∑ a' ∈ rangeFinset A,
        if componentOf μ A B a' = x then μ.dist A a' else 0 := by
    rw [← μ.sum_dist_pairRV_snd (blockRV μ A B) A x]
    exact Finset.sum_congr rfl fun a' _ => dist_blockRV_pair μ A B x a'
  have hnum : μ.dist (pairRV C (blockRV μ A B)) (c, x) =
      ∑ a' ∈ rangeFinset A,
        if componentOf μ A B a' = x then μ.dist (pairRV C A) (c, a') else 0 := by
    rw [← μ.sum_dist_pairRV_snd (pairRV C (blockRV μ A B)) A (c, x)]
    exact Finset.sum_congr rfl fun a' _ => dist_C_blockRV_pair μ A B C c x a'
  have hterm : ∀ a', componentOf μ A B a' = x →
      μ.dist (pairRV C A) (c, a') = q * μ.dist A a' := by
    intro a' ha'x
    rcases (μ.dist_nonneg A a').lt_or_eq with ha' | ha'
    · have heqv := eqvGen_of_componentOf_eq μ A B a' a (ha'x.trans hax.symm)
      have hlaw := condDist_eq_of_eqvGen μ A B C hBC hAC a' a heqv c
      simp only [valueEvent] at hlaw
      rw [μ.condDist_fiber] at hlaw
      change μ.dist (pairRV C A) (c, a') =
        μ.condDist C (valueEvent A a) c * μ.dist A a'
      exact (div_eq_iff ha'.ne').mp hlaw
    · rw [← ha', μ.dist_pairRV_eq_zero_of_snd C A c ha'.symm, mul_zero]
  have hsum :
      (∑ a' ∈ rangeFinset A,
        if componentOf μ A B a' = x then μ.dist (pairRV C A) (c, a') else 0) =
      q * ∑ a' ∈ rangeFinset A,
        if componentOf μ A B a' = x then μ.dist A a' else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a' _
    by_cases ha'x : componentOf μ A B a' = x
    · simp only [ite_eq_left ha'x]
      exact hterm a' ha'x
    · simp [ha'x]
  simp only [valueEvent]
  rw [μ.condDist_fiber, hnum, hsum, ← hden]
  exact mul_div_cancel_right₀ q hx.ne'

/-- A conditional joint probability, multiplied by its conditioning probability, is the
corresponding three-variable joint probability. -/
private theorem condDist_pair_mul_dist_eq_dist_triple (μ : FiniteProbSpace Ω)
    (A B C : Ω → ℕ) (a b c : ℕ) (ha : 0 < μ.dist A a) :
    μ.condDist (pairRV B C) (valueEvent A a) (b, c) * μ.dist A a =
      μ.dist (pairRV (pairRV A B) C) ((a, b), c) := by
  have hevent : ((valueEvent A a).filter fun ω => pairRV B C ω = (b, c)) =
      Finset.univ.filter fun ω => pairRV (pairRV A B) C ω = ((a, b), c) := by
    ext ω
    simp only [valueEvent, Finset.mem_filter, Finset.mem_univ, true_and, pairRV,
      Prod.mk.injEq]
    tauto
  unfold FiniteProbSpace.condDist FiniteProbSpace.dist
  rw [hevent]
  change μ.probOf _ / μ.dist A a * μ.dist A a = _
  exact div_mul_cancel₀ _ ha.ne'

/-- The block coordinate in the joint distribution of `(A, B)` and the block is redundant. -/
private theorem dist_AB_blockRV (μ : FiniteProbSpace Ω) (A B : Ω → ℕ)
    (a b x : ℕ) :
    μ.dist (pairRV (pairRV A B) (blockRV μ A B)) ((a, b), x) =
      if componentOf μ A B a = x then μ.dist (pairRV A B) (a, b) else 0 := by
  by_cases h : componentOf μ A B a = x
  · rw [ite_eq_left h]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairRV, blockRV,
      Prod.mk.injEq]
    constructor
    · exact fun hω => hω.1
    · rintro ⟨hA, hB⟩
      exact ⟨⟨hA, hB⟩, hA ▸ h⟩
  · rw [ite_eq_right h]
    unfold FiniteProbSpace.dist
    have hempty : (Finset.univ.filter fun ω =>
        pairRV (pairRV A B) (blockRV μ A B) ω = ((a, b), x)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ω _ hω
      apply h
      simp only [pairRV, Prod.mk.injEq] at hω
      exact hω.1.1 ▸ hω.2
    rw [hempty]
    simp [FiniteProbSpace.probOf]

/-- The same redundant-coordinate formula with `C` also included. -/
private theorem dist_ABC_blockRV (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (a b c x : ℕ) :
    μ.dist (pairRV (pairRV (pairRV A B) C) (blockRV μ A B)) (((a, b), c), x) =
      if componentOf μ A B a = x then
        μ.dist (pairRV (pairRV A B) C) ((a, b), c) else 0 := by
  by_cases h : componentOf μ A B a = x
  · rw [ite_eq_left h]
    unfold FiniteProbSpace.dist
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairRV, blockRV,
      Prod.mk.injEq]
    constructor
    · exact fun hω => hω.1
    · rintro ⟨⟨hA, hB⟩, hC⟩
      exact ⟨⟨⟨hA, hB⟩, hC⟩, hA ▸ h⟩
  · rw [ite_eq_right h]
    unfold FiniteProbSpace.dist
    have hempty : (Finset.univ.filter fun ω =>
        pairRV (pairRV (pairRV A B) C) (blockRV μ A B) ω = (((a, b), c), x)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ω _ hω
      apply h
      simp only [pairRV, Prod.mk.injEq] at hω
      exact hω.1.1.1 ▸ hω.2
    rw [hempty]
    simp [FiniteProbSpace.probOf]

/-- A pair has zero probability when its first coordinate does. -/
private theorem dist_pairRV_eq_zero_of_fst {α β : Type} [DecidableEq α] [DecidableEq β]
    (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (x : α) (y : β)
    (hx : μ.dist X x = 0) : μ.dist (pairRV X Y) (x, y) = 0 := by
  have hswap : μ.dist (pairRV X Y) (x, y) = μ.dist (pairRV Y X) (y, x) := by
    rw [μ.dist_pairRV, μ.dist_pairRV]
    congr 1
    ext ω
    simp [and_comm]
  rw [hswap]
  exact μ.dist_pairRV_eq_zero_of_snd Y X y hx

/-- Inside a block the conditional distribution of `γ` is constant: `I(β:γ|α) = 0` and
`I(α:γ|β) = 0` say that it depends only on `α` and only on `β` at every support point, so it
is constant along every edge of the support graph, hence on every component.  Therefore
`⟨α, β⟩` and `γ` are independent given the block number. -/
private theorem condMutualInfo_blockRV_eq_zero (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (hBC : condMutualInfo μ B C A = 0) (hAC : condMutualInfo μ A C B = 0) :
    condMutualInfo μ (pairRV A B) C (blockRV μ A B) = 0 := by
  apply (condMutualInfo_eq_zero_iff μ (pairRV A B) C (blockRV μ A B)).mpr
  rintro x hx ⟨a, b⟩ c
  by_cases hab : 0 < μ.dist (pairRV A B) (a, b)
  · obtain ⟨ω, hω, hp⟩ := (μ.dist_pos_iff (pairRV A B) (a, b)).mp hab
    have ha : 0 < μ.dist A a :=
      (μ.dist_pos_iff A a).mpr ⟨ω, congrArg Prod.fst hω, hp⟩
    have hlocal := (condMutualInfo_eq_zero_iff μ B C A).mp hBC a ha b c
    have hpair := condDist_mul_dist_eq_dist_pair μ A B a b ha
    have htriple := condDist_pair_mul_dist_eq_dist_triple μ A B C a b c ha
    rw [hlocal] at htriple
    have hjoint : μ.dist (pairRV (pairRV A B) C) ((a, b), c) =
        μ.dist (pairRV A B) (a, b) * μ.condDist C (valueEvent A a) c := by
      calc
        _ = (μ.condDist B (valueEvent A a) b * μ.condDist C (valueEvent A a) c) *
            μ.dist A a := htriple.symm
        _ = (μ.condDist B (valueEvent A a) b * μ.dist A a) *
            μ.condDist C (valueEvent A a) c := by ring
        _ = _ := by rw [hpair]
    by_cases hax : componentOf μ A B a = x
    · have hblock := condDist_blockRV_eq_condDist_A μ A B C hBC hAC x a hx hax c
      simp only [valueEvent] at hjoint hblock ⊢
      simp_rw [μ.condDist_fiber] at hjoint hblock ⊢
      rw [dist_ABC_blockRV, dist_AB_blockRV, ite_eq_left hax, hjoint, hblock]
      simp only [ite_eq_left hax]
      ring
    · simp only [valueEvent]
      simp_rw [μ.condDist_fiber]
      rw [dist_ABC_blockRV, dist_AB_blockRV, ite_eq_right hax]
      simp [hax]
  · have hab0 : μ.dist (pairRV A B) (a, b) = 0 :=
      le_antisymm (not_lt.mp hab) (μ.dist_nonneg _ _)
    have habc0 : μ.dist (pairRV (pairRV A B) C) ((a, b), c) = 0 :=
      dist_pairRV_eq_zero_of_fst μ (pairRV A B) C (a, b) c hab0
    simp only [valueEvent]
    simp_rw [μ.condDist_fiber]
    rw [dist_ABC_blockRV, dist_AB_blockRV]
    split_ifs <;> simp [hab0, habc0]

end DoubleMarkov

/-- **Problem 303(a)** (the double Markov property).  If `I(β:γ|α) = 0` and `I(α:γ|β) = 0`,
there is a random variable `ξ` with `H(ξ|α) = 0`, `H(ξ|β) = 0` and `I(⟨α, β⟩ : γ | ξ) = 0`.
Part (b) of the problem derives Theorem 219 from this.  SUV Problem 303, p. 345. -/
theorem exists_double_markov {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ)
    (hBC : condMutualInfo μ B C A = 0) (hAC : condMutualInfo μ A C B = 0) :
    ∃ X : Ω → ℕ, condEntropy μ X A = 0 ∧ condEntropy μ X B = 0 ∧
      condMutualInfo μ (pairRV A B) C X = 0 := by
  refine ⟨blockRV μ A B, ?_, condEntropy_blockRV_right μ A B,
    condMutualInfo_blockRV_eq_zero μ A B C hBC hAC⟩
  -- the block number is a function of `α` by definition
  rw [condEntropy_eq_zero_iff]
  refine ⟨componentOf μ A B, ?_⟩
  have h : (Finset.univ.filter fun ω => blockRV μ A B ω = componentOf μ A B (A ω))
      = Finset.univ :=
    Finset.filter_true_of_mem fun ω _ => rfl
  rw [h, FiniteProbSpace.probOf_univ]

/-- **Theorem 219.**  If `W(α, β, γ) = 0`, the variables `α, β, γ` have fully extractable
common information: there is a random variable `ξ` on the same space with
`H(ξ|α) = H(ξ|β) = H(ξ|γ) = 0` and `I(α:β|ξ) = I(β:γ|ξ) = I(α:γ|ξ) = 0`.  The book's proof
shows that the support of the joint distribution is block diagonal with positive entries in
each block and takes `ξ` to be the number of the block; Problem 302 asks for the missing
details.  SUV Theorem 219, p. 344. -/
theorem exists_common_information_of_pairwiseCondInfoSum_eq_zero {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (A B C : Ω → ℕ) (hW : pairwiseCondInfoSum μ A B C = 0) :
    ∃ X : Ω → ℕ, condEntropy μ X A = 0 ∧ condEntropy μ X B = 0 ∧ condEntropy μ X C = 0 ∧
      condMutualInfo μ A B X = 0 ∧ condMutualInfo μ B C X = 0 ∧
        condMutualInfo μ A C X = 0 := by
  obtain ⟨hABC, hACB, hBCA⟩ := condMutualInfo_eq_zero_of_pairwiseCondInfoSum_eq_zero μ A B C hW
  obtain ⟨X, hXA, hXB, hC⟩ := exists_double_markov μ A B C hBCA hACB
  obtain ⟨hAC, hBC⟩ := condMutualInfo_eq_zero_of_pairRV_eq_zero μ A B C X hC
  exact ⟨X, hXA, hXB, condEntropy_eq_zero_of_condMutualInfo_eq_zero μ X A B C hXA hXB hABC,
    condMutualInfo_eq_zero_of_double_markov μ A B C X hXA hXB hC hABC hACB hBCA, hBC, hAC⟩

/-! ### The deduction rule -/

section DeductionRule

variable {n : ℕ} {Ω : Type} [Fintype Ω]

/-- The resampled tuple on the coupling: the variables of `P₃` are read off the second
coordinate, all others off the first. -/
private def resampledTuple (X : Fin n → Ω → ℕ) (P₃ : Finset (Fin n)) : Fin n → Ω × Ω → ℕ :=
  fun i ω => if i ∈ P₃ then X i ω.2 else X i ω.1

omit [Fintype Ω] in
/-- A subtuple disjoint from `P₃` is read off the first coordinate. -/
private theorem subtuple_resampledTuple_fst (X : Fin n → Ω → ℕ) {I P₃ : Finset (Fin n)}
    (h : Disjoint I P₃) (ω : Ω × Ω) :
    subtuple (resampledTuple X P₃) I ω = subtuple X I ω.1 :=
  funext fun i => ite_eq_right (Finset.disjoint_left.1 h i.2)

omit [Fintype Ω] in
/-- A subtuple inside `P₃` is read off the second coordinate. -/
private theorem subtuple_resampledTuple_snd (X : Fin n → Ω → ℕ) {I P₃ : Finset (Fin n)}
    (h : I ⊆ P₃) (ω : Ω × Ω) :
    subtuple (resampledTuple X P₃) I ω = subtuple X I ω.2 :=
  funext fun i => ite_eq_left (h i.2)

omit [Fintype Ω] in
/-- Where `ξ_{P₁}` agrees on both coordinates, a subtuple disjoint from `P₂` is read off the
second coordinate. -/
private theorem subtuple_resampledTuple_snd_of_disjoint (X : Fin n → Ω → ℕ)
    {I P₁ P₂ P₃ : Finset (Fin n)} (hcover : P₁ ∪ P₂ ∪ P₃ = Finset.univ)
    (h : Disjoint I P₂) (ω : Ω × Ω) (hω : subtuple X P₁ ω.1 = subtuple X P₁ ω.2) :
    subtuple (resampledTuple X P₃) I ω = subtuple X I ω.2 := by
  funext i
  by_cases hi : i.val ∈ P₃
  · exact ite_eq_left hi
  · have hi1 : i.val ∈ P₁ := by
      have hu := Finset.mem_univ i.val
      rw [← hcover] at hu
      simp only [Finset.mem_union] at hu
      have := Finset.disjoint_left.1 h i.2
      tauto
    change (if i.val ∈ P₃ then X i.val ω.2 else X i.val ω.1) = X i.val ω.2
    rw [ite_eq_right hi]
    exact congrFun hω ⟨i.val, hi1⟩

/-- The entropy of a subtuple that avoids `P₂` or `P₃` is unchanged by the resampling. -/
private theorem entropySub_resampledTuple (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ)
    {P₁ P₂ P₃ : Finset (Fin n)} (hcover : P₁ ∪ P₂ ∪ P₃ = Finset.univ) (I : Finset (Fin n))
    (hI : Disjoint I P₂ ∨ Disjoint I P₃) :
    entropySub (coupling μ (subtuple X P₁)) (resampledTuple X P₃) I = entropySub μ X I := by
  rcases hI with hI | hI
  · exact entropy_coupling_of_eq_snd μ _ _ _ fun ω hω =>
      subtuple_resampledTuple_snd_of_disjoint X hcover hI ω hω
  · exact entropy_coupling_of_eq_fst μ _ _ _ fun ω _ => subtuple_resampledTuple_fst X hI ω

/-- `basicInequality n P₂ P₃ P₁`, evaluated on entropies, is `−I(ξ_{P₂} : ξ_{P₃} | ξ_{P₁})`. -/
private theorem evalEntropy_basicInequality (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ)
    (P₁ P₂ P₃ : Finset (Fin n)) :
    (basicInequality n P₂ P₃ P₁).evalEntropy μ X
      = - condMutualInfo μ (subtuple X P₂) (subtuple X P₃) (subtuple X P₁) := by
  have hv0 : ∀ T : Finset (Fin n),
      (if T.Nonempty then entropySub μ X T else 0) = entropySub μ X T := by
    intro T
    split_ifs with h
    · rfl
    · rw [Finset.not_nonempty_iff_eq_empty.1 h, entropySub_empty]
  unfold LinearForm.evalEntropy
  simp only [basicInequality, add_mul, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_nonemptyParts, hv0]
  rw [condMutualInfo_eq, entropySub_union_union, entropySub_union, entropySub_union]
  have h1 : entropySub μ X P₁ = entropy μ (subtuple X P₁) := rfl
  linarith

/-- On the coupling along `ξ_{P₁}` the resampled tuple has `I(ξ_{P₂} : ξ_{P₃} | ξ_{P₁}) = 0`,
so the weaker form of the deduction rule evaluates there to the value of the original form on
the original tuple. -/
private theorem evalEntropy_resampled_eq (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ)
    (f : LinearForm n) {P₁ P₂ P₃ : Finset (Fin n)} (h₁₃ : Disjoint P₁ P₃)
    (h₂₃ : Disjoint P₂ P₃) (hcover : P₁ ∪ P₂ ∪ P₃ = Finset.univ)
    (hsupp : ∀ I : Finset (Fin n), f I ≠ 0 → Disjoint I P₂ ∨ Disjoint I P₃) :
    LinearForm.evalEntropy (fun I => f I + basicInequality n P₂ P₃ P₁ I)
        (coupling μ (subtuple X P₁)) (resampledTuple X P₃)
      = f.evalEntropy μ X := by
  have hb := evalEntropy_basicInequality (coupling μ (subtuple X P₁)) (resampledTuple X P₃)
    P₁ P₂ P₃
  rw [funext (subtuple_resampledTuple_fst X h₂₃), funext (subtuple_resampledTuple_snd X
    (subset_refl P₃)), funext (subtuple_resampledTuple_fst X h₁₃),
    condMutualInfo_coupling_eq_zero, neg_zero] at hb
  unfold LinearForm.evalEntropy at hb ⊢
  simp only [add_mul, Finset.sum_add_distrib, hb, add_zero]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : f I = 0
  · rw [hI, zero_mul, zero_mul]
  · rw [entropySub_resampledTuple μ X hcover I (hsupp I hI)]

end DeductionRule

/-- **The deduction rule.**  Split the variables into three disjoint groups `P₁, P₂, P₃` so
that no term of the inequality contains variables of both `P₂` and `P₃`.  Then the inequality
follows from the weaker one in which `I(ξ_{P₂} : ξ_{P₃} | ξ_{P₁})` is added to the right-hand
side.  In the sign convention of `LinearForm` the weaker inequality is
`f − I(P₂ : P₃ | P₁) ≤ 0`, and `basicInequality n P₂ P₃ P₁` is exactly `−I(P₂ : P₃ | P₁)`.
The book adds that the rule yields infinitely many independent non-Shannon inequalities for
four variables; that remark is cited, not stated.  SUV Section 10.13, p. 347 (unnumbered). -/
theorem holdsForEntropies_of_deduction_rule {n : ℕ} (f : LinearForm n)
    (P₁ P₂ P₃ : Finset (Fin n)) (h₁₂ : Disjoint P₁ P₂) (h₁₃ : Disjoint P₁ P₃)
    (h₂₃ : Disjoint P₂ P₃) (hcover : P₁ ∪ P₂ ∪ P₃ = Finset.univ)
    (hsupp : ∀ I : Finset (Fin n), f I ≠ 0 → Disjoint I P₂ ∨ Disjoint I P₃)
    (hweak : HoldsForEntropies (fun I => f I + basicInequality n P₂ P₃ P₁ I)) :
    HoldsForEntropies f := by
  -- the coupling argument does not use `Disjoint P₁ P₂`: the variables of `P₁ ∪ P₂` are all
  -- read off the first coordinate
  have _ := h₁₂
  intro Ω _ μ X
  rw [← evalEntropy_resampled_eq μ X f h₁₃ h₂₃ hcover hsupp]
  exact hweak (Ω × Ω) _ _

/-! ### The second proof of Theorem 218 -/

/-- The diagram identity of the second proof of Theorem 218:
`I(α:β) + 2H(ε|α) + 2H(ε|β) = H(ε) + W(α, β, ε) + 3H(ε|α, β)`.
SUV Section 10.13, p. 348 (unnumbered). -/
theorem mutualInfo_add_two_condEntropy_eq {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (A B E : Ω → ℕ) :
    mutualInfo μ A B + 2 * condEntropy μ E A + 2 * condEntropy μ E B
      = entropy μ E + pairwiseCondInfoSum μ A B E + 3 * condEntropy μ E (pairRV A B) := by
  simp only [pairwiseCondInfoSum, condMutualInfo_eq, mutualInfo, condEntropy_eq_sub]
  linarith [entropy_pairRV_comm μ A E, entropy_pairRV_comm μ B E, entropy_pairRV_comm μ A B,
    entropy_pairRV_comm μ (pairRV A B) E, entropy_pairRV_swap_right μ A B E,
    entropy_pair_rotate μ A B E]

/-- The inequality of Theorem 218 with the extra term `3 H(ε | α, β)` on the right.  It is the
sum of three instances of (conditional) Problem 296 and the identity
`mutualInfo_add_two_condEntropy_eq`; the second proof of Theorem 218 removes the extra term by
applying it to `k` independent copies with `E` replaced by the `E'` of Theorem 220.
SUV Section 10.13, p. 348 (unnumbered). -/
theorem mutualInfo_le_nonShannon_add_three_condEntropy {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (A B C D E : Ω → ℕ) :
    mutualInfo μ A B
      ≤ condMutualInfo μ A B C + condMutualInfo μ A B D + mutualInfo μ C D
        + pairwiseCondInfoSum μ A B E + 3 * condEntropy μ E (pairRV A B) := by
  have h3 := entropy_le_condEntropy_add_condEntropy_add_mutualInfo μ E C D
  have h1 := condEntropy_le_condEntropy_pairRV_add μ E A B C
  have h2 := condEntropy_le_condEntropy_pairRV_add μ E A B D
  have m1 := condEntropy_pairRV_le_condEntropy μ E A C
  have m2 := condEntropy_pairRV_le_condEntropy μ E B C
  have m3 := condEntropy_pairRV_le_condEntropy μ E A D
  have m4 := condEntropy_pairRV_le_condEntropy μ E B D
  have hid := mutualInfo_add_two_condEntropy_eq μ A B E
  linarith

end Kolmogorov
