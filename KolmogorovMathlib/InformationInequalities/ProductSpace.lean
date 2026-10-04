import KolmogorovMathlib.Entropy.Inequalities
import KolmogorovMathlib.Entropy.PairDistributions

/-!
# Products of finite probability spaces

The product of two finite probability spaces on `Fin m` and `Fin m'`, laid out on `Fin (m * m')`
through `finProdFinEquiv`, and the facts that make it the space of independent copies: a
variable of one factor keeps its distribution and its entropy, and a pair of variables taken
from the two factors has the product distribution, hence the sum of the two entropies.

These are the tools for the closure properties of the entropy region in SUV Section 10.10
(Problems 292–293, p. 337): the sum of two entropy vectors is realised by independent copies of
the two tuples.
-/

namespace Kolmogorov

open Finset

/-- The product of two finite probability spaces on `Fin m` and `Fin m'`, laid out on
`Fin (m * m')` through `finProdFinEquiv`: independent copies of the two spaces. -/
noncomputable def prodSpace {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) : FiniteProbSpace (Fin (m * m')) where
  prob k := μ.prob (finProdFinEquiv.symm k).1 * ν.prob (finProdFinEquiv.symm k).2
  prob_nonneg _ := mul_nonneg (μ.prob_nonneg _) (ν.prob_nonneg _)
  sum_prob := by
    have h : ∑ k : Fin (m * m'), μ.prob (finProdFinEquiv.symm k).1
          * ν.prob (finProdFinEquiv.symm k).2
        = ∑ p : Fin m × Fin m', μ.prob p.1 * ν.prob p.2 :=
      Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl
    rw [h, Fintype.sum_prod_type, ← Finset.sum_mul_sum, μ.sum_prob, ν.sum_prob, one_mul]

/-- A sum over the product space of a term that factors splits into a product of two sums. -/
theorem sum_prodSpace_ite {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) (P : Fin m → Prop) [DecidablePred P] (Q : Fin m' → Prop)
    [DecidablePred Q] :
    ∑ k : Fin (m * m'), (if P (finProdFinEquiv.symm k).1 ∧ Q (finProdFinEquiv.symm k).2
        then μ.prob (finProdFinEquiv.symm k).1 * ν.prob (finProdFinEquiv.symm k).2 else 0)
      = (∑ ω, if P ω then μ.prob ω else 0) * (∑ ω', if Q ω' then ν.prob ω' else 0) := by
  have h : ∑ k : Fin (m * m'), (if P (finProdFinEquiv.symm k).1 ∧ Q (finProdFinEquiv.symm k).2
        then μ.prob (finProdFinEquiv.symm k).1 * ν.prob (finProdFinEquiv.symm k).2 else 0)
      = ∑ p : Fin m × Fin m', (if P p.1 ∧ Q p.2 then μ.prob p.1 * ν.prob p.2 else 0) :=
    Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl
  rw [h, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hP : P a <;> by_cases hQ : Q b <;> simp [hP, hQ]

/-- On the product space, a variable of the first factor and a variable of the second have
the product distribution. -/
theorem dist_prodSpace_pair {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Fin m → α) (B : Fin m' → β) (a : α) (b : β) :
    (prodSpace μ ν).dist (pairRV (fun k => A (finProdFinEquiv.symm k).1)
      (fun k => B (finProdFinEquiv.symm k).2)) (a, b) = μ.dist A a * ν.dist B b := by
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter, pairRV,
    Prod.mk.injEq]
  exact sum_prodSpace_ite μ ν (fun ω => A ω = a) (fun ω' => B ω' = b)

/-- A variable of the first factor keeps its distribution on the product space. -/
theorem dist_prodSpace_fst {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) {α : Type} [DecidableEq α] (A : Fin m → α) (a : α) :
    (prodSpace μ ν).dist (fun k => A (finProdFinEquiv.symm k).1) a = μ.dist A a := by
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter]
  have h := sum_prodSpace_ite μ ν (fun ω => A ω = a) (fun _ => True)
  simp only [and_true, ite_true, ν.sum_prob, mul_one] at h
  exact h

/-- A variable of the second factor keeps its distribution on the product space. -/
theorem dist_prodSpace_snd {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) {β : Type} [DecidableEq β] (B : Fin m' → β) (b : β) :
    (prodSpace μ ν).dist (fun k => B (finProdFinEquiv.symm k).2) b = ν.dist B b := by
  simp only [FiniteProbSpace.dist, FiniteProbSpace.probOf, Finset.sum_filter]
  have h := sum_prodSpace_ite μ ν (fun _ => True) (fun ω' => B ω' = b)
  simp only [true_and, ite_true, μ.sum_prob, one_mul] at h
  exact h

/-- Two random variables with the same distribution have the same entropy. -/
theorem entropy_congr_dist {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] {α : Type*}
    [DecidableEq α] (μ : FiniteProbSpace Ω) (μ' : FiniteProbSpace Ω') (X : Ω → α) (X' : Ω' → α)
    (h : ∀ a, μ'.dist X' a = μ.dist X a) : entropy μ' X' = entropy μ X := by
  have h1 : entropy μ' X' = ∑ a ∈ rangeFinset X' ∪ rangeFinset X, negMulLog2 (μ'.dist X' a) :=
    Finset.sum_subset Finset.subset_union_left fun a _ ha => by
      rw [μ'.dist_eq_zero_of_not_mem_range ha, negMulLog2_zero]
  have h2 : entropy μ X = ∑ a ∈ rangeFinset X' ∪ rangeFinset X, negMulLog2 (μ.dist X a) :=
    Finset.sum_subset Finset.subset_union_right fun a _ ha => by
      rw [μ.dist_eq_zero_of_not_mem_range ha, negMulLog2_zero]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun a _ => by rw [h a]

/-- A variable of the first factor keeps its entropy on the product space. -/
theorem entropy_prodSpace_fst {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) {α : Type} [DecidableEq α] (A : Fin m → α) :
    entropy (prodSpace μ ν) (fun k => A (finProdFinEquiv.symm k).1) = entropy μ A :=
  entropy_congr_dist μ (prodSpace μ ν) A _ (dist_prodSpace_fst μ ν A)

/-- A variable of the second factor keeps its entropy on the product space. -/
theorem entropy_prodSpace_snd {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) {β : Type} [DecidableEq β] (B : Fin m' → β) :
    entropy (prodSpace μ ν) (fun k => B (finProdFinEquiv.symm k).2) = entropy ν B :=
  entropy_congr_dist ν (prodSpace μ ν) B _ (dist_prodSpace_snd μ ν B)

/-- On the product space, the entropy of a pair of variables of the two factors is the sum
of their entropies: the two are independent. -/
theorem entropy_prodSpace_pair {m m' : ℕ} (μ : FiniteProbSpace (Fin m))
    (ν : FiniteProbSpace (Fin m')) {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Fin m → α) (B : Fin m' → β) :
    entropy (prodSpace μ ν) (pairRV (fun k => A (finProdFinEquiv.symm k).1)
      (fun k => B (finProdFinEquiv.symm k).2)) = entropy μ A + entropy ν B := by
  set Z := pairRV (fun k : Fin (m * m') => A (finProdFinEquiv.symm k).1)
    (fun k => B (finProdFinEquiv.symm k).2) with hZ
  have hsub : rangeFinset Z ⊆ rangeFinset A ×ˢ rangeFinset B := by
    intro p hp
    obtain ⟨k, rfl⟩ := mem_rangeFinset.1 hp
    exact Finset.mem_product.2 ⟨mem_rangeFinset.2 ⟨_, rfl⟩, mem_rangeFinset.2 ⟨_, rfl⟩⟩
  have h1 : entropy (prodSpace μ ν) Z
      = ∑ p ∈ rangeFinset A ×ˢ rangeFinset B, negMulLog2 ((prodSpace μ ν).dist Z p) := by
    refine Finset.sum_subset hsub fun p _ hp => ?_
    rw [(prodSpace μ ν).dist_eq_zero_of_not_mem_range hp, negMulLog2_zero]
  have h2 : ∀ a ∈ rangeFinset A, ∑ b ∈ rangeFinset B, negMulLog2 ((prodSpace μ ν).dist Z (a, b))
      = negMulLog2 (μ.dist A a) + μ.dist A a * entropy ν B := by
    intro a _
    have h2' : ∀ b ∈ rangeFinset B, negMulLog2 ((prodSpace μ ν).dist Z (a, b))
        = ν.dist B b * negMulLog2 (μ.dist A a) + μ.dist A a * negMulLog2 (ν.dist B b) := by
      intro b _
      rw [hZ, dist_prodSpace_pair, negMulLog2_mul]
    rw [Finset.sum_congr rfl h2', Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ν.sum_dist_eq_one, one_mul]
    rfl
  rw [h1, Finset.sum_product, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.sum_mul,
    μ.sum_dist_eq_one, one_mul]
  rfl

end Kolmogorov
