/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Subtuples

/-!
# Distributions of pairs and the entropy summand

SUV Section 7.2, pp. 217–221: the elementary facts behind the entropy inequalities of
Section 7.2.

This module holds the computations that `KolmogorovMathlib.Entropy.Inequalities` builds on:
the distribution of a pair `⟨ξ, η⟩` as the probability of an intersection of fibres, its
marginals, the conditional distribution given a fibre, the double-sum forms of `H(⟨ξ, η⟩)` and
`H(ξ|η)`, and the properties of the entropy summand `negMulLog2` (its expression through
`logb`, the weighted Gibbs inequality `sum_mul_negMulLog2_le` with its equality case, and the
product rule `negMulLog2_mul`), and the vanishing criteria: when the entropy summand
vanishes, when `H(ξ|A)` vanishes (`condEntropyGiven_eq_zero_iff`), when an event has
probability one and when a value has positive probability.  No book item is stated here.
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Distributions of pairs and conditional distributions -/

/-- A larger event has larger probability. -/
theorem FiniteProbSpace.probOf_mono (μ : FiniteProbSpace Ω) {E F : Finset Ω} (h : E ⊆ F) :
    μ.probOf E ≤ μ.probOf F :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => μ.prob_nonneg ω

/-- A conditional distribution takes values at most one. -/
theorem FiniteProbSpace.condDist_le_one (μ : FiniteProbSpace Ω) (X : Ω → α) (E : Finset Ω)
    (a : α) : μ.condDist X E a ≤ 1 :=
  div_le_one_of_le₀ (μ.probOf_mono (Finset.filter_subset _ _)) (μ.probOf_nonneg _)

/-- The entropy of a conditional distribution is non-negative. -/
theorem condEntropyGiven_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) (E : Finset Ω) :
    0 ≤ condEntropyGiven μ X E :=
  Finset.sum_nonneg fun a _ =>
    negMulLog2_nonneg (μ.condDist_nonneg X E a) (μ.condDist_le_one X E a)

/-- The distribution of a pair is the probability of the intersection of the two fibres. -/
theorem FiniteProbSpace.dist_pairRV (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (a : α)
    (b : β) :
    μ.dist (pairRV X Y) (a, b) =
      μ.probOf ((Finset.univ.filter fun ω => Y ω = b).filter fun ω => X ω = a) := by
  unfold dist
  congr 1
  ext ω
  simp [pairRV, and_comm]

/-- The probability of a pair of values is at most the probability of the second value. -/
theorem FiniteProbSpace.dist_pairRV_le_snd (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (a : α) (b : β) : μ.dist (pairRV X Y) (a, b) ≤ μ.dist Y b := by
  rw [μ.dist_pairRV]
  exact μ.probOf_mono (Finset.filter_subset _ _)

/-- When the second value has probability zero, so has every pair with that value. -/
theorem FiniteProbSpace.dist_pairRV_eq_zero_of_snd (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (a : α) {b : β} (hb : μ.dist Y b = 0) : μ.dist (pairRV X Y) (a, b) = 0 :=
  le_antisymm ((μ.dist_pairRV_le_snd X Y a b).trans hb.le) (μ.dist_nonneg _ _)

/-- Summing the distribution of a pair over the first coordinate gives the distribution of the
second coordinate. -/
theorem FiniteProbSpace.sum_dist_pairRV_fst (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (b : β) : ∑ a ∈ rangeFinset X, μ.dist (pairRV X Y) (a, b) = μ.dist Y b := by
  simp_rw [μ.dist_pairRV]
  simp only [dist, probOf]
  exact Finset.sum_fiberwise_of_maps_to (fun ω _ => mem_rangeFinset.2 ⟨ω, rfl⟩) μ.prob

/-- Summing the distribution of a pair over the second coordinate gives the distribution of the
first coordinate. -/
theorem FiniteProbSpace.sum_dist_pairRV_snd (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (a : α) : ∑ b ∈ rangeFinset Y, μ.dist (pairRV X Y) (a, b) = μ.dist X a := by
  have hfil : ∀ b, ((Finset.univ.filter fun ω => Y ω = b).filter fun ω => X ω = a)
      = (Finset.univ.filter fun ω => X ω = a).filter fun ω => Y ω = b := by
    intro b
    ext ω
    simp [and_comm]
  simp_rw [μ.dist_pairRV, hfil]
  simp only [dist, probOf]
  exact Finset.sum_fiberwise_of_maps_to (fun ω _ => mem_rangeFinset.2 ⟨ω, rfl⟩) μ.prob

/-- The conditional distribution given a value of `Y` is the ratio of the pair distribution and
the distribution of `Y`. -/
theorem FiniteProbSpace.condDist_fiber (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (b : β)
    (a : α) :
    μ.condDist X (Finset.univ.filter fun ω => Y ω = b) a =
      μ.dist (pairRV X Y) (a, b) / μ.dist Y b := by
  rw [μ.dist_pairRV]
  rfl

/-- The entropy of a pair as a double sum over the ranges of the two components. -/
theorem entropy_pairRV_eq_sum_sum (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ (pairRV X Y) =
      ∑ b ∈ rangeFinset Y, ∑ a ∈ rangeFinset X, negMulLog2 (μ.dist (pairRV X Y) (a, b)) := by
  calc entropy μ (pairRV X Y)
      = ∑ p ∈ rangeFinset X ×ˢ rangeFinset Y, negMulLog2 (μ.dist (pairRV X Y) p) := by
        refine Finset.sum_subset ?_ ?_
        · intro p hp
          obtain ⟨ω, rfl⟩ := mem_rangeFinset.1 hp
          exact Finset.mem_product.2 ⟨mem_rangeFinset.2 ⟨ω, rfl⟩, mem_rangeFinset.2 ⟨ω, rfl⟩⟩
        · intro p _ hp
          rw [μ.dist_eq_zero_of_not_mem_range hp, negMulLog2_zero]
    _ = _ := Finset.sum_product_right _ _ _

/-- The conditional entropy as a double sum over the ranges. -/
theorem condEntropy_eq_sum_sum (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    condEntropy μ X Y = ∑ b ∈ rangeFinset Y, ∑ a ∈ rangeFinset X,
      μ.dist Y b * negMulLog2 (μ.dist (pairRV X Y) (a, b) / μ.dist Y b) := by
  simp only [condEntropy, condEntropyGiven, Finset.mul_sum, μ.condDist_fiber]

/-! ### The entropy summand -/

/-- `negMulLog2 x = -x · log₂ x`. -/
theorem negMulLog2_eq (x : ℝ) : negMulLog2 x = -x * Real.logb 2 x := by
  simp only [negMulLog2, Real.negMulLog, Real.logb]
  ring

/-- The summand of a conditional entropy, weighted by the probability of the condition:
`q · (-(j/q) log₂ (j/q)) = -j log₂ j + j log₂ q` for `q > 0`. -/
theorem mul_negMulLog2_div {j q : ℝ} (hq : 0 < q) :
    q * negMulLog2 (j / q) = negMulLog2 j + j * Real.logb 2 q := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · rw [negMulLog2_eq, negMulLog2_eq, Real.logb_div hj hq.ne']
    field_simp
    ring

/-- **Jensen's inequality for the entropy summand**: `negMulLog2` is concave on `[0, ∞)`, so a
convex combination of its values is at most its value at the convex combination. -/
theorem sum_mul_negMulLog2_le {ι : Type*} (s : Finset ι) (w p : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, w i * negMulLog2 (p i) ≤ negMulLog2 (∑ i ∈ s, w i * p i) := by
  have h := Real.concaveOn_negMulLog.le_map_sum hw hw1 fun i hi => Set.mem_Ici.2 (hp i hi)
  simp only [smul_eq_mul] at h
  have hl : ∑ i ∈ s, w i * negMulLog2 (p i)
      = (∑ i ∈ s, w i * Real.negMulLog (p i)) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [negMulLog2, mul_div_assoc]
  rw [hl, negMulLog2]
  exact div_le_div_of_nonneg_right h (Real.log_nonneg one_le_two)

/-- **The equality case of Jensen's inequality for the entropy summand**: `negMulLog2` is
strictly concave, so equality forces every point of positive weight to equal the average. -/
theorem eq_sum_of_sum_mul_negMulLog2_eq {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hp : ∀ i ∈ s, 0 ≤ p i)
    (h : ∑ i ∈ s, w i * negMulLog2 (p i) = negMulLog2 (∑ i ∈ s, w i * p i)) :
    ∀ j ∈ s, w j ≠ 0 → p j = ∑ i ∈ s, w i * p i := by
  have hl : ∑ i ∈ s, w i * negMulLog2 (p i)
      = (∑ i ∈ s, w i * Real.negMulLog (p i)) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [negMulLog2, mul_div_assoc]
  rw [hl, negMulLog2, div_left_inj' (Real.log_pos one_lt_two).ne'] at h
  have := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff' hw hw1
    fun i hi => Set.mem_Ici.2 (hp i hi)).1 (by simpa only [smul_eq_mul] using h.symm)
  simpa only [smul_eq_mul] using this

/-- The conditional distributions of `X` given the values of `Y`, averaged with the weights
`Pr[Y = b]`, give back the distribution of `X`. -/
theorem FiniteProbSpace.sum_dist_mul_condDist_fiber (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (a : α) :
    ∑ b ∈ rangeFinset Y, μ.dist Y b * (μ.dist (pairRV X Y) (a, b) / μ.dist Y b) =
      μ.dist X a := by
  rw [← μ.sum_dist_pairRV_snd X Y a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases (μ.dist_nonneg Y b).lt_or_eq with hq | hq
  · exact mul_div_cancel₀ _ hq.ne'
  · rw [← hq, zero_mul, μ.dist_pairRV_eq_zero_of_snd X Y a hq.symm]

/-- The Jensen bound for one value `a`: the average of the conditional-entropy summands at `a`
is at most the entropy summand at `a`. -/
theorem sum_dist_mul_negMulLog2_condDist_le (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (a : α) :
    ∑ b ∈ rangeFinset Y, μ.dist Y b * negMulLog2 (μ.dist (pairRV X Y) (a, b) / μ.dist Y b) ≤
      negMulLog2 (μ.dist X a) := by
  rw [← μ.sum_dist_mul_condDist_fiber X Y a]
  exact sum_mul_negMulLog2_le _ _ _ (fun b _ => μ.dist_nonneg Y b) (μ.sum_dist_eq_one Y)
    fun b _ => div_nonneg (μ.dist_nonneg _ _) (μ.dist_nonneg _ _)

/-- The entropy summand of a product: `negMulLog2 (x y) = y · negMulLog2 x + x · negMulLog2 y`. -/
theorem negMulLog2_mul (x y : ℝ) : negMulLog2 (x * y) = y * negMulLog2 x + x * negMulLog2 y := by
  simp only [negMulLog2, Real.negMulLog_mul]
  ring

/-- For a `Fintype` value type the conditional entropy given an event is the sum over all
values: the values not taken contribute `negMulLog2 0 = 0`. -/
theorem condEntropyGiven_eq_sum_univ [Fintype α] (μ : FiniteProbSpace Ω) (X : Ω → α)
    (E : Finset Ω) : condEntropyGiven μ X E = ∑ a, negMulLog2 (μ.condDist X E a) := by
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
  have hempty : (E.filter fun ω => X ω = a) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun ω _ h => ha (mem_rangeFinset.2 ⟨ω, h⟩)
  simp [FiniteProbSpace.condDist, hempty, FiniteProbSpace.probOf]

/-! ### Vanishing of the entropy summand and of conditional entropy -/

/-- The entropy summand vanishes at one: `negMulLog2 1 = 0`. -/
theorem negMulLog2_one : negMulLog2 1 = 0 := by
  simp [negMulLog2]

/-- The entropy summand is positive strictly inside the probability range. -/
private theorem negMulLog2_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < negMulLog2 x := by
  refine div_pos ?_ (Real.log_pos one_lt_two)
  simp only [Real.negMulLog]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos h0) (Real.log_neg h0 h1)

/-- On `[0, 1]` the entropy summand vanishes only at the endpoints. -/
private theorem eq_zero_or_eq_one_of_negMulLog2_eq_zero {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (h : negMulLog2 x = 0) : x = 0 ∨ x = 1 := by
  by_contra hne
  push Not at hne
  exact (negMulLog2_pos (h0.lt_of_ne hne.1.symm) (h1.lt_of_ne hne.2)).ne' h

/-- The conditional distribution given an event of positive probability sums to one over the
range of the variable. -/
theorem FiniteProbSpace.sum_condDist_eq_one (μ : FiniteProbSpace Ω) (X : Ω → α) {E : Finset Ω}
    (hE : 0 < μ.probOf E) : ∑ a ∈ rangeFinset X, μ.condDist X E a = 1 := by
  simp only [condDist, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hE.ne']
  simp only [probOf]
  exact Finset.sum_fiberwise_of_maps_to (fun ω _ => mem_rangeFinset.2 ⟨ω, rfl⟩) μ.prob

/-- A value outside the range of a random variable has conditional probability zero. -/
theorem FiniteProbSpace.condDist_eq_zero_of_not_mem_range (μ : FiniteProbSpace Ω) {X : Ω → α}
    (E : Finset Ω) {a : α} (ha : a ∉ rangeFinset X) : μ.condDist X E a = 0 := by
  have hempty : (E.filter fun ω => X ω = a) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun ω _ h => ha (mem_rangeFinset.2 ⟨ω, h⟩)
  simp [condDist, hempty, probOf]

/-- **Zero conditional entropy given an event**: for an event of positive probability the
conditional entropy vanishes exactly when the conditional distribution is concentrated at one
value. -/
theorem condEntropyGiven_eq_zero_iff (μ : FiniteProbSpace Ω) (X : Ω → α) {E : Finset Ω}
    (hE : 0 < μ.probOf E) :
    condEntropyGiven μ X E = 0 ↔ ∃ a, μ.condDist X E a = 1 := by
  constructor
  · intro h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
      negMulLog2_nonneg (μ.condDist_nonneg X E a) (μ.condDist_le_one X E a)).1 h
    by_contra hno
    push Not at hno
    refine zero_ne_one ((Finset.sum_eq_zero fun a ha => ?_).symm.trans (μ.sum_condDist_eq_one X hE))
    exact (eq_zero_or_eq_one_of_negMulLog2_eq_zero (μ.condDist_nonneg X E a)
      (μ.condDist_le_one X E a) (hterm a ha)).resolve_right (hno a)
  · rintro ⟨a, ha⟩
    have hsum := μ.sum_condDist_eq_one X hE
    have hamem : a ∈ rangeFinset X :=
      by_contra fun hn => one_ne_zero (ha.symm.trans (μ.condDist_eq_zero_of_not_mem_range E hn))
    have hother : ∀ b ∈ rangeFinset X, b ≠ a → μ.condDist X E b = 0 := by
      intro b hb hba
      have h2 : ∑ c ∈ (rangeFinset X).erase a, μ.condDist X E c = 0 := by
        rw [Finset.sum_erase_eq_sub hamem, hsum, ha, sub_self]
      exact (Finset.sum_eq_zero_iff_of_nonneg fun c _ => μ.condDist_nonneg X E c).1 h2 b
        (Finset.mem_erase.2 ⟨hba, hb⟩)
    unfold condEntropyGiven
    refine Finset.sum_eq_zero fun b hb => ?_
    by_cases hba : b = a
    · rw [hba, ha]
      exact negMulLog2_one
    · rw [hother b hb hba, negMulLog2_zero]

/-- The probability that `X = f(Y)`, decomposed along the values of `Y`. -/
theorem FiniteProbSpace.probOf_eq_comp_eq_sum (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (f : β → α) :
    μ.probOf (Finset.univ.filter fun ω => X ω = f (Y ω)) =
      ∑ b ∈ rangeFinset Y, μ.dist (pairRV X Y) (f b, b) := by
  simp_rw [μ.dist_pairRV]
  simp only [probOf]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun ω => X ω = f (Y ω))
    (t := rangeFinset Y) (g := Y) (fun ω _ => mem_rangeFinset.2 ⟨ω, rfl⟩) μ.prob]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm (a := X ω = f (Y ω))]
  exact and_congr_right fun h => by rw [h]

/-- An event has probability one exactly when it contains every outcome of positive weight. -/
theorem FiniteProbSpace.probOf_eq_one_iff (μ : FiniteProbSpace Ω) (E : Finset Ω) :
    μ.probOf E = 1 ↔ ∀ ω, 0 < μ.prob ω → ω ∈ E := by
  classical
  have hsplit : μ.probOf (Finset.univ \ E) + μ.probOf E = 1 := by
    rw [← μ.sum_prob]
    exact Finset.sum_sdiff (Finset.subset_univ E)
  constructor
  · intro h ω hω
    by_contra hωE
    have h0 : μ.probOf (Finset.univ \ E) = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => μ.prob_nonneg ω).1 h0 ω
      (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hωE⟩)
    exact hω.ne' this
  · intro h
    have h0 : μ.probOf (Finset.univ \ E) = 0 :=
      Finset.sum_eq_zero fun ω hω => by
        by_contra hne
        exact (Finset.mem_sdiff.1 hω).2
          (h ω (lt_of_le_of_ne (μ.prob_nonneg ω) (Ne.symm hne)))
    linarith

/-- A value has positive probability exactly when some outcome of positive weight takes it. -/
theorem FiniteProbSpace.dist_pos_iff (μ : FiniteProbSpace Ω) (X : Ω → α) (a : α) :
    0 < μ.dist X a ↔ ∃ ω, X ω = a ∧ 0 < μ.prob ω := by
  simp only [dist, probOf]
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have h0 : ∑ ω ∈ Finset.univ.filter (fun ω => X ω = a), μ.prob ω = 0 :=
      Finset.sum_eq_zero fun ω hω =>
        le_antisymm (hno ω (Finset.mem_filter.1 hω).2) (μ.prob_nonneg ω)
    exact h.ne' h0
  · rintro ⟨ω, hω, hpos⟩
    exact Finset.sum_pos' (fun ω _ => μ.prob_nonneg ω)
      ⟨ω, Finset.mem_filter.2 ⟨Finset.mem_univ _, hω⟩, hpos⟩

end Kolmogorov
