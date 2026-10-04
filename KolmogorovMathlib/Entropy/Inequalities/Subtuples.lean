import KolmogorovMathlib.Entropy.Inequalities.Fano

/-!
# Inequalities for three and for `n` variables

SUV Section 7.2, Problems 230–233, p. 225.

The inequality `2H(α, β, γ) ≤ H(α, β) + H(β, γ) + H(α, γ)`, conditional entropy under recoding,
the chain rule for subtuples `entropySub`, the `n`-variable inequality of Problem 231, the
Shearer inequality and the discrete Loomis–Whitney inequality
(`card_pow_le_prod_card_image`).
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Inequalities for three and for `n` variables -/

/-- **The entropy analogue of `2C(x, y, z) ≤ C(x, y) + C(y, z) + C(x, z)`**:
`2H(α, β, γ) ≤ H(α, β) + H(β, γ) + H(α, γ)`.  SUV Problem 230, p. 225. -/
theorem two_mul_entropy_triple_le (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    2 * entropy μ (pairRV (pairRV X Y) Z) ≤
      entropy μ (pairRV X Y) + entropy μ (pairRV Y Z) + entropy μ (pairRV X Z) := by
  have h1 := entropy_triple_add_entropy_le_add_entropy_pair μ X Y Z
  have h2 := entropy_pairRV_le_add μ (pairRV X Y) Z
  linarith

/-! ### Conditional entropy under recoding and the chain rule for subtuples -/

/-- `H(ξ|η) = H(⟨ξ,η⟩) − H(η)`, Theorem 142(d) solved for the conditional entropy. -/
theorem condEntropy_eq_sub (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    condEntropy μ X Y = entropy μ (pairRV X Y) - entropy μ Y := by
  rw [entropy_pairRV_eq_add_condEntropy]
  ring

/-- Recoding the variable and the condition along injective maps does not change the
conditional entropy. -/
theorem condEntropy_comp_of_injective {δ ε : Type*} [DecidableEq δ] [DecidableEq ε]
    (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) {g : α → δ} {h : β → ε}
    (hg : Function.Injective g) (hh : Function.Injective h) :
    condEntropy μ (g ∘ X) (h ∘ Y) = condEntropy μ X Y := by
  rw [condEntropy_eq_sub, condEntropy_eq_sub, entropy_comp_of_injective μ Y hh]
  have e := entropy_comp_of_injective μ (pairRV X Y) (hg.prodMap hh)
  have e' : entropy μ (pairRV (g ∘ X) (h ∘ Y)) = entropy μ (pairRV X Y) := e
  rw [e']

/-- **Conditioning on more does not increase entropy**: `H(ξ | η, ζ) ≤ H(ξ | ζ)`. -/
theorem condEntropy_pairRV_right_le (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : condEntropy μ X (pairRV Y Z) ≤ condEntropy μ X Z := by
  rw [condEntropy_eq_sub, condEntropy_eq_sub, ← entropy_pairRV_assoc]
  linarith [entropy_triple_add_entropy_le_add_entropy_pair μ X Y Z]

/-- **Conditioning on more does not increase entropy**: `H(ξ | η, ζ) ≤ H(ξ | η)`. -/
theorem condEntropy_pairRV_left_le (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : condEntropy μ X (pairRV Y Z) ≤ condEntropy μ X Y := by
  have h := condEntropy_comp_of_injective μ X (pairRV Y Z) Function.injective_id
    Prod.swap_injective
  have h' : condEntropy μ X (pairRV Z Y) = condEntropy μ X (pairRV Y Z) := h
  exact h'.symm.trans_le (condEntropy_pairRV_right_le μ X Z Y)

/-- Conditioning on a larger subtuple gives a smaller conditional entropy. -/
theorem condEntropy_subtuple_union_le {n : ℕ} (μ : FiniteProbSpace Ω) (Z : Ω → β)
    (X : Fin n → Ω → α) (I K : Finset (Fin n)) :
    condEntropy μ Z (subtuple X (I ∪ K)) ≤ condEntropy μ Z (subtuple X I) := by
  set g : (↥(I ∪ K) → α) → (↥I → α) × (↥K → α) :=
    fun h => (fun i : ↥I => h ⟨i.1, Finset.mem_union_left K i.2⟩,
      fun j : ↥K => h ⟨j.1, Finset.mem_union_right I j.2⟩) with hg_def
  have hg : Function.Injective g := by
    intro h₁ h₂ hh
    funext i
    rcases Finset.mem_union.1 i.2 with hi | hi
    · exact congrFun (congrArg Prod.fst hh) ⟨i.1, hi⟩
    · exact congrFun (congrArg Prod.snd hh) ⟨i.1, hi⟩
  have hcomp : pairRV (subtuple X I) (subtuple X K) = g ∘ subtuple X (I ∪ K) := rfl
  rw [← condEntropy_comp_of_injective μ Z (subtuple X (I ∪ K)) Function.injective_id hg,
    ← hcomp]
  exact condEntropy_pairRV_left_le μ Z _ _

/-- **The chain rule for subtuples**: `H(ξ_{I ∪ {i}}) = H(ξ_I) + H(ξ_i | ξ_I)`. -/
theorem entropySub_insert {n : ℕ} (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) (i : Fin n)
    (I : Finset (Fin n)) :
    entropySub μ X (insert i I) = entropySub μ X I + condEntropy μ (X i) (subtuple X I) := by
  rw [Finset.insert_eq, entropySub_union, entropy_pairRV_eq_add_condEntropy]
  simp only [entropySub]
  congr 1
  have hg : Function.Injective fun a : α => (fun _ : ↥({i} : Finset (Fin n)) => a) := by
    intro a b h
    exact congrFun h ⟨i, Finset.mem_singleton_self i⟩
  have hcomp : subtuple X {i} = (fun a : α => fun _ : ↥({i} : Finset (Fin n)) => a) ∘ X i := by
    funext ω j
    exact congrArg (fun t => X t ω) (Finset.mem_singleton.1 j.2)
  have e := condEntropy_comp_of_injective μ (X i) (subtuple X I) hg Function.injective_id
  rw [hcomp]
  exact e

/-- **The chain rule for a subtuple, summed**: `H(ξ_S) = ∑_{i ∈ S} H(ξ_i | ξ_{S, <i})`, the
condition of the `i`th term being the members of `S` of smaller index. -/
theorem entropySub_eq_sum_condEntropy {n : ℕ} (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (S : Finset (Fin n)) :
    entropySub μ X S =
      ∑ i ∈ S, condEntropy μ (X i) (subtuple X (S.filter fun j => j < i)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hfa : ((insert a s).filter fun j => j < a) = s := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl a), Finset.filter_true_of_mem hlt]
    have hfi : ∀ i ∈ s, ((insert a s).filter fun j => j < i) = s.filter fun j => j < i :=
      fun i hi => by rw [Finset.filter_insert, ite_eq_right (lt_asymm (hlt i hi))]
    rw [Finset.sum_insert ha, entropySub_insert, hfa, ih, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hfi i hi]

/-- `∑_{i ∈ S} H(ξ_i | ξ_{<i}) ≤ H(ξ_S)`: the terms of the chain rule for `ξ_S`, with each
condition enlarged to all the variables of smaller index. -/
theorem sum_condEntropy_le_entropySub {n : ℕ} (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, condEntropy μ (X i) (subtuple X (Finset.univ.filter fun j => j < i)) ≤
      entropySub μ X S := by
  rw [entropySub_eq_sum_condEntropy]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := condEntropy_subtuple_union_le μ (X i) X (S.filter fun j => j < i)
    ((Finset.univ.filter fun j => j < i) \ S.filter fun j => j < i)
  rwa [Finset.union_sdiff_of_subset (Finset.filter_subset_filter _ (Finset.subset_univ S))] at h

/-- **The Shearer inequality.**  If `T₁, …, T_k` are tuples made of the variables `α₁, …, α_n` and
every variable occurs in exactly `r` of them, then `r H(α₁, …, α_n) ≤ H(T₁) + … + H(T_k)`.
SUV Problem 232, p. 225. -/
theorem mul_entropySub_univ_le_sum_of_uniform_cover {n k r : ℕ} (μ : FiniteProbSpace Ω)
    (X : Fin n → Ω → α) (T : Fin k → Finset (Fin n))
    (hT : ∀ i : Fin n, (Finset.univ.filter fun j : Fin k => i ∈ T j).card = r) :
    (r : ℝ) * entropySub μ X Finset.univ ≤ ∑ j : Fin k, entropySub μ X (T j) := by
  set c : Fin n → ℝ :=
    fun i => condEntropy μ (X i) (subtuple X (Finset.univ.filter fun j => j < i)) with hc
  have huniv : entropySub μ X Finset.univ = ∑ i, c i :=
    entropySub_eq_sum_condEntropy μ X Finset.univ
  calc (r : ℝ) * entropySub μ X Finset.univ = ∑ i, (r : ℝ) * c i := by
        rw [huniv, Finset.mul_sum]
    _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin k => i ∈ T j), c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, hT i, nsmul_eq_mul]
    _ = ∑ j : Fin k, ∑ i ∈ T j, c i := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ ∑ j : Fin k, entropySub μ X (T j) :=
        Finset.sum_le_sum fun j _ => sum_condEntropy_le_entropySub μ X (T j)

/-- **The `n`-variable inequality**: `(n − 1) H(α₁, …, α_n) ≤ ∑_i H(α₁, …, α̂_i, …, α_n)`, the
right-hand side having one term for each omitted variable.  This is the Shearer inequality for
the cover by the `n` sets `{1, …, n} ∖ {i}`, in which every variable occurs `n − 1` times.
SUV Problem 231, p. 225. -/
theorem sub_one_mul_entropySub_univ_le_sum {n : ℕ} (μ : FiniteProbSpace Ω) (X : Fin n → Ω → α) :
    ((n : ℝ) - 1) * entropySub μ X Finset.univ ≤
      ∑ i : Fin n, entropySub μ X (Finset.univ.erase i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := mul_entropySub_univ_le_sum_of_uniform_cover μ X (fun j => Finset.univ.erase j)
      (r := n - 1) fun i => by
        have hfil : (Finset.univ.filter fun j : Fin n => i ∈ Finset.univ.erase j)
            = Finset.univ.erase i := by
          ext j
          simp [Finset.mem_erase, ne_comm]
        rw [hfil, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    rw [hcast] at h
    exact h

/-- The uniform distribution on a non-empty finite set `A` of integer points, as a probability
space on the subtype `A`: the first step of the entropy proof of Loomis–Whitney. -/
private noncomputable def uniformOn {n : ℕ} {A : Finset (Fin n → ℤ)} (hA : A.Nonempty) :
    FiniteProbSpace A where
  prob := fun _ => 1 / A.card
  prob_nonneg := fun _ => by positivity
  sum_prob := by
    have h : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one_div_cancel h]

/-- Under the uniform distribution on `A`, an injective random variable has entropy `log |A|`:
every value is taken with probability `1/|A|`. -/
private theorem entropy_uniformOn_of_injective {n : ℕ} {A : Finset (Fin n → ℤ)}
    (hA : A.Nonempty) {β : Type*} [DecidableEq β] {X : A → β} (hX : Function.Injective X) :
    entropy (uniformOn hA) X = Real.logb 2 A.card := by
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hdist : ∀ b ∈ rangeFinset X, (uniformOn hA).dist X b = 1 / A.card := by
    intro b hb
    obtain ⟨a, rfl⟩ := mem_rangeFinset.1 hb
    have hfib : (Finset.univ.filter fun ω : A => X ω = X a) = {a} := by
      ext ω
      simp [hX.eq_iff]
    rw [FiniteProbSpace.dist, FiniteProbSpace.probOf, hfib, Finset.sum_singleton]
    rfl
  have hrange : (rangeFinset X).card = A.card := by
    rw [rangeFinset, Finset.card_image_of_injective _ hX, Finset.card_univ, Fintype.card_coe]
  rw [entropy, Finset.sum_congr rfl fun b hb => by rw [hdist b hb], Finset.sum_const, hrange,
    nsmul_eq_mul, negMulLog2_eq, one_div, Real.logb_inv, neg_mul_neg, ← mul_assoc,
    mul_inv_cancel₀ hcard, one_mul]

/-- **Theorem 139 in terms of the range**: a random variable taking `m` values has entropy at
most `log m`. -/
private theorem entropy_le_logb_card_rangeFinset (μ : FiniteProbSpace Ω) (X : Ω → α) :
    entropy μ X ≤ Real.logb 2 (rangeFinset X).card := by
  let X' : Ω → rangeFinset X := fun ω => ⟨X ω, mem_rangeFinset.2 ⟨ω, rfl⟩⟩
  have huniv : rangeFinset X' = Finset.univ := by
    ext ⟨a, ha⟩
    obtain ⟨ω, hω⟩ := mem_rangeFinset.1 ha
    exact ⟨fun _ => Finset.mem_univ _, fun _ => mem_rangeFinset.2 ⟨ω, Subtype.ext hω⟩⟩
  have hsum : ∑ a, μ.dist X' a = 1 := by
    rw [← huniv]
    exact μ.sum_dist_eq_one X'
  calc entropy μ X = entropy μ (Subtype.val ∘ X') := rfl
    _ = entropy μ X' := entropy_comp_of_injective μ X' Subtype.val_injective
    _ = entropyDist (μ.dist X') := entropy_eq_entropyDist μ X'
    _ ≤ Real.logb 2 (Fintype.card (rangeFinset X)) :=
        entropyDist_le_logb_card (μ.dist_nonneg X') hsum
    _ = Real.logb 2 (rangeFinset X).card := by rw [Fintype.card_coe]

/-- The coordinates of a uniformly random point of `A`, as an `n`-tuple of random variables. -/
private def coordRV {n : ℕ} (A : Finset (Fin n → ℤ)) : Fin n → A → ℤ := fun i a => a.val i

/-- The entropy of the whole tuple of coordinates of a uniformly random point of `A` is
`log |A|`: the tuple determines the point. -/
private theorem entropySub_univ_uniformOn {n : ℕ} {A : Finset (Fin n → ℤ)} (hA : A.Nonempty) :
    entropySub (uniformOn hA) (coordRV A) Finset.univ = Real.logb 2 A.card := by
  refine entropy_uniformOn_of_injective hA fun a b h => Subtype.ext (funext fun i => ?_)
  exact congrFun h ⟨i, Finset.mem_univ i⟩

/-- The tuple of all coordinates but the `i`th of a uniformly random point of `A` is a function
of the projection `a ↦ update a i 0`, so its entropy is at most the logarithm of the number of
projected points. -/
private theorem entropySub_erase_uniformOn_le {n : ℕ} {A : Finset (Fin n → ℤ)}
    (hA : A.Nonempty) (i : Fin n) :
    entropySub (uniformOn hA) (coordRV A) (Finset.univ.erase i) ≤
      Real.logb 2 ((A.image fun a => Function.update a i 0).card : ℝ) := by
  set P : A → (Fin n → ℤ) := fun a => Function.update a.val i 0 with hP
  have hcomp : subtuple (coordRV A) (Finset.univ.erase i) =
      (fun v : Fin n → ℤ => fun j : (Finset.univ.erase i : Finset (Fin n)) => v j.val) ∘ P := by
    funext a j
    have hj : j.val ≠ i := (Finset.mem_erase.1 j.property).1
    simp [subtuple, coordRV, hP, Function.update_of_ne hj]
  have hrange : rangeFinset P = A.image fun a => Function.update a i 0 := by
    ext v
    simp [rangeFinset, hP, Subtype.exists]
  calc entropySub (uniformOn hA) (coordRV A) (Finset.univ.erase i)
      ≤ entropy (uniformOn hA) P := by
        unfold entropySub
        rw [hcomp]
        exact entropy_comp_le (uniformOn hA) P
          fun v : Fin n → ℤ => fun j : (Finset.univ.erase i : Finset (Fin n)) => v j.val
    _ ≤ Real.logb 2 (rangeFinset P).card := entropy_le_logb_card_rangeFinset _ _
    _ = _ := by rw [hrange]

/-- **The discrete Loomis–Whitney inequality.**  For a finite set `A` of integer points of
`ℤ^n`, the `(n − 1)`st power of `|A|` is at most the product of the sizes of the `n` projections
of `A` onto the coordinate hyperplanes (a projection is realised by setting one coordinate to
zero).  The set is non-empty (for `A = ∅` and `n = 1` the left side is `0⁰ = 1`).  It is obtained
from Problem 231 by taking the uniform distribution on `A`.

**Weaker than the printed statement**: the book asks for the bound `V^{n−1} ≤ V₁ ⋯ V_n` on the
volume of an `n`-dimensional body and the volumes of its projections onto the coordinate
hyperplanes, and mentions the discrete case only in the hint, as the first step.  "Body" is not
defined on the page, projections of measurable sets need not be measurable, and the passage to
the limit is only hinted at, so only the discrete inequality is stated.
SUV Problem 233, p. 225. -/
theorem card_pow_le_prod_card_image {n : ℕ} {A : Finset (Fin n → ℤ)} (hA : A.Nonempty) :
    (A.card : ℝ) ^ (n - 1) ≤
      ∏ i : Fin n, ((A.image fun a => Function.update a i 0).card : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.zero_sub, pow_zero, Finset.univ_eq_empty, Finset.prod_empty, le_refl]
  · have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hposi : ∀ i : Fin n, (0 : ℝ) < ((A.image fun a => Function.update a i 0).card : ℝ) :=
      fun i => by exact_mod_cast (hA.image _).card_pos
    have h := sub_one_mul_entropySub_univ_le_sum (uniformOn hA) (coordRV A)
    rw [entropySub_univ_uniformOn hA] at h
    have h2 : ((n : ℝ) - 1) * Real.logb 2 A.card ≤
        ∑ i : Fin n, Real.logb 2 ((A.image fun a => Function.update a i 0).card : ℝ) :=
      h.trans (Finset.sum_le_sum fun i _ => entropySub_erase_uniformOn_le hA i)
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
    rw [← Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (pow_pos hpos _)
      (Finset.prod_pos fun i _ => hposi i), Real.logb_pow, hcast,
      Real.logb_prod _ _ fun i _ => (hposi i).ne']
    exact h2

end Kolmogorov
