import KolmogorovMathlib.Entropy.Inequalities.Independence

/-!
# Mutual information, Fano's inequality and perfect secrecy

SUV Section 7.2, Problems 224–226 and 228–229, pp. 223–225.

Monotonicity of mutual information, its chain rule and the data-processing inequality, Fano's
inequality `H(α | β) ≤ P(α ≠ f(β)) log₂ |A| + h(P(α ≠ f(β)))` with the binary entropy function
`binaryEntropy`, and Shannon's theorem on perfect cryptosystems.
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Mutual information: monotonicity, the chain rule and data processing -/

/-- **Mutual information increases with the first argument**: `I(⟨α, β⟩ : γ) ≥ I(α : γ)`.
SUV Problem 224, p. 223. -/
theorem mutualInfo_le_mutualInfo_pairRV (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : mutualInfo μ X Z ≤ mutualInfo μ (pairRV X Y) Z := by
  unfold mutualInfo
  have h1 := entropy_triple_add_entropy_le_add_entropy_pair μ Y Z X
  have h2 : entropy μ (pairRV (pairRV Y Z) X) = entropy μ (pairRV (pairRV X Y) Z) := by
    rw [entropy_pairRV_comm, entropy_pairRV_assoc]
  have h3 := entropy_pairRV_comm μ Y X
  have h4 := entropy_pairRV_comm μ Z X
  linarith

/-- **The chain rule for mutual information**:
`I(⟨α, β⟩ : γ) = I(α : γ) + I(β : γ | α)`.  SUV Problem 225, p. 223. -/
theorem mutualInfo_pairRV_eq_add_condMutualInfo (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    mutualInfo μ (pairRV X Y) Z = mutualInfo μ X Z + condMutualInfo μ Y Z X := by
  unfold mutualInfo condMutualInfo
  have h1 := entropy_pairRV_eq_add_condEntropy μ Y X
  have h2 := entropy_pairRV_eq_add_condEntropy μ Z X
  have h3 := entropy_pairRV_eq_add_condEntropy μ (pairRV Y Z) X
  have h4 := entropy_pairRV_comm μ X Y
  have h5 := entropy_pairRV_comm μ X Z
  have h6 : entropy μ (pairRV (pairRV Y Z) X) = entropy μ (pairRV (pairRV X Y) Z) := by
    rw [entropy_pairRV_comm, entropy_pairRV_assoc]
  linarith

/-- **The data-processing inequality.**  If `α` and `γ` are independent relative to `β`, i.e.
`I(α : γ | β) = 0` (a Markov chain `α – β – γ`), then `I(α : γ) ≤ I(α : β)`.
SUV Problem 226, p. 223. -/
theorem mutualInfo_le_mutualInfo_of_condMutualInfo_eq_zero (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) (h : condMutualInfo μ X Z Y = 0) :
    mutualInfo μ X Z ≤ mutualInfo μ X Y := by
  unfold mutualInfo
  unfold condMutualInfo at h
  have h1 := entropy_pairRV_eq_add_condEntropy μ X Y
  have h2 := entropy_pairRV_eq_add_condEntropy μ Z Y
  have h3 := entropy_pairRV_eq_add_condEntropy μ (pairRV X Z) Y
  have h4 := entropy_triple_add_entropy_le_add_entropy_pair μ X Y Z
  have h5 := entropy_pairRV_swap_right μ X Y Z
  have h6 := entropy_pairRV_comm μ Y Z
  linarith

/-- **The information passing through a Markov chain is bounded by the entropy of the middle
variable**: `I(α : γ | β) = 0` implies `I(α : γ) ≤ H(β)`.  SUV Problem 226, p. 223. -/
theorem mutualInfo_le_entropy_of_condMutualInfo_eq_zero (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) (h : condMutualInfo μ X Z Y = 0) :
    mutualInfo μ X Z ≤ entropy μ Y := by
  have h1 := mutualInfo_le_mutualInfo_of_condMutualInfo_eq_zero μ X Y Z h
  have h2 := entropy_le_entropy_pairRV_left μ X Y
  unfold mutualInfo at h1 ⊢
  linarith
/-! ### Fano's inequality and perfect secrecy -/

/-- The entropy of a two-valued distribution with probabilities `ε` and `1 − ε`, the function
`h(ε)` of Fano's inequality.  SUV Problem 228, p. 224. -/
noncomputable def binaryEntropy (ε : ℝ) : ℝ := negMulLog2 ε + negMulLog2 (1 - ε)

/-- Adjoining a variable to the conditioned side does not decrease conditional entropy:
`H(ξ|η) ≤ H(⟨ξ, ζ⟩|η)`. -/
private theorem condEntropy_le_condEntropy_pairRV_left (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) : condEntropy μ X Y ≤ condEntropy μ (pairRV X Z) Y := by
  have h1 := entropy_pairRV_eq_add_condEntropy μ X Y
  have h2 := entropy_pairRV_eq_add_condEntropy μ (pairRV X Z) Y
  have h3 := entropy_pairRV_swap_right μ X Z Y
  have h4 := entropy_le_entropy_pairRV_left μ (pairRV X Y) Z
  linarith

/-- **The chain rule for conditional entropy**: `H(⟨ξ, ζ⟩|η) = H(ζ|η) + H(ξ|η, ζ)`. -/
private theorem condEntropy_pairRV_eq_add_condEntropy_pairRV (μ : FiniteProbSpace Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    condEntropy μ (pairRV X Z) Y = condEntropy μ Z Y + condEntropy μ X (pairRV Y Z) := by
  have h1 := entropy_pairRV_eq_add_condEntropy μ (pairRV X Z) Y
  have h2 := entropy_pairRV_eq_add_condEntropy μ Z Y
  have h3 := entropy_pairRV_eq_add_condEntropy μ X (pairRV Y Z)
  have h4 := entropy_pairRV_swap_right μ X Z Y
  have h5 := entropy_pairRV_assoc μ X Y Z
  have h6 := entropy_pairRV_comm μ Z Y
  linarith

/-- The entropy of the indicator of `α ≠ β` is `h(Pr[α ≠ β])`. -/
private theorem entropy_mismatch_eq_binaryEntropy (μ : FiniteProbSpace Ω) (X Y : Ω → α) :
    entropy μ (fun ω => decide (X ω ≠ Y ω)) =
      binaryEntropy (μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω)) := by
  have htrue : μ.dist (fun ω => decide (X ω ≠ Y ω)) true =
      μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) := by
    simp [FiniteProbSpace.dist]
  have hfalse : μ.dist (fun ω => decide (X ω ≠ Y ω)) false =
      1 - μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) := by
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => X ω ≠ Y ω) μ.prob
    rw [μ.sum_prob] at hpart
    have hf : (Finset.univ.filter fun ω => decide (X ω ≠ Y ω) = false) =
        Finset.univ.filter fun ω => ¬ X ω ≠ Y ω := by
      ext ω
      simp
    rw [FiniteProbSpace.dist, FiniteProbSpace.probOf, hf]
    unfold FiniteProbSpace.probOf
    linarith
  rw [entropy_eq_entropyDist, entropyDist, Fintype.sum_bool, htrue, hfalse, binaryEntropy]

/-- The function `h` is increasing on `[0, 1/2]`, so `Pr[α ≠ β] ≤ ε < 1/2` gives
`h(Pr[α ≠ β]) ≤ h(ε)`. -/
private theorem binaryEntropy_mono_of_le_half {p ε : ℝ} (hp : 0 ≤ p) (hpε : p ≤ ε)
    (hε : ε < 1 / 2) : binaryEntropy p ≤ binaryEntropy ε := by
  have hc := Real.concaveOn_negMulLog
  set t : ℝ := (1 - p - ε) / (1 - 2 * p) with ht
  have h2p : 0 < 1 - 2 * p := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) h2p.le
  have ht1 : 0 ≤ 1 - t := by
    rw [ht, sub_nonneg, div_le_one h2p]
    linarith
  have hsum : t + (1 - t) = 1 := by ring
  have hkey : t * (1 - 2 * p) = 1 - p - ε := by
    rw [ht]
    exact div_mul_cancel₀ _ h2p.ne'
  have hε1 : t * p + (1 - t) * (1 - p) = ε := by linear_combination -hkey
  have hε2 : t * (1 - p) + (1 - t) * p = 1 - ε := by linear_combination hkey
  have hpI : p ∈ Set.Ici (0 : ℝ) := hp
  have h1pI : 1 - p ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith)
  have h1 := hc.2 hpI h1pI ht0 ht1 hsum
  have h2 := hc.2 h1pI hpI ht0 ht1 hsum
  simp only [smul_eq_mul] at h1 h2
  rw [hε1] at h1
  rw [hε2] at h2
  unfold binaryEntropy negMulLog2
  rw [← add_div, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le
  linarith


private theorem condEntropyGiven_le_logb_card_rangeFinset (μ : FiniteProbSpace Ω) (X : Ω → α)
    (E : Finset Ω) :
    condEntropyGiven μ X E ≤ Real.logb 2 ((rangeFinset X).card : ℝ) := by
  let p : rangeFinset X → ℝ := fun a => μ.condDist X E a.1
  have hp : ∀ a, 0 ≤ p a := fun a => μ.condDist_nonneg _ _ _
  have h_eq : condEntropyGiven μ X E = ∑ a : rangeFinset X, negMulLog2 (p a) := by
    unfold condEntropyGiven p
    have H : ∑ a ∈ rangeFinset X, negMulLog2 (μ.condDist X E a) =
        ∑ a ∈ (Finset.univ : Finset (rangeFinset X)), negMulLog2 (μ.condDist X E a.1) := by
      exact Finset.sum_attach _ _ |>.symm
    exact H
  rw [h_eq]
  by_cases he : 0 < μ.probOf E
  · have hsum : ∑ a : rangeFinset X, p a = 1 := by
      have h_eq1 : ∑ a : rangeFinset X, p a = ∑ a ∈ rangeFinset X, μ.condDist X E a := by
        unfold p
        have H : ∑ a ∈ (Finset.univ : Finset (rangeFinset X)), μ.condDist X E a.1 =
            ∑ a ∈ rangeFinset X, μ.condDist X E a := by
          exact Finset.sum_attach _ _
        exact H
      have h_eq3 : ∑ a ∈ rangeFinset X, μ.condDist X E a = 1 := μ.sum_condDist_eq_one X he
      rw [h_eq1, h_eq3]
    have h_le := entropyDist_le_logb_card hp hsum
    unfold entropyDist at h_le
    have h_card : Fintype.card (rangeFinset X) = (rangeFinset X).card := Fintype.card_coe _
    rw [h_card] at h_le
    exact h_le
  · have h0 : μ.probOf E = 0 := le_antisymm (not_lt.1 he) (μ.probOf_nonneg _)
    have H0 : ∀ a, p a = 0 := by
      intro a
      unfold p FiniteProbSpace.condDist
      rw [h0, div_zero]
    have H_sum0 : ∑ a : rangeFinset X, negMulLog2 (p a) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [H0 a, negMulLog2_zero]
    rw [H_sum0]
    have hlog_nonneg : 0 ≤ Real.logb 2 ((rangeFinset X).card : ℝ) := by
      apply Real.logb_nonneg
      · norm_num
      · have h_card : 1 ≤ (rangeFinset X).card := by
          rw [Nat.one_le_iff_ne_zero, ne_eq, Finset.card_eq_zero]
          rw [← Finset.not_nonempty_iff_eq_empty, not_not]
          obtain ⟨ω⟩ : Nonempty Ω := by
            by_contra hΩ
            have : IsEmpty Ω := not_nonempty_iff.1 hΩ
            simpa using μ.sum_prob
          use X ω
          rw [mem_rangeFinset]
          use ω
        exact_mod_cast h_card
    exact hlog_nonneg

private theorem condEntropyGiven_mismatch_eq_zero_of_false {Ω α : Type*} [Fintype Ω]
    [DecidableEq α] (μ : FiniteProbSpace Ω) (X Y : Ω → α)
    (b : α × Bool) (hb : b.2 = false) :
    condEntropyGiven μ X (Finset.univ.filter fun ω =>
      pairRV Y (fun ω => decide (X ω ≠ Y ω)) ω = b) = 0 := by
  let Y' : Ω → α × Bool := pairRV Y fun ω => decide (X ω ≠ Y ω)
  unfold condEntropyGiven
  apply Finset.sum_eq_zero
  intro a _
  by_cases h_cond : μ.condDist X (Finset.univ.filter fun ω => Y' ω = b) a = 0
  · rw [h_cond, negMulLog2_zero]
  · have h_cond_one : μ.condDist X (Finset.univ.filter fun ω => Y' ω = b) a = 1 := by
      unfold FiniteProbSpace.condDist
      have h_pos : 0 < μ.probOf (Finset.univ.filter fun ω => Y' ω = b) := by
        by_contra hp
        have h0 : μ.probOf (Finset.univ.filter fun ω => Y' ω = b) = 0 :=
          le_antisymm (not_lt.1 hp) (μ.probOf_nonneg _)
        have h_cond_zero : μ.condDist X (Finset.univ.filter fun ω => Y' ω = b) a = 0 := by
          unfold FiniteProbSpace.condDist
          rw [h0, div_zero]
        exact h_cond h_cond_zero
      have ha_eq_b1 : a = b.1 := by
        have h_cond_pos : 0 < μ.condDist X (Finset.univ.filter fun ω => Y' ω = b) a := by
          exact lt_of_le_of_ne (μ.condDist_nonneg X _ _) (Ne.symm h_cond)
        unfold FiniteProbSpace.condDist at h_cond_pos
        have h_num_pos : 0 < μ.probOf ((Finset.univ.filter fun ω => Y' ω = b).filter
            fun ω => X ω = a) := by
          exact ((div_pos_iff_of_pos_right h_pos).1 h_cond_pos)
        have h_num_ne_zero : μ.probOf ((Finset.univ.filter fun ω => Y' ω = b).filter
            fun ω => X ω = a) ≠ 0 := ne_of_gt h_num_pos
        have h_nonempty : ((Finset.univ.filter fun ω => Y' ω = b).filter
            fun ω => X ω = a).Nonempty := by
          by_contra hn
          have hE : ((Finset.univ.filter fun ω => Y' ω = b).filter fun ω => X ω = a) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.1 hn
          rw [hE] at h_num_ne_zero
          have hE2 : μ.probOf ∅ = 0 := by
            unfold FiniteProbSpace.probOf
            rw [Finset.sum_empty]
          exact h_num_ne_zero hE2
        obtain ⟨ω, hω⟩ := h_nonempty
        rw [Finset.mem_filter, Finset.mem_filter] at hω
        have hy : Y' ω = b := hω.1.2
        have hx : X ω = Y ω := by
          have h1 : (decide (X ω ≠ Y ω)) = false := by
            calc (decide (X ω ≠ Y ω)) = (Y' ω).2 := rfl
              _ = b.2 := congrArg Prod.snd hy
              _ = false := hb
          exact of_not_not (decide_eq_false_iff_not.1 h1)
        have hy_val : Y ω = b.1 := congrArg Prod.fst hy
        have hxa : X ω = a := hω.2
        rw [← hxa, hx, hy_val]
      have h_prob_eq : μ.probOf ((Finset.univ.filter fun ω => Y' ω = b).filter
          fun ω => X ω = a) = μ.probOf (Finset.univ.filter fun ω => Y' ω = b) := by
        congr 1
        ext ω
        rw [Finset.mem_filter, Finset.mem_filter]
        constructor
        · intro h; exact h.1
        · intro h
          have hy : Y' ω = b := h.2
          have hx : X ω = Y ω := by
            have h1 : (decide (X ω ≠ Y ω)) = false := by
              calc (decide (X ω ≠ Y ω)) = (Y' ω).2 := rfl
                _ = b.2 := congrArg Prod.snd hy
                _ = false := hb
            exact of_not_not (decide_eq_false_iff_not.1 h1)
          have hy_val : Y ω = b.1 := congrArg Prod.fst hy
          have hxa : X ω = a := by
            rw [hx, hy_val, ← ha_eq_b1]
          exact ⟨h, hxa⟩
      rw [h_prob_eq, div_self (ne_of_gt h_pos)]
    rw [h_cond_one, negMulLog2_one]

private theorem sum_dist_pairRV_mismatch_eq_probOf_mismatch {Ω α : Type*} [Fintype Ω]
    [DecidableEq α] (μ : FiniteProbSpace Ω) (X Y : Ω → α) :
    (∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true)
      (rangeFinset (pairRV Y fun ω => decide (X ω ≠ Y ω))),
      μ.dist (pairRV Y fun ω => decide (X ω ≠ Y ω)) b) =
    μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) := by
  let Y' : Ω → α × Bool := pairRV Y fun ω => decide (X ω ≠ Y ω)
  unfold FiniteProbSpace.dist FiniteProbSpace.probOf
  have : DecidableEq Ω := Classical.decEq Ω
  have h_eq : ∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
      ∑ ω ∈ Finset.univ.filter fun ω => Y' ω = b, μ.prob ω =
      ∑ ω ∈ Finset.univ.filter fun ω => X ω ≠ Y ω, μ.prob ω := by
    have H_disj : (∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
        ∑ ω ∈ Finset.univ.filter fun ω => Y' ω = b, μ.prob ω) =
        ∑ ω ∈ Finset.biUnion (Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'))
          (fun b => Finset.univ.filter fun ω => Y' ω = b), μ.prob ω := by
      symm
      apply Finset.sum_biUnion
      intro x _ y _ hxy
      apply Finset.disjoint_left.2
      intro ω hwx hwy
      rw [Finset.mem_filter] at hwx hwy
      have hx : Y' ω = x := hwx.2
      have hy : Y' ω = y := hwy.2
      exact hxy (hx.symm.trans hy)
    rw [H_disj]
    apply Finset.sum_congr
    · ext ω
      rw [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro ⟨b, hb, hωb⟩
        rw [Finset.mem_filter] at hb hωb
        have hy : (Y' ω).2 = true := by
          rw [hωb.2]
          exact hb.2
        unfold Y' pairRV at hy
        have hx : X ω ≠ Y ω := by
          have h1 : (decide (X ω ≠ Y ω)) = true := hy
          exact decide_eq_true_iff.1 h1
        exact ⟨Finset.mem_univ _, hx⟩
      · intro hω
        have hx : X ω ≠ Y ω := hω.2
        have h_y_val : (Y' ω).2 = true := by
          unfold Y' pairRV
          exact decide_eq_true_iff.2 hx
        use Y' ω
        constructor
        · rw [Finset.mem_filter]
          constructor
          · rw [mem_rangeFinset]
            use ω
          · exact h_y_val
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  exact h_eq

/-- Given `β` and the indicator of `α ≠ β`, the variable `α` is determined when the indicator
is `0` and takes at most `|range α|` values when it is `1`, so `H(α | β, [α ≠ β])` is at most
`Pr[α ≠ β] · log |range α|`. -/
private theorem condEntropy_pairRV_mismatch_le (μ : FiniteProbSpace Ω) (X Y : Ω → α) :
    condEntropy μ X (pairRV Y fun ω => decide (X ω ≠ Y ω)) ≤
      μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) *
        Real.logb 2 ((rangeFinset X).card : ℝ) := by
  let Y' : Ω → α × Bool := pairRV Y fun ω => decide (X ω ≠ Y ω)
  have H : condEntropy μ X Y' = ∑ b ∈ rangeFinset Y',
      μ.dist Y' b * condEntropyGiven μ X (Finset.univ.filter fun ω => Y' ω = b) := rfl
  rw [H]
  have H0 : ∀ b : α × Bool, b.2 = false →
      condEntropyGiven μ X (Finset.univ.filter fun ω => Y' ω = b) = 0 := by
    intro b hb
    exact condEntropyGiven_mismatch_eq_zero_of_false μ X Y b hb
  have H1 : ∑ b ∈ rangeFinset Y', μ.dist Y' b *
      condEntropyGiven μ X (Finset.univ.filter fun ω => Y' ω = b) =
      ∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
        μ.dist Y' b * condEntropyGiven μ X (Finset.univ.filter fun ω => Y' ω = b) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb_in hb_not_filter
    rw [Finset.mem_filter, not_and] at hb_not_filter
    have hb2 : b.2 = false := by
      have hbool : b.2 = true ∨ b.2 = false := by cases b.2 <;> simp
      rcases hbool with ht | hf
      · exact (hb_not_filter hb_in ht).elim
      · exact hf
    rw [H0 b hb2, mul_zero]
  rw [H1]
  have H2 : ∀ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
      condEntropyGiven μ X (Finset.univ.filter fun ω => Y' ω = b) ≤
        Real.logb 2 ((rangeFinset X).card : ℝ) := by
    intro b _
    exact condEntropyGiven_le_logb_card_rangeFinset μ X _
  have H3 : ∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
      μ.dist Y' b * condEntropyGiven μ X (Finset.univ.filter fun ω => Y' ω = b) ≤
      ∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
        μ.dist Y' b * Real.logb 2 ((rangeFinset X).card : ℝ) := by
    apply Finset.sum_le_sum
    intro b hb
    apply mul_le_mul_of_nonneg_left (H2 b hb) (μ.dist_nonneg Y' b)
  have H4 : ∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'),
      μ.dist Y' b * Real.logb 2 ((rangeFinset X).card : ℝ) =
      (∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'), μ.dist Y' b) *
        Real.logb 2 ((rangeFinset X).card : ℝ) := by
    rw [Finset.sum_mul]
  have H5 : (∑ b ∈ Finset.filter (fun b : α × Bool => b.2 = true) (rangeFinset Y'), μ.dist Y' b) =
      μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) := by
    exact sum_dist_pairRV_mismatch_eq_probOf_mismatch μ X Y
  exact H3.trans (by rw [H4, H5])

/-- **Fano's inequality.**  If `α` and `β` differ with probability at most `ε` and `α` takes at
most `a` values, then `H(α|β) ≤ ε log a + h(ε)`.  The smallness hypothesis is the printed
`ε < 1/2`; it is what makes `h` increasing on the relevant range, so that `Pr[α ≠ β] ≤ ε` may be
replaced by `ε` inside `h`.  The hypothesis `0 ≤ ε` is implied by `hne`.

This is the printed bound; the sharp form of Fano's inequality, with `log (a − 1)` in place of
`log a`, is stronger and is not what the page states.  SUV Problem 228, pp. 224–225. -/
theorem condEntropy_le_mul_logb_add_binaryEntropy (μ : FiniteProbSpace Ω) (X Y : Ω → α)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hne : μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) ≤ ε) {a : ℕ}
    (ha : (rangeFinset X).card ≤ a) :
    condEntropy μ X Y ≤ ε * Real.logb 2 (a : ℝ) + binaryEntropy ε := by
  set E : Ω → Bool := fun ω => decide (X ω ≠ Y ω) with hE
  set p := μ.probOf (Finset.univ.filter fun ω => X ω ≠ Y ω) with hp
  have hp0 : 0 ≤ p := μ.probOf_nonneg _
  have hcard : 1 ≤ (rangeFinset X).card := by
    rcases isEmpty_or_nonempty Ω with h | ⟨⟨ω₀⟩⟩
    · simpa using μ.sum_prob
    · exact Finset.Nonempty.card_pos ⟨X ω₀, mem_rangeFinset.2 ⟨ω₀, rfl⟩⟩
  have hcardR : (1 : ℝ) ≤ (rangeFinset X).card := by exact_mod_cast hcard
  have hlog0 : 0 ≤ Real.logb 2 ((rangeFinset X).card : ℝ) := Real.logb_nonneg (by norm_num) hcardR
  have hlog : Real.logb 2 ((rangeFinset X).card : ℝ) ≤ Real.logb 2 (a : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast ha)
  have h1 := condEntropy_le_condEntropy_pairRV_left μ X Y E
  have h2 := condEntropy_pairRV_eq_add_condEntropy_pairRV μ X Y E
  have h3 := condEntropy_le_entropy μ E Y
  have h4 := entropy_mismatch_eq_binaryEntropy μ X Y
  have h5 := binaryEntropy_mono_of_le_half hp0 hne hε
  have h6 := condEntropy_pairRV_mismatch_le μ X Y
  have h7 : p * Real.logb 2 ((rangeFinset X).card : ℝ) ≤ ε * Real.logb 2 (a : ℝ) :=
    mul_le_mul hne hlog hlog0 hε0
  linarith

/-- **Shannon's theorem on perfect cryptosystems.**  If the message `α` is determined by the
ciphertext `β` together with the key `γ` (`H(α|β,γ) = 0`) and the ciphertext carries no
information about the message (`I(β:α) = 0`), then the key has at least the entropy of the
message.  SUV Problem 229, p. 225. -/
theorem entropy_le_entropy_of_condEntropy_pairRV_eq_zero (μ : FiniteProbSpace Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) (h1 : condEntropy μ X (pairRV Y Z) = 0)
    (h2 : mutualInfo μ Y X = 0) : entropy μ X ≤ entropy μ Z := by
  unfold mutualInfo at h2
  have h3 := entropy_pairRV_eq_add_condEntropy μ X (pairRV Y Z)
  have h4 := entropy_pairRV_comm μ Y X
  have h5 : entropy μ (pairRV X Y) ≤ entropy μ (pairRV X (pairRV Y Z)) := by
    rw [← entropy_pairRV_assoc]
    exact entropy_le_entropy_pairRV_left μ _ Z
  have h6 := entropy_pairRV_le_add μ Y Z
  linarith

end Kolmogorov
