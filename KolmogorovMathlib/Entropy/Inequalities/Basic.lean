import KolmogorovMathlib.Entropy.Coding
import KolmogorovMathlib.Entropy.PairDistributions

/-!
# Conditional entropy, the entropy of a pair, and functions of a random variable

SUV Sections 7.2.1–7.2.2 (Theorems 141–143, Problems 218, 220 and 227), pp. 218–224.

The four properties of conditional entropy (Theorem 142), subadditivity of entropy
(Theorem 141), conditioning on an event of positive probability, the repackaging of pairs, and
monotonicity of entropy under a function (Theorem 143), together with the four-point examples
of Problems 218 (conditioning on an event can increase or decrease entropy) and 227 (the triple
information can be negative).
-/

namespace Kolmogorov

open Finset

variable {Ω : Type*} [Fintype Ω] {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ### Two examples on four points -/

/-- The uniform distribution on four points, the space of the examples of Problems 218
and 227. -/
private noncomputable def unif4 : FiniteProbSpace (Fin 4) where
  prob _ := 1 / 4
  prob_nonneg _ := by norm_num
  sum_prob := by simp

/-- Under `unif4` an event `E ⊆ Fin 4` has probability `|E|/4`; used in the four-point examples
of Problems 218 and 227. -/
private theorem probOf_unif4 (E : Finset (Fin 4)) : unif4.probOf E = (E.card : ℝ) / 4 := by
  simp only [FiniteProbSpace.probOf, unif4, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The entropy summand at `1/2` is `1/2`: the value of `-(1/2) log₂ (1/2)` needed by the
four-point examples of Problems 218 and 227. -/
private theorem negMulLog2_half : negMulLog2 (1 / 2) = 1 / 2 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have h : Real.log (1 / 2) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  simp only [negMulLog2, Real.negMulLog, h]
  rw [div_eq_iff h2]
  ring

/-- The entropy summand at `1/4` is `1/2`: the value of `-(1/4) log₂ (1/4)` needed by the
four-point examples of Problems 218 and 227. -/
private theorem negMulLog2_quarter : negMulLog2 (1 / 4) = 1 / 2 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have h : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast
    ring
  simp only [negMulLog2, Real.negMulLog, h]
  rw [div_eq_iff h2]
  ring

/-- The entropy summand at `3/4` is below `1/2`, which makes the indicator of one of four
equiprobable points have entropy below `1`: the four-point example of Problem 218. -/
private theorem negMulLog2_three_quarters_lt : negMulLog2 (3 / 4) < 1 / 2 := by
  have hlog : Real.log (3 / 4) = -Real.log (4 / 3) := by
    rw [← Real.log_inv]
    norm_num
  have h1 : Real.log (4 / 3) < 4 / 3 - 1 := Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  have h2 : Real.log (1 / 2) ≤ 1 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at h2
  simp only [negMulLog2, Real.negMulLog, hlog]
  rw [div_lt_iff₀ (Real.log_pos one_lt_two)]
  nlinarith

/-- The indicator of the point `0` of `Fin 4`. -/
private def ind0 : Fin 4 → Bool := fun ω => decide (ω = 0)

/-- The entropy of the indicator `ind0` of one point of `unif4`, computed as
`1/2 + negMulLog2 (3/4)`: the random variable of the four-point example of Problem 218. -/
private theorem entropy_unif4_ind0 : entropy unif4 ind0 = 1 / 2 + negMulLog2 (3 / 4) := by
  rw [entropy_eq_entropyDist]
  simp only [entropyDist, Fintype.sum_bool, FiniteProbSpace.dist, probOf_unif4]
  have h1 : (Finset.univ.filter fun ω => ind0 ω = true).card = 1 := by decide
  have h2 : (Finset.univ.filter fun ω => ind0 ω = false).card = 3 := by decide
  rw [h1, h2]
  norm_num [negMulLog2_quarter]


/-- **The triple information can be negative.**  For two independent uniform bits `α`, `β` and
their sum `γ = α ⊕ β` the value `I(α : β : γ)` is negative.  SUV Problem 227, p. 224. -/
theorem exists_tripleInfo_neg :
    ∃ (μ : FiniteProbSpace (Fin 4)) (X Y Z : Fin 4 → Bool), tripleInfo μ X Y Z < 0 := by
  refine ⟨unif4, fun ω => decide (ω = 1 ∨ ω = 3), fun ω => decide (ω = 2 ∨ ω = 3),
    fun ω => decide (ω = 1 ∨ ω = 2), ?_⟩
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [tripleInfo, entropy_eq_entropyDist, entropyDist, Fintype.sum_prod_type,
    Fintype.sum_bool, FiniteProbSpace.dist, FiniteProbSpace.probOf, unif4, Finset.sum_filter,
    Fin.sum_univ_four, pairRV, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two, h3,
    Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not]
  norm_num [negMulLog2_quarter, negMulLog2_half]

/-! ### Conditioning on an event -/

/-- **Conditioning on an event can increase the entropy.**  SUV Problem 218, p. 219. -/
theorem exists_entropy_lt_condEntropyGiven :
    ∃ (μ : FiniteProbSpace (Fin 4)) (X : Fin 4 → Bool) (E : Finset (Fin 4)),
      0 < μ.probOf E ∧ entropy μ X < condEntropyGiven μ X E := by
  refine ⟨unif4, ind0, {0, 1}, ?_, ?_⟩
  · rw [probOf_unif4]
    have : (({0, 1} : Finset (Fin 4)).card) = 2 := by decide
    rw [this]
    norm_num
  · rw [entropy_unif4_ind0, condEntropyGiven_eq_sum_univ]
    simp only [Fintype.sum_bool, FiniteProbSpace.condDist, probOf_unif4]
    have h1 : (({0, 1} : Finset (Fin 4)).filter fun ω => ind0 ω = true).card = 1 := by decide
    have h2 : (({0, 1} : Finset (Fin 4)).filter fun ω => ind0 ω = false).card = 1 := by decide
    have h3 : (({0, 1} : Finset (Fin 4)).card) = 2 := by decide
    rw [h1, h2, h3]
    have := negMulLog2_three_quarters_lt
    norm_num [negMulLog2_half]
    linarith

/-- **Conditioning on an event can decrease the entropy.**  SUV Problem 218, p. 219. -/
theorem exists_condEntropyGiven_lt_entropy :
    ∃ (μ : FiniteProbSpace (Fin 4)) (X : Fin 4 → Bool) (E : Finset (Fin 4)),
      0 < μ.probOf E ∧ condEntropyGiven μ X E < entropy μ X := by
  refine ⟨unif4, ind0, {1, 2}, ?_, ?_⟩
  · rw [probOf_unif4]
    have : (({1, 2} : Finset (Fin 4)).card) = 2 := by decide
    rw [this]
    norm_num
  · rw [entropy_unif4_ind0, condEntropyGiven_eq_sum_univ]
    simp only [Fintype.sum_bool, FiniteProbSpace.condDist, probOf_unif4]
    have h1 : (({1, 2} : Finset (Fin 4)).filter fun ω => ind0 ω = true).card = 0 := by decide
    have h2 : (({1, 2} : Finset (Fin 4)).filter fun ω => ind0 ω = false).card = 2 := by decide
    have h3 : (({1, 2} : Finset (Fin 4)).card) = 2 := by decide
    rw [h1, h2, h3]
    have := negMulLog2_nonneg (x := 3 / 4) (by norm_num) (by norm_num)
    norm_num [negMulLog2_one]
    linarith

/-! ### The value type of a random variable is inhabited -/

omit [DecidableEq α] in
/-- The value type of a random variable on a probability space is inhabited: the space has an
outcome, since the weights sum to one. -/
private theorem nonempty_of_finiteProbSpace (μ : FiniteProbSpace Ω) (X : Ω → α) :
    Nonempty α := by
  by_contra hα
  have : IsEmpty Ω := ⟨fun ω => hα ⟨X ω⟩⟩
  simpa using μ.sum_prob

/-! ### Theorem 142: the properties of conditional entropy -/

/-- **Conditional entropy is non-negative.**  SUV Theorem 142(a), p. 220. -/
theorem condEntropy_nonneg (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ condEntropy μ X Y :=
  Finset.sum_nonneg fun b _ => mul_nonneg (μ.dist_nonneg Y b) (condEntropyGiven_nonneg μ X _)

/-- **Conditional entropy vanishes exactly for a function of the condition**: `H(ξ|η) = 0` if and
only if `ξ = f(η)` with probability one for some function `f`.  SUV Theorem 142(b), p. 220. -/
theorem condEntropy_eq_zero_iff (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    condEntropy μ X Y = 0 ↔
      ∃ f : β → α, μ.probOf (Finset.univ.filter fun ω => X ω = f (Y ω)) = 1 := by
  constructor
  · intro h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
      mul_nonneg (μ.dist_nonneg Y b) (condEntropyGiven_nonneg μ X _)).1 h
    have : Nonempty α := nonempty_of_finiteProbSpace μ X
    have hex : ∀ b, ∃ a, 0 < μ.dist Y b →
        μ.condDist X (Finset.univ.filter fun ω => Y ω = b) a = 1 := by
      intro b
      by_cases hb : 0 < μ.dist Y b
      · have hbr : b ∈ rangeFinset Y :=
          by_contra fun hn => hb.ne' (μ.dist_eq_zero_of_not_mem_range hn)
        obtain ⟨a, ha⟩ := (condEntropyGiven_eq_zero_iff μ X hb).1
          ((mul_eq_zero.1 (hterm b hbr)).resolve_left hb.ne')
        exact ⟨a, fun _ => ha⟩
      · exact ⟨Classical.arbitrary α, fun h => absurd h hb⟩
    choose f hf using hex
    refine ⟨f, ?_⟩
    rw [μ.probOf_eq_comp_eq_sum, ← μ.sum_dist_eq_one Y]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases (μ.dist_nonneg Y b).lt_or_eq with hb | hb
    · have h1 := hf b hb
      rw [μ.condDist_fiber, div_eq_one_iff_eq hb.ne'] at h1
      exact h1
    · rw [← hb]
      exact μ.dist_pairRV_eq_zero_of_snd X Y _ hb.symm
  · rintro ⟨f, hf⟩
    rw [μ.probOf_eq_comp_eq_sum, ← μ.sum_dist_eq_one Y] at hf
    have hterm := (Finset.sum_eq_sum_iff_of_le fun b _ => μ.dist_pairRV_le_snd X Y (f b) b).1 hf
    unfold condEntropy
    refine Finset.sum_eq_zero fun b hb => ?_
    rcases (μ.dist_nonneg Y b).lt_or_eq with hq | hq
    · rw [(condEntropyGiven_eq_zero_iff μ X hq).2 ⟨f b, ?_⟩, mul_zero]
      rw [μ.condDist_fiber, hterm b hb, div_self hq.ne']
    · rw [← hq, zero_mul]

/-- **Conditioning does not increase entropy**: `H(ξ|η) ≤ H(ξ)`.
SUV Theorem 142(c), p. 220. -/
theorem condEntropy_le_entropy (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    condEntropy μ X Y ≤ entropy μ X := by
  rw [condEntropy_eq_sum_sum, Finset.sum_comm, entropy]
  exact Finset.sum_le_sum fun a _ => sum_dist_mul_negMulLog2_condDist_le μ X Y a

/-- **The chain rule**: `H(⟨ξ, η⟩) = H(η) + H(ξ|η)`.  SUV Theorem 142(d), p. 220. -/
theorem entropy_pairRV_eq_add_condEntropy (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ (pairRV X Y) = entropy μ Y + condEntropy μ X Y := by
  rw [entropy_pairRV_eq_sum_sum, condEntropy_eq_sum_sum, entropy, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases (μ.dist_nonneg Y b).lt_or_eq with hq | hq
  · simp_rw [mul_negMulLog2_div hq]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.sum_dist_pairRV_fst, negMulLog2_eq (μ.dist Y b)]
    ring
  · have h0 : ∀ a ∈ rangeFinset X, negMulLog2 (μ.dist (pairRV X Y) (a, b)) = 0 := fun a _ => by
      rw [μ.dist_pairRV_eq_zero_of_snd X Y a hq.symm, negMulLog2_zero]
    rw [Finset.sum_eq_zero h0, ← hq]
    simp

/-! ### Theorem 141: entropy of a pair -/

/-- **The entropy of a pair does not exceed the sum of the entropies.**
SUV Theorem 141, p. 218. -/
theorem entropy_pairRV_le_add (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ (pairRV X Y) ≤ entropy μ X + entropy μ Y := by
  have h1 := entropy_pairRV_eq_add_condEntropy μ X Y
  have h2 := condEntropy_le_entropy μ X Y
  linarith

/-! ### Conditioning on an event of positive probability -/

namespace FiniteProbSpace

open Classical in
/-- The probability space conditioned on an event `E` of positive probability: the weights of
the outcomes in `E` are divided by `Pr[E]` and the other outcomes get weight zero.  Its
distributions are the conditional distributions given `E`, so every entropy inequality can be
relativized by conditioning on each value of a random variable and averaging.
SUV Section 7.2.4, p. 223. -/
noncomputable def condSpace (μ : FiniteProbSpace Ω) (E : Finset Ω) (hE : 0 < μ.probOf E) :
    FiniteProbSpace Ω where
  prob ω := if ω ∈ E then μ.prob ω / μ.probOf E else 0
  prob_nonneg ω := by
    split_ifs
    · exact div_nonneg (μ.prob_nonneg ω) hE.le
    · exact le_rfl
  sum_prob := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
    exact div_self hE.ne'

open Classical in
/-- The distribution of a random variable on the conditioned space is its conditional
distribution given the event. -/
theorem dist_condSpace (μ : FiniteProbSpace Ω) {E : Finset Ω} (hE : 0 < μ.probOf E)
    (X : Ω → α) (a : α) : (μ.condSpace E hE).dist X a = μ.condDist X E a := by
  have hfil : (Finset.univ.filter fun ω => X ω = a) ∩ E = E.filter fun ω => X ω = a := by
    ext ω
    simp [and_comm]
  simp only [dist, condDist, probOf, condSpace, Finset.sum_ite_mem, hfil, Finset.sum_div]

/-- The entropy on the conditioned space is the entropy of the conditional distribution. -/
theorem entropy_condSpace (μ : FiniteProbSpace Ω) {E : Finset Ω} (hE : 0 < μ.probOf E)
    (X : Ω → α) : entropy (μ.condSpace E hE) X = condEntropyGiven μ X E := by
  unfold entropy condEntropyGiven
  exact Finset.sum_congr rfl fun a _ => by rw [μ.dist_condSpace hE]

end FiniteProbSpace

/-! ### Repackaging pairs -/

/-- Entropy is invariant under swapping the two components of a pair. -/
theorem entropy_pairRV_comm (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ (pairRV X Y) = entropy μ (pairRV Y X) :=
  (entropy_comp_of_injective μ (pairRV X Y) Prod.swap_injective).symm

/-- Entropy is invariant under re-associating a triple. -/
theorem entropy_pairRV_assoc (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    entropy μ (pairRV (pairRV X Y) Z) = entropy μ (pairRV X (pairRV Y Z)) := by
  have hf : Function.Injective fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2)) :=
    fun p q h => by simpa [Prod.ext_iff, and_assoc, and_comm, and_left_comm] using h
  exact (entropy_comp_of_injective μ (pairRV (pairRV X Y) Z) hf).symm

/-- Entropy is invariant under exchanging the last two components of a triple. -/
theorem entropy_pairRV_swap_right (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    entropy μ (pairRV (pairRV X Y) Z) = entropy μ (pairRV (pairRV X Z) Y) := by
  have hf : Function.Injective fun p : (α × β) × γ => ((p.1.1, p.2), p.1.2) :=
    fun p q h => by simpa [Prod.ext_iff, and_assoc, and_comm, and_left_comm] using h
  exact (entropy_comp_of_injective μ (pairRV (pairRV X Y) Z) hf).symm

/-- A pair has at least the entropy of its first component. -/
theorem entropy_le_entropy_pairRV_left (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ X ≤ entropy μ (pairRV X Y) := by
  have h1 := entropy_pairRV_eq_add_condEntropy μ Y X
  have h2 := condEntropy_nonneg μ Y X
  rw [entropy_pairRV_comm]
  linarith

/-- A pair has at least the entropy of its second component. -/
theorem entropy_le_entropy_pairRV_right (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ Y ≤ entropy μ (pairRV X Y) := by
  have h1 := entropy_pairRV_eq_add_condEntropy μ X Y
  have h2 := condEntropy_nonneg μ X Y
  linarith

/-! ### Theorem 143: a function of a random variable -/

/-- **A function of a random variable has no larger entropy**: `H(f(ξ)) ≤ H(ξ)`.
SUV Theorem 143, p. 221. -/
theorem entropy_comp_le (μ : FiniteProbSpace Ω) (X : Ω → α) (f : α → γ) :
    entropy μ (fun ω => f (X ω)) ≤ entropy μ X := by
  have hinj : Function.Injective fun a : α => (a, f a) := fun a b h => congrArg Prod.fst h
  have h1 := entropy_comp_of_injective μ X hinj
  have h2 := entropy_le_entropy_pairRV_right μ X fun ω => f (X ω)
  exact h2.trans_eq h1

/-- **The equality case of `H(f(ξ)) ≤ H(ξ)`**: equality holds exactly when `f` is injective on
the values of `ξ` that have positive probability.  The book asks when the inequality of
Theorem 143 becomes an equality and does not print the answer; this is the answer.
SUV Problem 220, p. 221. -/
theorem entropy_comp_eq_iff (μ : FiniteProbSpace Ω) (X : Ω → α) (f : α → γ) :
    entropy μ (fun ω => f (X ω)) = entropy μ X ↔
      Set.InjOn f {a : α | 0 < μ.dist X a} := by
  have hinj : Function.Injective fun a : α => (a, f a) := fun a b h => congrArg Prod.fst h
  have h1 := entropy_comp_of_injective μ X hinj
  have h1' : entropy μ (pairRV X fun ω => f (X ω)) = entropy μ X := h1
  have h2 := entropy_pairRV_eq_add_condEntropy μ X (fun ω => f (X ω))
  have key : entropy μ (fun ω => f (X ω)) = entropy μ X ↔
      condEntropy μ X (fun ω => f (X ω)) = 0 := by
    constructor <;> intro h <;> linarith
  rw [key, condEntropy_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩ a ha a' ha' hff
    rw [μ.probOf_eq_one_iff] at hg
    obtain ⟨ω, rfl, hω⟩ := (μ.dist_pos_iff X a).1 ha
    obtain ⟨ω', rfl, hω'⟩ := (μ.dist_pos_iff X a').1 ha'
    have e1 := (Finset.mem_filter.1 (hg ω hω)).2
    have e2 := (Finset.mem_filter.1 (hg ω' hω')).2
    calc X ω = g (f (X ω)) := e1
      _ = g (f (X ω')) := by rw [hff]
      _ = X ω' := e2.symm
  · intro hinj'
    have : Nonempty α := nonempty_of_finiteProbSpace μ X
    refine ⟨Function.invFunOn f {a | 0 < μ.dist X a},
      (μ.probOf_eq_one_iff _).2 fun ω hω => ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have hmem : X ω ∈ {a | 0 < μ.dist X a} := (μ.dist_pos_iff X (X ω)).2 ⟨ω, rfl, hω⟩
    exact (hinj'.leftInvOn_invFunOn hmem).symm

end Kolmogorov
