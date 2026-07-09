import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionShift
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.OptimalityDeficiency
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

namespace Kolmogorov

open scoped ENNReal

/-!
# Deficiencies and Affine Equivalence (Phase E interfaces)

This module records the Section 3 headline statements as explicit gates.  The
gates are ordinary hypotheses over the vocabulary already available in the
project; they do not introduce a separate abstract conditional set-complexity
API.  These gates are isolated interfaces; they can be discharged once the required
Levin-Gacs and improving-descriptions infrastructure has been connected.
-/

/-- Gate for Theorem 3 (`thm:improving-descriptions`): stochasticity via an
arbitrary probability model can be converted to optimal stochasticity via a
finite set with parameter-logarithmic slack.  It explicitly takes the corrected
log-slack improving-descriptions propositions as inputs; the old constant-slack
statements are not part of this interface. -/
-- Planned follow-up: simplify this gate after the improving-descriptions interfaces are
-- reorganized.  Mathematically the main Section 3 input should be the complexity
-- half `A -> C`; the size half `A -> B` should be supplied as a corollary via
-- description-shift/portioning, not as an independent assumption.
def StochasticToOptimalSetGate (U : Map) : Prop :=
  ImprovingDescriptionsSizeLogSlack U →
  ImprovingDescriptionsComplexityLogSlack U →
    ∃ c : ℕ, ∀ x : BitString, ∀ n alpha beta : ℕ,
      x.length = n →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x (alpha + logSlack c (n + alpha + beta)) (beta + logSlack c (n + alpha + beta))

/-- Theorem 3 exported under its intended name, gated by the real statement that
later work must prove. -/
theorem optimal_set_of_stochastic (U : Map)
    (h_size : ImprovingDescriptionsSizeLogSlack U)
    (h_comp : ImprovingDescriptionsComplexityLogSlack U)
    (h_gate : StochasticToOptimalSetGate U) :
    ∃ c : ℕ, ∀ x : BitString, ∀ n alpha beta : ℕ,
      x.length = n →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x (alpha + logSlack c (n + alpha + beta)) (beta + logSlack c (n + alpha + beta)) :=
  h_gate h_size h_comp

/-- Theorem 3 specialized to an optimal decompressor, still with the explicit
stochastic-to-set gate. Later work should prove `StochasticToOptimalSetGate`
from the Section 3 infrastructure and then this wrapper becomes the intended
optimal-decompressor corollary. -/
theorem optimal_set_of_stochastic_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U)
    (h_gate : StochasticToOptimalSetGate U) :
    ∃ c : ℕ, ∀ x : BitString, ∀ n alpha beta : ℕ,
      x.length = n →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x (alpha + logSlack c (n + alpha + beta)) (beta + logSlack c (n + alpha + beta)) := by
  have h_size := exists_description_smaller_size_of_many_logSlack U hU
  have h_comp := exists_description_smaller_complexity_of_many_logSlack U hU
  exact optimal_set_of_stochastic U h_size h_comp h_gate

/-- The algebraic skeleton for the complexity half of the deficiency redistribution.
Given a set `B` resulting from an `(i-k, j)`-description improvement, its
complexity redistributes the gap `k = delta - d`.

The precondition `k ≤ i` is the genuine condition of the complexity-improvement
half (it appears as `k ≤ i` in `ImprovingDescriptionsComplexityLogSlack`); without
it the truncated subtraction `i - k` makes the statement fail (e.g. `i = 0`,
`k = delta - d > 0`). -/
theorem exists_card_dyadic_bracket (A : Finset BitString) (hA : A.Nonempty) :
    ∃ j : ℕ, (2 : ℝ≥0∞) ^ j / 2 ≤ (A.card : ℝ≥0∞) ∧ A.card ≤ 2 ^ j := by
  refine ⟨A.card.size, ?_, le_of_lt (Nat.lt_size_self A.card)⟩
  have hpos : 0 < A.card := hA.card_pos
  have hj : 1 ≤ A.card.size := Nat.size_pos.mpr hpos
  have hle : 2 ^ (A.card.size - 1) ≤ A.card := Nat.lt_size.mp (by omega)
  rw [show A.card.size = (A.card.size - 1) + 1 by omega, pow_succ,
    mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
  exact_mod_cast hle

theorem setOptimalityDeficiencyLe_of_profile {U : Map} {B : Finset BitString} {hB : B.Nonempty}
    {x : BitString} {s t beta : ℕ}
    (hx : x ∈ B)
    (h_comp : setComplexity U B hB ≤ (s : ENat))
    (h_size : B.card ≤ 2 ^ t)
    (h_arith : (s : ENat) + t ≤ KPPlain U x + beta) :
    SetOptimalityDeficiencyLe U B hB x beta := by
  rw [setOptimalityDeficiencyLe_iff_of_mem hx]
  cases hx_comp : KPPlain U x <;> cases hB_comp : setComplexity U B hB <;> simp_all [complexityWeight]
  refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right (show (B.card : ENNReal)⁻¹ ≥ (2^t : ENNReal)⁻¹ from ?_) _) _)
  · simp_all [← ENNReal.mul_inv, ← ENNReal.inv_pow]
    rw [← ENNReal.toReal_le_toReal] <;> norm_num
    · field_simp
      norm_cast at *
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ (by decide) (by omega)
    · exact ENNReal.mul_ne_top (by norm_num) (by norm_num)
  · gcongr; norm_cast

theorem ManyIJDescriptions_k_le_i_add_one {U : Map} {x : BitString} {i j k : ℕ} (h : ManyIJDescriptions U x i j k) : k ≤ i + 1 := by
  unfold ManyIJDescriptions at h
  have h_bound : ((descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => x ∈ S)).card ≤ 2 ^ (i + 1) := by
    exact (Finset.card_filter_le _ _).trans (card_descriptionsWithComplexityLeAndSizeLe U i j)
  have h_pow := h.trans h_bound
  exact (Nat.pow_le_pow_iff_right (by decide)).mp h_pow

/-- GapCountingBridge captures the corrected, visible-parameter conclusion of
`manyIJDescriptions_of_setOptimalityDeficiency`.

The slack argument is `n + delta + d`, not `n + i + j + d`: `i` and `j` are
internal description parameters, while Theorem 4 is budgeted by the visible
optimality and randomness deficiencies.

⚠️ LOOSE INTERFACE.  This bridge takes the *upper-bound* predicate
`SetOptimalityDeficiencyLe U A hA x delta` as a hypothesis, in which `delta` is a
monotone upper bound and can be inflated arbitrarily (cf. `mono_beta`).  It is an
abstract `Prop`-level gate only; it is **not** proven, and it must **not** be
instantiated by manufacturing the redistributed gap `delta - d` from the loose
deficiency alone — that is exactly the unsound step the original Theorem 4 took.
The sound interface is the tight `TightGapCountingBridge`, whose hypothesis is the
realized gap `RealizedSetOptimalityGap` (pinning `delta = i + j - kx`) and which is
discharged unconditionally by `manyIJDescriptions_of_realizedSetOptimalityGap`. -/
def GapCountingBridge (U : Map) : Prop :=
  ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
      (n delta d i j c_soi : ℕ),
    x.length = n →
    x ∈ A →
    setComplexity U A hA = (i : ENat) →
    A.card ≤ 2 ^ j →
    SetOptimalityDeficiencyLe U A hA x delta →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
    d ≤ delta + c_soi →
    ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) ∧
      ManyIJDescriptions U x i j (delta - d - slack)

/-- TightGapCountingBridge captures the tight visible-parameter conclusion
of `manyIJDescriptions_of_realizedSetOptimalityGap`. -/
def TightGapCountingBridge (U : Map) : Prop :=
  ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
      (n delta d i j kx c_soi : ℕ),
    x.length = n →
    RealizedSetOptimalityGap U A hA x delta i j kx →
    CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
    d ≤ delta + c_soi →
    ∃ slack : ℕ, slack ≤ logSlack c (n + delta + d) ∧
      ManyIJDescriptions U x i j (delta - d - slack)

/-- Adding one to the visible slack parameter only costs a constant-factor
increase in the slack value. -/
theorem logSlack_add_one (c : ℕ) (n : ℕ) :
    logSlack c (n + 1) ≤ logSlack c n + c * 2 := by
  unfold logSlack
  have : (Nat.bits (n + 1)).length ≤ (Nat.bits n).length + 2 := by
    simpa using length_natBits_add_le n 1
  nlinarith

theorem dyadic_bracket_lower_bound {j k : ℕ} (h : (2 : ℝ≥0∞) ^ j / 2 ≤ (2 : ℝ≥0∞) ^ k) : j - 1 ≤ k := by
  cases j
  · exact Nat.zero_le _
  · rename_i j
    rw [Nat.succ_sub_one]
    have h1 : ((2 ^ (j + 1) : ℕ) : ℝ≥0∞) / 2 ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := by exact_mod_cast h
    have h2 : ((2 ^ j * 2 : ℕ) : ℝ≥0∞) / 2 ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := by
      have h_eq : 2 ^ (j + 1) = 2 ^ j * 2 := by ring
      rw [h_eq] at h1
      exact h1
    have h3 : ((2 ^ j : ℕ) : ℝ≥0∞) * 2 / 2 ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := by exact_mod_cast h2
    have h4 : ((2 ^ j : ℕ) : ℝ≥0∞) ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := by
      calc
        ((2 ^ j : ℕ) : ℝ≥0∞) = ((2 ^ j : ℕ) : ℝ≥0∞) * 2 / 2 := by
          rw [mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
        _ ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := h3
    have h5 : 2 ^ j ≤ 2 ^ k := by exact_mod_cast h4
    exact (Nat.pow_le_pow_iff_right (by decide)).mp h5

theorem setOptimalityCardBound {U : Map} {A : Finset BitString} {hA : A.Nonempty}
    {x : BitString} {delta i : ℕ} (hx : x ∈ A)
    (h_comp : setComplexity U A hA = (i : ENat))
    (h_opt : SetOptimalityDeficiencyLe U A hA x delta) :
    ∃ j : ℕ, A.card ≤ 2 ^ j ∧ (j : ENat) + i ≤ KPPlain U x + delta := by
  by_cases h : KPPlain U x = ⊤
  · refine ⟨A.card, ?_, ?_⟩
    · induction A.card with
      | zero => exact zero_le _
      | succ n ih =>
        rw [Nat.pow_succ]
        calc
          n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
          _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (Nat.one_le_pow _ _ (by decide)) _
          _ = 2 ^ n * 2 := by ring
    · rw [h]
      exact le_top
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, KPPlain U x = k := (ENat.ne_top_iff_exists.mp h).imp fun m hm => hm.symm
    refine ⟨k + delta - i, ?_, ?_⟩
    · have h_opt' := h_opt
      rw [setOptimalityDeficiencyLe_iff_of_mem hx] at h_opt'
      simp only [hk, h_comp, complexityWeight_coe] at h_opt'
      have h_card2 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ k ≤ (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i := by
        calc
          (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ k
            ≤ (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ delta * ((2 : ℝ≥0∞)⁻¹ ^ i * (A.card : ℝ≥0∞)⁻¹)) := by gcongr
          _ = (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i * ((A.card : ℝ≥0∞) * (A.card : ℝ≥0∞)⁻¹) := by ring
          _ = (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i := by
            rw [ENNReal.mul_inv_cancel]
            · exact mul_one _
            · exact_mod_cast hA.card_pos.ne'
            · exact ENNReal.natCast_ne_top A.card
      have h_card3 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k ≤ ((2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i) * (2 : ℝ≥0∞) ^ k := by
        gcongr
      have h_card4 : (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ k := by
        calc
          (A.card : ℝ≥0∞)
            = (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k) := by
              rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]
          _ = (A.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k := by ring
          _ ≤ ((2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i) * (2 : ℝ≥0∞) ^ k := h_card3
      have h_card5 : (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ i := by
        have h_eq : (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ k = (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ i := by ring
        exact h_card4.trans (le_of_eq h_eq)
      have h_card6 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ i ≤ (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k := by
        calc
          (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ i
            ≤ ((2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ i) * (2 : ℝ≥0∞) ^ i := by gcongr
          _ = (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ i) := by ring
          _ = (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k := by
            rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]
      have h_card7 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ i ≤ (2 : ℝ≥0∞) ^ (delta + k) := by
        calc
          (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ i ≤ (2 : ℝ≥0∞) ^ delta * (2 : ℝ≥0∞) ^ k := h_card6
          _ = (2 : ℝ≥0∞) ^ (delta + k) := by rw [pow_add]
      have h_card9 : A.card * 2 ^ i ≤ 2 ^ (delta + k) := by exact_mod_cast h_card7
      have hi : setComplexity U A hA ≤ KPPlain U x + (delta : ENat) := setComplexity_le_of_setOptimalityDeficiency hx h_opt
      rw [h_comp, hk] at hi
      have h_i_le : i ≤ delta + k := by
        rw [← ENat.coe_add] at hi
        have := (ENat.coe_le_coe (n := i) (m := k + delta)).mp hi
        omega
      have h_card10 : A.card * 2 ^ i ≤ 2 ^ (delta + k - i) * 2 ^ i := by
        rw [← pow_add, Nat.sub_add_cancel h_i_le]
        exact h_card9
      have h_pos : 0 < 2 ^ i := Nat.two_pow_pos i
      have h_card11 : A.card * 2 ^ i ≤ 2 ^ (k + delta - i) * 2 ^ i := by
        have h_eq : delta + k - i = k + delta - i := by omega
        rw [h_eq] at h_card10
        exact h_card10
      exact Nat.le_of_mul_le_mul_right h_card11 h_pos
    · have hi : setComplexity U A hA ≤ KPPlain U x + (delta : ENat) := setComplexity_le_of_setOptimalityDeficiency hx h_opt
      rw [h_comp, hk] at hi
      rw [← ENat.coe_add] at hi
      have h_i_le : i ≤ k + delta := by
        have := (ENat.coe_le_coe (n := i) (m := k + delta)).mp hi
        exact this
      rw [hk]
      have h_nat : (k + delta - i : ℕ) + i ≤ k + delta := by omega
      exact_mod_cast h_nat

/-- ⚠️ LOOSE FORM of Theorem 4, kept only as an abstract wrapper.

Its gap-counting hypothesis is the loose `GapCountingBridge U`, which consumes the
monotone `SetOptimalityDeficiencyLe U A hA x delta`.  Because `delta` there is a
free upper bound, this statement must **never** be discharged unconditionally from
`SetOptimalityDeficiencyLe` without a tightness witness — doing so reintroduces the
false `deficiencies_theorem_of_optimal`.  Use `deficiencies_theorem_tight` (gated by
`TightGapCountingBridge`) and its unconditional corollary
`deficiencies_theorem_tight_of_optimal` instead; those are budgeted by the realized
gap `RealizedSetOptimalityGap`. -/
theorem deficiencies_theorem (U : Map) (hU : IsOptimalPrefixConditional U)
    (_h_size : ImprovingDescriptionsSizeLogSlack U)
    (h_comp : ImprovingDescriptionsComplexityLogSlack U)
    (h_gap : GapCountingBridge U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j c_soi : ℕ),
      x.length = n →
      x ∈ A →
      setComplexity U A hA = (i : ENat) →
      A.card ≤ 2 ^ j →
      SetOptimalityDeficiencyLe U A hA x delta →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d)) := by
  rcases h_gap with ⟨c1, hc1⟩
  rcases h_comp with ⟨c2, hc2⟩
  obtain ⟨bb, hbb⟩ := visible_param_linear_bound U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c2 4 bb
  refine ⟨c1 + 2 * C0 + 2, ?_⟩
  intro A hA x n delta d i j c_soi hn hxA h_compA hj h_opt h_def hd
  -- Re-bracket the size parameter to the tight dyadic value `j0` coming from the
  -- optimality-deficiency cardinality bound; this keeps the internal budget
  -- `n + i + j0` linearly controlled by the visible budget `n + delta + d`.
  obtain ⟨j0, hj0_card, hj0_bound⟩ := setOptimalityCardBound hxA h_compA h_opt
  rcases hc1 A hA x n delta d i j0 c_soi hn hxA h_compA hj0_card h_opt h_def hd with
    ⟨slack1, hslack1, h_many⟩
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptions U x i j0 k :=
    ManyIJDescriptions.mono_k (Nat.min_le_left _ _) h_many
  have hkc : delta - d - slack1 ≤ i + 1 := ManyIJDescriptions_k_le_i_add_one h_many
  rcases hc2 x n i j0 k hn h_many' hk_le_i with ⟨B, hB, hxB, hcompB, hsizeB⟩
  -- Fold the internal complexity-improvement slack into the visible-parameter slack.
  have hvis : n + i + j0 ≤ 4 * (n + delta + d) + bb := by
    have h1 := hbb x n i j0 delta d hn hj0_bound
    omega
  have hslackvis : logSlack c2 (n + i + j0) ≤ logSlack C0 (n + delta + d) :=
    le_trans (logSlack_mono_right c2 hvis) (hC0 (n + delta + d))
  -- The redistributed gap `delta - d` is paid for by the gap-counting slack `slack1`.
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  -- The combining bound that folds the gap-counting slack `logSlack c1` and the
  -- visible complexity slack `logSlack C0` (used twice) into the final slack.
  have hcomb : logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d) + 1 ≤
      logSlack (c1 + 2 * C0 + 2) (n + delta + d) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits (n + delta + d)).length)]
  refine ⟨B, hB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [h_compA]
    norm_cast
    omega
  · apply setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB
    cases h : KPPlain U x <;> norm_cast at *
    · exact le_top
    · rw [h] at hj0_bound
      norm_cast at hj0_bound
      omega

/-- **Realized gap implies the loose optimality deficiency.**

`RealizedSetOptimalityGap U A hA x delta i j kx` is a *tight* witness: it pins
`delta = i + j - kx` to the realized profile of `A` (set complexity `i`, dyadic
size bracket `2^j/2 ≤ |A| ≤ 2^j`, and `KP(x) = kx`).  The loose predicate
`SetOptimalityDeficiencyLe U A hA x delta` is the upper-bound / monotone form.

This lemma proves the *sound* direction: a realized gap always yields the loose
optimality deficiency.  (The converse — manufacturing a realized gap from the
loose predicate — is exactly the unsound step that the original bug took, since
the loose `delta` can be inflated arbitrarily; that direction is *not* provided.)

Multiplicatively the loose form unfolds (at `x ∈ A`) to
`2⁻¹^kx ≤ 2^delta * (2⁻¹^i * |A|⁻¹)`.  Using the upper cardinality bound
`|A| ≤ 2^j` we have `2⁻¹^j ≤ |A|⁻¹`, so it suffices to show
`2⁻¹^kx ≤ 2^delta * 2⁻¹^(i+j)`.  When `kx ≤ i + j` we have `i + j = delta + kx`
and both sides are equal; when `kx > i + j` we have `delta = 0` and the bound
follows from `2⁻¹ ≤ 1` with `i + j ≤ kx`.  The dyadic *lower* bracket
`2^j/2 ≤ |A|` is not needed here — it only tightens the gap for the lower-bound
direction. -/
theorem setOptimalityDeficiencyLe_of_realizedSetOptimalityGap {U : Map}
    {A : Finset BitString} {hA : A.Nonempty} {x : BitString} {delta i j kx : ℕ}
    (h : RealizedSetOptimalityGap U A hA x delta i j kx) :
    SetOptimalityDeficiencyLe U A hA x delta := by
  obtain ⟨hx, h_comp, h_card, _h_lower, hkx, hdelta⟩ := h
  rw [setOptimalityDeficiencyLe_iff_of_mem hx, h_comp, ← hkx,
    complexityWeight_coe, complexityWeight_coe]
  -- Goal: `(2⁻¹)^kx ≤ 2^delta * ((2⁻¹)^i * (A.card)⁻¹)`.
  have hcard_inv : (2 : ℝ≥0∞)⁻¹ ^ j ≤ (A.card : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.inv_pow]
    gcongr
    exact_mod_cast h_card
  have key : (2 : ℝ≥0∞)⁻¹ ^ kx ≤ (2 : ℝ≥0∞) ^ delta * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞)⁻¹ ^ j) := by
    rw [← pow_add]
    rcases Nat.lt_or_ge (i + j) kx with hlt | hle
    · -- `kx > i + j` forces `delta = 0`; use `2⁻¹ ≤ 1` with `i + j ≤ kx`.
      have hzero : delta = 0 := by omega
      rw [hzero, pow_zero, one_mul]
      exact pow_le_pow_right_of_le_one' (by norm_num) (by omega)
    · -- `delta = i + j - kx`, hence `i + j = delta + kx` and both sides are equal.
      have hsum : i + j = delta + kx := by omega
      rw [hsum, pow_add, ← mul_assoc, ← mul_pow,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
  refine key.trans ?_
  gcongr

theorem deficiencies_theorem_tight (U : Map) (hU : IsOptimalPrefixConditional U)
    (_h_size : ImprovingDescriptionsSizeLogSlack U)
    (h_comp : ImprovingDescriptionsComplexityLogSlack U)
    (h_gap : TightGapCountingBridge U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d)) := by
  rcases h_gap with ⟨c1, hc1⟩
  rcases h_comp with ⟨c2, hc2⟩
  obtain ⟨bb, hbb⟩ := visible_param_linear_bound U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c2 4 bb
  refine ⟨c1 + 2 * C0 + 2, ?_⟩
  intro A hA x n delta d i j kx c_soi hn h_realized h_def hd
  have hxA := h_realized.1
  have h_compA := h_realized.2.1
  have hj_card := h_realized.2.2.1
  have hj_lower := h_realized.2.2.2.1
  have hkx := h_realized.2.2.2.2.1
  have hdelta_eq := h_realized.2.2.2.2.2
  have hkx_eq : KPPlain U x = (kx : ENat) := hkx.symm
  have h_opt : SetOptimalityDeficiencyLe U A hA x delta :=
    setOptimalityDeficiencyLe_of_realizedSetOptimalityGap h_realized
  -- Re-bracket the size parameter to the tight dyadic value `j0` coming from the
  -- optimality-deficiency cardinality bound; this keeps the internal budget
  -- `n + i + j0` linearly controlled by the visible budget `n + delta + d`.
  obtain ⟨j0, hj0_card, hj0_bound⟩ := setOptimalityCardBound hxA h_compA h_opt
  rcases hc1 A hA x n delta d i j kx c_soi hn h_realized h_def hd with
    ⟨slack1, hslack1, h_many⟩
  set k := min (delta - d - slack1) i with hk_def
  have hk_le_i : k ≤ i := Nat.min_le_right _ _
  have h_many' : ManyIJDescriptions U x i j k :=
    ManyIJDescriptions.mono_k (Nat.min_le_left _ _) h_many
  have hkc : delta - d - slack1 ≤ i + 1 := ManyIJDescriptions_k_le_i_add_one h_many
  rcases hc2 x n i j k hn h_many' hk_le_i with ⟨B, hB, hxB, hcompB, hsizeB⟩
  -- Fold the internal complexity-improvement slack into the visible-parameter slack.
  have hj0_bound' : (j : ENat) + i ≤ KPPlain U x + delta := by
    rw [hkx_eq]
    norm_cast
    omega
  have hvis : n + i + j ≤ 4 * (n + delta + d) + bb := by
    have h1 := hbb x n i j delta d hn hj0_bound'
    omega
  have hslackvis : logSlack c2 (n + i + j) ≤ logSlack C0 (n + delta + d) :=
    le_trans (logSlack_mono_right c2 hvis) (hC0 (n + delta + d))
  -- The redistributed gap `delta - d` is paid for by the gap-counting slack `slack1`.
  have hdk : (delta - d) - k ≤ slack1 + 1 := by omega
  have hdeltak : delta - k ≤ d + slack1 + 1 := by omega
  -- The combining bound that folds the gap-counting slack `logSlack c1` and the
  -- visible complexity slack `logSlack C0` (used twice) into the final slack.
  have hcomb : logSlack c1 (n + delta + d) + 2 * logSlack C0 (n + delta + d) + 1 ≤
      logSlack (c1 + 2 * C0 + 2) (n + delta + d) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits (n + delta + d)).length)]
  refine ⟨B, hB, hxB, ?_, ?_⟩
  · refine le_trans (add_le_add hcompB (le_refl ((delta - d : ℕ) : ENat))) ?_
    rw [h_compA]
    norm_cast
    omega
  · apply setOptimalityDeficiencyLe_of_profile hxB hcompB hsizeB
    cases hh : KPPlain U x <;> norm_cast at *
    · exact le_top
    · rw [hh] at hj0_bound'
      norm_cast at hj0_bound'
      omega

/-- Unconditional corollary discharging the Theorem 4 tight gate. -/
theorem deficiencies_theorem_tight_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d)) := by
  have h_size := exists_description_smaller_size_of_many_logSlack U hU
  have h_comp := exists_description_smaller_complexity_of_many_logSlack U hU
  have h_gap : TightGapCountingBridge U := manyIJDescriptions_of_realizedSetOptimalityGap U hU
  exact deficiencies_theorem_tight U hU h_size h_comp h_gap
theorem isOptimalSetStochastic_imp_profile_of_large_sizeBudget (U : Map) (x : BitString)
    (alpha beta j slack : ℕ)
    (h_opt : IsOptimalSetStochastic U x alpha beta)
    (h_arith : KPPlain U x + beta ≤ (j + slack : ENat)) :
    InDescriptionProfile U x (alpha + slack) (j + slack) := by
  obtain ⟨ S, hS, hx, hc, hdef ⟩ := h_opt;
  refine ⟨ S, hS, hx, ?_, ?_ ⟩;
  · exact le_trans hc ( Nat.cast_le.mpr ( Nat.le_add_right _ _ ) );
  · -- From `hdef`, we have `complexityWeight (KPPlain U x) ≤ (2:ℝ≥0∞)^beta * (complexityWeight (setComplexity U S hS) * (S.card : ℝ≥0∞)⁻¹)`.
    have hdef' : complexityWeight (KPPlain U x) ≤ (2 : ENNReal) ^ beta * (1 * (S.card : ENNReal)⁻¹) := by
      rw [ setOptimalityDeficiencyLe_iff_of_mem hx ] at hdef;
      exact hdef.trans ( mul_le_mul_right ( mul_le_mul_left ( complexityWeight_le_one _ ) _ ) _ );
    -- From `h_arith`, we have `KPPlain U x + beta ≤ j + slack`.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, KPPlain U x = k := by
      cases h : KPPlain U x <;> simp_all +decide;
      cases h_arith;
    simp_all +decide [ complexityWeight_coe ];
    -- From `hdef'`, we have `2⁻¹ ^ k ≤ 2 ^ beta * (S.card : ℝ≥0∞)⁻¹`.
    -- Multiplying both sides by `2 ^ k * S.card`, we get `S.card ≤ 2 ^ (k + beta)`.
    have h_card : (S.card : ENNReal) ≤ 2 ^ (k + beta) := by
      convert mul_le_mul_right hdef' ( 2 ^ k * S.card ) using 1 ; ring_nf
      · simp +decide [ mul_assoc ];
        rw [ ← mul_pow, ENNReal.inv_mul_cancel ] <;> norm_num;
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, pow_add ];
        rw [ ← mul_assoc, ENNReal.mul_inv_cancel ] <;> norm_num [ hS.ne_empty ];
    norm_cast at *;
    exact h_card.trans ( pow_le_pow_right₀ ( by decide ) h_arith )

/-!
The exact affine converse of Theorem 5.
If `x` is `(alpha, beta)`-optimal stochastic, it has a description profile witness.
The proof uses `descriptionShift_complexity` (`inDescriptionProfile_portion`)
to convert the optimality-deficiency bound into the explicit log-size bound
by shifting `s = alpha - KP(S)` bits from the size parameter into the complexity parameter.
-/
theorem isOptimalSetStochastic_imp_profile (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (alpha beta j : ℕ),
      IsOptimalSetStochastic U x alpha beta →
      KPPlain U x + beta ≤ (alpha : ENat) + j →
      InDescriptionProfile U x (alpha + logSlack c (alpha + beta + j)) (j + 1) := by
  -- Follows from `inDescriptionProfile_portion` applied to the optimal set witness `S`.
  -- By definition, `|S| ≤ 2^{KP(x) + beta - KP(S)} ≤ 2^{alpha + j - KP(S)}`.
  -- Let `s = alpha - KP(S)`. Then `|S| ≤ 2^{j + s}`, so `S` is a `(KP(S), j + s)` description.
  -- Shifting by `s` yields a `(KP(S) + s + 2|bits s| + c, (j + s) - s + 1)` description,
  -- which is exactly `(alpha + O(log s), j + 1)`.
  obtain ⟨c, hc⟩ := inDescriptionProfile_portion U hU
  refine ⟨c + 2, fun x alpha beta j h_opt h_arith => ?_⟩
  obtain ⟨S, hS, hx, hcomp, hdef⟩ := h_opt
  -- The set complexity `m₀ = KP(S)` is finite (`≤ alpha`).
  obtain ⟨m₀, hm₀_eq⟩ : ∃ m : ℕ, setComplexity U S hS = m := by
    cases h : setComplexity U S hS <;> simp_all +decide
  have hm₀_le : m₀ ≤ alpha := by rw [hm₀_eq] at hcomp; exact_mod_cast hcomp
  -- The plain complexity `k = KP(x)` is finite (`≤ alpha + j`).
  obtain ⟨k, hk⟩ : ∃ k : ℕ, KPPlain U x = k := by
    cases h : KPPlain U x <;> simp_all +decide
    cases h_arith
  have h_arith_nat : k + beta ≤ alpha + j := by
    rw [hk] at h_arith; exact_mod_cast h_arith
  -- The sharp deficiency bound (keeping the `KP(S)` factor): `2⁻¹^k ≤ 2^beta · 2⁻¹^{m₀} · |S|⁻¹`.
  have hcard_ne : (S.card : ENNReal) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hcard_top : (S.card : ENNReal) ≠ ⊤ := by simp
  have hdef2 : (2 : ENNReal)⁻¹ ^ k ≤ 2 ^ beta * ((2 : ENNReal)⁻¹ ^ m₀ * (S.card : ENNReal)⁻¹) := by
    rw [setOptimalityDeficiencyLe_iff_of_mem hx] at hdef
    rw [hk, hm₀_eq, complexityWeight_coe, complexityWeight_coe] at hdef
    exact hdef
  -- Clearing denominators gives the integer incidence bound `2^{m₀} · |S| ≤ 2^{k+beta}`.
  have h_card : (2 : ENNReal) ^ m₀ * (S.card : ENNReal) ≤ 2 ^ (k + beta) := by
    convert mul_le_mul' hdef2 (le_refl (2 ^ k * 2 ^ m₀ * (S.card : ENNReal))) using 1
    · rw [show (2 : ENNReal)⁻¹ ^ k * (2 ^ k * 2 ^ m₀ * (S.card : ENNReal))
            = ((2 : ENNReal)⁻¹ ^ k * 2 ^ k) * (2 ^ m₀ * S.card) by ring,
        ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]
    · rw [show 2 ^ beta * ((2 : ENNReal)⁻¹ ^ m₀ * (S.card : ENNReal)⁻¹) * (2 ^ k * 2 ^ m₀ * (S.card : ENNReal))
            = (2 ^ k * 2 ^ beta) * ((2 : ENNReal)⁻¹ ^ m₀ * 2 ^ m₀) * ((S.card : ENNReal)⁻¹ * S.card) by ring,
        ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
        ENNReal.inv_mul_cancel hcard_ne hcard_top, one_pow, mul_one, mul_one, ← pow_add]
  have h_card_nat : 2 ^ m₀ * S.card ≤ 2 ^ (k + beta) := by exact_mod_cast h_card
  -- Hence `|S| ≤ 2^{k+beta-m₀} ≤ 2^{j+s}` for the shift amount `s = alpha - m₀`.
  have hScard_pos : 0 < S.card := hS.card_pos
  set s := alpha - m₀ with hs_def
  have hS_card : S.card ≤ 2 ^ (j + s) := by
    have hle : S.card ≤ 2 ^ (k + beta - m₀) := by
      rcases Nat.lt_or_ge (k + beta) m₀ with hlt | hge
      · exfalso
        have h1 : (2 : ℕ) ^ (k + beta) < 2 ^ m₀ := Nat.pow_lt_pow_right (by norm_num) hlt
        have h2 : (2 : ℕ) ^ m₀ ≤ 2 ^ m₀ * S.card := Nat.le_mul_of_pos_right _ hScard_pos
        omega
      · have hmul : 2 ^ m₀ * S.card ≤ 2 ^ m₀ * 2 ^ (k + beta - m₀) := by
          rw [← pow_add, Nat.add_sub_cancel' hge]; exact h_card_nat
        exact Nat.le_of_mul_le_mul_left hmul (pow_pos (by norm_num) m₀)
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- `S` is a `(m₀, j + s)`-description; shifting `s` bits lands at `(alpha + O(log s), j + 1)`.
  have hprof : InDescriptionProfile U x m₀ (j + s) := ⟨S, hS, hx, le_of_eq hm₀_eq, hS_card⟩
  have hportion := hc x m₀ (j + s) s hprof (Nat.le_add_left s j)
  rw [Nat.add_sub_cancel] at hportion
  have hcomplex_eq : m₀ + s = alpha := by rw [hs_def]; exact Nat.add_sub_cancel' hm₀_le
  rw [hcomplex_eq] at hportion
  -- Absorb the address cost `2·|bits s| + c` into `logSlack (c+2) (alpha+beta+j)`.
  refine hportion.mono_i ?_
  have hbits : (Nat.bits s).length ≤ (Nat.bits (alpha + beta + j)).length := by
    apply length_natBits_lt_pow
    exact lt_of_le_of_lt (by rw [hs_def]; omega) (lt_two_pow_length_natBits (alpha + beta + j))
  have h1 : 2 * (Nat.bits s).length ≤ (c + 2) * (Nat.bits (alpha + beta + j)).length := by
    calc 2 * (Nat.bits s).length
        ≤ 2 * (Nat.bits (alpha + beta + j)).length := by omega
      _ ≤ (c + 2) * (Nat.bits (alpha + beta + j)).length := Nat.mul_le_mul (by omega) (le_refl _)
  unfold logSlack
  omega

end Kolmogorov
