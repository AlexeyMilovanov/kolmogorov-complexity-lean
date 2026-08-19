import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseRegimes
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedPairSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RadiusMonotone

/-!
# The complexity-parameter regime of the consumer-shaped ordinal noise transport

`UpwardOrdinalNoiseRegimes.lean` widens the discharged region of the consumer
transport along the *deficiency* axis (`beta` below a fixed power of the
model-code budget) and records the resulting dichotomy.  This module widens it
along the orthogonal, *complexity* axis.

The point is that the target string of the transport, the ordinal pair
`strongModelOrdinalBitsPair A hA x = pairCode (codedUniformOn A hA).code
(strongModelOrdinalBits A x)`, has a visible plain complexity budget of its own:
the model code costs at most `baseBudget = n + epsilon + logSlack c n`
(`plainK_strongModelCode_le`) and the ordinal index has length at most the same
budget (`finiteSetLogCard_le_length_add_deficiency_log`), so
`plainK_pair_le_plainK_add_length_budget` bounds the pair by
`2 * baseBudget + O(log baseBudget)`.  Once the complexity parameter `alpha`
exceeds that bound, the Dirac model on the pair
(`isStochastic_dirac_of_plainK`) already witnesses stochasticity with deficiency
`0`, and no transport argument is needed at all.

Two results follow.

* `strongModelOrdinalNoiseTransport_of_alpha_ge` — the consumer transport
  conclusion holds unconditionally, for *every* `beta` and with no stochasticity
  hypothesis whatsoever, as soon as `2 * (n + epsilon + logSlack cBudget n)
  ≤ alpha`.
* `strongModelOrdinalNoiseTransport_trichotomy` — combining this with
  `strongModelOrdinalNoiseTransport_dichotomy`, for each fixed exponent `k`
  every stochasticity witness of the model code either already yields transport
  at the source-scale radius, or has *both* a small complexity coordinate
  (`alpha < 2 * (n + epsilon + logSlack cAlpha n)`) and a Pareto-minimal
  sub-witness whose deficiency exceeds the chosen fixed power of the model-code
  budget.

Nothing here assumes an open statement; the second branch of the trichotomy is a
*description* of the residual case, not a claim of transport in it.
-/

namespace Kolmogorov

/-- **Consumer ordinal transport for large complexity parameter.**  If the
complexity parameter `alpha` already dominates twice the model-code budget
`n + epsilon + logSlack cBudget n`, then the ordinal pair is stochastic at
`(alpha + radius, beta + radius)` for *every* `beta`, with no stochasticity
hypothesis on the model code.

Indeed the pair costs at most `2 * (n + epsilon + logSlack cBudget n) +
O(log ·)` plain bits, so its own Dirac model is already available inside the
complexity budget and has zero randomness deficiency. -/
theorem strongModelOrdinalNoiseTransport_of_alpha_ge
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ cBudget c : ℕ, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      2 * (n + epsilon + logSlack cBudget n) ≤ alpha →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
        (alpha + (c * epsilon + logSlack c n))
        (beta + (c * epsilon + logSlack c n)) := by
  obtain ⟨cModel, hModel⟩ := plainK_strongModelCode_le V T hV hT.1
  obtain ⟨cWidth, hWidth⟩ := finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_plainK_add_length_budget V U hV hU
  obtain ⟨cD, hD⟩ := isStochastic_dirac_of_plainK V U hV hU
  obtain ⟨bPair, hbPair⟩ := logSlack_le_add_const cPair
  obtain ⟨CD, hCD⟩ := logSlack_linear_bound cD 3 bPair
  obtain ⟨C, hAbsorb⟩ :=
    upward_ordinal_noise_radius_absorb (cPair + CD) 0 (cModel + cWidth) cWidth
  refine ⟨cModel + cWidth, C, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef halpha
  set modelCode := (codedUniformOn A hA).code with hmodelCode
  set u := strongModelOrdinalBits A x with hu
  set N := n + epsilon + logSlack (cModel + cWidth) n with hNdef
  -- The model code fits the budget `N`.
  obtain ⟨kM, hkM⟩ := exists_plainK_eq_nat V hV modelCode
  have hkMN : kM ≤ N := by
    have hb := hModel x A hA n epsilon hxn hstrong
    rw [← hmodelCode, hkM] at hb
    have hb' : kM ≤ n + epsilon + logSlack cModel n := by exact_mod_cast hb
    have := logSlack_mono_left (Nat.le_add_right cModel cWidth) n
    omega
  -- The ordinal index also fits the budget `N`.
  have huLen : u.length = finiteSetLogCard A := strongModelOrdinalBits_length A x hx
  have hWidthBound : finiteSetLogCard A ≤ n + epsilon + logSlack cWidth n :=
    hWidth A hA x n epsilon hxn hx hdef
  have huN : u.length ≤ N := by
    have := logSlack_mono_left (Nat.le_add_left cWidth cModel) n
    omega
  -- Hence the pair has a visible plain complexity budget.
  obtain ⟨kP, hkP⟩ := exists_plainK_eq_nat V hV (pairCode modelCode u)
  have hkPle : kP ≤ kM + u.length + logSlack cPair N := by
    have hb := hPair modelCode u kM N hkM hkMN huN
    rw [hkP] at hb
    exact_mod_cast hb
  -- The Dirac model on the pair witnesses stochasticity with deficiency `0`.
  have hdirac : IsStochastic U (pairCode modelCode u) (kP + logSlack cD kP) 0 :=
    hD (pairCode modelCode u) kP hkP
  -- Radius bookkeeping.
  have hkP3 : kP ≤ 3 * N + bPair := by
    have := hbPair N
    omega
  have hslackD : logSlack cD kP ≤ logSlack CD N :=
    (logSlack_mono_right cD hkP3).trans (hCD N)
  have hfold : logSlack cPair N + logSlack CD N = logSlack (cPair + CD) N :=
    logSlack_add_const _ _ _
  have habs :
      (cPair + CD) * (0 * epsilon + logSlack 0 n) + logSlack (cPair + CD) N +
          logSlack (cPair + CD) u.length ≤ C * epsilon + logSlack C n :=
    hAbsorb n epsilon u.length (by omega)
  have hzero : (cPair + CD) * (0 * epsilon + logSlack 0 n) = 0 := by simp [logSlack]
  have hle : kP + logSlack cD kP ≤ alpha + (C * epsilon + logSlack C n) := by
    rw [hzero] at habs
    omega
  have hfinal :
      IsStochastic U (pairCode modelCode u)
        (alpha + (C * epsilon + logSlack C n))
        (beta + (C * epsilon + logSlack C n)) :=
    isStochastic_mono hle (Nat.zero_le _) hdirac
  simpa [strongModelOrdinalBitsPair, hmodelCode, hu] using hfinal

/-- **The consumer ordinal transport trichotomy.**  For each fixed exponent `k`,
every stochasticity witness `(alpha, beta)` of the canonical model code either
already gives the ordinal pair at the source-scale radius, or is confined to the
*small complexity, large deficiency* corner: `alpha` stays below twice the
model-code budget, and a Pareto-minimal sub-witness `(a, b)` has deficiency above
the chosen fixed power of that budget.

This sharpens `strongModelOrdinalNoiseTransport_dichotomy` by the extra
complexity-axis constraint coming from
`strongModelOrdinalNoiseTransport_of_alpha_ge`.  The theorem is unconditional
and its second branch only *describes* the residual case; establishing transport
there remains the alternative research direction (see `PropUpwardFrontier.lean`). -/
theorem strongModelOrdinalNoiseTransport_trichotomy
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (k : ℕ) :
    ∃ cBudget cAlpha c : ℕ, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      IsStochastic U (codedUniformOn A hA).code alpha beta →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
          (alpha + (c * epsilon + logSlack c n))
          (beta + (c * epsilon + logSlack c n)) ∨
        (alpha < 2 * (n + epsilon + logSlack cAlpha n) ∧
          ∃ a b : ℕ, a ≤ alpha ∧ b ≤ beta ∧
            IsStochastic U (codedUniformOn A hA).code a b ∧
            (n + epsilon + logSlack cBudget n) ^ k < b ∧
            (∀ b' : ℕ, b' < b → ¬ IsStochastic U (codedUniformOn A hA).code a b') ∧
            (∀ a' : ℕ, a' < a → ¬ IsStochastic U (codedUniformOn A hA).code a' b)) := by
  obtain ⟨cBudget, cDich, hdich⟩ :=
    strongModelOrdinalNoiseTransport_dichotomy V U T hV hU hT k
  obtain ⟨cAlpha, cLarge, hlarge⟩ :=
    strongModelOrdinalNoiseTransport_of_alpha_ge V U T hV hU hT
  refine ⟨cBudget, cAlpha, cDich + cLarge, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  by_cases halpha : 2 * (n + epsilon + logSlack cAlpha n) ≤ alpha
  · refine Or.inl ?_
    have h := hlarge x A hA n epsilon alpha beta hxn hx hstrong hdef halpha
    exact isStochastic_radius_mono (Nat.le_add_left _ _) epsilon n h
  · rcases hdich x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch with h | h
    · exact Or.inl (isStochastic_radius_mono (Nat.le_add_right _ _) epsilon n h)
    · exact Or.inr ⟨not_le.mp halpha, h⟩

end Kolmogorov
