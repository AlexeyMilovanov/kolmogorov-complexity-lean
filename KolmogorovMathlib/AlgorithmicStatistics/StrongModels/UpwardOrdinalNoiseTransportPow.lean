import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseTransport
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerHardRegime

/-!
# The consumer-shaped ordinal noise transport for polynomially bounded deficiency

`UpwardOrdinalNoiseTransport.lean` proves the consumer instance
`StrongModelOrdinalNoiseTransportStatement`-shaped transport unconditionally in
the regime `beta ≤ n + epsilon + logSlack cBudget n`
(`strongModelOrdinalNoiseTransport_of_beta_le`).  This module widens that regime
from the linear budget to **any fixed power** of it.

Two steps are needed.

* `budgetedRandomNoiseTransport_of_beta_le_pow` repeats the assembly of
  `budgetedRandomNoiseTransport_of_beta_le`, with its budget-scale corner input
  replaced by `budgeted_stochasticity_to_plain_corner_of_beta_le_pow`
  (`BudgetedCornerHardRegime.lean`), which proves the corner whenever
  `beta ≤ baseBudget ^ k`.
* `strongModelOrdinalNoiseTransport_of_beta_le_pow` then plugs it into the
  existing consumer-side assembly (model-code budget, ordinal width, ordinal
  randomness and the radius absorption lemma
  `upward_ordinal_noise_radius_absorb`), exactly as in the linear case.

Nothing here assumes an open statement: the remaining regime is the one where
`beta` exceeds every fixed power of the model-code budget.
-/

namespace Kolmogorov

/-- **The budgeted random-noise transport for `beta ≤ baseBudget ^ k`.**  The
polynomial-regime version of `budgetedRandomNoiseTransport_of_beta_le`: the only
change is that the budget-scale corner is supplied by
`budgeted_stochasticity_to_plain_corner_of_beta_le_pow`. -/
theorem budgetedRandomNoiseTransport_of_beta_le_pow
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) (k : Nat) :
    ∃ c : Nat, ∀ (x y : BitString) (baseBudget epsilon alpha beta : Nat),
      plainK V x ≤ (baseBudget : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      beta ≤ baseBudget ^ k →
      IsStochastic U x alpha beta →
      IsStochastic U (pairCode x y)
        (alpha + (c * epsilon + logSlack c baseBudget + logSlack c y.length))
        (beta + (c * epsilon + logSlack c baseBudget + logSlack c y.length)) := by
  obtain ⟨c0, hC0⟩ := budgeted_stochasticity_to_plain_corner_of_beta_le_pow V U hV hU k
  obtain ⟨cR, hR⟩ := isStochastic_alpha_le_budget V U hV hU
  obtain ⟨cE, hE⟩ := inPlainDescriptionProfile_pair_of_base V hV
  obtain ⟨cP, hP⟩ := plainK_pair_ge_plainK_add_length_of_random_budget V U hV hU
  obtain ⟨cS, hS⟩ := isStochastic_of_plainProfile_twoPartSum_sharp V U hV hU
  obtain ⟨b0, hb0⟩ := logSlack_le_add_const c0
  obtain ⟨bR, hbR⟩ := logSlack_le_add_const cR
  obtain ⟨bE, hbE⟩ := logSlack_le_add_const cE
  obtain ⟨CS, hCS⟩ := logSlack_linear_bound cS 3 (b0 + bR + bE)
  refine ⟨cP + c0 + cE + CS + cR + 1, ?_⟩
  intro x y baseBudget epsilon alpha beta hxBudget hrandom hbeta hstoch
  set c := cP + c0 + cE + CS + cR + 1 with hc
  -- Exact natural values of the two plain complexities involved.
  obtain ⟨kx, hkx⟩ := exists_plainK_eq_nat V hV x
  obtain ⟨kxy, hkxy⟩ := exists_plainK_eq_nat V hV (pairCode x y)
  have hkxB : kx ≤ baseBudget := by
    rw [hkx] at hxBudget
    exact_mod_cast hxBudget
  -- Step 1: cap the complexity parameter at the visible budget.
  set alpha' := min alpha (baseBudget + logSlack cR baseBudget) with halpha'
  have hstoch' : IsStochastic U x alpha' beta :=
    hR x kx baseBudget alpha beta hkx hkxB hstoch
  have halpha'_le : alpha' ≤ alpha := min_le_left _ _
  have halpha'_bud : alpha' ≤ baseBudget + logSlack cR baseBudget := min_le_right _ _
  -- Step 2: the budget-scale forward corner, now a theorem for `beta ≤ baseBudget`.
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    hC0 x kx baseBudget alpha' beta hkx hkxB hbeta hstoch'
  -- Step 3: extend every model of `x` by the full noise cube.
  have hprofPair :
      InPlainDescriptionProfile V (pairCode x y)
        (i + logSlack cE y.length) (j + y.length) := hE x y i j hprof
  set i2 := i + logSlack cE y.length with hi2
  set j2 := j + y.length with hj2
  -- Step 4: budget-scale symmetry of information for the pair.
  have hsoi : kx + y.length ≤ kxy + epsilon + logSlack cP (baseBudget + y.length) :=
    hP x y epsilon kx kxy (baseBudget + y.length) hkx hkxy hrandom
      (by omega) (by omega)
  set beta2 :=
    beta + epsilon + logSlack cP (baseBudget + y.length) + logSlack c0 baseBudget +
      logSlack cE y.length with hbeta2
  have hsum : i2 + j2 ≤ kxy + beta2 := by
    simp only [hi2, hj2, hbeta2]
    omega
  -- Step 5: back to stochasticity, with a slack logarithmic in `i2` only.
  have hpair := hS (pairCode x y) i2 kxy i2 j2 beta2 le_rfl hkxy hprofPair hsum
  -- Radius bookkeeping.
  have hi2_bound : i2 ≤ 3 * (baseBudget + y.length) + (b0 + bR + bE) := by
    have h0 := hb0 baseBudget
    have hRb := hbR baseBudget
    have hEb := hbE y.length
    simp only [hi2]
    omega
  have hslackS : logSlack cS i2 ≤ logSlack CS baseBudget + logSlack CS y.length := by
    calc logSlack cS i2
        ≤ logSlack cS (3 * (baseBudget + y.length) + (b0 + bR + bE)) :=
          logSlack_mono_right cS hi2_bound
      _ ≤ logSlack CS (baseBudget + y.length) := hCS (baseBudget + y.length)
      _ ≤ logSlack CS baseBudget + logSlack CS y.length :=
          logSlack_add_le CS baseBudget y.length
  have hslackP :
      logSlack cP (baseBudget + y.length) ≤
        logSlack cP baseBudget + logSlack cP y.length :=
    logSlack_add_le cP baseBudget y.length
  have hbudgetFold :
      logSlack c0 baseBudget + logSlack CS baseBudget + logSlack cP baseBudget ≤
        logSlack c baseBudget := by
    have h1 : logSlack c0 baseBudget + logSlack CS baseBudget
        = logSlack (c0 + CS) baseBudget := logSlack_add_const _ _ _
    have h2 : logSlack (c0 + CS) baseBudget + logSlack cP baseBudget
        = logSlack (c0 + CS + cP) baseBudget := logSlack_add_const _ _ _
    have h3 : logSlack (c0 + CS + cP) baseBudget ≤ logSlack c baseBudget :=
      logSlack_mono_left (by omega) baseBudget
    omega
  have hnoiseFold :
      logSlack cE y.length + logSlack CS y.length + logSlack cP y.length ≤
        logSlack c y.length := by
    have h1 : logSlack cE y.length + logSlack CS y.length
        = logSlack (cE + CS) y.length := logSlack_add_const _ _ _
    have h2 : logSlack (cE + CS) y.length + logSlack cP y.length
        = logSlack (cE + CS + cP) y.length := logSlack_add_const _ _ _
    have h3 : logSlack (cE + CS + cP) y.length ≤ logSlack c y.length :=
      logSlack_mono_left (by omega) y.length
    omega
  have heps : epsilon ≤ c * epsilon := Nat.le_mul_of_pos_left epsilon (by omega)
  exact isStochastic_mono (by omega) (by omega) hpair

/-- **The consumer-shaped ordinal transport for polynomially bounded `beta`.**
The `beta ≤ baseBudget ^ k` analogue of
`strongModelOrdinalNoiseTransport_of_beta_le`: for every fixed exponent `k`, the
pair `(model code, ordinal index)` of a strong set model stays stochastic up to
the source-scale radius `c * epsilon + logSlack c n`, provided the deficiency
parameter is bounded by the `k`-th power of the canonical model-code budget. -/
theorem strongModelOrdinalNoiseTransport_of_beta_le_pow
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (k : Nat) :
    ∃ cBudget c : Nat, ∀ x A (hA : A.Nonempty)
        n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      beta ≤ (n + epsilon + logSlack cBudget n) ^ k →
      IsStochastic U (codedUniformOn A hA).code alpha beta →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
        (alpha + (c * epsilon + logSlack c n))
        (beta + (c * epsilon + logSlack c n)) := by
  obtain ⟨cNoise, hNoise⟩ :=
    budgetedRandomNoiseTransport_of_beta_le_pow V U hV hU k
  obtain ⟨cBudget, hBudget⟩ :=
    plainK_strongModelCode_le V T hV hT.1
  obtain ⟨cWidth, hWidth⟩ :=
    finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨cOrdinal, hOrdinal⟩ :=
    strongModelOrdinalBits_plain_random_given_model V U hV hU
  obtain ⟨C, hAbsorb⟩ :=
    upward_ordinal_noise_radius_absorb cNoise cOrdinal cBudget cWidth
  refine ⟨cBudget, C, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hbeta hstoch
  let modelCode := (codedUniformOn A hA).code
  let u := strongModelOrdinalBits A x
  let noiseEpsilon := cOrdinal * epsilon + logSlack cOrdinal n
  let baseBudget := n + epsilon + logSlack cBudget n
  have huLen : u.length = finiteSetLogCard A :=
    strongModelOrdinalBits_length A x hx
  have hModelBudget : plainK V modelCode ≤ (baseBudget : ENat) := by
    simpa [modelCode, baseBudget] using
      hBudget x A hA n epsilon hxn hstrong
  have hWidthBound :
      finiteSetLogCard A ≤ n + epsilon + logSlack cWidth n :=
    hWidth A hA x n epsilon hxn hx hdef
  have hRandom :
      (u.length : ENat) ≤ condK V u modelCode + (noiseEpsilon : ENat) := by
    simpa [u, modelCode, noiseEpsilon, huLen] using
      hOrdinal A hA x n epsilon hxn hx hdef
  have hForward := hNoise modelCode u baseBudget noiseEpsilon alpha beta
    hModelBudget hRandom (by simpa [baseBudget] using hbeta) hstoch
  have hRawLe :
      cNoise * noiseEpsilon + logSlack cNoise baseBudget +
          logSlack cNoise u.length
        ≤ C * epsilon + logSlack C n :=
    hAbsorb n epsilon u.length (by simpa [huLen] using hWidthBound)
  have hForward' :
      IsStochastic U (pairCode modelCode u)
        (alpha + (C * epsilon + logSlack C n))
        (beta + (C * epsilon + logSlack C n)) :=
    isStochastic_mono (Nat.add_le_add_left hRawLe alpha)
      (Nat.add_le_add_left hRawLe beta) hForward
  simpa [strongModelOrdinalBitsPair, modelCode, u] using hForward'

end Kolmogorov
