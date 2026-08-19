import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedNoiseTransport
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedSectionThree

/-!
# The budgeted noise transport, unconditionally, for deficiencies within budget

`budgetedRandomNoiseTransport_of_budgetedPlainCorner` derives the budgeted
random-noise transport from `BudgetedPlainProfileCornerStatement`, which is still
open in general.  The complexity-scale §3 chain proves that corner whenever the
deficiency parameter fits the visible budget
(`budgeted_stochasticity_to_plain_corner_of_beta_le`), so in that regime the
transport itself becomes an unconditional theorem.

`budgetedRandomNoiseTransport_of_beta_le` below is exactly
`BudgetedRandomNoiseTransportStatement V U` with the extra hypothesis
`beta ≤ baseBudget`; it carries no unproved side condition.  Note in particular
that neither `l(x)` nor `alpha` is restricted.
-/

namespace Kolmogorov

open Nat

/-- **The budgeted random-noise transport for `beta ≤ baseBudget`.**  Adding
`x`-random noise `y` to a string `x` of complexity at most `baseBudget` preserves
`(alpha, beta)`-stochasticity up to the budget-scale slack
`c * epsilon + logSlack c baseBudget + logSlack c l(y)`, provided the deficiency
parameter fits the budget.

This is the conclusion of `budgetedRandomNoiseTransport_of_budgetedPlainCorner`
with its open corner hypothesis discharged by the complexity-scale §3 chain. -/
theorem budgetedRandomNoiseTransport_of_beta_le
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (baseBudget epsilon alpha beta : Nat),
      plainK V x ≤ (baseBudget : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      beta ≤ baseBudget →
      IsStochastic U x alpha beta →
      IsStochastic U (pairCode x y)
        (alpha + (c * epsilon + logSlack c baseBudget + logSlack c y.length))
        (beta + (c * epsilon + logSlack c baseBudget + logSlack c y.length)) := by
  obtain ⟨c0, hC0⟩ := budgeted_stochasticity_to_plain_corner_of_beta_le V U hV hU
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

end Kolmogorov
