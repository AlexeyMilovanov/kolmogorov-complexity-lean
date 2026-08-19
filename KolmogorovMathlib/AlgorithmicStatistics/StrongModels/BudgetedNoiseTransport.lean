import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedPairSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional

/-!
# Reducing the budgeted noise transport to a budget-scale plain corner

`BudgetedRandomNoiseTransportStatement V U` is the remaining input of the
upward-closure assembly: it measures every logarithmic overhead against a
*complexity* budget for the head string, never against its length.  The proved
length-scale transport `stochasticity_pair_of_plain_random_noise` cannot supply
it, because a model code may be exponentially longer than its complexity.

This module isolates *where* the length scale actually enters that proof.  Each
of its four steps is available (or is reproved here) at the budget scale except
one, the §3 forward corner:

* the `alpha`-reduction `isStochastic_alpha_le_budget` — budget scale already;
* the forward plain corner — **the only missing input**, packaged below as
  `BudgetedPlainProfileCornerStatement`;
* the uniform noise extension `inPlainDescriptionProfile_pair_of_base` — its
  slack is `O(log l(y))`, i.e. logarithmic in the noise length only;
* the pair symmetry of information — supplied at the budget scale by
  `plainK_pair_ge_plainK_add_length_of_random_budget`;
* the two-part-sum conversion — reproved here as
  `isStochastic_of_plainProfile_twoPartSum_sharp`, whose slack is logarithmic in
  the *complexity coordinate* `i` alone (the size coordinate, the deficiency
  parameter and the complexity of the object play no role).

The main theorem `budgetedRandomNoiseTransport_of_budgetedPlainCorner` then
derives the full budgeted transport from the corner statement alone.  This
replaces the open pair-level obligation by a single-string §3 research interface
that mentions neither the noise string nor any length.

For comparison, `budgeted_stochasticity_to_plain_corner_of_length_le` proves
exactly the corner in the regime `l(x) ≤ baseBudget`, `beta ≤ baseBudget`; the
statement below asks for it with no such restriction.
-/

namespace Kolmogorov

open Nat

/-- **Sharp form of the two-part-sum conversion.**  Identical to
`isStochastic_of_plainProfile_twoPartSum` except that the budget `N` only has to
dominate the *complexity coordinate* `i`: the size coordinate `j`, the
deficiency parameter `beta` and the complexity `C(z)` need not fit in `N`.

This sharpening is what makes a budget-scale add-noise transport possible: in
the application `j` and `beta` can be exponentially larger than the visible
complexity budget, while `i` stays inside it by the `alpha`-reduction. -/
theorem isStochastic_of_plainProfile_twoPartSum_sharp
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (z : BitString) (N kz i j beta : Nat),
      i ≤ N →
      plainK V z = (kz : ENat) →
      InPlainDescriptionProfile V z i j →
      i + j ≤ kz + beta →
      IsStochastic U z (i + logSlack c N) (beta + logSlack c N) := by
  obtain ⟨cB, hB⟩ := inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨cP, hP⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨cR, hR⟩ := randomness_optimality U hU
  refine ⟨cB + cP + cR, fun z N kz i j beta hi hkz hprof hsum => ?_⟩
  obtain ⟨A, hA, hzA, hcompA, hcardA⟩ := hB z i j hprof
  have hkzP : (kz : ENat) ≤ KPPlain U z + (cP : ENat) := by
    have h := hP z; rwa [hkz] at h
  have hnat : i + logSlack cB i + j ≤ kz + beta + logSlack cB i := by omega
  have h_arith : (↑(i + logSlack cB i) : ENat) + (j : ENat)
      ≤ KPPlain U z + ((beta + cP + logSlack cB i : Nat) : ENat) := by
    calc (↑(i + logSlack cB i) : ENat) + (j : ENat)
        = ((i + logSlack cB i + j : Nat) : ENat) := by push_cast; ring
      _ ≤ ((kz + beta + logSlack cB i : Nat) : ENat) := by exact_mod_cast hnat
      _ = (kz : ENat) + ((beta + logSlack cB i : Nat) : ENat) := by push_cast; ring
      _ ≤ (KPPlain U z + (cP : ENat)) + ((beta + logSlack cB i : Nat) : ENat) := by
          gcongr
      _ = KPPlain U z + ((beta + cP + logSlack cB i : Nat) : ENat) := by push_cast; abel
  have hopt : OptimalityDeficiencyLe U (codedUniformOn A hA) z
      (beta + cP + logSlack cB i) :=
    setOptimalityDeficiencyLe_of_profile hzA hcompA hcardA h_arith
  have hdef := hR (codedUniformOn A hA) z (beta + cP + logSlack cB i) hopt
  have hstoch : IsStochastic U z (i + logSlack cB i)
      (beta + cP + logSlack cB i + cR) :=
    isStochastic_of_model U z (codedUniformOn A hA) (i + logSlack cB i)
      (beta + cP + logSlack cB i + cR) (codedUniformOn_isProbability A hA)
      (by simpa [setComplexity, CodedFiniteDistribution.complexity] using hcompA) hdef
  refine isStochastic_mono ?_ ?_ hstoch
  · have h1 : logSlack cB i ≤ logSlack (cB + cP + cR) N :=
      (logSlack_mono_right cB hi).trans (logSlack_mono_left (by omega) N)
    omega
  · have hle : logSlack cB i ≤ logSlack cB N := logSlack_mono_right cB hi
    have hroom : logSlack cB N + (cP + cR) ≤ logSlack (cB + cP + cR) N := by
      have h := logSlack_add_const_le cB (cP + cR) N
      rw [Nat.add_assoc cB cP cR]
      exact h
    omega

/-- **The budget-scale forward plain corner.**  An `(alpha, beta)`-stochasticity
witness for `x` yields an ordinary plain `(i, j)` description with

* `i ≤ alpha + O(log baseBudget)` and
* `i + j ≤ C(x) + beta + O(log baseBudget)`,

where the *only* visible parameter in the slack is a complexity budget
`baseBudget ≥ C(x)`: neither the length `l(x)`, nor `alpha`, nor `beta` occurs.

The `alpha`-freeness is already proved (`isStochastic_alpha_le_budget`); the
proved corner `budgeted_stochasticity_to_plain_corner_of_length_le` gives this
statement whenever `l(x) ≤ baseBudget` and `beta ≤ baseBudget`.

It is *not* claimed here that the statement holds in general: the proved §3
route (deficiencies theorem plus improving descriptions) pays
`O(log (C(x) + alpha + beta))`, and the residual `log beta` is precisely what
the length-scale argument removes by truncating `beta` first.  This shows that
the currently proved §3 route does not establish the statement; it is not a
refutation of the statement in the large-`beta` regime.  The proposition is
retained as a research/reduction interface for the conditional assembly below,
not as an external dependency that may be assumed to complete `prop:upward`.
The completion route remains the direct charged heavy-truncation argument. -/
def BudgetedPlainProfileCornerStatement (V U : Map) : Prop :=
  ∃ c : Nat, ∀ (x : BitString) (kx baseBudget alpha beta : Nat),
    plainK V x = (kx : ENat) →
    kx ≤ baseBudget →
    IsStochastic U x alpha beta →
    ∃ i j,
      InPlainDescriptionProfile V x i j ∧
      i ≤ alpha + logSlack c baseBudget ∧
      i + j ≤ kx + beta + logSlack c baseBudget

/-- **The reduction.**  The budget-scale forward corner implies the full
budgeted random-noise transport required by `prop:upward`.

All remaining ingredients are budget-scale: the `alpha`-reduction, the uniform
noise extension (slack `O(log l(y))`), the budgeted pair symmetry of information
`plainK_pair_ge_plainK_add_length_of_random_budget`, and the sharp two-part-sum
conversion `isStochastic_of_plainProfile_twoPartSum_sharp`, whose slack is
logarithmic in the complexity coordinate only. -/
theorem budgetedRandomNoiseTransport_of_budgetedPlainCorner
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hCorner : BudgetedPlainProfileCornerStatement V U) :
    BudgetedRandomNoiseTransportStatement V U := by
  obtain ⟨c0, hC0⟩ := hCorner
  obtain ⟨cR, hR⟩ := isStochastic_alpha_le_budget V U hV hU
  obtain ⟨cE, hE⟩ := inPlainDescriptionProfile_pair_of_base V hV
  obtain ⟨cP, hP⟩ := plainK_pair_ge_plainK_add_length_of_random_budget V U hV hU
  obtain ⟨cS, hS⟩ := isStochastic_of_plainProfile_twoPartSum_sharp V U hV hU
  obtain ⟨b0, hb0⟩ := logSlack_le_add_const c0
  obtain ⟨bR, hbR⟩ := logSlack_le_add_const cR
  obtain ⟨bE, hbE⟩ := logSlack_le_add_const cE
  obtain ⟨CS, hCS⟩ := logSlack_linear_bound cS 3 (b0 + bR + bE)
  refine ⟨cP + c0 + cE + CS + cR + 1, ?_⟩
  intro x y baseBudget epsilon alpha beta hxBudget hrandom hstoch
  set c := cP + c0 + cE + CS + cR + 1 with hc
  change IsStochastic U (pairCode x y)
    (alpha + (c * epsilon + logSlack c baseBudget + logSlack c y.length))
    (beta + (c * epsilon + logSlack c baseBudget + logSlack c y.length))
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
  -- Step 2: the budget-scale forward corner.
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    hC0 x kx baseBudget alpha' beta hkx hkxB hstoch'
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

/-- **Upward closure from the budget-scale corner.**  Composing the reduction
with the existing conditional assembly
`propUpward_of_budgetedRandomNoiseTransport`, the whole of `prop:upward` now
rests on the single-string §3 corner statement. -/
theorem propUpward_of_budgetedPlainCorner
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hCorner : BudgetedPlainProfileCornerStatement V U) :
    PropUpwardStatement U T :=
  propUpward_of_budgetedRandomNoiseTransport V U T hV hU hT
    (budgetedRandomNoiseTransport_of_budgetedPlainCorner V U hV hU hCorner)

end Kolmogorov
