import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerLengthScale

/-!
# Restricting the open regime of the budgeted plain corner to minimal witnesses

`BudgetedPlainProfileCornerStatement V U` (`BudgetedNoiseTransport.lean`) is the
remaining input of `prop:upward`.  `BudgetedCornerHardRegime.lean` and
`BudgetedCornerLengthScale.lean` reduce it to the doubly superpolynomial regime
`alpha < kx ≤ baseBudget`, `baseBudget ^ k < beta`, `baseBudget ^ k < l(x)` with a
length that is not simple.

This module narrows that regime once more along a completely different axis: the
open case may additionally be assumed to concern a **Pareto-minimal**
stochasticity witness, i.e. a pair `(alpha, beta)` such that

* no smaller deficiency parameter works at the same complexity level
  (`∀ b < beta, ¬ IsStochastic U x alpha b`), and
* no smaller complexity level works at the same deficiency parameter
  (`∀ a < alpha, ¬ IsStochastic U x a beta`).

The reason is monotonicity: `IsStochastic` is upward closed in both coordinates
(`IsStochastic.mono_alpha`, `IsStochastic.mono_beta`), while the two conclusions
of the corner are *decreasing* in both coordinates.  Hence a corner produced for
a smaller witness is automatically a corner for the given one, and by
well-ordering of `ℕ` a Pareto-minimal witness below any given witness always
exists (`exists_pareto_minimal_stochastic_witness`).

Passing to a minimal witness also automatically re-enters the already proved
polynomial regime whenever the minimal deficiency happens to be small, so the
combined reduction `budgetedPlainCorner_of_hard_regime_superpoly_minimal`
retains every superpolynomiality restriction of
`budgetedPlainCorner_of_hard_regime_superpoly` and adds the two minimality
hypotheses on top of it.

Nothing here assumes an open statement, and no frozen interface is edited.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **A Pareto-minimal stochasticity witness below a given one.**  If `x` is
`(alpha, beta)`-stochastic then there are `a ≤ alpha` and `b ≤ beta` such that `x`
is `(a, b)`-stochastic, no strictly smaller deficiency parameter works at level
`a`, and no strictly smaller complexity level works at deficiency `b`.

Both minimizations are by well-ordering of `ℕ`; the first minimality statement
survives the second minimization because stochasticity is monotone in the
complexity coordinate. -/
theorem exists_pareto_minimal_stochastic_witness
    (U : Map) (x : BitString) (alpha beta : ℕ) (h : IsStochastic U x alpha beta) :
    ∃ a b : ℕ, a ≤ alpha ∧ b ≤ beta ∧ IsStochastic U x a b ∧
      (∀ b' : ℕ, b' < b → ¬ IsStochastic U x a b') ∧
      (∀ a' : ℕ, a' < a → ¬ IsStochastic U x a' b) := by
  classical
  have hb : ∃ b : ℕ, IsStochastic U x alpha b := ⟨beta, h⟩
  set b0 := Nat.find hb with hb0
  have hb0le : b0 ≤ beta := Nat.find_le h
  have hb0spec : IsStochastic U x alpha b0 := Nat.find_spec hb
  have hb0min : ∀ b' : ℕ, b' < b0 → ¬ IsStochastic U x alpha b' := fun b' hlt =>
    Nat.find_min hb hlt
  have ha : ∃ a : ℕ, IsStochastic U x a b0 := ⟨alpha, hb0spec⟩
  set a0 := Nat.find ha with ha0
  have ha0le : a0 ≤ alpha := Nat.find_le hb0spec
  have ha0spec : IsStochastic U x a0 b0 := Nat.find_spec ha
  have ha0min : ∀ a' : ℕ, a' < a0 → ¬ IsStochastic U x a' b0 := fun a' hlt =>
    Nat.find_min ha hlt
  refine ⟨a0, b0, ha0le, hb0le, ha0spec, ?_, ha0min⟩
  intro b' hlt hstoch
  exact hb0min b' hlt (hstoch.mono_alpha ha0le)

/-- A deficiency-minimal stochasticity coordinate cannot be lowered by one
using the same probability model.  This is the direct diagnostic consequence
of minimality used before analyzing a tight level-set witness. -/
theorem deficiency_not_le_pred_of_beta_minimal
    {U : Map} {z : BitString} {alpha beta : Nat}
    {P : CodedFiniteDistribution}
    (hmin : ∀ b < beta, ¬ IsStochastic U z alpha b)
    (hprob : P.IsProbability)
    (hcomp : P.complexity U ≤ (alpha : ENat)) :
    beta = 0 ∨ ¬ DeficiencyLe U P z (beta - 1) := by
  by_cases hzero : beta = 0
  · exact Or.inl hzero
  · refine Or.inr fun hpred => ?_
    exact hmin (beta - 1) (by omega)
      (isStochastic_of_model U z P alpha (beta - 1) hprob hcomp hpred)

/-- **The budgeted plain corner is inherited from any smaller witness.**  Both
corner inequalities are decreasing in `alpha` and in `beta`, so a corner produced
for `(a, b)` with `a ≤ alpha` and `b ≤ beta` is already a corner for
`(alpha, beta)`. -/
theorem budgeted_plain_corner_mono_witness
    (V : Map) (x : BitString) (kx baseBudget alpha beta a b c i j : ℕ)
    (ha : a ≤ alpha) (hb : b ≤ beta)
    (hprof : InPlainDescriptionProfile V x i j)
    (hi : i ≤ a + logSlack c baseBudget)
    (hij : i + j ≤ kx + b + logSlack c baseBudget) :
    ∃ i' j', InPlainDescriptionProfile V x i' j' ∧
      i' ≤ alpha + logSlack c baseBudget ∧
      i' + j' ≤ kx + beta + logSlack c baseBudget :=
  ⟨i, j, hprof, by omega, by omega⟩

/-- **The exact budget-scale corner whenever *some* witness below `(alpha, beta)`
has polynomially bounded deficiency.**  A strengthening of
`budgeted_stochasticity_to_plain_corner_of_min_le_pow`: it suffices that the
polynomial bound `min b l(x) ≤ baseBudget ^ k` be met by an auxiliary witness
`(a, b)` with `a ≤ alpha` and `b ≤ beta`, not by `(alpha, beta)` itself. -/
theorem budgeted_stochasticity_to_plain_corner_of_witness_min_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta a b : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      a ≤ alpha →
      b ≤ beta →
      min b x.length ≤ baseBudget ^ k →
      IsStochastic U x a b →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := budgeted_stochasticity_to_plain_corner_of_min_le_pow V U hV hU k
  refine ⟨c, fun x kx baseBudget alpha beta a b hkx hkxB ha hb hmin hstoch => ?_⟩
  obtain ⟨i, j, hprof, hi, hij⟩ := hc x kx baseBudget a b hkx hkxB hmin hstoch
  exact budgeted_plain_corner_mono_witness V x kx baseBudget alpha beta a b c i j
    ha hb hprof hi hij

/-- **The budgeted plain corner reduces to its doubly superpolynomial regime with
a Pareto-minimal witness.**  A sharpening of
`budgetedPlainCorner_of_hard_regime_superpoly`: the open regime may additionally
be assumed to satisfy

```text
∀ b < beta, ¬ IsStochastic U x alpha b   and   ∀ a < alpha, ¬ IsStochastic U x a beta,
```

i.e. the stochasticity witness is Pareto-minimal in both coordinates.

Given an arbitrary witness, `exists_pareto_minimal_stochastic_witness` produces a
minimal one below it; if its deficiency parameter is polynomially bounded, the
already proved polynomial regime applies, and otherwise `hHard` applies to the
minimal witness.  Both outcomes transfer back to the original witness by
`budgeted_plain_corner_mono_witness`.

Nothing here assumes the open regime; `hHard` is a faithful statement of what is
still missing. -/
theorem budgetedPlainCorner_of_hard_regime_superpoly_minimal
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ)
    (hHard : ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      alpha < kx →
      baseBudget ^ k < beta →
      baseBudget ^ k < x.length →
      (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
        beta < x.length ∧ kx + beta < x.length + m) →
      IsStochastic U x alpha beta →
      (∀ b : ℕ, b < beta → ¬ IsStochastic U x alpha b) →
      (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget) :
    BudgetedPlainProfileCornerStatement V U := by
  obtain ⟨cH, hH⟩ := hHard
  obtain ⟨cM, hM⟩ :=
    budgeted_stochasticity_to_plain_corner_of_witness_min_le_pow V U hV hU k
  refine budgetedPlainCorner_of_hard_regime_superpoly V U hV hU k ⟨max cM cH, ?_⟩
  intro x kx baseBudget alpha beta hkx hkxB hka hbeta hlen hnotsimple hstoch
  have hcM : logSlack cM baseBudget ≤ logSlack (max cM cH) baseBudget :=
    logSlack_mono_left (le_max_left _ _) baseBudget
  have hcH : logSlack cH baseBudget ≤ logSlack (max cM cH) baseBudget :=
    logSlack_mono_left (le_max_right _ _) baseBudget
  obtain ⟨a, b, hab, hbb, hstochab, hbmin, hamin⟩ :=
    exists_pareto_minimal_stochastic_witness U x alpha beta hstoch
  by_cases hpoly : b ≤ baseBudget ^ k
  · -- The minimal witness is already inside the proved polynomial regime.
    obtain ⟨i, j, hprof, hi, hij⟩ :=
      hM x kx baseBudget alpha beta a b hkx hkxB hab hbb
        ((min_le_left _ _).trans hpoly) hstochab
    exact ⟨i, j, hprof, by omega, by omega⟩
  · -- Otherwise the minimal witness still lies in the superpolynomial regime.
    push Not at hpoly
    have hnot' : ∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ a →
        b < x.length ∧ kx + b < x.length + m := by
      intro m hm hma
      obtain ⟨h1, h2⟩ := hnotsimple m hm (hma.trans hab)
      exact ⟨by omega, by omega⟩
    obtain ⟨i, j, hprof, hi, hij⟩ :=
      hH x kx baseBudget a b hkx hkxB (lt_of_le_of_lt hab hka) hpoly hlen hnot'
        hstochab hbmin hamin
    exact ⟨i, j, hprof, by omega, by omega⟩

/-- **The visible budget of the plain corner may be taken tight.**  The corner
statement is *equivalent* to its special case `baseBudget = C(x)`: the hypothesis
`kx ≤ baseBudget` is only used through the monotonicity of `logSlack` in its
argument, so a corner with the smaller slack `logSlack c kx` implies the corner
for every admissible budget, and conversely the general statement specializes at
`baseBudget := kx`.

This removes the budget variable from the alternative research direction altogether. -/
theorem budgetedPlainCorner_iff_tight_budget (V U : Map) :
    BudgetedPlainProfileCornerStatement V U ↔
      ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
        plainK V x = (kx : ENat) →
        IsStochastic U x alpha beta →
        ∃ i j,
          InPlainDescriptionProfile V x i j ∧
          i ≤ alpha + logSlack c kx ∧
          i + j ≤ kx + beta + logSlack c kx := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x kx alpha beta hkx hstoch => hc x kx kx alpha beta hkx le_rfl hstoch⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun x kx baseBudget alpha beta hkx hkxB hstoch => ?_⟩
    obtain ⟨i, j, hprof, hi, hij⟩ := hc x kx alpha beta hkx hstoch
    have hslack : logSlack c kx ≤ logSlack c baseBudget := logSlack_mono_right c hkxB
    exact ⟨i, j, hprof, by omega, by omega⟩

/-- **The tightest reduction of the budgeted plain corner obtained so far.**  The
full `BudgetedPlainProfileCornerStatement V U` follows from the corner in the
regime

```text
alpha < kx,   C(x) ^ k < beta,   C(x) ^ k < l(x),
```

with a non-simple length, a Pareto-minimal stochasticity witness, *and* with the
slack measured against `C(x)` itself rather than against an arbitrary admissible
budget.  So neither the budget variable nor any non-minimal witness remains in
the open part of the statement.

It combines `budgetedPlainCorner_iff_tight_budget` (budget elimination) with
`budgetedPlainCorner_of_hard_regime_superpoly_minimal` (superpolynomiality and
minimality). -/
theorem budgetedPlainCorner_of_hard_regime_superpoly_minimal_tight
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ)
    (hHard : ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      alpha < kx →
      kx ^ k < beta →
      kx ^ k < x.length →
      (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
        beta < x.length ∧ kx + beta < x.length + m) →
      IsStochastic U x alpha beta →
      (∀ b : ℕ, b < beta → ¬ IsStochastic U x alpha b) →
      (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c kx ∧
        i + j ≤ kx + beta + logSlack c kx) :
    BudgetedPlainProfileCornerStatement V U := by
  obtain ⟨c, hc⟩ := hHard
  refine budgetedPlainCorner_of_hard_regime_superpoly_minimal V U hV hU k ⟨c, ?_⟩
  intro x kx baseBudget alpha beta hkx hkxB hka hbeta hlen hnotsimple hstoch hbmin hamin
  have hpow : kx ^ k ≤ baseBudget ^ k := Nat.pow_le_pow_left hkxB k
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    hc x kx alpha beta hkx hka (lt_of_le_of_lt hpow hbeta) (lt_of_le_of_lt hpow hlen)
      hnotsimple hstoch hbmin hamin
  have hslack : logSlack c kx ≤ logSlack c baseBudget := logSlack_mono_right c hkxB
  exact ⟨i, j, hprof, by omega, by omega⟩

/-- Elementary `ℝ≥0∞` scale arithmetic: if `k ≤ q + b` then the weight `2⁻¹ ^ q`
is dominated by `2 ^ b * 2⁻¹ ^ k`. -/
theorem two_inv_pow_le_two_pow_mul_two_inv_pow {q k b : Nat} (hqk : k ≤ q + b) :
    (2 : ℝ≥0∞)⁻¹ ^ q ≤ (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ k := by
  have hstep : (2 : ℝ≥0∞)⁻¹ ^ (q + b) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    rw [← ENNReal.inv_pow, ← ENNReal.inv_pow]
    exact ENNReal.inv_le_inv.mpr (pow_two_mono hqk)
  have hone : (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ b = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
  have hcancel : (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ (q + b) = (2 : ℝ≥0∞)⁻¹ ^ q := by
    rw [pow_add, ← mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ b), mul_assoc, hone, mul_one]
  calc (2 : ℝ≥0∞)⁻¹ ^ q = (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ (q + b) := hcancel.symm
    _ ≤ (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞)⁻¹ ^ k := by gcongr

/-- **Two-sided scale bookkeeping for a tight level-set witness.**  If `P` gives
`z` mass at least `2⁻¹ ^ k`, and the deficiency of `z` under `P` is *not* bounded
by `beta - 1` (the diagnostic supplied by `deficiency_not_le_pred_of_beta_minimal`
at a deficiency-minimal coordinate), then the exact complexity level
`q = KP(z | P.code)` and `beta` together are bounded by the mass level `k`. -/
theorem levelSet_level_lower_of_beta_minimal
    {U : Map} {z : BitString} {P : CodedFiniteDistribution}
    {q k beta : Nat}
    (hKP : KP U z P.code = (q : ENat))
    (hmass : (2 : ℝ≥0∞)⁻¹ ^ k ≤ P.mass z)
    (hbeta : 0 < beta)
    (hnot : ¬ DeficiencyLe U P z (beta - 1)) :
    q + beta ≤ k + 1 := by
  by_contra hcon
  push Not at hcon
  apply hnot
  change complexityWeight (KP U z P.code) ≤ (2 : ℝ≥0∞) ^ (beta - 1) * P.mass z
  rw [hKP, complexityWeight_coe]
  refine le_trans
    (two_inv_pow_le_two_pow_mul_two_inv_pow (q := q) (k := k) (b := beta - 1) (by omega)) ?_
  gcongr

end Kolmogorov
