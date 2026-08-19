import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseAlphaRegime
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.WidthChargedNoiseTransport

/-!
# The width-slack regime of the consumer-shaped ordinal noise transport

`UpwardOrdinalNoiseRegimes.lean` and `UpwardOrdinalNoiseAlphaRegime.lean` widen
the discharged region of the consumer transport along the deficiency axis (`beta`
below a fixed power of the model-code budget) and the complexity axis (`alpha`
above twice that budget).  `WidthChargedNoiseTransport.lean` supplies a third,
orthogonal discharge:
`strongModelOrdinalNoiseTransport_of_width_slack` proves the transport whenever
*some* stochasticity sub-witness `(a, b)` of the model code leaves enough
deficiency room to absorb the model width, i.e.
`b + finiteSetLogCard A + logSlack c n ≤ beta`.  (The width-charged pair
extension pays exactly `finiteSetLogCard A = log #A` of deficiency for coupling
the model code to its ordinal index, so this is the natural additive room the
transport needs.)

This module turns that conditional discharge into *unconditional dichotomies* by
feeding it the canonical Pareto-minimal witness
(`exists_pareto_minimal_stochastic_witness`):

* `strongModelOrdinalNoiseTransport_width_dichotomy` — for every stochasticity
  witness `(alpha, beta)` either the ordinal pair is already stochastic at the
  source-scale radius, or the Pareto-minimal witness `(a, b)` below it lies in the
  *near-Pareto width sliver* `beta < b + finiteSetLogCard A + logSlack c n`
  (the deficiency budget exceeds the minimal deficiency by less than the model
  width plus a logarithmic term).

* `strongModelOrdinalNoiseTransport_width_trichotomy` — combining the width
  discharge with `strongModelOrdinalNoiseTransport_trichotomy`, the residual of
  the whole consumer lane, for each fixed exponent `k`, is pinned to the
  *intersection* of all three previous residual descriptions: a Pareto-minimal
  witness `(a, b)` with

  - small complexity `alpha < 2 * (n + epsilon + logSlack cAlpha n)`,
  - super-polynomial deficiency `(n + epsilon + logSlack cBudget n) ^ k < b`, and
  - a near-Pareto width sliver `beta < b + finiteSetLogCard A + logSlack c n`.

  This is strictly smaller than the residual of either previous dichotomy, so it
  is a genuine narrowing of the open crux.

Nothing here assumes an open statement: both theorems are proved by case analysis
over already-proved branches, and the residual disjunct only *describes* the
remaining case — it makes no claim of transport there.  Establishing transport in
that residual sliver remains the genuine open crux documented in
`PropUpwardFrontier.lean`.
-/

namespace Kolmogorov

/-- **The width-slack transport dichotomy.**  For every stochasticity witness
`(alpha, beta)` of the canonical model code, either the ordinal pair
`strongModelOrdinalBitsPair A hA x` is already stochastic at the source-scale
radius `c * epsilon + logSlack c n`, or the Pareto-minimal witness `(a, b)` below
`(alpha, beta)` leaves too little deficiency room to absorb the model width:
`beta < b + finiteSetLogCard A + logSlack c n`.

Transport in the discharged branch comes from
`strongModelOrdinalNoiseTransport_of_width_slack`; the residual branch is the
negation of its width-slack hypothesis at the Pareto-minimal witness.  The
theorem is unconditional and kernel-checked; its second branch *describes* the
residual case and asserts no transport there. -/
theorem strongModelOrdinalNoiseTransport_width_dichotomy
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      IsStochastic U (codedUniformOn A hA).code alpha beta →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
          (alpha + (c * epsilon + logSlack c n))
          (beta + (c * epsilon + logSlack c n)) ∨
        (∃ a b : ℕ, a ≤ alpha ∧ b ≤ beta ∧
          IsStochastic U (codedUniformOn A hA).code a b ∧
          beta < b + finiteSetLogCard A + logSlack c n ∧
          (∀ b' : ℕ, b' < b → ¬ IsStochastic U (codedUniformOn A hA).code a b') ∧
          (∀ a' : ℕ, a' < a → ¬ IsStochastic U (codedUniformOn A hA).code a' b)) := by
  obtain ⟨c, hwidth⟩ :=
    strongModelOrdinalNoiseTransport_of_width_slack V U T hV hU hT
  refine ⟨c, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  obtain ⟨a, b, hab, hbb, hstochab, hbmin, hamin⟩ :=
    exists_pareto_minimal_stochastic_witness U (codedUniformOn A hA).code alpha beta hstoch
  by_cases hws : b + finiteSetLogCard A + logSlack c n ≤ beta
  · refine Or.inl ?_
    exact hwidth x A hA n epsilon alpha beta hxn hx hstrong hdef
      ⟨a, b, hab, hbb, hstochab, hws⟩
  · exact Or.inr ⟨a, b, hab, hbb, hstochab, not_le.mp hws, hbmin, hamin⟩

/-- **The width-refined transport trichotomy.**  For each fixed exponent `k`,
every stochasticity witness `(alpha, beta)` of the canonical model code either
already gives the ordinal pair at the source-scale radius, or is confined to the
intersection of the three previously-isolated residual regions: a Pareto-minimal
witness `(a, b)` with small complexity `alpha < 2 * (n + epsilon + logSlack cAlpha
n)`, super-polynomial deficiency `(n + epsilon + logSlack cBudget n) ^ k < b`, and
a near-Pareto width sliver `beta < b + finiteSetLogCard A + logSlack c n`.

This sharpens `strongModelOrdinalNoiseTransport_trichotomy` by the extra
width-sliver constraint coming from
`strongModelOrdinalNoiseTransport_of_width_slack`: whenever the Pareto-minimal
witness leaves enough deficiency room to absorb the model width, transport is
provided instead.  The theorem is unconditional and kernel-checked; its second
branch only *describes* the residual case, and establishing transport there
remains an alternative research direction (see `PropUpwardFrontier.lean`). -/
theorem strongModelOrdinalNoiseTransport_width_trichotomy
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
            beta < b + finiteSetLogCard A + logSlack c n ∧
            (∀ b' : ℕ, b' < b → ¬ IsStochastic U (codedUniformOn A hA).code a b') ∧
            (∀ a' : ℕ, a' < a → ¬ IsStochastic U (codedUniformOn A hA).code a' b)) := by
  obtain ⟨cBudget, cAlpha, cTri, htri⟩ :=
    strongModelOrdinalNoiseTransport_trichotomy V U T hV hU hT k
  obtain ⟨cW, hwidth⟩ :=
    strongModelOrdinalNoiseTransport_of_width_slack V U T hV hU hT
  refine ⟨cBudget, cAlpha, cTri + cW, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  rcases htri x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch with htrans | hres
  · exact Or.inl (isStochastic_radius_mono (Nat.le_add_right _ _) epsilon n htrans)
  · obtain ⟨halpha_small, a, b, hab, hbb, hstochab, hbpow, hbmin, hamin⟩ := hres
    by_cases hws : b + finiteSetLogCard A + logSlack cW n ≤ beta
    · refine Or.inl ?_
      have h : IsStochastic U (strongModelOrdinalBitsPair A hA x)
          (alpha + (cW * epsilon + logSlack cW n))
          (beta + (cW * epsilon + logSlack cW n)) :=
        hwidth x A hA n epsilon alpha beta hxn hx hstrong hdef
          ⟨a, b, hab, hbb, hstochab, hws⟩
      exact isStochastic_radius_mono (Nat.le_add_left _ _) epsilon n h
    · refine Or.inr ⟨halpha_small, a, b, hab, hbb, hstochab, hbpow, ?_, hbmin, hamin⟩
      have hlt : beta < b + finiteSetLogCard A + logSlack cW n := not_le.mp hws
      have hmono : logSlack cW n ≤ logSlack (cTri + cW) n :=
        logSlack_mono_left (Nat.le_add_left _ _) n
      omega

end Kolmogorov
