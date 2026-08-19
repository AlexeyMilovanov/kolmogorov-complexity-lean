import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseTransportPow
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerMinimalWitness

/-!
# Pareto reduction of the consumer-shaped ordinal noise transport

`UpwardOrdinalNoiseTransportPow.lean` discharges the consumer instance
`StrongModelOrdinalNoiseTransportStatement`-shaped transport unconditionally
whenever the deficiency parameter satisfies `beta ≤ baseBudget ^ k`
(`strongModelOrdinalNoiseTransport_of_beta_le_pow`, with
`baseBudget = n + epsilon + logSlack cBudget n`).

This module widens the discharged region along the *witness* axis, using the
Pareto-minimal reduction `exists_pareto_minimal_stochastic_witness`
(`BudgetedCornerMinimalWitness.lean`) together with the joint monotonicity of
`IsStochastic` (`isStochastic_mono`) and the fact that the transport radius
`c * epsilon + logSlack c n` does **not** depend on `(alpha, beta)`.

Two unconditional facts result:

* `strongModelOrdinalNoiseTransport_of_witness_beta_le_pow` — transport holds for
  a given witness `(alpha, beta)` as soon as *some* stochasticity witness
  `(a, b)` below it has polynomially bounded deficiency `b ≤ baseBudget ^ k`.
  Since the radius is witness-independent, the polynomial-regime transport for
  `(a, b)` transfers upward to `(alpha, beta)`.
* `strongModelOrdinalNoiseTransport_dichotomy` — for every stochasticity witness
  either transport already holds, or the Pareto-minimal witness below it has a
  deficiency above the chosen fixed-power bound `baseBudget ^ k < b`.  This pins
  the residual of this consumer lane, for each fixed `k`, to a Pareto-minimal
  model-code witness above that power bound.

Nothing here assumes an open statement.  The dichotomy is a proved theorem whose
second branch is a precise *description* of the residual case, not a claim of
transport in it.  Both theorems are kernel-checked with no open leaf (their only
foundational dependencies are `propext`, `Classical.choice`, `Quot.sound`), and
neither manufactures an unconditional `prop_upward`; the truth of transport in
the residual above-fixed-power branch remains the genuine alternative research direction
documented in `PropUpwardFrontier.lean`.
-/

namespace Kolmogorov

/-- **Consumer ordinal transport whenever some sub-witness has polynomial
deficiency.**  If `(a, b)` is a stochasticity witness for the model code with
`a ≤ alpha`, `b ≤ beta`, and `b ≤ baseBudget ^ k`, then the ordinal pair
`strongModelOrdinalBitsPair A hA x` is stochastic at the source-scale radius
`c * epsilon + logSlack c n` for the *original* witness `(alpha, beta)`.

The radius is independent of the witness, so the polynomial-regime transport for
`(a, b)` (`strongModelOrdinalNoiseTransport_of_beta_le_pow`) transfers upward to
`(alpha, beta)` by `isStochastic_mono`. -/
theorem strongModelOrdinalNoiseTransport_of_witness_beta_le_pow
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (k : ℕ) :
    ∃ cBudget c : ℕ, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      IsStochastic U (codedUniformOn A hA).code alpha beta →
      (∃ a b : ℕ, a ≤ alpha ∧ b ≤ beta ∧
        IsStochastic U (codedUniformOn A hA).code a b ∧
        b ≤ (n + epsilon + logSlack cBudget n) ^ k) →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
        (alpha + (c * epsilon + logSlack c n))
        (beta + (c * epsilon + logSlack c n)) := by
  obtain ⟨cBudget, c, hpow⟩ :=
    strongModelOrdinalNoiseTransport_of_beta_le_pow V U T hV hU hT k
  refine ⟨cBudget, c, ?_⟩
  rintro x A hA n epsilon alpha beta hxn hx hstrong hdef _hstoch
    ⟨a, b, hab, hbb, hstochab, hbpow⟩
  have hforward :=
    hpow x A hA n epsilon a b hxn hx hstrong hdef hbpow hstochab
  exact isStochastic_mono
    (Nat.add_le_add_right hab (c * epsilon + logSlack c n))
    (Nat.add_le_add_right hbb (c * epsilon + logSlack c n)) hforward

/-- **The consumer ordinal transport dichotomy.**  For every stochasticity
witness `(alpha, beta)` of the canonical model code, either the ordinal pair is
already stochastic at the source-scale radius `c * epsilon + logSlack c n`, or the
Pareto-minimal witness `(a, b)` below `(alpha, beta)` has deficiency above the
chosen fixed-power bound `baseBudget ^ k < b`.

For each fixed `k`, this is the exact residual after witnesses bounded by the
`k`-th power are discharged: the only case in which this consumer-lane theorem
does not already provide transport is a Pareto-minimal witness above that power
bound.  The theorem is unconditional and kernel-checked; its second branch
*describes* the residual case — it does not assert transport there.  Establishing
transport in that residual branch is the genuine alternative research direction (see
`PropUpwardFrontier.lean`). -/
theorem strongModelOrdinalNoiseTransport_dichotomy
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (k : ℕ) :
    ∃ cBudget c : ℕ, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
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
          (n + epsilon + logSlack cBudget n) ^ k < b ∧
          (∀ b' : ℕ, b' < b → ¬ IsStochastic U (codedUniformOn A hA).code a b') ∧
          (∀ a' : ℕ, a' < a → ¬ IsStochastic U (codedUniformOn A hA).code a' b)) := by
  obtain ⟨cBudget, c, hwitness⟩ :=
    strongModelOrdinalNoiseTransport_of_witness_beta_le_pow V U T hV hU hT k
  refine ⟨cBudget, c, ?_⟩
  intro x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
  obtain ⟨a, b, hab, hbb, hstochab, hbmin, hamin⟩ :=
    exists_pareto_minimal_stochastic_witness U (codedUniformOn A hA).code alpha beta hstoch
  by_cases hpoly : b ≤ (n + epsilon + logSlack cBudget n) ^ k
  · exact Or.inl
      (hwitness x A hA n epsilon alpha beta hxn hx hstrong hdef hstoch
        ⟨a, b, hab, hbb, hstochab, hpoly⟩)
  · exact Or.inr ⟨a, b, hab, hbb, hstochab, not_le.mp hpoly, hbmin, hamin⟩

end Kolmogorov
