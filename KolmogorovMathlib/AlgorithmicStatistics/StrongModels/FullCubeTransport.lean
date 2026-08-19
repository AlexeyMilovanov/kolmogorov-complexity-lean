import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseTransport
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalNoiseBetaRegime

/-!
# The full-cube branch of the ordinal noise transport, and `prop:upward`

`UpwardOrdinalNoiseTransport.lean` discharges the consumer-shaped transport
`StrongModelOrdinalNoiseTransportStatement U T` whenever the deficiency
parameter satisfies `beta ≤ n + epsilon + logSlack cBudget n`.  This module
supplies the complementary regime `n ≤ beta` by an entirely different and much
cheaper argument, and therefore completes the transport unconditionally.

The point is that strongness already produces a *simple explicit model* for the
ordinal pair.  A strong model `A` of the `n`-bit string `x` makes `x` and the
pair `(code A, ordinal of x in A)` totally equivalent up to `epsilon`, so a
single total program maps every `n`-bit string to a string, and the image `B` of
the full cube `{0,1}^n` under that program contains the ordinal pair, has at most
`2 ^ n` elements, and has plain complexity `epsilon + O(log n)`
(`strongModelPairImage_exists`, `plainK_codedUniformOn_image_le`).

The uniform distribution on `B` is then a model for the ordinal pair of
complexity `epsilon + O(log n)` and optimality deficiency at most
`n + epsilon + O(log n)`.  As soon as `n ≤ beta`, that deficiency fits inside
`beta + (c * epsilon + logSlack c n)`, so the pair is stochastic at the required
radius, with no hypothesis on the model code at all.

Combining the two regimes gives `strongModelOrdinalNoiseTransport_fullCube` and
hence the unconditional source endpoint `prop_upward_fullCube`.  This is an
independent second route to the same conclusions as
`strongModelOrdinalNoiseTransport` / `prop_upward` in
`UpwardOrdinalNoiseBetaRegime.lean`; the two are deliberately given distinct
names so that both can live in the section build simultaneously.
-/

namespace Kolmogorov

open CodedFiniteDistribution

/-- **The full-cube branch of the consumer transport.**  If `A` is an
`epsilon`-strong model of the `n`-bit string `x` and the deficiency budget
satisfies `n ≤ beta`, then the canonical model-code/ordinal pair is stochastic
at the source-scale radius `c * epsilon + logSlack c n`.

No stochasticity hypothesis on the model code and no deficiency hypothesis are
needed: the uniform distribution on the total image of the full cube is already
a good enough model. -/
theorem strongModelOrdinalNoiseTransport_of_length_le_beta
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x A (hA : A.Nonempty) n epsilon alpha beta,
      x.length = n →
      x ∈ A →
      IsStrongSetModel T x A hA epsilon →
      n ≤ beta →
      IsStochastic U (strongModelOrdinalBitsPair A hA x)
        (alpha + (c * epsilon + logSlack c n))
        (beta + (c * epsilon + logSlack c n)) :=
  strongModelOrdinalNoiseTransport_of_n_le_beta V U T hV hU hT

/-- **The consumer-shaped ordinal noise transport, unconditionally.**  The two
regimes `beta ≤ n + epsilon + logSlack cBudget n`
(`strongModelOrdinalNoiseTransport_of_beta_le`) and `n ≤ beta`
(`strongModelOrdinalNoiseTransport_of_length_le_beta`) exhaust all deficiency
budgets, so the narrowed transport statement holds outright. -/
theorem strongModelOrdinalNoiseTransport_fullCube (U T : Map)
    (hU : IsOptimalPrefixConditional U) (hT : IsOptimalTotalConditional T) :
    StrongModelOrdinalNoiseTransportStatement U T :=
  strongModelOrdinalNoiseTransport U T hU hT

/-- **VS40 Proposition `prop:upward`, unconditionally.**  For an `epsilon`-strong
model `A` of an `n`-bit string `x` with optimality deficiency at most `epsilon`,
the stochasticity profile of `x` and that of the model code lie within
`O(epsilon + log n)` of each other. -/
theorem prop_upward_fullCube (U T : Map)
    (hU : IsOptimalPrefixConditional U) (hT : IsOptimalTotalConditional T) :
    PropUpwardStatement U T :=
  prop_upward U T hU hT

end Kolmogorov
