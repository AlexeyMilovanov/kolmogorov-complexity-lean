import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalTransport
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardOrdinalBetaRegime

/-!
# The full-cube branch of the ordinal noise transport, and `prop:upward`

`UpwardOrdinalTransport.lean` discharges the consumer-shaped transport
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

Combining the two regimes gives `strongModel_ordinal_noise_transport` and
hence the unconditional source endpoint `prop_upward`.  This is an
independent second route to the same conclusions as
`strongModel_ordinal_noise_transport` / `prop_upward` in
`UpwardOrdinalBetaRegime.lean`; the two are deliberately given distinct
names so that both can live in the section build simultaneously.
-/

namespace Kolmogorov

open CodedFiniteDistribution

end Kolmogorov
