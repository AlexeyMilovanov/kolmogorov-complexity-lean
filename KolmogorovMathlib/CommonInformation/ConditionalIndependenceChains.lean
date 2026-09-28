import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains.ChainDist
import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains.Extension
import KolmogorovMathlib.CommonInformation.ConditionalIndependenceChains.Existence
import KolmogorovMathlib.CommonInformation.FiniteQuadruple
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation

/-!
# Conditional independence chains (SUV Exercise 315)

SUV Exercise 315 (p. 364) extends the conditionally-independent-but-dependent
Boolean pair of Theorem 217 / Exercise 314 (`FiniteQuadruple.lean`) to an
arbitrary agreement probability `c ∈ (0, 1)`.  The source asks for **finite
chains** of Boolean random variables `α₀, α₁, …, α_k` and `β₀, β₁, …, β_k` on a
common probability space such that

* `α₀` and `β₀` are uniformly distributed in `{0,1}`;
* `Pr[α₀ = β₀] = c`;
* `αᵢ` and `βᵢ` are independent given `α_{i+1}`  (for `0 ≤ i < k`);
* `αᵢ` and `βᵢ` are independent given `β_{i+1}`  (for `0 ≤ i < k`);
* `α_k` and `β_k` are independent.

## Encoding

A joint law of the `2k+2` Boolean variables is a nonnegative weight function on
`Fin (2k+2) → Bool` of total mass `1` (`Kolmogorov.ChainDist`).  Coordinate `i`
(`0 ≤ i ≤ k`) is `αᵢ`; coordinate `k+1+i` is `βᵢ`
(`Kolmogorov.chainAlphaIdx`, `Kolmogorov.chainBetaIdx`).  Conditional
independence is stated in the **division-free** product form
`Pr[X=x, Y=y, Z=z] · Pr[Z=z] = Pr[X=x, Z=z] · Pr[Y=y, Z=z]`, which is correct
even on null conditioning fibers, matching `QuadDist.CondIndepGivenGamma`.

## Main results

* `Kolmogorov.ChainDist.IsIndep315Chain` — the full chain of conditional
  independence relations of the source, quantified over `i : Fin k` with the
  `Fin.castSucc`/`Fin.succ`/`Fin.last` indexing.
* `Kolmogorov.base_chain` — **fully proved**: for `c ∈ [3/8, 5/8]` a length-`1`
  chain exists.  This is precisely the Exercise-314 quadruple `(α, β, γ, δ)`
  reread as `(α₀, β₀, α₁, β₁)`: `CondIndepGivenGamma` becomes
  `α₀ ⫫ β₀ | α₁`, `CondIndepGivenDelta` becomes `α₀ ⫫ β₀ | β₁`, and
  `GammaDeltaIndep` becomes the top relation `α₁ ⫫ β₁`.
* `Kolmogorov.exists_indepChain` — the honest full
  statement for every `c ∈ (0, 1)`.  The base range `[3/8, 5/8]` is discharged
  by `base_chain`, and the range below `3/8` by the proved `α₀`-inversion
  construction.  The high range is obtained from the explicit distribution
  extension `extend_independence_chain` and the proved iteration-surjectivity
  theorem `iterate_reaches`.
-/
