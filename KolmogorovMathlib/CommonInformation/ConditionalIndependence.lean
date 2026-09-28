import KolmogorovMathlib.CommonInformation.ConditionalIndependence.Part01
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

/-!
# C7: Conditional independence and common information (SUV Theorem 228)

This file formalizes **SUV Theorem 228** (p. 362): for arbitrary strings
`x, y, z, u, v`,
```
C(z) ≤ 2·C(z|x) + 2·C(z|y) + I(x:y|u) + I(x:y|v) + I(u:v)
```
with `O(log C(x,y,u,z,v))` precision.

Following the chapter conventions we keep **plain** complexity throughout and
express every mutual-information term by its exact additive, subtraction-free
form:
```
I(x:y|u) = C(x|u) + C(y|u) − C(x,y|u),   I(u:v) = C(u) + C(v) − C(u,v).
```
Multiplying out and moving all subtracted terms to the left, Theorem 228 becomes
the fully subtraction-free inequality
```
C(z) + C(x,y|u) + C(x,y|v) + C(u,v)
    ≤ 2·C(z|x) + 2·C(z|y) + C(x|u) + C(y|u) + C(x|v) + C(y|v) + C(u) + C(v) + O(log).
```
This is `conditional_independence_nonextractability_bound`, stated in the chapter's
*values* form (`HasPlainComplexityValue` / `HasPlainConditionalComplexityValue`
witnesses, one uniform `logSlack C`).

## Proof architecture

SUV's proof is a purely arithmetical combination of one inequality applied to
three contexts.  The single ingredient is the complexity form of the Shannon
inequality of Problem 296 (p. 341), relativized to a context `w`:
```
C(z|w) ≤ C(z|a,w) + C(z|b,w) + I(a:b|w)          (subtraction-free:)
C(z|w) + C(a,b|w) ≤ C(z|a,w) + C(z|b,w) + C(a|w) + C(b|w) + O(log).
```
This is `base_conditional_mutualInformation_inequality`.  Its proof first
derives plain conditional symmetry of information, uniformly in `w`, from the
repository's conditional prefix-symmetry theorem.  It then proves the needed
submodularity inequality through conditional pair coding, computable pair
swaps, and projection of a coded triple.

`conditional_independence_nonextractability_bound` is then derived with a complete,
kernel-checked reduction:
* the base inequality at `(z, u, v, [])`, `(z, x, y, u)`, `(z, x, y, v)`;
* `condK_condPair_left_le` (condition monotonicity `C(z|a,w) ≤ C(z|a) + O(1)`,
  proved below), which turns the six relativized conditional complexities into
  the four appearing in the statement.

**Exercises 314–316** (the fixed-frequency stochastic construction) are *not*
formalized here: they additionally require the absent SUV Section 7
(Theorem 146) entropy↔complexity bridge, whose formalization is a separate,
human-gated decision (see `PLAN_COMMON_INFORMATION.md`, milestone C7).  They are
deliberately omitted rather than represented by fake statements.
-/
