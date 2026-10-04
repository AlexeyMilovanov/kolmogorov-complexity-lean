import KolmogorovMathlib.InformationInequalities.Typization.Candidate
import KolmogorovMathlib.InformationInequalities.Typization.Romashchenko
import KolmogorovMathlib.InformationInequalities.Typization.Uniform

/-!
# The typization trick and Romashchenko's theorem

SUV Section 10.6, pp. 326–328.

Theorem 211 starts from an arbitrary tuple of strings `x_1, …, x_n` of complexity at most `N`
and produces an almost uniform set whose projection and section sizes reproduce the
complexities of the tuple: `log m(J | I) = C(x_J | x_I) + O(log N)`.  The set is
`A(x) = {y : κ(y) ≤ κ(x) componentwise}`, where `κ(x)` is the complexity vector of all
conditional complexities `C(x_I | x_J)` of disjoint subtuples — the set of tuples in which `x`
is typical.  It contains `x`, has about `2^{C(x)}` elements because it is enumerable from
`κ(x)` (`O(log N)` bits), and its sections are bounded by `2^{C(x_J | x_I) + 1}`; the chain
rule then makes it `N^d`-uniform.

Theorem 212 finishes Romashchenko's equivalence: an entropy inequality holds for complexities
with `O(log N)` precision.  Together with the easy direction of Section 10.1 this is the
chapter's first headline — linear inequalities for Kolmogorov complexities and for Shannon
entropies are the same.

Precision conventions.  Both theorems are about strings of **complexity** at most `N`, not of
length at most `N`: that is the form of Section 10.6 (and of Theorems 213–214), and it is the
form of `HoldsForComplexitiesCplx`.  All complexities are plain, with respect to an optimal
decompressor `D`.  The printed conclusion of Theorem 212 is `∑_I λ_I K(ξ_I) ≤ O(log N)`,
which mixes the notation for random variables and for prefix complexity; what is meant, and
what is stated here, is the plain complexity `C(x_I)` of the string tuples (plain and prefix
complexity agree up to `O(log N)` for such strings).

The section is split by topic: the typization candidate `A(x)` in `Typization/Candidate.lean`,
its almost uniformity (Theorem 211) in `Typization/Uniform.lean`, and Romashchenko's theorem
(Theorem 212) in `Typization/Romashchenko.lean`.
-/
