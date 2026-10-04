import KolmogorovMathlib.InformationInequalities.Easy.Direction
import KolmogorovMathlib.InformationInequalities.Easy.Examples
import KolmogorovMathlib.InformationInequalities.Easy.OneTerm

/-!
# The easy direction, and the first combinatorial translations

SUV Section 10.1, pp. 313–318.

The chapter's headline question is which coefficient families `λ_I` satisfy
`∑_I λ_I C(x_I) ≤ O(log N)` for all tuples of strings of length at most `N`.  Section 10.1
settles the easy half of Romashchenko's answer: such an inequality for complexities forces the
inequality `∑_I λ_I H(ξ_I) ≤ 0` for entropies.  The argument takes `N` independent copies of
the column `⟨ξ_1, …, ξ_n⟩`, reads the resulting `n × N` matrix as a tuple of rows and applies
Theorem 147 of Chapter 7, which says that the expected complexity of the `I`-rows is
`N · H(ξ_I) + O(log N)`; dividing by `N` and letting `N → ∞` kills the error term.

The section then starts the combinatorial translation, in which `C(x_I)` becomes `log m_A(I)`
(the log-size of a projection) and `C(x_J | x_I)` becomes `log m_A(J | I)` (the log-size of a
maximal section).  Two examples are worked out — the set inequality
`|A|² ≤ m(1,2) m(1,3) m(2,3)` and Problem 283 — and two naive translations are shown to fail,
which is what motivates uniform sets in Section 10.2.

Sign convention: a form is the assertion `∑_I λ_I · (quantity of I) ≤ 0`, so a printed
`LHS ≤ RHS` is `LHS − RHS`; see `InformationInequalities/Basic.lean`.

The section is split by topic: the easy direction in `Easy/Direction.lean`, the set inequality
and the failing naive translations in `Easy/Examples.lean`, and Problem 283 in
`Easy/OneTerm.lean`.
-/
