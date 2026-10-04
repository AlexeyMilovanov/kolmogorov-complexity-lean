import KolmogorovMathlib.Entropy.Inequalities.Basic
import KolmogorovMathlib.Entropy.Inequalities.Independence
import KolmogorovMathlib.Entropy.Inequalities.Fano
import KolmogorovMathlib.Entropy.Inequalities.Subtuples

/-!
# Entropy inequalities for pairs, tuples and conditions

SUV Sections 7.2.1–7.2.4, pp. 218–225.

This module states the inequalities of Section 7.2: subadditivity of entropy (Theorem 141), the
four properties of conditional entropy (Theorem 142), monotonicity under a function
(Theorem 143), the entropy criterion for independence (Theorem 144) and the basic inequality
`I(ξ:η|α) ≥ 0` (Theorem 145), together with the problems of the section — the chain rule and the
data-processing inequality for mutual information, a negative `I(α:β:γ)`, Fano's inequality,
Shannon's theorem on perfect cryptosystems, the `n`-variable inequality of Problem 231, the
Shearer inequality and the discrete Loomis–Whitney inequality.

Entropies are base two.  `condEntropy`, `mutualInfo`, `condMutualInfo` and `tripleInfo` are the
definitions of `KolmogorovMathlib.Entropy.Conditional`, which are the book's; in particular
`H(ξ|η) = H(ξ,η) − H(η)` is Theorem 142(d) below and not a definition.  The entropy of a tuple of
`n` random variables and of its subtuples is `entropySub`, so that Problems 231–232 are stated in
the vocabulary that Chapter 10 uses.

The section is split by topic: `Entropy/Inequalities/Basic.lean` (Theorems 141–143 and the
four-point examples), `Entropy/Inequalities/Independence.lean` (Theorems 144–145),
`Entropy/Inequalities/Fano.lean` (mutual information, Fano's inequality, perfect secrecy) and
`Entropy/Inequalities/Subtuples.lean` (three and `n` variables, Shearer, Loomis–Whitney).
-/
