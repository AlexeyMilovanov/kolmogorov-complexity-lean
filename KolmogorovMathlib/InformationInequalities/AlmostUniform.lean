import KolmogorovMathlib.InformationInequalities.AlmostUniform.Basic
import KolmogorovMathlib.InformationInequalities.AlmostUniform.Entropy

/-!
# Almost uniform sets

SUV Section 10.5, pp. 324–325.

A set `A ⊆ X_1 × ⋯ × X_n` is `c`-uniform when, for every ordering of the coordinates, the
right-hand side of the chain inequality
`m(k_1, …, k_n) ≤ m(k_1) · m(k_2 | k_1) ⋯ m(k_n | k_1, …, k_{n-1})`
exceeds the left-hand side `|A|` by a factor at most `c` (`IsCUniform`).  Theorem 210 lists the
properties of uniform sets that survive, up to a factor `c`, for `c`-uniform sets: the
two-step section inequality is tight up to `c`, projections stay `c`-uniform, a subset
holding an `ε`-fraction is `c/ε`-uniform, and the entropies of a uniformly random point are
within `log c` of the log-sizes of the corresponding projections and sections.  The unnumbered
corollary after the proof transfers entropy inequalities to `c`-uniform sets with error
`λ log c`.

Parts (d) and (e) mention entropies, so there the coordinate sets are one finite type `α`
(see the module docstring of `UniformSetsTheorems` for why this is no loss).  Logarithms and
entropies are base two.

The section is split by topic: Theorem 210(a)–(c) in `AlmostUniform/Basic.lean` and the
entropy statements, Theorem 210(d)–(e) and the corollary, in `AlmostUniform/Entropy.lean`.
-/
