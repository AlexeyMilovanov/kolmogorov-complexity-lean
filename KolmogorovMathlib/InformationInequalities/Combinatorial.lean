/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.Combinatorial.Examples
import KolmogorovMathlib.InformationInequalities.Combinatorial.Cover
import KolmogorovMathlib.InformationInequalities.Combinatorial.UnionDecomposition

/-!
# Combinatorial interpretations of information inequalities

SUV Sections 10.7–10.9, pp. 328–336.

The statement "`x` has complexity at most `k`" is translated as "`x` belongs to a set of at
most `2^k` elements", and every inequality between complexities is rewritten in terms of this
relation.  Small complexities are the ones we can enumerate, so an inequality
`C(z) ≥ C(x) + C(y)` becomes the dual statement "if `C(z) < u + v` then `C(x) < u` or
`C(y) < v`", and its translation is a statement about **covers**.

* Section 10.7 works two examples: the pair formula `C(x, y) ≥ C(x) + C(y | x)` (Problem 288)
  and the basic inequality, whose translation is a cover of `A` by two sets, one with a short
  first projection and one of small volume.
* Section 10.8 (Theorem 213) proves the general equivalence between an inequality
  `∑ λ_I C(x_I) ≤ ∑ μ_J C(x_J) + O(log N)` with positive coefficients and a cover statement
  with polylogarithmic slack.  Problem 290 asks for the version with conditional terms and
  leaves its formulation to the reader; it is archived, with the formulation that was chosen,
  in `docs/ARCHIVED_TARGETS.md`.
* Section 10.9 (Theorem 214) gives a second interpretation that treats all coefficients alike:
  `A` is a union of polylogarithmically many parts, each satisfying the product inequality up
  to a polylogarithmic factor.  It rests on the decomposition lemma: every set is a union of
  polylogarithmically many almost uniform parts.

Polylogarithmic factors.  The book writes `(log |A|)^d`, which is at most `1` for `|A| ≤ 2`
and makes the statements degenerate for tiny sets; here the factor is `(2 + log₂ |A|)^d`,
which agrees with the book's up to a change of `d` as soon as `|A| ≥ 4`.  This is a **repair
of the degenerate small-alphabet case**, not a strengthening or a weakening: for `|A| ≥ 4`,
with `L = log₂ |A| ≥ 2`, one has `L^d ≤ (2 + L)^d ≤ L^(2d)`, so the two families of statements
(over all `d`) coincide.  Complexities are plain and bounded by `N` (complexity, not length,
as in Sections 10.8–10.9).

The development is split by section: `Combinatorial.Examples` (Section 10.7),
`Combinatorial.Cover` (Section 10.8, Theorem 213), `Combinatorial.Partition` (the decomposition
lemmas of Section 10.9), `Combinatorial.UnionDecomposition` (Theorem 214), and
`Combinatorial.TypizationBounds` (size estimates shared by Theorems 213 and 214).
-/
