/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.InformationInequalities.Basic

/-!
# Ingleton's inequality and the non-Shannon inequality

SUV Sections 10.11 and 10.13, p. 339 and p. 344.

Two concrete linear forms, both in the sign convention of this directory
(`∑_I λ_I · (quantity of I) ≤ 0`, so a printed `LHS ≤ RHS` becomes `LHS − RHS`).  The
variables `ξ_1, …, ξ_n` of the book are the indices `0, …, n-1` of `Fin n` here.

Both are written as coefficient tables (`LinearForm.ofTable`), so that a reader can compare
them with the page line by line.  A coefficient at a concrete set is computed with
`simp +decide [ingletonForm, LinearForm.ofTable]` — the `+decide` settles the equalities
between the explicit `Finset`s of the table — and likewise for `nonShannonForm`.

**Ingleton's inequality** (Theorem 215, p. 339), printed in terms of mutual information as
`I(ξ₃:ξ₄) ≤ I(ξ₃:ξ₄|ξ₁) + I(ξ₃:ξ₄|ξ₂) + I(ξ₁:ξ₂)` and, in terms of unconditional entropies,
as `12 + 3 + 4 + 134 + 234 ≤ 13 + 23 + 14 + 24 + 34` (the book writes only the indices, so
`134` is `H(ξ₁, ξ₃, ξ₄)`).  It is *not* true for entropies of random variables — that is
Theorem 217 — and it is true for dimensions of subspaces.

**The non-Shannon inequality** (Theorem 218, p. 344; Makarychev, Makarychev, Romashchenko and
Vereshchagin): for every quintuple `α, β, γ, δ, ε` of random variables,
`I(α:β) ≤ I(α:β|γ) + I(α:β|δ) + I(γ:δ) + I(α:β|ε) + I(α:ε|β) + I(β:ε|α)`.
Expanding the mutual informations into entropies of subtuples of `(α, β, γ, δ, ε)` — here
`α, β, γ, δ, ε` are the indices `0, 1, 2, 3, 4` — and collecting terms gives
`2·H(α) + 2·H(β) + H(ε) − 3·H(αβ) − H(αγ) − H(βγ) − H(αδ) − H(βδ) + H(γδ)`
`− 2·H(αε) − 2·H(βε) + H(αβγ) + H(αβδ) + 3·H(αβε) ≤ 0`, which is the table below.  The
inequality is not a consequence of the basic inequalities, which is the point of the section.
-/

namespace Kolmogorov

/-- Ingleton's inequality as a linear form in four variables:
`H(ξ₁ξ₂) + H(ξ₃) + H(ξ₄) + H(ξ₁ξ₃ξ₄) + H(ξ₂ξ₃ξ₄)`
`− H(ξ₁ξ₃) − H(ξ₂ξ₃) − H(ξ₁ξ₄) − H(ξ₂ξ₄) − H(ξ₃ξ₄) ≤ 0`.
The book's `ξ_i` is the index `i - 1` of `Fin 4`.  SUV Theorem 215, p. 339. -/
def ingletonForm : LinearForm 4 :=
  LinearForm.ofTable
    [({0, 1}, 1), ({2}, 1), ({3}, 1), ({0, 2, 3}, 1), ({1, 2, 3}, 1),
      ({0, 2}, -1), ({1, 2}, -1), ({0, 3}, -1), ({1, 3}, -1), ({2, 3}, -1)]

/-- The non-Shannon inequality of Theorem 218 as a linear form in five variables, obtained by
expanding `I(α:β) ≤ I(α:β|γ) + I(α:β|δ) + I(γ:δ) + I(α:β|ε) + I(α:ε|β) + I(β:ε|α)` into
entropies of subtuples.  The variables `α, β, γ, δ, ε` are the indices `0, 1, 2, 3, 4` of
`Fin 5`.  SUV Theorem 218, p. 344. -/
def nonShannonForm : LinearForm 5 :=
  LinearForm.ofTable
    [({0}, 2), ({1}, 2), ({4}, 1),
      ({0, 1}, -3), ({0, 2}, -1), ({1, 2}, -1), ({0, 3}, -1), ({1, 3}, -1),
      ({2, 3}, 1), ({0, 4}, -2), ({1, 4}, -2),
      ({0, 1, 2}, 1), ({0, 1, 3}, 1), ({0, 1, 4}, 3)]

end Kolmogorov
