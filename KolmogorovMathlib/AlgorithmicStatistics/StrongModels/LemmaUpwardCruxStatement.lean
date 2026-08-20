import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerSharpProfile

/-!
# The Upward Crux Interface

This module isolates the exact $\alpha,\beta$-independent optimal-set conversion
required to complete the unconditional proof of `prop:upward` (the upward closure
of strong models). The public endpoint `prop_upward` is reduced to exactly this
hypothesis `hConv` (or the equivalent hard-regime corner).

By extracting it as a standalone `def`, we provide a stub-free research interface
for the remaining information-splitting efforts, analogous to S9's `LemmaOmpExactRadiusStatement`.
-/

namespace Kolmogorov

/-- **The Upward Crux Statement.**
The budget-scale plain corner in the hard regime depends on an $\alpha,\beta$-independent
optimal-set conversion. This is a research interface for the sharper, witness-uniform version
of upward transport. It is not the completion obligation for `prop_upward`, which is proved
unconditionally via the full-cube image in `UpwardOrdinalNoiseBetaRegime.lean`.

This interface requires a radius (for the optimality deficiency) that depends
*only* on the prefix complexity of `x` (i.e. `p`), rather than on `p + alpha + beta`
or `x.length`. -/
def LemmaUpwardCruxStatement (U : Map) : Prop :=
  ∃ c : ℕ, ∀ (x : BitString) (p alpha beta : ℕ),
    KPPlain U x = (p : ENat) →
    IsStochastic U x alpha beta →
    IsOptimalSetStochastic U x
      (alpha + logSlack c p) (beta + logSlack c p)

/-- **`prop:upward` from the budget-scale optimal-set conversion.**  Composing
`budgetedPlainCorner_of_optimalSetConversion_budget` with the corner-based
assembly `propUpward_of_budgetedPlainCorner`: the upward crux interface
`LemmaUpwardCruxStatement U` is enough to conclude `PropUpwardStatement U T`. -/
theorem propUpward_of_optimalSetConversion_budget
    (V U T : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hConv : LemmaUpwardCruxStatement U) :
    PropUpwardStatement U T :=
  propUpward_of_budgetedPlainCorner V U T hV hU hT
    (budgetedPlainCorner_of_optimalSetConversion_budget V U hV hU hConv)

end Kolmogorov
