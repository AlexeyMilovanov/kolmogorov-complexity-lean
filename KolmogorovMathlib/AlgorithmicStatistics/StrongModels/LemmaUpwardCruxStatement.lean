import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerProfile

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

open CodedFiniteDistribution
/-- The upward crux, as a proposition about `U`: there is a constant `c` such that every
`(alpha, beta)`-stochastic `x` with `KPPlain U x = p` is
`(alpha + logSlack c p, beta + logSlack c p)`-optimal-set stochastic.  The radius depends on the
prefix complexity `p` alone, not on `alpha`, `beta` or `x.length`.  It is used as a hypothesis;
it is not proved here. -/
def LemmaUpwardCruxStatement (U : Map) : Prop :=
  ∃ c : ℕ, ∀ (x : BitString) (p alpha beta : ℕ),
    KPPlain U x = (p : ENat) →
    IsStochastic U x alpha beta →
    IsOptimalSetStochastic U x
      (alpha + logSlack c p) (beta + logSlack c p)

/-- The upward crux implies `PropUpwardStatement U T`. -/
theorem propUpward_of_optimalSetConversion_budget
    (V U T : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T)
    (hConv : LemmaUpwardCruxStatement U) :
    PropUpwardStatement U T :=
  propUpward_of_budgetedPlainCorner V U T hV hU hT
    (budgetedPlainCorner_of_optimalSetConversion_budget V U hV hU hConv)

end Kolmogorov
