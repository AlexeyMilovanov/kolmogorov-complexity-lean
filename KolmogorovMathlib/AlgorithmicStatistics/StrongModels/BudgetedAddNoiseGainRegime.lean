import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedAddNoiseIntrinsicSize

/-!
# Gain regime of the budgeted conditional compression

`BudgetedAddNoisePolySize.lean` and `BudgetedAddNoiseIntrinsicSize.lean`
discharge the budget-scale conditional compression
`BudgetedConditionalCompressionStatement` along the *size* axis:
`budgetedConditionalCompression_of_card_le_pow` proves it whenever the model
satisfies `|H| ≤ 2 ^ budget ^ k` for a fixed exponent `k`.

This file adds the orthogonal *gain* axis.  The compression conclusion asks for
a model of `x` whose complexity is at most `iH - g + logSlack c budget`, where
`g = C([H] | x)` is the compression gain.  If that gain is itself only
logarithmic in the budget, then no compression has to be performed at all: the
given model `H` already satisfies the conclusion, because the budget-scale
slack pays for the whole claimed drop.  This is
`inPlainDescriptionProfile_of_small_condK_gain`, a slack-free leaf that needs
neither optimality of the machines nor the exact value of `g`.

Combining the two axes gives
`budgetedConditionalCompression_of_card_le_pow_or_small_gain`: for every fixed
exponent `k` and every fixed margin `w`, the body of
`BudgetedConditionalCompressionStatement` holds for every model that is either
polynomially small in the budget or carries at most `logSlack w budget` bits of
information about `x`.  The residual of the compression input is therefore
confined to models that are simultaneously *superpolynomially large in the
complexity budget* and *informative about the string they describe*.

This is a partial discharge of the compression input, not a reduction of it:
the disjunction is proved for each individual model that satisfies it, and no
claim is made — or should be expected — that every model satisfies it.
Accordingly nothing here discharges `BudgetedConditionalCompressionStatement`
or the frozen target `BudgetedPairProjectionStatement`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **Small-gain leaf.**  A model `H` of `x` of plain set complexity at most
`iH` and log-size at most `j1` witnesses the description-profile point
`(iH - g + s, j1 + s)` for *every* claimed gain `g` bounded by the available
slack `s`: the slack alone already pays for the claimed complexity drop, so `H`
itself may be returned unchanged.

No optimality hypothesis, no compression, and no relation between `g` and the
conditional complexity of `H` given `x` are needed. -/
theorem inPlainDescriptionProfile_of_small_condK_gain
    (V : Map) (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
    (iH j1 g s : Nat) (hxH : x ∈ H)
    (hcompl : plainSetComplexity V H hH ≤ (iH : ENat))
    (hcard : H.card ≤ 2 ^ j1) (hgs : g ≤ s) :
    InPlainDescriptionProfile V x (iH - g + s) (j1 + s) := by
  refine ⟨H, hH, hxH, ?_, ?_⟩
  · exact hcompl.trans (by exact_mod_cast (by omega : iH ≤ iH - g + s))
  · exact hcard.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))

/-- **Budget-scale conditional compression, size-or-gain regime.**  For every
fixed exponent `k` and margin `w`, the body of
`BudgetedConditionalCompressionStatement` holds for each model that is either
polynomially small in the complexity budget (`|H| ≤ 2 ^ budget ^ k`, discharged
by `budgetedConditionalCompression_of_card_le_pow`) or carries only
logarithmically much information about `x` (`g ≤ logSlack w budget`, discharged
by `inPlainDescriptionProfile_of_small_condK_gain`).

Since the size disjunct is stated for the *cardinality* of the model, the
declared size coordinate `j1` is unconstrained in both branches. -/
theorem budgetedConditionalCompression_of_card_le_pow_or_small_gain
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k w : Nat) :
    ∃ c : Nat, ∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
        (iH j1 g budget : Nat),
      x ∈ H →
      plainSetComplexity V H hH ≤ (iH : ENat) →
      H.card ≤ 2 ^ j1 →
      condK V (codedUniformOn H hH).code x = (g : ENat) →
      iH ≤ budget →
      (H.card ≤ 2 ^ budget ^ k ∨ g ≤ logSlack w budget) →
      InPlainDescriptionProfile V x
        (iH - g + logSlack c budget) (j1 + logSlack c budget) := by
  obtain ⟨cPow, hPow⟩ := budgetedConditionalCompression_of_card_le_pow V U hV hU k
  refine ⟨cPow + w, ?_⟩
  intro H hH x iH j1 g budget hxH hcompl hcard hg hbudget hregime
  have hmono : logSlack cPow budget ≤ logSlack (cPow + w) budget :=
    logSlack_mono_left (Nat.le_add_right _ _) budget
  rcases hregime with hsize | hgain
  · exact ((hPow H hH x iH j1 g budget hxH hcompl hcard hg hbudget hsize).mono_i
      (by omega)).mono_j (by omega)
  · have hgs : g ≤ logSlack (cPow + w) budget :=
      hgain.trans (logSlack_mono_left (Nat.le_add_left _ _) budget)
    exact inPlainDescriptionProfile_of_small_condK_gain V H hH x iH j1 g
      (logSlack (cPow + w) budget) hxH hcompl hcard hgs

end Kolmogorov
