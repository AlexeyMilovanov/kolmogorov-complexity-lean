import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedAddNoisePolySize

/-!
# Intrinsic-size form of the budgeted add-noise inputs

`BudgetedAddNoisePolySize.lean` removes every polynomially large *declared*
size coordinate from the two open budget-scale inputs of the low add-noise
branch.  Both statements are, however, formulated with a user-supplied upper
bound (`j1`, resp. `j`) on the log-size of the model, and that bound is what
the polynomial hypotheses constrain.  A declared bound may be arbitrarily
wasteful: a model with two elements may legitimately be presented with size
coordinate `2 ^ 2 ^ n`.

This file replaces the declared bound by the *intrinsic* size `⌈log₂ |H|⌉` of
the model.  Since the size coordinate of the conclusion is monotone, working
with the intrinsic size only strengthens the results:

* `inPlainDescriptionProfile_of_condK_compression_intrinsic_size` charges the
  size-scale compression slack against `⌈log₂ |H|⌉` instead of `j1`;
* `budgetedConditionalCompression_of_card_le_pow` proves the body of
  `BudgetedConditionalCompressionStatement` whenever `|H| ≤ 2 ^ (budget ^ k)`,
  with no hypothesis at all on the declared coordinate `j1`;
* `inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_witness_card_le_pow`
  does the same for the budgeted fibre projection: only the cardinality of the
  witnessing pair model has to be polynomially bounded in the visible budgets.

Each of these strictly extends the corresponding polynomial-size regime, which
is recovered by taking the declared bound as the intrinsic one.
-/

namespace Kolmogorov

/-- **Conditional compression at the intrinsic size scale.**  The slack of
`inPlainDescriptionProfile_of_condK_compression_size_scale` may be charged
against the actual log-cardinality `⌈log₂ |H|⌉` of the model rather than
against the declared size coordinate `j1`. -/
theorem inPlainDescriptionProfile_of_condK_compression_intrinsic_size
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
        (iH j1 g : Nat),
      x ∈ H →
      plainSetComplexity V H hH ≤ (iH : ENat) →
      H.card ≤ 2 ^ j1 →
      condK V (codedUniformOn H hH).code x = (g : ENat) →
      InPlainDescriptionProfile V x
        (iH - g + logSlack c (iH + Nat.clog 2 H.card))
        (j1 + logSlack c (iH + Nat.clog 2 H.card)) := by
  obtain ⟨c, hc⟩ := inPlainDescriptionProfile_of_condK_compression_size_scale V U hV hU
  refine ⟨c, ?_⟩
  intro H hH x iH j1 g hxH hcompl hcard hg
  have hintr : H.card ≤ 2 ^ Nat.clog 2 H.card := Nat.le_pow_clog (by norm_num) _
  have hle : Nat.clog 2 H.card ≤ j1 := Nat.clog_le_of_le_pow hcard
  exact (hc H hH x iH (Nat.clog 2 H.card) g hxH hcompl hintr hg).mono_j (by omega)

/-- **Budget-scale conditional compression, polynomial-cardinality regime.**
The body of `BudgetedConditionalCompressionStatement` holds, for every fixed
exponent `k`, as soon as the *cardinality* of the compressed model satisfies
`|H| ≤ 2 ^ (budget ^ k)`.  No hypothesis is imposed on the declared size
coordinate `j1`, so this strictly extends
`budgetedConditionalCompression_of_size_le_pow`. -/
theorem budgetedConditionalCompression_of_card_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : Nat) :
    ∃ c : Nat, ∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
        (iH j1 g budget : Nat),
      x ∈ H →
      plainSetComplexity V H hH ≤ (iH : ENat) →
      H.card ≤ 2 ^ j1 →
      condK V (codedUniformOn H hH).code x = (g : ENat) →
      iH ≤ budget →
      H.card ≤ 2 ^ budget ^ k →
      InPlainDescriptionProfile V x
        (iH - g + logSlack c budget) (j1 + logSlack c budget) := by
  obtain ⟨cIntr, hIntr⟩ :=
    inPlainDescriptionProfile_of_condK_compression_intrinsic_size V U hV hU
  obtain ⟨c1, hc1⟩ := logSlack_le_of_le_pow cIntr k
  refine ⟨cIntr + c1, ?_⟩
  intro H hH x iH j1 g budget hxH hcompl hcard hg hbudget hcardpow
  have hm : Nat.clog 2 H.card ≤ budget ^ k := Nat.clog_le_of_le_pow hcardpow
  have hfold : logSlack cIntr (iH + Nat.clog 2 H.card) ≤ logSlack (cIntr + c1) budget := by
    have h1 : logSlack cIntr (iH + Nat.clog 2 H.card) ≤
        logSlack cIntr (budget + budget ^ k) :=
      logSlack_mono_right cIntr (by omega)
    have h2 : logSlack cIntr (budget + budget ^ k) ≤
        logSlack cIntr budget + logSlack cIntr (budget ^ k) :=
      logSlack_add_le cIntr budget (budget ^ k)
    have h3 : logSlack cIntr (budget ^ k) ≤ logSlack c1 budget :=
      hc1 budget (budget ^ k) le_rfl
    have h4 : logSlack cIntr budget + logSlack c1 budget = logSlack (cIntr + c1) budget := by
      unfold logSlack; ring
    omega
  exact ((hIntr H hH x iH j1 g hxH hcompl hcard hg).mono_i (by omega)).mono_j (by omega)

/-- **Budgeted fibre projection of a pair model, polynomial-cardinality
regime.**  The exact budget-scale conclusion of
`BudgetedPairProjectionStatement` holds whenever the pair model is witnessed by
a finite set `B` whose *cardinality* is at most `2 ^ ((baseBudget + l(y)) ^ k)`.
The declared size coordinate `j` of the model is unconstrained, so this
strictly extends
`inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow`. -/
theorem inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_witness_card_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : Nat) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat)
        (B : Finset BitString) (hB : B.Nonempty),
      pairCode x y ∈ B →
      plainSetComplexity V B hB ≤ (i : ENat) →
      B.card ≤ 2 ^ j →
      B.card ≤ 2 ^ (baseBudget + y.length) ^ k →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ baseBudget →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c baseBudget + logSlack c y.length)
        (j - y.length + logSlack c baseBudget + logSlack c y.length) := by
  obtain ⟨c, hc⟩ :=
    inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow V U hV hU k
  refine ⟨c, ?_⟩
  intro x y epsilon i j baseBudget B hB hmem hcompl hcard hcardpow hrandom hbudget
  have hintr : B.card ≤ 2 ^ Nat.clog 2 B.card := Nat.le_pow_clog (by norm_num) _
  have hjle : Nat.clog 2 B.card ≤ j := Nat.clog_le_of_le_pow hcard
  have hjpow : Nat.clog 2 B.card ≤ (baseBudget + y.length) ^ k :=
    Nat.clog_le_of_le_pow hcardpow
  have hprofile : InPlainDescriptionProfile V (pairCode x y) i (Nat.clog 2 B.card) :=
    ⟨B, hB, hmem, hcompl, hintr⟩
  exact (hc x y epsilon i (Nat.clog 2 B.card) baseBudget hprofile hrandom hbudget
    hjpow).mono_j (by omega)

end Kolmogorov
