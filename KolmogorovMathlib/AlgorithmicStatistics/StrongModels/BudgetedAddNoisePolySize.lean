import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedAddNoiseLowBranch
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerHardRegime

/-!
# Polynomial-size regime of the budgeted pair projection

`BudgetedAddNoiseLowBranch.lean` proves the budget-scale fibre projection
`inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le` outright when
the size coordinate `j` of the pair model also fits inside the complexity
budget, `j ≤ baseBudget`.  The only remaining obstruction to the frozen target
`BudgetedPairProjectionStatement` is the residual `log j` charge in the regime
where `j` is much larger than the visible budgets.

This file removes every *polynomially* larger size coordinate from that
obstruction.  The observation is that the proved small-size branch may be
applied with the enlarged budget `max baseBudget j`, which is legitimate since
its hypotheses only ask that the budget dominate both `i` and `j`.  The
resulting slack `logSlack c (max baseBudget j)` is logarithmic, hence still
budget-scale as soon as `j` is bounded by a fixed power of `baseBudget + l(y)`.

Consequently the size coordinate must be *superpolynomial* in the visible
budgets for the frozen statement to remain open; this mirrors the
`budgeted_stochasticity_to_plain_corner_of_beta_le_pow` reduction of the
corner lane.

The same folding argument is applied to the compression input of the low
branch: `budgetedConditionalCompression_of_size_le_pow` proves the body of
`BudgetedConditionalCompressionStatement` whenever the log-size of the
compressed model is bounded by a fixed power of the complexity budget.
-/

namespace Kolmogorov

/-- Folding lemma: a slack logarithmic in `max b j` is bounded by the sum of the
slacks in the two visible budgets `b` and `n`, provided `j` is bounded by a
fixed power of `b + n`. -/
theorem logSlack_max_le_of_le_pow (c k : Nat) :
    ∃ c' : Nat, ∀ b j n : Nat, j ≤ (b + n) ^ k →
      logSlack c (max b j) ≤ logSlack c' b + logSlack c' n := by
  obtain ⟨c1, hc1⟩ := logSlack_le_of_le_pow c k
  refine ⟨c + c1, ?_⟩
  intro b j n hj
  have hmax : max b j ≤ b + (b + n) ^ k := by
    have : max b j ≤ b + j := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega
  have h1 : logSlack c (max b j) ≤ logSlack c (b + (b + n) ^ k) :=
    logSlack_mono_right c hmax
  have h2 : logSlack c (b + (b + n) ^ k) ≤ logSlack c b + logSlack c ((b + n) ^ k) :=
    logSlack_add_le c b ((b + n) ^ k)
  have h3 : logSlack c ((b + n) ^ k) ≤ logSlack c1 (b + n) := hc1 (b + n) ((b + n) ^ k) le_rfl
  have h4 : logSlack c1 (b + n) ≤ logSlack c1 b + logSlack c1 n := logSlack_add_le c1 b n
  have h5 : logSlack c b + logSlack c1 b = logSlack (c + c1) b := by
    unfold logSlack; ring
  have h6 : logSlack c1 n ≤ logSlack (c + c1) n := logSlack_mono_left (Nat.le_add_left _ _) n
  omega

/-- **Budgeted fibre projection of a pair model, polynomial-size regime.**  For
every fixed exponent `k` the exact budget-scale conclusion of
`BudgetedPairProjectionStatement` holds whenever the size coordinate of the pair
model satisfies `j ≤ (baseBudget + l(y)) ^ k`.

The proof applies the proved small-size branch with the enlarged budget
`max baseBudget j` and folds the resulting logarithmic slack back into the two
visible budgets `baseBudget` and `l(y)`.  Taking `k = 1` recovers (and
strictly extends) `inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le`. -/
theorem inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : Nat) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon i j baseBudget : Nat),
      InPlainDescriptionProfile V (pairCode x y) i j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      i ≤ baseBudget →
      j ≤ (baseBudget + y.length) ^ k →
      InPlainDescriptionProfile V x
        (i + epsilon + logSlack c baseBudget + logSlack c y.length)
        (j - y.length + logSlack c baseBudget + logSlack c y.length) := by
  obtain ⟨c0, h0⟩ := inPlainDescriptionProfile_fst_of_pair_model_budgeted_of_size_le V U hV hU
  obtain ⟨c1, hc1⟩ := logSlack_max_le_of_le_pow c0 k
  refine ⟨c0 + c1, ?_⟩
  intro x y epsilon i j baseBudget hprofile hrandom hbudget hj
  have hmain := h0 x y epsilon i j (max baseBudget j) hprofile hrandom
    (le_trans hbudget (le_max_left _ _)) (le_max_right _ _)
  have hslack : logSlack c0 (max baseBudget j) ≤
      logSlack c1 baseBudget + logSlack c1 y.length := hc1 baseBudget j y.length hj
  have hfold1 : logSlack c1 baseBudget ≤ logSlack (c0 + c1) baseBudget :=
    logSlack_mono_left (Nat.le_add_left _ _) baseBudget
  have hfold2 : logSlack c0 y.length + logSlack c1 y.length =
      logSlack (c0 + c1) y.length := by
    unfold logSlack; ring
  exact (hmain.mono_i (by omega)).mono_j (by omega)

/-- **Budget-scale conditional compression, polynomial-size regime.**  The
compression input `BudgetedConditionalCompressionStatement` of the budgeted low
branch holds, for every fixed exponent `k`, whenever the log-size `j1` of the
compressed model is bounded by `budget ^ k`: the proved size-scale compression
`inPlainDescriptionProfile_of_condK_compression_size_scale` then already pays
only a budget-scale slack. -/
theorem budgetedConditionalCompression_of_size_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : Nat) :
    ∃ c : Nat, ∀ (H : Finset BitString) (hH : H.Nonempty) (x : BitString)
        (iH j1 g budget : Nat),
      x ∈ H →
      plainSetComplexity V H hH ≤ (iH : ENat) →
      H.card ≤ 2 ^ j1 →
      condK V (codedUniformOn H hH).code x = (g : ENat) →
      iH ≤ budget →
      j1 ≤ budget ^ k →
      InPlainDescriptionProfile V x
        (iH - g + logSlack c budget) (j1 + logSlack c budget) := by
  obtain ⟨cSize, hSize⟩ := inPlainDescriptionProfile_of_condK_compression_size_scale V U hV hU
  obtain ⟨c1, hc1⟩ := logSlack_le_of_le_pow cSize k
  refine ⟨cSize + c1, ?_⟩
  intro H hH x iH j1 g budget hxH hcompl hcard hg hbudget hj1
  have hfold : logSlack cSize (iH + j1) ≤ logSlack (cSize + c1) budget := by
    have h1 : logSlack cSize (iH + j1) ≤ logSlack cSize (budget + budget ^ k) :=
      logSlack_mono_right cSize (by omega)
    have h2 : logSlack cSize (budget + budget ^ k) ≤
        logSlack cSize budget + logSlack cSize (budget ^ k) :=
      logSlack_add_le cSize budget (budget ^ k)
    have h3 : logSlack cSize (budget ^ k) ≤ logSlack c1 budget :=
      hc1 budget (budget ^ k) le_rfl
    have h4 : logSlack cSize budget + logSlack c1 budget = logSlack (cSize + c1) budget := by
      unfold logSlack; ring
    omega
  exact ((hSize H hH x iH j1 g hxH hcompl hcard hg).mono_i (by omega)).mono_j (by omega)

end Kolmogorov
