import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerMinimalWitness
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerSharpProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaUpwardCruxStatement
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerRoundedLength
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerLengthScale

namespace Kolmogorov

/-
**Retired false leaf `exists_rounded_corner_exponent`.**  An earlier draft stated
the rounded-exponent existence as

    ∃ c, ∀ l S alpha, c*|bits l|+c ≤ S → c*|bits l|+c ≤ alpha →
      ∃ t, 2^t + 2*|bits ⌈l/2^t⌉| + 2*|bits t| + c ≤ min S alpha,

left as an unproved placeholder leaf.  That statement is **mathematically FALSE**:
at `l = 0` we have `|bits 0| = 0`, so both hypotheses reduce to `c ≤ S` and
`c ≤ alpha`; taking `S = alpha = c` gives `min S alpha = c`, yet every `t` has
`2^t ≥ 1`, so `2^t + … + c > c`.  No constant `c` repairs it, so the placeholder
could never be discharged.

The defect is not only the degenerate case but the *shape*: the genuine consumer
`budgeted_plain_corner_of_rounded_length_log` charges the radius term `2^t`
(inside `⌈l/2^t⌉·2^t ≈ l + 2^t`) to the **two-part** budget `kx + beta = l + S`,
and only the address `2*|bits ⌈l/2^t⌉| + 2*|bits t|` to `alpha`.  Conflating both
into `min S alpha` over-charges `alpha` by `2^t`.  The corrected, provable leaf
keeps the two budgets separate; it is stated in the Aristotle packet and is not
needed by any declaration below (the hard-regime wrapper consumes the *failure*
of the rounded gate directly).
-/

noncomputable def roundedCornerLogConstant
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) : ℕ :=
  Classical.choose (budgeted_plain_corner_of_rounded_length_log V U hV hU)

theorem budgetedPlainCorner_of_hard_regime_rounded_minimal_tight
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ)
    (hHard : ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      alpha < kx →
      kx ^ k < beta →
      kx ^ k < x.length →
      (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
        beta < x.length ∧ kx + beta < x.length + m) →
      (∀ t : ℕ,
        alpha < 2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
              + 2 * (Nat.bits t).length + roundedCornerLogConstant V U hV hU ∨
        kx + beta < ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t + 1 +
           (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
             + 2 * (Nat.bits t).length + roundedCornerLogConstant V U hV hU)) →
      IsStochastic U x alpha beta →
      (∀ b : ℕ, b < beta → ¬ IsStochastic U x alpha b) →
      (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c kx ∧
        i + j ≤ kx + beta + logSlack c kx) :
    BudgetedPlainProfileCornerStatement V U := by
  let cR := roundedCornerLogConstant V U hV hU
  have hR : ∀ (x : BitString) (kx baseBudget alpha beta t : ℕ),
      2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
          + 2 * (Nat.bits t).length + cR ≤ alpha →
      ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t + 1 +
          (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
            + 2 * (Nat.bits t).length + cR) ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack cR baseBudget ∧
        i + j ≤ kx + beta + logSlack cR baseBudget :=
    Classical.choose_spec (budgeted_plain_corner_of_rounded_length_log V U hV hU)
  obtain ⟨cH, hH⟩ := hHard
  refine budgetedPlainCorner_of_hard_regime_superpoly_minimal_tight V U hV hU k
    ⟨max cR cH, fun x kx alpha beta hkx hka hbeta hlen hnot hstoch hbmin hamin => ?_⟩
  set c := max cR cH
  have hcR : cR ≤ c := le_max_left _ _
  have hcH : cH ≤ c := le_max_right _ _
  by_cases hrounded : ∃ t : ℕ,
      2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
          + 2 * (Nat.bits t).length + cR ≤ alpha ∧
      ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t + 1 +
          (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
            + 2 * (Nat.bits t).length + cR) ≤ kx + beta
  · obtain ⟨t, hma, hsum⟩ := hrounded
    obtain ⟨i, j, hprof, hi, hij⟩ := hR x kx kx alpha beta t hma hsum
    have hslack : logSlack cR kx ≤ logSlack c kx := logSlack_mono_const hcR
    exact ⟨i, j, hprof, by omega, by omega⟩
  · have hnotR : ∀ (t : ℕ),
        alpha < 2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
              + 2 * (Nat.bits t).length + cR ∨
        kx + beta < ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t + 1 +
           (2 * (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
             + 2 * (Nat.bits t).length + cR) := by
      intro t
      have h := not_exists.mp hrounded t
      rw [not_and_or, not_le, not_le] at h
      exact h
    obtain ⟨i, j, hprof, hi, hij⟩ :=
      hH x kx alpha beta hkx hka hbeta hlen hnot hnotR hstoch hbmin hamin
    have hslack : logSlack cH kx ≤ logSlack c kx := logSlack_mono_const hcH
    exact ⟨i, j, hprof, by omega, by omega⟩

end Kolmogorov
