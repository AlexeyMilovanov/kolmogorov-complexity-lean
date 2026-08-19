import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedNoiseTransport
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedSectionThree
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileBridges

/-!
# A slack-free optimal-set to description-profile conversion

`isOptimalSetStochastic_imp_profile` (`TwoPart/Deficiencies.lean`) converts an
optimal finite-set stochasticity witness into a point of the description
profile *at a prescribed size coordinate* `j`, and therefore has to pay the
address cost of a description shift, i.e. a `logSlack c (alpha + beta + j)`
charge on the complexity coordinate.

For the budgeted corner of §7 the size coordinate need not be prescribed: the
corner only constrains `i` and `i + j`.  This module records that, with the
size coordinate left free, the conversion is completely slack-free:

* `isOptimalSetStochastic_imp_profile_sharp` — an optimal-set witness of
  parameters `(alpha, beta)` for a string of prefix complexity `k` yields a
  profile point with `i ≤ alpha` and `i + j = k + beta` exactly.

The reason is that the optimality-deficiency inequality already *is* the
incidence bound `2 ^ C(S) * |S| ≤ 2 ^ (K(x) + beta)`; taking `i` to be the true
set complexity of the witness and `j := k + beta - i` uses it as is, with no
shift and hence no address to encode.

Two consequences are recorded:

* `budgeted_plain_corner_of_isOptimalSetStochastic` — the budget-scale plain
  corner holds unconditionally for *optimal-set* stochasticity witnesses, with
  the only slack coming from the constant-cost prefix-to-plain bridge and the
  `O(log C(x))` plain-versus-prefix gap; in particular no `O(log beta)` term
  appears;
* `budgetedPlainCorner_of_optimalSetConversion_budget` — consequently the whole
  remaining distance between the proved §3 chain and the open budget-scale
  plain corner `BudgetedPlainProfileCornerStatement` is concentrated in one
  single statement, the *optimal-set conversion* (Theorem 3 of the source) with
  its logarithmic loss measured against the complexity of `x` alone.

Nothing here is assumed: the sharp conversion is proved unconditionally, and
the corner reduction is a theorem whose hypothesis is displayed explicitly.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **Slack-free optimal-set conversion.**  If `x` has prefix complexity `k` and
admits an optimal finite-set stochasticity witness with parameters
`(alpha, beta)`, then `x` has a description-profile point `(i, j)` with
`i ≤ alpha` and `i + j = k + beta`.

Unlike `isOptimalSetStochastic_imp_profile` no logarithmic slack is paid: the
size coordinate is not prescribed in advance, so the witness itself can be used
at its true complexity coordinate and no description shift is needed. -/
theorem isOptimalSetStochastic_imp_profile_sharp
    (U : Map) (x : BitString) (alpha beta k : ℕ)
    (hk : KPPlain U x = (k : ENat))
    (hopt : IsOptimalSetStochastic U x alpha beta) :
    ∃ i j : ℕ, InDescriptionProfile U x i j ∧ i ≤ alpha ∧ i + j = k + beta := by
  obtain ⟨S, hS, hx, hcomp, hdef⟩ := hopt
  obtain ⟨m₀, hm₀_eq⟩ : ∃ m : ℕ, setComplexity U S hS = m := by
    cases h : setComplexity U S hS <;> simp_all
  have hm₀_le : m₀ ≤ alpha := by rw [hm₀_eq] at hcomp; exact_mod_cast hcomp
  have hcard_ne : (S.card : ENNReal) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hcard_top : (S.card : ENNReal) ≠ ⊤ := by simp
  have hdef2 : (2 : ENNReal)⁻¹ ^ k ≤ 2 ^ beta * ((2 : ENNReal)⁻¹ ^ m₀ * (S.card : ENNReal)⁻¹) := by
    rw [setOptimalityDeficiencyLe_iff_of_mem hx] at hdef
    rw [hk, hm₀_eq, complexityWeight_coe, complexityWeight_coe] at hdef
    exact hdef
  have h_card : (2 : ENNReal) ^ m₀ * (S.card : ENNReal) ≤ 2 ^ (k + beta) := by
    have H := mul_le_mul' hdef2 (le_refl (2 ^ k * 2 ^ m₀ * (S.card : ENNReal)))
    have H_LHS : (2 : ENNReal)⁻¹ ^ k * (2 ^ k * 2 ^ m₀ * (S.card : ENNReal)) =
        2 ^ m₀ * S.card := by
      rw [show (2 : ENNReal)⁻¹ ^ k * (2 ^ k * 2 ^ m₀ * (S.card : ENNReal)) =
          ((2 : ENNReal)⁻¹ ^ k * 2 ^ k) * (2 ^ m₀ * S.card) by ring]
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]
    have H_RHS : 2 ^ beta * ((2 : ENNReal)⁻¹ ^ m₀ * (S.card : ENNReal)⁻¹) *
        (2 ^ k * 2 ^ m₀ * (S.card : ENNReal)) = 2 ^ (k + beta) := by
      rw [show 2 ^ beta * ((2 : ENNReal)⁻¹ ^ m₀ * (S.card : ENNReal)⁻¹) *
          (2 ^ k * 2 ^ m₀ * (S.card : ENNReal)) = (2 ^ k * 2 ^ beta) *
          ((2 : ENNReal)⁻¹ ^ m₀ * 2 ^ m₀) * ((S.card : ENNReal)⁻¹ * S.card) by ring]
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
          ENNReal.inv_mul_cancel hcard_ne hcard_top, one_pow, mul_one, mul_one, pow_add]
    rw [H_LHS, H_RHS] at H
    exact H
  have h_card_nat : 2 ^ m₀ * S.card ≤ 2 ^ (k + beta) := by exact_mod_cast h_card
  have hScard_pos : 0 < S.card := hS.card_pos
  have hm₀_kb : m₀ ≤ k + beta := by
    by_contra hlt
    push Not at hlt
    have h1 : (2 : ℕ) ^ (k + beta) < 2 ^ m₀ := Nat.pow_lt_pow_right (by norm_num) hlt
    have h2 : (2 : ℕ) ^ m₀ ≤ 2 ^ m₀ * S.card := Nat.le_mul_of_pos_right _ hScard_pos
    omega
  have hS_card : S.card ≤ 2 ^ (k + beta - m₀) := by
    have hmul : 2 ^ m₀ * S.card ≤ 2 ^ m₀ * 2 ^ (k + beta - m₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hm₀_kb]; exact h_card_nat
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos (by norm_num) m₀)
  exact ⟨m₀, k + beta - m₀, ⟨S, hS, hx, le_of_eq hm₀_eq, hS_card⟩, hm₀_le, by omega⟩

/-- **The plain corner for an optimal-set stochasticity witness.**  If `x` has
plain complexity `kx` and an *optimal finite-set* witness with parameters
`(alpha, beta)`, then `x` has a plain description-profile point `(i, j)` with

* `i ≤ alpha + logSlack c kx`, and
* `i + j ≤ kx + beta + logSlack c kx`.

This is the budget-scale plain corner for optimal-set stochasticity, proved
unconditionally and with no dependence on the length `l(x)` nor on `beta`: the
only slack paid is the constant-cost prefix-to-plain bridge together with the
`O(log C(x))` gap between the plain complexity `kx` and the prefix complexity
of `x`.  The complexity coordinate itself is not charged at all beyond that
bridge, by `isOptimalSetStochastic_imp_profile_sharp`. -/
theorem budgeted_plain_corner_of_isOptimalSetStochastic
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      IsOptimalSetStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c kx ∧
        i + j ≤ kx + beta + logSlack c kx := by
  obtain ⟨cBr, hBr⟩ := inPlainDescriptionProfile_of_inDescriptionProfile V U hV hU
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨2 + (cBits + cKP + cBr), ?_⟩
  intro x kx alpha beta hkx hopt
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp (KPPlain_ne_top_of_optimal U hU x)
  have hp_eq : KPPlain U x = (p : ENat) := hp.symm
  have hp_bd : p ≤ kx + 2 * (Nat.bits kx).length + cBits + cKP := by
    have h3 : (p : ENat) ≤ ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by
      calc (p : ENat) = KPPlain U x := hp
        _ ≤ (kx : ENat) + KPPlain U (Nat.bits kx) + (cKP : ENat) := hKP x kx hkx
        _ ≤ (kx : ENat) + ((2 * (Nat.bits kx).length + cBits : ℕ) : ENat) + (cKP : ENat) := by
              gcongr; exact hBits (Nat.bits kx)
        _ = ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by push_cast; ring
    exact_mod_cast h3
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    isOptimalSetStochastic_imp_profile_sharp U x alpha beta p hp_eq hopt
  have hbits_slack : 2 * (Nat.bits kx).length ≤ logSlack 2 kx := by
    unfold logSlack; omega
  have hslack : logSlack 2 kx + (cBits + cKP + cBr) ≤ logSlack (2 + (cBits + cKP + cBr)) kx :=
    logSlack_add_const_le 2 (cBits + cKP + cBr) kx
  exact ⟨i + cBr, j, hBr x i j hprof, by omega, by omega⟩

/-- **The budget-scale plain corner from the budget-scale optimal-set
conversion.**  If every stochasticity witness of a string can be converted into
an *optimal finite-set* witness at the cost of `logSlack c K(x)` in both
parameters, then the budget-scale plain corner
`BudgetedPlainProfileCornerStatement V U` holds.

This is the sharpest available reduction of the remaining `prop:upward`
research direction: by `budgeted_plain_corner_of_isOptimalSetStochastic` the passage from
an optimal-set witness to the plain corner is already budget-scale, so the
entire residual `O(log beta)` charge of the proved chain
(`budgeted_stochasticity_to_plain_corner_add_logSlack_beta`, whose slack comes
from `stochasticity_to_optimal_set_budget` measuring against
`K(x) + alpha + beta`) lives in the optimal-set conversion `hConv` alone.

Nothing is assumed here: `hConv` is displayed as an explicit hypothesis, and it
is exactly Theorem 3 of the source with its logarithmic loss measured against
the complexity of `x` only. -/
theorem budgetedPlainCorner_of_optimalSetConversion_budget
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hConv : ∃ c : ℕ, ∀ (x : BitString) (p alpha beta : ℕ),
      KPPlain U x = (p : ENat) →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x
        (alpha + logSlack c p) (beta + logSlack c p)) :
    BudgetedPlainProfileCornerStatement V U := by
  obtain ⟨cConv, hConv⟩ := hConv
  obtain ⟨cCorner, hCorner⟩ := budgeted_plain_corner_of_isOptimalSetStochastic V U hV hU
  obtain ⟨cKP, hKP⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨CConv, hCConv⟩ := logSlack_linear_bound cConv 3 (cBits + cKP)
  refine ⟨CConv + cCorner, ?_⟩
  intro x kx baseBudget alpha beta hkx hkxN hstoch
  obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp (KPPlain_ne_top_of_optimal U hU x)
  have hp_eq : KPPlain U x = (p : ENat) := hp.symm
  have hbits_self : (Nat.bits kx).length ≤ kx := length_natBits_le_self kx
  have hp_bd : p ≤ kx + 2 * (Nat.bits kx).length + cBits + cKP := by
    have h3 : (p : ENat) ≤ ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by
      calc (p : ENat) = KPPlain U x := hp
        _ ≤ (kx : ENat) + KPPlain U (Nat.bits kx) + (cKP : ENat) := hKP x kx hkx
        _ ≤ (kx : ENat) + ((2 * (Nat.bits kx).length + cBits : ℕ) : ENat) + (cKP : ENat) := by
              gcongr; exact hBits (Nat.bits kx)
        _ = ((kx + 2 * (Nat.bits kx).length + cBits + cKP : ℕ) : ENat) := by push_cast; ring
    exact_mod_cast h3
  obtain ⟨i, j, hprof, hi, hij⟩ :=
    hCorner x kx (alpha + logSlack cConv p) (beta + logSlack cConv p) hkx
      (hConv x p alpha beta hp_eq hstoch)
  have hfold : logSlack cConv p ≤ logSlack CConv baseBudget :=
    le_trans (logSlack_mono_right cConv (show p ≤ 3 * baseBudget + (cBits + cKP) by omega))
      (hCConv baseBudget)
  have hcorner_fold : logSlack cCorner kx ≤ logSlack cCorner baseBudget :=
    logSlack_mono_right cCorner hkxN
  have hsum : logSlack CConv baseBudget + logSlack cCorner baseBudget =
      logSlack (CConv + cCorner) baseBudget := logSlack_add_const _ _ _
  exact ⟨i, j, hprof, by omega, by omega⟩

end Kolmogorov
