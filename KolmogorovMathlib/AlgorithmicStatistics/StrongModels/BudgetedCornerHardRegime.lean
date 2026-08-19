import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedNoiseTransport
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedSectionThree
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity

/-!
# Collapsing the budgeted plain corner to its single open regime

`BudgetedPlainProfileCornerStatement V U` (`BudgetedNoiseTransport.lean`) is the
sole remaining input of `prop:upward`.  Three of the four regimes of its
`(alpha, beta)`-plane are already proved unconditionally:

* `kx ≤ alpha`: the singleton description already realizes the corner
  (`budgeted_plain_corner_of_kx_le_alpha`), independently of `beta`;
* `beta ≤ baseBudget`: the complexity-scale §3 chain proves the corner
  (`budgeted_stochasticity_to_plain_corner_of_beta_le`).

`budgetedPlainCorner_of_hard_regime` below is the pure case split that assembles
the full corner from those two proved leaves together with a hypothesis covering
**only** the remaining regime

```text
alpha < kx ≤ baseBudget < beta,
```

i.e. the corner for a string whose complexity fits the budget but whose
deficiency parameter `beta` is strictly above the budget, and whose model
complexity `alpha` is strictly below `C(x)`.  This isolates exactly what is still
open: the level of `x` inside its stochasticity witness can be as large as
`C(x) + beta`, so removing the residual `log beta` charge in this regime is the
genuine mathematical crux (see the header of `BudgetedNoiseTransport.lean`).

Nothing here assumes the hard regime holds; `budgetedPlainCorner_of_hard_regime`
is a reduction, and its hypothesis `hHard` is a faithful, precisely delineated
statement of the alternative research direction.  No frozen interface is edited.
-/

namespace Kolmogorov

/-- **The budgeted plain corner reduces to its single open regime.**  Given the
corner for the regime `alpha < kx ≤ baseBudget < beta`, the full
`BudgetedPlainProfileCornerStatement V U` follows by a case split: the regime
`kx ≤ alpha` is `budgeted_plain_corner_of_kx_le_alpha`, the regime
`beta ≤ baseBudget` is `budgeted_stochasticity_to_plain_corner_of_beta_le`, and
the remaining regime is exactly `hHard`.

This does not prove the corner; it collapses the open part of the corner to the
single hard regime, so a subsequent proof only has to treat `alpha < kx` and
`baseBudget < beta` simultaneously. -/
theorem budgetedPlainCorner_of_hard_regime
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hHard : ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      alpha < kx →
      baseBudget < beta →
      IsStochastic U x alpha beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget) :
    BudgetedPlainProfileCornerStatement V U := by
  obtain ⟨cA, hA⟩ := budgeted_plain_corner_of_kx_le_alpha V hV
  obtain ⟨cB, hB⟩ := budgeted_stochasticity_to_plain_corner_of_beta_le V U hV hU
  obtain ⟨cH, hH⟩ := hHard
  refine ⟨max (max cA cB) cH, fun x kx baseBudget alpha beta hkx hkxN hstoch => ?_⟩
  set c := max (max cA cB) cH with hc
  have hcA : logSlack cA baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_trans (le_max_left cA cB) (le_max_left _ cH)) baseBudget
  have hcB : logSlack cB baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_trans (le_max_right cA cB) (le_max_left _ cH)) baseBudget
  have hcH : logSlack cH baseBudget ≤ logSlack c baseBudget :=
    logSlack_mono_left (le_max_right _ cH) baseBudget
  by_cases hka : kx ≤ alpha
  · -- Singleton regime: the model complexity already reaches `C(x)`.
    obtain ⟨i, j, hprof, hi, hij⟩ := hA x kx baseBudget alpha beta hkx hka
    exact ⟨i, j, hprof, by omega, by omega⟩
  · push Not at hka
    by_cases hbb : beta ≤ baseBudget
    · -- Deficiency within budget: the §3 chain proves the corner.
      obtain ⟨i, j, hprof, hi, hij⟩ := hB x kx baseBudget alpha beta hkx hkxN hbb hstoch
      exact ⟨i, j, hprof, by omega, by omega⟩
    · push Not at hbb
      -- The single open regime `alpha < kx ≤ baseBudget < beta`.
      obtain ⟨i, j, hprof, hi, hij⟩ := hH x kx baseBudget alpha beta hkx hkxN hka hbb hstoch
      exact ⟨i, j, hprof, by omega, by omega⟩

lemma size_pow_le (m k : ℕ) : (m^k).size ≤ k * m.size + 1 := by
  by_cases hk : k = 0
  · subst hk; simp
  have h1 : m < 2 ^ m.size := Nat.lt_size_self m
  have h2 : m ^ k < (2 ^ m.size) ^ k := Nat.pow_lt_pow_left h1 hk
  rw [← Nat.pow_mul] at h2
  rw [Nat.mul_comm] at h2
  have h3 : (m ^ k).size ≤ k * m.size := Nat.size_le.mpr h2
  omega

/-- A fixed polynomial bound on the visible parameter can be absorbed by
increasing the constant of `logSlack`. -/
theorem logSlack_le_of_le_pow (c k : ℕ) :
    ∃ c' : ℕ, ∀ m b : ℕ, b ≤ m ^ k → logSlack c b ≤ logSlack c' m := by
  use c * k + 2 * c
  intro m b hb
  unfold logSlack
  have h1 : (Nat.bits b).length = b.size := Nat.size_eq_bits_len b
  have h2 : (Nat.bits m).length = m.size := Nat.size_eq_bits_len m
  rw [h1, h2]
  have hb_size : b.size ≤ (m ^ k).size := Nat.size_le_size hb
  have hk_size : (m ^ k).size ≤ k * m.size + 1 := size_pow_le m k
  generalize m.size = S at hk_size h2 ⊢
  generalize b.size = B at hb_size h1 ⊢
  nlinarith

/-- The residual `logSlack _ beta` in the stochasticity-to-plain conversion is
budget-scale whenever `beta` is bounded by a fixed power of `baseBudget`. -/
theorem budgeted_stochasticity_to_plain_corner_of_beta_le_pow
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) → kx ≤ baseBudget → beta ≤ baseBudget ^ k →
      IsStochastic U x alpha beta →
      ∃ i j, InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c_base, hc⟩ := budgeted_stochasticity_to_plain_corner_add_logSlack_beta V U hV hU
  obtain ⟨c', hc'⟩ := logSlack_le_of_le_pow c_base k
  use c_base + c'
  intro x kx baseBudget alpha beta hkx hkxN hb hstoch
  obtain ⟨i, j, hprof, hi, hij⟩ := hc x kx baseBudget alpha beta hkx hkxN hstoch
  have h_beta : logSlack c_base beta ≤ logSlack c' baseBudget := hc' baseBudget beta hb
  have h_slack1 :
      logSlack c_base baseBudget + logSlack c_base beta ≤ logSlack (c_base + c') baseBudget := by
    unfold logSlack at h_beta ⊢
    rw [Nat.add_mul]
    linarith
  refine ⟨i, j, hprof, by omega, by omega⟩

/-- The plain prefix complexity of the code of an index `b` that is bounded by a
fixed power `m ^ k` of the visible budget is itself budget-scale: it is at most
`logSlack c m` for a uniform `c`.  This is the "cheap index" leaf shared by both
open S4 routes (the level-precision charge for `prop:upward` and the pooled
enumeration index for the direct `prop:add-noise` multiplicity argument).

It is a pure composition of the logarithmic `natCode` bound
`KPPlain_natCode_le_log` (`Prefix/Properties.lean`) with the polynomial-argument
absorption `logSlack_le_of_le_pow` proved above. -/
theorem natCode_KPPlain_le_of_le_pow (U : Map) (hU : IsOptimalPrefixConditional U) (k : ℕ) :
    ∃ c : ℕ, ∀ (m b : ℕ), b ≤ m ^ k → KPPlain U (natCode b) ≤ (logSlack c m : ENat) := by
  obtain ⟨c0, hc0⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨c', hc'⟩ := logSlack_le_of_le_pow (c0 + 2) k
  refine ⟨c', fun m b hb => ?_⟩
  have hstep1 : KPPlain U (natCode b) ≤ (logSlack (c0 + 2) b : ENat) := by
    refine le_trans (hc0 b) ?_
    have hnat : 2 * (Nat.bits b).length + c0 ≤ logSlack (c0 + 2) b := by
      unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits b).length)]
    calc (2 * (Nat.bits b).length + (c0 : ENat))
        = ((2 * (Nat.bits b).length + c0 : ℕ) : ENat) := by push_cast; ring
      _ ≤ ((logSlack (c0 + 2) b : ℕ) : ENat) := by exact_mod_cast hnat
  exact le_trans hstep1 (by exact_mod_cast hc' m b hb)

end Kolmogorov
