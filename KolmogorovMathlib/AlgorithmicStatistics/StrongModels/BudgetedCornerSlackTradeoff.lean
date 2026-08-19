import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerRoundedLength
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Lemma4Support

/-!
# The budget/slack trade-off of the rounded-length corner

`budgeted_plain_corner_of_rounded_length_log`
(`BudgetedCornerRoundedLength.lean`) proves the budget-scale plain corner for a
string `x` from an exponent `t` whose *ceiling* radius
`n = ⌈l(x)/2^t⌉ · 2^t` simultaneously fits the model budget `alpha` (through the
explicit address cost of the quotient `⌈l(x)/2^t⌉` and of `t`) and the two-part
budget `kx + beta`.

Both side conditions of that theorem still mention the ceiling quotient
`⌈l(x)/2^t⌉ = (l(x) + 2^t - 1) / 2^t`, which is awkward for a caller: what a
caller controls is the *floor* scale `l(x) / 2^t`, i.e. the number of bits saved
by rounding at scale `2^t`.  This module removes the ceiling from the side
conditions and displays the corner as a plain trade-off between the two budgets:

* the address cost paid against `alpha` is
  `2 * (|bits (l(x) / 2^t)| + 1) + 2 * |bits t| + c`, i.e. essentially
  `2 * (log l(x) - t) + 2 * log t`, and therefore *decreases* as the rounding
  scale `t` grows;
* the amount of two-part slack consumed above `l(x)` is `2^t` plus that same
  address cost, and therefore *increases* as `t` grows.

`budgeted_plain_corner_of_slack_tradeoff` is exactly that statement, and
`budgeted_plain_corner_of_exact_scale` is its `t = 0` specialisation (no
rounding: the radius is `l(x)` itself, the address cost is the full
`2 * |bits l(x)| + O(1)`).

Nothing here is assumed; both theorems are unconditional consequences of the
rounded-length lane, and no frozen interface is edited.
-/

namespace Kolmogorov

/-- The ceiling quotient exceeds the floor quotient by at most one. -/
theorem ceilDiv_le_div_add_one (l t : ℕ) :
    (l + 2 ^ t - 1) / 2 ^ t ≤ l / 2 ^ t + 1 := by
  have hpos : 0 < 2 ^ t := pow_pos (by norm_num) t
  calc (l + 2 ^ t - 1) / 2 ^ t
      ≤ (l + 2 ^ t) / 2 ^ t := Nat.div_le_div_right (by omega)
    _ = l / 2 ^ t + 1 := Nat.add_div_right l hpos

/-- **The budget/slack trade-off form of the rounded-length corner.**  Fix a
rounding scale `t`.  Write `a := 2 * (|bits (l(x) / 2^t)| + 1) + 2 * |bits t| + c`
for the explicit address cost of the rounded radius at that scale.  If `a` fits
the model budget `alpha`, and the two-part budget `kx + beta` covers
`l(x) + 2^t + a`, then the exact budget-scale plain corner holds with slack
`logSlack c baseBudget`.

Compared with `budgeted_plain_corner_of_rounded_length_log`, the side conditions
no longer mention the ceiling quotient `⌈l(x)/2^t⌉`: the address cost is
expressed through the floor scale `l(x) / 2^t`, and the rounding overhead is
charged as the single term `2^t` of two-part slack.  Increasing `t` lowers the
`alpha`-side cost by (roughly) one bit per unit of `t` while doubling the
`beta`-side overhead `2^t`. -/
theorem budgeted_plain_corner_of_slack_tradeoff
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta t : ℕ),
      2 * ((Nat.bits (x.length / 2 ^ t)).length + 1) + 2 * (Nat.bits t).length + c ≤ alpha →
      x.length + 2 ^ t
          + (2 * ((Nat.bits (x.length / 2 ^ t)).length + 1) + 2 * (Nat.bits t).length + c)
          ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := budgeted_plain_corner_of_rounded_length_log V U hV hU
  refine ⟨c, fun x kx baseBudget alpha beta t hAlpha hBudget => ?_⟩
  have hPpos : 0 < 2 ^ t := pow_pos (by norm_num) t
  -- the address cost at the ceiling scale is at most the one at the floor scale
  have hbits : (Nat.bits ((x.length + 2 ^ t - 1) / 2 ^ t)).length
      ≤ (Nat.bits (x.length / 2 ^ t)).length + 1 :=
    (length_natBits_mono (ceilDiv_le_div_add_one x.length t)).trans (length_natBits_succ_le _)
  -- the rounded radius overshoots `l(x)` by less than `2 ^ t`
  have hmul : ((x.length + 2 ^ t - 1) / 2 ^ t) * 2 ^ t ≤ x.length + 2 ^ t - 1 :=
    Nat.div_mul_le_self _ _
  exact hc x kx baseBudget alpha beta t (by omega) (by omega)

/-- **The exact-scale corner (`t = 0`).**  With no rounding at all the radius is
`l(x)` itself and the address cost is the full logarithmic cost of the length:
if `2 * (|bits l(x)| + 1) + c ≤ alpha` and
`l(x) + 1 + (2 * (|bits l(x)| + 1) + c) ≤ kx + beta`, then the exact
budget-scale plain corner holds. -/
theorem budgeted_plain_corner_of_exact_scale
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      2 * ((Nat.bits x.length).length + 1) + c ≤ alpha →
      x.length + 1 + (2 * ((Nat.bits x.length).length + 1) + c) ≤ kx + beta →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget := by
  obtain ⟨c, hc⟩ := budgeted_plain_corner_of_slack_tradeoff V U hV hU
  refine ⟨c, fun x kx baseBudget alpha beta hAlpha hBudget => ?_⟩
  have hbits0 : (Nat.bits 0).length = 0 := by simp
  refine hc x kx baseBudget alpha beta 0 ?_ ?_ <;>
    simp only [pow_zero, Nat.div_one, hbits0, Nat.mul_zero, Nat.add_zero] <;> omega

end Kolmogorov
