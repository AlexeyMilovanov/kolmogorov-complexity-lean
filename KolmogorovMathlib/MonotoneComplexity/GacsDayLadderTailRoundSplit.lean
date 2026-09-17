import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFloorArithmetic

/-!
# Keeping the frozen rounds apart: the clamping gain

`GacsDayLadderTailFloorArithmetic.not_aggregatedGrayTailFloorBound` shows that
the coupled hereditary estimate of Section 6.6/6.7 of
the Gacs-Day tail blueprint becomes **false** as soon as the frozen
rounds are collapsed into a single clamped signed term.  This module records
the exact reason, in the form that Section 6.7 has to use.

The controller hands out one signed lower bound per frozen round `r`,

```text
z r = kappa * (2 * selectedRequest r - totalRequest r)   (clamped at 0),
```

and Section 6.6 charges each selected son's owner-round increment, i.e. it
subtracts a nonnegative `w r` from round `r` before clamping.  The elementary
identity

```text
max 0 (z - w) = z - min z w
```

(`max_zero_sub_eq_sub_min`) turns the honest per-round sum into

```text
∑ r, max 0 (z r - w r) = ∑ r, z r - ∑ r, min (z r) (w r),
```

whereas the collapsed form only ever supplies `∑ r, z r - ∑ r, w r`.  The
difference `∑ r, (w r - min (z r) (w r))` is exactly the mass that the
aggregated shortcut throws away, and it is the mass that pays for the
refuting witness: there the whole owner charge sits in a single round whose own
credit is smaller than the charge, so clamping recovers all of the excess.

The final theorem of this file verifies that claim: it exhibits an explicit
cap-consistent numeric round-credit witness realizing the parameters of
`not_aggregatedGrayTailFloorBound`, and checks that the *round-split* credit
plus the reserve credit does reach the target `33`, with margin `1 / 2`.
So the witness that kills the aggregated form is not a counterexample to the
round-split form.

These declarations do not construct a certified execution of the tail controller.
They verify the arithmetic identity and the per-round cap for an abstract numeric
witness; controller realizability remains an explicit hypothesis of the final lemma.
-/

namespace Kolmogorov

open Finset

/-! ### The clamping identity -/

/-- Clamping after subtracting a charge is the same as subtracting only the
part of the charge that the credit can pay. -/
theorem max_zero_sub_eq_sub_min (z w : ℚ) :
    max 0 (z - w) = z - min z w := by
  rcases le_total z w with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-- **The honest per-round sum.**  Summing the clamped, owner-charged round
credits loses only `min (z r) (w r)` in each round. -/
theorem sum_max_zero_sub_eq {ι : Type*} (s : Finset ι) (z w : ι → ℚ) :
    ∑ i ∈ s, max 0 (z i - w i) = (∑ i ∈ s, z i) - ∑ i ∈ s, min (z i) (w i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => max_zero_sub_eq_sub_min (z i) (w i)

/-- **The clamping gain.**  The round-split credit always dominates the
aggregated credit, and the gap is the part of the owner charge that exceeds the
credit of the round it is charged to. -/
theorem sum_max_zero_sub_ge_sub {ι : Type*} (s : Finset ι) (z w : ι → ℚ) :
    (∑ i ∈ s, z i) - (∑ i ∈ s, w i) ≤ ∑ i ∈ s, max 0 (z i - w i) := by
  rw [sum_max_zero_sub_eq s z w, sub_le_sub_iff_left]
  exact Finset.sum_le_sum fun i _ => min_le_right _ _

/-- The clamped sum also dominates the single aggregate positive part. -/
theorem max_zero_sum_le_sum_max_zero {ι : Type*} (s : Finset ι) (z : ι → ℚ) :
    max 0 (∑ i ∈ s, z i) ≤ ∑ i ∈ s, max 0 (z i) :=
  max_le (Finset.sum_nonneg fun _ _ => le_max_left _ _)
    (Finset.sum_le_sum fun _ _ => le_max_right _ _)

/-! ### An explicit cap-consistent numeric witness for the refuting parameters

The parameters of `not_aggregatedGrayTailFloorBound` are `kappa = 2`,
`eps = 1`, `n = 4` outer roots with `B = 4` source sons each; twelve sons carry
`gamma = 15/16` and are resolved, four carry `0` and stay unresolved.  A single
round cannot create a request of `15/16`, because
`grayTailRoundSonBase_le_lastCap` caps one round's increment at
`eps / (12 * kappa) = 1/24`.  The shortest decomposition respecting that cap has
`23` rounds.  We take the increment of each of the twelve resolved sons to be
`1/24` in every round except round `21`, where it is `1/48`; the total is
`22 / 24 + 1 / 48 = 15 / 16`, and the owner (last) round of all twelve sons is
round `22`, contributing the maximal owner increment `1/24` used by the
refutation. -/

/-- The per-son request increment of round `r` in the explicit numeric witness. -/
def refutingIncrement (r : ℕ) : ℚ := if r = 21 then 1 / 48 else 1 / 24

/-- The owner charge of round `r`: twelve sons, each charged `1/24`, all owned
by the last round. -/
def refutingOwnerCharge (r : ℕ) : ℚ := if r = 22 then 12 * (1 / 24) else 0

/-- Every round increment respects the certified one-round cap
`eps / (12 * kappa) = 1/24`. -/
theorem refutingIncrement_le_cap (r : ℕ) : refutingIncrement r ≤ 1 / 24 := by
  unfold refutingIncrement
  split <;> norm_num

/-- The refuting increment of a round is nonnegative. -/
theorem refutingIncrement_nonneg (r : ℕ) : 0 ≤ refutingIncrement r := by
  unfold refutingIncrement
  split <;> norm_num

/-- The numeric increments accumulate the request `15 / 16` of the refutation. -/
theorem sum_refutingIncrement : ∑ r ∈ range 23, refutingIncrement r = 15 / 16 := by
  norm_num [Finset.sum_range_succ, refutingIncrement]

/-- The owner charges really total `12 * (1/24) = 1/2`, the aggregate owner
charge of the refutation. -/
theorem sum_refutingOwnerCharge :
    ∑ r ∈ range 23, refutingOwnerCharge r = 1 / 2 := by
  norm_num [Finset.sum_range_succ, refutingOwnerCharge]

/-- The round credit of round `r` in the refuting witness: `max 0 (2 * (12 * refutingIncrement r) -
2 * 2 * refutingOwnerCharge r)`, the doubled selected increment of the round minus four times
its owner charge, truncated at zero. -/
def refutingRoundCredit (r : ℕ) : ℚ :=
  max 0 (2 * (12 * refutingIncrement r) - 2 * 2 * refutingOwnerCharge r)

/-- **The refuting witness survives the round-split form.**  With the frozen
rounds kept apart, the credit of the explicit numeric witness above plus the reserve
credit `eps * 12` reaches `67 / 2`, which is above the target `33` that the
aggregated form fails to reach (it only reaches `65 / 2`). -/
theorem roundSplit_credit_at_refuting_witness :
    (∑ r ∈ range 23, refutingRoundCredit r) + 1 * 12 = 67 / 2 := by
  norm_num [Finset.sum_range_succ, refutingRoundCredit, refutingIncrement,
    refutingOwnerCharge]

/-- Restated against the target of `not_aggregatedGrayTailFloorBound`:
`kappa' * (3 * alpha + floor) = (5/2) * (3 * 4 + 6/5) = 33`. -/
theorem roundSplit_bound_at_refuting_witness :
    (halfAmplification 2 + 1 / 2) * (3 * 4 + 6 / 5)
      ≤ (∑ r ∈ range 23, refutingRoundCredit r) + 1 * 12 := by
  rw [roundSplit_credit_at_refuting_witness]
  unfold halfAmplification
  norm_num

/-- For contrast, the aggregated credit at the same numeric witness: collapsing the
rounds gives only `41 / 2`, so `41/2 + 12 = 65/2 < 33`.  The gap `1` is exactly
`∑ r, (w r - min (z r) (w r))`, concentrated in the owner round. -/
theorem aggregated_credit_at_refuting_witness :
    max 0 (2 * (12 * ∑ r ∈ range 23, refutingIncrement r) -
        2 * 2 * ∑ r ∈ range 23, refutingOwnerCharge r) + 1 * 12 = 65 / 2 := by
  rw [sum_refutingIncrement, sum_refutingOwnerCharge]
  norm_num


/-! ### The extremal arithmetic family: the round-split constant is exactly right

The witness above is one instance of a one-parameter family of extremal
histories, and computing the family explains why the aggregated form fails and
the round-split form does not.

Fix `eps`, `B` source sons per root, `n` outer roots and select all of them.
Take `d` roots all of whose sons stay unresolved with request `0`, and `n - d`
roots all of whose sons are resolved.  The one-quarter stopping inequality allows
this exactly when `4 * d <= n`.  Give every resolved son the smallest request
that the raise rule converts into `eps`, namely `eps * (1 - 1/(6*kappa))`, and
charge it the maximal owner increment `eps / (12*kappa)`, all owner rounds
being the same last round.  Then

```text
round credits        = kappa * Gamma          = (n - d) * B * eps * (kappa - 1/6),
clamped owner charge =                          (n - d) * B * eps * (1/12),
aggregated charge    =                          (n - d) * B * eps * (1/6),
reserve credit       =                          (n - d) * B * eps,
target               = kappa' * ((n - d) * B * eps) + (3/4) * d * B * eps,
```

using `kappa' * floor = (3/4) * alpha` and `alpha = B * eps`.  The clamped
charge is half the aggregated one because the whole owner charge is
concentrated in a round whose own credit,
`kappa * (n - d) * B * eps/(12*kappa)`, is only half of it.

The three theorems below compute the two credits against the target.  The
round-split surplus is `B * eps * (n - 4*d) / 4`: nonnegative precisely under
the one-quarter stopping rule and **exactly zero** at `n = 4 * d`.  The
aggregated surplus is `B * eps * ((n - d)/6 - 3*d/4)`, which is already
negative there.  So the round-split accounting is not merely convenient, it is
the tightest form that can hold, and the aggregated one cannot be repaired by
any better estimate of the same quantities. -/

/-- The round-split credit `(n - d) * B * eps * (kappa + 3/4)` of the extremal arithmetic
family. -/
def extremalRoundSplitCredit (kappa eps B n d : ℚ) : ℚ :=
  (n - d) * B * eps * (kappa + 3 / 4)

/-- The aggregated credit of the extremal arithmetic family: `(n - d) * B * eps * (kappa + 2 /
3)`. -/
def extremalAggregatedCredit (kappa eps B n d : ℚ) : ℚ :=
  (n - d) * B * eps * (kappa + 2 / 3)

/-- Hereditary target of the same numeric witness, with all roots selected. -/
def extremalTarget (kappa eps B n d : ℚ) : ℚ :=
  (n - d) * B * eps * (kappa + 1 / 2) + 3 / 4 * d * B * eps

/-- The round-split surplus of the extremal arithmetic family is exactly
`B * eps * (n - 4 * d) / 4`. -/
theorem extremalRoundSplitCredit_sub_target (kappa eps B n d : ℚ) :
    extremalRoundSplitCredit kappa eps B n d - extremalTarget kappa eps B n d =
      B * eps * (n - 4 * d) / 4 := by
  unfold extremalRoundSplitCredit extremalTarget
  ring

/-- **The round-split form survives the extremal arithmetic family**, for every
amplification, exactly under the one-quarter stopping rule. -/
theorem extremalTarget_le_roundSplitCredit {kappa eps B n d : ℚ}
    (hB : 0 ≤ B) (heps : 0 ≤ eps) (hd : 4 * d ≤ n) :
    extremalTarget kappa eps B n d ≤ extremalRoundSplitCredit kappa eps B n d := by
  have h := extremalRoundSplitCredit_sub_target kappa eps B n d
  nlinarith [mul_nonneg hB heps, sub_nonneg.mpr hd]

/-- The aggregated surplus of the same numeric witness. -/
theorem extremalAggregatedCredit_sub_target (kappa eps B n d : ℚ) :
    extremalAggregatedCredit kappa eps B n d - extremalTarget kappa eps B n d =
      B * eps * (2 * n - 11 * d) / 12 := by
  unfold extremalAggregatedCredit extremalTarget
  ring

/-- **The aggregated form fails on the extremal arithmetic family** as soon as the
stopping rule is met with equality and something is actually unresolved. -/
theorem extremal_aggregated_lt_target {kappa eps B n d : ℚ}
    (hB : 0 < B) (heps : 0 < eps) (hd : 0 < d) (hn : n = 4 * d) :
    extremalAggregatedCredit kappa eps B n d < extremalTarget kappa eps B n d := by
  have h := extremalAggregatedCredit_sub_target kappa eps B n d
  subst hn
  nlinarith [mul_pos hB heps]

end Kolmogorov
