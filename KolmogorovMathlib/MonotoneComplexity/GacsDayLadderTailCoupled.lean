import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRoundSplit

/-!
# From round-indexed credits to a root-indexed balance

Section 6.7 of the Gacs-Day tail blueprint asks for one coupled
finite inequality whose left-hand side is the *round-indexed* owner-charged
credit

```text
∑ r, max 0 (kappa * (z r - w r))    +    eps * (selected reserve count),
```

and whose right-hand side is the *root-indexed* hereditary target

```text
(kappa + 1/2) * (2 * ∑_{i ∈ I} Q i - ∑_i Q i).
```

`GacsDayLadderTailRoundSplit` established the exact clamping identity

```text
∑ r, max 0 (z r - w r) = ∑ r, z r - ∑ r, min (z r) (w r)
```

and showed that the round family may not be collapsed.  This module performs
the next reduction step, and — just as importantly — pins down the *shape* the
reduction must have.

## What is proved

* `sum_max_zero_sub_ge_max_zero_sub` and `sum_max_zero_mul_ge`: given any
  bound `∑ r, min (z r) (w r) ≤ W` on the clamping loss, the round-split credit
  dominates `kappa * max 0 (∑ r, z r - W)`.  The outer `max 0` is free, because
  the round-split credit is a sum of nonnegative terms.
* `grayTail_coupled_of_rootBalance`: with the request identity
  `∑ r, z r = 2 * ∑_{i ∈ I} gamma i - ∑_i gamma i` this reduces the coupled
  hereditary inequality, for one selected subfamily `I`, to a purely
  root-indexed statement in `Q`, `gamma`, the selected reserve count, and the
  single number `W`.
* `rootBalance_of_target_nonpos`: the root-indexed statement is automatic
  whenever the signed target is nonpositive, which is the regime of every
  strongly unbalanced subfamily.
* `owner_charge_le_of_cap`: the certified per-call cap
  `x ≤ eps / (12 * kappa)` turns a per-son owner charge count into
  `kappa * W ≤ eps * count / 12`, the concrete `W` used by the tail.

## What is refuted by the weak numeric interface

`not_signedRootCoupledBound`.  At the level of the currently exposed scalar
hypotheses, it is tempting to drop the outer `max 0` and
work with the signed root-level inequality

```text
(kappa + 1/2) * (2 * ∑_{i ∈ I} Q i - ∑_i Q i)
  ≤ kappa * (2 * ∑_{i ∈ I} gamma i - ∑_i gamma i) + eps * ∑_{i ∈ I} res i,
```

because for `I = univ` that is exactly the estimate the extremal configuration
of `GacsDayLadderTailRoundSplit` meets with equality.  It is **false** for
general `I`.  Four roots, `eps = 1`, `kappa = 2`, every root displaying
`Q i = 3/10`, three roots carrying `gamma = 3/10` and one reserve each, one
root carrying no request and no reserve, and `I` the singleton consisting of
that last root, gives `-3/2 ≤ -9/5`, which is false.  The true credit for that
`I` is `0`, not the negative signed expression: the rounds selected by `I`
carry no selected request, so every clamped round credit vanishes.

The refuting configuration satisfies the displayed floor, threshold, and
one-quarter scalar constraints for `a = e`, hence `B = 1` source son per root.
It is **not** a certified feasible controller history: its unresolved son has
`gamma = 0`, whereas the mandatory first round and
`familyPointwiseGrayAtB` give every participating son a positive lower gain.
Thus the theorem only refutes deleting the positive part from the weak numeric
interface below; a signed argument strengthened by the full controller-history
hypotheses remains logically possible.

The moral for Section 6.7 is the exact analogue of the moral of
`not_aggregatedGrayTailFloorBound` one level up: the nonnegativity of the
round-split credit is not a cosmetic convenience but part of the statement, and
the root-level leaf has to be stated with `max 0` retained, as in
`grayTail_coupled_of_rootBalance`.

## Two candidate constraints on the remaining leaf

The following observations explain why the obvious weak-interface
simplifications do not close `grayTail_coupled_of_rootBalance`.  They are not
kernel-checked impossibility results for full feasible controller histories.

*The owner charge `W` must stay symbolic.*  Replacing `W` by the per-call cap
bound `eps * (selected reserve count) / (12 * kappa)` is safe only for long
histories.  In a one-round history every son carries a request of at most
`dyadicScale (grayCallDepth q e)`, every root therefore displays exactly the
floor, the target is `(3/4) * n * dyadicScale a`, and the reserves pay it
exactly; substituting the maximal cap for `W` destroys that equality.  The leaf
must use both `W ≤ eps * count / (12 * kappa)` (`owner_charge_le_of_cap`) and
`W ≤` selected accumulated request.

*No uniform linear relaxation follows from the weak numeric interface.*  Writing
`max 0 x ≥ lambda * x` for a fixed `lambda ∈ [0,1]` turns the leaf into the
root-level condition

```text
∑ i, max (- psi_lambda i) (psi_lambda i - (11/12) * eps * R i) ≤ 0,
psi_lambda i = (kappa + 1/2) * Q i - (1 - lambda) * kappa * gamma i.
```

The extremal three-quarters configuration of `GacsDayLadderTailRoundSplit`
forces `lambda = 0`, while the four-root configuration refuting
`SignedRootCoupledBound` forces `lambda ≥ 1/6`.  So no single `lambda` works
under only those scalar assumptions.  Whether the full controller-history
hypotheses permit a signed or linearly relaxed route remains part of the
remaining proof.
-/

namespace Kolmogorov

open Finset

/-! ### Scaling a clamped credit -/

/-- A nonnegative factor commutes with the positive part. -/
lemma max_zero_mul_of_nonneg {k u : ℚ} (hk : 0 ≤ k) :
    max 0 (k * u) = k * max 0 u := by
  rcases le_total 0 u with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonneg hk h)]
  · rw [max_eq_left h, max_eq_left (by nlinarith), mul_zero]

/-- A nonnegative factor commutes with a sum of positive parts. -/
lemma sum_max_zero_mul {ι : Type*} (s : Finset ι) (k : ℚ) (hk : 0 ≤ k)
    (u : ι → ℚ) :
    ∑ i ∈ s, max 0 (k * u i) = k * ∑ i ∈ s, max 0 (u i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => max_zero_mul_of_nonneg hk

/-! ### The clamping loss bound gives a nonnegative aggregate credit -/

/-- Any bound `W` on the total clamping loss turns the round-split credit into
the *clamped* aggregate credit.  The outer `max 0` costs nothing because the
round-split credit is a sum of nonnegative terms. -/
theorem sum_max_zero_sub_ge_max_zero_sub {ι : Type*}
    (s : Finset ι) (z w : ι → ℚ) (W : ℚ)
    (hclamp : ∑ i ∈ s, min (z i) (w i) ≤ W) :
    max 0 ((∑ i ∈ s, z i) - W) ≤ ∑ i ∈ s, max 0 (z i - w i) := by
  have hkey : (∑ i ∈ s, z i) - W ≤ ∑ i ∈ s, max 0 (z i - w i) := by
    rw [sum_max_zero_sub_eq s z w]
    linarith
  have hnonneg : (0 : ℚ) ≤ ∑ i ∈ s, max 0 (z i - w i) :=
    Finset.sum_nonneg fun _ _ => le_max_left _ _
  exact max_le hnonneg hkey

/-- The scaled form used by the tail: every frozen round contributes
`max 0 (kappa * (z r - w r))`. -/
theorem sum_max_zero_mul_ge {ι : Type*}
    (s : Finset ι) (kappa : ℚ) (hk : 0 ≤ kappa) (z w : ι → ℚ) (W : ℚ)
    (hclamp : ∑ i ∈ s, min (z i) (w i) ≤ W) :
    kappa * max 0 ((∑ i ∈ s, z i) - W)
      ≤ ∑ i ∈ s, max 0 (kappa * (z i - w i)) := by
  rw [sum_max_zero_mul s kappa hk]
  exact mul_le_mul_of_nonneg_left
    (sum_max_zero_sub_ge_max_zero_sub s z w W hclamp) hk

/-! ### The reduction to a root-indexed balance -/

/-- **Rounds to roots.**  Given

* a bound `W` on the total clamping loss of the owner charges,
* the request identity relating the round-indexed signed credits `z` to the
  selected and total accumulated root requests,
* and the *root-indexed* balance `hbal`,

the coupled hereditary inequality holds for the subfamily `I`.

Nothing about the controller is assumed here: `z`, `w`, `Q`, `gamma` and `res`
are arbitrary rational data, and `hclamp`, `hz`, `hbal` are exactly the three
facts the tail proof has to supply. -/
theorem grayTail_coupled_of_rootBalance
    {ιR ιS : Type*} (rounds : Finset ιR) (roots I : Finset ιS)
    (kappa eps W : ℚ) (hk : 0 ≤ kappa)
    (z w : ιR → ℚ) (Q gamma res : ιS → ℚ)
    (hclamp : ∑ r ∈ rounds, min (z r) (w r) ≤ W)
    (hz : ∑ r ∈ rounds, z r
      = 2 * (∑ i ∈ I, gamma i) - ∑ i ∈ roots, gamma i)
    (hbal : (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i)
      ≤ kappa * max 0 ((2 * (∑ i ∈ I, gamma i) - ∑ i ∈ roots, gamma i) - W)
        + eps * ∑ i ∈ I, res i) :
    (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i)
      ≤ (∑ r ∈ rounds, max 0 (kappa * (z r - w r))) + eps * ∑ i ∈ I, res i := by
  have hcredit := sum_max_zero_mul_ge rounds kappa hk z w W hclamp
  rw [hz] at hcredit
  linarith

/-- The root-indexed balance is automatic on a subfamily whose signed target is
nonpositive; the credit side is always nonnegative. -/
theorem rootBalance_of_target_nonpos
    {ιS : Type*} (roots I : Finset ιS) (kappa eps W : ℚ)
    (hk : 0 ≤ kappa) (heps : 0 ≤ eps) (Q gamma res : ιS → ℚ)
    (hres : ∀ i ∈ I, 0 ≤ res i) (hkk : 0 ≤ kappa + 1 / 2)
    (htarget : 2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i ≤ 0) :
    (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i)
      ≤ kappa * max 0 ((2 * (∑ i ∈ I, gamma i) - ∑ i ∈ roots, gamma i) - W)
        + eps * ∑ i ∈ I, res i := by
  have h1 : (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hkk htarget
  have h2 : (0 : ℚ) ≤
      kappa * max 0 ((2 * (∑ i ∈ I, gamma i) - ∑ i ∈ roots, gamma i) - W) :=
    mul_nonneg hk (le_max_left _ _)
  have h3 : (0 : ℚ) ≤ eps * ∑ i ∈ I, res i :=
    mul_nonneg heps (Finset.sum_nonneg hres)
  linarith

/-- The root-indexed balance is automatic whenever the selected reserve credit
alone already pays the target.  Applying this lemma to short controller
histories still requires a separate theorem deriving that premise from the
actual trace, terminal floor, and stopping rule. -/
theorem rootBalance_of_reserve_credit
    {ιS : Type*} (roots I : Finset ιS) (kappa eps W : ℚ) (hk : 0 ≤ kappa)
    (Q gamma res : ιS → ℚ)
    (h : (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i)
      ≤ eps * ∑ i ∈ I, res i) :
    (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i ∈ roots, Q i)
      ≤ kappa * max 0 ((2 * (∑ i ∈ I, gamma i) - ∑ i ∈ roots, gamma i) - W)
        + eps * ∑ i ∈ I, res i := by
  have h2 : (0 : ℚ) ≤
      kappa * max 0 ((2 * (∑ i ∈ I, gamma i) - ∑ i ∈ roots, gamma i) - W) :=
    mul_nonneg hk (le_max_left _ _)
  linarith

/-! ### The certified per-call cap in the form the balance uses -/

/-- The proved per-call cap `x ≤ eps / (12 * kappa)` on one owner increment
turns a total owner charge over `count` selected sons into the bound
`kappa * W ≤ eps * count / 12`, which is the only way `W` enters
`grayTail_coupled_of_rootBalance`. -/
theorem owner_charge_le_of_cap {kappa eps W count : ℚ}
    (hk : 0 < kappa) (hW : W ≤ count * (eps / (12 * kappa))) :
    kappa * W ≤ eps * count / 12 := by
  have h : kappa * W ≤ kappa * (count * (eps / (12 * kappa))) :=
    mul_le_mul_of_nonneg_left hW hk.le
  have hne : kappa ≠ 0 := ne_of_gt hk
  have hrw : kappa * (count * (eps / (12 * kappa))) = eps * count / 12 := by
    field_simp
  linarith [hrw ▸ h]

/-! ### The signed root-level shortcut is false -/

/-- The signed root-level coupled bound: the reduction of
`grayTail_coupled_of_rootBalance` with the outer `max 0` deleted and `W = 0`.
For `I = univ` this is exactly the estimate that the extremal configuration of
`GacsDayLadderTailRoundSplit` meets with equality, which is why it is
tempting. -/
def SignedRootCoupledBound : Prop :=
  ∀ (n : ℕ) (kappa eps : ℚ) (Q gamma res : Fin n → ℚ),
    2 ≤ kappa → 0 < eps →
    (∀ i, 0 ≤ gamma i) → (∀ i, 0 ≤ res i) → (∀ i, gamma i ≤ Q i) →
    ∀ I : Finset (Fin n),
      (kappa + 1 / 2) * (2 * (∑ i ∈ I, Q i) - ∑ i, Q i)
        ≤ kappa * (2 * (∑ i ∈ I, gamma i) - ∑ i, gamma i)
          + eps * ∑ i ∈ I, res i

/-- **The signed root-level shortcut is false under the weak scalar
hypotheses of `SignedRootCoupledBound`.**  On a subfamily carrying no selected
request the true credit is `0`, while the signed expression is strictly
negative and can fall below the (also negative) target.  This does not rule out
a strengthened statement using the full controller-history invariants. -/
theorem not_signedRootCoupledBound : ¬ SignedRootCoupledBound := by
  intro H
  have h := H 4 2 1
    (fun _ => 3 / 10) ![0, 3 / 10, 3 / 10, 3 / 10] ![0, 1, 1, 1]
    (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    {(0 : Fin 4)}
  revert h
  norm_num [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]

end Kolmogorov
