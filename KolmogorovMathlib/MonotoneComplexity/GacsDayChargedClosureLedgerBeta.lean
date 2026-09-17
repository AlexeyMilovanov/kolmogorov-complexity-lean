import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureLedgerRequest

/-!
# The reserve half of the charged final charge: mass arithmetic

This file supplies the two purely quantitative facts about the *reserve*
ledger of the charged final charge that are independent of the still open
source-reserve collision control.

* `grayChargeMass_grayChargeAtRoot_reserveCharge` splits the reserve charge
  over outer roots: because every cell of one reserve contribution is owned by
  the root of its coordinate, the fibre of the flattened reserve charge at a
  root is exactly the concatenation of the contributions sitting at that root.
  Together with the per-reserve upper bound this bounds the reserve half of the
  H5 per-root cap by the number of reserves at that root times one coarse unit.

* `grayCharged_aggregate_beta_of_reserve_mass` is the H2 (`aggregate_beta`)
  field of `GrayChargedChargeProvenance`, obtained from the exact reserve mass
  alone: if the reserve ledger carries one unit `dyadicScale e` per resolved
  source and at least three quarters of the `n * 2 ^ (e - a)` sources are
  resolved, then the total mass of the final charge already exceeds
  `n * (3 / 4) * dyadicScale a`.  No source contribution is needed, only its
  nonnegativity.
-/

namespace Kolmogorov

/-! ## List arithmetic -/

/-- Summing a constant over the elements selected by a Boolean predicate. -/
lemma sum_map_ite_const_rat {alpha : Type _} (l : List alpha)
    (p : alpha -> Bool) (C : Rat) :
    (l.map fun x => if p x = true then C else 0).sum =
      ((l.countP p : Nat) : Rat) * C := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : p x = true
      · simp only [h, Nat.cast_add, Nat.cast_one, if_pos]
        ring
      · simp [h]

/-! ## The per-root fibres of the reserve ledger -/

/-- **Per-root split of the reserve charge.**  Each reserve contribution is
owned by the root of its coordinate, so the fibre of the flattened reserve
charge at a root collects exactly the contributions of that root. -/
lemma grayChargeMass_grayChargeAtRoot_reserveCharge
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) (i : Nat) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveCharge reserves)) =
      (reserves.map fun r =>
        if r.coordinate.1.val = i then
          grayChargeMass (e + grayTailNewLoss q L) r.cells else 0).sum := by
  rw [grayChargedReserveCharge, grayChargeAtRoot_flatMap, grayChargeMass_flatMap]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro r _
  rw [grayChargeAtRoot_of_single_owner r.cells_owner]
  by_cases h : r.coordinate.1.val = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, grayChargeMass_nil]

/-- **Reserve half of the H5 per-root cap, geometric form.**  The reserve mass
displayed at one outer root is at most one root scale per reserve sitting at
that root. -/
lemma grayChargedReserveCharge_perRoot_mass_le
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) (i : Nat) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveCharge reserves)) <=
      ((reserves.countP fun r => decide (r.coordinate.1.val = i) : Nat) : Rat) *
        dyadicScale a := by
  rw [grayChargeMass_grayChargeAtRoot_reserveCharge,
    ← sum_map_ite_const_rat reserves (fun r => decide (r.coordinate.1.val = i))
      (dyadicScale a)]
  refine List.sum_le_sum ?_
  intro r _
  by_cases h : r.coordinate.1.val = i
  · simp only [h, decide_true, if_true]
    exact r.root_upper
  · simp [h]

/-! ## H2 for the final charge -/

/-- Rescaling one dyadic scale to a coarser one. -/
lemma dyadicScale_eq_pow_sub_mul {a e : Nat} (hae : a <= e) :
    dyadicScale a = ((2 ^ (e - a) : Nat) : Rat) * dyadicScale e := by
  obtain ⟨k, rfl⟩ : exists k, e = a + k := ⟨e - a, by omega⟩
  simp only [Nat.add_sub_cancel_left, dyadicScale, pow_add]
  push_cast
  rw [show (2:Rat) ^ k * ((1 / 2) ^ a * (1 / 2) ^ k)
      = ((2:Rat) * (1/2)) ^ k * (1/2) ^ a by rw [mul_pow]; ring]
  norm_num

/-- Three quarters of the sources, each carrying one coarse unit, already
exceed the aggregate beta target. -/
lemma grayCharged_aggregate_beta_arith
    {a e n card : Nat} (hae : a <= e)
    (hthree : 3 * (n * grayChargedSourceCount a e) <= 4 * card) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <= (card : Rat) * dyadicScale e := by
  have hpos : (0 : Rat) < dyadicScale e := by unfold dyadicScale; positivity
  rw [dyadicScale_eq_pow_sub_mul (e := e) hae]
  have h : (3 : Rat) * ((n : Rat) * ((2 ^ (e - a) : Nat) : Rat)) <=
      4 * (card : Rat) := by
    have h' := hthree
    unfold grayChargedSourceCount at h'
    exact_mod_cast h'
  nlinarith [hpos]

/-- **H2 (`aggregate_beta`) for the charged final charge.**  If the final
charge splits into a recursive half and a reserve half carrying exactly one
coarse unit per resolved source, and at least three quarters of the
`n * 2 ^ (e - a)` sources are resolved, then its total mass meets the aggregate
beta target.  Only nonnegativity of the recursive half is used. -/
theorem grayCharged_aggregate_beta_of_reserve_mass
    {d a e n card : Nat} {S R F : FamilyGrayCharge}
    (hae : a <= e)
    (hR : grayChargeMass d R = (card : Rat) * dyadicScale e)
    (hthree : 3 * (n * grayChargedSourceCount a e) <= 4 * card)
    (hF : grayChargeMass d F = grayChargeMass d S + grayChargeMass d R) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <= grayChargeMass d F := by
  rw [hF, hR]
  have h1 := grayCharged_aggregate_beta_arith (n := n) hae hthree
  have h2 := grayChargedChargeMass_nonneg d S
  linarith

end Kolmogorov
