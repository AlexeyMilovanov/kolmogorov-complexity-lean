import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs

/-!
# V2 schedule: the stage-indexed footprint of the Day-literal ladder

Blueprint v11, Stage A1/A2, checked against §9.0 item 4 of the v14 proof
document.

The pinned ladder's per-stage footprint `fp` is output-indexed to match the
live tail step (`ChargedGrayRung q L → ChargedGrayRung (q+1)
(grayTailNewLoss q L)`): the stage-`j` rung consumes the per-round budget
`L = fp (j−1)` and exports depth `a + fp j`.  The seed `fp 2 = 3` is the
stage-2 base rung's exported loss (`e = a` there, so `D − a = D − e = 3`);
the values below the seed are set to the seed and never used (every
producer and consumer carries the domain hypothesis `3 ≤ j`).

The committed `D − e` ladder (`canonicalGrayLoss`, coefficient 256) is
LEGACY: it keeps feeding the universal spec during the migration, its
values diverge from the pinned chain starting at stage 3
(`canonicalGrayLoss 3 = 7680 ≠ 7707 = fp 3`), and it is deleted together
with the universal spec at Stage E.
-/

namespace Kolmogorov

/-- The stage-indexed footprint of the pinned ladder:
`fp 2 = 3`, `fp j = (256·j² + 8)·fp (j−1) + 256·j + 3` for `j ≥ 3`. -/
def grayFootprint : Nat → Nat
  | 0 => 3
  | 1 => 3
  | 2 => 3
  | (j + 3) => (256 * (j + 3) ^ 2 + 8) * grayFootprint (j + 2)
      + 256 * (j + 3) + 3

/-- The footprint of the second stage of the schedule is `3`. -/
@[simp] lemma grayFootprint_two : grayFootprint 2 = 3 := rfl

/-- The footprint of the third stage of the schedule is `7707`. -/
lemma grayFootprint_three : grayFootprint 3 = 7707 := by
  change (256 * 3 ^ 2 + 8) * grayFootprint 2 + 256 * 3 + 3 = 7707
  norm_num

/-- The closed-form step, valid from the seed upward. -/
lemma grayFootprint_succ {j : Nat} (hj : 2 ≤ j) :
    grayFootprint (j + 1) =
      (256 * (j + 1) ^ 2 + 8) * grayFootprint j + 256 * (j + 1) + 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rfl

/-- The step in the `8L + 3 + newLoss` form the schedule uses. -/
lemma grayFootprint_succ_newLoss {j : Nat} (hj : 2 ≤ j) :
    grayFootprint (j + 1) =
      8 * grayFootprint j + 3 + grayTailNewLoss j (grayFootprint j) := by
  rw [grayFootprint_succ hj, grayTailNewLoss_eq]
  ring

/-- The spend span of the stage-`j` rung: eight anchor-hugging spend
windows of width `fp (j−1)` plus the `+3` offset.  Meaningful for
`j ≥ 3`. -/
def graySpendSpan (j : Nat) : Nat := 8 * grayFootprint (j - 1) + 3

/-- The `D − e` loss of the stage-`j` rung's children (the stage-`(j−1)`
rungs at budget `fp (j−2)`).  Meaningful for `j ≥ 4`. -/
def grayChildLoss (j : Nat) : Nat :=
  grayTailNewLoss (j - 2) (grayFootprint (j - 2))

/-- **The nesting theorem** (blueprint A1, exact): a stage-`j` rung's child
occupies exactly its round window — spend span plus child loss equals the
parent's per-round budget `fp (j−1)`. -/
theorem graySpendSpan_add_childLoss {j : Nat} (hj : 4 ≤ j) :
    graySpendSpan (j - 1) + grayChildLoss j = grayFootprint (j - 1) := by
  unfold graySpendSpan grayChildLoss
  have h2 : 2 ≤ j - 2 ∨ j = 4 := by omega
  have hstep := grayFootprint_succ_newLoss (j := j - 2) (by omega)
  have hidx : j - 2 + 1 = j - 1 := by omega
  rw [hidx] at hstep
  have hidx2 : j - 1 - 1 = j - 2 := by omega
  rw [hidx2]
  omega

/-- **The bridge identity** (blueprint A2): the stage-`j` pinned rung at
budget `L = fp (j−1)` and anchor `a` exports depth exactly `a + fp j`:
`(a + 8L + 3) + grayTailNewLoss (j−1) L = a + fp j`. -/
theorem grayFootprint_bridge {j a : Nat} (hj : 3 ≤ j) :
    (a + 8 * grayFootprint (j - 1) + 3) +
        grayTailNewLoss (j - 1) (grayFootprint (j - 1)) =
      a + grayFootprint j := by
  have hstep := grayFootprint_succ_newLoss (j := j - 1) (by omega)
  have hidx : j - 1 + 1 = j := by omega
  rw [hidx] at hstep
  omega

/-- **The budget fit check** (blueprint A2): the below-`e` consumption of
the advantage schedule — the reserve layer plus the `N − 8` used rounds —
fits inside the frozen `grayTailNewLoss`; the difference is the aggregate
unused capacity (a fit check only; no endpoint claim). -/
theorem grayTailNewLoss_fit (q L : Nat) :
    Nat.size (3 * q + 5) + 2 + (grayTailRoundCount q - 8) * L ≤
      grayTailNewLoss q L := by
  rw [grayTailNewLoss_eq, grayTailRoundCount]
  have hsize : Nat.size (3 * q + 5) ≤ 3 * q + 5 := Nat.size_le.mpr
    (Nat.lt_two_pow_self)
  have hcount : (256 * (q + 1) ^ 2 - 8) * L ≤ 256 * (q + 1) ^ 2 * L :=
    Nat.mul_le_mul_right L (by omega)
  nlinarith [sq_nonneg (q + 1), Nat.zero_le L]

end Kolmogorov
