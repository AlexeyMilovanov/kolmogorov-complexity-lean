import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvSlots
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailGlobalProgress

/-!
# V2 re-anchored advantage goal and the mass-recovery bridge (Reading C)

Blueprint Stage C2, audit verdict Reading C.  The wide block tests its
acceptance goal at the **round anchor** `ε_r = grayTailRoundEps q L e r`
(α-depth `dyadicScale ε_r`), so every one of the `mult(r)` block roots per
fibre requests `≈ 2^{−ε_r}`; the mass-recovery bridge
`grayAdvBlockMult · dyadicScale ε_r = dyadicScale callDepth` shows the fibre
sum restores the committed call-depth-scale request — which is exactly what
the frozen-tail global-progress contradiction consumes (so Reading C, unlike
the emergent Reading B, keeps that argument alive).

Everything here is standalone (no controller wiring): the goal is a plain
`familyChargedGrayGoalAtB` at the block anchor, and the bridge is arithmetic
on `grayAdvMult_mass`.
-/

namespace Kolmogorov

/-- The re-anchored advantage acceptance goal of round `r`: the charged gray
goal at α-depth `dyadicScale ε_r`, window `(ε_r, ε_r + L]`. -/
def grayChargedBlockGoalAtB (q L e r n : Nat) (A : Allocation)
    (c : FamilyClientMove) (s : FamilyServerMove) : Bool :=
  familyChargedGrayGoalAtB 4 (halfAmplification q)
    (dyadicScale (grayTailRoundEps q L e r))
    ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r))
    (grayTailRoundEps q L e r) (grayTailRoundDelta q L e r) n A c s

/-- Per-root request bounds of an accepted block round, at the block anchor. -/
lemma grayChargedBlockGoalAtB_root_bounds
    {q L e r n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedBlockGoalAtB q L e r n A move server = true)
    (j : Fin n) :
    dyadicScale (grayTailRoundEps q L e r) / 2 ≤ getFamilyReq move j.val [] ∧
      getFamilyReq move j.val [] ≤ dyadicScale (grayTailRoundEps q L e r) := by
  unfold grayChargedBlockGoalAtB at hgoal
  obtain ⟨G, _hGmem, hG⟩ := familyChargedGrayGoalAtB.exists_charge hgoal
  have hj := familyGrayChargeAtB.root hG j.isLt
  exact ⟨hj.1, hj.2.1⟩

/-- The block round's total request lower bound, at the block anchor. -/
lemma grayChargedBlockGoal_totalRequest_lower
    {q L e r n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedBlockGoalAtB q L e r n A move server = true) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r)) ≤
      halfAmplification q * totalRootRequest n move := by
  unfold grayChargedBlockGoalAtB at hgoal
  have hweak := familyChargedGrayGoalAtB.to_familyGrayGoalAtB hgoal
  unfold familyGrayGoalAtB at hweak
  rw [Bool.and_eq_true] at hweak
  exact of_decide_eq_true hweak.2

/-- The block multiplicity equals the multiplicity-lemma form. -/
lemma grayAdvBlockMult_eq (q L e r : Nat) :
    grayAdvBlockMult q L r =
      grayAdvMult (grayCallDepth q e) (grayTailRoundEps q L e r) := by
  unfold grayAdvBlockMult grayAdvMult grayTailRoundEps
  congr 1
  omega

/-- `callDepth ≤ ε_r` (the round anchor is at least the call depth). -/
lemma grayCallDepth_le_roundEps (q L e r : Nat) :
    grayCallDepth q e ≤ grayTailRoundEps q L e r := by
  rw [grayTailRoundEps]; omega

/-- **The mass-recovery bridge** (why Reading C keeps global progress alive):
the `mult(r)` block roots per fibre, each at scale `2^{−ε_r}`, sum to exactly
the committed call-depth-scale request `2^{−grayCallDepth}` per fibre. -/
theorem grayAdvBlock_fibre_mass (q L e r : Nat) :
    (grayAdvBlockMult q L r : Rat) * dyadicScale (grayTailRoundEps q L e r) =
      dyadicScale (grayCallDepth q e) := by
  rw [grayAdvBlockMult_eq q L e r]
  exact grayAdvMult_mass (grayCallDepth_le_roundEps q L e r)

/-- The fibre-summed total request lower bound of a block round recovers the
committed call-depth magnitude: `fibres · (3/4)·dyadicScale callDepth`.  With
`n = fibres · mult(r)` roots and per-root bound at `dyadicScale ε_r`, the block
aggregate is `fibres · (3/4) · dyadicScale callDepth`. -/
theorem grayChargedBlockGoal_fibre_totalRequest_lower
    {q L e r fibres n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hn : (n : Rat) = (fibres : Rat) * grayAdvBlockMult q L r)
    (hgoal : grayChargedBlockGoalAtB q L e r n A move server = true) :
    (fibres : Rat) * ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) ≤
      halfAmplification q * totalRootRequest n move := by
  have hlow := grayChargedBlockGoal_totalRequest_lower hgoal
  have hrw : (n : Rat) * ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r)) =
      (fibres : Rat) * ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) := by
    rw [hn]
    rw [show ((fibres : Rat) * grayAdvBlockMult q L r) *
          ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r)) =
        (fibres : Rat) * ((3 / 4 : Rat) *
          ((grayAdvBlockMult q L r : Rat) * dyadicScale (grayTailRoundEps q L e r))) by ring]
    rw [grayAdvBlock_fibre_mass]
  rw [hrw] at hlow
  exact hlow

end Kolmogorov
