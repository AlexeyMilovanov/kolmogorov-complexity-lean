import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Goal
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSources

/-!
# V2 advantage-source local charge (Stage D1, advantage side)

The advantage analogue of `grayChargedLocalChargeOfSpendGoal`: the designated
gray charge extracted from an accepted **block** advantage round's goal,
living in the per-round window `(ε_r, ε_r + L]` at the block anchor
`ε_r = grayTailRoundEps q L e r`.

`grayChargedBlockGoalAtB` unfolds to `familyChargedGrayGoalAtB 4 κ
(dyadicScale ε_r) ((3/4)·dyadicScale ε_r) ε_r deltaRound …`, so the generic
`exists_charge` extractor applies verbatim; only the scale parameters differ
from the spend side.  In the block architecture the round anchor `ε_r`
coincides with the sub-call's outer scale, so this charge is already anchored
where the §9.2 chase and the export both consume it (export-anchor note).
-/

namespace Kolmogorov

/-- The designated local gray charge of an accepted V2 advantage block round,
extracted from its `grayChargedBlockGoalAtB` witness. -/
noncomputable def grayChargedLocalChargeOfBlockGoal
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    FamilyGrayCharge :=
  (familyChargedGrayGoalAtB.exists_charge h).choose

/-- The extracted advantage charge satisfies the local charged gray goal at
the block scales (`α`-depth `ε_r`, window `(ε_r, deltaRound]`). -/
lemma grayChargedLocalChargeOfBlockGoal_valid
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    familyGrayChargeAtB 4 (halfAmplification q)
        (dyadicScale (grayTailRoundEps q L e r))
        ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r))
        (grayTailRoundEps q L e r) (grayTailRoundDelta q L e r)
        n A c s
        (grayChargedLocalChargeOfBlockGoal h) = true :=
  (familyChargedGrayGoalAtB.exists_charge h).choose_spec.2

/-- The extracted advantage charge is a sublist of the charge universe. -/
lemma grayChargedLocalChargeOfBlockGoal_mem
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    grayChargedLocalChargeOfBlockGoal h ∈
      (familyGrayChargeUniverse n (grayTailRoundDelta q L e r)).sublists :=
  (familyChargedGrayGoalAtB.exists_charge h).choose_spec.1

/-- Every cell of the extracted advantage charge is designated-gray in the
round's window over its owner's allocation. -/
lemma grayChargedLocalChargeOfBlockGoal_cells
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true)
    (z : Nat × BitString) (hz : z ∈ grayChargedLocalChargeOfBlockGoal h) :
    z.1 < n ∧
      z.2 ∈ newGrayCellsList (grayTailRoundEps q L e r)
        (grayTailRoundDelta q L e r) (getFamilyAlloc s z.1 []) A := by
  have hvalid := grayChargedLocalChargeOfBlockGoal_valid h
  unfold familyGrayChargeAtB at hvalid
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hvalid
  have hB := hvalid.1.1.1.1.2
  rw [List.all_eq_true] at hB
  have hz2 := hB z hz
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hz2
  exact hz2

/-- Aggregate mass lower bound (`κ·totalRootRequest ≤ mass`) of the advantage
charge — the ratio-κ corner input. -/
lemma grayChargedLocalChargeOfBlockGoal_mass_lower
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    halfAmplification q * totalRootRequest n c ≤
      grayChargeMass (grayTailRoundDelta q L e r)
        (grayChargedLocalChargeOfBlockGoal h) :=
  (familyGrayChargeAtB.aggregate (grayChargedLocalChargeOfBlockGoal_valid h)).2

/-- Aggregate β lower bound (`n·(3/4)·dyadicScale ε_r ≤ mass`). -/
lemma grayChargedLocalChargeOfBlockGoal_beta_lower
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale (grayTailRoundEps q L e r)) ≤
      grayChargeMass (grayTailRoundDelta q L e r)
        (grayChargedLocalChargeOfBlockGoal h) :=
  (familyGrayChargeAtB.aggregate (grayChargedLocalChargeOfBlockGoal_valid h)).1

/-- **Day's per-element upper bound (5.4), η=4**: the charge mass on any single
root is at most `4·κ·req_i`.  This is the ingredient the block encoding carries
that the de-scoped controller lacked — it caps reserve overlap per root. -/
lemma grayChargedLocalChargeOfBlockGoal_root_upper
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true)
    {i : Nat} (hi : i < n) :
    grayChargeMass (grayTailRoundDelta q L e r)
        (grayChargeAtRoot i (grayChargedLocalChargeOfBlockGoal h)) ≤
      4 * halfAmplification q * getFamilyReq c i [] :=
  (familyGrayChargeAtB.root (grayChargedLocalChargeOfBlockGoal_valid h) hi).2.2

/-- The advantage charge has globally unique owner-tagged cells. -/
lemma grayChargedLocalChargeOfBlockGoal_nodup
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    (grayChargedLocalChargeOfBlockGoal h).Nodup :=
  familyGrayChargeAtB.nodup (grayChargedLocalChargeOfBlockGoal_valid h)

/-- The advantage charge has globally unique cells (owner tag erased). -/
lemma grayChargedLocalChargeOfBlockGoal_cells_nodup
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true) :
    ((grayChargedLocalChargeOfBlockGoal h).map Prod.snd).Nodup :=
  familyGrayChargeAtB.cells_nodup (grayChargedLocalChargeOfBlockGoal_valid h)

/-- Day's hereditary subfamily lower bound (outcome (ii)(c)) for the advantage
charge: no subfamily `I` carries disproportionately little designated mass. -/
lemma grayChargedLocalChargeOfBlockGoal_subfamily
    {q L e r n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedBlockGoalAtB q L e r n A c s = true)
    {I : List Nat} (hI : I ∈ (List.range n).sublists) :
    halfAmplification q *
        (2 * totalRootRequestOnList I c - totalRootRequest n c) ≤
      grayChargeMass (grayTailRoundDelta q L e r)
        ((grayChargedLocalChargeOfBlockGoal h).filter fun z => decide (z.1 ∈ I)) :=
  familyGrayChargeAtB.subfamily (grayChargedLocalChargeOfBlockGoal_valid h) hI

end Kolmogorov
