import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSources

/-!
# V2 spend-source local charge

Blueprint / plan XIII, roomy-conjunct residual R1 (proof doc v14 §9.4): the
committed source ledger (`grayChargedFrozenSources`) filters to the fine
(advantage) rounds via `hfineAll`, so the spend rounds' gray is not counted
— but the corner needs it (XII.7).  This module supplies the spend analogue
of `grayChargedLocalChargeOfGoal`: the charge extracted from an accepted
spend round's goal, living in the window `(spendEps, spendEps+L]` with
`spendEps ≤ e`.

`grayChargedSpendGoalAtB` and the fine `grayChargedTailGoalAtB` both unfold
to `familyChargedGrayGoalAtB`, so the generic `exists_charge` extractor
applies to both; only the scale parameters differ (spend uses α-depth
`a+3` = `grayChargedSpendAlphaDepth a`, gray window
`(spendEps, spendDelta]`).

Nothing here touches the committed chain or the fine ledger; it is a new
component to be aggregated beside the fine sources in the corner assembly
(residual R5).
-/

namespace Kolmogorov

/-- The designated local gray charge of an accepted spend round, extracted
from its `grayChargedSpendGoalAtB` witness. -/
noncomputable def grayChargedLocalChargeOfSpendGoal
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true) :
    FamilyGrayCharge :=
  (familyChargedGrayGoalAtB.exists_charge h).choose

/-- The extracted spend charge satisfies the local charged gray goal at the
spend scales (`α`-depth `a+3`, window `(spendEps, spendDelta]`). -/
lemma grayChargedLocalChargeOfSpendGoal_valid
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true) :
    familyGrayChargeAtB 4 (halfAmplification q)
        (dyadicScale (grayChargedSpendAlphaDepth a))
        ((3 / 4 : Rat) * dyadicScale (grayChargedSpendAlphaDepth a))
        (grayChargedSpendEps a L e pass) (grayChargedSpendDelta a L e pass)
        m A c s
        (grayChargedLocalChargeOfSpendGoal h) = true :=
  (familyChargedGrayGoalAtB.exists_charge h).choose_spec.2

/-- The local spend charge of an accepted spend round of the final replay, at the round's own
scales. It is defined for the coarse rounds, those with `¬ grayCallDepth q e ≤ p.epsDepth`,
which are exactly the spend rounds the fine ledger excludes. -/
noncomputable def grayChargedSpendRoundCharge
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : List.Mem p
      (grayChargedRunState q L a e n sigma A sm t).core.frozen)
    (hcoarse : ¬ grayCallDepth q e ≤ p.epsDepth) :
    FamilyGrayCharge :=
  grayChargedLocalChargeOfSpendGoal
    (Classical.choose_spec
      (grayChargedStateAt_frozen_spend_goal hp hcoarse)).2.2

/-- **Roomy residual R3: the spend-source mass lower bound.**  The gray
mass of an accepted spend round's local charge is at least `κ_q` times the
displayed spend request `totalRootRequest`, at the spend fine end
`spendDelta`.  This is the spend twin of the fine `recursive_lower`, read
straight off the `familyGrayChargeAtB` aggregate clause. -/
lemma grayChargedLocalChargeOfSpendGoal_mass_lower
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true) :
    halfAmplification q * totalRootRequest m c ≤
      grayChargeMass (grayChargedSpendDelta a L e pass)
        (grayChargedLocalChargeOfSpendGoal h) :=
  (familyGrayChargeAtB.aggregate
    (grayChargedLocalChargeOfSpendGoal_valid h)).2

/-- The spend charge's aggregate `β`-bound, likewise, for the beta side of
the corner. -/
lemma grayChargedLocalChargeOfSpendGoal_beta_lower
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true) :
    (m : Rat) * ((3 / 4 : Rat) * dyadicScale (grayChargedSpendAlphaDepth a)) ≤
      grayChargeMass (grayChargedSpendDelta a L e pass)
        (grayChargedLocalChargeOfSpendGoal h) :=
  (familyGrayChargeAtB.aggregate
    (grayChargedLocalChargeOfSpendGoal_valid h)).1

/-- **Day's per-element upper bound (5.4), η=4**, for the spend charge: mass on
any single root ≤ `4·κ·req_i`. -/
lemma grayChargedLocalChargeOfSpendGoal_root_upper
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true)
    {i : Nat} (hi : i < m) :
    grayChargeMass (grayChargedSpendDelta a L e pass)
        (grayChargeAtRoot i (grayChargedLocalChargeOfSpendGoal h)) ≤
      4 * halfAmplification q * getFamilyReq c i [] :=
  (familyGrayChargeAtB.root (grayChargedLocalChargeOfSpendGoal_valid h) hi).2.2

/-- Hereditary subfamily lower bound for the spend charge. -/
lemma grayChargedLocalChargeOfSpendGoal_subfamily
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true)
    {I : List Nat} (hI : I ∈ (List.range m).sublists) :
    halfAmplification q *
        (2 * totalRootRequestOnList I c - totalRootRequest m c) ≤
      grayChargeMass (grayChargedSpendDelta a L e pass)
        ((grayChargedLocalChargeOfSpendGoal h).filter fun z => decide (z.1 ∈ I)) :=
  familyGrayChargeAtB.subfamily (grayChargedLocalChargeOfSpendGoal_valid h) hI

/-- The spend charge has globally unique owner-tagged cells. -/
lemma grayChargedLocalChargeOfSpendGoal_nodup
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true) :
    (grayChargedLocalChargeOfSpendGoal h).Nodup :=
  familyGrayChargeAtB.nodup (grayChargedLocalChargeOfSpendGoal_valid h)

/-- The spend charge has globally unique cells (owner tag erased). -/
lemma grayChargedLocalChargeOfSpendGoal_cells_nodup
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true) :
    ((grayChargedLocalChargeOfSpendGoal h).map Prod.snd).Nodup :=
  familyGrayChargeAtB.cells_nodup (grayChargedLocalChargeOfSpendGoal_valid h)

/-- Every cell of the spend charge is designated-gray in the spend window over
its owner's allocation. -/
lemma grayChargedLocalChargeOfSpendGoal_cells
    {q L a e pass m : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (h : grayChargedSpendGoalAtB q L a e pass m A c s = true)
    (z : Nat × BitString) (hz : z ∈ grayChargedLocalChargeOfSpendGoal h) :
    z.1 < m ∧
      z.2 ∈ newGrayCellsList (grayChargedSpendEps a L e pass)
        (grayChargedSpendDelta a L e pass) (getFamilyAlloc s z.1 []) A := by
  have hvalid := grayChargedLocalChargeOfSpendGoal_valid h
  unfold familyGrayChargeAtB at hvalid
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hvalid
  have hB := hvalid.1.1.1.1.2
  rw [List.all_eq_true] at hB
  have hz2 := hB z hz
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hz2
  exact hz2

end Kolmogorov
