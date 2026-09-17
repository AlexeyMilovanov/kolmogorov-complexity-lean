import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ProvenanceReduced
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedGoal

/-!
# D5: the V2 charged gray goal of a finished run

From a finished V2 replay at the pinned gap with the server non-positive, the
executable charged gray goal holds at the reserve horizon `U`, certified at
the call's anchor `a` (proof document v15.1, A2′).  No named obligation
remains: the anchored server-resolved datum of v14 (`hSRanch`) is retired.
-/

namespace Kolmogorov

/-- **The V2 charged gray goal at the reserve horizon** (pinned gap), at the
call's anchor `a`. -/
theorem grayChargedV2_chargedGoal_of_replay
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    ∃ U, T + 1 <= U ∧
      familyChargedGrayGoalAtB 4 (halfAmplification (q + 1)) (dyadicScale a)
        ((3 / 4 : Rat) * dyadicScale a) a (e + grayTailNewLoss q L) n A
        (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U) = true := by
  obtain ⟨U, hU, reserves, hmove, hdatumAll, hsrflag, F, hFperm, hFsub,
    hFnodup, hFvalid, hbeta, hreq, hcap, hH4⟩ :=
    grayChargedV2_geometry_of_l5_reduced hsm hpin hae hnotpos replay
  exact ⟨U, hU, grayChargedV2_chargedGoal_of_validity hpin hae replay hmove F
    hFsub hFnodup hFvalid hbeta hreq hcap hH4⟩

end Kolmogorov
