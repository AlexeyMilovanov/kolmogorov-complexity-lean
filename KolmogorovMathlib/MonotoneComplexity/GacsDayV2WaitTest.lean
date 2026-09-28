import KolmogorovMathlib.MonotoneComplexity.GacsDayV2WaitCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RaisedServed

/-!
# v15 step 2: the raised-service wait exits

Proof document v15.1, A3.  The controller-side test `grayChargedRaisedServedB`
lives in `GacsDayV2RaisedServed` (below the controller); here the run-level
exit is derived from the common service horizon of `GacsDayV2WaitCore`:
unless the outer client wins the positive game, the test of the advantage
terminal succeeds at some time after the advantage exit and stays true.
-/

namespace Kolmogorov

/-- The V2 raised sources of a final replay are the raised slots of the
advantage terminal's frozen ledger (by definition). -/
theorem grayChargedReplayV2RaisedSources_eq
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    grayChargedReplayV2RaisedSources replay =
      grayChargedRaisedSources (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (frozenV1OfV2 replay.advantageTerminal) := rfl

/-- **The wait exits** (v15.1 A3): unless the outer client wins the positive
game, the raised-service test of the advantage terminal succeeds at some time
after the advantage exit, and from then on. -/
theorem grayChargedReplayV2_raisedServedB_of_not_positive
    {q L a e n T : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    ∃ u, T + 1 ≤ u ∧ ∀ v, u ≤ v →
      grayChargedRaisedServedB e (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (frozenV1OfV2 replay.advantageTerminal)
        (sm v) = true := by
  obtain ⟨u0, hu0⟩ := grayChargedReplayV2_raised_all_served_of_not_positive
    (U := T + 1) hsm hnotpos replay le_rfl
  have hu : grayChargedRaisedServedB e (grayChargedSourceCount a e)
      (grayChargedThreshold q e) (frozenV1OfV2 replay.advantageTerminal)
      (sm u0) = true := by
    rw [grayChargedRaisedServedB_eq_true_iff]
    intro z hz
    exact hu0 z hz
  refine ⟨max u0 (T + 1), le_max_right _ _, fun v hv => ?_⟩
  exact grayChargedRaisedServedB_mono_time hsm (le_trans (le_max_left _ _) hv) hu

end Kolmogorov
