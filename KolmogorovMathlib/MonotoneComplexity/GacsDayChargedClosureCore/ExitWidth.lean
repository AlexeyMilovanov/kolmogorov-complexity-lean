import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFrontierDefs
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderCode
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailGlobalProgress
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.TailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore.FinalReplay

/-!
# How wide the charged run is when it leaves a phase

`grayChargedTailStep_width_or_roundCount_of_done` splits the two reasons a tail step can finish
a tail — the width has been exhausted or the round budget has — and
`grayCharged_advantage_exit_terminal_width` bounds the slots that survive the exit from the
`advantage` phase. `grayChargedFinalReplayOfFinal` assembles the certified controller facts at
such a time into the full final replay record used by the closure argument.
-/

namespace Kolmogorov

/-- A tail step that finishes the tail does so for one of the two reasons the construction
allows: the surviving slots number at most a quarter of `n * grayChargedSourceCount a e`, or
the advantage round budget `grayChargedAdvantageRoundCount q` is exhausted. -/
lemma grayChargedTailStep_width_or_roundCount_of_done {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (m : FamilyServerMove)
    (hactive : st.done = false)
    (hdone : (grayChargedTailStep q L a e sigma A st m).done = true) :
    4 * (grayChargedTailStep q L a e sigma A st m).slots.length <=
        n * grayChargedSourceCount a e ∨
      grayChargedAdvantageRoundCount q <=
        (grayChargedTailStep q L a e sigma A st m).frozen.length := by
  rw [grayChargedTailStep_eq] at hdone ⊢
  by_cases hslots : st.slots.isEmpty = true
  · simp [hactive, hslots] at hdone
  · simp only [Bool.not_eq_true] at hslots
    by_cases hgoal : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
    · rw [if_neg (by simp [hactive, hslots]), if_pos hgoal] at hdone ⊢
      dsimp only at hdone ⊢
      rcases Bool.or_eq_true _ _ |>.mp hdone with h | h
      · exact Or.inl ((grayTailGlobalQuarterB_eq_true_iff _ _).mp h)
      · exact Or.inr (by simpa using h)
    · simp [hactive, hslots, hgoal] at hdone

/-- When the run leaves the `advantage` phase at time `t`, the slots surviving that step number
at most a quarter of `n * grayChargedSourceCount a e`. -/
lemma grayCharged_advantage_exit_terminal_width
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hbefore :
      (grayChargedRunState q L a e n sigma A sm t).phase = .advantage)
    (hafter :
      (grayChargedRunState q L a e n sigma A sm (t + 1)).phase ≠
        .advantage) :
    4 * (grayChargedTailStep q L a e sigma A
        (grayChargedRunState q L a e n sigma A sm t).core (sm t)).slots.length
      <= n * grayChargedSourceCount a e := by
  have hdone := grayCharged_advantage_exit_terminal_done hbefore hafter
  have hactive := grayChargedRunState_core_done_false_of_advantage hbefore
  rcases grayChargedTailStep_width_or_roundCount_of_done q L a e sigma A _ (sm t) hactive hdone with
    h | h
  · exact h
  · have hcore := grayChargedStateAt_core_eq_tailStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t hbefore
    rw [hcore] at h ⊢
    rw [← grayChargedTailStateAt_succ] at h ⊢
    rw [grayChargedTail_slots_eq_nil_of_roundCount_stateAt_global h]
    simp

open Classical in
/-- Section 3.3: the full final replay record, built from the certified
controller facts. -/
noncomputable def grayChargedFinalReplayOfFinal
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hfinal : GrayChargedFinalAt q L a e n sigma A sm T) :
    GrayChargedFinalReplay q L a e n sigma A sm T :=
  let hexit := grayChargedFinalAt_advantage_exit hfinal
  { final := hfinal
    successor_done := grayChargedFinalAt_successor_done hfinal
    successor_frozen_extends :=
      grayChargedStateAt_succ_frozen_prefix q L a e sigma A sm T
    frozen_serverTime_le := fun p hp =>
      Nat.lt_succ_iff.mp
        (grayChargedStateAt_frozen_serverTime_lt q L a e sigma A sm (T + 1)
          p hp)
    frozen_alloc_subset_late := fun U hU p hp =>
      grayChargedStateAt_frozen_alloc_subset_late q L a e sigma A sm hsm
        (T + 1) U hU p hp
    done_stable := grayChargedFinalAt_done_stable hfinal
    move_stable := grayChargedFinalAt_move_stable hfinal
    advantageExitTime := hexit.choose
    advantageExit_le := hexit.choose_spec.1
    advantage_before := hexit.choose_spec.2.1
    advantage_after := hexit.choose_spec.2.2
    advantageTerminal := grayChargedTailStep q L a e sigma A
      (grayChargedRunState q L a e n sigma A sm hexit.choose).core
      (sm hexit.choose)
    advantageTerminal_eq := rfl
    terminal_width := grayCharged_advantage_exit_terminal_width
      hexit.choose_spec.2.1 hexit.choose_spec.2.2 }

end Kolmogorov
