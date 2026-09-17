import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part01

/-!
# The replay record of a finished V2 run

`GrayChargedFinalReplayV2` collects, in a form independent of the service horizon, everything the
closure argument needs to know about a finished V2 charged run, and
`grayChargedFinalReplayV2OfFinal` builds that record from the certified controller facts
available at a final time.
-/

namespace Kolmogorov

/-- The replay record of a finished V2 charged run, independent of the service horizon: the terminal
width is the mult-scaled wide form, and two exit times are recorded, `advantageExitTime`, the
last advantage time at which pass 0 takes its snapshot, and `advantageDoneTime ≤
advantageExitTime`, the advantage terminal at which the terminal slots and the source
classification are read. -/
structure GrayChargedFinalReplayV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (T : Nat) : Type where
  final : GrayChargedFinalAtV2 q L a e n sigma A sm T
  successor_done :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).phase = .done
  successor_frozen_extends :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T).core.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen
  frozen_serverTime_le : forall p,
    p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen ->
      p.serverTime <= T
  frozen_alloc_subset_late : forall U, T + 1 <= U -> forall p,
    p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen ->
      allocationSubset p.allocated
        (grayTailLocalAllocatedList
          (grayTailLocalServerMove p.fineEnd p.slots (sm U)))
  done_stable : forall U, T + 1 <= U ->
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).phase = .done ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen =
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen
  move_stable : forall U, T + 1 <= U ->
    grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T
  advantageExitTime : Nat
  advantageExit_le : advantageExitTime <= T
  advantage_before :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm advantageExitTime).phase = .advantage
  advantage_after :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (advantageExitTime + 1)).phase ≠ .advantage
  advantageTerminal : GrayTailStateV2 n (grayTailBranch q L a e)
  advantageTerminal_eq : advantageTerminal =
    grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm advantageExitTime).core
      (sm advantageExitTime)
  terminal_width :
    4 * advantageTerminal.slots.length <=
      n * grayChargedSourceCount a e *
        (grayAdvBlockGrandsons (grayTailBranch q L a e) q L
          advantageTerminal.frozen.length).length
  advantageDoneTime : Nat
  advantageDone_le : advantageDoneTime <= advantageExitTime
  advantageDone_before :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm advantageDoneTime).phase = .advantage
  advantageDone_active :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm advantageDoneTime).core.done = false
  advantageDone_step :
    (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm advantageDoneTime).core
      (sm advantageDoneTime)).done = true
  advantageTerminal_slots_eq : advantageTerminal.slots =
    (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm advantageDoneTime).core
      (sm advantageDoneTime)).slots
  advantageTerminal_frozen_eq : advantageTerminal.frozen =
    (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm advantageDoneTime).core
      (sm advantageDoneTime)).frozen

open Classical in
/-- The V2 final replay record, built from the certified controller facts. -/
noncomputable def grayChargedFinalReplayV2OfFinal
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    GrayChargedFinalReplayV2 q L a e n sigma A sm T :=
  let hexit := grayChargedFinalAtV2_advantage_exit hfinal
  let hdone := grayChargedV2_exit_done_time q L a e sigma A sm hexit.choose
    hexit.choose_spec.2.1 hexit.choose_spec.2.2
  { final := hfinal
    successor_done := grayChargedFinalAtV2_successor_done hfinal
    successor_frozen_extends :=
      grayChargedRunStateV2_frozen_prefix_succ q L a e sigma A sm T
    frozen_serverTime_le := fun p hp =>
      Nat.lt_succ_iff.mp
        (grayChargedRunStateV2_frozen_serverTime_lt q L a e sigma A sm (T + 1)
          p hp)
    frozen_alloc_subset_late := fun U hU p hp =>
      grayChargedRunStateV2_frozen_alloc_subset_late q L a e sigma A sm hsm
        (T + 1) U hU p hp
    done_stable := grayChargedFinalAtV2_done_stable hfinal
    move_stable := grayChargedFinalAtV2_move_stable hfinal
    advantageExitTime := hexit.choose
    advantageExit_le := hexit.choose_spec.1
    advantage_before := hexit.choose_spec.2.1
    advantage_after := hexit.choose_spec.2.2
    advantageTerminal := grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm hexit.choose).core
      (sm hexit.choose)
    advantageTerminal_eq := rfl
    terminal_width := grayChargedV2_advantage_exit_terminal_width
      hexit.choose_spec.2.1 hexit.choose_spec.2.2
    advantageDoneTime := hdone.choose
    advantageDone_le := hdone.choose_spec.1
    advantageDone_before := hdone.choose_spec.2.1
    advantageDone_active := hdone.choose_spec.2.2.1
    advantageDone_step := hdone.choose_spec.2.2.2.1
    advantageTerminal_slots_eq := hdone.choose_spec.2.2.2.2.1
    advantageTerminal_frozen_eq := hdone.choose_spec.2.2.2.2.2 }

end Kolmogorov
