import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailLayout
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayCharge
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedFamily

/-!
# The designated-gray advantage controller

This is the executable advantage phase of the repaired Gacs-Day induction.
Its state and displayed move are intentionally the established tail controller
ones; only the acceptance test changes.  A round is frozen exactly when the
finite `eta = 4` designated-gray certificate exists.
-/

namespace Kolmogorov

/-- The exact finite charged test used by every recursive advantage call. -/
def grayChargedTailGoalAtB (q e epsRound deltaRound n : Nat)
    (A : Allocation) (c : FamilyClientMove) (s : FamilyServerMove) : Bool :=
  familyChargedGrayGoalAtB 4 (halfAmplification q)
    (dyadicScale (grayCallDepth q e))
    ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
    epsRound deltaRound n A c s

/-- One advantage-phase transition of the charged tail controller.  A waiting state ends
the run once all its anchoring slots are anchored and otherwise restarts the round; a
finished or slotless state only advances the clock; an active state whose current move
meets `grayChargedTailGoalAtB` freezes the round, harvests the next slot candidates and
the new unavailable set, and otherwise records the move in the local history.  Same shape
as `grayTailStep`, with the charged round test in place of the gray one. -/
def grayChargedTailStep {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove) : GrayTailState n b :=
  if grayTailWaitingB st then
    if grayTailAllAnchoredB e A st.anchoringSlots sm then
      { st with
        time := st.time + 1
        roundStart := st.time + 1
        done := true
        slots := []
        history := ([], []) }
    else
      { st with
        time := st.time + 1
        roundStart := st.time + 1
        history := ([], []) }
  else if st.done then { st with time := st.time + 1 }
  else if st.slots.isEmpty then
    { st with time := st.time + 1 }
  else
    let r := st.frozen.length
    let epsRound := grayTailRoundEps q L e r
    let deltaRound := grayTailRoundDelta q L e r
    let current := grayTailCurrentMove q L e sigma st
    let localSM := grayTailLocalServerMove deltaRound st.slots sm
    if grayChargedTailGoalAtB q e epsRound deltaRound st.slots.length
        st.unavailable current localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let frozen' := st.frozen ++
        [{ serverTime := st.time
           roundIndex := r
           epsDepth := epsRound
           slots := st.slots
           move := current
           allocated := allocated
           unavailable := st.unavailable }]
      let threshold := dyadicScale e -
        dyadicScale e / (6 * halfAmplification q)
      let source := grayChargedSourceCount a e
      let candidates := grayTailNextSlots e source frozen'.length threshold A
        frozen' sm
      let unavailable' := A ++
        grayHarvest (grayTailRoundDelta q L e frozen'.length) candidates n sm
      let done' := grayTailGlobalQuarterB source candidates ||
        decide (grayChargedAdvantageRoundCount q <= frozen'.length)
      { time := st.time + 1
        roundStart := st.time + 1
        done := done'
        frozen := frozen'
        unavailable := unavailable'
        slots := candidates
        anchoringSlots := []
        history := ([], []) }
    else
      { st with
        time := st.time + 1
        history :=
          (st.history.1 ++ [current], st.history.2 ++ [localSM]) }

/-- State reconstructed from a finite server history during the advantage
phase. -/
def grayChargedTailFold {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) : GrayTailState n b :=
  history.foldl (grayChargedTailStep q L a e sigma A)
    (grayChargedTailInitialState n b a e A)

/-- The client move displayed in the advantage phase: the grafted tail move
`grayTailOutput` of the underlying gray controller. -/
def grayChargedTailOutput {n b : Nat} (q L a e : Nat)
    (sigma : FamilyStrategyScheme) (st : GrayTailState n b) :
    FamilyClientMove :=
  grayTailOutput q L a e sigma st

/-- The executable advantage strategy before Day's spend phase is attached. -/
def grayChargedAdvantageStrategy
    (q L a e : Nat) (sigma : FamilyStrategyScheme) : ClientFamilyStrategy :=
  fun A n history =>
    let st : GrayTailState n
        (ladderBranching (grayTailBaseBranch q L) a e) :=
      grayChargedTailFold q L a e sigma A history.2
    grayChargedTailOutput q L a e sigma st

/-- The charged tail step unfolded: a terminated state only ticks; otherwise the round is played,
and if it meets its goal it is frozen, the next slots are selected and the tail finishes when
the surviving slots are few or the round budget is spent. -/
lemma grayChargedTailStep_eq {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove) :
    grayChargedTailStep q L a e sigma A st sm =
      if (st.done || st.slots.isEmpty) then { st with time := st.time + 1 }
      else
        let r := st.frozen.length
        let epsRound := grayTailRoundEps q L e r
        let deltaRound := grayTailRoundDelta q L e r
        let current := grayTailCurrentMove q L e sigma st
        let localSM := grayTailLocalServerMove deltaRound st.slots sm
        if grayChargedTailGoalAtB q e epsRound deltaRound st.slots.length
            st.unavailable current localSM then
          let allocated := grayTailLocalAllocatedList localSM
          let frozen' := st.frozen ++
            [{ serverTime := st.time, roundIndex := r, epsDepth := epsRound
               slots := st.slots, move := current, allocated := allocated
               unavailable := st.unavailable }]
          let threshold := dyadicScale e -
            dyadicScale e / (6 * halfAmplification q)
          let source := grayChargedSourceCount a e
          let candidates := grayTailNextSlots e source frozen'.length threshold A
            frozen' sm
          let unavailable' := A ++
            grayHarvest (grayTailRoundDelta q L e frozen'.length) candidates n sm
          { time := st.time + 1, roundStart := st.time + 1
            done := grayTailGlobalQuarterB (n := n) source candidates ||
              decide (grayChargedAdvantageRoundCount q <= frozen'.length)
            frozen := frozen', unavailable := unavailable', slots := candidates
            anchoringSlots := [], history := ([], []) }
        else
          { st with
            time := st.time + 1
            history := (st.history.1 ++ [current],
              st.history.2 ++ [localSM]) } := by
  by_cases hd : st.done = true
  · simp [grayChargedTailStep, grayTailWaitingB, hd]
  · by_cases hs : st.slots.isEmpty = true
    · simp [grayChargedTailStep, grayTailWaitingB, hd, hs]
    · simp [grayChargedTailStep, grayTailWaitingB, hd, hs]

end Kolmogorov
