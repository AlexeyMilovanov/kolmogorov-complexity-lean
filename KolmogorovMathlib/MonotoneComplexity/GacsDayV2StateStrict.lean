import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Goal
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Controller
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Round

/-!
# Strict V2 block controller on `GrayTailRoundV2` (blueprint A3/A6)

The blueprint-faithful wide-block advantage controller: it stores each frozen
round as a `GrayTailRoundV2` (the role-split record `blockAnchor` / `childEps`
/ `fineEnd`), and invokes the child rung at the **schedule-correct** child
scale `childEps = blockAnchor + graySpendSpan (q−1)` (NOT the earlier
`blockAnchor + L` shortcut).  Everything block-structural (slot geometry, the
block goal at `dyadicScale ε_r`, the snapshot harvest) is reused from the
already-proved lemmas — those are record-agnostic.
-/

namespace Kolmogorov

/-- The strict V2 controller state: the clock and the round start, the done flag, the frozen
`GrayTailRoundV2` rounds, the unavailable set, the open slots, the anchoring slots and the
stored game history. -/
structure GrayTailStateV2 (n b : Nat) where
  time : Nat
  roundStart : Nat
  done : Bool
  frozen : List (GrayTailRoundV2 n b)
  unavailable : Allocation
  slots : List (GrayTailSlot n b)
  anchoringSlots : List (GrayTailSlot n b)
  history : FamilyGameHistory

/-- The scale-aligned, schedule-correct current move: the child rung is invoked
at outer anchor `ε_r` (block anchor) with its own bin at
`childEps = ε_r + graySpendSpan (q−1)`. -/
def grayBlockCurrentMoveV2 {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b) : FamilyClientMove :=
  let r := st.frozen.length
  sigma (grayTailRoundEps q L e r)
    (grayTailRoundEps q L e r + graySpendSpan q)
    st.unavailable st.slots.length st.history

/-- The strict V2 wide-block advantage step on `GrayTailRoundV2`. An accepted round records
`blockAnchor = grayTailRoundEps q L e r`, `childEps = blockAnchor + graySpendSpan (q - 1)` and
`fineEnd = blockAnchor + L`, and the quarter test that ends the phase counts source fibres. -/
def grayChargedBlockTailStepV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove) : GrayTailStateV2 n b :=
  if st.done then { st with time := st.time + 1 }
  else if st.slots.isEmpty then { st with time := st.time + 1 }
  else
    let r := st.frozen.length
    let epsRound := grayTailRoundEps q L e r
    let deltaRound := grayTailRoundDelta q L e r
    let current := grayBlockCurrentMoveV2 q L e sigma st
    let localSM := grayTailLocalServerMove deltaRound st.slots sm
    if grayChargedBlockGoalAtB q L e r st.slots.length
        st.unavailable current localSM then
      let allocated := grayTailLocalAllocatedList localSM
      let round : GrayTailRoundV2 n b :=
        { serverTime := st.time
          roundIndex := r
          blockAnchor := epsRound
          childEps := epsRound + graySpendSpan q
          fineEnd := deltaRound
          slots := st.slots
          move := current
          allocated := allocated
          unavailable := st.unavailable }
      let frozen' := st.frozen ++ [round]
      let frozenV1 := frozen'.map GrayTailRoundV2.toV1
      let threshold := dyadicScale e -
        dyadicScale e / (6 * halfAmplification q)
      let source := grayChargedSourceCount a e
      let candidates := grayBlockNextSlots q L e source frozen'.length threshold A
        frozenV1 sm
      let unavailable' := A ++
        grayHarvest (grayTailRoundDelta q L e frozen'.length) candidates n sm
      let done' := grayTailGlobalQuarterB source
          (grayTailNextSlots e source frozen'.length threshold A frozenV1 sm) ||
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

/-- The strict V2 initial state: round 0's whole grandson block. -/
def grayChargedBlockTailInitialStateV2 (n b a e q L : Nat) (A : Allocation) :
    GrayTailStateV2 n b where
  time := 0
  roundStart := 0
  done := false
  frozen := []
  unavailable := A
  slots := grayAdvBlockSlots n b (grayChargedSourceCount a e) q L 0
  anchoringSlots := []
  history := ([], [])

end Kolmogorov
