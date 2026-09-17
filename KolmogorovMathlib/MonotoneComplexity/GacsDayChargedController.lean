import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailTermination

/-!
# The complete advantage-and-spend controller

The advantage phase is the charged controller already verified in the tail
modules.  On its terminal transition, this controller starts Day's spend
phase.  At most four disjoint batches are run.  A batch is present precisely
for roots whose actual accumulated request is below `alpha / 2`.
-/

namespace Kolmogorov

/-- The phase of the charged controller: collecting an advantage, running spend pass `pass`, or
finished. -/
inductive GrayChargedPhase where
  | advantage
  | spend (pass : Nat)
  | done
deriving DecidableEq

/-- A charged controller state: its phase together with the underlying tail state. -/
structure GrayChargedState (n b : Nat) where
  phase : GrayChargedPhase
  core : GrayTailState n b

/-- The charged controller before the first move: the `advantage` phase over the initial tail
state. -/
def grayChargedInitialState (n b a e : Nat) (A : Allocation) :
    GrayChargedState n b :=
  { phase := .advantage
    core := grayChargedTailInitialState n b a e A }

/-- The threshold a son request must reach to count as served, namely `dyadicScale e` reduced by
the fraction `1 / (6 * halfAmplification q)` of itself. -/
def grayChargedThreshold (q e : Nat) : Rat :=
  dyadicScale e - dyadicScale e / (6 * halfAmplification q)

/-- The charged test of one spend sub-call, at the coarse spend scales. -/
def grayChargedSpendGoalAtB (q L a e pass n : Nat)
    (A : Allocation) (c : FamilyClientMove) (s : FamilyServerMove) : Bool :=
  familyChargedGrayGoalAtB 4 (halfAmplification q)
    (dyadicScale (grayChargedSpendAlphaDepth a))
    ((3 / 4 : Rat) * dyadicScale (grayChargedSpendAlphaDepth a))
    (grayChargedSpendEps a L e pass) (grayChargedSpendDelta a L e pass) n A c s

/-- The move of the spend sub-call in pass `pass`. -/
def grayChargedSpendMove {n b : Nat}
    (_q L a e pass : Nat) (sigma : FamilyStrategyScheme)
    (st : GrayTailState n b) : FamilyClientMove :=
  sigma (grayChargedSpendAlphaDepth a) (grayChargedSpendEps a L e pass)
    st.unavailable st.slots.length st.history

/-- The slots the controller opens in spend pass `pass`: `grayChargedSpendSlots` at the source
count, spend count and threshold of `q, a, e`, i.e. one fresh block of
`grayChargedSpendCount q a e` spare children above the source range for each *deficient* root of
`frozen` -- a root whose request is below `dyadicScale a / 2`.  Roots that are not deficient get
no slot. -/
def grayChargedSlotsForPass {n b : Nat}
    (q a e pass : Nat) (frozen : GrayTailFrozen n b) :
    List (GrayTailSlot n b) :=
  grayChargedSpendSlots (grayChargedSourceCount a e)
    (grayChargedSpendCount q a e) pass (grayChargedThreshold q e)
    (dyadicScale e) (dyadicScale a) frozen

/-- Convert the terminal advantage snapshot to either the first spend pass or
the final state when every root already satisfies H4. -/
def grayChargedStartSpend {n b : Nat}
    (q L a e : Nat) (A : Allocation) (core : GrayTailState n b)
    (sm : FamilyServerMove) : GrayChargedState n b :=
  let slots := grayChargedSlotsForPass q a e 0 core.frozen
  if slots.isEmpty then
    { phase := .done
      core := { core with done := true, slots := [], history := ([], []) } }
  else
    { phase := .spend 0
      core :=
        { core with done := false, slots := slots, history := ([], []),
                    unavailable := A ++ grayHarvest (grayChargedSpendDelta a L e 0) slots n sm } }

/-- Full transition.  The recursive scheme is threaded explicitly in the
definition so every accepted round records the actual recursive move. -/
def grayChargedStep {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedState n b) (sm : FamilyServerMove) :
    GrayChargedState n b :=
  match st.phase with
  | .done => { st with core := { st.core with time := st.core.time + 1 } }
  | .advantage =>
      let next := grayChargedTailStep q L a e sigma A st.core sm
      if next.done then grayChargedStartSpend q L a e A next sm
      else { phase := .advantage, core := next }
  | .spend pass =>
      if st.core.slots.isEmpty then
        { phase := .done
          core := { st.core with time := st.core.time + 1, done := true } }
      else
        let r := st.core.frozen.length
        let epsRound := grayChargedSpendEps a L e pass
        let deltaRound := grayChargedSpendDelta a L e pass
        let current := grayChargedSpendMove q L a e pass sigma st.core
        let localSM := grayTailLocalServerMove deltaRound st.core.slots sm
        if grayChargedSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable current localSM then
          let allocated := grayTailLocalAllocatedList localSM
          let p : GrayTailRound n b :=
            { serverTime := st.core.time
              roundIndex := r
              epsDepth := epsRound
              slots := st.core.slots
              move := current
              allocated := allocated
              unavailable := st.core.unavailable }
          let frozen' := st.core.frozen ++ [p]
          let slotsNext := grayChargedSlotsForPass q a e (pass + 1) frozen'
          let unavailable' := A ++
            grayHarvest (grayChargedSpendDelta a L e (pass + 1)) slotsNext n sm
          let base : GrayTailState n b :=
            { time := st.core.time + 1
              roundStart := st.core.time + 1
              done := false
              frozen := frozen'
              unavailable := unavailable'
              slots := []
              anchoringSlots := []
              history := ([], []) }
          if pass + 1 < 8 then
            let slots := grayChargedSlotsForPass q a e (pass + 1) frozen'
            if slots.isEmpty then
              { phase := .done, core := { base with done := true } }
            else
              { phase := .spend (pass + 1), core := { base with slots := slots } }
          else
            { phase := .done, core := { base with done := true } }
        else
          { phase := .spend pass
            core := { st.core with
              time := st.core.time + 1
              history :=
                (st.core.history.1 ++ [current],
                  st.core.history.2 ++ [localSM]) } }

/-- The charged controller state reached by replaying a history of server moves from the initial
state. -/
def grayChargedFold {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) : GrayChargedState n b :=
  history.foldl (grayChargedStep q L a e sigma A)
    (grayChargedInitialState n b a e A)

/-- The charged client family strategy: it replays the history into a controller state and
displays the frozen requests together with the current move of its phase. -/
def grayChargedStrategy
    (q L a e : Nat) (sigma : FamilyStrategyScheme) : ClientFamilyStrategy :=
  fun A n history =>
    let st : GrayChargedState n
        (ladderBranching (grayTailBaseBranch q L) a e) :=
      grayChargedFold q L a e sigma A history.2
    let current := match st.phase with
      | .done => []
      | .advantage => if st.core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma st.core
      | .spend pass => if st.core.slots.isEmpty then []
        else grayChargedSpendMove q L a e pass sigma st.core
    grayChargedTailFamilyMove (grayChargedSourceCount a e)
      (grayChargedThreshold q e) (dyadicScale e) st.core.frozen
      st.core.slots current

end Kolmogorov
