import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendPhase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ProgressBase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RaisedServed

/-!
# The complete V2 advantage-and-spend controller (blueprint C4, wrapper)

Strict mirror of `grayChargedStep` on the V2 block core: the advantage phase
is the certified V2 wide-block tail controller; on its terminal transition
the controller enters the **raised-service wait** (proof document v15.1, A3):
it keeps the phase tag `.advantage` over the terminal (done) core — whose
strict step only ticks the clock, so the displayed move is the terminal
display with the SUV-raised requests — until every raised source son is
served at scale `2^-e` (`grayChargedRaisedServedB`), and only then starts
the spend phase with the C1 block multiplicities (`grayBlockSpendSlotsV2`)
and pass 0's harvest taken at the wait exit; at most eight passes run, each
freezing a `GrayTailRoundV2` whose `blockAnchor` is the pass anchor and whose
`childEps = blockAnchor + graySpendSpan q` (schedule-correct).  The waiting
state is the marker `phase = .advantage ∧ core.done = true` (the phase type
is shared with the V1 controller).
-/

namespace Kolmogorov

/-- The V2 charged state: a phase tag over the V2 block core. -/
structure GrayChargedStateV2 (n b : Nat) where
  phase : GrayChargedPhase
  core : GrayTailStateV2 n b

/-- Initial V2 charged state: the advantage phase over round 0's wide block. -/
def grayChargedInitialStateV2 (n b a e q L : Nat) (A : Allocation) :
    GrayChargedStateV2 n b :=
  { phase := .advantage
    core := grayChargedBlockTailInitialStateV2 n b a e q L A }

/-- The V2 spend slots of pass `pass`, read off the projected frozen ledger. -/
def grayChargedSlotsForPassV2 {n b : Nat}
    (q L a e pass : Nat) (frozen : List (GrayTailRoundV2 n b)) :
    List (GrayTailSlot n b) :=
  grayBlockSpendSlotsV2 (grayChargedSourceCount a e) L pass
    (grayChargedThreshold q e) (dyadicScale e) (dyadicScale a)
    (frozen.map GrayTailRoundV2.toV1)

/-- Convert the terminal advantage snapshot to either the first spend pass or
the final state when every root already satisfies H4. -/
def grayChargedStartSpendV2 {n b : Nat}
    (q L a e : Nat) (A : Allocation) (core : GrayTailStateV2 n b)
    (sm : FamilyServerMove) : GrayChargedStateV2 n b :=
  let slots := grayChargedSlotsForPassV2 q L a e 0 core.frozen
  if slots.isEmpty then
    { phase := .done
      core := { core with done := true, slots := [], history := ([], []) } }
  else
    { phase := .spend 0
      core := { core with
        done := false
        roundStart := core.time
        slots := slots
        history := ([], [])
        unavailable := A ++
          grayHarvest (grayChargedSpendDelta a L e 0) slots n sm } }

/-- The raised-service test of the V2 controller on a block core: every
SUV-raised source son of the core's frozen ledger is served at scale `2^-e`
by the current server move. -/
def grayChargedWaitServedB {n b : Nat} (q a e : Nat)
    (core : GrayTailStateV2 n b) (sm : FamilyServerMove) : Bool :=
  grayChargedRaisedServedB e (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (frozenV1OfV2 core) sm

/-- One transition of the V2 charged controller: in the done phase only the clock advances; in the
advantage phase the block core takes a step and, once it is terminal and every raised source son
is served, the controller moves to the first spend pass; in a spend phase it finishes when no
slot is left and otherwise steps the spend core. -/
def grayChargedStepV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedStateV2 n b) (sm : FamilyServerMove) :
    GrayChargedStateV2 n b :=
  match st.phase with
  | .done => { st with core := { st.core with time := st.core.time + 1 } }
  | .advantage =>
      let next := grayChargedBlockTailStepV2 q L a e sigma A st.core sm
      if next.done then
        if grayChargedWaitServedB q a e next sm then
          grayChargedStartSpendV2 q L a e A next sm
        else { phase := .advantage, core := next }
      else { phase := .advantage, core := next }
  | .spend pass =>
      if st.core.slots.isEmpty then
        { phase := .done
          core := { st.core with time := st.core.time + 1, done := true } }
      else
        let r := st.core.frozen.length
        let epsRound := grayChargedSpendEps a L e pass
        let deltaRound := grayChargedSpendDelta a L e pass
        let current := grayBlockSpendMoveV2 q L a e pass sigma st.core
        let localSM := grayTailLocalServerMove deltaRound st.core.slots sm
        if grayChargedBlockSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable current localSM then
          let allocated := grayTailLocalAllocatedList localSM
          let p : GrayTailRoundV2 n b :=
            { serverTime := st.core.time
              roundIndex := r
              blockAnchor := epsRound
              childEps := epsRound + graySpendSpan q
              fineEnd := deltaRound
              slots := st.core.slots
              move := current
              allocated := allocated
              unavailable := st.core.unavailable }
          let frozen' := st.core.frozen ++ [p]
          let slotsNext := grayChargedSlotsForPassV2 q L a e (pass + 1) frozen'
          let unavailable' := A ++
            grayHarvest (grayChargedSpendDelta a L e (pass + 1)) slotsNext n sm
          let base : GrayTailStateV2 n b :=
            { time := st.core.time + 1
              roundStart := st.core.time + 1
              done := false
              frozen := frozen'
              unavailable := unavailable'
              slots := []
              anchoringSlots := []
              history := ([], []) }
          if pass + 1 < 8 then
            let slots := grayChargedSlotsForPassV2 q L a e (pass + 1) frozen'
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

/-- The V2 charged controller state obtained by folding the charged step over a history of
server moves, starting from the initial state. -/
def grayChargedFoldV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (history : List FamilyServerMove) : GrayChargedStateV2 n b :=
  history.foldl (grayChargedStepV2 q L a e sigma A)
    (grayChargedInitialStateV2 n b a e q L A)

/-- The V2 charged run state at time `t`. -/
def grayChargedRunStateV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : GrayChargedStateV2 n b :=
  grayChargedFoldV2 q L a e sigma A (grayTailServerPrefix sm t)

/-- The V2 controller state at time `t + 1` is one step applied to the state at time `t`. -/
lemma grayChargedRunStateV2_succ {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    grayChargedRunStateV2 (n := n) (b := b) q L a e sigma A sm (t + 1) =
      grayChargedStepV2 q L a e sigma A
        (grayChargedRunStateV2 q L a e sigma A sm t) (sm t) := by
  simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix_succ]

/-- An advantage step that does not stop remains in the advantage phase with
the stepped V2 core. -/
lemma grayChargedStepV2_advantage_continue {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedStateV2 n b) (sm : FamilyServerMove)
    (h : st.phase = .advantage)
    (hnext : (grayChargedBlockTailStepV2 q L a e sigma A st.core sm).done =
      false) :
    grayChargedStepV2 q L a e sigma A st sm =
      { phase := .advantage
        core := grayChargedBlockTailStepV2 q L a e sigma A st.core sm } := by
  unfold grayChargedStepV2
  rw [h]
  simp [hnext]

/-- An advantage step whose stepped core is done but whose raised sons are
not all served yet **waits**: the phase tag stays `.advantage` over the
(done) stepped core. -/
lemma grayChargedStepV2_advantage_wait {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedStateV2 n b) (sm : FamilyServerMove)
    (h : st.phase = .advantage)
    (hnext : (grayChargedBlockTailStepV2 q L a e sigma A st.core sm).done =
      true)
    (hserved : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A st.core sm) sm = false) :
    grayChargedStepV2 q L a e sigma A st sm =
      { phase := .advantage
        core := grayChargedBlockTailStepV2 q L a e sigma A st.core sm } := by
  unfold grayChargedStepV2
  rw [h]
  simp [hnext, hserved]

/-- An advantage step whose stepped core is done and whose raised sons are
all served **exits** to the spend phase (or to `done`). -/
lemma grayChargedStepV2_advantage_exit {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedStateV2 n b) (sm : FamilyServerMove)
    (h : st.phase = .advantage)
    (hnext : (grayChargedBlockTailStepV2 q L a e sigma A st.core sm).done =
      true)
    (hserved : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A st.core sm) sm = true) :
    grayChargedStepV2 q L a e sigma A st sm =
      grayChargedStartSpendV2 q L a e A
        (grayChargedBlockTailStepV2 q L a e sigma A st.core sm) sm := by
  unfold grayChargedStepV2
  rw [h]
  simp [hnext, hserved]

/-- The strict block step of a done core only ticks the clock. -/
lemma grayChargedBlockTailStepV2_of_done {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hdone : st.done = true) :
    grayChargedBlockTailStepV2 q L a e sigma A st sm =
      { st with time := st.time + 1 } := by
  simp [grayChargedBlockTailStepV2, hdone]

end Kolmogorov
