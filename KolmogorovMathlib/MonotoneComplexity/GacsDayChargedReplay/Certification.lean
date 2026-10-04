import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.SourceInvariant

/-!
# One charged step preserves certification

`grayChargedCertified_step` is the induction step behind the replay: a certified charged state at
time `t` steps to a certified state at time `t + 1`. It is proved by cases on the phase —
`grayChargedCertified_step_advantage`, `grayChargedCertified_step_done`, and the two spend cases
according to whether the spend goal is reached, the successful one freezing the round.
`GrayChargedCertified.toCore` and `GrayChargedCoreCertified.toTraceAt_of_reset` relate
certification of a state to certification of its core, and the remaining lemmas record what
opening a spend pass and ticking a finished clock do.
-/

namespace Kolmogorov

/-- In a charged step, if the initial phase is advantage, the next certified state is obtained by
stepping the core tail strategy and transitioning depending on whether the tail step completed. -/
private lemma grayChargedCertified_step_advantage {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {core : GrayTailState n b}
    (hcore : GrayChargedTailCertified q L e A sm t core)
    (hsource : GrayTailSourceInvariant (grayChargedSourceCount a e) core)
    (hactive : core.done = false) :
    GrayChargedCertified q L a e sigma A sm (t + 1)
      (grayChargedStep q L a e sigma A { phase := .advantage, core := core } (sm t)) := by
  let next := grayChargedTailStep q L a e sigma A core (sm t)
  have hnext : GrayChargedTailCertified q L e A sm (t + 1) next :=
    grayChargedTailCertified_step sigma hcore
  have hsourceNext :
      GrayTailSourceInvariant (grayChargedSourceCount a e) next :=
    grayChargedSourceInvariant_step q L a e sigma A core (sm t) hsource
  by_cases hdone : next.done = true
  · have hslotsNE : core.slots.isEmpty = false := by
      by_contra hbad
      have hemp : core.slots.isEmpty = true := by
        cases h : core.slots.isEmpty <;> simp_all
      have hnd : next.done = false := by
        simp [next, grayChargedTailStep, grayTailWaitingB, hactive, hemp]
      rw [hnd] at hdone
      exact Bool.noConfusion hdone
    have hlast : Option.map GrayTailRound.serverTime
        next.frozen.getLast? = some core.time :=
      grayChargedTailStep_done_getLast q L a e sigma A core (sm t)
        hactive hslotsNE hdone
    have hm : (sm t) = grayHarvestSnapshot sm
        (Option.map GrayTailRound.serverTime next.frozen.getLast?) := by
      rw [hlast]
      simp [grayHarvestSnapshot, hcore.time_eq]
    have hstart := grayChargedStartSpend_certified
      (sigma := sigma) hnext hsourceNext hm
    simpa [grayChargedStep, next, hdone] using hstart
  · have hnextActive : next.done = false := by
      cases h : next.done <;> simp_all
    have hout : GrayChargedCertified q L a e sigma A sm (t + 1)
        { phase := .advantage, core := next } :=
      GrayChargedCertified.advantage next hnext hsourceNext hnextActive
    simpa [grayChargedStep, next, hdone] using hout

/-- In a charged step, if the initial phase is done, the state remains done with its core
ticked by one time step. -/
private lemma grayChargedCertified_step_done {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {core : GrayTailState n b}
    (hdone : GrayChargedDoneCertified q L a e A sm t core) :
    GrayChargedCertified q L a e sigma A sm (t + 1)
      (grayChargedStep q L a e sigma A { phase := .done, core := core } (sm t)) := by
  apply GrayChargedCertified.done
  refine ⟨?_, ?_, ?_, ?_, hdone.frozen_layout, ?_⟩
  · simpa [grayChargedStep] using
      hdone.core.tick core.roundStart core.done core.history
  · simpa [grayChargedStep] using hdone.slots_empty
  · simpa [grayChargedStep] using hdone.done_true
  · simpa [grayChargedStep] using hdone.history_empty
  · simpa [grayChargedStep] using hdone.frozen_bound

/-- In a charged spend pass step when the spend goal is not reached, the core ticks and remains
in the same spend pass. -/
private lemma grayChargedCertified_step_spend_goal_false {n b q L a e t pass : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {core : GrayTailState n b}
    (hspend : GrayChargedSpendCertified q L a e A sm t pass core)
    (hslots : core.slots.isEmpty = false)
    (hgoal : grayChargedSpendGoalAtB q L a e pass core.slots.length core.unavailable
      (grayChargedSpendMove q L a e pass sigma core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots (sm t)) = false) :
    GrayChargedCertified q L a e sigma A sm (t + 1)
      (grayChargedStep q L a e sigma A { phase := .spend pass, core := core } (sm t)) := by
  let epsRound := grayChargedSpendEps a L e pass
  let deltaRound := grayChargedSpendDelta a L e pass
  let current := grayChargedSpendMove q L a e pass sigma core
  let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
  let nextCore : GrayTailState n b :=
    { core with time := core.time + 1, history :=
        (core.history.1 ++ [current], core.history.2 ++ [localSM]) }
  have hcoreNext :
      GrayChargedCoreCertified q L a e A sm (t + 1) nextCore := by
    simpa [nextCore] using
      hspend.core.tick core.roundStart core.done
        (core.history.1 ++ [current], core.history.2 ++ [localSM])
  have hspendCert : GrayChargedSpendCertified q L a e A sm
      (t + 1) pass nextCore := by
    refine ⟨hcoreNext, hspend.pass_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [nextCore] using hspend.unavailable_snap
    · simpa [nextCore] using hspend.slots_eq
    · simpa [nextCore] using hspend.slots_nonempty
    · simpa [nextCore] using hspend.done_false
    · simpa [nextCore] using hspend.frozen_layout
    · simpa [nextCore] using hspend.frozen_bound
  have hout : GrayChargedCertified q L a e sigma A sm (t + 1)
      { phase := .spend pass, core := nextCore } :=
    GrayChargedCertified.spend pass nextCore hspendCert
  simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
    current, localSM, nextCore] using hout

/-- In a charged spend pass step when the spend goal is reached, the round is frozen and the
state transitions to either the next spend pass or done. -/
private lemma grayChargedCertified_step_spend_goal_true {n b q L a e t pass : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {core : GrayTailState n b}
    (hspend : GrayChargedSpendCertified q L a e A sm t pass core)
    (hslots : core.slots.isEmpty = false)
    (hgoal : grayChargedSpendGoalAtB q L a e pass core.slots.length core.unavailable
      (grayChargedSpendMove q L a e pass sigma core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots (sm t)) = true) :
    GrayChargedCertified q L a e sigma A sm (t + 1)
      (grayChargedStep q L a e sigma A { phase := .spend pass, core := core } (sm t)) := by
  let epsRound := grayChargedSpendEps a L e pass
  let deltaRound := grayChargedSpendDelta a L e pass
  let current := grayChargedSpendMove q L a e pass sigma core
  let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
  let p : GrayTailRound n b :=
    { serverTime := core.time
      roundIndex := core.frozen.length
      epsDepth := epsRound
      slots := core.slots
      move := current
      allocated := grayTailLocalAllocatedList localSM
      unavailable := core.unavailable }
  let frozen' := core.frozen ++ [p]
  let base : GrayTailState n b :=
    { time := core.time + 1
      roundStart := core.time + 1
      done := false
      frozen := frozen'
      unavailable := A ++
        grayHarvest (grayChargedSpendDelta a L e (pass + 1))
          (grayChargedSlotsForPass q a e (pass + 1) frozen') n (sm t)
      slots := []
      anchoringSlots := []
      history := ([], []) }
  have hpSlots : p.slots = core.slots := rfl
  have hdeltaEq : grayChargedSpendDelta a L e pass =
      grayChargedSpendEps a L e pass + L := rfl
  have hfreeze : GrayChargedCoreCertified q L a e A sm (t + 1) base := by
    dsimp [base, frozen']
    apply hspend.core.freezeSpend (pass := pass) p hpSlots
    · rfl
    · simpa [p] using hspend.core.time_eq
    · exact hspend.pass_lt
    · simp [p, epsRound]
    · simp [p, localSM, epsRound, deltaRound, hdeltaEq,
        hspend.core.time_eq]
    · simpa [p, epsRound, grayChargedSpendDelta] using
        hspend.unavailable_snap
    · simpa [p, current, localSM, epsRound, deltaRound, hdeltaEq,
        hspend.core.time_eq] using hgoal
    · intro s hs
      apply grayChargedSlotsForPass_spendSlot (frozen := core.frozen)
      rw [hpSlots] at hs
      rw [<- hspend.slots_eq]
      exact hs
    · rw [hpSlots]
      intro h
      rw [h] at hslots
      simp at hslots
  have hlayout : GrayChargedFrozenLayout
      (grayChargedSourceCount a e) (grayChargedSpendCount q a e)
      (pass + 1) frozen' := by
    simpa [frozen'] using grayChargedSpendLayout_advance hspend hpSlots
  by_cases hpass : pass + 1 < 8
  · let slots := grayChargedSlotsForPass q a e (pass + 1) frozen'
    by_cases hempty : slots.isEmpty = true
    · have hnil : slots = [] := List.isEmpty_iff.mp hempty
      have hslotsNil :
          grayChargedSlotsForPass q a e (pass + 1) frozen' = [] := by
        simpa [slots] using hnil
      let doneCore : GrayTailState n b := { base with done := true }
      have hcoreDone :
          GrayChargedCoreCertified q L a e A sm (t + 1) doneCore := by
        have h := hfreeze.withSlots true [] (by simp) (by simp)
        simpa [doneCore, base] using h
      have hdoneCert :
          GrayChargedDoneCertified q L a e A sm (t + 1) doneCore := by
        refine ⟨hcoreDone, ?_, ?_, ?_, hlayout.mono (by omega), ?_⟩
        · simp [doneCore, base]
        · simp [doneCore]
        · simp [doneCore, base]
        · dsimp [doneCore, base, frozen']
          have hfb := hspend.frozen_bound
          rw [List.length_append, List.length_singleton]
          omega
      have hout : GrayChargedCertified q L a e sigma A sm (t + 1)
          { phase := .done, core := doneCore } :=
        GrayChargedCertified.done doneCore hdoneCert
      simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
        current, localSM, p, frozen', base, slots, doneCore, hpass,
        hempty, hnil, hslotsNil] using hout
    · have hnempty : slots ≠ [] := by
        intro hnil
        apply hempty
        simp [hnil]
      have hslotsNe :
          grayChargedSlotsForPass q a e (pass + 1) frozen' ≠ [] := by
        simpa [slots] using hnempty
      let nextCore : GrayTailState n b := { base with slots := slots }
      have hcoreNext :
          GrayChargedCoreCertified q L a e A sm (t + 1) nextCore := by
        have h := grayChargedCore_with_next hfreeze hlayout hpass
        simpa [nextCore, slots, base] using h
      have hnonempty : slots.isEmpty = false := by
        cases h : slots.isEmpty <;> simp_all
      have hspendCert : GrayChargedSpendCertified q L a e A sm
          (t + 1) (pass + 1) nextCore := by
        refine ⟨hcoreNext, hpass, ?_, ?_, ?_, ?_, hlayout, ?_⟩
        · simp [nextCore, base, slots, frozen', p,
            grayHarvestSnapshot,
            hspend.core.time_eq]
        · simp [nextCore, slots, base]
        · simpa [nextCore] using hnonempty
        · simp [nextCore, base]
        · dsimp [nextCore, slots, base, frozen']
          have hfb := hspend.frozen_bound
          rw [List.length_append, List.length_singleton]
          omega
      have hout : GrayChargedCertified q L a e sigma A sm (t + 1)
          { phase := .spend (pass + 1), core := nextCore } :=
        GrayChargedCertified.spend (pass + 1) nextCore hspendCert
      simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
        current, localSM, p, frozen', base, slots, nextCore, hpass,
        hempty, hnempty, hslotsNe] using hout
  · have hpassLt := hspend.pass_lt
    have hpassEq : pass + 1 = 8 := by omega
    let doneCore : GrayTailState n b := { base with done := true }
    have hcoreDone :
        GrayChargedCoreCertified q L a e A sm (t + 1) doneCore := by
      have h := hfreeze.withSlots true [] (by simp) (by simp)
      simpa [doneCore, base] using h
    have hdoneCert :
        GrayChargedDoneCertified q L a e A sm (t + 1) doneCore := by
      refine ⟨hcoreDone, ?_, ?_, ?_, ?_, ?_⟩
      · simp [doneCore, base]
      · simp [doneCore]
      · simp [doneCore, base]
      · simpa [hpassEq] using hlayout
      · dsimp [doneCore, base, frozen']
        have hfb := hspend.frozen_bound
        rw [List.length_append, List.length_singleton]
        omega
    have hout : GrayChargedCertified q L a e sigma A sm (t + 1)
        { phase := .done, core := doneCore } :=
      GrayChargedCertified.done doneCore hdoneCert
    simpa [grayChargedStep, hslots, hgoal, epsRound, deltaRound,
      current, localSM, p, frozen', base, doneCore, hpass,
      hspend.core.time_eq] using hout

/-- A charged step turns a certified state at time `t` into a certified state at time `t + 1`. -/
lemma grayChargedCertified_step {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayChargedState n b}
    (hst : GrayChargedCertified q L a e sigma A sm t st) :
    GrayChargedCertified q L a e sigma A sm (t + 1)
      (grayChargedStep q L a e sigma A st (sm t)) := by
  cases hst with
  | advantage core hcore hsource hactive =>
      exact grayChargedCertified_step_advantage hcore hsource hactive
  | done core hdone =>
      exact grayChargedCertified_step_done hdone
  | spend pass core hspend =>
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      let epsRound := grayChargedSpendEps a L e pass
      let deltaRound := grayChargedSpendDelta a L e pass
      let current := grayChargedSpendMove q L a e pass sigma core
      let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
      by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
          core.slots.length core.unavailable current localSM = true
      · exact grayChargedCertified_step_spend_goal_true hspend hslots hgoal
      · have hgoalFalse : grayChargedSpendGoalAtB q L a e pass
            core.slots.length core.unavailable current localSM = false := by
          cases h : grayChargedSpendGoalAtB q L a e pass
            core.slots.length core.unavailable current localSM <;> simp_all
        exact grayChargedCertified_step_spend_goal_false hspend hslots hgoalFalse

/-- A certified charged state has a certified core. -/
lemma GrayChargedCertified.toCore {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayChargedState n b}
    (hst : GrayChargedCertified q L a e sigma A sm t st) :
    GrayChargedCoreCertified q L a e A sm t st.core := by
  cases hst with
  | advantage _ hcore hsource _ => exact hcore.toCore hsource
  | spend _ _ hspend => exact hspend.core
  | done _ hdone => exact hdone.core

/-- A tail step that finishes the tail leaves the round start equal to the current time. -/
lemma grayChargedTail_done_roundStart_eq_time {n b q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {st : GrayTailState n b} {m : FamilyServerMove}
    (hactive : st.done = false)
    (hdone : (grayChargedTailStep q L a e sigma A st m).done = true) :
    (grayChargedTailStep q L a e sigma A st m).roundStart =
      (grayChargedTailStep q L a e sigma A st m).time := by
  by_cases hslots : st.slots.isEmpty = true
  · simp [grayChargedTailStep, grayTailWaitingB, hactive, hslots] at hdone
  · by_cases hgoal : grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = true
    · simp [grayChargedTailStep, grayTailWaitingB, hactive, hslots, hgoal]
    · simp [grayChargedTailStep, grayTailWaitingB, hactive, hslots, hgoal]
        at hdone

/-- A charged step preserves well-formedness of the history, provided a terminated core carries
an empty history. -/
lemma grayChargedHistoryOK_step {n b q L a e : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    (st : GrayChargedState n b) (m : FamilyServerMove)
    (hterm : (st.core.done || st.core.slots.isEmpty) = true ->
      st.core.history = ([], []))
    (hst : GrayChargedHistoryOK q L a e sigma st) :
    GrayChargedHistoryOK q L a e sigma
      (grayChargedStep q L a e sigma A st m) := by
  cases hphase : st.phase with
  | done =>
      have hst' : GrayChargedHistoryOK q L a e sigma
          { phase := .done, core := st.core } := by
        unfold GrayChargedHistoryOK at hst ⊢
        simpa [hphase] using hst
      have hstep : grayChargedStep q L a e sigma A st m
          = { phase := .done,
              core := { st.core with time := st.core.time + 1 } } := by
        simp only [grayChargedStep, hphase]
      rw [hstep]
      exact hst'
  | advantage =>
      have hst' : GrayTailHistoryOK q L e sigma st.core := by
        unfold GrayChargedHistoryOK at hst
        rw [hphase] at hst
        exact hst
      let next := grayChargedTailStep q L a e sigma A st.core m
      have hnext : GrayTailHistoryOK q L e sigma next := by
        exact grayChargedTailHistoryOK_step q L a e sigma A st.core m hst'
      by_cases hdone : next.done = true
      · simp only [grayChargedStep, hphase, next, hdone, ↓reduceIte]
        unfold grayChargedStartSpend
        dsimp only
        split <;> simp [GrayChargedHistoryOK]
      · have hne :
            ¬ (grayChargedTailStep q L a e sigma A st.core m).done = true := hdone
        have hstep : grayChargedStep q L a e sigma A st m
            = { phase := .advantage,
                core := grayChargedTailStep q L a e sigma A st.core m } := by
          simp only [grayChargedStep, hphase, ite_eq_right hne]
        rw [hstep]
        exact hnext
  | spend pass =>
      by_cases hslots : st.core.slots.isEmpty = true
      · have hhist : st.core.history = ([], []) :=
          hterm (by simp [hslots])
        unfold GrayChargedHistoryOK
        simp [grayChargedStep, hphase, hslots, hhist]
      · let epsRound := grayChargedSpendEps a L e pass
        let deltaRound := grayChargedSpendDelta a L e pass
        let current := grayChargedSpendMove q L a e pass sigma st.core
        let localSM := grayTailLocalServerMove deltaRound st.core.slots m
        by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable current localSM = true
        · simp only [grayChargedStep, hphase, hslots,
            Bool.false_eq_true, ↓reduceIte, deltaRound,
            current, localSM, hgoal]
          split
          · split
            · simp [GrayChargedHistoryOK]
            · simp [GrayChargedHistoryOK]
          · simp [GrayChargedHistoryOK]
        · have hst' : GrayChargedHistoryOK q L a e sigma
              { phase := .spend pass, core := st.core } := by
            unfold GrayChargedHistoryOK at hst ⊢
            simpa [hphase] using hst
          have happend := grayChargedHistoryOK_spendAppend q L a e pass
            sigma st.core hst'
            (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
              st.core.slots m)
          unfold GrayChargedHistoryOK
          simp only [grayChargedStep, hphase, hslots,
            Bool.false_eq_true, ↓reduceIte, deltaRound,
            current, localSM, hgoal]
          exact happend

/-- A certified core whose round has just started with an empty history is traced at any delta. -/
lemma GrayChargedCoreCertified.toTraceAt_of_reset {n b q L a e t : Nat}
    (delta : Nat)
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (hcore : GrayChargedCoreCertified q L a e A sm t st)
    (hroundStart : st.roundStart = t)
    (hhistory : st.history = ([], [])) :
    GrayTailTraceAt delta sm t st := by
  refine ⟨hcore.time_eq, ?_, ?_, ?_, ?_⟩
  · intro _
    simp [hroundStart, hhistory]
  · simp [hhistory]
  · intro p hp
    rw [hroundStart]
    exact (hcore.round_valid p hp).2.1
  · intro _
    exact hhistory

/-- A finished state stays traced when its clock ticks. -/
lemma grayChargedDoneTrace_tick {n b q L a e t : Nat}
    (delta : Nat)
    {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (hdone : GrayChargedDoneCertified q L a e A sm t st)
    (htrace : GrayTailTraceAt delta sm t st) :
    GrayTailTraceAt delta sm (t + 1) { st with time := st.time + 1 } := by
  have hterminal : (st.done || st.slots.isEmpty) = true := by
    simp [hdone.slots_empty]
  have hhistory := htrace.terminal_empty hterminal
  refine ⟨congrArg (fun u => u + 1) htrace.time_eq, ?_, ?_,
    htrace.frozen_before, ?_⟩
  · intro hactive
    exact (hactive (by simp [hdone.slots_empty])).elim
  · simp [hhistory]
  · intro _
    exact hhistory

/-- Opening a spend pass leaves the round start unchanged. -/
lemma grayChargedStartSpend_roundStart {n b : Nat}
    (q L a e : Nat) (A : Allocation) (st : GrayTailState n b)
    (m : FamilyServerMove) :
    (grayChargedStartSpend q L a e A st m).core.roundStart = st.roundStart := by
  unfold grayChargedStartSpend
  dsimp only
  split <;> rfl

/-- Opening a spend pass resets the history to empty. -/
lemma grayChargedStartSpend_history {n b : Nat}
    (q L a e : Nat) (A : Allocation) (st : GrayTailState n b)
    (m : FamilyServerMove) :
    (grayChargedStartSpend q L a e A st m).core.history = ([], []) := by
  unfold grayChargedStartSpend
  dsimp only
  split <;> rfl

end Kolmogorov
