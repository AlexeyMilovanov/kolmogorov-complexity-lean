import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.LegalOuterMoves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.RootIncrements
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.EntryMonotonicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields.AvoidsSmall
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFields
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedMonotonicity.DisplayedMoves

/-!
# One step of the charged outer run: the phase analysis

The charged outer run alternates an advantage phase, in which the strategy freezes one tail
round after another, with eight spending passes.  This module runs the phase analysis of a
single step against a legal server play and concludes that the run never withdraws a request:
the move displayed at time `t + 1` asks for at least as much as the move displayed at time `t`,
at every node of every client.  The three shapes of a step -- a round or a pass that misses its
goal and only extends the history, and the last advantage round, which opens the first spending
pass -- are treated one by one, and the main results are
`grayChargedDisplayedMove_stateAt_succ_mono` and, for the play of the charged strategy itself,
`grayCharged_output_monotone`.
-/

namespace Kolmogorov

/-- **An advantage round that misses its goal.**  When the round running at time `t` does not
reach its goal, the step only extends the history of that round, so the displayed move does not
decrease at any node. -/
lemma grayChargedDisplayedMove_step_mono_of_missedGoal
    {q L B a e n t i : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {core : GrayTailState n (grayTailBranch q L a e)}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hcore : GrayChargedTailCertified q L e A sm t core)
    (hactive : core.done = false) (hslots : core.slots.isEmpty = false)
    (hgoalFalse : grayChargedTailGoalAtB q e
      (grayTailRoundEps q L e core.frozen.length)
      (grayTailRoundDelta q L e core.frozen.length)
      core.slots.length core.unavailable
      (grayTailCurrentMove q L e sigma core)
      (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
        core.slots (sm t)) = false)
    (hst : grayChargedStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t =
      { phase := .advantage, core := core })
    (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma
        { phase := .advantage, core := core }) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma
        (grayChargedStep q L a e sigma A
          { phase := .advantage, core := core } (sm t))) i x := by
  have hslots : ¬ core.slots.isEmpty = true := by simp [hslots]
  have hhist := grayChargedHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have htrace := grayChargedTrace_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hhistN := grayChargedHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + 1)
  have htraceN := grayChargedTrace_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + 1)
  rw [hst] at hhist htrace
  rw [grayChargedStateAt_succ, hst] at hhistN htraceN
  let st0 : GrayChargedState n (grayTailBranch q L a e) :=
    { phase := .advantage, core := core }
  have hhist0 : GrayTailHistoryOK q L e sigma core := by
    unfold GrayChargedHistoryOK at hhist
    simp only [grayChargedRoundStrategy] at hhist
    exact hhist
  have htrace0 : GrayTailTrace q L e sm t core := by
    have h := htrace
    unfold GrayChargedTrace at h
    simp only [grayChargedRoundDelta] at h
    exact GrayTailTraceAt.toTrace h
  have hround : core.frozen.length < grayTailRoundCount q := by
    have hlt := hcore.frozen_bound.2 hactive
    calc
      core.frozen.length < grayChargedAdvantageRoundCount q := hlt
      _ <= grayChargedAdvantageRoundCount q + 8 := by omega
      _ = grayTailRoundCount q :=
        grayChargedAdvantageRoundCount_add_eight q
  have hstep : grayChargedStep q L a e sigma A st0 (sm t) =
      { phase := st0.phase
        core :=
          { st0.core with
            time := st0.core.time + 1
            history :=
              (st0.core.history.1 ++
                [grayTailCurrentMove q L e sigma st0.core],
               st0.core.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st0.core.frozen.length)
                  st0.core.slots (sm t)]) } } := by
    simp [st0, grayChargedStep, grayChargedTailStep,
      grayTailWaitingB, hactive, hslots, hgoalFalse]
  have hphaseStep :
      (grayChargedStep q L a e sigma A st0 (sm t)).phase =
        .advantage := by
    rw [hstep]
  have hstepEta : grayChargedStep q L a e sigma A st0 (sm t) =
      { phase := .advantage,
        core := (grayChargedStep q L a e sigma A
          st0 (sm t)).core } := by
    rw [← hphaseStep]
  have hhist' : GrayTailHistoryOK q L e sigma
      (grayChargedStep q L a e sigma A st0 (sm t)).core := by
    rw [hstepEta] at hhistN
    unfold GrayChargedHistoryOK at hhistN
    simp only [grayChargedRoundStrategy] at hhistN
    exact hhistN
  have htrace' : GrayTailTrace q L e sm (t + 1)
      (grayChargedStep q L a e sigma A st0 (sm t)).core := by
    rw [hstepEta] at htraceN
    have h := htraceN
    unfold GrayChargedTrace at h
    simp only [grayChargedRoundDelta] at h
    exact GrayTailTraceAt.toTrace h
  exact grayChargedDisplayedMove_step_mono_of_history
    ha hae hB hRung hsm st0 hcore hround
    hhist0 htrace0 (by simpa using hslots)
    hstep hhist' htrace'
    (by simp [st0, grayChargedOutputEntries, hslots])
    (by simp [st0, grayChargedOutputEntries, grayChargedStep,
      grayChargedTailStep, grayTailWaitingB, hactive, hslots,
      hgoalFalse]) i hi x

/-- **The last advantage round.**  When freezing the current round exhausts the advantage
rounds, the step opens the first spending pass: the new entry table extends the old one by
entries with nonnegative requests, so the displayed move does not decrease at any node. -/
lemma grayChargedDisplayedMove_step_mono_of_startSpend
    {q L B a e n t i : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {core next : GrayTailState n (grayTailBranch q L a e)}
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hslots : core.slots.isEmpty = false)
    (hfrozenEntries : grayTailFrozenEntries next.frozen =
      grayTailFrozenEntries core.frozen ++
        grayTailSlotEntries core.slots (grayTailCurrentMove q L e sigma core))
    (hstartEmpty : ¬ (grayChargedSlotsForPass q a e 0 next.frozen).isEmpty = true)
    (hst : grayChargedStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t =
      { phase := .advantage, core := core })
    (hstep : grayChargedStep q L a e sigma A { phase := .advantage, core := core } (sm t) =
      grayChargedStartSpend q L a e A next (sm t))
    (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma
        { phase := .advantage, core := core }) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma
        (grayChargedStep q L a e sigma A
          { phase := .advantage, core := core } (sm t))) i x := by
  have hslots : ¬ core.slots.isEmpty = true := by simp [hslots]
  let st0 : GrayChargedState n (grayTailBranch q L a e) :=
    { phase := .advantage, core := core }
  have hphaseStep :
      (grayChargedStep q L a e sigma A st0 (sm t)).phase =
        .spend 0 := by
    rw [hstep]
    simp [grayChargedStartSpend, hstartEmpty]
  have hslotsStep :
      (grayChargedStep q L a e sigma A st0 (sm t)).core.slots.isEmpty
        = false := by
    rw [hstep]
    simp only [grayChargedStartSpend]
    rw [ite_eq_right (by simpa using hstartEmpty)]
    simpa using hstartEmpty
  have hstartListNe :
      grayChargedSlotsForPass q a e 0 next.frozen ≠ [] := by
    intro hnil
    apply hstartEmpty
    simp [hnil]
  refine grayChargedDisplayedMove_step_mono_of_append
    (st1 := st0)
    (move2 := grayChargedSpendMove q L a e 0 sigma
      (grayChargedStep q L a e sigma A st0 (sm t)).core)
    hi x ?_ ?_
  · rw [hstep]
    simp [st0, grayChargedStartSpend, hstartListNe,
      grayChargedOutputEntries, hfrozenEntries, hslots,
      grayTailEntries, List.append_assoc]
  · intro pr hpr y
    refine grayChargedSpendSlotEntries_stateAt_nonneg
      (t := t + 1) hroom hB hRung hsm (pass := 0) ?_ ?_ pr ?_ y
    · rw [grayChargedStateAt_succ, hst]
      exact hphaseStep
    · rw [grayChargedStateAt_succ, hst]
      exact hslotsStep
    · rw [grayChargedStateAt_succ, hst]
      exact hpr

/-- **The advantage phase of the monotonicity step.**  If at time `t` the charged run is in the
advantage phase with certified core `core`, then the move displayed after one step requests at
least as much as the move displayed before it, at every node. -/
lemma grayChargedDisplayedMove_step_mono_advantage
    {q L B a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t : Nat) (core : GrayTailState n (grayTailBranch q L a e))
    (hcore : GrayChargedTailCertified q L e A sm t core)
    (hsource : GrayTailSourceInvariant (grayChargedSourceCount a e) core)
    (hactive : core.done = false)
    (hst : grayChargedStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t =
      { phase := .advantage, core := core })
    (i : Nat) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma
        { phase := .advantage, core := core }) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma
        (grayChargedStep q L a e sigma A
          { phase := .advantage, core := core } (sm t))) i x := by
  let st0 : GrayChargedState n (grayTailBranch q L a e) :=
    { phase := .advantage, core := core }
  by_cases hdoneStep :
      (grayChargedStep q L a e sigma A st0 (sm t)).phase = .done
  · have hcert0 : GrayChargedCertified q L a e sigma A sm t st0 :=
      .advantage core hcore hsource hactive
    have heq := grayChargedStep_done_display_eq
      q L a e sigma A sm st0 hcert0 hdoneStep
    simpa [st0] using
      (congrArg (fun m => getFamilyReq m i x) heq).symm.le
  · by_cases hslots : core.slots.isEmpty = true
    · simp [grayChargedStep, grayChargedTailStep, grayTailWaitingB,
        grayChargedDisplayedMove, hactive,
        hslots]
    · by_cases hgoal : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e core.frozen.length)
          (grayTailRoundDelta q L e core.frozen.length)
          core.slots.length core.unavailable
          (grayTailCurrentMove q L e sigma core)
          (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
            core.slots (sm t)) = true
      · let next := grayChargedTailStep
            q L a e sigma A core (sm t)
        let p : GrayTailRound n (grayTailBranch q L a e) :=
          { serverTime := core.time
            roundIndex := core.frozen.length
            epsDepth := grayTailRoundEps q L e core.frozen.length
            slots := core.slots
            move := grayTailCurrentMove q L e sigma core
            allocated := grayTailLocalAllocatedList
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e core.frozen.length)
                core.slots (sm t))
            unavailable := core.unavailable }
        have hnextFrozen : next.frozen = core.frozen ++ [p] := by
          simp [next, p, grayChargedTailStep, grayTailWaitingB,
            hactive, hslots, hgoal]
        by_cases hnextDone : next.done = true
        · by_cases hstartEmpty :
              (grayChargedSlotsForPass q a e 0 next.frozen).isEmpty =
                true
          · exfalso
            apply hdoneStep
            simp [st0, grayChargedStep, next, hnextDone,
              grayChargedStartSpend, hstartEmpty]
          · have hstep : grayChargedStep q L a e sigma A st0 (sm t) =
                grayChargedStartSpend q L a e A next (sm t) := by
              change (if next.done then
                  grayChargedStartSpend q L a e A next (sm t)
                else { phase := .advantage, core := next }) =
                  grayChargedStartSpend q L a e A next (sm t)
              rw [ite_eq_left hnextDone]
            exact grayChargedDisplayedMove_step_mono_of_startSpend hroom hB hRung hsm
              (by simpa using hslots)
              (by simp [hnextFrozen, grayTailFrozenEntries_append_one, p])
              hstartEmpty hst hstep hi x
        · have hstep : grayChargedStep q L a e sigma A st0 (sm t) =
                { phase := .advantage, core := next } := by
            change (if next.done then
                grayChargedStartSpend q L a e A next (sm t)
              else { phase := .advantage, core := next }) =
                { phase := .advantage, core := next }
            simp [hnextDone]
          by_cases hnextEmpty : next.slots.isEmpty = true
          · refine grayChargedDisplayedMove_step_mono_of_append
              (st1 := st0)
              (move2 := grayTailCurrentMove q L e sigma
                (grayChargedStep q L a e sigma A st0 (sm t)).core)
              hi x ?_ ?_
            · rw [hstep]
              have hnextNil : next.slots = [] :=
                List.isEmpty_iff.mp hnextEmpty
              simp [st0, grayChargedOutputEntries, hnextFrozen, hslots,
                hnextNil, grayTailEntries, grayTailSlotEntries,
                grayTailFrozenEntries_append_one, p]
            · intro pr hpr y
              rw [hstep] at hpr
              have hnextNil : next.slots = [] :=
                List.isEmpty_iff.mp hnextEmpty
              simp [hnextNil, grayTailSlotEntries] at hpr
          · refine grayChargedDisplayedMove_step_mono_of_append
              (st1 := st0)
              (move2 := grayTailCurrentMove q L e sigma
                (grayChargedStep q L a e sigma A st0 (sm t)).core)
              hi x ?_ ?_
            · rw [hstep]
              simp [st0, grayChargedOutputEntries, hnextFrozen, hslots,
                hnextEmpty, grayTailEntries,
                grayTailFrozenEntries_append_one, List.append_assoc, p]
            · intro pr hpr y
              refine grayChargedCurrentSlotEntries_stateAt_nonneg
                (t := t + 1) ha hae hB hRung hsm ?_ ?_ pr ?_ y
              · rw [grayChargedStateAt_succ, hst]
                rw [hstep]
              · rw [grayChargedStateAt_succ, hst]
                rw [hstep]
                simpa using hnextEmpty
              · rw [grayChargedStateAt_succ, hst]
                exact hpr
      · exact grayChargedDisplayedMove_step_mono_of_missedGoal ha hae hB hRung hsm hcore
          hactive (by simpa using hslots) (Bool.eq_false_of_not_eq_true hgoal) hst hi x

/-- **A spending pass that misses its goal.**  When the pass running at time `t` does not reach
its goal, the step only extends the history of that pass, so the displayed move does not
decrease at any node. -/
lemma grayChargedDisplayedMove_step_mono_of_missedGoal_spend
    {q L B a e n t pass i : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {core : GrayTailState n (grayTailBranch q L a e)}
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hspend : GrayChargedSpendCertified q L a e A sm t pass core)
    (hgoalFalse : grayChargedSpendGoalAtB q L a e pass
      core.slots.length core.unavailable
      (grayChargedSpendMove q L a e pass sigma core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
        core.slots (sm t)) = false)
    (hst : grayChargedStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t =
      { phase := .spend pass, core := core })
    (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma
        { phase := .spend pass, core := core }) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma
        (grayChargedStep q L a e sigma A
          { phase := .spend pass, core := core } (sm t))) i x := by
  have hhist := grayChargedHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have htrace := grayChargedTrace_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hhistN := grayChargedHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + 1)
  have htraceN := grayChargedTrace_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + 1)
  rw [hst] at hhist htrace
  rw [grayChargedStateAt_succ, hst] at hhistN htraceN
  let st0 : GrayChargedState n (grayTailBranch q L a e) :=
    { phase := .spend pass, core := core }
  have hhist0 : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass, core := core } := hhist
  have htrace0 : GrayTailTraceAt (grayChargedSpendDelta a L e pass)
      sm t core := htrace
  have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
  have hlocal := grayChargedSpendFutureServer_legal
    hroom hspend.pass_lt hspend.core hspend.unavailable_snap hsm
  have hstep : grayChargedStep q L a e sigma A st0 (sm t) =
      { phase := st0.phase
        core :=
          { st0.core with
            time := st0.core.time + 1
            history :=
              (st0.core.history.1 ++
                [grayChargedSpendMove q L a e pass sigma st0.core],
               st0.core.history.2 ++
                [grayTailLocalServerMove
                  (grayChargedSpendDelta a L e pass)
                  st0.core.slots (sm t)]) } } := by
    simp [st0, grayChargedStep, hslots, hgoalFalse]
  have hphaseStep :
      (grayChargedStep q L a e sigma A st0 (sm t)).phase =
        .spend pass := by
    rw [hstep]
  have hstepEta : grayChargedStep q L a e sigma A st0 (sm t) =
      { phase := .spend pass,
        core := (grayChargedStep q L a e sigma A
          st0 (sm t)).core } := by
    rw [← hphaseStep]
  have hhist' : GrayChargedHistoryOK q L a e sigma
      (n := n) (b := grayTailBranch q L a e)
      { phase := .spend pass,
        core := (grayChargedStep q L a e sigma A st0 (sm t)).core } := by
    rw [hstepEta] at hhistN
    exact hhistN
  have htrace' : GrayTailTraceAt (grayChargedSpendDelta a L e pass)
      sm (t + 1)
      (grayChargedStep q L a e sigma A st0 (sm t)).core := by
    rw [hstepEta] at htraceN
    have h := htraceN
    unfold GrayChargedTrace at h
    simpa only [grayChargedRoundDelta] using h
  exact grayChargedDisplayedMove_step_mono_of_history_spend
    hB hRung st0 hhist0 htrace0 hlocal hslots
    hstep hhist' htrace'
    (by simp [st0, grayChargedOutputEntries, hslots])
    (by simp [st0, grayChargedOutputEntries, grayChargedStep,
      hslots, hgoalFalse]) i hi x

/-- **The spending phase of the monotonicity step.**  If at time `t` the charged run is in the
`pass`-th spending phase with certified core `core`, then the move displayed after one step
requests at least as much as the move displayed before it, at every node. -/
lemma grayChargedDisplayedMove_step_mono_spend
    {q L B a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t pass : Nat) (core : GrayTailState n (grayTailBranch q L a e))
    (hspend : GrayChargedSpendCertified q L a e A sm t pass core)
    (hst : grayChargedStateAt (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t =
      { phase := .spend pass, core := core })
    (i : Nat) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq (grayChargedDisplayedMove q L a e sigma
        { phase := .spend pass, core := core }) i x <=
      getFamilyReq (grayChargedDisplayedMove q L a e sigma
        (grayChargedStep q L a e sigma A
          { phase := .spend pass, core := core } (sm t))) i x := by
  let st0 : GrayChargedState n (grayTailBranch q L a e) :=
    { phase := .spend pass, core := core }
  have hcert0 : GrayChargedCertified q L a e sigma A sm t st0 :=
    .spend pass core hspend
  by_cases hdoneStep :
      (grayChargedStep q L a e sigma A st0 (sm t)).phase = .done
  · have heq := grayChargedStep_done_display_eq
      q L a e sigma A sm st0 hcert0 hdoneStep
    simpa [st0] using
      (congrArg (fun m => getFamilyReq m i x) heq).symm.le
  · have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
    by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
        core.slots.length core.unavailable
        (grayChargedSpendMove q L a e pass sigma core)
        (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
          core.slots (sm t)) = true
    · by_cases hpass : pass + 1 < 8
      · let frozen' := core.frozen ++
            [{ serverTime := core.time
               roundIndex := core.frozen.length
               epsDepth := grayChargedSpendEps a L e pass
               slots := core.slots
               move := grayChargedSpendMove q L a e pass sigma core
               allocated := grayTailLocalAllocatedList
                 (grayTailLocalServerMove
                   (grayChargedSpendDelta a L e pass)
                   core.slots (sm t))
               unavailable := core.unavailable }]
        by_cases hnextEmpty :
            (grayChargedSlotsForPass q a e (pass + 1) frozen').isEmpty =
              true
        · exfalso
          apply hdoneStep
          simp [st0, grayChargedStep, hslots, hgoal, hpass, frozen',
            hnextEmpty]
        · have hphaseStep :
              (grayChargedStep q L a e sigma A st0 (sm t)).phase =
                .spend (pass + 1) := by
            simp [st0, grayChargedStep, hslots, hgoal, hpass, frozen',
              hnextEmpty]
          have hstepEta : grayChargedStep q L a e sigma A st0 (sm t) =
              { phase := .spend (pass + 1),
                core := (grayChargedStep q L a e sigma A
                  st0 (sm t)).core } := by
            rw [← hphaseStep]
          have hcertN := grayChargedCertified_stateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + 1)
          rw [grayChargedStateAt_succ, hst, hstepEta] at hcertN
          have hslotsStep :
              (grayChargedStep q L a e sigma A
                st0 (sm t)).core.slots.isEmpty = false := by
            cases hcertN with
            | spend p2 c2 hsp2 => exact hsp2.slots_nonempty
          refine grayChargedDisplayedMove_step_mono_of_append
            (st1 := st0)
            (move2 := grayChargedSpendMove q L a e (pass + 1) sigma
              (grayChargedStep q L a e sigma A st0 (sm t)).core)
            hi x ?_ ?_
          · simp [st0, grayChargedStep, hslots, hgoal, hpass, frozen',
              hnextEmpty, grayChargedOutputEntries, grayTailEntries,
              grayTailFrozenEntries_append_one, List.append_assoc]
          · intro pr hpr y
            refine grayChargedSpendSlotEntries_stateAt_nonneg
              (t := t + 1) hroom hB hRung hsm (pass := pass + 1)
              ?_ ?_ pr ?_ y
            · rw [grayChargedStateAt_succ, hst]
              exact hphaseStep
            · rw [grayChargedStateAt_succ, hst]
              exact hslotsStep
            · rw [grayChargedStateAt_succ, hst]
              exact hpr
      · exfalso
        apply hdoneStep
        simp [st0, grayChargedStep, hslots, hgoal, hpass]
    · exact grayChargedDisplayedMove_step_mono_of_missedGoal_spend hroom hB hRung hsm
        hspend (Bool.eq_false_of_not_eq_true hgoal) hst hi x

/-- Against a legal server play, the move displayed by the charged run at time `t + 1` requests
at least as much as the move displayed at time `t`, at every node. -/
theorem grayChargedDisplayedMove_stateAt_succ_mono
    {q L B a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (sm : Nat -> FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t i : Nat) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq
        (grayChargedDisplayedMove q L a e sigma
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t)) i x <=
      getFamilyReq
        (grayChargedDisplayedMove q L a e sigma
          (grayChargedStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + 1))) i x := by
  rw [grayChargedStateAt_succ]
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  generalize hst :
      grayChargedStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t = st at hcert ⊢
  cases hcert with
  | done core hdone =>
      simp [grayChargedStep, grayChargedDisplayedMove]
  | advantage core hcore hsource hactive =>
      exact grayChargedDisplayedMove_step_mono_advantage
        ha hae hroom hB hRung hsm t core hcore hsource hactive hst i hi x
  | spend pass core hspend =>
      exact grayChargedDisplayedMove_step_mono_spend
        hroom hB hRung hsm t pass core hspend hst i hi x


/-- Against a legal server play, the requests of the charged strategy are monotone in time: they
never decrease at any node of any client. -/
theorem grayCharged_output_monotone
    {q L B a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (sm : Nat -> FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t i : Nat) (hi : i < n) (x : GacsDayNode) :
    getFamilyReq
        (playClientFamily A n
          (grayChargedStrategy q L a e sigma) sm t) i x <=
      getFamilyReq
        (playClientFamily A n
          (grayChargedStrategy q L a e sigma) sm (t + 1)) i x := by
  rw [playClientFamily_grayChargedStrategy,
    playClientFamily_grayChargedStrategy]
  exact grayChargedDisplayedMove_stateAt_succ_mono
    ha hae hroom hB hRung sm hsm t i hi x

end Kolmogorov
