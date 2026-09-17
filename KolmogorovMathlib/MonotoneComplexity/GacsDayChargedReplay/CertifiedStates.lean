import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailPointwise
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.SourceInvariant
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedReplay.Certification

/-!
# Replaying the charged controller against a server play

`grayChargedStateAt sm t` is the controller state obtained by replaying the first `t` moves of a
server play, and the theorems here say that state is well behaved: its core is certified
(`grayChargedCoreCertified_stateAt`), it is traced against the play it was replayed from
(`grayChargedTrace_stateAt`, whose step cases are `grayChargedTrace_step_advantage` and
`grayChargedTrace_step_spend`), and its history is well formed
(`grayChargedHistoryOK_stateAt`). The closing lemmas describe what a successful spend round does
to the round start and history, and `grayChargedSpendFutureServer` names the server play the
spend phase hands to its recursive call.
-/

namespace Kolmogorov

/-- A spend round that meets its goal closes: the next round starts at the following time. -/
lemma grayChargedStep_spend_success_roundStart {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (pass : Nat) (st : GrayTailState n b) (m : FamilyServerMove)
    (hslots : st.slots.isEmpty = false)
    (hgoal : grayChargedSpendGoalAtB q L a e pass
      st.slots.length st.unavailable
      (grayChargedSpendMove q L a e pass sigma st)
      (grayTailLocalServerMove
        (grayChargedSpendDelta a L e pass) st.slots m) = true) :
    (grayChargedStep q L a e sigma A
      { phase := .spend pass, core := st } m).core.roundStart = st.time + 1 := by
  simp only [grayChargedStep, hslots, Bool.false_eq_true, ↓reduceIte,
    hgoal]
  split
  · split <;> rfl
  · rfl

/-- A spend round that meets its goal closes with an empty history. -/
lemma grayChargedStep_spend_success_history {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (pass : Nat) (st : GrayTailState n b) (m : FamilyServerMove)
    (hslots : st.slots.isEmpty = false)
    (hgoal : grayChargedSpendGoalAtB q L a e pass
      st.slots.length st.unavailable
      (grayChargedSpendMove q L a e pass sigma st)
      (grayTailLocalServerMove
        (grayChargedSpendDelta a L e pass) st.slots m) = true) :
    (grayChargedStep q L a e sigma A
      { phase := .spend pass, core := st } m).core.history = ([], []) := by
  simp only [grayChargedStep, hslots, Bool.false_eq_true, ↓reduceIte,
    hgoal]
  split
  · split <;> rfl
  · rfl

/-- A charged step in the advantage phase preserves the trace relation. -/
private lemma grayChargedTrace_step_advantage {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat → FamilyServerMove} {core : GrayTailState n b}
    (hcore : GrayChargedTailCertified q L e A sm t core)
    (hsource : GrayTailSourceInvariant (grayChargedSourceCount a e) core)
    (hactive : core.done = false)
    (htrace : GrayChargedTrace q L a e sm t { phase := .advantage, core := core }) :
    GrayChargedTrace q L a e sm (t + 1)
      (grayChargedStep q L a e sigma A { phase := .advantage, core := core } (sm t)) := by
  have htrace0 : GrayTailTrace q L e sm t core := by
    exact ⟨htrace.time_eq, htrace.active_time, htrace.servers_eq,
      htrace.frozen_before, htrace.terminal_empty⟩
  let next := grayChargedTailStep q L a e sigma A core (sm t)
  have hnextCert : GrayChargedTailCertified q L e A sm (t + 1) next :=
    grayChargedTailCertified_step sigma hcore
  by_cases hdone : next.done = true
  · have hinput : GrayChargedCertified q L a e sigma A sm t
        { phase := .advantage, core := core } :=
      GrayChargedCertified.advantage core hcore hsource hactive
    have houtCert := grayChargedCertified_step hinput
    have houtCore := houtCert.toCore
    have hroundNext : next.roundStart = t + 1 := by
      calc
        next.roundStart = next.time :=
          grayChargedTail_done_roundStart_eq_time hactive hdone
        _ = t + 1 := hnextCert.time_eq
    have hround :
        (grayChargedStep q L a e sigma A
          { phase := .advantage, core := core } (sm t)).core.roundStart =
            t + 1 := by
      calc
        _ = next.roundStart := by
          simpa [grayChargedStep, next, hdone] using
            grayChargedStartSpend_roundStart q L a e A next (sm t)
        _ = t + 1 := hroundNext
    have hhistory :
        (grayChargedStep q L a e sigma A
          { phase := .advantage, core := core } (sm t)).core.history =
            ([], []) := by
      simpa [grayChargedStep, next, hdone] using
        grayChargedStartSpend_history q L a e A next (sm t)
    exact houtCore.toTraceAt_of_reset _ hround hhistory
  · have hnextTrace := grayChargedTailTrace_step
        (a := a) (A := A) sigma htrace0
    have hphaseNext : (grayChargedStep q L a e sigma A
        { phase := .advantage, core := core } (sm t)).phase =
          .advantage := by
      simp [grayChargedStep, next, hdone]
    unfold GrayChargedTrace
    rw [hphaseNext]
    simp only [grayChargedRoundDelta]
    simpa [grayChargedStep, next, hdone] using
      GrayTailTraceAt.ofTrace hnextTrace

/-- A charged step in the spend phase preserves the trace relation. -/
private lemma grayChargedTrace_step_spend {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat → FamilyServerMove} {pass : Nat} {core : GrayTailState n b}
    (hspend : GrayChargedSpendCertified q L a e A sm t pass core)
    (htrace : GrayChargedTrace q L a e sm t { phase := .spend pass, core := core }) :
    GrayChargedTrace q L a e sm (t + 1)
      (grayChargedStep q L a e sigma A { phase := .spend pass, core := core } (sm t)) := by
  have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
  let epsRound := grayChargedSpendEps a L e pass
  let deltaRound := grayChargedSpendDelta a L e pass
  let current := grayChargedSpendMove q L a e pass sigma core
  let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
  by_cases hgoal : grayChargedSpendGoalAtB q L a e pass
      core.slots.length core.unavailable current localSM = true
  · have hinput : GrayChargedCertified q L a e sigma A sm t
        { phase := .spend pass, core := core } :=
      GrayChargedCertified.spend pass core hspend
    have hgoal' : grayChargedSpendGoalAtB q L a e pass
        core.slots.length core.unavailable
        (grayChargedSpendMove q L a e pass sigma core)
        (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
          core.slots (sm t)) = true := by
      simpa [epsRound, deltaRound, current, localSM] using hgoal
    have houtCert := grayChargedCertified_step hinput
    have houtCore := houtCert.toCore
    have hround :
        (grayChargedStep q L a e sigma A
          { phase := .spend pass, core := core } (sm t)).core.roundStart =
            t + 1 := by
      calc
        _ = core.time + 1 :=
          grayChargedStep_spend_success_roundStart q L a e sigma A
            pass core (sm t) hslots hgoal'
        _ = t + 1 := congrArg (fun u => u + 1) hspend.core.time_eq
    have hhistory :
        (grayChargedStep q L a e sigma A
          { phase := .spend pass, core := core } (sm t)).core.history =
            ([], []) := by
      exact grayChargedStep_spend_success_history q L a e sigma A
        pass core (sm t) hslots hgoal'
    exact houtCore.toTraceAt_of_reset _ hround hhistory
  · have htr : GrayTailTraceAt (grayChargedSpendDelta a L e pass)
        sm t core := htrace
    have hactive : (core.done || core.slots.isEmpty) ≠ true := by
      simp [hspend.done_false, hslots]
    have hlen := htr.active_time hactive
    refine ?_
    unfold GrayChargedTrace
    have hphaseNext : (grayChargedStep q L a e sigma A
        { phase := .spend pass, core := core } (sm t)).phase =
          .spend pass := by
      simp [grayChargedStep, hslots, hgoal, deltaRound,
        current, localSM]
    rw [hphaseNext]
    simp only [grayChargedRoundDelta]
    have hcoreNext : (grayChargedStep q L a e sigma A
        { phase := .spend pass, core := core } (sm t)).core =
          { core with time := core.time + 1, history :=
              (core.history.1 ++ [current],
                core.history.2 ++ [localSM]) } := by
      simp [grayChargedStep, hslots, hgoal, deltaRound,
        current, localSM]
    rw [hcoreNext]
    refine ⟨congrArg (fun u => u + 1) htr.time_eq, ?_, ?_,
      htr.frozen_before, ?_⟩
    · intro _
      simp only [List.length_append, List.length_singleton]
      rw [<- Nat.add_assoc, hlen]
    · simp only [List.length_append, List.length_singleton]
      change
        core.history.2 ++
            [grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
              core.slots (sm t)] =
          List.ofFn
            (fun j : Fin (core.history.2.length + 1) =>
              grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                core.slots (sm (core.roundStart + j.val)))
      rw [grayTail_ofFn_succ_last_nat core.history.2.length
          (fun u =>
            grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
              core.slots (sm (core.roundStart + u))),
        <- htr.servers_eq]
      congr 2
      rw [hlen]
    · intro hterm
      exact absurd hterm (by simp [hspend.done_false, hslots])

/-- A charged step preserves the trace relation between the controller and the server play. -/
lemma grayChargedTrace_step {n b q L a e t : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayChargedState n b}
    (hcert : GrayChargedCertified q L a e sigma A sm t st)
    (htrace : GrayChargedTrace q L a e sm t st) :
    GrayChargedTrace q L a e sm (t + 1)
      (grayChargedStep q L a e sigma A st (sm t)) := by
  cases hcert with
  | done core hdone =>
      have htrace' : GrayTailTraceAt
          (grayChargedRoundDelta q L a e .done core) sm t core := htrace
      simpa [grayChargedStep, GrayChargedTrace,
        grayChargedRoundDelta] using
        grayChargedDoneTrace_tick _ hdone htrace'
  | advantage core hcore hsource hactive =>
      exact grayChargedTrace_step_advantage hcore hsource hactive htrace
  | spend pass core hspend =>
      exact grayChargedTrace_step_spend hspend htrace

/-- The charged controller state after replaying the first `t` moves of the server play `sm`. -/
def grayChargedStateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : GrayChargedState n b :=
  grayChargedFold q L a e sigma A (grayTailServerPrefix sm t)

/-- The state at time `t + 1` is one charged step applied to the state at time `t`. -/
lemma grayChargedStateAt_succ {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    grayChargedStateAt (n := n) (b := b) q L a e sigma A sm (t + 1) =
      grayChargedStep q L a e sigma A
        (grayChargedStateAt q L a e sigma A sm t) (sm t) := by
  simp [grayChargedStateAt, grayChargedFold, grayTailServerPrefix_succ]

/-- Every state of a charged run is certified. -/
theorem grayChargedCertified_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedCertified q L a e sigma A sm t
      (grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedCertified_initial q L a e sigma A sm
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      exact grayChargedCertified_step ih

/-- The core of every state of a charged run is certified. -/
theorem grayChargedCoreCertified_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedCoreCertified q L a e A sm t
      (grayChargedStateAt (n := n) (b := b) q L a e sigma A sm t).core := by
  have h := grayChargedCertified_stateAt
    (n := n) (b := b) q L a e sigma A sm t
  exact h.toCore

/-- Every state of a charged run is traced against the server play it was replayed from. -/
theorem grayChargedTrace_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedTrace q L a e sm t
      (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      unfold GrayChargedTrace
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
          grayChargedTailInitialState]
      · simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
          grayChargedTailInitialState]
      · simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
          grayChargedTailInitialState]
      · simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
          grayChargedTailInitialState]
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      exact grayChargedTrace_step
        (grayChargedCertified_stateAt q L a e sigma A sm t) ih

/-- Every state of a charged run carries a well-formed history. -/
theorem grayChargedHistoryOK_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedHistoryOK q L a e sigma
      (grayChargedStateAt (n := n) (b := b)
        q L a e sigma A sm t) := by
  induction t with
  | zero =>
      unfold GrayChargedHistoryOK
      simp [grayChargedStateAt, grayChargedFold, grayChargedInitialState,
        grayChargedTailInitialState]
  | succ t ih =>
      rw [grayChargedStateAt_succ]
      exact grayChargedHistoryOK_step _ (sm t)
        (GrayTailTraceAt.terminal_empty
          (grayChargedTrace_stateAt q L a e sigma A sm t)) ih

/-- The spend-phase future server: the same replayed truncation, at the
coarse spend delta of the pass. -/
def grayChargedSpendFutureServer {n b : ℕ}
    (a L e pass : ℕ) (st : GrayTailState n b)
    (sm : ℕ → FamilyServerMove) : ℕ → FamilyServerMove :=
  fun t =>
    grayTailLocalServerMove
      (grayChargedSpendDelta a L e pass) st.slots
      (sm (st.roundStart + t))

end Kolmogorov
