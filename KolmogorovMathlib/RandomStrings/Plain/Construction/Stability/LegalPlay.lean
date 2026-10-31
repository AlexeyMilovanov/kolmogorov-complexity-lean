/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestOpponent
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.SettledLowerLevels

/-!
# Legal play of the true-marker opponent

This module sets up the vocabulary for the blueprint lemma `constr:opponent`
(`true_marker_opponent_stream_legal`): the true-marker phase is never cancelled for exceeding the
opponent budget, and its incoming counter increments form a legal opponent play against the
controlled winning strategy.

It defines the observations of the frozen transition that the proof needs: the state just before
a level is processed in a tick (`fighterBeforeLevel`), just before its internal closure
(`fighterBeforeClosure`), and at an arbitrary step of that closure (`fighterClosureAt`).  On top
of these it states the two legality predicates `TrueMarkerClosureLegal` (every flush and every
controlled response inside a closure is a legal move) and `TrueMarkerLegalPlay` (the official
positions of the phase form one strategy-following play of a common finite counter game).

It then proves the first part of the lemma, `trueMarker_started_and_neverEndsFor_opponentExhausted`
(the phase is started and the tail bound prevents opponent exhaustion), together with the
bookkeeping facts about `fighterCancel`, `fighterAbortAbove` and `fighterPayoff` and about phase
buffers (`length_buffer_eq_of_mem_active_fighterState`) that the later modules
`OpponentStream`, `ClosureBufferInitialization` and `CommonGameInvariantTick` use to establish
closure legality and the common game.
-/

namespace Kolmogorov.Milovanov

/-- Replay the actual prefix of a tick's increasing-level service, stopping before level `l`.
Blueprint node `constr:opponent` (supporting definition). This is an observation of the
frozen transition, using its same schedule and event, not a new event clock. -/
def fighterBeforeLevel (P : FighterParams) (d tick l : ℕ) : FighterState :=
  let state := fighterState P d (tick - 1)
  let current := { state with tick := tick, schedule := masterState P.B tick }
  let event := eventAt P.B tick
  let owner := event.bind (fun e => fighterOwner d e.2.2.1.length)
  let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
  ((levels.mergeSort (· ≤ ·)).takeWhile (· < l)).foldl
    (fun s j => fighterProcessLevel P d j event s) current

/-- The actual state just before this level's internal closure at a tick.
Blueprint node `constr:opponent` (supporting definition). Pending tests, replacement,
and opponent detection are exactly the prefix of `fighterProcessLevel`. -/
def fighterBeforeClosure (P : FighterParams) (d tick l : ℕ) : FighterState :=
  let checked := fighterFulfillReady P d l (fighterBeforeLevel P d tick l)
  match eventAt P.B tick with
  | none => checked
  | some e =>
    if fighterOwner d e.2.2.1.length = some l ∧ e.2.2.1.length ≤ levelScale l ∧
        P.Admissible d l then
      fighterStartPhase P d l (e.2.2.1, e.1) checked
    else fighterOpponent P d l e.2.2 checked

/-- Observe an intermediate state of the actual finite closure, with an explicit step count.
Blueprint node `constr:opponent` (supporting definition). Steps past the first fixpoint stutter. -/
def fighterClosureAt (P : FighterParams) (d tick l step : ℕ) : FighterState :=
  fighterClosure P d l step (fighterBeforeClosure P d tick l)

/-- Each internal flush is a legal opponent move and each controlled response uses the strategy.
Blueprint node `constr:opponent` (supporting definition). Quantification includes the states
between opponent insertion and response, which are absent from the completed-tick archive. -/
def TrueMarkerClosureLegal (P : FighterParams) (d l : ℕ) : Prop :=
  ∀ tick ≥ markerTick P.B (levelScale l), ∀ step,
    step ≤ fighterClosureFuel d l (fighterBeforeClosure P d tick l) →
    let state := fighterClosureAt P d tick l step
    ∀ phase, state.activeAt d l = some phase →
      phase.candidate = markerCandidate P.B (levelScale l) →
      phase.BufferInvariant d ∧
      (∀ next, fighterFlushBuffer d l state = some next →
        (phase.game d).LegalMove (phase.official d) phase.buffer ∧
        (phase.game d).activePlayer (phase.official d) ≠ phase.controlledPlayer ∧
        ∃ afterPhase, next.activeAt d l = some afterPhase ∧
          afterPhase.officialCode =
            ((phase.game d).afterMove (phase.official d) phase.buffer).encode ∧
          afterPhase.buffer = List.replicate (phase.game d).coordinates.length 0) ∧
      (∀ next, fighterStrategyMove P d l state = some next →
        ∃ move, (phase.game d).strategy (phase.official d) = some move ∧
          (phase.game d).LegalMove (phase.official d) move ∧
          (phase.game d).activePlayer (phase.official d) = phase.controlledPlayer ∧
          ∃ afterPhase, next.activeAt d l = some afterPhase ∧
            afterPhase.officialCode =
              ((phase.game d).afterMove (phase.official d) move).encode)

/-- The official positions form one legal strategy-following play with the buffer identities.
Blueprint node `constr:opponent` (supporting definition). Finite legal paths between tick
positions retain multiple moves within a tick, and the common game fixes the initial position. -/
def TrueMarkerLegalPlay (P : FighterParams) (d l : ℕ) : Prop :=
  TrueMarkerClosureLegal P d l ∧ ∃ game : FiniteCounterGame,
    game.StrategyWins false game.strategy game.initialPosition ∧
    (∀ tick ≥ markerTick P.B (levelScale l), ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ phase.game d = game ∧
      phase.BufferInvariant d ∧
      Relation.ReflTransGen (game.StrategyStep false game.strategy) game.initialPosition
        (decodeCounterPosition game phase.officialCode)) ∧
    ∀ tick later, markerTick P.B (levelScale l) ≤ tick → tick ≤ later →
      ∀ phase nextPhase, TrueMarkerPhaseAt P d l tick phase →
        TrueMarkerPhaseAt P d l later nextPhase →
        Relation.ReflTransGen (game.StrategyStep false game.strategy)
          (decodeCounterPosition game phase.officialCode)
          (decodeCounterPosition game nextPhase.officialCode)

/-- The true-marker phase is started, and injective charging bounded by the tail-budget bound
ensures it never ends for opponent exhaustion.
Blueprint node `constr:opponent` (first part of the proof). -/
lemma trueMarker_started_and_neverEndsFor_opponentExhausted
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (_hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    TrueMarkerPhaseStarted P d l ∧ TrueMarkerNeverEndsFor P d l .opponentExhausted := by
  classical
  have hmarker : markerTick P.B (levelScale l) ≠ 0 := by
    intro hzero
    have hevent : eventAt P.B (markerTick P.B (levelScale l)) = none := by
      rw [hzero]
      rfl
    have hlength := hlate.2
    simp only [lastProgram, hevent, Option.map_none, Option.getD_none,
      List.length_nil, Nat.not_lt_zero] at hlength
  have hnonempty : ((boundedPrograms (levelScale l)).toFinset).Nonempty := by
    refine ⟨[], ?_⟩
    simp only [List.mem_toFinset, mem_boundedPrograms_iff, List.length_nil, Nat.zero_le]
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup
    (boundedPrograms (levelScale l)).toFinset hnonempty (programTick P.B)
  have hhalts : {t | ∃ i x, eventAt P.B t = some (t, i, p, x)}.Nonempty := by
    by_contra hempty
    have hzero : programTick P.B p = 0 := by
      rw [programTick, Set.not_nonempty_iff_eq_empty.mp hempty]
      exact Nat.sInf_empty
    exact hmarker (hmax.trans hzero)
  obtain ⟨i, x, hevent⟩ := Nat.sInf_mem hhalts
  change eventAt P.B (programTick P.B p) = some (programTick P.B p, i, p, x) at hevent
  rw [← hmax] at hevent
  change eventAt P.B (markerTick P.B (levelScale l)) =
    some (markerTick P.B (levelScale l), i, p, x) at hevent
  have hlast : lastProgram P.B (levelScale l) = p := by
    simp only [lastProgram, hevent, Option.map_some, Option.getD_some]
  have hlen : p.length ≤ levelScale l := by
    simpa only [List.mem_toFinset, mem_boundedPrograms_iff] using hp
  rw [← hlast] at hlen hevent
  have howner : fighterOwner d (lastProgram P.B (levelScale l)).length = some l := by
    apply ((fighter_owner_spec _ _).2 l).mpr
    have hscale : levelScale l ≤ levelUpper l :=
      tower_le_tower (by omega)
    exact ⟨hlate.1.1, hlate.2, hlen.trans hscale⟩
  have hstarted : TrueMarkerPhaseStarted P d l :=
    mem_started_fighterState_of_eventAt P d l _ i _ x
      hgood.positive hevent howner hlen hlate.1
  have hn : P.n₀ ≤ levelScale l := (le_max_right _ _).trans hlate.1.2.1
  have htail : rest P.B (levelScale l) (levelUpper l) ≤
      P.c₁ * 2 ^ (levelUpper l - levelScale l) := by
    simpa only [level_upper_eq] using P.tail_bound (levelScale l) hn
  exact ⟨hstarted, trueMarkerNeverEndsFor_opponentExhausted P d l htail⟩

/-! ### Buffer lengths -/

/-- A phase satisfies the buffer invariant, and its buffer has one entry per coordinate of its
game. Blueprint node `constr:opponent` (supporting definition). -/
def BufferShaped (d : ℕ) (p : FighterPhase) : Prop :=
  p.BufferInvariant d ∧ p.buffer.length = (p.game d).coordinates.length

/-- Every active phase of the state has a buffer with one entry per coordinate of its game. -/
private def BufferLengthsMatch (d : ℕ) (s : FighterState) : Prop :=
  ∀ p ∈ s.active, p.buffer.length = (p.game d).coordinates.length

/-- A freshly constructed phase has a zero buffer indexed by the duplicate-free list of retained
coordinates of its game. -/
private lemma length_buffer_fighter_construction (P : FighterParams) (d l : ℕ) (c : Candidate)
    (s : FighterState) :
    (fighter_construction P d l c s).buffer.length =
      ((fighter_construction P d l c s).game d).coordinates.length := by
  have hcoords (g : FiniteCounterGame) :
      g.controlWinningPlayer.coordinates = g.coordinates := by
    unfold FiniteCounterGame.controlWinningPlayer
    split <;> rfl
  dsimp only [fighter_construction, FighterPhase.fundRequests, FighterPhase.game]
  rw [decode_encode_counter_game, hcoords]
  simp only [List.length_replicate, FiniteCounterGame.coordinates, finite_counter_game]
  exact congrArg List.length (eraseDups_eq_self_of_nodup (nodup_eraseDups_list _)).symm

private lemma length_buffer_eq_of_activeAt {d l : ℕ} {s : FighterState} {p : FighterPhase}
    (hs : BufferLengthsMatch d s) (hp : s.activeAt d l = some p) :
    p.buffer.length = (p.game d).coordinates.length :=
  hs p (List.mem_of_find?_eq_some hp)

private lemma bufferLengthsMatch_foldl {α : Type} {d : ℕ} (f : α → FighterState → FighterState)
    (hf : ∀ a s, BufferLengthsMatch d s → BufferLengthsMatch d (f a s)) (xs : List α)
    {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (xs.foldl (fun s a => f a s) s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih (hf a s hs)

private lemma bufferLengthsMatch_putPhase {d : ℕ} {s : FighterState} {p : FighterPhase}
    (hs : BufferLengthsMatch d s) (hp : p.buffer.length = (p.game d).coordinates.length) :
    BufferLengthsMatch d (s.putPhase d p) := by
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs next (List.mem_filter.mp hn).1

private lemma bufferLengthsMatch_fighterCancel {d : ℕ} (l cause : ℕ) (reason : PhaseEnd)
    {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · intro p hp
    exact hs p (List.mem_filter.mp hp).1

private lemma bufferLengthsMatch_fighterAbortAbove {d : ℕ} (l : ℕ) {s : FighterState}
    (hs : BufferLengthsMatch d s) : BufferLengthsMatch d (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply bufferLengthsMatch_foldl _ _ _ hs
  intro p t ht
  split
  · exact bufferLengthsMatch_fighterCancel _ _ _ ht
  · exact ht

private lemma bufferLengthsMatch_fighterAllocate {d : ℕ} (l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (out : BitString) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none => exact bufferLengthsMatch_fighterCancel _ _ _ hs
    | some p => exact bufferLengthsMatch_fighterAbortAbove _ hs

private lemma bufferLengthsMatch_fighterPayoff (P : FighterParams) {d : ℕ} (l : ℕ)
    (q : Coordinate) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := bufferLengthsMatch_fighterAllocate l .payoff q.2 q.1 hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha old hold
    · exact hs

private lemma bufferLengthsMatch_fighterFulfillReady (P : FighterParams) {d : ℕ} (l : ℕ)
    {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact bufferLengthsMatch_foldl _ (fun q _ ↦ bufferLengthsMatch_fighterPayoff P l q) _ hs

private lemma bufferLengthsMatch_fighterFuelUnit (P : FighterParams) {d : ℕ} (l : ℕ)
    (q : Coordinate) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := length_buffer_eq_of_activeAt hs hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := bufferLengthsMatch_fighterAllocate l .fuel (levelUpper l + d) out
        (bufferLengthsMatch_putPhase hs hq : BufferLengthsMatch d (s.putPhase d charged))
      change BufferLengthsMatch d
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact bufferLengthsMatch_fighterFulfillReady P l (bufferLengthsMatch_putPhase ha hq)
    · exact hs

private lemma bufferLengthsMatch_fighterFuelUnits (P : FighterParams) {d : ℕ} (l : ℕ)
    (q : Coordinate) (count : ℕ) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (bufferLengthsMatch_fighterFuelUnit P l q hs)

private lemma bufferLengthsMatch_fighterDummy {d : ℕ} (l : ℕ) {s : FighterState}
    (hs : BufferLengthsMatch d s) : BufferLengthsMatch d (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := length_buffer_eq_of_activeAt hs hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := bufferLengthsMatch_fighterAllocate l .dummy (levelInput d l) output hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact bufferLengthsMatch_putPhase ha hq

private lemma bufferLengthsMatch_fighterOpponent (P : FighterParams) {d : ℕ} (l : ℕ)
    (e : ProgramEvent) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    split
    · exact hs
    · rename_i q index htuple
      split
      · exact hs
      · split
        · exact bufferLengthsMatch_fighterCancel _ _ _ hs
        · apply bufferLengthsMatch_fighterFulfillReady
          apply bufferLengthsMatch_putPhase hs
          change ((phase.game d).addCounters phase.buffer (phase.unitVector d q)).length =
            (phase.game d).coordinates.length
          simp only [FiniteCounterGame.addCounters, List.length_map, List.length_range]

private lemma bufferLengthsMatch_fighterStartPhase (P : FighterParams) {d : ℕ} (l : ℕ)
    (c : Candidate) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  exact bufferLengthsMatch_putPhase
    (bufferLengthsMatch_fighterAbortAbove l (bufferLengthsMatch_fighterCancel _ _ _ hs))
    (length_buffer_fighter_construction P d l c _)

private lemma bufferLengthsMatch_fighterFlushBuffer {d : ℕ} (l : ℕ) {s : FighterState}
    (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact bufferLengthsMatch_putPhase hs List.length_replicate
    · exact hs

private lemma bufferLengthsMatch_fighterStrategyMove (P : FighterParams) {d : ℕ} (l : ℕ)
    {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d ((fighterStrategyMove P d l s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) =>
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : BufferLengthsMatch d next := by
            apply bufferLengthsMatch_foldl _ _ _ hs
            intro qi t ht
            exact bufferLengthsMatch_fighterFuelUnits P l qi.1 (move[qi.2]?.getD 0) ht
          change BufferLengthsMatch d ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hlen := length_buffer_eq_of_activeAt hn hlive
            exact bufferLengthsMatch_putPhase hn hlen
        · exact hs
    · exact hs

private lemma bufferLengthsMatch_fighterLevelAction (P : FighterParams) {d : ℕ} (l : ℕ)
    {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact bufferLengthsMatch_fighterDummy l hs
    · split
      · exact bufferLengthsMatch_fighterPayoff P l _ hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact bufferLengthsMatch_fighterStrategyMove P l hs
        | some next =>
          simpa only [hf, Option.getD_some] using bufferLengthsMatch_fighterFlushBuffer l hs

private lemma bufferLengthsMatch_fighterClosure (P : FighterParams) {d : ℕ} (l fuel : ℕ)
    {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := bufferLengthsMatch_fighterLevelAction P l hs
      simp only [ha, Option.getD_some] at hn
      exact ih hn

private lemma bufferLengthsMatch_fighterProcessLevel (P : FighterParams) {d : ℕ} (l : ℕ)
    (e : Option TimedEvent) {s : FighterState} (hs : BufferLengthsMatch d s) :
    BufferLengthsMatch d (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply bufferLengthsMatch_fighterClosure
  have hready := bufferLengthsMatch_fighterFulfillReady P l hs
  cases e with
  | none => exact hready
  | some e =>
    dsimp only
    split
    · exact bufferLengthsMatch_fighterStartPhase P l _ hready
    · exact bufferLengthsMatch_fighterOpponent P l _ hready

/-- Every phase of the fighter state at any tick has a buffer with one entry per coordinate of its
game. Blueprint node `constr:opponent` (supporting lemma). -/
lemma length_buffer_eq_of_mem_active_fighterState (P : FighterParams) (d tick : ℕ) :
    ∀ phase ∈ (fighterState P d tick).active,
      phase.buffer.length = (phase.game d).coordinates.length := by
  suffices BufferLengthsMatch d (fighterState P d tick) from this
  induction tick with
  | zero => simp [fighterState, initialFighterState, BufferLengthsMatch]
  | succ tick ih =>
    change BufferLengthsMatch d (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [BufferLengthsMatch, initialFighterState]
    · exact bufferLengthsMatch_foldl
        (fun l s ↦ fighterProcessLevel P d l (eventAt P.B (tick + 1)) s)
        (fun l _ hs ↦ bufferLengthsMatch_fighterProcessLevel P l _ hs) _ ih

/-! ### Cancellation, abortion and payoff do not create higher-level phases -/

private lemma activeAt_fighterCancel_aborted_eq_none (d l cause : ℕ) (s : FighterState) :
    (fighterCancel d l .aborted cause s).activeAt d l = none := by
  unfold fighterCancel
  cases hs : s.activeAt d l
  · exact hs
  · simp [FighterState.activeAt, List.find?_filter]

/-- If the fold of aborting every phase above `j` starts from a state with no phase at level
`l > j`, or from a list that contains a phase of level `l`, then it ends with no phase at `l`. -/
private lemma activeAt_foldl_abort_eq_none (d j l : ℕ) (ps : List FighterPhase)
    (s : FighterState) (hjl : j < l)
    (h : s.activeAt d l = none ∨ ∃ p ∈ ps, p.level = l) :
    (ps.foldl (fun s p => if j < p.level then fighterCancel d p.level .aborted j s else s)
      s).activeAt d l = none := by
  induction ps generalizing s with
  | nil =>
    rcases h with h_none | ⟨p, hp_mem, _⟩
    · exact h_none
    · contradiction
  | cons p ps ih =>
    rw [List.foldl_cons]
    by_cases hpj : j < p.level
    · by_cases hpl : p.level = l
      · have h_cancel : (fighterCancel d p.level .aborted j s).activeAt d l = none := by
          rw [hpl]
          exact activeAt_fighterCancel_aborted_eq_none d l j s
        simp only [hpj, ite_true]
        exact ih (fighterCancel d p.level .aborted j s) (Or.inl h_cancel)
      · have h_cancel : (fighterCancel d p.level .aborted j s).activeAt d l = s.activeAt d l :=
          activeAt_fighterCancel_eq_of_ne d p.level l .aborted j s hpl
        simp only [hpj, ite_true]
        rcases h with h_none | ⟨p', hp_mem, hp_eq⟩
        · exact ih _ (Or.inl (h_cancel.trans h_none))
        · simp only [List.mem_cons] at hp_mem
          rcases hp_mem with rfl | hp_mem
          · exact absurd hp_eq hpl
          · exact ih _ (Or.inr ⟨p', hp_mem, hp_eq⟩)
    · simp only [hpj, ite_false]
      rcases h with h_none | ⟨p', hp_mem, hp_eq⟩
      · exact ih s (Or.inl h_none)
      · simp only [List.mem_cons] at hp_mem
        rcases hp_mem with rfl | hp_mem
        · exact absurd (hp_eq ▸ hjl) hpj
        · exact ih s (Or.inr ⟨p', hp_mem, hp_eq⟩)

/-- Aborting all phases above level `j` leaves no phase at any higher level `l`. -/
lemma activeAt_fighterAbortAbove_eq_none_of_lt (d j l : ℕ) (state : FighterState)
    (hjl : j < l) : (fighterAbortAbove d j state).activeAt d l = none := by
  unfold fighterAbortAbove
  cases h : state.activeAt d l
  · exact activeAt_foldl_abort_eq_none d j l state.active state hjl (Or.inl h)
  · refine activeAt_foldl_abort_eq_none d j l state.active state hjl (Or.inr ?_)
    unfold FighterState.activeAt at h
    have h_some := List.find?_some h
    exact ⟨_, List.mem_of_find?_eq_some h, beq_iff_eq.mp h_some⟩

/-- Mapping a level-preserving function over a list of phases preserves the absence of a phase
at a given level. -/
private lemma find?_level_map_eq_none (x : ℕ) (active : List FighterPhase)
    (f : FighterPhase → FighterPhase) (h_level : ∀ p, (f p).level = p.level)
    (h_none : List.find? (fun p => p.level == x) active = none) :
    List.find? (fun p => p.level == x) (active.map f) = none := by
  induction active with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.find?_cons] at h_none
    cases h_p : (p.level == x)
    · simp only [h_p] at h_none
      have h_f : ((f p).level == x) = false := by
        rw [h_level p]
        exact h_p
      simp only [List.map_cons, List.find?_cons, h_f]
      exact ih h_none
    · simp only [h_p] at h_none
      contradiction

/-- A payoff action at level `j` does not create a phase at a higher level `l`: any phase found at
`l` afterwards was already present before. -/
lemma activeAt_eq_of_fighterPayoff_activeAt_eq_some (P : FighterParams) (d j l : ℕ)
    (q : Coordinate) (state : FighterState) (hjl : j < l) :
    ∀ phase, (fighterPayoff P d j q state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterPayoff at hphase
  cases h_active : state.activeAt d j with
  | none =>
    simp only [h_active] at hphase
    exact hphase
  | some val =>
    simp only [h_active] at hphase
    by_cases h_cond : q ∈ val.pending ∧ q ∉ state.fulfilled ∧ fighterSafe P d state.tick q = true
    · simp only [ite_eq_left_iff.mpr (fun hc => (hc h_cond).elim)] at hphase
      cases h_alloc : fighterAllocate d j DirectiveKind.payoff q.2 q.1 state with
      | mk next success =>
        simp only [h_alloc] at hphase
        cases success
        · simp only [Bool.false_eq_true, ite_false] at hphase
          unfold fighterAllocate at h_alloc
          simp only [h_active] at h_alloc
          split at h_alloc
          · injection h_alloc with h_next _
            rw [← h_next, activeAt_fighterCancel_eq_of_ne d j l .saturated j _ (ne_of_lt hjl)]
              at hphase
            exact hphase
          · injection h_alloc with _ h_true_eq_false
            contradiction
        · simp only [reduceIte] at hphase
          unfold fighterAllocate at h_alloc
          simp only [h_active] at h_alloc
          split at h_alloc
          · injection h_alloc with _ h_false_eq_true
            contradiction
          · rename_i p_fresh h_fresh
            injection h_alloc with h_next _
            have h_abort := activeAt_fighterAbortAbove_eq_none_of_lt d j l
              { state with allocated := state.allocated ++
                [AllocatedDirective.mk j val.candidate state.tick DirectiveKind.payoff q.2
                  p_fresh q.1] } hjl
            unfold FighterState.activeAt at h_abort hphase
            rw [← h_next, find?_level_map_eq_none l _
              (fun p => { p with pending := p.pending.filter (fun r => r != q) })
              (fun _ ↦ rfl) h_abort] at hphase
            contradiction
    · simp only [ite_eq_right_iff.mpr (fun hc => (h_cond hc).elim)] at hphase
      exact hphase

end Kolmogorov.Milovanov
