/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGame
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.EventuallyBounded

/-!
# The true-marker opponent stream is legal

This module proves blueprint node `constr:opponent`, a stability fact about the true-marker
phase of the fighter construction: the phase is never canceled for exhausting the opponent
budget, the stream of incoming counter increments is a legal opponent play against the
controlled winning strategy, and the live output eventually satisfies the predicate `P`.

The argument tracks the buffering policy of the fighter phase. A purely administrative view of a
phase (`officialPhaseView`) is shown to be preserved by payoffs, fuel purchases, dummy
allocations and by the servicing of other levels. With it, the policy "an official controlled
turn has an empty buffer" is preserved by closure, by level processing and by a whole master
tick. Hence at a completed tick the official game is on the opponent's turn: a controlled turn
with an empty buffer would enable the winning strategy's response, and an opponent turn with a
false live predicate would enable the affordable buffered flush, both contradicting completion
of the enabled actions.

The main result `true_marker_opponent_stream_legal` combines this with the common winning game
of `CommonGame` and the fuel-batch preservation lemma of `EventuallyBounded`; it is used by the
diagonal simulation to compare the constructed oracle with its finite game.
-/

namespace Kolmogorov.Milovanov

/-- A zero-sum buffer leaves every counter answer unchanged, even with a malformed counter-vector
length. -/
private lemma answers_eq_of_buffer_sum_zero
    (game : FiniteCounterGame) (counters buffer : List ℕ)
    (hzero : buffer.sum = 0) :
    game.counterAnswer (game.addCounters counters buffer) = game.counterAnswer counters := by
  have hget (i : ℕ) : buffer[i]?.getD 0 = 0 := by
    cases he : buffer[i]? with
    | none => rfl
    | some a =>
      have hmem : a ∈ buffer := List.mem_of_getElem? he
      have hle := List.single_le_sum (fun n _ ↦ Nat.zero_le n) a hmem
      simp only [Option.getD_some]
      omega
  have hvalue : game.coordinateValue (game.addCounters counters buffer) =
      game.coordinateValue counters := by
    funext q
    by_cases hq : q ∈ game.coordinates
    · have hi : game.coordinates.idxOf q < game.coordinates.length :=
        List.idxOf_lt_length_iff.mpr hq
      simp [FiniteCounterGame.coordinateValue, hq, FiniteCounterGame.addCounters,
        List.getElem?_range hi, hget]
    · simp [FiniteCounterGame.coordinateValue, hq]
  funext q
  simp only [FiniteCounterGame.counterAnswer, hvalue]

/-- A false live predicate on the opponent's official turn enables the affordable buffered
opponent move. -/
private lemma flushBuffer_enabled_of_opponent_turn
    (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hs : state.activeAt d l = some phase)
    (hinv : phase.BufferInvariant d)
    (hlen : phase.buffer.length = (phase.game d).coordinates.length)
    (hfalse : phase.predicateHolds d = false)
    (hturn : (phase.game d).activePlayer (phase.official d) ≠
      phase.controlledPlayer) :
    fighterFlushBuffer d l state ≠ none := by
  have hactive : (phase.game d).activePlayer (phase.official d) = true := by
    rw [hinv.1] at hturn
    cases ha : (phase.game d).activePlayer (phase.official d) <;> simp_all
  have hpos : 0 < phase.buffer.sum := by
    by_contra hn
    have hz : phase.buffer.sum = 0 := by omega
    have hans := answers_eq_of_buffer_sum_zero
      (phase.game d) (phase.official d).counters phase.buffer hz
    have hout : phase.virtualOutput d = (phase.game d).output (phase.official d) := by
      dsimp [FighterPhase.virtualOutput, FiniteCounterGame.output]
      rw [hinv.2.1, hans]
    have hobj := (counter_game_active_objectives (phase.game d) (phase.official d)).2
    rw [hactive] at hobj
    simp only [Bool.not_true] at hobj
    unfold FighterPhase.predicateHolds at hfalse
    rw [hinv.1, hout, hobj] at hfalse
    contradiction
  have hmove : (phase.game d).LegalMove (phase.official d) phase.buffer := by
    refine ⟨hlen, hpos, ?_, ?_⟩
    · simp only [CounterPosition.remaining, hactive, ite_true]
      rw [hinv.2.2.2]
      omega
    · rw [hactive, ← hinv.2.1]
      change (phase.game d).objective true (phase.virtualOutput d) = true
      unfold FighterPhase.predicateHolds at hfalse
      rw [hinv.1] at hfalse
      cases hp : (phase.game d).equalityPlayer <;>
        by_cases ho : phase.virtualOutput d = (phase.game d).target <;>
        simp_all [FiniteCounterGame.objective]
  simp [fighterFlushBuffer, hs, hfalse, hturn, hmove]

/-- A reachable winning controlled turn with an empty buffer enables a selected legal response. -/
private lemma strategyMove_enabled_of_controlled_turn
    (P : FighterParams) (d l : ℕ)
    (state : FighterState) (phase : FighterPhase)
    (hs : state.activeAt d l = some phase)
    (hinv : phase.BufferInvariant d)
    (hfalse : phase.predicateHolds d = false)
    (hzero : phase.buffer.sum = 0)
    (hturn : (phase.game d).activePlayer (phase.official d) =
      phase.controlledPlayer)
    (hwins : (phase.game d).StrategyWins false
      (phase.game d).strategy (phase.game d).initialPosition)
    (hpath : Relation.ReflTransGen
      ((phase.game d).StrategyStep false (phase.game d).strategy)
      (phase.game d).initialPosition (phase.official d)) :
    fighterStrategyMove P d l state ≠ none := by
  have hactive : (phase.game d).activePlayer (phase.official d) = false :=
    hturn.trans hinv.1
  have hobj := (counter_game_active_objectives (phase.game d) (phase.official d)).1
  rw [hactive] at hobj
  have hwin := hwins (phase.official d) hpath
  have hnterm : ¬ (phase.game d).Terminal (phase.official d) := by
    intro hterm
    have hw := hwin.1 hterm
    rw [hobj] at hw
    contradiction
  obtain ⟨move, hm, hmove⟩ := hwin.2 hactive hnterm
  have hcost : move.sum ≤ phase.controlledRemaining := by
    have hc := hmove.2.2.1
    simpa only [CounterPosition.remaining, hactive, Bool.false_eq_true, ite_false,
      hinv.2.2.1] using hc
  simp only [fighterStrategyMove, hs, bind, Option.bind_some]
  simp only [hfalse, hzero, hturn, and_self, ite_true, hm, Option.bind_some,
    hmove, hcost]
  split <;> simp

/-- The fields relevant to the buffering policy, with all administrative fields erased. -/
private def officialPhaseView
    (p : FighterPhase) : FighterPhase :=
  ⟨p.level, p.candidate, ([], [], []), [], p.gameCode, [], p.officialCode,
    [], 0, 0, p.buffer, [], none, false, p.controlledPlayer⟩

/-- Payoffs, fuel purchases, and dummy allocations preserve any invariant of the official
position, buffer, game, and phase identity in every surviving record. -/
private lemma officialPhaseView_passive_actions
    (P : FighterParams) (d : ℕ) (Q : FighterPhase → Prop) :
    let Good := fun s : FighterState ↦ ∀ p ∈ s.active,
      Q (officialPhaseView p)
    (∀ l q s, Good s → Good (fighterPayoff P d l q s)) ∧
    (∀ l s, Good s → Good (fighterFulfillReady P d l s)) ∧
    (∀ l q count s, Good s → Good (fighterFuelUnits P d l q count s)) ∧
    (∀ l s, Good s → Good (fighterDummy d l s)) := by
  let view := officialPhaseView
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active, Q (view p)
  have hlookup {s : FighterState} {l : ℕ} {p : FighterPhase}
      (hs : Good s) (hp : s.activeAt d l = some p) : Q (view p) :=
    hs p (List.mem_of_find?_eq_some hp)
  have hfold {α : Type} (f : α → FighterState → FighterState)
      (hf : ∀ a s, Good s → Good (f a s)) (xs : List α) (s : FighterState)
      (hs : Good s) : Good (xs.foldl (fun s a ↦ f a s) s) := by
    induction xs generalizing s with
    | nil => exact hs
    | cons a xs ih => exact ih _ (hf a s hs)
  have hput (s : FighterState) (p : FighterPhase) (hs : Good s)
      (hp : Q (view p)) : Good (s.putPhase d p) := by
    intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs next (List.mem_filter.mp hn).1
  have hcancel (l cause : ℕ) (reason : PhaseEnd) (s : FighterState) (hs : Good s) :
      Good (fighterCancel d l reason cause s) := by
    unfold fighterCancel
    split
    · exact hs
    · intro p hp
      exact hs p (List.mem_filter.mp hp).1
  have habort (l : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterAbortAbove d l s) := by
    unfold fighterAbortAbove
    apply hfold _ _ _ _ hs
    intro p t ht
    split
    · exact hcancel _ _ _ _ ht
    · exact ht
  have halloc (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
      (s : FighterState) (hs : Good s) :
      Good (fighterAllocate d l kind target out s).1 := by
    unfold fighterAllocate
    split
    · exact hs
    · cases hf : (if target = 0 then (none : Option BitString) else
          (fighterInputs d (target - 1)).find? (fun p ↦
            !s.allocated.any (fun a ↦ a.input == p))) with
      | none => exact hcancel _ _ _ _ hs
      | some p => exact habort _ _ hs
  have hpay (l : ℕ) (q : Coordinate) (s : FighterState) (hs : Good s) :
      Good (fighterPayoff P d l q s) := by
    unfold fighterPayoff
    split
    · exact hs
    · split
      · have ha := halloc l .payoff q.2 q.1 s hs
        cases he : fighterAllocate d l .payoff q.2 q.1 s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · intro p hp
            obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
            exact ha old hold
      · exact hs
  have hfulfill (l : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterFulfillReady P d l s) := by
    unfold fighterFulfillReady
    split
    · exact hs
    · exact hfold _ (hpay l) _ _ hs
  have hunit (l : ℕ) (q : Coordinate) (s : FighterState) (hs : Good s) :
      Good (fighterFuelUnit P d l q s) := by
    unfold fighterFuelUnit
    split
    · exact hs
    · rename_i phase hp
      have hq := hlookup hs hp
      split
      · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
        let index := fighterFreshString d
          (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
        let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
        have ha := halloc l .fuel (levelUpper l + d) out (s.putPhase d charged)
          (hput s charged hs hq)
        change Good
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
          · exact hfulfill l _ (hput next _ ha hq)
      · exact hs
  have hunits (l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterFuelUnits P d l q count s) := by
    induction count generalizing s with
    | zero => exact hs
    | succ count ih => exact ih _ (hunit l q s hs)
  have hdummy (l : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterDummy d l s) := by
    unfold fighterDummy
    split
    · exact hs
    · rename_i phase hp
      have hq := hlookup hs hp
      split
      · exact hs
      · rename_i output hout
        split
        · exact hs
        · have ha := halloc l .dummy (levelInput d l) output s hs
          cases he : fighterAllocate d l .dummy (levelInput d l) output s with
          | mk next success =>
            simp only [he] at ha ⊢
            cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
            · exact ha
            · exact hput next _ ha hq
  exact ⟨hpay, hfulfill, hunits, hdummy⟩

/-- Servicing a different level preserves every invariant of the tracked phase's official
position, buffer, game, and identity in all records that survive. -/
private lemma officialPhaseView_processLevel_of_ne
    (P : FighterParams) (d k l : ℕ) (hne : k ≠ l)
    (event : Option TimedEvent) (Q : FighterPhase → Prop)
    (state : FighterState)
    (hs : ∀ p ∈ state.active, p.level = l →
      Q (officialPhaseView p)) :
    ∀ p ∈ (fighterProcessLevel P d k event state).active, p.level = l →
      Q (officialPhaseView p) := by
  let view := officialPhaseView
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active, p.level = l → Q (view p)
  obtain ⟨hpay, hfulfill, hunits, hdummy⟩ :=
    officialPhaseView_passive_actions
      P d (fun p ↦ p.level = l → Q p)
  have hfold {α : Type} (f : α → FighterState → FighterState)
      (hf : ∀ a s, Good s → Good (f a s)) (xs : List α) (s : FighterState)
      (hs : Good s) : Good (xs.foldl (fun s a ↦ f a s) s) := by
    induction xs generalizing s with
    | nil => exact hs
    | cons a xs ih => exact ih _ (hf a s hs)
  have hput (s : FighterState) (p : FighterPhase) (hs : Good s)
      (hp : p.level = k) : Good (s.putPhase d p) := by
    intro next hn hl
    rcases List.mem_cons.mp hn with rfl | hn
    · exact (hne (hp.symm.trans hl)).elim
    · exact hs next (List.mem_filter.mp hn).1 hl
  have hcancel (j cause : ℕ) (reason : PhaseEnd) (s : FighterState) (hs : Good s) :
      Good (fighterCancel d j reason cause s) := by
    unfold fighterCancel
    split
    · exact hs
    · intro p hp
      exact hs p (List.mem_filter.mp hp).1
  have habort (s : FighterState) (hs : Good s) : Good (fighterAbortAbove d k s) := by
    unfold fighterAbortAbove
    apply hfold _ _ _ _ hs
    intro p t ht
    split
    · exact hcancel _ _ _ _ ht
    · exact ht
  have hstart (c : Candidate) (s : FighterState) (hs : Good s) :
      Good (fighterStartPhase P d k c s) := by
    unfold fighterStartPhase
    exact hput _ _ (habort _ (hcancel _ _ _ _ hs)) rfl
  have hopponent (e : ProgramEvent) (s : FighterState) (hs : Good s) :
      Good (fighterOpponent P d k e s) := by
    unfold fighterOpponent
    split
    · exact hs
    · rename_i phase hp
      have hlevel : phase.level = k :=
        beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == k) hp)
      split
      · exact hs
      · split
        · exact hs
        · split
          · exact hcancel _ _ _ _ hs
          · apply hfulfill k
            exact hput _ _ hs hlevel
  have hflush (s : FighterState) (hs : Good s) :
      Good ((fighterFlushBuffer d k s).getD s) := by
    unfold fighterFlushBuffer
    cases hp : s.activeAt d k with
    | none => exact hs
    | some phase =>
      have hlevel : phase.level = k :=
        beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == k) hp)
      simp only [bind, Option.bind_some]
      split
      · exact hput _ _ hs hlevel
      · exact hs
  have hstrategy (s : FighterState) (hs : Good s) :
      Good ((fighterStrategyMove P d k s).getD s) := by
    unfold fighterStrategyMove
    cases hp : s.activeAt d k with
    | none => exact hs
    | some phase =>
      simp only [bind, Option.bind_some]
      split
      · cases hm : (phase.game d).strategy (phase.official d) with
        | none => exact hs
        | some move =>
          simp only [Option.bind_some]
          split
          · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
              fighterFuelUnits P d k q (move[i]?.getD 0) s) s
            have hn : Good next := by
              apply hfold _ _ _ _ hs
              intro qi t ht
              exact hunits k qi.1 (move[qi.2]?.getD 0) t ht
            change Good ((match next.activeAt d k with
              | none => some next
              | some live => some (next.putPhase d
                { live with officialCode :=
                    ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
            cases hlive : next.activeAt d k with
            | none => exact hn
            | some live =>
              have hlevel : live.level = k := beq_iff_eq.mp
                (List.find?_some (p := fun p : FighterPhase ↦ p.level == k) hlive)
              exact hput next _ hn hlevel
          · exact hs
      · exact hs
  have haction (s : FighterState) (hs : Good s) :
      Good ((fighterLevelAction P d k s).getD s) := by
    unfold fighterLevelAction
    cases hp : s.activeAt d k with
    | none => exact hs
    | some phase =>
      simp only [bind, Option.bind_some]
      split
      · exact hdummy k s hs
      · split
        · exact hpay k _ s hs
        · cases hf : fighterFlushBuffer d k s with
          | none => exact hstrategy s hs
          | some next =>
            have h := hflush s hs
            simpa only [hf, Option.getD_some] using h
  have hclosure (fuel : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterClosure P d k fuel s) := by
    induction fuel generalizing s with
    | zero => exact hs
    | succ fuel ih =>
      simp only [fighterClosure]
      cases ha : fighterLevelAction P d k s with
      | none => exact hs
      | some next =>
        have hn := haction s hs
        simp only [ha, Option.getD_some] at hn
        exact ih next hn
  unfold fighterProcessLevel fighterCloseLevel
  apply hclosure
  cases event with
  | none => exact hfulfill k state hs
  | some e =>
    dsimp only
    split
    · exact hstart _ _ (hfulfill k state hs)
    · exact hopponent _ _ (hfulfill k state hs)

/-- Internal closure preserves the policy that an official controlled turn has an empty buffer. A
flush resets the buffer, and the guarded controlled response preserves that empty buffer
throughout its fuel batch. -/
private lemma empty_buffer_on_controlled_turn_closure
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (fuel : ℕ)
    (state : FighterState)
    (hs : ∀ p ∈ state.active, p.level = l → p.candidate = candidate →
      (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0) :
    ∀ p ∈ (fighterClosure P d l fuel state).active,
      p.level = l → p.candidate = candidate →
      (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0 := by
  let view := officialPhaseView
  let Q := fun p : FighterPhase ↦ p.level = l → p.candidate = candidate →
    (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active, Q p
  obtain ⟨hpay, hfulfill, hunits, hdummy⟩ :=
    officialPhaseView_passive_actions P d Q
  have hput (s : FighterState) (p : FighterPhase) (hs : Good s)
      (hp : Q p) : Good (s.putPhase d p) := by
    intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs next (List.mem_filter.mp hn).1
  have hfold {α : Type} (f : α → FighterState → FighterState)
      (hf : ∀ a s, Good s → Good (f a s)) (xs : List α) (s : FighterState)
      (hs : Good s) : Good (xs.foldl (fun s a ↦ f a s) s) := by
    induction xs generalizing s with
    | nil => exact hs
    | cons a xs ih => exact ih _ (hf a s hs)
  have hflush (s : FighterState) (hs : Good s) :
      Good ((fighterFlushBuffer d l s).getD s) := by
    unfold fighterFlushBuffer
    cases hp : s.activeAt d l with
    | none => exact hs
    | some phase =>
      simp only [bind, Option.bind_some]
      split
      · apply hput s _ hs
        intro _ _ _
        change (List.replicate (phase.game d).coordinates.length 0).sum = 0
        simp
      · exact hs
  have hstrategy (s : FighterState) (hs : Good s) :
      Good ((fighterStrategyMove P d l s).getD s) := by
    unfold fighterStrategyMove
    cases hp : s.activeAt d l with
    | none => exact hs
    | some phase =>
      simp only [bind, Option.bind_some]
      split
      · rename_i hguard
        cases hm : (phase.game d).strategy (phase.official d) with
        | none => exact hs
        | some move =>
          simp only [Option.bind_some]
          split
          · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
              fighterFuelUnits P d l q (move[i]?.getD 0) s) s
            have hn : Good next := by
              apply hfold _ _ _ _ hs
              intro qi t ht
              exact hunits l qi.1 (move[qi.2]?.getD 0) t ht
            change Good ((match next.activeAt d l with
              | none => some next
              | some live => some (next.putPhase d
                { live with officialCode :=
                    ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
            cases hlive : next.activeAt d l with
            | none => exact hn
            | some live =>
              obtain ⟨old, hold, -, hbuffer⟩ :=
                gameCode_buffer_eq_of_fuelBatch
                  P d l (phase.game d).coordinates move s live hlive
              rw [hp] at hold
              cases hold
              apply hput next _ hn
              intro _ _ _
              exact (congrArg List.sum hbuffer).trans hguard.2.1
          · exact hs
      · exact hs
  have haction (s : FighterState) (hs : Good s) :
      Good ((fighterLevelAction P d l s).getD s) := by
    unfold fighterLevelAction
    cases hp : s.activeAt d l with
    | none => exact hs
    | some phase =>
      simp only [bind, Option.bind_some]
      split
      · exact hdummy l s hs
      · split
        · exact hpay l _ s hs
        · cases hf : fighterFlushBuffer d l s with
          | none => exact hstrategy s hs
          | some next =>
            have h := hflush s hs
            simpa only [hf, Option.getD_some] using h
  induction fuel generalizing state with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l state with
    | none => exact hs
    | some next =>
      have hn := haction state hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

/-- If the tracked phase enters its level service on an opponent official turn, event processing
and completed closure preserve the controlled-turn empty-buffer policy. A new phase starts with a
zero buffer. -/
private lemma empty_buffer_on_controlled_turn_processLevel
    (P : FighterParams) (d l : ℕ) (candidate : Candidate)
    (event : Option TimedEvent) (state : FighterState)
    (hs : ∀ p ∈ state.active, p.level = l → p.candidate = candidate →
      (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer) :
    ∀ p ∈ (fighterProcessLevel P d l event state).active,
      p.level = l → p.candidate = candidate →
      (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0 := by
  let Strong := fun s : FighterState ↦ ∀ p ∈ s.active, p.level = l →
    p.candidate = candidate → (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer
  let Q := fun p : FighterPhase ↦ p.level = l → p.candidate = candidate →
    (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active, Q p
  have hweak (s : FighterState) (hs : Strong s) : Good s := by
    intro p hp hl hc ht
    exact (hs p hp hl hc ht).elim
  obtain ⟨_, hfulfill, _, _⟩ :=
    officialPhaseView_passive_actions P d
      (fun p ↦ p.level = l → p.candidate = candidate →
        (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer)
  have hput_strong (s : FighterState) (p : FighterPhase) (hs : Strong s)
      (hp : p.level = l → p.candidate = candidate →
        (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer) :
      Strong (s.putPhase d p) := by
    intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs next (List.mem_filter.mp hn).1
  have hcancel_strong (reason : PhaseEnd) (s : FighterState) (hs : Strong s) :
      Strong (fighterCancel d l reason l s) := by
    unfold fighterCancel
    split
    · exact hs
    · intro p hp
      exact hs p (List.mem_filter.mp hp).1
  have hopponent (e : ProgramEvent) (s : FighterState) (hs : Strong s) :
      Strong (fighterOpponent P d l e s) := by
    unfold fighterOpponent
    split
    · exact hs
    · rename_i phase hp
      have hq := hs phase (List.mem_of_find?_eq_some hp)
      split
      · exact hs
      · split
        · exact hs
        · split
          · exact hcancel_strong _ _ hs
          · apply hfulfill l
            exact hput_strong _ _ hs hq
  have hput (s : FighterState) (p : FighterPhase) (hs : Good s)
      (hp : Q p) : Good (s.putPhase d p) := by
    intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs next (List.mem_filter.mp hn).1
  have hcancel (j cause : ℕ) (reason : PhaseEnd) (s : FighterState) (hs : Good s) :
      Good (fighterCancel d j reason cause s) := by
    unfold fighterCancel
    split
    · exact hs
    · intro p hp
      exact hs p (List.mem_filter.mp hp).1
  have habort (s : FighterState) (hs : Good s) : Good (fighterAbortAbove d l s) := by
    have hfold (ps : List FighterPhase) (s : FighterState) (hs : Good s) :
        Good (ps.foldl (fun s p ↦ if l < p.level then
          fighterCancel d p.level .aborted l s else s) s) := by
      induction ps generalizing s with
      | nil => exact hs
      | cons p ps ih =>
        rw [List.foldl_cons]
        split
        · exact ih _ (hcancel _ _ _ _ hs)
        · exact ih _ hs
    exact hfold _ s hs
  have hstart (c : Candidate) (s : FighterState) (hs : Good s) :
      Good (fighterStartPhase P d l c s) := by
    unfold fighterStartPhase
    apply hput _ _ (habort _ (hcancel _ _ _ _ hs))
    intro _ _ _
    simp [fighter_construction, FighterPhase.fundRequests]
  unfold fighterProcessLevel fighterCloseLevel
  apply empty_buffer_on_controlled_turn_closure
    P d l candidate
  cases event with
  | none => exact hweak _ (hfulfill l state hs)
  | some e =>
    dsimp only
    split
    · exact hstart _ _ (hweak _ (hfulfill l state hs))
    · exact hweak _ (hopponent _ _ (hfulfill l state hs))

/-- One master tick preserves the controlled-turn empty-buffer policy when all incoming records of
the tracked identity are on the opponent's official turn. The deduplicated level schedule services
that level at most once. -/
private lemma empty_buffer_on_controlled_turn_tick
    (P : FighterParams) (d l tick : ℕ) (candidate : Candidate) (state : FighterState)
    (hs : ∀ p ∈ state.active, p.level = l → p.candidate = candidate →
      (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer) :
    ∀ p ∈ (fighter_actions P d tick state).active,
      p.level = l → p.candidate = candidate →
      (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0 := by
  let Strong := fun s : FighterState ↦ ∀ p ∈ s.active, p.level = l →
    p.candidate = candidate → (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active, p.level = l →
    p.candidate = candidate → (p.game d).activePlayer (p.official d) = p.controlledPlayer →
      p.buffer.sum = 0
  have hweak (s : FighterState) (hs : Strong s) : Good s := by
    intro p hp hl hc ht
    exact (hs p hp hl hc ht).elim
  have hother (k : ℕ) (hne : k ≠ l) (s : FighterState) (hs : Good s) :
      Good (fighterProcessLevel P d k (eventAt P.B tick) s) :=
    officialPhaseView_processLevel_of_ne
      P d k l hne (eventAt P.B tick)
      (fun p ↦ p.candidate = candidate →
        (p.game d).activePlayer (p.official d) = p.controlledPlayer → p.buffer.sum = 0)
      s hs
  have hfold_other (levels : List ℕ) (hlevels : ∀ k ∈ levels, k ≠ l)
      (s : FighterState) (hs : Good s) :
      Good (levels.foldl (fun s k ↦ fighterProcessLevel P d k (eventAt P.B tick) s) s) := by
    induction levels generalizing s with
    | nil => exact hs
    | cons k levels ih =>
      exact ih (fun j hj ↦ hlevels j (List.mem_cons_of_mem k hj)) _
        (hother k (hlevels k (List.mem_cons_self)) s hs)
  have hfold (levels : List ℕ) (hlevels : levels.Nodup)
      (s : FighterState) (hs : Strong s) :
      Good (levels.foldl (fun s k ↦ fighterProcessLevel P d k (eventAt P.B tick) s) s) := by
    induction levels generalizing s with
    | nil => exact hweak s hs
    | cons k levels ih =>
      obtain ⟨hk, ht⟩ := List.nodup_cons.mp hlevels
      rw [List.foldl_cons]
      by_cases hkl : k = l
      · subst k
        apply hfold_other levels
        · intro j hj heq
          subst j
          exact hk hj
        · exact
            empty_buffer_on_controlled_turn_processLevel
              P d l candidate (eventAt P.B tick) s hs
      · apply ih ht
        exact
          officialPhaseView_processLevel_of_ne
            P d k l hkl (eventAt P.B tick)
            (fun p ↦ p.candidate = candidate →
              (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer)
            s hs
  unfold fighter_actions
  split
  · simp [initialFighterState]
  · apply hfold
    · rw [List.nodup_mergeSort]
      exact nodup_eraseDups_list _
    · exact hs

/-- At a completed true-marker tick the official turn belongs to the opponent. Induction uses the
tick policy; an empty-buffer controlled turn would admit a legal winning response, contradicting
completion of enabled actions. -/
private lemma official_opponent_turn_of_completed_tick
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d)
    (hlegal : TrueMarkerLegalPlay P d l)
    (tick : ℕ) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase) :
    (phase.game d).activePlayer (phase.official d) ≠ phase.controlledPlayer := by
  let Strong := fun s : FighterState ↦ ∀ p ∈ s.active, p.level = l →
    p.candidate = markerCandidate P.B (levelScale l) →
      (p.game d).activePlayer (p.official d) ≠ p.controlledPlayer
  have hall : ∀ tick, Strong (fighterState P d tick) := by
    intro tick
    induction tick with
    | zero => simp [Strong, fighterState, initialFighterState]
    | succ tick ih =>
      have hpolicy :=
        empty_buffer_on_controlled_turn_tick
          P d l (tick + 1) (markerCandidate P.B (levelScale l)) (fighterState P d tick) ih
      intro p hp hl hc hturn
      have hzero : p.buffer.sum = 0 := hpolicy p hp hl hc hturn
      have htime :=
        (fighterState_candidates_le_tick P d (tick + 1)).1 p hp
      rw [hc] at htime
      change markerTick P.B (levelScale l) ≤ tick + 1 at htime
      have hlookup : (fighterState P d (tick + 1)).activeAt d l = some p :=
        FighterState.activeAt_eq_some_of_mem d l _ p
          (fighterState_active_levels_nodup P d (tick + 1) hd) hp hl
      have hplay := hlegal.2
      obtain ⟨game, hwins, hticks, _⟩ := hplay
      obtain ⟨other, hother, hgame, hinv, hpath⟩ := hticks (tick + 1) htime
      have heq : p = other := Option.some.inj (hlookup.symm.trans hother.2.2.2)
      subst other
      have hans :=
        answers_eq_of_buffer_sum_zero
          (p.game d) (p.official d).counters p.buffer hzero
      have hout : p.virtualOutput d = (p.game d).output (p.official d) := by
        dsimp [FighterPhase.virtualOutput, FiniteCounterGame.output]
        rw [hinv.2.1, hans]
      have hactive : (p.game d).activePlayer (p.official d) = false :=
        hturn.trans hinv.1
      have hobj := (counter_game_active_objectives (p.game d) (p.official d)).1
      rw [hactive] at hobj
      have hfalse : p.predicateHolds d = false := by
        unfold FighterPhase.predicateHolds
        rw [hinv.1, hout]
        exact hobj
      have hwins' : (p.game d).StrategyWins false
          (p.game d).strategy (p.game d).initialPosition := by
        rw [← hgame] at hwins
        exact hwins
      have hpath' : Relation.ReflTransGen
          ((p.game d).StrategyStep false (p.game d).strategy)
          (p.game d).initialPosition (p.official d) := by
        rw [← hgame] at hpath
        exact hpath
      have henabled :=
        strategyMove_enabled_of_controlled_turn
          P d l (fighterState P d (tick + 1)) p hlookup hinv hfalse hzero hturn hwins' hpath'
      have hnone := (fighterLevelAction_eq_none_iff
        P d l (fighterState P d (tick + 1)) p hlookup).mp
          (fighterLevelAction_fighterState_eq_none P d (tick + 1) l)
      exact henabled hnone.2.2.2
  exact hall tick phase (List.mem_of_find?_eq_some hphase.2.2.2)
    hphase.2.1 hphase.2.2.1

/-- Legal true-marker play has a true live predicate at every completed true-marker tick. -/
private lemma predicateHolds_eventually
    (P : FighterParams) (d l : ℕ) (hd : 1 ≤ d) (hlegal : TrueMarkerLegalPlay P d l) :
    ∃ tick₀ ≥ markerTick P.B (levelScale l), ∀ tick ≥ tick₀, ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ phase.predicateHolds d = true := by
  refine ⟨markerTick P.B (levelScale l), le_rfl, ?_⟩
  intro tick htick
  have hplay := hlegal
  obtain ⟨hclosure, game, hwins, hticks, hlater⟩ := hplay
  obtain ⟨phase, hphase, hgame, hbuf, hpath⟩ :=
    hticks tick htick
  refine ⟨phase, hphase, ?_⟩
  by_contra hnot
  have hfalse : phase.predicateHolds d = false := by
    cases hp : phase.predicateHolds d <;> simp_all
  have hmem : phase ∈ (fighterState P d tick).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  have hlen :=
    length_buffer_eq_of_mem_active_fighterState
      P d tick phase hmem
  have hquiet := fighterLevelAction_fighterState_eq_none P d tick l
  have hnone := (fighterLevelAction_eq_none_iff
    P d l (fighterState P d tick) phase hphase.2.2.2).mp hquiet
  have hturn :=
    official_opponent_turn_of_completed_tick
      P d l hd hlegal tick phase hphase
  exact (flushBuffer_enabled_of_opponent_turn
    d l (fighterState P d tick) phase hphase.2.2.2 hbuf hlen hfalse hturn) hnone.2.2.1

/-- The true-marker opponent never exhausts its budget; play is legal and eventually satisfies `P`.
Blueprint node `constr:opponent`. Legality includes every flushed vector, the controlled
strategy responses, and the official/live counter and remaining-budget identities at every tick. -/
theorem true_marker_opponent_stream_legal (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    TrueMarkerPhaseStarted P d l ∧ TrueMarkerNeverEndsFor P d l .opponentExhausted ∧
    TrueMarkerLegalPlay P d l ∧
    ∃ tick₀ ≥ markerTick P.B (levelScale l), ∀ tick ≥ tick₀, ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ phase.predicateHolds d = true := by
  have h1 := trueMarker_started_and_neverEndsFor_opponentExhausted P C cGap cRank d₀ d l
    hfixed hgood hlate
  have h4 := trueMarkerClosureLegal_of_goodPadding
    P C cGap cRank d₀ d l hfixed hgood hlate
  have h5 := trueMarkerLegalPlay_of_trueMarkerClosureLegal P C cGap cRank d₀ d l hfixed
    hgood hlate h4
  have h6 := predicateHolds_eventually P d l hgood.positive h5
  exact ⟨h1.1, h1.2, h5, h6⟩

end Milovanov

end Kolmogorov
