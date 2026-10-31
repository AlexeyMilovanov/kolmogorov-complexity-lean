/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferActions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.LegalPlay

/-!
# Buffer initialization before closure

Lower-level service cannot change a higher phase that remains active. We prove this
through event handling, fuel allocation, and closure, then use it to transport the buffer
invariant from the previous tick to the beginning of the current level's closure.
New phases start with equal official and live counters and a zero buffer; opponent events
preserve the corresponding counter and budget equations. The buffer-invariance proof in
`ClosureBufferCandidates` uses this initialization as part of blueprint node `constr:opponent`,
the legal-play component of the stability argument for the main oracle separation theorem.
-/

namespace Kolmogorov.Milovanov

/-- Installing a phase leaves lookups at every other level unchanged. -/
lemma activeAt_putPhase_of_level_ne
    (d l : ℕ) (s : FighterState) (p : FighterPhase) (hpl : p.level ≠ l) :
    (s.putPhase d p).activeAt d l = s.activeAt d l := by
  simp only [FighterState.putPhase, FighterState.activeAt, List.find?_cons,
    beq_eq_false_iff_ne.mpr hpl]
  exact FighterState.find?_level_filter_ne _ _ _ hpl.symm

private lemma activeAt_eq_of_payoff_fold
    (P : FighterParams) (d j l : ℕ) (qs : List Coordinate) (state : FighterState) (hjl : j < l) :
    ∀ phase, (qs.foldl (fun s q ↦ fighterPayoff P d j q s) state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  induction qs generalizing state with
  | nil =>
    intro phase hphase
    exact hphase
  | cons q qs ih =>
    intro phase hphase
    rw [List.foldl_cons] at hphase
    have h_ih := ih (fighterPayoff P d j q state) phase hphase
    exact activeAt_eq_of_fighterPayoff_activeAt_eq_some P d j l q state hjl phase h_ih

private lemma activeAt_eq_of_fulfillReady_of_lt
    (P : FighterParams) (d j l : ℕ) (state : FighterState) (hjl : j < l) :
    ∀ phase, (fighterFulfillReady P d j state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterFulfillReady at hphase
  cases h_active : state.activeAt d j with
  | none =>
    rw [h_active] at hphase
    exact hphase
  | some val =>
    rw [h_active] at hphase
    exact activeAt_eq_of_payoff_fold P d j l val.pending state hjl phase hphase

private lemma activeAt_startPhase_eq_none_of_lt
    (P : FighterParams) (d j l : ℕ) (event : Candidate) (state : FighterState) (hjl : j < l) :
    (fighterStartPhase P d j event state).activeAt d l = none := by
  unfold fighterStartPhase
  dsimp only
  change (FighterState.putPhase _ d _).activeAt d l = none
  rw [activeAt_putPhase_of_level_ne d l _ _ (ne_of_lt hjl)]
  exact activeAt_fighterAbortAbove_eq_none_of_lt d j l _ hjl

private lemma activeAt_eq_of_opponent_of_lt
    (P : FighterParams) (d j l : ℕ) (e : ProgramEvent) (state : FighterState) (hjl : j < l) :
    ∀ phase, (fighterOpponent P d j e state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterOpponent at hphase
  split at hphase
  · exact hphase
  · next val h_act =>
    split at hphase
    · exact hphase
    · split at hphase
      · exact hphase
      · split at hphase
        · have h_cancel := activeAt_fighterCancel_eq_of_ne d j l .opponentExhausted j state
            (ne_of_lt hjl)
          rw [h_cancel] at hphase
          exact hphase
        · next p_q p_index _ _ _ =>
          have h1 := activeAt_eq_of_fulfillReady_of_lt P d j l _ hjl phase hphase
          have h_act_eq : val.level = j := by
            unfold FighterState.activeAt at h_act
            have h_find := List.find?_some h_act
            exact beq_iff_eq.mp h_find
          rw [activeAt_putPhase_of_level_ne] at h1
          · exact h1
          · change val.level ≠ l
            omega

/-- A higher phase surviving an event at a lower level was already active before the event. -/
lemma activeAt_eq_of_event_of_lt
    (P : FighterParams) (d j l : ℕ) (event : Option TimedEvent) (state : FighterState)
    (hjl : j < l) :
    ∀ phase, (match event with
    | none => state
    | some e =>
      if fighterOwner d e.2.2.1.length = some j ∧ e.2.2.1.length ≤ levelScale j ∧
          P.Admissible d j then
        fighterStartPhase P d j (e.2.2.1, e.1) state
      else fighterOpponent P d j e.2.2 state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  cases hevent : event with
  | none =>
    rw [hevent] at hphase
    exact hphase
  | some e =>
    rw [hevent] at hphase
    dsimp only at hphase
    split at hphase
    · have h_absent := activeAt_startPhase_eq_none_of_lt P d j l (e.2.2.1, e.1) state hjl
      rw [h_absent] at hphase
      contradiction
    · exact activeAt_eq_of_opponent_of_lt P d j l e.2.2 state hjl phase hphase

private lemma activeAt_eq_of_dummy_of_lt
    (d j l : ℕ) (state : FighterState) (hjl : j < l) :
    ∀ phase, (fighterDummy d j state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterDummy at hphase
  cases ha : state.activeAt d j with
  | none =>
    simp only [ha] at hphase
    exact hphase
  | some p =>
    simp only [ha] at hphase
    have hp : p.level = j :=
      beq_iff_eq.mp (List.find?_some (p := fun q : FighterPhase ↦ q.level == j) ha)
    cases hd : p.dummy with
    | none =>
      simp only [hd] at hphase
      exact hphase
    | some output =>
      simp only [hd] at hphase
      cases hi : p.dummyIssued with
      | true =>
        simp only [hi, ite_true] at hphase
        exact hphase
      | false =>
        simp only [hi, Bool.false_eq_true, ite_false, fighterAllocate, ha] at hphase
        split at hphase
        · simp only [Bool.false_eq_true, ite_false] at hphase
          rw [activeAt_fighterCancel_eq_of_ne
            d j l .saturated j { state with failed := true } (ne_of_lt hjl)] at hphase
          exact hphase
        · simp only [ite_true] at hphase
          rw [activeAt_putPhase_of_level_ne d l _ _ (by change p.level ≠ l; omega)] at hphase
          rw [activeAt_fighterAbortAbove_eq_none_of_lt
            d j l _ hjl] at hphase
          contradiction

private lemma activeAt_eq_of_flushBuffer_of_lt
    (d j l : ℕ) (state next : FighterState) (hjl : j < l)
    (h : fighterFlushBuffer d j state = some next) :
    ∀ phase, next.activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterFlushBuffer at h
  cases hstate_act : state.activeAt d j with
  | none =>
    rw [hstate_act] at h
    simp only [Option.bind_eq_bind, Option.bind] at h
    cases h
  | some phase_j =>
    rw [hstate_act] at h
    simp only [Option.bind_eq_bind, Option.bind] at h
    change (if phase_j.predicateHolds d = false ∧
        (phase_j.game d).activePlayer (phase_j.official d) ≠ phase_j.controlledPlayer ∧
        (phase_j.game d).LegalMove (phase_j.official d) phase_j.buffer then
      some (state.putPhase d { phase_j with
        officialCode := ((phase_j.game d).afterMove (phase_j.official d) phase_j.buffer).encode,
        buffer := List.replicate (phase_j.game d).coordinates.length 0 })
    else none) = some next at h
    split_ifs at h with hcond
    · simp only [Option.some.injEq] at h
      rw [← h] at hphase
      have h_eq : phase_j.level = j :=
        beq_iff_eq.mp (List.find?_some (p := fun q : FighterPhase ↦ q.level == j) hstate_act)
      have h_ne : phase_j.level ≠ l := by
        rw [h_eq]
        exact ne_of_lt hjl
      have h_put := activeAt_putPhase_of_level_ne d l state
        { phase_j with
          officialCode := ((phase_j.game d).afterMove (phase_j.official d) phase_j.buffer).encode
          buffer := List.replicate (phase_j.game d).coordinates.length 0 } h_ne
      rwa [h_put] at hphase

private lemma activeAt_eq_of_fuelUnit_of_lt
    (P : FighterParams) (d j l : ℕ) (q : Coordinate) (s : FighterState) (hjl : j < l) :
    ∀ phase, (fighterFuelUnit P d j q s).activeAt d l = some phase →
      s.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterFuelUnit at hphase
  cases ha : s.activeAt d j with
  | none =>
    simp only [ha] at hphase
    exact hphase
  | some p =>
    simp only [ha] at hphase
    have hp : p.level = j :=
      beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) ha)
    split at hphase
    · let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
      have hcharged : (s.putPhase d charged).activeAt d j = some charged := by
        simp [FighterState.putPhase, FighterState.activeAt, charged, hp]
      let index := fighterFreshString d (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
      change (match fighterAllocate d j .fuel (levelUpper j + d)
          (pairCode (triple q.1 (q.2 - d) p.candidate.1) index) (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d j
          (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
        else next).activeAt d l = some phase at hphase
      simp only [fighterAllocate, hcharged] at hphase
      split at hphase
      · simp only [Bool.false_eq_true, ite_false] at hphase
        rw [activeAt_fighterCancel_eq_of_ne
          d j l .saturated j _ (ne_of_lt hjl)] at hphase
        change (s.putPhase d charged).activeAt d l = some phase at hphase
        rw [activeAt_putPhase_of_level_ne d l _ _ (by change p.level ≠ l; omega)] at hphase
        exact hphase
      · simp only [ite_true] at hphase
        have hbefore := activeAt_eq_of_fulfillReady_of_lt
          P d j l _ hjl phase hphase
        rw [activeAt_putPhase_of_level_ne d l _ _ (by change p.level ≠ l; omega)] at hbefore
        rw [activeAt_fighterAbortAbove_eq_none_of_lt
          d j l _ hjl] at hbefore
        contradiction
    · exact hphase

private lemma activeAt_eq_of_fuelUnits_of_lt
    (P : FighterParams) (d j l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) (hjl : j < l) :
    ∀ phase, (fighterFuelUnits P d j q count s).activeAt d l = some phase →
      s.activeAt d l = some phase := by
  induction count generalizing s with
  | zero =>
    intro phase h
    exact h
  | succ count ih =>
    intro phase h
    unfold fighterFuelUnits at h
    have h1 := ih _ _ h
    exact activeAt_eq_of_fuelUnit_of_lt P d j l q s hjl phase h1

private lemma activeAt_eq_of_fuel_fold_of_lt
    (P : FighterParams) (d j l : ℕ) (xs : List (Coordinate × ℕ))
    (move : CounterMove) (s : FighterState) (hjl : j < l) :
    ∀ phase, (xs.foldl (fun t (q, i) ↦
      fighterFuelUnits P d j q (move[i]?.getD 0) t) s).activeAt d l = some phase →
      s.activeAt d l = some phase := by
  induction xs generalizing s with
  | nil =>
    intro phase h
    exact h
  | cons x xs ih =>
    intro phase h
    rw [List.foldl_cons] at h
    have h1 := ih _ _ h
    exact activeAt_eq_of_fuelUnits_of_lt P d j l x.1 (move[x.2]?.getD 0) s hjl phase h1

private lemma activeAt_eq_of_strategyMove_of_lt
    (P : FighterParams) (d j l : ℕ) (state next : FighterState) (hjl : j < l)
    (h : fighterStrategyMove P d j state = some next) :
    ∀ phase, next.activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterStrategyMove at h
  cases hstate : state.activeAt d j with
  | none =>
    simp only [hstate, bind, Option.bind_none] at h
    cases h
  | some pj =>
    simp only [hstate, bind, Option.bind_some] at h
    split at h
    · cases hm : (pj.game d).strategy (pj.official d) with
      | none =>
        simp only [hm, Option.bind_none] at h
        cases h
      | some move =>
        simp only [hm, Option.bind_some] at h
        split at h
        · let next_fold := ((pj.game d).coordinates.zipIdx).foldl
            (fun s (q, i) ↦ fighterFuelUnits P d j q (move[i]?.getD 0) s) state
          change (match next_fold.activeAt d j with
            | none => some next_fold
            | some live => some (next_fold.putPhase d _)) = some next at h
          cases hfold : next_fold.activeAt d j with
          | none =>
            simp only [hfold, Option.some.injEq] at h
            subst h
            exact activeAt_eq_of_fuel_fold_of_lt P d j l ((pj.game d).coordinates.zipIdx) move
              state hjl phase hphase
          | some live =>
            simp only [hfold, Option.some.injEq] at h
            subst h
            have hlevel : (live : FighterPhase).level = j := by
              revert hfold
              unfold FighterState.activeAt
              intro hf
              have h2 := List.find?_some (p := fun (p : FighterPhase) ↦ p.level == j) hf
              exact beq_iff_eq.mp h2
            have hpl : ({ live with
                officialCode := ((pj.game d).afterMove (pj.official d) move).encode } :
                FighterPhase).level ≠ l := by
              change (live : FighterPhase).level ≠ l
              rw [hlevel]
              omega
            have hput := activeAt_putPhase_of_level_ne d l next_fold _ hpl
            rw [hput] at hphase
            exact activeAt_eq_of_fuel_fold_of_lt P d j l ((pj.game d).coordinates.zipIdx) move
              state hjl phase hphase
        · cases h
    · cases h

private lemma activeAt_eq_of_levelAction_of_lt
    (P : FighterParams) (d j l : ℕ) (state next : FighterState) (hjl : j < l)
    (h : fighterLevelAction P d j state = some next) :
    ∀ phase, next.activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  dsimp [fighterLevelAction] at h
  cases h1 : state.activeAt d j with
  | none =>
    rw [h1] at h
    dsimp [bind] at h
    contradiction
  | some phasej =>
    rw [h1] at h
    dsimp [bind] at h
    split_ifs at h
    · injection h with heq
      subst heq
      exact activeAt_eq_of_dummy_of_lt d j l state hjl phase hphase
    · cases h2 : phasej.pending.find? (fun q ↦
          decide (q ∉ state.fulfilled) && fighterSafe P d state.tick q) with
      | some q =>
        rw [h2] at h
        injection h with heq
        subst heq
        exact activeAt_eq_of_fighterPayoff_activeAt_eq_some P d j l q state hjl phase hphase
      | none =>
        rw [h2] at h
        cases h3 : fighterFlushBuffer d j state with
        | some next' =>
          rw [h3] at h
          injection h with heq
          subst heq
          exact activeAt_eq_of_flushBuffer_of_lt d j l state next' hjl h3 phase hphase
        | none =>
          rw [h3] at h
          exact activeAt_eq_of_strategyMove_of_lt P d j l state next hjl h phase hphase

private lemma activeAt_eq_of_closure_of_lt
    (P : FighterParams) (d j l fuel : ℕ) (state : FighterState) (hjl : j < l) :
    ∀ phase, (fighterClosure P d j fuel state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  induction fuel generalizing state with
  | zero =>
      intro phase hphase
      exact hphase
  | succ fuel ih =>
      intro phase hphase
      cases hact : fighterLevelAction P d j state with
      | none =>
          simpa [fighterClosure, hact] using hphase
      | some next =>
          have hmid : (fighterClosure P d j fuel next).activeAt d l = some phase := by
            simpa [fighterClosure, hact] using hphase
          have hnext : next.activeAt d l = some phase := ih next phase hmid
          exact activeAt_eq_of_levelAction_of_lt
            P d j l state next hjl hact phase hnext

private lemma activeAt_eq_of_processLevel_of_lt
    (P : FighterParams) (d j l : ℕ) (event : Option TimedEvent) (state : FighterState)
    (hjl : j < l) :
    ∀ phase, (fighterProcessLevel P d j event state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  intro phase hphase
  unfold fighterProcessLevel at hphase
  have h1 := activeAt_eq_of_closure_of_lt P d j l _ _ hjl phase hphase
  have h2 := activeAt_eq_of_event_of_lt P d j l event _ hjl phase h1
  have h3 := activeAt_eq_of_fulfillReady_of_lt P d j l state hjl phase h2
  exact h3

private lemma activeAt_eq_of_processLevel_fold_of_lt
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent)
    (levels : List ℕ) (state : FighterState)
    (hlevels : ∀ j ∈ levels, j < l) :
    ∀ phase,
      (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) state).activeAt d l = some phase →
      state.activeAt d l = some phase := by
  induction levels generalizing state with
  | nil =>
    intro phase hphase
    exact hphase
  | cons hd tl ih =>
    intro phase hphase
    dsimp only [List.foldl_cons] at hphase
    have h_tl : ∀ j ∈ tl, j < l := fun j hj ↦ hlevels j (List.mem_cons_of_mem hd hj)
    have hmid := ih (fighterProcessLevel P d hd event state) h_tl phase hphase
    have h_hd : hd < l := hlevels hd (List.Mem.head tl)
    exact activeAt_eq_of_processLevel_of_lt P d hd l event state h_hd phase hmid

/-- Servicing lower levels transports the previous tick's buffer invariant to this level. -/
private lemma bufferShaped_beforeLevel
    (P : FighterParams) (d tick l : ℕ) (hd : 1 ≤ d) :
    ∀ phase, (fighterBeforeLevel P d tick l).activeAt d l = some phase →
      BufferShaped d phase := by
  intro phase hphase
  unfold fighterBeforeLevel at hphase
  let state := fighterState P d (tick - 1)
  let current : FighterState := { state with tick := tick, schedule := masterState P.B tick }
  have h_current_active : current.activeAt d l = state.activeAt d l := by rfl
  let event := eventAt P.B tick
  let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
  let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
  let L := levels.mergeSort (· ≤ ·) |>.takeWhile (· < l)
  have h_lt : ∀ j ∈ L, j < l := by
    intro j hj
    have h_decide := List.mem_takeWhile_imp hj
    exact of_decide_eq_true h_decide
  have horig := activeAt_eq_of_processLevel_fold_of_lt P d l event L current h_lt phase hphase
  rw [h_current_active] at horig
  have hmem : phase ∈ (fighterState P d (tick - 1)).active := List.mem_of_find?_eq_some horig
  exact ⟨(fighter_live_invariants P d (tick - 1) hd phase hmem).1,
    length_buffer_eq_of_mem_active_fighterState P d (tick - 1) phase hmem⟩

/-- Immediate payoff checks change only pending requests in a surviving phase. -/
private lemma bufferShaped_fulfillReady
    (P : FighterParams) (d l : ℕ) (state : FighterState) :
    ∀ phase, (fighterFulfillReady P d l state).activeAt d l = some phase →
      ∃ origPhase, state.activeAt d l = some origPhase ∧
        (BufferShaped d origPhase → BufferShaped d phase) := by
  intro phase hphase
  obtain ⟨original, horiginal, pending, rfl⟩ :=
    pending_update_of_activeAt_fighterFulfillReady P d l state phase hphase
  exact ⟨original, horiginal, fun h ↦ h⟩

/-- A newly installed phase starts with the counter and budget equations and a zero buffer. -/
private lemma bufferShaped_startPhase
    (P : FighterParams) (d l : ℕ) (state : FighterState) (candidate : Candidate) :
    ∀ phase, (fighterStartPhase P d l candidate state).activeAt d l = some phase →
      BufferShaped d phase := by
  intro phase hphase
  unfold fighterStartPhase at hphase
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l state)
  let p := fighter_construction P d l candidate waiting
  have hfind : (waiting.putPhase d p).active.find? (fun x ↦ x.level == l) = some phase := hphase
  have hl : p.level = l := rfl
  simp only [FighterState.putPhase, List.find?_cons, hl, beq_self_eq_true,
    Option.some.injEq] at hfind
  have heq : phase = p := hfind.symm
  subst heq
  change p.BufferInvariant d ∧ p.buffer.length = (p.game d).coordinates.length
  let coords := retainedCoordinateList (constructedLiteralConstant P.literal d) (levelInput d l)
    (P.family.tree d l (levelInput d l))
  let indices := coords.map (fighterInitialIndices P d l candidate waiting.allocated)
  let counters := indices.map (fun xs ↦ xs.toFinset.card)
  let R := P.c₁ * 2 ^ (levelUpper l - levelScale l)
  let original := finite_counter_game coords
    (coordinatePriceTable P.B P.lam P.n₀ (levelScale l) d candidate coords) counters
    ((P.family.tree d l (levelInput d l)).queries.filter (fun q ↦
      decide (q.1 ∈ fighterStageOutputs P d q.2 waiting.tick waiting.allocated))) R
    ((P.family.tree d l (levelInput d l)).normalize (constructedLiteralConstant P.literal d))
    (fighterStageOutputs P d (levelInput d l) waiting.tick waiting.allocated).card
  let game := original.controlWinningPlayer
  let initial : FighterPhase := ⟨l, candidate, waiting.schedule, waiting.allocated, game.encode,
    indices, game.initialPosition.encode, counters, R, R, List.replicate coords.length 0,
    [], none, false, false⟩
  change BufferShaped d initial
  have htable : game.coordinateTable = coords := by
    dsimp [game, FiniteCounterGame.controlWinningPlayer]
    split <;> rfl
  have hcounter : game.initialCounters = counters := by
    dsimp [game, FiniteCounterGame.controlWinningPlayer]
    split <;> rfl
  have hbudget : game.budget = R := by
    dsimp [game, FiniteCounterGame.controlWinningPlayer]
    split <;> rfl
  have hcoords : game.coordinates = coords := by
    rw [FiniteCounterGame.coordinates, htable]
    exact eraseDups_eq_self_of_nodup (nodup_eraseDups_list _)
  have hgame : initial.game d = game := decode_encode_counter_game game
  have hlen : counters.length = game.coordinates.length := by
    simp [counters, indices, hcoords]
  have hoff : (initial.official d).counters = counters ∧
      (initial.official d).leftBudget = R ∧ (initial.official d).rightBudget = R := by
    change (decodeCounterPosition (initial.game d) game.initialPosition.encode).counters =
        counters ∧
      (decodeCounterPosition (initial.game d) game.initialPosition.encode).leftBudget = R ∧
      (decodeCounterPosition (initial.game d) game.initialPosition.encode).rightBudget = R
    rw [hgame, decode_encode_counter_position]
    simp [FiniteCounterGame.initialPosition, hcounter, hbudget]
  change (false = false ∧ counters = (initial.game d).addCounters
      (initial.official d).counters (List.replicate coords.length 0) ∧
      (initial.official d).leftBudget = R ∧
      (initial.official d).rightBudget = R + (List.replicate coords.length 0).sum) ∧
    (List.replicate coords.length 0).length = (initial.game d).coordinates.length
  rw [hoff.1, hoff.2.1, hoff.2.2, hgame, ← hcoords]
  simp [FiniteCounterGame.addCounters_replicate_zero game counters hlen]

private lemma activeAt_cancel_opponentExhausted
    (d l : ℕ) (state : FighterState) :
    (fighterCancel d l .opponentExhausted l state).activeAt d l = none := by
  unfold fighterCancel
  split
  · assumption
  · simp [FighterState.activeAt, List.find?_filter]

private lemma coordinate_mem_of_opponentTuple_eq_some
    (d : ℕ) (phase : FighterPhase) (event : ProgramEvent) (q : Coordinate) (index : BitString) :
    fighterOpponentTuple d phase event = some (q, index) →
      q ∈ (phase.game d).coordinates := by
  intro h
  unfold fighterOpponentTuple at h
  split at h
  · contradiction
  · rename_i hlen
    cases hd : decodeTriple (decodeFirst event.2) with
    | none => simp [hd] at h
    | some v =>
      rcases v with ⟨x, k, w⟩
      simp only [hd, bind, Option.bind_some] at h
      split at h
      · rename_i hcond
        cases h
        exact hcond.2.1
      · contradiction

private lemma bufferShaped_insert_opponent
    (d : ℕ) (phase : FighterPhase) (q : Coordinate) (index : BitString)
    (hq : q ∈ (phase.game d).coordinates)
    (hbudget : phase.opponentRemaining ≠ 0) :
    BufferShaped d phase →
      BufferShaped d
        { phase.insertIndex d q index with
          opponentRemaining := phase.opponentRemaining - 1
          buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) } := by
  rintro ⟨⟨hctrl, hlive, hleft, hright⟩, hlen⟩
  have hunitlen : (phase.unitVector d q).length = (phase.game d).coordinates.length := by
    simp [FighterPhase.unitVector]
  have hsum := FiniteCounterGame.sum_addCounters (phase.game d) phase.buffer
    (phase.unitVector d q) hlen hunitlen
  rw [FighterPhase.sum_unitVector phase d q hq] at hsum
  change (phase.controlledPlayer = false ∧
      (phase.game d).addCounters phase.liveCounters (phase.unitVector d q) =
        (phase.game d).addCounters (phase.official d).counters
          ((phase.game d).addCounters phase.buffer (phase.unitVector d q)) ∧
      (phase.official d).leftBudget = phase.controlledRemaining ∧
      (phase.official d).rightBudget = phase.opponentRemaining - 1 +
        ((phase.game d).addCounters phase.buffer (phase.unitVector d q)).sum) ∧
    ((phase.game d).addCounters phase.buffer (phase.unitVector d q)).length =
      (phase.game d).coordinates.length
  refine ⟨⟨hctrl, ?_, hleft, ?_⟩, by simp [FiniteCounterGame.addCounters]⟩
  · rw [hlive, FiniteCounterGame.addCounters_assoc]
  · omega

private lemma bufferShaped_opponent
    (P : FighterParams) (d l : ℕ) (state : FighterState) (event : ProgramEvent) :
    ∀ phase, (fighterOpponent P d l event state).activeAt d l = some phase →
      ∃ origPhase, state.activeAt d l = some origPhase ∧
      (BufferShaped d origPhase →
       BufferShaped d phase) := by
  intro phase hphase
  unfold fighterOpponent at hphase
  cases h_act : state.activeAt d l with
  | none =>
    rw [h_act] at hphase
    dsimp only at hphase
    rw [hphase] at h_act
    contradiction
  | some p =>
    rw [h_act] at hphase
    dsimp only at hphase
    cases h_tuple : fighterOpponentTuple d p event with
    | none =>
      rw [h_tuple] at hphase
      dsimp only at hphase
      have hphase_eq : some p = some phase := by
        rw [← h_act]
        exact hphase
      have heq : p = phase := Option.some.inj hphase_eq
      subst heq
      refine ⟨p, rfl, fun h ↦ h⟩
    | some pair =>
      rw [h_tuple] at hphase
      dsimp only at hphase
      rcases pair with ⟨q, index⟩
      split at hphase
      · have hphase_eq : some p = some phase := by
          rw [← h_act]
          exact hphase
        have heq : p = phase := Option.some.inj hphase_eq
        subst heq
        refine ⟨p, rfl, fun h ↦ h⟩
      · split at hphase
        · have h_cancel := activeAt_cancel_opponentExhausted d l state
          rw [hphase] at h_cancel
          contradiction
        · rename_i h_idx h_budget
          refine ⟨p, rfl, ?_⟩
          intro hp_shape
          have h_hq : q ∈ (p.game d).coordinates :=
            coordinate_mem_of_opponentTuple_eq_some d p event q index h_tuple
          have h_insert := bufferShaped_insert_opponent d p q index h_hq h_budget hp_shape
          let inserted := p.insertIndex d q index
          let next := { inserted with
            opponentRemaining := p.opponentRemaining - 1
            buffer := (p.game d).addCounters p.buffer (p.unitVector d q) }
          have h_fund : BufferShaped d (next.fundRequests d state.fulfilled) := h_insert
          have h_level : (next.fundRequests d state.fulfilled).level = l := by
            change p.level = l
            exact beq_iff_eq.mp
              (List.find?_some (p := fun phase : FighterPhase ↦ phase.level == l) h_act)
          have h_put := FighterState.activeAt_putPhase d l state
            (next.fundRequests d state.fulfilled) h_level
          rcases bufferShaped_fulfillReady P d l _ phase hphase with ⟨origPhase, horig, hinv⟩
          have h_orig_eq : origPhase = (next.fundRequests d state.fulfilled) := by
            have h_eq : some origPhase = some (next.fundRequests d state.fulfilled) := by
              rw [← horig]
              exact h_put
            exact Option.some.inj h_eq
          subst h_orig_eq
          exact hinv h_fund

/-- The true-marker phase satisfies the buffer invariant at the beginning of each closure. -/
lemma bufferInvariant_beforeClosure
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (_hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (_hlate : LateAdmissibleOccurrence P d l) :
    ∀ tick ≥ markerTick P.B (levelScale l), ∀ phase,
      (fighterBeforeClosure P d tick l).activeAt d l = some phase →
      phase.candidate = markerCandidate P.B (levelScale l) →
      phase.BufferInvariant d := by
  intro tick _ phase hphase _
  unfold fighterBeforeClosure at hphase
  have hd : 1 ≤ d := hgood.positive
  cases hevent : eventAt P.B tick with
  | none =>
    rw [hevent] at hphase
    dsimp only at hphase
    rcases bufferShaped_fulfillReady P d l _ phase hphase with ⟨origPhase2, horig2, hinv2⟩
    exact (hinv2 (bufferShaped_beforeLevel P d tick l hd origPhase2 horig2)).1
  | some e =>
    rw [hevent] at hphase
    dsimp only at hphase
    split at hphase
    · exact (bufferShaped_startPhase P d l _ _ phase hphase).1
    · rcases bufferShaped_opponent P d l _ _ phase hphase with ⟨origPhase3, horig3, hinv3⟩
      rcases bufferShaped_fulfillReady P d l _ origPhase3 horig3 with ⟨origPhase2, horig2, hinv2⟩
      exact (hinv3 (hinv2 (bufferShaped_beforeLevel P d tick l hd origPhase2 horig2))).1

end Kolmogorov.Milovanov
