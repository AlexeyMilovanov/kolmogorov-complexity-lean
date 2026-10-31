/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Conditional
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability

/-!
# Virtual and actual answers of the fighter simulation

This module compares the two oracles that meet in the eventual-agreement lemma
`constr:agreement`.  The *actual* answer function `fighterActualAnswer` is the semantic oracle
`{(x, k) | plainK U_d x ≤ k}` with the literal normalization of the construction.  The *virtual*
answer function `fighterVirtualAnswerAt` is read off the true-marker phase of the simulation at a
given tick, and `fighterVirtualOutputAt` evaluates the whole referee tree against it.

Besides these definitions the module proves the bookkeeping facts about the simulation state
`fighterState P d tick` that make the virtual answers stabilize:

* `fighter_actual_answer_eq` and `true_marker_virtual_output_eq`: normalization does not change
  actual answers, and the live evaluation of the referee tree is the phase's stored output;
* `FighterPhase.Grows`: the relation "same level, candidate and game, every live coordinate
  counter has not decreased", which relates a phase to its updates within one event;
* `fighterState_candidate_time_le`: no phase record precedes its own emission timestamp, which
  gives `trueMarkerPhase_eq_none_of_lt` (no record before the marker tick);
* `fighterVirtualAnswerAt_persists`: once the true-marker phase is active, positive virtual
  answers persist.

The modules `Diagonal.VirtualStabilization`, `Diagonal.SimulationState`,
`Diagonal.FundedFrames`, `Diagonal.SimulationEvents` and `Diagonal.OracleAgreement` build on
these facts to prove that the virtual oracle stabilizes and agrees with the actual one.
-/

namespace Kolmogorov.Milovanov

/-- Live normalized virtual answers of the true-marker phase at a specified tick.
Blueprint node `constr:agreement` (supporting definition). Before a record exists the default
has only literal positives; an archived record uses its frozen last counters. -/
noncomputable def fighterVirtualAnswerAt (P : FighterParams) (d l tick : ℕ) :
    Coordinate → Bool :=
  match trueMarkerPhase P d l tick with
  | some phase => phase.virtualAnswer P d
  | none => normalizedAnswer (constructedLiteralConstant P.literal d) (fun _ => false)

/-- Evaluate the full referee tree against the phase's current virtual answer function.
Blueprint node `constr:agreement` (supporting definition). -/
noncomputable def fighterVirtualOutputAt (P : FighterParams) (d l tick : ℕ) : ℕ :=
  (P.family.tree d l (levelInput d l)).eval (fighterVirtualAnswerAt P d l tick)

/-- The actual oracle `{(x,k) | plainK U_d x ≤ k}` with the stage-3 literal normalization.
Blueprint node `constr:agreement` (supporting definition). No finite-table approximation
or virtual counter is consulted by this semantic answer function. -/
noncomputable def fighterActualAnswer (P : FighterParams) (d : ℕ) : Coordinate → Bool :=
  normalizedAnswer (constructedLiteralConstant P.literal d)
    (coordinateOracleAnswer (fighterOracle P d))

/-- Literal normalization preserves every actual coordinate answer for positive padding.
Blueprint node `constr:agreement`. The proof uses the frozen unconditional literal bound. -/
theorem fighter_actual_answer_eq (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) :
    fighterActualAnswer P d = coordinateOracleAnswer (fighterOracle P d) := by
  funext q
  by_cases h : q.1.length + constructedLiteralConstant P.literal d ≤ q.2
  · have hx : Simple (fighterU P d) q.1 q.2 :=
      (constructed_machine_literal_bound P.B P.literal d hd (fighterG P d) q.1).trans
        (by exact_mod_cast h)
    simp [fighterActualAnswer, normalizedAnswer, h, coordinateOracleAnswer,
      fighterOracle, actualCoordinateOracle, hx]
  · simp [fighterActualAnswer, normalizedAnswer, h]

/-- Full-tree live evaluation is the phase's stored preprocessed-game output.
Blueprint node `constr:agreement`. The phase identity ensures the saved game belongs
to this referee, rather than to an unrelated finite game with the same candidate. -/
theorem true_marker_virtual_output_eq (P : FighterParams) (d l tick : ℕ)
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase) :
    fighterVirtualOutputAt P d l tick = phase.virtualOutput d := by
  let Q : ℕ → Candidate → CounterGameCode → List AllocatedDirective → Prop :=
    fun j _ code _ =>
      (decodeCounterGame code).referee =
        (P.family.tree d j (levelInput d j)).normalize
          (constructedLiteralConstant P.literal d)
  have hinit : ∀ j c s,
      Q j c (fighter_construction P d j c s).gameCode
        (fighter_construction P d j c s).initialAllocations := by
    intro j c s
    dsimp only [Q, fighter_construction, FighterPhase.fundRequests]
    rw [decode_encode_counter_game]
    unfold FiniteCounterGame.controlWinningPlayer
    split <;> rfl
  have hinv := fighterState_forall_active_of_init P d tick Q hinit phase
    (List.mem_of_find?_eq_some hphase.2.2.2)
  have htree : (phase.game d).referee =
      (P.family.tree d l (levelInput d l)).normalize
        (constructedLiteralConstant P.literal d) := by
    change (decodeCounterGame phase.gameCode).referee = _
    simpa only [Q, hphase.2.1] using hinv
  have htm : trueMarkerPhase P d l tick = some phase := by
    unfold trueMarkerPhase fighterPhaseAt
    dsimp only
    rw [hphase.2.2.2]
    dsimp only
    rw [hphase.2.2.1]
    simp only [ite_true]
  have hans : fighterVirtualAnswerAt P d l tick =
      phase.virtualAnswer P d := by
    unfold fighterVirtualAnswerAt
    rw [htm]
  unfold fighterVirtualOutputAt
  rw [hans]
  unfold FighterPhase.virtualAnswer FighterPhase.virtualOutput
  rw [htree, QueryTree.eval_normalize]
  rfl

/-- A record update preserves the phase identity and game and increases its live counters.
The other fields may change, including pending requests when the phase is archived. -/
def FighterPhase.Grows (d : ℕ) (before after : FighterPhase) : Prop :=
  after.level = before.level ∧ after.candidate = before.candidate ∧
    after.game d = before.game d ∧
    ∀ q, (before.game d).coordinateValue before.liveCounters q ≤
      (after.game d).coordinateValue after.liveCounters q

/-- Every phase grows into itself. -/
theorem FighterPhase.Grows.refl (d : ℕ) (phase : FighterPhase) : phase.Grows d phase :=
  ⟨rfl, rfl, rfl, fun _ => le_rfl⟩

private theorem FighterPhase.Grows.trans (d : ℕ) {a b c : FighterPhase}
    (hab : a.Grows d b) (hbc : b.Grows d c) : a.Grows d c :=
  ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hbc.2.2.1.trans hab.2.2.1,
    fun q => (hab.2.2.2 q).trans (hbc.2.2.2 q)⟩

private theorem FiniteCounterGame.coordinateValue_le_addCounters (game : FiniteCounterGame)
    (counters move : List ℕ) (q : Coordinate) :
    game.coordinateValue counters q ≤ game.coordinateValue (game.addCounters counters move) q := by
  unfold FiniteCounterGame.coordinateValue
  split
  · rename_i hq
    have hi := List.idxOf_lt_length_of_mem hq
    simp [FiniteCounterGame.addCounters, hi]
  · exact le_rfl

/-- Inserting an index for a coordinate only increases the live counters of a phase. -/
theorem FighterPhase.Grows.insertIndex (d : ℕ) (phase : FighterPhase) (q : Coordinate)
    (index : BitString) : phase.Grows d (phase.insertIndex d q index) :=
  ⟨rfl, rfl, rfl, fun r ↦ FiniteCounterGame.coordinateValue_le_addCounters (phase.game d)
    phase.liveCounters (phase.unitVector d q) r⟩

namespace FighterState

/-- A successful allocation keeps the active phase of the allocating level. -/
theorem activeAt_fighterAllocate_of_success (d l : ℕ) (kind : DirectiveKind) (target : ℕ)
    (out : BitString) (s : FighterState) (hs : (fighterAllocate d l kind target out s).2 = true) :
    ((fighterAllocate d l kind target out s).1).activeAt d l = s.activeAt d l := by
  cases hp : s.activeAt d l with
  | none => simp [fighterAllocate, hp] at hs
  | some p =>
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none => simp [fighterAllocate, hp, hf] at hs
    | some input =>
      simpa only [fighterAllocate, hp, hf] using
        (activeAt_fighterAbortAbove_of_le d l l
          { s with allocated := s.allocated ++
            [AllocatedDirective.mk l p.candidate s.tick kind target input out] } le_rfl).trans hp

/-- Each resulting record either has the current event's timestamp or descends from the
previous active record of its level. An archive entry may also be inherited unchanged.
This relation tracks the source of records without presupposing that a phase survives. -/
private def Descends (d born : ℕ) (before after : FighterState) : Prop :=
  (∀ l next, after.activeAt d l = some next → next.candidate.2 = born ∨
    ∃ phase, before.activeAt d l = some phase ∧ phase.Grows d next) ∧
  ∀ e ∈ after.ended, e ∈ before.ended ∨ e.1.candidate.2 = born ∨
    ∃ phase, before.activeAt d e.1.level = some phase ∧ phase.Grows d e.1

namespace Descends

private theorem refl (d born : ℕ) (s : FighterState) : Descends d born s s :=
  ⟨fun _ phase hp => Or.inr ⟨phase, hp, FighterPhase.Grows.refl d phase⟩, fun _ he => Or.inl he⟩

private theorem trans (d born : ℕ) {a b c : FighterState}
    (hab : Descends d born a b) (hbc : Descends d born b c) : Descends d born a c := by
  refine ⟨?_, ?_⟩
  · intro l next hn
    rcases hbc.1 l next hn with h | ⟨mid, hm, hmn⟩
    · exact Or.inl h
    · rcases hab.1 l mid hm with h | ⟨old, ho, hom⟩
      · exact Or.inl (by rw [hmn.2.1]; exact h)
      · exact Or.inr ⟨old, ho, FighterPhase.Grows.trans d hom hmn⟩
  · intro e he
    rcases hbc.2 e he with he | h | ⟨mid, hm, hme⟩
    · exact hab.2 e he
    · exact Or.inr (Or.inl h)
    · rcases hab.1 e.1.level mid hm with h | ⟨old, ho, hom⟩
      · exact Or.inr (Or.inl (by rw [hme.2.1]; exact h))
      · exact Or.inr (Or.inr ⟨old, ho, FighterPhase.Grows.trans d hom hme⟩)

private theorem of_active_ended_eq (d born : ℕ) (s t : FighterState)
    (ha : t.active = s.active) (he : t.ended = s.ended) : Descends d born s t := by
  refine ⟨?_, ?_⟩
  · intro l next hn
    exact Or.inr ⟨next, by simpa [activeAt, ha] using hn, FighterPhase.Grows.refl d next⟩
  · intro e h
    exact Or.inl (he ▸ h)

private theorem foldl {α : Type} (d born : ℕ) (f : α → FighterState → FighterState)
    (hf : ∀ a s, Descends d born s (f a s)) (xs : List α) (s : FighterState) :
    Descends d born s (xs.foldl (fun s a => f a s) s) := by
  induction xs generalizing s with
  | nil => exact refl d born s
  | cons a xs ih => exact trans d born (hf a s) (ih _)

private theorem putPhase (d born : ℕ) (s : FighterState) (p : FighterPhase)
    (hp : p.candidate.2 = born ∨ ∃ old,
      s.activeAt d p.level = some old ∧ old.Grows d p) :
    Descends d born s (s.putPhase d p) := by
  refine ⟨?_, fun _ h => Or.inl h⟩
  intro j next hn
  by_cases hj : j = p.level
  · subst j
    have heq : next = p := by
      simpa [FighterState.putPhase, activeAt] using hn.symm
    subst next
    exact hp
  · rw [FighterState.activeAt_putPhase_of_ne d j s p hj] at hn
    exact Or.inr ⟨next, hn, FighterPhase.Grows.refl d next⟩

private theorem cancel (d born k : ℕ) (r : PhaseEnd) (cause : ℕ) (s : FighterState) :
    Descends d born s (fighterCancel d k r cause s) := by
  unfold fighterCancel
  split
  · exact refl d born s
  · rename_i phase hphase
    have hl : phase.level = k := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    refine ⟨?_, ?_⟩
    · intro j next hn
      have hj : j ≠ k := by
        intro h
        subst j
        have hmem := List.mem_of_find?_eq_some hn
        have hnlevel := FighterState.level_eq_of_activeAt_eq_some (p := next) hn
        simpa [hnlevel] using (List.mem_filter.mp hmem).2
      have hold : s.activeAt d j = some next := by
        change (s.active.filter (fun p => p.level != k)).find?
          (fun p => p.level == j) = some next at hn
        rwa [FighterState.find?_level_filter_ne _ _ _ hj] at hn
      exact Or.inr ⟨next, hold, FighterPhase.Grows.refl d next⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact Or.inl he
      · have heq := List.mem_singleton.mp he
        subst e
        exact Or.inr (Or.inr ⟨phase, by simpa [hl] using hphase,
          FighterPhase.Grows.refl d phase⟩)

private theorem abortAbove (d born l : ℕ) (s : FighterState) :
    Descends d born s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply foldl
  intro p t
  split
  · exact cancel d born _ _ _ t
  · exact refl d born t

private theorem allocate (d born l : ℕ) (kind : DirectiveKind) (target : ℕ)
    (out : BitString) (s : FighterState) :
    Descends d born s (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact refl d born s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none =>
      exact trans d born (of_active_ended_eq d born s _ rfl rfl)
        (cancel d born l .saturated l _)
    | some input =>
      exact trans d born (of_active_ended_eq d born s _ rfl rfl) (abortAbove d born l _)

private theorem recordPayoff (d born : ℕ) (q : Coordinate) (s : FighterState) :
    Descends d born s
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map (fun p => { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨?_, fun _ h => Or.inl h⟩
  intro l next hn
  have hm :
      ({ s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map (fun p => { p with pending := p.pending.filter (· != q) }) }
        : FighterState).activeAt d l =
      (s.activeAt d l).map (fun p => { p with pending := p.pending.filter (· != q) }) := by
    simp [activeAt, List.find?_map]
  rw [hm] at hn
  cases hp : s.activeAt d l with
  | none => simp [hp] at hn
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at hn
    subst next
    exact Or.inr ⟨p, rfl, FighterPhase.Grows.refl d p⟩

private theorem payoff (P : FighterParams) (d born l : ℕ) (q : Coordinate)
    (s : FighterState) : Descends d born s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact refl d born s
  · split
    · have ha := allocate d born l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact trans d born ha (recordPayoff d born q next)
    · exact refl d born s

private theorem fulfillReady (P : FighterParams) (d born l : ℕ) (s : FighterState) :
    Descends d born s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact refl d born s
  · apply foldl
    intro q t
    exact payoff P d born l q t

private theorem fuelUnit (P : FighterParams) (d born l : ℕ) (q : Coordinate)
    (s : FighterState) : Descends d born s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact refl d born s
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc : Descends d born s (s.putPhase d charged) :=
        putPhase d born s charged
          (Or.inr ⟨phase, by simpa [charged, hl] using hphase, FighterPhase.Grows.refl d phase⟩)
      have ha := allocate d born l .fuel (levelUpper l + d) out (s.putPhase d charged)
      have hbefore := trans d born hc ha
      change Descends d born s
        (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
        | (next, success) => if success then
            fighterFulfillReady P d l (next.putPhase d
              ((charged.insertIndex d q index).fundRequests d next.fulfilled)) else next)
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact hbefore
        · have hstay : next.activeAt d l = some charged := by
            have hh := activeAt_fighterAllocate_of_success d l .fuel (levelUpper l + d) out
              (s.putPhase d charged) (by rw [he])
            rw [he] at hh
            exact hh.trans (by simp [FighterState.putPhase, activeAt, charged, hl])
          apply trans d born hbefore
          apply trans d born
            (putPhase d born next
              ((charged.insertIndex d q index).fundRequests d next.fulfilled)
              (Or.inr ⟨charged,
                by simpa [FighterPhase.fundRequests, FighterPhase.insertIndex, charged, hl]
                  using hstay,
                FighterPhase.Grows.insertIndex d charged q index⟩))
          exact fulfillReady P d born l _
    · exact refl d born s

private theorem fuelUnits (P : FighterParams) (d born l : ℕ) (q : Coordinate)
    (count : ℕ) (s : FighterState) : Descends d born s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact refl d born s
  | succ count ih => exact trans d born (fuelUnit P d born l q s) (ih _)

private theorem opponent (P : FighterParams) (d born l : ℕ) (event : ProgramEvent)
    (s : FighterState) : Descends d born s (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact refl d born s
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact refl d born s
    · rename_i q index htuple
      split
      · exact refl d born s
      · split
        · exact cancel d born l .opponentExhausted l s
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          change Descends d born s
            (fighterFulfillReady P d l (s.putPhase d (next.fundRequests d s.fulfilled)))
          apply trans d born
            (putPhase d born s (next.fundRequests d s.fulfilled) (Or.inr ⟨phase,
              by simpa [FighterPhase.fundRequests, next, inserted, FighterPhase.insertIndex, hl]
                using hphase,
              FighterPhase.Grows.insertIndex d phase q index⟩))
          exact fulfillReady P d born l _

private theorem dummy (d born l : ℕ) (s : FighterState) :
    Descends d born s (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact refl d born s
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact refl d born s
    · rename_i out hout
      split
      · exact refl d born s
      · have ha := allocate d born l .dummy (levelInput d l) out s
        cases he : fighterAllocate d l .dummy (levelInput d l) out s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hstay : next.activeAt d l = some phase := by
              have hh := activeAt_fighterAllocate_of_success d l .dummy (levelInput d l) out s
                (by rw [he])
              rw [he] at hh
              exact hh.trans hphase
            exact trans d born ha
              (putPhase d born next { phase with dummyIssued := true }
                (Or.inr ⟨phase, by simpa [hl] using hstay, FighterPhase.Grows.refl d phase⟩))

private theorem flushBuffer (d born l : ℕ) (s : FighterState) :
    Descends d born s ((fighterFlushBuffer d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterFlushBuffer, hs] using refl d born s
  | some phase =>
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hs
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · exact putPhase d born s
        { phase with
          officialCode := ((phase.game d).afterMove (phase.official d) phase.buffer).encode
          buffer := List.replicate (phase.game d).coordinates.length 0 }
        (Or.inr ⟨phase, by simpa [hl] using hs, FighterPhase.Grows.refl d phase⟩)
    · exact refl d born s

private theorem strategyMove (P : FighterParams) (d born l : ℕ) (s : FighterState) :
    Descends d born s ((fighterStrategyMove P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterStrategyMove, hs] using refl d born s
  | some phase =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none =>
        simp only [Option.bind_none, Option.getD_none]
        exact refl d born s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := ((phase.game d).coordinates.zipIdx).foldl (fun s (q, i) =>
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : Descends d born s next := by
            apply foldl
            intro qi t
            exact fuelUnits P d born l qi.1 (move[qi.2]?.getD 0) t
          change Descends d born s
            ((match next.activeAt d l with
              | none => some next
              | some live => some (next.putPhase d
                  { live with officialCode :=
                      ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d l with
          | none => exact hn
          | some live =>
            have hl := FighterState.level_eq_of_activeAt_eq_some (p := live) hlive
            exact trans d born hn
              (putPhase d born next
                { live with officialCode :=
                    ((phase.game d).afterMove (phase.official d) move).encode }
                (Or.inr ⟨live, by simpa [hl] using hlive, FighterPhase.Grows.refl d live⟩))
        · exact refl d born s
    · exact refl d born s

private theorem levelAction (P : FighterParams) (d born l : ℕ) (s : FighterState) :
    Descends d born s ((fighterLevelAction P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterLevelAction, hs] using refl d born s
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact dummy d born l s
    · split
      · exact payoff P d born l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove P d born l s
        | some next =>
          have h := flushBuffer d born l s
          simpa only [hf] using h

private theorem closure (P : FighterParams) (d born l fuel : ℕ) (s : FighterState) :
    Descends d born s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact refl d born s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact refl d born s
    | some next =>
      have hn := levelAction P d born l s
      simp only [ha, Option.getD_some] at hn
      exact trans d born hn (ih next)

private theorem startPhase (P : FighterParams) (d born l : ℕ) (candidate : Candidate)
    (s : FighterState) (hborn : candidate.2 = born) :
    Descends d born s (fighterStartPhase P d l candidate s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : Descends d born s waiting :=
    trans d born (cancel d born l .replaced l s) (abortAbove d born l _)
  have hp := putPhase d born waiting (fighter_construction P d l candidate waiting)
    (Or.inl (by simpa [fighter_construction, FighterPhase.fundRequests] using hborn))
  apply trans d born hw
  apply trans d born hp
  exact of_active_ended_eq d born _ _ rfl rfl

private theorem processLevel (P : FighterParams) (d born l : ℕ) (event : Option TimedEvent)
    (s : FighterState) (hevent : ∀ e, event = some e → e.1 = born) :
    Descends d born s (fighterProcessLevel P d l event s) := by
  unfold fighterProcessLevel
  apply trans d born (fulfillReady P d born l s)
  cases event with
  | none => exact closure P d born l _ _
  | some e =>
    dsimp only
    split
    · exact trans d born (startPhase P d born l _ _ (hevent e rfl)) (closure P d born l _ _)
    · exact trans d born (opponent P d born l _ _) (closure P d born l _ _)

/-- All finite operations in one event preserve record ancestry and counter growth;
the only new phase is stamped by that event's actual emission tick. -/
private theorem actions (P : FighterParams) (d tick : ℕ) (s : FighterState) :
    Descends d tick s (fighter_actions P d tick s) := by
  unfold fighter_actions
  split
  · constructor
    · intro l phase hp
      simp [activeAt, initialFighterState] at hp
    · intro e he
      simp [initialFighterState] at he
  · apply trans d tick (of_active_ended_eq d tick s _ rfl rfl)
    apply foldl
    intro l t
    exact processLevel P d tick l (eventAt P.B tick) t
      (fun _ h => (canonical_enumeration_spec_sound P.B h).1)

end Descends

end FighterState

/-- Every active or archived phase has already reached its own emission timestamp. -/
theorem fighterState_candidate_time_le (P : FighterParams) (d tick : ℕ) :
    (∀ l phase, (fighterState P d tick).activeAt d l = some phase →
      phase.candidate.2 ≤ tick) ∧
    (∀ e ∈ (fighterState P d tick).ended, e.1.candidate.2 ≤ tick) := by
  induction tick with
  | zero => simp [fighterState, initialFighterState, FighterState.activeAt]
  | succ tick ih =>
    have hstep : FighterState.Descends d (tick + 1) (fighterState P d tick)
        (fighterState P d (tick + 1)) :=
      FighterState.Descends.actions P d (tick + 1) (fighterState P d tick)
    refine ⟨?_, ?_⟩
    · intro l phase hp
      rcases hstep.1 l phase hp with h | ⟨old, ho, hgrowth⟩
      · exact h.le
      · rw [hgrowth.2.1]
        exact (ih.1 l old ho).trans (Nat.le_succ tick)
    · intro e he
      rcases hstep.2 e he with he | h | ⟨old, ho, hgrowth⟩
      · exact (ih.2 e he).trans (Nat.le_succ tick)
      · exact h.le
      · rw [hgrowth.2.1]
        exact (ih.1 e.1.level old ho).trans (Nat.le_succ tick)

/-- The phase named by the marker's emission timestamp has no record before that timestamp.
Neither an active record nor an archived record can precede its own start event. -/
theorem trueMarkerPhase_eq_none_of_lt
    (P : FighterParams) (d l tick : ℕ)
    (htick : tick < markerTick P.B (levelScale l)) :
    trueMarkerPhase P d l tick = none := by
  have hb := fighterState_candidate_time_le P d tick
  let state := fighterState P d tick
  have harchive : (state.ended.find? (fun e =>
      decide (e.1.level = l ∧ e.1.candidate = markerCandidate P.B (levelScale l)))).map
      Prod.fst = none := by
    cases hf : state.ended.find? (fun e =>
        decide (e.1.level = l ∧ e.1.candidate = markerCandidate P.B (levelScale l))) with
    | none => rfl
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have htest := List.find?_some (p := fun e : EndedPhase =>
        decide (e.1.level = l ∧ e.1.candidate = markerCandidate P.B (levelScale l))) hf
      have hyes : e.1.level = l ∧ e.1.candidate = markerCandidate P.B (levelScale l) :=
        of_decide_eq_true htest
      have htime := hb.2 e he
      rw [hyes.2] at htime
      simp only [markerCandidate] at htime
      omega
  unfold trueMarkerPhase fighterPhaseAt
  change (match state.activeAt d l with
    | some phase => if phase.candidate = markerCandidate P.B (levelScale l) then some phase
        else (state.ended.find? (fun e =>
          decide (e.1.level = l ∧ e.1.candidate = markerCandidate P.B (levelScale l)))).map
          Prod.fst
    | none => (state.ended.find? (fun e =>
        decide (e.1.level = l ∧ e.1.candidate = markerCandidate P.B (levelScale l)))).map
        Prod.fst) = none
  cases hp : state.activeAt d l with
  | none => exact harchive
  | some phase =>
    dsimp only
    split_ifs with hc
    · have htime := hb.1 l phase hp
      rw [hc] at htime
      simp only [markerCandidate] at htime
      omega
    · exact harchive

/-- Across one completed event, two surviving records of the same true-marker phase have
the same game, and every live coordinate counter can only increase. The timestamp in
`TrueMarkerPhaseAt` excludes replacing this phase by a fresh start at the next tick. -/
private theorem trueMarkerPhaseAt_counter_growth
    (P : FighterParams) (d l tick : ℕ) (phase next : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase)
    (hnext : TrueMarkerPhaseAt P d l (tick + 1) next) :
    next.game d = phase.game d ∧
      ∀ q, (phase.game d).coordinateValue phase.liveCounters q ≤
        (next.game d).coordinateValue next.liveCounters q := by
  have hstep : FighterState.Descends d (tick + 1) (fighterState P d tick)
      (fighterState P d (tick + 1)) :=
    FighterState.Descends.actions P d (tick + 1) (fighterState P d tick)
  rcases hstep.1 l next hnext.2.2.2 with hborn | ⟨old, hold, hgrowth⟩
  · rw [hnext.2.2.1] at hborn
    simp only [markerCandidate] at hborn
    have := hphase.1
    omega
  · have heq : old = phase := Option.some.inj (hold.symm.trans hphase.2.2.2)
    subst old
    exact hgrowth.2.2

/-- In a fixed finite game, increasing the coordinate counters preserves every positive
normalized answer, including initial positives and zero-price funded coordinates. -/
private theorem normalizedAnswer_counterAnswer_mono
    (game : FiniteCounterGame) (before after : List ℕ) (cU : ℕ)
    (hgrowth : ∀ q, game.coordinateValue before q ≤ game.coordinateValue after q)
    (q : Coordinate)
    (hyes : normalizedAnswer cU (game.counterAnswer before) q = true) :
    normalizedAnswer cU (game.counterAnswer after) q = true := by
  simp only [normalizedAnswer, Bool.or_eq_true, decide_eq_true_eq] at hyes ⊢
  rcases hyes with h | h
  · exact Or.inl h
  · right
    rw [counter_answer_eq_true] at h ⊢
    rcases h with h | ⟨r, hr, hx, hk, hfunded⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, hx, hk, hfunded.trans (hgrowth r)⟩

/-- An active true-marker record is exactly the record read by the live answer function. -/
theorem fighterVirtualAnswerAt_eq_of_trueMarkerPhaseAt
    (P : FighterParams) (d l tick : ℕ) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase) :
    fighterVirtualAnswerAt P d l tick = phase.virtualAnswer P d := by
  simp [fighterVirtualAnswerAt, trueMarkerPhase, fighterPhaseAt,
    hphase.2.2.2, hphase.2.2.1]

/-- If the true-marker phase is active throughout the tail, its positive live answers
persist. This is induction on ticks using only one-event counter growth. -/
theorem fighterVirtualAnswerAt_persists
    (P : FighterParams) (d l : ℕ)
    (hactive : ∀ tick ≥ markerTick P.B (levelScale l),
      ∃ phase, TrueMarkerPhaseAt P d l tick phase)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (later : ℕ) (hlater : tick ≤ later) (q : Coordinate)
    (hyes : fighterVirtualAnswerAt P d l tick q = true) :
    fighterVirtualAnswerAt P d l later q = true := by
  induction hlater with
  | refl => exact hyes
  | @step later hle ih =>
    obtain ⟨phase, hphase⟩ := hactive later (htick.trans hle)
    obtain ⟨next, hnext⟩ := hactive (later + 1)
      ((htick.trans hle).trans (Nat.le_succ later))
    obtain ⟨hgame, hgrowth⟩ :=
      trueMarkerPhaseAt_counter_growth P d l later phase next hphase hnext
    rw [fighterVirtualAnswerAt_eq_of_trueMarkerPhaseAt P d l later phase hphase] at ih
    rw [fighterVirtualAnswerAt_eq_of_trueMarkerPhaseAt P d l (later + 1) next hnext]
    unfold FighterPhase.virtualAnswer at ih ⊢
    rw [hgame] at hgrowth ⊢
    exact normalizedAnswer_counterAnswer_mono _ _ _ _ hgrowth q ih

end Kolmogorov.Milovanov
