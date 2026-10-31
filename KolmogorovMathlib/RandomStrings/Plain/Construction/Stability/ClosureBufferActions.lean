/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace

/-!
# Single actions preserve the buffer invariant

The closure of a level (`fighterClosure`) repeatedly applies `fighterLevelAction`, which performs
one enabled action on the active phase of the level: the optional dummy allocation, a safe
payoff, the flush of the opponent buffer, or an entire controlled response
(`fighterStrategyMove`).

This module proves that each of these actions preserves `FighterPhase.BufferInvariant` of the
phase of the level (`bufferInvariant_activeAt_fighterLevelAction`).  A controlled response is
treated atomically: the successful fuel units add the unit vectors of the selected move to the
live counters and spend the controlled budget, after which the official child records exactly
the summed move.

Along the way it records how the lookup of a level's phase behaves under the individual
subroutines, which the other stability modules reuse:

* `activeAt_fighterAllocate`: allocation keeps the lookup of the issuing level on success and
  removes it on failure;
* `pending_update_of_activeAt_fighterPayoff`, `pending_update_of_activeAt_fighterFulfillReady`:
  payoffs change only the pending list of the surviving record;
* `controlledResponseView_fighterFuelUnit`: a surviving fuel unit adds its unit vector to the
  live counters and spends one controlled unit.

The result is used by `ClosureBufferCandidates` to propagate the buffer invariant along the
whole closure of a level.
-/

namespace Kolmogorov.Milovanov

/-- Allocation preserves the lookup of the issuing level on success and removes it on failure,
even in an arbitrary finite state. -/
lemma activeAt_fighterAllocate (d l : ℕ) (s : FighterState)
    (kind : DirectiveKind) (target : ℕ) (output : BitString) :
    (fighterAllocate d l kind target output s).1.activeAt d l =
      if (fighterAllocate d l kind target output s).2 then s.activeAt d l else none := by
  unfold fighterAllocate
  split
  · assumption
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact activeAt_fighterCancel d l _ _ _
    | some p => exact activeAt_fighterAbortAbove d l _

/-- A surviving payoff changes only the pending list of the earlier active record of the
issuing level. -/
lemma pending_update_of_activeAt_fighterPayoff (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) :
    ∀ live, (fighterPayoff P d l q s).activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧ ∃ pending, live = { old with pending := pending } := by
  have hrefl (live : FighterPhase) (h : s.activeAt d l = some live) :
      ∃ old, s.activeAt d l = some old ∧ ∃ pending, live = { old with pending := pending } :=
    ⟨live, h, live.pending, rfl⟩
  unfold fighterPayoff
  split
  · exact hrefl
  · split
    · have ha := activeAt_fighterAllocate d l s .payoff q.2 q.1
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
        · intro live hlive
          rw [ha] at hlive
          contradiction
        · intro live hlive
          simp only [FighterState.activeAt, List.find?_map] at hlive
          obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hlive
          exact ⟨old, ha ▸ hold, _, rfl⟩
    · exact hrefl

/-- The immediate payoff fold changes only pending lists; it cannot revive a cancelled issuing
phase. -/
lemma pending_update_of_activeAt_fighterFulfillReady (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    ∀ live, (fighterFulfillReady P d l s).activeAt d l = some live →
      ∃ old, s.activeAt d l = some old ∧ ∃ pending, live = { old with pending := pending } := by
  have hfold (qs : List Coordinate) (s : FighterState) :
      ∀ live, (qs.foldl (fun s q ↦ fighterPayoff P d l q s) s).activeAt d l = some live →
        ∃ old, s.activeAt d l = some old ∧ ∃ pending, live = { old with pending := pending } := by
    induction qs generalizing s with
    | nil => exact fun live h ↦ ⟨live, h, live.pending, rfl⟩
    | cons q qs ih =>
      intro live hlive
      obtain ⟨mid, hm, pending, rfl⟩ := ih _ live hlive
      obtain ⟨old, ho, pending', rfl⟩ :=
        pending_update_of_activeAt_fighterPayoff P d l q s mid hm
      exact ⟨old, ho, pending, rfl⟩
  unfold fighterFulfillReady
  split
  · exact fun live h ↦ ⟨live, h, live.pending, rfl⟩
  · exact hfold _ _

/-- A surviving designated fuel unit adds its unit vector to the live counters and spends one
controlled unit, preserving the other tracked fields. -/
lemma controlledResponseView_fighterFuelUnit (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (q : Coordinate)
    (hp : s.activeAt d l = some p) (hq : q ∈ (p.game d).coordinates)
    (hbudget : 0 < p.controlledRemaining) :
    ∀ live, (fighterFuelUnit P d l q s).activeAt d l = some live →
      controlledResponseView live = controlledResponseView
        { p with liveCounters := (p.game d).addCounters p.liveCounters (p.unitVector d q)
                 controlledRemaining := p.controlledRemaining - 1 } := by
  have hlevel : p.level = l := FighterState.level_eq_of_activeAt_eq_some hp
  let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
  let index := fighterFreshString d (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
  let output := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
  simp only [fighterFuelUnit, hp, ite_eq_left
    (show q ∈ (p.game d).coordinates ∧ 0 < p.controlledRemaining from ⟨hq, hbudget⟩)]
  have ha := activeAt_fighterAllocate d l (s.putPhase d charged) .fuel (levelUpper l + d) output
  cases he : fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
  | mk next success =>
    rw [he] at ha
    cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
    · intro live hlive
      rw [ha] at hlive
      contradiction
    · intro live hlive
      obtain ⟨old, hold, pending, rfl⟩ :=
        pending_update_of_activeAt_fighterFulfillReady P d l _ live hlive
      have hput : (next.putPhase d
          ((charged.insertIndex d q index).fundRequests d next.fulfilled)).activeAt d l =
          some ((charged.insertIndex d q index).fundRequests d next.fulfilled) := by
        simp [FighterState.putPhase, FighterState.activeAt, FighterPhase.fundRequests,
          FighterPhase.insertIndex, charged, hlevel]
      rw [hput] at hold
      cases hold
      rfl

/-- An affordable finite unit trace, if it survives, spends exactly its length and increments
each counter by the number of commands at that coordinate. Cancellation leaves every remaining
command inert. -/
private lemma activeAt_replayFuelUnits (P : FighterParams) (d l : ℕ)
    (commands : List Coordinate) (s : FighterState) (p : FighterPhase)
    (hp : s.activeAt d l = some p)
    (hlen : p.liveCounters.length = (p.game d).coordinates.length)
    (hcommands : ∀ q ∈ commands, q ∈ (p.game d).coordinates)
    (hbudget : commands.length ≤ p.controlledRemaining) :
    ∀ live, (replayFuelUnits P d l commands s).activeAt d l = some live →
      live.gameCode = p.gameCode ∧ live.controlledPlayer = p.controlledPlayer ∧
      live.opponentRemaining = p.opponentRemaining ∧ live.buffer = p.buffer ∧
      live.controlledRemaining + commands.length = p.controlledRemaining ∧
      live.liveCounters.length = (p.game d).coordinates.length ∧
      ∀ i (hi : i < (p.game d).coordinates.length),
        live.liveCounters[i]?.getD 0 = p.liveCounters[i]?.getD 0 +
          commands.count ((p.game d).coordinates[i]'hi) := by
  have hnone (commands : List Coordinate) (s : FighterState) (hs : s.activeAt d l = none) :
      replayFuelUnits P d l commands s = s := by
    induction commands with
    | nil => rfl
    | cons q commands ih =>
      simpa only [replayFuelUnits, List.foldl_cons, fighterFuelUnit, hs] using ih
  induction commands generalizing s p with
  | nil =>
    intro live hlive
    rw [show replayFuelUnits P d l [] s = s from rfl, hp] at hlive
    cases hlive
    exact ⟨rfl, rfl, rfl, rfl, by simp, hlen, by simp⟩
  | cons q commands ih =>
    have hq := hcommands q (by simp)
    have hpos : 0 < p.controlledRemaining := by
      simp only [List.length_cons] at hbudget
      omega
    have hview := controlledResponseView_fighterFuelUnit P d l s p q hp hq hpos
    change ∀ live, (replayFuelUnits P d l commands (fighterFuelUnit P d l q s)).activeAt d l =
      some live → _
    cases ht : (fighterFuelUnit P d l q s).activeAt d l with
    | none =>
      rw [hnone commands _ ht]
      intro live hlive
      rw [ht] at hlive
      contradiction
    | some mid =>
      have hv := hview mid ht
      simp only [controlledResponseView, Prod.mk.injEq] at hv
      obtain ⟨hgamecode, hplayer, hopponent, hbuffer, hcounters, hremaining⟩ := hv
      have hgame : mid.game d = p.game d := congrArg decodeCounterGame hgamecode
      have hlenmid : mid.liveCounters.length = (mid.game d).coordinates.length := by
        rw [hcounters, hgame]
        simp [FiniteCounterGame.addCounters]
      have htail : ∀ r ∈ commands, r ∈ (mid.game d).coordinates := by
        intro r hr
        rw [hgame]
        exact hcommands r (List.mem_cons_of_mem q hr)
      have hcost : commands.length ≤ mid.controlledRemaining := by
        simp only [List.length_cons] at hbudget
        omega
      intro live hlive
      obtain ⟨hg, hc, ho, hb, hr, hll, hvals⟩ := ih _ mid ht hlenmid htail hcost live hlive
      refine ⟨hg.trans hgamecode, hc.trans hplayer, ho.trans hopponent,
        hb.trans hbuffer, ?_, by simpa only [hgame] using hll, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro i hi
        have hiv : i < (mid.game d).coordinates.length := by simpa only [hgame] using hi
        have hval := hvals i hiv
        simp only [hgame] at hval
        have hunit : (p.unitVector d q)[i]?.getD 0 =
            if (p.game d).coordinates[i]'hi = q then 1 else 0 := by
          simp [FighterPhase.unitVector, List.getElem?_eq_getElem hi]
        have hmid : mid.liveCounters[i]?.getD 0 = p.liveCounters[i]?.getD 0 +
            if (p.game d).coordinates[i]'hi = q then 1 else 0 := by
          rw [hcounters]
          simpa [FiniteCounterGame.addCounters, List.getElem?_range hi] using
            congrArg (fun n ↦ p.liveCounters[i]?.getD 0 + n) hunit
        by_cases heq : q = (p.game d).coordinates[i]'hi
        · simp only [heq, ite_true] at hmid
          simp only [heq, List.count_cons_self]
          omega
        · simp only [Ne.symm heq, ite_false, Nat.add_zero] at hmid
          rw [List.count_cons_of_ne heq]
          omega

/-- A surviving affordable vector batch adds exactly that vector to the live counters and
subtracts its sum from the controlled budget, preserving the game, controlled player, opponent
budget, and buffer. -/
private lemma controlledResponseView_foldl_fighterFuelUnits (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (move : CounterMove)
    (hp : s.activeAt d l = some p)
    (hlive : p.liveCounters.length = (p.game d).coordinates.length)
    (hlen : move.length = (p.game d).coordinates.length)
    (hbudget : move.sum ≤ p.controlledRemaining) :
    let next := (p.game d).coordinates.zipIdx.foldl
      (fun s qi ↦ fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) s
    ∀ live, next.activeAt d l = some live →
      controlledResponseView live = controlledResponseView
        { p with liveCounters := (p.game d).addCounters p.liveCounters move
                 controlledRemaining := p.controlledRemaining - move.sum } := by
  dsimp only
  rw [foldl_fighterFuelUnits_eq_replayFuelUnits P d l _ move hlen s]
  obtain ⟨hmem, hlength, hcount⟩ :=
    unitCommands_spec (p.game d).coordinates move (nodup_eraseDups_list _) hlen
  have heffect := activeAt_replayFuelUnits P d l (unitCommands (p.game d).coordinates move)
    s p hp hlive hmem (by simpa only [hlength] using hbudget)
  intro live hl
  obtain ⟨hg, hc, ho, hb, hr, hll, hvals⟩ := heffect live hl
  simp only [controlledResponseView, Prod.mk.injEq]
  refine ⟨hg, hc, ho, hb, ?_, ?_⟩
  · apply List.ext_getElem
    · simpa [FiniteCounterGame.addCounters] using hll
    · intro i hi hi'
      have hgi : i < (p.game d).coordinates.length := by omega
      have hv := hvals i hgi
      rw [hcount i hgi] at hv
      have hgval : ((p.game d).addCounters p.liveCounters move)[i]?.getD 0 =
          p.liveCounters[i]?.getD 0 + move[i]?.getD 0 :=
        FiniteCounterGame.getD_addCounters _ _ _ _ hgi
      rw [List.getElem?_eq_getElem hi, Option.getD_some] at hv
      rw [List.getElem?_eq_getElem hi', Option.getD_some] at hgval
      omega
  · rw [hlength] at hr
    omega

/-- Counter addition is commutative in its two vector arguments. -/
private lemma addCounters_right_comm (g : FiniteCounterGame) (a b c : List ℕ) :
    g.addCounters (g.addCounters a b) c = g.addCounters (g.addCounters a c) b := by
  apply List.ext_getElem
  · simp [FiniteCounterGame.addCounters]
  · intro i hi hi'
    have hgi : i < g.coordinates.length := by
      simpa [FiniteCounterGame.addCounters] using hi
    simp [FiniteCounterGame.addCounters, List.getElem?_range hgi, Nat.add_right_comm]

/-- Installing and decoding the official child restores the buffer invariant from the exact live
effect of the controlled vector. -/
private lemma bufferInvariant_of_controlledResponseView (d : ℕ) (p live : FighterPhase)
    (move : CounterMove) (hinv : p.BufferInvariant d)
    (hactive : (p.game d).activePlayer (p.official d) = p.controlledPlayer)
    (hview : controlledResponseView live = controlledResponseView
      { p with liveCounters := (p.game d).addCounters p.liveCounters move
               controlledRemaining := p.controlledRemaining - move.sum }) :
    ({ live with
      officialCode := ((p.game d).afterMove (p.official d) move).encode }).BufferInvariant d := by
  simp only [controlledResponseView, Prod.mk.injEq] at hview
  obtain ⟨hg, hctrl, hop, hbuf, hcounters, hremaining⟩ := hview
  have hgame : live.game d = p.game d := congrArg decodeCounterGame hg
  have hactive' : (p.game d).activePlayer (p.official d) = false := hactive.trans hinv.1
  change live.controlledPlayer = false ∧ live.liveCounters =
      (live.game d).addCounters
        (decodeCounterPosition (live.game d)
          ((p.game d).afterMove (p.official d) move).encode).counters live.buffer ∧
    (decodeCounterPosition (live.game d)
      ((p.game d).afterMove (p.official d) move).encode).leftBudget =
        live.controlledRemaining ∧
    (decodeCounterPosition (live.game d)
      ((p.game d).afterMove (p.official d) move).encode).rightBudget =
        live.opponentRemaining + live.buffer.sum
  rw [hgame, decode_encode_counter_position]
  refine ⟨hctrl.trans hinv.1, ?_, ?_, ?_⟩
  · change live.liveCounters = (p.game d).addCounters
      ((p.game d).addCounters (p.official d).counters move) live.buffer
    rw [hcounters, hinv.2.1, hbuf]
    exact addCounters_right_comm _ _ _ _
  · simpa [FiniteCounterGame.afterMove, hactive', hinv.2.2.1] using hremaining.symm
  · simp [FiniteCounterGame.afterMove, hactive', hop, hbuf, hinv.2.2.2]

/-- The optional dummy allocation preserves the buffer invariant of the issuing phase. -/
private lemma bufferInvariant_activeAt_fighterDummy (d l : ℕ) (state : FighterState)
    (phase : FighterPhase) (hphase : state.activeAt d l = some phase)
    (hinv : phase.BufferInvariant d) :
    ∀ phase', (fighterDummy d l state).activeAt d l = some phase' →
      phase'.BufferInvariant d := by
  have hrefl : ∀ phase', state.activeAt d l = some phase' → phase'.BufferInvariant d := by
    intro phase' h
    rw [hphase] at h
    cases h
    exact hinv
  unfold fighterDummy
  simp only [hphase]
  split
  · exact hrefl
  · rename_i output _
    split
    · exact hrefl
    · have ha := activeAt_fighterAllocate d l state .dummy (levelInput d l) output
      cases he : fighterAllocate d l .dummy (levelInput d l) output state with
      | mk allocated success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
        · intro phase' hphase'
          rw [ha] at hphase'
          contradiction
        · intro phase' hphase'
          rw [FighterState.activeAt_putPhase d l _ _ ?_] at hphase'
          · cases hphase'
            exact hinv
          · have hlevel := FighterState.level_eq_of_activeAt_eq_some hphase
            exact hlevel

/-- Flushing the opponent buffer into the official position preserves the buffer invariant. -/
private lemma bufferInvariant_activeAt_fighterFlushBuffer (d l : ℕ) (state next : FighterState)
    (phase : FighterPhase) (hphase : state.activeAt d l = some phase)
    (hinv : phase.BufferInvariant d) (hflush : fighterFlushBuffer d l state = some next) :
    ∀ phase', next.activeAt d l = some phase' → phase'.BufferInvariant d := by
  intro phase' hphase'
  unfold fighterFlushBuffer at hflush
  rw [hphase] at hflush
  simp only [bind, Option.bind_some] at hflush
  split at hflush
  · rename_i hcond
    cases hflush
    rw [FighterState.activeAt_putPhase d l _ _ ?_] at hphase'
    · cases hphase'
      have hactive : (phase.game d).activePlayer (phase.official d) = true := by
        simpa [hinv.1] using hcond.2.1
      have hlen : ((phase.game d).afterMove (phase.official d) phase.buffer).counters.length =
          (phase.game d).coordinates.length := by
        simp [FiniteCounterGame.afterMove, FiniteCounterGame.addCounters]
      refine ⟨hinv.1, ?_, ?_, ?_⟩
      · change phase.liveCounters = (phase.game d).addCounters
          (decodeCounterPosition (phase.game d)
            ((phase.game d).afterMove (phase.official d) phase.buffer).encode).counters
          (List.replicate (phase.game d).coordinates.length 0)
        rw [decode_encode_counter_position, FiniteCounterGame.addCounters_replicate_zero _ _ hlen]
        exact hinv.2.1
      · change (decodeCounterPosition (phase.game d)
          ((phase.game d).afterMove (phase.official d) phase.buffer).encode).leftBudget =
            phase.controlledRemaining
        rw [decode_encode_counter_position]
        simpa [FiniteCounterGame.afterMove, hactive] using hinv.2.2.1
      · change (decodeCounterPosition (phase.game d)
          ((phase.game d).afterMove (phase.official d) phase.buffer).encode).rightBudget =
            phase.opponentRemaining + (List.replicate (phase.game d).coordinates.length 0).sum
        rw [decode_encode_counter_position]
        simp [FiniteCounterGame.afterMove, hactive, hinv.2.2.2]
    · have hlevel := FighterState.level_eq_of_activeAt_eq_some hphase
      exact hlevel
  · cases hflush

/-- A complete controlled response preserves the buffer invariant: the live effect of the selected
move is installed as the official child. -/
private lemma bufferInvariant_activeAt_fighterStrategyMove (P : FighterParams) (d l : ℕ)
    (state next : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) (hinv : phase.BufferInvariant d)
    (hnext : fighterStrategyMove P d l state = some next) :
    ∀ phase', next.activeAt d l = some phase' → phase'.BufferInvariant d := by
  intro phase' hphase'
  simp only [fighterStrategyMove, hphase, bind, Option.bind_some] at hnext
  split at hnext
  · rename_i hguard
    cases hm : (phase.game d).strategy (phase.official d) with
    | none => simp [hm] at hnext
    | some move =>
      simp only [hm, Option.bind_some] at hnext
      split at hnext
      · rename_i hlegal
        let middle := (phase.game d).coordinates.zipIdx.foldl
          (fun s qi ↦ fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) state
        have hlen : phase.liveCounters.length = (phase.game d).coordinates.length := by
          rw [hinv.2.1]
          simp [FiniteCounterGame.addCounters]
        have hviews := controlledResponseView_foldl_fighterFuelUnits P d l state phase move
          hphase hlen hlegal.1.1 hlegal.2
        change (match middle.activeAt d l with
          | none => some middle
          | some live => some (middle.putPhase d
              { live with officialCode := ((phase.game d).afterMove (phase.official d) move).encode
              })) = some next at hnext
        cases hlive : middle.activeAt d l with
        | none =>
          simp only [hlive, Option.some.injEq] at hnext
          subst next
          rw [hlive] at hphase'
          contradiction
        | some live =>
          simp only [hlive, Option.some.injEq] at hnext
          subst next
          rw [FighterState.activeAt_putPhase d l _ _ ?_] at hphase'
          · cases hphase'
            exact bufferInvariant_of_controlledResponseView d phase live move hinv hguard.2.2
              (hviews live hlive)
          · have hlevel := FighterState.level_eq_of_activeAt_eq_some hlive
            exact hlevel
      · contradiction
  · contradiction

/-- One enabled action at a level preserves the buffer invariant of the level's active phase:
an opponent insertion adds the same unit to the live counters and the buffer, a flush transfers
the buffer into the official counters, and dummy and payoff actions leave these identities
untouched.  A controlled response is treated atomically: its successful fuel units update the live
counters and the controlled budget, after which the official child records exactly their summed
move. -/
lemma bufferInvariant_activeAt_fighterLevelAction (P : FighterParams) (d l : ℕ)
    (state next : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) (hinv : phase.BufferInvariant d)
    (hnext : fighterLevelAction P d l state = some next) :
    ∀ phase', next.activeAt d l = some phase' → phase'.BufferInvariant d := by
  simp only [fighterLevelAction, hphase, bind, Option.bind_some] at hnext
  split at hnext
  · cases hnext
    exact bufferInvariant_activeAt_fighterDummy d l state phase hphase hinv
  · split at hnext
    · cases hnext
      intro phase' hphase'
      obtain ⟨old, hold, pending, rfl⟩ :=
        pending_update_of_activeAt_fighterPayoff P d l _ state phase' hphase'
      rw [hphase] at hold
      cases hold
      exact hinv
    · split at hnext
      · rename_i hflush
        cases hnext
        exact bufferInvariant_activeAt_fighterFlushBuffer d l state next phase hphase hinv hflush
      · exact bufferInvariant_activeAt_fighterStrategyMove P d l state next phase hphase hinv hnext

end Kolmogorov.Milovanov
