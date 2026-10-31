/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.LiveCounters
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationState

/-!
# Simulation events of the true marker phase

This module proves the simulation case of the oracle agreement between the virtual and the actual
oracle of the true marker phase (blueprint node `constr:agreement`): a noninitial simple query
of the level tree is answered `true` by the final virtual answer.

The argument shows that every strict extension index of a retained coordinate eventually lies in
the stored index set of the true marker phase, so that its counter reaches the price of the
coordinate:

* indices already present in the base-machine table at the emission tick of the candidate are
  covered by the initialisation of the phase, because the phase invariant `PhaseInvariant` is
  preserved by every operation of the fighter construction;
* a later matching emission is serviced at the true marker level, and every surviving older record
  receives its index through `Descends`;
* `exists_tick_subset_indicesAt` collects the finitely many indices at a single tick.

The results are `fighterFinalVirtualAnswer_eq_true_of_simple_of_not_initialAnswer`, used by
`Diagonal.OracleAgreement` for the simulation case, and
`fighterAbortAbove_allocated_eq_active_sublist`, which describes priority abortion.
-/

namespace Kolmogorov.Milovanov

/-- All active and ended phases of a fighter state satisfy the predicate `F`. -/
private abbrev FighterState.AllPhases (F : FighterPhase → Prop) (s : FighterState) : Prop :=
  (∀ p ∈ s.active, F p) ∧ ∀ e ∈ s.ended, F e.1

private lemma FighterState.AllPhases.of_activeAt {F : FighterPhase → Prop} {s : FighterState}
    {d l : ℕ} {p : FighterPhase} (hs : s.AllPhases F) (hp : s.activeAt d l = some p) : F p :=
  hs.1 p (List.mem_of_find?_eq_some hp)

private lemma FighterState.AllPhases.foldl {F : FighterPhase → Prop} {α : Type}
    (f : α → FighterState → FighterState)
    (hf : ∀ a s, s.AllPhases F → (f a s).AllPhases F) (xs : List α) (s : FighterState)
    (hs : s.AllPhases F) : (xs.foldl (fun s a ↦ f a s) s).AllPhases F := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih _ (hf a s hs)

private lemma FighterState.AllPhases.putPhase {F : FighterPhase → Prop} {s : FighterState}
    (hs : s.AllPhases F) (d : ℕ) {p : FighterPhase} (hp : F p) : (s.putPhase d p).AllPhases F := by
  refine ⟨?_, hs.2⟩
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs.1 next (List.mem_filter.mp hn).1

/-- The hypotheses under which a predicate `F` on phases holds for all phases of every
fighter state: it only depends on the level, candidate, initial allocations, game code, stored
indices and opponent budget of a phase, it holds for a fresh phase, and it is preserved by
inserting an index, with or without charging the opponent budget. -/
private structure PhaseInvariant (P : FighterParams) (d : ℕ) (F : FighterPhase → Prop) :
    Prop where
  /-- `F` only depends on the listed fields of a phase. -/
  stable : ∀ p p' : FighterPhase,
    (p.level, p.candidate, p.initialAllocations, p.gameCode, p.indices, p.opponentRemaining) =
      (p'.level, p'.candidate, p'.initialAllocations, p'.gameCode, p'.indices,
        p'.opponentRemaining) → F p → F p'
  /-- `F` holds for a freshly constructed phase. -/
  init : ∀ l c s, validCandidate P.B (levelScale l) c = true →
    F (fighter_construction P d l c s)
  /-- `F` is preserved by a controlled insertion. -/
  controlled : ∀ p q index, F p → F (p.insertIndex d q index)
  /-- `F` is preserved by an affordable opponent insertion. -/
  opponent : ∀ p event q index,
    produces P.B.V event.1 [] event.2 →
    fighterOpponentTuple d p event = some (q, index) →
    index ∉ p.indicesAt d q → p.opponentRemaining ≠ 0 → F p →
    F { p.insertIndex d q index with opponentRemaining := p.opponentRemaining - 1 }

section PhaseInvariant

variable {P : FighterParams} {d : ℕ} {F : FighterPhase → Prop}

private lemma PhaseInvariant.allPhases_cancel (inv : PhaseInvariant P d F)
    (l cause : ℕ) (reason : PhaseEnd) (s : FighterState) (hs : s.AllPhases F) :
    (fighterCancel d l reason cause s).AllPhases F := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i p hp
    refine ⟨fun p hp ↦ hs.1 p (List.mem_filter.mp hp).1, ?_⟩
    intro e he
    rcases List.mem_append.mp he with hold | hnew
    · exact hs.2 e hold
    · have heq := List.mem_singleton.mp hnew
      subst e
      exact inv.stable p _ rfl (hs.of_activeAt hp)

private lemma PhaseInvariant.allPhases_abortAbove (inv : PhaseInvariant P d F)
    (l : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    (fighterAbortAbove d l s).AllPhases F := by
  unfold fighterAbortAbove
  refine FighterState.AllPhases.foldl _ ?_ _ _ hs
  intro p t ht
  split
  · exact inv.allPhases_cancel _ _ _ _ ht
  · exact ht

private lemma PhaseInvariant.allPhases_allocate (inv : PhaseInvariant P d F)
    (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString) (s : FighterState)
    (hs : s.AllPhases F) : (fighterAllocate d l kind target out s).1.AllPhases F := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact inv.allPhases_cancel _ _ _ _ hs
    | some p => exact inv.allPhases_abortAbove _ _ hs

private lemma PhaseInvariant.allPhases_payoff (inv : PhaseInvariant P d F)
    (l : ℕ) (q : Coordinate) (s : FighterState) (hs : s.AllPhases F) :
    (fighterPayoff P d l q s).AllPhases F := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := inv.allPhases_allocate l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · refine ⟨?_, ha.2⟩
          intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact inv.stable old _ rfl (ha.1 old hold)
    · exact hs

private lemma PhaseInvariant.allPhases_fulfillReady (inv : PhaseInvariant P d F)
    (l : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    (fighterFulfillReady P d l s).AllPhases F := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact FighterState.AllPhases.foldl _ (inv.allPhases_payoff l) _ _ hs

private lemma PhaseInvariant.allPhases_fuelUnit (inv : PhaseInvariant P d F)
    (l : ℕ) (q : Coordinate) (s : FighterState) (hs : s.AllPhases F) :
    (fighterFuelUnit P d l q s).AllPhases F := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.of_activeAt hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc : F charged := inv.stable phase _ rfl hq
      have ha := inv.allPhases_allocate l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (hs.putPhase d hc)
      change FighterState.AllPhases F
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
        · apply inv.allPhases_fulfillReady l
          exact ha.putPhase d
            (inv.stable (charged.insertIndex d q index) _ rfl (inv.controlled _ _ _ hc))
    · exact hs

private lemma PhaseInvariant.allPhases_fuelUnits (inv : PhaseInvariant P d F)
    (l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    (fighterFuelUnits P d l q count s).AllPhases F := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (inv.allPhases_fuelUnit l q s hs)

private lemma PhaseInvariant.allPhases_dummy (inv : PhaseInvariant P d F)
    (l : ℕ) (s : FighterState) (hs : s.AllPhases F) : (fighterDummy d l s).AllPhases F := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.of_activeAt hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := inv.allPhases_allocate l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact ha.putPhase d (inv.stable phase _ rfl hq)

private lemma PhaseInvariant.allPhases_opponent (inv : PhaseInvariant P d F)
    (l : ℕ) (e : ProgramEvent) (he : produces P.B.V e.1 [] e.2)
    (s : FighterState) (hs : s.AllPhases F) : (fighterOpponent P d l e s).AllPhases F := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.of_activeAt hp
    split
    · exact hs
    · rename_i q index htuple
      split
      · exact hs
      · rename_i hfresh
        split
        · exact inv.allPhases_cancel _ _ _ _ hs
        · rename_i hbudget
          apply inv.allPhases_fulfillReady l
          apply hs.putPhase d
          refine inv.stable { phase.insertIndex d q index with
            opponentRemaining := phase.opponentRemaining - 1 } _ rfl ?_
          exact inv.opponent phase e q index he htuple hfresh hbudget hq

private lemma PhaseInvariant.allPhases_startPhase (inv : PhaseInvariant P d F)
    (l : ℕ) (c : Candidate) (hc : validCandidate P.B (levelScale l) c = true)
    (s : FighterState) (hs : s.AllPhases F) : (fighterStartPhase P d l c s).AllPhases F := by
  unfold fighterStartPhase
  exact (inv.allPhases_abortAbove l _ (inv.allPhases_cancel l l .replaced s hs)).putPhase d
    (inv.init l c _ hc)

private lemma PhaseInvariant.allPhases_flushBuffer (inv : PhaseInvariant P d F)
    (l : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    ((fighterFlushBuffer d l s).getD s).AllPhases F := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := hs.of_activeAt hp
    simp only [bind, Option.bind_some]
    split
    · exact hs.putPhase d (inv.stable phase _ rfl hq)
    · exact hs

private lemma PhaseInvariant.allPhases_strategyMove (inv : PhaseInvariant P d F)
    (l : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    ((fighterStrategyMove P d l s).getD s).AllPhases F := by
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
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : next.AllPhases F := by
            refine FighterState.AllPhases.foldl _ ?_ _ _ hs
            intro qi t ht
            exact inv.allPhases_fuelUnits l qi.1 (move[qi.2]?.getD 0) t ht
          change FighterState.AllPhases F ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            exact hn.putPhase d (inv.stable live _ rfl (hn.of_activeAt hlive))
        · exact hs
    · exact hs

private lemma PhaseInvariant.allPhases_levelAction (inv : PhaseInvariant P d F)
    (l : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    ((fighterLevelAction P d l s).getD s).AllPhases F := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact inv.allPhases_dummy l s hs
    · split
      · exact inv.allPhases_payoff l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact inv.allPhases_strategyMove l s hs
        | some next =>
          have h := inv.allPhases_flushBuffer l s hs
          simpa only [hf, Option.getD_some] using h

private lemma PhaseInvariant.allPhases_closure (inv : PhaseInvariant P d F)
    (l fuel : ℕ) (s : FighterState) (hs : s.AllPhases F) :
    (fighterClosure P d l fuel s).AllPhases F := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := inv.allPhases_levelAction l s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private lemma PhaseInvariant.allPhases_processLevel (inv : PhaseInvariant P d F)
    (l : ℕ) (ev : Option TimedEvent) (hev : ∀ e, ev = some e → eventAt P.B e.1 = some e)
    (s : FighterState) (hs : s.AllPhases F) :
    (fighterProcessLevel P d l ev s).AllPhases F := by
  unfold fighterProcessLevel fighterCloseLevel
  apply inv.allPhases_closure
  cases ev with
  | none => exact inv.allPhases_fulfillReady l s hs
  | some e =>
    dsimp only
    have he := hev e rfl
    split
    · rename_i henabled
      apply inv.allPhases_startPhase l _ _ _ (inv.allPhases_fulfillReady l s hs)
      simp only [validCandidate, he, Option.any_some, decide_true, Bool.and_true]
      exact decide_eq_true henabled.2.1
    · exact inv.allPhases_opponent l _ (canonical_enumeration_spec_sound P.B he).2 _
        (inv.allPhases_fulfillReady l s hs)

/-- If `F` satisfies the hypotheses of `PhaseInvariant`, then every active and every ended phase
of every fighter state satisfies `F`. -/
private lemma PhaseInvariant.allPhases_fighterState (inv : PhaseInvariant P d F) (tick : ℕ) :
    (fighterState P d tick).AllPhases F := by
  induction tick with
  | zero =>
    exact ⟨by simp [fighterState, initialFighterState], by simp [fighterState, initialFighterState]⟩
  | succ tick ih =>
    change (fighter_actions P d (tick + 1) (fighterState P d tick)).AllPhases F
    unfold fighter_actions
    split
    · exact ⟨by simp [initialFighterState], by simp [initialFighterState]⟩
    · let current := { fighterState P d tick with
          tick := tick + 1, schedule := masterState P.B (tick + 1) }
      refine FighterState.AllPhases.foldl _ ?_ _ current ih
      intro l s hs
      apply inv.allPhases_processLevel l _ _ s hs
      intro e he
      have ht := (canonical_enumeration_spec_sound P.B he).1
      simpa only [ht] using he

end PhaseInvariant

/-- Every active phase still contains all matching extension indices from the base-machine table
at its candidate's emission tick. Later insertions preserve this snapshot coverage. -/
private lemma mem_indicesAt_of_mem_stageOutputs
    (P : FighterParams) (d tick : ℕ) (phase : FighterPhase)
    (hphase : phase ∈ (fighterState P d tick).active) :
    ∀ q ∈ (phase.game d).coordinates, ∀ index,
      pairCode (triple q.1 (q.2 - d) phase.candidate.1) index ∈
        stageOutputs P.B (levelUpper phase.level) phase.candidate.2 →
      index ∈ phase.indicesAt d q := by
  let Cover (p : FighterPhase) : Prop :=
    ∀ q ∈ (p.game d).coordinates, ∀ index,
      pairCode (triple q.1 (q.2 - d) p.candidate.1) index ∈
        stageOutputs P.B (levelUpper p.level) p.candidate.2 →
      index ∈ p.indicesAt d q
  have hinsert (p : FighterPhase) (q : Coordinate) (index : BitString)
      (hp : Cover p) : Cover (p.insertIndex d q index) := by
    intro r hr stored hy
    have hi := hp r hr stored hy
    rw [FighterPhase.indicesAt_insertIndex p d q r index hr]
    split
    · exact Finset.mem_insert_of_mem hi
    · exact hi
  have inv : PhaseInvariant P d Cover :=
    { stable := by
        intro p p' heq hp
        rcases p with ⟨l, c, s, a, g, is, o, v, b, r, f, pending, x, di, cp⟩
        rcases p' with ⟨l', c', s', a', g', is', o', v', b', r', f', pending', x', di', cp'⟩
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact hp
      init := by
        intro l c s hc q hq index hy
        rw [indicesAt_fighter_construction P d l c s q hq, List.mem_toFinset]
        exact mem_fighterInitialIndices P d l c s.allocated q index hc hy
      controlled := hinsert
      opponent := by
        intro p event q index he ht hf hb hp
        exact hinsert p q index hp }
  exact (inv.allPhases_fighterState tick).1 phase hphase

/-- A record with an older candidate descends from a previous record through any tracked
operation, with the same game and all its stored indices preserved. -/
private lemma exists_descends_of_candidate_ne
    (d born l : ℕ) (s t : FighterState) (next : FighterPhase)
    (hframe : FighterState.Descends d born s t)
    (hnext : t.activeAt d l = some next) (hold : next.candidate.2 ≠ born) :
    ∃ phase, s.activeAt d l = some phase ∧
      FighterPhase.Descends d phase next := by
  rcases hframe.1 l next hnext with hnew | hprev
  · exact (hold hnew).elim
  · exact hprev

/-- The detector recognizes a retained literal curried tuple when the program fits in the
phase's upper budget. The padding subtraction is reversed using its explicit lower bound. -/
private lemma fighterOpponentTuple_eq_some_of_pairCode
    (d : ℕ) (phase : FighterPhase) (q : Coordinate) (index : BitString)
    (event : ProgramEvent) (hdq : d ≤ q.2)
    (hq : q ∈ (phase.game d).coordinates)
    (hlen : event.1.length ≤ levelUpper phase.level)
    (hout : event.2 = pairCode (triple q.1 (q.2 - d) phase.candidate.1) index) :
    fighterOpponentTuple d phase event = some (q, index) := by
  have hcoord : (q.1, q.2 - d + d) = q := Prod.ext rfl (Nat.sub_add_cancel hdq)
  simp [fighterOpponentTuple, Nat.not_lt.mpr hlen, hout, decodeFirst_pairCode,
    decodeSecond_pairCode, decodeTriple_triple, hcoord, hq]

/-- Processing a matching later emission at its level supplies the index to every surviving
older record. A duplicate is already stored; zero opponent budget would cancel this
record; an affordable fresh insertion stores the index before closure. -/
private lemma mem_indicesAt_of_fighterProcessLevel
    (P : FighterParams) (d l born pos : ℕ) (event : ProgramEvent)
    (q : Coordinate) (index : BitString) (s : FighterState) (next : FighterPhase)
    (hnext : (fighterProcessLevel P d l (some (born, pos, event)) s).activeAt d l = some next)
    (hold : next.candidate.2 ≠ born) (hq : q ∈ (next.game d).coordinates)
    (hdq : d ≤ q.2) (hlen : event.1.length ≤ levelUpper l)
    (hlong : levelScale l < event.1.length)
    (hout : event.2 = pairCode (triple q.1 (q.2 - d) next.candidate.1) index) :
    index ∈ next.indicesAt d q := by
  classical
  let checked := fighterFulfillReady P d l s
  let inserted := fighterOpponent P d l event checked
  have hnostart : ¬ (fighterOwner d event.1.length = some l ∧
      event.1.length ≤ levelScale l ∧ P.Admissible d l) := by omega
  have hclose : (fighterCloseLevel P d l inserted).activeAt d l = some next := by
    simpa only [fighterProcessLevel, hnostart, ite_false] using hnext
  obtain ⟨mid, hmid, hmidnext⟩ := exists_descends_of_candidate_ne d born l inserted
    (fighterCloseLevel P d l inserted) next
    (FighterState.Descends.closure P d born l _ inserted) hclose hold
  have hmidold : mid.candidate.2 ≠ born := by
    rw [← hmidnext.2.1]
    exact hold
  obtain ⟨before, hbefore, hbeforemid⟩ := exists_descends_of_candidate_ne d born l checked
    inserted mid (FighterState.Descends.opponent P d born l event checked) hmid hmidold
  have hlevel : before.level = l :=
    FighterState.level_eq_of_activeAt_eq_some (p := before) hbefore
  have hbeforeq : q ∈ (before.game d).coordinates := by
    rw [← hbeforemid.2.2.1, ← hmidnext.2.2.1]
    exact hq
  have hbeforeout : event.2 =
      pairCode (triple q.1 (q.2 - d) before.candidate.1) index := by
    rw [← hbeforemid.2.1, ← hmidnext.2.1]
    exact hout
  have htuple := fighterOpponentTuple_eq_some_of_pairCode d before q index event hdq hbeforeq
    (by simpa only [hlevel] using hlen) hbeforeout
  have hstored : index ∈ mid.indicesAt d q := by
    by_cases hi : index ∈ before.indicesAt d q
    · have heq : mid = before := by
        have hm : checked.activeAt d l = some mid := by
          simpa only [inserted, fighterOpponent, hbefore, htuple, hi, ite_true] using hmid
        exact Option.some.inj (hm.symm.trans hbefore)
      simpa only [heq] using hi
    · by_cases hb : before.opponentRemaining = 0
      · have hm : (fighterCancel d l .opponentExhausted l checked).activeAt d l =
            some mid := by
          simpa only [inserted, fighterOpponent, hbefore, htuple, hi, ite_false, hb,
            ite_true] using hmid
        unfold fighterCancel at hm
        rw [hbefore] at hm
        change (checked.active.filter (fun p ↦ p.level != l)).find?
          (fun p ↦ p.level == l) = some mid at hm
        have hmem := List.mem_of_find?_eq_some hm
        have htest : mid.level = l := beq_iff_eq.mp
          (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hm)
        have hne := (List.mem_filter.mp hmem).2
        simp only [bne_iff_ne] at hne
        exact (hne htest).elim
      · let updated := { before.insertIndex d q index with
          opponentRemaining := before.opponentRemaining - 1
          buffer := (before.game d).addCounters before.buffer (before.unitVector d q) }
        let prepared := checked.putPhase d (updated.fundRequests d checked.fulfilled)
        have hm : (fighterFulfillReady P d l prepared).activeAt d l = some mid := by
          simpa only [inserted, fighterOpponent, hbefore, htuple, hi, ite_false, hb]
            using hmid
        obtain ⟨record, hrecord, hrecordmid⟩ := exists_descends_of_candidate_ne d born l prepared
          (fighterFulfillReady P d l prepared) mid
          (FighterState.Descends.fulfillReady P d born l prepared) hm hmidold
        have heq : record = updated.fundRequests d checked.fulfilled := by
          simpa [prepared, FighterState.putPhase, FighterState.activeAt,
            FighterPhase.fundRequests, updated, FighterPhase.insertIndex, hlevel]
            using hrecord.symm
        have hi' : index ∈ record.indicesAt d q := by
          rw [heq]
          change index ∈ (before.insertIndex d q index).indicesAt d q
          rw [FighterPhase.indicesAt_insertIndex before d q q index hbeforeq]
          simp
        exact hrecordmid.2.2.2 q hi'
  exact hmidnext.2.2.2 q hstored

/-- A later matching emission is serviced at the true-marker level in the global level fold.
The post-service record contains its index, and the remaining services preserve it. -/
private lemma mem_indicesAt_of_eventAt_succ
    (P : FighterParams) (d l tick pos : ℕ) (event : ProgramEvent)
    (phase next : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase)
    (hnext : TrueMarkerPhaseAt P d l (tick + 1) next)
    (hd : 1 ≤ d) (q : Coordinate) (index : BitString)
    (hq : q ∈ (next.game d).coordinates) (hdq : d ≤ q.2)
    (hevent : eventAt P.B (tick + 1) = some (tick + 1, pos, event))
    (hlen : event.1.length ≤ levelUpper l)
    (hlong : levelScale l < event.1.length)
    (hout : event.2 = pairCode (triple q.1 (q.2 - d) next.candidate.1) index) :
    index ∈ next.indicesAt d q := by
  classical
  let state := fighterState P d tick
  let current := { state with tick := tick + 1, schedule := masterState P.B (tick + 1) }
  let owner := fighterOwner d event.1.length
  let levels := ((current.active.map FighterPhase.level ++ owner.toList).eraseDups).mergeSort
    (· ≤ ·)
  let process := fun j s ↦ fighterProcessLevel P d j (some (tick + 1, pos, event)) s
  have hmem : l ∈ levels := by
    simp only [levels, List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
    left
    exact List.mem_map.mpr ⟨phase, List.mem_of_find?_eq_some hphase.2.2.2, hphase.2.1⟩
  obtain ⟨earlier, laterLevels, hlevels⟩ := List.mem_iff_append.mp hmem
  let before := earlier.foldl (fun s j ↦ process j s) current
  let after := process l before
  have hlook : (laterLevels.foldl (fun s j ↦ process j s) after).activeAt d l = some next := by
    have hh := hnext.2.2.2
    change (fighter_actions P d (tick + 1) state).activeAt d l = some next at hh
    unfold fighter_actions at hh
    have hd0 : d ≠ 0 := by omega
    simp only [hd0, ↓reduceIte] at hh
    rw [hevent] at hh
    change (levels.foldl (fun s j ↦ process j s) current).activeAt d l = some next at hh
    rw [hlevels, List.foldl_append, List.foldl_cons] at hh
    exact hh
  have htail := FighterState.Descends.foldl d (tick + 1) process
    (fun j s ↦ FighterState.Descends.processLevel P d (tick + 1) j
      (some (tick + 1, pos, event)) s (by intro e he; cases he; rfl)) laterLevels after
  have hold : next.candidate.2 ≠ tick + 1 := by
    rw [hnext.2.2.1]
    simp only [markerCandidate]
    have := hphase.1
    omega
  obtain ⟨record, hrecord, hrecordnext⟩ := exists_descends_of_candidate_ne d (tick + 1) l after
    (laterLevels.foldl (fun s j ↦ process j s) after) next htail hlook hold
  have hrecordold : record.candidate.2 ≠ tick + 1 := by
    rw [← hrecordnext.2.1]
    exact hold
  have hrq : q ∈ (record.game d).coordinates := by
    rw [← hrecordnext.2.2.1]
    exact hq
  have hrout : event.2 = pairCode (triple q.1 (q.2 - d) record.candidate.1) index := by
    rw [← hrecordnext.2.1]
    exact hout
  have hi := mem_indicesAt_of_fighterProcessLevel P d l (tick + 1) pos event q index before
    record hrecord hrecordold hrq hdq hlen hlong hrout
  exact hrecordnext.2.2.2 q hi

/-- Each strict extension index of a retained coordinate occurs in some live index set.
An index already in the saved table needs no insertion; otherwise its emission is
processed by the surviving phase, unless a controlled insertion has already supplied it. -/
private lemma exists_mem_indicesAt_of_mem_extensionSet
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (q : Coordinate) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase)
    (hqJ : q ∈ phase.J d) (index : BitString)
    (hi : index ∈ extensionSet P.B (levelScale l) 0
      (triple q.1 (q.2 - d) phase.candidate.1)) :
    ∃ tick ≥ markerTick P.B (levelScale l), ∃ live,
      TrueMarkerPhaseAt P d l tick live ∧ index ∈ live.indicesAt d q := by
  classical
  obtain ⟨_, game, _, hrecords, _⟩ :=
    (true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate).2.2.1
  obtain ⟨record, hrecord, hgame, _, _⟩ := hrecords (markerTick P.B (levelScale l)) le_rfl
  have heq : record = phase := Option.some.inj
    (hrecord.2.2.2.symm.trans hphase.2.2.2)
  subst record
  have hqcoords : q ∈ (phase.game d).coordinates := by
    simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
      List.mem_toFinset, List.mem_eraseDups] using hqJ
  have hret := (active_phase_game_tables P d _ phase
    (List.mem_of_find?_eq_some hphase.2.2.2)).1
  have hqret := hqJ
  rw [hret, hphase.2.1] at hqret
  have hdq : d ≤ q.2 := by
    obtain ⟨_, _, _, hlow, _⟩ :=
      (mem_finite_referee_coordinates _ _ _ q.1 q.2).mp hqret
    dsimp only [levelInput] at hlow
    omega
  let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
  have hsimple : Simple P.B.V output (levelUpper l) := by
    simpa only [extensionSet, Set.mem_ofPred_eq, extensionScale, Nat.add_zero,
      level_upper_eq] using hi
  obtain ⟨program, hlen, hprod⟩ := (simple_iff_exists_program _ _ _).mp hsimple
  obtain ⟨seen, pos, hevent⟩ :=
    (canonical_enumeration_spec_complete P.B program output).mp hprod
  have hseen : output ∈ stageOutputs P.B (levelUpper l) seen := by
    simp only [stageOutputs, stageOutputList, List.mem_toFinset,
      List.mem_eraseDups, List.mem_filterMap]
    refine ⟨(seen, pos, program, output),
      List.mem_of_getElem? ((canonical_enumeration_spec_position P.B hevent).2.2), ?_⟩
    simp only [hlen, ite_true]
  by_cases hbefore : seen ≤ markerTick P.B (levelScale l)
  · refine ⟨markerTick P.B (levelScale l), le_rfl, phase, hphase, ?_⟩
    apply mem_indicesAt_of_mem_stageOutputs P d _ phase
      (List.mem_of_find?_eq_some hphase.2.2.2) q hqcoords index
    change output ∈ stageOutputs P.B (levelUpper phase.level) phase.candidate.2
    rw [hphase.2.1, hphase.2.2.1]
    exact (canonical_enumeration_spec_mono P.B (levelUpper l) hbefore).1 hseen
  · have hmarker : markerTick P.B (levelScale l) < seen := by omega
    have hpos : 1 ≤ seen := by omega
    obtain ⟨previous, hprevious, _, _, _⟩ := hrecords (seen - 1) (by omega)
    obtain ⟨live, hlive, hgameLive, _, _⟩ := hrecords seen (by omega)
    refine ⟨seen, by omega, live, hlive, ?_⟩
    have hqlive : q ∈ (live.game d).coordinates := by
      rw [hgameLive, ← hgame]
      exact hqcoords
    have houtlive : output = pairCode (triple q.1 (q.2 - d) live.candidate.1) index := by
      dsimp only [output]
      rw [hphase.2.2.1, hlive.2.2.1]
    have hevent' : eventAt P.B (seen - 1 + 1) =
        some (seen - 1 + 1, pos, program, output) := by
      simpa only [Nat.sub_add_cancel hpos] using hevent
    have hlive' : TrueMarkerPhaseAt P d l (seen - 1 + 1) live := by
      simpa only [Nat.sub_add_cancel hpos] using hlive
    exact mem_indicesAt_of_eventAt_succ P d l (seen - 1) pos (program, output)
      previous live hprevious hlive' hgood.positive q index hqlive hdq hevent' hlen
      (lt_length_of_markerTick_lt_eventAt P.B (levelScale l) seen pos program output hmarker
        hevent)
      houtlive

/-- For any finite collection of indices, individual arrival witnesses and preservation in
each event yield one tick containing the entire collection. The empty collection uses
the first tick and requires no arrival witness. -/
private lemma exists_tick_subset_indicesAt
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (indices : Finset BitString)
    (hactive : ∀ tick ≥ markerTick P.B (levelScale l),
      ∃ phase, TrueMarkerPhaseAt P d l tick phase)
    (harrival : ∀ index ∈ indices, ∃ tick ≥ markerTick P.B (levelScale l), ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ index ∈ phase.indicesAt d q)
    (hgrowth : ∀ tick phase next, TrueMarkerPhaseAt P d l tick phase →
      TrueMarkerPhaseAt P d l (tick + 1) next →
        phase.indicesAt d q ⊆ next.indicesAt d q) :
    ∃ tick ≥ markerTick P.B (levelScale l), ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ indices ⊆ phase.indicesAt d q := by
  classical
  have hpersist (tick later : ℕ) (hle : tick ≤ later) (phase next : FighterPhase)
      (hphase : TrueMarkerPhaseAt P d l tick phase)
      (hnext : TrueMarkerPhaseAt P d l later next) :
      phase.indicesAt d q ⊆ next.indicesAt d q := by
    induction later, hle using Nat.le_induction generalizing next with
    | base =>
      have heq : phase = next := Option.some.inj
        (hphase.2.2.2.symm.trans hnext.2.2.2)
      subst next
      exact Finset.Subset.refl _
    | succ later hle ih =>
      obtain ⟨mid, hmid⟩ := hactive later (hphase.1.trans hle)
      exact (ih mid hmid).trans (hgrowth later mid next hmid hnext)
  induction indices using Finset.induction_on with
  | empty =>
    obtain ⟨phase, hphase⟩ := hactive _ le_rfl
    exact ⟨_, le_rfl, phase, hphase, Finset.empty_subset _⟩
  | @insert index indices hnot ih =>
    obtain ⟨tick, htick, phase, hphase, hindices⟩ :=
      ih (fun i hi ↦ harrival i (Finset.mem_insert_of_mem hi))
    obtain ⟨seen, hseen, record, hrecord, hi⟩ :=
      harrival index (Finset.mem_insert_self _ _)
    obtain ⟨live, hlive⟩ := hactive (max tick seen)
      (htick.trans (le_max_left _ _))
    refine ⟨max tick seen, htick.trans (le_max_left _ _), live, hlive, ?_⟩
    apply Finset.insert_subset_iff.mpr
    exact ⟨hpersist seen _ (le_max_right _ _) record live hrecord hlive hi,
      hindices.trans (hpersist tick _ (le_max_left _ _) phase live hphase hlive)⟩

/-- A noninitial simple query of the level tree is answered `true` by the final virtual answer of
the true marker candidate. All strict extension indices of the query's coordinate reach the stored
index set of the true marker phase, so its counter reaches the price and the query is funded. -/
lemma fighterFinalVirtualAnswer_eq_true_of_simple_of_not_initialAnswer (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      d ≤ q.2 → Simple P.B.V q.1 (q.2 - d) →
      (trueMarkerPhase P d l (markerTick P.B (levelScale l))).map
        (fun phase ↦ phase.initialAnswer P d q) ≠ some true →
      fighterFinalVirtualAnswer P d l (markerCandidate P.B (levelScale l)) q = true := by
  classical
  intro q hq hdq hsim hnotinit
  obtain ⟨_, game, _, hrecords, _⟩ :=
    (true_marker_opponent_stream_legal P C cGap cRank d₀ d l hfixed hgood hlate).2.2.1
  obtain ⟨phase, hphase, hgame, _, _⟩ := hrecords (markerTick P.B (levelScale l)) le_rfl
  have hqJ := mem_J_of_simple_of_not_initialAnswer
    P d l q phase hphase hq hdq hsim hnotinit
  have hprice := price_le_strictExtensionCount
    P C cGap cRank d₀ d l hfixed hgood hlate q phase hphase hqJ hsim
  let extensions := extensionSet P.B (levelScale l) 0
    (triple q.1 (q.2 - d) phase.candidate.1)
  have hfinite : extensions.Finite := extension_set_finite _ _ _ _
  have hactive : ∀ tick ≥ markerTick P.B (levelScale l),
      ∃ live, TrueMarkerPhaseAt P d l tick live := by
    intro tick htick
    obtain ⟨live, hlive, _⟩ := hrecords tick htick
    exact ⟨live, hlive⟩
  obtain ⟨tick, htick, live, hlive, hsubset⟩ :=
    exists_tick_subset_indicesAt P d l q hfinite.toFinset hactive
      (fun index hi ↦ exists_mem_indicesAt_of_mem_extensionSet
        P C cGap cRank d₀ d l hfixed hgood hlate q phase hphase hqJ index
          (hfinite.mem_toFinset.mp hi))
      (fun tick before after hb ha ↦ TrueMarkerPhaseAt.indicesAt_subset_succ
        P d l tick before after hb ha q)
  obtain ⟨record, hrecord, hrecordGame, _, _⟩ := hrecords tick htick
  have heq : record = live := Option.some.inj
    (hrecord.2.2.2.symm.trans hlive.2.2.2)
  subst record
  have hgames : live.game d = phase.game d := hrecordGame.trans hgame.symm
  have hqLive : q ∈ live.J d := by
    change q ∈ (live.game d).J
    rw [hgames]
    exact hqJ
  have hcard :=
    fighterState_counter_eq_card_indicesAt
      P d tick live (List.mem_of_find?_eq_some hlive.2.2.2) q hqLive
  have hfunded : (live.game d).price q ≤
      (live.game d).coordinateValue live.liveCounters q := by
    rw [hcard, hgames]
    apply hprice.trans
    change extensions.ncard ≤ (live.indicesAt d q).card
    rw [Set.ncard_eq_toFinset_card extensions hfinite]
    exact Finset.card_le_card hsubset
  apply (fighterFinalVirtualAnswer_eq_true_iff_exists_tick P d l q).mpr
  refine ⟨tick, htick, ?_⟩
  rw [fighterVirtualAnswerAt_eq_of_trueMarkerPhaseAt P d l tick live hlive]
  unfold FighterPhase.virtualAnswer normalizedAnswer
  rw [Bool.or_eq_true]
  right
  exact (counter_answer_eq_true _ _ _).mpr
    (Or.inr ⟨q, hqLive, rfl, le_rfl, hfunded⟩)

/-- Priority abortion preserves the graph and retains only old records at levels at most
the issuing level. The sublist assertion also preserves uniqueness of active levels. -/
lemma fighterAbortAbove_allocated_eq_active_sublist
    (d l : ℕ) (s : FighterState) :
    (fighterAbortAbove d l s).allocated = s.allocated ∧
      (fighterAbortAbove d l s).active.Sublist s.active ∧
      ∀ p ∈ (fighterAbortAbove d l s).active, p.level ≤ l := by
  have hcancel (j : ℕ) (t : FighterState) :
      (fighterCancel d j .aborted l t).allocated = t.allocated ∧
        (fighterCancel d j .aborted l t).active =
          t.active.filter (fun p ↦ p.level != j) := by
    unfold fighterCancel
    split
    · rename_i hnone
      refine ⟨rfl, ?_⟩
      symm
      apply List.filter_eq_self.mpr
      intro p hp
      have h := List.find?_eq_none.mp hnone p hp
      simpa using h
    · exact ⟨rfl, rfl⟩
  have hfold (xs : List FighterPhase) (t : FighterState) :
      let next := xs.foldl (fun u p ↦ if l < p.level then
        fighterCancel d p.level .aborted l u else u) t
      next.allocated = t.allocated ∧ next.active.Sublist t.active ∧
        ∀ p ∈ next.active, ∀ q ∈ xs, l < q.level → p.level ≠ q.level := by
    induction xs generalizing t with
    | nil => exact ⟨rfl, List.Sublist.refl _, by simp⟩
    | cons q xs ih =>
      dsimp only [List.foldl_cons]
      split
      · rename_i hq
        obtain ⟨ha, hs, hn⟩ := ih (fighterCancel d q.level .aborted l t)
        obtain ⟨hca, hcs⟩ := hcancel q.level t
        refine ⟨ha.trans hca, hs.trans (hcs ▸ List.filter_sublist), ?_⟩
        intro p hp r hr hrl
        rcases List.mem_cons.mp hr with rfl | hr
        · have hpm := hs.subset hp
          rw [hcs] at hpm
          simpa using (List.mem_filter.mp hpm).2
        · exact hn p hp r hr hrl
      · rename_i hq
        obtain ⟨ha, hs, hn⟩ := ih t
        refine ⟨ha, hs, ?_⟩
        intro p hp r hr hrl
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (hq hrl).elim
        · exact hn p hp r hr hrl
  obtain ⟨ha, hs, hn⟩ := hfold s.active s
  refine ⟨ha, hs, ?_⟩
  intro p hp
  by_contra h
  exact hn p hp p (hs.subset hp) (by omega) rfl

end Kolmogorov.Milovanov
