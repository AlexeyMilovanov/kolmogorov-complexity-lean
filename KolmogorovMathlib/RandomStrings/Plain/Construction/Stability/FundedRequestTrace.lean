/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestSaturation

/-!
# Traces of phases and their requests in the fighter run

The fighter construction keeps the phases of all levels in `FighterState.active` and archives
a phase in `FighterState.ended` when it is cancelled.  This module follows a phase, and
optionally one of its pending requests, along the run `fighterState`.  The *trace* of a phase
of level `l` with candidate `c` and of a request `q` is one of three locations: `q` is recorded
as globally fulfilled, a phase of the same level and candidate is still active (with `q`
still pending), or such a phase has been archived.  The central fact is that a trace persists
under every numerical tick, together with the invariant that the active levels are pairwise
distinct (`fighterState_active_levels_nodup`).

Consequences, used by the funded-request argument for the true marker (`FundedRequest`) and by
the phase separation and common-game invariants:

* `FighterState.activeAt_eq_some_of_mem`: lookup of the active phase of a level;
* `pending_mem_fulfilled_or_pending_of_le`: a pending request stays pending or becomes
  fulfilled while its phase survives;
* `fighterState_active_or_ended_of_le`: an active phase keeps an active or archived record;
* `fighterState_ended_reason_ne_saturated` (from `FundedRequestSaturation`) and
  `length_gt_of_eventAt_of_markerTick_lt`: no saturation record without allocation failure and
  no later event of a short program.
-/

namespace Kolmogorov.Milovanov

/-- The active phase with a given level, found by `FighterState.activeAt`, is any active phase
of that level, because the active levels are pairwise distinct. -/
theorem FighterState.activeAt_eq_some_of_mem
    (d l : ℕ) (s : FighterState) (p : FighterPhase)
    (hu : (s.active.map FighterPhase.level).Nodup) (hp : p ∈ s.active)
    (hl : p.level = l) : s.activeAt d l = some p := by
  cases hf : s.activeAt d l with
  | none =>
    have hn := List.find?_eq_none.mp hf p hp
    exact (hn (by simp [hl])).elim
  | some found =>
    have hfmem := List.mem_of_find?_eq_some hf
    have hfl : found.level = l :=
      beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hf)
    have heq := List.inj_on_of_nodup_map hu hfmem hp (hfl.trans hl.symm)
    rw [heq]

/-- The three possible locations of a phase of level `l` with candidate `c` and of its optional
request: successful global fulfillment of the request, an active phase of the same identity
(keeping the request pending), or the cancellation archive.  With no request, only the identity
of the phase is tracked. -/
private def PhaseTrace (l : ℕ) (c : Candidate) (request : Option Coordinate)
    (s : FighterState) : Prop :=
  (∃ q, request = some q ∧ q ∈ s.fulfilled) ∨
    (∃ p ∈ s.active, p.level = l ∧ p.candidate = c ∧
      ∀ q, request = some q → q ∈ p.pending) ∨
    ∃ e ∈ s.ended, e.1.level = l ∧ e.1.candidate = c

/-- The invariant carried along the run: the active levels are pairwise distinct, and (under the
assumption `need`) the trace of the tracked phase and request is present. -/
private abbrev TraceInv (l : ℕ) (c : Candidate) (request : Option Coordinate) (need : Prop)
    (s : FighterState) : Prop :=
  (s.active.map FighterPhase.level).Nodup ∧ (need → PhaseTrace l c request s)

/-- A request pending in a phase stays fulfilled or pending after the phase registers new
funding requests. -/
private theorem FighterPhase.mem_fulfilled_or_mem_pending_fundRequests
    (d : ℕ) (p : FighterPhase) (fulfilled : List Coordinate) {q : Coordinate}
    (hq : q ∈ p.pending) : q ∈ fulfilled ∨ q ∈ (p.fundRequests d fulfilled).pending := by
  by_cases hd : q ∈ fulfilled
  · exact Or.inl hd
  · right
    simp only [FighterPhase.fundRequests, List.mem_eraseDups, List.mem_filter,
      List.mem_append, decide_eq_true_eq]
    exact ⟨Or.inl hq, hd⟩

/-- After cancelling the phase of level `j`, no active phase has level `j`. -/
private theorem level_ne_of_mem_fighterCancel_active (d j cause : ℕ) (reason : PhaseEnd)
    (s : FighterState) : ∀ p ∈ (fighterCancel d j reason cause s).active, p.level ≠ j := by
  unfold fighterCancel
  split
  · rename_i hn
    intro p hp hlevel
    exact List.find?_eq_none.mp hn p hp (by simp [hlevel])
  · intro p hp
    simpa using (List.mem_filter.mp hp).2

namespace TraceInv

variable {l : ℕ} {c : Candidate} {request : Option Coordinate} {need : Prop}

/-- Putting a phase into the state preserves the invariant, if the phase it replaces has the same
candidate and its pending requests are retained or fulfilled. -/
private theorem put (d : ℕ) (p : FighterPhase) {s : FighterState}
    (hs : TraceInv l c request need s)
    (hov : ∀ old ∈ s.active, old.level = p.level → old.candidate = p.candidate ∧
      ∀ q ∈ old.pending, q ∈ s.fulfilled ∨ q ∈ p.pending) :
    TraceInv l c request need (s.putPhase d p) := by
  refine ⟨?_, fun hneed ↦ ?_⟩
  · simp only [FighterState.putPhase, List.map_cons, List.nodup_cons]
    refine ⟨?_, List.Nodup.sublist (List.filter_sublist.map _) hs.1⟩
    intro hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    have hne := (List.mem_filter.mp hold).2
    simp [heq] at hne
  · rcases hs.2 hneed with hpaid | hactive | hended
    · exact Or.inl hpaid
    · obtain ⟨old, hold, hlevel, hcand, hpend⟩ := hactive
      by_cases heq : old.level = p.level
      · obtain ⟨hc, hkeep⟩ := hov old hold heq
        by_cases hpaid : ∃ q, request = some q ∧ q ∈ s.fulfilled
        · exact Or.inl hpaid
        · right; left
          refine ⟨p, List.mem_cons_self, heq.symm.trans hlevel, hc.symm.trans hcand, ?_⟩
          intro q hq
          rcases hkeep q (hpend q hq) with hdone | hpending
          · exact (hpaid ⟨q, hq, hdone⟩).elim
          · exact hpending
      · right; left
        refine ⟨old, List.mem_cons_of_mem p (List.mem_filter.mpr ⟨hold, ?_⟩),
          hlevel, hcand, hpend⟩
        simpa using heq
    · exact Or.inr (Or.inr hended)

/-- Replacing the active phase `old` by a phase `p` of the same level and candidate preserves the
invariant, if the pending requests of `old` are retained or fulfilled. -/
private theorem update (d : ℕ) {s : FighterState} {j : ℕ} (old p : FighterPhase)
    (hs : TraceInv l c request need s) (hold : s.activeAt d j = some old)
    (hid : p.level = old.level ∧ p.candidate = old.candidate)
    (hkeep : ∀ q ∈ old.pending, q ∈ s.fulfilled ∨ q ∈ p.pending) :
    TraceInv l c request need (s.putPhase d p) := by
  apply put d p hs
  intro other ho hl
  have heq := List.inj_on_of_nodup_map hs.1 ho (List.mem_of_find?_eq_some hold)
    (hl.trans hid.1)
  subst other
  exact ⟨hid.2.symm, hkeep⟩

/-- Cancelling a phase preserves the invariant: the cancelled record moves to the archive. -/
private theorem cancel (d j cause : ℕ) (reason : PhaseEnd) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i phase hp
    refine ⟨List.Nodup.sublist (List.filter_sublist.map _) hs.1, fun hneed ↦ ?_⟩
    rcases hs.2 hneed with hpaid | hactive | hended
    · exact Or.inl hpaid
    · obtain ⟨old, hold, hlevel, hcand, hpend⟩ := hactive
      by_cases heq : old.level = j
      · have hpj : phase.level = j := beq_iff_eq.mp
          (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hp)
        have holdphase := List.inj_on_of_nodup_map hs.1 hold
          (List.mem_of_find?_eq_some hp) (heq.trans hpj.symm)
        subst old
        right; right
        exact ⟨({ phase with pending := [] }, s.tick, reason, cause),
          List.mem_append_right _ (List.mem_singleton.mpr rfl), hlevel, hcand⟩
      · right; left
        exact ⟨old, List.mem_filter.mpr ⟨hold, by simpa using heq⟩,
          hlevel, hcand, hpend⟩
    · obtain ⟨e, he, hl, hc⟩ := hended
      exact Or.inr (Or.inr ⟨e, List.mem_append_left _ he, hl, hc⟩)

/-- Aborting the larger levels preserves the invariant. -/
private theorem abortAbove (d j : ℕ) {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  refine foldl_preserves_invariant (TraceInv l c request need) _ _ (fun t p ht ↦ ?_) hs
  split
  · exact cancel d _ _ _ ht
  · exact ht

/-- A guarded allocation preserves the invariant. -/
private theorem allocate (d j : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterAllocate d j kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact cancel d j j .saturated (s := { s with failed := true }) hs
    | some input => exact abortAbove d j hs

/-- Recording a coordinate as globally fulfilled, and removing it from every pending list,
preserves the invariant. -/
private theorem record {s : FighterState} (q : Coordinate) (hs : TraceInv l c request need s) :
    TraceInv l c request need { s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨?_, fun hneed ↦ ?_⟩
  · simpa only [List.map_map, Function.comp_def] using hs.1
  · rcases hs.2 hneed with hpaid | hactive | hended
    · obtain ⟨r, hr, hd⟩ := hpaid
      exact Or.inl ⟨r, hr, List.mem_append_left _ hd⟩
    · obtain ⟨old, hold, hl, hc, hpend⟩ := hactive
      by_cases heq : request = some q
      · exact Or.inl ⟨q, heq, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
      · right; left
        refine ⟨{ old with pending := old.pending.filter (· != q) },
          List.mem_map.mpr ⟨old, hold, rfl⟩, hl, hc, ?_⟩
        intro r hr
        refine List.mem_filter.mpr ⟨hpend r hr, ?_⟩
        have hne : r ≠ q := fun h ↦ heq (h ▸ hr)
        simpa using hne
    · exact Or.inr (Or.inr hended)

/-- Paying a coordinate off preserves the invariant. -/
private theorem payoff (P : FighterParams) (d j : ℕ) (q : Coordinate) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate d j .payoff q.2 q.1 hs
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact record q ha
    · exact hs

/-- Fulfilling all ready requests of a level preserves the invariant. -/
private theorem fulfillReady (P : FighterParams) (d j : ℕ) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl_preserves_invariant (TraceInv l c request need) _ _
      (fun t q ht ↦ payoff P d j q ht) hs

/-- Spending one unit of the fuel budget on a coordinate preserves the invariant. -/
private theorem fuelUnit (P : FighterParams) (d j : ℕ) (q : Coordinate) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hlevel : phase.level = j := beq_iff_eq.mp
      (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hp)
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := update d phase charged hs hp ⟨rfl, rfl⟩ (fun _ h ↦ Or.inr h)
      have hcharged : (s.putPhase d charged).activeAt d j = some charged := by
        simp [FighterState.putPhase, FighterState.activeAt, charged, hlevel]
      have ha := allocate d j .fuel (levelUpper j + d) out hc
      change TraceInv l c request need
        (match fighterAllocate d j .fuel (levelUpper j + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d j
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · have hlive := activeAt_fighterAllocate_eq_of_success
            d j (levelUpper j + d) .fuel out (s.putPhase d charged) next charged hcharged he
          apply fulfillReady
          exact update d charged _ ha hlive ⟨rfl, rfl⟩
            (fun r hr ↦ FighterPhase.mem_fulfilled_or_mem_pending_fundRequests d _ _ hr)
    · exact hs

/-- Spending several units of the fuel budget on a coordinate preserves the invariant. -/
private theorem fuelUnits (P : FighterParams) (d j : ℕ) (q : Coordinate) (count : ℕ)
    {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (fuelUnit P d j q hs)

/-- The dummy allocation of a level preserves the invariant. -/
private theorem dummy (d j : ℕ) {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := allocate d j .dummy (levelInput d j) output hs
        cases he : fighterAllocate d j .dummy (levelInput d j) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hlive := activeAt_fighterAllocate_eq_of_success
              d j (levelInput d j) .dummy output s next phase hp he
            exact update d phase _ ha hlive ⟨rfl, rfl⟩ (fun _ h ↦ Or.inr h)

/-- Processing an opponent program event at a level preserves the invariant. -/
private theorem opponent (P : FighterParams) (d j : ℕ) (e : ProgramEvent) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterOpponent P d j e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    split
    · exact hs
    · rename_i q index ht
      split
      · exact hs
      · split
        · exact cancel d _ _ _ hs
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          apply fulfillReady
          exact update d phase (next.fundRequests d s.fulfilled) hs hp ⟨rfl, rfl⟩
            (fun r hr ↦ FighterPhase.mem_fulfilled_or_mem_pending_fundRequests d next _ hr)

/-- Starting a phase for a candidate at a level preserves the invariant. -/
private theorem startPhase (P : FighterParams) (d j : ℕ) (cand : Candidate)
    {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterStartPhase P d j cand s) := by
  unfold fighterStartPhase
  apply put d _ (abortAbove d j (cancel d j j .replaced hs))
  intro old ho hl
  exact (level_ne_of_mem_fighterCancel_active d j j .replaced s old
    (fighterAbortAbove_active_subset d j _ ho) hl).elim

/-- Flushing the buffer of a level preserves the invariant. -/
private theorem flushBuffer (d j : ℕ) {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need ((fighterFlushBuffer d j s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d j with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact update d phase _ hs hp ⟨rfl, rfl⟩ (fun _ h ↦ Or.inr h)
    · exact hs

/-- A strategy move at a level preserves the invariant. -/
private theorem strategyMove (P : FighterParams) (d j : ℕ) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need ((fighterStrategyMove P d j s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d j with
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
            fighterFuelUnits P d j q (move[i]?.getD 0) s) s
          have hn : TraceInv l c request need next :=
            foldl_preserves_invariant (TraceInv l c request need) _ _
              (fun t qi ht ↦ fuelUnits P d j qi.1 (move[qi.2]?.getD 0) ht) hs
          change TraceInv l c request need ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            exact update d live _ hn hlive ⟨rfl, rfl⟩ (fun _ h ↦ Or.inr h)
        · exact hs
    · exact hs

/-- The single action of a level preserves the invariant. -/
private theorem levelAction (P : FighterParams) (d j : ℕ) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need ((fighterLevelAction P d j s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d j with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy d j hs
    · split
      · exact payoff P d j _ hs
      · cases hf : fighterFlushBuffer d j s with
        | none => exact strategyMove P d j hs
        | some next =>
          have h := flushBuffer d j hs
          simpa only [hf, Option.getD_some] using h

/-- Closing a level, i.e. iterating its action with bounded fuel, preserves the invariant. -/
private theorem closure (P : FighterParams) (d j fuel : ℕ) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact hs
    | some next =>
      have hn := levelAction P d j hs
      simp only [ha, Option.getD_some] at hn
      exact ih hn

/-- Processing one level for one (optional) event preserves the invariant. -/
private theorem processLevel (P : FighterParams) (d j : ℕ) (e : Option TimedEvent)
    {s : FighterState} (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighterProcessLevel P d j e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply closure
  cases e with
  | none => exact fulfillReady P d j hs
  | some e =>
    dsimp only
    split
    · exact startPhase P d j _ (fulfillReady P d j hs)
    · exact opponent P d j _ (fulfillReady P d j hs)

end TraceInv

/-- Each atomic action and finite event fold of a tick preserves unique active levels and the
request trace.  A request disappears from a live record only when it is fulfilled or its phase
is archived. -/
private theorem TraceInv.actions (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d)
    (l : ℕ) (c : Candidate) (request : Option Coordinate) (need : Prop) {s : FighterState}
    (hs : TraceInv l c request need s) :
    TraceInv l c request need (fighter_actions P d tick s) := by
  unfold fighter_actions
  split
  · omega
  · exact foldl_preserves_invariant (TraceInv l c request need) _ _
      (fun t j ht ↦ TraceInv.processLevel P d j _ ht)
      (s := { s with tick := tick, schedule := masterState P.B tick }) hs

/-- Every reachable state of the fighter run has at most one active phase at each level. -/
theorem fighterState_active_levels_nodup
    (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d) :
    ((fighterState P d tick).active.map FighterPhase.level).Nodup := by
  induction tick with
  | zero => simp [fighterState, initialFighterState]
  | succ tick ih =>
    exact (TraceInv.actions P d (tick + 1) hd 0 ([], 0) none False
      (s := fighterState P d tick) ⟨ih, False.elim⟩).1

/-- The trace of a phase and request persists between completed numerical ticks. -/
private theorem phaseTrace_of_le
    (P : FighterParams) (d l tick later : ℕ) (c : Candidate) (request : Option Coordinate)
    (hd : 1 ≤ d) (hle : tick ≤ later)
    (htrace : PhaseTrace l c request (fighterState P d tick)) :
    PhaseTrace l c request (fighterState P d later) := by
  induction later, hle using Nat.le_induction with
  | base => exact htrace
  | succ later hle ih =>
    exact (TraceInv.actions P d (later + 1) hd l c request True
      (s := fighterState P d later) ⟨fighterState_active_levels_nodup P d later hd,
        fun _ ↦ ih⟩).2 trivial

/-- A request already pending in a phase is retained or fulfilled later: either it has been
globally fulfilled, or a surviving phase of the same identity still has it pending.  The absence
of the phase from the cancellation archive rules out the third trace location. -/
theorem pending_mem_fulfilled_or_pending_of_le
    (P : FighterParams) (d l tick later : ℕ) (hd : 1 ≤ d) (hle : tick ≤ later)
    (hsurvives : TrueMarkerPhaseSurvives P d l later)
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase)
    (q : Coordinate) (hpend : q ∈ phase.pending) :
    q ∈ (fighterState P d later).fulfilled ∨
      ∃ next, TrueMarkerPhaseAt P d l later next ∧ q ∈ next.pending := by
  have hstart : PhaseTrace l (markerCandidate P.B (levelScale l)) (some q)
      (fighterState P d tick) := by
    right; left
    refine ⟨phase, List.mem_of_find?_eq_some hphase.2.2.2, hphase.2.1, hphase.2.2.1, ?_⟩
    intro r hr
    exact (Option.some.inj hr) ▸ hpend
  have htrace := phaseTrace_of_le P d l tick later _ (some q) hd hle hstart
  rcases htrace with ⟨r, hr, hpaid⟩ | ⟨next, hn, hl, hc, hreq⟩ | ⟨e, he, hl, hc⟩
  · have heq := Option.some.inj hr
    exact Or.inl (heq ▸ hpaid)
  · right
    refine ⟨next, ⟨hsurvives.2.1, hl, hc, ?_⟩, hreq q rfl⟩
    exact FighterState.activeAt_eq_some_of_mem d l _ next
      (fighterState_active_levels_nodup P d later hd) hn hl
  · exact (hsurvives.2.2.2 e he hl hc).elim

/-- An active phase at an earlier tick has, at every later tick, either an active record of the
same level and candidate or a record of that identity in the cancellation archive. -/
theorem fighterState_active_or_ended_of_le
    (P : FighterParams) (d tick later : ℕ) (hd : 1 ≤ d) (hle : tick ≤ later)
    (phase : FighterPhase) (hphase : phase ∈ (fighterState P d tick).active) :
    (∃ next ∈ (fighterState P d later).active,
      next.level = phase.level ∧ next.candidate = phase.candidate) ∨
    ∃ e ∈ (fighterState P d later).ended,
      e.1.level = phase.level ∧ e.1.candidate = phase.candidate := by
  have hstart : PhaseTrace phase.level phase.candidate none (fighterState P d tick) := by
    right; left
    exact ⟨phase, hphase, rfl, rfl, fun _ h ↦ by cases h⟩
  have htrace := phaseTrace_of_le P d phase.level tick later phase.candidate none hd hle hstart
  rcases htrace with ⟨q, hq, hp⟩ | ⟨next, hn, hl, hc, hreq⟩ | he
  · cases hq
  · exact Or.inl ⟨next, hn, hl, hc⟩
  · exact Or.inr he

/-- Every program of length at most the marker scale has emitted by the marker tick, so every
event after `markerTick B n` belongs to a program longer than `n`.  This uses the maximum
defining `markerTick`, with no extra asymptotic threshold. -/
theorem length_gt_of_eventAt_of_markerTick_lt
    (B : Base) (n : ℕ) :
    ∀ t > markerTick B n, ∀ i p x,
      eventAt B t = some (t, i, p, x) → n < p.length := by
  intro t ht i p x hevent
  by_contra hlen
  have hp : p ∈ (boundedPrograms n).toFinset := by
    simp only [List.mem_toFinset, mem_boundedPrograms_iff]
    omega
  have htick : programTick B p = t := by
    unfold programTick
    have heq : {s | ∃ j y, eventAt B s = some (s, j, p, y)} = {t} := by
      ext s
      constructor
      · rintro ⟨j, y, hs⟩
        exact (canonical_enumeration_spec_unique B hs hevent).1
      · intro hs
        have hs' : s = t := Set.mem_singleton_iff.mp hs
        subst s
        exact ⟨i, x, hevent⟩
    rw [heq]
    exact csInf_singleton t
  have hb : programTick B p ≤ markerTick B n := Finset.le_sup hp
  omega

end Kolmogorov.Milovanov
