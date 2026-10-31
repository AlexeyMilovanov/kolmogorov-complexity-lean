/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.State

/-!
# Guarded allocations, buffered play, and finite event closure

Every allocation first finds an unused input. Fuel inserts an index only after
success; payoff success alone changes the global fulfilled table. Cancellation
archives the phase and erases its requests without deleting permanent descriptions.
Each event is handled in increasing level order. A level tests its old requests
before replacing its phase, then completes all its actions before the next level.
These operations implement blueprint node `constr:actions`.

The closure theorem `fighter_closure_fixpoint` bounds the number of enabled actions
by the remaining game budgets, unfulfilled payoff coordinates, and optional dummy.
It supplies the finite termination argument for blueprint node `constr:effective`.
The effective state machine uses these transitions to construct the directive stream;
the stability proofs use them to track surviving phases and their allocations.
-/

namespace Kolmogorov.Milovanov

/-- Cancel a level, retaining its last positions and discarding its pending requests.
Blueprint node `constr:actions` (supporting definition). -/
def fighterCancel (d l : ℕ) (reason : PhaseEnd) (cause : ℕ)
    (state : FighterState) : FighterState :=
  match state.activeAt d l with
  | none => state
  | some phase =>
    { state with
      active := state.active.filter (fun p ↦ p.level != l)
      ended := state.ended ++ [({ phase with pending := [] }, state.tick, reason, cause)] }

/-- Abort all active larger levels; abortion never restarts an old candidate.
Blueprint node `constr:actions` (supporting definition). -/
def fighterAbortAbove (d l : ℕ) (state : FighterState) : FighterState :=
  state.active.foldl (fun s phase ↦
    if l < phase.level then fighterCancel d phase.level .aborted l s else s) state

/-- All binary strings of a fixed length in lexicographic order, with false first.
Blueprint node `constr:actions` (supporting definition). -/
def fighterInputs (_d : ℕ) : ℕ → List BitString
  | 0 => [[]]
  | length + 1 =>
    (fighterInputs _d length).map (false :: ·) ++ (fighterInputs _d length).map (true :: ·)


/-- Every string in the input pool `fighterInputs d n` has length `n`. -/
theorem length_eq_of_mem_fighterInputs (d n : ℕ) (p : BitString)
    (hp : p ∈ fighterInputs d n) : p.length = n := by
  induction n generalizing p with
  | zero => have he : p = [] := List.mem_singleton.mp hp; simp [he]
  | succ n ih =>
    simp only [fighterInputs, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;> simp [ih q hq]

/-- Guarded assignment of the next unused input; success immediately injures larger levels.
Blueprint node `constr:actions` (supporting definition). Failure records saturation,
cancels the issuing phase, and leaves the permanent graph unchanged. -/
def fighterAllocate (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString)
    (state : FighterState) : FighterState × Bool :=
  match state.activeAt d l with
  | none => (state, false)
  | some phase =>
    let fresh := if target = 0 then none else
      (fighterInputs d (target - 1)).find? (fun p ↦
        !state.allocated.any (fun a ↦ a.input == p))
    match fresh with
    | none =>
      (fighterCancel d l .saturated l { state with failed := true }, false)
    | some p =>
      let entry := AllocatedDirective.mk l phase.candidate state.tick kind target p output
      (fighterAbortAbove d l { state with allocated := state.allocated ++ [entry] }, true)

/-- Test the entire emitted finite `V` table, with the odd-padding floor convention.
Blueprint node `constr:actions` (supporting definition). The lower guard makes the
test equivalent to an observed witness of `C_V(x) + h(d) ≤ r` even on malformed requests. -/
def fighterSafe (P : FighterParams) (d tick : ℕ) (q : Coordinate) : Bool :=
  decide (halfPadding d ≤ q.2 ∧ q.1 ∈ stageOutputs P.B (q.2 - halfPadding d) tick)

/-- Fulfill one currently pending safe request, recording the pair only on success.
Blueprint node `constr:actions` (supporting definition). Removing the pair from every
remaining pending list makes the global successful-allocation convention explicit. -/
def fighterPayoff (P : FighterParams) (d l : ℕ) (q : Coordinate)
    (state : FighterState) : FighterState :=
  match state.activeAt d l with
  | none => state
  | some phase =>
    if q ∈ phase.pending ∧ q ∉ state.fulfilled ∧ fighterSafe P d state.tick q = true then
      let (next, success) := fighterAllocate d l .payoff q.2 q.1 state
      if success then
        { next with
          fulfilled := next.fulfilled ++ [q]
          active := next.active.map (fun p ↦
            { p with pending := p.pending.filter (fun r ↦ r != q) }) }
      else next
    else state

/-- Check every current request of a level against the accumulated table immediately.
Blueprint node `constr:actions` (supporting definition). The fold is finite even if
allocation cancels the phase; later iterations then have nothing to service. -/
def fighterFulfillReady (P : FighterParams) (d l : ℕ) (state : FighterState) : FighterState :=
  match state.activeAt d l with
  | none => state
  | some phase => phase.pending.foldl (fun s q ↦ fighterPayoff P d l q s) state

/-- The coordinate unit vector in the game's deduplicated order.
Blueprint node `constr:actions` (supporting definition). -/
def FighterPhase.unitVector (phase : FighterPhase) (d : ℕ) (q : Coordinate) : CounterMove :=
  (phase.game d).coordinates.map (fun r ↦ if r = q then 1 else 0)

/-- Insert one backed fresh index and increase its live counter by one.
Blueprint node `constr:actions` (supporting definition). Callers establish freshness
and backing before using this helper; it performs no allocation by itself. -/
def FighterPhase.insertIndex (phase : FighterPhase) (d : ℕ) (q : Coordinate)
    (index : BitString) : FighterPhase :=
  let game := phase.game d
  let indices := game.coordinates.zipIdx |>.map (fun (r, i) ↦
    let old := phase.indices[i]?.getD []
    if r = q then (old ++ [index]).eraseDups else old)
  { phase with
    indices := indices
    liveCounters := game.addCounters phase.liveCounters (phase.unitVector d q) }

/-- Spend one controlled unit and allocate its fuel before inserting the fresh index.
Blueprint node `constr:actions` (supporting definition). After a successful insertion
all newly funded requests are tested immediately, without delaying further fuel. -/
def fighterFuelUnit (P : FighterParams) (d l : ℕ) (q : Coordinate)
    (state : FighterState) : FighterState :=
  match state.activeAt d l with
  | none => state
  | some phase =>
    if q ∈ (phase.game d).coordinates ∧ 0 < phase.controlledRemaining then
      let old := phase.indices[(phase.game d).coordinates.idxOf q]?.getD []
      let index := fighterFreshString d old
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let (next, success) := fighterAllocate d l .fuel (levelUpper l + d) output
        (state.putPhase d charged)
      if success then
        let inserted := (charged.insertIndex d q index).fundRequests d next.fulfilled
        fighterFulfillReady P d l (next.putPhase d inserted)
      else next
    else state

/-- Execute a bounded number of designated fuel units by structural recursion.
Blueprint node `constr:actions` (supporting definition). Cancellation makes all
remaining units inert, so a failed request is never retried. -/
def fighterFuelUnits (P : FighterParams) (d l : ℕ) (q : Coordinate) :
    ℕ → FighterState → FighterState
  | 0, state => state
  | count + 1, state => fighterFuelUnits P d l q count (fighterFuelUnit P d l q state)

/-- Detect a retained curried tuple from any emitted event, regardless of its owner.
Blueprint node `constr:actions` (supporting definition). Reconstruction checks all
encoding boundaries, and the program-length test is at the active phase's upper scale. -/
def fighterOpponentTuple (d : ℕ) (phase : FighterPhase) (event : ProgramEvent) :
    Option (Coordinate × BitString) := do
  if levelUpper phase.level < event.1.length then none else do
    let (x, q, w) ← decodeTriple (decodeFirst event.2)
    let index := decodeSecond event.2
    let coordinate := (x, q + d)
    if w = phase.candidate.1 ∧ coordinate ∈ (phase.game d).coordinates ∧
        pairCode (triple x q w) index = event.2 then
      some (coordinate, index)
    else none

/-- Insert and charge a genuinely new opponent tuple, buffering its official move.
Blueprint node `constr:actions` (supporting definition). Duplicate descriptions and
indices already purchased by the constructor cost nothing. An unaffordable insertion cancels. -/
def fighterOpponent (P : FighterParams) (d l : ℕ) (event : ProgramEvent)
    (state : FighterState) : FighterState :=
  match state.activeAt d l with
  | none => state
  | some phase =>
    match fighterOpponentTuple d phase event with
    | none => state
    | some (q, index) =>
      if index ∈ phase.indicesAt d q then state
      else if phase.opponentRemaining = 0 then
        fighterCancel d l .opponentExhausted l state
      else
        let inserted := phase.insertIndex d q index
        let next := { inserted with
          opponentRemaining := phase.opponentRemaining - 1
          buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
        fighterFulfillReady P d l
          (state.putPhase d (next.fundRequests d state.fulfilled))

/-- Allocate the optional dummy once, preserving the original virtual target and answers.
Blueprint node `constr:actions` (supporting definition). Its output was chosen outside
the whole referee tree and the initial small-output table. -/
def fighterDummy (d l : ℕ) (state : FighterState) : FighterState :=
  match state.activeAt d l with
  | none => state
  | some phase =>
    match phase.dummy with
    | none => state
    | some output =>
      if phase.dummyIssued then state else
        let (next, success) := fighterAllocate d l .dummy (levelInput d l) output state
        if success then next.putPhase d { phase with dummyIssued := true } else next

/-- Flush a predicate-changing buffer as one official opponent move, charging it once.
Blueprint node `constr:actions` (supporting definition). Intermediate output changes
that preserve the controlled predicate leave the official strategy position unchanged. -/
def fighterFlushBuffer (d l : ℕ) (state : FighterState) : Option FighterState := do
  let phase ← state.activeAt d l
  let game := phase.game d
  let official := phase.official d
  if phase.predicateHolds d = false ∧
      game.activePlayer official ≠ phase.controlledPlayer ∧
      game.LegalMove official phase.buffer then
    some (state.putPhase d { phase with
      officialCode := (game.afterMove official phase.buffer).encode
      buffer := List.replicate game.coordinates.length 0 })
  else none

/-- Execute an entire selected legal controlled move, with immediate per-unit allocation.
Blueprint node `constr:actions` (supporting definition). The official child is installed
only if the phase survives every fuel and payoff allocation of this response. -/
def fighterStrategyMove (P : FighterParams) (d l : ℕ) (state : FighterState) :
    Option FighterState := do
  let phase ← state.activeAt d l
  let game := phase.game d
  let official := phase.official d
  if phase.predicateHolds d = false ∧ phase.buffer.sum = 0 ∧
      game.activePlayer official = phase.controlledPlayer then
    let move ← game.strategy official
    if game.LegalMove official move ∧ move.sum ≤ phase.controlledRemaining then
      let next := game.coordinates.zipIdx |>.foldl (fun s (q, i) ↦
        fighterFuelUnits P d l q (move[i]?.getD 0) s) state
      match next.activeAt d l with
      | none => some next
      | some live => some (next.putPhase d { live with
          officialCode := (game.afterMove official move).encode })
    else none
  else none

/-- One enabled action at a level: dummy, safe payoff, buffer flush, or controlled response.
Blueprint node `constr:actions` (supporting definition). Unsafe pending requests do
not block the strategy; terminal play retains them for later emitted witnesses. -/
def fighterLevelAction (P : FighterParams) (d l : ℕ) (state : FighterState) :
    Option FighterState := do
  let phase ← state.activeAt d l
  if phase.dummy.isSome && !phase.dummyIssued then some (fighterDummy d l state) else
    match phase.pending.find? (fun q ↦
        decide (q ∉ state.fulfilled) && fighterSafe P d state.tick q) with
    | some q => some (fighterPayoff P d l q state)
    | none =>
      match fighterFlushBuffer d l state with
      | some next => some next
      | none => fighterStrategyMove P d l state

/-- Structural closure under enabled actions, using an explicit natural fuel argument.
Blueprint node `constr:actions` (supporting definition). -/
def fighterClosure (P : FighterParams) (d l : ℕ) : ℕ → FighterState → FighterState
  | 0, state => state
  | fuel + 1, state =>
    match fighterLevelAction P d l state with
    | none => state
    | some next => fighterClosure P d l fuel next

/-- A finite action bound from the two game budgets, coordinates, and pending requests.
Blueprint node `constr:actions` (supporting definition). The closure theorem below
is the proof obligation that this explicit bound suffices. -/
def fighterClosureFuel (d l : ℕ) (state : FighterState) : ℕ :=
  match state.activeAt d l with
  | none => 0
  | some phase =>
    2 * (phase.game d).budget + (phase.game d).coordinates.length + phase.pending.length + 5

/-- Complete a level's finite enabled work at the present master tick.
Blueprint node `constr:actions` (supporting definition). -/
def fighterCloseLevel (P : FighterParams) (d l : ℕ) (state : FighterState) : FighterState :=
  fighterClosure P d l (fighterClosureFuel d l state) state

/-- Start exactly one phase for a newly emitted candidate and injure larger active levels.
Blueprint node `constr:actions` (supporting definition). No other operation starts phases. -/
def fighterStartPhase (P : FighterParams) (d l : ℕ) (candidate : Candidate)
    (state : FighterState) : FighterState :=
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l state)
  let phase := fighter_construction P d l candidate waiting
  let next := waiting.putPhase d phase
  { next with started := next.started ++ [(l, candidate)] }

/-- Process the event and all resulting work at one level before visiting a larger level.
Blueprint node `constr:actions` (supporting definition). Old safe requests are checked
before same-level replacement; the new snapshot includes their successful allocations. -/
def fighterProcessLevel (P : FighterParams) (d l : ℕ) (event : Option TimedEvent)
    (state : FighterState) : FighterState :=
  let checked := fighterFulfillReady P d l state
  let next := match event with
    | none => checked
    | some e =>
      if fighterOwner d e.2.2.1.length = some l ∧ e.2.2.1.length ≤ levelScale l ∧
          P.Admissible d l then
        fighterStartPhase P d l (e.2.2.1, e.1) checked
      else fighterOpponent P d l e.2.2 checked
  fighterCloseLevel P d l next

/-- The total deterministic event transition along the frozen numerical master schedule.
Blueprint node `constr:actions`. Every event, including ownerless events and repeated
outputs, updates the common tables and services active levels in increasing order.
Zero padding has no phases or directives; the positive family uses the guarded allocator. -/
def fighter_actions (P : FighterParams) (d tick : ℕ) (state : FighterState) : FighterState :=
  let current := { state with tick := tick, schedule := masterState P.B tick }
  if d = 0 then { initialFighterState d with tick := tick, schedule := current.schedule } else
    let event := eventAt P.B tick
    let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
    let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
    (levels.mergeSort (· ≤ ·)).foldl
      (fun s l ↦ fighterProcessLevel P d l event s) current

/-- Coordinates which can still consume a payoff action, including coordinates not funded yet. -/
private def payoffReserve (d : ℕ) (fulfilled : List Coordinate)
    (phase : FighterPhase) : Finset Coordinate :=
  (phase.pending.toFinset ∪ (phase.game d).coordinates.toFinset) \ fulfilled.toFinset

/-- The remaining single dummy action. -/
private def dummyWeight (phase : FighterPhase) : ℕ :=
  if phase.dummy.isSome && !phase.dummyIssued then 1 else 0

/-- Budget, future payoff, and dummy reserves, plus one unit for a surviving phase. -/
private def actionWeight (d l : ℕ) (state : FighterState) : ℕ :=
  match state.activeAt d l with
  | none => 0
  | some phase => (phase.official d).budgetSum +
      (payoffReserve d state.fulfilled phase).card +
      dummyWeight phase + 1

/-- An internal subroutine preserves official play and can only remove payoff reserves. -/
private def actionStable (d l : ℕ) (s t : FighterState) : Prop :=
  ∀ p, t.activeAt d l = some p → ∃ q, s.activeAt d l = some q ∧
    p.gameCode = q.gameCode ∧ p.officialCode = q.officialCode ∧
    p.dummy = q.dummy ∧ p.dummyIssued = q.dummyIssued ∧
    payoffReserve d t.fulfilled p ⊆
      payoffReserve d s.fulfilled q

/-- Cancelling a level leaves it without an active phase. -/
theorem activeAt_fighterCancel (d l : ℕ) (s : FighterState)
    (reason : PhaseEnd) (cause : ℕ) :
    (fighterCancel d l reason cause s).activeAt d l = none := by
  unfold fighterCancel
  split
  · assumption
  · simp [FighterState.activeAt, List.find?_filter]

/-- Cancelling the phase of level `k` does not change the lookup at any other level `l`. -/
theorem activeAt_fighterCancel_eq_of_ne (d k l : ℕ) (reason : PhaseEnd) (cause : ℕ)
    (s : FighterState) (hne : k ≠ l) :
    (fighterCancel d k reason cause s).activeAt d l = s.activeAt d l := by
  unfold fighterCancel
  split
  · rfl
  · exact FighterState.find?_level_filter_ne _ _ _ hne.symm

/-- Aborting the levels above `l` does not change the active phase of a level `j ≤ l`. -/
theorem activeAt_fighterAbortAbove_of_le (d l j : ℕ) (s : FighterState) (hj : j ≤ l) :
    (fighterAbortAbove d l s).activeAt d j = s.activeAt d j := by
  unfold fighterAbortAbove
  have hfold : ∀ (xs : List FighterPhase) (t : FighterState),
      (xs.foldl (fun u p ↦ if l < p.level then
        fighterCancel d p.level .aborted l u else u) t).activeAt d j = t.activeAt d j := by
    intro xs
    induction xs with
    | nil => intro t; rfl
    | cons p xs ih =>
      intro t
      simp only [List.foldl_cons, ih]
      split
      · exact activeAt_fighterCancel_eq_of_ne _ _ _ _ _ _ (by omega)
      · rfl
  exact hfold _ _

/-- Priority cancellation preserves the issuing level. -/
theorem activeAt_fighterAbortAbove (d l : ℕ) (s : FighterState) :
    (fighterAbortAbove d l s).activeAt d l = s.activeAt d l :=
  activeAt_fighterAbortAbove_of_le d l l s le_rfl

/-- A successful allocation preserves the phase record of the issuing level; only strictly
larger levels are aborted. -/
theorem activeAt_fighterAllocate_eq_of_success
    (d l target : ℕ) (kind : DirectiveKind) (output : BitString)
    (s next : FighterState) (p : FighterPhase)
    (hp : s.activeAt d l = some p)
    (hsuccess : fighterAllocate d l kind target output s = (next, true)) :
    next.activeAt d l = some p := by
  simp only [fighterAllocate, hp] at hsuccess
  split at hsuccess
  · simp only [Prod.mk.injEq, Bool.false_eq_true, and_false] at hsuccess
  · simp only [Prod.mk.injEq, and_true] at hsuccess
    rw [← hsuccess, activeAt_fighterAbortAbove]
    exact hp

/-- Cancelling a phase only removes active records. -/
theorem fighterCancel_active_subset (d j cause : ℕ) (reason : PhaseEnd)
    (s : FighterState) : (fighterCancel d j reason cause s).active ⊆ s.active := by
  unfold fighterCancel
  split
  · exact fun _ h ↦ h
  · exact fun _ h ↦ (List.mem_filter.mp h).1

/-- Aborting the larger levels only removes active records. -/
theorem fighterAbortAbove_active_subset (d j : ℕ) (s : FighterState) :
    (fighterAbortAbove d j s).active ⊆ s.active := by
  have hf (ps : List FighterPhase) (s : FighterState) :
      (ps.foldl (fun s p ↦ if j < p.level then
        fighterCancel d p.level .aborted j s else s) s).active ⊆ s.active := by
    induction ps generalizing s with
    | nil => exact fun _ h ↦ h
    | cons p ps ih =>
      intro old ho
      have hm := ih _ ho
      dsimp only at hm
      split at hm
      · exact fighterCancel_active_subset d _ _ _ _ hm
      · exact hm
  exact hf _ _

/-- Aborting higher levels does not alter the list of phase starts. -/
theorem fighterAbortAbove_started (d l : ℕ) (s : FighterState) :
    (fighterAbortAbove d l s).started = s.started := by
  have h_fold : ∀ (active : List FighterPhase) (st : FighterState),
      (active.foldl (fun st phase ↦ if l < phase.level then
        fighterCancel d phase.level .aborted l st else st) st).started = st.started := by
    intro active
    induction active with
    | nil => intro st; rfl
    | cons p ps ih =>
      intro st
      rw [List.foldl_cons, ih]
      split
      · dsimp [fighterCancel]
        cases st.activeAt d p.level <;> rfl
      · rfl
  exact h_fold s.active s

/-- Allocation preserves the issuing phase on success and cancels it on failure, without changing
fulfilled pairs. -/
private lemma fulfilled_and_activeAt_fighterAllocate (d l : ℕ) (s : FighterState)
    (kind : DirectiveKind) (target : ℕ) (output : BitString) :
    (fighterAllocate d l kind target output s).1.fulfilled = s.fulfilled ∧
    (fighterAllocate d l kind target output s).1.activeAt d l =
      if (fighterAllocate d l kind target output s).2 then s.activeAt d l else none := by
  have hcancel (t : FighterState) : (fighterCancel d l .saturated l t).fulfilled = t.fulfilled := by
    unfold fighterCancel
    split <;> rfl
  have habort (t : FighterState) : (fighterAbortAbove d l t).fulfilled = t.fulfilled := by
    have hfold (ps : List FighterPhase) (t : FighterState) :
        (ps.foldl (fun t p ↦ if l < p.level then
          fighterCancel d p.level .aborted l t else t) t).fulfilled = t.fulfilled := by
      induction ps generalizing t with
      | nil => rfl
      | cons p ps ih =>
        rw [List.foldl_cons, ih]
        split
        · unfold fighterCancel
          split <;> rfl
        · rfl
    exact hfold _ _
  unfold fighterAllocate
  split
  · rename_i h
    exact ⟨rfl, h⟩
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      dsimp only
      exact ⟨hcancel _, activeAt_fighterCancel d l _ _ _⟩
    | some p =>
      dsimp only
      exact ⟨habort _, activeAt_fighterAbortAbove d l _⟩

/-- Internal preservation composes. -/
private lemma actionStable_trans (d l : ℕ) {s t u : FighterState}
    (hst : actionStable d l s t)
    (htu : actionStable d l t u) :
    actionStable d l s u := by
  intro p hp
  obtain ⟨q, hq, hg, ho, hd, hi, hr⟩ := htu p hp
  obtain ⟨r, hr', hg', ho', hd', hi', hr''⟩ := hst q hq
  exact ⟨r, hr', hg.trans hg', ho.trans ho', hd.trans hd', hi.trans hi', hr.trans hr''⟩

/-- Unchanged local resources give internal preservation. -/
private lemma actionStable_refl (d l : ℕ) (s : FighterState) :
    actionStable d l s s := by
  intro p hp
  exact ⟨p, hp, rfl, rfl, rfl, rfl, Finset.Subset.refl _⟩

/-- Funding requests does not add to the reserve, since all retained coordinates were reserved in
advance. -/
private lemma payoffReserve_fundRequests (d : ℕ) (p : FighterPhase)
    (fulfilled : List Coordinate) :
    payoffReserve d fulfilled (p.fundRequests d fulfilled) =
      payoffReserve d fulfilled p := by
  ext q
  simp only [payoffReserve, Finset.mem_sdiff, Finset.mem_union,
    List.mem_toFinset, FighterPhase.fundRequests, FighterPhase.game, List.mem_eraseDups,
    List.mem_filter, List.mem_append, decide_eq_true_eq]
  aesop

/-- Filtering a paid request and recording it removes exactly that coordinate from the reserve. -/
private lemma payoffReserve_record_payoff (d : ℕ) (p : FighterPhase)
    (fulfilled : List Coordinate) (q : Coordinate) :
    payoffReserve d (fulfilled ++ [q])
      { p with pending := p.pending.filter (· != q) } =
    (payoffReserve d fulfilled p).erase q := by
  ext r
  simp only [payoffReserve, FighterPhase.game, Finset.mem_sdiff, Finset.mem_union,
    List.mem_toFinset, List.mem_filter, bne_iff_ne, List.mem_append, List.mem_singleton,
    Finset.mem_erase]
  aesop

/-- Allocation preserves official play, dummy status, and the payoff reserve. -/
private lemma actionStable_fighterAllocate (d l : ℕ) (s : FighterState)
    (kind : DirectiveKind) (target : ℕ) (output : BitString) :
    actionStable d l s (fighterAllocate d l kind target output s).1 := by
  intro p hp
  have ha := fulfilled_and_activeAt_fighterAllocate d l s kind target output
  cases hb : (fighterAllocate d l kind target output s).2
  · simp only [hb, Bool.false_eq_true, ite_false] at ha
    rw [ha.2] at hp
    contradiction
  · simp only [hb, ite_true] at ha
    exact ⟨p, ha.2 ▸ hp, rfl, rfl, rfl, rfl, by rw [ha.1]⟩

/-- Recording a successful payoff preserves official play and removes its payoff reserve. -/
private lemma actionStable_record_payoff (d l : ℕ) (s : FighterState)
    (q : Coordinate) :
    actionStable d l s
      { s with fulfilled := s.fulfilled ++ [q]
               active := s.active.map (fun p ↦
                 { p with pending := p.pending.filter (· != q) }) } := by
  intro p hp
  simp only [FighterState.activeAt, List.find?_map] at hp
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hp
  refine ⟨r, hr, rfl, rfl, rfl, rfl, ?_⟩
  rw [payoffReserve_record_payoff]
  exact Finset.erase_subset _ _

/-- Servicing one payoff cannot increase internal resources. -/
private lemma actionStable_fighterPayoff (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) :
    actionStable d l s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact actionStable_refl d l s
  · split
    · have ha := actionStable_fighterAllocate d l s .payoff q.2 q.1
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact actionStable_trans d l ha
            (actionStable_record_payoff d l next q)
    · exact actionStable_refl d l s

/-- Finite internal folds cannot restore spent resources or canceled phases. -/
private lemma actionStable_foldl {α : Type} (d l : ℕ)
    (f : FighterState → α → FighterState)
    (hf : ∀ s a, actionStable d l s (f s a))
    (xs : List α) (s : FighterState) :
    actionStable d l s (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact actionStable_refl d l s
  | cons a xs ih => exact actionStable_trans d l (hf s a) (ih _)

/-- Immediate payoff checks preserve official play and cannot increase payoff reserves. -/
private lemma actionStable_fighterFulfillReady (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    actionStable d l s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact actionStable_refl d l s
  · apply actionStable_foldl
    intro t q
    exact actionStable_fighterPayoff P d l q t

/-- One fuel unit preserves official data, and newly funded requests were already reserved. -/
private lemma actionStable_fighterFuelUnit (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) :
    actionStable d l s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact actionStable_refl d l s
  · rename_i phase hphase
    have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc : actionStable d l s (s.putPhase d charged) := by
        intro p hp
        rw [FighterState.activeAt_putPhase d l s charged hlevel] at hp
        cases hp
        exact ⟨phase, hphase, rfl, rfl, rfl, rfl, Finset.Subset.refl _⟩
      have ha := actionStable_fighterAllocate d l
        (s.putPhase d charged) .fuel (levelUpper l + d) output
      have hbefore := actionStable_trans d l hc ha
      change actionStable d l s
        (match fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
        | (next, success) => if success then
          fighterFulfillReady P d l (next.putPhase d
            ((charged.insertIndex d q index).fundRequests d next.fulfilled)) else next)
      have hs := fulfilled_and_activeAt_fighterAllocate d l (s.putPhase d charged)
        .fuel (levelUpper l + d) output
      cases he : fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore hs
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hs ⊢
        · exact hbefore
        · have hn : next.activeAt d l = some charged := by
            rw [hs.2, FighterState.activeAt_putPhase d l s charged hlevel]
          apply actionStable_trans d l hbefore
          apply actionStable_trans d l _
            (actionStable_fighterFulfillReady P d l _)
          intro p hp
          rw [FighterState.activeAt_putPhase d l next
            ((charged.insertIndex d q index).fundRequests d next.fulfilled) hlevel] at hp
          cases hp
          refine ⟨charged, hn, rfl, rfl, rfl, rfl, ?_⟩
          exact (payoffReserve_fundRequests d (charged.insertIndex d q index)
            next.fulfilled).subset
    · exact actionStable_refl d l s

/-- A finite batch of fuel units preserves official play and cannot increase payoff reserves. -/
private lemma actionStable_fighterFuelUnits (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (count : ℕ) (s : FighterState) :
    actionStable d l s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact actionStable_refl d l s
  | succ count ih =>
      exact actionStable_trans d l
        (actionStable_fighterFuelUnit P d l q s) (ih _)

/-- The initial resource measure fits in the explicit action fuel. -/
private lemma actionWeight_le_fighterClosureFuel (d l : ℕ) (s : FighterState) :
    actionWeight d l s ≤ fighterClosureFuel d l s := by
  cases hs : s.activeAt d l with
  | none => simp [actionWeight, fighterClosureFuel, hs]
  | some p =>
    have hr : (payoffReserve d s.fulfilled p).card ≤
        p.pending.length + (p.game d).coordinates.length := by
      apply le_trans (Finset.card_le_card Finset.sdiff_subset)
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _))
    have hl := (p.official d).left_le
    have hb := (p.official d).right_le
    have hd : dummyWeight p ≤ 1 := by
      unfold dummyWeight
      split <;> omega
    simp only [actionWeight, fighterClosureFuel, hs]
    unfold CounterPosition.budgetSum
    omega

/-- Recording a payoff filters the current phase without changing its identity. -/
private lemma activeAt_record_payoff (d l : ℕ) (s : FighterState)
    (p : FighterPhase) (q : Coordinate) (hs : s.activeAt d l = some p) :
    ({ s with fulfilled := s.fulfilled ++ [q]
              active := s.active.map (fun p : FighterPhase ↦
                { p with pending := p.pending.filter (· != q) }) }).activeAt d l =
      some { p with pending := p.pending.filter (· != q) } := by
  simp only [FighterState.activeAt, List.find?_map]
  change (s.activeAt d l).map _ = _
  rw [hs]
  rfl

/-- A requested dummy consumes its one reserved action or cancels the phase. -/
private lemma actionWeight_fighterDummy_lt (d l : ℕ) (s : FighterState)
    (p : FighterPhase) (hs : s.activeAt d l = some p)
    (henabled : (p.dummy.isSome && !p.dummyIssued) = true) :
    actionWeight d l (fighterDummy d l s) <
      actionWeight d l s := by
  have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := p) hs
  cases hdum : p.dummy with
  | none => simp [hdum] at henabled
  | some output =>
    have hi : p.dummyIssued = false := by simpa [hdum] using henabled
    simp only [fighterDummy, hs, hdum, hi, Bool.false_eq_true, ite_false]
    have ha := fulfilled_and_activeAt_fighterAllocate d l s .dummy (levelInput d l) output
    cases he : fighterAllocate d l .dummy (levelInput d l) output s with
    | mk next success =>
      rw [he] at ha
      cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
      · simp [actionWeight, ha.2, hs]
      · have hput := FighterState.activeAt_putPhase d l next
          { p with dummyIssued := true } hlevel
        simp only [hdum] at hput
        simp only [actionWeight, hput, hs]
        change (p.official d).budgetSum +
            (payoffReserve d next.fulfilled p).card + 0 + 1 <
          (p.official d).budgetSum + (payoffReserve d s.fulfilled p).card +
            dummyWeight p + 1
        rw [ha.1]
        simp [dummyWeight, hdum, hi]

/-- A safe unfulfilled pending payoff consumes its reserved coordinate or cancels the phase. -/
private lemma actionWeight_fighterPayoff_lt (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (q : Coordinate)
    (hs : s.activeAt d l = some p) (hq : q ∈ p.pending) (hf : q ∉ s.fulfilled)
    (hsafe : fighterSafe P d s.tick q = true) :
    actionWeight d l (fighterPayoff P d l q s) <
      actionWeight d l s := by
  have hmem : q ∈ payoffReserve d s.fulfilled p := by
    simp [payoffReserve, hq, hf]
  have hcard := Finset.card_erase_lt_of_mem hmem
  simp only [fighterPayoff, hs]
  rw [ite_eq_left ⟨hq, hf, hsafe⟩]
  have ha := fulfilled_and_activeAt_fighterAllocate d l s .payoff q.2 q.1
  cases he : fighterAllocate d l .payoff q.2 q.1 s with
  | mk next success =>
    rw [he] at ha
    cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
    · simp [actionWeight, ha.2, hs]
    · have hn : next.activeAt d l = some p := ha.2.trans hs
      have hrec := activeAt_record_payoff d l next p q hn
      simp only [actionWeight, hrec, hs]
      rw [ha.1, payoffReserve_record_payoff]
      change (p.official d).budgetSum +
          ((payoffReserve d s.fulfilled p).erase q).card +
          dummyWeight p + 1 <
        (p.official d).budgetSum + (payoffReserve d s.fulfilled p).card +
          dummyWeight p + 1
      omega

/-- Flushing a legal positive buffer decreases the official budget and leaves other reserves
unchanged. -/
private lemma actionWeight_lt_of_flushBuffer (d l : ℕ) (s next : FighterState)
    (h : fighterFlushBuffer d l s = some next) :
    actionWeight d l next < actionWeight d l s := by
  cases hs : s.activeAt d l with
  | none => simp [fighterFlushBuffer, hs] at h
  | some p =>
    have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := p) hs
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some] at h
    split at h
    · rename_i henabled
      have hbudget := counter_move_decreases_budget (p.game d) (p.official d) p.buffer henabled.2.2
      cases h
      have hput := FighterState.activeAt_putPhase d l s
        { p with officialCode := ((p.game d).afterMove (p.official d) p.buffer).encode
                 buffer := List.replicate (p.game d).coordinates.length 0 } hlevel
      simp only [actionWeight, hput, hs]
      have ho : ({ p with
          officialCode := ((p.game d).afterMove (p.official d) p.buffer).encode
          buffer := List.replicate (p.game d).coordinates.length 0 }.official d).budgetSum =
          ((p.game d).afterMove (p.official d) p.buffer).budgetSum := by
        exact congrArg CounterPosition.budgetSum (decode_encode_counter_position _ _)
      rw [ho]
      change ((p.game d).afterMove (p.official d) p.buffer).budgetSum +
          (payoffReserve d s.fulfilled p).card +
          dummyWeight p + 1 <
        (p.official d).budgetSum + (payoffReserve d s.fulfilled p).card +
          dummyWeight p + 1
      omega
    · contradiction

/-- A controlled response installs a legal official child with smaller total budget; its fuel and
payoff subroutines cannot increase other reserves. -/
private lemma actionWeight_lt_of_strategyMove (P : FighterParams) (d l : ℕ)
    (s result : FighterState) (h : fighterStrategyMove P d l s = some result) :
    actionWeight d l result < actionWeight d l s := by
  cases hs : s.activeAt d l with
  | none => simp [fighterStrategyMove, hs] at h
  | some p =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some] at h
    split at h
    · cases hm : (p.game d).strategy (p.official d) with
      | none => simp [hm] at h
      | some move =>
        simp only [hm, Option.bind_some] at h
        split at h
        · rename_i hlegal
          have hbudget := counter_move_decreases_budget (p.game d) (p.official d) move hlegal.1
          let next := (p.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : actionStable d l s next := by
            apply actionStable_foldl
            intro t qi
            exact actionStable_fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) t
          change (match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
                { live with officialCode := ((p.game d).afterMove (p.official d) move).encode })) =
              some result at h
          cases hlive : next.activeAt d l with
          | none =>
            simp only [hlive, Option.some.injEq] at h
            subst result
            simp [actionWeight, hlive, hs]
          | some live =>
            simp only [hlive, Option.some.injEq] at h
            subst result
            obtain ⟨old, hold, hg, _, hd, hi, hr⟩ := hn live hlive
            rw [hs] at hold
            cases hold
            have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := live) hlive
            have hput := FighterState.activeAt_putPhase d l next
              { live with officialCode := ((p.game d).afterMove (p.official d) move).encode } hlevel
            have hgame : live.game d = p.game d := by
              exact congrArg decodeCounterGame hg
            have hnewbudget : ({ live with
                officialCode := ((p.game d).afterMove (p.official d) move).encode
              }.official d).budgetSum =
                ((p.game d).afterMove (p.official d) move).budgetSum := by
              change (decodeCounterPosition (live.game d)
                ((p.game d).afterMove (p.official d) move).encode).budgetSum = _
              rw [hgame, decode_encode_counter_position]
            have hdummy : dummyWeight live =
                dummyWeight p := by
              simp only [dummyWeight, hd, hi]
            have hcard := Finset.card_le_card hr
            simp only [actionWeight, hput, hs]
            rw [hnewbudget]
            change ((p.game d).afterMove (p.official d) move).budgetSum +
                (payoffReserve d next.fulfilled live).card +
                dummyWeight live + 1 <
              (p.official d).budgetSum + (payoffReserve d s.fulfilled p).card +
                dummyWeight p + 1
            omega
        · contradiction
    · contradiction

/-- Each enabled action strictly spends the combined budget, payoff, and dummy reserve. -/
private lemma actionWeight_lt_of_levelAction (P : FighterParams) (d l : ℕ)
    (s next : FighterState) (h : fighterLevelAction P d l s = some next) :
    actionWeight d l next < actionWeight d l s := by
  cases hs : s.activeAt d l with
  | none => simp [fighterLevelAction, hs] at h
  | some p =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some] at h
    split at h
    · rename_i hdummy
      cases h
      exact actionWeight_fighterDummy_lt d l s p hs hdummy
    · cases hq : p.pending.find? (fun q ↦
          decide (q ∉ s.fulfilled) && fighterSafe P d s.tick q) with
      | some q =>
        simp only [hq, Option.some.injEq] at h
        subst next
        have hmem := List.mem_of_find?_eq_some hq
        have htest := List.find?_some hq
        have htest' : q ∉ s.fulfilled ∧ fighterSafe P d s.tick q = true := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using htest
        exact actionWeight_fighterPayoff_lt P d l s p q hs hmem htest'.1 htest'.2
      | none =>
        simp only [hq] at h
        cases hf : fighterFlushBuffer d l s with
        | some t =>
          simp only [hf, Option.some.injEq] at h
          subst next
          exact actionWeight_lt_of_flushBuffer d l s t hf
        | none =>
          simp only [hf] at h
          exact actionWeight_lt_of_strategyMove P d l s next h

/-- Strict local progress exhausts enabled work once fuel reaches the resource measure. -/
private lemma levelAction_closure_eq_none_of_actionWeight_le (P : FighterParams) (d l fuel : ℕ)
    (s : FighterState) (hbound : actionWeight d l s ≤ fuel) :
    fighterLevelAction P d l (fighterClosure P d l fuel s) = none := by
  induction fuel generalizing s with
  | zero =>
    cases h : fighterLevelAction P d l s with
    | none => exact h
    | some next =>
      have hdec := actionWeight_lt_of_levelAction P d l s next h
      omega
  | succ fuel ih =>
    simp only [fighterClosure]
    cases h : fighterLevelAction P d l s with
    | none => exact h
    | some next =>
      apply ih
      have hdec := actionWeight_lt_of_levelAction P d l s next h
      omega

/-- The explicit action fuel reaches a fixpoint; no enabled work is truncated.
Blueprint node `constr:effective`. Every controlled move costs positive budget,
each payoff can succeed once, the dummy occurs once, and cancellation cannot restart. -/
theorem fighter_closure_fixpoint (P : FighterParams) (d l : ℕ) (state : FighterState) :
    fighterLevelAction P d l (fighterCloseLevel P d l state) = none := by
  exact levelAction_closure_eq_none_of_actionWeight_le P d l _ state
    (actionWeight_le_fighterClosureFuel d l state)

end Kolmogorov.Milovanov
