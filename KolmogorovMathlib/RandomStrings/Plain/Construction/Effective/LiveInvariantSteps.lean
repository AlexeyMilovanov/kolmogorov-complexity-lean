/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.StateMachine

/-!
# One-step preservation of the finite live invariant of the fighter construction

The fighter construction maintains, for every active phase, the official counter position of
its counter game together with a live copy of the counters and a buffer of pending opponent
moves.  This file defines the finite-state part of the invariant used in the proof of
`fighter_live_invariants`:

* `PhaseRegular` says that the buffer and counter vectors of a phase have the right lengths and
  satisfy the official/live equations;
* `PhaseBacked` says that every index stored in a phase is backed either by a base-machine
  description or by an entry of the permanent allocation graph;
* `FiniteLiveInvariant` combines both for all active phases of a state;
* `LiveInvariantStep P d s t` says that `t` retains every allocation of `s` and that the finite
  invariant passes from `s` to `t`.

The relation `LiveInvariantStep` is reflexive and transitive, and the file shows that it holds
for each elementary action of the construction: cancelling and aborting phases, allocating
directives, paying off requests, starting a phase, processing a base-machine event and flushing
the buffer.  The module `Construction.Effective.LiveInvariants` composes these actions along
the whole run of the construction.
-/

namespace Kolmogorov.Milovanov

/-- The vector lengths needed while preserving the official/live equations. -/
def PhaseRegular (d : ℕ) (p : FighterPhase) : Prop :=
  p.BufferInvariant d ∧ p.buffer.length = (p.game d).coordinates.length ∧
    (p.official d).counters.length = (p.game d).coordinates.length

/-- A finite backing witness is either a base-machine description or an entry in the
permanent graph, with the one-bit directive overhead included in its length bound. -/
def PhaseBacked (P : FighterParams) (d : ℕ)
    (allocated : List AllocatedDirective) (p : FighterPhase) : Prop :=
  ∀ q ∈ p.J d, ∀ index ∈ p.indicesAt d q,
    Simple P.B.V (pairCode (triple q.1 (q.2 - d) p.candidate.1) index)
        (levelUpper p.level) ∨
      ∃ a ∈ allocated,
        a.output = pairCode (triple q.1 (q.2 - d) p.candidate.1) index ∧
        a.input.length + 1 ≤ levelUpper p.level + d

/-- The finite-state invariant, before passing from graph entries to the limiting machine. -/
def FiniteLiveInvariant (P : FighterParams) (d : ℕ)
    (s : FighterState) : Prop :=
  ∀ p ∈ s.active, PhaseRegular d p ∧ PhaseBacked P d s.allocated p

/-- A local transition retains every allocation and preserves the finite-state invariant. -/
def LiveInvariantStep (P : FighterParams) (d : ℕ)
    (s t : FighterState) : Prop :=
  s.allocated ⊆ t.allocated ∧ (FiniteLiveInvariant P d s → FiniteLiveInvariant P d t)

/-- Doing nothing is a `LiveInvariantStep`. -/
lemma LiveInvariantStep.refl (P : FighterParams) (d : ℕ) (s : FighterState) :
    LiveInvariantStep P d s s := ⟨fun _ h ↦ h, id⟩

/-- `LiveInvariantStep` is transitive. -/
lemma LiveInvariantStep.trans (P : FighterParams) (d : ℕ)
    {s t u : FighterState} (h : LiveInvariantStep P d s t)
    (h' : LiveInvariantStep P d t u) :
    LiveInvariantStep P d s u :=
  ⟨fun _ ha ↦ h'.1 (h.1 ha), fun hs ↦ h'.2 (h.2 hs)⟩

/-- If every step of a left fold is a `LiveInvariantStep`, so is the whole fold. -/
lemma LiveInvariantStep.foldl {α : Type} (P : FighterParams) (d : ℕ)
    (f : FighterState → α → FighterState)
    (hf : ∀ s a, LiveInvariantStep P d s (f s a))
    (xs : List α) (s : FighterState) :
    LiveInvariantStep P d s (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact LiveInvariantStep.refl P d s
  | cons a xs ih => exact LiveInvariantStep.trans P d (hf s a) (ih _)

/-- Backing witnesses stay valid when the list of allocated directives grows. -/
lemma PhaseBacked.mono (P : FighterParams) (d : ℕ)
    {as bs : List AllocatedDirective} (h : as ⊆ bs) (p : FighterPhase)
    (hp : PhaseBacked P d as p) :
    PhaseBacked P d bs p := by
  intro q hq index hi
  rcases hp q hq index hi with hbase | ⟨a, ha, ho, hl⟩
  · exact Or.inl hbase
  · exact Or.inr ⟨a, h ha, ho, hl⟩

/-- A state with more allocations and the same active phases is a `LiveInvariantStep`. -/
lemma LiveInvariantStep.of_subset_of_active_eq (P : FighterParams) (d : ℕ)
    (s t : FighterState) (ha : s.allocated ⊆ t.allocated) (hp : t.active = s.active) :
    LiveInvariantStep P d s t := by
  refine ⟨ha, ?_⟩
  intro hs p hm
  obtain ⟨hr, hb⟩ := hs p (hp ▸ hm)
  exact ⟨hr, PhaseBacked.mono P d ha p hb⟩

/-- Replacing the phase at a level by a regular, backed phase preserves the finite invariant. -/
private lemma FiniteLiveInvariant.putPhase (P : FighterParams) (d : ℕ)
    (s : FighterState) (p : FighterPhase)
    (hp : PhaseRegular d p ∧ PhaseBacked P d s.allocated p)
    (hs : FiniteLiveInvariant P d s) :
    FiniteLiveInvariant P d (s.putPhase d p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hp
  · exact hs r (List.mem_filter.mp hr).1

private lemma LiveInvariantStep.cancel (P : FighterParams) (d l : ℕ)
    (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    LiveInvariantStep P d s (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact LiveInvariantStep.refl P d s
  · refine ⟨fun _ h ↦ h, ?_⟩
    intro hs p hp
    exact hs p (List.mem_filter.mp hp).1

private lemma LiveInvariantStep.abortAbove (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply LiveInvariantStep.foldl
  intro t p
  split
  · exact LiveInvariantStep.cancel P d p.level .aborted l t
  · exact LiveInvariantStep.refl P d t

private lemma fighterCancel_allocated (d l : ℕ)
    (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    (fighterCancel d l reason cause s).allocated = s.allocated := by
  unfold fighterCancel
  split <;> rfl

/-- Aborting the phases above a level does not change the list of allocated directives. -/
lemma fighterAbortAbove_allocated (d l : ℕ) (s : FighterState) :
    (fighterAbortAbove d l s).allocated = s.allocated := by
  have hf (xs : List FighterPhase) (t : FighterState) :
      (xs.foldl (fun t p ↦ if l < p.level then
        fighterCancel d p.level .aborted l t else t) t).allocated = t.allocated := by
    induction xs generalizing t with
    | nil => rfl
    | cons p xs ih =>
      rw [List.foldl_cons, ih]
      split
      · exact fighterCancel_allocated d p.level .aborted l t
      · rfl
  exact hf _ _

private lemma LiveInvariantStep.allocate (P : FighterParams) (d l : ℕ)
    (kind : DirectiveKind) (target : ℕ) (output : BitString) (s : FighterState) :
    LiveInvariantStep P d s (fighterAllocate d l kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact LiveInvariantStep.refl P d s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      dsimp only
      exact LiveInvariantStep.trans P d
        (LiveInvariantStep.of_subset_of_active_eq P d s { s with failed := true }
          (fun _ h ↦ h) rfl)
        (LiveInvariantStep.cancel P d l .saturated l _)
    | some p =>
      dsimp only
      apply LiveInvariantStep.trans P d _ (LiveInvariantStep.abortAbove P d l _)
      exact LiveInvariantStep.of_subset_of_active_eq P d s _
        (fun _ h ↦ List.mem_append_left _ h) rfl

private lemma LiveInvariantStep.recordFulfilled (P : FighterParams) (d : ℕ)
    (s : FighterState) (q : Coordinate) :
    LiveInvariantStep P d s
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map
          (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨fun _ h ↦ h, ?_⟩
  intro hs p hp
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
  exact hs old hold

/-- Paying off a request is a `LiveInvariantStep`. -/
lemma LiveInvariantStep.payoff (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) :
    LiveInvariantStep P d s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact LiveInvariantStep.refl P d s
  · split
    · have ha := LiveInvariantStep.allocate P d l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success
        · exact ha
        · exact LiveInvariantStep.trans P d ha
            (LiveInvariantStep.recordFulfilled P d next q)
    · exact LiveInvariantStep.refl P d s

/-- Fulfilling all ready requests is a `LiveInvariantStep`. -/
lemma LiveInvariantStep.fulfillReady (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact LiveInvariantStep.refl P d s
  · apply LiveInvariantStep.foldl
    intro t q
    exact LiveInvariantStep.payoff P d l q t

/-- Under the finite invariant, the phase active at a level is regular and backed. -/
lemma FiniteLiveInvariant.of_activeAt_eq_some (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (h : s.activeAt d l = some p)
    (hs : FiniteLiveInvariant P d s) :
    PhaseRegular d p ∧ PhaseBacked P d s.allocated p :=
  hs p (List.mem_of_find?_eq_some h)

/-- Coordinatewise formula for the sum of two counter vectors, valid at in-range indices. -/
lemma FiniteCounterGame.getD_addCounters (g : FiniteCounterGame)
    (a b : List ℕ) (i : ℕ) (hi : i < g.coordinates.length) :
    (g.addCounters a b)[i]?.getD 0 = a[i]?.getD 0 + b[i]?.getD 0 := by
  simp [FiniteCounterGame.addCounters, List.getElem?_range hi]

/-- Adding the zero vector to a counter vector of the right length does not change it. -/
lemma FiniteCounterGame.addCounters_replicate_zero (g : FiniteCounterGame)
    (a : List ℕ) (ha : a.length = g.coordinates.length) :
    g.addCounters a (List.replicate g.coordinates.length 0) = a := by
  apply List.ext_getElem
  · simpa [FiniteCounterGame.addCounters] using ha.symm
  · intro i hi hi'
    have hgi : i < g.coordinates.length := by simpa [FiniteCounterGame.addCounters] using hi
    simp [FiniteCounterGame.addCounters, List.getElem?_eq_getElem hi']

/-- Coordinatewise addition of counter vectors is associative. -/
lemma FiniteCounterGame.addCounters_assoc (g : FiniteCounterGame)
    (a b c : List ℕ) :
    g.addCounters (g.addCounters a b) c = g.addCounters a (g.addCounters b c) := by
  apply List.ext_getElem
  · simp [FiniteCounterGame.addCounters]
  · intro i hi hi'
    have hgi : i < g.coordinates.length := by simpa [FiniteCounterGame.addCounters] using hi
    simp [FiniteCounterGame.addCounters, List.getElem?_range hgi, Nat.add_assoc]

private lemma backed_of_mem_fighterInitialIndices (P : FighterParams) (d l : ℕ)
    (candidate : Candidate) (as : List AllocatedDirective) (q : Coordinate) (index : BitString)
    (hi : index ∈ fighterInitialIndices P d l candidate as q) :
    Simple P.B.V (pairCode (triple q.1 (q.2 - d) candidate.1) index) (levelUpper l) ∨
      ∃ a ∈ as, a.output = pairCode (triple q.1 (q.2 - d) candidate.1) index ∧
        a.input.length + 1 ≤ levelUpper l + d := by
  simp only [fighterInitialIndices, List.mem_eraseDups, List.mem_append] at hi
  rcases hi with hi | hi
  · have hold := of_decide_eq_true (List.mem_filter.mp hi).2
    by_cases hv : validCandidate P.B (levelScale l) candidate = true
    · left
      apply (canonical_enumeration_spec_union P.B _ _).mpr
      refine ⟨candidate.2, ?_⟩
      have hm := (mem_past_extension_indices P.B (levelScale l) candidate
        (levelScale l) (triple q.1 (q.2 - d) candidate.1) index hv).mp hold
      simpa only [extensionScale, level_upper_eq] using hm
    · simp [pastExtensionIndices, hv] at hold
  · obtain ⟨a, ha, hai⟩ := List.mem_filterMap.mp hi
    split at hai
    · rename_i hcond
      cases hai
      exact Or.inr ⟨a, ha, hcond.2.symm, hcond.1⟩
    · contradiction

/-- Blueprint node `fighter_live_invariants`, initialization: a freshly constructed phase has
equal official/live counters, equal budgets, and a zero buffer of the correct length.
Every initial index is backed either by its frozen base-table description or by an
entry of the supplied permanent allocation table within the upper description budget.
This statement concerns initialization only, for arbitrary candidates and finite states. -/
private theorem fighter_construction_regular_and_backed (P : FighterParams)
    (d l : ℕ) (candidate : Candidate) (s : FighterState) :
    PhaseRegular d (fighter_construction P d l candidate s) ∧
      PhaseBacked P d s.allocated (fighter_construction P d l candidate s) := by
  let coords := retainedCoordinateList (constructedLiteralConstant P.literal d)
    (levelInput d l) (P.family.tree d l (levelInput d l))
  let indices := coords.map (fighterInitialIndices P d l candidate s.allocated)
  let counters := indices.map (fun xs ↦ xs.toFinset.card)
  let R := P.c₁ * 2 ^ (levelUpper l - levelScale l)
  let original := finite_counter_game coords
    (coordinatePriceTable P.B P.lam P.n₀ (levelScale l) d candidate coords) counters
    ((P.family.tree d l (levelInput d l)).queries.filter (fun q ↦
      decide (q.1 ∈ fighterStageOutputs P d q.2 s.tick s.allocated))) R
    ((P.family.tree d l (levelInput d l)).normalize (constructedLiteralConstant P.literal d))
    (fighterStageOutputs P d (levelInput d l) s.tick s.allocated).card
  let game := original.controlWinningPlayer
  let p : FighterPhase := ⟨l, candidate, s.schedule, s.allocated, game.encode,
    indices, game.initialPosition.encode, counters, R, R, List.replicate coords.length 0,
    [], none, false, false⟩
  change PhaseRegular d p ∧ PhaseBacked P d s.allocated p
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
  have hgame : p.game d = game := decode_encode_counter_game game
  have hlen : counters.length = game.coordinates.length := by
    simp [counters, indices, hcoords]
  have hoff : (p.official d).counters = counters ∧
      (p.official d).leftBudget = R ∧ (p.official d).rightBudget = R := by
    change (decodeCounterPosition (p.game d) game.initialPosition.encode).counters = counters ∧
      (decodeCounterPosition (p.game d) game.initialPosition.encode).leftBudget = R ∧
      (decodeCounterPosition (p.game d) game.initialPosition.encode).rightBudget = R
    rw [hgame, decode_encode_counter_position]
    simp [FiniteCounterGame.initialPosition, hcounter, hbudget]
  refine ⟨?_, ?_⟩
  · change (false = false ∧ counters = (p.game d).addCounters (p.official d).counters
        (List.replicate coords.length 0) ∧ (p.official d).leftBudget = R ∧
        (p.official d).rightBudget = R + (List.replicate coords.length 0).sum) ∧
      (List.replicate coords.length 0).length = (p.game d).coordinates.length ∧
      (p.official d).counters.length = (p.game d).coordinates.length
    simp only [hoff.1, hoff.2.1, hoff.2.2, hgame]
    rw [← hcoords, FiniteCounterGame.addCounters_replicate_zero game counters hlen]
    simp [hlen]
  · intro q hq index hi
    have hqgame : q ∈ (p.game d).coordinates := by
      simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
        List.mem_eraseDups, List.mem_toFinset] using hq
    have hqcoords : q ∈ coords := by simpa only [hgame, hcoords] using hqgame
    simp only [FighterPhase.indicesAt, hqgame, ite_true] at hi
    change index ∈ (indices[(p.game d).coordinates.idxOf q]?.getD []).toFinset at hi
    rw [hgame, hcoords] at hi
    simp only [indices, List.getElem?_map, List.getElem?_idxOf hqcoords,
      Option.map_some, Option.getD_some, List.mem_toFinset] at hi
    exact backed_of_mem_fighterInitialIndices P d l candidate s.allocated q index hi

/-- Starting a phase at a level is a `LiveInvariantStep`. -/
lemma LiveInvariantStep.startPhase (P : FighterParams) (d l : ℕ)
    (candidate : Candidate) (s : FighterState) :
    LiveInvariantStep P d s (fighterStartPhase P d l candidate s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw := LiveInvariantStep.trans P d
    (LiveInvariantStep.cancel P d l .replaced l s)
    (LiveInvariantStep.abortAbove P d l _)
  refine ⟨hw.1, ?_⟩
  intro hs
  exact FiniteLiveInvariant.putPhase P d waiting _
    (fighter_construction_regular_and_backed P d l candidate waiting) (hw.2 hs)

/-- A dummy step at a level is a `LiveInvariantStep`. -/
lemma LiveInvariantStep.dummy (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s (fighterDummy d l s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterDummy, hs] using LiveInvariantStep.refl P d s
  | some p =>
    simp only [fighterDummy, hs]
    split
    · exact LiveInvariantStep.refl P d s
    · rename_i output hout
      split
      · exact LiveInvariantStep.refl P d s
      · have ha := LiveInvariantStep.allocate P d l .dummy (levelInput d l) output s
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · refine ⟨ha.1, ?_⟩
            intro hinv
            apply FiniteLiveInvariant.putPhase P d next _ _ (ha.2 hinv)
            obtain ⟨hr, hb⟩ := FiniteLiveInvariant.of_activeAt_eq_some P d l s p hs hinv
            exact ⟨hr, PhaseBacked.mono P d ha.1 p hb⟩

private lemma map_range_getD_zero_eq_self (xs : List ℕ) :
    (List.range xs.length).map (fun i ↦ xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem?_eq_getElem hi']

/-- Adding two length-correct counter vectors adds their totals. -/
lemma FiniteCounterGame.sum_addCounters (g : FiniteCounterGame) (a b : List ℕ)
    (ha : a.length = g.coordinates.length) (hb : b.length = g.coordinates.length) :
    (g.addCounters a b).sum = a.sum + b.sum := by
  simp only [FiniteCounterGame.addCounters, List.sum_map_add]
  rw [← ha, map_range_getD_zero_eq_self, ha, ← hb, map_range_getD_zero_eq_self]

/-- The unit vector of a retained coordinate has total one. -/
lemma FighterPhase.sum_unitVector (p : FighterPhase) (d : ℕ)
    (q : Coordinate) (hq : q ∈ (p.game d).coordinates) :
    (p.unitVector d q).sum = 1 := by
  have hf (xs : List Coordinate) (hnd : xs.Nodup) :
      (xs.map (fun r ↦ if r = q then 1 else 0)).sum = if q ∈ xs then 1 else 0 := by
    induction xs with
    | nil => simp
    | cons r xs ih =>
      obtain ⟨hr, ht⟩ := List.nodup_cons.mp hnd
      by_cases he : r = q
      · subst r
        simp [ih ht, hr]
      · simp [he, ih ht, Ne.symm he]
  simpa [FighterPhase.unitVector, hq] using hf (p.game d).coordinates
    (nodup_eraseDups_list _)

private lemma FighterPhase.mem_indicesAt_insertIndex (p : FighterPhase) (d : ℕ)
    (q r : Coordinate) (index stored : BitString) (hr : r ∈ p.J d)
    (hs : stored ∈ (p.insertIndex d q index).indicesAt d r) :
    stored ∈ p.indicesAt d r ∨ (r = q ∧ stored = index) := by
  have hr' : r ∈ (p.game d).coordinates := by
    simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
      List.mem_toFinset, List.mem_eraseDups] using hr
  have hgame : (p.insertIndex d q index).game d = p.game d := rfl
  have hindices : (p.insertIndex d q index).indices =
      (p.game d).coordinates.zipIdx.map (fun (t, i) ↦
        if t = q then (p.indices[i]?.getD [] ++ [index]).eraseDups
        else p.indices[i]?.getD []) := rfl
  simp only [FighterPhase.indicesAt, hgame, hindices, hr', ite_true, List.getElem?_map,
    List.getElem?_zipIdx, List.getElem?_idxOf hr', Option.map_some, Nat.zero_add,
    Option.getD_some, List.mem_toFinset] at hs ⊢
  by_cases he : r = q
  · subst r
    simp only [ite_true, List.mem_eraseDups, List.mem_append,
      List.mem_singleton] at hs
    exact hs.elim Or.inl (fun h ↦ Or.inr ⟨rfl, h⟩)
  · simp only [he, ite_false] at hs
    exact Or.inl hs

/-- Inserting a backed index into a phase keeps the phase backed. -/
lemma PhaseBacked.insertIndex (P : FighterParams) (d : ℕ)
    (as : List AllocatedDirective) (p : FighterPhase) (q : Coordinate) (index : BitString)
    (hp : PhaseBacked P d as p)
    (hindex : Simple P.B.V (pairCode (triple q.1 (q.2 - d) p.candidate.1) index)
        (levelUpper p.level) ∨
      ∃ a ∈ as, a.output = pairCode (triple q.1 (q.2 - d) p.candidate.1) index ∧
        a.input.length + 1 ≤ levelUpper p.level + d) :
    PhaseBacked P d as (p.insertIndex d q index) := by
  intro r hr stored hs
  rcases FighterPhase.mem_indicesAt_insertIndex p d q r index stored hr hs with
    hs | ⟨rfl, rfl⟩
  · exact hp r hr stored hs
  · exact hindex

/-- Decoding an opponent transaction supplies its retained coordinate, the exact literal output,
the program length bound, and the lower bound needed to undo subtraction of the padding. -/
theorem fighterOpponentTuple_spec
    (d : ℕ) (p : FighterPhase) (event : ProgramEvent) (q : Coordinate)
    (index : BitString) (h : fighterOpponentTuple d p event = some (q, index)) :
    q ∈ (p.game d).coordinates ∧ d ≤ q.2 ∧
      event.1.length ≤ levelUpper p.level ∧
      pairCode (triple q.1 (q.2 - d) p.candidate.1) index = event.2 := by
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
        refine ⟨hcond.2.1, by omega, Nat.le_of_not_gt hlen, ?_⟩
        simpa only [Nat.add_sub_cancel, hcond.1] using hcond.2.2
      · contradiction

private lemma PhaseRegular.opponentMove (p : FighterPhase) (d : ℕ)
    (q : Coordinate) (index : BitString)
    (hp : PhaseRegular d p) (hq : q ∈ (p.game d).coordinates)
    (hbudget : p.opponentRemaining ≠ 0) :
    PhaseRegular d
      { p.insertIndex d q index with
        opponentRemaining := p.opponentRemaining - 1
        buffer := (p.game d).addCounters p.buffer (p.unitVector d q) } := by
  obtain ⟨⟨hc, hv, hl, hr⟩, hbuf, hcounter⟩ := hp
  have hunitlen : (p.unitVector d q).length = (p.game d).coordinates.length := by
    simp [FighterPhase.unitVector]
  have hsum := FiniteCounterGame.sum_addCounters (p.game d) p.buffer (p.unitVector d q)
    hbuf hunitlen
  rw [FighterPhase.sum_unitVector p d q hq] at hsum
  change (p.controlledPlayer = false ∧
      (p.game d).addCounters p.liveCounters (p.unitVector d q) =
        (p.game d).addCounters (p.official d).counters
          ((p.game d).addCounters p.buffer (p.unitVector d q)) ∧
      (p.official d).leftBudget = p.controlledRemaining ∧
      (p.official d).rightBudget = p.opponentRemaining - 1 +
        ((p.game d).addCounters p.buffer (p.unitVector d q)).sum) ∧
    ((p.game d).addCounters p.buffer (p.unitVector d q)).length =
      (p.game d).coordinates.length ∧
    (p.official d).counters.length = (p.game d).coordinates.length
  refine ⟨⟨hc, ?_, hl, ?_⟩, by simp [FiniteCounterGame.addCounters], hcounter⟩
  · rw [hv, FiniteCounterGame.addCounters_assoc]
  · omega

/-- Blueprint node `fighter_live_invariants`, base events: one genuine base
halting event preserves the finite backing witnesses and the official/live equations.
A new retained index increments both live counters and buffer and spends one opponent
unit; duplicates are inert and exhaustion cancels. Immediate payoff checks may cancel
phases or filter pending requests. The event need not belong to this level. -/
theorem LiveInvariantStep.opponent (P : FighterParams) (d l : ℕ)
    (event : ProgramEvent) (s : FighterState)
    (hevent : produces P.B.V event.1 [] event.2) :
    LiveInvariantStep P d s (fighterOpponent P d l event s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterOpponent, hs] using LiveInvariantStep.refl P d s
  | some p =>
    simp only [fighterOpponent, hs]
    split
    · exact LiveInvariantStep.refl P d s
    · rename_i q index htuple
      split
      · exact LiveInvariantStep.refl P d s
      · split
        · exact LiveInvariantStep.cancel P d l .opponentExhausted l s
        · rename_i hbudget
          apply LiveInvariantStep.trans P d _ (LiveInvariantStep.fulfillReady P d l _)
          refine ⟨fun _ h ↦ h, ?_⟩
          intro hinv
          obtain ⟨hr, hb⟩ := FiniteLiveInvariant.of_activeAt_eq_some P d l s p hs hinv
          obtain ⟨hq, -, hlen, hout⟩ := fighterOpponentTuple_spec d p event q index htuple
          apply FiniteLiveInvariant.putPhase P d s _ _ hinv
          refine ⟨PhaseRegular.opponentMove p d q index hr hq hbudget, ?_⟩
          apply PhaseBacked.insertIndex P d s.allocated p q index hb
          left
          apply (simple_iff_exists_program _ _ _).mpr
          exact ⟨event.1, hlen, hout.symm ▸ hevent⟩

/-- Blueprint node `fighter_live_invariants`, buffer flush: an enabled legal
buffer flush transfers its counters and previously charged cost to the official
position and replaces the buffer by a zero vector. Stored indices and their finite
backing witnesses are unchanged. -/
theorem LiveInvariantStep.flushBuffer (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s ((fighterFlushBuffer d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterFlushBuffer, hs] using LiveInvariantStep.refl P d s
  | some p =>
    simp only [fighterFlushBuffer, hs, bind, Option.bind_some]
    split
    · rename_i henabled
      refine ⟨fun _ h ↦ h, ?_⟩
      intro hinv
      obtain ⟨hr, hb⟩ := FiniteLiveInvariant.of_activeAt_eq_some P d l s p hs hinv
      apply FiniteLiveInvariant.putPhase P d s _ _ hinv
      refine ⟨?_, hb⟩
      obtain ⟨⟨hc, hv, hl, hbgt⟩, hbuf, hcounter⟩ := hr
      have hactive : (p.game d).activePlayer (p.official d) = true := by
        rw [hc] at henabled
        exact Bool.eq_true_of_not_eq_false henabled.2.1
      change (p.controlledPlayer = false ∧
          p.liveCounters = (p.game d).addCounters
            (decodeCounterPosition (p.game d)
              ((p.game d).afterMove (p.official d) p.buffer).encode).counters
            (List.replicate (p.game d).coordinates.length 0) ∧
          (decodeCounterPosition (p.game d)
              ((p.game d).afterMove (p.official d) p.buffer).encode).leftBudget =
            p.controlledRemaining ∧
          (decodeCounterPosition (p.game d)
              ((p.game d).afterMove (p.official d) p.buffer).encode).rightBudget =
            p.opponentRemaining + (List.replicate (p.game d).coordinates.length 0).sum) ∧
        (List.replicate (p.game d).coordinates.length 0).length =
            (p.game d).coordinates.length ∧
        (decodeCounterPosition (p.game d)
          ((p.game d).afterMove (p.official d) p.buffer).encode).counters.length =
            (p.game d).coordinates.length
      rw [decode_encode_counter_position]
      have hlen : ((p.game d).afterMove (p.official d) p.buffer).counters.length =
          (p.game d).coordinates.length := by simp [FiniteCounterGame.afterMove,
            FiniteCounterGame.addCounters]
      rw [FiniteCounterGame.addCounters_replicate_zero _ _ hlen]
      refine ⟨⟨hc, hv, ?_, ?_⟩, by simp, hlen⟩
      · simpa [FiniteCounterGame.afterMove, hactive] using hl
      · simp [FiniteCounterGame.afterMove, hactive, hbgt]
    · exact LiveInvariantStep.refl P d s

end Kolmogorov.Milovanov
