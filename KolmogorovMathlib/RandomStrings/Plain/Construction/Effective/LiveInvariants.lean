/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.Allocations
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.LiveInvariantSteps

/-!
# The live invariant of the fighter construction

This file proves `fighter_live_invariants`: every phase that is active at some tick of the
fighter construction satisfies the buffer equations relating its official and live counters,
and every stored extension index is backed by a base-machine description or by an entry of the
permanent allocation graph.

The one-step preservation lemmas for the elementary actions (see `LiveInvariantStep`) live in
`Construction.Effective.LiveInvariantSteps`.  Here they are combined with the analysis of one
controlled strategy response (a trace of fuel units over the coordinates of a game move), then
along the closure of a level, over all levels of a tick, and finally by induction on the tick.
The resulting statement is used by the stability modules of the construction.
-/

namespace Kolmogorov.Milovanov

/-- During a response, only the issuing level may temporarily violate the buffer equations. -/
private def PassiveInvariant (P : FighterParams) (d l : ℕ)
    (s : FighterState) : Prop :=
  ∀ p ∈ s.active, (p.level ≠ l → PhaseRegular d p) ∧
    PhaseBacked P d s.allocated p

/-- Administrative routines only delete phases or change their pending lists, and
any surviving lookup comes from the same earlier lookup. -/
private def AdminStep (d l : ℕ) (s t : FighterState) : Prop :=
  s.allocated ⊆ t.allocated ∧
    (∀ p ∈ t.active, ∃ old ∈ s.active, ∃ pending, p = { old with pending := pending }) ∧
    ∀ p, t.activeAt d l = some p →
      ∃ old, s.activeAt d l = some old ∧ ∃ pending, p = { old with pending := pending }

private lemma AdminStep.refl (d l : ℕ) (s : FighterState) :
    AdminStep d l s s := by
  exact ⟨fun _ h => h, fun p hp => ⟨p, hp, p.pending, rfl⟩,
    fun p hp => ⟨p, hp, p.pending, rfl⟩⟩

private lemma AdminStep.trans (d l : ℕ) {s t u : FighterState}
    (h : AdminStep d l s t) (h' : AdminStep d l t u) :
    AdminStep d l s u := by
  refine ⟨fun _ ha => h'.1 (h.1 ha), ?_, ?_⟩
  · intro p hp
    obtain ⟨mid, hm, pending, rfl⟩ := h'.2.1 p hp
    obtain ⟨old, ho, pending', rfl⟩ := h.2.1 mid hm
    exact ⟨old, ho, pending, rfl⟩
  · intro p hp
    obtain ⟨mid, hm, pending, rfl⟩ := h'.2.2 p hp
    obtain ⟨old, ho, pending', rfl⟩ := h.2.2 mid hm
    exact ⟨old, ho, pending, rfl⟩

private lemma AdminStep.foldl {α : Type} (d l : ℕ)
    (f : FighterState → α → FighterState)
    (hf : ∀ s a, AdminStep d l s (f s a))
    (xs : List α) (s : FighterState) :
    AdminStep d l s (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact AdminStep.refl d l s
  | cons a xs ih => exact AdminStep.trans d l (hf s a) (ih _)

private lemma AdminStep.of_subset_of_active_eq (d l : ℕ) (s t : FighterState)
    (ha : s.allocated ⊆ t.allocated) (hp : t.active = s.active) :
    AdminStep d l s t := by
  refine ⟨ha, ?_, ?_⟩
  · intro p h
    exact ⟨p, hp ▸ h, p.pending, rfl⟩
  · intro p h
    have he : t.activeAt d l = s.activeAt d l := by simp only [FighterState.activeAt, hp]
    exact ⟨p, he ▸ h, p.pending, rfl⟩

private lemma AdminStep.cancel (d l k : ℕ) (reason : PhaseEnd)
    (cause : ℕ) (s : FighterState) :
    AdminStep d l s (fighterCancel d k reason cause s) := by
  unfold fighterCancel
  split
  · exact AdminStep.refl d l s
  · refine ⟨fun _ h => h, ?_, ?_⟩
    · intro p hp
      exact ⟨p, (List.mem_filter.mp hp).1, p.pending, rfl⟩
    · intro p hp
      have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := p) hp
      have hmem := List.mem_of_find?_eq_some hp
      have hne : l ≠ k := by
        have h := (List.mem_filter.mp hmem).2
        simpa only [hlevel, bne_iff_ne] using h
      have he : (s.active.filter (fun p => p.level != k)).find? (fun p => p.level == l) =
          s.active.find? (fun p => p.level == l) := by
        rw [List.find?_filter]
        apply List.find?_congr
        intro p hp
        by_cases h : p.level = l <;> simp [h, hne]
      exact ⟨p, he.symm.trans hp, p.pending, rfl⟩

private lemma AdminStep.abortAbove (d l : ℕ) (s : FighterState) :
    AdminStep d l s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply AdminStep.foldl
  intro t p
  split
  · exact AdminStep.cancel d l p.level .aborted l t
  · exact AdminStep.refl d l t

private lemma AdminStep.allocate (d l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (output : BitString) (s : FighterState) :
    AdminStep d l s (fighterAllocate d l kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact AdminStep.refl d l s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none =>
      dsimp only
      exact AdminStep.trans d l
        (AdminStep.of_subset_of_active_eq d l s { s with failed := true } (fun _ h => h) rfl)
        (AdminStep.cancel d l l .saturated l _)
    | some p =>
      dsimp only
      apply AdminStep.trans d l _ (AdminStep.abortAbove d l _)
      exact AdminStep.of_subset_of_active_eq d l s _
        (fun _ h => List.mem_append_left _ h) rfl

private lemma AdminStep.record (d l : ℕ) (s : FighterState)
    (q : Coordinate) :
    AdminStep d l s
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map
          (fun p => { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨fun _ h => h, ?_, ?_⟩
  · intro p hp
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hp
    exact ⟨old, ho, _, rfl⟩
  · intro p hp
    simp only [FighterState.activeAt, List.find?_map] at hp
    obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact ⟨old, ho, _, rfl⟩

private lemma AdminStep.payoff (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) :
    AdminStep d l s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact AdminStep.refl d l s
  · split
    · have ha := AdminStep.allocate d l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact AdminStep.trans d l ha
            (AdminStep.record d l next q)
    · exact AdminStep.refl d l s

private lemma AdminStep.fulfillReady (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    AdminStep d l s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact AdminStep.refl d l s
  · apply AdminStep.foldl
    intro t q
    exact AdminStep.payoff P d l q t

private lemma PassiveInvariant.of_adminStep (P : FighterParams) (d l : ℕ)
    {s t : FighterState} (h : AdminStep d l s t)
    (hs : PassiveInvariant P d l s) :
    PassiveInvariant P d l t := by
  intro p hp
  obtain ⟨old, ho, pending, rfl⟩ := h.2.1 p hp
  obtain ⟨hr, hb⟩ := hs old ho
  exact ⟨hr, PhaseBacked.mono P d h.1 old hb⟩

/-- Installing a phase of level `l` with backed indices keeps the passive invariant. -/
private lemma PassiveInvariant.putPhase (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (hlevel : p.level = l)
    (hp : PhaseBacked P d s.allocated p)
    (hs : PassiveInvariant P d l s) :
    PassiveInvariant P d l (s.putPhase d p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨fun h => (h hlevel).elim, hp⟩
  · exact hs r (List.mem_filter.mp hr).1

/-- The phase fields used by the final official-position update of a response. -/
def controlledResponseView (p : FighterPhase) :=
  (p.gameCode, p.controlledPlayer, p.opponentRemaining, p.buffer,
    p.liveCounters, p.controlledRemaining)

private lemma exists_allocated_of_fighterAllocate_eq_true (d l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (output : BitString) (s next : FighterState)
    (h : fighterAllocate d l kind target output s = (next, true)) :
    ∃ a ∈ next.allocated, a.output = output ∧ a.input.length + 1 = target := by
  unfold fighterAllocate at h
  split at h
  · simp at h
  · rename_i phase hphase
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none => simp [hf] at h
    | some input =>
      simp only [hf, Prod.mk.injEq, and_true] at h
      subst next
      have ht : target ≠ 0 := by intro ht; simp [ht] at hf
      simp only [ht, ↓reduceIte] at hf
      have hlen := length_eq_of_mem_fighterInputs d (target - 1) input
        (List.mem_of_find?_eq_some hf)
      rw [fighterAbortAbove_allocated]
      refine ⟨AllocatedDirective.mk l phase.candidate s.tick kind target input output,
        List.mem_append_right _ (by simp), rfl, ?_⟩
      dsimp only
      omega

private lemma activeAt_eq_none_of_fighterAllocate_eq_false (d l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (output : BitString) (s next : FighterState)
    (h : fighterAllocate d l kind target output s = (next, false)) :
    next.activeAt d l = none := by
  unfold fighterAllocate at h
  split at h
  · cases h
    assumption
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p =>
          !s.allocated.any (fun a => a.input == p))) with
    | none =>
      simp only [hf, Prod.mk.injEq, and_true] at h
      subst next
      exact activeAt_fighterCancel d l _ .saturated l
    | some input => simp [hf] at h

private lemma passiveInvariant_fighterFuelUnit (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (q : Coordinate)
    (hp : s.activeAt d l = some p) (hq : q ∈ (p.game d).coordinates)
    (hbudget : 0 < p.controlledRemaining) (hs : PassiveInvariant P d l s) :
    s.allocated ⊆ (fighterFuelUnit P d l q s).allocated ∧
      PassiveInvariant P d l (fighterFuelUnit P d l q s) ∧
      ∀ live, (fighterFuelUnit P d l q s).activeAt d l = some live →
        controlledResponseView live = controlledResponseView
          { p with liveCounters := (p.game d).addCounters p.liveCounters (p.unitVector d q)
                   controlledRemaining := p.controlledRemaining - 1 } := by
  have hlevel := FighterState.level_eq_of_activeAt_eq_some (p := p) hp
  have hb := (hs p (List.mem_of_find?_eq_some hp)).2
  let index := fighterFreshString d (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
  let output := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
  let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
  have hc := PassiveInvariant.putPhase P d l s charged hlevel hb hs
  have ha := AdminStep.allocate d l .fuel (levelUpper l + d) output
    (s.putPhase d charged)
  simp only [fighterFuelUnit, hp, ite_eq_left
    (show q ∈ (p.game d).coordinates ∧ 0 < p.controlledRemaining from ⟨hq, hbudget⟩)]
  cases he : fighterAllocate d l .fuel (levelUpper l + d) output (s.putPhase d charged) with
  | mk next success =>
    rw [he] at ha
    cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · refine ⟨ha.1, PassiveInvariant.of_adminStep P d l ha hc, ?_⟩
      intro live hlive
      rw [activeAt_eq_none_of_fighterAllocate_eq_false d l .fuel (levelUpper l + d) output
        (s.putPhase d charged) next he] at hlive
      contradiction
    · let inserted := (charged.insertIndex d q index).fundRequests d next.fulfilled
      have hnewback : PhaseBacked P d next.allocated inserted := by
        apply PhaseBacked.insertIndex P d next.allocated charged q index
          (PhaseBacked.mono P d ha.1 charged hb)
        obtain ⟨a, ham, hao, halen⟩ := exists_allocated_of_fighterAllocate_eq_true d l .fuel
          (levelUpper l + d) output (s.putPhase d charged) next he
        exact Or.inr ⟨a, ham, hao, by simpa only [charged, hlevel] using halen.le⟩
      have hnext := PassiveInvariant.of_adminStep P d l ha hc
      have hput := PassiveInvariant.putPhase P d l next inserted hlevel hnewback hnext
      have hf := AdminStep.fulfillReady P d l (next.putPhase d inserted)
      refine ⟨fun a ham => hf.1 (ha.1 ham),
        PassiveInvariant.of_adminStep P d l hf hput, ?_⟩
      intro live hlive
      obtain ⟨old, hold, pending, rfl⟩ := hf.2.2 live hlive
      rw [FighterState.activeAt_putPhase d l next inserted hlevel] at hold
      cases hold
      rfl

/-- Replay a finite list of unit fuel purchases. -/
def replayFuelUnits (P : FighterParams) (d l : ℕ)
    (commands : List Coordinate) (s : FighterState) : FighterState :=
  commands.foldl (fun s q => fighterFuelUnit P d l q s) s

private lemma replayFuelUnits_of_activeAt_eq_none (P : FighterParams) (d l : ℕ)
    (commands : List Coordinate) (s : FighterState) (hs : s.activeAt d l = none) :
    replayFuelUnits P d l commands s = s := by
  induction commands with
  | nil => rfl
  | cons q commands ih =>
    simpa only [replayFuelUnits, List.foldl_cons, fighterFuelUnit, hs] using ih

/-- The exact cost and counter increments of a surviving unit-purchase trace. -/
private def FuelTraceEffect (d : ℕ) (p live : FighterPhase)
    (commands : List Coordinate) : Prop :=
  live.gameCode = p.gameCode ∧ live.controlledPlayer = p.controlledPlayer ∧
    live.opponentRemaining = p.opponentRemaining ∧ live.buffer = p.buffer ∧
    live.controlledRemaining + commands.length = p.controlledRemaining ∧
    live.liveCounters.length = (p.game d).coordinates.length ∧
    ∀ i (hi : i < (p.game d).coordinates.length),
      live.liveCounters[i]?.getD 0 = p.liveCounters[i]?.getD 0 +
        commands.count ((p.game d).coordinates[i]'hi)

private lemma passiveInvariant_replayFuelUnits (P : FighterParams) (d l : ℕ)
    (commands : List Coordinate) (s : FighterState) (p : FighterPhase)
    (hp : s.activeAt d l = some p)
    (hs : PassiveInvariant P d l s)
    (hlen : p.liveCounters.length = (p.game d).coordinates.length)
    (hcommands : ∀ q ∈ commands, q ∈ (p.game d).coordinates)
    (hbudget : commands.length ≤ p.controlledRemaining) :
    s.allocated ⊆ (replayFuelUnits P d l commands s).allocated ∧
      PassiveInvariant P d l (replayFuelUnits P d l commands s) ∧
      ∀ live, (replayFuelUnits P d l commands s).activeAt d l = some live →
        FuelTraceEffect d p live commands := by
  induction commands generalizing s p with
  | nil =>
    refine ⟨fun _ h => h, hs, ?_⟩
    intro live hlive
    rw [show replayFuelUnits P d l [] s = s from rfl, hp] at hlive
    cases hlive
    exact ⟨rfl, rfl, rfl, rfl, by simp, hlen, by simp⟩
  | cons q commands ih =>
    have hq := hcommands q (by simp)
    have hpos : 0 < p.controlledRemaining := by simp only [List.length_cons] at hbudget; omega
    obtain ⟨ha, hpass, hview⟩ := passiveInvariant_fighterFuelUnit P d l s p q hp hq hpos hs
    change s.allocated ⊆ (replayFuelUnits P d l commands
        (fighterFuelUnit P d l q s)).allocated ∧
      PassiveInvariant P d l (replayFuelUnits P d l commands
        (fighterFuelUnit P d l q s)) ∧
      ∀ live, (replayFuelUnits P d l commands
          (fighterFuelUnit P d l q s)).activeAt d l = some live →
        FuelTraceEffect d p live (q :: commands)
    cases ht : (fighterFuelUnit P d l q s).activeAt d l with
    | none =>
      rw [replayFuelUnits_of_activeAt_eq_none P d l commands _ ht]
      refine ⟨ha, hpass, ?_⟩
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
      obtain ⟨ha', hpass', heffect⟩ := ih _ mid ht hpass hlenmid htail hcost
      refine ⟨fun a ham => ha' (ha ham), hpass', ?_⟩
      intro live hlive
      obtain ⟨hg, hc, ho, hb, hr, hll, hvals⟩ := heffect live hlive
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
          rw [hcounters, FiniteCounterGame.getD_addCounters _ _ _ i hi, hunit]
        by_cases heq : q = (p.game d).coordinates[i]'hi
        · simp only [heq, ite_true] at hmid
          simp only [heq, List.count_cons_self]
          omega
        · simp only [Ne.symm heq, ite_false, Nat.add_zero] at hmid
          rw [List.count_cons_of_ne heq]
          omega

/-- Expand a vector into one command for every unit purchased at each coordinate. -/
def unitCommands (coords : List Coordinate) (move : CounterMove) :
    List Coordinate :=
  (coords.zip move).flatMap (fun qi => List.replicate qi.2 qi.1)

/-- Expanding a vector into coordinate commands preserves its cost and its coordinate
multiplicities. -/
theorem unitCommands_spec (coords : List Coordinate)
    (move : CounterMove) (hnd : coords.Nodup) (hlen : move.length = coords.length) :
    (∀ q ∈ unitCommands coords move, q ∈ coords) ∧
      (unitCommands coords move).length = move.sum ∧
      ∀ i (hi : i < coords.length),
        (unitCommands coords move).count (coords[i]'hi) = move[i]?.getD 0 := by
  induction coords generalizing move with
  | nil =>
    have hm : move = [] := List.eq_nil_iff_length_eq_zero.mpr hlen
    subst move
    simp [unitCommands]
  | cons q coords ih =>
    cases move with
    | nil => simp at hlen
    | cons n move =>
      have htail : move.length = coords.length := by
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨hnq, hndtail⟩ := List.nodup_cons.mp hnd
      obtain ⟨hmem, hlength, hcount⟩ := ih move hndtail htail
      have he : unitCommands (q :: coords) (n :: move) =
          List.replicate n q ++ unitCommands coords move := rfl
      refine ⟨?_, ?_, ?_⟩
      · intro r hr
        rw [he, List.mem_append] at hr
        rcases hr with hr | hr
        · exact List.mem_cons.mpr (Or.inl (List.eq_of_mem_replicate hr))
        · exact List.mem_cons_of_mem q (hmem r hr)
      · simp [he, hlength]
      · intro i hi
        cases i with
        | zero =>
          have hn : q ∉ unitCommands coords move := fun h => hnq (hmem q h)
          simp [he, List.count_append, List.count_eq_zero.mpr hn]
        | succ i =>
          have hi' : i < coords.length := Nat.lt_of_succ_lt_succ hi
          have hne : q ≠ coords[i]'hi' := by
            intro h
            exact hnq (h ▸ List.getElem_mem hi')
          simpa [he, List.count_append, List.count_replicate, hne] using hcount i hi'

/-- Zipping a length-correct vector agrees with lookup by the coordinate indices. -/
theorem zip_eq_map_zipIdx_getD (coords : List Coordinate)
    (move : CounterMove) (hlen : move.length = coords.length) :
    coords.zip move = coords.zipIdx.map (fun qi => (qi.1, move[qi.2]?.getD 0)) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hi'
    have hci : i < coords.length := by simpa [hlen] using hi
    have hmi : i < move.length := by omega
    simp [List.getElem?_eq_getElem hmi]

/-- Repeated unit fuel purchases at one coordinate are a replay of that many unit commands. -/
theorem fighterFuelUnits_eq_replayFuelUnits (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (count : ℕ) (s : FighterState) :
    fighterFuelUnits P d l q count s =
      replayFuelUnits P d l (List.replicate count q) s := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    simpa only [fighterFuelUnits, replayFuelUnits, List.replicate_succ,
      List.foldl_cons] using ih (fighterFuelUnit P d l q s)

/-- A fold of fuel purchases along a counter move replays its expanded unit commands. -/
theorem foldl_fighterFuelUnits_eq_replayFuelUnits (P : FighterParams) (d l : ℕ)
    (coords : List Coordinate) (move : CounterMove) (hlen : move.length = coords.length)
    (s : FighterState) :
    coords.zipIdx.foldl (fun s qi => fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) s =
      replayFuelUnits P d l (unitCommands coords move) s := by
  simp only [replayFuelUnits, unitCommands,
    zip_eq_map_zipIdx_getD coords move hlen, List.flatMap_map, List.foldl_flatMap]
  simp only [fighterFuelUnits_eq_replayFuelUnits, replayFuelUnits]

private lemma passiveInvariant_foldl_fighterFuelUnits (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (move : CounterMove)
    (hp : s.activeAt d l = some p) (hs : FiniteLiveInvariant P d s)
    (hlen : move.length = (p.game d).coordinates.length)
    (hbudget : move.sum ≤ p.controlledRemaining) :
    let next := (p.game d).coordinates.zipIdx.foldl
      (fun s qi => fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) s
    s.allocated ⊆ next.allocated ∧ PassiveInvariant P d l next ∧
      ∀ live, next.activeAt d l = some live →
        controlledResponseView live = controlledResponseView
          { p with liveCounters := (p.game d).addCounters p.liveCounters move
                   controlledRemaining := p.controlledRemaining - move.sum } := by
  dsimp only
  rw [foldl_fighterFuelUnits_eq_replayFuelUnits P d l _ move hlen s]
  obtain ⟨hmem, hlength, hcount⟩ := unitCommands_spec
    (p.game d).coordinates move (nodup_eraseDups_list _) hlen
  have hreg := (FiniteLiveInvariant.of_activeAt_eq_some P d l s p hp hs).1
  have hlive : p.liveCounters.length = (p.game d).coordinates.length := by
    rw [hreg.1.2.1]
    simp [FiniteCounterGame.addCounters]
  have hpass : PassiveInvariant P d l s := by
    intro r hr
    exact ⟨fun _ => (hs r hr).1, (hs r hr).2⟩
  obtain ⟨ha, hpass', heffect⟩ := passiveInvariant_replayFuelUnits P d l
    (unitCommands (p.game d).coordinates move) s p hp hpass hlive hmem
    (by simpa only [hlength] using hbudget)
  refine ⟨ha, hpass', ?_⟩
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
      have hgval := FiniteCounterGame.getD_addCounters (p.game d) p.liveCounters move i hgi
      rw [List.getElem?_eq_getElem hi, Option.getD_some] at hv
      rw [List.getElem?_eq_getElem hi', Option.getD_some] at hgval
      omega
  · rw [hlength] at hr
    omega

private lemma allocated_subset_fighterFuelUnit (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) :
    s.allocated ⊆ (fighterFuelUnit P d l q s).allocated := by
  unfold fighterFuelUnit
  split
  · exact fun _ h => h
  · rename_i phase hphase
    split
    · dsimp only
      have ha := (AdminStep.allocate d l .fuel (levelUpper l + d)
        (pairCode (triple q.1 (q.2 - d) phase.candidate.1)
          (fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])))
        (s.putPhase d { phase with controlledRemaining := phase.controlledRemaining - 1 })).1
      generalize he : fighterAllocate d l .fuel (levelUpper l + d) _ _ = result at *
      rcases result with ⟨next, success⟩
      cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact ha
      · have hf := (AdminStep.fulfillReady P d l
          (next.putPhase d
            (({ phase with controlledRemaining := phase.controlledRemaining - 1 }.insertIndex d q
              (fighterFreshString d
                (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []))).fundRequests d
                next.fulfilled))).1
        exact fun a ham => hf (ha ham)
    · exact fun _ h => h

private lemma allocated_subset_fighterFuelUnits (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (count : ℕ) (s : FighterState) :
    s.allocated ⊆ (fighterFuelUnits P d l q count s).allocated := by
  induction count generalizing s with
  | zero => exact fun _ h => h
  | succ count ih => exact fun a ha => ih _ (allocated_subset_fighterFuelUnit P d l q s ha)

private lemma allocated_subset_foldl_fighterFuelUnits (P : FighterParams) (d l : ℕ)
    (move : CounterMove) (coords : List (Coordinate × ℕ)) (s : FighterState) :
    s.allocated ⊆ (coords.foldl
      (fun s qi => fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) s).allocated := by
  induction coords generalizing s with
  | nil => exact fun _ h => h
  | cons qi coords ih =>
    exact fun a ha => ih _ (allocated_subset_fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s ha)

private lemma FiniteLiveInvariant.of_passive_putPhase (P : FighterParams) (d l : ℕ)
    (s : FighterState) (p : FighterPhase) (hlevel : p.level = l)
    (hp : PhaseRegular d p ∧ PhaseBacked P d s.allocated p)
    (hs : PassiveInvariant P d l s) :
    FiniteLiveInvariant P d (s.putPhase d p) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hp
  · obtain ⟨hrmem, hrne⟩ := List.mem_filter.mp hr
    have hne : r.level ≠ l := by simpa only [hlevel, bne_iff_ne] using hrne
    exact ⟨(hs r hrmem).1 hne, (hs r hrmem).2⟩

private lemma FiniteLiveInvariant.of_passive_of_activeAt_eq_none (P : FighterParams) (d l : ℕ)
    (s : FighterState) (hnone : s.activeAt d l = none)
    (hs : PassiveInvariant P d l s) : FiniteLiveInvariant P d s := by
  intro p hp
  have hne : p.level ≠ l := by
    intro he
    have h := List.find?_eq_none.mp hnone p hp
    simp [he] at h
  exact ⟨(hs p hp).1 hne, (hs p hp).2⟩

private lemma PhaseRegular.of_controlledResponseView_eq (d : ℕ) (p live : FighterPhase)
    (move : CounterMove) (hp : PhaseRegular d p)
    (hbuffer : p.buffer.sum = 0)
    (hactive : (p.game d).activePlayer (p.official d) = p.controlledPlayer)
    (hview : controlledResponseView live = controlledResponseView
      { p with liveCounters := (p.game d).addCounters p.liveCounters move
               controlledRemaining := p.controlledRemaining - move.sum }) :
    PhaseRegular d
      { live with officialCode := ((p.game d).afterMove (p.official d) move).encode } := by
  obtain ⟨⟨hc, hv, hl, hr⟩, hbuflen, hcountlen⟩ := hp
  simp only [controlledResponseView, Prod.mk.injEq] at hview
  obtain ⟨hg, hctrl, hop, hbuf, hcounters, hremaining⟩ := hview
  have hgame : live.game d = p.game d := congrArg decodeCounterGame hg
  have hactive' : (p.game d).activePlayer (p.official d) = false := hactive.trans hc
  have hzero : p.buffer = List.replicate (p.game d).coordinates.length 0 := by
    rw [← hbuflen]
    apply List.eq_replicate_length.mpr
    exact List.sum_eq_zero_iff_forall_eq_nat.mp hbuffer
  have hlive : p.liveCounters = (p.official d).counters := by
    rw [hv, hzero, FiniteCounterGame.addCounters_replicate_zero _ _ hcountlen]
  change (live.controlledPlayer = false ∧ live.liveCounters =
        (live.game d).addCounters
          (decodeCounterPosition (live.game d)
            ((p.game d).afterMove (p.official d) move).encode).counters live.buffer ∧
      (decodeCounterPosition (live.game d)
          ((p.game d).afterMove (p.official d) move).encode).leftBudget =
        live.controlledRemaining ∧
      (decodeCounterPosition (live.game d)
          ((p.game d).afterMove (p.official d) move).encode).rightBudget =
        live.opponentRemaining + live.buffer.sum) ∧
    live.buffer.length = (live.game d).coordinates.length ∧
    (decodeCounterPosition (live.game d)
      ((p.game d).afterMove (p.official d) move).encode).counters.length =
        (live.game d).coordinates.length
  rw [hgame, decode_encode_counter_position]
  have hlen : ((p.game d).afterMove (p.official d) move).counters.length =
      (p.game d).coordinates.length := by
    simp [FiniteCounterGame.afterMove, FiniteCounterGame.addCounters]
  rw [hctrl, hc, hbuf, hzero, FiniteCounterGame.addCounters_replicate_zero _ _ hlen]
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, by simp, hlen⟩
  · simpa only [FiniteCounterGame.afterMove, hlive] using hcounters
  · simpa [FiniteCounterGame.afterMove, hactive', hl] using hremaining.symm
  · simp [FiniteCounterGame.afterMove, hactive', hop, hr, hbuffer]

/-- One atomic controlled strategy response preserves finite backing and the official/live
equations, including vector lengths. Each successful fuel unit adds its allocated graph
witness before inserting the index; failure cancels without reinsertion. If the phase
survives all coordinate batches, the installed official child records exactly the purchased
move and its cost. This is only one response, without event processing or action closure. -/
private theorem LiveInvariantStep.strategyMove (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s ((fighterStrategyMove P d l s).getD s) := by
  cases hp : s.activeAt d l with
  | none => simpa [fighterStrategyMove, hp] using LiveInvariantStep.refl P d s
  | some p =>
    simp only [fighterStrategyMove, hp, bind, Option.bind_some]
    split
    · rename_i hguard
      cases hm : (p.game d).strategy (p.official d) with
      | none =>
        simpa only [Option.bind_none, Option.getD_none] using LiveInvariantStep.refl P d s
      | some move =>
        simp only [Option.bind_some]
        split
        · rename_i hlegal
          let next := (p.game d).coordinates.zipIdx.foldl
            (fun s qi => fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) s
          have hmono := allocated_subset_foldl_fighterFuelUnits P d l move
            (p.game d).coordinates.zipIdx s
          change LiveInvariantStep P d s
            ((match next.activeAt d l with
              | none => some next
              | some live => some (next.putPhase d
                  { live with
                    officialCode := ((p.game d).afterMove (p.official d) move).encode })).getD s)
          cases hn : next.activeAt d l with
          | none =>
            refine ⟨hmono, ?_⟩
            intro hinv
            obtain ⟨_, hpass, _⟩ := passiveInvariant_foldl_fighterFuelUnits P d l s p move hp hinv
              hlegal.1.1 hlegal.2
            exact FiniteLiveInvariant.of_passive_of_activeAt_eq_none P d l next hn hpass
          | some live =>
            refine ⟨hmono, ?_⟩
            intro hinv
            obtain ⟨_, hpass, hviews⟩ := passiveInvariant_foldl_fighterFuelUnits P d l s p move
              hp hinv hlegal.1.1 hlegal.2
            have hview := hviews live hn
            have hreg := PhaseRegular.of_controlledResponseView_eq d p live move
              (FiniteLiveInvariant.of_activeAt_eq_some P d l s p hp hinv).1 hguard.2.1
              hguard.2.2 hview
            have hback := (hpass live (List.mem_of_find?_eq_some hn)).2
            exact FiniteLiveInvariant.of_passive_putPhase P d l next _
              (FighterState.level_eq_of_activeAt_eq_some (p := live) hn) ⟨hreg, hback⟩ hpass
        · exact LiveInvariantStep.refl P d s
    · exact LiveInvariantStep.refl P d s

private lemma LiveInvariantStep.levelAction (P : FighterParams) (d l : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s ((fighterLevelAction P d l s).getD s) := by
  cases hs : s.activeAt d l with
  | none => simpa [fighterLevelAction, hs] using LiveInvariantStep.refl P d s
  | some phase =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some]
    split
    · exact LiveInvariantStep.dummy P d l s
    · split
      · exact LiveInvariantStep.payoff P d l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact LiveInvariantStep.strategyMove P d l s
        | some next =>
          have h := LiveInvariantStep.flushBuffer P d l s
          simpa only [hf] using h

private lemma LiveInvariantStep.closure (P : FighterParams) (d l fuel : ℕ)
    (s : FighterState) :
    LiveInvariantStep P d s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact LiveInvariantStep.refl P d s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact LiveInvariantStep.refl P d s
    | some next =>
      have hn := LiveInvariantStep.levelAction P d l s
      simp only [ha, Option.getD_some] at hn
      exact LiveInvariantStep.trans P d hn (ih next)

private lemma LiveInvariantStep.processLevel (P : FighterParams) (d l : ℕ)
    (event : Option TimedEvent) (s : FighterState)
    (hevent : ∀ e, event = some e → produces P.B.V e.2.2.1 [] e.2.2.2) :
    LiveInvariantStep P d s (fighterProcessLevel P d l event s) := by
  unfold fighterProcessLevel
  apply LiveInvariantStep.trans P d (LiveInvariantStep.fulfillReady P d l s)
  cases event with
  | none => exact LiveInvariantStep.closure P d l _ _
  | some e =>
    dsimp only
    split
    · exact LiveInvariantStep.trans P d
        (LiveInvariantStep.startPhase P d l _ _)
        (LiveInvariantStep.closure P d l _ _)
    · exact LiveInvariantStep.trans P d
        (LiveInvariantStep.opponent P d l _ _ (hevent e rfl))
        (LiveInvariantStep.closure P d l _ _)

private lemma LiveInvariantStep.actions (P : FighterParams) (d tick : ℕ)
    (s : FighterState) (hd : 1 ≤ d) :
    LiveInvariantStep P d s (fighter_actions P d tick s) := by
  unfold fighter_actions
  simp only [show d ≠ 0 by omega, ↓reduceIte]
  apply LiveInvariantStep.trans P d
    (LiveInvariantStep.of_subset_of_active_eq P d s
      { s with tick := tick, schedule := masterState P.B tick } (fun _ h => h) rfl)
  apply LiveInvariantStep.foldl
  intro t l
  apply LiveInvariantStep.processLevel P d l _ t
  intro e he
  exact (canonical_enumeration_spec_sound P.B he).2

private lemma finiteLiveInvariant_fighterState (P : FighterParams) (d tick : ℕ)
    (hd : 1 ≤ d) : FiniteLiveInvariant P d (fighterState P d tick) := by
  induction tick with
  | zero => simp [FiniteLiveInvariant, fighterState, initialFighterState]
  | succ tick ih => exact (LiveInvariantStep.actions P d (tick + 1) _ hd).2 ih

/-- Successful allocations are permanent: the allocation graph only grows with the tick. -/
theorem fighterState_allocated_subset_of_le (P : FighterParams) (d : ℕ) (hd : 1 ≤ d)
    (tick later : ℕ) (hle : tick ≤ later) :
    (fighterState P d tick).allocated ⊆ (fighterState P d later).allocated := by
  induction later, hle using Nat.le_induction with
  | base => exact fun _ h => h
  | succ later hle ih =>
    intro a ha
    exact (LiveInvariantStep.actions P d (later + 1) _ hd).1 (ih ha)

private lemma find?_input_eq_some_of_nodup (as : List AllocatedDirective)
    (hnd : (as.map AllocatedDirective.input).Nodup) (a : AllocatedDirective) (ha : a ∈ as) :
    as.find? (fun b => b.input == a.input) = some a := by
  cases hf : as.find? (fun b => b.input == a.input) with
  | none =>
    have h := List.find?_eq_none.mp hf a ha
    simp at h
  | some b =>
    have hb := List.mem_of_find?_eq_some hf
    have heq : b.input = a.input := beq_iff_eq.mp
      (List.find?_some (p := fun b : AllocatedDirective => b.input == a.input) hf)
    have heq' : b = a := List.inj_on_of_nodup_map hnd hb ha heq
    subst b
    rfl

/-- A permanent allocation at any completed tick is an actual output of the
first-allocation search.
Allocation persistence and injectivity ensure that an earlier successful lookup of
the same input has exactly this output. This statement concerns graph realization
only, without any phase, index, game, or buffer invariant. -/
theorem output_mem_fighterG_of_mem_allocated (P : FighterParams) (d tick : ℕ)
    (hd : 1 ≤ d) (a : AllocatedDirective) (ha : a ∈ (fighterState P d tick).allocated) :
    a.output ∈ fighterG P d a.input := by
  have hlookup : fighterAllocationAt P d tick a.input = some a.output := by
    simp only [fighterAllocationAt, find?_input_eq_some_of_nodup _
      (fighter_allocations_injective P d tick) a ha, Option.map_some]
  have hex : (fighterAllocationAt P d tick a.input).isSome := by simp [hlookup]
  obtain ⟨first, hfirst, hle⟩ := Nat.rfind_min'
    (p := fun t => (fighterAllocationAt P d t a.input).isSome) hex
  have hspec := Nat.rfind_spec hfirst
  cases hf : fighterAllocationAt P d first a.input with
  | none => simp [hf] at hspec
  | some y =>
    obtain ⟨b, hb, hout⟩ := Option.map_eq_some_iff.mp hf
    have hbmem := List.mem_of_find?_eq_some hb
    have hinput : b.input = a.input := beq_iff_eq.mp
      (List.find?_some (p := fun b : AllocatedDirective => b.input == a.input) hb)
    have hbnow := fighterState_allocated_subset_of_le P d hd first tick hle hbmem
    have hba : b = a := List.inj_on_of_nodup_map
      (fighter_allocations_injective P d tick) hbnow ha hinput
    have hy : y = a.output := by simpa [hba] using hout.symm
    rw [fighterG]
    simp only [show d ≠ 0 by omega, ↓reduceIte]
    apply Part.mem_bind_iff.mpr
    refine ⟨first, hfirst, ?_⟩
    apply Part.mem_ofOption.mpr
    simpa [hy] using hf

/-- Live indices stay backed and the official/live buffer equations hold after each tick.
Blueprint node `constr:effective`. The statement applies to false candidates and small
guarded members as well as the eventual true-marker phase. -/
theorem fighter_live_invariants (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d) :
    ∀ phase ∈ (fighterState P d tick).active,
      phase.BufferInvariant d ∧ phase.Backed P d := by
  intro phase hp
  obtain ⟨hreg, hback⟩ := finiteLiveInvariant_fighterState P d tick hd phase hp
  refine ⟨hreg.1, ?_⟩
  intro q hq index hi
  rcases hback q hq index hi with hbase | ⟨a, ha, ho, hl⟩
  · obtain ⟨p, hplen, hprod⟩ := (simple_iff_exists_program _ _ _).mp hbase
    apply (simple_iff_exists_program _ _ _).mpr
    refine ⟨List.replicate d false ++ p, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]
      omega
    · simpa [produces, fighterU, constructed_conditional_machine] using hprod
  · apply (simple_iff_exists_program _ _ _).mpr
    refine ⟨true :: a.input, by simpa [List.length_cons] using hl, ?_⟩
    have hg := output_mem_fighterG_of_mem_allocated P d tick hd a ha
    cases d with
    | zero => omega
    | succ d =>
      simpa [produces, fighterU, constructed_conditional_machine, List.replicate_succ,
        ho] using hg

/-- The initial base-only counters coincide with the frozen stage-3 adapter.
Blueprint node `constr:effective`. Earlier allocated directives are an additional
union of indices, not a replacement for or a duplicate charge of the `V` table. -/
private lemma card_fighterInitialIndices_nil (P : FighterParams)
    (d l : ℕ) (candidate : Candidate) (q : Coordinate) :
    (fighterInitialIndices P d l candidate [] q).toFinset.card =
      pastExtensionCount P.B (levelScale l) candidate (levelScale l)
        (triple q.1 (q.2 - d) candidate.1) := by
  dsimp [fighterInitialIndices, pastExtensionCount]
  set base := triple q.1 (q.2 - d) candidate.1
  have h1 : validCandidate P.B (levelScale l) candidate = true ∨
      validCandidate P.B (levelScale l) candidate = false := by
    cases h : validCandidate P.B (levelScale l) candidate
    · right; rfl
    · left; rfl
  cases h1
  · case inl ht =>
    simp only [pastExtensionIndices, ht, ite_true, List.append_nil]
    have h2 : (((stageOutputList P.B (levelUpper l) candidate.2).map decodeSecond).filter
      (fun s => decide (s ∈ Finset.image decodeSecond
        ((stageOutputs P.B (extensionScale (levelScale l)) candidate.2).filter
          (fun output => pairCode base (decodeSecond output) = output))))).eraseDups.toFinset =
      Finset.image decodeSecond
        ((stageOutputs P.B (extensionScale (levelScale l)) candidate.2).filter
          (fun output => pairCode base (decodeSecond output) = output)) := by
      ext a
      simp only [List.mem_toFinset, Kolmogorov.mem_eraseDups_list, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · intro h
        exact h.2
      · intro h
        refine ⟨?_, h⟩
        have h3 := mem_past_extension_indices P.B (levelScale l) candidate (levelScale l) base a ht
        simp only [pastExtensionIndices, ht, ite_true] at h3
        have h4 := h3.mp h
        have h5 : levelUpper l = extensionScale (levelScale l) := level_upper_eq l |>.symm
        rw [← h5] at h4
        have h6 : pairCode base a ∈ stageOutputList P.B (levelUpper l) candidate.2 := by
          have h7 : (stageOutputList P.B (levelUpper l) candidate.2).toFinset =
              stageOutputs P.B (levelUpper l) candidate.2 := rfl
          rw [← h7] at h4
          exact List.mem_toFinset.mp h4
        have h8 : decodeSecond (pairCode base a) ∈
            (stageOutputList P.B (levelUpper l) candidate.2).map decodeSecond := by
          apply List.mem_map_of_mem
          exact h6
        have h9 : decodeSecond (pairCode base a) = a := decodeSecond_pairCode base a
        rwa [h9] at h8
    have h2_card : (((stageOutputList P.B (levelUpper l) candidate.2).map decodeSecond).filter
      (fun s => decide (s ∈ Finset.image decodeSecond
        ((stageOutputs P.B (extensionScale (levelScale l)) candidate.2).filter
          (fun output => pairCode base (decodeSecond output) = output))))).eraseDups.toFinset.card =
      (Finset.image decodeSecond
        ((stageOutputs P.B (extensionScale (levelScale l)) candidate.2).filter
          (fun output => pairCode base (decodeSecond output) = output))).card := by
      rw [h2]
    exact h2_card
  · case inr hf =>
    simp only [pastExtensionIndices, hf]
    simp

/-- The counters of the base-only initial indices over a coordinate list are the base counters
of the frozen stage-3 adapter. -/
theorem fighter_initial_base_counters (P : FighterParams) (d l : ℕ) (candidate : Candidate)
    (coords : List Coordinate) :
    coords.eraseDups.map (fun q => (fighterInitialIndices P d l candidate [] q).toFinset.card) =
      coordinateBaseCounters P.B (levelScale l) d candidate coords := by
  dsimp [coordinateBaseCounters]
  apply List.map_congr_left
  intro q hq
  exact card_fighterInitialIndices_nil P d l candidate q

end Kolmogorov.Milovanov
