/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferInitialization

/-!
# Lower phases survive the processing of higher levels

At each tick the fighter construction processes the active levels in increasing order
(`fighterProcessLevel`).  Servicing a level `j` may change the permanent tables and the phases at
levels above `j`, but a phase at a lower level `l < j` is never restarted, cancelled or advanced:
the only field that can change is its list of pending requests, which shrinks when a request is
paid off.

This module proves that fact action by action, up to `fighterProcessLevel`, and then for a fold
of `fighterProcessLevel` over any list of levels above `l`
(`activeAt_foldl_fighterProcessLevel`).  It also proves
`exists_fighterState_eq_foldl_fighterProcessLevel`, which splits the traversal of the active
levels at one tick into the part up to the level `l` and a fold over the strictly larger levels.
Both are used in `Construction.Stability.CommonGame` to follow a true-marker phase through the
event at its marker tick.
-/

namespace Kolmogorov.Milovanov

/-- The level-`l` phase of `t` is the level-`l` phase of `s` up to its `pending` list: if it is
active in `s`, it is active in `t` with every field except `pending` unchanged. -/
private def PendingOnlyChange (d l : ℕ) (s t : FighterState) : Prop :=
  ∀ old, s.activeAt d l = some old →
    ∃ pending, t.activeAt d l = some { old with pending := pending }

section PendingOnlyChange

variable {P : FighterParams} {d j l : ℕ}

private lemma PendingOnlyChange.refl {s : FighterState} : PendingOnlyChange d l s s :=
  fun old hold ↦ ⟨old.pending, hold⟩

private lemma PendingOnlyChange.trans {s t u : FighterState} (h₁ : PendingOnlyChange d l s t)
    (h₂ : PendingOnlyChange d l t u) : PendingOnlyChange d l s u := by
  intro old hold
  obtain ⟨p₁, hp₁⟩ := h₁ old hold
  obtain ⟨p₂, hp₂⟩ := h₂ _ hp₁
  exact ⟨p₂, hp₂⟩

private lemma PendingOnlyChange.of_activeAt_eq {s t : FighterState}
    (h : t.activeAt d l = s.activeAt d l) : PendingOnlyChange d l s t :=
  fun old hold ↦ ⟨old.pending, h.trans hold⟩

private lemma PendingOnlyChange.foldl {α : Type} (f : α → FighterState → FighterState)
    (xs : List α) (hf : ∀ a ∈ xs, ∀ s, PendingOnlyChange d l s (f a s)) (s : FighterState) :
    PendingOnlyChange d l s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact .refl
  | cons a xs ih =>
    exact (hf a (List.mem_cons_self ..) s).trans
      (ih (fun b hb ↦ hf b (List.mem_cons_of_mem a hb)) _)

/-- Writing a phase of level `j` does not change the phase at a lower level `l`. -/
private lemma activeAt_putPhase_of_lt {s : FighterState} {phase : FighterPhase}
    (hphase : phase.level = j) (hjl : l < j) :
    (s.putPhase d phase).activeAt d l = s.activeAt d l :=
  FighterState.activeAt_putPhase_of_ne d l s phase (by omega)

/-- Allocating at level `j` does not change the phase at a lower level `l`. -/
private lemma activeAt_fighterAllocate_of_lt {kind : DirectiveKind} {target : ℕ}
    {output : BitString} {s : FighterState} (hjl : l < j) :
    (fighterAllocate d j kind target output s).1.activeAt d l = s.activeAt d l := by
  unfold fighterAllocate
  split
  · rfl
  · dsimp only
    cases (if target = 0 then none else
        (fighterInputs d (target - 1)).find? (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)))
    · exact activeAt_fighterCancel_eq_of_ne _ _ _ _ _ _ hjl.ne'
    · exact activeAt_fighterAbortAbove_of_le _ _ _ _ hjl.le

/-- Shape of the work after an allocation attempt at level `j`: the allocator leaves the lower
phase alone, so only the follow-up `r` done on success needs checking. -/
private lemma pendingOnlyChange_ite_allocate {e : FighterState × Bool} {s r : FighterState}
    (he : e.1.activeAt d l = s.activeAt d l)
    (hr : e.2 = true → PendingOnlyChange d l s e.1 → PendingOnlyChange d l s r) :
    PendingOnlyChange d l s (if e.2 = true then r else e.1) := by
  split
  · exact hr ‹_› (.of_activeAt_eq he)
  · exact .of_activeAt_eq he

/-- Recording the payment of `q`, which removes `q` from every pending list, changes the lower
phase at most in its pending list. -/
private lemma pendingOnlyChange_record_payment {s t : FighterState} (q : Coordinate)
    (h : PendingOnlyChange d l s t) :
    PendingOnlyChange d l s { t with
      fulfilled := t.fulfilled ++ [q]
      active := t.active.map
        (fun p ↦ { p with pending := p.pending.filter (fun r ↦ r != q) }) } := by
  intro old hold
  obtain ⟨pending, hp⟩ := h old hold
  refine ⟨pending.filter (fun r ↦ r != q), ?_⟩
  simp only [FighterState.activeAt, List.find?_map] at hp ⊢
  change Option.map _ (t.active.find? (fun p ↦ p.level == l)) = _
  rw [hp]
  rfl

private lemma fighterPayoff_pendingOnlyChange {q : Coordinate} {s : FighterState}
    (hjl : l < j) : PendingOnlyChange d l s (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact .refl
  · split
    · exact pendingOnlyChange_ite_allocate (activeAt_fighterAllocate_of_lt hjl)
        fun _ ha ↦ pendingOnlyChange_record_payment q ha
    · exact .refl

private lemma fighterFulfillReady_pendingOnlyChange {s : FighterState} (hjl : l < j) :
    PendingOnlyChange d l s (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact .refl
  · exact PendingOnlyChange.foldl (fun q t ↦ fighterPayoff P d j q t) _
      (fun _ _ _ ↦ fighterPayoff_pendingOnlyChange hjl) s

private lemma fighterStartPhase_pendingOnlyChange {candidate : Candidate} {s : FighterState}
    (hjl : l < j) : PendingOnlyChange d l s (fighterStartPhase P d j candidate s) := by
  refine .of_activeAt_eq ?_
  unfold fighterStartPhase
  refine (activeAt_putPhase_of_lt (j := j) ?_ hjl).trans
    ((activeAt_fighterAbortAbove_of_le _ _ _ _ hjl.le).trans
      (activeAt_fighterCancel_eq_of_ne _ _ _ _ _ _ hjl.ne'))
  unfold fighter_construction
  rfl

private lemma fighterOpponent_pendingOnlyChange {event : ProgramEvent} {s : FighterState}
    (hjl : l < j) : PendingOnlyChange d l s (fighterOpponent P d j event s) := by
  unfold fighterOpponent
  split
  · exact .refl
  · next phase hphase =>
    have hlevel := FighterState.level_eq_of_activeAt_eq_some hphase
    split
    · exact .refl
    · split
      · exact .refl
      · split
        · exact .of_activeAt_eq (activeAt_fighterCancel_eq_of_ne _ _ _ _ _ _ hjl.ne')
        · refine (PendingOnlyChange.of_activeAt_eq
            (activeAt_putPhase_of_lt ?_ hjl)).trans (fighterFulfillReady_pendingOnlyChange hjl)
          exact hlevel

private lemma fighterDummy_pendingOnlyChange {s : FighterState} (hjl : l < j) :
    PendingOnlyChange d l s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact .refl
  · next phase hphase =>
    have hlevel := FighterState.level_eq_of_activeAt_eq_some hphase
    split
    · exact .refl
    · split
      · exact .refl
      · refine pendingOnlyChange_ite_allocate (activeAt_fighterAllocate_of_lt hjl)
          fun _ ha ↦ ha.trans (.of_activeAt_eq (activeAt_putPhase_of_lt ?_ hjl))
        exact hlevel

private lemma fighterFlushBuffer_pendingOnlyChange {s t : FighterState} (hjl : l < j)
    (h : fighterFlushBuffer d j s = some t) : PendingOnlyChange d l s t := by
  unfold fighterFlushBuffer at h
  cases hphase : s.activeAt d j with
  | none => simp [hphase] at h
  | some phase =>
    have hlevel := FighterState.level_eq_of_activeAt_eq_some hphase
    simp only [hphase, bind, Option.bind_some] at h
    split at h
    · cases h
      refine .of_activeAt_eq (activeAt_putPhase_of_lt ?_ hjl)
      exact hlevel
    · cases h

private lemma fighterFuelUnit_pendingOnlyChange {q : Coordinate} {s : FighterState}
    (hjl : l < j) : PendingOnlyChange d l s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact .refl
  · next phase hphase =>
    have hlevel := FighterState.level_eq_of_activeAt_eq_some hphase
    dsimp only
    split
    · refine .trans (t := s.putPhase d
        { phase with controlledRemaining := phase.controlledRemaining - 1 })
        (.of_activeAt_eq (activeAt_putPhase_of_lt ?_ hjl)) ?_
      · exact hlevel
      refine pendingOnlyChange_ite_allocate (activeAt_fighterAllocate_of_lt hjl) fun _ ha ↦ ?_
      refine ha.trans ((PendingOnlyChange.of_activeAt_eq
        (activeAt_putPhase_of_lt ?_ hjl)).trans (fighterFulfillReady_pendingOnlyChange hjl))
      exact hlevel
    · exact .refl

private lemma fighterFuelUnits_pendingOnlyChange {q : Coordinate} (count : ℕ)
    {s : FighterState} (hjl : l < j) :
    PendingOnlyChange d l s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact .refl
  | succ count ih =>
    unfold fighterFuelUnits
    exact (fighterFuelUnit_pendingOnlyChange hjl).trans ih

private lemma fighterStrategyMove_pendingOnlyChange {s t : FighterState} (hjl : l < j)
    (h : fighterStrategyMove P d j s = some t) : PendingOnlyChange d l s t := by
  unfold fighterStrategyMove at h
  cases hphase : s.activeAt d j with
  | none => simp [hphase] at h
  | some phase =>
    simp only [hphase, bind, Option.bind_some] at h
    split at h
    · cases hstrat : (phase.game d).strategy (phase.official d) with
      | none => simp [hstrat] at h
      | some move =>
        simp only [hstrat, Option.bind_some] at h
        split at h
        · have hfold := PendingOnlyChange.foldl (d := d) (l := l)
            (fun (qi : Coordinate × ℕ) u ↦ fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) u)
            (phase.game d).coordinates.zipIdx
            (fun _ _ _ ↦ fighterFuelUnits_pendingOnlyChange _ hjl) s
          split at h
          · cases h
            exact hfold
          · rename_i live hlive
            have hlevel := FighterState.level_eq_of_activeAt_eq_some hlive
            cases h
            refine hfold.trans (.of_activeAt_eq (activeAt_putPhase_of_lt ?_ hjl))
            exact hlevel
        · cases h
    · cases h

private lemma fighterLevelAction_pendingOnlyChange {s t : FighterState} (hjl : l < j)
    (h : fighterLevelAction P d j s = some t) : PendingOnlyChange d l s t := by
  unfold fighterLevelAction at h
  cases hphase : s.activeAt d j with
  | none => simp [hphase] at h
  | some phase =>
    simp only [hphase, bind, Option.bind] at h
    split at h
    · cases h
      exact fighterDummy_pendingOnlyChange hjl
    · split at h
      · cases h
        exact fighterPayoff_pendingOnlyChange hjl
      · split at h
        · rename_i next hflush
          cases h
          exact fighterFlushBuffer_pendingOnlyChange hjl hflush
        · exact fighterStrategyMove_pendingOnlyChange hjl h

private lemma fighterClosure_pendingOnlyChange (fuel : ℕ) {s : FighterState} (hjl : l < j) :
    PendingOnlyChange d l s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl
  | succ fuel ih =>
    simp only [fighterClosure]
    cases h : fighterLevelAction P d j s with
    | none => exact .refl
    | some t => exact (fighterLevelAction_pendingOnlyChange hjl h).trans ih

private lemma fighterProcessLevel_pendingOnlyChange {event : Option TimedEvent}
    {s : FighterState} (hjl : l < j) :
    PendingOnlyChange d l s (fighterProcessLevel P d j event s) := by
  unfold fighterProcessLevel fighterCloseLevel
  dsimp only
  refine .trans ?_ (fighterClosure_pendingOnlyChange _ hjl)
  have hready : PendingOnlyChange d l s (fighterFulfillReady P d j s) :=
    fighterFulfillReady_pendingOnlyChange hjl
  cases event with
  | none => exact hready
  | some e =>
    dsimp only
    split
    · exact hready.trans (fighterStartPhase_pendingOnlyChange hjl)
    · exact hready.trans (fighterOpponent_pendingOnlyChange hjl)

end PendingOnlyChange

/-- Processing any list of levels strictly above `l` leaves an active level-`l` phase unchanged
except possibly for its pending list. -/
lemma activeAt_foldl_fighterProcessLevel (P : FighterParams) (d l : ℕ) (event : Option TimedEvent)
    (levels : List ℕ) (state : FighterState) (hlevels : ∀ j ∈ levels, l < j) :
    ∀ old, state.activeAt d l = some old →
      ∃ next,
        (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) state).activeAt d l =
            some next ∧
          ∃ pending, next = { old with pending := pending } := by
  intro old hold
  obtain ⟨pending, hp⟩ := PendingOnlyChange.foldl (d := d) (l := l)
    (fun j s ↦ fighterProcessLevel P d j event s) levels
    (fun j hj _ ↦ fighterProcessLevel_pendingOnlyChange (hlevels j hj)) state old hold
  exact ⟨_, hp, pending, rfl⟩

private lemma pairwise_lt_mergeSort {xs : List ℕ} (hxs : xs.Nodup) :
    (xs.mergeSort (· ≤ ·)).Pairwise (· < ·) := by
  have hle := List.pairwise_mergeSort' (· ≤ ·) xs
  have hne : (xs.mergeSort (· ≤ ·)).Nodup := by rwa [List.nodup_mergeSort]
  exact (hle.and hne).imp fun h ↦ lt_of_le_of_ne h.1 h.2

/-- A strictly increasing list containing `l` splits into the entries below `l`, then `l`. -/
private lemma exists_eq_takeWhile_append_cons {l : ℕ} {xs : List ℕ} (hs : xs.Pairwise (· < ·))
    (hm : l ∈ xs) : ∃ tail, xs = xs.takeWhile (· < l) ++ l :: tail := by
  induction xs with
  | nil => simp at hm
  | cons j xs ih =>
    by_cases hj : j = l
    · subst j
      exact ⟨xs, by simp⟩
    · have hm' : l ∈ xs := (List.mem_cons.mp hm).resolve_left (Ne.symm hj)
      have hlt : j < l := (List.pairwise_cons.mp hs).1 l hm'
      obtain ⟨tail, ht⟩ := ih (List.pairwise_cons.mp hs).2 hm'
      refine ⟨tail, ?_⟩
      simpa [List.takeWhile_cons, hlt] using congrArg (List.cons j) ht

/-- If level `l` is active after the closure of its own level work at tick `tick + 1`, then the
state at that tick is obtained from the closed state by processing a list of levels strictly
above `l`: the levels are traversed in increasing order, and the part up to `l` is exactly what
`fighterBeforeClosure` and `fighterCloseLevel` compute. -/
lemma exists_fighterState_eq_foldl_fighterProcessLevel (P : FighterParams) (d l tick : ℕ)
    (hd : 0 < d) (closePhase : FighterPhase)
    (hclose : (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l)).activeAt d l =
      some closePhase) :
    ∃ (levels : List ℕ), (∀ j ∈ levels, l < j) ∧
      fighterState P d (tick + 1) =
        levels.foldl (fun s j ↦ fighterProcessLevel P d j (eventAt P.B (tick + 1)) s)
          (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l)) := by
  let before := fighterBeforeClosure P d (tick + 1) l
  have hbefore : ∃ p, before.activeAt d l = some p := by
    cases hb : before.activeAt d l with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have hc : (fighterCloseLevel P d l before).activeAt d l = some closePhase := hclose
      simp [fighterCloseLevel, fighterClosureFuel, hb, fighterClosure] at hc
  let current : FighterState :=
    { fighterState P d ((tick + 1) - 1) with
      tick := tick + 1, schedule := masterState P.B (tick + 1) }
  let event := eventAt P.B (tick + 1)
  let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
  let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
  let traversal := levels.mergeSort (· ≤ ·)
  have hevent : ∀ e, event = some e → e.1 = tick + 1 := by
    intro e he
    dsimp [event, eventAt] at he
    rw [Option.filter_eq_some_iff] at he
    exact of_decide_eq_true he.2
  have hsupport (ls : List ℕ) (hls : ∀ j ∈ ls, j ∈ levels)
      (s : FighterState) (ht : s.tick = tick + 1)
      (hs : ∀ p ∈ s.active, p.level ∈ levels) :
      (ls.foldl (fun s j ↦ fighterProcessLevel P d j event s) s).tick = tick + 1 ∧
      ∀ p ∈ (ls.foldl (fun s j ↦ fighterProcessLevel P d j event s) s).active,
        p.level ∈ levels := by
    induction ls generalizing s with
    | nil => exact ⟨ht, hs⟩
    | cons j ls ih =>
      have hj := fighterProcessLevel_preserves_active P d j event s
        (fun level _ _ _ ↦ level ∈ levels)
        (fun e he ↦ (hevent e he).trans ht.symm)
        (fun _ _ _ ↦ hls j (by simp)) hs
      exact ih (fun k hk ↦ hls k (List.mem_cons_of_mem j hk)) _ (hj.1.trans ht) hj.2
  have hpref : ∀ p ∈ (fighterBeforeLevel P d (tick + 1) l).active, p.level ∈ levels := by
    apply (hsupport (traversal.takeWhile (· < l)) ?_ current rfl ?_).2
    · intro j hj
      have hm := List.takeWhile_subset (fun j ↦ decide (j < l)) hj
      simpa only [traversal, List.mem_mergeSort] using hm
    · intro p hp
      exact List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inl (List.mem_map_of_mem hp)))
  have hmem : l ∈ levels := by
    obtain ⟨p, hp⟩ := hbefore
    have hprior (old : FighterPhase)
        (ho : (fighterBeforeLevel P d (tick + 1) l).activeAt d l = some old) : l ∈ levels := by
      have hl : old.level = l :=
        beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) ho)
      simpa only [hl] using hpref old (List.mem_of_find?_eq_some ho)
    cases he : eventAt P.B (tick + 1) with
    | none =>
      cases ho : (fighterBeforeLevel P d (tick + 1) l).activeAt d l with
      | none =>
        have hn : before.activeAt d l = none := by
          simp [before, fighterBeforeClosure, he, fighterFulfillReady, ho]
        rw [hn] at hp
        contradiction
      | some old => exact hprior old ho
    | some e =>
      by_cases hstart : fighterOwner d e.2.2.1.length = some l ∧
          e.2.2.1.length ≤ levelScale l ∧ P.Admissible d l
      · apply List.mem_eraseDups.mpr
        apply List.mem_append.mpr
        right
        simp [owner, event, he, hstart.1]
      · cases ho : (fighterBeforeLevel P d (tick + 1) l).activeAt d l with
        | none =>
          have hn : before.activeAt d l = none := by
            simp [before, fighterBeforeClosure, he, hstart, fighterFulfillReady, ho,
              fighterOpponent]
          rw [hn] at hp
          contradiction
        | some old => exact hprior old ho
  have hsorted : traversal.Pairwise (· < ·) :=
    pairwise_lt_mergeSort (Kolmogorov.nodup_eraseDups_list _)
  obtain ⟨tail, htraversal⟩ := exists_eq_takeWhile_append_cons hsorted
    (by simpa only [traversal, List.mem_mergeSort] using hmem)
  have hstate : fighterState P d (tick + 1) =
      fighter_actions P d (tick + 1) (fighterState P d ((tick + 1) - 1)) := by
    simpa only [Nat.add_sub_cancel] using
      (show fighterState P d (tick + 1) =
        fighter_actions P d (tick + 1) (fighterState P d tick) from rfl)
  have hdne : d ≠ 0 := Nat.ne_of_gt hd
  have hfull : fighterState P d (tick + 1) =
      tail.foldl (fun s j ↦ fighterProcessLevel P d j event s)
        (fighterCloseLevel P d l before) := by
    rw [hstate]
    simp only [fighter_actions, hdne, ite_false]
    change traversal.foldl (fun s j ↦ fighterProcessLevel P d j event s) current = _
    rw [htraversal, List.foldl_append, List.foldl_cons]
    rfl
  have htail : ∀ j ∈ tail, l < j := by
    have hs := hsorted
    rw [htraversal] at hs
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1
  exact ⟨tail, htail, hfull⟩

end Kolmogorov.Milovanov
