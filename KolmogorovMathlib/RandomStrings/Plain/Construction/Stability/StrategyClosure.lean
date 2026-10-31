/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferCandidates
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.StrategyPostponement

/-!
# Legal strategy responses during closure

This module establishes legality of internal closure for the true-marker phase in blueprint
node `constr:opponent`. A failure-free completed tick gives a failure-free completion of every
active replayed level. This ensures that funding a selected strategy move preserves an active
phase, while flushing a buffer records a legal opponent move. The capacity certificate for
good padding then yields `TrueMarkerClosureLegal`, used by the common-game invariants and the
opponent-stream legality theorem.
-/

namespace Kolmogorov.Milovanov

/-- If the completed closure of a level is failure-free, folding `fighterFuelUnits` over the
game's coordinates with the amounts of an enabled legal strategy move leaves `failed = false`. -/
private lemma foldl_fighterFuelUnits_failed_eq_false
    (P : FighterParams) (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) (move : List ℕ)
    (henabled : phase.predicateHolds d = false ∧ phase.buffer.sum = 0 ∧
      (phase.game d).activePlayer (phase.official d) = phase.controlledPlayer)
    (hstrategy : (phase.game d).strategy (phase.official d) = some move)
    (hlegal : (phase.game d).LegalMove (phase.official d) move ∧
      move.sum ≤ phase.controlledRemaining)
    (hservice : (fighterCloseLevel P d l state).failed = false) :
    ((phase.game d).coordinates.zipIdx.foldl
      (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s)
      state).failed = false := by
  by_contra hbatch
  let Bad (s : FighterState) : Prop := s.failed = true ∨ ∃ response,
    fighterStrategyMove P d l s = some response ∧ response.failed = true
  obtain ⟨haction, _, _⟩ :=
    fighter_failed_persists P d
  have hbad_action (s next : FighterState) (hs : Bad s)
      (hn : fighterLevelAction P d l s = some next) : Bad next := by
    rcases hs with hf | ⟨response, hr, hf⟩
    · left
      have h := haction l s hf
      simpa only [hn, Option.getD_some] using h
    · exact failed_response_survives_level_action
        P d l s response next hr hf hn
  have hbad_closure (fuel : ℕ) (s : FighterState) (hs : Bad s) :
      Bad (fighterClosure P d l fuel s) := by
    induction fuel generalizing s with
    | zero => exact hs
    | succ fuel ih =>
      simp only [fighterClosure]
      cases hn : fighterLevelAction P d l s with
      | none => exact hs
      | some next => exact ih next (hbad_action s next hs hn)
  let middle := (phase.game d).coordinates.zipIdx.foldl
    (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) state
  have hfold : (phase.game d).coordinates.zipIdx.foldl
      (fun s qi ↦ fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) state = middle := by
    apply congrArg (fun f ↦ (phase.game d).coordinates.zipIdx.foldl f state)
    funext s ⟨q, i⟩
    rfl
  have hmfailed : middle.failed = true := Bool.eq_true_of_ne_false hbatch
  have hresponse : fighterStrategyMove P d l state =
      match middle.activeAt d l with
      | none => some middle
      | some live => some (middle.putPhase d
          { live with
            officialCode := ((phase.game d).afterMove (phase.official d) move).encode }) := by
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some, henabled,
      and_self, ite_true, hstrategy, hlegal, hfold]
    rfl
  have hstart : Bad state := by
    right
    cases hm : middle.activeAt d l with
    | none => exact ⟨middle, hresponse.trans (by rw [hm]), hmfailed⟩
    | some live =>
      exact ⟨middle.putPhase d
        { live with officialCode := ((phase.game d).afterMove (phase.official d) move).encode },
        hresponse.trans (by rw [hm]), hmfailed⟩
  have hfinish := hbad_closure (fighterClosureFuel d l state) state hstart
  change Bad (fighterCloseLevel P d l state) at hfinish
  have hnone : fighterStrategyMove P d l (fighterCloseLevel P d l state) = none := by
    have hfix := fighter_closure_fixpoint P d l state
    cases hp : (fighterCloseLevel P d l state).activeAt d l with
    | none => simp [fighterStrategyMove, hp]
    | some p =>
      simp only [fighterLevelAction, hp, bind, Option.bind_some] at hfix
      split at hfix
      · contradiction
      · split at hfix
        · contradiction
        · split at hfix
          · contradiction
          · exact hfix
  rcases hfinish with hf | ⟨response, hr, _⟩
  · rw [hservice] at hf
    cases hf
  · rw [hnone] at hr
    contradiction

/-- Closure leaves a state unchanged once no level action is enabled. -/
private lemma fighterClosure_eq_of_action_eq_none (P : FighterParams) (d l n : ℕ)
    (s : FighterState) (hs : fighterLevelAction P d l s = none) :
    fighterClosure P d l n s = s := by
  cases n <;> simp [fighterClosure, hs]

/-- Splitting the closure fuel composes two segments of the same action sequence. -/
private lemma fighterClosure_add (P : FighterParams) (d l a b : ℕ) (s : FighterState) :
    fighterClosure P d l (a + b) s =
      fighterClosure P d l b (fighterClosure P d l a s) := by
  induction a generalizing s with
  | zero => simp [fighterClosure]
  | succ a ih =>
    cases hs : fighterLevelAction P d l s with
    | none =>
      rw [fighterClosure_eq_of_action_eq_none P d l (a + 1 + b) s hs,
        fighterClosure_eq_of_action_eq_none P d l (a + 1) s hs,
        fighterClosure_eq_of_action_eq_none P d l b s hs]
    | some next => simpa only [Nat.succ_add, fighterClosure, hs] using ih next

/-- Restarting closure after any finite prefix reaches the same completed state. -/
private lemma fighterCloseLevel_fighterClosure (P : FighterParams) (d l n : ℕ)
    (s : FighterState) :
    fighterCloseLevel P d l (fighterClosure P d l n s) = fighterCloseLevel P d l s := by
  let mid := fighterClosure P d l n s
  let f := fighterClosureFuel d l s
  let g := fighterClosureFuel d l mid
  calc
    fighterCloseLevel P d l mid =
        fighterClosure P d l f (fighterCloseLevel P d l mid) :=
      (fighterClosure_eq_of_action_eq_none P d l f _ (fighter_closure_fixpoint P d l mid)).symm
    _ = fighterClosure P d l f
        (fighterClosure P d l g (fighterClosure P d l n s)) := rfl
    _ = fighterClosure P d l (g + f) (fighterClosure P d l n s) :=
      (fighterClosure_add P d l g f _).symm
    _ = fighterClosure P d l (n + (g + f)) s :=
      (fighterClosure_add P d l n (g + f) s).symm
    _ = fighterClosure P d l (f + (n + g)) s := by congr 1; omega
    _ = fighterClosure P d l (n + g) (fighterClosure P d l f s) :=
      fighterClosure_add P d l f (n + g) s
    _ = fighterCloseLevel P d l s :=
      fighterClosure_eq_of_action_eq_none P d l (n + g) _ (fighter_closure_fixpoint P d l s)

/-- If a completed tick is failure-free, completing the closure of an active phase at any
intermediate replay position of that tick is also failure-free. -/
lemma fighterCloseLevel_closureAt_failed_eq_false
    (P : FighterParams) (d l tick step : ℕ) (hd : d ≠ 0) (htick : 0 < tick)
    (hfailed : (fighterState P d tick).failed = false)
    (phase : FighterPhase)
    (hphase : (fighterClosureAt P d tick l step).activeAt d l = some phase) :
    (fighterCloseLevel P d l (fighterClosureAt P d tick l step)).failed = false := by
  obtain ⟨_, _, hprocess⟩ :=
    fighter_failed_persists P d
  let before := fighterBeforeClosure P d tick l
  have hbefore : ∃ p, before.activeAt d l = some p := by
    cases hb : before.activeAt d l with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have ha : fighterLevelAction P d l before = none := by
        simp [fighterLevelAction, hb]
      have hsame := fighterClosure_eq_of_action_eq_none P d l step before ha
      change (fighterClosure P d l step before).activeAt d l = some phase at hphase
      rw [hsame, hb] at hphase
      contradiction
  let current : FighterState :=
    { fighterState P d (tick - 1) with tick := tick, schedule := masterState P.B tick }
  let event := eventAt P.B tick
  let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
  let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
  let traversal := levels.mergeSort (· ≤ ·)
  have hevent : ∀ e, event = some e → e.1 = tick := by
    intro e he
    dsimp [event, eventAt] at he
    rw [Option.filter_eq_some_iff] at he
    exact of_decide_eq_true he.2
  have hsupport (ls : List ℕ) (hls : ∀ j ∈ ls, j ∈ levels)
      (s : FighterState) (ht : s.tick = tick)
      (hs : ∀ p ∈ s.active, p.level ∈ levels) :
      (ls.foldl (fun s j ↦ fighterProcessLevel P d j event s) s).tick = tick ∧
      ∀ p ∈ (ls.foldl (fun s j ↦ fighterProcessLevel P d j event s) s).active,
        p.level ∈ levels := by
    induction ls generalizing s with
    | nil => exact ⟨ht, hs⟩
    | cons j ls ih =>
      have hj := fighterProcessLevel_preserves_active P d j event s
        (fun level _ _ _ ↦ level ∈ levels)
        (fun e he ↦ (hevent e he).trans ht.symm)
        (fun _ _ _ ↦ hls j (by simp)) hs
      exact ih (fun k hk ↦ hls k (List.mem_cons_of_mem j hk)) _
        (hj.1.trans ht) hj.2
  have hpref : ∀ p ∈ (fighterBeforeLevel P d tick l).active, p.level ∈ levels := by
    apply (hsupport (traversal.takeWhile (· < l)) ?_ current rfl ?_).2
    · intro j hj
      have hm := List.takeWhile_subset (fun j ↦ decide (j < l)) hj
      simpa only [traversal, List.mem_mergeSort] using hm
    · intro p hp
      apply List.mem_eraseDups.mpr
      exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem hp))
  have hmem : l ∈ levels := by
    obtain ⟨p, hp⟩ := hbefore
    have hprior (old : FighterPhase)
        (ho : (fighterBeforeLevel P d tick l).activeAt d l = some old) : l ∈ levels := by
      have hl : old.level = l :=
        beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) ho)
      simpa only [hl] using hpref old (List.mem_of_find?_eq_some ho)
    cases he : eventAt P.B tick with
    | none =>
      cases ho : (fighterBeforeLevel P d tick l).activeAt d l with
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
      · cases ho : (fighterBeforeLevel P d tick l).activeAt d l with
        | none =>
          have hn : before.activeAt d l = none := by
            simp [before, fighterBeforeClosure, he, hstart,
              fighterFulfillReady, ho, fighterOpponent]
          rw [hn] at hp
          contradiction
        | some old => exact hprior old ho
  have hsorted : traversal.Pairwise (· < ·) := by
    have hle := List.pairwise_mergeSort' (· ≤ ·) levels
    have hne : traversal.Nodup := by
      rw [List.nodup_mergeSort]
      exact Kolmogorov.nodup_eraseDups_list _
    exact (hle.and hne).imp (fun h ↦ lt_of_le_of_ne h.1 h.2)
  have hsplit (xs : List ℕ) (hs : xs.Pairwise (· < ·)) (hm : l ∈ xs) :
      ∃ tail, xs = xs.takeWhile (· < l) ++ l :: tail := by
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
  obtain ⟨tail, htraversal⟩ := hsplit traversal hsorted
    (by simpa only [traversal, List.mem_mergeSort] using hmem)
  have hstate : fighterState P d tick = fighter_actions P d tick
      (fighterState P d (tick - 1)) := by
    cases tick with
    | zero => omega
    | succ t => rfl
  have hfull : fighterState P d tick =
      tail.foldl (fun s j ↦ fighterProcessLevel P d j event s)
        (fighterCloseLevel P d l before) := by
    rw [hstate]
    simp only [fighter_actions, hd, ite_false]
    change traversal.foldl (fun s j ↦ fighterProcessLevel P d j event s) current = _
    rw [htraversal, List.foldl_append, List.foldl_cons]
    rfl
  have hclosed : (fighterCloseLevel P d l before).failed = false := by
    by_contra h
    have hf : (fighterCloseLevel P d l before).failed = true := Bool.eq_true_of_ne_false h
    have hend := List.foldlRecOn (motive := fun s : FighterState ↦ s.failed = true)
      tail (fun s j ↦ fighterProcessLevel P d j event s) hf
      (fun s hs j _ ↦ hprocess j event s hs)
    change (tail.foldl (fun s j ↦ fighterProcessLevel P d j event s)
      (fighterCloseLevel P d l before)).failed = true at hend
    rw [← hfull, hfailed] at hend
    cases hend
  change (fighterCloseLevel P d l (fighterClosure P d l step before)).failed = false
  rw [fighterCloseLevel_fighterClosure]
  exact hclosed

/-- A successful buffer flush is a legal opponent move and stores its official child with an
empty buffer. -/
private lemma legalMove_of_fighterFlushBuffer_eq_some
    (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase)
    (next : FighterState)
    (hflush : fighterFlushBuffer d l state = some next) :
    (phase.game d).LegalMove (phase.official d) phase.buffer ∧
    (phase.game d).activePlayer (phase.official d) ≠ phase.controlledPlayer ∧
    ∃ afterPhase, next.activeAt d l = some afterPhase ∧
      afterPhase.officialCode =
        ((phase.game d).afterMove (phase.official d) phase.buffer).encode ∧
      afterPhase.buffer = List.replicate (phase.game d).coordinates.length 0 := by
  unfold fighterFlushBuffer at hflush
  rw [hphase] at hflush
  dsimp [bind, Option.bind] at hflush
  split at hflush
  · rename_i hguard
    rcases hguard with ⟨hpred, hturn, hlegal⟩
    have hnext : next = state.putPhase d { phase with
      officialCode := ((phase.game d).afterMove (phase.official d) phase.buffer).encode,
      buffer := List.replicate (phase.game d).coordinates.length 0 } := by
      injection hflush; symm; assumption
    subst hnext
    refine ⟨hlegal, hturn, ?_⟩
    let afterPhase := { phase with
      officialCode := ((phase.game d).afterMove (phase.official d) phase.buffer).encode,
      buffer := List.replicate (phase.game d).coordinates.length 0 }
    use afterPhase
    have hl : afterPhase.level = l := by
      change phase.level = l
      exact beq_iff_eq.mp
        (List.find?_some (p := fun phase : FighterPhase ↦ phase.level == l) hphase)
    refine ⟨?_, rfl, rfl⟩
    change (state.putPhase d afterPhase).activeAt d l = some afterPhase
    simp [FighterState.putPhase, FighterState.activeAt, hl]
  · contradiction

/-- In a state with failure-free completed closure, a successful controlled response selects
a legal strategy move and stores the resulting official position in an active phase. -/
private lemma exists_legal_strategy_move_of_fighterStrategyMove_eq_some
    (P : FighterParams) (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase)
    (hservice : (fighterCloseLevel P d l state).failed = false)
    (next : FighterState) (hnext : fighterStrategyMove P d l state = some next) :
    ∃ move, (phase.game d).strategy (phase.official d) = some move ∧
      (phase.game d).LegalMove (phase.official d) move ∧
      (phase.game d).activePlayer (phase.official d) = phase.controlledPlayer ∧
      ∃ afterPhase, next.activeAt d l = some afterPhase ∧
        afterPhase.officialCode =
          ((phase.game d).afterMove (phase.official d) move).encode := by
  simp only [fighterStrategyMove, hphase, bind, Option.bind_some] at hnext
  split at hnext
  · rename_i hguard
    cases hmove : (phase.game d).strategy (phase.official d) with
    | none => simp [hmove] at hnext
    | some move =>
      simp only [hmove, Option.bind_some] at hnext
      split at hnext
      · rename_i hlegal
        refine ⟨move, rfl, hlegal.1, hguard.2.2, ?_⟩
        let middle := (phase.game d).coordinates.zipIdx.foldl
          (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s)
          state
        change (match middle.activeAt d l with
          | none => some middle
          | some live => some (middle.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })) =
            some next at hnext
        have hbatch := foldl_fighterFuelUnits_failed_eq_false
          P d l state phase hphase move hguard hmove hlegal hservice
        obtain ⟨live, hlive⟩ :=
          exists_activeAt_fuel_fold_of_not_failed
            P d l state phase hphase move hbatch
        change middle.activeAt d l = some live at hlive
        rw [hlive] at hnext
        cases Option.some.inj hnext
        have hlevel : live.level = l :=
          beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hlive)
        refine ⟨{ live with officialCode :=
          ((phase.game d).afterMove (phase.official d) move).encode }, ?_, rfl⟩
        simp [FighterState.putPhase, FighterState.activeAt, hlevel]
      · contradiction
  · contradiction

/-- The capacity certificate for good padding makes every true-marker closure move legal.
Buffer flushes are opponent moves, and controlled responses follow the game's strategy.
Blueprint node `constr:opponent`. -/
lemma trueMarkerClosureLegal_of_goodPadding (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l) :
    TrueMarkerClosureLegal P d l := by
  have hmarker : markerTick P.B (levelScale l) ≠ 0 := by
    intro hzero
    have hevent : eventAt P.B (markerTick P.B (levelScale l)) = none := by
      rw [hzero]
      rfl
    have hlength := hlate.2
    simp only [lastProgram, hevent, Option.map_none, Option.getD_none,
      List.length_nil, Nat.not_lt_zero] at hlength
  intro tick htick step hstep
  dsimp only
  intro phase hphase hcand
  have hbuf : phase.BufferInvariant d :=
    bufferInvariant_closureAt
      P C cGap cRank d₀ d l hfixed hgood hlate tick htick step hstep phase hphase hcand
  refine ⟨hbuf, ?_, ?_⟩
  · intro next hflush
    exact legalMove_of_fighterFlushBuffer_eq_some
      d l (fighterClosureAt P d tick l step) phase hphase next hflush
  · intro next hstrat
    have hservice := fighterCloseLevel_closureAt_failed_eq_false
      P d l tick step (Nat.ne_of_gt hgood.positive)
      ((Nat.pos_of_ne_zero hmarker).trans_le htick)
      (hfixed.capacity d hgood.capacity_threshold hgood.even tick) phase hphase
    exact exists_legal_strategy_move_of_fighterStrategyMove_eq_some
      P d l (fighterClosureAt P d tick l step) phase hphase hservice next hstrat

end Kolmogorov.Milovanov
