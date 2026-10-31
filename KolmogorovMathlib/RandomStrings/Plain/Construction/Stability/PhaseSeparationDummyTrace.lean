/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FundedRequestTrace

/-!
# Persistence of frozen dummy records

A fighter phase fixes its level, candidate, and optional dummy output when it starts.
These fields survive every update (d := d), and cancellation transfers them to the archive.
This module proves their persistence between completed ticks, using uniqueness of active
levels to justify record replacement. The phase-separation argument uses this trace to
compare a phase with a dummy allocation made at a later tick, in blueprint node
`constr:separation`.
-/

namespace Kolmogorov.Milovanov

/-- An active or archived record retains the phase identity and its optional dummy output. -/
private abbrev DummyTrace (phase : FighterPhase) (s : FighterState) : Prop :=
  (∃ p ∈ s.active, p.level = phase.level ∧ p.candidate = phase.candidate ∧
    p.dummy = phase.dummy) ∨
  ∃ e ∈ s.ended, e.1.level = phase.level ∧ e.1.candidate = phase.candidate ∧
    e.1.dummy = phase.dummy

/-- Unique active levels allow replacements to preserve the trace of a fixed phase. -/
private abbrev DummyTraceInvariant (phase : FighterPhase) (s : FighterState) : Prop :=
  (s.active.map FighterPhase.level).Nodup ∧ DummyTrace phase s

namespace DummyTraceInvariant

variable {P : FighterParams} {d : ℕ} {tracked : FighterPhase}

private lemma putPhase (s : FighterState) (p : FighterPhase) (hs : DummyTraceInvariant tracked s)
    (hov : ∀ old ∈ s.active, old.level = p.level →
      old.candidate = p.candidate ∧ old.dummy = p.dummy) :
    DummyTraceInvariant tracked (s.putPhase d p) := by
  refine ⟨?_, ?_⟩
  · simp only [FighterState.putPhase, List.map_cons, List.nodup_cons]
    refine ⟨?_, List.pairwise_map.mpr ((List.pairwise_map.mp hs.1).filter _)⟩
    intro hm
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp hm
    have hne := (List.mem_filter.mp hold).2
    simp [heq] at hne
  · rcases hs.2 with ⟨old, hold, hlevel, hcand, hdum⟩ | hended
    · by_cases heq : old.level = p.level
      · obtain ⟨hc, hd⟩ := hov old hold heq
        exact Or.inl ⟨p, List.mem_cons_self, heq.symm.trans hlevel,
          hc.symm.trans hcand, hd.symm.trans hdum⟩
      · exact Or.inl ⟨old,
          List.mem_cons_of_mem p (List.mem_filter.mpr ⟨hold, by simpa using heq⟩),
          hlevel, hcand, hdum⟩
    · exact Or.inr hended

private lemma update {s : FighterState} {old p : FighterPhase} {j : ℕ}
    (hs : DummyTraceInvariant tracked s)
    (hold : s.activeAt d j = some old)
    (hfields : (p.level, p.candidate, p.dummy) = (old.level, old.candidate, old.dummy)) :
    DummyTraceInvariant tracked (s.putPhase d p) := by
  obtain ⟨hlevel, hrest⟩ := Prod.mk.inj hfields
  obtain ⟨hcand, hdummy⟩ := Prod.mk.inj hrest
  apply putPhase (d := d) s p hs
  intro other ho hl
  have heq := List.inj_on_of_nodup_map hs.1 ho (List.mem_of_find?_eq_some hold)
    (hl.trans hlevel)
  subst other
  exact ⟨hcand.symm, hdummy.symm⟩

private lemma cancel (j cause : ℕ) (reason : PhaseEnd) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i found hp
    refine ⟨List.pairwise_map.mpr ((List.pairwise_map.mp hs.1).filter _), ?_⟩
    rcases hs.2 with ⟨old, hold, hlevel, hcand, hdum⟩ | ⟨e, he, hl, hc, hd⟩
    · by_cases heq : old.level = j
      · have hpj : found.level = j := beq_iff_eq.mp
          (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hp)
        have holdphase := List.inj_on_of_nodup_map hs.1 hold
          (List.mem_of_find?_eq_some hp) (heq.trans hpj.symm)
        subst old
        exact Or.inr ⟨({ found with pending := [] }, s.tick, reason, cause),
          List.mem_append_right _ (List.mem_singleton.mpr rfl), hlevel, hcand, hdum⟩
      · exact Or.inl ⟨old, List.mem_filter.mpr ⟨hold, by simpa using heq⟩,
          hlevel, hcand, hdum⟩
    · exact Or.inr ⟨e, List.mem_append_left _ he, hl, hc, hd⟩

private lemma abortAbove (j : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  apply List.foldlRecOn _ _ hs
  intro t ht p _
  split
  · exact cancel (d := d) _ _ _ _ ht
  · exact ht

private lemma allocate (j : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterAllocate d j kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · rename_i phase hp
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact cancel (d := d) j j .saturated { s with failed := true } hs
    | some input =>
      exact abortAbove (d := d) j { s with allocated := s.allocated ++
        [⟨j, phase.candidate, s.tick, kind, target, input, out⟩] } hs

private lemma recordFulfilled (s : FighterState) (q : Coordinate)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked { s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using hs.1
  · rcases hs.2 with ⟨old, hold, hl, hc, hd⟩ | hended
    · exact Or.inl ⟨{ old with pending := old.pending.filter (· != q) },
        List.mem_map.mpr ⟨old, hold, rfl⟩, hl, hc, hd⟩
    · exact Or.inr hended

private lemma payoff (j : ℕ) (q : Coordinate) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate (d := d) j .payoff q.2 q.1 s hs
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact recordFulfilled next q ha
    · exact hs

private lemma fulfillReady (j : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn _ _ hs (fun t ht q _ ↦ payoff (d := d) (P := P) j q t ht)

private lemma fuelUnit (j : ℕ) (q : Coordinate) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterFuelUnit P d j q s) := by
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
      have hc := update (d := d) (p := charged) hs hp rfl
      have hcharged : (s.putPhase d charged).activeAt d j = some charged := by
        simp [FighterState.putPhase, FighterState.activeAt, charged, hlevel]
      have ha := allocate (d := d) j .fuel (levelUpper j + d) out (s.putPhase d charged) hc
      change DummyTraceInvariant tracked
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
          apply fulfillReady (d := d) (P := P)
          exact update (d := d) ha hlive rfl
    · exact hs

private lemma fuelUnits (j : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuelUnit (d := d) (P := P) j q s hs)

private lemma dummy (j : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := allocate (d := d) j .dummy (levelInput d j) output s hs
        cases he : fighterAllocate d j .dummy (levelInput d j) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hlive := activeAt_fighterAllocate_eq_of_success
              d j (levelInput d j) .dummy output s next phase hp he
            exact update (d := d) ha hlive rfl

private lemma opponent (j : ℕ) (e : ProgramEvent) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterOpponent P d j e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel (d := d) _ _ _ _ hs
        · apply fulfillReady (d := d) (P := P)
          exact update (d := d) hs hp rfl

private lemma startPhase (j : ℕ) (cand : Candidate) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterStartPhase P d j cand s) := by
  have hnone : ∀ p ∈ (fighterCancel d j .replaced j s).active, p.level ≠ j := by
    unfold fighterCancel
    split
    · rename_i hn
      intro p hp hlevel
      have h := List.find?_eq_none.mp hn p hp
      exact h (by simp [hlevel])
    · intro p hp
      simpa using (List.mem_filter.mp hp).2
  unfold fighterStartPhase
  apply putPhase (d := d) _ _ (abortAbove (d := d) j _ (cancel (d := d) j j .replaced s hs))
  intro old ho hl
  exact (hnone old (fighterAbortAbove_active_subset d j _ ho) hl).elim

private lemma flushBuffer (j : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked ((fighterFlushBuffer d j s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d j with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact update (d := d) hs hp rfl
    · exact hs

private lemma strategyMove (j : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked ((fighterStrategyMove P d j s).getD s) := by
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
          have hn : DummyTraceInvariant tracked next := by
            apply List.foldlRecOn _ _ hs
            intro t ht qi _
            exact fuelUnits (d := d) (P := P) j qi.1 (move[qi.2]?.getD 0) t ht
          change DummyTraceInvariant tracked ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            exact update (d := d) hn hlive rfl
        · exact hs
    · exact hs

private lemma levelAction (j : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked ((fighterLevelAction P d j s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d j with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy (d := d) j s hs
    · split
      · exact payoff (d := d) (P := P) j _ s hs
      · cases hf : fighterFlushBuffer d j s with
        | none => exact strategyMove (d := d) (P := P) j s hs
        | some next =>
          have h := flushBuffer (d := d) j s hs
          simpa only [hf, Option.getD_some] using h

private lemma closure (j fuel : ℕ) (s : FighterState) (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact hs
    | some next =>
      have hn := levelAction (d := d) (P := P) j s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private lemma processLevel (j : ℕ) (e : Option TimedEvent) (s : FighterState)
    (hs : DummyTraceInvariant tracked s) :
    DummyTraceInvariant tracked (fighterProcessLevel P d j e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply closure (d := d) (P := P)
  cases e with
  | none => exact fulfillReady (d := d) (P := P) j s hs
  | some e =>
    dsimp only
    split
    · exact startPhase (d := d) (P := P) j _ _ (fulfillReady (d := d) (P := P) j s hs)
    · exact opponent (d := d) (P := P) j _ _ (fulfillReady (d := d) (P := P) j s hs)

private lemma actions (hd : 1 ≤ d) (time : ℕ) (state : FighterState)
    (hs : DummyTraceInvariant tracked state) :
    DummyTraceInvariant tracked (fighter_actions P d time state) := by
  unfold fighter_actions
  rw [ite_eq_right (by omega : d ≠ 0)]
  let current := { state with tick := time, schedule := masterState P.B time }
  exact List.foldlRecOn _ _ (b := current) hs
    (fun t ht j _ ↦ processLevel (d := d) (P := P) j _ t ht)

end DummyTraceInvariant

/-- The frozen dummy fields of an active phase persist in an active or archived record
at every later completed tick. -/
lemma exists_dummy_record_of_le {P : FighterParams} {d tick later : ℕ}
    {phase : FighterPhase} (hd : 1 ≤ d) (hle : tick ≤ later)
    (hphase : phase ∈ (fighterState P d tick).active) :
    (∃ p ∈ (fighterState P d later).active,
      p.level = phase.level ∧ p.candidate = phase.candidate ∧ p.dummy = phase.dummy) ∨
    ∃ e ∈ (fighterState P d later).ended,
      e.1.level = phase.level ∧ e.1.candidate = phase.candidate ∧ e.1.dummy = phase.dummy := by
  have hall : ∀ time ≥ tick, DummyTraceInvariant phase (fighterState P d time) := by
    intro time htime
    induction time, htime using Nat.le_induction with
    | base =>
      exact ⟨fighterState_active_levels_nodup P d tick hd,
        Or.inl ⟨phase, hphase, rfl, rfl, rfl⟩⟩
    | succ time htime ih => exact DummyTraceInvariant.actions hd (time + 1) _ ih
  exact (hall later hle).2

end Kolmogorov.Milovanov
