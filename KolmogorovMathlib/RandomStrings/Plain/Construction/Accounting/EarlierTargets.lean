/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.LevelRanges

/-!
# Earlier targets and saturated input pools

This module proves the earlier-level bound in blueprint node `constr:intervals`:
every target of an earlier activated level lies below the logarithm of the current
level's scale, plus padding, and hence below that scale itself.

The accounting invariant records admissibility of all started levels, valid directive
ranges, and the presence of active phases in the start history. At positive padding, each state
operation preserves this invariant and extends the permanent logs. A newly raised failure flag
therefore supplies a positive target whose entire input pool is already allocated.
`CapacityFailure` uses this witness for its counting argument; `UniformRank` uses the
upper bound on target ranges to count outputs from earlier levels.
-/

namespace Kolmogorov.Milovanov

/-- Valid payoff coordinates and pending requests at an admissible phase. -/
private def phaseTargetsValid (P : FighterParams) (d : ℕ) (phase : FighterPhase) : Prop :=
  P.Admissible d phase.level ∧
    (∀ q ∈ (phase.game d).coordinates, FighterTargetRange d phase.level .payoff q.2) ∧
    (∀ q ∈ phase.pending, FighterTargetRange d phase.level .payoff q.2)

/-- Valid target ranges, recorded active phases, and admissible entries in the start log. -/
private def accountingInvariant (P : FighterParams) (d : ℕ) (s : FighterState) : Prop :=
  fighterTargetRangesValid P d s ∧
    (∀ phase ∈ s.active, (phase.level, phase.candidate) ∈ s.started) ∧
    ∀ entry ∈ s.started, P.Admissible d entry.1

/-- A positive target of a started level whose input pool is fully occupied. -/
private def saturatedTarget (d : ℕ) (s : FighterState) : Prop :=
  ∃ r l kind, (∃ candidate, (l, candidate) ∈ s.started) ∧
    FighterTargetRange d l kind r ∧ r > 0 ∧
    ∀ p ∈ fighterInputs d (r - 1), s.allocated.any (fun a ↦ a.input == p) = true

/-- Permanent logs grow, the target invariant holds, and new failures witness saturation. -/
private def accountingExtension (P : FighterParams) (d : ℕ) (s t : FighterState) : Prop :=
  s.started ⊆ t.started ∧ s.allocated ⊆ t.allocated ∧ accountingInvariant P d t ∧
    (t.failed = true → s.failed = true ∨ saturatedTarget d t)

private lemma pool_occupied_of_search_none (d r : ℕ) (s : FighterState)
    (hsearch : (fighterInputs d (r - 1)).find?
      (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)) = none) :
    ∀ p ∈ fighterInputs d (r - 1),
      s.allocated.any (fun a ↦ a.input == p) = true := by
  intro p hp
  simpa using List.find?_eq_none.mp hsearch p hp

/-- Saturation persists when both permanent logs grow. -/
private lemma saturated_target_mono (d : ℕ) (s t : FighterState)
    (hstarted : s.started ⊆ t.started) (hallocated : s.allocated ⊆ t.allocated)
    (h : saturatedTarget d s) : saturatedTarget d t := by
  obtain ⟨r, l, kind, ⟨candidate, hc⟩, hrange, hr, hall⟩ := h
  refine ⟨r, l, kind, ⟨candidate, hstarted hc⟩, hrange, hr, ?_⟩
  intro p hp
  obtain ⟨a, ha, heq⟩ := List.any_eq_true.mp (hall p hp)
  exact List.any_eq_true.mpr ⟨a, hallocated ha, heq⟩

variable {P : FighterParams} {d : ℕ}

private lemma accounting_refl (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s s :=
  ⟨fun _ h ↦ h, fun _ h ↦ h, hs, fun h ↦ Or.inl h⟩

private lemma accounting_trans {s t u : FighterState}
    (hst : accountingExtension P d s t)
    (htu : accountingExtension P d t u) : accountingExtension P d s u := by
  refine ⟨fun _ h ↦ htu.1 (hst.1 h), fun _ h ↦ htu.2.1 (hst.2.1 h),
    htu.2.2.1, ?_⟩
  intro hf
  rcases htu.2.2.2 hf with hf | hw
  · rcases hst.2.2.2 hf with hf | hw
    · exact Or.inl hf
    · exact Or.inr (saturated_target_mono d t u htu.1 htu.2.1 hw)
  · exact Or.inr hw

private lemma accounting_foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, accountingInvariant P d s → accountingExtension P d s (f a s))
    (xs : List α) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact accounting_refl s hs
  | cons a xs ih =>
    have ha := hf a s hs
    exact accounting_trans ha (ih _ ha.2.2.1)

private lemma accounting_of_logs_eq (s t : FighterState) (hs : accountingInvariant P d t)
    (hstart : t.started = s.started) (halloc : t.allocated = s.allocated)
    (hfailed : t.failed = s.failed) : accountingExtension P d s t := by
  refine ⟨?_, ?_, hs, ?_⟩
  · intro a ha
    exact hstart.symm ▸ ha
  · intro a ha
    exact halloc.symm ▸ ha
  · intro hf
    exact Or.inl (hfailed.symm.trans hf)

private lemma accounting_cancel (j : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState)
    (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact accounting_refl s hs
  · refine accounting_of_logs_eq s _ ?_ ?_ ?_ ?_ <;> try rfl
    refine ⟨⟨hs.1.1, ?_⟩, ?_, hs.2.2⟩
    · intro phase hp
      exact hs.1.2 phase (List.mem_filter.mp hp).1
    · intro phase hp
      exact hs.2.1 phase (List.mem_filter.mp hp).1

private lemma accounting_abort_above (j : ℕ) (s : FighterState)
    (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterAbortAbove d j s) := by
  unfold fighterAbortAbove
  apply accounting_foldl _ _ _ _ hs
  intro phase t ht
  split
  · exact accounting_cancel _ _ _ _ ht
  · exact accounting_refl t ht

private lemma accounting_put_phase
    (s : FighterState) (phase : FighterPhase) (hs : accountingInvariant P d s)
    (hp : phaseTargetsValid P d phase) (hh : (phase.level, phase.candidate) ∈ s.started) :
    accountingExtension P d s (s.putPhase d phase) := by
  refine accounting_of_logs_eq s _ ?_ ?_ ?_ ?_ <;> try rfl
  refine ⟨⟨hs.1.1, ?_⟩, ?_, hs.2.2⟩
  · intro p hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hp
    · exact hs.1.2 p (List.mem_filter.mp hmem).1
  · intro p hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hh
    · exact hs.2.1 p (List.mem_filter.mp hmem).1

private lemma phase_targets_fund_requests
    (phase : FighterPhase) (fulfilled : List Coordinate) (hp : phaseTargetsValid P d phase) :
    phaseTargetsValid P d (phase.fundRequests d fulfilled) := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro q hq
  change q ∈ (List.filter _ (_ ++ _)).eraseDups at hq
  simp only [List.mem_eraseDups, List.mem_filter, List.mem_append] at hq
  rcases hq.1 with hq | hq
  · exact hp.2.2 q hq
  · exact hp.2.1 q hq.1

private lemma active_at_mem_level (s : FighterState) (j : ℕ) (phase : FighterPhase)
    (hphase : s.activeAt d j = some phase) :
    phase ∈ s.active ∧ phase.level = j :=
  ⟨List.mem_of_find?_eq_some hphase,
    beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hphase)⟩

private lemma accounting_allocate
    (hd : 1 ≤ d) (j : ℕ) (kind : DirectiveKind) (r : ℕ) (out : BitString)
    (s : FighterState) (hs : accountingInvariant P d s) (hrange : FighterTargetRange d j kind r) :
    accountingExtension P d s (fighterAllocate d j kind r out s).1 := by
  have hr : 0 < r := by
    cases kind <;> simp only [FighterTargetRange] at hrange <;> omega
  unfold fighterAllocate
  cases hphase : s.activeAt d j with
  | none => exact accounting_refl s hs
  | some phase =>
    obtain ⟨hmem, hlevel⟩ := active_at_mem_level s j phase hphase
    have hph := hs.1.2 phase hmem
    have hh := hs.2.1 phase hmem
    simp only [ite_eq_right (by omega : r ≠ 0)]
    cases hf : (fighterInputs d (r - 1)).find?
        (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)) with
    | none =>
      have hw : saturatedTarget d { s with failed := true } := by
        refine ⟨r, j, kind, ⟨phase.candidate, ?_⟩, hrange, hr, ?_⟩
        · simpa only [hlevel] using hh
        · exact pool_occupied_of_search_none d r s hf
      have he : accountingExtension P d s { s with failed := true } :=
        ⟨fun _ h ↦ h, fun _ h ↦ h, hs, fun _ ↦ Or.inr hw⟩
      exact accounting_trans he (accounting_cancel j .saturated j _ hs)
    | some input =>
      let entry := AllocatedDirective.mk j phase.candidate s.tick kind r input out
      let next := { s with allocated := s.allocated ++ [entry] }
      have hn : accountingInvariant P d next := by
        refine ⟨⟨?_, hs.1.2⟩, hs.2⟩
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hs.1.1 a ha
        · obtain rfl := List.mem_singleton.mp ha
          refine ⟨?_, hrange⟩
          change P.Admissible d j
          simpa only [hlevel] using hph.1
      have he : accountingExtension P d s next :=
        ⟨fun _ h ↦ h, fun _ h ↦ List.mem_append_left _ h, hn, fun h ↦ Or.inl h⟩
      exact accounting_trans he (accounting_abort_above j next hn)

private lemma accounting_record_payoff
    (s : FighterState) (q : Coordinate) (hs : accountingInvariant P d s) :
    accountingExtension P d s { s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine accounting_of_logs_eq s _ ?_ ?_ ?_ ?_ <;> try rfl
  refine ⟨⟨hs.1.1, ?_⟩, ?_, hs.2.2⟩
  · intro phase hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
    have hg := hs.1.2 old hold
    exact ⟨hg.1, hg.2.1, fun r hr ↦ hg.2.2 r (List.mem_filter.mp hr).1⟩
  · intro phase hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
    exact hs.2.1 old hold

private lemma accounting_payoff
    (hd : 1 ≤ d) (j : ℕ) (q : Coordinate) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact accounting_refl s hs
  · rename_i phase hphase
    split
    · rename_i hguard
      obtain ⟨hmem, hlevel⟩ := active_at_mem_level s j phase hphase
      have hrange := (hs.1.2 phase hmem).2.2 q hguard.1
      rw [hlevel] at hrange
      have ha := accounting_allocate hd j .payoff q.2 q.1 s hs hrange
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        rw [he] at ha
        cases success
        · exact ha
        · exact accounting_trans ha (accounting_record_payoff next q ha.2.2.1)
    · exact accounting_refl s hs

private lemma accounting_fulfill_ready
    (hd : 1 ≤ d) (j : ℕ) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterFulfillReady P d j s) := by
  unfold fighterFulfillReady
  split
  · exact accounting_refl s hs
  · exact accounting_foldl (fun q s ↦ fighterPayoff P d j q s) (accounting_payoff hd j) _ _ hs

private lemma accounting_fuel_unit
    (hd : 1 ≤ d) (j : ℕ) (q : Coordinate) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact accounting_refl s hs
  · rename_i phase hphase
    obtain ⟨hmem, hlevel⟩ := active_at_mem_level s j phase hphase
    have hp : phaseTargetsValid P d phase := hs.1.2 phase hmem
    have hh := hs.2.1 phase hmem
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := accounting_put_phase s charged hs hp hh
      have ha := accounting_allocate hd j .fuel (levelUpper j + d) output
        (s.putPhase d charged) hc.2.2.1 rfl
      have hbefore := accounting_trans hc ha
      change accountingExtension P d s (match fighterAllocate d j .fuel (levelUpper j + d) output
          (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d j
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) output
          (s.putPhase d charged) with
      | mk next success =>
        rw [he] at hbefore
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact hbefore
        · have hi := accounting_put_phase next
            ((charged.insertIndex d q index).fundRequests d next.fulfilled)
            hbefore.2.2.1 (phase_targets_fund_requests _ _ hp) (hbefore.1 hh)
          exact accounting_trans hbefore
            (accounting_trans hi (accounting_fulfill_ready hd j _ hi.2.2.1))
    · exact accounting_refl s hs

private lemma accounting_fuel_units
    (hd : 1 ≤ d) (j : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState)
    (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact accounting_refl s hs
  | succ count ih =>
    have hn := accounting_fuel_unit hd j q s hs
    exact accounting_trans hn (ih _ hn.2.2.1)

private lemma accounting_dummy
    (hd : 1 ≤ d) (j : ℕ) (s : FighterState)
    (hs : accountingInvariant P d s) : accountingExtension P d s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact accounting_refl s hs
  · rename_i phase hphase
    split
    · exact accounting_refl s hs
    · rename_i output hout
      split
      · exact accounting_refl s hs
      · obtain ⟨hmem, hlevel⟩ := active_at_mem_level s j phase hphase
        have hp : phaseTargetsValid P d phase := hs.1.2 phase hmem
        have hh := hs.2.1 phase hmem
        have ha := accounting_allocate hd j .dummy (levelInput d j) output s hs rfl
        cases he : fighterAllocate d j .dummy (levelInput d j) output s with
        | mk next success =>
          rw [he] at ha
          cases success
          · exact ha
          · exact accounting_trans ha (accounting_put_phase next { phase with dummyIssued := true }
              ha.2.2.1 hp (ha.1 hh))

private lemma accounting_flush_buffer (j : ℕ) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s ((fighterFlushBuffer d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterFlushBuffer, hphase] using accounting_refl s hs
  | some phase =>
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact accounting_put_phase s _ hs (hs.1.2 phase (active_at_mem_level s j phase hphase).1)
        (hs.2.1 phase (active_at_mem_level s j phase hphase).1)
    · exact accounting_refl s hs

private lemma accounting_strategy_move
    (hd : 1 ≤ d) (j : ℕ) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s ((fighterStrategyMove P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterStrategyMove, hphase] using accounting_refl s hs
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact accounting_refl s hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) s) s
          have hn : accountingExtension P d s next :=
            accounting_foldl _ (fun qi t ht ↦ accounting_fuel_units hd j qi.1 _ t ht) _ s hs
          change accountingExtension P d s ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d { live with
                officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d j with
          | none => exact hn
          | some live =>
            exact accounting_trans hn (accounting_put_phase next _ hn.2.2.1
              (hn.2.2.1.1.2 live (active_at_mem_level next j live hlive).1)
              (hn.2.2.1.2.1 live (active_at_mem_level next j live hlive).1))
        · exact accounting_refl s hs
    · exact accounting_refl s hs

private lemma accounting_level_action
    (hd : 1 ≤ d) (j : ℕ) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s ((fighterLevelAction P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterLevelAction, hphase] using accounting_refl s hs
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact accounting_dummy hd j s hs
    · split
      · exact accounting_payoff hd j _ s hs
      · cases hf : fighterFlushBuffer d j s with
        | none => exact accounting_strategy_move hd j s hs
        | some next => simpa only [hf, Option.getD_some] using accounting_flush_buffer j s hs

private lemma accounting_closure
    (hd : 1 ≤ d) (j fuel : ℕ) (s : FighterState) (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact accounting_refl s hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact accounting_refl s hs
    | some next =>
      have hn := accounting_level_action hd j s hs
      simp only [ha, Option.getD_some] at hn
      exact accounting_trans hn (ih next hn.2.2.1)

private lemma accounting_start_phase
    (hd : 1 ≤ d) (j : ℕ) (candidate : Candidate) (s : FighterState) (hs : accountingInvariant P d s)
    (hadm : P.Admissible d j) :
    accountingExtension P d s (fighterStartPhase P d j candidate s) := by
  let waiting := fighterAbortAbove d j (fighterCancel d j .replaced j s)
  have hc := accounting_cancel j .replaced j s hs
  have hw : accountingExtension P d s waiting :=
    accounting_trans hc (accounting_abort_above j _ hc.2.2.1)
  let phase := fighter_construction P d j candidate waiting
  have hcons := construction_payoff_target_ranges
    P d j hd hadm candidate waiting
  let logged := { waiting with started := waiting.started ++ [(j, candidate)] }
  have hl : accountingInvariant P d logged := by
    refine ⟨hw.2.2.1.1, ?_, ?_⟩
    · intro p hp
      exact List.mem_append_left _ (hw.2.2.1.2.1 p hp)
    · intro entry he
      rcases List.mem_append.mp he with he | he
      · exact hw.2.2.1.2.2 entry he
      · obtain rfl := List.mem_singleton.mp he
        exact hadm
  have he : accountingExtension P d waiting logged :=
    ⟨fun _ h ↦ List.mem_append_left _ h, fun _ h ↦ h, hl, fun h ↦ Or.inl h⟩
  have hp : phaseTargetsValid P d phase := ⟨hadm, hcons.2.1, hcons.2.2⟩
  have hh : (phase.level, phase.candidate) ∈ logged.started :=
    List.mem_append_right _ (List.mem_singleton_self _)
  exact accounting_trans hw (accounting_trans he (accounting_put_phase logged phase hl hp hh))

private lemma accounting_opponent
    (hd : 1 ≤ d) (j : ℕ) (event : ProgramEvent) (s : FighterState)
    (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterOpponent P d j event s) := by
  unfold fighterOpponent
  split
  · exact accounting_refl s hs
  · rename_i phase hphase
    have hp : phaseTargetsValid P d phase := hs.1.2 phase (active_at_mem_level s j phase hphase).1
    have hh := hs.2.1 phase (active_at_mem_level s j phase hphase).1
    split
    · exact accounting_refl s hs
    · rename_i q index htuple
      split
      · exact accounting_refl s hs
      · split
        · exact accounting_cancel _ _ _ s hs
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          have hn := accounting_put_phase s (next.fundRequests d s.fulfilled) hs
            (phase_targets_fund_requests next s.fulfilled hp) hh
          exact accounting_trans hn (accounting_fulfill_ready hd j _ hn.2.2.1)

private lemma accounting_process_level
    (hd : 1 ≤ d) (j : ℕ) (event : Option TimedEvent) (s : FighterState)
    (hs : accountingInvariant P d s) :
    accountingExtension P d s (fighterProcessLevel P d j event s) := by
  unfold fighterProcessLevel fighterCloseLevel
  have hc := accounting_fulfill_ready hd j s hs
  apply accounting_trans hc
  cases event with
  | none => exact accounting_closure hd _ _ _ hc.2.2.1
  | some e =>
    dsimp only
    split
    · rename_i hguard
      have hn := accounting_start_phase hd j (e.2.2.1, e.1) (fighterFulfillReady P d j s)
        hc.2.2.1 hguard.2.2
      exact accounting_trans hn (accounting_closure hd _ _ _ hn.2.2.1)
    · have hn := accounting_opponent hd j e.2.2 (fighterFulfillReady P d j s) hc.2.2.1
      exact accounting_trans hn (accounting_closure hd _ _ _ hn.2.2.1)

/-- A positive-padding tick extends the permanent logs and accounts for every new failure. -/
private lemma accounting_actions (hd : 1 ≤ d) (tick : ℕ) (s : FighterState)
    (hs : accountingInvariant P d s) : accountingExtension P d s (fighter_actions P d tick s) := by
  unfold fighter_actions
  rw [ite_eq_right (by omega : d ≠ 0)]
  have hc : accountingExtension P d s { s with tick := tick, schedule := masterState P.B tick } :=
    accounting_of_logs_eq s _ hs rfl rfl rfl
  exact accounting_trans hc
    (accounting_foldl _ (fun j t ht ↦ accounting_process_level hd j (eventAt P.B tick) t ht)
      _ _ hc.2.2.1)

/-- Completed states have valid accounting data, and a failure witnesses a saturated target. -/
private lemma fighter_state_accounting (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d) :
    accountingInvariant P d (fighterState P d tick) ∧
      ((fighterState P d tick).failed = true → saturatedTarget d (fighterState P d tick)) := by
  induction tick with
  | zero =>
    simp [fighterState, initialFighterState, accountingInvariant,
      fighterTargetRangesValid]
  | succ tick ih =>
    have ht := accounting_actions hd (tick + 1) (fighterState P d tick) ih.1
    refine ⟨ht.2.2.1, ?_⟩
    intro hf
    rcases ht.2.2.2 hf with hold | hw
    · exact saturated_target_mono d _ _ ht.1 ht.2.1 (ih.2 hold)
    · exact hw

private lemma activated_admissible (P : FighterParams) (d l tick : ℕ)
    (hl : FighterActivated P d l tick) : P.Admissible d l := by
  obtain ⟨candidate, hmem⟩ := hl
  by_cases hd : d = 0
  · subst d
    cases tick with
    | zero => cases hmem
    | succ tick =>
      change (l, candidate) ∈ (fighter_actions P 0 (tick + 1) (fighterState P 0 tick)).started
        at hmem
      simp [fighter_actions, initialFighterState] at hmem
  · exact (fighter_state_accounting P d tick (by omega)).1.2.2 (l, candidate) hmem

/-- Every target in a level's directive ranges lies below its upper endpoint plus padding. -/
theorem target_le_upper_add (d i r : ℕ) (kind : DirectiveKind)
    (hr : FighterTargetRange d i kind r) : r ≤ levelUpper i + d := by
  cases kind with
  | dummy =>
    exact hr.trans_le (Nat.add_le_add_right (levelScale_lt_levelUpper i).le d)
  | payoff => exact hr.2.le.trans ((levelRangeBound_le_upper i).trans (Nat.le_add_right _ _))
  | fuel => exact hr.le

/-- Every earlier activated level's target is at most `log₂ n + d`, and hence at most `n`.
Blueprint node `constr:intervals`. -/
theorem fighter_earlier_target_bound (P : FighterParams) (d j l tick r : ℕ)
    (hj : FighterActivated P d j tick) (hl : FighterActivated P d l tick) (hjl : j < l)
    (kind : DirectiveKind) (hr : FighterTargetRange d j kind r) :
    r ≤ Nat.log2 (levelScale l) + d ∧ Nat.log2 (levelScale l) + d ≤ levelScale l := by
  have hj_adm := activated_admissible P d j tick hj
  have hl_adm := activated_admissible P d l tick hl
  have hupper := fighter_previous_upper_bound j l hj_adm.1 hjl
  have hr_bound := target_le_upper_add d j r kind hr
  obtain ⟨hn, hd, _⟩ := fighter_admissible_square P d l hl_adm
  have hpad := fighter_log_padding_bound (levelScale l) d hn hd
  constructor <;> omega

/-- If any completed state has failed, a started level has a positive target whose entire
input pool is occupied. The witness is used in the description-capacity counting argument. -/
lemma saturated_target_of_failure (P : FighterParams) (d : ℕ) :
    (∃ tick, (fighterState P d tick).failed = true) →
    ∃ t r l kind, FighterActivated P d l t ∧ FighterTargetRange d l kind r ∧ r > 0 ∧
      ∀ p ∈ fighterInputs d (r - 1),
        (fighterState P d t).allocated.any (fun a ↦ a.input == p) = true := by
  rintro ⟨tick, hfailed⟩
  by_cases hd : d = 0
  · subst d
    cases tick with
    | zero => cases hfailed
    | succ tick =>
      change (fighter_actions P 0 (tick + 1) (fighterState P 0 tick)).failed = true at hfailed
      simp [fighter_actions, initialFighterState] at hfailed
  · obtain ⟨r, l, kind, hstarted, hrange, hr, hall⟩ :=
      (fighter_state_accounting P d tick (by omega)).2 hfailed
    exact ⟨tick, r, l, kind, hstarted, hrange, hr, hall⟩

end Kolmogorov.Milovanov
