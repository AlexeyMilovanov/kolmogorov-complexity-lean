/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.AllocationGraph
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.FundedFrames
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.LiveCounters
import KolmogorovMathlib.RandomStrings.Plain.Construction.Diagonal.SimulationEvents

/-!
# Payoff directives are funded

A payoff directive in the permanent allocation graph of the fighter simulation is issued by a
phase for a coordinate `(output, target)` of its retained set.  The main result
`fighterState_payoff_receipt` says that at every tick, each payoff directive has a *receipt*:
a witness that its coordinate was funded, i.e. that the price of the coordinate does not exceed
the value of its live counter, in the phase that issued it.  The witness lives either in the
active phase of the directive's level with the directive's candidate, or in an entry of the
cancellation archive `FighterState.ended`.

The proof is an induction over the ticks.  The invariant combines two phase-level facts: live
counters equal the number of stored indices (`Diagonal.LiveCounters`), and every pending request
of a phase is funded.  Funding survives every update of a phase because counters only grow
(`FighterPhase.Grows`), and a payoff is allocated only for a pending request.

The statement is used in `Diagonal.OracleAgreement` to turn a payoff of the true-marker phase
into a positive answer of its limiting phase oracle.
-/

namespace Kolmogorov.Milovanov

/-- The coordinate `q` is retained by `p` and its price is covered by its live counter. -/
private abbrev Funded (d : ℕ) (p : FighterPhase) (q : Coordinate) : Prop :=
  q ∈ p.J d ∧ (p.game d).price q ≤ (p.game d).coordinateValue p.liveCounters q

/-- Live counters of retained coordinates count the stored indices, and every pending request is
funded. -/
private abbrev PhaseFunding (d : ℕ) (p : FighterPhase) : Prop :=
  (∀ q ∈ p.J d, (p.game d).coordinateValue p.liveCounters q = (p.indicesAt d q).card) ∧
    ∀ q ∈ p.pending, Funded d p q

/-- A payoff directive `a` is funded in the active phase of its level, or in a cancelled phase
of the same level and candidate. -/
private abbrev PayoffReceipt (d : ℕ) (s : FighterState) (a : AllocatedDirective) : Prop :=
  (∃ p, s.activeAt d a.level = some p ∧ p.candidate = a.candidate ∧
    Funded d p (a.output, a.target)) ∨
  ∃ e ∈ s.ended, e.1.level = a.level ∧ e.1.candidate = a.candidate ∧
    Funded d e.1 (a.output, a.target)

/-- The invariant of a simulation state: all active phases are consistently funded and all
payoff directives have a receipt. -/
private abbrev ReceiptInv (d : ℕ) (s : FighterState) : Prop :=
  (∀ p ∈ s.active, PhaseFunding d p) ∧ ∀ a ∈ s.allocated, a.kind = .payoff → PayoffReceipt d s a

section

variable (P : FighterParams) {d : ℕ}

private lemma funded_of_grows {p r : FighterPhase} (hg : FighterPhase.Grows d p r)
    {q : Coordinate} (hq : Funded d p q) : Funded d r q := by
  refine ⟨?_, ?_⟩
  · change q ∈ (r.game d).J
    rw [hg.2.2.1]
    exact hq.1
  · rw [hg.2.2.1]
    have h := hq.2.trans (hg.2.2.2 q)
    rwa [hg.2.2.1] at h

private lemma ReceiptInv.phase {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : ReceiptInv d s) (hp : s.activeAt d l = some p) : PhaseFunding d p :=
  hs.1 p (List.mem_of_find?_eq_some hp)

private lemma ReceiptInv.of_eq {s t : FighterState} (hs : ReceiptInv d s)
    (ha : t.allocated = s.allocated) (hp : t.active = s.active) (he : t.ended = s.ended) :
    ReceiptInv d t := by
  refine ⟨fun p h ↦ hs.1 p (hp ▸ h), ?_⟩
  intro a h hkind
  rcases hs.2 a (ha ▸ h) hkind with ⟨p, hlook, hc, hf⟩ | ⟨e, hem, hl, hc, hf⟩
  · exact Or.inl ⟨p, by simpa only [FighterState.activeAt, hp] using hlook, hc, hf⟩
  · exact Or.inr ⟨e, he ▸ hem, hl, hc, hf⟩

/-- Replacing the phase of a level by a phase that grows the old one keeps the invariant. -/
private lemma ReceiptInv.putPhase {s : FighterState} {p : FighterPhase}
    (hs : ReceiptInv d s) (hp : PhaseFunding d p)
    (hg : ∀ old, s.activeAt d p.level = some old → FighterPhase.Grows d old p) :
    ReceiptInv d (s.putPhase d p) := by
  refine ⟨?_, ?_⟩
  · intro next hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hp
    · exact hs.1 next (List.mem_filter.mp hn).1
  · intro a ha hk
    rcases hs.2 a ha hk with ⟨old, hold, hc, hf⟩ | ⟨e, he, hl, hc, hf⟩
    · by_cases hl : a.level = p.level
      · have hgrowth := hg old (by simpa only [hl] using hold)
        exact Or.inl ⟨p, by simp [FighterState.putPhase, FighterState.activeAt, hl],
          hgrowth.2.1.trans hc, funded_of_grows hgrowth hf⟩
      · exact Or.inl ⟨old,
          (FighterState.activeAt_putPhase_of_ne d a.level s p hl).trans hold, hc, hf⟩
    · exact Or.inr ⟨e, he, hl, hc, hf⟩

private lemma ReceiptInv.putPhase_of_grows {s : FighterState} {old p : FighterPhase}
    (hs : ReceiptInv d s) (hold : s.activeAt d old.level = some old) (hp : PhaseFunding d p)
    (hg : FighterPhase.Grows d old p) : ReceiptInv d (s.putPhase d p) := by
  apply hs.putPhase hp
  intro r hr
  rw [hg.1, hold] at hr
  obtain rfl := Option.some.inj hr
  exact hg

private lemma PhaseFunding.fundRequests {p : FighterPhase} (hp : PhaseFunding d p)
    (fulfilled : List Coordinate) : PhaseFunding d (p.fundRequests d fulfilled) := by
  refine ⟨hp.1, ?_⟩
  intro q hq
  simp only [FighterPhase.fundRequests, List.mem_eraseDups, List.mem_filter,
    List.mem_append, decide_eq_true_eq] at hq
  rcases hq.1 with hold | ⟨hcoords, hprice⟩
  · exact hp.2 q hold
  · have hret : q ∈ p.J d := by
      simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
        List.mem_toFinset, List.mem_eraseDups] using hcoords
    refine ⟨hret, ?_⟩
    change (p.game d).price q ≤ (p.game d).coordinateValue p.liveCounters q
    rw [hp.1 q hret]
    exact hprice

private lemma PhaseFunding.insertIndex {p : FighterPhase} (q : Coordinate) (index : BitString)
    (hp : PhaseFunding d p) (hfresh : index ∉ p.indicesAt d q) :
    PhaseFunding d (p.insertIndex d q index) := by
  refine ⟨insertIndex_counter_eq_card_indicesAt d p q index hp.1 hfresh, ?_⟩
  intro r hr
  exact funded_of_grows (FighterPhase.Grows.insertIndex d p q index) (hp.2 r hr)

private lemma ReceiptInv.cancel (l cause : ℕ) (reason : PhaseEnd) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · rename_i phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    refine ⟨fun p hp ↦ hs.1 p (List.mem_filter.mp hp).1, ?_⟩
    intro a ha hk
    rcases hs.2 a ha hk with ⟨p, hp, hc, hf⟩ | ⟨e, he, hel, hc, hf⟩
    · by_cases hal : a.level = l
      · have heq : p = phase := Option.some.inj ((hal ▸ hp).symm.trans hphase)
        subst p
        exact Or.inr ⟨({ phase with pending := [] }, s.tick, reason, cause),
          List.mem_append_right _ (List.mem_singleton.mpr rfl), hl.trans hal.symm, hc, hf⟩
      · exact Or.inl ⟨p, by
          change (s.active.filter (fun p ↦ p.level != l)).find?
            (fun p ↦ p.level == a.level) = some p
          rwa [FighterState.find?_level_filter_ne _ _ _ hal], hc, hf⟩
    · exact Or.inr ⟨e, List.mem_append_left _ he, hel, hc, hf⟩

private lemma ReceiptInv.abortAbove (l : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  refine List.foldlRecOn (motive := ReceiptInv d) _ _ hs fun t ht p _ ↦ ?_
  split
  · exact ht.cancel _ _ _
  · exact ht

/-- A successful allocation keeps the invariant, provided a payoff is only allocated for a
coordinate that is funded in the phase of its level. -/
private lemma ReceiptInv.allocate (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    {s : FighterState} (hs : ReceiptInv d s)
    (hrequest : kind = .payoff → ∀ p, s.activeAt d l = some p → Funded d p (out, target)) :
    ReceiptInv d (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · rename_i phase hphase
    cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      exact ReceiptInv.cancel l l .saturated (hs.of_eq rfl rfl rfl)
    | some input =>
      apply ReceiptInv.abortAbove
      refine ⟨hs.1, ?_⟩
      intro a ha hk
      rcases List.mem_append.mp ha with ha | ha
      · exact hs.2 a ha hk
      · obtain rfl := List.mem_singleton.mp ha
        exact Or.inl ⟨phase, hphase, rfl, hrequest hk phase hphase⟩

private lemma ReceiptInv.recordFulfilled (q : Coordinate) {s : FighterState}
    (hs : ReceiptInv d s) :
    ReceiptInv d { s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) }) } := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
    exact ⟨(hs.1 old hold).1, fun r hr ↦ (hs.1 old hold).2 r (List.mem_filter.mp hr).1⟩
  · intro a ha hk
    rcases hs.2 a ha hk with ⟨p, hp, hc, hf⟩ | ⟨e, he, hl, hc, hf⟩
    · refine Or.inl ⟨{ p with pending := p.pending.filter (· != q) }, ?_, hc, hf⟩
      change (s.active.map (fun p ↦ { p with pending := p.pending.filter (· != q) })).find?
        (fun p ↦ p.level == a.level) = _
      simpa only [FighterState.activeAt, List.find?_map, Function.comp_def,
        Option.map_some] using
        congrArg (Option.map (fun p : FighterPhase ↦
          { p with pending := p.pending.filter (· != q) })) hp
    · exact Or.inr ⟨e, he, hl, hc, hf⟩

private lemma ReceiptInv.payoff (l : ℕ) (q : Coordinate) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · rename_i phase hphase
    split
    · rename_i hguard
      have ha := hs.allocate l .payoff q.2 q.1 (fun _ p hp ↦ by
        have heq : p = phase := Option.some.inj (hp.symm.trans hphase)
        subst p
        exact (hs.phase hphase).2 q hguard.1)
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact ha.recordFulfilled q
    · exact hs

private lemma ReceiptInv.fulfillReady (l : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn (motive := ReceiptInv d) _ _ hs fun t ht _ _ ↦ ht.payoff P l _

/-- One unit of fuel spent on a coordinate keeps the invariant: the charged phase and the phase
with the new index inserted both grow the old phase. -/
private lemma ReceiptInv.fuelUnit (l : ℕ) (q : Coordinate) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hphase
    have hp := hs.phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · rename_i hguard
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hcharged : ReceiptInv d (s.putPhase d charged) :=
        hs.putPhase_of_grows (old := phase) (by simpa only [hl] using hphase) hp
          (FighterPhase.Grows.refl d phase)
      have ha := hcharged.allocate l .fuel (levelUpper l + d) out (by intro h; cases h)
      change ReceiptInv d
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
        · have hstay : next.activeAt d charged.level = some charged := by
            have h := FighterState.activeAt_fighterAllocate_of_success d l .fuel
              (levelUpper l + d) out (s.putPhase d charged) (by rw [he])
            rw [he] at h
            simpa [FighterState.putPhase, FighterState.activeAt, charged, hl] using h
          have hfresh : index ∉ charged.indicesAt d q := by
            simp only [FighterPhase.indicesAt,
              show charged.game d = phase.game d from rfl, hguard.1, ite_true,
              List.mem_toFinset]
            exact fighterFreshString_notMem d _
          have hins := (hp.insertIndex (d := d) q index hfresh).fundRequests next.fulfilled
          have hg : FighterPhase.Grows d charged
              ((charged.insertIndex d q index).fundRequests d next.fulfilled) :=
            FighterPhase.Grows.insertIndex d charged q index
          exact ReceiptInv.fulfillReady P l (ha.putPhase_of_grows hstay hins hg)
    · exact hs

private lemma ReceiptInv.fuelUnits (l : ℕ) (q : Coordinate) (count : ℕ) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih (hs.fuelUnit P l q)

private lemma ReceiptInv.dummy (l : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hphase
    have hp := hs.phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := hs.allocate l .dummy (levelInput d l) output (by intro h; cases h)
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · have hstay : next.activeAt d phase.level = some phase := by
              have h := FighterState.activeAt_fighterAllocate_of_success d l .dummy
                (levelInput d l) output s (by rw [he])
              rw [he] at h
              simpa only [hl] using h.trans hphase
            exact ha.putPhase_of_grows (old := phase) hstay hp (FighterPhase.Grows.refl d phase)

private lemma ReceiptInv.opponent (l : ℕ) (e : ProgramEvent) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hphase
    have hp := hs.phase hphase
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hphase
    split
    · exact hs
    · rename_i q index hpair
      split
      · exact hs
      · rename_i hfresh
        split
        · exact hs.cancel _ _ _
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          have hn : PhaseFunding d next := hp.insertIndex q index hfresh
          have hg : FighterPhase.Grows d phase (next.fundRequests d s.fulfilled) :=
            FighterPhase.Grows.insertIndex d phase q index
          exact ReceiptInv.fulfillReady P l (hs.putPhase_of_grows (old := phase)
            (by simpa only [hl] using hphase) (hn.fundRequests s.fulfilled) hg)

private lemma ReceiptInv.startPhase (l : ℕ) (c : Candidate) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hw : ReceiptInv d waiting := (hs.cancel l l .replaced).abortAbove l
  have hempty : waiting.activeAt d l = none := by
    rw [activeAt_fighterAbortAbove_of_le d l l _ le_rfl]
    unfold fighterCancel
    split
    · assumption
    · simp [FighterState.activeAt, List.find?_filter]
  have hp : PhaseFunding d (fighter_construction P d l c waiting) := by
    have hcount := fighter_construction_counter_eq_card_indicesAt P d l c waiting
    unfold fighter_construction
    apply PhaseFunding.fundRequests
    exact ⟨hcount, fun q hq ↦ (List.not_mem_nil hq).elim⟩
  have hput : ReceiptInv d (waiting.putPhase d (fighter_construction P d l c waiting)) := by
    apply hw.putPhase hp
    intro old hold
    have hlevel : (fighter_construction P d l c waiting).level = l := rfl
    rw [hlevel, hempty] at hold
    contradiction
  exact hput.of_eq rfl rfl rfl

private lemma ReceiptInv.flushBuffer (l : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hgood := hs.phase hp
    have hl := FighterState.level_eq_of_activeAt_eq_some (p := phase) hp
    simp only [bind, Option.bind_some]
    split
    · exact hs.putPhase_of_grows (old := phase) (by simpa only [hl] using hp) hgood
        (FighterPhase.Grows.refl d phase)
    · exact hs

private lemma ReceiptInv.strategyMove (l : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d ((fighterStrategyMove P d l s).getD s) := by
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
          have hn : ReceiptInv d next :=
            List.foldlRecOn (motive := ReceiptInv d) _ _ hs fun t ht qi _ ↦
              ht.fuelUnits P l qi.1 (move[qi.2]?.getD 0)
          change ReceiptInv d ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            have hgood := hn.phase hlive
            have hl := FighterState.level_eq_of_activeAt_eq_some (p := live) hlive
            exact hn.putPhase_of_grows (old := live) (by simpa only [hl] using hlive) hgood
              (FighterPhase.Grows.refl d live)
        · exact hs
    · exact hs

private lemma ReceiptInv.levelAction (l : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact hs.dummy l
    · split
      · exact hs.payoff P l _
      · cases hf : fighterFlushBuffer d l s with
        | none => exact hs.strategyMove P l
        | some next =>
          simpa only [hf, Option.getD_some] using hs.flushBuffer l

private lemma ReceiptInv.closure (l fuel : ℕ) {s : FighterState} (hs : ReceiptInv d s) :
    ReceiptInv d (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := hs.levelAction P l
      simp only [ha, Option.getD_some] at hn
      exact ih hn

private lemma ReceiptInv.processLevel (l : ℕ) (e : Option TimedEvent) {s : FighterState}
    (hs : ReceiptInv d s) : ReceiptInv d (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply ReceiptInv.closure
  cases e with
  | none => exact hs.fulfillReady P l
  | some e =>
    dsimp only
    split
    · exact (hs.fulfillReady P l).startPhase P l _
    · exact (hs.fulfillReady P l).opponent P l _

private lemma receiptInv_fighterState (d tick : ℕ) : ReceiptInv d (fighterState P d tick) := by
  induction tick with
  | zero => simp [ReceiptInv, fighterState, initialFighterState]
  | succ tick ih =>
    change ReceiptInv d (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [ReceiptInv, initialFighterState]
    · exact List.foldlRecOn (motive := ReceiptInv d) _ _ (ih.of_eq rfl rfl rfl)
        fun t ht l _ ↦ ht.processLevel P l _

end

/-- Every payoff directive allocated by tick `tick` has a funded witness in its issuing phase,
which is the active phase of its level and candidate or an entry of the cancellation archive.
The witness coordinate is retained by the phase, and its price is covered by the live counter. -/
theorem fighterState_payoff_receipt (P : FighterParams) (d tick : ℕ) :
    ∀ a ∈ (fighterState P d tick).allocated, a.kind = .payoff →
      (∃ phase, (fighterState P d tick).activeAt d a.level = some phase ∧
        phase.candidate = a.candidate ∧ (a.output, a.target) ∈ phase.J d ∧
        (phase.game d).price (a.output, a.target) ≤
          (phase.game d).coordinateValue phase.liveCounters (a.output, a.target)) ∨
      ∃ e ∈ (fighterState P d tick).ended,
        e.1.level = a.level ∧ e.1.candidate = a.candidate ∧
        (a.output, a.target) ∈ e.1.J d ∧
        (e.1.game d).price (a.output, a.target) ≤
          (e.1.game d).coordinateValue e.1.liveCounters (a.output, a.target) :=
  (receiptInv_fighterState P d tick).2

end Kolmogorov.Milovanov
