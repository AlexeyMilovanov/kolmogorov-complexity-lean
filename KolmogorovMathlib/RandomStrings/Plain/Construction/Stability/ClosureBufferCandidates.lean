/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.AllocationOccupancy
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferInitialization
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ClosureBufferActions

/-!
# Candidates and buffers during closure

Closure actions preserve the candidate of every surviving phase. Combining this fact with
buffer initialization and preservation for individual actions gives the buffer invariant
throughout the true-marker closure. The module also proves that successful fuel processing
keeps the issuing phase active and that allocation failures persist, facts used by
`StrategyClosure` to establish the legality of the opponent stream for blueprint node
`constr:opponent`. The common-game arguments use candidate preservation to identify the
surviving phase and failure persistence to rule out cancellations during closure.
-/

namespace Kolmogorov.Milovanov

/-- Every phase active after an action has the candidate of a phase active before it. -/
private def CandidatePreserved (d l : ℕ) (before after : FighterState) : Prop :=
  ∀ p', after.activeAt d l = some p' →
    ∃ p, before.activeAt d l = some p ∧ p.candidate = p'.candidate

/-- Allocating the dummy changes only the issuance flag of a surviving phase. -/
private lemma candidate_preserved_dummy
    (d l : ℕ) (state : FighterState) :
    CandidatePreserved d l state (fighterDummy d l state) := by
  intro live hlive
  unfold fighterDummy at hlive
  cases hp : state.activeAt d l with
  | none => simp [hp] at hlive
  | some phase =>
    simp only [hp] at hlive
    cases hd : phase.dummy with
    | none =>
      simp only [hd] at hlive
      exact ⟨live, hp.symm.trans hlive, rfl⟩
    | some output =>
      simp only [hd] at hlive
      split at hlive
      · exact ⟨live, hp.symm.trans hlive, rfl⟩
      · have ha := activeAt_fighterAllocate d l state .dummy (levelInput d l) output
        cases he : fighterAllocate d l .dummy (levelInput d l) output state with
        | mk next success =>
          rw [he] at ha hlive
          cases success with
          | false =>
            simp only [Bool.false_eq_true, ite_false] at hlive ha
            rw [ha] at hlive
            contradiction
          | true =>
            simp only [ite_true] at hlive
            have hlevel : phase.level = l :=
              beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
            rw [FighterState.activeAt_putPhase d l next
              { phase with dummy := some output, dummyIssued := true } hlevel] at hlive
            cases hlive
            exact ⟨phase, rfl, rfl⟩

/-- A payoff only changes the pending requests of a surviving phase. -/
private lemma candidate_preserved_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState) :
    CandidatePreserved d l state (fighterPayoff P d l q state) := by
  intro live hlive
  obtain ⟨old, hold, pending, rfl⟩ :=
    pending_update_of_activeAt_fighterPayoff P d l q state live hlive
  exact ⟨old, hold, rfl⟩

/-- The flush branch preserves the candidate. -/
private lemma candidate_preserved_flushBuffer
    (d l : ℕ) (state next : FighterState) :
    fighterFlushBuffer d l state = some next → CandidatePreserved d l state next := by
  intro hflush p' hp'
  unfold fighterFlushBuffer at hflush
  simp only [bind, Option.bind] at hflush
  cases hphase : state.activeAt d l with
  | none => simp [hphase] at hflush
  | some phase =>
    simp only [hphase] at hflush
    split at hflush
    · injection hflush with hnext
      subst hnext
      use phase
      refine ⟨rfl, ?_⟩
      have hlevel : phase.level = l := by
        exact beq_iff_eq.mp (List.find?_some (p := fun phase : FighterPhase ↦ phase.level == l)
          hphase)
      unfold FighterState.putPhase FighterState.activeAt at hp'
      have h_eq : (fun (p : FighterPhase) ↦ p.level == l)
          { phase with
            officialCode := ((phase.game d).afterMove (phase.official d) phase.buffer).encode
            buffer := List.replicate (phase.game d).coordinates.length 0 } = true := by
        simp only [beq_iff_eq]
        exact hlevel
      simp only [List.find?_cons, h_eq] at hp'
      injection hp' with heq
      rw [←heq]
    · simp at hflush

/-- One designated fuel unit preserves the candidate of every surviving phase. -/
private lemma candidate_preserved_fuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (state : FighterState) :
    CandidatePreserved d l state (fighterFuelUnit P d l q state) := by
  intro live hlive
  cases hp : state.activeAt d l with
  | none =>
    simp [fighterFuelUnit, hp] at hlive
  | some p =>
    by_cases hg : q ∈ (p.game d).coordinates ∧
        0 < p.controlledRemaining
    · have hlevel : p.level = l :=
        beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
      let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
      let index := fighterFreshString d (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
      revert live
      simp only [fighterFuelUnit, hp, ite_eq_left hg]
      have ha :=
        activeAt_fighterAllocate
          d l (state.putPhase d charged) .fuel
          (levelUpper l + d) output
      cases he : fighterAllocate d l .fuel (levelUpper l + d)
          output (state.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;>
          simp only [Bool.false_eq_true, ite_false, ite_true] at ha ⊢
        · intro live hlive
          rw [ha] at hlive
          contradiction
        · intro live hlive
          obtain ⟨old, hold, pending, rfl⟩ :=
            pending_update_of_activeAt_fighterFulfillReady
              P d l _ live hlive
          have hput :
              (next.putPhase d
                ((charged.insertIndex d q index).fundRequests d
                  next.fulfilled)).activeAt d l =
                some ((charged.insertIndex d q index).fundRequests d
                  next.fulfilled) := by
            simp [FighterState.putPhase, FighterState.activeAt,
              FighterPhase.fundRequests, FighterPhase.insertIndex,
              charged, hlevel]
          rw [hput] at hold
          cases hold
          exact ⟨p, rfl, rfl⟩
    · have heq : p = live := by
        revert hlive
        simp [fighterFuelUnit, hp, hg]
      subst heq
      exact ⟨p, rfl, rfl⟩

/-- The fuel units fold preserves the candidate. -/
private lemma candidate_preserved_fuelUnits
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (state : FighterState) :
    CandidatePreserved d l state (fighterFuelUnits P d l q count state) := by
  induction count generalizing state with
  | zero =>
    intro p' hp'
    exact ⟨p', hp', rfl⟩
  | succ count ih =>
    intro p' hp'
    obtain ⟨mid, hmid, hcandidate⟩ :=
      ih (fighterFuelUnit P d l q state) p' hp'
    obtain ⟨old, hold, heq⟩ :=
      candidate_preserved_fuelUnit
        P d l q state mid hmid
    exact ⟨old, hold, heq.trans hcandidate⟩

/-- Coordinate batches preserve surviving candidates. -/
private lemma candidate_preserved_fuel_fold
    (P : FighterParams) (d l : ℕ) (state : FighterState)
    (coords : List (Coordinate × ℕ)) (move : CounterMove) :
    CandidatePreserved d l state
      (coords.foldl (fun s (q, i) ↦
        fighterFuelUnits P d l q (move[i]?.getD 0) s) state) := by
  induction coords generalizing state with
  | nil =>
    intro p' hp'
    exact ⟨p', hp', rfl⟩
  | cons head tail ih =>
    intro p' hp'
    have h1 := ih (fighterFuelUnits P d l head.1 (move[head.2]?.getD 0) state) p' hp'
    rcases h1 with ⟨p_mid, hp_mid, hpcand_mid⟩
    have h2 := candidate_preserved_fuelUnits P d l head.1 (move[head.2]?.getD 0) state p_mid hp_mid
    rcases h2 with ⟨p0, hp0, hp0cand⟩
    exact ⟨p0, hp0, hp0cand.trans hpcand_mid⟩

/-- Installing the surviving phase's official code preserves its candidate. -/
private lemma candidate_preserved_update_officialCode
    (d l : ℕ) (state middle next : FighterState)
    (code : CounterPositionCode)
    (hpres : CandidatePreserved d l state middle)
    (h : (match middle.activeAt d l with
      | none => some middle
      | some live => some (middle.putPhase d
          { live with officialCode := code })) = some next) :
    CandidatePreserved d l state next := by
  cases hv : middle.activeAt d l with
  | none =>
    simp only [hv, Option.some.injEq] at h
    subst next
    exact hpres
  | some live =>
    simp only [hv, Option.some.injEq] at h
    subst next
    intro p hp
    have hl : live.level = l :=
      beq_iff_eq.mp (List.find?_some
        (p := fun p : FighterPhase ↦ p.level == l) hv)
    have hu : (middle.putPhase d
        { live with officialCode := code }).activeAt d l =
        some { live with officialCode := code } := by
      simp [FighterState.putPhase, FighterState.activeAt, hl]
    rw [hu] at hp
    cases hp
    exact hpres live hv

/-- The strategy branch preserves the candidate. -/
private lemma candidate_preserved_strategyMove
    (P : FighterParams) (d l : ℕ) (state next : FighterState) :
    fighterStrategyMove P d l state = some next → CandidatePreserved d l state next := by
  intro h
  cases hp : state.activeAt d l with
  | none => simp [fighterStrategyMove, hp] at h
  | some p =>
    simp only [fighterStrategyMove, hp, bind, Option.bind_some] at h
    split at h
    · cases hm : (p.game d).strategy (p.official d) with
      | none => simp [hm] at h
      | some m =>
        simp only [hm, Option.bind_some] at h
        split at h
        · exact
            candidate_preserved_update_officialCode
              d l state _ next
              (((p.game d).afterMove (p.official d) m).encode)
              (candidate_preserved_fuel_fold
                P d l state (p.game d).coordinates.zipIdx m)
              h
        · contradiction
    · contradiction

/-- Every phase surviving a level action has the same candidate as the phase active before
that action. -/
lemma candidate_eq_of_activeAt_fighterLevelAction
    (P : FighterParams) (d l : ℕ) (state next : FighterState) :
    fighterLevelAction P d l state = some next →
    ∀ p', next.activeAt d l = some p' →
    ∃ p, state.activeAt d l = some p ∧ p.candidate = p'.candidate := by
  intro hact p' hp'
  have hpres : CandidatePreserved d l state next := by
    unfold fighterLevelAction at hact
    cases hactive : state.activeAt d l with
    | none => simp [hactive] at hact
    | some phase =>
      simp only [hactive, bind, Option.bind_some, Bool.and_eq_true, Bool.not_eq_true'] at hact
      by_cases hdummy : phase.dummy.isSome = true ∧ phase.dummyIssued = false
      · simp only [hdummy, and_self, ite_true, Option.some.injEq] at hact
        subst hact
        exact candidate_preserved_dummy d l state
      · simp only [hdummy, ite_false] at hact
        generalize hq : phase.pending.find? (fun q ↦
          decide (q ∉ state.fulfilled) && fighterSafe P d state.tick q) = oq at hact
        cases oq with
        | some q =>
          change some (fighterPayoff P d l q state) = some next at hact
          injection hact with hnext
          subst next
          exact candidate_preserved_payoff P d l q state
        | none =>
          change (match fighterFlushBuffer d l state with
            | some next => some next
            | none => fighterStrategyMove P d l state) = some next at hact
          generalize hflush : fighterFlushBuffer d l state = oflush at hact
          cases oflush with
          | some flushed =>
            change some flushed = some next at hact
            injection hact with hnext
            subst next
            exact candidate_preserved_flushBuffer d l state flushed hflush
          | none =>
            change fighterStrategyMove P d l state = some next at hact
            exact candidate_preserved_strategyMove P d l state next hact
  exact hpres p' hp'

/-- A true-marker phase satisfies the buffer invariant at every bounded closure iterate
at or after the marker tick. -/
lemma bufferInvariant_closureAt
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∀ tick ≥ markerTick P.B (levelScale l), ∀ step,
      step ≤ fighterClosureFuel d l (fighterBeforeClosure P d tick l) →
      ∀ phase,
        (fighterClosureAt P d tick l step).activeAt d l = some phase →
        phase.candidate = markerCandidate P.B (levelScale l) →
        phase.BufferInvariant d := by
  intro tick htick step _ phase hphase hcand
  unfold fighterClosureAt at hphase
  have hind : ∀ step' state,
    (∀ p, state.activeAt d l = some p → p.candidate = markerCandidate P.B (levelScale l) →
      p.BufferInvariant d) →
    ∀ p', (fighterClosure P d l step' state).activeAt d l = some p' →
      p'.candidate = markerCandidate P.B (levelScale l) →
      p'.BufferInvariant d := by
    intro step'
    induction step' with
    | zero =>
      intro state hinit p' hp' hcand'
      exact hinit p' hp' hcand'
    | succ step' ih =>
      intro state hinit p' hp' hcand'
      rw [fighterClosure] at hp'
      cases hact : fighterLevelAction P d l state with
      | none =>
        rw [hact] at hp'
        exact hinit p' hp' hcand'
      | some next =>
        rw [hact] at hp'
        apply ih next _ p' hp' hcand'
        intro p'' hp'' hcand''
        have hcand_preserve :=
          candidate_eq_of_activeAt_fighterLevelAction P d l state next
          hact p'' hp''
        rcases hcand_preserve with ⟨p, hp, hcand_eq⟩
        have hp_cand : p.candidate = markerCandidate P.B (levelScale l) := by
          rw [hcand_eq, hcand'']
        have hp_inv : p.BufferInvariant d := hinit p hp hp_cand
        exact bufferInvariant_activeAt_fighterLevelAction P d l state next p hp hp_inv hact p'' hp''
  exact hind step (fighterBeforeClosure P d tick l)
    (bufferInvariant_beforeClosure P C cGap cRank d₀ d l hfixed hgood hlate tick htick)
    phase hphase hcand

/-- Processing a controlled move's fuel units and immediate payoffs keeps the issuing level
active whenever the final state has no allocation failure. -/
lemma exists_activeAt_fuel_fold_of_not_failed
    (P : FighterParams) (d l : ℕ)
    (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase)
    (move : List ℕ)
    (hfailed : ((phase.game d).coordinates.zipIdx.foldl
      (fun s (q, i) ↦
        fighterFuelUnits P d l q (move[i]?.getD 0) s)
      state).failed = false) :
    ∃ live, ((phase.game d).coordinates.zipIdx.foldl
      (fun s (q, i) ↦
        fighterFuelUnits P d l q (move[i]?.getD 0) s)
      state).activeAt d l = some live := by
  let Good (s : FighterState) : Prop :=
    s.failed = true ∨ ∃ live, s.activeAt d l = some live
  have halloc (kind : DirectiveKind) (target : ℕ) (out : BitString)
      (s : FighterState) (hs : Good s) :
      Good (fighterAllocate d l kind target out s).1 := by
    cases hp : s.activeAt d l with
    | none => simpa only [fighterAllocate, hp] using hs
    | some p =>
      have ha := fighterAllocate_spec d l target kind out s p hp
      cases hb : (fighterAllocate d l kind target out s).2 with
      | false => exact Or.inl (ha.1 hb).1
      | true =>
        obtain ⟨_, _, _, _, _, _, _, hactive⟩ := ha.2 hb
        exact Or.inr ⟨p, hactive⟩
  have hpay (q : Coordinate) (s : FighterState) (hs : Good s) :
      Good (fighterPayoff P d l q s) := by
    unfold fighterPayoff
    split
    · exact hs
    · split
      · have ha := halloc .payoff q.2 q.1 s hs
        cases he : fighterAllocate d l .payoff q.2 q.1 s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · rcases ha with hf | ⟨live, hlive⟩
            · exact Or.inl hf
            · right
              refine ⟨{ live with pending := live.pending.filter (fun r ↦ r != q) }, ?_⟩
              simp only [FighterState.activeAt, List.find?_map]
              change (next.activeAt d l).map (fun p ↦
                { p with pending := p.pending.filter (fun r ↦ r != q) }) = _
              rw [hlive]
              rfl
      · exact hs
  have hfulfill (s : FighterState) (hs : Good s) :
      Good (fighterFulfillReady P d l s) := by
    unfold fighterFulfillReady
    split
    · exact hs
    · exact foldl_preserves_invariant Good _ _ (fun t q ht ↦ hpay q t ht) hs
  have hunit (q : Coordinate) (s : FighterState) (hs : Good s) :
      Good (fighterFuelUnit P d l q s) := by
    unfold fighterFuelUnit
    split
    · exact hs
    · rename_i p hp
      split
      · have hlevel : p.level = l :=
          beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
        let charged := { p with controlledRemaining := p.controlledRemaining - 1 }
        let index := fighterFreshString d
          (p.indices[(p.game d).coordinates.idxOf q]?.getD [])
        let out := pairCode (triple q.1 (q.2 - d) p.candidate.1) index
        have hcharged : Good (s.putPhase d charged) := by
          right
          exact ⟨charged, by simp [FighterState.putPhase, FighterState.activeAt, charged, hlevel]⟩
        have ha := halloc .fuel (levelUpper l + d) out (s.putPhase d charged) hcharged
        change Good
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
          · apply hfulfill
            right
            refine ⟨(charged.insertIndex d q index).fundRequests d next.fulfilled, ?_⟩
            simp [FighterState.putPhase, FighterState.activeAt, FighterPhase.fundRequests,
              FighterPhase.insertIndex, charged, hlevel]
      · exact hs
  have hunits (q : Coordinate) (count : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterFuelUnits P d l q count s) := by
    induction count generalizing s with
    | zero => exact hs
    | succ count ih => exact ih _ (hunit q s hs)
  have hresult : Good ((phase.game d).coordinates.zipIdx.foldl
      (fun s (q, i) ↦ fighterFuelUnits P d l q (move[i]?.getD 0) s) state) :=
    foldl_preserves_invariant Good _ _
      (fun s qi hs ↦ hunits qi.1 (move[qi.2]?.getD 0) s hs) (Or.inr ⟨phase, hphase⟩)
  rcases hresult with hf | hactive
  · rw [hfailed] at hf
    cases hf
  · exact hactive

private lemma fighterPayoff_failed_of_failed (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) (hs : s.failed = true) :
    (fighterPayoff P d l q s).failed = true := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := fighterAllocate_failed_of_failed d l q.2 .payoff q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact ha
    · exact hs

private lemma fighterFulfillReady_failed_of_failed (P : FighterParams) (d l : ℕ)
    (s : FighterState) (hs : s.failed = true) :
    (fighterFulfillReady P d l s).failed = true := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl_preserves_invariant (fun s : FighterState ↦ s.failed = true) _ _
      (fun s q hs ↦ fighterPayoff_failed_of_failed P d l q s hs) hs

private lemma fighterFuelUnit_failed_of_failed (P : FighterParams) (d l : ℕ)
    (q : Coordinate) (s : FighterState) (hs : s.failed = true) :
    (fighterFuelUnit P d l q s).failed = true := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := fighterAllocate_failed_of_failed d l (levelUpper l + d) .fuel out
        (s.putPhase d charged) hs
      change (match fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
          | (next, success) => if success then
            fighterFulfillReady P d l
              (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
            else next).failed = true
      cases he : fighterAllocate d l .fuel (levelUpper l + d) out (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · exact fighterFulfillReady_failed_of_failed P d l _ ha
    · exact hs

/-- Executing a controlled strategy move cannot clear an allocation failure. -/
private lemma fighterStrategyMove_failed_of_failed (P : FighterParams) (d l : ℕ)
    (s : FighterState) (hs : s.failed = true) :
    ((fighterStrategyMove P d l s).getD s).failed = true := by
  have hunits (q : Coordinate) (count : ℕ) (s : FighterState) (hs : s.failed = true) :
      (fighterFuelUnits P d l q count s).failed = true := by
    induction count generalizing s with
    | zero => exact hs
    | succ count ih => exact ih _ (fighterFuelUnit_failed_of_failed P d l q s hs)
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
          have hn : next.failed = true :=
            foldl_preserves_invariant (fun s : FighterState ↦ s.failed = true) _ _
              (fun t qi ht ↦ hunits qi.1 (move[qi.2]?.getD 0) t ht) hs
          change ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s).failed =
              true
          split <;> exact hn
        · exact hs
    · exact hs

/-- Each enabled level action retains an already raised failure flag. -/
private lemma fighterLevelAction_failed_of_failed (P : FighterParams) (d l : ℕ)
    (s : FighterState) (hs : s.failed = true) :
    ((fighterLevelAction P d l s).getD s).failed = true := by
  let Good (s : FighterState) : Prop := s.failed = true
  have hdummy (l : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterDummy d l s) := by
    unfold fighterDummy
    split
    · exact hs
    · rename_i phase hp
      split
      · exact hs
      · rename_i output hout
        split
        · exact hs
        · have ha := fighterAllocate_failed_of_failed d l (levelInput d l) .dummy output s hs
          cases he : fighterAllocate d l .dummy (levelInput d l) output s with
          | mk next success =>
            simp only [he] at ha ⊢
            cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
            · exact ha
            · exact ha
  have hflush (l : ℕ) (s : FighterState) (hs : Good s) :
      Good ((fighterFlushBuffer d l s).getD s) := by
    unfold fighterFlushBuffer
    cases hp : s.activeAt d l with
    | none => exact hs
    | some phase =>
      simp only [bind, Option.bind_some]
      split
      · exact hs
      · exact hs
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact hdummy l s hs
    · split
      · exact fighterPayoff_failed_of_failed P d l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact fighterStrategyMove_failed_of_failed P d l s hs
        | some next =>
          have h := hflush l s hs
          simpa only [hf, Option.getD_some] using h

/-- Once allocation sets the failure flag, every subsequent level action, finite closure,
and event service retains it. -/
lemma fighter_failed_persists
    (P : FighterParams) (d : ℕ) :
    (∀ l (s : FighterState), s.failed = true →
      ((fighterLevelAction P d l s).getD s).failed = true) ∧
    (∀ l fuel (s : FighterState), s.failed = true →
      (fighterClosure P d l fuel s).failed = true) ∧
    (∀ l event (s : FighterState), s.failed = true →
      (fighterProcessLevel P d l event s).failed = true) := by
  let Good (s : FighterState) : Prop :=
    s.failed = true
  have hcancel (j cause : ℕ) (reason : PhaseEnd) (s : FighterState) (hs : Good s) :
      Good (fighterCancel d j reason cause s) := by
    unfold fighterCancel
    split <;> exact hs
  have habort (l : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterAbortAbove d l s) := by
    exact (fighterAbortAbove_frame d l s).2.2.2.1.trans hs
  have hopponent (l : ℕ) (e : ProgramEvent) (s : FighterState) (hs : Good s) :
      Good (fighterOpponent P d l e s) := by
    unfold fighterOpponent
    split
    · exact hs
    · rename_i phase hp
      split
      · exact hs
      · split
        · exact hs
        · split
          · exact hcancel _ _ _ _ hs
          · exact fighterFulfillReady_failed_of_failed P d l _ hs
  have hstart (l : ℕ) (c : Candidate) (s : FighterState) (hs : Good s) :
      Good (fighterStartPhase P d l c s) := by
    unfold fighterStartPhase
    exact habort l _ (hcancel l l .replaced s hs)
  have hclosure (l fuel : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterClosure P d l fuel s) := by
    induction fuel generalizing s with
    | zero => exact hs
    | succ fuel ih =>
      simp only [fighterClosure]
      cases ha : fighterLevelAction P d l s with
      | none => exact hs
      | some next =>
        have hn := fighterLevelAction_failed_of_failed P d l s hs
        simp only [ha, Option.getD_some] at hn
        exact ih next hn
  have hprocess (l : ℕ) (e : Option TimedEvent) (s : FighterState) (hs : Good s) :
      Good (fighterProcessLevel P d l e s) := by
    unfold fighterProcessLevel fighterCloseLevel
    apply hclosure
    cases e with
    | none => exact fighterFulfillReady_failed_of_failed P d l s hs
    | some e =>
      dsimp only
      split
      · exact hstart l _ _ (fighterFulfillReady_failed_of_failed P d l s hs)
      · exact hopponent l _ _ (fighterFulfillReady_failed_of_failed P d l s hs)
  exact ⟨fighterLevelAction_failed_of_failed P d, hclosure, hprocess⟩

end Kolmogorov.Milovanov
