/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.HigherLevelServices

/-!
# The initial common game of the true marker phase

Fix a level `l` with a late admissible occurrence and a legal closure at the marker tick.  This
module shows that the true marker phase exists at the marker tick, that it is unique there, and
that the counter game it carries is won by the controlled player `false` from its initial
position (`exists_common_game_strategyWins`).  This is the first ingredient of the construction
of a common winning game along all ticks in `CommonGame.lean`.

The existence proof follows the fighter state machine through the marker tick: the marker event
installs the phase of level `l` (`exists_phase_fighterBeforeClosure`), the phase survives the
closure of level `l` (`exists_phase_fighterCloseLevel`, built from the single-action lemmas
`exists_activeAt_fighterDummy_of_closureAt`, `exists_activeAt_fighterPayoff_of_closureAt` and
`exists_activeAt_fighterLevelAction_of_closureAt`), and the services of strictly higher levels
never touch the level and candidate of the phase of level `l`
(`phaseKeyAt_fighterProcessLevel`, from `HigherLevelServices.lean`).  The dummy and payoff
lemmas are also used by `CommonGameInvariantBase.lean`.
-/

namespace Kolmogorov.Milovanov

/-- Two phases satisfying `TrueMarkerPhaseAt` at the marker tick of level `l` coincide. -/
private lemma trueMarkerPhaseAt_unique (P : FighterParams) (d l : ℕ) (phase₁ phase₂ : FighterPhase)
    (h₁ : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase₁)
    (h₂ : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase₂) :
    phase₁ = phase₂ := by
  rcases h₁ with ⟨_, _, _, h₁'⟩
  rcases h₂ with ⟨_, _, _, h₂'⟩
  rw [h₁'] at h₂'
  exact Option.some.inj h₂'

/-- The controlled player `false` wins the initial position of the game of any phase found at the
marker tick of level `l`: this is the invariant carried by every constructed phase. -/
private lemma winner_initialPosition_eq_false_of_trueMarkerPhaseAt (P : FighterParams)
    (d l : ℕ) (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase) :
    (phase.game d).winner (phase.game d).initialPosition = false := by
  let Q (l : ℕ) (c : Candidate) (code : CounterGameCode) (_ : List AllocatedDirective) :=
    (decodeCounterGame code).winner (decodeCounterGame code).initialPosition = false
  have hinit : ∀ l c s, Q l c (fighter_construction P d l c s).gameCode
      (fighter_construction P d l c s).initialAllocations := by
    intro l' c' s'
    dsimp only [Q, fighter_construction, FighterPhase.fundRequests]
    rw [decode_encode_counter_game]
    unfold FiniteCounterGame.controlWinningPlayer
    have h1 := symmetric_game_target_flip
      (finite_counter_game
          (retainedCoordinateList (constructedLiteralConstant P.literal d) (levelInput d l')
            (P.family.tree d l' (levelInput d l')))
          (coordinatePriceTable P.B P.lam P.n₀ (levelScale l') d c'
            (retainedCoordinateList (constructedLiteralConstant P.literal d) (levelInput d l')
              (P.family.tree d l' (levelInput d l'))))
          (List.map (fun xs => xs.toFinset.card)
            (List.map (fighterInitialIndices P d l' c' s'.allocated)
              (retainedCoordinateList (constructedLiteralConstant P.literal d) (levelInput d l')
                (P.family.tree d l' (levelInput d l')))))
          (List.filter (fun q => decide (q.1 ∈ fighterStageOutputs P d q.2 s'.tick s'.allocated))
            (P.family.tree d l' (levelInput d l')).queries)
          (P.c₁ * 2 ^ (levelUpper l' - levelScale l'))
          (QueryTree.normalize (constructedLiteralConstant P.literal d)
            (P.family.tree d l' (levelInput d l')))
          (fighterStageOutputs P d (levelInput d l') s'.tick s'.allocated).card)
    exact h1.1
  have h1 := active_phase_of_construction P d
    (fun l c allocations code => Q l c code allocations) (fun l c s _ => hinit l c s)
    (markerTick P.B (levelScale l))
  have h2 : phase ∈ (fighterState P d (markerTick P.B (levelScale l))).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  exact h1 phase h2

/-- The marker tick of a level with a late admissible occurrence is positive, since the last
program of scale `levelScale l` is non-empty. -/
private lemma markerTick_pos (P : FighterParams) (d l : ℕ)
    (hlate : LateAdmissibleOccurrence P d l) : 0 < markerTick P.B (levelScale l) := by
  refine Nat.pos_of_ne_zero fun hzero ↦ ?_
  have hevent : eventAt P.B (markerTick P.B (levelScale l)) = none := by
    rw [hzero]
    rfl
  have hlength := hlate.2
  simp only [lastProgram, hevent, Option.map_none, Option.getD_none, List.length_nil,
    Nat.not_lt_zero] at hlength

/-- At the marker tick of a level `l` with a late admissible occurrence, the master schedule emits
a program of length at most `levelScale l`, and this program is owned by the fighter of level
`l`. -/
private lemma exists_markerEvent_owner (P : FighterParams) (d l : ℕ)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∃ i p x, eventAt P.B (markerTick P.B (levelScale l)) =
        some (markerTick P.B (levelScale l), i, p, x) ∧
      p.length ≤ levelScale l ∧ fighterOwner d p.length = some l := by
  classical
  have hmarker := (markerTick_pos P d l hlate).ne'
  have hnonempty : ((boundedPrograms (levelScale l)).toFinset).Nonempty := by
    refine ⟨[], ?_⟩
    simp only [List.mem_toFinset, mem_boundedPrograms_iff, List.length_nil, Nat.zero_le]
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup
    (boundedPrograms (levelScale l)).toFinset hnonempty (programTick P.B)
  have hhalts : {t | ∃ i x, eventAt P.B t = some (t, i, p, x)}.Nonempty := by
    by_contra hempty
    have hzero : programTick P.B p = 0 := by
      rw [programTick, Set.not_nonempty_iff_eq_empty.mp hempty]
      exact Nat.sInf_empty
    exact hmarker (hmax.trans hzero)
  obtain ⟨i, x, hevent⟩ := Nat.sInf_mem hhalts
  change eventAt P.B (programTick P.B p) = some (programTick P.B p, i, p, x) at hevent
  rw [← hmax] at hevent
  change eventAt P.B (markerTick P.B (levelScale l)) =
    some (markerTick P.B (levelScale l), i, p, x) at hevent
  have hlast : lastProgram P.B (levelScale l) = p := by
    simp only [lastProgram, hevent, Option.map_some, Option.getD_some]
  have hlen : p.length ≤ levelScale l := by
    simpa only [List.mem_toFinset, mem_boundedPrograms_iff] using hp
  have howner : fighterOwner d p.length = some l := by
    apply ((fighter_owner_spec _ _).2 l).mpr
    have hscale : levelScale l ≤ levelUpper l :=
      tower_le_tower (by omega)
    exact ⟨hlate.1.1, by simpa only [hlast] using hlate.2, hlen.trans hscale⟩
  exact ⟨i, p, x, hevent, hlen, howner⟩

/-- The marker event installs the phase of level `l` for the marker candidate before the closure
of level `l` at the marker tick. -/
lemma exists_phase_fighterBeforeClosure (P : FighterParams) (d l : ℕ)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∃ phase, (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l).activeAt d l =
        some phase ∧
      phase.level = l ∧ phase.candidate = markerCandidate P.B (levelScale l) := by
  obtain ⟨i, p, x, hevent, hlen, howner⟩ := exists_markerEvent_owner P d l hlate
  have hlast : lastProgram P.B (levelScale l) = p := by
    simp only [lastProgram, hevent, Option.map_some, Option.getD_some]
  rw [← hlast] at hlen hevent howner
  unfold fighterBeforeClosure
  simp only [hevent, howner, hlen, hlate.1]
  dsimp only [fighterStartPhase]
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l
    (fighterFulfillReady P d l (fighterBeforeLevel P d (markerTick P.B (levelScale l)) l)))
  let phase := fighter_construction P d l
    (lastProgram P.B (levelScale l), markerTick P.B (levelScale l)) waiting
  use phase
  have H : (waiting.putPhase d phase).activeAt d l = some phase := by
    dsimp [FighterState.putPhase, FighterState.activeAt]
    have hl : phase.level = l := rfl
    simp [hl]
  refine ⟨H, rfl, rfl⟩

/-- Completing the service of level `l` from any intermediate state of the closure at a tick after
the marker tick does not set the failure flag. -/
private lemma fighterCloseLevel_failed_eq_false_of_closureAt (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick) (step : ℕ) (phase : FighterPhase)
    (hphase : (fighterClosureAt P d tick l step).activeAt d l = some phase) :
    (fighterCloseLevel P d l (fighterClosureAt P d tick l step)).failed = false :=
  fighterCloseLevel_closureAt_failed_eq_false
    P d l tick step (Nat.ne_of_gt hgood.positive)
    ((markerTick_pos P d l hlate).trans_le htick)
    (hfixed.capacity d hgood.capacity_threshold hgood.even tick) phase hphase

/-- A dummy allocation in an intermediate closure state at a tick after the marker tick preserves
the candidate and the level of the phase of level `l`. -/
lemma exists_activeAt_fighterDummy_of_closureAt (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick) (step : ℕ)
    (state : FighterState) (hstate : state = fighterClosureAt P d tick l step)
    (phase : FighterPhase) (hphase : state.activeAt d l = some phase) :
    ∃ p', (fighterDummy d l state).activeAt d l = some p' ∧ p'.candidate = phase.candidate ∧
      p'.level = phase.level := by
  cases hdummy : phase.dummy with
  | none =>
      exact ⟨phase, by simp [fighterDummy, hphase, hdummy], rfl, rfl⟩
  | some output =>
      cases hissued : phase.dummyIssued with
      | true =>
          exact ⟨phase, by simp [fighterDummy, hphase, hdummy, hissued], rfl, rfl⟩
      | false =>
          have hservice : (fighterCloseLevel P d l state).failed = false := by
            subst state
            exact fighterCloseLevel_failed_eq_false_of_closureAt
              P C cGap cRank d₀ d l hfixed hgood hlate tick htick step phase hphase
          have haction : fighterLevelAction P d l state = some (fighterDummy d l state) := by
            simp [fighterLevelAction, hphase, hdummy, hissued]
          have hpos : 0 < fighterClosureFuel d l state := by
            simp [fighterClosureFuel, hphase]
          obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
          have heq : fighterCloseLevel P d l state =
              fighterClosure P d l fuel (fighterDummy d l state) := by
            simp only [fighterCloseLevel, hfuel, fighterClosure, haction]
          have hfailed : (fighterDummy d l state).failed = false := by
            by_contra h
            have hf :=
              fighter_failed_persists P d
                |>.2.1 l fuel (fighterDummy d l state) (Bool.eq_true_of_ne_false h)
            rw [← heq, hservice] at hf
            contradiction
          have halloc :=
            fighterAllocate_spec
              d l (levelInput d l) .dummy output state phase hphase
          cases he : fighterAllocate d l .dummy (levelInput d l) output state with
          | mk next success =>
              rw [he] at halloc
              cases success with
              | false =>
                  have hf : next.failed = true := (halloc.1 rfl).1
                  have hn : next.failed = false := by
                    simpa only [fighterDummy, hphase, hdummy, hissued,
                      Bool.false_eq_true, ite_false, he] using hfailed
                  rw [hn] at hf
                  contradiction
              | true =>
                  have hlevel : phase.level = l :=
                    FighterState.level_eq_of_activeAt_eq_some hphase
                  refine ⟨{ phase with dummyIssued := true }, ?_, rfl, rfl⟩
                  simp only [fighterDummy, hphase, hdummy, hissued,
                    Bool.false_eq_true, ite_false, he, ite_true]
                  simp [FighterState.putPhase, FighterState.activeAt, hlevel]

/-- A dummy allocation either sets the failure flag or preserves a pending safe request whose
allocation pool is already saturated.  This holds for arbitrary local states. -/
private lemma fighterDummy_preserves_blocked_request (P : FighterParams) (d l : ℕ)
    (s : FighterState) (phase : FighterPhase) (hphase : s.activeAt d l = some phase)
    (q : Coordinate)
    (hrequest : q ∈ phase.pending ∧ q ∉ s.fulfilled ∧ fighterSafe P d s.tick q = true)
    (hblocked : (fighterAllocate d l .payoff q.2 q.1 s).2 = false) :
    let t := fighterDummy d l s
    t.failed = true ∨ ∃ p, t.activeAt d l = some p ∧
      q ∈ p.pending ∧ q ∉ t.fulfilled ∧ fighterSafe P d t.tick q = true ∧
      (fighterAllocate d l .payoff q.2 q.1 t).2 = false := by
  have hstart : s.failed = true ∨ ∃ p, s.activeAt d l = some p ∧
      q ∈ p.pending ∧ q ∉ s.fulfilled ∧ fighterSafe P d s.tick q = true ∧
      (fighterAllocate d l .payoff q.2 q.1 s).2 = false :=
    Or.inr ⟨phase, hphase, hrequest.1, hrequest.2.1, hrequest.2.2, hblocked⟩
  simp only [fighterDummy, hphase]
  cases hdummy : phase.dummy with
  | none => exact hstart
  | some out =>
    cases hi : phase.dummyIssued <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · have ha := fighterAllocate_spec
        d l (levelInput d l) .dummy out s phase hphase
      cases he : fighterAllocate d l .dummy (levelInput d l) out s with
      | mk u success =>
        rw [he] at ha
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact Or.inl (ha.1 rfl).1
        · obtain ⟨input, hlen, hfresh, halloc, hutick, huf, hufailed, hup⟩ := ha.2 rfl
          let t := u.putPhase d { phase with dummy := some out, dummyIssued := true }
          have hlevel : phase.level = l := FighterState.level_eq_of_activeAt_eq_some hphase
          have htp : t.activeAt d l =
              some { phase with dummy := some out, dummyIssued := true } := by
            simp [t, FighterState.putPhase, FighterState.activeAt, hlevel]
          right
          refine ⟨{ phase with dummy := some out, dummyIssued := true }, htp, hrequest.1, ?_, ?_,
            ?_⟩
          · change q ∉ u.fulfilled
            rw [huf]
            exact hrequest.2.1
          · change fighterSafe P d u.tick q = true
            rw [hutick]
            exact hrequest.2.2
          · have hoc := card_occupiedInputs_append
              s t ⟨l, phase.candidate, s.tick, .dummy, levelInput d l, input, out⟩ halloc hfresh q.2
            apply Bool.eq_false_of_ne_true
            intro hsuc
            have hs := fighterAllocate_success_of_card_le
              d l q.2 .payoff .payoff q.1 q.1 s t phase
              { phase with dummy := some out, dummyIssued := true }
              hphase htp (by omega) hsuc
            rw [hblocked] at hs
            contradiction
    · exact hstart

/-- A payoff of an arbitrary coordinate either sets the failure flag or preserves a pending safe
saturated request.  Successful payment of another coordinate only enlarges the occupied input
sets. -/
private lemma fighterPayoff_preserves_blocked_request (P : FighterParams) (d l : ℕ)
    (s : FighterState) (phase : FighterPhase) (hphase : s.activeAt d l = some phase)
    (q : Coordinate)
    (hrequest : q ∈ phase.pending ∧ q ∉ s.fulfilled ∧ fighterSafe P d s.tick q = true)
    (hblocked : (fighterAllocate d l .payoff q.2 q.1 s).2 = false) (r : Coordinate) :
    let t := fighterPayoff P d l r s
    t.failed = true ∨ ∃ p, t.activeAt d l = some p ∧
      q ∈ p.pending ∧ q ∉ t.fulfilled ∧ fighterSafe P d t.tick q = true ∧
      (fighterAllocate d l .payoff q.2 q.1 t).2 = false := by
  simp only [fighterPayoff, hphase]
  by_cases hr : r ∈ phase.pending ∧ r ∉ s.fulfilled ∧ fighterSafe P d s.tick r = true
  · rw [ite_eq_left hr]
    have ha := fighterAllocate_spec
      d l r.2 .payoff r.1 s phase hphase
    cases he : fighterAllocate d l .payoff r.2 r.1 s with
    | mk u success =>
      rw [he] at ha
      cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact Or.inl (ha.1 rfl).1
      · obtain ⟨input, hlen, hfresh, halloc, hutick, huf, hufailed, hup⟩ := ha.2 rfl
        have hne : q ≠ r := by
          intro heq
          subst r
          have hs : (fighterAllocate d l .payoff q.2 q.1 s).2 = true := by rw [he]
          rw [hblocked] at hs
          contradiction
        let t : FighterState := { u with
          fulfilled := u.fulfilled ++ [r]
          active := u.active.map (fun p => { p with pending := p.pending.filter (· != r) }) }
        have htp : t.activeAt d l =
            some { phase with pending := phase.pending.filter (· != r) } := by
          simp only [t, FighterState.activeAt, List.find?_map]
          change (u.activeAt d l).map _ = _
          rw [hup]
          rfl
        right
        refine ⟨{ phase with pending := phase.pending.filter (· != r) }, htp, ?_, ?_, ?_, ?_⟩
        · simp [hrequest.1, hne]
        · rw [huf]
          simpa [hne] using hrequest.2.1
        · rw [hutick]
          exact hrequest.2.2
        · have hoc := card_occupiedInputs_append
            s t ⟨l, phase.candidate, s.tick, .payoff, r.2, input, r.1⟩ halloc hfresh q.2
          apply Bool.eq_false_of_ne_true
          intro hsuc
          have hs := fighterAllocate_success_of_card_le
            d l q.2 .payoff .payoff q.1 q.1 s t phase
            { phase with pending := phase.pending.filter (· != r) }
            hphase htp (by omega) hsuc
          rw [hblocked] at hs
          contradiction
  · rw [ite_eq_right hr]
    exact Or.inr ⟨phase, hphase, hrequest.1, hrequest.2.1, hrequest.2.2, hblocked⟩

/-- A pending safe request in an arbitrary local state has a successful payoff allocation whenever
completed local service is failure-free.  Saturation persists through earlier actions, and the
closure fixpoint cannot leave this request enabled. -/
private lemma fighterAllocate_payoff_success_of_closeLevel_not_failed (P : FighterParams)
    (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase) (q : Coordinate)
    (hrequest : q ∈ phase.pending ∧ q ∉ state.fulfilled ∧ fighterSafe P d state.tick q = true)
    (hservice : (fighterCloseLevel P d l state).failed = false) :
    (fighterAllocate d l .payoff q.2 q.1 state).2 = true := by
  by_contra hsuccess
  have hblocked := Bool.eq_false_of_ne_true hsuccess
  let Bad (s : FighterState) : Prop := s.failed = true ∨ ∃ p,
    s.activeAt d l = some p ∧ q ∈ p.pending ∧ q ∉ s.fulfilled ∧
      fighterSafe P d s.tick q = true ∧
      (fighterAllocate d l .payoff q.2 q.1 s).2 = false
  obtain ⟨haction, _, _⟩ :=
    fighter_failed_persists P d
  have hbad_action (s next : FighterState) (hs : Bad s)
      (hn : fighterLevelAction P d l s = some next) : Bad next := by
    rcases hs with hf | ⟨p, hp, hq, hqf, hsafe, halloc⟩
    · left
      have h := haction l s hf
      simpa only [hn, Option.getD_some] using h
    · simp only [fighterLevelAction, hp, bind, Option.bind_some] at hn
      by_cases hdummy : (p.dummy.isSome && !p.dummyIssued) = true
      · rw [ite_eq_left hdummy] at hn
        have heq := Option.some.inj hn
        subst next
        exact fighterDummy_preserves_blocked_request P d l s p hp q ⟨hq, hqf, hsafe⟩ halloc
      · rw [ite_eq_right hdummy] at hn
        cases hpay : p.pending.find? (fun r => decide (r ∉ s.fulfilled) && fighterSafe P d s.tick r)
          with
        | some r =>
          simp only [hpay, Option.some.injEq] at hn
          subst next
          exact fighterPayoff_preserves_blocked_request P d l s p hp q ⟨hq, hqf, hsafe⟩ halloc r
        | none =>
          have hnot := List.find?_eq_none.mp hpay q hq
          exact False.elim (hnot (by simp [hqf, hsafe]))
  have hbad_closure (fuel : ℕ) (s : FighterState) (hs : Bad s) :
      Bad (fighterClosure P d l fuel s) := by
    induction fuel generalizing s with
    | zero => exact hs
    | succ fuel ih =>
      simp only [fighterClosure]
      cases hn : fighterLevelAction P d l s with
      | none => exact hs
      | some next => exact ih next (hbad_action s next hs hn)
  have hfinish := hbad_closure (fighterClosureFuel d l state) state
    (Or.inr ⟨phase, hphase, hrequest.1, hrequest.2.1, hrequest.2.2, hblocked⟩)
  change Bad (fighterCloseLevel P d l state) at hfinish
  rcases hfinish with hf | ⟨p, hp, hq, hqf, hsafe, _⟩
  · rw [hservice] at hf
    contradiction
  · have hfix := fighter_closure_fixpoint P d l state
    simp only [fighterLevelAction, hp, bind, Option.bind_some] at hfix
    split at hfix
    · contradiction
    · cases hpay : p.pending.find? (fun r =>
          decide (r ∉ (fighterCloseLevel P d l state).fulfilled) &&
            fighterSafe P d (fighterCloseLevel P d l state).tick r) with
      | some r => simp only [hpay] at hfix; contradiction
      | none =>
        have hnot := List.find?_eq_none.mp hpay q hq
        exact hnot (by simp [hqf, hsafe])

/-- A payoff in a state whose completed local service is failure-free preserves the candidate and
the level of the phase of level `l`.  A successful payoff allocation preserves the issuing phase
and only removes the fulfilled request from its pending list. -/
private lemma exists_activeAt_fighterPayoff_of_closeLevel_not_failed (P : FighterParams)
    (d l : ℕ) (state : FighterState) (phase : FighterPhase)
    (hphase : state.activeAt d l = some phase)
    (hservice : (fighterCloseLevel P d l state).failed = false) (q : Coordinate) :
    ∃ p', (fighterPayoff P d l q state).activeAt d l = some p' ∧
      p'.candidate = phase.candidate ∧ p'.level = phase.level := by
  by_cases hrequest :
      q ∈ phase.pending ∧ q ∉ state.fulfilled ∧ fighterSafe P d state.tick q = true
  · have hsuccess := fighterAllocate_payoff_success_of_closeLevel_not_failed
      P d l state phase hphase q hrequest hservice
    cases he : fighterAllocate d l .payoff q.2 q.1 state with
    | mk next success =>
      rw [he] at hsuccess
      cases success with
      | false => cases hsuccess
      | true =>
        have hpnext := (fighterAllocate_spec
          d l q.2 .payoff q.1 state phase hphase).2 (by rw [he])
        rw [he] at hpnext
        obtain ⟨_, _, _, _, _, _, _, hpnext⟩ := hpnext
        refine ⟨{ phase with pending := phase.pending.filter (· != q) }, ?_, rfl, rfl⟩
        simp only [fighterPayoff, hphase]
        rw [ite_eq_left hrequest, he]
        simp only [ite_true]
        simp only [FighterState.activeAt, List.find?_map]
        change (next.activeAt d l).map _ = _
        rw [hpnext]
        rfl
  · exact ⟨phase, by simp [fighterPayoff, hphase, hrequest], rfl, rfl⟩

/-- A payoff in an intermediate closure state at a tick after the marker tick preserves the
candidate and the level of the phase of level `l`. -/
lemma exists_activeAt_fighterPayoff_of_closureAt (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick) (step : ℕ)
    (state : FighterState) (hstate : state = fighterClosureAt P d tick l step)
    (phase : FighterPhase) (hphase : state.activeAt d l = some phase) (q : Coordinate) :
    ∃ p', (fighterPayoff P d l q state).activeAt d l = some p' ∧ p'.candidate = phase.candidate ∧
      p'.level = phase.level := by
  have hservice : (fighterCloseLevel P d l state).failed = false := by
    subst state
    exact fighterCloseLevel_failed_eq_false_of_closureAt
      P C cGap cRank d₀ d l hfixed hgood hlate tick htick step phase hphase
  exact exists_activeAt_fighterPayoff_of_closeLevel_not_failed P d l state phase hphase hservice q

/-- One action of the closure of level `l` at the marker tick preserves the candidate and the level
of the phase of level `l`, provided the closure at the marker tick is legal. -/
private lemma exists_activeAt_fighterLevelAction_of_closureAt (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l) (step : ℕ)
    (hstep : step < fighterClosureFuel d l
      (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l))
    (phase : FighterPhase)
    (hphase : (fighterClosureAt P d (markerTick P.B (levelScale l)) l step).activeAt d l =
      some phase)
    (hcandidate : phase.candidate = markerCandidate P.B (levelScale l))
    (next : FighterState)
    (hnext : fighterLevelAction P d l
      (fighterClosureAt P d (markerTick P.B (levelScale l)) l step) = some next) :
    ∃ p', next.activeAt d l = some p' ∧ p'.candidate = phase.candidate ∧
      p'.level = phase.level := by
  set state := fighterClosureAt P d (markerTick P.B (levelScale l)) l step with hstate
  have hfinish (p : FighterPhase)
      (hp : next.activeAt d l = some p) :
      ∃ p', next.activeAt d l = some p' ∧
        p'.candidate = phase.candidate ∧ p'.level = phase.level := by
    obtain ⟨old, hold, hc⟩ :=
      candidate_eq_of_activeAt_fighterLevelAction
        P d l state next hnext p hp
    have he : old = phase := Option.some.inj (hold.symm.trans hphase)
    subst old
    exact ⟨p, hp, hc.symm,
      (FighterState.level_eq_of_activeAt_eq_some hp).trans
        (FighterState.level_eq_of_activeAt_eq_some hphase).symm⟩
  unfold fighterLevelAction at hnext
  rw [hphase] at hnext
  change (do
    if phase.dummy.isSome && !phase.dummyIssued then some (fighterDummy d l state) else
      match phase.pending.find? (fun q =>
          decide (q ∉ state.fulfilled) && fighterSafe P d state.tick q) with
      | some q => some (fighterPayoff P d l q state)
      | none =>
        match fighterFlushBuffer d l state with
        | some next => some next
        | none => fighterStrategyMove P d l state) = some next at hnext
  split at hnext
  · injection hnext with hnext_eq
    rw [← hnext_eq]
    exact exists_activeAt_fighterDummy_of_closureAt P C cGap cRank d₀ d l hfixed hgood hlate
      _ le_rfl step state hstate phase hphase
  · split at hnext
    · rename_i q hq
      injection hnext with hnext_eq
      rw [← hnext_eq]
      exact exists_activeAt_fighterPayoff_of_closureAt P C cGap cRank d₀ d l hfixed hgood hlate
        _ le_rfl step state hstate phase hphase q
    · have hlegal := hclosure _ le_rfl step hstep.le phase hphase hcandidate
      cases hf : fighterFlushBuffer d l state with
      | some flushed =>
          simp only [hf] at hnext
          have he : flushed = next := Option.some.inj hnext
          subst next
          obtain ⟨_, _, afterPhase, hafter, _, _⟩ :=
            hlegal.2.1 flushed hf
          exact hfinish afterPhase hafter
      | none =>
          simp only [hf] at hnext
          obtain ⟨move, _, _, _, afterPhase, hafter, _⟩ :=
            hlegal.2.2 next hnext
          exact hfinish afterPhase hafter

/-- The one-step unfolding of `fighterClosure` at the end of the iteration. -/
private lemma fighterClosure_succ_eq (P : FighterParams) (d l k : ℕ) (s : FighterState) :
    fighterClosure P d l (k + 1) s =
      match fighterLevelAction P d l (fighterClosure P d l k s) with
      | none => fighterClosure P d l k s
      | some next => next := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases ha : fighterLevelAction P d l s with
    | none => simp only [fighterClosure, ha]
    | some next => simpa only [fighterClosure, ha] using ih next

/-- The phase of level `l` installed by the marker event survives the whole closure of level `l`
at the marker tick, with the same level and candidate. -/
private lemma exists_phase_fighterCloseLevel (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d)
    (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (hbefore : ∃ phase,
      (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l).activeAt d l = some phase ∧
        phase.level = l ∧ phase.candidate = markerCandidate P.B (levelScale l)) :
    ∃ p,
      (fighterCloseLevel P d l
        (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l)).activeAt d l = some p ∧
      p.level = l ∧ p.candidate = markerCandidate P.B (levelScale l) := by
  unfold fighterCloseLevel
  set fuel := fighterClosureFuel d l (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l)
  have h_ind : ∀ k ≤ fuel, ∃ phase,
      (fighterClosureAt P d (markerTick P.B (levelScale l)) l k).activeAt d l = some phase ∧
      phase.candidate = markerCandidate P.B (levelScale l) ∧ phase.level = l := by
    intro k hk
    induction k with
    | zero =>
      obtain ⟨phase, hphase, hlevel, hcand⟩ := hbefore
      exact ⟨phase, hphase, hcand, hlevel⟩
    | succ k ih =>
      obtain ⟨phase, hphase, hcand, hlevel⟩ := ih (Nat.le_of_succ_le hk)
      have hsucc := fighterClosure_succ_eq P d l k
        (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l)
      cases h_act : fighterLevelAction P d l
          (fighterClosureAt P d (markerTick P.B (levelScale l)) l k) with
      | none =>
          refine ⟨phase, ?_, hcand, hlevel⟩
          change (fighterClosure P d l (k + 1) _).activeAt d l = _
          rw [hsucc]
          change (match fighterLevelAction P d l
            (fighterClosureAt P d (markerTick P.B (levelScale l)) l k) with
            | none => fighterClosureAt P d (markerTick P.B (levelScale l)) l k
            | some next => next).activeAt d l = _
          rw [h_act]
          exact hphase
      | some next =>
          obtain ⟨p', hp', hc', hl'⟩ := exists_activeAt_fighterLevelAction_of_closureAt
            P C cGap cRank d₀ d l hfixed hgood hlate hclosure k (Nat.lt_of_succ_le hk) phase
            hphase hcand next h_act
          refine ⟨p', ?_, hc'.trans hcand, hl'.trans hlevel⟩
          change (fighterClosure P d l (k + 1) _).activeAt d l = _
          rw [hsucc]
          change (match fighterLevelAction P d l
            (fighterClosureAt P d (markerTick P.B (levelScale l)) l k) with
            | none => fighterClosureAt P d (markerTick P.B (levelScale l)) l k
            | some next => next).activeAt d l = _
          rw [h_act]
          exact hp'
  obtain ⟨p, hp1, hp2, hp3⟩ := h_ind fuel le_rfl
  exact ⟨p, hp1, hp3, hp2⟩

/-- A strictly increasing list containing `l` factors as its lower prefix, `l`, and a strictly
higher tail. -/
private lemma exists_takeWhile_append_cons_of_pairwise_lt (l : ℕ) (levels : List ℕ)
    (hsorted : levels.Pairwise (· < ·)) (hmem : l ∈ levels) :
    ∃ tail : List ℕ, levels = levels.takeWhile (· < l) ++ l :: tail ∧ ∀ j ∈ tail, l < j := by
  induction levels with
  | nil => simp at hmem
  | cons a xs ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hsorted
    rcases List.mem_cons.mp hmem with rfl | hm
    · exact ⟨xs, by simp, ha⟩
    · have hal : a < l := ha l hm
      obtain ⟨tail, ht, htail⟩ := ih hs hm
      refine ⟨tail, ?_, htail⟩
      simpa [List.takeWhile_cons, hal] using congrArg (List.cons a) ht

/-- The state at the marker tick is obtained from the closure of level `l` by running the services
of some strictly higher levels. -/
private lemma exists_fighterState_markerTick_eq_foldl (P : FighterParams) (d l : ℕ) (hd : 0 < d)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∃ tail : List ℕ, (∀ j ∈ tail, l < j) ∧
      fighterState P d (markerTick P.B (levelScale l)) =
        tail.foldl
          (fun s j ↦ fighterProcessLevel P d j
            (eventAt P.B (markerTick P.B (levelScale l))) s)
          (fighterCloseLevel P d l
            (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l)) := by
  classical
  have hpositive := markerTick_pos P d l hlate
  obtain ⟨i, p, x, hevent, -, howner⟩ := exists_markerEvent_owner P d l hlate
  let τ := markerTick P.B (levelScale l)
  let current : FighterState :=
    { fighterState P d (τ - 1) with tick := τ, schedule := masterState P.B τ }
  let event := eventAt P.B τ
  let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
  let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
  let traversal := levels.mergeSort (· ≤ ·)
  have hsorted : traversal.Pairwise (· < ·) := by
    have hle := List.pairwise_mergeSort' (· ≤ ·) levels
    have hne : traversal.Nodup := by
      rw [List.nodup_mergeSort]
      exact Kolmogorov.nodup_eraseDups_list _
    exact (hle.and hne).imp (fun h ↦ lt_of_le_of_ne h.1 h.2)
  have hmem : l ∈ traversal := by
    simp [traversal, levels, owner, event, τ, hevent, howner]
  obtain ⟨tail, hsplit, htail⟩ :=
    exists_takeWhile_append_cons_of_pairwise_lt l traversal hsorted hmem
  let F := fun s j ↦ fighterProcessLevel P d j event s
  have hbefore : fighterBeforeLevel P d τ l =
      (traversal.takeWhile (· < l)).foldl F current := rfl
  have hclose : F (fighterBeforeLevel P d τ l) l =
      fighterCloseLevel P d l (fighterBeforeClosure P d τ l) := rfl
  have hτ : τ - 1 + 1 = τ := Nat.sub_add_cancel hpositive
  have hstate : fighterState P d τ =
      fighter_actions P d τ (fighterState P d (τ - 1)) := by
    simpa only [hτ] using
      (show fighterState P d (τ - 1 + 1) =
        fighter_actions P d (τ - 1 + 1) (fighterState P d (τ - 1)) from rfl)
  refine ⟨tail, htail, ?_⟩
  change fighterState P d τ = _
  rw [hstate, fighter_actions, ite_eq_right (Nat.ne_of_gt hd)]
  change traversal.foldl F current = _
  rw [hsplit, List.foldl_append, List.foldl_cons, ← hbefore, hclose]

/-- Once the phase installed by the marker event has survived the closure of level `l`, it also
survives the services of the higher levels at the same tick, so the true marker phase exists at
the marker tick. -/
lemma exists_trueMarkerPhaseAt_of_phase_fighterCloseLevel (P : FighterParams)
    (C cGap cRank d₀ d l : ℕ) (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (hbefore : ∃ phase,
      (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l).activeAt d l = some phase ∧
        phase.level = l ∧ phase.candidate = markerCandidate P.B (levelScale l)) :
    ∃ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase := by
  obtain ⟨p, hp1, hp2, hp3⟩ :=
    exists_phase_fighterCloseLevel P C cGap cRank d₀ d l hfixed hgood hlate hclosure hbefore
  obtain ⟨tail, htail1, htail2⟩ :=
    exists_fighterState_markerTick_eq_foldl P d l hgood.positive hlate
  obtain ⟨next, hnext1, hnext2, hnext3⟩ := exists_activeAt_foldl_fighterProcessLevel P d l
    (eventAt P.B (markerTick P.B (levelScale l)))
    (fighterCloseLevel P d l (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l)) tail
    htail1 p hp1
  refine ⟨next, le_refl _, ?_, ?_, ?_⟩
  · rw [hnext2]
    exact hp2
  · rw [hnext3]
    exact hp3
  · rw [htail2]
    exact hnext1

/-- The true marker phase of level `l` exists at the marker tick. -/
lemma exists_trueMarkerPhaseAt (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l) :
    ∃ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase :=
  exists_trueMarkerPhaseAt_of_phase_fighterCloseLevel P C cGap cRank d₀ d l hfixed hgood hlate
    hclosure (exists_phase_fighterBeforeClosure P d l hlate)

/-- The initial game of the true marker phase at the marker tick is a finite counter game won by
`false`, and every true marker phase at that tick carries this same game. -/
lemma exists_common_game_strategyWins (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l) :
    ∃ game : FiniteCounterGame, game.StrategyWins false game.strategy game.initialPosition ∧
      ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
        phase.game d = game := by
  obtain ⟨phase, hphase⟩ := exists_trueMarkerPhaseAt P C cGap cRank d₀ d l hfixed hgood hlate
    hclosure
  refine ⟨phase.game d, ?_, fun p hp ↦ ?_⟩
  · have hwins :=
      finite_counter_game_computable_winner.2 (phase.game d) (phase.game d).initialPosition
    rw [winner_initialPosition_eq_false_of_trueMarkerPhaseAt P d l phase hphase] at hwins
    exact hwins
  · rw [trueMarkerPhaseAt_unique P d l p phase hp hphase]

end Kolmogorov.Milovanov
