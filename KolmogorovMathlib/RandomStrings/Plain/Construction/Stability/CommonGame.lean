/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantTick
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameHigherLevels

/-!
# A common winning game along the true-marker play

For blueprint node `constr:opponent`, this module combines phase survival and game invariance
with reachability of official counter-game positions. Internal closure gives legal moves that
follow the controlled strategy; preprocessing and higher-level services leave the official
position unchanged. Starting from the winning initial game, these facts yield a single legal
play across all ticks, with the buffer invariant at every true-marker phase. The construction's
stability argument uses this play to bound opponent activity.
-/

namespace Kolmogorov.Milovanov

/-- Higher-level services preserve the game and buffer invariant of a true-marker phase. -/
private lemma true_marker_after_higher_levels
    (P : FighterParams) (d l : ℕ) (hd : 0 < d)
    (game : FiniteCounterGame)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (closePhase : FighterPhase)
    (hclose : (fighterCloseLevel P d l
      (fighterBeforeClosure P d (tick + 1) l)).activeAt d l = some closePhase)
    (hcand : closePhase.candidate = markerCandidate P.B (levelScale l))
    (hgame : closePhase.game d = game)
    (hbuf : closePhase.BufferInvariant d) :
    ∃ next, TrueMarkerPhaseAt P d l (tick + 1) next ∧
      next.game d = game ∧ next.BufferInvariant d := by
  obtain ⟨levels, hlevels, hstate⟩ :=
    exists_fighterState_eq_foldl_fighterProcessLevel
      P d l tick hd closePhase hclose
  obtain ⟨nextPhase, hnext, pending, hpending⟩ :=
    activeAt_foldl_fighterProcessLevel
      P d l (eventAt P.B (tick + 1)) levels
      (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l))
      hlevels closePhase hclose
  have hlevel : closePhase.level = l := by
    have h1 := List.find?_some hclose
    exact beq_iff_eq.mp h1
  refine ⟨nextPhase, ?_, ?_, ?_⟩
  · unfold TrueMarkerPhaseAt
    have htick_succ : markerTick P.B (levelScale l) ≤ tick + 1 := Nat.le_succ_of_le htick
    exact ⟨htick_succ, by rw [hpending, hlevel], by rw [hpending, hcand], by rw [hstate, hnext]⟩
  · rw [hpending]
    exact hgame
  · rw [hpending]
    exact hbuf

/-- A true-marker phase survives the next tick with its game and buffer invariant. -/
private lemma exists_trueMarkerPhaseAt_succ
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase)
    (hphase_game : phase.game d = game) :
    ∃ next, TrueMarkerPhaseAt P d l (tick + 1) next ∧
      next.game d = game ∧ next.BufferInvariant d := by
  obtain ⟨beforePhase, hbefore, hcand, hgame, _⟩ :=
    true_marker_before_closure_invariant
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure
      game tick htick phase hphase hphase_game
  obtain ⟨closePhase, hclose, hcloseCand, hcloseGame, hcloseBuf⟩ :=
    true_marker_close_level_invariant
      P C cGap cRank d₀ d l hfixed hgood hclosure
      game tick htick beforePhase hbefore hcand hgame
  exact
    true_marker_after_higher_levels
      P d l hgood.positive
      game tick htick closePhase hclose hcloseCand hcloseGame hcloseBuf

/-- At every tick from the marker onward, a true-marker phase carries the common game
and satisfies the buffer invariant. -/
private lemma exists_trueMarkerPhaseAt_with_invariants
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game) :
    ∀ tick ≥ markerTick P.B (levelScale l), ∃ phase,
      TrueMarkerPhaseAt P d l tick phase ∧ phase.game d = game ∧ phase.BufferInvariant d := by
  intro tick htick
  induction tick, htick using Nat.le_induction with
  | base =>
    exact exists_trueMarkerPhaseAt_markerTick_with_invariants
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame
  | succ t ht ih =>
    obtain ⟨phase, hphase, hgame_eq, _⟩ := ih
    exact exists_trueMarkerPhaseAt_succ
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game t ht phase hphase hgame_eq

/-- The marker event installs a phase whose official position is the initial game position. -/
private lemma exists_marker_phase_initialPosition
    (P : FighterParams) (d l : ℕ)
    (hlate : LateAdmissibleOccurrence P d l) :
    ∃ phase,
      (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l).activeAt d l = some phase ∧
      phase.level = l ∧
      phase.candidate = markerCandidate P.B (levelScale l) ∧
      decodeCounterPosition (phase.game d) phase.officialCode = (phase.game d).initialPosition := by
  have hnonempty : ((boundedPrograms (levelScale l)).toFinset).Nonempty := by
    refine ⟨[], ?_⟩
    simp only [List.mem_toFinset, mem_boundedPrograms_iff, List.length_nil, Nat.zero_le]
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup
    (boundedPrograms (levelScale l)).toFinset hnonempty (programTick P.B)
  have hmarker : markerTick P.B (levelScale l) ≠ 0 := by
    intro hzero
    have hevent : eventAt P.B (markerTick P.B (levelScale l)) = none := by
      rw [hzero]
      rfl
    have hlength := hlate.2
    simp only [lastProgram, hevent, Option.map_none, Option.getD_none,
      List.length_nil, Nat.not_lt_zero] at hlength
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
  rw [← hlast] at hlen hevent
  have howner : fighterOwner d (lastProgram P.B (levelScale l)).length = some l := by
    apply ((fighter_owner_spec _ _).2 l).mpr
    have hscale : levelScale l ≤ levelUpper l :=
      tower_le_tower (by omega)
    exact ⟨hlate.1.1, hlate.2, hlen.trans hscale⟩
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
  refine ⟨H, rfl, rfl, ?_⟩
  let coords := retainedCoordinateList
    (constructedLiteralConstant P.literal d) (levelInput d l)
    (P.family.tree d l (levelInput d l))
  let candidate : Candidate :=
    (lastProgram P.B (levelScale l), markerTick P.B (levelScale l))
  let indices := coords.map
    (fighterInitialIndices P d l candidate waiting.allocated)
  let counters := indices.map (fun xs ↦ xs.toFinset.card)
  let R := P.c₁ * 2 ^ (levelUpper l - levelScale l)
  let original := finite_counter_game coords
    (coordinatePriceTable P.B P.lam P.n₀ (levelScale l) d candidate coords) counters
    ((P.family.tree d l (levelInput d l)).queries.filter
      (fun q ↦ decide (q.1 ∈ fighterStageOutputs P d q.2 waiting.tick waiting.allocated))) R
    ((P.family.tree d l (levelInput d l)).normalize (constructedLiteralConstant P.literal d))
    (fighterStageOutputs P d (levelInput d l) waiting.tick waiting.allocated).card
  let game := original.controlWinningPlayer
  have hgame : phase.game d = game :=
    decode_encode_counter_game game
  change decodeCounterPosition (phase.game d)
    game.initialPosition.encode = (phase.game d).initialPosition
  rw [hgame, decode_encode_counter_position]

/-- Each internal action advances the official position along a legal strategy-following path. -/
private lemma strategySteps_of_fighterLevelAction
    (P : FighterParams) (d l tick step : ℕ)
    (hclosure : TrueMarkerClosureLegal P d l)
    (htick : markerTick P.B (levelScale l) ≤ tick)
    (hstep : step ≤ fighterClosureFuel d l (fighterBeforeClosure P d tick l))
    (game : FiniteCounterGame) (phase : FighterPhase)
    (hphase : (fighterClosureAt P d tick l step).activeAt d l = some phase)
    (hcand : phase.candidate = markerCandidate P.B (levelScale l))
    (hgame : phase.game d = game)
    (next : FighterState)
    (haction : fighterLevelAction P d l (fighterClosureAt P d tick l step) = some next)
    (afterPhase : FighterPhase) (hafter : next.activeAt d l = some afterPhase) :
    Relation.ReflTransGen (game.StrategyStep false game.strategy)
      (decodeCounterPosition game phase.officialCode)
      (decodeCounterPosition game afterPhase.officialCode) := by
  subst game
  let state := fighterClosureAt P d tick l step
  have hp : state.activeAt d l = some phase := hphase
  have ha : fighterLevelAction P d l state = some next := haction
  have hlegal := hclosure tick htick step hstep phase hphase hcand
  have hdummy : ∀ live, (fighterDummy d l state).activeAt d l = some live →
      live.officialCode = phase.officialCode := by
    simp only [fighterDummy, hp]
    cases hd : phase.dummy with
    | none =>
      intro live hlive
      rw [hp] at hlive
      cases hlive
      rfl
    | some output =>
      simp only
      split
      · intro live hlive
        rw [hp] at hlive
        cases hlive
        rfl
      · have halloc :=
          activeAt_fighterAllocate
            d l state .dummy (levelInput d l) output
        cases he : fighterAllocate d l .dummy (levelInput d l) output state with
        | mk allocated success =>
          rw [he] at halloc
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true] at halloc ⊢
          · intro live hlive
            rw [halloc] at hlive
            contradiction
          · intro live hlive
            have hlevel : phase.level = l := beq_iff_eq.mp
              (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hp)
            have hput : (allocated.putPhase d { phase with dummyIssued := true }).activeAt d l =
                some { phase with dummyIssued := true } := by
              simp [FighterState.putPhase, FighterState.activeAt, hlevel]
            simp only [hd] at hput
            rw [hput] at hlive
            cases hlive
            rfl
  have hpayoff (q : Coordinate) : ∀ live,
      (fighterPayoff P d l q state).activeAt d l = some live →
      live.officialCode = phase.officialCode := by
    intro live hlive
    obtain ⟨old, hold, pending, rfl⟩ :=
      pending_update_of_activeAt_fighterPayoff
        P d l q state live hlive
    rw [hp] at hold
    cases hold
    rfl
  have hflush (flushed : FighterState) (hf : fighterFlushBuffer d l state = some flushed)
      (hlive : flushed.activeAt d l = some afterPhase) :
      Relation.ReflTransGen ((phase.game d).StrategyStep false (phase.game d).strategy)
        (decodeCounterPosition (phase.game d) phase.officialCode)
        (decodeCounterPosition (phase.game d) afterPhase.officialCode) := by
    obtain ⟨hm, hturn, live, hl, ho, _⟩ := hlegal.2.1 flushed hf
    rw [hlive] at hl
    cases hl
    rw [ho]
    simp only [FighterPhase.official] at hm hturn ⊢
    rw [decode_encode_counter_position]
    apply Relation.ReflTransGen.single
    refine ⟨phase.buffer, hm, rfl, ?_⟩
    intro hcontrolled
    exact False.elim (hturn (hcontrolled.trans hlegal.1.1.symm))
  have hstrategy (hs : fighterStrategyMove P d l state = some next) :
      Relation.ReflTransGen ((phase.game d).StrategyStep false (phase.game d).strategy)
        (decodeCounterPosition (phase.game d) phase.officialCode)
        (decodeCounterPosition (phase.game d) afterPhase.officialCode) := by
    obtain ⟨move, hmove, hm, _, live, hl, ho⟩ := hlegal.2.2 next hs
    rw [hafter] at hl
    cases hl
    rw [ho]
    simp only [FighterPhase.official] at hmove hm ⊢
    rw [decode_encode_counter_position]
    exact Relation.ReflTransGen.single ⟨move, hm, rfl, fun _ ↦ hmove⟩
  simp only [fighterLevelAction, hp, bind, Option.bind_some] at ha
  split at ha
  · cases ha
    rw [hdummy afterPhase hafter]
  · split at ha
    · cases ha
      rw [hpayoff _ afterPhase hafter]
    · cases hf : fighterFlushBuffer d l state with
      | some flushed =>
        simp only [hf, Option.some.injEq] at ha
        subst next
        exact hflush flushed hf hafter
      | none =>
        simp only [hf] at ha
        exact hstrategy ha

/-- A surviving true-marker phase retains its game through closure, and its official position
is reachable from the position before closure. -/
private lemma game_eq_and_strategySteps_of_closureAt
    (P : FighterParams) (d l tick : ℕ)
    (hclosure : TrueMarkerClosureLegal P d l)
    (htick : markerTick P.B (levelScale l) ≤ tick)
    (beforePhase : FighterPhase)
    (hbefore : (fighterBeforeClosure P d tick l).activeAt d l = some beforePhase) :
    ∀ step ≤ fighterClosureFuel d l (fighterBeforeClosure P d tick l),
      ∀ afterPhase, (fighterClosureAt P d tick l step).activeAt d l = some afterPhase →
        afterPhase.candidate = markerCandidate P.B (levelScale l) →
        afterPhase.game d = beforePhase.game d ∧
        Relation.ReflTransGen
          ((beforePhase.game d).StrategyStep false (beforePhase.game d).strategy)
          (decodeCounterPosition (beforePhase.game d) beforePhase.officialCode)
          (decodeCounterPosition (beforePhase.game d) afterPhase.officialCode) := by
  intro step
  induction step with
  | zero =>
    intro hstep afterPhase hafter hcand'
    change (fighterBeforeClosure P d tick l).activeAt d l = some afterPhase at hafter
    rw [hbefore] at hafter
    cases hafter
    exact ⟨rfl, Relation.ReflTransGen.refl⟩
  | succ step ih =>
    intro hstep afterPhase hafter hcand'
    have heq : fighterClosureAt P d tick l (step + 1) =
        (fighterLevelAction P d l (fighterClosureAt P d tick l step)).getD
          (fighterClosureAt P d tick l step) :=
      fighterClosure_succ_eq_levelAction
        P d l step _
    rw [heq] at hafter
    cases ha : fighterLevelAction P d l (fighterClosureAt P d tick l step) with
    | none =>
      simp only [ha, Option.getD_none] at hafter
      exact ih (by omega) afterPhase hafter hcand'
    | some next =>
      simp only [ha, Option.getD_some] at hafter
      obtain ⟨old, hold, hcandidate, hcode⟩ :=
        candidate_gameCode_of_activeAt_fighterLevelAction
          P d l _ next ha afterPhase hafter
      have holdCand : old.candidate = markerCandidate P.B (levelScale l) :=
        hcandidate.symm.trans hcand'
      obtain ⟨hgame, hpath⟩ := ih (by omega) old hold holdCand
      refine ⟨(congrArg decodeCounterGame hcode).trans hgame, hpath.trans ?_⟩
      exact strategySteps_of_fighterLevelAction
        P d l tick step hclosure htick (Nat.le_of_succ_le hstep)
        (beforePhase.game d) old hold holdCand
        hgame next ha afterPhase hafter

/-- At the marker tick, the official position is reachable from the initial game position. -/
private lemma strategySteps_from_initial_at_markerTick
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame) :
    ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase → phase.game d = game →
      Relation.ReflTransGen (game.StrategyStep false game.strategy) game.initialPosition
        (decodeCounterPosition game phase.officialCode) := by
  intro phase hphase hgame_eq
  obtain ⟨beforePhase, hbefore, hbeforeLevel, hbeforeCand, hbeforeInit⟩ :=
    exists_marker_phase_initialPosition
      P d l hlate
  obtain ⟨closePhase, hclose, hcloseLevel, hcloseCand⟩ :=
    exists_marker_phase_after_closure
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure _ le_rfl
      ⟨beforePhase, hbefore, hbeforeLevel, hbeforeCand⟩
  obtain ⟨hcloseGame, hclosePath⟩ :=
    game_eq_and_strategySteps_of_closureAt
      P d l (markerTick P.B (levelScale l)) hclosure le_rfl
      beforePhase hbefore _ le_rfl closePhase hclose hcloseCand
  have hmarker : markerTick P.B (levelScale l) ≠ 0 := by
    intro hzero
    have hevent : eventAt P.B (markerTick P.B (levelScale l)) = none := by
      rw [hzero]
      rfl
    have hlength := hlate.2
    simp only [lastProgram, hevent, Option.map_none, Option.getD_none,
      List.length_nil, Nat.not_lt_zero] at hlength
  obtain ⟨tick, htick⟩ := Nat.exists_eq_succ_of_ne_zero hmarker
  change markerTick P.B (levelScale l) = tick + 1 at htick
  have hclose' :
      (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l)).activeAt d l =
        some closePhase := by
    simpa only [← htick] using hclose
  obtain ⟨levels, hlevels, hstate⟩ :=
    exists_fighterState_eq_foldl_fighterProcessLevel
      P d l tick hgood.positive closePhase hclose'
  rw [← htick] at hstate
  obtain ⟨nextPhase, hnext, pending, hpending⟩ :=
    activeAt_foldl_fighterProcessLevel
      P d l (eventAt P.B (markerTick P.B (levelScale l))) levels
      (fighterCloseLevel P d l (fighterBeforeClosure P d (markerTick P.B (levelScale l)) l))
      hlevels closePhase hclose
  rw [← hstate] at hnext
  have hsame : nextPhase = phase := Option.some.inj (hnext.symm.trans hphase.2.2.2)
  rw [hsame] at hpending
  have hcloseGame' : closePhase.game d = game := by
    simpa only [hpending, FighterPhase.game] using hgame_eq
  have hbeforeGame : beforePhase.game d = game := hcloseGame.symm.trans hcloseGame'
  rw [hbeforeGame] at hbeforeInit hclosePath
  rw [hbeforeInit] at hclosePath
  simpa only [hpending] using hclosePath

/-- A tick after the marker has true-marker phases both before and after internal closure. -/
private lemma exists_true_marker_closure_phases
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick) :
    ∃ beforePhase afterClosurePhase,
      (fighterBeforeClosure P d (tick + 1) l).activeAt d l = some beforePhase ∧
      beforePhase.candidate = markerCandidate P.B (levelScale l) ∧
      beforePhase.game d = game ∧
      (fighterCloseLevel P d l
        (fighterBeforeClosure P d (tick + 1) l)).activeAt d l = some afterClosurePhase ∧
      afterClosurePhase.candidate = markerCandidate P.B (levelScale l) := by
  obtain ⟨currentPhase, hcurrent, hcurrentGame, _⟩ :=
    exists_trueMarkerPhaseAt_with_invariants
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame tick htick
  obtain ⟨beforePhase, hbefore, hcand, hbeforeGame, _⟩ :=
    true_marker_before_closure_invariant
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure
      game tick htick currentPhase hcurrent hcurrentGame
  obtain ⟨afterClosurePhase, hafter, _, hafterCand⟩ :=
    exists_marker_phase_after_closure
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure (tick + 1)
      (Nat.le_succ_of_le htick)
      ⟨beforePhase, hbefore, FighterState.level_eq_of_activeAt_eq_some hbefore, hcand⟩
  exact ⟨beforePhase, afterClosurePhase, hbefore, hcand, hbeforeGame, hafter, hafterCand⟩

/-- Preprocessing at a tick after the marker preserves the official position code. -/
private lemma officialCode_beforeClosure_eq
    (P : FighterParams) (d l : ℕ) (hd : 0 < d)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase)
    (beforePhase : FighterPhase)
    (hbefore : (fighterBeforeClosure P d (tick + 1) l).activeAt d l = some beforePhase) :
    beforePhase.officialCode = phase.officialCode := by
  have hopponent (state : FighterState) (event : ProgramEvent) :
      ∀ live, (fighterOpponent P d l event state).activeAt d l = some live →
        ∃ old, state.activeAt d l = some old ∧ live.officialCode = old.officialCode := by
    have hrefl (live : FighterPhase) (h : state.activeAt d l = some live) :
        ∃ old, state.activeAt d l = some old ∧ live.officialCode = old.officialCode :=
      ⟨live, h, rfl⟩
    unfold fighterOpponent
    split
    · exact hrefl
    · next old hold =>
      have hlevel : old.level = l := beq_iff_eq.mp
        (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) hold)
      cases ht : fighterOpponentTuple d old event with
      | none => exact hrefl
      | some qi =>
        rcases qi with ⟨q, index⟩
        dsimp only
        split
        · exact hrefl
        · split
          · intro live hlive
            have hcancel : (fighterCancel d l .opponentExhausted l state).activeAt d l =
                none := by
              simp only [fighterCancel, hold]
              simp [FighterState.activeAt, List.find?_filter]
            rw [hcancel] at hlive
            contradiction
          · let funded := ({ old.insertIndex d q index with
                opponentRemaining := old.opponentRemaining - 1
                buffer := (old.game d).addCounters old.buffer (old.unitVector d q)
              }).fundRequests d state.fulfilled
            intro live hlive
            obtain ⟨mid, hmid, pending, hlive_eq⟩ :=
              pending_update_of_activeAt_fighterFulfillReady
                P d l (state.putPhase d funded) live hlive
            have hput : (state.putPhase d funded).activeAt d l = some funded := by
              simp [FighterState.putPhase, FighterState.activeAt, funded,
                FighterPhase.fundRequests, FighterPhase.insertIndex, hlevel]
            rw [hput] at hmid
            cases hmid
            exact ⟨old, hold, by rw [hlive_eq]; rfl⟩
  have hchecked (live : FighterPhase)
      (hlive : (fighterFulfillReady P d l
        (fighterBeforeLevel P d (tick + 1) l)).activeAt d l = some live) :
      live.officialCode = phase.officialCode := by
    obtain ⟨old, hold, pending, hlive_eq⟩ :=
      pending_update_of_activeAt_fighterFulfillReady
        P d l (fighterBeforeLevel P d (tick + 1) l) live hlive
    rw [fighterBeforeLevel_succ_eq_of_markerTick_le
      P d l tick hd htick] at hold
    have hsame : old = phase := Option.some.inj (hold.symm.trans hphase.2.2.2)
    rw [hlive_eq, hsame]
  unfold fighterBeforeClosure at hbefore
  cases he : eventAt P.B (tick + 1) with
  | none =>
    simp only [he] at hbefore
    exact hchecked beforePhase hbefore
  | some event =>
    have hlong : levelScale l < event.2.2.1.length := by
      rcases event with ⟨t, i, p, x⟩
      have ht : t = tick + 1 := (canonical_enumeration_spec_sound P.B he).1
      subst t
      exact length_gt_of_eventAt_of_markerTick_lt P.B (levelScale l)
        (tick + 1) (by omega) i p x he
    have hnostart : ¬ (fighterOwner d event.2.2.1.length = some l ∧
        event.2.2.1.length ≤ levelScale l ∧ P.Admissible d l) := by omega
    simp only [he, hnostart, ite_false] at hbefore
    obtain ⟨old, hold, hcode⟩ := hopponent _ event.2.2 beforePhase hbefore
    exact hcode.trans (hchecked old hold)

/-- Completing internal closure yields a legal strategy-following path
between official positions. -/
private lemma strategySteps_of_fighterCloseLevel
    (P : FighterParams) (d l : ℕ)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (beforePhase : FighterPhase)
    (hbefore : (fighterBeforeClosure P d (tick + 1) l).activeAt d l = some beforePhase)
    (hcandidate : beforePhase.candidate = markerCandidate P.B (levelScale l))
    (hgame_eq : beforePhase.game d = game)
    (afterClosurePhase : FighterPhase)
    (hafter : (fighterCloseLevel P d l
        (fighterBeforeClosure P d (tick + 1) l)).activeAt d l = some afterClosurePhase) :
    Relation.ReflTransGen (game.StrategyStep false game.strategy)
      (decodeCounterPosition game beforePhase.officialCode)
      (decodeCounterPosition game afterClosurePhase.officialCode) := by
  have hpreserved : ∀ fuel (state : FighterState) (live : FighterPhase),
      (fighterClosure P d l fuel state).activeAt d l = some live →
        ∃ old, state.activeAt d l = some old ∧ live.candidate = old.candidate := by
    intro fuel
    induction fuel with
    | zero =>
      intro state live hlive
      exact ⟨live, hlive, rfl⟩
    | succ fuel ih =>
      intro state live hlive
      simp only [fighterClosure] at hlive
      cases ha : fighterLevelAction P d l state with
      | none =>
        simp only [ha] at hlive
        exact ⟨live, hlive, rfl⟩
      | some next =>
        simp only [ha] at hlive
        obtain ⟨mid, hmid, hcand⟩ := ih next live hlive
        obtain ⟨old, hold, hmidCand, _⟩ :=
          candidate_gameCode_of_activeAt_fighterLevelAction
            P d l state next ha mid hmid
        exact ⟨old, hold, hcand.trans hmidCand⟩
  obtain ⟨old, hold, hcand⟩ := hpreserved
    (fighterClosureFuel d l (fighterBeforeClosure P d (tick + 1) l))
    (fighterBeforeClosure P d (tick + 1) l) afterClosurePhase hafter
  have hold_eq : old = beforePhase := by
    rw [hbefore] at hold
    exact Option.some.inj hold.symm
  have hafterCand : afterClosurePhase.candidate = markerCandidate P.B (levelScale l) := by
    rw [hold_eq] at hcand
    exact hcand.trans hcandidate
  have hreach :=
    (game_eq_and_strategySteps_of_closureAt
      P d l (tick + 1) hclosure (Nat.le_trans htick (Nat.le_succ tick))
      beforePhase hbefore _ le_rfl afterClosurePhase hafter
      hafterCand).2
  rw [← hgame_eq]
  exact hreach

/-- The higher-level services following closure preserve the official position code. -/
private lemma officialCode_after_higher_levels_eq
    (P : FighterParams) (d l : ℕ) (hd : 0 < d)
    (tick : ℕ)
    (afterClosurePhase : FighterPhase)
    (hafter_closure : (fighterCloseLevel P d l
        (fighterBeforeClosure P d (tick + 1) l)).activeAt d l = some afterClosurePhase)
    (nextPhase : FighterPhase)
    (hnext : TrueMarkerPhaseAt P d l (tick + 1) nextPhase) :
    nextPhase.officialCode = afterClosurePhase.officialCode := by
  obtain ⟨levels, hlevels_lt, hstate_eq⟩ := exists_fighterState_eq_foldl_fighterProcessLevel
    P d l tick hd afterClosurePhase hafter_closure
  have hfold := activeAt_foldl_fighterProcessLevel P d l (eventAt P.B (tick + 1)) levels
    (fighterCloseLevel P d l (fighterBeforeClosure P d (tick + 1) l)) hlevels_lt
    afterClosurePhase hafter_closure
  rcases hfold with ⟨foldPhase, hfoldPhase_active, pending, hfoldPhase_eq⟩
  have hnext_active := hnext.2.2.2
  rw [hstate_eq] at hnext_active
  rw [hfoldPhase_active] at hnext_active
  have h_eq : foldPhase = nextPhase := Option.some.inj hnext_active
  subst h_eq
  rw [hfoldPhase_eq]

/-- The official positions of true-marker phases at consecutive ticks are joined by a legal
strategy-following path. -/
private lemma strategySteps_trueMarkerPhaseAt_succ
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game)
    (tick : ℕ) (htick : markerTick P.B (levelScale l) ≤ tick)
    (phase nextPhase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase)
    (hnextPhase : TrueMarkerPhaseAt P d l (tick + 1) nextPhase) :
    Relation.ReflTransGen (game.StrategyStep false game.strategy)
      (decodeCounterPosition game phase.officialCode)
      (decodeCounterPosition game nextPhase.officialCode) := by
  obtain ⟨beforePhase, afterClosurePhase, hbefore, hcand1, hgame_eq, hafter, _⟩ :=
    exists_true_marker_closure_phases
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame tick htick
  have h1 := officialCode_beforeClosure_eq
    P d l hgood.positive tick htick phase hphase beforePhase hbefore
  have h2 := strategySteps_of_fighterCloseLevel
    P d l hclosure game tick htick beforePhase hbefore hcand1 hgame_eq afterClosurePhase hafter
  have h3 := officialCode_after_higher_levels_eq
    P d l hgood.positive tick afterClosurePhase hafter nextPhase hnextPhase
  rw [← h1, h3]
  exact h2

/-- Reachability from the initial position extends from one tick to the next. -/
private lemma strategySteps_from_initial_succ
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game)
    (tick : ℕ) (htick : tick ≥ markerTick P.B (levelScale l))
    (ih : ∀ phase, TrueMarkerPhaseAt P d l tick phase → phase.game d = game →
      Relation.ReflTransGen (game.StrategyStep false game.strategy) game.initialPosition
        (decodeCounterPosition game phase.officialCode)) :
    ∀ phase, TrueMarkerPhaseAt P d l (tick + 1) phase → phase.game d = game →
      Relation.ReflTransGen (game.StrategyStep false game.strategy) game.initialPosition
        (decodeCounterPosition game phase.officialCode) := by
  intro nextPhase hnextPhase _
  have hinv := exists_trueMarkerPhaseAt_with_invariants
    P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame tick htick
  obtain ⟨phase_t, hphase_t, hphase_game, _⟩ := hinv
  have h1 := ih phase_t hphase_t hphase_game
  have h2 := strategySteps_trueMarkerPhaseAt_succ
    P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame tick htick phase_t nextPhase
    hphase_t hnextPhase
  exact Relation.ReflTransGen.trans h1 h2

/-- Every true-marker official position is reachable from the initial position
of the common game. -/
private lemma strategySteps_from_initial_of_trueMarkerPhaseAt
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game) :
    ∀ tick ≥ markerTick P.B (levelScale l), ∀ phase,
      TrueMarkerPhaseAt P d l tick phase → phase.game d = game →
      Relation.ReflTransGen (game.StrategyStep false game.strategy) game.initialPosition
        (decodeCounterPosition game phase.officialCode) := by
  intro tick htick
  induction tick, htick using Nat.le_induction with
  | base =>
    exact strategySteps_from_initial_at_markerTick
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game
  | succ t ht ih =>
    exact strategySteps_from_initial_succ
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame t ht ih

/-- The official positions of true-marker phases at increasing ticks are joined by a legal
strategy-following path. -/
private lemma strategySteps_between_trueMarkerPhases
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l)
    (game : FiniteCounterGame)
    (hgame : ∀ phase, TrueMarkerPhaseAt P d l (markerTick P.B (levelScale l)) phase →
      phase.game d = game) :
    ∀ tick later, markerTick P.B (levelScale l) ≤ tick → tick ≤ later →
      ∀ phase nextPhase, TrueMarkerPhaseAt P d l tick phase →
        TrueMarkerPhaseAt P d l later nextPhase →
        Relation.ReflTransGen (game.StrategyStep false game.strategy)
          (decodeCounterPosition game phase.officialCode)
          (decodeCounterPosition game nextPhase.officialCode) := by
  intro tick later htick hle
  induction later, hle using Nat.le_induction with
  | base =>
    intro phase nextPhase hphase hnextPhase
    have h_eq : phase = nextPhase := by
      unfold TrueMarkerPhaseAt at hphase hnextPhase
      rcases hphase with ⟨_, _, _, h1⟩
      rcases hnextPhase with ⟨_, _, _, h2⟩
      rw [h1] at h2
      exact Option.some.inj h2
    subst h_eq
    exact Relation.ReflTransGen.refl
  | succ t ht ih =>
    intro phase nextPhase hphase hnextPhase
    have hinv := exists_trueMarkerPhaseAt_with_invariants
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame t (le_trans htick ht)
    obtain ⟨phase_t, hphase_t, _, _⟩ := hinv
    have h1 := ih phase phase_t hphase hphase_t
    have h2 := strategySteps_trueMarkerPhaseAt_succ
      P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame t (le_trans htick ht) phase_t
      nextPhase hphase_t hnextPhase
    exact Relation.ReflTransGen.trans h1 h2

/-- The true-marker phases form a legal strategy-following play of a common winning game,
with the buffer invariant at every tick (blueprint node `constr:opponent`). -/
lemma trueMarkerLegalPlay_of_trueMarkerClosureLegal
    (P : FighterParams) (C cGap cRank d₀ d l : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀)
    (hgood : GoodPadding P d₀ cRank cGap d) (hlate : LateAdmissibleOccurrence P d l)
    (hclosure : TrueMarkerClosureLegal P d l) :
    TrueMarkerLegalPlay P d l := by
  obtain ⟨game, hwins, hgame⟩ :=
    exists_common_game_strategyWins P C cGap cRank d₀ d l hfixed hgood hlate hclosure
  have hinv := exists_trueMarkerPhaseAt_with_invariants
    P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame
  have hreach_init := strategySteps_from_initial_of_trueMarkerPhaseAt
    P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame
  have hreach_ticks := strategySteps_between_trueMarkerPhases
    P C cGap cRank d₀ d l hfixed hgood hlate hclosure game hgame
  refine ⟨hclosure, game, hwins, ?_, hreach_ticks⟩
  intro tick htick
  obtain ⟨phase, hphase, hgame_eq, hbuf⟩ := hinv tick htick
  exact ⟨phase, hphase, hgame_eq, hbuf, hreach_init tick htick phase hphase hgame_eq⟩

end Kolmogorov.Milovanov
