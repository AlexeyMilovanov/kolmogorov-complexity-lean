/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Order.OrderIsoNat
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.CommonGameInvariantTick

/-!
# Stabilization of the official counter position

Two facts about the true-marker phase of the fighter construction.

* `gameCode_buffer_eq_of_fuelBatch`: the batch of fuel purchases that implements a controlled
  response keeps the game code and the buffer of the phase found at the level. `OpponentStream`
  uses it for the buffering policy of controlled turns.
* `true_marker_officialCode_eventually_stable`: along a true-marker legal play the official
  position code is eventually constant. Every legal move of the finite counter game consumes
  budget, so the decoded budgets decrease and stabilize, and every stored official code is
  canonical, so equal decoded positions give equal codes.

The second fact is the stabilization step of the blueprint proof of node `constr:opponent`.
The Lean proof of `true_marker_opponent_stream_legal` does not need it: it shows directly that
the live predicate holds at every tick from the marker tick on. The stabilization result is
kept as a complementary statement about the construction and is not used elsewhere.
-/

namespace Kolmogorov.Milovanov

/-- The sum of the remaining budgets cannot increase along a strategy play. -/
private lemma budgetSum_le_of_strategy_reachable
    (game : FiniteCounterGame) (pos next : CounterPosition game) :
    Relation.ReflTransGen (game.StrategyStep false game.strategy) pos next →
    next.budgetSum ≤ pos.budgetSum := by
  intro h
  induction h with
  | refl => exact le_rfl
  | tail b hbc ih =>
    rcases hbc with ⟨move, hlegal, heq, _⟩
    subst heq
    have hlt := counter_move_decreases_budget game _ move hlegal
    exact hlt.le.trans ih

/-- A strategy play with equal initial and final budgets contains no moves. -/
private lemma eq_of_strategy_reachable_of_budgetSum_eq
    (game : FiniteCounterGame) (pos next : CounterPosition game) :
    Relation.ReflTransGen (game.StrategyStep false game.strategy) pos next →
    next.budgetSum = pos.budgetSum →
    pos = next := by
  intro h
  induction h with
  | refl =>
    intro _
    rfl
  | tail hab hbc _ih =>
    intro heq
    rcases hbc with ⟨move, hlegal, heq_c, _⟩
    subst heq_c
    have hlt := counter_move_decreases_budget game _ move hlegal
    have hle := budgetSum_le_of_strategy_reachable game pos _ hab
    omega

/-- A predicate holds for the stored game and official position of every active phase. -/
private def activeCodesSatisfy (Q : CounterGameCode × CounterPositionCode → Prop)
    (s : FighterState) : Prop :=
  ∀ p ∈ s.active, Q (p.gameCode, p.officialCode)

section CodeInvariants

variable {Q : CounterGameCode × CounterPositionCode → Prop}

/-- A looked-up active phase satisfies any invariant of the active game-position codes. -/
private lemma active_codes_of_activeAt
    (d : ℕ) {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : activeCodesSatisfy Q s) (hp : s.activeAt d l = some p) : Q (p.gameCode, p.officialCode) :=
  hs p (List.mem_of_find?_eq_some hp)

/-- Inserting a phase preserves a code invariant if the inserted phase satisfies it. -/
private lemma active_codes_putPhase
    (d : ℕ) (s : FighterState) (p : FighterPhase) (hs : activeCodesSatisfy Q s)
    (hp : Q (p.gameCode, p.officialCode)) : activeCodesSatisfy Q (s.putPhase d p) := by
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs next (List.mem_filter.mp hn).1

/-- Canceling a phase preserves every invariant of the surviving game-position codes. -/
private lemma active_codes_cancel
    (d : ℕ) (l cause : ℕ) (reason : PhaseEnd) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · intro p hp
    exact hs p (List.mem_filter.mp hp).1

/-- Aborting higher levels preserves every invariant of the surviving game-position codes. -/
private lemma active_codes_abortAbove
    (d l : ℕ) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply List.foldlRecOn _ _ hs
  intro t ht p _
  split
  · exact active_codes_cancel d _ _ _ _ ht
  · exact ht

/-- Allocating a directive preserves every invariant of the surviving game-position codes. -/
private lemma active_codes_allocate
    (d l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact active_codes_cancel d _ _ _ _ hs
    | some p => exact active_codes_abortAbove d _ _ hs

/-- A payoff preserves every invariant of the active game-position codes. -/
private lemma active_codes_payoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := active_codes_allocate d l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha old hold
    · exact hs

/-- Fulfilling ready requests preserves every invariant of the active game-position codes. -/
private lemma active_codes_fulfillReady
    (P : FighterParams) (d l : ℕ) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact List.foldlRecOn _ _ hs (fun t ht q _ ↦ active_codes_payoff P d l q t ht)

/-- Buying one fuel unit preserves every invariant of the active game-position codes. -/
private lemma active_codes_fuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := active_codes_of_activeAt d hs hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := active_codes_allocate d l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (active_codes_putPhase d s charged hs hq)
      change activeCodesSatisfy Q
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
        · exact active_codes_fulfillReady P d l _ (active_codes_putPhase d next _ ha hq)
    · exact hs

/-- Buying fuel preserves every invariant of the active game-position codes. -/
private lemma active_codes_fuelUnits
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (active_codes_fuelUnit P d l q s hs)

/-- Issuing a dummy directive preserves every invariant of the active game-position codes. -/
private lemma active_codes_dummy
    (d l : ℕ) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := active_codes_of_activeAt d hs hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := active_codes_allocate d l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact active_codes_putPhase d next _ ha hq

/-- Processing an opponent event preserves every invariant of the active game-position codes. -/
private lemma active_codes_opponent
    (P : FighterParams) (d l : ℕ) (event : ProgramEvent) (s : FighterState)
    (hs : activeCodesSatisfy Q s) :
    activeCodesSatisfy Q (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := active_codes_of_activeAt d hs hp
    split
    · exact hs
    · rename_i q index htuple
      split
      · exact hs
      · split
        · exact active_codes_cancel d _ _ _ _ hs
        · apply active_codes_fulfillReady (Q := Q) P d l
          apply active_codes_putPhase d _ _ hs
          exact hq

end CodeInvariants

/-- A batch of fuel purchases at a level keeps the game code and the buffer of the phase found
at that level before the batch; a failed purchase cannot expose an unrelated phase there. -/
lemma gameCode_buffer_eq_of_fuelBatch
    (P : FighterParams) (d l : ℕ) (coords : List Coordinate) (move : CounterMove)
    (state : FighterState) :
    ∀ live, (coords.zipIdx.foldl (fun s qi ↦
      fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) state).activeAt d l = some live →
      ∃ old, state.activeAt d l = some old ∧
        live.gameCode = old.gameCode ∧ live.buffer = old.buffer := by
  let R := fun s t : FighterState ↦ ∀ live, t.activeAt d l = some live →
    ∃ old, s.activeAt d l = some old ∧ live.gameCode = old.gameCode ∧ live.buffer = old.buffer
  have hrefl (s : FighterState) : R s s := fun p hp ↦ ⟨p, hp, rfl, rfl⟩
  have htrans {s t u : FighterState} (hst : R s t) (htu : R t u) : R s u := by
    intro live hlive
    obtain ⟨mid, hmid, hgame, hbuf⟩ := htu live hlive
    obtain ⟨old, hold, hgame', hbuf'⟩ := hst mid hmid
    exact ⟨old, hold, hgame.trans hgame', hbuf.trans hbuf'⟩
  have hunit (q : Coordinate) (s : FighterState) : R s (fighterFuelUnit P d l q s) := by
    intro live hlive
    cases hs : s.activeAt d l with
    | none => simp [fighterFuelUnit, hs] at hlive
    | some old =>
      by_cases hguard : q ∈ (old.game d).coordinates ∧ 0 < old.controlledRemaining
      · have hv := controlledResponseView_fighterFuelUnit
          P d l s old q hs hguard.1 hguard.2 live hlive
        simp only [controlledResponseView, Prod.mk.injEq] at hv
        exact ⟨old, rfl, hv.1, hv.2.2.2.1⟩
      · simp only [fighterFuelUnit, hs, hguard, ite_false] at hlive
        cases hlive
        exact ⟨_, rfl, rfl, rfl⟩
  have hunits (q : Coordinate) (count : ℕ) (s : FighterState) :
      R s (fighterFuelUnits P d l q count s) := by
    induction count generalizing s with
    | zero => exact hrefl s
    | succ count ih => exact htrans (hunit q s) (ih _)
  exact List.foldlRecOn (motive := R state) _ _ (hrefl state)
    (fun s hs qi _ ↦ htrans hs (hunits qi.1 (move[qi.2]?.getD 0) s))

/-- Initialization stores the encoding of the initial position in the stored game. -/
private lemma fighter_construction_officialCode_eq_encode
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (state : FighterState) :
    let phase := fighter_construction P d l candidate state
    phase.officialCode = (decodeCounterPosition (phase.game d) phase.officialCode).encode := by
  dsimp only [fighter_construction, FighterPhase.fundRequests, FighterPhase.game]
  rw [decode_encode_counter_game, decode_encode_counter_position]

/-- Servicing a level preserves canonical official codes. Flushes and controlled responses store
encoded successor positions in the same game. -/
private lemma officialCode_eq_encode_processLevel
    (P : FighterParams) (d l : ℕ) (event : Option TimedEvent) (state : FighterState)
    (hs : ∀ p ∈ state.active,
      p.officialCode = (decodeCounterPosition (p.game d) p.officialCode).encode) :
    ∀ p ∈ (fighterProcessLevel P d l event state).active,
      p.officialCode = (decodeCounterPosition (p.game d) p.officialCode).encode := by
  let Q : CounterGameCode × CounterPositionCode → Prop := fun c ↦
    c.2 = (decodeCounterPosition (decodeCounterGame c.1) c.2).encode
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active, Q (p.gameCode, p.officialCode)
  have haction (s next : FighterState) (hs : Good s)
      (ha : fighterLevelAction P d l s = some next) : Good next := by
    cases hp : s.activeAt d l with
    | none => simp [fighterLevelAction, hp] at ha
    | some phase =>
      simp only [fighterLevelAction, hp, bind, Option.bind_some] at ha
      split at ha
      · cases ha
        exact active_codes_dummy d l s hs
      · split at ha
        · cases ha
          exact active_codes_payoff P d l _ s hs
        · cases hf : fighterFlushBuffer d l s with
          | some flushed =>
            simp only [hf, Option.some.injEq] at ha
            subst next
            simp only [fighterFlushBuffer, hp, bind, Option.bind_some] at hf
            split at hf
            · cases hf
              apply active_codes_putPhase d _ _ hs
              change ((phase.game d).afterMove (phase.official d) phase.buffer).encode =
                (decodeCounterPosition (phase.game d)
                  ((phase.game d).afterMove (phase.official d) phase.buffer).encode).encode
              rw [decode_encode_counter_position]
            · contradiction
          | none =>
            simp only [hf, fighterStrategyMove, hp, bind, Option.bind_some] at ha
            split at ha
            · cases hm : (phase.game d).strategy (phase.official d) with
              | none => simp [hm] at ha
              | some move =>
                simp only [hm, Option.bind_some] at ha
                split at ha
                · let middle := (phase.game d).coordinates.zipIdx.foldl
                    (fun s qi ↦ fighterFuelUnits P d l qi.1 (move[qi.2]?.getD 0) s) s
                  have hmiddle : Good middle :=
                    List.foldlRecOn _ _ hs (fun t ht qi _ ↦
                      active_codes_fuelUnits P d l qi.1 (move[qi.2]?.getD 0) t ht)
                  change (match middle.activeAt d l with
                    | none => some middle
                    | some live => some (middle.putPhase d
                        { live with officialCode :=
                          ((phase.game d).afterMove (phase.official d) move).encode })) =
                      some next at ha
                  cases hlive : middle.activeAt d l with
                  | none =>
                    simp only [hlive, Option.some.injEq] at ha
                    subst next
                    exact hmiddle
                  | some live =>
                    simp only [hlive, Option.some.injEq] at ha
                    subst next
                    apply active_codes_putPhase d _ _ hmiddle
                    obtain ⟨old, hold, hg, -⟩ := gameCode_buffer_eq_of_fuelBatch
                      P d l (phase.game d).coordinates move s live hlive
                    rw [hp] at hold
                    cases hold
                    have hgame : live.game d = phase.game d := congrArg decodeCounterGame hg
                    change ((phase.game d).afterMove (phase.official d) move).encode =
                      (decodeCounterPosition (live.game d)
                        ((phase.game d).afterMove (phase.official d) move).encode).encode
                    rw [hgame, decode_encode_counter_position]
                · contradiction
            · contradiction
  have hclosure (fuel : ℕ) (s : FighterState) (hs : Good s) :
      Good (fighterClosure P d l fuel s) := by
    induction fuel generalizing s with
    | zero => exact hs
    | succ fuel ih =>
      simp only [fighterClosure]
      cases ha : fighterLevelAction P d l s with
      | none => exact hs
      | some next => exact ih next (haction s next hs ha)
  have hstart (candidate : Candidate) (s : FighterState) (hs : Good s) :
      Good (fighterStartPhase P d l candidate s) := by
    let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
    have hw : Good waiting :=
      active_codes_abortAbove d l _ (active_codes_cancel d l l .replaced s hs)
    have hnew : Q ((fighter_construction P d l candidate waiting).gameCode,
        (fighter_construction P d l candidate waiting).officialCode) :=
      fighter_construction_officialCode_eq_encode
        P d l candidate waiting
    exact active_codes_putPhase d waiting _ hw hnew
  change Good (fighterProcessLevel P d l event state)
  unfold fighterProcessLevel fighterCloseLevel
  apply hclosure
  have hchecked : Good (fighterFulfillReady P d l state) := active_codes_fulfillReady P d l state hs
  cases event with
  | none => exact hchecked
  | some e =>
    dsimp only
    split
    · exact hstart _ _ hchecked
    · exact active_codes_opponent P d l e.2.2 _ hchecked

/-- Every active phase reached by the fighter has a canonical official position code. -/
private lemma officialCode_eq_encode_fighterState
    (P : FighterParams) (d tick : ℕ) :
    ∀ p ∈ (fighterState P d tick).active,
      p.officialCode = (decodeCounterPosition (p.game d) p.officialCode).encode := by
  let Good := fun s : FighterState ↦ ∀ p ∈ s.active,
    p.officialCode = (decodeCounterPosition (p.game d) p.officialCode).encode
  change Good (fighterState P d tick)
  induction tick with
  | zero =>
    intro p hp
    change p ∈ ([] : List FighterPhase) at hp
    cases hp
  | succ tick ih =>
    change Good (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · intro p hp
      change p ∈ ([] : List FighterPhase) at hp
      cases hp
    · exact List.foldlRecOn _ _ ih (fun s hs l _ ↦
        officialCode_eq_encode_processLevel P d l _ s hs)

/-- The official code is canonical when decoded in the common true-marker game. -/
private lemma officialCode_eq_encode_trueMarker
    (P : FighterParams) (d l tick : ℕ)
    (hlegal : TrueMarkerLegalPlay P d l)
    (htick : markerTick P.B (levelScale l) ≤ tick)
    (phase : FighterPhase)
    (hphase : TrueMarkerPhaseAt P d l tick phase) :
    phase.officialCode =
      (decodeCounterPosition (Classical.choose hlegal.2) phase.officialCode).encode := by
  obtain ⟨other, hother, hgame, _⟩ :=
    (Classical.choose_spec hlegal.2).2.1 tick htick
  have heq : other = phase :=
    Option.some.inj (hother.2.2.2.symm.trans hphase.2.2.2)
  subst other
  have hcode :=
    officialCode_eq_encode_fighterState
      P d tick phase (List.mem_of_find?_eq_some hphase.2.2.2)
  rw [hgame] at hcode
  exact hcode

/-- In a true-marker legal play, the official position codes at consecutive ticks eventually
coincide: each legal move consumes budget, and every stored official code is canonical. This is
the stabilization step of the blueprint proof of `constr:opponent`; the Lean proof of
`true_marker_opponent_stream_legal` does not use it. -/
lemma true_marker_officialCode_eventually_stable
    (P : FighterParams) (d l : ℕ) (hlegal : TrueMarkerLegalPlay P d l) :
    ∃ tick_final ≥ markerTick P.B (levelScale l),
      ∀ tick ≥ tick_final, ∀ phase nextPhase,
        TrueMarkerPhaseAt P d l tick phase →
        TrueMarkerPhaseAt P d l (tick + 1) nextPhase →
        phase.officialCode = nextPhase.officialCode := by
  let game := Classical.choose hlegal.2
  have hwins_game_reach := Classical.choose_spec hlegal.2
  have hgame := hwins_game_reach.2.1
  have hreach := hwins_game_reach.2.2
  let tau := markerTick P.B (levelScale l)
  let f := fun tick ↦ match (fighterState P d tick).activeAt d l with
    | none => 0
    | some phase => (decodeCounterPosition game phase.officialCode).budgetSum
  have hf_eq (tick : ℕ) (phase : FighterPhase)
      (hphase : TrueMarkerPhaseAt P d l tick phase) :
      f tick = (decodeCounterPosition game phase.officialCode).budgetSum := by
    dsimp only [f]
    rw [hphase.2.2.2]
  have hf_decr : ∀ tick ≥ tau, f (tick + 1) ≤ f tick := by
    intro tick htick
    have htick_succ : tau ≤ tick + 1 := by omega
    obtain ⟨phase1, hphase1, _⟩ := hgame tick htick
    obtain ⟨phase2, hphase2, _⟩ := hgame (tick + 1) htick_succ
    rw [hf_eq tick phase1 hphase1]
    rw [hf_eq (tick + 1) phase2 hphase2]
    have h_rel := hreach tick (tick + 1) htick (by omega) phase1 phase2 hphase1 hphase2
    exact budgetSum_le_of_strategy_reachable game _ _ h_rel
  have hf_antitone : Antitone (fun tick ↦ f (tau + tick)) :=
    antitone_nat_of_succ_le fun tick ↦ hf_decr (tau + tick) (Nat.le_add_right tau tick)
  obtain ⟨offset, hconstant⟩ := WellFoundedLT.antitone_chain_condition hf_antitone
  have hf_const (tick : ℕ) (htick : tau + offset ≤ tick) : f tick = f (tau + offset) := by
    have htau : tau ≤ tick := by omega
    have hoffset : offset ≤ tick - tau := by omega
    simpa only [Nat.add_sub_of_le htau] using (hconstant (tick - tau) hoffset).symm
  use tau + offset, Nat.le_add_right tau offset
  intro tick htick_ge phase nextPhase hphase hnextPhase
  have htick_tau : tau ≤ tick := by omega
  have htick_succ_tau : tau ≤ tick + 1 := by omega
  have h_rel := hreach tick (tick + 1) htick_tau (by omega) phase nextPhase hphase hnextPhase
  have h_eq : (decodeCounterPosition game nextPhase.officialCode).budgetSum =
      (decodeCounterPosition game phase.officialCode).budgetSum := by
    have h1 := hf_eq tick phase hphase
    have h2 := hf_eq (tick + 1) nextPhase hnextPhase
    rw [← h1, ← h2]
    exact (hf_const (tick + 1) (by omega)).trans (hf_const tick htick_ge).symm
  have h_pos_eq := eq_of_strategy_reachable_of_budgetSum_eq game _ _ h_rel h_eq
  have hcode1 := officialCode_eq_encode_trueMarker P d l tick hlegal htick_tau phase hphase
  have hcode2 := officialCode_eq_encode_trueMarker
    P d l (tick + 1) hlegal htick_succ_tau nextPhase hnextPhase
  rw [hcode1, hcode2, h_pos_eq]

end Kolmogorov.Milovanov
