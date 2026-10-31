/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Conditional
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability

/-!
# Live counters count the stored indices

An active phase of the fighter simulation stores, for every retained coordinate, the list of
indices already inserted at that coordinate (`FighterPhase.indices`), and separately a vector of
live counters (`FighterPhase.liveCounters`) that the counter game reads.  The main result
`fighterState_counter_eq_card_indicesAt` says that the two always agree: the value of the live
counter at a retained coordinate is the cardinality of the stored index set there.

The proof checks that a freshly constructed phase satisfies the equation
(`fighter_construction_counter_eq_card_indicesAt`), that inserting an index absent from the
coordinate's list preserves it (`insertIndex_counter_eq_card_indicesAt`), using that the
deterministic fuel index is absent from the list it is chosen against
(`fighterFreshString_notMem`, from `Construction.State`), and that every other primitive action
of the simulation leaves both fields alone.

The equation is used by `Diagonal.OracleAgreement` to read funded coordinates off the counters of
the named true-marker phase.
-/

namespace Kolmogorov.Milovanov

/-- Initialization preserves the coordinate order through game encoding and role exchange.
Each live counter of a freshly constructed phase is the cardinality of the corresponding stored
index list. -/
lemma fighter_construction_counter_eq_card_indicesAt
    (P : FighterParams) (d l : ℕ) (candidate : Candidate) (s : FighterState) :
    ∀ r ∈ (fighter_construction P d l candidate s).J d,
      ((fighter_construction P d l candidate s).game d).coordinateValue
        (fighter_construction P d l candidate s).liveCounters r =
          ((fighter_construction P d l candidate s).indicesAt d r).card := by
  let coords := retainedCoordinateList (constructedLiteralConstant P.literal d)
    (levelInput d l) (P.family.tree d l (levelInput d l))
  let indices := coords.map (fighterInitialIndices P d l candidate s.allocated)
  let counters := indices.map (fun xs ↦ xs.toFinset.card)
  let R := P.c₁ * 2 ^ (levelUpper l - levelScale l)
  let original := finite_counter_game coords
    (coordinatePriceTable P.B P.lam P.n₀ (levelScale l) d candidate coords) counters
    ((P.family.tree d l (levelInput d l)).queries.filter (fun q ↦
      decide (q.1 ∈ fighterStageOutputs P d q.2 s.tick s.allocated))) R
    ((P.family.tree d l (levelInput d l)).normalize (constructedLiteralConstant P.literal d))
    (fighterStageOutputs P d (levelInput d l) s.tick s.allocated).card
  let game := original.controlWinningPlayer
  have htable : game.coordinateTable = coords := by
    dsimp [game, FiniteCounterGame.controlWinningPlayer]
    split <;> rfl
  have hcoords : game.coordinates = coords := by
    rw [FiniteCounterGame.coordinates, htable]
    have herase {α : Type} [BEq α] [LawfulBEq α] (xs : List α)
        (h : xs.Nodup) : xs.eraseDups = xs := by
      induction xs with
      | nil => rfl
      | cons a xs ih =>
        rw [List.eraseDups_cons]
        have hf : xs.filter (fun x ↦ !x == a) = xs := by
          apply List.filter_eq_self.mpr
          intro x hx
          have hne : x ≠ a := by intro he; subst x; exact (List.nodup_cons.mp h).1 hx
          simp [hne]
        rw [hf, ih (List.nodup_cons.mp h).2]
    exact herase coords (nodup_eraseDups_list _)
  have hgame : (fighter_construction P d l candidate s).game d = game :=
    decode_encode_counter_game game
  intro r hr
  have hrgame : r ∈ ((fighter_construction P d l candidate s).game d).coordinates := by
    simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
      List.mem_toFinset, List.mem_eraseDups] using hr
  have hr' : r ∈ game.coordinates := by simpa only [hgame] using hrgame
  have hrc : r ∈ coords := by simpa only [hcoords] using hr'
  change game.coordinateValue counters r =
    (if r ∈ game.coordinates then
      (indices[game.coordinates.idxOf r]?.getD []).toFinset else ∅).card
  simp only [FiniteCounterGame.coordinateValue, hcoords, hrc, ite_true,
    counters, indices, List.getElem?_map, List.getElem?_idxOf hrc,
    Option.map_some, Option.getD_some]

/-- Inserting an index absent from the selected coordinate preserves the counter/cardinality
equality at every retained coordinate. The selected counter and set cardinality both
increase by one; all other retained coordinates keep their values. -/
lemma insertIndex_counter_eq_card_indicesAt
    (d : ℕ) (phase : FighterPhase) (q : Coordinate) (index : BitString)
    (hinv : ∀ r ∈ phase.J d,
      (phase.game d).coordinateValue phase.liveCounters r = (phase.indicesAt d r).card)
    (hfresh : index ∉ phase.indicesAt d q) :
    ∀ r ∈ (phase.insertIndex d q index).J d,
      ((phase.insertIndex d q index).game d).coordinateValue
        (phase.insertIndex d q index).liveCounters r =
          ((phase.insertIndex d q index).indicesAt d r).card := by
  intro r hr
  have hr' : r ∈ (phase.game d).coordinates := by
    simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
      FighterPhase.insertIndex, FighterPhase.game, List.mem_toFinset, List.mem_eraseDups]
      using hr
  have hi := List.idxOf_lt_length_of_mem hr'
  have h := hinv r hr
  change (if r ∈ (phase.game d).coordinates then
    ((phase.game d).addCounters phase.liveCounters (phase.unitVector d q))[
      (phase.game d).coordinates.idxOf r]?.getD 0 else 0) =
    (if r ∈ (phase.game d).coordinates then
      ((((phase.game d).coordinates.zipIdx.map (fun (t, i) ↦
        let old := phase.indices[i]?.getD []
        if t = q then (old ++ [index]).eraseDups else old))[
          (phase.game d).coordinates.idxOf r]?.getD []).toFinset) else ∅).card
  simp only [hr', ite_true, FiniteCounterGame.addCounters, FighterPhase.unitVector,
    List.getElem?_map, List.getElem?_range hi, List.getElem?_zipIdx,
    List.getElem?_idxOf hr', Option.map_some, Nat.zero_add, Option.getD_some]
  simp only [FiniteCounterGame.coordinateValue, FighterPhase.indicesAt, hr', ite_true] at h
  by_cases he : r = q
  · subst r
    have hf : index ∉
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []).toFinset := by
      simpa only [FighterPhase.indicesAt, hr', ite_true] using hfresh
    have heq (xs : List BitString) : xs.eraseDups.toFinset = xs.toFinset := by
      ext x
      simp only [List.mem_toFinset, List.mem_eraseDups]
    simp only [ite_true, heq, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hf, h]
  · simp only [he, ite_false, Nat.add_zero]
    exact h

namespace FighterPhase

/-- The live counter of every retained coordinate of `p` is the cardinality of its stored
index set. -/
private def CounterCard (d : ℕ) (p : FighterPhase) : Prop :=
  ∀ r ∈ p.J d, (p.game d).coordinateValue p.liveCounters r = (p.indicesAt d r).card

end FighterPhase

namespace FighterState

/-- Every active phase of `s` satisfies `FighterPhase.CounterCard`. -/
private def CounterCard (d : ℕ) (s : FighterState) : Prop :=
  ∀ p ∈ s.active, p.CounterCard d

namespace CounterCard

variable {P : FighterParams} {d : ℕ}

private theorem of_activeAt {s : FighterState} {l : ℕ} {p : FighterPhase}
    (hs : CounterCard d s) (hp : s.activeAt d l = some p) : p.CounterCard d :=
  hs p (List.mem_of_find?_eq_some hp)

private theorem foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, CounterCard d s → CounterCard d (f a s)) (xs : List α) (s : FighterState)
    (hs : CounterCard d s) : CounterCard d (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih _ (hf a s hs)

private theorem putPhase (s : FighterState) (p : FighterPhase) (hs : CounterCard d s)
    (hp : p.CounterCard d) : CounterCard d (s.putPhase d p) := by
  intro next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp
  · exact hs next (List.mem_filter.mp hn).1

private theorem cancel (l cause : ℕ) (reason : PhaseEnd) (s : FighterState)
    (hs : CounterCard d s) : CounterCard d (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · intro p hp
    exact hs p (List.mem_filter.mp hp).1

private theorem abortAbove (l : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply foldl _ _ _ _ hs
  intro p t ht
  split
  · exact cancel _ _ _ _ ht
  · exact ht

private theorem allocate (l : ℕ) (kind : DirectiveKind) (target : ℕ) (out : BitString)
    (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact hs
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact cancel _ _ _ _ hs
    | some p => exact abortAbove _ _ hs

private theorem payoff (l : ℕ) (q : Coordinate) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact hs
  · split
    · have ha := allocate (d := d) l .payoff q.2 q.1 s hs
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · intro p hp
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha old hold
    · exact hs

private theorem fulfillReady (l : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact hs
  · exact foldl _ (payoff l) _ _ hs

private theorem fuelUnit (l : ℕ) (q : Coordinate) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt hs hp
    split
    · rename_i hguard
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := allocate (d := d) l .fuel (levelUpper l + d) out (s.putPhase d charged)
        (putPhase s charged hs hq)
      change CounterCard d
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
        · have hfresh : index ∉ charged.indicesAt d q := by
            simp only [FighterPhase.indicesAt, show charged.game d = phase.game d from rfl,
              hguard.1, ite_true, List.mem_toFinset]
            exact fighterFreshString_notMem d _
          have hins : (charged.insertIndex d q index).CounterCard d :=
            insertIndex_counter_eq_card_indicesAt d charged q index hq hfresh
          exact fulfillReady l _ (putPhase next _ ha hins)
    · exact hs

private theorem fuelUnits (l : ℕ) (q : Coordinate) (count : ℕ) (s : FighterState)
    (hs : CounterCard d s) : CounterCard d (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuelUnit l q s hs)

private theorem dummy (l : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt hs hp
    split
    · exact hs
    · rename_i output hout
      split
      · exact hs
      · have ha := allocate (d := d) l .dummy (levelInput d l) output s hs
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · exact putPhase next _ ha hq

private theorem opponent (l : ℕ) (e : ProgramEvent) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := of_activeAt hs hp
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact cancel _ _ _ _ hs
        · apply fulfillReady l
          apply putPhase s _ hs
          exact insertIndex_counter_eq_card_indicesAt d phase _ _ hq (by assumption)

private theorem startPhase (l : ℕ) (c : Candidate) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  exact putPhase _ _ (abortAbove l _ (cancel _ _ _ s hs))
    (fighter_construction_counter_eq_card_indicesAt P d l c _)

private theorem flushBuffer (l : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    have hq := of_activeAt hs hp
    simp only [bind, Option.bind_some]
    split
    · exact putPhase s _ hs hq
    · exact hs

private theorem strategyMove (l : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d ((fighterStrategyMove P d l s).getD s) := by
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
          have hn : CounterCard d next := by
            apply foldl _ _ _ _ hs
            intro qi t ht
            exact fuelUnits l qi.1 (move[qi.2]?.getD 0) t ht
          change CounterCard d ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            exact putPhase next _ hn (of_activeAt (p := live) hn hlive)
        · exact hs
    · exact hs

private theorem levelAction (l : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact hs
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact dummy l s hs
    · split
      · exact payoff l _ s hs
      · cases hf : fighterFlushBuffer d l s with
        | none => exact strategyMove l s hs
        | some next =>
          simpa only [hf, Option.getD_some] using flushBuffer (d := d) l s hs

private theorem closure (l fuel : ℕ) (s : FighterState) (hs : CounterCard d s) :
    CounterCard d (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact hs
    | some next =>
      have hn := levelAction (P := P) (d := d) l s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

private theorem processLevel (l : ℕ) (e : Option TimedEvent) (s : FighterState)
    (hs : CounterCard d s) : CounterCard d (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply closure
  cases e with
  | none => exact fulfillReady l s hs
  | some e =>
    dsimp only
    split
    · exact startPhase l _ _ (fulfillReady l s hs)
    · exact opponent l _ _ (fulfillReady l s hs)

end CounterCard

end FighterState

/-- In every reachable active phase, the live counter of each retained coordinate equals the
cardinality of its stored index set. Initialization stores the cardinalities of the initial
index lists as counters; every insertion (fuel or opponent) adds an index absent from the
coordinate's list and one counter unit at that coordinate; all other updates keep both fields. -/
lemma fighterState_counter_eq_card_indicesAt (P : FighterParams) (d tick : ℕ) :
    ∀ phase ∈ (fighterState P d tick).active, ∀ r ∈ phase.J d,
      (phase.game d).coordinateValue phase.liveCounters r = (phase.indicesAt d r).card := by
  change FighterState.CounterCard d (fighterState P d tick)
  induction tick with
  | zero => simp [fighterState, initialFighterState, FighterState.CounterCard]
  | succ tick ih =>
    change FighterState.CounterCard d (fighter_actions P d (tick + 1) (fighterState P d tick))
    unfold fighter_actions
    split
    · simp [FighterState.CounterCard, initialFighterState]
    · exact FighterState.CounterCard.foldl
        (fun l s ↦ fighterProcessLevel P d l (eventAt P.B (tick + 1)) s)
        (fun l s ↦ FighterState.CounterCard.processLevel l _ s) _ _ ih

end Kolmogorov.Milovanov
