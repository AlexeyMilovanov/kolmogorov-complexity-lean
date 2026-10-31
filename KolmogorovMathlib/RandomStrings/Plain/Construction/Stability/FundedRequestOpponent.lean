/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.FighterInvariant

/-!
# The opponent budget of a true-marker phase is never exhausted

The fighter construction charges every genuinely new opponent insertion against a budget of
`P.c₁ * 2 ^ (levelUpper l - levelScale l)` units.  This module shows that the phase started at the
true marker of a level cannot be cancelled because this budget ran out, as soon as the tail
bound `rest P.B (levelScale l) (levelUpper l)` fits in the budget.

The argument is an accounting of the charged coordinate/index pairs.  The *opponent ledger*
(`OpponentLedger`) of a phase is an explicit finite set of charged pairs whose size, together
with the remaining budget, is the initial budget; each charged pair is stored in the phase,
is described by a short base-machine program, and has an output absent from the initial output
snapshot.  The ledger is preserved by every elementary scheduler operation
(`opponentLedger_fighterState`, an instance of `FighterInvariant`).  An archived exhaustion
(`exists_fresh_tuple_of_opponentExhausted`) would then add one more charged pair to a full
ledger, and the injectivity of the literal encoding
(`card_le_rest_of_simple_pairCode`) bounds such a set by the post-marker output tail.

The result `trueMarkerNeverEndsFor_opponentExhausted` is one of the four exclusions combined in
`FundedRequest` to show that a true-marker phase survives forever, and is also used in
`LegalPlay`.
-/

namespace Kolmogorov.Milovanov

/-- A controlled or opponent insertion keeps all old indices at every retained coordinate and
adds the inserted index at the target coordinate. -/
lemma FighterPhase.indicesAt_insertIndex
    (p : FighterPhase) (d : ℕ) (q r : Coordinate) (index : BitString)
    (hr : r ∈ (p.game d).coordinates) :
    (p.insertIndex d q index).indicesAt d r =
      if r = q then insert index (p.indicesAt d r) else p.indicesAt d r := by
  classical
  change (if r ∈ (p.game d).coordinates then
    ((((p.game d).coordinates.zipIdx.map (fun (t, i) =>
      let old := p.indices[i]?.getD []
      if t = q then (old ++ [index]).eraseDups else old))[(p.game d).coordinates.idxOf r]?.getD
        []).toFinset) else ∅) = _
  simp only [hr, ite_true, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_idxOf hr, Option.map_some, Nat.zero_add, Option.getD_some]
  unfold FighterPhase.indicesAt
  simp only [hr, ite_true]
  split
  · ext s
    simp only [List.mem_toFinset, List.mem_eraseDups,
      List.mem_append, List.mem_singleton, Finset.mem_insert]
    exact or_comm
  · rfl

/-- An insertion never removes an index from any retained coordinate. -/
private lemma indicesAt_subset_insertIndex
    (p : FighterPhase) (d : ℕ) (q r : Coordinate) (index : BitString)
    (hr : r ∈ (p.game d).coordinates) :
    p.indicesAt d r ⊆ (p.insertIndex d q index).indicesAt d r := by
  classical
  rw [FighterPhase.indicesAt_insertIndex p d q r index hr]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- A valid candidate's initial index list contains every literal curried output in its frozen
base table. -/
lemma mem_fighterInitialIndices
    (P : FighterParams) (d l : ℕ) (c : Candidate) (as : List AllocatedDirective)
    (q : Coordinate) (index : BitString)
    (hc : validCandidate P.B (levelScale l) c = true)
    (hy : pairCode (triple q.1 (q.2 - d) c.1) index ∈
      stageOutputs P.B (levelUpper l) c.2) :
    index ∈ fighterInitialIndices P d l c as q := by
  have hpast : index ∈ pastExtensionIndices P.B (levelScale l) c (levelScale l)
      (triple q.1 (q.2 - d) c.1) := by
    apply (mem_past_extension_indices _ _ _ _ _ _ hc).mpr
    simpa only [extensionScale, level_upper_eq] using hy
  simp only [fighterInitialIndices, List.mem_eraseDups, List.mem_append]
  left
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa only [decide_eq_true_eq] using hpast⟩
  apply List.mem_map.mpr
  refine ⟨pairCode (triple q.1 (q.2 - d) c.1) index, ?_, decodeSecond_pairCode _ _⟩
  exact List.mem_toFinset.mp hy

/-- Initialization stores exactly the initial index list at every retained coordinate, in the
game's order. -/
lemma indicesAt_fighter_construction
    (P : FighterParams) (d l : ℕ) (c : Candidate) (s : FighterState)
    (q : Coordinate)
    (hq : q ∈ ((fighter_construction P d l c s).game d).coordinates) :
    (fighter_construction P d l c s).indicesAt d q =
      (fighterInitialIndices P d l c s.allocated q).toFinset := by
  let coords := retainedCoordinateList (constructedLiteralConstant P.literal d)
    (levelInput d l) (P.family.tree d l (levelInput d l))
  have hcoords : ((fighter_construction P d l c s).game d).coordinates = coords := by
    dsimp only [fighter_construction, FighterPhase.fundRequests, FighterPhase.game]
    rw [decode_encode_counter_game]
    unfold FiniteCounterGame.controlWinningPlayer
    split <;> exact eraseDups_eq_self_of_nodup (nodup_eraseDups_list _)
  have hq' : q ∈ coords := hcoords ▸ hq
  unfold FighterPhase.indicesAt
  simp only [hq, ↓reduceIte]
  rw [hcoords]
  change ((coords.map (fighterInitialIndices P d l c s.allocated))[coords.idxOf q]?.getD
    []).toFinset = _
  rw [List.getElem?_map, List.getElem?_idxOf hq']
  rfl

/-- The opponent ledger of a phase: it keeps its valid candidate and all initial base-table
indices, together with an explicitly chosen set of charged coordinate/index pairs.  That set has
exactly the spent opponent budget; its members remain stored, have actual short base
descriptions, and were absent from the initial output snapshot. -/
private def OpponentLedger (P : FighterParams) (d : ℕ) (p : FighterPhase) : Prop :=
  validCandidate P.B (levelScale p.level) p.candidate = true ∧
    (∀ q ∈ (p.game d).coordinates, ∀ index,
      pairCode (triple q.1 (q.2 - d) p.candidate.1) index ∈
        stageOutputs P.B (levelUpper p.level) p.candidate.2 →
      index ∈ p.indicesAt d q) ∧
    ∃ S : Finset (Coordinate × BitString),
      S.card + p.opponentRemaining = P.c₁ * 2 ^ (levelUpper p.level - levelScale p.level) ∧
      ∀ a ∈ S, a.1 ∈ (p.game d).coordinates ∧ d ≤ a.1.2 ∧
        a.2 ∈ p.indicesAt d a.1 ∧
        Simple P.B.V (pairCode (triple a.1.1 (a.1.2 - d) p.candidate.1) a.2)
          (levelUpper p.level) ∧
        pairCode (triple a.1.1 (a.1.2 - d) p.candidate.1) a.2 ∉
          stageOutputs P.B (levelUpper p.level) p.candidate.2

/-- The opponent ledger depends only on the level, candidate, initial allocations, game code,
indices and remaining opponent budget of a phase. -/
private lemma OpponentLedger.congr {P : FighterParams} {d : ℕ} (p p' : FighterPhase)
    (heq : (p.level, p.candidate, p.initialAllocations, p.gameCode, p.indices,
        p.opponentRemaining) =
      (p'.level, p'.candidate, p'.initialAllocations, p'.gameCode, p'.indices,
        p'.opponentRemaining))
    (hp : OpponentLedger P d p) : OpponentLedger P d p' := by
  rcases p with ⟨l, c, s, a, g, is, o, v, b, r, f, pending, x, di, cp⟩
  rcases p' with ⟨l', c', s', a', g', is', o', v', b', r', f', pending', x', di', cp'⟩
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact hp

/-- A phase just constructed at a valid candidate has an empty ledger and an untouched
budget; snapshot coverage follows from the finite initialization table. -/
private lemma OpponentLedger.construction (P : FighterParams) (d l : ℕ) (c : Candidate)
    (s : FighterState) (hc : validCandidate P.B (levelScale l) c = true) :
    OpponentLedger P d (fighter_construction P d l c s) := by
  classical
  refine ⟨hc, ?_, ∅, by simp [fighter_construction, FighterPhase.fundRequests], ?_⟩
  · intro q hq index hy
    rw [indicesAt_fighter_construction P d l c s q hq, List.mem_toFinset]
    exact mem_fighterInitialIndices P d l c s.allocated q index hc hy
  · simp

/-- A controlled insertion preserves snapshot coverage and all existing charged pairs, and
spends no opponent budget. -/
private lemma OpponentLedger.insertIndex {P : FighterParams} {d : ℕ} {p : FighterPhase}
    (q : Coordinate) (index : BitString) (hp : OpponentLedger P d p) :
    OpponentLedger P d (p.insertIndex d q index) := by
  rcases hp with ⟨hc, hcoverage, S, hcard, hS⟩
  refine ⟨hc, ?_, S, hcard, ?_⟩
  · intro r hr stored hy
    exact indicesAt_subset_insertIndex p d q r index hr (hcoverage r hr stored hy)
  · intro a ha
    obtain ⟨hr, hd, hi, hs, hn⟩ := hS a ha
    exact ⟨hr, hd, indicesAt_subset_insertIndex p d q a.1 index hr hi, hs, hn⟩

/-- A fresh affordable opponent transaction extends the charged set by its actual
coordinate/index pair.  Membership in the old charged set would contradict freshness, snapshot
coverage excludes initial outputs, and the cardinality increase matches the budget debit. -/
private lemma OpponentLedger.insertOpponent {P : FighterParams} {d : ℕ} {p : FighterPhase}
    {event : ProgramEvent} {q : Coordinate} {index : BitString}
    (he : produces P.B.V event.1 [] event.2)
    (htuple : fighterOpponentTuple d p event = some (q, index))
    (hfresh : index ∉ p.indicesAt d q) (hbudget : p.opponentRemaining ≠ 0)
    (hp : OpponentLedger P d p) :
    OpponentLedger P d
      { p.insertIndex d q index with opponentRemaining := p.opponentRemaining - 1 } := by
  classical
  obtain ⟨hq, hd, hlen, hout⟩ := fighterOpponentTuple_spec d p event q index htuple
  rcases hp with ⟨hc, hcoverage, S, hcard, hS⟩
  have hnot : (q, index) ∉ S := fun h => hfresh (hS (q, index) h).2.2.1
  refine ⟨hc, ?_, insert (q, index) S, ?_, ?_⟩
  · intro r hr stored hy
    exact indicesAt_subset_insertIndex p d q r index hr (hcoverage r hr stored hy)
  · rw [Finset.card_insert_of_notMem hnot]
    change S.card + 1 + (p.opponentRemaining - 1) =
      P.c₁ * 2 ^ (levelUpper p.level - levelScale p.level)
    omega
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · refine ⟨hq, hd, ?_, ?_, ?_⟩
      · change index ∈ (p.insertIndex d q index).indicesAt d q
        rw [FighterPhase.indicesAt_insertIndex p d q q index hq]
        simp
      · apply (simple_iff_exists_program _ _ _).mpr
        exact ⟨event.1, hlen, hout ▸ he⟩
      · exact fun hy => hfresh (hcoverage q hq index hy)
    · obtain ⟨hr, hd, hi, hs, hn⟩ := hS a ha
      exact ⟨hr, hd, indicesAt_subset_insertIndex p d q a.1 index hr hi, hs, hn⟩

/-- The scheduler invariant whose active and archived phases all carry an opponent ledger. -/
private def opponentLedgerInvariant (P : FighterParams) (d : ℕ) : FighterInvariant P d where
  Active := OpponentLedger P d
  Archived e := OpponentLedger P d e.1
  active_congr := fun p p' heq hp ↦ OpponentLedger.congr p p' heq hp
  active_construction := fun l c s hc ↦ OpponentLedger.construction P d l c s hc
  active_insertIndex := fun _ q index hp ↦ hp.insertIndex q index
  archived_cancel := fun p _ _ _ _ hp ↦ OpponentLedger.congr p _ rfl hp

/-- An opponent insertion keeps the ledger invariant: it either does nothing, cancels the phase
for exhaustion of the budget, or extends the ledger by the charged pair. -/
private lemma holds_fighterOpponent_opponentLedger (P : FighterParams) (d l : ℕ)
    (event : ProgramEvent) (he : produces P.B.V event.1 [] event.2) (s : FighterState)
    (hs : (opponentLedgerInvariant P d).Holds s) :
    (opponentLedgerInvariant P d).Holds (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    have hq := hs.active_of_activeAt hp
    split
    · exact hs
    · rename_i q index htuple
      split
      · exact hs
      · rename_i hfresh
        split
        · refine hs.cancel l l .opponentExhausted fun p hp' ↦ ?_
          rw [hp] at hp'
          cases hp'
          exact OpponentLedger.congr phase _ rfl hq
        · rename_i hbudget
          refine (hs.putPhase ?_).fulfillReady l
          exact OpponentLedger.congr { phase.insertIndex d q index with
              opponentRemaining := phase.opponentRemaining - 1 } _ rfl
            (OpponentLedger.insertOpponent he htuple hfresh hbudget hq)

/-- Every active or archived phase of the fighter state carries an opponent ledger, which
accounts for the actual charged pairs without any tail-bound assumption. -/
private lemma opponentLedger_fighterState (P : FighterParams) (d tick : ℕ) :
    (∀ p ∈ (fighterState P d tick).active, OpponentLedger P d p) ∧
    ∀ e ∈ (fighterState P d tick).ended, OpponentLedger P d e.1 :=
  (opponentLedgerInvariant P d).holds_fighterState
    (fun l event he s hs ↦ holds_fighterOpponent_opponentLedger P d l event he s hs) tick

/-- The data left behind by an opponent insertion which cancelled a phase for exhausting its
budget: the budget is zero and the attempted pair is a fresh actual opponent transaction. -/
private def ExhaustionSource (P : FighterParams) (d : ℕ) (p : FighterPhase) : Prop :=
  p.opponentRemaining = 0 ∧ ∃ event q index,
    produces P.B.V event.1 [] event.2 ∧
    fighterOpponentTuple d p event = some (q, index) ∧ index ∉ p.indicesAt d q

/-- The scheduler invariant saying that every archived phase ended by opponent exhaustion has an
`ExhaustionSource`. -/
private def exhaustionSourceInvariant (P : FighterParams) (d : ℕ) : FighterInvariant P d where
  Active _ := True
  Archived e := e.2.2.1 = .opponentExhausted → ExhaustionSource P d e.1
  active_congr := fun _ _ _ _ ↦ trivial
  active_construction := fun _ _ _ _ ↦ trivial
  active_insertIndex := fun _ _ _ _ ↦ trivial
  archived_cancel := fun _ _ _ _ hne _ h ↦ absurd h hne

/-- An opponent insertion keeps the exhaustion-source invariant: the only way it archives a phase
for exhaustion is through the zero-budget branch of a fresh actual tuple. -/
private lemma holds_fighterOpponent_exhaustionSource (P : FighterParams) (d l : ℕ)
    (event : ProgramEvent) (he : produces P.B.V event.1 [] event.2) (s : FighterState)
    (hs : (exhaustionSourceInvariant P d).Holds s) :
    (exhaustionSourceInvariant P d).Holds (fighterOpponent P d l event s) := by
  unfold fighterOpponent
  split
  · exact hs
  · rename_i phase hp
    split
    · exact hs
    · rename_i q index htuple
      split
      · exact hs
      · rename_i hfresh
        split
        · rename_i hzero
          refine hs.cancel l l .opponentExhausted fun p hp' _ ↦ ?_
          rw [hp] at hp'
          cases hp'
          exact ⟨hzero, event, q, index, he, htuple, hfresh⟩
        · exact (hs.putPhase trivial).fulfillReady l

/-- An archived opponent exhaustion comes from the zero-budget branch of an actual fresh opponent
tuple.  The archive retains its indices and budget, so the attempted pair is still absent. -/
private lemma exists_fresh_tuple_of_opponentExhausted (P : FighterParams) (d tick : ℕ) :
    ∀ e ∈ (fighterState P d tick).ended, e.2.2.1 = .opponentExhausted →
      e.1.opponentRemaining = 0 ∧ ∃ event q index,
        produces P.B.V event.1 [] event.2 ∧
        fighterOpponentTuple d e.1 event = some (q, index) ∧
        index ∉ e.1.indicesAt d q :=
  ((exhaustionSourceInvariant P d).holds_fighterState
    (fun l event he s hs ↦ holds_fighterOpponent_exhaustionSource P d l event he s hs) tick).2

/-- The literal encoding is injective on coordinate/index pairs whose target is at least the
padding.  The lower bounds are essential for recovering the target after natural subtraction. -/
private lemma eq_of_pairCode_triple_eq
    (d : ℕ) (w : BitString) (a b : Coordinate × BitString)
    (ha : d ≤ a.1.2) (hb : d ≤ b.1.2)
    (h : pairCode (triple a.1.1 (a.1.2 - d) w) a.2 =
      pairCode (triple b.1.1 (b.1.2 - d) w) b.2) : a = b := by
  have hp : (triple a.1.1 (a.1.2 - d) w, a.2) =
      (triple b.1.1 (b.1.2 - d) w, b.2) := pairCode_injective h
  have ht := @triple_injective (a.1.1, a.1.2 - d, w)
    (b.1.1, b.1.2 - d, w) (congrArg Prod.fst hp)
  have hx : a.1.1 = b.1.1 :=
    congrArg (fun v : BitString × ℕ × BitString => v.1) ht
  have hr : a.1.2 - d = b.1.2 - d :=
    congrArg (fun v : BitString × ℕ × BitString => v.2.1) ht
  have htarget : a.1.2 = b.1.2 := by omega
  have hs : a.2 = b.2 := congrArg (fun v : BitString × BitString => v.2) hp
  exact Prod.ext (Prod.ext hx htarget) hs

/-- Any finite set of coordinate/index pairs with distinct literal post-marker outputs has
cardinality at most `rest`.  Finiteness comes from the set of all outputs of bounded programs. -/
private lemma card_le_rest_of_simple_pairCode
    (B : Base) (d n N : ℕ) (w : BitString) (S : Finset (Coordinate × BitString))
    (hS : ∀ a ∈ S, d ≤ a.1.2 ∧
      Simple B.V (pairCode (triple a.1.1 (a.1.2 - d) w) a.2) N ∧
      pairCode (triple a.1.1 (a.1.2 - d) w) a.2 ∉
        stageOutputs B N (markerTick B n)) :
    S.card ≤ rest B n N := by
  classical
  let f : Coordinate × BitString → BitString :=
    fun a => pairCode (triple a.1.1 (a.1.2 - d) w) a.2
  have hinj : Set.InjOn f (S : Set (Coordinate × BitString)) := by
    intro a ha b hb heq
    exact eq_of_pairCode_triple_eq d w a b (hS a ha).1 (hS b hb).1 heq
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hsub : (S.image f : Set BitString) ⊆
      {y | Simple B.V y N ∧ y ∉ stageOutputs B N (markerTick B n)} := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact (hS a ha).2
  have hfinite : {y | Simple B.V y N ∧ y ∉ stageOutputs B N (markerTick B n)}.Finite :=
    (simple_finite_card_lt B.V N).1.subset (fun _ hy => hy.1)
  have hle := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hcard] at hle
  exact hle

/-- The true-marker phase of a level cannot exhaust its opponent budget when the post-marker
output tail fits in that budget.  Each newly charged index has a distinct literal curried output
of a program of length at most `levelUpper l`, absent from the initial marker snapshot, and
initial and controlled indices are never charged again.  An exhaustion would therefore require
more distinct post-marker outputs than the supplied tail bound. -/
theorem trueMarkerNeverEndsFor_opponentExhausted
    (P : FighterParams) (d l : ℕ)
    (htail : rest P.B (levelScale l) (levelUpper l) ≤
      P.c₁ * 2 ^ (levelUpper l - levelScale l)) :
    TrueMarkerNeverEndsFor P d l .opponentExhausted := by
  classical
  intro tick e he hl hc hexhausted
  obtain ⟨hzero, event, q, index, hevent, htuple, hfresh⟩ :=
    exists_fresh_tuple_of_opponentExhausted P d tick e he hexhausted
  obtain ⟨-, hcoverage, S, hcard, hS⟩ := (opponentLedger_fighterState P d tick).2 e he
  obtain ⟨hq, hdq, hlen, hout⟩ := fighterOpponentTuple_spec d e.1 event q index htuple
  simp only [hl, hc, markerCandidate] at hcoverage hcard hS hlen hout
  have hnot : (q, index) ∉ S := fun h => hfresh (hS (q, index) h).2.2.1
  have hbound := card_le_rest_of_simple_pairCode P.B d (levelScale l) (levelUpper l)
    (lastProgram P.B (levelScale l)) (insert (q, index) S) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · refine ⟨hdq, ?_, ?_⟩
        · exact (simple_iff_exists_program _ _ _).mpr ⟨event.1, hlen, hout ▸ hevent⟩
        · exact fun hy => hfresh (hcoverage q hq index hy)
      · obtain ⟨-, hda, -, hsa, hna⟩ := hS a ha
        exact ⟨hda, hsa, hna⟩)
  rw [Finset.card_insert_of_notMem hnot] at hbound
  rw [hzero, Nat.add_zero] at hcard
  omega

end Kolmogorov.Milovanov
