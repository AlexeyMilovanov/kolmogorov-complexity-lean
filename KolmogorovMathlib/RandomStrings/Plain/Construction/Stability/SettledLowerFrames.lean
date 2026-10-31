/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.ServiceInvariant

/-!
# Frames of lower levels while higher levels are serviced

Once the true marker program is long, the construction cannot change the lower levels any
more: all later events are longer than the protected cutoff, so the lower levels are only
serviced by "stuttering" ticks. This module collects the facts behind that argument.

* the tower is monotone, and the upper endpoint of a lower level lies below the lower
  endpoint of a higher level;
* marker incompressibility gives, for all large levels, the ownership window of the last
  program, together with the witnessed marker event and the absence of later short events;
* an event-free (or only long-event) tick leaves the bounded output tables, hence the safety
  tests `fighterSafe` on protected coordinates, unchanged;
* `FighterRequestRanges d state` records that the game coordinates and pending requests of
  each active level lie strictly between its input and its event-length budget, and this is
  preserved by one level service (`fighterProcessLevel_tick_and_requestRanges`);
* servicing a level at or above a cutoff `l` does not alter the local histories of the levels
  below `l`, nor the archive of abortions caused below `l`
  (`fighterProcessLevel_lower_history_eq_of_le`).

The last two results are instances of `ServiceInvariant`. They are used by
`SettledLowerLevels` to show that completed states of the lower levels are settled, and
the remaining lemmas are used by the common-game and phase-separation modules.
-/

namespace Kolmogorov.Milovanov

/-- The upper endpoint of a lower level is at most the lower endpoint of a higher level. -/
lemma levelUpper_le_levelLower (j l : ℕ) (hj : j < l) : levelUpper j ≤ levelLower l :=
  tower_le_tower (by omega)

/-- Marker incompressibility gives the ownership window eventually: for all large levels `l`
the last program at the level scale is longer than `levelLower l` and at most `levelScale l`.
The conclusion also retains that the marker candidate is valid and that no later event has a
program of length at most the level scale. -/
lemma exists_level_threshold_marker_window (B : Base) :
    ∃ l₀ : ℕ, ∀ l ≥ l₀,
      (levelLower l < (lastProgram B (levelScale l)).length ∧
        (lastProgram B (levelScale l)).length ≤ levelScale l) ∧
      validCandidate B (levelScale l) (markerCandidate B (levelScale l)) = true ∧
      ∀ t > markerTick B (levelScale l), ∀ i p x,
        eventAt B t = some (t, i, p, x) → levelScale l < p.length := by
  obtain ⟨cW, nW, _, hW⟩ := last_program_conditional_complexity B
  obtain ⟨nV, _, hV⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨nE, _, hE⟩ := last_program_stabilizes_short_descriptions_no_later B
  obtain ⟨c₂, hc₂⟩ := plainK_le_length B.V B.optimalV
  obtain ⟨c₃, hc₃⟩ := condK_le_plainK B.V B.optimalV
  let c := c₂ + c₃ + cW
  refine ⟨max 1 (max (max nW (max nV nE)) (c + 1)), ?_⟩
  intro l hl
  have hlpos : 1 ≤ l := (le_max_left _ _).trans hl
  have hln : l ≤ levelScale l := (by omega : l ≤ 2 * l).trans (le_tower _)
  have hll : l ≤ levelLower l := (by omega : l ≤ 2 * l - 1).trans (le_tower _)
  have hnW : nW ≤ levelScale l := by omega
  have hnV : nV ≤ levelScale l := by omega
  have hnE : nE ≤ levelScale l := by omega
  have hc : c < levelLower l := by omega
  have hscale : levelScale l = 2 ^ levelLower l := by
    unfold levelScale levelLower
    have heq : 2 * l = (2 * l - 1) + 1 := by omega
    rw [heq]
    rfl
  have htwice : 2 * levelLower l ≤ levelScale l := by
    rw [hscale]
    exact fighter_twice_le_pow _
  have hK : (levelScale l : ENat) ≤
      ((lastProgram B (levelScale l)).length + c : ℕ) := by
    calc
      (levelScale l : ENat) ≤ condK B.V (lastProgram B (levelScale l))
          (bits (levelScale l)) + cW := (hW _ hnW).2.1
      _ ≤ plainK B.V (lastProgram B (levelScale l)) + c₃ + cW := by
        gcongr
        exact hc₃ _ _
      _ ≤ (lastProgram B (levelScale l)).length + c₂ + c₃ + cW := by
        gcongr
        exact hc₂ _
      _ = ((lastProgram B (levelScale l)).length + c : ℕ) := by
        simp only [Nat.cast_add, c]
        ac_rfl
  have hnat : levelScale l ≤ (lastProgram B (levelScale l)).length + c := by
    exact_mod_cast hK
  exact ⟨⟨by omega, (hW _ hnW).1⟩, (hV _ hnV).1, hE _ hnE⟩

/-- The marker event occurs at a positive tick, and it and every subsequent event have
programs longer than the cutoff `K`, provided the last program is longer than `K` and all
later events are longer than `n`. -/
lemma markerTick_pos_and_lt_length_of_ge (B : Base) (n K : ℕ)
    (hvalid : validCandidate B n (markerCandidate B n) = true)
    (hK : K < (lastProgram B n).length)
    (hlater : ∀ t > markerTick B n, ∀ i p x,
      eventAt B t = some (t, i, p, x) → n < p.length) :
    0 < markerTick B n ∧
      ∀ t ≥ markerTick B n, ∀ e, eventAt B t = some e → K < e.2.2.1.length := by
  obtain ⟨hlen, i, x, hev⟩ := (canonical_enumeration_spec_candidate B n _).mp hvalid
  have hm : eventAt B (markerTick B n) =
      some (markerTick B n, i, lastProgram B n, x) := hev
  refine ⟨(canonical_enumeration_spec_position B hm).1, ?_⟩
  intro t ht e he
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, hm] at he
    cases he
    exact hK
  · obtain ⟨u, j, p, y⟩ := e
    have hu : u = t := (canonical_enumeration_spec_sound B he).1
    subst u
    exact hK.trans_le (hlen.trans (hlater t h j p y he).le)

/-- A tick whose event, if any, has a program longer than `K` leaves every output table of
index at most `K` unchanged. -/
private lemma stageOutputs_eq_pred_of_long_event (B : Base) (t K : ℕ)
    (hevent : ∀ e, eventAt B t = some e → K < e.2.2.1.length) :
    ∀ k ≤ K, stageOutputs B k t = stageOutputs B k (t - 1) := by
  intro k hk
  cases t with
  | zero => rfl
  | succ t =>
    let pending := (masterState B t).1 ++ (plainBatch B (t + 1)).filter (fun e =>
      decide (e.1 ∉ (masterState B t).1.map Prod.fst ++
        (masterState B t).2.1.map (fun e => e.2.2.1)))
    cases hp : pending with
    | nil =>
      dsimp [pending] at hp
      simp only [stageOutputs, stageOutputList, eventHistory, masterState, masterStep,
        hp, Nat.add_sub_cancel]
    | cons e rest =>
      dsimp [pending] at hp
      have hev : eventAt B (t + 1) =
          some (t + 1, (eventHistory B t).length, e) := by
        simp only [eventAt, eventHistory, masterState, masterStep, hp]
        simp
      have hlen : ¬ e.1.length ≤ k := by
        have := hevent _ hev
        change K < e.1.length at this
        omega
      simp only [stageOutputs, stageOutputList, eventHistory, masterState, masterStep, hp]
      simp [List.filterMap_append, hlen]

/-- A tick whose event, if any, has a program longer than `K` leaves the safety test of every
coordinate within the protected program budget `K` unchanged. -/
lemma fighterSafe_eq_pred_of_long_event
    (P : FighterParams) (d t K : ℕ)
    (hevent : ∀ e, eventAt P.B t = some e → K < e.2.2.1.length)
    (q : Coordinate) (hq : q.2 - halfPadding d ≤ K) :
    fighterSafe P d t q = fighterSafe P d (t - 1) q := by
  simp only [fighterSafe, stageOutputs_eq_pred_of_long_event P.B t K hevent _ hq]

/-- The request-range invariant of one phase: its game coordinates and pending requests have
thresholds strictly above the level's input and strictly below its event-length budget. -/
def FighterPhase.RequestRanges (phase : FighterPhase) (d : ℕ) : Prop :=
  (∀ q ∈ (phase.game d).coordinates,
    levelInput d phase.level + 1 ≤ q.2 ∧ q.2 < levelUpper phase.level) ∧
  ∀ q ∈ phase.pending, levelInput d phase.level + 1 ≤ q.2 ∧ q.2 < levelUpper phase.level

/-- The finite range invariant of a global state: every active phase satisfies
`FighterPhase.RequestRanges`. -/
def FighterRequestRanges (d : ℕ) (state : FighterState) : Prop :=
  ∀ phase ∈ state.active, phase.RequestRanges d

private lemma FighterPhase.RequestRanges.congr {phase phase' : FighterPhase} {d : ℕ}
    (h : phase.RequestRanges d) (hgame : phase'.gameCode = phase.gameCode)
    (hpending : phase'.pending = phase.pending) (hlevel : phase'.level = phase.level) :
    phase'.RequestRanges d := by
  have hgame' : phase'.game d = phase.game d := by simp only [FighterPhase.game, hgame]
  unfold FighterPhase.RequestRanges
  rw [hgame', hpending, hlevel]
  exact h

private lemma FighterPhase.RequestRanges.fundRequests {phase : FighterPhase} {d : ℕ}
    (fulfilled : List Coordinate) (h : phase.RequestRanges d) :
    (phase.fundRequests d fulfilled).RequestRanges d := by
  refine ⟨h.1, ?_⟩
  intro q hq
  simp only [FighterPhase.fundRequests, List.mem_eraseDups, List.mem_filter,
    List.mem_append, decide_eq_true_eq] at hq
  rcases hq.1 with hmem | hmem
  · exact h.2 q hmem
  · exact h.1 q hmem.1

/-- The phase freshly constructed at an admissible level satisfies the request ranges. -/
private lemma FighterPhase.requestRanges_construction (P : FighterParams) (d j : ℕ)
    (hd : 1 ≤ d) (hadm : P.Admissible d j) (candidate : Candidate) (s : FighterState) :
    (fighter_construction P d j candidate s).RequestRanges d := by
  have hcoords (g : FiniteCounterGame) : g.controlWinningPlayer.coordinates = g.coordinates := by
    unfold FiniteCounterGame.controlWinningPlayer
    split <;> rfl
  unfold fighter_construction
  apply FighterPhase.RequestRanges.fundRequests
  constructor
  · intro q hq
    simp only [FighterPhase.game, decode_encode_counter_game] at hq
    rw [hcoords] at hq
    simp only [FiniteCounterGame.coordinates, finite_counter_game, List.mem_eraseDups] at hq
    have hmem : q ∈ finite_referee_coordinates (d + P.literal.cV) (levelInput d j)
        (P.family.tree d j (levelInput d j)) := List.mem_toFinset.mpr hq
    obtain ⟨threshold, _, _, hmin, _⟩ :=
      (mem_finite_referee_coordinates _ _ _ q.1 q.2).mp hmem
    have hmax := retained_coordinates_within_key_lemma_range P.family P.literal.cV P.n₀
      d j P.threshold hd hadm q.1 q.2 hmem
    exact ⟨hmin, hmax.2.2.1.trans hmax.2.2.2⟩
  · simp

private lemma FighterRequestRanges.putPhase {d : ℕ} {s : FighterState} {phase : FighterPhase}
    (hs : FighterRequestRanges d s) (hp : phase.RequestRanges d) :
    FighterRequestRanges d (s.putPhase d phase) := by
  intro p hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hp
  · exact hs p (List.mem_filter.mp hmem).1

private lemma FighterRequestRanges.cancel {d : ℕ} {s : FighterState}
    (hs : FighterRequestRanges d s) (j : ℕ) (reason : PhaseEnd) (cause : ℕ) :
    FighterRequestRanges d (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact hs
  · exact fun p hp ↦ hs p (List.mem_filter.mp hp).1

private lemma FighterRequestRanges.record {d : ℕ} {s : FighterState}
    (hs : FighterRequestRanges d s) (q : Coordinate) :
    FighterRequestRanges d
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map
          (fun p ↦ { p with pending := p.pending.filter (fun r ↦ r != q) }) } := by
  intro p hp
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
  have ho := hs old hold
  exact ⟨ho.1, fun r hr ↦ ho.2 r (List.mem_filter.mp hr).1⟩

/-- Servicing a level preserves the request ranges of the state, as an instance of
`ServiceInvariant` that also tracks the clock `c`. -/
private def requestRangesInvariant (P : FighterParams) (d k c : ℕ) (hd : 1 ≤ d) :
    ServiceInvariant P d k where
  Inv s := s.tick = c ∧ FighterRequestRanges d s
  PhaseInv phase := phase.RequestRanges d
  phaseInv_of_activeAt hs hp := hs.2 _ (List.mem_of_find?_eq_some hp)
  phaseInv_congr h hgame hpending hlevel := h.congr hgame hpending hlevel
  phaseInv_fundRequests h := h.fundRequests _
  phaseInv_construction s candidate hadm :=
    FighterPhase.requestRanges_construction P d k hd hadm candidate s
  inv_putPhase hs hp := ⟨hs.1, hs.2.putPhase hp⟩
  inv_cancel _ hs := ⟨by unfold fighterCancel; split <;> exact hs.1, hs.2.cancel _ _ _⟩
  inv_failed hs := hs
  inv_allocated _ hs := hs
  inv_started hs := hs
  inv_record hs _ _ _ := ⟨hs.1, hs.2.record _⟩

/-- One level service does not change the clock and preserves the request ranges.
The start branch obtains its ranges from admissibility; all other branches retain the game
and only fund, filter, or discard bounded requests. -/
lemma fighterProcessLevel_tick_and_requestRanges
    (P : FighterParams) (d k : ℕ) (hd : 1 ≤ d) (event : Option TimedEvent)
    (state : FighterState) (hranges : FighterRequestRanges d state) :
    (fighterProcessLevel P d k event state).tick = state.tick ∧
      FighterRequestRanges d (fighterProcessLevel P d k event state) :=
  (requestRangesInvariant P d k state.tick hd).inv_processLevel event ⟨rfl, hranges⟩

/-- The observable prefix protected while larger levels are serviced: the local histories of
the levels below `l`, and the archive of abortions caused below `l`. -/
private def LowerFrame (d l : ℕ) (before after : FighterState) : Prop :=
  (∀ j < l, fighterLevelHistory after d j = fighterLevelHistory before d j) ∧
    after.ended.filter (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) =
      before.ended.filter (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l))

private lemma LowerFrame.refl (d l : ℕ) (s : FighterState) : LowerFrame d l s s :=
  ⟨fun _ _ ↦ rfl, rfl⟩

private lemma LowerFrame.trans {d l : ℕ} {s t u : FighterState}
    (hst : LowerFrame d l s t) (htu : LowerFrame d l t u) : LowerFrame d l s u :=
  ⟨fun j hj ↦ (htu.1 j hj).trans (hst.1 j hj), htu.2.trans hst.2⟩

/-- Replacing the phase record of a level at least `l` preserves the protected prefix. -/
private lemma LowerFrame.putPhase
    (d l : ℕ) (s : FighterState) (phase : FighterPhase) (hp : l ≤ phase.level) :
    LowerFrame d l s (s.putPhase d phase) := by
  refine ⟨?_, rfl⟩
  intro j hj
  have hne : j ≠ phase.level := by omega
  have hact : (s.putPhase d phase).activeAt d j = s.activeAt d j := by
    simp only [FighterState.putPhase, FighterState.activeAt, List.find?_cons,
      beq_eq_false_iff_ne.mpr (Ne.symm hne)]
    exact FighterState.find?_level_filter_ne _ _ _ hne
  change ((s.putPhase d phase).activeAt d j, _, _, _) = _
  rw [hact]
  rfl

/-- Canceling a level at least `l` preserves smaller histories, and an abortion with a cause
at least `l` does not enter the protected abortion archive. -/
private lemma LowerFrame.cancel
    (d l k : ℕ) (hk : l ≤ k) (reason : PhaseEnd) (cause : ℕ)
    (hcause : reason = .aborted → l ≤ cause) (s : FighterState) :
    LowerFrame d l s (fighterCancel d k reason cause s) := by
  unfold fighterCancel
  split
  · exact LowerFrame.refl d l s
  · rename_i phase hphase
    have hlevel : phase.level = k := FighterState.level_eq_of_activeAt_eq_some hphase
    refine ⟨?_, ?_⟩
    · intro j hj
      have hne : j ≠ k := by omega
      simp only [fighterLevelHistory, FighterState.activeAt,
        FighterState.find?_level_filter_ne _ j k hne, List.filter_append]
      have hnot : (phase.level == j) = false := beq_eq_false_iff_ne.mpr (by omega)
      simp [hnot]
    · have hnot : ¬ (reason = .aborted ∧ cause < l) := by
        rintro ⟨hreason, hlt⟩
        have := hcause hreason
        omega
      simp [List.filter_append, hnot]

/-- Logging an allocation of a level at least `l` changes no protected allocation log. -/
private lemma LowerFrame.allocated
    (d l : ℕ) (s : FighterState) (a : AllocatedDirective) (ha : l ≤ a.level) :
    LowerFrame d l s { s with allocated := s.allocated ++ [a] } := by
  refine ⟨?_, rfl⟩
  intro j hj
  have hne : (a.level == j) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [fighterLevelHistory, List.filter_append, hne, FighterState.activeAt]

/-- Logging a start of a level at least `l` changes no protected start log. -/
private lemma LowerFrame.started
    (d l k : ℕ) (s : FighterState) (candidate : Candidate) (hk : l ≤ k) :
    LowerFrame d l s { s with started := s.started ++ [(k, candidate)] } := by
  refine ⟨?_, rfl⟩
  intro j hj
  have hne : (k == j) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [fighterLevelHistory, List.filter_append, hne, FighterState.activeAt]

/-- A successful payoff of a level `k ≥ l` cannot delete a pending request of a level below
`l`. The payoff threshold is above the input of level `k`, whereas every smaller pending
threshold is below its own upper endpoint, which is at most the scale of level `k`. -/
private lemma LowerFrame.record
    (d l k : ℕ) (hk : l ≤ k) (s : FighterState) (q : Coordinate)
    (hq : levelInput d k + 1 ≤ q.2) (hranges : FighterRequestRanges d s) :
    LowerFrame d l s
      { s with
        fulfilled := s.fulfilled ++ [q]
        active := s.active.map (fun p => { p with pending := p.pending.filter (· != q) }) } := by
  have hpending (p : FighterPhase) (hp : p ∈ s.active) (hpl : p.level < l) :
      p.pending.filter (· != q) = p.pending := by
    apply List.filter_eq_self.mpr
    intro r hr
    have hbound := (hranges p hp).2 r hr
    have hupper : levelUpper p.level ≤ levelScale k := tower_le_tower (by omega)
    have hmin : levelScale k + d + 1 ≤ q.2 := hq
    have hne : r ≠ q := by
      intro heq
      rw [heq] at hbound
      omega
    exact bne_iff_ne.mpr hne
  refine ⟨?_, rfl⟩
  intro j hj
  have hact : ({ s with
      fulfilled := s.fulfilled ++ [q]
      active := s.active.map (fun p => { p with pending := p.pending.filter (· != q) }) } :
        FighterState).activeAt d j = s.activeAt d j := by
    simp only [FighterState.activeAt, List.find?_map]
    change (s.active.find? (fun p => p.level == j)).map
      (fun p => { p with pending := p.pending.filter (· != q) }) = _
    cases hs : s.active.find? (fun p => p.level == j) with
    | none => rfl
    | some phase =>
      have hlevel : phase.level = j := beq_iff_eq.mp
        (List.find?_some (p := fun p : FighterPhase => p.level == j) hs)
      have hp := hpending phase (List.mem_of_find?_eq_some hs) (by omega)
      simp only [Option.map_some, hp]
  change (({ s with
    fulfilled := s.fulfilled ++ [q]
    active := s.active.map (fun p => { p with pending := p.pending.filter (· != q) }) } :
      FighterState).activeAt d j, _, _, _) = _
  rw [hact]
  rfl

/-- Servicing a level `k ≥ l` preserves the request ranges and the protected prefix of the
levels below `l`, as an instance of `ServiceInvariant` relative to the initial state. -/
private def lowerFrameInvariant (P : FighterParams) (d l k : ℕ) (hd : 1 ≤ d) (hlk : l ≤ k)
    (state : FighterState) : ServiceInvariant P d k where
  Inv s := FighterRequestRanges d s ∧ LowerFrame d l state s
  PhaseInv phase := phase.RequestRanges d ∧ l ≤ phase.level
  phaseInv_of_activeAt hs hp := ⟨hs.1 _ (List.mem_of_find?_eq_some hp),
    by have := FighterState.level_eq_of_activeAt_eq_some hp; omega⟩
  phaseInv_congr h hgame hpending hlevel := ⟨h.1.congr hgame hpending hlevel, hlevel ▸ h.2⟩
  phaseInv_fundRequests h := ⟨h.1.fundRequests _, h.2⟩
  phaseInv_construction s candidate hadm :=
    ⟨FighterPhase.requestRanges_construction P d k hd hadm candidate s, hlk⟩
  inv_putPhase hs hp := ⟨hs.1.putPhase hp.1, hs.2.trans (.putPhase d l _ _ hp.2)⟩
  inv_cancel hj hs :=
    ⟨hs.1.cancel _ _ _, hs.2.trans (.cancel d l _ (hlk.trans hj) _ _ (fun _ ↦ hlk) _)⟩
  inv_failed hs := hs
  inv_allocated ha hs := ⟨hs.1, hs.2.trans (.allocated d l _ _ (hlk.trans ha.ge))⟩
  inv_started hs := ⟨hs.1, hs.2.trans (.started d l k _ _ hlk)⟩
  inv_record hs hp hlevel hmem :=
    ⟨hs.1.record _, hs.2.trans (.record d l k hlk _ _
      (by simpa only [hlevel] using (hp.1.2 _ hmem).1) hs.1)⟩

/-- Servicing a level `k` at or above the cutoff `l` preserves every local history of the
levels below `l` and introduces no abortion whose cause is below `l`. This is a frame rule
for one finite service, including initialization and its entire enabled-action closure; it
rests on the request ranges, which make the threshold intervals of different levels disjoint,
so that a payoff of a higher level cannot delete a request of a lower one. -/
lemma fighterProcessLevel_lower_history_eq_of_le
    (P : FighterParams) (d l k : ℕ) (hd : 1 ≤ d) (hlk : l ≤ k)
    (event : Option TimedEvent) (state : FighterState)
    (hranges : FighterRequestRanges d state) :
    (∀ j < l,
      fighterLevelHistory (fighterProcessLevel P d k event state) d j =
        fighterLevelHistory state d j) ∧
    (fighterProcessLevel P d k event state).ended.filter
        (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) =
      state.ended.filter (fun e => decide (e.2.2.1 = .aborted ∧ e.2.2.2 < l)) :=
  ((lowerFrameInvariant P d l k hd hlk state).inv_processLevel event
    ⟨hranges, LowerFrame.refl d l state⟩).2

end Kolmogorov.Milovanov
