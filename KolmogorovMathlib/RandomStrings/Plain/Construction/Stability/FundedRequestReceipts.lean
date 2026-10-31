/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.Padding

/-!
# Funded requests and permanent allocation receipts

This module supplies the request invariants for blueprint node
`true_marker_funded_request_realized`. Every funded coordinate of a live phase is pending or
already fulfilled, and every fulfillment has a permanent allocation with the requested output
and description length. A common transition relation tracks these properties together with
clock preservation and growth of the permanent tables through the fighter actions.

The extension-count and price bounds turn funding at the true marker into eventual safety.
`FundedRequest` combines these bounds with completion of the internal actions to prove eventual
realization; the phase-separation argument also uses the allocation receipts and table growth.
-/

namespace Kolmogorov.Milovanov

/-- A successful allocation records the requested output with exactly the target description
length, including the one-bit directive overhead.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
theorem exists_allocation_of_fighterAllocate_success
    (d l target : ℕ) (kind : DirectiveKind) (output : BitString)
    (s next : FighterState)
    (hsuccess : fighterAllocate d l kind target output s = (next, true)) :
    ∃ a ∈ next.allocated, a.input.length + 1 = target ∧ a.output = output := by
  unfold fighterAllocate at hsuccess
  split at hsuccess
  · simp only [Prod.mk.injEq, Bool.false_eq_true, and_false] at hsuccess
  · rename_i phase hphase
    by_cases ht : target = 0
    · simp only [ht, ite_true, Prod.mk.injEq, Bool.false_eq_true, and_false] at hsuccess
    · simp only [ht, ite_false] at hsuccess
      cases hf : (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p)) with
      | none => simp only [hf, Prod.mk.injEq, Bool.false_eq_true, and_false] at hsuccess
      | some input =>
        simp only [hf, Prod.mk.injEq, and_true] at hsuccess
        rw [← hsuccess, fighterAbortAbove_allocated]
        refine ⟨⟨l, phase.candidate, s.tick, kind, target, input, output⟩,
          List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_, rfl⟩
        have hlen := length_eq_of_mem_fighterInputs d (target - 1) input
          (List.mem_of_find?_eq_some hf)
        dsimp only
        omega


/-- A funded coordinate is either globally fulfilled or still pending at its phase. -/
private def phaseRequestsCovered (d : ℕ) (fulfilled : List Coordinate)
    (p : FighterPhase) : Prop :=
  ∀ q ∈ p.J d, (p.game d).price q ≤ (p.indicesAt d q).card →
    q ∈ fulfilled ∨ q ∈ p.pending

/-- All live phases account for their funded requests. -/
private def fundedRequestsCovered (d : ℕ) (s : FighterState) : Prop :=
  ∀ p ∈ s.active, phaseRequestsCovered d s.fulfilled p

/-- A permanent graph entry realizes the output and exact description length of a request. -/
def AllocationReceipt (s : FighterState) (q : Coordinate) : Prop :=
  ∃ a ∈ s.allocated, a.input.length + 1 = q.2 ∧ a.output = q.1

/-- Internal actions keep the clock, enlarge both permanent tables, justify new fulfillments,
and preserve coverage of funded requests. These properties compose along finite action runs. -/
private structure RequestTransition (d : ℕ) (s t : FighterState) : Prop where
  tick_eq : t.tick = s.tick
  allocated_mono : s.allocated ⊆ t.allocated
  fulfilled_mono : s.fulfilled ⊆ t.fulfilled
  receipts : ∀ q ∈ t.fulfilled, q ∈ s.fulfilled ∨ AllocationReceipt t q
  covered : fundedRequestsCovered d s → fundedRequestsCovered d t

section Transitions

variable {P : FighterParams} {d : ℕ}

private lemma phaseRequestsCovered.mono {f g : List Coordinate} (hfg : f ⊆ g)
    {p : FighterPhase} (hp : phaseRequestsCovered d f p) : phaseRequestsCovered d g p := by
  intro q hq hf
  exact (hp q hq hf).imp (fun h ↦ hfg h) id

private lemma fundedRequestsCovered.of_activeAt {s : FighterState} {l : ℕ}
    {p : FighterPhase} (hs : fundedRequestsCovered d s) (hp : s.activeAt d l = some p) :
    phaseRequestsCovered d s.fulfilled p :=
  hs p (List.mem_of_find?_eq_some hp)

private lemma phaseRequestsCovered.fundRequests (p : FighterPhase) (fulfilled : List Coordinate) :
    phaseRequestsCovered d fulfilled (p.fundRequests d fulfilled) := by
  intro q hq hf
  by_cases hdone : q ∈ fulfilled
  · exact Or.inl hdone
  · right
    have hmem : q ∈ (p.game d).coordinates := by
      simpa only [FighterPhase.fundRequests, FighterPhase.J, FiniteCounterGame.J,
        FiniteCounterGame.coordinates, FighterPhase.game, List.mem_toFinset,
        List.mem_eraseDups] using hq
    change q ∈ ((p.pending ++ (p.game d).coordinates.filter
      (fun q ↦ decide ((p.game d).price q ≤ (p.indicesAt d q).card))).filter
        (fun q ↦ decide (q ∉ fulfilled))).eraseDups
    simp only [List.mem_eraseDups, List.mem_filter, List.mem_append, decide_eq_true_eq]
    exact ⟨Or.inr ⟨hmem, hf⟩, hdone⟩

private lemma AllocationReceipt.mono {s t : FighterState} (h : s.allocated ⊆ t.allocated)
    {q : Coordinate} (hq : AllocationReceipt s q) : AllocationReceipt t q := by
  obtain ⟨a, ha, hlen, hout⟩ := hq
  exact ⟨a, h ha, hlen, hout⟩

private lemma RequestTransition.refl (s : FighterState) : RequestTransition d s s :=
  ⟨rfl, fun _ h ↦ h, fun _ h ↦ h, fun _ h ↦ Or.inl h, id⟩

private lemma RequestTransition.trans {s t u : FighterState}
    (h₁ : RequestTransition d s t) (h₂ : RequestTransition d t u) : RequestTransition d s u := by
  refine ⟨h₂.tick_eq.trans h₁.tick_eq, fun _ h ↦ h₂.allocated_mono (h₁.allocated_mono h),
    fun _ h ↦ h₂.fulfilled_mono (h₁.fulfilled_mono h), ?_, h₂.covered ∘ h₁.covered⟩
  intro q hq
  rcases h₂.receipts q hq with hold | hnew
  · exact (h₁.receipts q hold).imp_right (AllocationReceipt.mono h₂.allocated_mono)
  · exact Or.inr hnew

private lemma RequestTransition.foldl {α : Type} (f : α → FighterState → FighterState)
    (hf : ∀ a s, RequestTransition d s (f a s)) (xs : List α) (s : FighterState) :
    RequestTransition d s (xs.foldl (fun s a ↦ f a s) s) := by
  induction xs generalizing s with
  | nil => exact .refl s
  | cons a xs ih => exact (hf a s).trans (ih _)

private lemma RequestTransition.putPhase (s : FighterState) (p : FighterPhase)
    (hp : fundedRequestsCovered d s → phaseRequestsCovered d s.fulfilled p) :
    RequestTransition d s (s.putPhase d p) := by
  refine ⟨rfl, fun _ h ↦ h, fun _ h ↦ h, fun _ h ↦ Or.inl h, ?_⟩
  intro hs next hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hp hs
  · exact hs next (List.mem_filter.mp hn).1

private lemma RequestTransition.cancel (l cause : ℕ) (reason : PhaseEnd) (s : FighterState) :
    RequestTransition d s (fighterCancel d l reason cause s) := by
  unfold fighterCancel
  split
  · exact .refl s
  · refine ⟨rfl, fun _ h ↦ h, fun _ h ↦ h, fun _ h ↦ Or.inl h, ?_⟩
    intro hs p hp
    exact hs p (List.mem_filter.mp hp).1

private lemma RequestTransition.abort_above (l : ℕ) (s : FighterState) :
    RequestTransition d s (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  apply RequestTransition.foldl
  intro p t
  split
  · exact RequestTransition.cancel _ _ _ _
  · exact .refl t

private lemma RequestTransition.allocate (l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (out : BitString) (s : FighterState) :
    RequestTransition d s (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  split
  · exact .refl s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none =>
      have hc := RequestTransition.cancel (d := d) l l .saturated { s with failed := true }
      exact ⟨hc.tick_eq, hc.allocated_mono, hc.fulfilled_mono, hc.receipts, hc.covered⟩
    | some p =>
      apply RequestTransition.trans _ (RequestTransition.abort_above _ _)
      exact ⟨rfl, fun _ h ↦ List.mem_append_left _ h, fun _ h ↦ h,
        fun _ h ↦ Or.inl h, id⟩

private lemma RequestTransition.payoff (l : ℕ) (q : Coordinate) (s : FighterState) :
    RequestTransition d s (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  split
  · exact .refl s
  · split
    · have ha := RequestTransition.allocate (d := d) l .payoff q.2 q.1 s
      cases he : fighterAllocate d l .payoff q.2 q.1 s with
      | mk next success =>
        simp only [he] at ha ⊢
        cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact ha
        · apply ha.trans
          refine ⟨rfl, fun _ h ↦ h, fun _ h ↦ List.mem_append_left _ h, ?_, ?_⟩
          · intro r hr
            rcases List.mem_append.mp hr with hold | hnew
            · exact Or.inl hold
            · have hrq : r = q := List.mem_singleton.mp hnew
              subst r
              exact Or.inr (exists_allocation_of_fighterAllocate_success
                d l q.2 .payoff q.1 s next he)
          · intro hs p hp z hz hf
            obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
            rcases hs old hold z hz hf with hdone | hpend
            · exact Or.inl (List.mem_append_left _ hdone)
            · by_cases heq : z = q
              · exact Or.inl (by simp [heq])
              · exact Or.inr (List.mem_filter.mpr ⟨hpend, by simpa using heq⟩)
    · exact .refl s

private lemma RequestTransition.fulfill_ready (l : ℕ) (s : FighterState) :
    RequestTransition d s (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  split
  · exact .refl s
  · exact RequestTransition.foldl _ (RequestTransition.payoff l) _ s

private lemma RequestTransition.fuel_unit (l : ℕ) (q : Coordinate) (s : FighterState) :
    RequestTransition d s (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact .refl s
  · rename_i phase hp
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let out := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have hc := RequestTransition.putPhase s charged (fun hs ↦ hs.of_activeAt (p := phase) hp)
      have ha := hc.trans (RequestTransition.allocate l .fuel (levelUpper l + d) out _)
      change RequestTransition d s
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
        · exact ha.trans ((RequestTransition.putPhase next _
            (fun _ ↦ phaseRequestsCovered.fundRequests _ _)).trans
              (RequestTransition.fulfill_ready l _))
    · exact .refl s

private lemma RequestTransition.fuel_units (l : ℕ) (q : Coordinate) (count : ℕ)
    (s : FighterState) : RequestTransition d s (fighterFuelUnits P d l q count s) := by
  induction count generalizing s with
  | zero => exact .refl s
  | succ count ih => exact (RequestTransition.fuel_unit l q s).trans (ih _)

private lemma RequestTransition.dummy (l : ℕ) (s : FighterState) :
    RequestTransition d s (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact .refl s
  · rename_i phase hp
    split
    · exact .refl s
    · rename_i output hout
      split
      · exact .refl s
      · have ha := RequestTransition.allocate (d := d) l .dummy (levelInput d l) output s
        cases he : fighterAllocate d l .dummy (levelInput d l) output s with
        | mk next success =>
          simp only [he] at ha ⊢
          cases success <;> simp only [Bool.false_eq_true, ite_false, ite_true]
          · exact ha
          · refine ⟨ha.tick_eq, ha.allocated_mono, ha.fulfilled_mono, ha.receipts, ?_⟩
            intro hs
            exact (RequestTransition.putPhase next { phase with dummyIssued := true }
              (fun _ ↦ (hs.of_activeAt (p := phase) hp).mono ha.fulfilled_mono)).covered
                (ha.covered hs)

private lemma RequestTransition.opponent (l : ℕ) (e : ProgramEvent) (s : FighterState) :
    RequestTransition d s (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  split
  · exact .refl s
  · rename_i phase hp
    split
    · exact .refl s
    · rename_i q index htuple
      split
      · exact .refl s
      · split
        · exact RequestTransition.cancel _ _ _ _
        · let inserted := phase.insertIndex d q index
          let next := { inserted with
            opponentRemaining := phase.opponentRemaining - 1
            buffer := (phase.game d).addCounters phase.buffer (phase.unitVector d q) }
          exact (RequestTransition.putPhase s (next.fundRequests d s.fulfilled)
            (fun _ ↦ phaseRequestsCovered.fundRequests _ _)).trans
              (RequestTransition.fulfill_ready l _)

private lemma RequestTransition.start_phase (l : ℕ) (c : Candidate) (s : FighterState) :
    RequestTransition d s (fighterStartPhase P d l c s) := by
  unfold fighterStartPhase
  have hw := (RequestTransition.cancel (d := d) l l .replaced s).trans
    (RequestTransition.abort_above l _)
  apply hw.trans
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  have hp := RequestTransition.putPhase waiting (fighter_construction P d l c waiting)
    (fun _ ↦ phaseRequestsCovered.fundRequests _ _)
  exact ⟨hp.tick_eq, hp.allocated_mono, hp.fulfilled_mono, hp.receipts, hp.covered⟩

private lemma RequestTransition.flush_buffer (l : ℕ) (s : FighterState) :
    RequestTransition d s ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hp : s.activeAt d l with
  | none => exact .refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact RequestTransition.putPhase s _ (fun hs ↦ hs.of_activeAt (p := phase) hp)
    · exact .refl s

private lemma RequestTransition.strategy_move (l : ℕ) (s : FighterState) :
    RequestTransition d s ((fighterStrategyMove P d l s).getD s) := by
  unfold fighterStrategyMove
  cases hp : s.activeAt d l with
  | none => exact .refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact .refl s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) s
          have hn : RequestTransition d s next := by
            apply RequestTransition.foldl
            intro qi t
            exact RequestTransition.fuel_units l qi.1 (move[qi.2]?.getD 0) t
          change RequestTransition d s ((match next.activeAt d l with
            | none => some next
            | some live => some (next.putPhase d
              { live with officialCode :=
                  ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          split
          · exact hn
          · rename_i live hlive
            exact hn.trans (RequestTransition.putPhase next _
              (fun hs ↦ hs.of_activeAt (p := live) hlive))
        · exact .refl s
    · exact .refl s

private lemma RequestTransition.level_action (l : ℕ) (s : FighterState) :
    RequestTransition d s ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases hp : s.activeAt d l with
  | none => exact .refl s
  | some phase =>
    simp only [bind, Option.bind_some]
    split
    · exact RequestTransition.dummy l s
    · split
      · exact RequestTransition.payoff l _ s
      · cases hf : fighterFlushBuffer d l s with
        | none => exact RequestTransition.strategy_move l s
        | some next =>
          simpa only [hf, Option.getD_some] using RequestTransition.flush_buffer (d := d) l s

private lemma RequestTransition.closure (l fuel : ℕ) (s : FighterState) :
    RequestTransition d s (fighterClosure P d l fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d l s with
    | none => exact .refl s
    | some next =>
      have hn := RequestTransition.level_action (P := P) (d := d) l s
      simp only [ha, Option.getD_some] at hn
      exact hn.trans (ih next)

private lemma RequestTransition.process_level (l : ℕ) (e : Option TimedEvent)
    (s : FighterState) : RequestTransition d s (fighterProcessLevel P d l e s) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply (RequestTransition.fulfill_ready l s).trans
  cases e with
  | none => exact RequestTransition.closure l _ _
  | some e =>
    dsimp only
    split
    · exact (RequestTransition.start_phase l _ _).trans (RequestTransition.closure l _ _)
    · exact (RequestTransition.opponent l _ _).trans (RequestTransition.closure l _ _)

end Transitions

/-- Resetting the clock and schedule is followed by a finite run of request-preserving actions. -/
private theorem requestTransition_fighter_actions (P : FighterParams) (d tick : ℕ)
    (hd : 1 ≤ d) (state : FighterState) :
    RequestTransition d { state with tick := tick, schedule := masterState P.B tick }
      (fighter_actions P d tick state) := by
  unfold fighter_actions
  simp only [show d ≠ 0 by omega, ↓reduceIte]
  exact RequestTransition.foldl _ (fun l s ↦ RequestTransition.process_level l _ s) _ _

/-- The completed fighter state has the numerical master tick as its clock.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
theorem fighterState_tick
    (P : FighterParams) (d tick : ℕ) (hd : 1 ≤ d) :
    (fighterState P d tick).tick = tick := by
  cases tick with
  | zero => rfl
  | succ tick =>
    exact (requestTransition_fighter_actions P d (tick + 1) hd _).tick_eq

/-- Allocations and globally fulfilled coordinates persist between completed ticks.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
theorem fighterState_tables_mono
    (P : FighterParams) (d before later : ℕ) (hd : 1 ≤ d) (hle : before ≤ later) :
    (fighterState P d before).allocated ⊆ (fighterState P d later).allocated ∧
      (fighterState P d before).fulfilled ⊆ (fighterState P d later).fulfilled := by
  induction later, hle using Nat.le_induction with
  | base => exact ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  | succ later hle ih =>
    have hstep := requestTransition_fighter_actions P d (later + 1) hd (fighterState P d later)
    exact ⟨fun _ h ↦ hstep.allocated_mono (ih.1 h), fun _ h ↦ hstep.fulfilled_mono (ih.2 h)⟩

/-- The rank bound and its slack bound the number of backed indices at a true marker by
the corresponding relaxed extension count.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
lemma indicesAt_card_le_extensionCount
    (P : FighterParams) (cRank d l tick δ : ℕ) (hd : 1 ≤ d)
    (ha : P.Admissible d l) (hrank : FighterRankHypothesis P cRank)
    (hslack : KP P.B.D (bits d) [] + (cRank : ENat) ≤ (δ : ℕ))
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase)
    (x : BitString) (r : ℕ) (hq : (x, r) ∈ phase.J d) :
    (phase.indicesAt d (x, r)).card ≤
      extensionCount P.B (levelScale l) δ
        (triple x (r - d) (lastProgram P.B (levelScale l))) := by
  have hsub : (phase.indicesAt d (x, r) : Set BitString) ⊆
      extensionSet P.B (levelScale l) δ
        (triple x (r - d) (lastProgram P.B (levelScale l))) := by
    intro index hi
    obtain ⟨program, hlen, hprod⟩ :=
      true_marker_indices_backed P d l tick hd phase hphase (x, r) hq index hi
    have hsmall : pairCode (triple x (r - d) (lastProgram P.B (levelScale l))) index ∈
        fighterSmallSet P d (levelScale l) := by
      apply (simple_iff_exists_program _ _ _).mpr
      exact ⟨program, by simpa only [level_upper_eq] using hlen, hprod⟩
    have hbound := hrank d hd l ha _ hsmall
    change plainK P.B.V _ ≤ ((extensionScale (levelScale l) + δ : ℕ) : ENat)
    calc
      plainK P.B.V _ ≤ (2 ^ levelScale l : ℕ) + KP P.B.D (bits d) [] +
          (cRank : ENat) := hbound
      _ = (2 ^ levelScale l : ℕ) +
          (KP P.B.D (bits d) [] + (cRank : ENat)) := by rw [add_assoc]
      _ ≤ (2 ^ levelScale l : ℕ) + (δ : ENat) := add_le_add le_rfl hslack
      _ = ((extensionScale (levelScale l) + δ : ℕ) : ENat) := by
        simp only [extensionScale, Nat.cast_add]
  have hc := Set.ncard_le_ncard hsub (extension_set_finite P.B (levelScale l) δ _)
  simpa only [Set.ncard_coe_finset, extensionCount] using hc

/-- For retained coordinates, the Key Lemma turns a sufficient extension count into the
plain-complexity bound needed for safety, with even padding and square-root slack.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
lemma plainK_le_of_extension_price_le_count
    (P : FighterParams) (cGap d l : ℕ) (hd : 1 ≤ d) (heven : Even d)
    (ha : P.Admissible d l)
    (hprice : ExtensionPriceSpec P.B (extensionPriceAlgorithm P.B P.lam P.n₀) cGap P.n₀)
    (hslack : cGap * (Nat.sqrt d + 1) ≤ d / 2)
    (x : BitString) (r : ℕ)
    (hq : (x, r) ∈ finite_referee_coordinates (constructedLiteralConstant P.literal d)
      (levelInput d l) (P.family.tree d l (levelInput d l)))
    (hcount : compute_extension_price P.B P.lam P.n₀ (levelScale l)
      (markerCandidate P.B (levelScale l)) x (r - d) ≤
      extensionCount P.B (levelScale l) (Nat.sqrt d)
        (triple x (r - d) (lastProgram P.B (levelScale l)))) :
    plainK P.B.V x ≤ (r - d / 2 : ℕ) := by
  have hret : (x, r) ∈ finite_referee_coordinates (d + P.literal.cV)
      (levelInput d l) (P.family.tree d l (levelInput d l)) := hq
  obtain ⟨hstr, hqrange, hrange⟩ := retained_coordinates_within_key_lemma_range
    P.family P.literal.cV P.n₀ d l P.threshold hd ha x r hret
  have hkey : KeyParameters P.B P.n₀ (levelScale l)
      (markerCandidate P.B (levelScale l)) x (r - d) := by
    exact ⟨(le_max_right _ _).trans ha.2.1, ⟨2 * l, rfl⟩, rfl,
      hqrange, hstr.1.trans hstr.2.le⟩
  have hsafe := (hprice _ _ x (r - d) hkey).2 (Nat.sqrt d) hcount
  have hlow : d ≤ r := by
    obtain ⟨k, hk, hnontrivial, hlow, hhigh⟩ :=
      (mem_finite_referee_coordinates _ _ _ x r).mp hq
    dsimp only [levelInput] at hlow
    omega
  have he : d / 2 * 2 = d := Nat.div_mul_cancel heven.two_dvd
  apply hsafe.trans
  exact_mod_cast (show r - d + cGap * (Nat.sqrt d + 1) ≤ r - d / 2 by omega)

/-- A plain-complexity witness appears in the accumulated emitted table at some tick
no earlier than the specified starting tick.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
lemma exists_tick_fighterSafe_of_plainK_le
    (P : FighterParams) (d tick : ℕ) (x : BitString) (r : ℕ)
    (hr : d / 2 ≤ r) (hsafe : plainK P.B.V x ≤ (r - d / 2 : ℕ)) :
    ∃ later ≥ tick, fighterSafe P d later (x, r) = true := by
  obtain ⟨seen, hseen⟩ := (canonical_enumeration_spec_union P.B (r - d / 2) x).mp hsafe
  refine ⟨max seen tick, le_max_right _ _, ?_⟩
  have hm := (canonical_enumeration_spec_mono P.B (r - d / 2)
    (le_max_left seen tick)).1 hseen
  exact decide_eq_true (And.intro hr hm)

/-- A safe pending request in a completed active phase is globally fulfilled: otherwise
it would enable a payoff action, contradicting completion.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
lemma mem_fulfilled_of_pending_safe
    (P : FighterParams) (d tick l : ℕ) (phase : FighterPhase)
    (hphase : (fighterState P d tick).activeAt d l = some phase)
    (q : Coordinate) (hpend : q ∈ phase.pending)
    (hsafe : fighterSafe P d (fighterState P d tick).tick q = true) :
    q ∈ (fighterState P d tick).fulfilled := by
  by_contra hnot
  have hlevel : phase.level = l := by
    exact beq_iff_eq.mp (List.find?_some (p := fun phase : FighterPhase ↦ phase.level == l)
      hphase)
  have hn := fighter_event_actions_complete P d tick phase
    (List.mem_of_find?_eq_some hphase)
  rw [hlevel] at hn
  simp only [fighterLevelAction, hphase, bind, Option.bind_some] at hn
  cases hd : phase.dummy.isSome && !phase.dummyIssued
  · simp only [hd, Bool.false_eq_true, ite_false] at hn
    cases hf : phase.pending.find? (fun q ↦
        decide (q ∉ (fighterState P d tick).fulfilled) &&
          fighterSafe P d (fighterState P d tick).tick q) with
    | none =>
      exact (List.find?_eq_none.mp hf q hpend) (by simp [hnot, hsafe])
    | some found => simp only [hf, reduceCtorEq] at hn
  · simp only [hd, ite_true, reduceCtorEq] at hn

/-- Every funded coordinate of every live phase is pending or globally fulfilled.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
theorem mem_fulfilled_or_pending_of_funded
    (P : FighterParams) (d tick : ℕ) (phase : FighterPhase)
    (hphase : phase ∈ (fighterState P d tick).active)
    (q : Coordinate) (hq : q ∈ phase.J d)
    (hfunded : (phase.game d).price q ≤ (phase.indicesAt d q).card) :
    q ∈ (fighterState P d tick).fulfilled ∨ q ∈ phase.pending := by
  have hall : fundedRequestsCovered d (fighterState P d tick) := by
    clear hphase
    induction tick with
    | zero => simp [fundedRequestsCovered, fighterState, initialFighterState]
    | succ tick ih =>
      change fundedRequestsCovered d (fighter_actions P d (tick + 1) (fighterState P d tick))
      by_cases hd : d = 0
      · simp [fighter_actions, hd, fundedRequestsCovered, initialFighterState]
      · exact (requestTransition_fighter_actions P d (tick + 1) (by omega) _).covered ih
  exact hall phase hphase q hq hfunded

/-- Every global fulfillment has a permanent allocation receipt with the exact requested
description length and output.
Blueprint node `true_marker_funded_request_realized` (supporting lemma). -/
theorem exists_allocation_of_mem_fulfilled
    (P : FighterParams) (d tick : ℕ) (q : Coordinate)
    (hfulfilled : q ∈ (fighterState P d tick).fulfilled) :
    ∃ a ∈ (fighterState P d tick).allocated,
      a.input.length + 1 = q.2 ∧ a.output = q.1 := by
  cases d with
  | zero =>
    cases tick <;> simp [fighterState, fighter_actions, initialFighterState] at hfulfilled
  | succ d =>
    induction tick with
    | zero => simp [fighterState, initialFighterState] at hfulfilled
    | succ tick ih =>
      have hf := requestTransition_fighter_actions
        P (d + 1) (tick + 1) (by omega) (fighterState P (d + 1) tick)
      rcases hf.receipts q hfulfilled with hold | hnew
      · obtain ⟨a, ha, hlen, hout⟩ := ih hold
        exact ⟨a, hf.allocated_mono ha, hlen, hout⟩
      · exact hnew

end Kolmogorov.Milovanov
