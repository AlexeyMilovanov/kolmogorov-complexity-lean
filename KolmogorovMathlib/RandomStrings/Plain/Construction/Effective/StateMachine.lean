/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions

/-!
# The fighter state machine and its primitive recursive toolbox

This module collects the semantic objects that are read off the event-by-event construction
of the fighter family (blueprint nodes `constr:algorithm`, `constr:actions`,
`constr:effective`, `constr:smallset`) and the primitive recursive lemmas needed to show that
one event transition is computable.

* `fighterState P d` iterates the total event transition `fighter_actions` from the empty state
  along the master clock; `fighterAllocationAt` and `fighterG` read the partial directive
  function `G_d` off the graph of successful allocations, and `fighterU`, `fighterOracle` and
  `fighterSmallSet` are the resulting conditional machine, its cumulative complexity oracle and
  the set of strings of small complexity.
* `fighterPhaseAt`, `fighterPhaseOracle`, `fighterFinalVirtualAnswer` and
  `fighterFinalVirtualOutput` describe the limit behaviour of a single phase, including phases
  that were canceled or aborted and are only kept in the archive.
* `FighterPhase.BufferInvariant` and `FighterPhase.Backed` are the two state invariants which
  the later modules maintain along the closure of an event.
* `fighter_owner_spec` characterises the bounded owner search `fighterOwner` as the unique level
  whose ownership interval contains the length of the incoming program.
* The remaining lemmas show that the projections and constructors of the records
  `FighterState`, `FighterPhase` and `AllocatedDirective`, the level functions, the owner
  search, the admissibility test and the basic list operations (`find?`, `filter`, `eraseDups`,
  `mergeSort`) are primitive recursive or computable.  They are the building blocks that
  `Allocations`, `ConstructionTransitions` and `GameTransitions` combine into the computability
  of the event transition (`fighter_event_transition_computable`).
-/

namespace Kolmogorov.Milovanov

/-- Iterate the total event transition from the empty state along the common master clock.
Blueprint node `constr:effective` (supporting definition). -/
def fighterState (P : FighterParams) (d : ℕ) : ℕ → FighterState
  | 0 => initialFighterState d
  | tick + 1 => fighter_actions P d (tick + 1) (fighterState P d tick)

/-- Look up a successful graph assignment at a finite tick.
Blueprint node `constr:effective` (supporting definition). -/
def fighterAllocationAt (P : FighterParams) (d tick : ℕ) (input : BitString) :
    Option BitString :=
  ((fighterState P d tick).allocated.find? (fun a => a.input == input)).map
    AllocatedDirective.output

/-- The partial directive function `G_d`, searching for the first successful allocation.
Blueprint node `constr:effective` (supporting definition). Padding zero explicitly
denotes the nowhere-defined branch, and no saturation failure assigns any output. -/
def fighterG (P : FighterParams) (d : ℕ) (input : BitString) : Part BitString :=
  if d = 0 then Part.none else
    (Nat.rfind (fun tick => Part.some (fighterAllocationAt P d tick input).isSome)).bind
      (fun tick => Part.ofOption (fighterAllocationAt P d tick input))

/-- The constructed conditional decompressor `U_d`, using exactly the frozen branch split.
Blueprint node `constr:effective` (supporting definition). -/
def fighterU (P : FighterParams) (d : ℕ) : Map :=
  constructed_conditional_machine P.B d (fighterG P d)

/-- The actual cumulative coordinate oracle `{(x,k) | plainK U_d x ≤ k}`.
Blueprint node `constr:effective` (supporting definition). This reuses the stage-3 oracle. -/
def fighterOracle (P : FighterParams) (d : ℕ) : Set Coordinate :=
  actualCoordinateOracle (fighterU P d)

/-- The full semantic output set `S_{n,d}` at description budget `2^n + d`.
Blueprint node `constr:smallset` (supporting definition). -/
def fighterSmallSet (P : FighterParams) (d n : ℕ) : Set BitString :=
  {y | plainK (fighterU P d) y ≤ (2 ^ n + d : ℕ)}

/-- Find a particular phase by level, candidate program, and emission tick, even after it ends.
Blueprint node `constr:algorithm` (supporting definition). Active records take precedence;
the archive provides the last positions of canceled or priority-aborted phases. -/
def fighterPhaseAt (P : FighterParams) (d l : ℕ) (candidate : Candidate) (tick : ℕ) :
    Option FighterPhase :=
  let state := fighterState P d tick
  match state.activeAt d l with
  | some phase =>
    if phase.candidate = candidate then some phase else
      (state.ended.find? (fun e =>
        decide (e.1.level = l ∧ e.1.candidate = candidate))).map Prod.fst
  | none => (state.ended.find? (fun e =>
      decide (e.1.level = l ∧ e.1.candidate = candidate))).map Prod.fst

/-- The eventual virtual positive coordinates of a specified phase.
Blueprint node `constr:algorithm` (supporting definition). For a surviving phase the
monotone live counters give its limiting answer; for a canceled phase the archive freezes it. -/
def fighterPhaseOracle (P : FighterParams) (d l : ℕ) (candidate : Candidate) : Set Coordinate :=
  {q | ∃ tick phase, fighterPhaseAt P d l candidate tick = some phase ∧
    phase.virtualAnswer P d q = true}

/-- Semantic final virtual answers, including universal literal answers.
Blueprint node `constr:algorithm` (supporting definition). This limit is never called by
the event algorithm; stabilization and actual-oracle agreement belong to stage 5. -/
noncomputable def fighterFinalVirtualAnswer (P : FighterParams) (d l : ℕ)
    (candidate : Candidate) : Coordinate → Bool :=
  normalizedAnswer (constructedLiteralConstant P.literal d)
    (coordinateOracleAnswer (fighterPhaseOracle P d l candidate))

/-- The final virtual output of the level's full referee on the specified phase's limit.
Blueprint node `constr:algorithm` (supporting definition). -/
noncomputable def fighterFinalVirtualOutput (P : FighterParams) (d l : ℕ)
    (candidate : Candidate) : ℕ :=
  (P.family.tree d l (levelInput d l)).eval (fighterFinalVirtualAnswer P d l candidate)

/-- The official/live counter equation and the already-charged opponent-buffer equation.
Blueprint node `constr:actions` (supporting definition). This invariant is intended at
completed event boundaries, not during an atomic controlled response that later fails. -/
def FighterPhase.BufferInvariant (phase : FighterPhase) (d : ℕ) : Prop :=
  phase.controlledPlayer = false ∧
  phase.liveCounters = (phase.game d).addCounters (phase.official d).counters phase.buffer ∧
  (phase.official d).leftBudget = phase.controlledRemaining ∧
  (phase.official d).rightBudget = phase.opponentRemaining + phase.buffer.sum

/-- Every stored index has a real description at the phase's upper description budget.
Blueprint node `constr:actions` (supporting definition). No marker truth or capacity
assumption is built into this backing property. -/
def FighterPhase.Backed (phase : FighterPhase) (P : FighterParams) (d : ℕ) : Prop :=
  ∀ q ∈ phase.J d, ∀ index ∈ phase.indicesAt d q,
    Simple (fighterU P d) (pairCode (triple q.1 (q.2 - d) phase.candidate.1) index)
      (levelUpper phase.level + d)

/-! ### The tower and the ownership intervals -/

private lemma levelLower_mono : Monotone levelLower := fun _ _ h ↦ tower_le_tower (by omega)

private lemma levelUpper_eq_levelLower_succ (l : ℕ) : levelUpper l = levelLower (l + 1) := by
  unfold levelLower levelUpper
  congr 1

private lemma levelLower_eq_levelUpper_pred {l : ℕ} (hl : 1 ≤ l) :
    levelLower l = levelUpper (l - 1) := by
  rw [levelUpper_eq_levelLower_succ, Nat.sub_add_cancel hl]

private lemma two_le_levelLower {l : ℕ} (hl : 1 ≤ l) : 2 ≤ levelLower l :=
  calc 2 = levelLower 1 := rfl
    _ ≤ levelLower l := levelLower_mono hl

/-- Two levels whose ownership intervals both contain a given length coincide. -/
private lemma level_unique {length x l : ℕ} (hx : levelLower x < length ∧ length ≤ levelUpper x)
    (hl : levelLower l < length ∧ length ≤ levelUpper l) : x = l := by
  have key : ∀ {a b : ℕ}, a < b → levelUpper a ≤ levelLower b := fun {a b} hab ↦ by
    rw [levelUpper_eq_levelLower_succ]
    exact levelLower_mono hab
  rcases lt_trichotomy x l with h | h | h
  · have := key h
    omega
  · exact h
  · have := key h
    omega

/-- Every length above `2` lies in the ownership interval of some level at most that length. -/
private lemma exists_level_owner (length : ℕ) (h : 2 < length) :
    ∃ l ≤ length, 1 ≤ l ∧ levelLower l < length ∧ length ≤ levelUpper l := by
  have hlen : length ≤ levelUpper length :=
    (strictMono_tower.id_le length).trans (tower_le_tower (by omega))
  have hex : ∃ l, length ≤ levelUpper l := ⟨length, hlen⟩
  have hspec := Nat.find_spec hex
  have hpos : 1 ≤ Nat.find hex := by
    by_contra h0
    have h2 : length ≤ levelUpper 0 := by
      rwa [show Nat.find hex = 0 by omega] at hspec
    have : levelUpper 0 = 2 := rfl
    omega
  refine ⟨Nat.find hex, Nat.find_min' hex hlen, hpos, ?_, hspec⟩
  rw [levelLower_eq_levelUpper_pred hpos]
  exact not_le.1 (Nat.find_min hex (by omega))

/-- The bounded owner search gives precisely the unique positive ownership interval.
Blueprint node `constr:effective`. Short events are ownerless but still enter the tables. -/
theorem fighter_owner_spec (d length : ℕ) :
    (fighterOwner d length = none ↔ length ≤ 2) ∧
    ∀ l, fighterOwner d length = some l ↔
      1 ≤ l ∧ levelLower l < length ∧ length ≤ levelUpper l := by
  by_cases h : length ≤ 2
  · have hnone : fighterOwner d length = none := by simp [fighterOwner, h]
    refine ⟨by simp [hnone, h], fun l ↦ ?_⟩
    rw [hnone, iff_comm]
    simp only [reduceCtorEq, iff_false, not_and]
    intro hl hlow
    have := two_le_levelLower hl
    omega
  · have hfind : fighterOwner d length = (List.range (length + 1)).find? (fun l ↦
        decide (1 ≤ l ∧ levelLower l < length ∧ length ≤ levelUpper l)) := by
      simp [fighterOwner, h]
    obtain ⟨l₀, hl₀, hl₀1, hl₀2, hl₀3⟩ := exists_level_owner length (by omega)
    obtain ⟨x, hx⟩ : ∃ x, fighterOwner d length = some x := by
      rw [hfind, ← Option.isSome_iff_exists, List.find?_isSome]
      exact ⟨l₀, List.mem_range.2 (by omega), by simp [hl₀1, hl₀2, hl₀3]⟩
    have hx' : 1 ≤ x ∧ levelLower x < length ∧ length ≤ levelUpper x := by
      rw [hfind] at hx
      simpa using List.find?_some hx
    refine ⟨by simp [hx, h], fun l ↦ ?_⟩
    rw [hx, Option.some.injEq]
    exact ⟨fun hxl ↦ hxl ▸ hx', fun hl ↦ level_unique hx'.2 hl.2⟩

/-! ### Projections and constructors of the state records -/

/-- The `tick` component of a fighter state is primitive recursive. -/
theorem FighterState.primrec_tick : Primrec FighterState.tick :=
  Primrec.fst.comp (Primrec.of_equiv (e := FighterState.equivProd))

/-- The `schedule` component of a fighter state is primitive recursive. -/
theorem FighterState.primrec_schedule : Primrec FighterState.schedule :=
  Primrec.fst.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterState.equivProd))

/-- The `allocated` graph of a fighter state is primitive recursive in the state. -/
theorem FighterState.primrec_allocated : Primrec FighterState.allocated :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp
    (Primrec.of_equiv (e := FighterState.equivProd))

/-- The `fulfilled` table of a fighter state is primitive recursive in the state. -/
theorem FighterState.primrec_fulfilled : Primrec FighterState.fulfilled :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
    (Primrec.of_equiv (e := FighterState.equivProd))

/-- The `failed` flag-list of a fighter state is primitive recursive in the state. -/
theorem FighterState.primrec_failed : Primrec FighterState.failed :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp (Primrec.of_equiv (e := FighterState.equivProd))

/-- The list of `active` phases of a fighter state is primitive recursive in the state. -/
theorem FighterState.primrec_active : Primrec FighterState.active :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterState.equivProd))

/-- The `started` table of a fighter state is primitive recursive in the state. -/
theorem FighterState.primrec_started : Primrec FighterState.started :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
      (Primrec.of_equiv (e := FighterState.equivProd))

/-- The archive of `ended` phases of a fighter state is primitive recursive in the state. -/
theorem FighterState.primrec_ended : Primrec FighterState.ended :=
  Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
      (Primrec.of_equiv (e := FighterState.equivProd))

/-- Building a fighter state from computable components is computable. -/
theorem FighterState.computable_mk {α : Type*} [Primcodable α]
    {f0 : α → ℕ} (h0 : Computable f0)
    {f1 : α → ScheduleState} (h1 : Computable f1)
    {f2 : α → List AllocatedDirective} (h2 : Computable f2)
    {f3 : α → List Coordinate} (h3 : Computable f3)
    {f4 : α → Bool} (h4 : Computable f4)
    {f5 : α → List FighterPhase} (h5 : Computable f5)
    {f6 : α → List (ℕ × Candidate)} (h6 : Computable f6)
    {f7 : α → List EndedPhase} (h7 : Computable f7) :
    Computable (fun a ↦
      FighterState.mk (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a)) := by
  change Computable
    (fun a ↦ FighterState.equivProd.symm (f0 a, f1 a, f2 a, f3 a, f4 a, f5 a, f6 a, f7 a))
  apply Computable.comp (Primrec.of_equiv_symm (e := FighterState.equivProd)).to_comp
  exact h0.pair <| h1.pair <| h2.pair <| h3.pair <| h4.pair <| h5.pair <| h6.pair h7

/-- Building a fighter state from primitive recursive components is primitive recursive. -/
theorem FighterState.primrec_mk {α : Type*} [Primcodable α]
    {f0 : α → ℕ} (h0 : Primrec f0)
    {f1 : α → ScheduleState} (h1 : Primrec f1)
    {f2 : α → List AllocatedDirective} (h2 : Primrec f2)
    {f3 : α → List Coordinate} (h3 : Primrec f3)
    {f4 : α → Bool} (h4 : Primrec f4)
    {f5 : α → List FighterPhase} (h5 : Primrec f5)
    {f6 : α → List (ℕ × Candidate)} (h6 : Primrec f6)
    {f7 : α → List EndedPhase} (h7 : Primrec f7) :
    Primrec (fun a ↦ FighterState.mk (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a)) := by
  change Primrec
    (fun a ↦ FighterState.equivProd.symm (f0 a, f1 a, f2 a, f3 a, f4 a, f5 a, f6 a, f7 a))
  apply Primrec.comp (Primrec.of_equiv_symm (e := FighterState.equivProd))
  exact h0.pair <| h1.pair <| h2.pair <| h3.pair <| h4.pair <| h5.pair <| h6.pair h7

/-- The `level` of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_level : Primrec FighterPhase.level :=
  Primrec.fst.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `candidate` of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_candidate : Primrec FighterPhase.candidate :=
  Primrec.fst.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The stored `snapshot` of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_snapshot : Primrec FighterPhase.snapshot :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp
    (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `initialAllocations` of a phase record are primitive recursive in the record. -/
theorem FighterPhase.primrec_initialAllocations : Primrec FighterPhase.initialAllocations :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
    (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `gameCode` of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_gameCode : Primrec FighterPhase.gameCode :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `indices` table of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_indices : Primrec FighterPhase.indices :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `officialCode` of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_officialCode : Primrec FighterPhase.officialCode :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
      (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `liveCounters` of a phase record are primitive recursive in the record. -/
theorem FighterPhase.primrec_liveCounters : Primrec FighterPhase.liveCounters :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
      (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `controlledRemaining` budget of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_controlledRemaining :
    Primrec FighterPhase.controlledRemaining :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `opponentRemaining` budget of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_opponentRemaining : Primrec FighterPhase.opponentRemaining :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The opponent `buffer` of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_buffer : Primrec FighterPhase.buffer :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
        (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `pending` payoff requests of a phase record are primitive recursive in the record. -/
theorem FighterPhase.primrec_pending : Primrec FighterPhase.pending :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp
        (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `dummy` output of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_dummy : Primrec FighterPhase.dummy :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
        Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `dummyIssued` flag of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_dummyIssued : Primrec FighterPhase.dummyIssued :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
        Primrec.snd.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- The `controlledPlayer` flag of a phase record is primitive recursive in the record. -/
theorem FighterPhase.primrec_controlledPlayer : Primrec FighterPhase.controlledPlayer :=
  Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
      Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
        Primrec.snd.comp <| Primrec.snd.comp (Primrec.of_equiv (e := FighterPhase.equivProd))

/-- Building a phase record from primitive recursive components is primitive recursive. -/
theorem FighterPhase.primrec_mk {α : Type*} [Primcodable α]
    {f0 : α → ℕ} (h0 : Primrec f0)
    {f1 : α → Candidate} (h1 : Primrec f1)
    {f2 : α → ScheduleState} (h2 : Primrec f2)
    {f3 : α → List AllocatedDirective} (h3 : Primrec f3)
    {f4 : α → CounterGameCode} (h4 : Primrec f4)
    {f5 : α → List (List BitString)} (h5 : Primrec f5)
    {f6 : α → CounterPositionCode} (h6 : Primrec f6)
    {f7 : α → List ℕ} (h7 : Primrec f7)
    {f8 : α → ℕ} (h8 : Primrec f8)
    {f9 : α → ℕ} (h9 : Primrec f9)
    {f10 : α → CounterMove} (h10 : Primrec f10)
    {f11 : α → List Coordinate} (h11 : Primrec f11)
    {f12 : α → Option BitString} (h12 : Primrec f12)
    {f13 : α → Bool} (h13 : Primrec f13)
    {f14 : α → Bool} (h14 : Primrec f14) :
    Primrec (fun a ↦ FighterPhase.mk (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a)
      (f8 a) (f9 a) (f10 a) (f11 a) (f12 a) (f13 a) (f14 a)) := by
  change Primrec (fun a ↦ FighterPhase.equivProd.symm
    (f0 a, f1 a, f2 a, f3 a, f4 a, f5 a, f6 a, f7 a, f8 a, f9 a, f10 a, f11 a, f12 a, f13 a,
      f14 a))
  apply Primrec.comp (Primrec.of_equiv_symm (e := FighterPhase.equivProd))
  exact h0.pair <| h1.pair <| h2.pair <| h3.pair <| h4.pair <| h5.pair <| h6.pair <|
    h7.pair <| h8.pair <| h9.pair <| h10.pair <| h11.pair <| h12.pair <| h13.pair h14

/-- Emptying the pending payoff requests of a phase record is primitive recursive. -/
private theorem FighterPhase.primrec_clearPending :
    Primrec (fun a : FighterPhase ↦ { a with pending := [] }) :=
  (FighterPhase.primrec_mk FighterPhase.primrec_level FighterPhase.primrec_candidate
    FighterPhase.primrec_snapshot FighterPhase.primrec_initialAllocations
    FighterPhase.primrec_gameCode FighterPhase.primrec_indices FighterPhase.primrec_officialCode
    FighterPhase.primrec_liveCounters FighterPhase.primrec_controlledRemaining
    FighterPhase.primrec_opponentRemaining FighterPhase.primrec_buffer (Primrec.const [])
    FighterPhase.primrec_dummy FighterPhase.primrec_dummyIssued
    FighterPhase.primrec_controlledPlayer).of_eq fun _ ↦ rfl

/-- Marking the dummy directive of a phase record as issued is primitive recursive. -/
theorem FighterPhase.primrec_markDummy :
    Primrec (fun a : FighterPhase ↦ { a with dummyIssued := true }) :=
  (FighterPhase.primrec_mk FighterPhase.primrec_level FighterPhase.primrec_candidate
    FighterPhase.primrec_snapshot FighterPhase.primrec_initialAllocations
    FighterPhase.primrec_gameCode FighterPhase.primrec_indices FighterPhase.primrec_officialCode
    FighterPhase.primrec_liveCounters FighterPhase.primrec_controlledRemaining
    FighterPhase.primrec_opponentRemaining FighterPhase.primrec_buffer FighterPhase.primrec_pending
    FighterPhase.primrec_dummy (Primrec.const true)
    FighterPhase.primrec_controlledPlayer).of_eq fun _ ↦ rfl

/-- The `input` of a graph entry is primitive recursive in the entry. -/
theorem AllocatedDirective.primrec_input : Primrec AllocatedDirective.input :=
  Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp <|
    Primrec.snd.comp <| Primrec.snd.comp (Primrec.of_equiv (e := AllocatedDirective.equivProd))

/-- Building a graph entry from primitive recursive components is primitive recursive. -/
theorem AllocatedDirective.primrec_mk {α : Type*} [Primcodable α]
    {f0 : α → ℕ} (h0 : Primrec f0)
    {f1 : α → Candidate} (h1 : Primrec f1)
    {f2 : α → ℕ} (h2 : Primrec f2)
    {f3 : α → DirectiveKind} (h3 : Primrec f3)
    {f4 : α → ℕ} (h4 : Primrec f4)
    {f5 : α → BitString} (h5 : Primrec f5)
    {f6 : α → BitString} (h6 : Primrec f6) :
    Primrec (fun a ↦ AllocatedDirective.mk (f0 a) (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a)) := by
  change Primrec
    (fun a ↦ AllocatedDirective.equivProd.symm (f0 a, f1 a, f2 a, f3 a, f4 a, f5 a, f6 a))
  apply Primrec.comp (Primrec.of_equiv_symm (e := AllocatedDirective.equivProd))
  exact h0.pair <| h1.pair <| h2.pair <| h3.pair <| h4.pair <| h5.pair h6

/-! ### Generic list operations -/

/-- `if`-then-`else` on a decidable computable predicate is computable. -/
theorem computable_ite_decide
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Computable (fun a ↦ decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a ↦ if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp hf hg

/-- `List.filter` with a computable list and a computable predicate is computable. -/
theorem computable_filter
    {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a ↦ (f a).filter (p a)) := by
  have hs : Computable₂ (fun (a : α) (u : β × List β) ↦
      bif p a u.1 then u.1 :: u.2 else u.2) :=
    (Computable.cond (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.list_cons.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.list_foldr hf (Computable.const []) hs).of_eq ?_
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons, List.filter_cons]
    cases p a b <;> simp only [Bool.cond_false, Bool.cond_true, Bool.false_eq_true,
      ↓reduceIte, ih]

/-- Sorting a list of natural numbers is primitive recursive. -/
theorem primrec_mergeSort_le :
    Primrec (fun l : List ℕ ↦ l.mergeSort (· ≤ ·)) := by
  have hi : Primrec₂ (List.orderedInsert (· ≤ ·) : ℕ → List ℕ → List ℕ) := by
    have hs : Primrec₂ (fun (a : ℕ × List ℕ) (u : ℕ × List ℕ × List ℕ) ↦
        if a.1 ≤ u.1 then a.1 :: u.1 :: u.2.1 else u.1 :: u.2.2) := by
      change Primrec (fun a : (ℕ × List ℕ) × (ℕ × List ℕ × List ℕ) ↦
        if a.1.1 ≤ a.2.1 then a.1.1 :: a.2.1 :: a.2.2.1 else a.2.1 :: a.2.2.2)
      apply Primrec.ite
        (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    refine (Primrec.list_rec Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) hs).of_eq ?_
    intro (a, l)
    induction l with
    | nil => rfl
    | cons b l ih => simp only [List.orderedInsert_cons, ih]
  have hs : Primrec₂ (fun (_ : List ℕ) (u : ℕ × List ℕ) ↦
      List.orderedInsert (· ≤ ·) u.1 u.2) := (hi.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hs).of_eq
    (fun l ↦ (List.mergeSort_eq_insertionSort (· ≤ ·) l).symm)

/-- Boolean equality on a `Primcodable` type with lawful `BEq` is primitive recursive. -/
theorem primrec₂_beq {α : Type*} [Primcodable α] [BEq α] [LawfulBEq α] :
    Primrec₂ (fun a b : α ↦ a == b) := by
  classical
  exact (Primrec.eq.decide : Primrec₂ (fun a b : α ↦ decide (a = b))).of_eq
    (fun a b ↦ by apply Bool.eq_iff_iff.mpr; simp)

/-! ### Level functions, ownership and admissibility -/

private theorem primrec_tower : Primrec tower := by
  have h := Primrec.nat_iterate Primrec.id (Primrec.const 1)
    (primrec_two_pow_aux.comp Primrec.snd).to₂
  refine h.of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun x : ℕ ↦ 2 ^ x)^[n + 1] 1 = tower (n + 1)
    change (fun x : ℕ ↦ 2 ^ x)^[n] 1 = tower n at ih
    rw [Function.iterate_succ_apply', ih]; rfl

/-- The marker scale `n_l` of a level is primitive recursive in the level. -/
theorem primrec_levelScale : Primrec levelScale :=
  primrec_tower.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)

/-- The upper endpoint `N_l` of a level's ownership interval is primitive recursive in the
level. -/
theorem primrec_levelUpper : Primrec levelUpper :=
  primrec_tower.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))

private theorem primrec_levelLower : Primrec levelLower :=
  primrec_tower.comp
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1))

/-- The bounded owner search `fighterOwner` is primitive recursive. -/
theorem primrec₂_fighterOwner : Primrec₂ fighterOwner := by
  unfold fighterOwner
  apply Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.const 2)) (Primrec.const none)
  apply list_find?_primrec (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
  change Primrec (fun a : (ℕ × ℕ) × ℕ ↦
    decide (1 ≤ a.2 ∧ levelLower a.2 < a.1.2 ∧ a.1.2 ≤ levelUpper a.2))
  apply PrimrecPred.decide
  exact (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd).and
    ((Primrec.nat_lt.comp (primrec_levelLower.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).and
      (Primrec.nat_le.comp (Primrec.snd.comp Primrec.fst)
        (primrec_levelUpper.comp Primrec.snd)))

/-- Admissibility of a level for the construction parameters is a computable test. -/
theorem computable_decide_admissible (P : FighterParams) :
    Computable (fun a : ℕ × ℕ ↦ decide (P.Admissible a.1 a.2)) := by
  have hs : Computable (fun a : ℕ × ℕ ↦ levelScale a.2) :=
    primrec_levelScale.to_comp.comp Computable.snd
  have hm : Computable (fun a : ℕ × ℕ ↦ levelInput a.1 a.2) :=
    Primrec.nat_add.to_comp.comp hs Computable.fst
  have hr : Computable (fun a : ℕ × ℕ ↦ levelRangeBound a.2) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp hs
      (NatLog.nat_log2_primrec.to_comp.comp hs)
  have hb := P.family.bound_computable.comp (Computable.snd.pair hm)
  have h1 : Computable (fun a : ℕ × ℕ ↦ decide (1 ≤ a.2)) :=
    (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd).decide.to_comp
  have h2 : Computable (fun a : ℕ × ℕ ↦
      decide (max (max 32 (a.1 ^ 2)) P.n₀ ≤ levelScale a.2)) := by
    apply (Primrec.nat_le.decide.to_comp).comp _ hs
    exact Primrec.nat_max.to_comp.comp
      (Primrec.nat_max.to_comp.comp (Computable.const 32)
        ((Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp Computable.fst
          (Computable.const 2))) (Computable.const P.n₀)
  have h3 : Computable (fun a : ℕ × ℕ ↦
      decide (P.family.bound a.2 (levelInput a.1 a.2) + (a.1 + P.literal.cV) <
        levelRangeBound a.2)) :=
    Primrec.nat_lt.decide.to_comp.comp
      (Primrec.nat_add.to_comp.comp hb
        (Primrec.nat_add.to_comp.comp Computable.fst (Computable.const P.literal.cV))) hr
  exact (Primrec.and.to_comp.comp h1 (Primrec.and.to_comp.comp h2 h3)).of_eq
    (fun a ↦ by
      apply Bool.eq_iff_iff.mpr
      simp [FighterParams.Admissible, admissible_clocked_occurrence])

/-! ### Operations on the active phases -/

/-- Looking up the active phase of a level in a state is primitive recursive. -/
theorem primrec_activeAt :
    Primrec (fun a : ℕ × ℕ × FighterState ↦ a.2.2.activeAt a.1 a.2.1) := by
  apply list_find?_primrec
    (FighterState.primrec_active.comp (Primrec.snd.comp Primrec.snd))
  exact (primrec₂_beq.comp
    (FighterPhase.primrec_level.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to₂

/-- Replacing the unique active record of a level, as done by `FighterState.putPhase`, is
computable. -/
theorem computable_putPhase :
    Computable (fun a : ℕ × FighterPhase × FighterState ↦ a.2.2.putPhase a.1 a.2.1) := by
  have hs : Computable (fun a : ℕ × FighterPhase × FighterState ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have hp : Computable (fun a : ℕ × FighterPhase × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hl : Computable (fun a : (ℕ × FighterPhase × FighterState) × FighterPhase ↦
      a.2.level != a.1.2.1.level) :=
    Primrec.not.to_comp.comp (primrec₂_beq.to_comp.comp
      (FighterPhase.primrec_level.to_comp.comp Computable.snd)
      (FighterPhase.primrec_level.to_comp.comp (hp.comp Computable.fst)))
  apply FighterState.computable_mk
  · exact FighterState.primrec_tick.to_comp.comp hs
  · exact FighterState.primrec_schedule.to_comp.comp hs
  · exact FighterState.primrec_allocated.to_comp.comp hs
  · exact FighterState.primrec_fulfilled.to_comp.comp hs
  · exact FighterState.primrec_failed.to_comp.comp hs
  · exact Computable.list_cons.comp hp
      (computable_filter (FighterState.primrec_active.to_comp.comp hs) hl)
  · exact FighterState.primrec_started.to_comp.comp hs
  · exact FighterState.primrec_ended.to_comp.comp hs

/-- Cancelling one active level, `fighterCancel`, filters it from the active records and
archives its final phase with an empty pending list; otherwise the state is unchanged.
This is a primitive finite-record operation and does not initialize or execute a phase.
Blueprint node `constr:effective` (supporting lemma). -/
theorem primrec_fighterCancel :
    Primrec (fun a : ℕ × ℕ × PhaseEnd × ℕ × FighterState ↦
      fighterCancel a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) := by
  have hs : Primrec (fun a : ℕ × ℕ × PhaseEnd × ℕ × FighterState ↦ a.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec (fun a : ℕ × ℕ × PhaseEnd × ℕ × FighterState ↦ a.1) := Primrec.fst
  have hl : Primrec (fun a : ℕ × ℕ × PhaseEnd × ℕ × FighterState ↦ a.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ho := primrec_activeAt.comp (hd.pair (hl.pair hs))
  have hbranch : Primrec (fun a : (ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase ↦
      { a.1.2.2.2.2 with
        active := a.1.2.2.2.2.active.filter (fun p ↦ p.level != a.1.2.1)
        ended := a.1.2.2.2.2.ended ++
          [({ a.2 with pending := [] }, a.1.2.2.2.2.tick, a.1.2.2.1, a.1.2.2.2.1)] }) := by
    have hf : Primrec (fun a : (ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase ↦
        a.1.2.2.2.2) := hs.comp Primrec.fst
    have hl' : Primrec (fun a : (ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase ↦
        a.1.2.1) := hl.comp Primrec.fst
    have hr' : Primrec (fun a : (ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase ↦
        a.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hc' : Primrec (fun a : (ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase ↦
        a.1.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.fst)))
    have hp : Primrec (fun a : (ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase ↦
        { a.2 with pending := [] }) :=
      FighterPhase.primrec_clearPending.comp Primrec.snd
    have hpred : Primrec (fun a : ((ℕ × ℕ × PhaseEnd × ℕ × FighterState) × FighterPhase) ×
        FighterPhase ↦ a.2.level != a.1.1.2.1) :=
      Primrec.not.comp (primrec₂_beq.comp
        (FighterPhase.primrec_level.comp Primrec.snd)
        (hl'.comp Primrec.fst))
    have hactive := Primrec.list_filter
      (FighterState.primrec_active.comp hf) hpred.to₂
    have hended := Primrec.list_concat.comp (FighterState.primrec_ended.comp hf)
      (hp.pair ((FighterState.primrec_tick.comp hf).pair (hr'.pair hc')))
    exact (FighterState.primrec_mk
      (FighterState.primrec_tick.comp hf)
      (FighterState.primrec_schedule.comp hf)
      (FighterState.primrec_allocated.comp hf)
      (FighterState.primrec_fulfilled.comp hf)
      (FighterState.primrec_failed.comp hf) hactive
      (FighterState.primrec_started.comp hf) hended).of_eq (fun a ↦ rfl)
  exact (Primrec.option_casesOn (o := fun a : ℕ × ℕ × PhaseEnd × ℕ × FighterState ↦
      a.2.2.2.2.activeAt a.1 a.2.1) (f := fun a ↦ a.2.2.2.2)
    (g := fun a phase ↦ { a.2.2.2.2 with
      active := a.2.2.2.2.active.filter (fun p ↦ p.level != a.2.1)
      ended := a.2.2.2.2.ended ++
        [({ phase with pending := [] }, a.2.2.2.2.tick, a.2.2.1, a.2.2.2.1)] })
    ho hs hbranch.to₂).of_eq (fun a ↦ by
      unfold fighterCancel
      cases a.2.2.2.2.activeAt a.1 a.2.1 <;> rfl)

/-- The priority abort `fighterAbortAbove` of all levels above a given one is primitive
recursive. -/
theorem primrec_fighterAbortAbove :
    Primrec (fun a : ℕ × ℕ × FighterState ↦ fighterAbortAbove a.1 a.2.1 a.2.2) := by
  have hs : Primrec (fun a : ℕ × ℕ × FighterState ↦ a.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hh : Primrec₂ (fun (a : ℕ × ℕ × FighterState) (u : FighterState × FighterPhase) ↦
      if a.2.1 < u.2.level then fighterCancel a.1 u.2.level .aborted a.2.1 u.1 else u.1) := by
    have hd : Primrec
        (fun a : (ℕ × ℕ × FighterState) × (FighterState × FighterPhase) ↦ a.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hl : Primrec
        (fun a : (ℕ × ℕ × FighterState) × (FighterState × FighterPhase) ↦ a.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hp : Primrec
        (fun a : (ℕ × ℕ × FighterState) × (FighterState × FighterPhase) ↦ a.2.2.level) :=
      FighterPhase.primrec_level.comp (Primrec.snd.comp Primrec.snd)
    have ht : Primrec
        (fun a : (ℕ × ℕ × FighterState) × (FighterState × FighterPhase) ↦ a.2.1) :=
      Primrec.fst.comp Primrec.snd
    exact (Primrec.ite
      (Primrec.nat_lt.comp hl hp)
      (primrec_fighterCancel.comp
        (hd.pair (hp.pair ((Primrec.const PhaseEnd.aborted).pair (hl.pair ht))))) ht).to₂
  exact (Primrec.list_foldl
    (FighterState.primrec_active.comp hs) hs hh).of_eq (fun a ↦ rfl)

end Kolmogorov.Milovanov
