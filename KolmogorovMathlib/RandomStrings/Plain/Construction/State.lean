/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame

/-!
# Finite state of the effective fighter family

Padding is an argument of the construction, not part of its fixed parameters.
Records contain primitive finite data. Games and positions use the reversible
stage-3 codes; index lists denote finite sets through `FighterPhase.indicesAt`.
The permanent graph, fulfilled pairs, and phase archive survive cancellation.
-/

namespace Kolmogorov.Milovanov

/-- Fixed data, chosen before padding. The tail certificate is the conclusion of
`exponential_tail_budget`, with the common threshold enlarged when necessary.
Blueprint node `constr:algorithm` (supporting definition). -/
structure FighterParams where
  /-- The fixed optimal interpreters and their numerical simulation codes. -/
  B : Base
  /-- Plain literal data, independent of the padding. -/
  literal : PlainLiteral B
  /-- The effective, infinitely repeated family of finite referees. -/
  family : RefereeFamily
  /-- The fixed price algorithm's exponent loss. -/
  lam : ℕ
  /-- The common price and admissibility threshold. -/
  n₀ : ℕ
  /-- The fixed exponential tail multiplier. -/
  c₁ : ℕ
  /-- The common threshold includes the numerical exceptions. -/
  threshold : 32 ≤ n₀
  /-- The tail multiplier is positive. -/
  tail_positive : 1 ≤ c₁
  /-- The stage-1 exponential tail estimate with these explicit constants. -/
  tail_bound : ∀ n ≥ n₀, rest B n (2 ^ n) ≤ c₁ * 2 ^ (2 ^ n - n)

/-- The three kinds of successful allocation.
Blueprint node `constr:algorithm` (supporting definition). -/
inductive DirectiveKind where
  /-- The single optional target-flipping description of a phase. -/
  | dummy
  /-- A description purchased by one controlled counter unit. -/
  | fuel
  /-- A funded coordinate with an observed safety witness. -/
  | payoff
  deriving DecidableEq, Repr

/-- A reversible finite encoding of directive kinds.
Blueprint node `constr:algorithm` (supporting definition). -/
def DirectiveKind.equivSum : DirectiveKind ≃ Unit ⊕ (Unit ⊕ Unit) where
  toFun k := match k with
    | .dummy => .inl ()
    | .fuel => .inr (.inl ())
    | .payoff => .inr (.inr ())
  invFun k := match k with
    | .inl _ => .dummy
    | .inr (.inl _) => .fuel
    | .inr (.inr _) => .payoff
  left_inv := by intro k; cases k <;> rfl
  right_inv := by rintro (⟨⟩ | (⟨⟩ | ⟨⟩)) <;> rfl

/-- Primitive coding obtained from the displayed finite sum.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : Primcodable DirectiveKind := Primcodable.ofEquiv _ DirectiveKind.equivSum

/-- A permanent graph entry, with its issuing phase and allocation timestamp.
Blueprint node `constr:algorithm` (supporting definition). -/
structure AllocatedDirective where
  /-- The issuing level. -/
  level : ℕ
  /-- The issuing candidate, including its start tick. -/
  candidate : Candidate
  /-- The tick during whose finite closure allocation succeeded. -/
  tick : ℕ
  /-- Dummy, fuel, or payoff. -/
  kind : DirectiveKind
  /-- The requested unconditional description length. -/
  target : ℕ
  /-- The allocated input of `G`, of length `target - 1`. -/
  input : BitString
  /-- The permanent output of that input. -/
  output : BitString
  deriving DecidableEq, Repr

/-- Graph entries are exactly a product of primitive finite data.
Blueprint node `constr:algorithm` (supporting definition). -/
def AllocatedDirective.equivProd : AllocatedDirective ≃
    ℕ × Candidate × ℕ × DirectiveKind × ℕ × BitString × BitString where
  toFun a := (a.level, a.candidate, a.tick, a.kind, a.target, a.input, a.output)
  invFun := fun (l, c, t, k, r, p, x) => ⟨l, c, t, k, r, p, x⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro a; rfl

/-- Primitive coding of permanent graph entries.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : Primcodable AllocatedDirective := Primcodable.ofEquiv _ AllocatedDirective.equivProd

/-- A phase stores both official play and the live backed counters.
Blueprint node `constr:algorithm` (supporting definition). All coordinate-indexed
lists use the deduplicated order of the encoded game's coordinates. -/
structure FighterPhase where
  /-- The level at which this phase was started. -/
  level : ℕ
  /-- Its program and exact emission tick. -/
  candidate : Candidate
  /-- Initial synchronized tables, after the candidate event was emitted. -/
  snapshot : ScheduleState
  /-- All allocations already present before this phase's optional dummy. -/
  initialAllocations : List AllocatedDirective
  /-- Coordinates, prices, initial answers, budget, target, and chosen predicate. -/
  gameCode : CounterGameCode
  /-- Distinct backed indices, represented by duplicate-free finite lists. -/
  indices : List (List BitString)
  /-- The official position of the positional winning strategy. -/
  officialCode : CounterPositionCode
  /-- Counters including unflushed opponent increments. -/
  liveCounters : List ℕ
  /-- Remaining controlled units; attempts, including failed attempts, cost one. -/
  controlledRemaining : ℕ
  /-- Remaining opponent units, charged at insertion rather than at flush. -/
  opponentRemaining : ℕ
  /-- The opponent increment vector since the last official position. -/
  buffer : CounterMove
  /-- Funded, unfulfilled requests; terminal virtual play does not erase them. -/
  pending : List Coordinate
  /-- The fresh dummy chosen when the winning original player sought equality. -/
  dummy : Option BitString
  /-- Whether the chosen dummy was successfully allocated. -/
  dummyIssued : Bool
  /-- The constructor's name after role exchange, always `false` in reachable states. -/
  controlledPlayer : Bool

/-- Exact primitive product code for a phase, including its frozen snapshots.
Blueprint node `constr:algorithm` (supporting definition). -/
abbrev FighterPhaseCode := ℕ × Candidate × ScheduleState × List AllocatedDirective ×
  CounterGameCode × List (List BitString) × CounterPositionCode × List ℕ × ℕ × ℕ ×
  CounterMove × List Coordinate × Option BitString × Bool × Bool

/-- Reversible phase serialization; no strategy function or proof is serialized.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.equivProd : FighterPhase ≃ FighterPhaseCode where
  toFun p := (p.level, p.candidate, p.snapshot, p.initialAllocations, p.gameCode, p.indices,
    p.officialCode, p.liveCounters, p.controlledRemaining, p.opponentRemaining, p.buffer,
    p.pending, p.dummy, p.dummyIssued, p.controlledPlayer)
  invFun := fun (l, c, s, a, g, i, o, v, b, e, f, r, x, h, k) =>
    ⟨l, c, s, a, g, i, o, v, b, e, f, r, x, h, k⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rfl

/-- Primitive coding inherited from the phase's finite product representation.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : Primcodable FighterPhase := Primcodable.ofEquiv _ FighterPhase.equivProd

/-- Equality of phases is decidable through their explicit primitive encoding.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : DecidableEq FighterPhase := Encodable.decidableEqOfEncodable _

/-- Why a phase became waiting; priority abortion is distinguished from replacement.
Blueprint node `constr:algorithm` (supporting definition). -/
inductive PhaseEnd where
  /-- Another candidate started at the same level. -/
  | replaced
  /-- A smaller level started or issued a directive. -/
  | aborted
  /-- A new distinct opponent index exceeded the remaining budget. -/
  | opponentExhausted
  /-- The requested input length was saturated. -/
  | saturated
  deriving DecidableEq, Repr

/-- A reversible encoding of the four cancellation reasons.
Blueprint node `constr:algorithm` (supporting definition). -/
def PhaseEnd.equivProd : PhaseEnd ≃ Bool × Bool where
  toFun r := match r with
    | .replaced => (false, false)
    | .aborted => (false, true)
    | .opponentExhausted => (true, false)
    | .saturated => (true, true)
  invFun r := match r with
    | (false, false) => .replaced
    | (false, true) => .aborted
    | (true, false) => .opponentExhausted
    | (true, true) => .saturated
  left_inv := by intro r; cases r <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- Primitive coding of phase-end reasons.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : Primcodable PhaseEnd := Primcodable.ofEquiv _ PhaseEnd.equivProd

/-- An ended phase, its end tick, reason, and the level responsible for its cancellation.
The archived phase has an empty pending list. Blueprint node `constr:algorithm`
(supporting definition). -/
abbrev EndedPhase := FighterPhase × ℕ × PhaseEnd × ℕ

/-- The finite global state; absence from `active` means waiting.
Blueprint node `constr:algorithm` (supporting definition). The archive and start log
are observational history and never restart a phase. -/
structure FighterState where
  /-- The current numerical master tick. -/
  tick : ℕ
  /-- Current queue, emitted history, and synchronized prefix observations. -/
  schedule : ScheduleState
  /-- The finite permanent graph, in allocation order. -/
  allocated : List AllocatedDirective
  /-- Only successfully fulfilled payoff pairs, shared by all phases. -/
  fulfilled : List Coordinate
  /-- Persistent indication that some allocation encountered saturation. -/
  failed : Bool
  /-- At most one active phase per level in reachable states. -/
  active : List FighterPhase
  /-- Every phase start, including phases subsequently canceled. -/
  started : List (ℕ × Candidate)
  /-- Canceled and aborted phases with their last live and official positions. -/
  ended : List EndedPhase

/-- The exact finite product underlying global-state coding.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterState.equivProd : FighterState ≃ ℕ × ScheduleState × List AllocatedDirective ×
    List Coordinate × Bool × List FighterPhase × List (ℕ × Candidate) × List EndedPhase where
  toFun s := (s.tick, s.schedule, s.allocated, s.fulfilled, s.failed, s.active, s.started, s.ended)
  invFun := fun (t, e, a, f, b, p, h, c) => ⟨t, e, a, f, b, p, h, c⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro s; rfl

/-- Primitive global-state coding, not an axiom asserting encodability.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : Primcodable FighterState := Primcodable.ofEquiv _ FighterState.equivProd

/-- Equality of global states is decidable through their finite encoding.
Blueprint node `constr:algorithm` (supporting definition). -/
instance : DecidableEq FighterState := Encodable.decidableEqOfEncodable _

/-- Half padding for every member, including odd positive padding.
Blueprint node `constr:algorithm` (supporting definition). -/
def halfPadding (d : ℕ) : ℕ := d / 2

/-- Admissibility uses the fixed constants and the separate padding argument.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterParams.Admissible (P : FighterParams) (d l : ℕ) : Prop :=
  admissible_clocked_occurrence P.family P.literal.cV P.n₀ d l

/-- The admissibility test is executable on the supplied family.
Blueprint node `constr:algorithm` (supporting definition). -/
instance (P : FighterParams) (d l : ℕ) : Decidable (P.Admissible d l) :=
  inferInstanceAs (Decidable (admissible_clocked_occurrence _ _ _ _ _))

/-- The owner interval is searched in a finite initial segment; short events have no owner.
Blueprint node `constr:algorithm` (supporting definition). The bound `length + 1`
is sufficient because the tower strictly increases. -/
def fighterOwner (_d length : ℕ) : Option ℕ :=
  if length ≤ 2 then none else
    (List.range (length + 1)).find? (fun l =>
      decide (1 ≤ l ∧ levelLower l < length ∧ length ≤ levelUpper l))

/-- Initial state of each padding member, with all levels waiting.
Blueprint node `constr:algorithm` (supporting definition). -/
def initialFighterState (_d : ℕ) : FighterState :=
  ⟨0, ([], [], []), [], [], false, [], [], []⟩

/-- Look up the active phase at a level; `none` is the waiting status.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterState.activeAt (state : FighterState) (_d l : ℕ) : Option FighterPhase :=
  state.active.find? (fun phase => phase.level == l)

/-- Replace the unique active record of a level without changing permanent tables.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterState.putPhase (state : FighterState) (_d : ℕ) (phase : FighterPhase) : FighterState :=
  { state with active := phase :: state.active.filter (fun p => p.level != phase.level) }


/-- A phase found at level `l` has level `l`. -/
theorem FighterState.level_eq_of_activeAt_eq_some {s : FighterState} {d l : ℕ}
    {p : FighterPhase} (h : s.activeAt d l = some p) : p.level = l :=
  beq_iff_eq.mp (List.find?_some (p := fun p : FighterPhase ↦ p.level == l) h)

/-- Installing a phase makes it the active phase of its level. -/
theorem FighterState.activeAt_putPhase (d l : ℕ) (s : FighterState) (p : FighterPhase)
    (h : p.level = l) : (s.putPhase d p).activeAt d l = some p := by
  simp [FighterState.putPhase, FighterState.activeAt, h]

/-- Removing the phases of level `k` does not change the lookup of another level `j`. -/
theorem FighterState.find?_level_filter_ne (ps : List FighterPhase) (j k : ℕ) (hne : j ≠ k) :
    (ps.filter (fun p ↦ p.level != k)).find? (fun p ↦ p.level == j) =
      ps.find? (fun p ↦ p.level == j) := by
  rw [List.find?_filter]
  apply List.find?_congr
  intro p hp
  by_cases h : p.level = j <;> simp [h, hne]

/-- Installing a phase does not change the active phase of any other level. -/
theorem FighterState.activeAt_putPhase_of_ne (d j : ℕ) (s : FighterState) (p : FighterPhase)
    (hne : j ≠ p.level) : (s.putPhase d p).activeAt d j = s.activeAt d j := by
  simp only [FighterState.putPhase, FighterState.activeAt, List.find?_cons,
    beq_eq_false_iff_ne.mpr (Ne.symm hne)]
  exact FighterState.find?_level_filter_ne _ _ _ hne

/-- The phase's decoded stage-3 game, including its chosen winning predicate and budget.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.game (phase : FighterPhase) (_d : ℕ) : FiniteCounterGame :=
  decodeCounterGame phase.gameCode

/-- The finite retained coordinate set `J`.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.J (phase : FighterPhase) (d : ℕ) : Finset Coordinate := (phase.game d).J

/-- Read an actual finite set of backed extension indices at a retained coordinate.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.indicesAt (phase : FighterPhase) (d : ℕ) (q : Coordinate) : Finset BitString :=
  if q ∈ (phase.game d).coordinates then
    (phase.indices[(phase.game d).coordinates.idxOf q]?.getD []).toFinset
  else ∅

/-- The official position from which the stage-3 positional strategy is queried.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.official (phase : FighterPhase) (d : ℕ) : CounterPosition (phase.game d) :=
  decodeCounterPosition (phase.game d) phase.officialCode

/-- The live position; the remaining opponent budget already charges the buffer.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.live (phase : FighterPhase) (d : ℕ) : CounterPosition (phase.game d) :=
  decodeCounterPosition (phase.game d)
    (phase.liveCounters, phase.controlledRemaining, phase.opponentRemaining)

/-- The normalized virtual coordinate answer, including universal literal answers.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.virtualAnswer (phase : FighterPhase) (P : FighterParams) (d : ℕ) :
    Coordinate → Bool :=
  normalizedAnswer (constructedLiteralConstant P.literal d)
    ((phase.game d).counterAnswer phase.liveCounters)

/-- Current live referee output, evaluated on the preprocessed tree.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.virtualOutput (phase : FighterPhase) (d : ℕ) : ℕ :=
  (phase.game d).referee.eval ((phase.game d).counterAnswer phase.liveCounters)

/-- Whether the chosen controlled predicate holds at the live counters.
Blueprint node `constr:algorithm` (supporting definition). -/
def FighterPhase.predicateHolds (phase : FighterPhase) (d : ℕ) : Bool :=
  (phase.game d).objective phase.controlledPlayer (phase.virtualOutput d)

/-- The finite unconditional table at a threshold, including all earlier allocations.
Blueprint node `constr:algorithm` (supporting definition). The explicit guards avoid
spurious zero-length simulation or directive witnesses below their branch overheads. -/
def fighterStageOutputList (P : FighterParams) (d k tick : ℕ)
    (allocated : List AllocatedDirective) : List BitString :=
  ((if d ≤ k then stageOutputList P.B (k - d) tick else []) ++
    (if 1 ≤ k ∧ 1 ≤ d then
      ((allocated.filter (fun a => decide (a.input.length ≤ k - 1))).map
        AllocatedDirective.output)
    else [])).eraseDups

/-- The set of distinct outputs in the explicit finite unconditional table.
Blueprint node `constr:algorithm` (supporting definition). -/
def fighterStageOutputs (P : FighterParams) (d k tick : ℕ)
    (allocated : List AllocatedDirective) : Finset BitString :=
  (fighterStageOutputList P d k tick allocated).toFinset

/-- A deterministic fresh string, longer than every string in the supplied finite list.
Blueprint node `constr:algorithm` (supporting definition). No unbounded search is needed. -/
def fighterFreshString (_d : ℕ) (forbidden : List BitString) : BitString :=
  List.replicate (forbidden.foldl (fun n x => max n x.length) 0 + 1) false

/-- The deterministic fuel index is absent from the finite forbidden list it is chosen against,
since its length is strictly greater than the length of every string in that list. -/
theorem fighterFreshString_notMem (d : ℕ) (forbidden : List BitString) :
    fighterFreshString d forbidden ∉ forbidden := by
  have hbound (xs : List BitString) (n : ℕ) :
      n ≤ xs.foldl (fun n x ↦ max n x.length) n ∧
      ∀ x ∈ xs, x.length ≤ xs.foldl (fun n x ↦ max n x.length) n := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨hseed, hmem⟩ := ih (max n x.length)
      refine ⟨(Nat.le_max_left _ _).trans hseed, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (Nat.le_max_right _ _).trans hseed
      · exact hmem y hy
  intro hmem
  have hlen := (hbound forbidden 0).2 _ hmem
  simp only [fighterFreshString, List.length_replicate] at hlen
  omega

/-- Initially backed indices use the frozen past-extension table and earlier allocations.
Blueprint node `constr:algorithm` (supporting definition). Only allocated inputs within
the `N + d` description budget contribute, and the curried encoding is checked exactly. -/
def fighterInitialIndices (P : FighterParams) (d l : ℕ) (candidate : Candidate)
    (allocated : List AllocatedDirective) (q : Coordinate) : List BitString :=
  let base := triple q.1 (q.2 - d) candidate.1
  let oldSet := pastExtensionIndices P.B (levelScale l) candidate (levelScale l) base
  let old := ((stageOutputList P.B (levelUpper l) candidate.2).map decodeSecond).filter
    (fun s => decide (s ∈ oldSet))
  let added := allocated.filterMap (fun a =>
    if a.input.length + 1 ≤ levelUpper l + d ∧
        pairCode base (decodeSecond a.output) = a.output then
      some (decodeSecond a.output)
    else none)
  (old ++ added).eraseDups

/-- Add all funded coordinates to the pending list, omitting globally fulfilled pairs.
Blueprint node `constr:algorithm` (supporting definition). This includes zero prices. -/
def FighterPhase.fundRequests (phase : FighterPhase) (d : ℕ)
    (fulfilled : List Coordinate) : FighterPhase :=
  let game := phase.game d
  let funded := game.coordinates.filter (fun q =>
    decide (game.price q ≤ (phase.indicesAt d q).card))
  { phase with pending := ((phase.pending ++ funded).filter
      (fun q => decide (q ∉ fulfilled))).eraseDups }

/-- Initialize the finite game after a candidate's event, before the optional dummy allocation.
Blueprint node `constr:algorithm`. This uses the full initial `U` table, selects the
winning role, and retains the original target `K` even when the chosen objective is equality.
The event/action layer installs the phase, allocates its dummy, and completes its strategy. -/
def fighter_construction (P : FighterParams) (d l : ℕ) (candidate : Candidate)
    (state : FighterState) : FighterPhase :=
  let n := levelScale l
  let m := levelInput d l
  let tree := P.family.tree d l m
  let coords := retainedCoordinateList (constructedLiteralConstant P.literal d) m tree
  let prices := coordinatePriceTable P.B P.lam P.n₀ n d candidate coords
  let indices := coords.map (fighterInitialIndices P d l candidate state.allocated)
  let counters := indices.map (fun xs => xs.toFinset.card)
  let yes := tree.queries.filter (fun q =>
    decide (q.1 ∈ fighterStageOutputs P d q.2 state.tick state.allocated))
  let K := (fighterStageOutputs P d m state.tick state.allocated).card
  let R := P.c₁ * 2 ^ (levelUpper l - n)
  let original := finite_counter_game coords prices counters yes R
    (tree.normalize (constructedLiteralConstant P.literal d)) K
  let game := original.controlWinningPlayer
  let dummy := if original.winner original.initialPosition then
      some (fighterFreshString d (tree.queries.map Prod.fst ++
        fighterStageOutputList P d m state.tick state.allocated))
    else none
  let phase : FighterPhase := ⟨l, candidate, state.schedule, state.allocated, game.encode,
    indices, game.initialPosition.encode, counters, R, R, List.replicate coords.length 0,
    [], dummy, false, false⟩
  phase.fundRequests d state.fulfilled

end Kolmogorov.Milovanov
