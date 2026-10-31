/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting
import KolmogorovMathlib.RandomStrings.Plain.Construction.Actions
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Construction.Stability.PhasePreservation
import KolmogorovMathlib.RandomStrings.Plain.Construction.State
import KolmogorovMathlib.RandomStrings.Plain.ExtensionPrice
import KolmogorovMathlib.RandomStrings.Plain.FiniteGame
import KolmogorovMathlib.RandomStrings.Plain.Markers
import Mathlib.Data.Nat.Sqrt

/-!
# The global padding constant and the vocabulary of the true-marker phase

This module fixes the constants of the diagonal construction in the order the blueprint requires.
`FighterPriceHypotheses`, `FighterRankHypothesis` and `FighterCapacityHypothesis` collect the
price, rank and capacity facts that depend only on the construction, and `FighterFixedConstants`
bundles them (`fighter_fixed_constants_exist`).  `choose_fighter_padding` then picks one even
padding `d` that is above the capacity threshold and satisfies the two arithmetic slack bounds
of `GoodPadding` (blueprint node `constr:dchoice`); `fighter_good_padding_exists` combines this
with the capacity certificate.  `fighter_price_hypotheses_mono` lets the price and tail
thresholds be raised to a common value beforehand.

The second half defines the vocabulary used to talk about the phase started by the true marker of
a late admissible occurrence: `LateAdmissibleOccurrence`, `trueMarkerPhase`, `TrueMarkerPhaseAt`,
`TrueMarkerPhaseSurvives`, `LowerLevelsSettled`, `TrueMarkerNeverEndsFor` and the separation
property `TrueMarkerSeparation` (blueprint nodes `constr:lowerstable`, `constr:opponent`,
`constr:realization`, `constr:separation`).  It also proves two initialization facts about such a
phase, `true_marker_indices_backed` and `true_marker_initial_table_on_tree`, and
`active_phase_game_tables`, which identifies the retained coordinates and prices of every active
phase.  The later modules of the stability argument import these definitions and facts.
-/

namespace Kolmogorov.Milovanov

/-- The common price constants and the specification of the construction's exact algorithm.
Blueprint node `constr:dchoice` (supporting definition). -/
def FighterPriceHypotheses (P : FighterParams) (C cGap : ℕ) : Prop :=
  ExtensionPriceSpec P.B (extensionPriceAlgorithm P.B P.lam P.n₀) cGap P.n₀ ∧
    ExtensionPriceConstants P.B C P.lam P.n₀

/-- A named uniform rank compiler constant, for every positive guarded family member.
Blueprint node `constr:dchoice` (supporting definition). -/
def FighterRankHypothesis (P : FighterParams) (cRank : ℕ) : Prop :=
  ∀ d ≥ 1, ∀ l, P.Admissible d l → ∀ y ∈ fighterSmallSet P d (levelScale l),
    plainK P.B.V y ≤ (2 ^ levelScale l : ℕ) + KP P.B.D (bits d) [] + (cRank : ENat)

/-- A named threshold preventing allocation failure for all larger even paddings.
Blueprint node `constr:dchoice` (supporting definition). -/
def FighterCapacityHypothesis (P : FighterParams) (d₀ : ℕ) : Prop :=
  ∀ d ≥ d₀, Even d → ∀ tick, (fighterState P d tick).failed = false

/-- Certificates for all constants fixed before choosing the successful padding member.
Blueprint node `constr:dchoice` (supporting definition). -/
structure FighterFixedConstants (P : FighterParams) (C cGap cRank d₀ : ℕ) : Prop where
  /-- Soundness, completeness, and the shared structural volume constants. -/
  price : FighterPriceHypotheses P C cGap
  /-- The uniform rank description bound, independent of the future padding. -/
  rank : FighterRankHypothesis P cRank
  /-- The threshold for the guarded allocation capacity bound. -/
  capacity : FighterCapacityHypothesis P d₀

/-- Exactly the five arithmetic requirements on the final padding; square roots are floors.
Blueprint node `constr:dchoice` (supporting definition). Capacity additionally uses its
separate certificate in `FighterFixedConstants`, not an assumption hidden in this predicate. -/
structure GoodPadding (P : FighterParams) (d₀ cRank cGap d : ℕ) : Prop where
  /-- The final padding is even. -/
  even : Even d
  /-- The simulation and directive branches are disjoint. -/
  positive : 1 ≤ d
  /-- The named capacity threshold is met. -/
  capacity_threshold : d₀ ≤ d
  /-- The rank compiler fits in the integer square-root relaxation. -/
  rank_slack : KP P.B.D (bits d) [] + (cRank : ENat) ≤ (Nat.sqrt d : ℕ)
  /-- The price soundness loss fits in half the padding. -/
  price_slack : cGap * (Nat.sqrt d + 1) ≤ d / 2

/-- Enlarging the common threshold preserves the same price algorithm above that threshold.
Blueprint node `constr:dchoice`. This lets the price and tail thresholds be combined before
constructing `FighterParams`, without changing any constants after padding is selected. -/
theorem fighter_price_hypotheses_mono (B : Base) (C lam cGap n₀ n₁ : ℕ) (hn : n₀ ≤ n₁)
    (hconstants : ExtensionPriceConstants B C lam n₀)
    (hspec : ExtensionPriceSpec B (extensionPriceAlgorithm B lam n₀) cGap n₀) :
    ExtensionPriceConstants B C lam n₁ ∧
      ExtensionPriceSpec B (extensionPriceAlgorithm B lam n₁) cGap n₁ := by
  constructor
  · obtain ⟨hC, hlam, hn₀, hvolumes⟩ := hconstants
    refine ⟨hC, hlam, hn₀.trans hn, ?_⟩
    intro n candidate x q hp
    exact hvolumes n candidate x q ⟨hn.trans hp.1, hp.2⟩
  · intro n candidate x q hp
    have hp₀ : KeyParameters B n₀ n candidate x q := ⟨hn.trans hp.1, hp.2⟩
    have heq : extensionPriceAlgorithm B lam n₁ (n, candidate, x, q) =
        extensionPriceAlgorithm B lam n₀ (n, candidate, x, q) := by
      simp only [extensionPriceAlgorithm, compute_extension_price,
        Nat.not_lt.mpr hp.1, Nat.not_lt.mpr hp₀.1]
    rw [heq]
    exact hspec n candidate x q hp₀

/-- Price certificates extend to joint fixed constants using the stage-4 rank and capacity bounds.
Blueprint node `constr:dchoice`. Neither of the newly selected constants depends on padding. -/
theorem fighter_fixed_constants_exist (P : FighterParams) (C cGap : ℕ)
    (hprice : FighterPriceHypotheses P C cGap) :
    ∃ cRank d₀ : ℕ, FighterFixedConstants P C cGap cRank d₀ := by
  obtain ⟨cRank, hrank⟩ := constructed_machine_uniform_rank_code P
  obtain ⟨d₀, hcapacity⟩ := fighter_description_capacity P
  exact ⟨cRank, d₀, hprice, hrank, hcapacity⟩

/-- Binary exponential growth dominates the linear bound used for each block of eight. -/
private lemma eight_mul_add_nine_le_two_pow (k : ℕ) (hk : 8 ≤ k) : 8 * k + 9 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.pow_succ]
    nlinarith

/-- The integer logarithmic cost leaves any fixed slack beyond an explicit square threshold. -/
private lemma exists_two_mul_clog_add_le_sqrt (c : ℕ) :
    ∃ N : ℕ, ∀ d ≥ N, 2 * Nat.clog 2 (d + 2) + c ≤ Nat.sqrt d := by
  refine ⟨(max 64 (2 * c)) ^ 2, ?_⟩
  intro d hd
  have hs : max 64 (2 * c) ≤ Nat.sqrt d := Nat.le_sqrt'.mpr hd
  have hs64 : 64 ≤ Nat.sqrt d := (le_max_left _ _).trans hs
  have hsc : 2 * c ≤ Nat.sqrt d := (le_max_right _ _).trans hs
  have hk : 8 ≤ Nat.sqrt d / 8 := by omega
  have hpow : Nat.sqrt d + 2 ≤ 2 ^ (Nat.sqrt d / 8) := by
    have := eight_mul_add_nine_le_two_pow (Nat.sqrt d / 8) hk
    omega
  have hd_sq : d + 2 ≤ (Nat.sqrt d + 2) ^ 2 := by
    have := Nat.lt_succ_sqrt' d
    nlinarith
  have hd_pow : d + 2 ≤ 2 ^ (2 * (Nat.sqrt d / 8)) := by
    calc
      d + 2 ≤ (Nat.sqrt d + 2) ^ 2 := hd_sq
      _ ≤ (2 ^ (Nat.sqrt d / 8)) ^ 2 := Nat.pow_le_pow_left hpow 2
      _ = 2 ^ (2 * (Nat.sqrt d / 8)) := by rw [← pow_mul, Nat.mul_comm]
  have hlog : Nat.clog 2 (d + 2) ≤ 2 * (Nat.sqrt d / 8) :=
    Nat.clog_le_of_le_pow hd_pow
  omega

/-- The prefix complexity of `bits d` plus a fixed constant is eventually below `√d`. -/
private theorem exists_rank_slack (B : Base) (cRank : ℕ) :
    ∃ N : ℕ, ∀ d ≥ N,
      KP B.D (bits d) [] + (cRank : ENat) ≤ (Nat.sqrt d : ℕ) := by
  obtain ⟨c, hc⟩ := literal_and_tuple_code_interface_integer B
  obtain ⟨N, hN⟩ := exists_two_mul_clog_add_le_sqrt (c + cRank)
  refine ⟨N, ?_⟩
  intro d hd
  have hcode : KP B.D (bits d) [] ≤ (integerLiteralBound c d : ENat) := by
    simpa only [KPPlain_eq_KP] using hc d
  calc
    KP B.D (bits d) [] + (cRank : ENat)
        ≤ (integerLiteralBound c d : ENat) + (cRank : ENat) := add_le_add hcode le_rfl
    _ = ((integerLiteralBound c d + cRank : ℕ) : ENat) := by simp only [Nat.cast_add]
    _ ≤ (Nat.sqrt d : ℕ) := by
      exact_mod_cast (show integerLiteralBound c d + cRank ≤ Nat.sqrt d by
        simpa only [integerLiteralBound, Nat.add_assoc] using hN d hd)

/-- A fixed multiple of `√d + 1` is eventually below `d / 2`. -/
private theorem exists_gap_slack (cGap : ℕ) :
    ∃ N : ℕ, ∀ d ≥ N,
      cGap * (Nat.sqrt d + 1) ≤ d / 2 := by
  use 16 * (cGap + 1)^2
  intro d hd
  have h1 : 4 * (cGap + 1) ≤ Nat.sqrt d := by
    have h_sq : (4 * (cGap + 1)) * (4 * (cGap + 1)) ≤ d := by
      calc
        (4 * (cGap + 1)) * (4 * (cGap + 1)) = 16 * (cGap + 1)^2 := by ring
        _ ≤ d := hd
    exact Nat.le_sqrt.mpr h_sq
  have hs1 : Nat.sqrt d + 1 ≤ 2 * Nat.sqrt d := by
    calc
      Nat.sqrt d + 1 ≤ Nat.sqrt d + Nat.sqrt d := by
        apply Nat.add_le_add_left
        calc
          1 ≤ 4 * (cGap + 1) := by omega
          _ ≤ Nat.sqrt d := h1
      _ = 2 * Nat.sqrt d := by omega
  have h_bound : 2 * (cGap * (Nat.sqrt d + 1)) ≤ d := by
    calc
      2 * (cGap * (Nat.sqrt d + 1)) = cGap * (2 * (Nat.sqrt d + 1)) := by ring
      _ ≤ cGap * (2 * (2 * Nat.sqrt d)) := by
        apply Nat.mul_le_mul_left
        omega
      _ = 4 * cGap * Nat.sqrt d := by ring
      _ ≤ 4 * (cGap + 1) * Nat.sqrt d := by
        apply Nat.mul_le_mul_right
        omega
      _ ≤ Nat.sqrt d * Nat.sqrt d := by
        apply Nat.mul_le_mul_right
        exact h1
      _ = Nat.sqrt d ^ 2 := by ring
      _ ≤ d := Nat.sqrt_le' d
  omega

/-- One even padding meets arbitrary previously fixed rank, gap, and capacity constants.
Blueprint node `constr:dchoice`. Prefix complexity uses binary `bits d` and empty condition. -/
theorem choose_fighter_padding (B : Base) (d₀ cRank cGap : ℕ) :
    ∃ d : ℕ, Even d ∧ 1 ≤ d ∧ d₀ ≤ d ∧
      KP B.D (bits d) [] + (cRank : ENat) ≤ (Nat.sqrt d : ℕ) ∧
      cGap * (Nat.sqrt d + 1) ≤ d / 2 := by
  obtain ⟨N1, hN1⟩ := exists_rank_slack B cRank
  obtain ⟨N2, hN2⟩ := exists_gap_slack cGap
  set M := max 1 (max d₀ (max N1 N2)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMd : d₀ ≤ M := (le_max_left _ _).trans (le_max_right 1 _)
  have hMN1 : N1 ≤ M := by simp [hM]
  have hMN2 : N2 ≤ M := by simp [hM]
  exact ⟨2 * M, even_two_mul M, by omega, by omega, hN1 _ (by omega), hN2 _ (by omega)⟩

/-- The arithmetic choice gives a good member with no allocation failure at any tick.
Blueprint node `constr:dchoice`. This assembles the interface consumed by the counting diagonal. -/
theorem fighter_good_padding_exists (P : FighterParams) (C cGap cRank d₀ : ℕ)
    (hfixed : FighterFixedConstants P C cGap cRank d₀) :
    ∃ d : ℕ, GoodPadding P d₀ cRank cGap d ∧
      ∀ tick, (fighterState P d tick).failed = false := by
  obtain ⟨d, heven, hpos, hthreshold, hrank, hgap⟩ :=
    choose_fighter_padding P.B d₀ cRank cGap
  exact ⟨d, ⟨heven, hpos, hthreshold, hrank, hgap⟩,
    hfixed.capacity d hthreshold heven⟩

/-- A late occurrence is admissible and its true marker lies above the ownership lower bound.
Blueprint node `constr:lowerstable` (supporting definition). No future survival is assumed. -/
def LateAdmissibleOccurrence (P : FighterParams) (d l : ℕ) : Prop :=
  P.Admissible d l ∧ levelLower l < (lastProgram P.B (levelScale l)).length

/-- The marker's own emission event started this level's named phase at that exact tick.
Blueprint node `constr:lowerstable` (supporting definition). -/
def TrueMarkerPhaseStarted (P : FighterParams) (d l : ℕ) : Prop :=
  (l, markerCandidate P.B (levelScale l)) ∈
    (fighterState P d (markerTick P.B (levelScale l))).started

/-- The true-marker phase record at a tick, retaining the archive after a possible cancellation.
Blueprint node `constr:realization` (supporting definition). This is a semantic lookup only. -/
noncomputable def trueMarkerPhase (P : FighterParams) (d l tick : ℕ) : Option FighterPhase :=
  fighterPhaseAt P d l (markerCandidate P.B (levelScale l)) tick

/-- An active record of the phase with precisely this marker, level, and start timestamp.
Blueprint node `constr:realization` (supporting definition). -/
def TrueMarkerPhaseAt (P : FighterParams) (d l tick : ℕ) (phase : FighterPhase) : Prop :=
  markerTick P.B (levelScale l) ≤ tick ∧ phase.level = l ∧
    phase.candidate = markerCandidate P.B (levelScale l) ∧
    (fighterState P d tick).activeAt d l = some phase

/-- Survival through a tick includes every intervening active record and excludes every end log.
Blueprint node `constr:realization` (supporting definition). It does not assume survival
after the specified tick, and cannot be witnessed solely by an archived phase. -/
def TrueMarkerPhaseSurvives (P : FighterParams) (d l tick : ℕ) : Prop :=
  TrueMarkerPhaseStarted P d l ∧ markerTick P.B (levelScale l) ≤ tick ∧
    (∀ t, markerTick P.B (levelScale l) ≤ t → t ≤ tick →
      ∃ phase, TrueMarkerPhaseAt P d l t phase) ∧
    ∀ e ∈ (fighterState P d tick).ended,
      e.1.level = l → e.1.candidate = markerCandidate P.B (levelScale l) → False

/-- The complete observable history of one level, including counters, requests, and cancellations.
Blueprint node `constr:lowerstable` (supporting definition). Successful graph entries persist. -/
def fighterLevelHistory (state : FighterState) (d l : ℕ) :
    Option FighterPhase × List (ℕ × Candidate) × List AllocatedDirective × List EndedPhase :=
  (state.activeAt d l, state.started.filter (fun e => e.1 == l),
    state.allocated.filter (fun a => a.level == l),
    state.ended.filter (fun e => e.1.level == l))

/-- No lower level changes at or after the given tick, compared with the preceding state.
Blueprint node `constr:lowerstable` (supporting definition). Active-record equality fixes
all counters and requests; the logs also exclude a start followed by immediate cancellation. -/
def LowerLevelsSettled (P : FighterParams) (d l tick : ℕ) : Prop :=
  ∀ j < l, ∀ t ≥ tick,
    fighterLevelHistory (fighterState P d t) d j =
      fighterLevelHistory (fighterState P d (tick - 1)) d j

/-- No end record of the true-marker phase has the specified cancellation reason.
Blueprint node `constr:opponent` (supporting definition). All future ticks are quantified. -/
def TrueMarkerNeverEndsFor (P : FighterParams) (d l : ℕ) (reason : PhaseEnd) : Prop :=
  ∀ tick, ∀ e ∈ (fighterState P d tick).ended,
    e.1.level = l → e.1.candidate = markerCandidate P.B (levelScale l) →
      e.2.2.1 ≠ reason

/-- Initial normalized answers from the saved finite table, before this phase's dummy.
Blueprint node `constr:realization` (supporting definition). This exposes the full table on
all coordinates; the game's `initialYes` stores only its restriction to actual tree queries. -/
def FighterPhase.initialAnswer (phase : FighterPhase) (P : FighterParams) (d : ℕ) :
    Coordinate → Bool :=
  normalizedAnswer (constructedLiteralConstant P.literal d) (fun q =>
    decide (q.1 ∈ fighterStageOutputs P d q.2 phase.candidate.2 phase.initialAllocations))

/-- The current finite actual table with the same literal normalization as the referee.
Blueprint node `constr:separation` (supporting definition). -/
def fighterStageAnswer (P : FighterParams) (d tick : ℕ) : Coordinate → Bool :=
  normalizedAnswer (constructedLiteralConstant P.literal d) (fun q =>
    decide (q.1 ∈ fighterStageOutputs P d q.2 tick (fighterState P d tick).allocated))

/-- Outputs justified by a base description or a permanent directive from levels at most `l`.
Blueprint node `constr:separation` (supporting definition). This uses actual allocated inputs,
not prospective requests or a second run of the construction with higher levels removed. -/
def FighterLowerSources (P : FighterParams) (d l k : ℕ) (x : BitString) : Prop :=
  (d ≤ k ∧ Simple P.B.V x (k - d)) ∨
    ∃ tick a, a ∈ (fighterState P d tick).allocated ∧ a.level ≤ l ∧
      a.input.length + 1 ≤ k ∧ a.output = x

/-- Higher-level directives are irrelevant on the whole tree and at the extension-set budget.
Blueprint node `constr:separation` (supporting definition). Both finite normalized answers
and the limiting actual oracle are determined by the base machine and lower-or-equal levels. -/
def FighterHigherLevelsIrrelevant (P : FighterParams) (d l : ℕ) : Prop :=
  (∀ tick, ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
    fighterStageAnswer P d tick q =
      normalizedAnswer (constructedLiteralConstant P.literal d) (fun r =>
        decide (r.1 ∈ fighterStageOutputs P d r.2 tick
          ((fighterState P d tick).allocated.filter (fun a => decide (a.level ≤ l))))) q) ∧
  (∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
    q ∈ fighterOracle P d ↔ FighterLowerSources P d l q.2 q.1) ∧
  fighterSmallSet P d (levelScale l) =
    {x | FighterLowerSources P d l (2 ^ levelScale l + d) x}

/-- Low queried answers are fixed and the final count has exactly the optional dummy increment.
Blueprint node `constr:separation` (supporting definition). No stability away from the tree
is asserted: in particular the dummy's own threshold answer can change. -/
structure TrueMarkerSeparation (P : FighterParams) (d l : ℕ) (phase : FighterPhase) :
    Prop where
  /-- Low queries have their initial normalized answers at every subsequent finite tick. -/
  low_stages : ∀ tick ≥ markerTick P.B (levelScale l),
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries, q.2 ≤ levelInput d l →
      fighterStageAnswer P d tick q = phase.initialAnswer P d q
  /-- The same low queries agree with the actual limiting oracle. -/
  low_limit : ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
    q.2 ≤ levelInput d l →
      coordinateOracleAnswer (fighterOracle P d) q = phase.initialAnswer P d q
  /-- The actual set whose count is the diagonal target is finite. -/
  finite : {x | plainK (fighterU P d) x ≤ (levelInput d l : ℕ)}.Finite
  /-- The game's target is the initial finite count before its dummy. -/
  initial_count : (phase.game d).target =
    (fighterStageOutputs P d (levelInput d l) phase.candidate.2 phase.initialAllocations).card
  /-- Successful dummy allocation increases the final count by precisely one. -/
  final_count : {x | plainK (fighterU P d) x ≤ (levelInput d l : ℕ)}.ncard =
    (phase.game d).target + if phase.dummyIssued then 1 else 0
  /-- Every query and extension-set membership has a witness from the permitted sources. -/
  higher_levels : FighterHigherLevelsIrrelevant P d l

/-- Each index in a live true-marker phase has an actual description of the literal curried tuple.
Blueprint node `constr:realization`. Backing is inherited from the unconditional stage-4
invariant, so this statement does not need the price or rank hypotheses. -/
theorem true_marker_indices_backed (P : FighterParams) (d l tick : ℕ) (hd : 1 ≤ d)
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase) :
    ∀ q ∈ phase.J d, ∀ index ∈ phase.indicesAt d q,
      ∃ program : BitString, program.length ≤ levelUpper l + d ∧
        produces (fighterU P d) program []
          (pairCode (triple q.1 (q.2 - d) (lastProgram P.B (levelScale l))) index) := by
  have hmem : phase ∈ (fighterState P d tick).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  have hback := (fighter_live_invariants P d tick hd phase hmem).2
  intro q hq index hi
  have h := hback q hq index hi
  rw [hphase.2.1, hphase.2.2.1] at h
  exact (simple_iff_exists_program _ _ _).mp h

/-- A freshly constructed phase stores, as its initial yes table, the queries of the referee's
query tree that the saved finite table answers positively at the candidate's tick. -/
private theorem initialYes_fighter_construction
    (P : FighterParams) (d l : ℕ) (c : Candidate)
    (s : FighterState) (ht : c.2 = s.tick) :
    let p := fighter_construction P d l c s
    (p.game d).initialYes =
      (P.family.tree d p.level (levelInput d p.level)).queries.filter
        (fun q => decide (q.1 ∈ fighterStageOutputs P d q.2
          p.candidate.2 p.initialAllocations)) := by
  intro p
  change (fighter_construction P d l c s |>.game d).initialYes = _
  have hp_alloc : p.initialAllocations = s.allocated := by rfl
  have hp_cand : p.candidate = c := by rfl
  have hp_level : p.level = l := by rfl
  rw [hp_alloc, hp_cand, hp_level, ht]
  dsimp [p, fighter_construction, FighterPhase.game]
  dsimp [FighterPhase.fundRequests]
  rw [decode_encode_counter_game]
  dsimp [FiniteCounterGame.controlWinningPlayer]
  split <;> rfl

/-- The stored initial yes table agrees with the saved initial table on the complete tree.
Blueprint node `constr:realization`. Retained coordinates not queried in the tree need not
be explicit members of `initialYes`; `initialAnswer` still reads their full finite snapshot. -/
theorem true_marker_initial_table_on_tree (P : FighterParams) (d l tick : ℕ)
    (phase : FighterPhase) (hphase : TrueMarkerPhaseAt P d l tick phase) :
    ∀ q ∈ (P.family.tree d l (levelInput d l)).queries,
      phase.initialAnswer P d q =
        normalizedAnswer (constructedLiteralConstant P.literal d)
          (fun r => decide (r ∈ (phase.game d).initialYes)) q := by
  have hactive := active_phase_of_construction P d
    (fun l c allocations code =>
      (decodeCounterGame code).initialYes =
        (P.family.tree d l (levelInput d l)).queries.filter
          (fun q => decide (q.1 ∈ fighterStageOutputs P d q.2 c.2 allocations)))
    (fun l c s hc => by
      have h := initialYes_fighter_construction P d l c s hc
      dsimp [FighterPhase.game] at h
      exact h) tick
  have hp_active : phase ∈ (fighterState P d tick).active :=
    List.mem_of_find?_eq_some hphase.2.2.2
  have h1 : (decodeCounterGame phase.gameCode).initialYes =
      (P.family.tree d phase.level (levelInput d phase.level)).queries.filter
        (fun q => decide (q.1 ∈
          fighterStageOutputs P d q.2 phase.candidate.2 phase.initialAllocations)) :=
    hactive phase hp_active
  have h2 : (phase.game d).initialYes = (decodeCounterGame phase.gameCode).initialYes := rfl
  intro q hq
  rw [h2, h1, hphase.2.1]
  simp [FighterPhase.initialAnswer, normalizedAnswer, hq, List.mem_filter]

/-- Every active phase has exactly the retained coordinate set and the candidate price table
assigned at its initialization, independently of subsequent counter and request updates.
Blueprint node `constr:realization` (supporting lemma). -/
theorem active_phase_game_tables
    (P : FighterParams) (d tick : ℕ) (phase : FighterPhase)
    (hphase : phase ∈ (fighterState P d tick).active) :
    phase.J d = finite_referee_coordinates (constructedLiteralConstant P.literal d)
      (levelInput d phase.level) (P.family.tree d phase.level (levelInput d phase.level)) ∧
    ∀ q ∈ phase.J d, (phase.game d).price q =
      compute_extension_price P.B P.lam P.n₀ (levelScale phase.level)
        phase.candidate q.1 (q.2 - d) := by
  let coords (l : ℕ) := retainedCoordinateList (constructedLiteralConstant P.literal d)
    (levelInput d l) (P.family.tree d l (levelInput d l))
  let Q (l : ℕ) (c : Candidate) (_ : List AllocatedDirective) (code : CounterGameCode) :=
    (decodeCounterGame code).coordinateTable = coords l ∧
      (decodeCounterGame code).prices =
        coordinatePriceTable P.B P.lam P.n₀ (levelScale l) d c (coords l)
  have hinit : ∀ l c s, c.2 = s.tick → Q l c (fighter_construction P d l c s).initialAllocations
      (fighter_construction P d l c s).gameCode := by
    intro l c s _
    dsimp only [Q, fighter_construction, FighterPhase.fundRequests]
    rw [decode_encode_counter_game]
    unfold FiniteCounterGame.controlWinningPlayer
    split <;> exact ⟨rfl, rfl⟩
  obtain ⟨htable, hprices⟩ := active_phase_of_construction P d Q hinit tick phase hphase
  refine ⟨?_, ?_⟩
  · change (decodeCounterGame phase.gameCode).coordinateTable.toFinset = _
    rw [htable]
    rfl
  · intro q hq
    have hmem : q ∈ (phase.game d).coordinates := by
      simpa only [FighterPhase.J, FiniteCounterGame.J, FiniteCounterGame.coordinates,
        List.mem_toFinset, List.mem_eraseDups] using hq
    have hmap : (phase.game d).prices = (phase.game d).coordinates.map
        (fun q => compute_extension_price P.B P.lam P.n₀ (levelScale phase.level)
          phase.candidate q.1 (q.2 - d)) := by
      change (decodeCounterGame phase.gameCode).prices = _
      rw [hprices]
      change (coords phase.level).eraseDups.map _ =
        (decodeCounterGame phase.gameCode).coordinates.map _
      rw [FiniteCounterGame.coordinates, htable]
    unfold FiniteCounterGame.price FiniteCounterGame.coordinateValue
    simp only [hmem, ↓reduceIte]
    rw [hmap, List.getElem?_map, List.getElem?_idxOf hmem]
    rfl

end Kolmogorov.Milovanov
