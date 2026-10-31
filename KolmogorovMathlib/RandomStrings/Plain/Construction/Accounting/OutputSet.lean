/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.CapacityFailure

/-!
# Payoff directives and the description capacity of the fighter family

This module proves two consequences of the guarded allocator of the construction.

* `fighter_description_capacity` (blueprint node `constr:capacity`): for every sufficiently
  large even padding `d`, no allocation ever fails, at any tick.  The proof looks at the first
  failed allocation (`exists_saturated_target_count_of_failed`), whose target range
  and exhausted capacity `2 ^ (r - 1)` are compared with the bounds on the number of requested
  descriptions: dummy and fuel directives are bounded by the phase counts
  (`fighter_phase_count`), and payoff directives by the number of simple strings at the target
  (`length_directivesAtTarget_le`).
* `constructed_machine_output_set_finite` (blueprint node `constr:smallset`): every set of
  strings of bounded description length for the machine of a padding member is finite.

The payoff bound rests on two invariants of the reachable states.  Both are shown by the same
traversal of the transition functions of `Construction/Actions.lean`, which is carried out once
for an abstract property of the permanent tables (`AllocationInvariant`): payoff directives never
repeat an output for the same target, and every payoff directive was issued for a string that is
simple at the corresponding target minus the half padding.
-/

namespace Kolmogorov.Milovanov

/-- A property `I` of fighter states which depends only on the permanent tables `allocated`
and `fulfilled`, holds initially, and is preserved by the allocation of directives other than
payoffs and by every payoff attempt.  Such a property is preserved by every transition of the
construction (`AllocationInvariant.holds`). -/
private structure AllocationInvariant (P : FighterParams) (d : ℕ)
    (I : FighterState → Prop) : Prop where
  /-- The property only depends on `allocated` and `fulfilled`. -/
  of_tables : ∀ {s t : FighterState}, t.allocated = s.allocated → t.fulfilled = s.fulfilled →
    I s → I t
  /-- The property holds in the initial state. -/
  initial : I (initialFighterState d)
  /-- Allocating a dummy or fuel directive preserves the property. -/
  allocate : ∀ (l : ℕ) (kind : DirectiveKind) (target : ℕ) (output : BitString)
    (t : FighterState), kind ≠ .payoff → I t → I (fighterAllocate d l kind target output t).1
  /-- Every payoff attempt preserves the property. -/
  payoff : ∀ (l : ℕ) (q : Coordinate) (t : FighterState), I t → I (fighterPayoff P d l q t)

namespace AllocationInvariant

variable {P : FighterParams} {d : ℕ} {I : FighterState → Prop}

private lemma putPhase (hI : AllocationInvariant P d I) {t : FighterState}
    (phase : FighterPhase) (ht : I t) : I (t.putPhase d phase) :=
  hI.of_tables (s := t) rfl rfl ht

private lemma cancel (hI : AllocationInvariant P d I) (j : ℕ) (reason : PhaseEnd)
    (cause : ℕ) {t : FighterState} (ht : I t) : I (fighterCancel d j reason cause t) :=
  have h := fighterCancel_allocated_fulfilled d j reason cause t
  hI.of_tables h.1 h.2 ht

private lemma abortAbove (hI : AllocationInvariant P d I) (l : ℕ) {t : FighterState}
    (ht : I t) : I (fighterAbortAbove d l t) :=
  have h := fighterAbortAbove_allocated_fulfilled d l t
  hI.of_tables h.1 h.2 ht

private lemma fulfillReady (hI : AllocationInvariant P d I) (l : ℕ) {t : FighterState}
    (ht : I t) : I (fighterFulfillReady P d l t) := by
  unfold fighterFulfillReady
  split
  · exact ht
  · exact foldl_preserves_invariant I _ _ (fun s q hs ↦ hI.payoff l q s hs) ht

private lemma fuelUnit (hI : AllocationInvariant P d I) (l : ℕ) (q : Coordinate)
    {t : FighterState} (ht : I t) : I (fighterFuelUnit P d l q t) := by
  unfold fighterFuelUnit
  split
  · exact ht
  · split_ifs
    · dsimp only
      split
      · exact hI.fulfillReady l (hI.putPhase _ (hI.allocate _ _ _ _ _ (by decide)
          (hI.putPhase _ ht)))
      · exact hI.allocate _ _ _ _ _ (by decide) (hI.putPhase _ ht)
    · exact ht

private lemma fuelUnits (hI : AllocationInvariant P d I) (l : ℕ) (q : Coordinate)
    (count : ℕ) {t : FighterState} (ht : I t) : I (fighterFuelUnits P d l q count t) := by
  induction count generalizing t with
  | zero => exact ht
  | succ count ih => exact ih (hI.fuelUnit l q ht)

private lemma dummy (hI : AllocationInvariant P d I) (l : ℕ) {t : FighterState}
    (ht : I t) : I (fighterDummy d l t) := by
  unfold fighterDummy
  split
  · exact ht
  · split
    · exact ht
    · split_ifs
      · exact ht
      · dsimp only
        split
        · exact hI.putPhase _ (hI.allocate _ _ _ _ _ (by decide) ht)
        · exact hI.allocate _ _ _ _ _ (by decide) ht

private lemma flushBuffer (hI : AllocationInvariant P d I) (l : ℕ) {t next : FighterState}
    (h : fighterFlushBuffer d l t = some next) (ht : I t) : I next := by
  unfold fighterFlushBuffer at h
  cases hphase : t.activeAt d l with
  | none =>
    rw [hphase] at h
    exact absurd h (by simp)
  | some phase =>
    rw [hphase] at h
    dsimp only [Option.bind_some, bind, Option.bind] at h
    split_ifs at h
    cases h
    exact hI.putPhase _ ht

private lemma strategyMove (hI : AllocationInvariant P d I) (l : ℕ) {t next : FighterState}
    (h : fighterStrategyMove P d l t = some next) (ht : I t) : I next := by
  cases hs : t.activeAt d l with
  | none => simp [fighterStrategyMove, hs] at h
  | some p =>
    simp only [fighterStrategyMove, hs, bind, Option.bind_some] at h
    split at h
    · cases hm : (p.game d).strategy (p.official d) with
      | none => simp [hm] at h
      | some move =>
        simp only [hm, Option.bind_some] at h
        split at h
        · let after := (p.game d).coordinates.zipIdx.foldl (fun s (q, i) ↦
            fighterFuelUnits P d l q (move[i]?.getD 0) s) t
          have hafter : I after := by
            refine foldl_preserves_invariant I _ _ ?_ ht
            rintro s ⟨q, i⟩ hs
            exact hI.fuelUnits l q _ hs
          change (match after.activeAt d l with
            | none => some after
            | some live => some (after.putPhase d
                { live with officialCode := ((p.game d).afterMove (p.official d) move).encode })) =
              some next at h
          cases hlive : after.activeAt d l with
          | none =>
            simp only [hlive, Option.some.injEq] at h
            subst next
            exact hafter
          | some live =>
            simp only [hlive, Option.some.injEq] at h
            subst next
            exact hI.putPhase _ hafter
        · contradiction
    · contradiction

private lemma levelAction (hI : AllocationInvariant P d I) (l : ℕ) {t next : FighterState}
    (h : fighterLevelAction P d l t = some next) (ht : I t) : I next := by
  cases hs : t.activeAt d l with
  | none => simp [fighterLevelAction, hs] at h
  | some p =>
    simp only [fighterLevelAction, hs, bind, Option.bind_some] at h
    split at h
    · cases h
      exact hI.dummy l ht
    · cases hq : p.pending.find? (fun q ↦
          decide (q ∉ t.fulfilled) && fighterSafe P d t.tick q) with
      | some q =>
        simp only [hq, Option.some.injEq] at h
        subst next
        exact hI.payoff l q t ht
      | none =>
        simp only [hq] at h
        cases hf : fighterFlushBuffer d l t with
        | some flushed =>
          simp only [hf, Option.some.injEq] at h
          subst next
          exact hI.flushBuffer l hf ht
        | none =>
          simp only [hf] at h
          exact hI.strategyMove l h ht

private lemma closure (hI : AllocationInvariant P d I) (l fuel : ℕ) {t : FighterState}
    (ht : I t) : I (fighterClosure P d l fuel t) := by
  induction fuel generalizing t with
  | zero => exact ht
  | succ fuel ih =>
    unfold fighterClosure
    cases h : fighterLevelAction P d l t with
    | none => exact ht
    | some next => exact ih (hI.levelAction l h ht)

private lemma startPhase (hI : AllocationInvariant P d I) (l : ℕ) (candidate : Candidate)
    {t : FighterState} (ht : I t) : I (fighterStartPhase P d l candidate t) :=
  hI.of_tables (s := fighterAbortAbove d l (fighterCancel d l .replaced l t)) rfl rfl
    (hI.abortAbove l (hI.cancel l .replaced l ht))

private lemma opponent (hI : AllocationInvariant P d I) (l : ℕ) (event : ProgramEvent)
    {t : FighterState} (ht : I t) : I (fighterOpponent P d l event t) := by
  unfold fighterOpponent
  split
  · exact ht
  · split
    · exact ht
    · split
      · exact ht
      · split
        · exact hI.cancel l .opponentExhausted l ht
        · exact hI.fulfillReady l (hI.putPhase _ ht)

private lemma processLevel (hI : AllocationInvariant P d I) (l : ℕ)
    (event : Option TimedEvent) {t : FighterState} (ht : I t) :
    I (fighterProcessLevel P d l event t) := by
  unfold fighterProcessLevel fighterCloseLevel
  apply hI.closure
  cases event with
  | none => exact hI.fulfillReady l ht
  | some e =>
    dsimp only
    split_ifs
    · exact hI.startPhase l _ (hI.fulfillReady l ht)
    · exact hI.opponent l _ (hI.fulfillReady l ht)

private lemma actions (hI : AllocationInvariant P d I) (tick : ℕ) {t : FighterState}
    (ht : I t) : I (fighter_actions P d tick t) := by
  dsimp only [fighter_actions]
  split_ifs
  · exact hI.of_tables (s := initialFighterState d) rfl rfl hI.initial
  · refine foldl_preserves_invariant I (fun s l ↦ fighterProcessLevel P d l (eventAt P.B tick) s) _
      (fun s l hs ↦ hI.processLevel l _ hs) ?_
    exact hI.of_tables (s := t) rfl rfl ht

/-- A property satisfying `AllocationInvariant` holds in every reachable state. -/
private lemma holds (hI : AllocationInvariant P d I) (tick : ℕ) : I (fighterState P d tick) := by
  induction tick with
  | zero => exact hI.initial
  | succ tick ih => exact hI.actions (tick + 1) ih

end AllocationInvariant

/-- A successful payoff attempt allocates a payoff directive for a pair that is not yet in the
`fulfilled` table, and then records the pair there; hence `PayoffLedger` is preserved. -/
private lemma payoffLedger_payoff (P : FighterParams) (d l : ℕ) (q : Coordinate)
    {state : FighterState} (h_inv : PayoffLedger state) :
    PayoffLedger (fighterPayoff P d l q state) := by
  unfold fighterPayoff
  split
  · exact h_inv
  · split_ifs with hguard
    · obtain ⟨hful, hcases⟩ :=
        fighterAllocate_fulfilled_allocated d l .payoff q.2 q.1 state
      rcases hA : fighterAllocate d l .payoff q.2 q.1 state with ⟨next, success⟩
      rw [hA] at hful hcases
      dsimp only at hful hcases ⊢
      rcases hcases with ⟨hs, hal⟩ | ⟨hs, entry, hk, ht, ho, hal⟩
      · subst hs
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold PayoffLedger
        rw [hal, hful]
        exact h_inv
      · subst hs
        obtain ⟨hnd, hmem⟩ := h_inv
        simp only [↓reduceIte]
        unfold PayoffLedger
        dsimp only
        rw [hal, hful]
        refine ⟨?_, ?_⟩
        · rw [List.filter_append, List.map_append]
          have hfe : [entry].filter (fun a ↦ decide (a.kind = .payoff)) = [entry] := by
            simp [hk]
          rw [hfe, List.map_singleton, ho, ht, ← List.concat_eq_append]
          refine List.Nodup.concat ?_ hnd
          intro hin
          obtain ⟨a, ha, hpair⟩ := List.mem_map.1 hin
          obtain ⟨ha_mem, ha_kind⟩ := List.mem_filter.1 ha
          have hq : (a.output, a.target) ∈ state.fulfilled :=
            hmem a ha_mem (of_decide_eq_true ha_kind)
          rw [hpair] at hq
          exact hguard.2.1 hq
        · intro a ha hka
          rcases List.mem_append.1 ha with ha | ha
          · exact List.mem_append_left _ (hmem a ha hka)
          · rw [List.mem_singleton] at ha
            subst ha
            rw [ho, ht]
            exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact h_inv

private lemma allocationInvariant_payoffLedger (P : FighterParams) (d : ℕ) :
    AllocationInvariant P d PayoffLedger where
  of_tables ha hf h := by
    unfold PayoffLedger
    rw [ha, hf]
    exact h
  initial := payoffLedger_initialFighterState d
  allocate l kind target output t hk ht :=
    payoffLedger_fighterAllocate_of_ne_payoff d l target kind output t hk ht
  payoff l q _ ht := payoffLedger_payoff P d l q ht

/-- Every payoff directive of a state was issued for a string which is simple at its target
minus the half padding. -/
private def SimplePayoffOutputs (P : FighterParams) (d : ℕ) (state : FighterState) : Prop :=
  ∀ a ∈ state.allocated, a.kind = .payoff → Simple P.B.V a.output (a.target - halfPadding d)

/-- A payoff attempt only allocates safe pairs, and safety implies simplicity at the target
minus the half padding. -/
private lemma simple_of_safe (P : FighterParams) (d tick : ℕ) (q : Coordinate)
    (hsafe : fighterSafe P d tick q = true) :
    Simple P.B.V q.1 (q.2 - halfPadding d) := by
  unfold fighterSafe at hsafe
  have h := decide_eq_true_iff.mp hsafe
  apply (canonical_enumeration_spec_union P.B (q.2 - halfPadding d) q.1).mpr
  exact ⟨tick, h.2⟩

/-- An allocation preserves `SimplePayoffOutputs` if a newly issued payoff directive has a
simple output. -/
private lemma simplePayoffOutputs_allocate {P : FighterParams} {d : ℕ} (l : ℕ)
    (kind : DirectiveKind) (target : ℕ) (output : BitString) {t : FighterState}
    (hnew : kind = .payoff → Simple P.B.V output (target - halfPadding d))
    (ht : SimplePayoffOutputs P d t) :
    SimplePayoffOutputs P d (fighterAllocate d l kind target output t).1 := by
  obtain ⟨_, hcases⟩ :=
    fighterAllocate_fulfilled_allocated d l kind target output t
  rcases hcases with ⟨_, ha⟩ | ⟨_, entry, hk, hr, ho, ha⟩
  · intro a ham
    rw [ha] at ham
    exact ht a ham
  · intro a ham hkind
    rw [ha] at ham
    rcases List.mem_append.mp ham with hold | hentry
    · exact ht a hold hkind
    · obtain rfl := List.mem_singleton.mp hentry
      rw [ho, hr]
      exact hnew (hk.symm.trans hkind)

private lemma allocationInvariant_simplePayoffOutputs (P : FighterParams) (d : ℕ) :
    AllocationInvariant P d (SimplePayoffOutputs P d) where
  of_tables ha _ h := by
    intro a hmem
    rw [ha] at hmem
    exact h a hmem
  initial := by
    intro a ha
    exact absurd ha List.not_mem_nil
  allocate l kind target output t hk ht :=
    simplePayoffOutputs_allocate l kind target output (fun h ↦ absurd h hk) ht
  payoff l q t ht := by
    unfold fighterPayoff
    split
    · exact ht
    · split
      · rename_i hguard
        have ha := simplePayoffOutputs_allocate (d := d) l .payoff q.2 q.1 (t := t)
          (fun _ ↦ simple_of_safe P d t.tick q hguard.2.2) ht
        cases he : fighterAllocate d l .payoff q.2 q.1 t with
        | mk next success =>
          rw [he] at ha
          cases success <;> exact ha
      · exact ht

/-- The directives of kind `kind` and target `r` issued by level `l` so far. -/
private def directivesAtTarget (state : FighterState) (l : ℕ) (kind : DirectiveKind)
    (r : ℕ) : List AllocatedDirective :=
  state.allocated.filter (fun a ↦ decide (a.level = l ∧ a.kind = kind ∧ a.target = r))

/-- The outputs of the payoff directives of one level at one target are pairwise distinct. -/
private lemma nodup_outputs_directivesAtTarget (P : FighterParams) (d l tick r : ℕ) :
    ((directivesAtTarget (fighterState P d tick) l .payoff r).map
      AllocatedDirective.output).Nodup := by
  obtain ⟨h_nodup, -⟩ := (allocationInvariant_payoffLedger P d).holds tick
  have h_sub : (directivesAtTarget (fighterState P d tick) l .payoff r).Sublist
      ((fighterState P d tick).allocated.filter (fun a ↦ decide (a.kind = .payoff))) := by
    apply List.monotone_filter_right
    intro a ha
    simp only [decide_eq_true_eq] at ha ⊢
    exact ha.2.1
  have h_pairs := h_nodup.sublist (h_sub.map (fun a : AllocatedDirective ↦ (a.output, a.target)))
  have h_eq : (directivesAtTarget (fighterState P d tick) l .payoff r).map
      (fun a : AllocatedDirective ↦ (a.output, a.target)) =
      ((directivesAtTarget (fighterState P d tick) l .payoff r).map
        AllocatedDirective.output).map (fun x ↦ (x, r)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    simp only [directivesAtTarget, List.mem_filter, decide_eq_true_eq] at ha
    simp [ha.2.2.2]
  rw [h_eq] at h_pairs
  exact h_pairs.of_map _

/-- The outputs of the payoff directives at target `r` are simple at `r - d / 2`. -/
private lemma simple_of_mem_directivesAtTarget (P : FighterParams) (d l tick r : ℕ)
    {a : AllocatedDirective} (ha : a ∈ directivesAtTarget (fighterState P d tick) l .payoff r) :
    Simple P.B.V a.output (r - d / 2) := by
  obtain ⟨hmem, hdec⟩ := List.mem_filter.mp ha
  obtain ⟨-, hkind, htarget⟩ := decide_eq_true_iff.mp hdec
  have := (allocationInvariant_simplePayoffOutputs P d).holds tick a hmem hkind
  rwa [htarget] at this

/-- At a payoff target `r`, the safety rule and the global no-repetition table bound the number of
issued payoff directives by `2 ^ (r - d / 2 + 1)`. -/
private lemma length_directivesAtTarget_le (P : FighterParams) (d l tick r : ℕ) :
    (directivesAtTarget (fighterState P d tick) l .payoff r).length ≤ 2 ^ (r - d / 2 + 1) := by
  set L := directivesAtTarget (fighterState P d tick) l .payoff r
  obtain ⟨hfin, hlt⟩ := simple_finite_card_lt P.B.V (r - d / 2)
  have hsub : ((L.map AllocatedDirective.output).toFinset : Set BitString) ⊆
      {x | Simple P.B.V x (r - d / 2)} := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact simple_of_mem_directivesAtTarget P d l tick r ha
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup
    (nodup_outputs_directivesAtTarget P d l tick r), List.length_map] at hcard
  exact hcard.trans hlt.le

/-- The directives of a given kind and target issued by a level are among the directives of that
kind issued by the level. -/
private lemma length_directivesAtTarget_le_directiveCount (P : FighterParams)
    (d l tick r : ℕ) (kind : DirectiveKind) :
    (directivesAtTarget (fighterState P d tick) l kind r).length ≤
      fighterDirectiveCount P d l tick kind := by
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro a ha
  simp only [decide_eq_true_eq] at ha ⊢
  exact ⟨ha.1, ha.2.1⟩

/-- Sufficiently large even padding prevents every allocation failure at every tick.
Blueprint node `constr:capacity`. The threshold is chosen after the fixed parameters
and before padding; no true-marker or successful-realization assumption is present. -/
theorem fighter_description_capacity (P : FighterParams) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, Even d → ∀ tick, (fighterState P d tick).failed = false := by
  use max 6 (Nat.log2 (2 * P.c₁) + 2)
  intro d hd heven tick
  by_contra hfail
  obtain ⟨t, r, l, kind, _, hr, hcap⟩ := exists_saturated_target_count_of_failed P d
    ⟨tick, Bool.eq_true_of_ne_false hfail⟩
  obtain ⟨hdummy_bound, hdummy_count, hfuel_count⟩ := fighter_phase_count P d l t
  have hcap' : 2 ^ (r - 1) ≤ fighterDirectiveCount P d l t kind :=
    hcap.trans (length_directivesAtTarget_le_directiveCount P d l t r kind)
  cases kind with
  | dummy =>
    dsimp [FighterTargetRange] at hr
    subst hr
    have h1 : 2 ^ (levelScale l + d - 1) ≤ 2 ^ (levelScale l + 1) :=
      hcap'.trans (hdummy_count.trans hdummy_bound.le)
    have h2 : levelScale l + d - 1 ≤ levelScale l + 1 :=
      (Nat.pow_le_pow_iff_right (by decide)).mp h1
    omega
  | payoff =>
    have h1 : 2 ^ (r - 1) ≤ 2 ^ (r - d / 2 + 1) :=
      hcap.trans (length_directivesAtTarget_le P d l t r)
    have h2 : r - 1 ≤ r - d / 2 + 1 := (Nat.pow_le_pow_iff_right (by decide)).mp h1
    have h3 : levelScale l + d + 1 ≤ r := hr.1
    have h4 : d / 2 * 2 = d := Nat.div_mul_cancel (Even.two_dvd heven)
    omega
  | fuel =>
    dsimp [FighterTargetRange] at hr
    subst hr
    have h1 : 2 ^ (levelUpper l + d - 1) ≤ 2 * P.c₁ * 2 ^ levelUpper l := hcap'.trans hfuel_count
    have h2 : 2 ^ (levelUpper l + d - 1) = 2 ^ (d - 1) * 2 ^ levelUpper l := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h2] at h1
    have h3 : 2 ^ (d - 1) ≤ 2 * P.c₁ := Nat.le_of_mul_le_mul_right h1 (Nat.pow_pos (by decide))
    have hc₁ : 2 * P.c₁ ≠ 0 := (lt_of_lt_of_le (Nat.pow_pos (by decide)) h3).ne'
    have h4 : d - 1 ≤ Nat.log2 (2 * P.c₁) := (Nat.le_log2 hc₁).mpr h3
    omega

/-- Bounded-description output sets are finite for every member, including guarded failures.
Blueprint node `constr:smallset`. This requires neither capacity nor conditional optimality. -/
theorem constructed_machine_output_set_finite (P : FighterParams) (d n : ℕ) :
    (fighterSmallSet P d n).Finite :=
  (simple_finite_card_lt (fighterU P d) (2 ^ n + d)).1

end Kolmogorov.Milovanov
