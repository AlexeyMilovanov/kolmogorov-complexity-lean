/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Accounting.FuelHistory

/-!
# Phase count and fuel bounds of the fighter construction

This module proves the blueprint node `constr:phasecount`: at every tick and level `l`, the
fighter state has fewer than `2 ^ (levelScale l + 1)` phases, at most one dummy directive per
phase, and at most `2 * P.c₁ * 2 ^ levelUpper l` fuel directives.  The fuel bound rests on a
per-candidate invariant: the fuel directives already allocated to a candidate, plus the
unspent controlled budget of its active phase, never exceed `P.c₁ * 2 ^ (levelUpper l -
levelScale l)`.  The invariant is carried through every action of a tick (cancelling, aborting,
allocating, paying off, charging a fuel unit, starting a phase) and then summed over the
candidates that ever started a phase.

The module also contains the numerical inequalities of the blueprint node `constr:intervals`
(`fighter_admissible_square`, `fighter_log_padding_bound`, `fighter_dummy_below_range`,
`fighter_range_below_upper`, `fighter_previous_upper_bound`), which show that the directive
target ranges of different levels are disjoint.  Both families of bounds are used by the
accounting modules that import this file (`LevelRanges`, `EarlierTargets`, ...).
-/

namespace Kolmogorov.Milovanov

/-- The number of fuel directives allocated at level `l` to the candidate `c` in `s`. -/
private def fuelCount (l : ℕ) (c : Candidate) (s : FighterState) : ℕ :=
  (s.allocated.filter (fun a =>
    decide (a.level = l ∧ a.kind = .fuel ∧ a.candidate = c))).length

/-- The accounting invariant of level `l`: for every candidate, its allocated fuel directives,
plus the unspent controlled budget of its active phase, fit into the per-phase budget. -/
private def FuelBudgetGood (P : FighterParams) (l : ℕ) (s : FighterState) : Prop :=
  (∀ c, fuelCount l c s ≤ P.c₁ * 2 ^ (levelUpper l - levelScale l)) ∧
  (∀ p ∈ s.active, p.level = l →
    fuelCount l p.candidate s + p.controlledRemaining ≤ P.c₁ * 2 ^ (levelUpper l - levelScale l))

/-- The transition `s → t` keeps all fuel directives and, for every active phase of `t`, an
active phase of `s` with the same level, candidate and controlled budget. -/
private def FuelPassive (s t : FighterState) : Prop :=
  t.allocated.filter (fun a => decide (a.kind = .fuel)) =
    s.allocated.filter (fun a => decide (a.kind = .fuel)) ∧
  ∀ p ∈ t.active, ∃ q ∈ s.active,
    p.level = q.level ∧ p.candidate = q.candidate ∧
      p.controlledRemaining = q.controlledRemaining

/-- Transitions that preserve the fuel list preserve every fuel count. -/
private lemma fuelCount_eq_of_passive {s t : FighterState} (h : FuelPassive s t) (l : ℕ)
    (c : Candidate) : fuelCount l c t = fuelCount l c s := by
  have h' := congrArg (fun xs : List AllocatedDirective =>
    (xs.filter (fun a => decide (a.level = l ∧ a.candidate = c))).length) h.1
  simpa only [fuelCount, List.filter_filter, ← Bool.decide_and,
    and_assoc, and_left_comm, and_comm] using h'

/-- The accounting invariant is transported along passive transitions. -/
private lemma fuelBudgetGood_of_passive (P : FighterParams) (l : ℕ) {s t : FighterState}
    (hs : FuelBudgetGood P l s) (h : FuelPassive s t) : FuelBudgetGood P l t := by
  refine ⟨fun c ↦ ?_, ?_⟩
  · rw [fuelCount_eq_of_passive h]
    exact hs.1 c
  · intro p hp hl
    obtain ⟨q, hq, hlevel, hc, hb⟩ := h.2 p hp
    rw [fuelCount_eq_of_passive h, hc, hb]
    exact hs.2 q hq (hlevel.symm.trans hl)

private lemma FuelPassive.refl (s : FighterState) : FuelPassive s s :=
  ⟨rfl, fun p hp ↦ ⟨p, hp, rfl, rfl, rfl⟩⟩

private lemma FuelPassive.trans {s t u : FighterState} (hst : FuelPassive s t)
    (htu : FuelPassive t u) : FuelPassive s u := by
  refine ⟨htu.1.trans hst.1, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hl, hc, hb⟩ := htu.2 p hp
  obtain ⟨r, hr, hl', hc', hb'⟩ := hst.2 q hq
  exact ⟨r, hr, hl.trans hl', hc.trans hc', hb.trans hb'⟩

/-- Cancelling a phase only removes active phases and keeps all fuel directives. -/
private lemma fuelPassive_cancel (d j : ℕ) (reason : PhaseEnd) (cause : ℕ) (s : FighterState) :
    FuelPassive s (fighterCancel d j reason cause s) := by
  unfold fighterCancel
  split
  · exact .refl s
  · exact ⟨rfl, fun p hp ↦ ⟨p, List.mem_of_mem_filter hp, rfl, rfl, rfl⟩⟩

/-- Aborting all phases above level `j` is a fold of passive cancellations. -/
private lemma fuelPassive_abortAbove (d j : ℕ) (s : FighterState) :
    FuelPassive s (fighterAbortAbove d j s) := by
  have hfold (ps : List FighterPhase) (s : FighterState) :
      FuelPassive s (ps.foldl (fun s p ↦
        if j < p.level then fighterCancel d p.level .aborted j s else s) s) := by
    induction ps generalizing s with
    | nil => exact .refl s
    | cons p ps ih =>
      refine FuelPassive.trans (t := if j < p.level then
        fighterCancel d p.level .aborted j s else s) ?_ (ih _)
      split
      · exact fuelPassive_cancel _ _ _ _ _
      · exact .refl s
  exact hfold _ _

/-- Installing a phase whose own budget is within the bound preserves the invariant. -/
private lemma fuelBudgetGood_putPhase (P : FighterParams) (d l : ℕ) (s : FighterState)
    (p : FighterPhase) (hs : FuelBudgetGood P l s)
    (hp : p.level = l →
      fuelCount l p.candidate s + p.controlledRemaining ≤
        P.c₁ * 2 ^ (levelUpper l - levelScale l)) :
    FuelBudgetGood P l (s.putPhase d p) := by
  refine ⟨hs.1, fun q hq hl ↦ ?_⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp hl
  · exact hs.2 q (List.mem_of_mem_filter hq) hl

/-- Replacing the active phase by one with the same level, candidate and controlled budget
is passive, even when restoring the record of an earlier active phase. -/
private lemma fuelPassive_putPhase_restore {s t : FighterState} (d : ℕ) (h : FuelPassive s t)
    (p q : FighterPhase) (hq : q ∈ s.active) (hl : p.level = q.level)
    (hc : p.candidate = q.candidate) (hb : p.controlledRemaining = q.controlledRemaining) :
    FuelPassive s (t.putPhase d p) := by
  refine ⟨h.1, fun r hr ↦ ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨q, hq, hl, hc, hb⟩
  · exact h.2 r (List.mem_of_mem_filter hr)

/-- Allocations of a kind other than fuel add no fuel directive and can only cancel phases. -/
private lemma fuelPassive_allocate_of_ne_fuel (d j : ℕ) (kind : DirectiveKind) (target : ℕ)
    (output : BitString) (s : FighterState) (hk : kind ≠ .fuel) :
    FuelPassive s (fighterAllocate d j kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact .refl s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact fuelPassive_cancel d j .saturated j { s with failed := true }
    | some input =>
      refine FuelPassive.trans (t := { s with allocated := s.allocated ++ [_] })
        ?_ (fuelPassive_abortAbove d j _)
      refine ⟨?_, fun p hp ↦ ⟨p, hp, rfl, rfl, rfl⟩⟩
      simp [List.filter_append, hk]

/-- Fulfilling a payoff request changes no fuel directive and no controlled budget. -/
private lemma fuelPassive_payoff (P : FighterParams) (d j : ℕ) (q : Coordinate)
    (s : FighterState) : FuelPassive s (fighterPayoff P d j q s) := by
  unfold fighterPayoff
  split
  · exact .refl s
  · split
    · have ha := fuelPassive_allocate_of_ne_fuel d j .payoff q.2 q.1 s (by decide)
      cases he : fighterAllocate d j .payoff q.2 q.1 s with
      | mk next success =>
        rw [he] at ha
        cases success
        · exact ha
        · refine ⟨ha.1, fun p hp ↦ ?_⟩
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
          exact ha.2 old hold
    · exact .refl s

/-- Checking the pending payoff requests is a fold of passive payoff actions. -/
private lemma fuelPassive_fulfillReady (P : FighterParams) (d j : ℕ) (s : FighterState) :
    FuelPassive s (fighterFulfillReady P d j s) := by
  have hfold (qs : List Coordinate) (s : FighterState) :
      FuelPassive s (qs.foldl (fun s q ↦ fighterPayoff P d j q s) s) := by
    induction qs generalizing s with
    | nil => exact .refl s
    | cons q qs ih => exact (fuelPassive_payoff P d j q s).trans (ih _)
  unfold fighterFulfillReady
  split
  · exact .refl s
  · exact hfold _ _

/-- Appending one successful fuel directive is paid for by first decrementing the positive
controlled budget of the issuing phase. -/
private lemma fuelBudgetGood_charge_append (P : FighterParams) (d l j : ℕ) (s : FighterState)
    (phase : FighterPhase) (input output : BitString) (hs : FuelBudgetGood P l s)
    (hphase : s.activeAt d j = some phase) (hpos : 0 < phase.controlledRemaining) :
    let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
    FuelBudgetGood P l { s.putPhase d charged with allocated := s.allocated ++
      [AllocatedDirective.mk j phase.candidate s.tick .fuel (levelUpper j + d) input output] } := by
  intro charged
  have hmem : phase ∈ s.active := List.mem_of_find?_eq_some hphase
  have hlevel : phase.level = j := beq_iff_eq.mp
    (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hphase)
  let next := { s.putPhase d charged with allocated := s.allocated ++
    [AllocatedDirective.mk j phase.candidate s.tick .fuel (levelUpper j + d) input output] }
  have hc (c : Candidate) : fuelCount l c next =
      fuelCount l c s + if j = l ∧ phase.candidate = c then 1 else 0 := by
    simp only [fuelCount, next, List.filter_append, List.length_append]
    simp [List.filter_cons]
    split_ifs <;> rfl
  refine ⟨fun c ↦ ?_, fun p hp hl ↦ ?_⟩
  · rw [hc]
    split
    · rename_i h
      have hb := hs.2 phase hmem (hlevel.trans h.1)
      rw [h.2] at hb
      omega
    · simpa using hs.1 c
  · rcases List.mem_cons.mp hp with hp | hp
    · subst p
      rw [hc]
      have hjl : j = l := hlevel.symm.trans hl
      simp only [hjl, and_self, ite_true, charged]
      have hb := hs.2 phase hmem hl
      omega
    · obtain ⟨hp, hne⟩ := List.mem_filter.mp hp
      have hjl : j ≠ l := by
        intro hjl
        have he : p.level = charged.level := hl.trans (hjl.symm.trans hlevel.symm)
        simp [he] at hne
      rw [hc]
      simp only [hjl, false_and, ite_false, Nat.add_zero]
      exact hs.2 p hp hl

/-- The guarded fuel allocator of a charged phase either keeps the invariant unchanged on the
phase or appends its one paid-for fuel directive; the charged phase stays within budget. -/
private lemma fuelBudgetGood_allocate_charged (P : FighterParams) (d l j : ℕ) (s : FighterState)
    (phase : FighterPhase) (output : BitString) (hs : FuelBudgetGood P l s)
    (hphase : s.activeAt d j = some phase) (hpos : 0 < phase.controlledRemaining) :
    let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
    let next := (fighterAllocate d j .fuel (levelUpper j + d) output
      (s.putPhase d charged)).1
    FuelBudgetGood P l next ∧
      (j = l → fuelCount l phase.candidate next + charged.controlledRemaining ≤
        P.c₁ * 2 ^ (levelUpper l - levelScale l)) := by
  intro charged next
  have hmem : phase ∈ s.active := List.mem_of_find?_eq_some hphase
  have hlevel : phase.level = j := beq_iff_eq.mp
    (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hphase)
  have hb (hjl : j = l) : fuelCount l phase.candidate s + charged.controlledRemaining ≤
      P.c₁ * 2 ^ (levelUpper l - levelScale l) := by
    have h := hs.2 phase hmem (hlevel.trans hjl)
    dsimp only [charged]
    omega
  have hcharged : FuelBudgetGood P l (s.putPhase d charged) :=
    fuelBudgetGood_putPhase P d l s charged hs fun hl ↦ hb (hlevel.symm.trans hl)
  have hlookup : (s.putPhase d charged).activeAt d j = some charged := by
    simp [FighterState.putPhase, FighterState.activeAt, charged, hlevel]
  dsimp only [next, fighterAllocate]
  rw [hlookup]
  dsimp only
  cases hf : (if levelUpper j + d = 0 then (none : Option BitString) else
      (fighterInputs d (levelUpper j + d - 1)).find? (fun p ↦
        !(s.putPhase d charged).allocated.any (fun a ↦ a.input == p))) with
  | none =>
    have he := fuelPassive_cancel d j .saturated j { s.putPhase d charged with failed := true }
    refine ⟨fuelBudgetGood_of_passive P l hcharged he, fun hjl ↦ ?_⟩
    rw [fuelCount_eq_of_passive he]
    exact hb hjl
  | some input =>
    let appended := { s.putPhase d charged with allocated := s.allocated ++
      [AllocatedDirective.mk j phase.candidate s.tick .fuel (levelUpper j + d) input output] }
    have happend : FuelBudgetGood P l appended :=
      fuelBudgetGood_charge_append P d l j s phase input output hs hphase hpos
    have he := fuelPassive_abortAbove d j appended
    refine ⟨fuelBudgetGood_of_passive P l happend he, fun hjl ↦ ?_⟩
    change fuelCount l phase.candidate (fighterAbortAbove d j appended) +
      charged.controlledRemaining ≤ _
    rw [fuelCount_eq_of_passive he]
    exact happend.2 charged List.mem_cons_self (hlevel.trans hjl)

/-- One fuel attempt of a controlled phase preserves the accounting invariant: it spends a
positive unit of budget, and the subsequent insertion and payoff checks add no fuel. -/
private lemma fuelBudgetGood_fuelUnit (P : FighterParams) (d l j : ℕ) (q : Coordinate)
    (s : FighterState) (hs : FuelBudgetGood P l s) :
    FuelBudgetGood P l (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact hs
  · rename_i phase hphase
    split
    · rename_i hguard
      let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := fuelBudgetGood_allocate_charged P d l j s phase output hs hphase hguard.2
      dsimp only at ha
      change FuelBudgetGood P l
        (match fighterAllocate d j .fuel (levelUpper j + d) output (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d j
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) output
          (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        cases success
        · exact ha.1
        · refine fuelBudgetGood_of_passive P l (t := fighterFulfillReady P d j _) ?_
            (fuelPassive_fulfillReady P d j _)
          refine fuelBudgetGood_putPhase P d l next _ ha.1 fun hl ↦ ?_
          have hlevel : phase.level = j := beq_iff_eq.mp
            (List.find?_some (p := fun p : FighterPhase ↦ p.level == j) hphase)
          exact ha.2 (hlevel.symm.trans hl)
    · exact hs

/-- Finitely many fuel attempts preserve the accounting invariant. -/
private lemma fuelBudgetGood_fuelUnits (P : FighterParams) (d l j : ℕ) (q : Coordinate)
    (count : ℕ) (s : FighterState) (hs : FuelBudgetGood P l s) :
    FuelBudgetGood P l (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact hs
  | succ count ih => exact ih _ (fuelBudgetGood_fuelUnit P d l j q s hs)

/-- An opponent insertion keeps the fuel directives and controlled budgets, or cancels. -/
private lemma fuelPassive_opponent (P : FighterParams) (d j : ℕ) (event : ProgramEvent)
    (s : FighterState) : FuelPassive s (fighterOpponent P d j event s) := by
  unfold fighterOpponent
  split
  · exact .refl s
  · rename_i phase hphase
    split
    · exact .refl s
    · split
      · exact .refl s
      · split
        · exact fuelPassive_cancel _ _ _ _ _
        · refine FuelPassive.trans ?_ (fuelPassive_fulfillReady P d j _)
          exact fuelPassive_putPhase_restore d (.refl s) _ phase
            (List.mem_of_find?_eq_some hphase) rfl rfl rfl

/-- Issuing a dummy directive, and marking it issued, is passive for the fuel accounting. -/
private lemma fuelPassive_dummy (d j : ℕ) (s : FighterState) :
    FuelPassive s (fighterDummy d j s) := by
  unfold fighterDummy
  split
  · exact .refl s
  · rename_i phase hphase
    split
    · exact .refl s
    · rename_i output hout
      split
      · exact .refl s
      · have ha := fuelPassive_allocate_of_ne_fuel d j .dummy (levelInput d j) output s
          (by decide)
        cases he : fighterAllocate d j .dummy (levelInput d j) output s with
        | mk next success =>
          rw [he] at ha
          cases success
          · exact ha
          · exact fuelPassive_putPhase_restore d ha _ phase
              (List.mem_of_find?_eq_some hphase) rfl rfl rfl

/-- Flushing a buffer changes the official play but preserves fuel directives and controlled
budgets. -/
private lemma fuelPassive_flushBuffer (d j : ℕ) (s : FighterState) :
    FuelPassive s ((fighterFlushBuffer d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterFlushBuffer, hphase] using FuelPassive.refl s
  | some phase =>
    simp only [fighterFlushBuffer, hphase, bind, Option.bind_some]
    split
    · exact fuelPassive_putPhase_restore d (.refl s) _ phase
        (List.mem_of_find?_eq_some hphase) rfl rfl rfl
    · exact .refl s

/-- A controlled strategy response, a fold of fuel attempts followed by an update of the
official position, preserves the accounting invariant. -/
private lemma fuelBudgetGood_strategyMove (P : FighterParams) (d l j : ℕ) (s : FighterState)
    (hs : FuelBudgetGood P l s) : FuelBudgetGood P l ((fighterStrategyMove P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterStrategyMove, hphase] using hs
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact hs
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) s) s
          have hn : FuelBudgetGood P l next := by
            apply FighterState.invariant_foldl
              (FuelBudgetGood P l) _ _ _ s hs
            intro t qi ht
            exact fuelBudgetGood_fuelUnits P d l j qi.1 _ t ht
          change FuelBudgetGood P l ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d
                { live with officialCode := ((phase.game d).afterMove
                  (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d j with
          | none => exact hn
          | some live =>
            exact fuelBudgetGood_putPhase P d l next _ hn fun hl ↦
              hn.2 live (List.mem_of_find?_eq_some hlive) hl
        · exact hs
    · exact hs

/-- Every enabled level action is passive or an accounted controlled response. -/
private lemma fuelBudgetGood_levelAction (P : FighterParams) (d l j : ℕ) (s : FighterState)
    (hs : FuelBudgetGood P l s) : FuelBudgetGood P l ((fighterLevelAction P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterLevelAction, hphase] using hs
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact fuelBudgetGood_of_passive P l hs (fuelPassive_dummy d j s)
    · split
      · exact fuelBudgetGood_of_passive P l hs (fuelPassive_payoff P d j _ s)
      · cases hf : fighterFlushBuffer d j s with
        | none => exact fuelBudgetGood_strategyMove P d l j s hs
        | some next =>
          have h := fuelBudgetGood_of_passive P l hs (fuelPassive_flushBuffer d j s)
          simpa only [hf, Option.getD_some] using h

/-- The structural closure of a level preserves the accounting invariant. -/
private lemma fuelBudgetGood_closure (P : FighterParams) (d l j fuel : ℕ) (s : FighterState)
    (hs : FuelBudgetGood P l s) : FuelBudgetGood P l (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact hs
    | some next =>
      have hn := fuelBudgetGood_levelAction P d l j s hs
      simp only [ha, Option.getD_some] at hn
      exact ih next hn

/-- A fresh candidate, one without any earlier fuel directive at level `j`, starts its phase
with the full initial budget, so the invariant holds. -/
private lemma fuelBudgetGood_startPhase (P : FighterParams) (d l j : ℕ) (c : Candidate)
    (s : FighterState) (hs : FuelBudgetGood P l s) (hfresh : fuelCount j c s = 0) :
    FuelBudgetGood P l (fighterStartPhase P d j c s) := by
  let waiting := fighterAbortAbove d j (fighterCancel d j .replaced j s)
  have hw : FuelPassive s waiting :=
    (fuelPassive_cancel d j .replaced j s).trans (fuelPassive_abortAbove d j _)
  refine fuelBudgetGood_putPhase P d l waiting _ (fuelBudgetGood_of_passive P l hs hw) ?_
  intro hl
  have hjl : j = l := hl
  subst j
  change fuelCount l c waiting + P.c₁ * 2 ^ (levelUpper l - levelScale l) ≤ _
  rw [fuelCount_eq_of_passive hw, hfresh]
  simp

/-- Every fuel directive of `t` is already in `s`, or belongs to level `j`. -/
private def FuelFrame (j : ℕ) (s t : FighterState) : Prop :=
  ∀ a ∈ t.allocated, a.kind = .fuel → a ∈ s.allocated ∨ a.level = j

private lemma FuelFrame.refl (j : ℕ) (s : FighterState) : FuelFrame j s s :=
  fun _ ha _ ↦ Or.inl ha

private lemma FuelFrame.trans {j : ℕ} {s t u : FighterState} (hst : FuelFrame j s t)
    (htu : FuelFrame j t u) : FuelFrame j s u :=
  fun a ha hk ↦ (htu a ha hk).elim (fun h ↦ hst a h hk) Or.inr

private lemma FuelPassive.fuelFrame {s t : FighterState} (h : FuelPassive s t) (j : ℕ) :
    FuelFrame j s t := by
  intro a ha hk
  have hmem : a ∈ t.allocated.filter (fun a ↦ decide (a.kind = .fuel)) :=
    List.mem_filter.mpr ⟨ha, by simpa using hk⟩
  rw [h.1] at hmem
  exact Or.inl (List.mem_of_mem_filter hmem)

private lemma fuelFrame_foldl {α : Type} (j : ℕ) (f : FighterState → α → FighterState)
    (hf : ∀ t x, FuelFrame j t (f t x)) (xs : List α) (s : FighterState) :
    FuelFrame j s (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact .refl j s
  | cons x xs ih => exact (hf s x).trans (ih _)

/-- An allocation at level `j` adds directives of level `j` only. -/
private lemma fuelFrame_allocate (d j : ℕ) (kind : DirectiveKind) (target : ℕ)
    (output : BitString) (s : FighterState) :
    FuelFrame j s (fighterAllocate d j kind target output s).1 := by
  unfold fighterAllocate
  split
  · exact .refl j s
  · cases hf : (if target = 0 then (none : Option BitString) else
        (fighterInputs d (target - 1)).find? (fun p ↦
          !s.allocated.any (fun a ↦ a.input == p))) with
    | none => exact (fuelPassive_cancel d j .saturated j { s with failed := true }).fuelFrame j
    | some input =>
      refine FuelFrame.trans (t := { s with allocated := s.allocated ++ [_] }) ?_
        ((fuelPassive_abortAbove d j _).fuelFrame j)
      intro a ha _
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (congrArg AllocatedDirective.level (List.mem_singleton.mp ha))

/-- A fuel attempt at level `j` adds directives of level `j` only. -/
private lemma fuelFrame_fuelUnit (P : FighterParams) (d j : ℕ) (q : Coordinate)
    (s : FighterState) : FuelFrame j s (fighterFuelUnit P d j q s) := by
  unfold fighterFuelUnit
  split
  · exact .refl j s
  · rename_i phase hphase
    split
    · let charged := { phase with controlledRemaining := phase.controlledRemaining - 1 }
      let index := fighterFreshString d
        (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])
      let output := pairCode (triple q.1 (q.2 - d) phase.candidate.1) index
      have ha := fuelFrame_allocate d j .fuel (levelUpper j + d) output (s.putPhase d charged)
      change FuelFrame j s
        (match fighterAllocate d j .fuel (levelUpper j + d) output (s.putPhase d charged) with
        | (next, success) => if success then fighterFulfillReady P d j
            (next.putPhase d ((charged.insertIndex d q index).fundRequests d next.fulfilled))
          else next)
      cases he : fighterAllocate d j .fuel (levelUpper j + d) output
          (s.putPhase d charged) with
      | mk next success =>
        rw [he] at ha
        have hnext : FuelFrame j s next := FuelFrame.trans (fun a ha _ ↦ Or.inl ha) ha
        cases success
        · exact hnext
        · exact hnext.trans (FuelFrame.trans (fun a ha _ ↦ Or.inl ha)
            ((fuelPassive_fulfillReady P d j _).fuelFrame j))
    · exact .refl j s

/-- Finitely many fuel attempts at level `j` add directives of level `j` only. -/
private lemma fuelFrame_fuelUnits (P : FighterParams) (d j : ℕ) (q : Coordinate) (count : ℕ)
    (s : FighterState) : FuelFrame j s (fighterFuelUnits P d j q count s) := by
  induction count generalizing s with
  | zero => exact .refl j s
  | succ count ih => exact (fuelFrame_fuelUnit P d j q s).trans (ih _)

/-- A strategy response at level `j` adds directives of level `j` only. -/
private lemma fuelFrame_strategyMove (P : FighterParams) (d j : ℕ) (s : FighterState) :
    FuelFrame j s ((fighterStrategyMove P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterStrategyMove, hphase] using FuelFrame.refl j s
  | some phase =>
    simp only [fighterStrategyMove, hphase, bind, Option.bind_some]
    split
    · cases hm : (phase.game d).strategy (phase.official d) with
      | none => exact .refl j s
      | some move =>
        simp only [Option.bind_some]
        split
        · let next := (phase.game d).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P d j qi.1 (move[qi.2]?.getD 0) s) s
          have hn : FuelFrame j s next := by
            refine fuelFrame_foldl j _ ?_ _ s
            intro t qi
            exact fuelFrame_fuelUnits P d j qi.1 _ t
          change FuelFrame j s ((match next.activeAt d j with
            | none => some next
            | some live => some (next.putPhase d
                { live with officialCode := ((phase.game d).afterMove
                  (phase.official d) move).encode })).getD s)
          cases hlive : next.activeAt d j with
          | none => exact hn
          | some live => exact hn.trans fun a ha _ ↦ Or.inl ha
        · exact .refl j s
    · exact .refl j s

/-- An enabled level action at level `j` adds directives of level `j` only. -/
private lemma fuelFrame_levelAction (P : FighterParams) (d j : ℕ) (s : FighterState) :
    FuelFrame j s ((fighterLevelAction P d j s).getD s) := by
  cases hphase : s.activeAt d j with
  | none => simpa [fighterLevelAction, hphase] using FuelFrame.refl j s
  | some phase =>
    simp only [fighterLevelAction, hphase, bind, Option.bind_some]
    split
    · exact (fuelPassive_dummy d j s).fuelFrame j
    · split
      · exact (fuelPassive_payoff P d j _ s).fuelFrame j
      · cases hf : fighterFlushBuffer d j s with
        | none => exact fuelFrame_strategyMove P d j s
        | some next =>
          have h := (fuelPassive_flushBuffer d j s).fuelFrame j
          simpa only [hf, Option.getD_some] using h

/-- The structural closure of level `j` adds directives of level `j` only. -/
private lemma fuelFrame_closure (P : FighterParams) (d j fuel : ℕ) (s : FighterState) :
    FuelFrame j s (fighterClosure P d j fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl j s
  | succ fuel ih =>
    simp only [fighterClosure]
    cases ha : fighterLevelAction P d j s with
    | none => exact .refl j s
    | some next =>
      have hn := fuelFrame_levelAction P d j s
      simp only [ha, Option.getD_some] at hn
      exact hn.trans (ih next)

/-- Servicing level `j` adds fuel directives of level `j` only. -/
private lemma fuelFrame_processLevel (P : FighterParams) (d j : ℕ) (event : Option TimedEvent)
    (s : FighterState) : FuelFrame j s (fighterProcessLevel P d j event s) := by
  have hc := (fuelPassive_fulfillReady P d j s).fuelFrame j
  unfold fighterProcessLevel fighterCloseLevel
  refine FuelFrame.trans ?_ (fuelFrame_closure P d j _ _)
  cases event with
  | none => exact hc
  | some e =>
    dsimp only
    split
    · refine hc.trans (FuelFrame.trans ?_ fun a ha _ ↦ Or.inl ha)
      exact ((fuelPassive_cancel d j .replaced j _).trans
        (fuelPassive_abortAbove d j _)).fuelFrame j
    · exact hc.trans ((fuelPassive_opponent P d j e.2.2 _).fuelFrame j)

/-- Processing the levels of a duplicate-free list preserves the accounting invariant,
provided the fuel directives of the unprocessed levels are older than the current event.
Then a candidate emitted at the new tick has no fuel directive when its owner is visited. -/
private lemma fuelBudgetGood_foldl_processLevel (P : FighterParams) (d l tick : ℕ)
    (event : Option TimedEvent) (levels : List ℕ) (hnodup : levels.Nodup)
    (hevent : match event with | some e => e.1 = tick + 1 | none => True)
    (s : FighterState) (hs : FuelBudgetGood P l s)
    (hunprocessed : ∀ a ∈ s.allocated, a.kind = .fuel →
      a.level ∈ levels → a.candidate.2 ≤ tick) :
    FuelBudgetGood P l (levels.foldl (fun s j ↦ fighterProcessLevel P d j event s) s) := by
  induction levels generalizing s with
  | nil => exact hs
  | cons j levels ih =>
    obtain ⟨hj, hlevels⟩ := List.nodup_cons.mp hnodup
    have hnext : FuelBudgetGood P l (fighterProcessLevel P d j event s) := by
      have hc := fuelPassive_fulfillReady P d j s
      have hchecked := fuelBudgetGood_of_passive P l hs hc
      unfold fighterProcessLevel fighterCloseLevel
      refine fuelBudgetGood_closure P d l j _ _ ?_
      cases event with
      | none => exact hchecked
      | some e =>
        dsimp only
        split
        · refine fuelBudgetGood_startPhase P d l j _ _ hchecked ?_
          rw [fuelCount_eq_of_passive hc]
          simp only [fuelCount, List.length_eq_zero_iff, List.filter_eq_nil_iff,
            decide_eq_true_eq]
          intro a ha h
          have hle := hunprocessed a ha h.2.1 (h.1 ▸ List.mem_cons_self)
          have ht : a.candidate.2 = e.1 := congrArg Prod.snd h.2.2
          dsimp only at hevent
          omega
        · exact fuelBudgetGood_of_passive P l hchecked (fuelPassive_opponent P d j e.2.2 _)
    refine ih hlevels _ hnext fun a ha hk hlevel ↦ ?_
    rcases fuelFrame_processLevel P d j event s a ha hk with ha | hal
    · exact hunprocessed a ha hk (List.mem_cons_of_mem j hlevel)
    · exact (hj (hal ▸ hlevel)).elim

/-- At the start of tick `tick + 1` all earlier fuel directives are older than the new event,
so processing its levels in increasing order preserves the accounting invariant. -/
private lemma fuelBudgetGood_actions (P : FighterParams) (d l tick : ℕ)
    (hs : FuelBudgetGood P l (fighterState P d tick)) :
    FuelBudgetGood P l (fighter_actions P d (tick + 1) (fighterState P d tick)) := by
  unfold fighter_actions
  split
  · simp [FuelBudgetGood, fuelCount, initialFighterState]
  · let current := { fighterState P d tick with
        tick := tick + 1, schedule := masterState P.B (tick + 1) }
    let event := eventAt P.B (tick + 1)
    let owner := event.bind (fun e ↦ fighterOwner d e.2.2.1.length)
    let levels := (current.active.map FighterPhase.level ++ owner.toList).eraseDups
    have hnodup : (levels.mergeSort (· ≤ ·)).Nodup := by
      rw [List.nodup_mergeSort]
      exact nodup_eraseDups_list _
    have hevent : match event with | some e => e.1 = tick + 1 | none => True := by
      dsimp only [event]
      cases he : eventAt P.B (tick + 1) with
      | none => trivial
      | some e => exact (canonical_enumeration_spec_sound P.B he).1
    refine fuelBudgetGood_foldl_processLevel P d l tick event (levels.mergeSort (· ≤ ·)) hnodup
      hevent current hs ?_
    intro a ha hk _
    have hstarted := fighterState_allocated_fuel_mem_started P d tick a ha hk
    exact (fighterState_started_event P d tick (a.level, a.candidate) hstarted).1

/-- At every tick the accounting invariant holds: by induction from the empty state, both the
fuel bound and the bound including the unspent budget of every active phase. -/
private lemma fuelBudgetGood_fighterState (P : FighterParams) (d l tick : ℕ) :
    FuelBudgetGood P l (fighterState P d tick) := by
  induction tick with
  | zero => simp [FuelBudgetGood, fuelCount, fighterState, initialFighterState]
  | succ tick ih => exact fuelBudgetGood_actions P d l tick ih

/-- A phase identity receives at most `P.c₁ * 2 ^ (levelUpper l - levelScale l)` fuel
directives: initialisation gives this budget, each attempted fuel unit decrements a positive
remaining budget, a success adds one allocation, and a failure cancels without adding one. -/
private lemma fuelCount_le_budget (P : FighterParams) (d l tick : ℕ) (c : Candidate) :
    ((fighterState P d tick).allocated.filter (fun a =>
      decide (a.level = l ∧ a.kind = .fuel ∧ a.candidate = c))).length
      ≤ P.c₁ * 2 ^ (levelUpper l - levelScale l) :=
  (fuelBudgetGood_fighterState P d l tick).1 c

/-- A list whose elements all fall into the classes of `keys` (under `f`), each class
containing at most `R` elements, has at most `keys.length * R` elements. -/
private lemma length_le_length_keys_mul {α β : Type} [DecidableEq β]
    (xs : List α) (keys : List β) (f : α → β) (R : ℕ)
    (hhistory : ∀ x ∈ xs, f x ∈ keys)
    (hbudget : ∀ k ∈ keys, (xs.filter (fun x ↦ decide (f x = k))).length ≤ R) :
    xs.length ≤ keys.length * R := by
  induction keys generalizing xs with
  | nil =>
      cases xs with
      | nil => simp
      | cons x xs =>
          have h := hhistory x (by simp)
          simp at h
  | cons k ks ih =>
      let p : α → Bool := fun x ↦ decide (f x = k)
      let ys := xs.filter (fun x ↦ !p x)
      have hcov : ∀ x ∈ ys, f x ∈ ks := by
        intro x hx
        obtain ⟨hx, hn⟩ := List.mem_filter.mp hx
        have hne : f x ≠ k := by simpa [p] using hn
        exact (List.mem_cons.mp (hhistory x hx)).resolve_left hne
      have hbud : ∀ j ∈ ks, (ys.filter (fun x ↦ decide (f x = j))).length ≤ R := by
        intro j hj
        have hs : ys.Sublist xs := List.filter_sublist
        exact (hs.filter (fun x ↦ decide (f x = j))).length_le.trans
          (hbudget j (by simp [hj]))
      have ht := ih ys hcov hbud
      have hh : (xs.filter p).length ≤ R := hbudget k (by simp)
      have hs := List.length_eq_length_filter_add (l := xs) p
      change xs.length = (xs.filter p).length + ys.length at hs
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- The number of fuel directives at level `l` is at most the number of phases times the
per-phase fuel budget. -/
private lemma fighterDirectiveCount_fuel_le (P : FighterParams) (d l tick : ℕ) :
    fighterDirectiveCount P d l tick .fuel ≤
      fighterPhaseCount P d l tick * (P.c₁ * 2 ^ (levelUpper l - levelScale l)) := by
  let xs := (fighterState P d tick).allocated.filter
    (fun a ↦ decide (a.level = l ∧ a.kind = .fuel))
  let keys := ((fighterState P d tick).started.filter (fun e ↦ e.1 == l)).map Prod.snd
  let f := AllocatedDirective.candidate
  let R := P.c₁ * 2 ^ (levelUpper l - levelScale l)
  have hhistory : ∀ x ∈ xs, f x ∈ keys := by
    intro x hx
    obtain ⟨hx, hd⟩ := List.mem_filter.mp hx
    simp only [decide_eq_true_eq] at hd
    have hs := fighterState_allocated_fuel_mem_started P d tick x hx hd.2
    exact List.mem_map.mpr ⟨(l, x.candidate), List.mem_filter.mpr ⟨by rwa [← hd.1], by simp⟩, rfl⟩
  have hbudget : ∀ k ∈ keys, (xs.filter (fun x ↦ decide (f x = k))).length ≤ R := by
    intro k _
    have h_eq : xs.filter (fun x ↦ decide (f x = k)) =
        (fighterState P d tick).allocated.filter
          (fun a ↦ decide (a.level = l ∧ a.kind = .fuel ∧ a.candidate = k)) := by
      dsimp [xs, f]
      rw [List.filter_filter]
      congr 1
      ext a
      simp only [← Bool.decide_and, and_assoc, Bool.and_comm]
    rw [h_eq]
    exact fuelCount_le_budget P d l tick k
  have h := length_le_length_keys_mul xs keys f R hhistory hbudget
  simpa [fighterDirectiveCount, fighterPhaseCount, xs, keys, f, R, List.length_map] using h

/-- Fewer than `2 ^ (levelScale l + 1)` phases, each with a fuel budget of
`P.c₁ * 2 ^ (levelUpper l - levelScale l)`, use at most `2 * P.c₁ * 2 ^ levelUpper l` fuel. -/
private lemma phaseCount_mul_fuelBudget_le (P : FighterParams) (d l tick : ℕ)
    (h_count : fighterPhaseCount P d l tick < 2 ^ (levelScale l + 1)) :
    fighterPhaseCount P d l tick * (P.c₁ * 2 ^ (levelUpper l - levelScale l)) ≤
      2 * P.c₁ * 2 ^ levelUpper l := by
  have h_bound : levelScale l ≤ levelUpper l := (tower_lt_tower_add_one (2 * l)).le
  calc fighterPhaseCount P d l tick * (P.c₁ * 2 ^ (levelUpper l - levelScale l))
    _ ≤ 2 ^ (levelScale l + 1) * (P.c₁ * 2 ^ (levelUpper l - levelScale l)) :=
        Nat.mul_le_mul_right _ h_count.le
    _ = 2 * P.c₁ * (2 ^ levelScale l * 2 ^ (levelUpper l - levelScale l)) := by ring
    _ = 2 * P.c₁ * 2 ^ (levelScale l + (levelUpper l - levelScale l)) := by rw [← pow_add]
    _ = 2 * P.c₁ * 2 ^ levelUpper l := by rw [Nat.add_sub_of_le h_bound]

/-- Each program starts at most one phase; each phase uses at most one dummy and `R` fuel.
Blueprint node `constr:phasecount`. The bounds hold at every tick, even for false candidates
and padding members where the allocation guard is reached. -/
theorem fighter_phase_count (P : FighterParams) (d l tick : ℕ) :
    fighterPhaseCount P d l tick < 2 ^ (levelScale l + 1) ∧
    fighterDirectiveCount P d l tick .dummy ≤ fighterPhaseCount P d l tick ∧
    fighterDirectiveCount P d l tick .fuel ≤ 2 * P.c₁ * 2 ^ levelUpper l :=
  ⟨fighterPhaseCount_lt_two_pow P d l tick,
    fighterDirectiveCount_dummy_le_fighterPhaseCount P d l tick,
    (fighterDirectiveCount_fuel_le P d l tick).trans
      (phaseCount_mul_fuelBudget_le P d l tick (fighterPhaseCount_lt_two_pow P d l tick))⟩

/-- Admissibility supplies the padding-square inequality without changing the fixed threshold.
Blueprint node `constr:intervals`. -/
theorem fighter_admissible_square (P : FighterParams) (d l : ℕ) (ha : P.Admissible d l) :
    32 ≤ levelScale l ∧ d ^ 2 ≤ levelScale l ∧ d ≤ Nat.sqrt (levelScale l) := by
  have h := ha.2.1
  have hd : d ^ 2 ≤ levelScale l := by omega
  exact ⟨by omega, hd, Nat.le_sqrt'.mpr hd⟩

/-- Binary exponential growth dominates twice its exponent at every natural exponent.
Blueprint node `constr:intervals`. -/
theorem fighter_twice_le_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.pow_succ]
    by_cases hk : k = 0
    · subst k; norm_num
    · have hkpos : 1 ≤ k := by omega
      nlinarith

/-- Floor binary logarithms fit in half the number, including the zero convention.
Blueprint node `constr:intervals`. -/
theorem fighter_log2_le_half (n : ℕ) : Nat.log2 n ≤ n / 2 := by
  by_cases hn : n = 0
  · subst n; decide
  · have hp : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn).mp le_rfl
    have ht := fighter_twice_le_pow (Nat.log2 n)
    omega

/-- The integer square root fits in half a number above the fixed numerical cutoff.
Blueprint node `constr:intervals`. -/
theorem fighter_half_add_sqrt_le (n : ℕ) (hn : 32 ≤ n) : n / 2 + Nat.sqrt n ≤ n := by
  have hs : 2 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr (by omega)
  have hsq := Nat.sqrt_le' n
  have hdouble : 2 * Nat.sqrt n ≤ n := by nlinarith
  omega

/-- The full previous-level endpoint estimate, uniform whenever `d² ≤ n`.
Blueprint node `constr:intervals`. All divisions and square roots are natural floors. -/
theorem fighter_log_padding_bound (n d : ℕ) (hn : 32 ≤ n) (hd : d ^ 2 ≤ n) :
    Nat.log2 n + d ≤ n / 2 + Nat.sqrt n ∧ n / 2 + Nat.sqrt n ≤ n :=
  ⟨Nat.add_le_add (fighter_log2_le_half n) (Nat.le_sqrt'.mpr hd),
    fighter_half_add_sqrt_le n hn⟩

/-- The dummy target lies strictly below the square, which lies in the tower target bound.
Blueprint node `constr:intervals`. -/
theorem fighter_dummy_below_range (n d : ℕ) (hn : 32 ≤ n) (hd : d ^ 2 ≤ n) :
    n + d < n ^ 2 ∧ n ^ 2 ≤ towerRangeBound n := by
  have hdle : d ≤ n := (Nat.le_sqrt'.mpr hd).trans (Nat.sqrt_le_self n)
  have hlog : 2 ≤ Nat.log2 n := (Nat.le_log2 (by omega)).mpr (by omega)
  exact ⟨by nlinarith, Nat.pow_le_pow_right (by omega) hlog⟩

/-- The payoff range is strictly below the exponential endpoint at tower scales at least 32.
Blueprint node `constr:intervals`. This is the frozen stage-2 range separation theorem. -/
theorem fighter_range_below_upper (n : ℕ) (hn : 32 ≤ n) (ht : IsTower n) :
    towerRangeBound n < 2 ^ n :=
  tower_range_separation n hn ht

/-- The previous positive-level upper endpoint is at most the logarithm of the current scale.
Blueprint node `constr:intervals`. -/
theorem fighter_previous_upper_bound (j l : ℕ) (hj : 1 ≤ j) (hjl : j < l) :
    levelUpper j ≤ Nat.log2 (levelScale l) := by
  unfold levelUpper levelScale
  have h_log : Nat.log2 (tower (2 * l)) = tower (2 * l - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 * l = k + 1 := ⟨2 * l - 1, by omega⟩
    rw [hk]
    have h_eq : tower (k + 1) = 2 ^ tower k := rfl
    rw [h_eq, Nat.log2_two_pow]
    congr
  rw [h_log]
  exact strictMono_tower.monotone (by omega)

end Kolmogorov.Milovanov
