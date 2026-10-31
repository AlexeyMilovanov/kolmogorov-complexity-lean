/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.GameTransitions

/-!
# Effective allocation and fighter execution

For blueprint node `constr:effective`, this module assembles the computable game transitions
into level actions, event processing, and the full fighter state sequence. It derives a
partial recursive directive stream and conditional optimality of the fighter machine.
The guarded allocation search never reuses an input, including when a small-padding member
runs out of capacity. Preservation of this invariant through phase actions and event traversal
provides the freshness theorem used by the live-state invariants and later counting arguments.
The directive stream supplies the effective family used to compile the final separating machine.
-/

namespace Kolmogorov.Milovanov

/-- Issuing a pending dummy, and marking it issued on success, is computable. -/
private theorem computable_fighterDummy :
    Computable (fun a : ℕ × ℕ × FighterState ↦ fighterDummy a.1 a.2.1 a.2.2) := by
  have hs : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have hb : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
      match a.2.dummy with
      | none => a.1.2.2
      | some output =>
        if a.2.dummyIssued then a.1.2.2 else
          let (next, success) := fighterAllocate a.1.1 a.1.2.1 .dummy
            (levelInput a.1.1 a.1.2.1) output a.1.2.2
          if success then next.putPhase a.1.1 { a.2 with dummyIssued := true } else next) := by
    have hd : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦ a.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hl :
        Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦ a.1.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have ht :
        Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦ a.1.1.2.2) :=
      hs.comp (Computable.fst.comp Computable.fst)
    have hp : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦
        { a.1.2 with dummyIssued := true }) :=
      FighterPhase.primrec_markDummy.to_comp.comp
        (Computable.snd.comp Computable.fst)
    have hm : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦
        levelInput a.1.1.1 a.1.1.2.1) :=
      Primrec.nat_add.to_comp.comp (primrec_levelScale.to_comp.comp hl) hd
    have ha := computable_fighterAllocate.comp
      (hd.pair (hl.pair ((Computable.const DirectiveKind.dummy).pair
        (hm.pair (Computable.snd.pair ht)))))
    have hn := Computable.fst.comp ha
    have hy := Computable.snd.comp ha
    have hput := computable_putPhase.comp (hd.pair (hp.pair hn))
    have hresult := computable_ite_decide
      (Primrec.eq.decide.to_comp.comp hy (Computable.const true)) hput hn
    have hissued : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦
        a.1.2.dummyIssued) := FighterPhase.primrec_dummyIssued.to_comp.comp
      (Computable.snd.comp Computable.fst)
    have hout := computable_ite_decide
      (Primrec.eq.decide.to_comp.comp hissued (Computable.const true)) ht hresult
    have hout' : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × BitString ↦
        if a.1.2.dummyIssued then a.1.1.2.2 else
          let (next, success) := fighterAllocate a.1.1.1 a.1.1.2.1 .dummy
            (levelInput a.1.1.1 a.1.1.2.1) a.2 a.1.1.2.2
          if success then next.putPhase a.1.1.1 { a.1.2 with dummyIssued := true } else next) :=
      hout.of_eq (fun a ↦ by
        cases h : fighterAllocate a.1.1.1 a.1.1.2.1 .dummy
          (levelInput a.1.1.1 a.1.1.2.1) a.2 a.1.1.2.2
        rfl)
    exact (Computable.option_casesOn
      (α := (ℕ × ℕ × FighterState) × FighterPhase) (β := BitString) (σ := FighterState)
      (o := fun a ↦ a.2.dummy) (f := fun a ↦ a.1.2.2)
      (g := fun a output ↦
        if a.2.dummyIssued then a.1.2.2 else
          let (next, success) := fighterAllocate a.1.1 a.1.2.1 .dummy
            (levelInput a.1.1 a.1.2.1) output a.1.2.2
          if success then next.putPhase a.1.1 { a.2 with dummyIssued := true } else next)
      (FighterPhase.primrec_dummy.to_comp.comp Computable.snd)
      (hs.comp Computable.fst) hout'.to₂).of_eq
        (fun a ↦ by cases a.2.dummy <;> rfl)
  exact (Computable.option_casesOn (α := ℕ × ℕ × FighterState)
    (β := FighterPhase) (σ := FighterState)
    (o := fun a ↦ a.2.2.activeAt a.1 a.2.1) (f := fun a ↦ a.2.2)
    (g := fun a phase ↦ match phase.dummy with
      | none => a.2.2
      | some output =>
        if phase.dummyIssued then a.2.2 else
          let (next, success) := fighterAllocate a.1 a.2.1 .dummy
            (levelInput a.1 a.2.1) output a.2.2
          if success then next.putPhase a.1 { phase with dummyIssued := true } else next)
    primrec_activeAt.to_comp hs hb.to₂).of_eq
      (fun a ↦ by unfold fighterDummy; cases a.2.2.activeAt a.1 a.2.1 <;> rfl)

private theorem computable_ready_request (P : FighterParams) :
    Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
      a.2.pending.find? (fun q ↦ decide (q ∉ a.1.2.2.fulfilled) &&
        fighterSafe P a.1.1 a.1.2.2.tick q)) := by
  have hs : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have ht : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × Coordinate ↦
      a.1.1.2.2) := hs.comp (Computable.fst.comp Computable.fst)
  have hd : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × Coordinate ↦ a.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hmem := list_mem_decide_primrec.to_comp.comp Computable.snd
    (FighterState.primrec_fulfilled.to_comp.comp ht)
  have hsafe := (computable_fighterSafe P).comp
    (hd.pair ((FighterState.primrec_tick.to_comp.comp ht).pair Computable.snd))
  have hpred : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × Coordinate ↦
      decide (a.2 ∉ a.1.1.2.2.fulfilled) && fighterSafe P a.1.1.1 a.1.1.2.2.tick a.2) :=
    (Primrec.and.to_comp.comp (Primrec.not.to_comp.comp hmem) hsafe).of_eq
      (fun a ↦ by apply Bool.eq_iff_iff.mpr; simp)
  exact computable_find?
    (FighterPhase.primrec_pending.to_comp.comp Computable.snd) hpred.to₂

/-- Selecting and executing the next enabled action of a live phase is computable. -/
private theorem computable_fighterLevelAction (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × FighterState ↦ fighterLevelAction P a.1 a.2.1 a.2.2) := by
  have hdummy := computable_fighterDummy
  have hpay := computable_fighterPayoff P computable_fighterAllocate
  have hfulfill := computable_fighterFulfillReady P hpay
  have hfuel := computable_fighterFuelUnit P computable_fighterAllocate hfulfill
  have hunits := computable_fighterFuelUnits P hfuel
  have hstrategy := computable_fighterStrategyMove P hunits
  have hflush := computable_fighterFlushBuffer
  have hbranch : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
      if a.2.dummy.isSome && !a.2.dummyIssued then
        some (fighterDummy a.1.1 a.1.2.1 a.1.2.2)
      else match a.2.pending.find? (fun q ↦ decide (q ∉ a.1.2.2.fulfilled) &&
          fighterSafe P a.1.1 a.1.2.2.tick q) with
        | some q => some (fighterPayoff P a.1.1 a.1.2.1 q a.1.2.2)
        | none => match fighterFlushBuffer a.1.1 a.1.2.1 a.1.2.2 with
          | some next => some next
          | none => fighterStrategyMove P a.1.1 a.1.2.1 a.1.2.2) := by
    have hd :
        Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × Coordinate ↦ a.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hl :
        Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × Coordinate ↦ a.1.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hs :
        Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × Coordinate ↦ a.1.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hpaybody : Computable₂ (fun (a : (ℕ × ℕ × FighterState) × FighterPhase) (q : Coordinate) ↦
        fighterPayoff P a.1.1 a.1.2.1 q a.1.2.2) :=
      (hpay.comp (hd.pair (hl.pair (Computable.snd.pair hs)))).to₂
    have hp := computable_ready_request P
    have hpmap := Computable.option_map hp hpaybody
    have hfall : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
        fighterFlushBuffer a.1.1 a.1.2.1 a.1.2.2 <|>
          fighterStrategyMove P a.1.1 a.1.2.1 a.1.2.2) :=
      Primrec.option_orElse.to_comp.comp (hflush.comp Computable.fst)
        (hstrategy.comp Computable.fst)
    have hrest := Primrec.option_orElse.to_comp.comp hpmap hfall
    have htest : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
        a.2.dummy.isSome && !a.2.dummyIssued) :=
      Primrec.and.to_comp.comp
        (Primrec.option_isSome.to_comp.comp
          (FighterPhase.primrec_dummy.to_comp.comp Computable.snd))
        (Primrec.not.to_comp.comp
          (FighterPhase.primrec_dummyIssued.to_comp.comp Computable.snd))
    have hraw := Computable.cond htest
      (Computable.option_some.comp (hdummy.comp Computable.fst)) hrest
    refine hraw.of_eq ?_
    intro a
    cases htest : a.2.dummy.isSome && !a.2.dummyIssued
    · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
      cases hp : a.2.pending.find? (fun q ↦ decide (q ∉ a.1.2.2.fulfilled) &&
        fighterSafe P a.1.1 a.1.2.2.tick q)
      · cases fighterFlushBuffer a.1.1 a.1.2.1 a.1.2.2 <;> rfl
      · rfl
    · simp only [Bool.cond_true, ↓reduceIte]
  exact (Computable.option_bind (α := ℕ × ℕ × FighterState)
    (β := FighterPhase) (σ := FighterState)
    (f := fun a ↦ a.2.2.activeAt a.1 a.2.1)
    primrec_activeAt.to_comp hbranch.to₂).of_eq
      (fun a ↦ rfl)

private theorem computable_fighterClosureFuel :
    Computable (fun a : ℕ × ℕ × FighterState ↦ fighterClosureFuel a.1 a.2.1 a.2.2) := by
  have hc : Primrec (fun p : FighterPhase ↦ (p.game 0).coordinates) :=
    primrec_eraseDups.comp
      (Primrec.fst.comp FighterPhase.primrec_gameCode)
  have hb : Primrec (fun p : FighterPhase ↦ (p.game 0).budget) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp FighterPhase.primrec_gameCode))))
  have hh : Computable₂ (fun (_ : ℕ × ℕ × FighterState) (p : FighterPhase) ↦
      2 * (p.game 0).budget + (p.game 0).coordinates.length + p.pending.length + 5) :=
    (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp
        (Primrec.nat_add.to_comp.comp
          (Primrec.nat_mul.to_comp.comp (Computable.const 2) (hb.to_comp.comp Computable.snd))
          (Computable.list_length.comp (hc.to_comp.comp Computable.snd)))
        (Computable.list_length.comp
          (FighterPhase.primrec_pending.to_comp.comp Computable.snd)))
      (Computable.const 5)).to₂
  exact (Computable.option_casesOn primrec_activeAt.to_comp
    (Computable.const 0) hh).of_eq (fun a ↦ by
      unfold fighterClosureFuel
      cases a.2.2.activeAt a.1 a.2.1 <;> rfl)

private theorem computable_fighterClosure (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × ℕ × FighterState ↦
      fighterClosure P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hact := computable_fighterLevelAction P
  have hd : Computable (fun a : ℕ × ℕ × ℕ × FighterState ↦ a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hn : Computable (fun a : ℕ × ℕ × ℕ × FighterState ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : ℕ × ℕ × ℕ × FighterState ↦ a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun a : (ℕ × ℕ × ℕ × FighterState) × (ℕ × FighterState) ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have hh : Computable₂ (fun (a : ℕ × ℕ × ℕ × FighterState) (u : ℕ × FighterState) ↦
      (fighterLevelAction P a.1 a.2.1 u.2).getD u.2) := (Computable.option_getD (hact.comp
    ((hd.comp Computable.fst).pair ((hl.comp Computable.fst).pair ht))) ht).to₂
  have hr := Computable.nat_rec hn hs hh
  refine hr.of_eq ?_
  intro a
  dsimp only
  rw [natRec_eq_iterate]
  have heq : ∀ n s,
      (fun t ↦ (fighterLevelAction P a.1 a.2.1 t).getD t)^[n] s =
        fighterClosure P a.1 a.2.1 n s := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply, fighterClosure]
      cases h : fighterLevelAction P a.1 a.2.1 s with
      | none =>
        simp only [Option.getD_none]
        exact Function.iterate_fixed (by simp [h]) n
      | some t => simpa only [Option.getD_some] using ih t
  exact heq _ _

private theorem computable_fighterCloseLevel (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × FighterState ↦ fighterCloseLevel P a.1 a.2.1 a.2.2) := by
  have hd : Computable (fun a : ℕ × ℕ × FighterState ↦ a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hs : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  exact ((computable_fighterClosure P).comp
    (hd.pair (hl.pair (computable_fighterClosureFuel.pair hs)))).of_eq
      (fun a ↦ rfl)

private theorem computable_fighterStartPhase (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × Candidate × FighterState ↦
      fighterStartPhase P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hinit := computable_fighterStageConstruction P
  have hd : Computable (fun a : ℕ × ℕ × Candidate × FighterState ↦ a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × Candidate × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hw : Computable (fun a : ℕ × ℕ × Candidate × FighterState ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : ℕ × ℕ × Candidate × FighterState ↦ a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hc := primrec_fighterCancel.to_comp.comp
    (hd.pair (hl.pair ((Computable.const PhaseEnd.replaced).pair (hl.pair hs))))
  have hwaiting := primrec_fighterAbortAbove.to_comp.comp (hd.pair (hl.pair hc))
  have hphase := hinit.comp (hd.pair (hl.pair (hw.pair hwaiting)))
  have hnext := computable_putPhase.comp (hd.pair (hphase.pair hwaiting))
  exact (FighterState.computable_mk
    (FighterState.primrec_tick.to_comp.comp hnext)
    (FighterState.primrec_schedule.to_comp.comp hnext)
    (FighterState.primrec_allocated.to_comp.comp hnext)
    (FighterState.primrec_fulfilled.to_comp.comp hnext)
    (FighterState.primrec_failed.to_comp.comp hnext)
    (FighterState.primrec_active.to_comp.comp hnext)
    (Computable.list_concat.comp
      (FighterState.primrec_started.to_comp.comp hnext) (hl.pair hw))
    (FighterState.primrec_ended.to_comp.comp hnext)).of_eq (fun a ↦ rfl)

private theorem computable_phase_start_guard (P : FighterParams) :
    Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦
      decide (fighterOwner a.1.1 a.2.2.2.1.length = some a.1.2.1 ∧
        a.2.2.2.1.length ≤ levelScale a.1.2.1 ∧ P.Admissible a.1.1 a.1.2.1)) := by
  have hd' :
      Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦ a.1.1) :=
    Computable.fst.comp Computable.fst
  have hl' :
      Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦ a.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hp : Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦
      a.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hlen := Computable.list_length.comp hp
  have hown := primrec₂_fighterOwner.to_comp.comp hd' hlen
  have h1 := Primrec.eq.decide.to_comp.comp hown (Computable.option_some.comp hl')
  have h2 := Primrec.nat_le.decide.to_comp.comp hlen
    (primrec_levelScale.to_comp.comp hl')
  have h3 := (computable_decide_admissible P).comp (hd'.pair hl')
  exact (Primrec.and.to_comp.comp h1 (Primrec.and.to_comp.comp h2 h3)).of_eq
    (fun a ↦ by apply Bool.eq_iff_iff.mpr; simp)

private theorem computable_fighterProcessLevel (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × Option TimedEvent × FighterState ↦
      fighterProcessLevel P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hpay := computable_fighterPayoff P computable_fighterAllocate
  have hfulfill := computable_fighterFulfillReady P hpay
  have hstart := computable_fighterStartPhase P
  have hopponent := computable_fighterOpponent P hfulfill
  have hclose := computable_fighterCloseLevel P
  have hd : Computable (fun a : ℕ × ℕ × Option TimedEvent × FighterState ↦ a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × Option TimedEvent × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have he : Computable (fun a : ℕ × ℕ × Option TimedEvent × FighterState ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : ℕ × ℕ × Option TimedEvent × FighterState ↦ a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hchecked := hfulfill.comp (hd.pair (hl.pair hs))
  have hb : Computable₂ (fun (a : ℕ × ℕ × Option TimedEvent × FighterState) (e : TimedEvent) ↦
      if fighterOwner a.1 e.2.2.1.length = some a.2.1 ∧ e.2.2.1.length ≤ levelScale a.2.1 ∧
          P.Admissible a.1 a.2.1 then
        fighterStartPhase P a.1 a.2.1 (e.2.2.1, e.1) (fighterFulfillReady P a.1 a.2.1 a.2.2.2)
      else fighterOpponent P a.1 a.2.1 e.2.2 (fighterFulfillReady P a.1 a.2.1 a.2.2.2)) := by
    have hd' :
        Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦ a.1.1) :=
        hd.comp Computable.fst
    have hl' :
        Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦ a.1.2.1) :=
        hl.comp Computable.fst
    have hc' : Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦
        fighterFulfillReady P a.1.1 a.1.2.1 a.1.2.2.2) := hchecked.comp Computable.fst
    have hp : Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦
        a.2.2.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
    have hguard := computable_phase_start_guard P
    have hw := hp.pair (Computable.fst.comp Computable.snd)
    have hyes := hstart.comp (hd'.pair (hl'.pair (hw.pair hc')))
    have hev : Computable (fun a : (ℕ × ℕ × Option TimedEvent × FighterState) × TimedEvent ↦
        a.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
    have hno := hopponent.comp (hd'.pair (hl'.pair (hev.pair hc')))
    exact (computable_ite_decide hguard hyes hno).to₂
  have hn := Computable.option_casesOn he hchecked hb
  exact (hclose.comp (hd.pair (hl.pair hn))).of_eq (fun a ↦ by
    unfold fighterProcessLevel
    cases a.2.2.1 <;> rfl)

private theorem computable_update_schedule (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × FighterState ↦
      { a.2.2 with tick := a.2.1, schedule := masterState P.B a.2.1 }) := by
  have ht : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hs : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have hschedule := (canonical_enumeration_spec P.B).comp ht
  apply FighterState.computable_mk ht hschedule
  · exact FighterState.primrec_allocated.to_comp.comp hs
  · exact FighterState.primrec_fulfilled.to_comp.comp hs
  · exact FighterState.primrec_failed.to_comp.comp hs
  · exact FighterState.primrec_active.to_comp.comp hs
  · exact FighterState.primrec_started.to_comp.comp hs
  · exact FighterState.primrec_ended.to_comp.comp hs

private theorem computable_initial_schedule (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × FighterState ↦
      { initialFighterState a.1 with tick := a.2.1, schedule := masterState P.B a.2.1 }) := by
  have ht : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hschedule := (canonical_enumeration_spec P.B).comp ht
  apply FighterState.computable_mk ht hschedule
  · exact Computable.const []
  · exact Computable.const []
  · exact Computable.const false
  · exact Computable.const []
  · exact Computable.const []
  · exact Computable.const []

private theorem primrec_event_owner_list :
    Primrec (fun a : ℕ × Option TimedEvent ↦
      (a.2.bind (fun e ↦ fighterOwner a.1 e.2.2.1.length)).toList) := by
  have hlen : Primrec (fun a : (ℕ × Option TimedEvent) × TimedEvent ↦ a.2.2.2.1.length) :=
    Primrec.list_length.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hg : Primrec₂ (fun (a : ℕ × Option TimedEvent) (e : TimedEvent) ↦
      fighterOwner a.1 e.2.2.1.length) :=
    (primrec₂_fighterOwner.comp (Primrec.fst.comp Primrec.fst) hlen).to₂
  have ho : Primrec (fun a : ℕ × Option TimedEvent ↦
      a.2.bind (fun e ↦ fighterOwner a.1 e.2.2.1.length)) :=
    Primrec.option_bind Primrec.snd hg
  have ht : Primrec (fun o : Option ℕ ↦ o.toList) :=
    (Primrec.option_casesOn Primrec.id (Primrec.const [])
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂).of_eq
        (fun o ↦ by cases o <;> rfl)
  exact ht.comp ho

private theorem primrec_ordered_levels :
    Primrec (fun a : List FighterPhase × List ℕ ↦
      ((a.1.map FighterPhase.level ++ a.2).eraseDups).mergeSort (· ≤ ·)) := by
  have hm : Primrec (fun a : List FighterPhase × List ℕ ↦ a.1.map FighterPhase.level) :=
    Primrec.list_map Primrec.fst
      (FighterPhase.primrec_level.comp Primrec.snd).to₂
  exact primrec_mergeSort_le.comp
    (primrec_eraseDups.comp (Primrec.list_append.comp hm Primrec.snd))

/-- The ordered traversal of active levels and the optional event owner is computable. -/
private theorem computable_event_levels (P : FighterParams) :
    Computable (fun a : ℕ × ℕ × FighterState ↦
      let event := eventAt P.B a.2.1
      let owner := event.bind (fun e ↦ fighterOwner a.1 e.2.2.1.length)
      ((a.2.2.active.map FighterPhase.level ++ owner.toList).eraseDups).mergeSort (· ≤ ·)) := by
  have ht : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hs : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have ho := primrec_event_owner_list.to_comp.comp
    (Computable.fst.pair ((canonical_enumeration_spec_tables P.B).2.2.comp ht))
  have ha := FighterState.primrec_active.to_comp.comp hs
  exact (primrec_ordered_levels.to_comp.comp (ha.pair ho)).of_eq
    (fun a ↦ rfl)

/-- A total event transition is uniformly computable on the explicit primitive state record.
Blueprint node `constr:effective`. Game computation uses `solveCounterGameCode`,
whose output agrees with the semantic game. -/
theorem fighter_event_transition_computable (P : FighterParams) :
    Computable (fun input : ℕ × ℕ × FighterState =>
      fighter_actions P input.1 input.2.1 input.2.2) := by
  have hprocess := computable_fighterProcessLevel P
  have hd : Computable (fun a : ℕ × ℕ × FighterState ↦ a.1) := Computable.fst
  have ht : Computable (fun a : ℕ × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hcurrent := computable_update_schedule P
  have hzero := computable_initial_schedule P
  have hevent := (canonical_enumeration_spec_tables P.B).2.2.comp ht
  have hlevels := computable_event_levels P
  have hstep : Computable₂ (fun (a : ℕ × ℕ × FighterState) (p : FighterState × ℕ) ↦
      fighterProcessLevel P a.1 p.2 (eventAt P.B a.2.1) p.1) :=
    (hprocess.comp ((hd.comp Computable.fst).pair
      ((Computable.snd.comp Computable.snd).pair
        ((hevent.comp Computable.fst).pair (Computable.fst.comp Computable.snd))))).to₂
  have hfold := Computable.list_foldl hlevels hcurrent hstep
  exact (computable_ite_decide
    ((Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp) hzero hfold).of_eq
      (fun a ↦ rfl)

/-- The complete finite state is computable uniformly in padding and numerical tick.
Blueprint node `constr:effective`. -/
theorem fighter_state_computable (P : FighterParams) :
    Computable (fun input : ℕ × ℕ => fighterState P input.1 input.2) := by
  have ht : Computable (fun a : ℕ × ℕ ↦ a.2) := Computable.snd
  have hzero : Computable (fun a : ℕ × ℕ ↦ initialFighterState a.1) :=
    (Computable.const (initialFighterState 0)).of_eq (fun _ ↦ rfl)
  have hh : Computable₂ (fun (a : ℕ × ℕ) (s : ℕ × FighterState) ↦
      fighter_actions P a.1 (s.1 + 1) s.2) := by
    have hpadding : Computable (fun a : (ℕ × ℕ) × (ℕ × FighterState) ↦ a.1.1) :=
      Computable.fst.comp Computable.fst
    have htick : Computable (fun a : (ℕ × ℕ) × (ℕ × FighterState) ↦ a.2.1 + 1) :=
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).to_comp
    have hstate : Computable (fun a : (ℕ × ℕ) × (ℕ × FighterState) ↦ a.2.2) :=
      Computable.snd.comp Computable.snd
    exact ((fighter_event_transition_computable P).comp
      (hpadding.pair (htick.pair hstate))).to₂
  have hr := Computable.nat_rec ht hzero hh
  refine hr.of_eq ?_
  intro a
  dsimp only
  induction a.2 with
  | zero => rfl
  | succ t ih =>
    rw [fighterState]
    exact congrArg (fighter_actions P a.1 (t + 1)) ih

/-- First-allocation search is partial recursive uniformly in padding and program.
Blueprint node `constr:effective`. This statement covers the entire guarded family. -/
theorem fighter_directive_stream_partrec (P : FighterParams) :
    Partrec (fun input : ℕ × BitString => fighterG P input.1 input.2) := by
  have houtput : Primrec AllocatedDirective.output :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.of_equiv (e := AllocatedDirective.equivProd)))))))
  have hlookup : Computable (fun a : (ℕ × BitString) × ℕ ↦
      fighterAllocationAt P a.1.1 a.2 a.1.2) := by
    have hstate : Computable (fun a : (ℕ × BitString) × ℕ ↦
        fighterState P a.1.1 a.2) :=
      (fighter_state_computable P).comp
        (g := fun a : (ℕ × BitString) × ℕ ↦ (a.1.1, a.2))
        ((Computable.fst.comp Computable.fst).pair Computable.snd)
    have hentries := FighterState.primrec_allocated.to_comp.comp hstate
    have htest : Computable₂ (fun (a : (ℕ × BitString) × ℕ)
        (entry : AllocatedDirective) ↦ entry.input == a.1.2) :=
      (primrec₂_beq.to_comp.comp
        (AllocatedDirective.primrec_input.to_comp.comp Computable.snd)
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).to₂
    exact Computable.option_map
      (computable_find? hentries htest)
      (houtput.to_comp.comp Computable.snd).to₂
  have hsearch := Partrec.rfindOpt hlookup.to₂
  have hguard : Computable (fun input : ℕ × BitString ↦ decide (input.1 = 0)) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp
  exact (Partrec.cond hguard Partrec.none hsearch).of_eq (fun input ↦ by
    simp only [Bool.cond_decide, Nat.rfindOpt, fighterG]
    rfl)

/-- Every positive member is conditionally optimal by the simulation theorem.
Blueprint node `constr:effective`. No large-padding capacity assertion is needed. -/
theorem fighter_machine_optimal_conditional (P : FighterParams) (d : ℕ) (hd : 1 ≤ d) :
    isOptimalConditional (fighterU P d) := by
  apply constructed_machine_optimal_conditional P.B d hd
  exact (fighter_directive_stream_partrec P).comp ((Computable.const d).pair Computable.id)

private abbrev allocationInputsNodup (s : FighterState) : Prop :=
  (s.allocated.map AllocatedDirective.input).Nodup

private lemma allocation_inputs_nodup_fighterCancel
    (d l : ℕ) (r : PhaseEnd) (c : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterCancel d l r c s) := by
  unfold fighterCancel
  split <;> exact h

private lemma allocation_inputs_nodup_fighterAbortAbove
    (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterAbortAbove d l s) := by
  unfold fighterAbortAbove
  refine List.foldlRecOn _ _ h ?_
  intro s hs a _
  dsimp only [fighterCancel]
  split_ifs with hc
  · cases h_act : s.activeAt d a.level
    · exact hs
    · exact hs
  · exact hs

/-- `fighterAllocate` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterAllocate (d l : ℕ) (kind : DirectiveKind)
    (target : ℕ) (out : Kolmogorov.BitString)
    (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterAllocate d l kind target out s).1 := by
  unfold fighterAllocate
  cases hs : s.activeAt d l with
  | none => exact h
  | some phase =>
    dsimp only
    by_cases ht : target = 0
    · simp only [ht, ↓reduceIte]
      exact allocation_inputs_nodup_fighterCancel d l .saturated l _ h
    · simp only [ht, ↓reduceIte]
      cases hf : (fighterInputs d (target - 1)).find?
          (fun p ↦ !s.allocated.any (fun a ↦ a.input == p)) with
      | none => exact allocation_inputs_nodup_fighterCancel d l .saturated l _ h
      | some p =>
        apply allocation_inputs_nodup_fighterAbortAbove
        unfold allocationInputsNodup at h ⊢
        dsimp only
        rw [List.map_append]
        rw [List.map_singleton]
        rw [List.nodup_append']
        refine ⟨h, ?_, ?_⟩
        · simp only [List.nodup_singleton]
        · rw [List.disjoint_iff_ne]
          intro x hx y hy h_eq
          simp only [List.mem_singleton] at hy
          subst hy
          subst h_eq
          have hfresh := List.find?_some hf
          have hnotmem : x ∉ s.allocated.map AllocatedDirective.input := by
            simpa only [Bool.not_eq_true_eq_eq_false, List.any_eq_false, beq_iff_eq,
              List.mem_map, not_exists, not_and] using hfresh
          exact hnotmem hx

private lemma allocation_inputs_nodup_putPhase (d : ℕ) (p : FighterPhase) (s : FighterState)
    (h : allocationInputsNodup s) :
    allocationInputsNodup (s.putPhase d p) := by
  unfold FighterState.putPhase
  exact h

private lemma allocation_inputs_nodup_fighterStartPhase
    (P : FighterParams) (d l : ℕ) (w : Candidate)
    (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterStartPhase P d l w s) := by
  let waiting := fighterAbortAbove d l (fighterCancel d l .replaced l s)
  change allocationInputsNodup (waiting.putPhase d (fighter_construction P d l w waiting))
  exact allocation_inputs_nodup_putPhase d (fighter_construction P d l w waiting) waiting
    (allocation_inputs_nodup_fighterAbortAbove d l _
      (allocation_inputs_nodup_fighterCancel d l .replaced l s h))

/-- `fighterDummy` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterDummy
    (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterDummy d l s) := by
  unfold fighterDummy
  split
  · exact h
  · rename_i phase h_act
    split
    · exact h
    · rename_i output h_dummy
      split_ifs with hissued
      · exact h
      · let next := fighterAllocate d l .dummy (levelInput d l) output s
        have h_alloc : allocationInputsNodup next.1 :=
          allocation_inputs_nodup_fighterAllocate d l .dummy
            (levelInput d l) output s h
        dsimp only
        split
        · exact allocation_inputs_nodup_putPhase d
              { phase with dummyIssued := true } next.1 h_alloc
        · exact h_alloc

/-- `fighterPayoff` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterPayoff
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterPayoff P d l q s) := by
  unfold fighterPayoff
  cases hs : s.activeAt d l
  · exact h
  · rename_i phase
    dsimp only
    split
    · rename_i h_if
      generalize eq : fighterAllocate d l .payoff q.2 q.1 s = res
      have h_alloc : allocationInputsNodup res.1 := by
        rw [← eq]
        exact allocation_inputs_nodup_fighterAllocate d l .payoff q.2 q.1 s h
      rcases res with ⟨next, success⟩
      change allocationInputsNodup next at h_alloc
      cases success
      · exact h_alloc
      · exact h_alloc
    · exact h

private lemma allocation_inputs_nodup_fighterFulfillReady
    (P : FighterParams) (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterFulfillReady P d l s) := by
  unfold fighterFulfillReady
  cases h_act : s.activeAt d l
  · exact h
  · exact List.foldlRecOn _ _ h
      (fun s hs q _ ↦ allocation_inputs_nodup_fighterPayoff P d l q s hs)

/-- `fighterFlushBuffer` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterFlushBuffer
    (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup ((fighterFlushBuffer d l s).getD s) := by
  unfold fighterFlushBuffer
  cases hs : s.activeAt d l
  · exact h
  · simp only [bind, Option.bind_some]
    split
    · exact allocation_inputs_nodup_putPhase d _ s h
    · exact h

/-- `fighterFuelUnit` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterFuelUnit
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (s : FighterState)
    (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterFuelUnit P d l q s) := by
  unfold fighterFuelUnit
  split
  · exact h
  · rename_i phase _
    split
    · rename_i h_cond
      dsimp only
      generalize h_alloc : fighterAllocate d l .fuel (levelUpper l + d) _ _ = res
      cases res
      rename_i next success
      have hnext := allocation_inputs_nodup_fighterAllocate d l .fuel (levelUpper l + d)
        (pairCode (triple q.1 (q.2 - d) phase.candidate.1)
          (fighterFreshString d (phase.indices[(phase.game d).coordinates.idxOf q]?.getD [])))
        (s.putPhase d { phase with controlledRemaining := phase.controlledRemaining - 1 })
        (allocation_inputs_nodup_putPhase d _ s h)
      rw [h_alloc] at hnext
      dsimp only
      split
      · apply allocation_inputs_nodup_fighterFulfillReady
        exact allocation_inputs_nodup_putPhase d _ next hnext
      · exact hnext
    · exact h

/-- `fighterFuelUnits` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterFuelUnits
    (P : FighterParams) (d l : ℕ) (q : Coordinate) (x : ℕ) (s : FighterState)
    (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterFuelUnits P d l q x s) := by
  induction x generalizing s with
  | zero => exact h
  | succ x ih =>
    exact ih _ (allocation_inputs_nodup_fighterFuelUnit P d l q s h)

/-- `fighterStrategyMove` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterStrategyMove
    (P : FighterParams) (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup ((fighterStrategyMove P d l s).getD s) := by
  unfold fighterStrategyMove
  cases h_act : s.activeAt d l <;> dsimp only [bind, Option.bind, Option.getD]
  · exact h
  · rename_i phase
    split_ifs with hc
    · cases h_move : (phase.game d).strategy (phase.official d) <;>
        dsimp only [bind, Option.bind, Option.getD]
      · exact h
      · rename_i move
        split_ifs with hc2
        · set s' := List.foldl (fun s (x : Coordinate × ℕ) ↦
            fighterFuelUnits P d l x.1 (move[x.2]?.getD 0) s)
              s (List.zipIdx (phase.game d).coordinates)
          have h_fold : allocationInputsNodup s' :=
            List.foldlRecOn _ _ h (fun s hs x _ ↦
              allocation_inputs_nodup_fighterFuelUnits P d l x.1 (move[x.2]?.getD 0) s hs)
          change allocationInputsNodup ((match s'.activeAt d l with
            | none => some s'
            | some live => some (s'.putPhase d { live with
                officialCode :=
                    ((phase.game d).afterMove (phase.official d) move).encode })).getD s)
          cases h_act2 : s'.activeAt d l with
          | none => simpa [h_act2] using h_fold
          | some live =>
              simpa [h_act2] using
                allocation_inputs_nodup_putPhase d _ s' h_fold
        · exact h
    · exact h

/-- `fighterLevelAction` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterLevelAction
    (P : FighterParams) (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup ((fighterLevelAction P d l s).getD s) := by
  unfold fighterLevelAction
  cases h_phase : s.activeAt d l with
  | none => exact h
  | some phase =>
    simp only [bind, Option.bind]
    split_ifs with h_dummy
    · exact allocation_inputs_nodup_fighterDummy d l s h
    · cases h_pend : phase.pending.find?
          (fun q ↦ decide (q ∉ s.fulfilled) && fighterSafe P d s.tick q) with
      | some q => exact allocation_inputs_nodup_fighterPayoff P d l q s h
      | none =>
        cases h_flush : fighterFlushBuffer d l s with
        | some next =>
          have h_flush_nodup := allocation_inputs_nodup_fighterFlushBuffer d l s h
          rwa [h_flush, Option.getD_some] at h_flush_nodup
        | none => exact allocation_inputs_nodup_fighterStrategyMove P d l s h

/-- `fighterClosure` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterClosure (P : FighterParams) (d l : ℕ) (x : ℕ)
    (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterClosure P d l x s) := by
  induction x generalizing s with
  | zero => exact h
  | succ x ih =>
    rw [fighterClosure]
    cases h_action : fighterLevelAction P d l s with
    | none => exact h
    | some next =>
      apply ih
      have h1 := allocation_inputs_nodup_fighterLevelAction P d l s h
      rw [h_action] at h1
      exact h1

private lemma allocation_inputs_nodup_fighterCloseLevel
    (P : FighterParams) (d l : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterCloseLevel P d l s) := by
  unfold fighterCloseLevel
  exact allocation_inputs_nodup_fighterClosure P d l _ s h

/-- `fighterOpponent` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighterOpponent
    (P : FighterParams) (d l : ℕ) (e : ProgramEvent) (s : FighterState)
    (h : allocationInputsNodup s) :
    allocationInputsNodup (fighterOpponent P d l e s) := by
  unfold fighterOpponent
  dsimp only
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · split
        · exact allocation_inputs_nodup_fighterCancel d l .opponentExhausted l s h
        · apply allocation_inputs_nodup_fighterFulfillReady
          apply allocation_inputs_nodup_putPhase
          exact h

/-- `fighter_actions` preserves distinctness of allocated inputs. -/
private lemma allocation_inputs_nodup_fighter_actions
    (P : FighterParams) (d tick : ℕ) (s : FighterState) (h : allocationInputsNodup s) :
    allocationInputsNodup (fighter_actions P d tick s) := by
  unfold fighter_actions
  split_ifs with hc
  · dsimp only [allocationInputsNodup]
    dsimp only [initialFighterState]
    exact List.nodup_nil
  · refine List.foldlRecOn _ _ h ?_
    intro s hs l _
    dsimp only [fighterProcessLevel]
    apply allocation_inputs_nodup_fighterCloseLevel
    cases eventAt P.B tick with
    | none => exact allocation_inputs_nodup_fighterFulfillReady P d l s hs
    | some e =>
      dsimp only
      split
      · exact allocation_inputs_nodup_fighterStartPhase P d l _ _
          (allocation_inputs_nodup_fighterFulfillReady P d l s hs)
      · exact allocation_inputs_nodup_fighterOpponent P d l _ _
          (allocation_inputs_nodup_fighterFulfillReady P d l s hs)

/-- Successful allocations never reuse an input, even in a member that later saturates.
Blueprint node `constr:effective`. This unconditional freshness supports small-set counting. -/
theorem fighter_allocations_injective (P : FighterParams) (d tick : ℕ) :
    ((fighterState P d tick).allocated.map AllocatedDirective.input).Nodup := by
  induction tick with
  | zero =>
    dsimp only [fighterState]
    dsimp only [initialFighterState]
    exact List.nodup_nil
  | succ t ih =>
    dsimp only [fighterState]
    exact allocation_inputs_nodup_fighter_actions P d (t + 1) (fighterState P d t) ih

end Kolmogorov.Milovanov
