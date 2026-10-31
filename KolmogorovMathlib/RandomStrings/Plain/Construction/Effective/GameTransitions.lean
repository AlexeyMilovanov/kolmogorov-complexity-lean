/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.CounterGameOperations

/-!
# Computable fighter game transitions

This module implements the game operations needed for blueprint node `constr:effective`.
It proves that fuel expenditure, opponent events, buffer flushing, and controlled strategy
responses are computable on finite fighter records. Allocation and request fulfillment
are supplied as computable maps; `Allocations` combines these results with those maps to
prove computability of the full event transition. The auxiliary results compute phase
indices, funded requests, budgets, and encoded official positions.
-/

namespace Kolmogorov.Milovanov

private theorem primrec_list_zipIdx {α : Type*} [Primcodable α] :
    Primrec (fun l : List α ↦ l.zipIdx) := by
  have hm : Primrec (fun l : List (α × ℕ) ↦ l.map (fun u ↦ (u.1, u.2 + 1))) :=
    Primrec.list_map Primrec.id
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂
  have hs : Primrec₂ (fun (_ : List α)
      (u : α × List α × List (α × ℕ)) ↦
      (u.1, 0) :: u.2.2.map (fun v ↦ (v.1, v.2 + 1))) :=
    (Primrec.list_cons.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.const 0))
      (hm.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hs).of_eq (fun l ↦ by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.zipIdx_cons']
      rw [← ih]
      rfl)

private theorem primrec_list_idxOf
    {α : Type*} [Primcodable α] [BEq α] [LawfulBEq α] :
    Primrec₂ (fun (a : α) (l : List α) ↦ l.idxOf a) := by
  classical
  have hb : (instBEqOfDecidableEq : BEq α) = (inferInstance : BEq α) :=
    lawful_beq_subsingleton _ _
  refine (Primrec.list_idxOf : Primrec₂ (@List.idxOf α instBEqOfDecidableEq)).of_eq ?_
  intro a l
  change @List.idxOf α instBEqOfDecidableEq a l = @List.idxOf α (inferInstance : BEq α) a l
  rw [hb]

private theorem primrec_phase_indices_list :
    Primrec (fun a : FighterPhase × Coordinate ↦
      a.1.indices[(a.1.game 0).coordinates.idxOf a.2]?.getD []) := by
  have hc := primrec_decodeCounterGame_coordinates.comp
    (FighterPhase.primrec_gameCode.comp
      (Primrec.fst : Primrec (Prod.fst : FighterPhase × Coordinate → FighterPhase)))
  have hi := primrec_list_idxOf.comp Primrec.snd hc
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (FighterPhase.primrec_indices.comp Primrec.fst) hi) (Primrec.const [])

private theorem primrec_phase_indices_card :
    Primrec (fun a : FighterPhase × Coordinate ↦ (a.1.indicesAt 0 a.2).card) := by
  have hc := primrec_decodeCounterGame_coordinates.comp
    (FighterPhase.primrec_gameCode.comp
      (Primrec.fst : Primrec (Prod.fst : FighterPhase × Coordinate → FighterPhase)))
  have hm : Primrec (fun a : FighterPhase × Coordinate ↦ decide (a.2 ∈ (a.1.game 0).coordinates)) :=
    (list_mem_decide_primrec.comp Primrec.snd hc).of_eq
      (fun a ↦ by apply decide_eq_decide.mpr; rfl)
  have hcard := Primrec.list_length.comp
    (primrec_eraseDups.comp primrec_phase_indices_list)
  refine (Primrec.ite hm.primrecPred hcard (Primrec.const 0)).of_eq ?_
  intro a
  by_cases h : a.2 ∈ (a.1.game 0).coordinates
  · simp only [h, ↓reduceIte, FighterPhase.indicesAt]
    exact (card_toFinset_eq_length_eraseDups _).symm
  · simp only [h, ↓reduceIte, FighterPhase.indicesAt, Finset.card_empty]

private theorem primrec_phase_price :
    Primrec (fun a : FighterPhase × Coordinate ↦ (a.1.game 0).price a.2) := by
  have hc := primrec_decodeCounterGame_coordinates.comp
    (FighterPhase.primrec_gameCode.comp
      (Primrec.fst : Primrec (Prod.fst : FighterPhase × Coordinate → FighterPhase)))
  have hp : Primrec (fun a : FighterPhase × Coordinate ↦ (a.1.game 0).prices) :=
    Primrec.fst.comp (Primrec.snd.comp
      (FighterPhase.primrec_gameCode.comp Primrec.fst))
  have hi := primrec_list_idxOf.comp Primrec.snd hc
  have hv := Primrec.option_getD.comp (Primrec.list_getElem?.comp hp hi) (Primrec.const 0)
  have hm : Primrec (fun a : FighterPhase × Coordinate ↦ decide (a.2 ∈ (a.1.game 0).coordinates)) :=
    (list_mem_decide_primrec.comp Primrec.snd hc).of_eq
      (fun a ↦ by apply decide_eq_decide.mpr; rfl)
  exact (Primrec.ite hm.primrecPred hv (Primrec.const 0)).of_eq (fun a ↦ rfl)

private theorem primrec_phase_fundRequests :
    Primrec (fun a : FighterPhase × List Coordinate ↦ a.1.fundRequests 0 a.2) := by
  have hc := primrec_decodeCounterGame_coordinates.comp
    (FighterPhase.primrec_gameCode.comp
      (Primrec.fst : Primrec (Prod.fst : FighterPhase × List Coordinate → FighterPhase)))
  have hargs : Primrec (fun a : (FighterPhase × List Coordinate) × Coordinate ↦ (a.1.1, a.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have hfund := Primrec.list_filter hc
    ((Primrec.nat_le.comp
      (primrec_phase_price.comp hargs)
      (primrec_phase_indices_card.comp hargs)).decide).to₂
  have hpend := Primrec.list_append.comp
    (FighterPhase.primrec_pending.comp Primrec.fst) hfund
  have hp : Primrec₂ (fun (a : FighterPhase × List Coordinate) (q : Coordinate) ↦
      decide (q ∉ a.2)) :=
    (Primrec.not.comp (list_mem_decide_primrec.comp
      Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂.of_eq
      (fun a q ↦ by simp)
  have hnew := primrec_eraseDups.comp (Primrec.list_filter hpend hp)
  exact (FighterPhase.primrec_mk
    (FighterPhase.primrec_level.comp Primrec.fst)
    (FighterPhase.primrec_candidate.comp Primrec.fst)
    (FighterPhase.primrec_snapshot.comp Primrec.fst)
    (FighterPhase.primrec_initialAllocations.comp Primrec.fst)
    (FighterPhase.primrec_gameCode.comp Primrec.fst)
    (FighterPhase.primrec_indices.comp Primrec.fst)
    (FighterPhase.primrec_officialCode.comp Primrec.fst)
    (FighterPhase.primrec_liveCounters.comp Primrec.fst)
    (FighterPhase.primrec_controlledRemaining.comp Primrec.fst)
    (FighterPhase.primrec_opponentRemaining.comp Primrec.fst)
    (FighterPhase.primrec_buffer.comp Primrec.fst) hnew
    (FighterPhase.primrec_dummy.comp Primrec.fst)
    (FighterPhase.primrec_dummyIssued.comp Primrec.fst)
    (FighterPhase.primrec_controlledPlayer.comp Primrec.fst)).of_eq (fun a ↦ rfl)

private theorem primrec_phase_unitVector :
    Primrec (fun a : FighterPhase × Coordinate ↦ a.1.unitVector 0 a.2) := by
  have hc := primrec_decodeCounterGame_coordinates.comp
    (FighterPhase.primrec_gameCode.comp
      (Primrec.fst : Primrec (Prod.fst : FighterPhase × Coordinate → FighterPhase)))
  have hp : Primrec₂ (fun (a : FighterPhase × Coordinate) (r : Coordinate) ↦
      if r = a.2 then 1 else 0) :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const 1) (Primrec.const 0)).to₂
  exact (Primrec.list_map hc hp).of_eq (fun a ↦ rfl)

private theorem primrec_phase_insertIndex :
    Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦ a.1.1.insertIndex 0 a.1.2 a.2) := by
  have hp : Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦ a.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc := FighterPhase.primrec_gameCode.comp hp
  have hcoords := primrec_decodeCounterGame_coordinates.comp hc
  have hz := primrec_list_zipIdx.comp hcoords
  have hphase : Primrec (fun a : ((FighterPhase × Coordinate) × BitString) × (Coordinate × ℕ) ↦
      a.1.1.1) := hp.comp Primrec.fst
  have hq : Primrec (fun a : ((FighterPhase × Coordinate) × BitString) × (Coordinate × ℕ) ↦
      a.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hi : Primrec (fun a : ((FighterPhase × Coordinate) × BitString) × (Coordinate × ℕ) ↦
      a.1.2) := Primrec.snd.comp Primrec.fst
  have hposition : Primrec (fun a : ((FighterPhase × Coordinate) × BitString) × (Coordinate × ℕ) ↦
      a.2.2) := Primrec.snd.comp Primrec.snd
  have hold := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (FighterPhase.primrec_indices.comp hphase) hposition)
    (Primrec.const [])
  have hnew := primrec_eraseDups.comp (Primrec.list_concat.comp hold hi)
  have hstep := Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) hq) hnew hold
  have hindices := Primrec.list_map hz hstep.to₂
  have hv := primrec_counterGame_addCounters.comp
    (hc.pair ((FighterPhase.primrec_liveCounters.comp hp).pair
      (primrec_phase_unitVector.comp Primrec.fst)))
  exact (FighterPhase.primrec_mk
    (FighterPhase.primrec_level.comp hp)
    (FighterPhase.primrec_candidate.comp hp)
    (FighterPhase.primrec_snapshot.comp hp)
    (FighterPhase.primrec_initialAllocations.comp hp) hc hindices
    (FighterPhase.primrec_officialCode.comp hp) hv
    (FighterPhase.primrec_controlledRemaining.comp hp)
    (FighterPhase.primrec_opponentRemaining.comp hp)
    (FighterPhase.primrec_buffer.comp hp)
    (FighterPhase.primrec_pending.comp hp)
    (FighterPhase.primrec_dummy.comp hp)
    (FighterPhase.primrec_dummyIssued.comp hp)
    (FighterPhase.primrec_controlledPlayer.comp hp)).of_eq (fun a ↦ rfl)

private theorem primrec_fighterFreshString : Primrec (fighterFreshString 0) := by
  have hs : Primrec₂ (fun (_ : List BitString) (u : ℕ × BitString) ↦ max u.1 u.2.length) :=
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))).to₂
  have hm := Primrec.list_foldl Primrec.id (Primrec.const 0) hs
  exact Primrec.list_replicate.comp (Primrec.succ.comp hm) (Primrec.const false)

private theorem primrec_phase_charge_controlled :
    Primrec (fun p : FighterPhase ↦
      { p with controlledRemaining := p.controlledRemaining - 1 }) := by
  exact (FighterPhase.primrec_mk
    FighterPhase.primrec_level
    FighterPhase.primrec_candidate
    FighterPhase.primrec_snapshot
    FighterPhase.primrec_initialAllocations
    FighterPhase.primrec_gameCode
    FighterPhase.primrec_indices
    FighterPhase.primrec_officialCode
    FighterPhase.primrec_liveCounters
    (Primrec.nat_sub.comp FighterPhase.primrec_controlledRemaining (Primrec.const 1))
    FighterPhase.primrec_opponentRemaining
    FighterPhase.primrec_buffer
    FighterPhase.primrec_pending
    FighterPhase.primrec_dummy
    FighterPhase.primrec_dummyIssued
    FighterPhase.primrec_controlledPlayer).of_eq (fun _ ↦ rfl)

/-- One controlled fuel unit is computable given computable allocation and request fulfillment.
It chooses a fresh index, charges the controlled budget, and allocates the encoded output.
Successful allocation inserts the index and funds requests before checking their safety. -/
theorem computable_fighterFuelUnit (P : FighterParams)
    (halloc : Computable (fun a : ℕ × ℕ × DirectiveKind × ℕ × BitString × FighterState ↦
      fighterAllocate a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2))
    (hfulfill : Computable (fun a : ℕ × ℕ × FighterState ↦
      fighterFulfillReady P a.1 a.2.1 a.2.2)) :
    Computable (fun a : ℕ × ℕ × Coordinate × FighterState ↦
      fighterFuelUnit P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hd : Computable (fun a : ℕ × ℕ × Coordinate × FighterState ↦ a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × Coordinate × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hq : Computable (fun a : ℕ × ℕ × Coordinate × FighterState ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : ℕ × ℕ × Coordinate × FighterState ↦ a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ho := primrec_activeAt.to_comp.comp (hd.pair (hl.pair hs))
  have hb : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦
      if a.1.2.2.1 ∈ (a.2.game a.1.1).coordinates ∧ 0 < a.2.controlledRemaining then
        let old := a.2.indices[(a.2.game a.1.1).coordinates.idxOf a.1.2.2.1]?.getD []
        let index := fighterFreshString a.1.1 old
        let output := pairCode (triple a.1.2.2.1.1 (a.1.2.2.1.2 - a.1.1) a.2.candidate.1) index
        let charged := { a.2 with controlledRemaining := a.2.controlledRemaining - 1 }
        let (next, success) := fighterAllocate a.1.1 a.1.2.1 .fuel
          (levelUpper a.1.2.1 + a.1.1) output (a.1.2.2.2.putPhase a.1.1 charged)
        if success then
          fighterFulfillReady P a.1.1 a.1.2.1
            (next.putPhase a.1.1 ((charged.insertIndex a.1.1 a.1.2.2.1 index).fundRequests
              a.1.1 next.fulfilled))
        else next
      else a.1.2.2.2) := by
    have hd' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦ a.1.1) :=
      hd.comp Computable.fst
    have hl' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦ a.1.2.1) :=
      hl.comp Computable.fst
    have hq' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦
        a.1.2.2.1) :=
      hq.comp Computable.fst
    have hs' : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦
        a.1.2.2.2) :=
      hs.comp Computable.fst
    have hp : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦ a.2) :=
      Computable.snd
    have hc := primrec_decodeCounterGame_coordinates.to_comp.comp
      (FighterPhase.primrec_gameCode.to_comp.comp hp)
    have hmem := list_mem_decide_primrec.to_comp.comp hq' hc
    have hpositive := Primrec.nat_lt.decide.to_comp.comp (Computable.const 0)
      (FighterPhase.primrec_controlledRemaining.to_comp.comp hp)
    have hguard : Computable (fun a : (ℕ × ℕ × Coordinate × FighterState) × FighterPhase ↦
        decide (a.1.2.2.1 ∈ (a.2.game a.1.1).coordinates ∧ 0 < a.2.controlledRemaining)) :=
      (Primrec.and.to_comp.comp hmem hpositive).of_eq
        (fun a ↦ by
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, decide_eq_true_eq, FighterPhase.game]
          exact decide_eq_true_iff.symm)
    have hold := primrec_phase_indices_list.to_comp.comp (hp.pair hq')
    have hindex := primrec_fighterFreshString.to_comp.comp hold
    have hw := Computable.fst.comp (FighterPhase.primrec_candidate.to_comp.comp hp)
    have hbase := triple_computable.1.comp ((Computable.fst.comp hq').pair
      ((Primrec.nat_sub.to_comp.comp (Computable.snd.comp hq') hd').pair hw))
    have hout := Computable₂.comp pairCode_computable hbase hindex
    have hcharged := primrec_phase_charge_controlled.to_comp.comp hp
    have hbefore := computable_putPhase.comp (hd'.pair (hcharged.pair hs'))
    have htarget := Primrec.nat_add.to_comp.comp
      (primrec_levelUpper.to_comp.comp hl') hd'
    have ha := halloc.comp (hd'.pair (hl'.pair ((Computable.const DirectiveKind.fuel).pair
      (htarget.pair (hout.pair hbefore)))))
    have hn := Computable.fst.comp ha
    have hy := Computable.snd.comp ha
    have hinserted := primrec_phase_insertIndex.to_comp.comp
      ((hcharged.pair hq').pair hindex)
    have hfund := primrec_phase_fundRequests.to_comp.comp
      (hinserted.pair (FighterState.primrec_fulfilled.to_comp.comp hn))
    have hpost := computable_putPhase.comp (hd'.pair (hfund.pair hn))
    have hdone := hfulfill.comp (hd'.pair (hl'.pair hpost))
    have hresponse := computable_ite_decide
      (Primrec.eq.decide.to_comp.comp hy (Computable.const true)) hdone hn
    have hraw := computable_ite_decide hguard hresponse hs'
    refine hraw.of_eq ?_
    intro a
    by_cases h : a.1.2.2.1 ∈ (a.2.game a.1.1).coordinates ∧ 0 < a.2.controlledRemaining
    · simp only [h]
      cases hf : fighterAllocate a.1.1 a.1.2.1 .fuel (levelUpper a.1.2.1 + a.1.1)
        (pairCode (triple a.1.2.2.1.1 (a.1.2.2.1.2 - a.1.1) a.2.candidate.1)
          (fighterFreshString a.1.1
            (a.2.indices[(a.2.game a.1.1).coordinates.idxOf a.1.2.2.1]?.getD [])))
        (a.1.2.2.2.putPhase a.1.1 { a.2 with controlledRemaining := a.2.controlledRemaining - 1 })
      simp only [FighterPhase.game, fighterFreshString] at hf ⊢
      simp only [hf]
      all_goals rfl
    · simp only [h, ↓reduceIte]
  exact (Computable.option_casesOn (α := ℕ × ℕ × Coordinate × FighterState)
    (β := FighterPhase) (σ := FighterState) ho hs hb.to₂).of_eq
      (fun a ↦ by unfold fighterFuelUnit; cases a.2.2.2.activeAt a.1 a.2.1 <;> rfl)

/-- A bounded batch of fuel units is computable whenever one fuel unit is computable. -/
theorem computable_fighterFuelUnits (P : FighterParams)
    (hunit : Computable (fun a : ℕ × ℕ × Coordinate × FighterState ↦
      fighterFuelUnit P a.1 a.2.1 a.2.2.1 a.2.2.2)) :
    Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦
      fighterFuelUnits P a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) := by
  have hd : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦ a.1) := Computable.fst
  have hl : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hq : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hn : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦ a.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hs : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦ a.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hh : Computable₂ (fun (a : ℕ × ℕ × Coordinate × ℕ × FighterState)
      (u : ℕ × FighterState) ↦ fighterFuelUnit P a.1 a.2.1 a.2.2.1 u.2) :=
    (hunit.comp ((hd.comp Computable.fst).pair
      ((hl.comp Computable.fst).pair
        ((hq.comp Computable.fst).pair (Computable.snd.comp Computable.snd))))).to₂
  have hr := Computable.nat_rec hn hs hh
  refine hr.of_eq ?_
  intro a
  dsimp only
  have heq : ∀ n s, (fun t ↦ fighterFuelUnit P a.1 a.2.1 a.2.2.1 t)^[n] s =
      fighterFuelUnits P a.1 a.2.1 a.2.2.1 n s := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply, fighterFuelUnits]
      exact ih _
  rw [natRec_eq_iterate]
  exact heq _ _

/-- Decode the curried opponent tuple and check its program length, candidate, retained
coordinate, and exact reconstruction. This applies to arbitrary finite phase records. -/
private theorem computable_fighterOpponentTuple :
    Computable (fun a : ℕ × FighterPhase × ProgramEvent ↦
      fighterOpponentTuple a.1 a.2.1 a.2.2) := by
  let A := ℕ × FighterPhase × ProgramEvent
  have hd : Computable (fun a : A ↦ a.1) := Computable.fst
  have hp : Computable (fun a : A ↦ a.2.1) := Computable.fst.comp Computable.snd
  have he : Computable (fun a : A ↦ a.2.2) := Computable.snd.comp Computable.snd
  have hz := Computable.snd.comp he
  have hlength := Computable.list_length.comp (Computable.fst.comp he)
  have hupper := primrec_levelUpper.to_comp.comp
    (FighterPhase.primrec_level.to_comp.comp hp)
  have hdecode := triple_computable.2.comp (decodeFirst_computable.comp hz)
  have hbranch : Computable (fun a : A × (BitString × ℕ × BitString) ↦
      if a.2.2.2 = a.1.2.1.candidate.1 ∧
          (a.2.1, a.2.2.1 + a.1.1) ∈ (a.1.2.1.game a.1.1).coordinates ∧
          pairCode (triple a.2.1 a.2.2.1 a.2.2.2) (decodeSecond a.1.2.2.2) =
            a.1.2.2.2 then
        some ((a.2.1, a.2.2.1 + a.1.1), decodeSecond a.1.2.2.2)
      else none) := by
    have hx : Computable (fun a : A × (BitString × ℕ × BitString) ↦ a.2.1) :=
      Computable.fst.comp Computable.snd
    have hk : Computable (fun a : A × (BitString × ℕ × BitString) ↦ a.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.snd)
    have hw : Computable (fun a : A × (BitString × ℕ × BitString) ↦ a.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    have hq := hx.pair (Primrec.nat_add.to_comp.comp hk (hd.comp Computable.fst))
    have hcoords : Computable (fun a : A × (BitString × ℕ × BitString) ↦
        (a.1.2.1.game a.1.1).coordinates) :=
      primrec_decodeCounterGame_coordinates.to_comp.comp
      (FighterPhase.primrec_gameCode.to_comp.comp
        (hp.comp Computable.fst))
    have hmem := list_mem_decide_primrec.to_comp.comp hq hcoords
    have hcandidate : Computable (fun a : A × (BitString × ℕ × BitString) ↦
        a.1.2.1.candidate.1) := Computable.fst.comp
      (FighterPhase.primrec_candidate.to_comp.comp
        (hp.comp Computable.fst))
    have hindex : Computable (fun a : A × (BitString × ℕ × BitString) ↦
        decodeSecond a.1.2.2.2) := decodeSecond_computable.comp (hz.comp Computable.fst)
    have htriple := triple_computable.1.comp (hx.pair (hk.pair hw))
    have hpair := Computable₂.comp pairCode_computable htriple hindex
    have hguard : Computable (fun a : A × (BitString × ℕ × BitString) ↦
        decide (a.2.2.2 = a.1.2.1.candidate.1 ∧
          (a.2.1, a.2.2.1 + a.1.1) ∈ (a.1.2.1.game a.1.1).coordinates ∧
          pairCode (triple a.2.1 a.2.2.1 a.2.2.2) (decodeSecond a.1.2.2.2) =
            a.1.2.2.2)) :=
      (Primrec.and.to_comp.comp
        (Primrec.eq.decide.to_comp.comp hw hcandidate)
        (Primrec.and.to_comp.comp hmem
          (Primrec.eq.decide.to_comp.comp hpair (hz.comp Computable.fst)))).of_eq
            (fun a ↦ by
              apply Bool.eq_iff_iff.mpr
              simp only [Bool.and_eq_true, decide_eq_true_iff])
    exact computable_ite_decide hguard
      (Computable.option_some.comp (hq.pair hindex)) (Computable.const none)
  refine (computable_ite_decide
    (Primrec.nat_lt.decide.to_comp.comp hupper hlength) (Computable.const none)
    (Computable.option_bind hdecode hbranch.to₂)).of_eq ?_
  intro a
  unfold fighterOpponentTuple
  by_cases h : levelUpper a.2.1.level < a.2.2.1.length
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    cases hdecode : decodeTriple (decodeFirst a.2.2.2) with
    | none => rfl
    | some t => rcases t with ⟨x, k, w⟩; rfl

/-- Test whether a decoded index already belongs to the retained coordinate's finite set,
including the empty-set default outside the game's coordinates. -/
private theorem primrec_phase_mem_indicesAt :
    Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦
      decide (a.2 ∈ a.1.1.indicesAt 0 a.1.2)) := by
  have hp : Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦ a.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦ a.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hc := primrec_decodeCounterGame_coordinates.comp
    (FighterPhase.primrec_gameCode.comp hp)
  have hcoord : Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦
      decide (a.1.2 ∈ (a.1.1.game 0).coordinates)) :=
    (list_mem_decide_primrec.comp hq hc).of_eq
      (fun a ↦ by apply decide_eq_decide.mpr; rfl)
  have hindex : Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦
      decide (a.2 ∈ a.1.1.indices[(a.1.1.game 0).coordinates.idxOf a.1.2]?.getD [])) :=
    (list_mem_decide_primrec.comp Primrec.snd
      (primrec_phase_indices_list.comp Primrec.fst)).of_eq
        (fun a ↦ by apply decide_eq_decide.mpr; rfl)
  refine (Primrec.ite hcoord.primrecPred hindex (Primrec.const false)).of_eq ?_
  intro a
  apply Bool.eq_iff_iff.mpr
  by_cases h : a.1.2 ∈ (a.1.1.game 0).coordinates
  · simp only [FighterPhase.game] at h
    simp only [FighterPhase.game, h, ↓reduceIte, FighterPhase.indicesAt,
      List.mem_toFinset, decide_eq_true_eq]
    exact decide_eq_true_iff
  · simp only [FighterPhase.game] at h
    simp only [FighterPhase.game, h, ↓reduceIte, Bool.false_eq_true, FighterPhase.indicesAt,
      Finset.notMem_empty, decide_false]

/-- Insert an index, increment the live counters and opponent buffer, and subtract one
opponent budget unit. No freshness or positive-budget assumption is needed to compute it. -/
private theorem primrec_phase_charge_opponent :
    Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦
      { a.1.1.insertIndex 0 a.1.2 a.2 with
        opponentRemaining := a.1.1.opponentRemaining - 1
        buffer := (a.1.1.game 0).addCounters a.1.1.buffer (a.1.1.unitVector 0 a.1.2) }) := by
  have hp : Primrec (fun a : (FighterPhase × Coordinate) × BitString ↦ a.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hi := primrec_phase_insertIndex
  have hb := primrec_counterGame_addCounters.comp
    ((FighterPhase.primrec_gameCode.comp hp).pair
      ((FighterPhase.primrec_buffer.comp hp).pair
        (primrec_phase_unitVector.comp Primrec.fst)))
  have hr := Primrec.nat_sub.comp
    (FighterPhase.primrec_opponentRemaining.comp hp) (Primrec.const 1)
  exact (FighterPhase.primrec_mk
    (FighterPhase.primrec_level.comp hi)
    (FighterPhase.primrec_candidate.comp hi)
    (FighterPhase.primrec_snapshot.comp hi)
    (FighterPhase.primrec_initialAllocations.comp hi)
    (FighterPhase.primrec_gameCode.comp hi)
    (FighterPhase.primrec_indices.comp hi)
    (FighterPhase.primrec_officialCode.comp hi)
    (FighterPhase.primrec_liveCounters.comp hi)
    (FighterPhase.primrec_controlledRemaining.comp hi) hr hb
    (FighterPhase.primrec_pending.comp hi)
    (FighterPhase.primrec_dummy.comp hi)
    (FighterPhase.primrec_dummyIssued.comp hi)
    (FighterPhase.primrec_controlledPlayer.comp hi)).of_eq (fun a ↦ rfl)

/-- For an already decoded coordinate and index, ignore duplicates, cancel on exhaustion,
or charge the insertion, fund requests, replace the phase, and use the supplied fulfillment
map. The supplied phase need not satisfy a reachability invariant. -/
private theorem computable_process_opponent_index
    (P : FighterParams)
    (hfulfill : Computable (fun a : ℕ × ℕ × FighterState ↦
      fighterFulfillReady P a.1 a.2.1 a.2.2)) :
    Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) ×
        (Coordinate × BitString) ↦
      if a.2.2 ∈ a.1.2.indicesAt a.1.1.1 a.2.1 then a.1.1.2.2
      else if a.1.2.opponentRemaining = 0 then
        fighterCancel a.1.1.1 a.1.1.2.1 .opponentExhausted a.1.1.2.1 a.1.1.2.2
      else
        let inserted := a.1.2.insertIndex a.1.1.1 a.2.1 a.2.2
        let next := { inserted with
          opponentRemaining := a.1.2.opponentRemaining - 1
          buffer := (a.1.2.game a.1.1.1).addCounters a.1.2.buffer
            (a.1.2.unitVector a.1.1.1 a.2.1) }
        fighterFulfillReady P a.1.1.1 a.1.1.2.1
          (a.1.1.2.2.putPhase a.1.1.1 (next.fundRequests a.1.1.1 a.1.1.2.2.fulfilled))) := by
  let A := ((ℕ × ℕ × FighterState) × FighterPhase) × (Coordinate × BitString)
  have hd : Computable (fun a : A ↦ a.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hl : Computable (fun a : A ↦ a.1.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hs : Computable (fun a : A ↦ a.1.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hp : Computable (fun a : A ↦ a.1.2) := Computable.snd.comp Computable.fst
  have hq : Computable (fun a : A ↦ a.2.1) := Computable.fst.comp Computable.snd
  have hi : Computable (fun a : A ↦ a.2.2) := Computable.snd.comp Computable.snd
  have hargs := (hp.pair hq).pair hi
  have hmem := primrec_phase_mem_indicesAt.to_comp.comp
    hargs
  have hzero := Primrec.eq.decide.to_comp.comp
    (FighterPhase.primrec_opponentRemaining.to_comp.comp hp)
    (Computable.const 0)
  have hcharged := primrec_phase_charge_opponent.to_comp.comp
    hargs
  have hfund := primrec_phase_fundRequests.to_comp.comp
    (hcharged.pair (FighterState.primrec_fulfilled.to_comp.comp hs))
  have hput := computable_putPhase.comp (hd.pair (hfund.pair hs))
  have hdone := hfulfill.comp (hd.pair (hl.pair hput))
  have hcancel := primrec_fighterCancel.to_comp.comp
    (hd.pair (hl.pair ((Computable.const PhaseEnd.opponentExhausted).pair (hl.pair hs))))
  exact (computable_ite_decide hmem hs
    (computable_ite_decide hzero hcancel hdone)).of_eq (fun a ↦ rfl)

/-- For a supplied phase and event, eliminate the validated tuple option and apply the
computable decoded-index processing map, returning the supplied state on failure. -/
private theorem computable_process_opponent_event
    (P : FighterParams)
    (hfulfill : Computable (fun a : ℕ × ℕ × FighterState ↦
      fighterFulfillReady P a.1 a.2.1 a.2.2)) :
    Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × ProgramEvent ↦
      match fighterOpponentTuple a.1.1.1 a.1.2 a.2 with
      | none => a.1.1.2.2
      | some (q, index) =>
        if index ∈ a.1.2.indicesAt a.1.1.1 q then a.1.1.2.2
        else if a.1.2.opponentRemaining = 0 then
          fighterCancel a.1.1.1 a.1.1.2.1 .opponentExhausted a.1.1.2.1 a.1.1.2.2
        else
          let inserted := a.1.2.insertIndex a.1.1.1 q index
          let next := { inserted with
            opponentRemaining := a.1.2.opponentRemaining - 1
            buffer := (a.1.2.game a.1.1.1).addCounters a.1.2.buffer
              (a.1.2.unitVector a.1.1.1 q) }
          fighterFulfillReady P a.1.1.1 a.1.1.2.1
            (a.1.1.2.2.putPhase a.1.1.1
              (next.fundRequests a.1.1.1 a.1.1.2.2.fulfilled))) := by
  let A := ((ℕ × ℕ × FighterState) × FighterPhase) × ProgramEvent
  have hd : Computable (fun a : A ↦ a.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hp : Computable (fun a : A ↦ a.1.2) := Computable.snd.comp Computable.fst
  have hs : Computable (fun a : A ↦ a.1.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ht := computable_fighterOpponentTuple.comp
    (hd.pair (hp.pair Computable.snd))
  have hprocess : Computable (fun a : A × (Coordinate × BitString) ↦
      ((a.1.1, a.2) : ((ℕ × ℕ × FighterState) × FighterPhase) ×
        (Coordinate × BitString))) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hb := (computable_process_opponent_index P hfulfill).comp
    hprocess
  exact (Computable.option_casesOn ht hs hb.to₂).of_eq (fun a ↦ by
    cases ht : fighterOpponentTuple a.1.1.1 a.1.2 a.2 with
    | none => rfl
    | some qi => rcases qi with ⟨q, index⟩; rfl)

/-- Processing an opponent event is computable given computable request fulfillment.
The transition validates the encoded tuple, ignores duplicates, cancels exhausted phases,
and otherwise charges the insertion and funds requests before checking their safety. -/
theorem computable_fighterOpponent (P : FighterParams)
    (hfulfill : Computable (fun a : ℕ × ℕ × FighterState ↦
      fighterFulfillReady P a.1 a.2.1 a.2.2)) :
    Computable (fun a : ℕ × ℕ × ProgramEvent × FighterState ↦
      fighterOpponent P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  let A := ℕ × ℕ × ProgramEvent × FighterState
  have hd : Computable (fun a : A ↦ a.1) := Computable.fst
  have hl : Computable (fun a : A ↦ a.2.1) := Computable.fst.comp Computable.snd
  have he : Computable (fun a : A ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun a : A ↦ a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hactive := primrec_activeAt.to_comp.comp
    (hd.pair (hl.pair hs))
  have hparams := hd.pair (hl.pair hs)
  have hargs : Computable (fun a : A × FighterPhase ↦
      ((((a.1.1, a.1.2.1, a.1.2.2.2), a.2), a.1.2.2.1) :
        ((ℕ × ℕ × FighterState) × FighterPhase) × ProgramEvent)) :=
    ((hparams.comp Computable.fst).pair Computable.snd).pair (he.comp Computable.fst)
  have hphase := (computable_process_opponent_event P hfulfill).comp
    hargs
  exact (Computable.option_casesOn hactive hs hphase.to₂).of_eq (fun a ↦ by
    unfold fighterOpponent
    cases ha : a.2.2.2.activeAt a.1 a.2.1 with
    | none => rfl
    | some phase =>
      dsimp only
      cases ht : fighterOpponentTuple a.1 phase a.2.2.1 with
      | none => rfl
      | some qi => rcases qi with ⟨q, index⟩; rfl)

private theorem primrec_phase_set_official_buffer :
    Primrec (fun a : FighterPhase × CounterPositionCode × CounterMove ↦
      { a.1 with officialCode := a.2.1, buffer := a.2.2 }) := by
  exact (FighterPhase.primrec_mk
    (FighterPhase.primrec_level.comp Primrec.fst)
    (FighterPhase.primrec_candidate.comp Primrec.fst)
    (FighterPhase.primrec_snapshot.comp Primrec.fst)
    (FighterPhase.primrec_initialAllocations.comp Primrec.fst)
    (FighterPhase.primrec_gameCode.comp Primrec.fst)
    (FighterPhase.primrec_indices.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)
    (FighterPhase.primrec_liveCounters.comp Primrec.fst)
    (FighterPhase.primrec_controlledRemaining.comp Primrec.fst)
    (FighterPhase.primrec_opponentRemaining.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd)
    (FighterPhase.primrec_pending.comp Primrec.fst)
    (FighterPhase.primrec_dummy.comp Primrec.fst)
    (FighterPhase.primrec_dummyIssued.comp Primrec.fst)
    (FighterPhase.primrec_controlledPlayer.comp Primrec.fst)).of_eq (fun a ↦ rfl)

private theorem computable_phase_predicateHolds :
    Computable (fun p : FighterPhase ↦ p.predicateHolds 0) :=
  (computable_counterGame_objective.comp
    (FighterPhase.primrec_gameCode.to_comp.pair
      (FighterPhase.primrec_liveCounters.to_comp.pair
        FighterPhase.primrec_controlledPlayer.to_comp))).of_eq (fun _ ↦ rfl)

private theorem computable_phase_flush_guard :
    Computable (fun p : FighterPhase ↦
      decide (p.predicateHolds 0 = false ∧
        (p.game 0).activePlayer (p.official 0) ≠ p.controlledPlayer ∧
        (p.game 0).LegalMove (p.official 0) p.buffer)) := by
  have hc := FighterPhase.primrec_gameCode.to_comp
  have hp := FighterPhase.primrec_officialCode.to_comp
  have hb := FighterPhase.primrec_buffer.to_comp
  have ha := computable_counterGame_activePlayer.comp (hc.pair hp)
  have hl := computable_counterGame_legalMove.comp (hc.pair (hp.pair hb))
  have h1 := Primrec.eq.decide.to_comp.comp computable_phase_predicateHolds
    (Computable.const false)
  have h2 := Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp ha
    FighterPhase.primrec_controlledPlayer.to_comp)
  exact (Primrec.and.to_comp.comp h1 (Primrec.and.to_comp.comp h2 hl)).of_eq
    (fun p ↦ by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, FighterPhase.game, FighterPhase.official]
      exact decide_eq_true_iff.symm)

private theorem computable_phase_flush :
    Computable (fun p : FighterPhase ↦
      { p with
        officialCode := ((p.game 0).afterMove (p.official 0) p.buffer).encode
        buffer := List.replicate (p.game 0).coordinates.length 0 }) := by
  have hc := FighterPhase.primrec_gameCode.to_comp
  have hp := FighterPhase.primrec_officialCode.to_comp
  have hb := FighterPhase.primrec_buffer.to_comp
  have hchild := computable_counterGame_afterMove.comp (hc.pair (hp.pair hb))
  have hz := Primrec.list_replicate.to_comp.comp
    (Computable.list_length.comp (primrec_decodeCounterGame_coordinates.to_comp.comp hc))
    (Computable.const 0)
  exact (primrec_phase_set_official_buffer.to_comp.comp
    (Computable.id.pair (hchild.pair hz))).of_eq (fun _ ↦ rfl)

/-- Flushing the opponent buffer is computable from the game and position codes.
The transition checks the live predicate, active player, and move legality, then updates
the official position and clears the buffer. -/
theorem computable_fighterFlushBuffer :
    Computable (fun a : ℕ × ℕ × FighterState ↦ fighterFlushBuffer a.1 a.2.1 a.2.2) := by
  have hb : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
      if a.2.predicateHolds a.1.1 = false ∧
          (a.2.game a.1.1).activePlayer (a.2.official a.1.1) ≠ a.2.controlledPlayer ∧
          (a.2.game a.1.1).LegalMove (a.2.official a.1.1) a.2.buffer then
        some (a.1.2.2.putPhase a.1.1 { a.2 with
          officialCode := ((a.2.game a.1.1).afterMove (a.2.official a.1.1) a.2.buffer).encode
          buffer := List.replicate (a.2.game a.1.1).coordinates.length 0 })
      else none) := by
    have hd : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦ a.1.1) :=
      Computable.fst.comp Computable.fst
    have hs : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦ a.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hn : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
        { a.2 with
          officialCode := ((a.2.game 0).afterMove (a.2.official 0) a.2.buffer).encode
          buffer := List.replicate (a.2.game 0).coordinates.length 0 }) :=
      computable_phase_flush.comp Computable.snd
    have hput := computable_putPhase.comp (hd.pair (hn.pair hs))
    exact (computable_ite_decide
      (computable_phase_flush_guard.comp Computable.snd)
      (Computable.option_some.comp hput) (Computable.const none)).of_eq (fun a ↦ rfl)
  exact (Computable.option_bind (α := ℕ × ℕ × FighterState)
    (β := FighterPhase) (σ := FighterState) primrec_activeAt.to_comp
    hb.to₂).of_eq (fun a ↦ rfl)

private theorem computable_phase_strategy :
    Computable (fun p : FighterPhase ↦ (p.game 0).strategy (p.official 0)) := by
  have hi := FighterPhase.primrec_gameCode.to_comp.pair
    FighterPhase.primrec_officialCode.to_comp
  have hs := finite_counter_game_computable_winner.1.comp hi
  refine (Computable.snd.comp hs).of_eq ?_
  intro p
  have hcanonical : (solveCounterGameCode (p.gameCode, p.officialCode)).2 =
      (solveCounterGameCode ((p.game 0).encode, (p.official 0).encode)).2 := by
    rw [solve_counter_game_code_agrees]
    rfl
  change (solveCounterGameCode (p.gameCode, p.officialCode)).2 = _
  rw [hcanonical, solve_counter_game_code_agrees]
  rfl

private theorem computable_phase_strategy_guard :
    Computable (fun p : FighterPhase ↦ decide (p.predicateHolds 0 = false ∧
      p.buffer.sum = 0 ∧ (p.game 0).activePlayer (p.official 0) = p.controlledPlayer)) := by
  have hc := FighterPhase.primrec_gameCode.to_comp
  have hp := FighterPhase.primrec_officialCode.to_comp
  have hactive := computable_counterGame_activePlayer.comp (hc.pair hp)
  have h1 := Primrec.eq.decide.to_comp.comp computable_phase_predicateHolds
    (Computable.const false)
  have h2 := Primrec.eq.decide.to_comp.comp
    (primrec_nat_list_sum.to_comp.comp
      FighterPhase.primrec_buffer.to_comp) (Computable.const 0)
  have h3 := Primrec.eq.decide.to_comp.comp hactive
    FighterPhase.primrec_controlledPlayer.to_comp
  exact (Primrec.and.to_comp.comp h1 (Primrec.and.to_comp.comp h2 h3)).of_eq (fun p ↦ by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, FighterPhase.game, FighterPhase.official]
    exact decide_eq_true_iff.symm)

private theorem computable_phase_move_guard :
    Computable (fun a : FighterPhase × CounterMove ↦ decide
      ((a.1.game 0).LegalMove (a.1.official 0) a.2 ∧ a.2.sum ≤ a.1.controlledRemaining)) := by
  have hc := FighterPhase.primrec_gameCode.to_comp.comp
    (Computable.fst : Computable (Prod.fst : FighterPhase × CounterMove → FighterPhase))
  have hp := FighterPhase.primrec_officialCode.to_comp.comp
    (Computable.fst : Computable (Prod.fst : FighterPhase × CounterMove → FighterPhase))
  have h1 := computable_counterGame_legalMove.comp (hc.pair (hp.pair Computable.snd))
  have h2 := Primrec.nat_le.decide.to_comp.comp
    (primrec_nat_list_sum.to_comp.comp Computable.snd)
    (FighterPhase.primrec_controlledRemaining.to_comp.comp Computable.fst)
  exact (Primrec.and.to_comp.comp h1 h2).of_eq (fun a ↦ by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, FighterPhase.game, FighterPhase.official]
    exact decide_eq_true_iff.symm)

private theorem computable_strategy_fuel_batch (P : FighterParams)
    (hunits : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦
      fighterFuelUnits P a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)) :
    Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦
      (a.1.2.game 0).coordinates.zipIdx.foldl (fun s qi ↦
        fighterFuelUnits P a.1.1.1 a.1.1.2.1 qi.1 (a.2[qi.2]?.getD 0) s) a.1.1.2.2) := by
  have hphase : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦
      a.1.2) :=
    Computable.snd.comp Computable.fst
  have hcoords := primrec_decodeCounterGame_coordinates.to_comp.comp
    (FighterPhase.primrec_gameCode.to_comp.comp hphase)
  have hlist := primrec_list_zipIdx.to_comp.comp hcoords
  have hstate : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦
      a.1.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hd : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
      (FighterState × (Coordinate × ℕ)) ↦ a.1.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hl : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
      (FighterState × (Coordinate × ℕ)) ↦ a.1.1.1.2.1) :=
    Computable.fst.comp
      (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
  have hq : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
      (FighterState × (Coordinate × ℕ)) ↦ a.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
      (FighterState × (Coordinate × ℕ)) ↦ a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hm : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
      (FighterState × (Coordinate × ℕ)) ↦ a.1.2) := Computable.snd.comp Computable.fst
  have hs : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
      (FighterState × (Coordinate × ℕ)) ↦ a.2.1) := Computable.fst.comp Computable.snd
  have hn := Computable.option_getD (Computable.list_getElem?.comp hm hi) (Computable.const 0)
  have hstep : Computable₂ (fun
      (a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove)
      (u : FighterState × (Coordinate × ℕ)) ↦
      fighterFuelUnits P a.1.1.1 a.1.1.2.1 u.2.1 (a.2[u.2.2]?.getD 0) u.1) :=
    (hunits.comp (hd.pair (hl.pair (hq.pair (hn.pair hs))))).to₂
  exact (Computable.list_foldl hlist hstate hstep).of_eq (fun a ↦ rfl)

private theorem computable_strategy_response (P : FighterParams)
    (hunits : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦
      fighterFuelUnits P a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)) :
    Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦
      let next := (a.1.2.game 0).coordinates.zipIdx.foldl (fun s qi ↦
        fighterFuelUnits P a.1.1.1 a.1.1.2.1 qi.1 (a.2[qi.2]?.getD 0) s) a.1.1.2.2
      match next.activeAt a.1.1.1 a.1.1.2.1 with
      | none => some next
      | some live => some (next.putPhase a.1.1.1
          { live with
            officialCode := ((a.1.2.game 0).afterMove (a.1.2.official 0) a.2).encode })) := by
  have hd : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦ a.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hl : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦
      a.1.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hp : Computable (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦ a.1.2) :=
    Computable.snd.comp Computable.fst
  have hn := computable_strategy_fuel_batch P hunits
  have ho := primrec_activeAt.to_comp.comp (hd.pair (hl.pair hn))
  have hc := computable_counterGame_afterMove.comp
    ((FighterPhase.primrec_gameCode.to_comp.comp hp).pair
      ((FighterPhase.primrec_officialCode.to_comp.comp hp).pair Computable.snd))
  have hs : Computable₂ (fun
      (a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) (live : FighterPhase) ↦
      some (((a.1.2.game 0).coordinates.zipIdx.foldl (fun s qi ↦
        fighterFuelUnits P a.1.1.1 a.1.1.2.1 qi.1 (a.2[qi.2]?.getD 0) s) a.1.1.2.2).putPhase a.1.1.1
          { live with
            officialCode := ((a.1.2.game 0).afterMove (a.1.2.official 0) a.2).encode })) := by
    have hup : Computable (fun a : (((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove) ×
        FighterPhase ↦
        { a.2 with
          officialCode := ((a.1.1.2.game 0).afterMove (a.1.1.2.official 0) a.1.2).encode }) :=
      (primrec_phase_set_official_buffer.to_comp.comp
        (Computable.snd.pair ((hc.comp Computable.fst).pair
          (FighterPhase.primrec_buffer.to_comp.comp Computable.snd)))).of_eq
            (fun a ↦ rfl)
    exact (Computable.option_some.comp (computable_putPhase.comp
      ((hd.comp Computable.fst).pair (hup.pair (hn.comp Computable.fst))))).to₂
  exact (Computable.option_casesOn ho (Computable.option_some.comp hn) hs).of_eq (fun a ↦ by
    dsimp only
    cases ((a.1.2.game 0).coordinates.zipIdx.foldl (fun s qi ↦
      fighterFuelUnits P a.1.1.1 a.1.1.2.1 qi.1 (a.2[qi.2]?.getD 0) s) a.1.1.2.2).activeAt
        a.1.1.1 a.1.1.2.1 <;> rfl)

/-- A controlled strategy response is computable given computable bounded fuel batches.
The transition uses `solveCounterGameCode` to select a move, checks legality and
affordability, spends fuel along the coordinates, and updates the surviving phase's
official position. -/
theorem computable_fighterStrategyMove (P : FighterParams)
    (hunits : Computable (fun a : ℕ × ℕ × Coordinate × ℕ × FighterState ↦
      fighterFuelUnits P a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)) :
    Computable (fun a : ℕ × ℕ × FighterState ↦
      fighterStrategyMove P a.1 a.2.1 a.2.2) := by
  have hbody : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
      if a.2.predicateHolds a.1.1 = false ∧ a.2.buffer.sum = 0 ∧
          (a.2.game a.1.1).activePlayer (a.2.official a.1.1) = a.2.controlledPlayer then do
        let move ← (a.2.game a.1.1).strategy (a.2.official a.1.1)
        if (a.2.game a.1.1).LegalMove (a.2.official a.1.1) move ∧
            move.sum ≤ a.2.controlledRemaining then
          let next := (a.2.game a.1.1).coordinates.zipIdx.foldl (fun s qi ↦
            fighterFuelUnits P a.1.1 a.1.2.1 qi.1 (move[qi.2]?.getD 0) s) a.1.2.2
          match next.activeAt a.1.1 a.1.2.1 with
          | none => some next
          | some live => some (next.putPhase a.1.1 { live with
              officialCode := ((a.2.game a.1.1).afterMove (a.2.official a.1.1) move).encode })
        else none
      else none) := by
    have hm : Computable (fun a : (ℕ × ℕ × FighterState) × FighterPhase ↦
        (a.2.game 0).strategy (a.2.official 0)) :=
      computable_phase_strategy.comp Computable.snd
    have hargs : Computable
        (fun a : ((ℕ × ℕ × FighterState) × FighterPhase) × CounterMove ↦ (a.1.2, a.2)) :=
      (Computable.snd.comp Computable.fst).pair Computable.snd
    have hg := computable_phase_move_guard.comp hargs
    have hresponse := computable_ite_decide hg
      (computable_strategy_response P hunits) (Computable.const none)
    have hselected := Computable.option_bind hm hresponse.to₂
    exact (computable_ite_decide
      (computable_phase_strategy_guard.comp Computable.snd)
      hselected (Computable.const none)).of_eq (fun a ↦ rfl)
  exact (Computable.option_bind (α := ℕ × ℕ × FighterState)
    (β := FighterPhase) (σ := FighterState) primrec_activeAt.to_comp
    hbody.to₂).of_eq (fun a ↦ rfl)

end Kolmogorov.Milovanov
