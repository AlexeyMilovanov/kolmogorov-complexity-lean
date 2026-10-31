/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.ConstructionTransitions

/-!
# Computable operations on encoded counter games

For blueprint node `constr:effective`, the fighter must evaluate game predicates and
update positions from finite codes. This module proves primitive recursiveness of the
coordinate and counter operations, and computability of objectives, active players,
move legality, and successor positions. `GameTransitions` uses these facts to implement
fuel expenditure, opponent events, buffer flushing, and strategy responses.
-/

namespace Kolmogorov.Milovanov

/-- Decoding the finite list of game coordinates is primitive recursive. -/
theorem primrec_decodeCounterGame_coordinates :
    Primrec (fun c : CounterGameCode ↦ (decodeCounterGame c).coordinates) :=
  primrec_eraseDups.comp Primrec.fst

private theorem primrec_decodeCounterGame_budget :
    Primrec (fun c : CounterGameCode ↦ (decodeCounterGame c).budget) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.id))))

private theorem primrec_decodeCounterGame_equalityPlayer :
    Primrec (fun c : CounterGameCode ↦ (decodeCounterGame c).equalityPlayer) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))

/-- Summing a finite list of natural numbers is primitive recursive. -/
theorem primrec_nat_list_sum : Primrec (List.sum : List ℕ → ℕ) := by
  have hs : Primrec₂ (fun (_ : List ℕ) (u : ℕ × ℕ) ↦ u.1 + u.2) :=
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hs).of_eq (fun l ↦ by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.sum_cons]
      exact congrArg (fun n ↦ a + n) ih)

/-- Adding a move to a counter vector is primitive recursive in the game code. -/
theorem primrec_counterGame_addCounters :
    Primrec (fun a : CounterGameCode × List ℕ × CounterMove ↦
      (decodeCounterGame a.1).addCounters a.2.1 a.2.2) := by
  have hlen : Primrec (fun a : CounterGameCode × List ℕ × CounterMove ↦
      (decodeCounterGame a.1).coordinates.length) :=
    Primrec.list_length.comp (primrec_decodeCounterGame_coordinates.comp Primrec.fst)
  have hv : Primrec (fun a : (CounterGameCode × List ℕ × CounterMove) × ℕ ↦ a.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hm : Primrec (fun a : (CounterGameCode × List ℕ × CounterMove) × ℕ ↦ a.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun a : (CounterGameCode × List ℕ × CounterMove) × ℕ ↦ a.2) := Primrec.snd
  have hv' := Primrec.option_getD.comp (Primrec.list_getElem?.comp hv hi) (Primrec.const 0)
  have hm' := Primrec.option_getD.comp (Primrec.list_getElem?.comp hm hi) (Primrec.const 0)
  exact (Primrec.list_map (Primrec.list_range.comp hlen)
    (Primrec.nat_add.comp hv' hm').to₂).of_eq (fun a ↦ rfl)

/-- The objective of either player is computable from the game code and counter vector. -/
theorem computable_counterGame_objective :
    Computable (fun a : CounterGameCode × List ℕ × Bool ↦
      (decodeCounterGame a.1).objective a.2.2
        ((decodeCounterGame a.1).referee.eval ((decodeCounterGame a.1).counterAnswer a.2.1))) := by
  have hc : Computable (fun a : CounterGameCode × List ℕ × Bool ↦ a.1) :=
    Computable.fst
  have hv : Computable (fun a : CounterGameCode × List ℕ × Bool ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hp : Computable (fun a : CounterGameCode × List ℕ × Bool ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have ht := computable_counterGameTargetReached.comp (hc.pair hv)
  have he := primrec_decodeCounterGame_equalityPlayer.to_comp.comp hc
  have hraw := Computable.cond (Primrec.eq.decide.to_comp.comp hp he)
    ht (Primrec.not.to_comp.comp ht)
  refine hraw.of_eq ?_
  intro a
  by_cases h : a.2.2 = (decodeCounterGame a.1).equalityPlayer
  · simp [FiniteCounterGame.objective, h]
  · simp [FiniteCounterGame.objective, h]

/-- The active player is computable from the game and position codes. -/
theorem computable_counterGame_activePlayer :
    Computable (fun a : CounterGameCode × CounterPositionCode ↦
      (decodeCounterGame a.1).activePlayer
        (decodeCounterPosition (decodeCounterGame a.1) a.2)) := by
  have hc : Computable (fun a : CounterGameCode × CounterPositionCode ↦ a.1) :=
    Computable.fst
  have hv : Computable (fun a : CounterGameCode × CounterPositionCode ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have ht := computable_counterGameTargetReached.comp (hc.pair hv)
  have he := primrec_decodeCounterGame_equalityPlayer.to_comp.comp hc
  have hraw := Computable.cond ht (Primrec.not.to_comp.comp he) he
  refine hraw.of_eq ?_
  intro a
  by_cases h : (decodeCounterGame a.1).referee.eval
      ((decodeCounterGame a.1).counterAnswer a.2.1) = (decodeCounterGame a.1).target
  · simp [FiniteCounterGame.activePlayer, FiniteCounterGame.output, decodeCounterPosition, h]
  · simp [FiniteCounterGame.activePlayer, FiniteCounterGame.output, decodeCounterPosition, h]

/-- Legality of a proposed move is decidable computably from the game and position codes. -/
theorem computable_counterGame_legalMove :
    Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦
      decide ((decodeCounterGame a.1).LegalMove
        (decodeCounterPosition (decodeCounterGame a.1) a.2.1) a.2.2)) := by
  have hc : Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦ a.1) :=
    Computable.fst
  have hp : Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hm : Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have hb := primrec_decodeCounterGame_budget.to_comp.comp hc
  have hl := Primrec.nat_min.to_comp.comp (Computable.fst.comp (Computable.snd.comp hp)) hb
  have hr := Primrec.nat_min.to_comp.comp (Computable.snd.comp (Computable.snd.comp hp)) hb
  have hs := primrec_nat_list_sum.to_comp.comp hm
  have hactive := computable_counterGame_activePlayer.comp (hc.pair hp)
  have hremaining := Computable.cond hactive hr hl
  have hadded := primrec_counterGame_addCounters.to_comp.comp
    (hc.pair ((Computable.fst.comp hp).pair hm))
  have hobj := computable_counterGame_objective.comp (hc.pair (hadded.pair hactive))
  have hlen := Primrec.eq.decide.to_comp.comp (Computable.list_length.comp hm)
    (Computable.list_length.comp (primrec_decodeCounterGame_coordinates.to_comp.comp hc))
  have hpositive := Primrec.nat_lt.decide.to_comp.comp (Computable.const 0) hs
  have haffordable := Primrec.nat_le.decide.to_comp.comp hs hremaining
  have hsuccess := Primrec.eq.decide.to_comp.comp hobj (Computable.const true)
  have hraw := Primrec.and.to_comp.comp hlen
    (Primrec.and.to_comp.comp hpositive (Primrec.and.to_comp.comp haffordable hsuccess))
  refine hraw.of_eq ?_
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  cases h : (decodeCounterGame a.1).activePlayer
      (decodeCounterPosition (decodeCounterGame a.1) a.2.1) <;>
    dsimp only [decodeCounterPosition] at h <;>
    simp [FiniteCounterGame.LegalMove, CounterPosition.remaining, decodeCounterPosition, h]

/-- The encoded position after a move is computable from the game and position codes. -/
theorem computable_counterGame_afterMove :
    Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦
      ((decodeCounterGame a.1).afterMove
        (decodeCounterPosition (decodeCounterGame a.1) a.2.1) a.2.2).encode) := by
  have hc : Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦ a.1) :=
    Computable.fst
  have hp : Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦ a.2.1) :=
    Computable.fst.comp Computable.snd
  have hm : Computable (fun a : CounterGameCode × CounterPositionCode × CounterMove ↦ a.2.2) :=
    Computable.snd.comp Computable.snd
  have hb := primrec_decodeCounterGame_budget.to_comp.comp hc
  have hl := Primrec.nat_min.to_comp.comp (Computable.fst.comp (Computable.snd.comp hp)) hb
  have hr := Primrec.nat_min.to_comp.comp (Computable.snd.comp (Computable.snd.comp hp)) hb
  have hs := primrec_nat_list_sum.to_comp.comp hm
  have hactive := computable_counterGame_activePlayer.comp (hc.pair hp)
  have hadded := primrec_counterGame_addCounters.to_comp.comp
    (hc.pair ((Computable.fst.comp hp).pair hm))
  have hleft := Primrec.nat_sub.to_comp.comp hl (Computable.cond hactive (Computable.const 0) hs)
  have hright := Primrec.nat_sub.to_comp.comp hr (Computable.cond hactive hs (Computable.const 0))
  refine (hadded.pair (hleft.pair hright)).of_eq ?_
  intro a
  cases h : (decodeCounterGame a.1).activePlayer
      (decodeCounterPosition (decodeCounterGame a.1) a.2.1) <;>
    dsimp only [decodeCounterPosition] at h <;>
    simp [FiniteCounterGame.afterMove, CounterPosition.encode, decodeCounterPosition, h]

end Kolmogorov.Milovanov
