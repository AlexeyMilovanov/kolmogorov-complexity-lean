/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Geometric.Defs
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

namespace Kolmogorov

open scoped ENNReal
open Computability

/-
Computability of the `geomCross` decision in `(l, s, o, ctx)`.
-/
lemma geomCross_decide_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun q : ℕ × ℕ × BitString × BitString =>
      decide (geomCross approx q.2.2.1 q.2.2.2 q.1 q.2.1)) := by
  have hdec : Computable (fun q : ℕ × ℕ × BitString × BitString => decide (2 ^ q.2.1 ≤ approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ (q.1 - 1))) := by
    have hdec : Computable (fun q : ℕ × ℕ × BitString × BitString => approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ (q.1 - 1)) := by
      apply Computable.comp (Primrec.nat_mul.to_comp) (Computable.pair _ _);
      · convert hcomp.comp ( Computable.snd ) using 1;
      · convert primrec_two_pow.to_comp.comp ( Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.const 1 ) |> Primrec.to_comp ) using 1;
    have hdec : Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      convert Primrec.nat_le using 1;
      constructor <;> intro h <;> simp_all +decide [ PrimrecPred, PrimrecRel ];
      · exact ⟨ inferInstance, h ⟩;
      · grind;
    convert hdec.to_comp.comp ( Computable.pair ( primrec_two_pow.to_comp.comp ( Computable.fst.comp ( Computable.snd ) ) ) ‹Computable fun q : ℕ × ℕ × BitString × BitString => approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ ( q.1 - 1 ) › ) using 1;
  have hdec : Computable (fun q : ℕ × ℕ × BitString × BitString => decide (1 ≤ q.1)) := by
    have hdec : Computable (fun q : ℕ => decide (1 ≤ q)) := by
      convert Computable.of_eq _ _;
      exact fun n => Nat.recOn n Bool.false fun _ _ => Bool.true;
      · exact Computable.nat_casesOn ( Computable.id ) ( Computable.const false ) ( Computable.const true );
      · rintro ( _ | _ ) <;> simp +decide;
    exact hdec.comp ( Computable.fst );
  rename_i h;
  convert Computable.cond hdec h ( Computable.const false ) using 1;
  ext; simp [geomCross]

/-- The geometric request stream is computable (uniformly in `ctx`). -/
lemma geomReq_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : BitString × ℕ => geomReq approx p.1 p.2) := by
  change Computable (fun p : BitString × ℕ => (evOut (Nat.unpair p.2).1).bind fun o => geomReqBody approx (p, o))
  have hl : Computable (fun p : BitString × ℕ => (Nat.unpair p.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have hevK_primrec : Primrec evK := by
    unfold evK
    exact Primrec.snd.comp Primrec.unpair
  have hs : Computable (fun p : BitString × ℕ => evK (Nat.unpair p.2).1) :=
    hevK_primrec.to_comp.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hevOut : Computable (fun p : BitString × ℕ => evOut (Nat.unpair p.2).1) :=
    evOut_computable.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hcond1 : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1))) := by
    have h_cross := geomCross_decide_computable approx hcomp
    have h_args : Computable (fun p : (BitString × ℕ) × BitString => (((Nat.unpair p.1.2).2), (evK (Nat.unpair p.1.2).1), p.2, p.1.1)) :=
      Computable.pair (hl.comp Computable.fst) (Computable.pair (hs.comp Computable.fst) (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
    exact (h_cross.comp h_args).of_eq (fun p => by dsimp only [Prod.fst, Prod.snd])
  have h_cross_eval : Computable (fun p : (BitString × ℕ) × BitString => decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1))) := by
    have h_cross := geomCross_decide_computable approx hcomp
    have hsub : Computable (fun p : (BitString × ℕ) × BitString => evK (Nat.unpair p.1.2).1 - 1) := by
      have h_sub_primrec : Primrec (fun n : ℕ => n - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
      exact h_sub_primrec.to_comp.comp (hs.comp Computable.fst)
    have h_args : Computable (fun p : (BitString × ℕ) × BitString => (((Nat.unpair p.1.2).2), (evK (Nat.unpair p.1.2).1 - 1), p.2, p.1.1)) :=
      Computable.pair (hl.comp Computable.fst) (Computable.pair hsub (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
    exact (h_cross.comp h_args).of_eq (fun p => by dsimp only [Prod.fst, Prod.snd])
  have heq0 : Computable (fun p : (BitString × ℕ) × BitString => decide (evK (Nat.unpair p.1.2).1 = 0)) := by
    have hsucc : Computable₂ (fun (n : ℕ) (m : ℕ) => false) := Computable.const false
    have h_dec : Computable (fun n : ℕ => decide (n = 0)) :=
      Computable.of_eq (Computable.nat_casesOn Computable.id (Computable.const true) hsucc) (by intro n; cases n <;> rfl)
    exact h_dec.comp (hs.comp Computable.fst)
  have hcond2 : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (evK (Nat.unpair p.1.2).1 = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1))) := by
    have h_not : Computable (fun p : (BitString × ℕ) × BitString => cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1))) false true) :=
      Computable.cond h_cross_eval (Computable.const false) (Computable.const true)
    have h_or : Computable (fun p : (BitString × ℕ) × BitString => cond (decide (evK (Nat.unpair p.1.2).1 = 0)) true (cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1))) false true)) :=
      Computable.cond heq0 (Computable.const true) h_not
    exact h_or.of_eq (fun p => decide_or_not_eq.symm)
  have hcond : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
              (evK (Nat.unpair p.1.2).1 = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1)))) := by
    have h_and : Computable (fun p : (BitString × ℕ) × BitString => cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1))) (decide (evK (Nat.unpair p.1.2).1 = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1))) false) :=
      Computable.cond hcond1 hcond2 (Computable.const false)
    exact h_and.of_eq (fun p => decide_and_eq.symm)
  have hbranch : Computable (fun p : (BitString × ℕ) × BitString => geomReqBody approx p) := by
    have h_then : Computable (fun p : (BitString × ℕ) × BitString => some (p.2, ((Nat.unpair p.1.2).2))) :=
      Computable.option_some.comp (Computable.pair Computable.snd (hl.comp Computable.fst))
    have h_else : Computable (fun p : (BitString × ℕ) × BitString => (none : Option (BitString × ℕ))) :=
      Computable.const none
    have h_ite : Computable (fun p : (BitString × ℕ) × BitString => cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧ (evK (Nat.unpair p.1.2).1 = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1 - 1)))) (some (p.2, ((Nat.unpair p.1.2).2))) none) :=
      Computable.cond hcond h_then h_else
    exact h_ite.of_eq (fun p => by
      rw [geomReqBody_eq]
      exact ite_eq_some.symm)
  exact Computable.option_bind hevOut hbranch


end Kolmogorov
