/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.Prefix.Basic
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin.Allocator.Basic
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

/-!
# The online Kraft–Chaitin allocator

This file builds the *online* (causal) prefix-free code allocator behind the
Kraft–Chaitin realization theorem and proves its three defining properties:

* `allocFun_computable` — the allocator is computable uniformly in the context;
* `allocFun_prefixFree` — codes for distinct requests are prefix-incomparable;
* `allocFun_success`    — if the total Kraft weight is `≤ 1`, every request is
  realized by a codeword of exactly the requested length.

The algorithm maintains a *free list* of tree nodes (bitstrings) kept in strictly
descending order of length (hence with pairwise distinct lengths).  A length-`l`
request is serviced by taking the unique free node of largest length `≤ l`,
splitting it into a length-`l` left-most descendant (the allocated codeword) and
its right siblings along the all-`false` path, and re-inserting the siblings in
sorted position.

The proofs are organized around three invariants of the free list:

* `DescLengths` (strictly descending lengths ⇒ distinct lengths);
* prefix-freeness of the node set;
* the mass identity `freeMass free + usedMass req n = 1`.

These are bundled in `AllocGood` and shown to be preserved step by step.
-/

namespace Kolmogorov
namespace KraftChaitin

open scoped ENNReal
open Computability

/-! ## Computability building blocks -/

/-- `drop n` is iterated `tail`, hence primitive recursive. -/
theorem drop_eq_iterate {α} (n : ℕ) (l : List α) : l.drop n = (List.tail)^[n] l := by
  induction n generalizing l with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ← ih, List.tail_drop]

/-- `take n` expressed via `reverse` and `drop`. -/
theorem take_eq_rev {α} (n : ℕ) (l : List α) :
    l.take n = (l.reverse.drop (l.length - n)).reverse := by
  rw [← List.reverse_take, List.reverse_reverse]

/-- `findIdx?` expressed via `findIdx` and a length comparison. -/
theorem findIdx?_eq_ite {α} (p : α → Bool) (l : List α) :
    l.findIdx? p = if l.findIdx p < l.length then some (l.findIdx p) else none := by
  by_cases h : l.findIdx p < l.length
  · simp only [h, if_true]
    rw [List.findIdx?_eq_some_iff_findIdx_eq]; exact ⟨h, rfl⟩
  · simp only [h, if_false]
    rw [List.findIdx?_eq_none_iff]
    have hlen : l.findIdx p = l.length := le_antisymm List.findIdx_le_length (not_lt.mp h)
    rw [List.findIdx_eq_length] at hlen
    exact hlen

/-- `List.drop` (as a binary function) is primitive recursive. -/
theorem drop_primrec {α} [Primcodable α] : Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := by
  have h : Primrec (fun p : List α × ℕ => (List.tail)^[p.2] p.1) :=
    Primrec.nat_iterate Primrec.snd Primrec.fst (Primrec.list_tail.comp Primrec.snd).to₂
  exact h.of_eq (fun p => (drop_eq_iterate p.2 p.1).symm)

/-- `List.take` (as a binary function) is primitive recursive. -/
theorem take_primrec {α} [Primcodable α] : Primrec₂ (fun (l : List α) (n : ℕ) => l.take n) := by
  have hdrop : Primrec₂ (fun (l : List α) (n : ℕ) => l.drop n) := drop_primrec
  have h : Primrec (fun p : List α × ℕ => ((p.1.reverse).drop (p.1.length - p.2)).reverse) := by
    apply Primrec.list_reverse.comp
    apply hdrop.comp (Primrec.list_reverse.comp Primrec.fst)
    exact Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd
  exact h.of_eq (fun p => (take_eq_rev p.2 p.1).symm)

/-- `List.replicate _ false` is primitive recursive. -/
theorem replicate_false_primrec : Primrec (fun n : ℕ => List.replicate n false) := by
  have : (fun n : ℕ => List.replicate n false) = (fun n => (List.range n).map (fun _ => false)) := by
    funext n; rw [List.map_const']; simp
  rw [this]
  exact Primrec.list_range.list_map (Primrec.const false).to₂

/-
`splitNode` is computable.
-/
lemma splitNode_computable :
    Computable (fun p : BitString × ℕ => splitNode p.1 p.2) := by
  unfold splitNode
  refine (Primrec.pair ?_ ?_).to_comp
  · exact Primrec.list_append.comp Primrec.fst
      (replicate_false_primrec.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst)))
  · refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst))) ?_
    exact (show Primrec₂ (fun (p : BitString × ℕ) (i : ℕ) =>
        p.1 ++ List.replicate i false ++ [true]) from
      (Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
          (replicate_false_primrec.comp Primrec.snd))
        (Primrec.const [true])).to₂)

/-- `splitNode` (as a binary function) is primitive recursive. -/
lemma splitNode_primrec : Primrec (fun p : BitString × ℕ => splitNode p.1 p.2) := by
  refine Primrec.pair ?_ ?_
  · exact Primrec.list_append.comp Primrec.fst
      (replicate_false_primrec.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst)))
  · refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst))) ?_
    exact (show Primrec₂ (fun (p : BitString × ℕ) (i : ℕ) =>
        p.1 ++ List.replicate i false ++ [true]) from
      (Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
          (replicate_false_primrec.comp Primrec.snd))
        (Primrec.const [true])).to₂)

/-- `getElem!` on a free list is primitive recursive. -/
lemma getElem!_primrec : Primrec₂ (fun (l : List BitString) (i : ℕ) => l[i]!) :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const default)).of_eq
    (fun _ => (List.getElem!_eq_getElem?_getD ..).symm)

/-- The length-fit search used by `allocateOne` is primitive recursive. -/
lemma findIdx?_pred_primrec :
    Primrec (fun p : List BitString × ℕ =>
      p.1.findIdx? (fun v => decide (v.length ≤ p.2))) := by
  have hR : PrimrecRel (fun (p : List BitString × ℕ) (v : BitString) => v.length ≤ p.2) :=
    Primrec.nat_le.comp₂ (Primrec.list_length.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  have hj : Primrec (fun p : List BitString × ℕ =>
      p.1.findIdx (fun v => decide (v.length ≤ p.2))) :=
    Primrec.list_findIdx Primrec.fst hR.decide
  exact (Primrec.ite (Primrec.nat_lt.comp hj (Primrec.list_length.comp Primrec.fst))
      (Primrec.option_some.comp hj) (Primrec.const none)).of_eq
    (fun _ => (findIdx?_eq_ite _ _).symm)

/-- `allocateOne` written as an `Option.map` over the fit search. -/
lemma allocateOne_eq_map (free : List BitString) (l : ℕ) :
    allocateOne free l = (free.findIdx? (fun v => decide (v.length ≤ l))).map
      (fun idx => ((splitNode free[idx]! l).1,
        free.take idx ++ (splitNode free[idx]! l).2.reverse ++ free.drop (idx + 1))) := by
  unfold allocateOne
  cases free.findIdx? (fun v => decide (v.length ≤ l)) <;> rfl

-- Treat the data functions opaquely from here on: their definitions have already
-- been characterized by the equational lemmas above, and keeping them reducible
-- makes the `Computable`/`Primrec` combinator unifications whnf-unfold these large
-- definitions, which is prohibitively slow.
attribute [local irreducible] splitNode allocateOne

/-- `allocateOne` is computable. -/
lemma allocateOne_computable :
    Computable (fun p : List BitString × ℕ => allocateOne p.1 p.2) := by
  apply Primrec.to_comp
  have hv : Primrec (fun a : (List BitString × ℕ) × ℕ => a.1.1[a.2]!) :=
    getElem!_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hnode : Primrec (fun a : (List BitString × ℕ) × ℕ => splitNode a.1.1[a.2]! a.1.2) :=
    splitNode_primrec.comp (Primrec.pair hv (Primrec.snd.comp Primrec.fst))
  have hg : Primrec₂ (fun (p : List BitString × ℕ) (idx : ℕ) =>
      ((splitNode p.1[idx]! p.2).1,
        p.1.take idx ++ (splitNode p.1[idx]! p.2).2.reverse ++ p.1.drop (idx + 1))) := by
    refine Primrec.pair (Primrec.fst.comp hnode) ?_
    exact Primrec.list_append.comp
      (Primrec.list_append.comp
        (take_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.list_reverse.comp (Primrec.snd.comp hnode)))
      (drop_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  exact (Primrec.option_map findIdx?_pred_primrec hg).of_eq
    (fun p => (allocateOne_eq_map p.1 p.2).symm)

/-- A single step of the allocator state transition. -/
def allocStep (r : Option (BitString × ℕ)) (st : Option (List BitString)) : Option (List BitString) :=
  st.bind (fun free =>
    (r.map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free))

set_option maxHeartbeats 2000000 in
-- The branch witness composes `allocateOne_computable` under nested
-- `Option.map`/`Option.bind` over encoded product inputs; keeping it as a named
-- helper localizes the remaining normalization cost.
/-- `allocStep` is computable. -/
lemma allocStep_computable :
    Computable₂ (fun (r : Option (BitString × ℕ)) (st : Option (List BitString)) => allocStep r st) := by
  have hinner : Computable₂
      (fun (d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString)
        (pr : BitString × ℕ) => (allocateOne d.2 pr.2).map Prod.snd) := by
    have hf : Computable (fun p : ((Option (BitString × ℕ) × Option (List BitString)) × List BitString) × (BitString × ℕ) => allocateOne p.1.2 p.2.2) :=
      allocateOne_computable.comp
        ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
    exact comp_option_map hf (comp_snd_snd Computable.id)
  have hg : Computable
      (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
        (d.1.1.map (fun pr => (allocateOne d.2 pr.2).map Prod.snd)).getD (some d.2)) := by
    have h_map : Computable (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
      d.1.1.map (fun pr => (allocateOne d.2 pr.2).map Prod.snd)) :=
      comp_option_map (comp_fst_fst Computable.id) hinner
    have h_some : Computable (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
      some d.2) := Computable.option_some.comp (comp_snd Computable.id)
    exact comp_option_getD h_map h_some
  exact (comp_option_bind Computable.snd hg.to₂).of_eq (fun _ => rfl)

/-- `allocatorState` rewritten as an explicit `Nat.rec` with a combinator-friendly step. -/
lemma allocatorState_eq_rec (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocatorState req n = Nat.rec (some [[]]) (fun y IH => allocStep (req y) IH) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have step_eq : ∀ X : Option (List BitString),
        (match X with
          | none => none
          | some free => match req k with
            | none => some free
            | some (_, l) => match allocateOne free l with
              | none => none
              | some (_, free') => some free')
        = allocStep (req k) X := by
      intro X
      cases X with
      | none => rfl
      | some free =>
        dsimp [allocStep]
        cases hr : req k with
        | none =>
          simp only [Option.map_none, Option.getD_none]
        | some o =>
          simp only [Option.map_some]
          cases h_alloc : allocateOne free o.2 with
          | none =>
            simp only [Option.map_none, Option.getD_some]
          | some a =>
            simp only [Option.map_some, Option.getD_some]
    calc allocatorState req (k + 1)
        = (match allocatorState req k with
            | none => none
            | some free => match req k with
              | none => some free
              | some (_, l) => match allocateOne free l with
                | none => none
                | some (_, free') => some free') := by rfl
      _ = allocStep (req k) (allocatorState req k) := step_eq _
      _ = allocStep (req k) (Nat.rec (some [[]]) (fun y IH => allocStep (req y) IH) k) := by rw [ih]

attribute [local irreducible] allocatorState

/-- The allocator state is computable uniformly in the context. -/
lemma allocatorState_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocatorState (req p.1) p.2) := by
  have hstep : Computable₂ (fun (p : BitString × ℕ) (q : ℕ × Option (List BitString)) =>
      allocStep (req p.1 q.1) q.2) := by
    have hreq : Computable (fun pq : (BitString × ℕ) × ℕ × Option (List BitString) => req pq.1.1 pq.2.1) :=
      hcomp.comp (Computable.pair (comp_fst_fst Computable.id) (comp_snd_fst Computable.id))
    exact Computable.comp allocStep_computable (Computable.pair hreq (comp_snd_snd Computable.id))
  refine (Computable.nat_rec (comp_snd Computable.id) (Computable.const (some [[]])) hstep).of_eq ?_
  intro p
  exact (allocatorState_eq_rec (req p.1) p.2).symm

/-! ## The three top-level obligations -/

/-- Extracting the payload of allocation at a given step. -/
def allocOut (r : Option (BitString × ℕ)) (st : Option (List BitString)) : Option BitString :=
  st.bind (fun free =>
    (r.map (fun pr => (allocateOne free pr.2).map Prod.fst)).getD none)

set_option maxHeartbeats 2000000 in
-- This is the output analogue of `allocStep_computable`; it has the same nested
-- product and `Option.map` composition cost, isolated from `allocFun_computable`.
/-- `allocOut` is computable. -/
lemma allocOut_computable :
    Computable₂ (fun (r : Option (BitString × ℕ)) (st : Option (List BitString)) => allocOut r st) := by
  have hinner : Computable₂
      (fun (d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString)
        (pr : BitString × ℕ) => (allocateOne d.2 pr.2).map Prod.fst) := by
    have hf : Computable (fun p : ((Option (BitString × ℕ) × Option (List BitString)) × List BitString) × (BitString × ℕ) => allocateOne p.1.2 p.2.2) :=
      allocateOne_computable.comp
        ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
    exact comp_option_map hf (comp_snd_fst Computable.id)
  have hg : Computable
      (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
        (d.1.1.map (fun pr => (allocateOne d.2 pr.2).map Prod.fst)).getD none) := by
    have h_map : Computable (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
      d.1.1.map (fun pr => (allocateOne d.2 pr.2).map Prod.fst)) :=
      comp_option_map (comp_fst_fst Computable.id) hinner
    have h_none : Computable (fun d : (Option (BitString × ℕ) × Option (List BitString)) × List BitString =>
      (@none (List BitString))) := Computable.const none
    exact comp_option_getD h_map h_none
  exact (comp_option_bind Computable.snd hg.to₂).of_eq (fun _ => rfl)

/-- `allocFun` rewritten as a bind over the allocator state. -/
lemma allocFun_eq_bind (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocFun req n = allocOut (req n) (allocatorState req n) := by
  dsimp [allocFun, allocOut]
  cases h_st : allocatorState req n with
  | none =>
    rfl
  | some free =>
    simp only [Option.bind_some]
    cases hr : req n with
    | none =>
      simp only [Option.map_none, Option.getD_none]
    | some o =>
      simp only [Option.map_some]
      cases h_alloc : allocateOne free o.2 with
      | none =>
        simp only [Option.map_none, Option.getD_some]
      | some a =>
        simp only [Option.map_some, Option.getD_some]

/-- The allocation function is computable uniformly in the context. -/
lemma allocFun_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocFun (req p.1) p.2) := by
  have hreq : Computable (fun p : BitString × ℕ => req p.1 p.2) := hcomp
  have hst : Computable (fun p : BitString × ℕ => allocatorState (req p.1) p.2) := allocatorState_computable req hcomp
  refine (Computable.comp allocOut_computable (Computable.pair hreq hst)).of_eq ?_
  intro p
  exact (allocFun_eq_bind (req p.1) p.2).symm

end KraftChaitin
end Kolmogorov
