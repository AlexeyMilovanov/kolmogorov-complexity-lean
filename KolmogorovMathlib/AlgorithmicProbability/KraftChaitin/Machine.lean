/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

import KolmogorovMathlib.AlgorithmicProbability.LSC.Defs
import KolmogorovMathlib.AlgorithmicProbability.LSC.Truncate
import KolmogorovMathlib.AlgorithmicProbability.LSC.Computability

namespace Kolmogorov

open scoped ENNReal
open Computability

/-! ### Kraft–Chaitin realization engine (moved below the truncation/`ev*` machinery so that `extract_request_stream` can reuse it). -/

/-
Step 1: Extract dyadic increments from a unit-mass lower-semicomputable function into a computable request stream family.
-/
lemma extract_request_stream {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ req : BitString → ℕ → Option (BitString × ℕ),
      Computable (fun p : BitString × ℕ => req p.1 p.2) ∧
      (∀ ctx : BitString, (∑' n, match req ctx n with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1) ∧
      (∀ ctx out : BitString, (∑' n, match req ctx n with | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) = f out ctx) := by
  obtain ⟨ approx, hmono ⟩ := hlsc;
  refine ⟨ fun ctx n => if ( Nat.unpair n ).2 < evNum approx ( Nat.unpair n ).1 ctx then ( evOut ( Nat.unpair n ).1 ).map fun o => ( o, evK ( Nat.unpair n ).1 ) else none, ?_, ?_, ?_ ⟩;
  · have h_cond : Computable (fun p : BitString × ℕ => if (Nat.unpair p.2).2 < evNum approx (Nat.unpair p.2).1 p.1 then true else false) := by
      have h_cond : Computable (fun p : BitString × ℕ => evNum approx (Nat.unpair p.2).1 p.1) := by
        have := evNum_computable hmono.2.2;
        convert this.comp ( Computable.pair ( Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) ) ) ( Computable.fst ) ) using 1;
      have h_cond : Computable (fun p : ℕ × ℕ => if p.1 < p.2 then true else false) := by
        convert Computable.of_eq _ _;
        exact fun p => Nat.recOn ( p.2 - p.1 ) false fun _ _ => true;
        · apply Computable.nat_casesOn;
          · have h_cond : Computable (fun p : ℕ × ℕ => p.2 - p.1) := by
              have h_sub : Primrec (fun p : ℕ × ℕ => p.2 - p.1) := by
                exact Primrec.nat_sub.comp ( Primrec.snd ) ( Primrec.fst )
              grind +suggestions;
            exact h_cond;
          · exact Computable.const false;
          · exact Computable.const true;
        · intro n; cases le_total n.1 n.2 <;> simp +decide [ *, Nat.sub_eq_zero_of_le ] ;
          cases lt_or_eq_of_le ‹_› <;> simp +decide [ * ];
          exact Nat.le_induction ( by tauto ) ( fun k hk ih => by tauto ) _ ( Nat.sub_pos_of_lt ‹_› );
      convert h_cond.comp ( Computable.pair ( Computable.snd.comp ( Computable.unpair.comp ( Computable.snd ) ) ) ‹Computable fun p : BitString × ℕ => evNum approx ( Nat.unpair p.2 ).1 p.1› ) using 1;
    have h_map : Computable (fun p : BitString × ℕ => Option.map (fun o => (o, evK (Nat.unpair p.2).1)) (evOut (Nat.unpair p.2).1)) := by
      have h_map : Computable (fun p : ℕ => Option.map (fun o => (o, evK (Nat.unpair p).1)) (evOut (Nat.unpair p).1)) := by
        have h_map : Computable (fun p : ℕ => evOut (Nat.unpair p).1) := by
          exact evOut_computable.comp ( Computable.fst.comp ( Computable.unpair ) );
        convert Computable.option_map h_map _ using 1;
        exact Computable.pair ( Computable.snd ) ( Computable.comp ( evK_computable ) ( Computable.fst.comp ( Computable.unpair.comp ( Computable.fst ) ) ) );
      exact h_map.comp ( Computable.snd );
    convert Computable.cond h_cond h_map ( Computable.const none ) using 1;
    grind;
  · intro ctx
    -- Reindex the sum over `n` to a sum over `t` and `j`.
    have h_reindex : (∑' n : ℕ, (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then (2⁻¹ : ℝ≥0∞) ^ (evK (Nat.unpair n).1) else 0)) = (∑' t : ℕ, (∑' j : ℕ, (if j < evNum approx t ctx then (2⁻¹ : ℝ≥0∞) ^ (evK t) else 0))) := by
      let e := Equiv.ofBijective (fun n : ℕ => ((Nat.unpair n).1, (Nat.unpair n).2))
        ⟨fun a₁ a₂ hn => by
            simpa using congr_arg (fun p => Nat.pair p.1 p.2) hn,
          fun a => ⟨Nat.pair a.1 a.2, by simp⟩⟩
      exact (e.tsum_eq
        (fun p : ℕ × ℕ =>
          if p.2 < evNum approx p.1 ctx then (2⁻¹ : ℝ≥0∞) ^ evK p.1 else 0)).trans
        (ENNReal.tsum_prod (f := fun (t : ℕ) (j : ℕ) =>
          if j < evNum approx t ctx then (2⁻¹ : ℝ≥0∞) ^ evK t else 0))
    have h_req_eq :
        (∑' n : ℕ,
          match
            (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
              Option.map (fun o => (o, evK (Nat.unpair n).1)) (evOut (Nat.unpair n).1)
            else none) with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
          | none => 0)
          =
        (∑' n : ℕ,
          if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
            (2 : ℝ≥0∞)⁻¹ ^ evK (Nat.unpair n).1
          else 0) := by
      refine tsum_congr fun n => ?_
      by_cases hlt : (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx
      · cases hout : evOut (Nat.unpair n).1 with
        | none =>
          have hzero : evNum approx (Nat.unpair n).1 ctx = 0 :=
            evNum_eq_none approx (Nat.unpair n).1 ctx hout
          simp [hzero] at hlt
        | some o =>
          simp [hlt]
      · simp [hlt]
    rw [h_req_eq, h_reindex]
    have h_inner :
        (∑' t : ℕ, ∑' j : ℕ,
          if j < evNum approx t ctx then (2 : ℝ≥0∞)⁻¹ ^ evK t else 0)
          = ∑' t : ℕ, evVal approx t ctx := by
      refine tsum_congr fun t => ?_
      rw [tsum_eq_sum (s := Finset.range (evNum approx t ctx))]
      · simp +decide [Finset.sum_ite, evVal]
        rw [Finset.filter_true_of_mem fun x hx => Finset.mem_range.mp hx]
        norm_num [dyadicValue]
        rw [div_eq_mul_inv, ENNReal.inv_pow]
      · aesop
    rw [h_inner]
    exact (le_of_eq (tsum_evVal hmono.1 hmono.2.1 ctx)).trans (h_sum ctx)
  · intro ctx out
    have h_sum_eq : (∑' n : ℕ, (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx ∧ evOut (Nat.unpair n).1 = some out then (2 : ℝ≥0∞)⁻¹ ^ evK (Nat.unpair n).1 else 0)) = f out ctx := by
      have h_sum_eq : ∑' t : ℕ, (if evOut t = some out then evVal approx t ctx else 0) = f out ctx := by
        convert tsum_evVal_out hmono.1 hmono.2.1 out ctx using 1
      have h_reindex : (∑' n : ℕ, (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx ∧ evOut (Nat.unpair n).1 = some out then (2 : ℝ≥0∞)⁻¹ ^ evK (Nat.unpair n).1 else 0)) =
          (∑' t : ℕ, ∑' j : ℕ, if j < evNum approx t ctx ∧ evOut t = some out then (2 : ℝ≥0∞)⁻¹ ^ evK t else 0) := by
        let e := Equiv.ofBijective (fun n : ℕ => ((Nat.unpair n).1, (Nat.unpair n).2))
          ⟨fun a₁ a₂ hn => by
              simpa using congr_arg (fun p => Nat.pair p.1 p.2) hn,
            fun a => ⟨Nat.pair a.1 a.2, by simp⟩⟩
        exact (e.tsum_eq
          (fun p : ℕ × ℕ =>
            if p.2 < evNum approx p.1 ctx ∧ evOut p.1 = some out then
              (2 : ℝ≥0∞)⁻¹ ^ evK p.1
            else 0)).trans
          (ENNReal.tsum_prod (f := fun (t : ℕ) (j : ℕ) =>
            if j < evNum approx t ctx ∧ evOut t = some out then
              (2 : ℝ≥0∞)⁻¹ ^ evK t
            else 0))
      have h_inner : ∀ t : ℕ, ∑' j : ℕ, (if j < evNum approx t ctx ∧ evOut t = some out then (2 : ℝ≥0∞)⁻¹ ^ (evK t) else 0) = if evOut t = some out then evVal approx t ctx else 0 := by
        intro t
        split_ifs <;> simp_all +decide [dyadicValue, evVal]
        rw [tsum_eq_sum (s := Finset.range (evNum approx t ctx))]
        · rw [Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_range.mp hx]
          norm_num [div_eq_mul_inv, ENNReal.inv_pow]
        · grind
      rw [h_reindex, tsum_congr h_inner]
      exact h_sum_eq
    have h_req_eq :
        (∑' n : ℕ,
          match
            (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
              Option.map (fun o => (o, evK (Nat.unpair n).1)) (evOut (Nat.unpair n).1)
            else none) with
          | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
          | none => 0)
          =
        (∑' n : ℕ,
          if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx ∧
              evOut (Nat.unpair n).1 = some out then
            (2 : ℝ≥0∞)⁻¹ ^ evK (Nat.unpair n).1
          else 0) := by
      refine tsum_congr fun n => ?_
      by_cases hlt : (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx
      · cases hout : evOut (Nat.unpair n).1 with
        | none =>
          have hzero : evNum approx (Nat.unpair n).1 ctx = 0 :=
            evNum_eq_none approx (Nat.unpair n).1 ctx hout
          simp [hzero] at hlt
        | some o =>
          by_cases ho : o = out <;> simp [hlt, ho]
      · simp [hlt]
    rw [h_req_eq]
    exact h_sum_eq

/-- **The online Kraft–Chaitin allocator (remaining hard combinatorial core).**

Given, uniformly in `ctx`, a computable request stream `req ctx n = some (o, l)`
of total Kraft weight `≤ 1`, produce a computable prefix-free code assignment
`alloc ctx n` realizing every requested length, with codes for distinct indices
pairwise prefix-incomparable.

This is the genuine *online* (causal) allocator: `alloc ctx n` may depend only on
requests with index `< n`, which is what makes it computable. It is realized by the
leftmost-free-dyadic-interval algorithm maintaining a free list of tree nodes of
pairwise distinct lengths (so a length-`l` request is always serviceable once the
used measure leaves `≥ 2^{-l}` of free space, the nodes of length `> l` summing to
`< 2^{-l}`). Allocating the smallest fitting free interval and returning its
right-siblings to the free list preserves the invariant; disjoint dyadic intervals
yield prefix-incomparable codes.

This allocator is fully formalized in
`KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator`: the free-list data
structure (`allocFun`), its computability (`allocFun_computable`), the
prefix-incomparability of distinct codes (`allocFun_prefixFree`), and the
serviceability of every request under the unit Kraft bound (`allocFun_success`) are
all proved there.  Together with the surrounding development — the geometric dyadic
request extraction (`extract_request_stream_geometric`), the prefix-machine
construction (`construct_prefix_machine`), and the realization bound
(`realization_bound_of_machine`) — this completes `kraftChaitin_realization_bound_unit`. -/
lemma exists_online_prefixFree_family (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hweight : ∀ ctx, (∑' n, match req ctx n with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1) :
    ∃ alloc : BitString → ℕ → Option BitString,
      Computable (fun p : BitString × ℕ => alloc p.1 p.2) ∧
      (∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l) ∧
      (∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm → n ≠ m → ¬ List.IsPrefix cn cm) := by
  refine ⟨fun ctx => KraftChaitin.allocFun (req ctx), ?_, ?_, ?_⟩
  · exact KraftChaitin.allocFun_computable req hcomp
  · intro ctx n o l hreq
    exact KraftChaitin.allocFun_success (req ctx) n o l hreq (hweight ctx)
  · intro ctx n m cn cm hn hm hneq
    exact KraftChaitin.allocFun_prefixFree (req ctx) n m cn cm hn hm hneq

/-
Computability of the inversion search predicate used to build the prefix machine.
-/
lemma construct_pred_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2)) :
    Computable (fun p : (BitString × BitString) × ℕ =>
      decide (alloc p.1.2 p.2 = some p.1.1 ∧ (req p.1.2 p.2).isSome = true)) := by
  have hallocdec : Computable (fun p : BitString × BitString × ℕ => decide (alloc p.2.1 p.2.2 = some p.1)) := by
    have hdecid : Computable (fun p : Option BitString × BitString => decide (p.1 = some p.2)) := by
      have hdecid : Computable (fun p : Option BitString × Option BitString => decide (p.1 = p.2)) := by
        have hdecid : Primrec (fun p : Option BitString × Option BitString => decide (p.1 = p.2)) := by
          convert Primrec.eq;
          any_goals exact Option BitString;
          constructor <;> intro h <;> rw [ PrimrecRel ] at *;
          · convert h using 1;
            constructor <;> intro h <;> rw [ PrimrecPred ] at *;
            · grind;
            · exact ⟨ inferInstance, h ⟩;
          · grind +suggestions;
        exact hdecid.to_comp;
      convert hdecid.comp ( Computable.fst.pair ( Computable.option_some.comp Computable.snd ) ) using 1;
    convert hdecid.comp ( hcomp.comp ( Computable.snd ) |> Computable.pair <| Computable.fst ) using 1
  have hreqdec : Computable (fun p : BitString × BitString × ℕ => (req p.2.1 p.2.2).isSome) := by
    have hreqdec : Computable (fun p : BitString × Nat => (req p.1 p.2).isSome) := by
      have hreqdec : Computable (fun p : BitString × Nat => req p.1 p.2) := hreqcomp
      convert Computable.comp _ hreqdec using 1;
      convert Primrec.option_isSome.to_comp using 1;
    convert hreqdec.comp ( Computable.fst.comp ( Computable.snd ) |> Computable.pair <| Computable.snd.comp ( Computable.snd ) ) using 1;
  have h_computable_and : Computable (fun p : BitString × BitString × ℕ => decide (alloc p.2.1 p.2.2 = some p.1 ∧ (req p.2.1 p.2.2).isSome)) := by
    convert Computable.cond ( hallocdec ) ( hreqdec ) ( Computable.const false ) using 1;
    grind;
  convert h_computable_and.comp ( Computable.fst.comp ( Computable.fst ) |> Computable.pair <| Computable.snd.comp ( Computable.fst ) |> Computable.pair <| Computable.snd ) using 1

/-
Partrec output stage used to build the prefix machine: at the found index `n`,
emit the first component of `req ctx n` (undefined if `req ctx n = none`).
-/
lemma construct_out_partrec (req : BitString → ℕ → Option (BitString × ℕ))
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Partrec₂ (fun (p : BitString × BitString) (n : ℕ) =>
      ((req p.2 n).map Prod.fst : Option BitString) |> Part.ofOption) := by
  -- The function `if p.2 = some x then some x.1 else none` is computable.
  have h_if_computable : Computable (fun p : Option (BitString × ℕ) => Option.map Prod.fst p) := by
    refine Computable.option_map ?_ ?_;
    · exact Computable.id;
    · exact Computable.fst.comp ( Computable.snd ) |> Computable.comp <| Computable.id;
  have h_partrec : Computable (fun p : (BitString × BitString) × ℕ => Option.map Prod.fst (req p.1.2 p.2)) :=
    h_if_computable.comp (hreqcomp.comp (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  exact h_partrec.ofOption

/-
Step 4: Construct a prefix decompressor from an allocator and a request stream.
-/
lemma construct_prefix_machine (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2))
    (_halloc : ∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm → n ≠ m → ¬ List.IsPrefix cn cm) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧
      ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c → M' (c, ctx) = Part.some o := by
  refine ⟨ ?_, ⟨ ?_, ?_ ⟩, ?_ ⟩;
  refine fun p => ( Nat.rfind fun n => Part.some ( decide ( alloc p.2 n = some p.1 ∧ ( req p.2 n ).isSome = true ) ) ) >>= fun n => Part.ofOption ( ( req p.2 n ).map Prod.fst );
  · refine Partrec.bind ?_ ?_;
    · have hpred₂ : Partrec₂ (fun (p : BitString × BitString) (n : ℕ) =>
          (Part.some (decide (alloc p.2 n = some p.1 ∧ (req p.2 n).isSome = true)) : Part Bool)) := by
        have hpred : Computable₂ (fun (p : BitString × BitString) (n : ℕ) =>
            decide (alloc p.2 n = some p.1 ∧ (req p.2 n).isSome = true)) := by
          simpa [Computable₂] using construct_pred_computable req alloc hreqcomp hcomp
        exact hpred.partrec₂
      exact Partrec.rfind hpred₂
    · convert construct_out_partrec req hreqcomp using 1;
  · intro ctx p hp q hq hpre;
    simp_all +decide [ domainAt ];
    grind +splitIndPred;
  · intro ctx n o l c hreq halloc'
    have hn : n ∈ Nat.rfind (fun n => Part.some (decide (alloc ctx n = some c ∧ (req ctx n).isSome = true))) := by
      grind +suggestions;
    rw [ show Nat.rfind ( fun n => Part.some ( decide ( alloc ctx n = some c ∧ ( req ctx n ).isSome = true ) ) ) = Part.some n from ?_ ];
    · aesop;
    · convert Part.eq_some_iff.mpr hn using 1

end Kolmogorov
