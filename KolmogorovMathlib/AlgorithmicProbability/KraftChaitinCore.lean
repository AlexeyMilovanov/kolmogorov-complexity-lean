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
/-!
# The abstract Kraft–Chaitin realization engine

This module isolates the genuinely hard Chapter-4 (SUV §4.x) coding engine — the
**online Kraft–Chaitin allocator** — into a single, abstract, reusable obligation
`kraftChaitin_realization_bound`, decoupled from every particular semimeasure.

The engine consumes a *lower-semicomputable* conditional function
`f : output → context → ℝ≥0∞` (interface `IsLSC`: a computable, monotone, dyadic
approximation converging to `f`) that is globally `2^{d}`-subnormalized
(`∀ ctx, ∑_out f out ctx ≤ 2^{d}`), and produces a genuine prefix decompressor
`M'` realizing `f` up to an additive coding constant `c₀`:
`2^{-c₀} · f(out | ctx) ≤ 2^{-KP_{M'}(out | ctx)}`.

This is the canonical textbook statement of the Kraft–Chaitin coding theorem
(hard direction): it is `≤×`, with no logarithm and no equality, and the constant
`c₀` is genuine positive coding overhead (it absorbs the `2^{-d}` down-scaling the
truncated allocator hardcodes).

Both of the project's remaining coding sorries reduce to this single engine:

* `aprioriMeasure_prefix_realization` (in `KraftChaitin`) applies it to
  `aprioriMeasure M` at level `d = 0`, using `aprioriMeasure_isLSC` and
  `tsum_aprioriMeasure_le_one`;
* `conditional_coding_section_realization` (in `ConditionalCoding`) applies it to a
  dynamically *truncated* scaled section at level `d`.

The `IsLSC` interface deliberately keeps the approximation **concrete** (a
`ℕ`-valued numerator over the dyadic denominator `2^{s}`, with `Computable`
witnessing computability) rather than introducing a generic typeclass: this avoids
universe/computability-class friction and keeps the engine's hypotheses exactly
the data an allocator consumes.
-/

namespace Kolmogorov

open scoped ENNReal
open Computability





/-- **Dynamic truncation of a lower-semicomputable function to a global mass bound.**

Given a lower-semicomputable `f` and a level `d`, there is a lower-semicomputable
`g` that is *globally* `2^{d}`-subnormalized (`∀ ctx, ∑_out g out ctx ≤ 2^{d}`) and
agrees with `f` on every context whose own `f`-mass already respects the bound
(`∑_out f out ctx ≤ 2^{d} → g = f` on that context).

This is the online "cap the running mass at `2^{d}`" operator: enumerate the dyadic
increments of `f` (via its `IsLSC` approximation) and accept each only while the
accumulated per-context mass stays `≤ 2^{d}`. The accepted stream is itself
lower-semicomputable and globally bounded; where `f`'s total mass never exceeds the
cap, no increment is ever dropped, so `g = f` there.

This packages the dynamic-truncation half of the *conditional* Kraft–Chaitin
construction (SUV §4.5): it converts the merely per-context-guarded scaled section
into a globally-bounded l.s.c. function the abstract allocator
`kraftChaitin_realization_bound` can consume directly.

The construction is the take-while online truncation `truncG`: enumerate all dyadic
increments of `f` as a single `ℕ`-indexed stream (output decoded via
`Encodable.decode₂`, stage from `Nat.unpair`), accept an increment iff the running
cumulative mass stays `≤ 2^{d}`, and read off the accepted mass per output as the
supremum of exact dyadic numerators over `2^{S}`. It is now fully proved: see the
`truncG*`/`ev*`/`cumNum`/`incNum` lemmas above for lower
semicomputability (`truncGapprox_mono`, `truncGapprox_computable`), the global
`2^{d}` bound (`tsum_truncG_le`), and agreement (`truncG_eq_f_of_le`). -/
theorem IsLSC.truncate {f : BitString → BitString → ℝ≥0∞} (hf : IsLSC f) (d : ℕ) :
    ∃ g : BitString → BitString → ℝ≥0∞, IsLSC g ∧
      (∀ ctx : BitString, (∑' out : BitString, g out ctx) ≤ (2 : ℝ≥0∞) ^ d) ∧
      (∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d →
        ∀ out : BitString, g out ctx = f out ctx) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hf
  refine ⟨truncG approx d, ⟨truncGapprox approx d, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro S out ctx; exact truncGapprox_mono d S out ctx
  · intro out ctx; rfl
  · exact truncGapprox_computable hcomp d
  · intro ctx; exact tsum_truncG_le d ctx
  · intro ctx hle out; exact truncG_eq_f_of_le hmono hsup d ctx hle out


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

/-! ### Geometric (threshold-crossing) dyadic request extraction

The geometric request stream emits, for each output `o` and dyadic length `l ≥ 1`,
exactly one request `(o, l)` precisely when the lower-semicomputable approximation
of `f o ctx` first crosses the threshold `2^{-(l-1)}` at some stage `s`. The
per-output requested lengths therefore form an upward-closed set `{ l ≥ L }`, whose
Kraft tail `∑_{l ≥ L} 2^{-l} = 2 · 2^{-L}` is bounded by `f o ctx`, while the
largest single weight `2^{-L}` geometrically dominates `f o ctx` (within `2^2`).
This is the decomposition consumed by `realization_bound_of_machine`. -/

/-- The threshold-crossing predicate: the stage-`s` dyadic value of `approx · o ctx`
has reached `2^{-(l-1)}`, i.e. `2^s ≤ approx s o ctx · 2^(l-1)` (and `l ≥ 1`). -/
def geomCross (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString) (l s : ℕ) : Prop :=
  1 ≤ l ∧ 2 ^ s ≤ approx s o ctx * 2 ^ (l - 1)

instance (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString) (l s : ℕ) :
    Decidable (geomCross approx o ctx l s) := by
  unfold geomCross; infer_instance

/-- The geometric request stream. Decode `n` into `(o, l, s)` via two `Nat.unpair`s
(and `evOut` for the output), and emit `(o, l)` exactly at the first stage `s` at
which `geomCross` becomes true for `(o, l)`. -/
lemma decide_or_not_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∨ ¬b) = cond (decide a) true (cond (decide b) false true) := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

lemma decide_and_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∧ b) = cond (decide a) (decide b) false := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

lemma ite_eq_some {P : Prop} [Decidable P] {α : Type _} {x : α} :
    (if P then some x else none) = cond (decide P) (some x) none := by
  by_cases hP : P <;> simp_all

/-- Body of the geometric request stream. -/
def geomReqBody (approx : ℕ → BitString → BitString → ℕ) (p : (BitString × ℕ) × BitString) : Option (BitString × ℕ) :=
  if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧ ((evK (Nat.unpair p.1.2).1) = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) ((evK (Nat.unpair p.1.2).1) - 1)) then
    some (p.2, ((Nat.unpair p.1.2).2))
  else none

lemma geomReqBody_eq (approx : ℕ → BitString → BitString → ℕ) (p : (BitString × ℕ) × BitString) :
  geomReqBody approx p =
    if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧ ((evK (Nat.unpair p.1.2).1) = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) ((evK (Nat.unpair p.1.2).1) - 1)) then
      some (p.2, ((Nat.unpair p.1.2).2))
    else none := rfl

/-- Geometric request stream. -/
def geomReq (approx : ℕ → BitString → BitString → ℕ) (ctx : BitString) (n : ℕ) :
    Option (BitString × ℕ) :=
  (evOut (Nat.unpair n).1).bind fun o => geomReqBody approx ((ctx, n), o)

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
      · convert primrec_two_pow_aux.to_comp.comp ( Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.const 1 ) |> Primrec.to_comp ) using 1;
    have hdec : Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      convert Primrec.nat_le using 1;
      constructor <;> intro h <;> simp_all +decide [ PrimrecPred, PrimrecRel ];
      · exact ⟨ inferInstance, h ⟩;
      · grind;
    convert hdec.to_comp.comp ( Computable.pair ( primrec_two_pow_aux.to_comp.comp ( Computable.fst.comp ( Computable.snd ) ) ) ‹Computable fun q : ℕ × ℕ × BitString × BitString => approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ ( q.1 - 1 ) › ) using 1;
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

/-
**Evaluation of `geomReq` at a canonical paired index.** Decoding
`Nat.pair (Nat.pair (Encodable.encode o) s) l` recovers output `o`, stage `s`
(`= evK`) and length `l`, so `geomReq` emits `(o, l)` here exactly when level `l`
is first crossed at stage `s`. This is the clean interface used by the Kraft and
geometric-bound proofs.
-/
lemma geomReq_pair (approx : ℕ → BitString → BitString → ℕ) (ctx o : BitString)
    (s l : ℕ) :
    geomReq approx ctx (Nat.pair (Nat.pair (Encodable.encode o) s) l) =
      if geomCross approx o ctx l s ∧ (s = 0 ∨ ¬ geomCross approx o ctx l (s - 1)) then
        some (o, l) else none := by
  unfold geomReq; simp +decide [ evOut, Nat.unpair_pair, Encodable.decode₂_encode ] ;
  convert geomReqBody_eq approx _ using 1;
  unfold evK; simp +decide [ Nat.unpair_pair ] ;

open Classical in
/-- **Per-output Kraft tail bound.** For a fixed output `o`, the crossed levels
`{ l ≥ 1 : ∃ s, geomCross approx o ctx l s }` form an upward-closed set `{ l ≥ L }`,
whose geometric Kraft tail `∑_{l ≥ L} 2⁻¹^l = 2⁻¹^(L-1)` is bounded by the limit
mass `f o ctx` (because the least crossed level `L` already has
`2⁻¹^(L-1) ≤ dyadicValue ... ≤ f o ctx`). -/
lemma geomReq_crossed_kraft_perOutput {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (o ctx : BitString) :
    (∑' l : ℕ, if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0)
      ≤ f o ctx := by
  by_cases h : ∃ l, 1 ≤ l ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ ( l - 1 );
  · obtain ⟨L, hL⟩ : ∃ L, 1 ≤ L ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ (L - 1) ∧ ∀ l < L, ¬(1 ≤ l ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ (l - 1)) := by
      exact ⟨ Nat.find h, Nat.find_spec h |>.1, Nat.find_spec h |>.2.choose, Nat.find_spec h |>.2.choose_spec, fun l hl hl' => Nat.find_min h hl hl' ⟩;
    have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) ≤ f o ctx := by
      have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) = (2 : ℝ≥0∞)⁻¹ ^ (L - 1) := by
        have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) = (∑' l : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (L + l)) := by
          rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
          use fun x => x.val - L;
          · -- If $x.val - L = y.val - L$, then adding $L$ to both sides gives $x.val = y.val$, which implies $x = y$ since $x$ and $y$ are in the set $\{l \mid L \leq l\}$.
            intro x y hxy
            have h_eq : x.val = y.val := by
              linarith [ Nat.sub_add_cancel ( show L ≤ x.val from by aesop ), Nat.sub_add_cancel ( show L ≤ y.val from by aesop ) ]
            exact Subtype.ext h_eq;
          · intro x hx; use ⟨ x + L, by aesop ⟩ ; aesop;
          · aesop;
        simp_all +decide [ pow_add, ENNReal.tsum_mul_left ];
        rcases L with ( _ | L ) <;> simp_all +decide [ pow_succ, mul_assoc ];
        rw [ ENNReal.inv_mul_cancel ] <;> norm_num;
      obtain ⟨ s, hs₁, hs₂ ⟩ := hL.2;
      have h_le : (2 : ℝ≥0∞)⁻¹ ^ (L - 1) ≤ dyadicValue (approx s o ctx) s := by
        unfold dyadicValue; norm_num [ ENNReal.div_eq_inv_mul ] ;
        rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
        · field_simp;
          rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num;
          exact_mod_cast hs₁;
        · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      exact h_sum.symm ▸ h_le.trans ( hsup o ctx ▸ le_iSup ( fun s => dyadicValue ( approx s o ctx ) s ) s );
    convert h_sum using 3;
    split_ifs <;> simp_all +decide [ geomCross ];
    · grind;
    · rename_i k hk₁ hk₂;
      contrapose! hk₁;
      exact ⟨ by linarith, by obtain ⟨ x, hx ⟩ := hL.2.1; exact ⟨ x, by exact le_trans hx ( Nat.mul_le_mul_left _ ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_right hk₂ 1 ) ) ) ⟩ ⟩;
  · simp_all +decide [ geomCross ];
    rw [ tsum_eq_single 0 ] <;> simp_all +decide [ not_and ]

open Classical in
/-- Under stagewise monotonicity, the threshold-crossing predicate is monotone in
the stage: once level `l` is crossed it stays crossed. -/
lemma geomCross_succ_of_geomCross {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (o ctx : BitString) (l s : ℕ) (h : geomCross approx o ctx l s) :
    geomCross approx o ctx l (s + 1) := by
  cases l <;> simp_all +decide [ pow_succ, dyadicValue ];
  · exact absurd h.1 ( by norm_num );
  · convert hmono s o ctx |> le_trans _ using 1;
    rotate_left;
    exact 1 / 2 ^ ‹_›;
    · have H2 : ( 2 ^ s : ENNReal ) ≤ approx s o ctx * 2 ^ ‹_› := by exact_mod_cast h.2;
      have H3 := ENNReal.div_le_div H2 (le_refl (2 ^ s * 2 ^ ‹_› : ENNReal));
      have H4 : (2 ^ s : ENNReal) / (2 ^ s * 2 ^ ‹_›) = 1 / 2 ^ ‹_› := by
        rw [ ENNReal.div_eq_div_iff ] <;> ring_nf <;> norm_num;
        exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      have H5 : ((approx s o ctx : ENNReal) * 2 ^ ‹_›) / (2 ^ s * 2 ^ ‹_›) = (approx s o ctx : ENNReal) / 2 ^ s := by
        rw [ ENNReal.mul_div_mul_right ] ; norm_num;
        exact ENNReal.pow_ne_top ( by norm_num );
      rwa [H4, H5] at H3
    · rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      · field_simp;
        norm_cast ; simp_all +decide [   mul_comm ];
        unfold geomCross; simp +decide [ pow_succ' ] ;
      · norm_num [ ENNReal.div_eq_top ]

open Classical in
/-- **Reindexing the geometric Kraft sum by output.** Every index `n` emitting a
request `(o, l)` corresponds (injectively) to a crossed level `l ≥ 1` of output `o`
(the unique first-crossing stage), so the total Kraft weight is bounded by the
double sum over outputs and their crossed levels. -/
lemma geomReq_kraft_le_perOutput_sum {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (ctx : BitString) :
    (∑' n, match geomReq approx ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
      ≤ ∑' o : BitString, ∑' l : ℕ,
          (if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0) := by
  have h_reindex : (∑' n : ℕ, (match geomReq approx ctx n with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)) = (∑' a : ℕ, ∑' s : ℕ, ∑' l : ℕ, (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l' | none => 0)) := by
    have h_reindex : ∀ (f : ℕ → ℝ≥0∞), (∑' n : ℕ, f n) = (∑' a : ℕ, ∑' s : ℕ, ∑' l : ℕ, f (Nat.pair (Nat.pair a s) l)) := by
      intro f;
      rw [ ← ENNReal.tsum_prod, ← ENNReal.tsum_prod ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun p : ( ℕ × ℕ ) × ℕ => Nat.pair ( Nat.pair p.1.1 p.1.2 ) p.2 ) ⟨ fun p₁ p₂ hp => by
        rcases p₁ with ⟨⟨a, s⟩, l⟩
        rcases p₂ with ⟨⟨a', s'⟩, l'⟩
        obtain ⟨hp₁, hp₂⟩ := Nat.pair_eq_pair.1 hp
        obtain ⟨ha, hs⟩ := Nat.pair_eq_pair.1 hp₁
        simp_all, fun p => ⟨ ⟨ ⟨ Nat.unpair p |>.1 |> Nat.unpair |>.1, Nat.unpair p |>.1 |> Nat.unpair |>.2 ⟩, Nat.unpair p |>.2 ⟩, by simp +decide ⟩ ⟩ ) ];
      rfl
    exact h_reindex _;
  -- By `tsum_eq_tsum_of_ne_zero_bij`, we can restrict the sum over `a` to outputs.
  have h_restrict : (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ, (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l' | none => 0)))) ≤ (∑' o : BitString, (∑' s : ℕ, (∑' l : ℕ, (match geomReq approx ctx (Nat.pair (Nat.pair (Encodable.encode o) s) l) with | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l' | none => 0)))) := by
    have h_restrict : (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ, (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l' | none => 0)))) = (∑' a : ℕ, Set.indicator (Set.range (Encodable.encode : BitString → ℕ)) (fun a => ∑' s : ℕ, ∑' l : ℕ, match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l' | none => 0) a) := by
      congr;
      ext a; rw [Set.indicator_apply]; split_ifs <;> simp_all +decide [ geomReq ] ;
      unfold evOut; simp +decide [ *, Encodable.decode₂ ] ;
    calc
      (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ,
          (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0))))
          ≤ ∑' a : ℕ,
              Set.indicator (Set.range (Encodable.encode : BitString → ℕ))
                (fun a => ∑' s : ℕ, ∑' l : ℕ,
                  match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
                  | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
                  | none => 0) a := h_restrict.le
      _ = ∑' o : BitString, (∑' s : ℕ, (∑' l : ℕ,
          (match geomReq approx ctx (Nat.pair (Nat.pair (Encodable.encode o) s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0))) := by
        erw [ ← tsum_subtype ];
        erw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ <| Encodable.encode_injective ) ] ; aesop;
  refine le_trans h_reindex.le <| h_restrict.trans ?_;
  refine ENNReal.tsum_le_tsum fun o => ?_;
  rw [ ENNReal.tsum_comm ];
  refine ENNReal.tsum_le_tsum fun l => ?_;
  split_ifs with h;
  · obtain ⟨ s₀, hs₀ ⟩ := Nat.findX h.2;
    rw [ tsum_eq_single s₀ ];
    · grind +suggestions;
    · intro b' hb'
      by_cases hb'_lt : b' < s₀;
      · rw [ geomReq_pair ] ; simp +decide [ hs₀.2 b' hb'_lt ];
      · rw [ geomReq_pair ];
        split_ifs <;> norm_num;
        rename_i h;
        exact h.2.elim ( fun h => by linarith [ Nat.pos_of_ne_zero ( show s₀ ≠ 0 from by rintro rfl; exact hs₀.2 0 ( Nat.pos_of_ne_zero ( by aesop ) ) hs₀.1 ) ] ) fun h => h ( by exact Nat.le_induction ( by tauto ) ( fun k hk ih => by exact geomCross_succ_of_geomCross hmono o ctx l k ih ) _ ( show b' - 1 ≥ s₀ from Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( le_of_not_gt hb'_lt ) ( Ne.symm hb' ) ) ) );
  · convert tsum_nonpos _;
    · infer_instance;
    · infer_instance;
    · intro s; rw [ geomReq_pair ] ;
      split_ifs <;> norm_num;
      exact h ⟨ by unfold geomCross at *; aesop, s, by tauto ⟩

open Classical in
/-- **Kraft bound for the geometric request stream.** Because each output's emitted
lengths form an upward-closed set `{ l ≥ L }` with `2 · 2^{-L} ≤ f o ctx`, the total
Kraft weight is bounded by `∑_o f o ctx ≤ 1`. -/
lemma geomReq_kraft_le_one {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1)
    (ctx : BitString) :
    (∑' n, match geomReq approx ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1 := by
  calc (∑' n, match geomReq approx ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
      ≤ ∑' o : BitString, ∑' l : ℕ,
          (if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0) :=
        geomReq_kraft_le_perOutput_sum hmono ctx
    _ ≤ ∑' o : BitString, f o ctx :=
        ENNReal.tsum_le_tsum (fun o => geomReq_crossed_kraft_perOutput hsup o ctx)
    _ ≤ 1 := h_sum ctx

/-
**Geometric domination for the geometric request stream.** Each output's mass
`f out ctx` is within a factor `2^2` of its largest single emitted request weight.

The mass bound `h_sum` (hence `f out ctx ≤ 1`) is genuinely needed: the smallest
emitted length is `1` (weight `2⁻¹`), so an output with `f out ctx ≥ 2` would
violate the `2^2`-domination. With `f out ctx ≤ 1` the largest crossed level `L`
satisfies `2⁻¹^L ≤ f out ctx < 2^2 · 2⁻¹^L`.
-/
lemma geomReq_geometric_bound {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (_hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1)
    (ctx out : BitString) :
    f out ctx ≤ (2 : ℝ≥0∞) ^ 2 *
      (⨆ n, match geomReq approx ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
  by_contra h_contra;
  obtain ⟨l, hl⟩ : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s ∧ ∀ l' : ℕ, l' < l → ¬∃ s' : ℕ, geomCross approx out ctx l' s' := by
    have hL : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s := by
      -- Since $f(out, ctx) > 0$, there exists some $s$ such that $dyadicValue (approx s out ctx) s > 0$.
      obtain ⟨s, hs⟩ : ∃ s : ℕ, dyadicValue (approx s out ctx) s > 0 := by
        have h_pos : f out ctx > 0 := by
          exact lt_of_not_ge fun h => h_contra <| le_trans h <| by positivity;
        exact not_forall_not.mp fun h => h_pos.ne' <| hsup out ctx ▸ by simp +decide [ show ∀ s : ℕ, dyadicValue ( approx s out ctx ) s = 0 from fun s => le_antisymm ( le_of_not_gt fun hs => h s hs ) zero_le ] ;
      refine ⟨ s + 1, ?_, s, ?_, ?_ ⟩ <;> norm_num [ geomCross ] at *;
      exact Nat.pos_of_ne_zero fun h => hs.ne' <| by unfold dyadicValue; simp +decide [ h ] ;
    obtain ⟨l, hl⟩ : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s ∧ ∀ l' : ℕ, l' < l → ¬∃ s' : ℕ, geomCross approx out ctx l' s' := by
      have h_well_founded : WellFounded (fun l l' : ℕ => l < l') := by
        exact wellFounded_lt
      obtain ⟨l, hl⟩ : ∃ l : ℕ, l ∈ {l : ℕ | 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s} ∧ ∀ l' : ℕ, l' ∈ {l : ℕ | 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s} → ¬l' < l := by
        have := h_well_founded.has_min { l | 1 ≤ l ∧ ∃ s, geomCross approx out ctx l s } ⟨ _, hL.choose_spec ⟩ ; tauto;
      exact ⟨ l, hl.1.1, hl.1.2.choose, hl.1.2.choose_spec, fun l' hl' hl'' => hl.2 l' ⟨ Nat.pos_of_ne_zero fun h => by subst h; exact absurd hl'' ( by rintro ⟨ s', hs' ⟩ ; exact absurd hs'.1 ( by norm_num ) ), hl'' ⟩ hl' ⟩;
    use l;
  obtain ⟨s, hs⟩ := hl.right
  have h_emitted : ⨆ n, (match geomReq approx ctx n with | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) ≥ (2 : ℝ≥0∞)⁻¹ ^ l := by
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℕ, geomCross approx out ctx l s₀ ∧ ∀ s' : ℕ, s' < s₀ → ¬geomCross approx out ctx l s' := by
      exact ⟨ Nat.find ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ), Nat.find_spec ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ), fun s' hs' => Nat.find_min ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ) hs' ⟩;
    refine le_trans ?_ ( le_ciSup ?_ ( Nat.pair ( Nat.pair ( Encodable.encode out ) s₀ ) l ) ) ; simp +decide [ hs₀, geomReq_pair ] ;
    · rcases s₀ with ( _ | s₀ ) <;> simp +decide [ hs₀ ] at hs₀ ⊢;
    · refine ⟨ 1, Set.forall_mem_range.2 fun n => ?_ ⟩ ; rcases geomReq approx ctx n with ( _ | ⟨ o, l ⟩ ) <;> norm_num;
      split_ifs <;> norm_num;
      exact pow_le_one₀ ( by norm_num ) ( by norm_num );
  -- Since $l$ is the smallest level where the cross condition holds, for any $s$, we have $dyadicValue (approx s out ctx) s < 2⁻¹^(l-2)$.
  have h_dyadic_lt : ∀ s, dyadicValue (approx s out ctx) s < (2 : ℝ≥0∞)⁻¹ ^ (l - 2) := by
    intro s
    by_cases hl_ge_2 : 2 ≤ l;
    · have h_dyadic_lt : ¬geomCross approx out ctx (l - 1) s := by
        exact fun h => hs.2 ( l - 1 ) ( Nat.sub_lt ( by linarith ) zero_lt_one ) ⟨ s, h ⟩;
      unfold geomCross at h_dyadic_lt; norm_num at h_dyadic_lt;
      unfold dyadicValue; norm_num [ ENNReal.div_lt_iff ] ;
      rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
      · rw [ div_pow, div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast ; norm_num;
        · exact h_dyadic_lt ( Nat.le_sub_one_of_lt hl_ge_2 );
        · positivity;
      · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · interval_cases l ; norm_num at *;
      contrapose! h_contra;
      refine le_trans ?_ ( mul_le_mul_right h_emitted _ );
      refine le_trans ( h_sum ctx |> le_trans ( ENNReal.le_tsum out ) ) ?_ ; norm_num;
      rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      norm_num [ ENNReal.mul_eq_top ];
  -- Therefore, $f out ctx \leq 2⁻¹^(l-2)$.
  have h_f_le : f out ctx ≤ (2 : ℝ≥0∞)⁻¹ ^ (l - 2) := by
    exact hsup out ctx ▸ iSup_le fun s => le_of_lt ( h_dyadic_lt s );
  refine h_contra <| h_f_le.trans ?_;
  refine le_trans ?_ ( mul_le_mul_right h_emitted _ );
  rcases l with ( _ | _ | l ) <;> norm_num [ pow_succ' ] at *;
  · rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    norm_num [ ENNReal.mul_eq_top ];
  · ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    norm_num [ ENNReal.mul_eq_top ]

/-- **Geometric dyadic request extraction.** A unit-mass lower-semicomputable `f`
has a computable request stream of total Kraft weight `≤ 1` together with a
constant `K` such that, for every output `out`, the total mass `f out ctx` is
within a factor `2^K` of the *largest single* request weight for `out`
(`⨆ n, …`). This is the threshold-crossing decomposition (one request per dyadic
level crossed, so the per-output requested lengths are strictly decreasing and the
shortest dominates the geometric tail). Unlike the unit-increment
`extract_request_stream` (which realizes `f` exactly but may split one output's
mass into arbitrarily many equal-length requests), this geometric form is exactly
what `realization_bound_of_machine` needs: `2^{-KP}` only sees the largest single
request, so the realization bound is provable iff `f out` is geometrically
dominated by that largest request. -/
lemma extract_request_stream_geometric {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ (req : BitString → ℕ → Option (BitString × ℕ)) (K : ℕ),
      Computable (fun p : BitString × ℕ => req p.1 p.2) ∧
      (∀ ctx : BitString, (∑' n, match req ctx n with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1) ∧
      (∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
        (⨆ n, match req ctx n with | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  exact ⟨geomReq approx, 2, geomReq_computable approx hcomp,
    geomReq_kraft_le_one hmono hsup h_sum,
    geomReq_geometric_bound hmono hsup h_sum⟩

/-- **Realization bound from a matched allocator (geometric form).** If a request
stream is realized by a prefix machine `M'` (each requested `(out, l)` gets an
allocated code of length `l` that `M'` maps back to `out`), and each output's mass
`f out` is within a factor `2^K` of its *largest single* request weight, then `M'`
achieves the multiplicative coding bound `2^{-K} · f(out|ctx) ≤ 2^{-KP_{M'}(out|ctx)}`.

This replaces the previous false form (which used the exact identity
`∑ requests = f` and is unprovable: with many equal-length requests `f out` can be
arbitrarily larger than the single largest request weight `= 2^{-KP}`). -/
lemma realization_bound_of_machine (f : BitString → BitString → ℝ≥0∞)
    (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (M' : Map) (K : ℕ)
    (hmatch : ∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hmachine : ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c → M' (c, ctx) = Part.some o)
    (hgeo : ∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
      (⨆ n, match req ctx n with | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) :
    ∃ c₀ : ℕ, ∀ out ctx : BitString, (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- The supremum of the per-request weights for `out` is `≤ 2^{-KP M' out ctx}`,
  -- since every realized request gives a code of its length producing `out`.
  have hS : ∀ ctx out : BitString,
      (⨆ n, match req ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)
        ≤ complexityWeight (KP M' out ctx) := by
    intro ctx out
    apply iSup_le
    intro n
    rcases h : req ctx n with _ | ⟨o, l⟩
    · simp
    · by_cases ho : o = out
      · subst ho
        obtain ⟨c, hc₁, hc₂⟩ := hmatch ctx n o l h
        have hprod : produces M' c ctx o := by
          have := hmachine ctx n o l c h hc₁
          simp [produces, this]
        have hKP : KP M' o ctx ≤ (programLength c : ENat) :=
          KP_le_programLength_of_produces hprod
        simpa [complexityWeight_programLength, progWeight, programLength, hc₂]
          using complexityWeight_le_of_le hKP
      · simp [ho]
  refine ⟨K, fun out ctx => ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ K * f out ctx
      ≤ (2 : ℝ≥0∞)⁻¹ ^ K * ((2 : ℝ≥0∞) ^ K *
          (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) := by
        gcongr
        exact hgeo ctx out
    _ = (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
        rw [← mul_assoc, ← mul_pow,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
    _ ≤ complexityWeight (KP M' out ctx) := hS ctx out

/-- **The abstract Kraft–Chaitin realization engine, unit-mass interface.**

This is the genuinely hard online prefix-free allocator, stated at the *unit mass*
level: a lower-semicomputable `f` whose per-context total mass is `≤ 1` is realized
by a genuine prefix decompressor up to an additive coding constant.

This is strictly more specific than the previous `2^d`-mass obligation: the
down-scaling reduction (`IsLSC.div_two_pow` plus the `ℝ≥0∞` exponent algebra) is
*proved* in `kraftChaitin_realization_bound` below, so the only remaining missing
content is the online leftmost-free-dyadic-interval allocator at mass `≤ 1`
(`exists_online_prefixFree_of_kraft_le_one`, to be built in a separate
`KraftChaitinOnline.lean`). -/
theorem kraftChaitin_realization_bound_unit {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- The genuinely hard online allocator (leftmost-free-dyadic-interval) at mass ≤ 1:
  -- 1. Extract the dyadic increments from `hlsc` as a computable request stream.
  obtain ⟨req, K, hreq_comp, hreq_wt, hgeo⟩ := extract_request_stream_geometric hlsc h_sum
  -- 2 & 3. Allocate prefix-free programs of the requested lengths online.
  obtain ⟨alloc, halloc_comp, halloc_match, halloc_pref⟩ := exists_online_prefixFree_family req hreq_comp hreq_wt
  -- 4. Construct `M'` via `Partrec` combinators from the resulting computable allocator.
  obtain ⟨M', hM', hM_match⟩ := construct_prefix_machine req alloc hreq_comp halloc_comp halloc_match halloc_pref
  obtain ⟨c₀, hc₀⟩ := realization_bound_of_machine f req alloc M' K halloc_match hM_match hgeo
  exact ⟨M', hM', c₀, hc₀⟩

theorem kraftChaitin_realization_bound {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f) (d : ℕ)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- Reduce the `2^d`-mass case to the unit-mass interface by dividing `f` by `2^d`.
  have hg_lsc : IsLSC (fun out ctx => f out ctx / (2 : ℝ≥0∞) ^ d) := hlsc.div_two_pow d
  have hg_sum : ∀ ctx : BitString,
      (∑' out : BitString, f out ctx / (2 : ℝ≥0∞) ^ d) ≤ 1 := by
    intro ctx
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [ENNReal.tsum_mul_left]
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_one]
    exact h_sum ctx
  obtain ⟨M', hM', c₀, hc₀⟩ := kraftChaitin_realization_bound_unit hg_lsc hg_sum
  refine ⟨M', hM', c₀ + d, fun out ctx => ?_⟩
  have hkey := hc₀ out ctx
  have hrw : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + d) * f out ctx
      = (2 : ℝ≥0∞)⁻¹ ^ c₀ * (f out ctx / (2 : ℝ≥0∞) ^ d) := by
    rw [pow_add, div_eq_mul_inv]
    simp only [← ENNReal.inv_pow]
    ring
  rw [hrw]
  exact hkey

end Kolmogorov
