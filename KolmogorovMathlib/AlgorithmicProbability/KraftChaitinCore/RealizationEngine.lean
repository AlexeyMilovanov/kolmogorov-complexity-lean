import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.Optimal
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.UniformNumerators

/-!
# From a lower-semicomputable function to a prefix machine

The engine behind the hard direction of the coding theorem.  It has three stages.

`IsLSC.truncate` makes a lower-semicomputable `f` globally subnormalized: it produces a
lower-semicomputable `g ≤ f` with total mass at most `2 ^ d` in every context, agreeing with
`f` wherever `f` already respected that bound, using the truncated approximation of
`LSCApproximation`.

`geomCross`, `geomReq` and `geomReq_computable` extract from such a `g` a computable *request
stream*: at each stage it requests the output whose approximation first crosses a given dyadic
level, and `geomReq_crossed_kraft_perOutput` bounds one output's contribution to the Kraft sum
by a geometric tail.

`exists_online_prefixFree_family` runs the online Kraft–Chaitin allocator on a request stream
of Kraft weight at most one, and `construct_prefix_machine` turns the resulting code
assignment into a prefix machine.  The Kraft bound for `geomReq` itself, and the theorems these
pieces prove, are in `GeometricBound`.
-/

namespace Kolmogorov
open scoped ENNReal

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
supremum of exact dyadic numerators over `2^{S}`. The
`truncG*`/`ev*`/`cumNum`/`incNum` lemmas above establish lower semicomputability
(`truncGapprox_mono`, `truncGapprox_computable`), the global `2^{d}` bound
(`tsum_truncG_le`), and agreement (`truncG_eq_f_of_le`). -/
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

/-! ### Kraft–Chaitin realization engine

This section follows the truncation and `ev*` machinery so that
`extract_request_stream` can reuse it. -/

/-
Step 1: Extract dyadic increments from a unit-mass lower-semicomputable function
into a computable request stream family.
-/
lemma extract_request_stream {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ req : BitString → ℕ → Option (BitString × ℕ),
      Computable (fun p : BitString × ℕ => req p.1 p.2) ∧
      (∀ ctx : BitString,
        (∑' n, match req ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
          | none => 0) ≤ 1) ∧
      (∀ ctx out : BitString,
        (∑' n, match req ctx n with
          | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
          | none => 0) = f out ctx) := by
  obtain ⟨ approx, hmono ⟩ := hlsc;
  refine ⟨ fun ctx n =>
    if ( Nat.unpair n ).2 < evNum approx ( Nat.unpair n ).1 ctx then
      ( evOut ( Nat.unpair n ).1 ).map fun o => ( o, evK ( Nat.unpair n ).1 )
    else none, ?_, ?_, ?_ ⟩;
  · have h_cond : Computable
      (fun p : BitString × ℕ =>
        if (Nat.unpair p.2).2 < evNum approx (Nat.unpair p.2).1 p.1 then true
        else false) := by
      have h_cond : Computable (fun p : BitString × ℕ => evNum approx (Nat.unpair p.2).1 p.1) := by
        have := evNum_computable hmono.2.2;
        convert this.comp ( Computable.pair
          ( Computable.fst.comp ( Computable.unpair.comp ( Computable.snd ) ) )
          ( Computable.fst ) ) using 1;
      have h_cond : Computable (fun p : ℕ × ℕ => if p.1 < p.2 then true else false) := by
        convert Computable.of_eq _ _;
        · exact fun p => Nat.recOn ( p.2 - p.1 ) false fun _ _ => true;
        · apply Computable.nat_casesOn;
          · have h_cond : Computable (fun p : ℕ × ℕ => p.2 - p.1) := by
              exact (Primrec.nat_sub.comp ( Primrec.snd ) ( Primrec.fst )).to_comp;
            exact h_cond;
          · exact Computable.const false;
          · exact Computable.const true;
        · intro n
          cases le_total n.1 n.2 <;>
            simp only [*, Bool.and_true, Bool.ite_false_right, Nat.rec_zero,
              Nat.sub_eq_zero_of_le, false_eq_decide_iff, not_lt]
          cases lt_or_eq_of_le ‹_› <;>
            simp only [*, Nat.rec_zero, decide_false, decide_true, lt_self_iff_false,
              tsub_self]
          exact Nat.le_induction ( by tauto ) ( fun k hk ih => by tauto ) _
            ( Nat.sub_pos_of_lt ‹_› );
      convert h_cond.comp ( Computable.pair
        ( Computable.snd.comp ( Computable.unpair.comp ( Computable.snd ) ) )
        ‹Computable fun p : BitString × ℕ =>
          evNum approx ( Nat.unpair p.2 ).1 p.1› ) using 1;
    have h_map : Computable
        (fun p : BitString × ℕ =>
          Option.map (fun o => (o, evK (Nat.unpair p.2).1))
            (evOut (Nat.unpair p.2).1)) := by
      have h_map : Computable
          (fun p : ℕ => Option.map (fun o => (o, evK (Nat.unpair p).1))
            (evOut (Nat.unpair p).1)) := by
        have h_map : Computable (fun p : ℕ => evOut (Nat.unpair p).1) := by
          exact evOut_computable.comp ( Computable.fst.comp ( Computable.unpair ) );
        convert Computable.option_map h_map _ using 1;
        exact Computable.pair ( Computable.snd )
          ( Computable.comp ( evK_computable )
            ( Computable.fst.comp ( Computable.unpair.comp ( Computable.fst ) ) ) );
      exact h_map.comp ( Computable.snd );
    convert Computable.cond h_cond h_map ( Computable.const none ) using 1;
    ext a; by_cases h : (Nat.unpair a.2).2 < evNum approx (Nat.unpair a.2).1 a.1 <;> simp [h]
  · intro ctx
    -- Reindex the sum over `n` to a sum over `t` and `j`.
    have h_reindex :
        (∑' n : Nat, if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
          (2⁻¹ : ENNReal) ^ evK (Nat.unpair n).1 else 0) =
        (∑' t : Nat, ∑' j : Nat,
          if j < evNum approx t ctx then (2⁻¹ : ENNReal) ^ evK t else 0) := by
      rw [← ENNReal.tsum_prod]
      rw [← Equiv.tsum_eq (Equiv.ofBijective
        (fun n : Nat => ((Nat.unpair n).1, (Nat.unpair n).2))
        ⟨fun a b hab => by
            simpa using congr_arg
              (fun q : Nat × Nat => Nat.pair q.1 q.2) hab,
          fun q => ⟨Nat.pair q.1 q.2, by simp⟩⟩)]
      congr! 1
    have hrequest :
        (∑' n : Nat, match
          (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
            (evOut (Nat.unpair n).1).map
              (fun o => (o, evK (Nat.unpair n).1))
          else none) with
        | some (_, length) => (2 : ENNReal)⁻¹ ^ length
        | none => 0) =
        (∑' n : Nat, if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx then
          (2 : ENNReal)⁻¹ ^ evK (Nat.unpair n).1 else 0) := by
      refine tsum_congr fun n => ?_
      by_cases hlt : (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx
      · cases hout : evOut (Nat.unpair n).1 with
        | none => simp [evNum, hout] at hlt
        | some out => simp [hlt]
      · simp [hlt]
    have hinner : ∀ t : Nat,
        (∑' j : Nat, if j < evNum approx t ctx then
          (2⁻¹ : ENNReal) ^ evK t else 0) = evVal approx t ctx := by
      intro t
      rw [tsum_eq_sum]
      any_goals exact Finset.range (evNum approx t ctx)
      · simp only [Finset.sum_const, Finset.sum_ite, evVal, not_lt, nsmul_eq_mul]
        rw [Finset.filter_true_of_mem fun x hx => Finset.mem_range.mp hx]
        norm_num [dyadicValue]
        rw [div_eq_mul_inv, ENNReal.inv_pow]
      · aesop
    rw [hrequest, h_reindex]
    calc
      (∑' t : Nat, ∑' j : Nat, if j < evNum approx t ctx then
          (2⁻¹ : ENNReal) ^ evK t else 0) =
          ∑' t : Nat, evVal approx t ctx := tsum_congr hinner
      _ = ∑' out : BitString, f out ctx :=
        tsum_evVal hmono.1 hmono.2.1 ctx
      _ ≤ 1 := h_sum ctx
  · intro ctx out
    have h_sum_eq :
        (∑' n : ℕ, (if (Nat.unpair n).2 < evNum approx (Nat.unpair n).1 ctx ∧
          evOut (Nat.unpair n).1 = some out then
            (2 : ℝ≥0∞)⁻¹ ^ evK (Nat.unpair n).1
          else 0)) = f out ctx := by
      have h_sum_eq :
          ∑' t : ℕ, (if evOut t = some out then evVal approx t ctx else 0) =
            f out ctx := by
        convert tsum_evVal_out hmono.1 hmono.2.1 out ctx using 1;
      convert h_sum_eq using 1;
      have h_sum_eq : ∀ t : ℕ, ∑' j : ℕ,
          (if j < evNum approx t ctx ∧ evOut t = some out then (2 : ℝ≥0∞)⁻¹ ^ (evK t) else 0) = if
          evOut t = some out then evVal approx t ctx else 0 := by
        intro t
        split_ifs <;>
          simp_all only [and_false, and_true, dyadicValue, evVal, tsum_zero,
            ↓reduceIte]
        rw [ tsum_eq_sum ];
        any_goals exact Finset.range ( evNum approx t ctx );
        · rw [ Finset.sum_congr rfl fun x hx => ite_eq_left <| Finset.mem_range.mp hx ]
          norm_num [ div_eq_mul_inv ]
          norm_num [ ENNReal.inv_pow ];
        · intro b hb; rw [ite_eq_right (by simpa using hb)]
      rw [ ← funext h_sum_eq ];
      rw [ ← ENNReal.tsum_prod ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective
        ( fun n : ℕ => ( Nat.unpair n |>.1, Nat.unpair n |>.2 ) )
        ⟨ fun n => ?_, fun n => ?_ ⟩ ) ];
      · congr! 1;
      · exact fun m hm => by simpa using congr_arg ( fun p => Nat.pair p.1 p.2 ) hm;
      · exact ⟨ Nat.pair n.1 n.2, by simp only [Nat.unpair_pair, Prod.mk.eta] ⟩;
    convert h_sum_eq using 3;
    cases h : evOut ( Nat.unpair ‹_› ).1 <;> aesop

/-- **The online Kraft–Chaitin allocator.**

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
    (hweight : ∀ ctx,
      (∑' n, match req ctx n with
        | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
        | none => 0) ≤ 1) :
    ∃ alloc : BitString → ℕ → Option BitString,
      Computable (fun p : BitString × ℕ => alloc p.1 p.2) ∧
      (∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l) ∧
      (∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm → n ≠ m →
        ¬ List.IsPrefix cn cm) := by
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
  have hallocdec : Computable
      (fun p : BitString × BitString × ℕ => decide (alloc p.2.1 p.2.2 = some p.1)) := by
    have hdecid : Computable
        (fun p : Option BitString × BitString => decide (p.1 = some p.2)) := by
      have hdecid : Computable
          (fun p : Option BitString × Option BitString => decide (p.1 = p.2)) := by
        have hdecid : Primrec
            (fun p : Option BitString × Option BitString => decide (p.1 = p.2)) := by
          convert Primrec.eq;
          any_goals exact Option BitString;
          constructor <;> intro h <;> rw [ PrimrecRel ] at *;
          · convert h using 1;
            constructor <;> intro h <;> rw [ PrimrecPred ] at *;
            · assumption
            · exact ⟨ inferInstance, h ⟩;
          · obtain ⟨ _, hp ⟩ := h; exact hp.of_eq (fun _ => by congr);
        exact hdecid.to_comp;
      convert hdecid.comp
        ( Computable.fst.pair ( Computable.option_some.comp Computable.snd ) ) using 1;
    convert hdecid.comp
      ( hcomp.comp ( Computable.snd ) |> Computable.pair <| Computable.fst ) using 1
  have hreqdec : Computable (fun p : BitString × BitString × ℕ => (req p.2.1 p.2.2).isSome) := by
    have hreqdec : Computable (fun p : BitString × Nat => (req p.1 p.2).isSome) := by
      have hreqdec : Computable (fun p : BitString × Nat => req p.1 p.2) := hreqcomp
      convert Computable.comp _ hreqdec using 1;
      convert Primrec.option_isSome.to_comp using 1;
    convert hreqdec.comp
      ( Computable.fst.comp ( Computable.snd ) |> Computable.pair
        <| Computable.snd.comp ( Computable.snd ) ) using 1;
  have h_computable_and : Computable
      (fun p : BitString × BitString × ℕ =>
        decide (alloc p.2.1 p.2.2 = some p.1 ∧ (req p.2.1 p.2.2).isSome)) := by
    convert Computable.cond ( hallocdec ) ( hreqdec ) ( Computable.const false ) using 1;
    ext a; simp only [Bool.decide_and, Bool.decide_eq_true, Bool.cond_false_right]
  convert h_computable_and.comp
    ( Computable.fst.comp ( Computable.fst ) |> Computable.pair
      <| Computable.snd.comp ( Computable.fst ) |> Computable.pair
      <| Computable.snd ) using 1

/-
Partrec output stage used to build the prefix machine: at the found index `n`,
emit the first component of `req ctx n` (undefined if `req ctx n = none`).
-/
lemma construct_out_partrec (req : BitString → ℕ → Option (BitString × ℕ))
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Partrec₂ (fun (p : BitString × BitString) (n : ℕ) =>
      ((req p.2 n).map Prod.fst : Option BitString) |> Part.ofOption) := by
  -- The function `if p.2 = some x then some x.1 else none` is computable.
  have h_if_computable : Computable
      (fun p : Option (BitString × ℕ) => Option.map Prod.fst p) := by
    refine Computable.option_map ?_ ?_;
    · exact Computable.id;
    · exact Computable.fst.comp ( Computable.snd ) |> Computable.comp <| Computable.id;
  have h_partrec : Computable
      (fun p : (BitString × BitString) × ℕ => Option.map Prod.fst (req p.1.2 p.2)) := by
    convert h_if_computable.comp
      ( hreqcomp.comp ( Computable.snd.comp ( Computable.fst ) |> Computable.pair
        <| Computable.snd ) ) using 1;
  change Partrec (fun p : (BitString × BitString) × Nat =>
    Part.ofOption (Option.map Prod.fst (req p.1.2 p.2)))
  exact h_partrec.ofOption

/-
Step 4: Construct a prefix decompressor from an allocator and a request stream.
-/
lemma construct_prefix_machine (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (hreqcomp : Computable (fun p : BitString × ℕ => req p.1 p.2))
    (hcomp : Computable (fun p : BitString × ℕ => alloc p.1 p.2))
    (_halloc : ∀ ctx n o l, req ctx n = some (o, l) →
      ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hprefix : ∀ ctx n m cn cm, alloc ctx n = some cn → alloc ctx m = some cm →
      n ≠ m → ¬ List.IsPrefix cn cm) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧
      ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c →
        M' (c, ctx) = Part.some o := by
  refine ⟨ ?_, ⟨ ?_, ?_ ⟩, ?_ ⟩;
  · refine fun p =>
      ( Nat.rfind fun n => Part.some
        ( decide ( alloc p.2 n = some p.1 ∧ ( req p.2 n ).isSome = true ) ) ) >>=
        fun n => Part.ofOption ( ( req p.2 n ).map Prod.fst );
  · refine Partrec.bind ?_ ?_;
    · exact Partrec.rfind
        ((construct_pred_computable req alloc hreqcomp hcomp).partrec.to₂)
    · exact construct_out_partrec req hreqcomp
  · intro ctx p hp q hq hpre;
    simp_all only [Bool.decide_and, Bool.decide_eq_true,
      Option.isSome_map, Part.bind_dom, Part.bind_eq_bind,
      Part.ofOption_dom, Set.mem_ofPred_eq,
      domainAt, ne_eq]
    obtain ⟨n, hnMem, _⟩ := hp.1
    obtain ⟨m, hmMem, _⟩ := hq.1
    have hnPred :
        decide (alloc ctx n = some p ∧ (req ctx n).isSome = true) = true := by
      simpa using hnMem
    have hmPred :
        decide (alloc ctx m = some q ∧ (req ctx m).isSome = true) = true := by
      simpa using hmMem
    have hnAlloc : alloc ctx n = some p := (decide_eq_true_eq.mp hnPred).1
    have hmAlloc : alloc ctx m = some q := (decide_eq_true_eq.mp hmPred).1
    by_cases hnm : n = m
    · subst m
      rw [hnAlloc] at hmAlloc
      cases hmAlloc
      rfl
    · exact (hprefix ctx n m p q hnAlloc hmAlloc hnm hpre).elim
  · intro ctx n o l c hreq halloc'
    have hn : n ∈ Nat.rfind
        (show Nat →. Bool from fun n =>
          Part.some (decide (alloc ctx n = some c ∧ (req ctx n).isSome = true))) := by
      rw [Nat.mem_rfind];
      refine ⟨?_, fun {m} hm => ?_⟩;
      · simp only [Part.mem_some_iff, eq_comm (a := true), decide_eq_true_eq];
        exact ⟨halloc', by rw [hreq]; rfl⟩;
      · simp only [Part.mem_some_iff, eq_comm (a := false), decide_eq_false_iff_not, not_and];
        intro hm_alloc;
        exact absurd (List.prefix_refl c)
          (hprefix ctx n m c c halloc' hm_alloc (Nat.ne_of_lt hm).symm);
    rw [show Nat.rfind (show Nat →. Bool from fun n => Part.some
      (decide (alloc ctx n = some c ∧ (req ctx n).isSome = true))) =
        Part.some n from ?_]
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
def geomCross (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString)
    (l s : ℕ) : Prop :=
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

private lemma decide_and_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∧ b) = cond (decide a) (decide b) false := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

private lemma ite_eq_some {P : Prop} [Decidable P] {α : Type _} {x : α} :
    (if P then some x else none) = cond (decide P) (some x) none := by
  by_cases hP : P <;> simp_all

private def geomReqBody (approx : ℕ → BitString → BitString → ℕ)
    (p : (BitString × ℕ) × BitString) : Option (BitString × ℕ) :=
  if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
      ((evK (Nat.unpair p.1.2).1) = 0 ∨
        ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          ((evK (Nat.unpair p.1.2).1) - 1)) then
    some (p.2, ((Nat.unpair p.1.2).2))
  else none

private lemma geomReqBody_eq (approx : ℕ → BitString → BitString → ℕ)
    (p : (BitString × ℕ) × BitString) :
  geomReqBody approx p =
    if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
        ((evK (Nat.unpair p.1.2).1) = 0 ∨
          ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
            ((evK (Nat.unpair p.1.2).1) - 1)) then
      some (p.2, ((Nat.unpair p.1.2).2))
    else none := rfl

/-- The request stream extracted from a stage approximation: at stage `n` it requests the output
of the corresponding enumeration step at the dyadic precision that stage crosses. -/
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
  have hdec : Computable
      (fun q : ℕ × ℕ × BitString × BitString =>
        decide (2 ^ q.2.1 ≤ approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ (q.1 - 1))) := by
    have hdec : Computable
        (fun q : ℕ × ℕ × BitString × BitString =>
          approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ (q.1 - 1)) := by
      apply Computable.comp (Primrec.nat_mul.to_comp) (Computable.pair _ _);
      · convert hcomp.comp ( Computable.snd ) using 1;
      · convert primrec_two_pow_aux.to_comp.comp
          ( Primrec.nat_sub.comp ( Primrec.fst ) ( Primrec.const 1 ) |>
            Primrec.to_comp ) using 1;
    have hdec : Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
      convert Primrec.nat_le using 1;
      constructor <;> intro h <;> simp_all only [PrimrecPred, PrimrecRel];
      · exact ⟨ inferInstance, h ⟩;
      · exact PrimrecRel.decide Primrec.nat_le
    convert hdec.to_comp.comp ( Computable.pair
      ( primrec_two_pow_aux.to_comp.comp ( Computable.fst.comp ( Computable.snd ) ) )
      ‹Computable fun q : ℕ × ℕ × BitString × BitString =>
        approx q.2.1 q.2.2.1 q.2.2.2 * 2 ^ ( q.1 - 1 )› ) using 1;
  have hdec : Computable (fun q : ℕ × ℕ × BitString × BitString => decide (1 ≤ q.1)) := by
    have hdec : Computable (fun q : ℕ => decide (1 ≤ q)) := by
      convert Computable.of_eq _ _;
      · exact fun n => Nat.recOn n Bool.false fun _ _ => Bool.true;
      · exact Computable.nat_casesOn ( Computable.id )
          ( Computable.const false ) ( Computable.const true );
      · rintro ( _ | _ ) <;> rfl;
    exact hdec.comp ( Computable.fst );
  rename_i h
  exact (Computable.cond hdec h (Computable.const false)).of_eq fun q => by
    simp only [geomCross, decide_and_eq]

/-- The geometric request stream is computable (uniformly in `ctx`). -/
lemma geomReq_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : BitString × ℕ => geomReq approx p.1 p.2) := by
  change Computable (fun p : BitString × ℕ =>
    (evOut (Nat.unpair p.2).1).bind fun o => geomReqBody approx (p, o))
  have hl : Computable (fun p : BitString × ℕ => (Nat.unpair p.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have hevK_primrec : Primrec evK := Primrec.snd.comp Primrec.unpair
  have hs : Computable (fun p : BitString × ℕ => evK (Nat.unpair p.2).1) :=
    hevK_primrec.to_comp.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hevOut : Computable (fun p : BitString × ℕ => evOut (Nat.unpair p.2).1) :=
    evOut_computable.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hcond1 : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
        (evK (Nat.unpair p.1.2).1))) := by
    have h_cross := geomCross_decide_computable approx hcomp
    have h_args : Computable (fun p : (BitString × ℕ) × BitString =>
        (((Nat.unpair p.1.2).2), (evK (Nat.unpair p.1.2).1), p.2, p.1.1)) :=
      Computable.pair (hl.comp Computable.fst)
        (Computable.pair (hs.comp Computable.fst)
          (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
    exact (h_cross.comp h_args).of_eq (fun p => by dsimp only [Prod.fst, Prod.snd])
  have h_cross_eval : Computable
      (fun p : (BitString × ℕ) × BitString =>
        decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1 - 1))) := by
    have h_cross := geomCross_decide_computable approx hcomp
    have hsub : Computable
        (fun p : (BitString × ℕ) × BitString => evK (Nat.unpair p.1.2).1 - 1) := by
      have h_sub_primrec : Primrec (fun n : ℕ => n - 1) :=
        Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
      exact h_sub_primrec.to_comp.comp (hs.comp Computable.fst)
    have h_args : Computable (fun p : (BitString × ℕ) × BitString =>
        (((Nat.unpair p.1.2).2), (evK (Nat.unpair p.1.2).1 - 1), p.2, p.1.1)) :=
      Computable.pair (hl.comp Computable.fst)
        (Computable.pair hsub
          (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
    exact (h_cross.comp h_args).of_eq (fun p => by dsimp only [Prod.fst, Prod.snd])
  have heq0 : Computable
      (fun p : (BitString × ℕ) × BitString => decide (evK (Nat.unpair p.1.2).1 = 0)) := by
    have hsucc : Computable₂ (fun (n : ℕ) (m : ℕ) => false) := Computable.const false
    have h_dec : Computable (fun n : ℕ => decide (n = 0)) :=
      Computable.of_eq
        (Computable.nat_casesOn Computable.id (Computable.const true) hsucc)
        (by intro n; cases n <;> rfl)
    exact h_dec.comp (hs.comp Computable.fst)
  have hcond2 : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (evK (Nat.unpair p.1.2).1 = 0 ∨
        ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1 - 1))) := by
    have h_not : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1 - 1))) false true) :=
      Computable.cond h_cross_eval (Computable.const false) (Computable.const true)
    have h_or : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (evK (Nat.unpair p.1.2).1 = 0)) true
          (cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
            (evK (Nat.unpair p.1.2).1 - 1))) false true)) :=
      Computable.cond heq0 (Computable.const true) h_not
    exact h_or.of_eq (fun p => decide_or_not_eq.symm)
  have hcond : Computable (fun p : (BitString × ℕ) × BitString =>
      decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧
        (evK (Nat.unpair p.1.2).1 = 0 ∨
          ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
            (evK (Nat.unpair p.1.2).1 - 1)))) := by
    have h_and : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1)))
          (decide (evK (Nat.unpair p.1.2).1 = 0 ∨
            ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
              (evK (Nat.unpair p.1.2).1 - 1))) false) :=
      Computable.cond hcond1 hcond2 (Computable.const false)
    exact h_and.of_eq (fun p => decide_and_eq.symm)
  have hbranch : Computable
      (fun p : (BitString × ℕ) × BitString => geomReqBody approx p) := by
    have h_then : Computable
        (fun p : (BitString × ℕ) × BitString =>
          some (p.2, ((Nat.unpair p.1.2).2))) :=
      Computable.option_some.comp (Computable.pair Computable.snd (hl.comp Computable.fst))
    have h_else : Computable
        (fun p : (BitString × ℕ) × BitString => (none : Option (BitString × ℕ))) :=
      Computable.const none
    have h_ite : Computable (fun p : (BitString × ℕ) × BitString =>
        cond (decide (geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
          (evK (Nat.unpair p.1.2).1) ∧
          (evK (Nat.unpair p.1.2).1 = 0 ∨
            ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2)
              (evK (Nat.unpair p.1.2).1 - 1))))
          (some (p.2, ((Nat.unpair p.1.2).2))) none) :=
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
  unfold geomReq; simp only [Encodable.decode₂_encode, Nat.unpair_pair, Option.bind_some, evOut] ;
  convert geomReqBody_eq approx _ using 1;
  unfold evK; simp only [Nat.unpair_pair] ;

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
  · obtain ⟨L, hL⟩ : ∃ L, 1 ≤ L ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ (L - 1) ∧ ∀ l < L,
      ¬(1 ≤ l ∧ ∃ s, 2 ^ s ≤ approx s o ctx * 2 ^ (l - 1)) := by
      exact ⟨ Nat.find h, Nat.find_spec h |>.1, Nat.find_spec h |>.2.choose,
        Nat.find_spec h |>.2.choose_spec,
        fun l hl hl' => Nat.find_min h hl hl' ⟩;
    have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) ≤ f o ctx := by
      have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) = (2 : ℝ≥0∞)⁻¹ ^ (L - 1) := by
        have h_sum : (∑' l : ℕ, if L ≤ l then (2 : ℝ≥0∞)⁻¹ ^ l else 0) =
            (∑' l : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (L + l)) := by
          rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
          · use fun x => x.val - L;
          · -- Adding `L` to `x.val - L = y.val - L` gives `x.val = y.val`.
            intro x y hxy
            have h_eq : x.val = y.val := by
              linarith [ Nat.sub_add_cancel
                  ( show L ≤ x.val from by by_contra hc; exact x.2 (ite_eq_right hc) ),
                Nat.sub_add_cancel
                  ( show L ≤ y.val from by by_contra hc; exact y.2 (ite_eq_right hc) ) ]
            exact Subtype.ext h_eq;
          · exact fun x _ => ⟨⟨x + L, by simp⟩, by simp⟩
          · rintro ⟨x, hx⟩
            have hle : L ≤ x := by by_contra hc; exact hx (ite_eq_right hc)
            rw [Nat.add_sub_cancel' hle, ite_eq_left hle]
        simp_all +decide only [not_and, not_exists, not_le, exists_and_right,
          pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        rcases L with ( _ | L )
        · simp_all +decide only [zero_tsub, pow_zero, mul_one, not_lt_zero,
            not_isEmpty_of_nonempty, IsEmpty.forall_iff, implies_true, and_true, false_and]
        · simp_all +decide only [le_add_iff_nonneg_left, zero_le,
            add_tsub_cancel_right, Order.lt_add_one_iff, true_and,
            Order.add_one_le_iff, pow_succ, mul_assoc]
          rw [ ENNReal.inv_mul_cancel ] <;> norm_num
      obtain ⟨ s, hs₁, hs₂ ⟩ := hL.2;
      have h_le : (2 : ℝ≥0∞)⁻¹ ^ (L - 1) ≤ dyadicValue (approx s o ctx) s := by
        unfold dyadicValue; norm_num [ ENNReal.div_eq_inv_mul ] ;
        rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
        · field_simp;
          rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast <;> norm_num;
          exact_mod_cast hs₁;
        · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
      exact h_sum.symm ▸ h_le.trans
        ( hsup o ctx ▸ le_iSup ( fun s => dyadicValue ( approx s o ctx ) s ) s );
    convert h_sum using 3;
    split_ifs <;>
      simp_all +decide only [not_and, not_exists, not_le, exists_and_right,
        geomCross, exists_and_left, and_self_left, pow_eq_zero_iff', ENNReal.inv_eq_zero,
        ne_eq, false_and]
    · rename_i k hk₁ hk₂
      obtain ⟨x, hx⟩ := hk₁.2
      have contra := hL.2.2 k hk₂ hk₁.1 x
      exact (Nat.not_lt_of_ge hx contra).elim
    · rename_i k hk₁ hk₂;
      contrapose! hk₁;
      exact ⟨ by linarith, by
        obtain ⟨ x, hx ⟩ := hL.2.1
        exact ⟨ x, by
          exact le_trans hx ( Nat.mul_le_mul_left _
            ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_right hk₂ 1 ) ) ) ⟩ ⟩;
  · simp_all +decide only [not_exists, not_and, not_le, geomCross,
      exists_and_left, and_self_left]
    rw [ tsum_eq_single 0 ]
    · simp_all +decide only [zero_tsub, pow_zero, mul_one, false_and, ↓reduceIte,
        zero_le]
    · simp_all +decide only [ne_eq, ite_eq_right_iff, not_false_eq_true,
        pow_eq_zero_iff, ENNReal.inv_eq_zero, imp_false, not_and, not_exists, not_le,
        implies_true]

open Classical in
/-- Under stagewise monotonicity, the threshold-crossing predicate is monotone in
the stage: once level `l` is crossed it stays crossed. -/
lemma geomCross_succ_of_geomCross {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (o ctx : BitString) (l s : ℕ) (h : geomCross approx o ctx l s) :
    geomCross approx o ctx l (s + 1) := by
  rcases h with ⟨hl, hcross⟩
  refine ⟨hl, ?_⟩
  have hcrossE :
      (2 ^ s : ENNReal) ≤
        (approx s o ctx : ENNReal) * (2 ^ (l - 1) : ENNReal) := by
    exact_mod_cast hcross
  have hs0 : (2 ^ s : ENNReal) ≠ 0 := by positivity
  have hsTop : (2 ^ s : ENNReal) ≠ ∞ :=
    ENNReal.pow_ne_top (by norm_num)
  have hB0 : (2 ^ (l - 1) : ENNReal) ≠ 0 := by positivity
  have hBTop : (2 ^ (l - 1) : ENNReal) ≠ ∞ :=
    ENNReal.pow_ne_top (by norm_num)
  have hleft :
      (1 : ENNReal) / 2 ^ (l - 1) ≤
        (approx s o ctx : ENNReal) / 2 ^ s := by
    calc
      (1 : ENNReal) / 2 ^ (l - 1) =
          ((2 ^ s : ENNReal) * 1) /
            ((2 ^ s : ENNReal) * 2 ^ (l - 1)) :=
        (ENNReal.mul_div_mul_left 1 (2 ^ (l - 1)) hs0 hsTop).symm
      _ ≤ ((approx s o ctx : ENNReal) * 2 ^ (l - 1)) /
            ((2 ^ s : ENNReal) * 2 ^ (l - 1)) := by
        simpa using ENNReal.div_le_div hcrossE
          (le_refl ((2 ^ s : ENNReal) * 2 ^ (l - 1)))
      _ = (approx s o ctx : ENNReal) / 2 ^ s :=
        ENNReal.mul_div_mul_right
          (approx s o ctx : ENNReal) (2 ^ s) hB0 hBTop
  have hmonoE :
      (approx s o ctx : ENNReal) / 2 ^ s ≤
        (approx (s + 1) o ctx : ENNReal) / 2 ^ (s + 1) := by
    simpa only [dyadicValue] using hmono s o ctx
  have hchain :
      (1 : ENNReal) / 2 ^ (l - 1) ≤
        (approx (s + 1) o ctx : ENNReal) / 2 ^ (s + 1) :=
    hleft.trans hmonoE
  have hC0 : (2 ^ (s + 1) : ENNReal) ≠ 0 := by positivity
  have hCTop : (2 ^ (s + 1) : ENNReal) ≠ ∞ :=
    ENNReal.pow_ne_top (by norm_num)
  have hmul :
      ((1 : ENNReal) / 2 ^ (l - 1)) * 2 ^ (s + 1) ≤
        (approx (s + 1) o ctx : ENNReal) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCTop)).mp hchain
  have hdiv :
      (2 ^ (s + 1) : ENNReal) / 2 ^ (l - 1) ≤
        (approx (s + 1) o ctx : ENNReal) := by
    simpa only [ENNReal.div_eq_inv_mul, one_mul, mul_one, mul_comm] using hmul
  have hgoalE :
      (2 ^ (s + 1) : ENNReal) ≤
        (approx (s + 1) o ctx : ENNReal) * 2 ^ (l - 1) :=
    (ENNReal.div_le_iff hB0 hBTop).mp hdiv
  exact_mod_cast hgoalE

end Kolmogorov
