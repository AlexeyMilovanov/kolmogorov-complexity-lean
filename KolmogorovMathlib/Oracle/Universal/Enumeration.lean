/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.OracleComputability
import KolmogorovMathlib.Prefix.Properties.Part01
import KolmogorovMathlib.Oracle.FinitePrefix
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Bounded oracle enumeration and relative enumerations

This module builds the bounded evaluator `oracleStage A t e n` for functions that are recursive
in the characteristic oracle of `A`: at stage `t` it tests every index `r < t`, unpairs it into a
prefix length and a running time, and runs the ordinary bounded evaluator of the code `e` on the
corresponding finite prefix of `A` and the input `n`. The first successful test is returned.
Stages are total and computable in the oracle (`oracleStage_computable`), successful outputs
persist (`oracleStage_persistent`), and every function recursive in the oracle is the union of
its stages for a suitable index (`oracleStage_universal`); `oracleEval` is the induced partial
evaluator (`oracleStage_evaluator`). This is blueprint node `oracle:bounded`.

On top of the evaluator the module proves blueprint node `oracle:enumeration`: a predicate is
`A`-c.e. exactly when it is the range of a total computable optional enumeration
(`relative_enumeration`), such an enumeration may be taken without repetitions
(`relative_enumeration_injective`), and the strict rational thresholds of an upper
semicomputable function form an `A`-c.e. set (`relative_enumeration_threshold`).

Finally `IsOptimalOraclePrefix` states optimality of a prefix decompressor among the prefix
decompressors computable in the characteristic oracle; the optimal oracle prefix machines
constructed in `KolmogorovMathlib.Oracle.Universal.Optimal` and the point-to-set principles
use it through these evaluators and enumerations.
-/

namespace Kolmogorov.PointToSet

open Nat.Partrec (Code)

open Classical in
/-- Test all paired prefix-length and time bounds below a stage, taking the first success.
The encoded ordinary program acts on a finite characteristic prefix and an input.
Blueprint node `oracle:bounded`. -/
noncomputable def oracleStage (A : Set ℕ) (t e n : ℕ) : Option ℕ :=
  (List.range t).findSome? fun r =>
    Code.evaln (Nat.unpair r).2 (Denumerable.ofNat Code e)
      (Encodable.encode
        ((List.range (Nat.unpair r).1).map (fun k => if k ∈ A then 1 else 0), n))

/-- Bounded evaluation is total and relative computable uniformly in stage, code and input.
Blueprint node `oracle:bounded`. -/
theorem oracleStage_computable (A : Set ℕ) :
    ComputableIn {charOracle A}
      (fun p : ℕ × ℕ × ℕ => oracleStage A p.1 p.2.1 p.2.2) := by
  classical
  have hchar : ComputableIn {charOracle A}
      (fun k : ℕ => if k ∈ A then 1 else 0) :=
    PartrecIn.oracle (charOracle A) (Set.mem_singleton _)
  -- Build the finite oracle prefix by appending one oracle answer at each step.
  have happ : Computable (fun p : List ℕ × ℕ => p.1 ++ [p.2]) :=
    Computable.list_append.comp Computable.fst
      (Computable.list_cons.comp Computable.snd (Computable.const []))
  have hpstep : ComputableIn₂ {charOracle A}
      (fun (_ : ℕ) (p : ℕ × List ℕ) =>
        p.2 ++ [if p.1 ∈ A then 1 else 0]) :=
    (happ.computableIn.comp
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (hchar.comp (ComputableIn.fst.comp ComputableIn.snd)))).to₂
  have hprefix : ComputableIn {charOracle A}
      (fun u : ℕ => (List.range u).map (fun k => if k ∈ A then 1 else 0)) := by
    refine (ComputableIn.nat_rec ComputableIn.id
      (ComputableIn.const ([] : List ℕ)) hpstep).of_eq ?_
    intro u
    change Nat.rec (motive := fun _ => List ℕ) []
      (fun k acc => acc ++ [if k ∈ A then 1 else 0]) u = _
    induction u with
    | zero => rfl
    | succ u ih =>
      simpa only [List.range_succ, List.map_append, List.map_singleton] using
        congrArg (fun l : List ℕ => l ++ [if u ∈ A then 1 else 0]) ih
  let test (p : ℕ × ℕ) (r : ℕ) : Option ℕ :=
    Code.evaln (Nat.unpair r).2 (Denumerable.ofNat Code p.1)
      (Encodable.encode
        ((List.range (Nat.unpair r).1).map (fun k => if k ∈ A then 1 else 0), p.2))
  -- Each test uses the ordinary bounded evaluator on a relatively computable prefix.
  have htime : Computable (fun p : (ℕ × ℕ) × ℕ => (Nat.unpair p.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have hcode : Computable (fun p : (ℕ × ℕ) × ℕ => Denumerable.ofNat Code p.1.1) :=
    (Computable.ofNat Code).comp (Computable.fst.comp Computable.fst)
  have hinput : ComputableIn {charOracle A}
      (fun p : (ℕ × ℕ) × ℕ => Encodable.encode
        ((List.range (Nat.unpair p.2).1).map (fun k => if k ∈ A then 1 else 0),
          p.1.2)) :=
    Computable.encode.computableIn.comp
      ((hprefix.comp (Computable.fst.comp
        (Computable.unpair.comp Computable.snd)).computableIn).pair
          (Computable.snd.comp Computable.fst).computableIn)
  have htest : ComputableIn₂ {charOracle A} test :=
    Code.primrec_evaln.to_comp.computableIn.comp
      ((htime.computableIn.pair hcode.computableIn).pair hinput)
  -- The accumulator keeps the first successful test when a new index is added.
  have hor : Computable (fun p : Option ℕ × Option ℕ => p.1.or p.2) :=
    Primrec.option_orElse.to_comp.of_eq fun p => by cases p.1 <;> rfl
  have hstep : ComputableIn₂ {charOracle A}
      (fun (p : ℕ × ℕ × ℕ) (q : ℕ × Option ℕ) => q.2.or (test p.2 q.1)) :=
    (hor.computableIn.comp
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (htest.comp (ComputableIn.snd.comp ComputableIn.fst)
          (ComputableIn.fst.comp ComputableIn.snd)))).to₂
  have hrec := ComputableIn.nat_rec ComputableIn.fst
    (ComputableIn.const (none : Option ℕ)) hstep
  refine hrec.of_eq fun p => ?_
  change Nat.rec (motive := fun _ => Option ℕ) none
    (fun r acc => acc.or (test p.2 r)) p.1 =
      (List.range p.1).findSome? (test p.2)
  generalize p.1 = t
  induction t with
  | zero => rfl
  | succ t ih =>
    simpa only [List.range_succ, List.findSome?_append, List.findSome?_singleton] using
      congrArg (fun o : Option ℕ => o.or (test p.2 t)) ih

/-- A successful stage output remains unchanged at every later stage.
Blueprint node `oracle:bounded`. -/
theorem oracleStage_persistent (A : Set ℕ) (e n v t s : ℕ) (hts : t ≤ s)
    (hv : oracleStage A t e n = some v) : oracleStage A s e n = some v := by
  unfold oracleStage at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hts
  rw [List.range_add, List.findSome?_append, hv, Option.some_or]

open Classical in
/-- The test performed by `oracleStage` at index `r`: run the ordinary bounded evaluator of the
code `e` for `(Nat.unpair r).2` steps on the characteristic prefix of `A` of length
`(Nat.unpair r).1` and the input `n`. -/
private noncomputable def stageTest (A : Set ℕ) (e n r : ℕ) : Option ℕ :=
  Code.evaln (Nat.unpair r).2 (Denumerable.ofNat Code e)
    (Encodable.encode
      ((List.range (Nat.unpair r).1).map (fun k => if k ∈ A then 1 else 0), n))

/-- A stage is the first successful test among the indices below it. -/
private theorem oracleStage_eq_findSome (A : Set ℕ) (t e n : ℕ) :
    oracleStage A t e n = (List.range t).findSome? (stageTest A e n) :=
  rfl

/-- Every partial recursive function of finite strings and numbers is computed by an ordinary
code under bounded evaluation, with the output in the range of the bounded evaluator. -/
private theorem exists_code_evaln_of_partrec {σ : Type*} [Primcodable σ] (Φ : σ →. ℕ)
    (hΦ : Partrec Φ) :
    ∃ e : ℕ, ∀ (x : σ) (v : ℕ), v ∈ Φ x ↔
      ∃ k, Code.evaln k (Denumerable.ofNat Code e) (Encodable.encode x) = some v := by
  let f : ℕ →. ℕ := fun x => (Part.ofOption (Encodable.decode (α := σ) x)).bind Φ
  have hf : Nat.Partrec f :=
    Partrec.nat_iff.mp
      (Partrec.bind (Computable.ofOption Computable.decode) (hΦ.comp Computable.snd))
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨Encodable.encode c, fun x v => ?_⟩
  have heval : c.eval (Encodable.encode x) = Φ x := by
    rw [hc]
    change (Part.ofOption (Encodable.decode (α := σ) (Encodable.encode x))).bind Φ = Φ x
    rw [Encodable.encodek]
    exact Part.bind_some _ Φ
  rw [Denumerable.ofNat_encode, ← heval]
  exact Code.evaln_complete

/-- If all successful tests of an index agree on the value `v`, then one successful test
yields `v` as the output of some stage. -/
private theorem exists_oracleStage_eq_some_of_stageTest (A : Set ℕ) (e n v : ℕ)
    (hcoh : ∀ r w, stageTest A e n r = some w → w = v)
    (hr : ∃ r, stageTest A e n r = some v) : ∃ t, oracleStage A t e n = some v := by
  obtain ⟨r, hr⟩ := hr
  refine ⟨r + 1, ?_⟩
  rw [oracleStage_eq_findSome]
  cases h : (List.range (r + 1)).findSome? (stageTest A e n) with
  | none =>
    have hnone := List.findSome?_eq_none_iff.mp h r (List.mem_range.mpr r.lt_succ_self)
    rw [hr] at hnone
    exact absurd hnone (by simp)
  | some w =>
    obtain ⟨r', _, hr'⟩ := List.exists_of_findSome?_eq_some h
    rw [hcoh r' w hr']

/-- Every relative partial function has an index with exactly its outputs.
Blueprint node `oracle:bounded`. -/
theorem oracleStage_universal (A : Set ℕ) (f : ℕ →. ℕ)
    (hf : PartrecIn {charOracle A} f) :
    ∃ e, ∀ n v, v ∈ f n ↔ ∃ t, oracleStage A t e n = some v := by
  classical
  obtain ⟨Φ, hΦ, _, hex⟩ :=
    exists_exact_string_operator (fun (j : ℕ) => if j ∈ A then 1 else 0) f hf
  obtain ⟨e, hcode⟩ := exists_code_evaln_of_partrec Φ hΦ
  refine ⟨e, fun n v => ⟨fun hv => ?_, ?_⟩⟩
  · obtain ⟨u, hu⟩ := (hex n v).mp hv
    obtain ⟨k, hk⟩ := (hcode _ v).mp hu
    refine exists_oracleStage_eq_some_of_stageTest A e n v (fun r w hw => ?_)
      ⟨Nat.pair u k, by simpa only [stageTest, Nat.unpair_pair] using hk⟩
    have hmem := (hcode _ w).mpr ⟨(Nat.unpair r).2, hw⟩
    exact Part.mem_unique ((hex n w).mpr ⟨(Nat.unpair r).1, hmem⟩) hv
  · rintro ⟨t, ht⟩
    rw [oracleStage_eq_findSome] at ht
    obtain ⟨r, _, hr⟩ := List.exists_of_findSome?_eq_some ht
    exact (hex n v).mpr ⟨(Nat.unpair r).1, (hcode _ v).mpr ⟨(Nat.unpair r).2, hr⟩⟩

/-- The partial computation associated with a bounded oracle index searches for success.
Blueprint node `oracle:bounded`. -/
noncomputable def oracleEval (A : Set ℕ) (e n : ℕ) : Part ℕ :=
  Nat.rfindOpt fun t => oracleStage A t e n

/-- The induced universal evaluator is partial computable in the characteristic oracle.
Blueprint node `oracle:bounded`. -/
theorem oracleStage_evaluator (A : Set ℕ) :
    PartrecIn {charOracle A} (fun p : ℕ × ℕ => oracleEval A p.1 p.2) := by
  have hswap : ComputableIn {charOracle A} (fun p : (ℕ × ℕ) × ℕ => (p.2, p.1)) :=
    ComputableIn.pair ComputableIn.snd ComputableIn.fst
  have hstage' := (oracleStage_computable A).comp hswap
  have hstage : ComputableIn₂ {charOracle A} (fun (p : ℕ × ℕ) t => oracleStage A t p.1 p.2) :=
    ComputableIn₂.mk hstage'
  unfold oracleEval
  exact PartrecIn.rfindOpt hstage

variable {α : Type*} [Primcodable α]

/-- The partial function on codes of points of `α` which is `0` at the code of `w` exactly when
`f w` converges, and undefined at all other numbers. -/
private noncomputable def domainIndicator (f : α →. ℕ) : ℕ →. ℕ :=
  fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind fun w => (f w).map fun _ => 0

/-- The indicator of the domain of a relatively partial recursive function is itself relatively
partial recursive. -/
private theorem domainIndicator_partrecIn (A : Set ℕ) (f : α →. ℕ)
    (hf : PartrecIn {charOracle A} f) : PartrecIn {charOracle A} (domainIndicator f) :=
  PartrecIn.bind (Partrec.partrecIn (Computable.ofOption Computable.decode))
    (PartrecIn.map (PartrecIn.comp hf ComputableIn.snd) (ComputableIn.const 0))

/-- The optional enumeration read off from the stages of the index `i`: at the number `s` with
`Nat.unpair s = (n, t)` it outputs the point with code `n` when stage `t` succeeds on `n`, and
`none` otherwise. -/
private noncomputable def stageEnumeration (A : Set ℕ) (i s : ℕ) : Option α :=
  cond (oracleStage A (Nat.unpair s).2 i (Nat.unpair s).1).isSome
    (Encodable.decode (Nat.unpair s).1) none

/-- The optional enumeration read off from the stages of a fixed index is computable in the
characteristic oracle. -/
private theorem stageEnumeration_computable (A : Set ℕ) (i : ℕ) :
    ComputableIn {charOracle A} (stageEnumeration (α := α) A i) := by
  have hunpair : ComputableIn {charOracle A} (fun s : ℕ => Nat.unpair s) :=
    Computable.unpair.computableIn
  have hstage : ComputableIn {charOracle A}
      (fun s : ℕ => oracleStage A (Nat.unpair s).2 i (Nat.unpair s).1) :=
    (oracleStage_computable A).comp
      ((ComputableIn.snd.comp hunpair).pair
        ((ComputableIn.const i).pair (ComputableIn.fst.comp hunpair)))
  have hisSome : Computable (Option.isSome (α := ℕ)) := Primrec.option_isSome.to_comp
  have hselect : Computable (fun p : Bool × ℕ => cond p.1 (Encodable.decode (α := α) p.2) none) :=
    Computable.cond Computable.fst (Computable.decode.comp Computable.snd)
      (Computable.const none)
  exact hselect.computableIn.comp
    ((hisSome.computableIn.comp hstage).pair (ComputableIn.fst.comp hunpair))

/-- If the index `i` enumerates the codes of the points of `f.Dom` through its stages, then the
optional enumeration `stageEnumeration A i` lists exactly the points satisfying `F`. -/
private theorem stageEnumeration_spec (A : Set ℕ) (F : α → Prop) (f : α →. ℕ)
    (hF : ∀ w, F w ↔ (f w).Dom) (i : ℕ)
    (hi : ∀ n v, v ∈ domainIndicator f n ↔ ∃ t, oracleStage A t i n = some v) (w : α) :
    F w ↔ ∃ s, stageEnumeration A i s = some w := by
  constructor
  · intro hw
    have hdom : (f w).Dom := (hF w).mp hw
    have hzero : 0 ∈ (f w).map fun _ => 0 := ⟨hdom, rfl⟩
    have hmem : 0 ∈ domainIndicator f (Encodable.encode w) :=
      Part.mem_bind_iff.mpr ⟨w, Part.mem_ofOption.mpr (Encodable.encodek w), hzero⟩
    obtain ⟨t, ht⟩ := (hi _ 0).mp hmem
    exact ⟨Nat.pair (Encodable.encode w) t, by simp [stageEnumeration, ht, Encodable.encodek]⟩
  · rintro ⟨s, hs⟩
    cases h : oracleStage A (Nat.unpair s).2 i (Nat.unpair s).1 with
    | none => simp [stageEnumeration, h] at hs
    | some v =>
      have hdec : Encodable.decode (α := α) (Nat.unpair s).1 = some w := by
        simpa [stageEnumeration, h] using hs
      obtain ⟨w', hw', hv⟩ := Part.mem_bind_iff.mp ((hi _ v).mpr ⟨_, h⟩)
      have hww : w' = w := Option.some.inj ((Part.mem_ofOption.mp hw').symm.trans hdec)
      subst hww
      obtain ⟨hdom, _⟩ := hv
      exact (hF w').mpr hdom

/-- Every relatively c.e. predicate is the range of a total computable optional enumeration. -/
private theorem exists_enumeration_of_isREIn (A : Set ℕ) (F : α → Prop) (hF : IsREIn A F) :
    ∃ e : ℕ → Option α, IsEnumerationIn A F e := by
  obtain ⟨f, hf, hFdom⟩ := hF
  obtain ⟨i, hi⟩ := oracleStage_universal A _ (domainIndicator_partrecIn A f hf)
  exact ⟨stageEnumeration A i, stageEnumeration_computable A i,
    stageEnumeration_spec A F f hFdom i hi⟩

/-- The range of a total computable optional enumeration is relatively c.e.: search for a stage
at which the enumeration outputs the queried point. -/
private theorem isREIn_of_enumeration (A : Set ℕ) (F : α → Prop)
    (hF : ∃ e : ℕ → Option α, IsEnumerationIn A F e) : IsREIn A F := by
  obtain ⟨e, he_comp, he_range⟩ := hF
  let hit (a : α) (t : ℕ) : Option ℕ :=
    bif decide ((e t).map Encodable.encode = some (Encodable.encode a)) then some 0 else none
  have hhit : ComputableIn₂ {charOracle A} hit := by
    have hcodes : ComputableIn {charOracle A} (fun t : ℕ => (e t).map Encodable.encode) :=
      (Computable.option_map Computable.id
        ((Computable.encode.comp Computable.snd).to₂ :
          Computable₂ (fun (_ : Option α) (x : α) => Encodable.encode x))).computableIn.comp
        he_comp
    have hlhs : ComputableIn {charOracle A} (fun p : α × ℕ => (e p.2).map Encodable.encode) :=
      hcodes.comp ComputableIn.snd
    have hrhs : ComputableIn {charOracle A}
        (fun p : α × ℕ => some (Encodable.encode p.1)) :=
      (Computable.option_some.comp Computable.encode).computableIn.comp ComputableIn.fst
    have hbeq : Computable (fun p : Option ℕ × Option ℕ => decide (p.1 = p.2)) :=
      Primrec.beq.to_comp
    have hguard : ComputableIn {charOracle A}
        (fun p : α × ℕ =>
          decide ((e p.2).map Encodable.encode = some (Encodable.encode p.1))) :=
      hbeq.computableIn.comp (hlhs.pair hrhs)
    have hcond : Computable (fun b : Bool => cond b (some 0) (none : Option ℕ)) :=
      Computable.cond Computable.id (Computable.const (some 0)) (Computable.const none)
    exact ComputableIn₂.mk (hcond.computableIn.comp hguard)
  have hmem : ∀ w t, (∃ a, a ∈ hit w t) ↔ e t = some w := by
    intro w t
    have hiff : (e t).map Encodable.encode = some (Encodable.encode w) ↔ e t = some w := by
      cases e t <;> simp [Encodable.encode_injective.eq_iff]
    by_cases h : e t = some w
    · simp [hit, h]
    · simp [hit, hiff, h]
  refine ⟨fun a => Nat.rfindOpt (hit a), relative_closure_rfindOpt A hit hhit, fun w => ?_⟩
  rw [Nat.rfindOpt_dom, he_range w]
  exact exists_congr fun t => (hmem w t).symm

/-- Relative enumerable predicates are exactly ranges of total optional enumerations.
Blueprint node `oracle:enumeration`. -/
theorem relative_enumeration (A : Set ℕ) (F : α → Prop) :
    IsREIn A F ↔ ∃ e : ℕ → Option α, IsEnumerationIn A F e :=
  ⟨exists_enumeration_of_isREIn A F, isREIn_of_enumeration A F⟩

/-- The projection of a relatively enumerable predicate on a product along its second factor
is relatively enumerable. -/
theorem IsREIn.exists {β : Type*} [Primcodable β] {A : Set ℕ} {F : α × β → Prop} (hF : IsREIn A F) :
    IsREIn A (fun x ↦ ∃ y, F (x, y)) := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A F).mp hF
  refine (relative_enumeration A _).mpr ⟨fun n ↦ (e n).map Prod.fst, ?_, fun x ↦ ?_⟩
  · have hm : Computable (fun o : Option (α × β) ↦ o.map Prod.fst) :=
      Computable.option_map Computable.id (Computable.fst.comp Computable.snd).to₂
    exact hm.computableIn.comp he
  · constructor
    · rintro ⟨y, hy⟩
      obtain ⟨n, hn⟩ := (henum (x, y)).mp hy
      exact ⟨n, by simp [hn]⟩
    · rintro ⟨n, hn⟩
      obtain ⟨⟨x', y⟩, hxy, rfl⟩ := Option.map_eq_some_iff.mp hn
      exact ⟨y, (henum (x', y)).mpr ⟨n, hxy⟩⟩

/-- The image of a relatively enumerable predicate under a computable map is relatively
enumerable. -/
theorem IsREIn.image {β : Type*} [Primcodable β] {A : Set ℕ} {F : α → Prop}
    (hF : IsREIn A F) {g : α → β} (hg : Computable g) :
    IsREIn A (fun b ↦ ∃ a, F a ∧ g a = b) := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A F).mp hF
  refine (relative_enumeration A _).mpr ⟨fun n ↦ (e n).map g, ?_, fun b ↦ ?_⟩
  · have hm : Computable (fun o : Option α ↦ o.map g) :=
      Computable.option_map Computable.id (hg.comp Computable.snd).to₂
    exact hm.computableIn.comp he
  · constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨n, hn⟩ := (henum a).mp ha
      exact ⟨n, by simp [hn]⟩
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, hab⟩ := Option.map_eq_some_iff.mp hn
      exact ⟨a, (henum a).mpr ⟨n, ha⟩, hab⟩

omit [Primcodable α] in
/-- Keep an optional enumeration only at the stages where its value does not occur earlier. -/
private def firstOccurrences [DecidableEq α] (e : ℕ → Option α) : ℕ → Option α :=
  fun t => if (List.range t).any (fun s => decide (e s = e t)) then none else e t

/-- Deduplicating a relatively computable optional enumeration keeps it relatively computable. -/
private theorem firstOccurrences_computable [DecidableEq α] (A : Set ℕ) (e : ℕ → Option α)
    (he : ComputableIn {charOracle A} e) :
    ComputableIn {charOracle A} (firstOccurrences e) := by
  have heq : ComputableIn {charOracle A}
      (fun p : ℕ × (ℕ × Bool) => decide (e p.2.1 = e p.1)) :=
    primrec_decideEq.computableIn.comp
      ((he.comp (ComputableIn.fst.comp ComputableIn.snd)).pair (he.comp ComputableIn.fst))
  have hstep : ComputableIn₂ {charOracle A}
      (fun (a : ℕ) (p : ℕ × Bool) => p.2 || decide (e p.1 = e a)) :=
    (Primrec.or.computableIn.comp ((ComputableIn.snd.comp ComputableIn.snd).pair heq)).to₂
  have hrec : ComputableIn {charOracle A}
      (fun a => @Nat.rec (fun _ => Bool) false (fun k ih => ih || decide (e k = e a)) a) :=
    ComputableIn.nat_rec ComputableIn.id (ComputableIn.const false) hstep
  have hrec_eq : ∀ a n, @Nat.rec (fun _ => Bool) false (fun k ih => ih || decide (e k = e a)) n =
      (List.range n).any (fun k => decide (e k = e a)) := by
    intro a n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.range_succ, ih]
  have hany : ComputableIn {charOracle A}
      (fun t => (List.range t).any (fun s => decide (e s = e t))) :=
    hrec.of_eq fun t => hrec_eq t t
  have hselect : Primrec (fun p : Bool × Option α => cond p.1 (none : Option α) p.2) :=
    Primrec.cond Primrec.fst (Primrec.const none) Primrec.snd
  exact (hselect.computableIn.comp (hany.pair he)).of_eq fun t => by
    simp only [firstOccurrences, Bool.cond_eq_ite]

omit [Primcodable α] in
/-- The deduplicated enumeration outputs `w` at a stage exactly when the original enumeration
outputs `w` there for the first time. -/
private theorem firstOccurrences_eq_some_iff [DecidableEq α] (e : ℕ → Option α) (t : ℕ) (w : α) :
    firstOccurrences e t = some w ↔ e t = some w ∧ ∀ s < t, e s ≠ some w := by
  unfold firstOccurrences
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  split_ifs with h
  · simp only [false_iff, not_and, not_forall]
    intro het
    obtain ⟨s, hs, hst⟩ := h
    exact ⟨s, hs, not_not.mpr (hst.trans het)⟩
  · exact ⟨fun het => ⟨het, fun s hs hse => h ⟨s, hs, hse.trans het.symm⟩⟩, fun H => H.1⟩

omit [Primcodable α] in
/-- Deduplication does not change the set of values that are enumerated. -/
private theorem exists_firstOccurrences_eq_some_iff [DecidableEq α] (e : ℕ → Option α) (w : α) :
    (∃ t, firstOccurrences e t = some w) ↔ ∃ t, e t = some w := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ((firstOccurrences_eq_some_iff e t w).mp ht).1⟩
  · intro hex
    refine ⟨Nat.find hex, (firstOccurrences_eq_some_iff e _ w).mpr ⟨Nat.find_spec hex, ?_⟩⟩
    exact fun s hs hse => Nat.find_min hex hs hse

omit [Primcodable α] in
/-- The deduplicated enumeration never outputs the same value at two different stages. -/
private theorem firstOccurrences_injective [DecidableEq α] (e : ℕ → Option α) {s t : ℕ} {w : α}
    (hs : firstOccurrences e s = some w) (ht : firstOccurrences e t = some w) : s = t := by
  rw [firstOccurrences_eq_some_iff] at hs ht
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hs.1 (ht.2 s h)
  · exact h
  · exact absurd ht.1 (hs.2 t h)

/-- Every relative enumerable predicate admits an enumeration with no repeated values.
Blueprint node `oracle:enumeration`. -/
theorem relative_enumeration_injective (A : Set ℕ) (F : α → Prop) (hF : IsREIn A F) :
    ∃ e : ℕ → Option α, IsEnumerationIn A F e ∧
      ∀ s t w, e s = some w → e t = some w → s = t := by
  let _ : DecidableEq α := Encodable.decidableEqOfEncodable α
  obtain ⟨e, he_comp, he_range⟩ := (relative_enumeration A F).mp hF
  exact ⟨firstOccurrences e,
    ⟨firstOccurrences_computable A e he_comp,
      fun w => (he_range w).trans (exists_firstOccurrences_eq_some_iff e w).symm⟩,
    fun _ _ _ hs ht => firstOccurrences_injective e hs ht⟩

/-- Whether stage `t` of the enumeration `e` lists a pair over the same point as `w` with a
strictly smaller rational. -/
private def thresholdWitness (e : ℕ → Option (α × ℚ)) (w : α × ℚ) (t : ℕ) : Bool :=
  match e t with
  | some wq' => decide (Encodable.encode wq'.1 = Encodable.encode w.1) && decide (wq'.2 < w.2)
  | none => false

/-- The threshold test of a relatively computable enumeration is computable in the oracle,
uniformly in the queried pair and the stage. -/
private theorem thresholdWitness_computable (A : Set ℕ) (e : ℕ → Option (α × ℚ))
    (he : ComputableIn {charOracle A} e) :
    ComputableIn {charOracle A} (fun pw : (α × ℚ) × ℕ => thresholdWitness e pw.1 pw.2) := by
  have hsame : Computable₂ (fun (p : (α × ℚ) × Option (α × ℚ)) (wq' : α × ℚ) =>
      decide (Encodable.encode wq'.1 = Encodable.encode p.1.1)) := by
    have hl : Computable₂ (fun (_ : (α × ℚ) × Option (α × ℚ)) (wq' : α × ℚ) =>
        Encodable.encode wq'.1) :=
      Computable.encode.comp₂ (Computable.fst.comp Computable.snd).to₂
    have hr : Computable₂ (fun (p : (α × ℚ) × Option (α × ℚ)) (_ : α × ℚ) =>
        Encodable.encode p.1.1) :=
      Computable.encode.comp₂ (Computable.fst.comp (Computable.fst.comp Computable.fst)).to₂
    exact (PrimrecRel.decide Primrec.eq).to_comp.comp₂ hl hr
  have hlt : Computable₂ (fun (p : (α × ℚ) × Option (α × ℚ)) (wq' : α × ℚ) =>
      decide (wq'.2 < p.1.2)) := by
    have hl : Computable₂ (fun (_ : (α × ℚ) × Option (α × ℚ)) (wq' : α × ℚ) => wq'.2) :=
      (Computable.snd.comp Computable.snd).to₂
    have hr : Computable₂ (fun (p : (α × ℚ) × Option (α × ℚ)) (_ : α × ℚ) => p.1.2) :=
      (Computable.snd.comp (Computable.fst.comp Computable.fst)).to₂
    exact (PrimrecRel.decide Kolmogorov.ComputableReals.primrec_ratLt).to_comp.comp₂ hl hr
  have hboth : Computable₂ (fun (p : (α × ℚ) × Option (α × ℚ)) (wq' : α × ℚ) =>
      decide (Encodable.encode wq'.1 = Encodable.encode p.1.1) && decide (wq'.2 < p.1.2)) := by
    have hcond := @Computable.cond _ _ _ _ _ _ _ hsame hlt (Computable.const false).to₂
    refine hcond.of_eq fun p => ?_
    dsimp only
    cases decide (Encodable.encode p.2.1 = Encodable.encode p.1.1.1) <;> rfl
  have hcases : Computable (fun p : (α × ℚ) × Option (α × ℚ) =>
      @Option.casesOn (α × ℚ) (fun _ => Bool) p.2 false (fun wq' =>
        decide (Encodable.encode wq'.1 = Encodable.encode p.1.1) &&
          decide (wq'.2 < p.1.2))) :=
    Computable.option_casesOn Computable.snd (Computable.const false) hboth
  refine (hcases.computableIn.comp
    (ComputableIn.pair ComputableIn.fst (he.comp ComputableIn.snd))).of_eq fun pw => ?_
  unfold thresholdWitness
  cases e pw.2 <;> rfl

/-- A pair `(w.1, q')` with `q' < w.2` is enumerated by `e` exactly when some stage of `e` passes
the threshold test at `w`. -/
private theorem exists_lt_enumerated_iff (U : α × ℚ → Prop) (e : ℕ → Option (α × ℚ))
    (he : ∀ x, U x ↔ ∃ t, e t = some x) (w : α × ℚ) :
    (∃ q' : ℚ, U (w.1, q') ∧ q' < w.2) ↔ ∃ t, thresholdWitness e w t = true := by
  constructor
  · rintro ⟨q', hU, hlt⟩
    obtain ⟨t, ht⟩ := (he _).mp hU
    exact ⟨t, by simp [thresholdWitness, ht, hlt]⟩
  · rintro ⟨t, ht⟩
    unfold thresholdWitness at ht
    cases het : e t with
    | none => simp [het] at ht
    | some wq' =>
      simp only [het, Bool.and_eq_true, decide_eq_true_eq] at ht
      have hfst : wq'.1 = w.1 := Encodable.encode_injective ht.1
      refine ⟨wq'.2, (he _).mpr ⟨t, ?_⟩, ht.2⟩
      rw [het, ← hfst]

omit [Primcodable α] in
/-- For an upper semicomputable function with enumerated strict upper bounds `U`, the value at
`w.1` is below `w.2` exactly when some bound `q' < w.2` at `w.1` is enumerated. -/
private theorem exists_lt_iff_exists_enumerated (F : α → Prop) (g : Subtype F → ℝ)
    (U : α × ℚ → Prop) (hsound : ∀ w q, U (w, q) → ∃ h : F w, g ⟨w, h⟩ < (q : ℝ))
    (hdense : ∀ w : Subtype F, ∀ ε : ℝ, 0 < ε → ∃ q : ℚ, U (w.val, q) ∧ (q : ℝ) < g w + ε)
    (w : α × ℚ) :
    (∃ h : F w.1, g ⟨w.1, h⟩ < (w.2 : ℝ)) ↔ ∃ q' : ℚ, U (w.1, q') ∧ q' < w.2 := by
  constructor
  · rintro ⟨hFw, hg⟩
    obtain ⟨q', hUq', hq'⟩ := hdense ⟨w.1, hFw⟩ ((w.2 : ℝ) - g ⟨w.1, hFw⟩) (sub_pos.mpr hg)
    exact ⟨q', hUq', by exact_mod_cast (by linarith : (q' : ℝ) < (w.2 : ℝ))⟩
  · rintro ⟨q', hUq', hlt⟩
    obtain ⟨hFw, hg⟩ := hsound w.1 q' hUq'
    exact ⟨hFw, hg.trans (by exact_mod_cast hlt)⟩

/-- Strict rational upper thresholds of a relative upper semicomputable function are
enumerable on the ambient type, uniformly in the threshold. Blueprint node `oracle:enumeration`. -/
theorem relative_enumeration_threshold (A : Set ℕ) (F : α → Prop)
    (g : Subtype F → ℝ) (hg : IsUpperSemicomputableOnIn A F g) :
    IsREIn A (fun w : α × ℚ => ∃ h : F w.1, g ⟨w.1, h⟩ < (w.2 : ℝ)) := by
  obtain ⟨U, hU_RE, hU_sound, hU_dense⟩ := hg
  obtain ⟨e, he_comp, he_enum⟩ := (relative_enumeration A U).mp hU_RE
  have hsearch : PartrecIn₂ {charOracle A} (fun w t => Part.some (thresholdWitness e w t)) :=
    (PartrecIn.some.comp (thresholdWitness_computable A e he_comp).partrecIn).to₂
  refine ⟨_, relative_closure_rfind A _ hsearch, fun w => ?_⟩
  refine (exists_lt_iff_exists_enumerated F g U hU_sound hU_dense w).trans
    ((exists_lt_enumerated_iff U e he_enum w).trans ?_)
  refine Iff.trans (exists_congr fun t => ?_)
    (Nat.rfind_dom (p := fun t => Part.some (thresholdWitness e w t))).symm
  exact ⟨fun h => ⟨Part.mem_some_iff.mpr h.symm, fun _ => Part.some_dom _⟩,
    fun h => (Part.mem_some_iff.mp h.1).symm⟩

/-- Prefix optimality relative to a total characteristic oracle uses the existing
decompressor, prefix-domain and `KP` interfaces. Blueprint node `oracle:universal`. -/
def IsOptimalOraclePrefix (A : Set ℕ) (U : Map) : Prop :=
  IsDecompressorIn (charOracle A) U ∧ IsPrefixMachine U ∧
    ∀ D : Map, IsDecompressorIn (charOracle A) D → IsPrefixMachine D →
      ∃ c : ℕ, ∀ x y, KP U x y ≤ KP D x y + (c : ENat)

end Kolmogorov.PointToSet
