/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Native.Referees.EffectiveInterface

/-!
# Correct clocked deciders and an effective referee family

This module enumerates all native machine, clock exponent, search index, and oracle flag
combinations, repeating each tuple at arbitrarily large positive indices. Their finite counting
referees form a computable `RefereeFamily` with polynomial query bounds and arbitrarily late
admissible occurrences (blueprint node `native:family`). The enumeration is independent of the
constructed decompressor: search indices are included as literal data.

For a clocked decider of the halting language on the actual native oracle, adapter correctness
identifies the referee's threshold tests with comparisons against the cumulative complexity
count. Binary-search correctness then gives `native_referee_counts_of_clocked_decider`
(blueprint node `native:correct-referee`). Through `Native.Referees`, these results supply the
family and correctness theorem used by the native oracle separation in `Plain.Target`.
-/

namespace Kolmogorov.Milovanov

open RandomStrings

/-- The computable surjection `γ`, decoding all OTM, exponent, index, and flag combinations.
Blueprint node `native:family` (supporting definition). No decompressor is an input. -/
def nativeTupleEnumeration (n : ℕ) : NativeTuple :=
  (decodeCode n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2.unpair.1,
    NativeOracleFlag.equivBool.symm (decide (n.unpair.2.unpair.2.unpair.2 % 2 = 1)))

/-- Every tuple is represented by the explicit surjection.
Blueprint node `native:family` (supporting lemma). -/
theorem native_tuple_enumeration_surjective : Function.Surjective nativeTupleEnumeration := by
  rintro ⟨c, e, e₀, flag⟩
  refine ⟨Nat.pair (encodeCode c) (Nat.pair e
    (Nat.pair e₀ (if NativeOracleFlag.equivBool flag then 1 else 0))), ?_⟩
  cases flag <;>
    simp [nativeTupleEnumeration, Nat.unpair_pair, decodeCode_encodeCode,
      NativeOracleFlag.equivBool]

/-- Positive-index repetition `l ↦ γ((l-1).unpair.1)`; index zero is an unused default.
Blueprint node `native:family` (supporting definition). -/
def nativeTupleAt (l : ℕ) : NativeTuple := nativeTupleEnumeration (l - 1).unpair.1

/-- Uniformly computable machine fields and transitions give computable canonical table codes. -/
private lemma computable_codeOfTable
    (γ : ℕ → OTMCode)
    (hk : Computable fun e ↦ (γ e).k)
    (hs : Computable fun e ↦ ((γ e).start : ℕ))
    (ha : Computable fun e ↦ ((γ e).accept : ℕ))
    (hr : Computable fun e ↦ ((γ e).reject : ℕ))
    (ht : Computable fun p : ℕ × ℕ × Sym ↦
      actTable (γ p.1) p.2.1 p.2.2) :
    Computable fun e ↦ codeOfTable (γ e).k (γ e).start
      (γ e).accept (γ e).reject (actTable (γ e)) := by
  have hentry : Computable (fun p : ℕ × ℕ × List ℕ ↦
      convAct (actTable (γ p.1) (p.2.1 / 3) (symOf (p.2.1 % 3)))) := by
    have hstate : Computable (fun p : ℕ × ℕ × List ℕ ↦ p.2.1 / 3) :=
      Primrec.nat_div.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 3)
    have hsym : Computable (fun p : ℕ × ℕ × List ℕ ↦ symOf (p.2.1 % 3)) :=
      symOf_primrec.to_comp.comp
        (Primrec.nat_mod.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 3))
    exact convAct_primrec.to_comp.comp (ht.comp (Computable.fst.pair (hstate.pair hsym)))
  have happend : Computable (fun p : ℕ × ℕ × List ℕ ↦
      p.2.2 ++ [convAct (actTable (γ p.1) (p.2.1 / 3) (symOf (p.2.1 % 3)))]) :=
    Primrec.list_concat.to_comp.comp (Computable.snd.comp Computable.snd) hentry
  have hL : Computable fun e ↦ tableList (actTable (γ e)) (3 * (γ e).k) := by
    have h := Computable.nat_rec (f := fun e ↦ 3 * (γ e).k) (g := fun _ ↦ ([] : List ℕ))
      (h := fun e (p : ℕ × List ℕ) ↦
        p.2 ++ [convAct (actTable (γ e) (p.1 / 3) (symOf (p.1 % 3)))])
      (Primrec.nat_mul.to_comp.comp (Computable.const 3) hk) (Computable.const []) happend
    refine h.of_eq fun e ↦ ?_
    generalize 3 * (γ e).k = n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [tableList_succ]
      exact congrArg (fun L ↦ L ++ [convAct (actTable (γ e) (n / 3) (symOf (n % 3)))]) ih
  exact ((Primrec₂.natPair.to_comp).comp ((Primrec.nat_sub.to_comp).comp hk (Computable.const 1))
    ((Primrec₂.natPair.to_comp).comp hs ((Primrec₂.natPair.to_comp).comp ha
      ((Primrec₂.natPair.to_comp).comp hr (Computable.encode.comp hL))))).of_eq fun _ ↦ rfl

/-- Decoding and canonically re-encoding an OTM code is computable. -/
private lemma computable_encodeCode_decodeCode :
    Computable (fun n ↦ encodeCode (decodeCode n)) := by
  have ht : Computable (fun p : ℕ × ℕ × Sym ↦
      actTable (decodeCode p.1) p.2.1 p.2.2) :=
    tableNum_primrec.to_comp.of_eq
      (fun p ↦ (tableNum_spec p.1 p.2.1 p.2.2).symm)
  have h := computable_codeOfTable
    decodeCode codeK_primrec.to_comp codeStart_primrec.to_comp
    codeAcc_primrec.to_comp codeRej_primrec.to_comp ht
  simpa only [codeOfTable_eq] using h

/-- Both the surjection and the repeated sequence have uniformly computable finite codes.
Blueprint node `native:family` (supporting lemma). -/
theorem native_tuple_enumeration_computable :
    Computable (fun n => encodeNativeTuple (nativeTupleEnumeration n)) ∧
      Computable (fun l => encodeNativeTuple (nativeTupleAt l)) := by
  have hc : Computable (fun n : ℕ ↦ encodeCode (decodeCode n.unpair.1)) :=
    computable_encodeCode_decodeCode.comp (Computable.fst.comp Computable.unpair)
  have htail : Computable (fun n : ℕ ↦ n.unpair.2.unpair) :=
    Computable.unpair.comp (Computable.snd.comp Computable.unpair)
  have hlast : Computable (fun n : ℕ ↦ n.unpair.2.unpair.2.unpair) :=
    Computable.unpair.comp (Computable.snd.comp htail)
  have he : Computable (fun n : ℕ ↦ n.unpair.2.unpair.1) := Computable.fst.comp htail
  have he₀ : Computable (fun n : ℕ ↦ n.unpair.2.unpair.2.unpair.1) :=
    Computable.fst.comp hlast
  have hf : Computable (fun n : ℕ ↦ NativeOracleFlag.equivBool.symm
      (decide (n.unpair.2.unpair.2.unpair.2 % 2 = 1))) := by
    have hmod : Computable (fun n : ℕ ↦ n.unpair.2.unpair.2.unpair.2 % 2) :=
      Primrec.nat_mod.to_comp.comp (Computable.snd.comp hlast) (Computable.const 2)
    have heq := (PrimrecRel.decide Primrec.eq).to_comp.comp hmod (Computable.const 1)
    have hsymm := (Primrec.of_equiv_symm (e := NativeOracleFlag.equivBool)).to_comp
    exact hsymm.comp heq
  have hEnumeration : Computable (fun n ↦ encodeNativeTuple (nativeTupleEnumeration n)) :=
    (hc.pair (he.pair (he₀.pair hf))).of_eq (fun _ ↦ rfl)
  have hRepeated : Computable (fun l ↦ encodeNativeTuple (nativeTupleAt l)) := by
    have hsub := (Primrec.nat_sub.to_comp).comp Computable.id (Computable.const 1)
    have hunpair := Computable.fst.comp (Computable.unpair.comp hsub)
    exact (hEnumeration.comp hunpair).of_eq (fun _ ↦ rfl)
  exact ⟨hEnumeration, hRepeated⟩

/-- Every tuple occurs beyond every cutoff at a positive index.
Blueprint node `native:family` (supporting lemma). This is the infinite-repetition assertion. -/
theorem native_tuple_occurs_above (θ : NativeTuple) (index : ℕ) :
    ∃ l : ℕ, index < l ∧ 1 ≤ l ∧ nativeTupleAt l = θ := by
  obtain ⟨n, hn⟩ := native_tuple_enumeration_surjective θ
  refine ⟨Nat.pair n index + 1, by have := Nat.right_le_pair n index; omega,
    by omega, ?_⟩
  simpa only [nativeTupleAt, Nat.add_sub_cancel, Nat.unpair_pair] using hn

/-- Executable tree data in exactly the abstract family's padding/index/input order.
Blueprint node `native:family` (supporting definition). -/
def nativeRefereeTree (cV d l m : ℕ) : QueryTree :=
  native_counting_referee cV (nativeTupleAt l) d m

/-- Executable family bounds retain the tuple's same polynomial at every occurrence.
Blueprint node `native:family` (supporting definition). -/
def nativeRefereeBound (l m : ℕ) : ℕ := nativeTupleBound (nativeTupleAt l) m

/-- Referee tree codes are computable uniformly in padding, occurrence index, and input size.
Blueprint node `native:family` (supporting lemma). -/
theorem native_referee_tree_computable (cV : ℕ) :
    Computable (fun input : ℕ × ℕ × ℕ =>
      (nativeRefereeTree cV input.1 input.2.1 input.2.2).encode) := by
  have htree := (native_referee_effective_interface cV).1
  have htuple := native_tuple_enumeration_computable.2
  have hinput : Computable (fun input : ℕ × ℕ × ℕ ↦
      (encodeNativeTuple (nativeTupleAt input.2.1), input.1, input.2.2)) :=
    Computable.pair (htuple.comp (Computable.fst.comp Computable.snd))
      (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))
  refine (htree.comp hinput).of_eq fun input ↦ ?_
  dsimp only [nativeRefereeTree]
  rw [decode_encode_native_tuple]

/-- Referee query bounds are computable uniformly in occurrence index and input size.
Blueprint node `native:family` (supporting lemma). -/
theorem native_referee_bound_computable :
    Computable (fun input : ℕ × ℕ => nativeRefereeBound input.1 input.2) := by
  have hbound : Computable (fun p : NativeTupleCode × ℕ ↦
      clock p.1.2.1 (nativeLiteralFactor p.1.2.2.1 * (p.2 + 1))) := by
    have he : Computable (fun p : NativeTupleCode × ℕ ↦ p.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have he₀ : Computable (fun p : NativeTupleCode × ℕ ↦ p.1.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
    have hlength : Computable (fun p : NativeTupleCode × ℕ ↦
        nativeLiteralFactor p.1.2.2.1 * (p.2 + 1)) :=
      Primrec.nat_mul.to_comp.comp (literal_threshold_instance_length.2.1.comp he₀)
        (Primrec.nat_add.to_comp.comp Computable.snd (Computable.const 1))
    exact clock_computable.comp he hlength
  exact (hbound.comp
    ((native_tuple_enumeration_computable.2.comp Computable.fst).pair Computable.snd)).of_eq
      (fun _ ↦ rfl)

/-- Every query in the referee tree obeys the bound of its enumerated tuple.
Blueprint node `native:family` (supporting lemma). -/
theorem native_referee_query_bound (cV d l m : ℕ) (_hl : 1 ≤ l)
    (q : Coordinate) (hq : q ∈ (nativeRefereeTree cV d l m).queries) :
    q.1.length ≤ nativeRefereeBound l m :=
  (native_referee_effective_interface cV).2.2 (nativeTupleAt l) d m |>.1 q hq

/-- The query bound at each positive occurrence is polynomial in the input size.
Blueprint node `native:family` (supporting lemma). -/
theorem native_referee_polynomial (l : ℕ) (_hl : 1 ≤ l) :
    PolynomialQueryBound (nativeRefereeBound l) :=
  native_tuple_bound_polynomial (nativeTupleAt l)

/-- Every positive occurrence has arbitrarily late repetitions of both its tree and bound.
Blueprint node `native:family` (supporting lemma). The same tuple repeats at all paddings. -/
theorem native_referee_repeats (cV d l : ℕ) (_hl : 1 ≤ l) (index : ℕ) :
    ∃ later, index < later ∧ 1 ≤ later ∧
      nativeRefereeTree cV d later = nativeRefereeTree cV d l ∧
      nativeRefereeBound later = nativeRefereeBound l := by
  obtain ⟨later, hindex, hpos, htuple⟩ := native_tuple_occurs_above (nativeTupleAt l) index
  refine ⟨later, hindex, hpos, ?_, ?_⟩
  · funext m
    change native_counting_referee cV (nativeTupleAt later) d m =
      native_counting_referee cV (nativeTupleAt l) d m
    rw [htuple]
  · funext m
    change nativeTupleBound (nativeTupleAt later) m = nativeTupleBound (nativeTupleAt l) m
    rw [htuple]

/-- The native trees and bounds form a computable, polynomially bounded, repeated referee family.
Blueprint node `native:family`. -/
theorem native_referee_family (cV : ℕ) :
    ∃ family : RefereeFamily, family.tree = nativeRefereeTree cV ∧
      family.bound = nativeRefereeBound := by
  exact ⟨{
    tree := nativeRefereeTree cV
    bound := nativeRefereeBound
    tree_computable := native_referee_tree_computable cV
    bound_computable := native_referee_bound_computable
    query_bound := native_referee_query_bound cV
    polynomial := native_referee_polynomial
    repeats := native_referee_repeats cV }, rfl, rfl⟩

/-- Each tuple has arbitrarily late admissible occurrences in any family with these data.
Blueprint node `native:family` (supporting lemma). The common threshold precedes padding. -/
theorem native_referee_late_admissible (cV n₀ : ℕ) (hn₀ : 32 ≤ n₀)
    (family : RefereeFamily) (htree : family.tree = nativeRefereeTree cV)
    (hbound : family.bound = nativeRefereeBound) (θ : NativeTuple)
    (d : ℕ) (hd : 1 ≤ d) (index : ℕ) :
    ∃ later, index < later ∧ family.tree d later = native_counting_referee cV θ d ∧
      family.bound later = nativeTupleBound θ ∧
      admissible_clocked_occurrence family cV n₀ d later := by
  obtain ⟨l, _, hl, htuple⟩ := native_tuple_occurs_above θ 0
  obtain ⟨later, hindex, ht, hb, ha⟩ :=
    clocked_machine_has_late_admissible_occurrence family cV n₀ l hn₀ hl d hd index
  refine ⟨later, hindex, ?_, ?_, ha⟩
  · rw [ht, htree]
    funext m
    change native_counting_referee cV (nativeTupleAt l) d m =
      native_counting_referee cV θ d m
    rw [htuple]
  · rw [hb, hbound]
    funext m
    change nativeTupleBound (nativeTupleAt l) m = nativeTupleBound θ m
    rw [htuple]

/-- Reading a coordinate list prepends its answers in reverse order to the initial table. -/
private lemma eval_nativeTableTree
    (out : NativeCoordinateTable → ℕ) (a : Coordinate → Bool)
    (l : List Coordinate) (tab : NativeCoordinateTable) :
    QueryTree.eval a (nativeTableTree out l tab) =
      out ((l.map (fun q ↦ (q, a q))).reverse ++ tab) := by
  induction l generalizing tab with
  | nil => rfl
  | cons q l ih =>
    cases h : a q <;>
      simp [nativeTableTree, QueryTree.eval, h, ih, List.reverse_cons, List.append_assoc]

/-- A table sampled from a function returns that function on every listed coordinate. -/
private lemma nativeCoordinateAnswer_map
    (l : List Coordinate) (a : Coordinate → Bool)
    (q : Coordinate) (hq : q ∈ l) :
    nativeCoordinateAnswer (l.map (fun r ↦ (r, a r))) q = a q := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    by_cases h : head = q
    · subst head
      simp [nativeCoordinateAnswer]
    · have hmem : q ∈ tail := (List.mem_cons.mp hq).resolve_left (Ne.symm h)
      simpa [nativeCoordinateAnswer, h] using ih hmem

/-- Normalization leaves answers unchanged at the coordinates retained for inspection. -/
private lemma normalizedAnswer_eq_of_mem_nativeCoordinateList
    (cU T : ℕ) (flag : NativeOracleFlag) (a : Coordinate → Bool)
    (q : Coordinate) (hq : q ∈ nativeCoordinateList cU flag T) :
    normalizedAnswer cU a q = a q := by
  have ⟨z, _, hzq⟩ := (native_coordinate_list_spec cU T flag).2.1 q |>.mp hq
  unfold nativeInspectedCoordinate at hzq
  cases h : nativeRawCoordinate flag z
  · simp [h] at hzq
  · rename_i raw_q
    simp only [h, Option.bind_eq_bind, Option.bind_some,
      Option.ite_none_right_eq_some, Option.some.injEq] at hzq
    rcases hzq with ⟨h_thresh, hzq'⟩
    subst hzq'
    unfold normalizedAnswer
    have h_false : decide (raw_q.1.length + cU ≤ raw_q.2) = false := by
      simp only [decide_eq_false_iff_not, not_le]
      exact h_thresh
    rw [h_false, Bool.false_or]

/-- A referee leaf depends only on answers at its listed coordinates. -/
private lemma nativeRefereeLeaf_congr
    (θ : NativeTuple) (cU m : ℕ) (t1 t2 : NativeCoordinateTable)
    (h : ∀ q ∈ nativeCoordinateList cU θ.2.2.2 (nativeTupleBound θ m),
      nativeCoordinateAnswer t1 q = nativeCoordinateAnswer t2 q) :
    nativeRefereeLeaf θ cU m t1 = nativeRefereeLeaf θ cU m t2 := by
  have hs :=
    (native_coordinate_list_spec cU (nativeTupleBound θ m) θ.2.2.2).2.2
  have h1 := hs t1 (nativeCoordinateAnswer t2) h
  have h2 := hs t2 (nativeCoordinateAnswer t2) (by
    intro q hq
    rfl)
  have ht : nativeRefereeRawTable θ cU m t1 =
      nativeRefereeRawTable θ cU m t2 := by
    unfold nativeRefereeRawTable
    apply List.map_congr_left
    intro z hz
    have hzlen : z.length ≤ nativeTupleBound θ m :=
      ((native_raw_words_spec.2 (nativeTupleBound θ m)).2 z).mp hz
    have heq := (h1 z hzlen).trans (h2 z hzlen).symm
    exact congrArg (fun b : Bool ↦ (z, b)) heq
  unfold nativeRefereeLeaf nativeRefereeTest
  rw [ht]

/-- Evaluating the referee is equivalent to evaluating its leaf on the sampled oracle table. -/
private lemma refereeSetOutput_native_counting_referee
    (A : Set Coordinate) (cV d m : ℕ) (θ : NativeTuple) :
    refereeSetOutput (d + cV) (native_counting_referee cV θ d m) A =
      nativeRefereeLeaf θ (d + cV) m
        ((nativeCoordinateList (d + cV) θ.2.2.2 (nativeTupleBound θ m)).map
          (fun q ↦ (q, coordinateOracleAnswer A q))) := by
  let coords := nativeCoordinateList (d + cV) θ.2.2.2 (nativeTupleBound θ m)
  let answer := coordinateOracleAnswer A
  unfold refereeSetOutput refereeOutput native_counting_referee
  rw [eval_nativeTableTree, List.append_nil]
  have hnormalized : coords.map (fun q ↦ (q, normalizedAnswer (d + cV) answer q)) =
      coords.map (fun q ↦ (q, answer q)) := by
    apply List.map_congr_left
    intro q hq
    rw [normalizedAnswer_eq_of_mem_nativeCoordinateList
      (d + cV) (nativeTupleBound θ m) θ.2.2.2 answer q hq]
  rw [hnormalized]
  apply nativeRefereeLeaf_congr
  intro q hq
  rw [← List.map_reverse, nativeCoordinateAnswer_map _ answer q (List.mem_reverse.mpr hq),
    nativeCoordinateAnswer_map _ answer q hq]

/-- Looking up a word in a table sampled from a function recovers its value. -/
private lemma lookupB_map
    (l : List BitString) (f : BitString → Bool) (x : BitString) (hx : x ∈ l) :
    lookupB x (l.map (fun a ↦ (a, f a))) = some (f x) := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    by_cases h : head = x
    · subst head
      simp [lookupB]
    · have hmem : x ∈ tail := (List.mem_cons.mp hx).resolve_left (Ne.symm h)
      simpa [lookupB, h] using ih hmem

/-- A materialized raw table agrees with the adapter on its universal word domain. -/
private lemma nativeRawTableAnswer_nativeRefereeRawTable
    (θ : NativeTuple) (m : ℕ) (cU : ℕ) (table : NativeCoordinateTable)
    (z : BitString) (hz : z ∈ nativeRawWords (nativeTupleBound θ m)) :
    nativeRawTableAnswer (nativeRefereeRawTable θ cU m table) z =
      native_oracle_answer_adapters cU θ.2.2.2 table z := by
  dsimp [nativeRawTableAnswer, nativeRefereeRawTable]
  rw [lookupB_map]
  · rfl
  · exact hz

/-- A correct clocked decider makes each referee test compare the actual count to its threshold. -/
private lemma nativeRefereeTest_eq_true_iff
    (U : Map) (cV d : ℕ) (hliteral : ∀ x,
      plainK U x ≤ (x.length + (d + cV) : ℕ))
    (θ : NativeTuple)
    (hsearch : ∀ m k, nativeThresholdInstance θ.2.2.1 m k ∈ HBin ↔
      k ≤ {x | plainK U x ≤ (m : ℕ)}.ncard)
    (hdecider : ClockedDecides θ.1 θ.2.1
      (nativeOracle θ.2.2.2 U) HBin)
    (m k : ℕ) (hk : k < 2 ^ (m + 1)) :
    nativeRefereeTest θ (d + cV) m
        ((nativeCoordinateList (d + cV) θ.2.2.2 (nativeTupleBound θ m)).map
          (fun q ↦ (q, coordinateOracleAnswer (actualCoordinateOracle U) q))) k = true ↔
      k ≤ {x | plainK U x ≤ (m : ℕ)}.ncard := by
  let cU := d + cV
  let T := nativeTupleBound θ m
  let z := nativeThresholdInstance θ.2.2.1 m k
  let L := nativeCoordinateList cU θ.2.2.2 T
  let tau := L.map (fun q ↦ (q, coordinateOracleAnswer (actualCoordinateOracle U) q))
  let rawTable := nativeRefereeRawTable θ cU m tau
  let B := nativeOracle θ.2.2.2 U
  have hT : clock θ.2.1 z.length ≤ T := native_referee_test_clock_le θ m k hk
  have h_adapter := clocked_acceptance_finite_table_adapter θ.1 θ.2.1 T rawTable z B hT (by
    intro w h_w_len
    have hz : w ∈ nativeRawWords T := by
      rw [(native_raw_words_spec.2 T).2 w]
      exact h_w_len
    have h_ans := nativeRawTableAnswer_nativeRefereeRawTable θ m cU tau w hz
    rw [h_ans]
    have h_coord := native_coordinate_list_spec cU T θ.2.2.2
    have h_adapter_corr := h_coord.2.2 tau (coordinateOracleAnswer (actualCoordinateOracle U)) (by
      intro q hq
      dsimp [tau]
      exact nativeCoordinateAnswer_map L
        (coordinateOracleAnswer (actualCoordinateOracle U)) q hq
    ) w h_w_len
    rw [h_adapter_corr]
    have h_oracle := (native_oracle_adapters_correct U cU hliteral).1 θ.2.2.2 w
    rw [h_oracle]
  )
  dsimp [nativeRefereeTest, z, rawTable, B, tau, L, T, cU] at *
  rw [h_adapter]
  have h_dec := hdecider (nativeThresholdInstance θ.2.2.1 m k)
  rw [← h_dec]
  rw [hsearch]

/-- A correct native decider makes its finite referee return the actual bounded-output count.
Blueprint node `native:correct-referee`. The conclusion uses exactly the stage-3 normalized
set evaluation consumed by the stage-5 diagonal, for one specified actual oracle only. -/
theorem native_referee_counts_of_clocked_decider (U : Map) (hU : isOptimalConditional U)
    (cV d : ℕ) (hliteral : ∀ x, plainK U x ≤ (x.length + (d + cV) : ℕ))
    (θ : NativeTuple)
    (hsearch : ∀ m k, nativeThresholdInstance θ.2.2.1 m k ∈ HBin ↔
      k ≤ {x | plainK U x ≤ (m : ℕ)}.ncard)
    (hdecider : ClockedDecides θ.1 θ.2.1 (nativeOracle θ.2.2.2 U) HBin) :
    ∀ m, refereeSetOutput (d + cV) (native_counting_referee cV θ d m)
      (actualCoordinateOracle U) = {x | plainK U x ≤ (m : ℕ)}.ncard := by
  -- Counting correctness needs no optimality beyond the stated literal and search properties.
  rcases hU with ⟨_, _⟩
  intro m
  rw [refereeSetOutput_native_counting_referee (actualCoordinateOracle U) cV d m θ]
  dsimp [nativeRefereeLeaf]
  have hbound : {x : BitString | plainK U x ≤ (m : ℕ)}.ncard < 2 ^ (m + 1) :=
    (simple_finite_card_lt U m).2
  exact native_binary_search_correct _ m _ hbound
    (nativeRefereeTest_eq_true_iff U cV d hliteral θ hsearch hdecider m)

end Kolmogorov.Milovanov
