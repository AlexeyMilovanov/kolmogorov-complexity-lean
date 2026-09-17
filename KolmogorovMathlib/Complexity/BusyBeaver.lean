/-
Copyright (c) 2025 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.EnumerableFamilies.CalibratedComplexity
import KolmogorovMathlib.Complexity.EnumerableFamilies

/-!
# The busy beaver, and the nine canonical objects

`objBusyBeaver` is `B(n)`, the largest number with a program of length at most `n`, and
`objMaxTime` the maximal halting time `BB(n)`.  Around them this module fixes the nine
objects of SUV Theorem 15 — the list of strings of complexity at most `n` with their
complexities, their number, the busy beaver, the maximal halting time, the list of halting
programs of length at most `n`, and (in `CanonicalObjects/HubReductions`) the four remaining
ones — each of which the theorem shows to have complexity `n + O(1)` and to determine the
others.

The first half of the module is the effective apparatus these need:
`enumeratedLongString` with its computability, the argument tuples `evalnIsSomeArg` and
`searchEvalnArg` handed to `Code.evaln`, and the search functions `searchWitnessIndex` and
`searchWitnessString`.  The bounded halting problem of SUV Theorems 11–13 is treated in the
same terms.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The enumeration test `enumeratedLongString` is computable in the threshold and the stage. -/
private lemma computable_enumeratedLongString (cB : Code) :
    Computable (fun (p : ℕ × ℕ) => enumeratedLongString cB p.1 p.2) := by
  have h_eq : (fun (p : ℕ × ℕ) => enumeratedLongString cB p.1 p.2) =
      (fun p : ℕ × ℕ => ((Encodable.decode p.2.unpair.1 : Option BitString).bind (fun x =>
        if evalnIsSome cB (p.2.unpair.2 + 1) x && decide (2 * 2 ^ p.1 < x.length)
        then some () else none)).isSome) := by
    ext ⟨k, m⟩
    dsimp [enumeratedLongString]
    cases (Encodable.decode m.unpair.1 : Option BitString) with
    | none => rfl
    | some x =>
      dsimp
      cases hb : evalnIsSome cB (m.unpair.2 + 1) x <;>
        cases hd : decide (2 * 2 ^ k < x.length) <;> simp
  rw [h_eq]
  have hH : Computable (fun p : ℕ × ℕ => (Encodable.decode p.2.unpair.1 : Option BitString)) :=
    Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have hE : Computable (fun q : (ℕ × ℕ) × BitString =>
      evalnIsSome cB (q.1.2.unpair.2 + 1) q.2) :=
    Computable.comp (f := fun (p : ℕ × BitString) => evalnIsSome cB (p.1.unpair.2 + 1) p.2)
      (g := fun q : (ℕ × ℕ) × BitString => (q.1.2, q.2))
      (evalnIsSome_computable cB)
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
  have hF : Computable (fun q : (ℕ × ℕ) × BitString =>
      decide (2 * 2 ^ q.1.1 < q.2.length)) := by
    have h1 : Computable (fun q : (ℕ × ℕ) × BitString => 2 * 2 ^ q.1.1) :=
      (Primrec.to_comp Primrec.nat_mul).comp
        (Computable.pair (Computable.const 2)
          (Computable.pow2.comp (Computable.fst.comp Computable.fst)))
    have h2 : Computable (fun q : (ℕ × ℕ) × BitString => q.2.length) :=
      Computable.list_length.comp Computable.snd
    exact Computable.comp (f := fun r : ℕ × ℕ => decide (r.1 < r.2))
      (g := fun q : (ℕ × ℕ) × BitString => (2 * 2 ^ q.1.1, q.2.length))
      Computable.natLt (Computable.pair h1 h2)
  have hG : Computable₂ (fun (p : ℕ × ℕ) (x : BitString) =>
      if evalnIsSome cB (p.2.unpair.2 + 1) x && decide (2 * 2 ^ p.1 < x.length)
      then some () else none) := by
    have hb : Computable (fun q : (ℕ × ℕ) × BitString =>
        evalnIsSome cB (q.1.2.unpair.2 + 1) q.2 && decide (2 * 2 ^ q.1.1 < q.2.length)) :=
      Computable.comp (f := fun r : Bool × Bool => r.1 && r.2)
        (g := fun q : (ℕ × ℕ) × BitString =>
          (evalnIsSome cB (q.1.2.unpair.2 + 1) q.2, decide (2 * 2 ^ q.1.1 < q.2.length)))
        (Primrec.to_comp Primrec.and) (Computable.pair hE hF)
    have hc : Computable (fun q : (ℕ × ℕ) × BitString =>
        if evalnIsSome cB (q.1.2.unpair.2 + 1) q.2 && decide (2 * 2 ^ q.1.1 < q.2.length)
        then some () else none) :=
      (Computable.cond hb (Computable.const (some ())) (Computable.const none)).of_eq
        (by
          intro q
          cases hq : (evalnIsSome cB (q.1.2.unpair.2 + 1) q.2 &&
            decide (2 * 2 ^ q.1.1 < q.2.length)) <;> simp)
    exact hc.to₂
  exact Computable.comp (f := fun o : Option Unit => o.isSome)
    (g := fun p : ℕ × ℕ => (Encodable.decode p.2.unpair.1 : Option BitString).bind (fun x =>
      if evalnIsSome cB (p.2.unpair.2 + 1) x && decide (2 * 2 ^ p.1 < x.length)
      then some () else none))
    (Primrec.to_comp Primrec.option_isSome) (Computable.option_bind hH hG)

/-- An infinite set enumerated by the code `cB` contains, for every `k`, a string longer than
`2 * 2 ^ k`, witnessed by a stage of the enumeration. -/
private lemma exists_enumeratedLongString_eq_true {B : Set BitString} (hB_inf : ¬ B.Finite)
    {cB : Code} (hdom : ∀ x : BitString, (cB.eval (Encodable.encode x)).Dom ↔ x ∈ B)
    (k : ℕ) : ∃ m : ℕ, enumeratedLongString cB k m = true := by
  by_contra h_none
  push Not at h_none
  have h_bounded : ∀ x ∈ B, x.length ≤ 2 * 2^k := by
    intro x hx
    by_contra h_gt
    push Not at h_gt
    have h_evaln_code : ∃ s, (Nat.Partrec.Code.evaln s cB (Encodable.encode x)).isSome := by
      have h_dom' := (hdom x).mpr hx
      rw [Part.dom_iff_mem] at h_dom'
      obtain ⟨y, hs⟩ := h_dom'
      rw [Nat.Partrec.Code.eval_eq_rfindOpt] at hs
      obtain ⟨s, hs_eval⟩ := Nat.rfindOpt_spec hs
      exact ⟨s, Option.isSome_iff_exists.mpr ⟨Encodable.encode y, hs_eval⟩⟩
    obtain ⟨s, hs⟩ := h_evaln_code
    let m := Nat.pair (Encodable.encode x) s
    have hm_check : enumeratedLongString cB k m = true := by
      dsimp [enumeratedLongString, m]
      rw [Nat.unpair_pair, Encodable.encodek]
      dsimp
      rw [Bool.and_eq_true]
      refine ⟨?_, decide_eq_true h_gt⟩
      obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hs
      exact Option.isSome_iff_exists.mpr
        ⟨val,
          Option.mem_def.mp (Nat.Partrec.Code.evaln_mono (Nat.le_succ s)
                              (Option.mem_def.mpr hval))⟩
    exact h_none m hm_check
  have h_sub_bp : B ⊆ (boundedPrograms (2 * 2^k)).toFinset := by
    intro x hx
    rw [Finset.mem_coe, List.mem_toFinset, mem_boundedPrograms_iff]
    exact h_bounded x hx
  exact hB_inf ((boundedPrograms (2 * 2^k)).toFinset.finite_toSet.subset h_sub_bp)

private lemma finite_of_isEnumerableSet_subset_compl_two_mul_plainK_lt_length (U : Map)
    (hU : isOptimalConditional U)
    (B : Set BitString)
    (hB_sub : B ⊆ {x : BitString | 2 * plainK U x < (x.length : ℕ∞)}ᶜ)
    (hB_enum : IsEnumerableSet B) : B.Finite := by
  let A := {x : BitString | 2 * plainK U x < (x.length : ℕ∞)}
  by_contra hB_inf
  obtain ⟨f_B, hf_part, hf_dom⟩ := hB_enum
  obtain ⟨cB, hcB⟩ := Nat.Partrec.Code.exists_code.mp hf_part
  let check := enumeratedLongString cB
  have h_check_comp : Computable (fun (p : ℕ × ℕ) => check p.1 p.2) :=
    computable_enumeratedLongString cB
  have hdom_cB : ∀ x : BitString, (cB.eval (Encodable.encode x)).Dom ↔ x ∈ B := fun x => by
    have hc_eval : (cB.eval (Encodable.encode x)).Dom ↔ (f_B x).Dom := by
      rw [hcB]
      simp [Encodable.encodek]
    exact hc_eval.trans (hf_dom x)
  have h_ex_m : ∀ k : ℕ, ∃ m : ℕ, check k m = true :=
    fun k => exists_enumeratedLongString_eq_true hB_inf hdom_cB k
  have h_dec_check : Computable (fun (p : ℕ × ℕ) => decide (check p.1 p.2 = true)) :=
    Computable.of_eq h_check_comp (by intro p; cases check p.1 p.2 <;> rfl)
  have h_rfind_comp : Computable (fun k => Nat.find (h_ex_m k)) :=
    Computable.natFind h_dec_check (fun k => by
      obtain ⟨m, hm⟩ := h_ex_m k
      exact ⟨m, by simp [hm]⟩)
  let g (k : ℕ) : BitString :=
    let m := Nat.find (h_ex_m k)
    let p := m.unpair
    match (Encodable.decode p.1 : Option BitString) with
    | some x => x
    | none => []
  have h_g_comp : Computable g := by
    have h_e : Computable (fun k => (Nat.find (h_ex_m k)).unpair.1) :=
      Computable.fst.comp (Computable.unpair.comp h_rfind_comp)
    have h_dec : Computable (fun k =>
                              (Encodable.decode (Nat.find (h_ex_m k)).unpair.1 : Option
                                BitString)) :=
      Computable.decode.comp h_e
    have h_g_eq : g = (fun k =>
                        (Encodable.decode (Nat.find (h_ex_m k)).unpair.1 : Option
                          BitString).getD []) := by
      ext k
      dsimp [g]
      cases (Encodable.decode (Nat.find (h_ex_m k)).unpair.1 : Option BitString) <;> rfl
    rw [h_g_eq]
    exact Computable.option_getD h_dec (Computable.const [])
  have h_g_spec (k : ℕ) :
      g k ∈ B ∧ 2 * 2^k < (g k).length := by
    have h_chk : check k (Nat.find (h_ex_m k)) = true := Nat.find_spec (h_ex_m k)
    dsimp [check, enumeratedLongString] at h_chk
    split at h_chk
    next x hdec =>
      rw [Bool.and_eq_true] at h_chk
      obtain ⟨h_eval_some, h_len_gt_dec⟩ := h_chk
      have h_len_gt : 2 * 2 ^ k < x.length := of_decide_eq_true h_len_gt_dec
      have hdec2 : (Encodable.decode (Nat.find (h_ex_m k)).unpair.1 : Option BitString)
          = some x := hdec
      have h_gk_eq : g k = x := by
        dsimp [g]
        rw [hdec2]
      rw [h_gk_eq]
      refine ⟨?_, h_len_gt⟩
      refine (hf_dom x).mp ?_
      have h_code_dom : (cB.eval (Encodable.encode x)).Dom := by
        rw [Part.dom_iff_mem]
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h_eval_some
        exact ⟨y, Nat.Partrec.Code.evaln_sound (Option.mem_def.mp hy)⟩
      rw [hcB] at h_code_dom
      simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom] at h_code_dom
      exact h_code_dom
    next hdec =>
      contradiction
  have h_g_lt (k : ℕ) : (2^k : ℕ∞) < plainK U (g k) := by
    obtain ⟨hg_B, hg_len⟩ := h_g_spec k
    have hg_not_A := hB_sub hg_B
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hg_not_A
    have h_arith : 2 * (2^k : ℕ∞) < 2 * plainK U (g k) := by
      calc 2 * (2^k : ℕ∞) = ((2 * 2^k : ℕ) : ℕ∞) := by push_cast; rfl
        _ < ((g k).length : ℕ∞) := ENat.natCast_lt_natCast.mpr hg_len
        _ ≤ 2 * plainK U (g k) := hg_not_A
    by_contra hle
    push Not at hle
    have hmul : 2 * plainK U (g k) ≤ 2 * (2 ^ k : ℕ∞) := by gcongr
    exact absurd h_arith (not_lt.mpr hmul)
  let f_str (s : BitString) : BitString := g (decodeBits s)
  have hf_str_comp : Computable f_str :=
    h_g_comp.comp decodeBits_computable
  obtain ⟨c1, hc1⟩ := plainK_map_le U hU f_str hf_str_comp
  obtain ⟨c2, hc2⟩ := plainKNat_le_length U hU
  have h_g_le (k : ℕ) : plainK U (g k) ≤ (programLength (Nat.bits k) : ℕ∞) + ((c1 + c2 : ℕ) : ℕ∞) :=
    by
    have h1 := hc1 (Nat.bits k)
    dsimp [f_str] at h1
    rw [decodeBits_natBits] at h1
    have h2 := hc2 k
    dsimp [plainKNat] at h2
    calc plainK U (g k) ≤ plainK U (Nat.bits k) + (c1 : ℕ∞) := h1
      _ ≤ ((programLength (Nat.bits k) : ℕ∞) + c2) + c1 := add_le_add h2 le_rfl
      _ = (programLength (Nat.bits k) : ℕ∞) + ((c1 + c2 : ℕ) : ℕ∞) := by
        push_cast
        rw [add_assoc, add_comm (c2 : ℕ∞)]
  obtain ⟨k, hk⟩ := growth_lemma (c1 + c2)
  have h_top := h_g_le k
  have h_lt := h_g_lt k
  have h_chain : (2^k : ℕ∞) < (2^k : ℕ∞) :=
    calc (2^k : ℕ∞) < plainK U (g k) := h_lt
      _ ≤ (programLength (Nat.bits k) : ℕ∞) + ((c1 + c2 : ℕ) : ℕ∞) := h_top
      _ < (2^k : ℕ∞) := hk
  exact lt_irrefl _ h_chain

/-- The argument tuple handed to `Code.evaln` when testing whether the code `cB`
accepts the string `p.2` within `p.1.unpair.2 + 1` steps. -/
def evalnIsSomeArg (cB : Code) (p : ℕ × BitString) : (ℕ × Code) × ℕ :=
  ((p.1.unpair.2 + 1, cB), Encodable.encode p.2)

/-- The argument tuple of `evalnIsSome` is primitive recursive in its input. -/
lemma evalnIsSomeArg_primrec (cB : Code) : Primrec (evalnIsSomeArg cB) :=
  Primrec.pair
    (Primrec.pair
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
      (Primrec.const cB))
    (Primrec.encode.comp Primrec.snd)

private def searchWitnessIndex (m : ℕ) : ℕ := m.unpair.1

private theorem searchWitnessIndex_computable : Computable searchWitnessIndex :=
  (Primrec.fst.comp Primrec.unpair).to_comp

private def searchWitnessString (m : ℕ) : Option BitString :=
  Encodable.decode (searchWitnessIndex m)

private theorem searchWitnessString_computable : Computable searchWitnessString :=
  ((Computable.decode (α := BitString)).comp searchWitnessIndex_computable).of_eq (fun _ => rfl)

private def searchEvalnArg (p : (ℕ × ℕ) × BitString) : ℕ × BitString :=
  (p.1.2, p.2)

private lemma searchEvalnArg_primrec : Primrec searchEvalnArg :=
  Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd

/-- Testing acceptance of a string within a stage read off the input is computable,
uniformly in a further numerical parameter. -/
theorem evalnIsSome_p_computable (cB : Code) :
    Computable (fun (p : (ℕ × ℕ) × BitString) => evalnIsSome cB (p.1.2.unpair.2 + 1) p.2) :=
  ((evalnIsSome_computable cB).comp searchEvalnArg_primrec.to_comp).of_eq (fun _ => rfl)

private theorem decide_two_mul_two_pow_lt_length_computable :
    Computable (fun (p : (ℕ × ℕ) × BitString) => decide (2 * 2 ^ p.1.1 < p.2.length)) := by
  have h_k : Computable (fun (p : (ℕ × ℕ) × BitString) => p.1.1) :=
    (Primrec.fst.comp Primrec.fst).to_comp
  have h_pow2 : Computable (fun (p : (ℕ × ℕ) × BitString) => 2 ^ p.1.1) :=
    Computable.pow2.comp h_k
  have h1 : Computable (fun (p : (ℕ × ℕ) × BitString) => 2 * 2 ^ p.1.1) :=
    (Primrec.to_comp Primrec.nat_mul).comp (Computable.pair (Computable.const 2) h_pow2)
  have h2 : Computable (fun (p : (ℕ × ℕ) × BitString) => p.2.length) :=
    (Primrec.list_length.comp Primrec.snd).to_comp
  exact (Computable.natLt.comp (Computable.pair h1 h2)).of_eq (fun _ => rfl)

private def searchLongStringStep (cB : Code) (p : (ℕ × ℕ) × BitString) : Bool :=
  evalnIsSome cB (p.1.2.unpair.2 + 1) p.2 && decide (2 * 2^p.1.1 < p.2.length)

private theorem searchLongStringStep_computable (cB : Code) :
    Computable (searchLongStringStep cB) :=
  (Computable.cond (evalnIsSome_p_computable cB)
    decide_two_mul_two_pow_lt_length_computable (Computable.const false)).of_eq
    (by
      intro p
      dsimp [searchLongStringStep]
      cases evalnIsSome cB (p.1.2.unpair.2 + 1) p.2 <;> rfl)

private theorem searchWitnessIndex_find_computable (cB : Code)
    (h_ex_m : ∀ k, ∃ m, enumeratedLongString cB k m = true) :
    Computable (fun k => (Nat.find (h_ex_m k)).unpair.1) :=
  searchWitnessIndex_computable.comp
    (Computable.natFind
      ((computable_enumeratedLongString cB).of_eq
        (by intro p; cases enumeratedLongString cB p.1 p.2 <;> rfl))
      (fun k => by obtain ⟨m, hm⟩ := h_ex_m k; exact ⟨m, hm⟩))

private theorem searchWitnessString_find_computable (cB : Code)
    (h_ex_m : ∀ k, ∃ m, enumeratedLongString cB k m = true) :
    Computable (fun k => (Encodable.decode (α := BitString) (Nat.find (h_ex_m k)).unpair.1)) :=
  (Computable.decode (α := BitString)).comp (searchWitnessIndex_find_computable cB h_ex_m)

/-- **Theorem 10.** The set `{x | C(x) < |x| / 2}` of simple strings is an
enumerable set that is simple in the sense of Post. -/
theorem simpleStrings_isSimple (U : Map) (hU : isOptimalConditional U) :
    IsPostSimple {x : BitString | 2 * plainK U x < (x.length : ℕ∞)} :=
  ⟨isEnumerableSet_two_mul_plainK_lt_length U hU, infinite_compl_two_mul_plainK_lt_length U,
    fun B hB_sub hB_enum =>
      finite_of_isEnumerableSet_subset_compl_two_mul_plainK_lt_length U hU B hB_sub hB_enum⟩

/-! ### Theorems 11–13: busy beaver and the bounded halting problem -/

private def bitStringExtension (f : ℕ →. ℕ) (w : BitString) : Part BitString :=
  (f (bitsToNat w)).map Nat.bits

private theorem bitStringExtension_partrec (f : ℕ →. ℕ) (hf : Partrec f) :
    Partrec (bitStringExtension f) := by
  unfold bitStringExtension
  have h1 : Partrec (fun w : BitString => f (bitsToNat w)) := hf.comp bitsToNat_primrec.to_comp
  exact h1.map (natBits_computable.comp Computable.snd).to₂

/-- **Theorem 11.** The busy-beaver value `B(n)` dominates every partial
computable function on all sufficiently large arguments of its domain. -/
theorem busyBeaver_dominates_partrec (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U)
    (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ m ∈ f n, ∃ b, busyBeaver c n = some b ∧ m ≤ b := by
  have hg_part : Partrec (bitStringExtension f) := bitStringExtension_partrec f hf
  obtain ⟨C1, hC1⟩ := plainK_partrec_map_le U hU (bitStringExtension f) hg_part
  obtain ⟨C2, hC2⟩ := plainKNat_le_length U hU
  obtain ⟨N, hN⟩ := bits_length_add_le_self_of_large (C2 + C1)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hg_mem : Nat.bits m ∈ bitStringExtension f (Nat.bits n) := by
    unfold bitStringExtension
    rw [bitsToNat_bits]
    exact Part.mem_map _ hm
  have hK_m : plainK U (Nat.bits m) ≤ plainK U (Nat.bits n) + (C1 : ENat) :=
    hC1 (Nat.bits n) (Nat.bits m) hg_mem
  have hK_n : plainKNat U n ≤ ((Nat.bits n).length : ENat) + (C2 : ENat) := by
    have h := hC2 n
    simpa [programLength] using h
  have hbound : plainKNat U m ≤ (n : ENat) := by
    change plainK U (Nat.bits m) ≤ (n : ENat)
    calc plainK U (Nat.bits m) ≤ plainK U (Nat.bits n) + (C1 : ENat) := hK_m
      _ = plainKNat U n + (C1 : ENat) := rfl
      _ ≤ (((Nat.bits n).length : ENat) + (C2 : ENat)) + (C1 : ENat) := by gcongr
      _ = (((Nat.bits n).length + C2 + C1 : ℕ) : ENat) := by push_cast; ring
      _ ≤ (n : ENat) := by
        exact_mod_cast (show (Nat.bits n).length + C2 + C1 ≤ n by
          have hN_n := hN n hn
          omega)
  have hmem_out : m ∈ boundedNatOutputs c n :=
    (mem_boundedNatOutputs_iff_plainKNat_le hc n m).mpr hbound
  obtain ⟨b, hb⟩ := busyBeaver_isSome_of_nonempty c n ⟨m, hmem_out⟩
  refine ⟨b, hb, ?_⟩
  exact ((busyBeaver_some_iff c n b).mp hb).2 m hmem_out

/-- **Theorem 12.** For every partial computable `d`, the associated busy-beaver
function `B_d` is bounded by `B` after a constant shift of the argument. -/
theorem busyBeaverOf_le_busyBeaver_shift (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U)
    (d : BitString →. ℕ) (hd : Partrec d) :
    ∃ k : ℕ, ∀ (n : ℕ) (p : BitString), p.length ≤ n → ∀ m ∈ d p,
      ∃ b, busyBeaver c (n + k) = some b ∧ m ≤ b := by
  have hd_str : Partrec (fun p => (d p).map Nat.bits) :=
    Partrec.map hd (natBits_computable.comp Computable.snd)
  obtain ⟨C1, hC1⟩ := plainK_partrec_map_le U hU (fun p => (d p).map Nat.bits) hd_str
  obtain ⟨C2, hC2⟩ := plainK_le_length U hU
  refine ⟨C2 + C1, fun n p hp m hm => ?_⟩
  have hmem_map : Nat.bits m ∈ (d p).map Nat.bits := Part.mem_map Nat.bits hm
  have hK1 := hC1 p (Nat.bits m) hmem_map
  have hK2 := hC2 p
  have hKnat : plainKNat U m ≤ ((n + (C2 + C1) : ℕ) : ENat) := by
    change plainK U (Nat.bits m) ≤ ((n + (C2 + C1) : ℕ) : ENat)
    calc plainK U (Nat.bits m) ≤ plainK U p + (C1 : ENat) := hK1
      _ ≤ ((p.length : ENat) + (C2 : ENat)) + (C1 : ENat) := by gcongr
      _ = (p.length : ENat) + ((C2 + C1 : ℕ) : ENat) := by push_cast; ring
      _ ≤ (n : ENat) + ((C2 + C1 : ℕ) : ENat) := by gcongr
      _ = ((n + (C2 + C1) : ℕ) : ENat) := by push_cast; ring
  have hmem : m ∈ boundedNatOutputs c (n + (C2 + C1)) :=
    (mem_boundedNatOutputs_iff_plainKNat_le hc (n + (C2 + C1)) m).mpr hKnat
  obtain ⟨b, hb⟩ := busyBeaver_isSome_of_nonempty c (n + (C2 + C1)) ⟨m, hmem⟩
  refine ⟨b, hb, ?_⟩
  exact ((busyBeaver_some_iff c (n + (C2 + C1)) b).mp hb).2 m hmem

/-- **Theorem 13.** Knowing any number exceeding `B(n + c)` suffices to list all
strings of length at most `n` on which a fixed machine halts. -/
theorem haltingList_of_busyBeaver_bound (U : Map) (hU : isOptimalConditional U) (c : Code)
    (hc : IsCodeFor c U)
    (M : BitString →. BitString) (hM : Partrec M) :
    ∃ k : ℕ, ∃ A : ℕ × ℕ → List BitString, Computable A ∧
      ∀ (n t b : ℕ), busyBeaver c (n + k) = some b → b < t →
        ∀ x : BitString, x ∈ A (n, t) ↔ (x.length ≤ n ∧ (M x).Dom) := by
  obtain ⟨c_M, hc_M⟩ := Nat.Partrec.Code.exists_code.mp hM
  have hcheck_prim : Primrec₂ (fun (p : ℕ × ℕ) (x : BitString) =>
      (Code.evaln p.2 c_M (Encodable.encode x)).isSome) := by
    have h1 : Primrec (fun q : (ℕ × ℕ) × BitString => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    have h2 : Primrec (fun q : (ℕ × ℕ) × BitString => Encodable.encode q.2) :=
      Primrec.encode.comp Primrec.snd
    have heval : Primrec (fun q : (ℕ × ℕ) × BitString =>
        Code.evaln q.1.2 c_M (Encodable.encode q.2)) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair h1 (Primrec.const c_M)) h2)
    exact (Primrec.option_isSome.comp heval).to₂
  let A : ℕ × ℕ → List BitString := fun p =>
    (boundedPrograms p.1).filter (fun x => (Code.evaln p.2 c_M (Encodable.encode x)).isSome)
  have hA_prim : Primrec A :=
    list_filter_primrec (primrec_boundedPrograms.comp Primrec.fst) hcheck_prim
  have hA : Computable A := hA_prim.to_comp
  have hfind_step : Partrec (fun x : BitString =>
      Nat.rfind (fun s => Part.some (Code.evaln s c_M (Encodable.encode x)).isSome)) := by
    have hpred : Primrec₂ (fun (x : BitString) (s : ℕ) =>
        (Code.evaln s c_M (Encodable.encode x)).isSome) := by
      have h1 : Primrec (fun q : BitString × ℕ => q.2) := Primrec.snd
      have h2 : Primrec (fun q : BitString × ℕ => Encodable.encode q.1) :=
        Primrec.encode.comp Primrec.fst
      have heval : Primrec (fun q : BitString × ℕ =>
          Code.evaln q.2 c_M (Encodable.encode q.1)) :=
        Nat.Partrec.Code.primrec_evaln.comp
          (Primrec.pair (Primrec.pair h1 (Primrec.const c_M)) h2)
      exact (Primrec.option_isSome.comp heval).to₂
    exact Partrec.rfind hpred.to_comp.partrec₂
  let f_M : BitString →. BitString := fun x =>
    (Nat.rfind (fun s => Part.some (Code.evaln s c_M (Encodable.encode x)).isSome)).map Nat.bits
  have hf_M : Partrec f_M := hfind_step.map (natBits_computable.comp Computable.snd).to₂
  obtain ⟨c_map, hmap⟩ := plainK_partrec_map_le U hU f_M hf_M
  obtain ⟨c_len, hlen⟩ := plainK_le_length U hU
  refine ⟨c_len + c_map, A, hA, fun n t b hb hbt x => ⟨fun hin => ?_, fun hx => ?_⟩⟩
  · simp only [A, List.mem_filter, mem_boundedPrograms_iff] at hin
    obtain ⟨hlenx, hstep⟩ := hin
    refine ⟨hlenx, ?_⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hstep
    have hsound := Nat.Partrec.Code.evaln_sound hr
    rw [hc_M] at hsound
    dsimp only [Part.ofOption] at hsound
    rw [Encodable.encodek] at hsound
    dsimp only [Part.ofOption] at hsound
    rw [Part.bind_some, Part.mem_map_iff] at hsound
    obtain ⟨y, hy, _⟩ := hsound
    exact Part.dom_iff_mem.mpr ⟨y, hy⟩
  · obtain ⟨hlenx, hdom⟩ := hx
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom
    have hy_eval : Encodable.encode y ∈ c_M.eval (Encodable.encode x) := by
      rw [hc_M]
      dsimp only
      rw [Encodable.encodek]
      dsimp only [Part.ofOption]
      rw [Part.bind_some, Part.mem_map_iff]
      exact ⟨y, hy, rfl⟩
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hy_eval
    have hrfind_dom : (Nat.rfind (fun s => Part.some
        (Code.evaln s c_M (Encodable.encode x)).isSome)).Dom := by
      refine Nat.rfind_dom.mpr ?_
      refine ⟨s, ?_, fun _ => Part.some_dom _⟩
      rw [Part.mem_some_iff]
      exact (Option.isSome_iff_exists.mpr ⟨Encodable.encode y, hs⟩).symm
    obtain ⟨s_x, hs_x⟩ := Part.dom_iff_mem.mp hrfind_dom
    have hs_x_mem : Nat.bits s_x ∈ f_M x := by
      dsimp [f_M]
      simp only [Part.mem_map_iff]
      exact ⟨s_x, hs_x, rfl⟩
    have hs_x_spec := (Nat.mem_rfind).mp hs_x
    have hs_x_isSome : (Code.evaln s_x c_M (Encodable.encode x)).isSome = true := by
      have h1 := hs_x_spec.1
      simp only [Part.mem_some_iff] at h1
      exact h1.symm
    have hK_map := hmap x (Nat.bits s_x) hs_x_mem
    have hK_len := hlen x
    have hK_val : plainKNat U s_x ≤ ((n + (c_len + c_map) : ℕ) : ENat) := by
      calc plainKNat U s_x = plainK U (Nat.bits s_x) := rfl
        _ ≤ plainK U x + (c_map : ENat) := hK_map
        _ ≤ ((x.length : ENat) + (c_len : ENat)) + (c_map : ENat) := by gcongr
        _ ≤ ((n : ENat) + (c_len : ENat)) + (c_map : ENat) := by
          gcongr
        _ = ((n + (c_len + c_map) : ℕ) : ENat) := by push_cast; ring
    have hmem_bounded : s_x ∈ boundedNatOutputs c (n + (c_len + c_map)) :=
      (mem_boundedNatOutputs_iff_plainKNat_le hc (n + (c_len + c_map)) s_x).mpr hK_val
    have hle_b := ((busyBeaver_some_iff c (n + (c_len + c_map)) b).mp hb).2 s_x hmem_bounded
    have hs_x_le_t : s_x ≤ t := by omega
    obtain ⟨r_x, hr_x⟩ := Option.isSome_iff_exists.mp hs_x_isSome
    have ht_x : Code.evaln t c_M (Encodable.encode x) = some r_x :=
      Nat.Partrec.Code.evaln_mono hs_x_le_t hr_x
    simp only [A, List.mem_filter, mem_boundedPrograms_iff]
    refine ⟨hlenx, ?_⟩
    simp [ht_x]

/-! ### The nine canonical objects of Theorem 15 -/

open Classical in
/-- The halting time of the program `p` for the machine `c` (`0` if `p` does not
halt). -/
noncomputable def haltTimeNat (c : Code) (p : BitString) : ℕ :=
  if h : ∃ t, haltsWithin c t p = true then Nat.find h else 0

/-- The list of all programs of length at most `n` on which the machine `c`
halts. -/
noncomputable def haltingProgramsBounded (c : Code) (n : ℕ) : List BitString :=
  (boundedPrograms n).filter (fun p => haltsWithin c (maxHaltingStage c n) p)

/-- The maximal halting time of the machine `c` on programs of length at most
`n`: the book's `BB(n)`. -/
noncomputable def maxHaltTimeNat (c : Code) (n : ℕ) : ℕ :=
  ((haltingProgramsBounded c n).map (haltTimeNat c)).foldr max 0

/-- Object (a): the list of all strings of complexity at most `n`, each paired
with its complexity. -/
noncomputable def objComplexityList (U : Map) (c : Code) (n : ℕ) : BitString :=
  listCode ((completedBoundedOutput c n).map (fun x => pairCode x (natBits (cVal U x))))

/-- Object (b): the number of strings of complexity at most `n`. -/
noncomputable def objComplexityCount (c : Code) (n : ℕ) : BitString :=
  natBits (completedBoundedOutput c n).length

/-- Object (c): the busy-beaver value `B(n)`. -/
noncomputable def objBusyBeaver (c : Code) (n : ℕ) : BitString :=
  natBits ((busyBeaver c n).getD 0)

/-- Object (d): the maximal halting time `BB(n)`. -/
noncomputable def objMaxTime (c : Code) (n : ℕ) : BitString :=
  natBits (maxHaltTimeNat c n)

/-- Object (e): the list of programs of length at most `n` in the domain of the
optimal decompressor. -/
noncomputable def objHaltingList (c : Code) (n : ℕ) : BitString :=
  listCode (haltingProgramsBounded c n)

end Kolmogorov
