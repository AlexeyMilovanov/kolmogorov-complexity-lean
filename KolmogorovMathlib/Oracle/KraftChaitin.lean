/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.Oracle.PrefixComplexity
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator.Computability
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Relative Kraft--Chaitin requests and finite-mass coding

This module proves relative Kraft--Chaitin realization (`oracle:kc`) by running the free-list
allocator on an oracle-computable stream of optional requests. It defines the stream's Kraft
mass and constructs a relative prefix decoder that realizes every request at its exact length.
Optimality then gives a uniform bound on relative prefix complexity.

For `oracle:coding`, strict thresholds of an upper semicomputable cost are enumerated without
repetition. A geometric-tail estimate bounds their request mass, giving a complexity bound
for every cost with finite exponential mass. The pressure and dimension arguments in
`PointToSet` use this coding theorem to turn weighted covers into short descriptions.
The coding constant may depend on a finite mass bound; computing that bound is not required.
-/

namespace Kolmogorov.PointToSet

open scoped ENNReal

/-- Kraft mass of an optional request stream; an idle stage has zero mass.
Blueprint node `oracle:kc`. -/
noncomputable def oracleRequestMass (req : ℕ → Option (BitString × ℕ)) : ℝ≥0∞ :=
  ∑' j, (req j).elim 0 (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2)

/-- Updating the free list from an optional request and the current state is computable. -/
private lemma free_list_update_computable :
    Computable (fun p : Option (BitString × ℕ) × Option (List BitString) ↦
      p.2.bind fun free ↦
        (p.1.map (fun pr ↦ (KraftChaitin.allocateOne free pr.2).map Prod.snd)).getD
          (some free)) := by
  have halloc : Computable (fun p : (BitString × ℕ) × List BitString ↦
      KraftChaitin.allocateOne p.2 p.1.2) :=
    @Computable.comp ((BitString × ℕ) × List BitString) (List BitString × ℕ)
      (Option (BitString × List BitString)) inferInstance inferInstance inferInstance
      (fun p ↦ KraftChaitin.allocateOne p.1 p.2) (fun p ↦ (p.2, p.1.2))
      KraftChaitin.allocateOne_computable
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
  have hfree : Computable (fun p : (BitString × ℕ) × List BitString ↦
      (KraftChaitin.allocateOne p.2 p.1.2).map Prod.snd) :=
    Computable.option_map halloc (Computable.snd.comp Computable.snd).to₂
  have hrequest : Computable₂
      (fun p : Option (BitString × ℕ) × List BitString ↦ fun pr : BitString × ℕ ↦
        (KraftChaitin.allocateOne p.2 pr.2).map Prod.snd) :=
    @Computable.comp ((Option (BitString × ℕ) × List BitString) × (BitString × ℕ))
      ((BitString × ℕ) × List BitString) (Option (List BitString))
      inferInstance inferInstance inferInstance
      (fun p ↦ (KraftChaitin.allocateOne p.2 p.1.2).map Prod.snd)
      (fun p ↦ (p.2, p.1.2)) hfree
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
  have hmap : Computable₂ (fun request : Option (BitString × ℕ) ↦
      fun free : List BitString ↦
        request.map (fun pr ↦ (KraftChaitin.allocateOne free pr.2).map Prod.snd)) :=
    Computable.option_map Computable.fst hrequest
  have hidle : Computable₂ (fun _ : Option (BitString × ℕ) ↦
      fun free : List BitString ↦ some free) :=
    (Computable.option_some.comp Computable.snd).to₂
  have hupdate : Computable₂ (fun request : Option (BitString × ℕ) ↦
      fun free : List BitString ↦
        (request.map (fun pr ↦ (KraftChaitin.allocateOne free pr.2).map Prod.snd)).getD
          (some free)) :=
    Computable.option_getD hmap hidle
  exact Computable.option_bind Computable.snd
    (hupdate.comp (Computable.fst.comp Computable.fst) Computable.snd)

/-- Relative natural recursion computes the free list after any finite request prefix. -/
private lemma allocator_state_computableIn {A : Set ℕ} (req : ℕ → Option (BitString × ℕ))
    (hreq : ComputableIn {charOracle A} req) :
    ComputableIn {charOracle A} (fun n ↦ KraftChaitin.allocatorState req n) := by
  have hinput : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ × Option (List BitString) ↦ (req p.2.1, p.2.2)) :=
    ComputableIn.pair (hreq.comp (ComputableIn.fst.comp ComputableIn.snd))
      (ComputableIn.snd.comp ComputableIn.snd)
  have hstep := (free_list_update_computable.computableIn.comp hinput).to₂
  have hrec := ComputableIn.nat_rec ComputableIn.id
    (ComputableIn.const (some ([[]] : List BitString))) hstep
  exact hrec.of_eq fun n ↦ (KraftChaitin.allocatorState_eq_rec req n).symm

/-- Extracting the code allocated from a supplied state and optional request is computable. -/
private lemma allocated_code_computable :
    Computable (fun p : Option (List BitString) × Option (BitString × ℕ) ↦
      p.1.bind fun free ↦ p.2.bind fun pr ↦
        (KraftChaitin.allocateOne free pr.2).map Prod.fst) := by
  have halloc : Computable
      (fun p : (List BitString × Option (BitString × ℕ)) × (BitString × ℕ) ↦
        KraftChaitin.allocateOne p.1.1 p.2.2) :=
    @Computable.comp ((List BitString × Option (BitString × ℕ)) × (BitString × ℕ))
      (List BitString × ℕ) (Option (BitString × List BitString))
      inferInstance inferInstance inferInstance
      (fun p ↦ KraftChaitin.allocateOne p.1 p.2) (fun p ↦ (p.1.1, p.2.2))
      KraftChaitin.allocateOne_computable
      ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
  have hcode : Computable
      (fun p : (List BitString × Option (BitString × ℕ)) × (BitString × ℕ) ↦
        (KraftChaitin.allocateOne p.1.1 p.2.2).map Prod.fst) :=
    halloc.option_map (Computable.fst.comp Computable.snd)
  have hrequest : Computable (fun p : List BitString × Option (BitString × ℕ) ↦
      p.2.bind fun pr ↦ (KraftChaitin.allocateOne p.1 pr.2).map Prod.fst) :=
    Computable.option_bind Computable.snd hcode
  have hinput : Computable
      (fun p : (Option (List BitString) × Option (BitString × ℕ)) × List BitString ↦
        (p.2, p.1.2)) :=
    Computable.pair Computable.snd (Computable.snd.comp Computable.fst)
  exact Computable.option_bind Computable.fst (hrequest.comp hinput)

/-- The code assigned to each stage is computable relative to the request stream. -/
private lemma alloc_fun_computableIn {A : Set ℕ} (req : ℕ → Option (BitString × ℕ))
    (hreq : ComputableIn {charOracle A} req) :
    ComputableIn {charOracle A} (KraftChaitin.allocFun req) := by
  have hinput := (allocator_state_computableIn req hreq).pair hreq
  refine (allocated_code_computable.computableIn.comp hinput).of_eq ?_
  intro n
  rw [KraftChaitin.allocFun_eq_bind]
  cases KraftChaitin.allocatorState req n with
  | none => rfl
  | some free => cases req n <;> rfl

/-- The decoder searches for the stage that allocated its input program. -/
private def allocationDecoder (req : ℕ → Option (BitString × ℕ)) : Map := fun p ↦
  (Nat.rfind fun n ↦ Part.some
    (decide (KraftChaitin.allocFun req n = some p.1 ∧ (req n).isSome = true))).bind
      fun n ↦ Part.ofOption ((req n).map Prod.fst)

/-- Recognizing a stage that allocated a given program is relatively computable. -/
private lemma allocation_test_computableIn {A : Set ℕ}
    (req : ℕ → Option (BitString × ℕ)) (hreq : ComputableIn {charOracle A} req) :
    ComputableIn₂ {charOracle A} (fun p : BitString × BitString ↦ fun n : ℕ ↦
      decide (KraftChaitin.allocFun req n = some p.1 ∧ (req n).isSome = true)) := by
  have heq : Computable (fun p : Option BitString × Option BitString ↦ decide (p.1 = p.2)) :=
    (PrimrecPred.decide (PrimrecRel.comp Primrec.eq Primrec.fst Primrec.snd)).to_comp
  have hcode : ComputableIn {charOracle A}
      (fun p : (BitString × BitString) × ℕ ↦ some p.1.1) :=
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.fst)).computableIn
  have hmatch := heq.computableIn.comp
    (((alloc_fun_computableIn req hreq).comp ComputableIn.snd).pair hcode)
  have hpresent : ComputableIn {charOracle A}
      (fun p : (BitString × BitString) × ℕ ↦ (req p.2).isSome) :=
    Primrec.option_isSome.computableIn.comp (hreq.comp ComputableIn.snd)
  have hand : Computable (fun p : Bool × Bool ↦ p.1 && p.2) :=
    (Computable.cond Computable.fst Computable.snd (Computable.const false)).of_eq
      (fun p ↦ by cases p.1 <;> rfl)
  exact (hand.computableIn.comp (hmatch.pair hpresent)).of_eq fun p ↦ by
    simp only [Bool.decide_and, Bool.decide_eq_true]

/-- Searching the allocated codes and returning the corresponding output is a relative decoder. -/
private lemma allocationDecoder_isDecompressorIn {A : Set ℕ}
    (req : ℕ → Option (BitString × ℕ)) (hreq : ComputableIn {charOracle A} req) :
    IsDecompressorIn (charOracle A) (allocationDecoder req) := by
  rw [isDecompressorIn_iff_partrecIn]
  have hpred := (allocation_test_computableIn req hreq).partrecIn₂
  have hsearch := PartrecIn.rfind hpred
  have houtput : Computable (fun o : Option (BitString × ℕ) ↦ o.map Prod.fst) :=
    Computable.option_map Computable.id (Computable.fst.comp Computable.snd).to₂
  have hdecode : PartrecIn {charOracle A} (fun o : Option BitString ↦ Part.ofOption o) :=
    (Computable.ofOption Computable.id).partrecIn
  have hout := hdecode.comp (houtput.computableIn.comp hreq)
  exact PartrecIn.bind hsearch (hout.comp ComputableIn.snd).to₂

/-- Prefix incomparability of allocated codes makes the search decoder a prefix machine. -/
private lemma allocationDecoder_isPrefixMachine (req : ℕ → Option (BitString × ℕ)) :
    IsPrefixMachine (allocationDecoder req) := by
  intro y p hp q hq hpre
  obtain ⟨xp, hxp⟩ := Part.dom_iff_mem.mp hp
  obtain ⟨np, hnp, _⟩ := Part.mem_bind_iff.mp hxp
  obtain ⟨xq, hxq⟩ := Part.dom_iff_mem.mp hq
  obtain ⟨nq, hnq, _⟩ := Part.mem_bind_iff.mp hxq
  have hp_alloc := (of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hnp)).symm).1
  have hq_alloc := (of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hnq)).symm).1
  by_contra hneq
  have hstages : np ≠ nq := by
    rintro rfl
    exact hneq (Option.some.inj (hp_alloc.symm.trans hq_alloc))
  exact KraftChaitin.allocFun_prefixFree req np nq p q hp_alloc hq_alloc hstages hpre

/-- Each successful allocation is found by the decoder, with the exact requested length. -/
private lemma allocationDecoder_produces (req : ℕ → Option (BitString × ℕ))
    (hmass : oracleRequestMass req ≤ 1) :
    ∀ j x l, req j = some (x, l) →
      ∃ p : BitString, p.length = l ∧ produces (allocationDecoder req) p [] x := by
  intro j x l hj
  have hweight : (∑' i, match req i with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
      | none => 0) ≤ 1 := by
    convert hmass using 1
    apply tsum_congr
    intro i
    cases req i <;> rfl
  obtain ⟨p, hp, hlen⟩ := KraftChaitin.allocFun_success req j x l hj hweight
  refine ⟨p, hlen, ?_⟩
  have hfound : j ∈ Nat.rfind (fun n ↦ Part.some
      (decide (KraftChaitin.allocFun req n = some p ∧ (req n).isSome = true))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · exact Part.mem_some_iff.mpr (decide_eq_true ⟨hp, by simp [hj]⟩).symm
    · intro m hm
      have hfalse : ¬ (KraftChaitin.allocFun req m = some p ∧ (req m).isSome = true) := by
        rintro ⟨hm_alloc, _⟩
        exact KraftChaitin.allocFun_prefixFree req m j p p hm_alloc hp
          (ne_of_lt hm) (List.prefix_refl p)
      exact Part.mem_some_iff.mpr (decide_eq_false hfalse).symm
  exact Part.mem_bind_iff.mpr ⟨j, hfound, by simp [hj]⟩

/-- Every relative enumerable stream of requests of mass at most one is realized by a
relative prefix machine at the exact requested lengths. Blueprint node `oracle:kc`. -/
theorem oracle_kraftChaitin (A : Set ℕ) (req : ℕ → Option (BitString × ℕ))
    (hreq : ComputableIn {charOracle A} req) (hmass : oracleRequestMass req ≤ 1) :
    ∃ D : Map, IsDecompressorIn (charOracle A) D ∧ IsPrefixMachine D ∧
      ∀ j x l, req j = some (x, l) →
        ∃ p : BitString, p.length = l ∧ produces D p [] x := by
  exact ⟨allocationDecoder req, allocationDecoder_isDecompressorIn req hreq,
    allocationDecoder_isPrefixMachine req, allocationDecoder_produces req hmass⟩

/-- Optimal simulation of one realized stream gives a constant independent of every
request, output and length. Blueprint node `oracle:kc`. -/
theorem oracle_kraftChaitin_bound (A : Set ℕ) (req : ℕ → Option (BitString × ℕ))
    (hreq : ComputableIn {charOracle A} req) (hmass : oracleRequestMass req ≤ 1) :
    ∃ c : ℕ, ∀ j x l, req j = some (x, l) → oracleComplexity A x ≤ l + c := by
  obtain ⟨D, hD, hprefix, hproduces⟩ := oracle_kraftChaitin A req hreq hmass
  obtain ⟨c, hc⟩ := (exists_optimalOraclePrefix_spec A).2.2 D hD hprefix
  refine ⟨c, fun j x l hj ↦ ?_⟩
  obtain ⟨p, hlen, hp⟩ := hproduces j x l hj
  have hbound : oraclePrefixComplexity A x [] ≤ (p.length : ℕ∞) + (c : ℕ∞) :=
    (hc x []).trans (add_le_add_left (KP_le_programLength_of_produces hp) (c : ℕ∞))
  rw [← oraclePrefixComplexity_coe A x [], hlen, ← ENat.natCast_add] at hbound
  exact ENat.natCast_le_natCast.mp hbound

/-- Twice a finite extended nonnegative real is bounded by a natural power of two. -/
private lemma exists_dyadic_scale (M : ℝ≥0∞) (hM : M < ⊤) :
    ∃ b : ℕ, 2 * M ≤ (2 : ℝ≥0∞) ^ b := by
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (2 * M).toReal (by norm_num : (1 : ℝ) < 2)
  refine ⟨b, ?_⟩
  have hfinite : 2 * M ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hM.ne
  calc
    2 * M = ENNReal.ofReal (2 * M).toReal := (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ b) := ENNReal.ofReal_le_ofReal hb.le
    _ = (2 : ℝ≥0∞) ^ b := by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num

/-- Strict integer thresholds of an upper semicomputable cost form a relatively enumerable set. -/
private lemma cost_requests_isREIn (A : Set ℕ) (F : BitString → Prop)
    (g : Subtype F → ℝ) (hg : IsUpperSemicomputableOnIn A F g) (b : ℕ) :
    IsREIn A (fun p : BitString × ℕ ↦
      ∃ h : F p.1, g ⟨p.1, h⟩ + (b : ℝ) < (p.2 : ℝ)) := by
  obtain ⟨f, hf, hdom⟩ := relative_enumeration_threshold A F g hg
  have hshift : Computable (fun p : BitString × ℕ ↦ (p.1, (p.2 : ℚ) - (b : ℚ))) :=
    Computable.fst.pair (Kolmogorov.ComputableReals.computable_ratSub.comp
      (Kolmogorov.computable_nat_to_rat.comp Computable.snd) (Computable.const (b : ℚ)))
  refine ⟨fun p ↦ f (p.1, (p.2 : ℚ) - (b : ℚ)), hf.comp hshift.computableIn, ?_⟩
  intro p
  simpa only [Rat.cast_sub, Rat.cast_natCast, lt_sub_iff_add_lt] using
    hdom (p.1, (p.2 : ℚ) - (b : ℚ))

/-- A stream with no repeated requests has mass at most the sum of all valid dyadic tails. -/
private lemma request_mass_le_dyadic_tails (F : BitString → Prop) (g : Subtype F → ℝ)
    (b : ℕ) (e : ℕ → Option (BitString × ℕ))
    (hvalid : ∀ s r, e s = some r → ∃ h : F r.1, g ⟨r.1, h⟩ + (b : ℝ) < (r.2 : ℝ))
    (hinj : ∀ s t r, e s = some r → e t = some r → s = t) :
    oracleRequestMass e ≤
      ∑' w : Subtype F, ∑' n : {n : ℕ // g w + (b : ℝ) < (n : ℝ)},
        (2 : ℝ≥0∞)⁻¹ ^ n.val := by
  classical
  let S := {s : ℕ // (e s).isSome}
  let r (s : S) := (e s.val).get s.property
  have hr (s : S) : e s.val = some (r s) := (Option.some_get s.property).symm
  have hvalid' (s : S) := hvalid s.val (r s) (hr s)
  let f : S → Σ w : Subtype F, {n : ℕ // g w + (b : ℝ) < (n : ℝ)} := fun s ↦
    ⟨⟨(r s).1, (hvalid' s).choose⟩, ⟨(r s).2, (hvalid' s).choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro s t hst
    have heq : r s = r t := Prod.ext
      (congrArg (fun p ↦ p.1.val) hst) (congrArg (fun p ↦ p.2.val) hst)
    exact Subtype.ext (hinj s.val t.val (r s) (hr s)
      ((hr t).trans (congrArg some heq.symm)))
  have hmass : oracleRequestMass e = ∑' s : S, (2 : ℝ≥0∞)⁻¹ ^ (r s).2 := by
    unfold oracleRequestMass
    rw [← tsum_subtype_eq_of_support_subset (s := {s | (e s).isSome})]
    · apply tsum_congr
      intro s
      rw [hr s]
      rfl
    · intro s hs
      change (e s).elim 0 (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2) ≠ 0 at hs
      cases he : e s with
      | none => simp [he] at hs
      | some r => simp [he]
  rw [hmass, ← ENNReal.tsum_sigma]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf (fun p ↦ (2 : ℝ≥0∞)⁻¹ ^ p.2.val)

/-- The dyadic tail strictly above a real threshold is bounded by twice its dyadic weight. -/
private lemma dyadic_tail_le (t : ℝ) :
    (∑' n : {n : ℕ // t < (n : ℝ)}, (2 : ℝ≥0∞)⁻¹ ^ n.val) ≤
      (2 : ℝ≥0∞) ^ (1 - t) := by
  by_cases ht : t < 0
  · calc
      (∑' n : {n : ℕ // t < (n : ℝ)}, (2 : ℝ≥0∞)⁻¹ ^ n.val)
          ≤ ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = 2 := ENNReal.tsum_geometric_two
      _ = (2 : ℝ≥0∞) ^ (1 : ℝ) := (ENNReal.rpow_one 2).symm
      _ ≤ (2 : ℝ≥0∞) ^ (1 - t) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · have ht := le_of_not_gt ht
    let k := ⌊t⌋₊ + 1
    have hk : t < (k : ℝ) := by exact_mod_cast Nat.lt_floor_add_one t
    have hthreshold (n : ℕ) : t < (n : ℝ) ↔ k ≤ n := Nat.floor_lt ht |>.symm
    let e : ℕ ≃ {n : ℕ // t < (n : ℝ)} :=
      { toFun := fun j ↦ ⟨k + j, (hthreshold (k + j)).mpr (Nat.le_add_right k j)⟩
        invFun := fun n ↦ n.val - k
        left_inv := fun j ↦ Nat.add_sub_cancel_left k j
        right_inv := fun ⟨n, hn⟩ ↦ Subtype.ext (Nat.add_sub_cancel' ((hthreshold n).mp hn)) }
    have hsum : (∑' n : {n : ℕ // t < (n : ℝ)}, (2 : ℝ≥0∞)⁻¹ ^ n.val) =
        ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + j) :=
      (Equiv.tsum_eq e _).symm
    rw [hsum]
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    have hweight : (2 : ℝ≥0∞)⁻¹ ^ k * 2 = (2 : ℝ≥0∞) ^ (1 - (k : ℝ)) := by
      rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
        ENNReal.rpow_one, ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow,
        mul_comm]
    rw [hweight]
    exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Translating all costs by the same amount factors the exponential mass. -/
private lemma tsum_dyadic_shift (F : BitString → Prop) (g : Subtype F → ℝ) (b : ℕ) :
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (1 - (g w + (b : ℝ)))) =
      (2 : ℝ≥0∞) ^ (1 - (b : ℝ)) * ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w) := by
  have hpoint (w : Subtype F) :
      (2 : ℝ≥0∞) ^ (1 - (g w + (b : ℝ))) =
        (2 : ℝ≥0∞) ^ (1 - (b : ℝ)) * (2 : ℝ≥0∞) ^ (-g w) := by
    rw [show 1 - (g w + (b : ℝ)) = (1 - (b : ℝ)) + -g w by ring]
    exact ENNReal.rpow_add _ _ (by norm_num) (by norm_num)
  simp_rw [hpoint]
  exact ENNReal.tsum_mul_left

/-- A dyadic scale dominating twice the mass makes the rescaled geometric bound at most one. -/
private lemma scaled_mass_le_one (b : ℕ) (M : ℝ≥0∞)
    (hscale : 2 * M ≤ (2 : ℝ≥0∞) ^ b) :
    (2 : ℝ≥0∞) ^ (1 - (b : ℝ)) * M ≤ 1 := by
  rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
    ENNReal.rpow_one, ENNReal.rpow_neg, ENNReal.rpow_natCast, mul_assoc, mul_left_comm]
  calc
    ((2 : ℝ≥0∞) ^ b)⁻¹ * (2 * M) ≤ ((2 : ℝ≥0∞) ^ b)⁻¹ * (2 : ℝ≥0∞) ^ b :=
      mul_le_mul_right hscale _
    _ = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)

/-- A bound on a single exponential weight ensures that the shifted cost is nonnegative. -/
private lemma shifted_cost_nonneg (t : ℝ) (b : ℕ)
    (hweight : 2 * (2 : ℝ≥0∞) ^ (-t) ≤ (2 : ℝ≥0∞) ^ b) :
    0 ≤ t + (b : ℝ) := by
  have hpow : (2 : ℝ≥0∞) ^ (1 - t) ≤ (2 : ℝ≥0∞) ^ (b : ℝ) := by
    rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
      ENNReal.rpow_one, ENNReal.rpow_natCast]
    exact hweight
  have hmono : StrictMono (fun x : ℝ ↦ (2 : ℝ≥0∞) ^ x) := fun _ _ h ↦
    ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) h
  have hle := hmono.le_iff_le.mp hpow
  linarith

/-- An upper semicomputable real cost on a relative enumerable ambient domain bounds
prefix complexity when its exponential mass has a finite real bound. The constant may
depend on that bound, but is chosen before the output. Blueprint node `oracle:coding`. -/
theorem oracle_coding_finite_mass (A : Set ℕ) (F : BitString → Prop)
    (g : Subtype F → ℝ) (hF : IsREIn A F) (hg : IsUpperSemicomputableOnIn A F g)
    (M : ℝ≥0∞) (hM : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w)) ≤ M)
    (hM_finite : M < ⊤) :
    ∃ c : ℕ, ∀ w : Subtype F, (oracleComplexity A w.val : ℝ) ≤ g w + c := by
  obtain ⟨b, hscale⟩ := exists_dyadic_scale M hM_finite
  let R : BitString × ℕ → Prop := fun p ↦ ∃ h : F p.1, g ⟨p.1, h⟩ + (b : ℝ) < (p.2 : ℝ)
  -- the enumerable bounds of `hg` already capture the domain; `hF` belongs to the frozen
  -- statement of this main theorem
  have _ := hF
  have hR : IsREIn A R := cost_requests_isREIn A F g hg b
  obtain ⟨e, henum, hinj⟩ := relative_enumeration_injective A R hR
  have hmass : oracleRequestMass e ≤ 1 := by
    calc
      oracleRequestMass e ≤
          ∑' w : Subtype F, ∑' n : {n : ℕ // g w + (b : ℝ) < (n : ℝ)},
            (2 : ℝ≥0∞)⁻¹ ^ n.val :=
        request_mass_le_dyadic_tails F g b e (fun s r hr ↦ (henum.2 r).mpr ⟨s, hr⟩) hinj
      _ ≤ ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (1 - (g w + (b : ℝ))) :=
        ENNReal.tsum_le_tsum (fun w ↦ dyadic_tail_le (g w + (b : ℝ)))
      _ = (2 : ℝ≥0∞) ^ (1 - (b : ℝ)) * ∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w) :=
        tsum_dyadic_shift F g b
      _ ≤ (2 : ℝ≥0∞) ^ (1 - (b : ℝ)) * M := mul_le_mul_right hM _
      _ ≤ 1 := scaled_mass_le_one b M hscale
  obtain ⟨c, hc⟩ := oracle_kraftChaitin_bound A e henum.1 hmass
  refine ⟨b + 1 + c, fun w ↦ ?_⟩
  have hweight : (2 : ℝ≥0∞) ^ (-g w) ≤ M := (ENNReal.le_tsum w).trans hM
  have hnonneg := shifted_cost_nonneg (g w) b ((mul_le_mul_right hweight 2).trans hscale)
  let n := ⌊g w + (b : ℝ)⌋₊ + 1
  have hn : g w + (b : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_floor_add_one _
  have hn_le : (n : ℝ) ≤ g w + (b : ℝ) + 1 := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using add_le_add_left (Nat.floor_le hnonneg) 1
  obtain ⟨t, ht⟩ := (henum.2 (w.val, n)).mp ⟨w.property, hn⟩
  calc
    (oracleComplexity A w.val : ℝ) ≤ n + c := by exact_mod_cast hc t w.val n ht
    _ ≤ g w + (b + 1 + c : ℕ) := by push_cast; linarith

end Kolmogorov.PointToSet
