/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.AlgorithmicProbability.OptimalCoding
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.Prefix.StableDecompressors

/-!
# Conditional prefix interfaces for the C-random strings argument

This module packages the facts about conditional prefix complexity `KP B.D` and plain
complexity `plainK B.V` of a base pair of optimal machines `B : Base` that the construction of
the C-random strings argument uses as black boxes.

* Uniform conditional coding (`FoundationPrefixCoding`): the a priori mass of the optimal
  conditional prefix machine agrees with `2 ^ (-KP)` up to a multiplicative constant, it has
  computable monotone dyadic approximations, it sums to at most one in every condition, and it
  dominates every uniformly lower semicomputable conditional mass.
* The exact conditional chain rule and the self-sufficiency of prefix complexity
  (`FoundationPrefixChainRule`, `FoundationPrefixSelfSufficiency`).
* Conditional prefix composition and removal of an auxiliary condition
  (`FoundationConditionalComposition`).
* A prefix description followed by a raw suffix is a plain description for every fixed partial
  computable decoder (`FoundationPrefixRaw`), which is the shared adapter of the crossing-index,
  slack and uniform-rank decoders of the construction.
* Plain and prefix complexity agree up to a constant when the length is supplied in the
  condition (`FoundationPlainPrefixBounds`).

Complexities remain in `ENat`. In statements that place a complexity value inside
a string, a natural `k` is explicitly identified with that value before encoding it
by `bits`. This avoids totalizing an infinite complexity and avoids unary contexts.
Mass inequalities use the repository's `complexityWeight` and dyadic normalization.
-/

namespace Kolmogorov.Milovanov

open scoped ENNReal

/-- Both coding inequalities hold with one constant uniform in output and condition.
Blueprint node `FoundationPrefixCoding`. -/
theorem conditional_coding_interface (B : Base) :
    ∃ c : ℕ, ∀ a b,
      complexityWeight (KP B.D a b + c) ≤ aprioriMeasure B.D a b ∧
      (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure B.D a b ≤ complexityWeight (KP B.D a b) := by
  obtain ⟨c, hc⟩ :=
    aprioriMeasure_le_complexityWeight_optimal B.optimalD B.optimalD.isPrefixDecompressor
  refine ⟨c, fun a b ↦ ⟨?_, hc a b⟩⟩
  exact (complexityWeight_le_of_le (le_self_add : KP B.D a b ≤ KP B.D a b + c)).trans
    (complexityWeight_KP_le_aprioriMeasure B.D a b)

/-- The conditional a priori mass sums to at most one separately in every condition.
Blueprint node `FoundationPrefixCoding`. -/
theorem conditional_coding_interface_mass (B : Base) (b : BitString) :
    (∑' a : BitString, aprioriMeasure B.D a b) ≤ 1 :=
  tsum_aprioriMeasure_le_one B.D b B.optimalD.isPrefixMachine

/-- The existing dyadic numerator approximation is computable for the supplied prefix code.
Blueprint node `FoundationPrefixCoding`. -/
theorem conditional_coding_interface_approx (B : Base) :
    Computable (fun p : ℕ × BitString × BitString =>
      aprioriApprox B.dCode p.1 p.2.1 p.2.2) :=
  aprioriApprox_computable B.dCode

/-- The dyadic approximations increase on their own fuel scale.
Blueprint node `FoundationPrefixCoding`. This fuel is not a V event index. -/
theorem conditional_coding_interface_mono (B : Base) (a b : BitString) :
    Monotone (fun s => dyadicValue (aprioriApprox B.dCode s a b) s) :=
  monotone_nat_of_le_succ (fun s ↦ aprioriApprox_mono B.dCode s a b)

/-- The supremum of the supplied code's dyadic approximations is its a priori mass.
Blueprint node `FoundationPrefixCoding`. -/
theorem conditional_coding_interface_limit (B : Base) (a b : BitString) :
    ⨆ s, dyadicValue (aprioriApprox B.dCode s a b) s = aprioriMeasure B.D a b :=
  aprioriApprox_iSup B.dCode B.dCode_eq a b

/-- Uniform conditional Kraft coding dominates every uniformly lower semicomputable mass.
Blueprint node `FoundationPrefixCoding`. The constant is chosen before either string. -/
theorem conditional_coding_interface_uniform (B : Base)
    (f : BitString → BitString → ℝ≥0∞) (hf : IsLSC f)
    (hmass : ∀ b, (∑' a : BitString, f a b) ≤ 1) :
    ∃ c : ℕ, ∀ a b, (2 : ℝ≥0∞)⁻¹ ^ c * f a b ≤ complexityWeight (KP B.D a b) := by
  obtain ⟨M, hM, c, hc⟩ := kraftChaitin_realization_bound hf 0 (by simpa using hmass)
  exact complexityWeight_dominates_of_prefix_realization B.optimalD hM hc

/-- Converts the condition `prefixCondComplexityContext z a k` of the conditional pair
complexity into the tuple condition `triple a k z` of the chain rule. -/
private def tripleCtx (s : BitString) : BitString :=
  triple (decodeFirst (decodeSecond s))
         (CodedFiniteDistribution.decodeNatCode (decodeSecond (decodeSecond s)))
         (decodeFirst s)

private theorem tripleCtx_computable : Computable tripleCtx := by
  have htuple : Computable (fun s : BitString =>
      (decodeFirst (decodeSecond s),
        CodedFiniteDistribution.decodeNatCode (decodeSecond (decodeSecond s)),
        decodeFirst s)) :=
    (decodeFirst_computable.comp decodeSecond_computable).pair
      ((CodedFiniteDistribution.decodeNatCode_primrec.to_comp.comp
        (decodeSecond_computable.comp decodeSecond_computable)).pair
        decodeFirst_computable)
  exact (triple_computable.1.comp htuple).of_eq (fun _ ↦ rfl)

/-- Upper exact conditional chain rule with the exact complexity in the second condition.
Blueprint node `FoundationPrefixChainRule`. All tuple fields use the fixed binary encoding. -/
theorem conditional_prefix_chain_interface (B : Base) :
    ∃ c : ℕ, ∀ (a b z : BitString) (k : ℕ), KP B.D a z = (k : ENat) →
      KP B.D (pairCode a b) z ≤ KP B.D a z + KP B.D b (triple a k z) + c := by
  obtain ⟨cMap, hMap⟩ := KP_cond_map_le B.D B.optimalD tripleCtx tripleCtx_computable
  obtain ⟨cUpper, hUpper⟩ := KPCondPair_chain_upper B.D B.optimalD
  refine ⟨cMap + cUpper, fun a b z k hk ↦ ?_⟩
  let y := prefixCondComplexityContext z a k
  have hy : tripleCtx y = triple a k z := by
    dsimp [y, prefixCondComplexityContext, tripleCtx]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode]
    rw [decodeSecond_pairCode, CodedFiniteDistribution.decodeNatCode_natCode]
  have h1 := hMap b y
  rw [hy] at h1
  have hk_cond : HasCondPrefixComplexityValue B.D a z k := hk.symm
  have h2 := hUpper a b z k hk_cond
  calc KP B.D (pairCode a b) z = KPCondPair B.D a b z := rfl
    _ ≤ KP B.D a z + KP B.D b y + (cUpper : ENat) := h2
    _ ≤ KP B.D a z + (KP B.D b (triple a k z) + (cMap : ENat)) + (cUpper : ENat) := by gcongr
    _ = KP B.D a z + KP B.D b (triple a k z) + ((cMap + cUpper : ℕ) : ENat) := by
      rw [Nat.cast_add]
      ac_rfl

/-- Converts the tuple condition `triple a k z` of the chain rule back into the condition
`prefixCondComplexityContext z a k` of the conditional pair complexity. -/
private def chainCtx (s : BitString) : BitString :=
  match Milovanov.decodeNat (decodeFirst (decodeSecond s)) with
  | some k => prefixCondComplexityContext (decodeSecond (decodeSecond s)) (decodeFirst s) k
  | none => []

private lemma chainCtx_computable : Computable chainCtx := by
  have h1 : Computable (fun s : BitString => decodeSecond (decodeSecond s)) :=
    decodeSecond_computable.comp decodeSecond_computable
  have h3 : Computable
      (fun s : BitString => Milovanov.decodeNat (decodeFirst (decodeSecond s))) :=
    bits_computable.2.comp (decodeFirst_computable.comp decodeSecond_computable)
  have h4 : Computable₂ (fun (s : BitString) (k : ℕ) ↦
      prefixCondComplexityContext (decodeSecond (decodeSecond s)) (decodeFirst s) k) := by
    have htuple : Computable (fun p : BitString × ℕ ↦
        ((decodeSecond (decodeSecond p.1), decodeFirst p.1), p.2)) :=
      (h1.comp Computable.fst).pair (decodeFirst_computable.comp Computable.fst) |>.pair
        Computable.snd
    exact (prefixCondComplexityContext_computable.comp htuple).of_eq (fun _ ↦ rfl)
  exact (Computable.option_casesOn h3 (Computable.const []) h4).of_eq (fun s ↦ by
    dsimp [chainCtx]
    cases Milovanov.decodeNat (decodeFirst (decodeSecond s)) <;> rfl)

/-- Lower exact conditional chain rule, with constant error independent of the condition.
Blueprint node `FoundationPrefixChainRule`. -/
theorem conditional_prefix_chain_interface_lower (B : Base) :
    ∃ c : ℕ, ∀ (a b z : BitString) (k : ℕ), KP B.D a z = (k : ENat) →
      KP B.D a z + KP B.D b (triple a k z) ≤ KP B.D (pairCode a b) z + c := by
  obtain ⟨cLower, hLower⟩ := KPCondPair_chain_lower B.D B.optimalD
  obtain ⟨cMap, hMapLe⟩ := KP_cond_map_le B.D B.optimalD chainCtx chainCtx_computable
  refine ⟨cLower + cMap, ?_⟩
  intro a b z k hk
  have hL := hLower a b z k hk.symm
  have hMap := hMapLe b (triple a k z)
  have hy : chainCtx (triple a k z) = prefixCondComplexityContext z a k := by
    dsimp [prefixCondComplexityContext, chainCtx, triple]
    rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode, decodeSecond_pairCode]
    rw [decodeNat_bits]
  rw [hy] at hMap
  calc
    KP B.D a z + KP B.D b (triple a k z)
      ≤ KP B.D a z + (KP B.D b (prefixCondComplexityContext z a k) + (cMap : ENat)) :=
        add_le_add le_rfl hMap
    _ = (KP B.D a z + KP B.D b (prefixCondComplexityContext z a k)) + (cMap : ENat) := by
        rw [add_assoc]
    _ ≤ (KPCondPair B.D a b z + (cLower : ENat)) + (cMap : ENat) := add_le_add hL le_rfl
    _ = KPCondPair B.D a b z + (cLower + cMap : ℕ) := by
        rw [Nat.cast_add, add_assoc]

/-- Adjoining the exact prefix complexity to the output costs a fixed constant.
Blueprint node `FoundationPrefixSelfSufficiency`. -/
theorem prefix_self_sufficiency_interface (B : Base) :
    ∃ c : ℕ, ∀ (a z : BitString) (k : ℕ), KP B.D a z = (k : ENat) →
      KP B.D (pairCode a (bits k)) z ≤ KP B.D a z + c := by
  obtain ⟨c1, h1⟩ := conditional_prefix_chain_interface B
  obtain ⟨c2, h2⟩ := KP_map_self_le B.D B.optimalD
    (fun s ↦ decodeFirst (decodeSecond s))
    (decodeFirst_computable.comp decodeSecond_computable)
  refine ⟨c1 + c2, fun a z k hk ↦ ?_⟩
  have hbits : decodeFirst (decodeSecond (triple a k z)) = bits k := by
    change decodeFirst (decodeSecond (pairCode a (pairCode (bits k) z))) = _
    rw [decodeSecond_pairCode, decodeFirst_pairCode]
  have h3 : KP B.D (bits k) (triple a k z) ≤ (c2 : ENat) := by
    have := h2 (triple a k z)
    rwa [hbits] at this
  calc KP B.D (pairCode a (bits k)) z
      ≤ KP B.D a z + KP B.D (bits k) (triple a k z) + (c1 : ENat) := h1 a (bits k) z k hk
    _ ≤ KP B.D a z + (c2 : ENat) + (c1 : ENat) := by gcongr
    _ = KP B.D a z + ((c1 + c2 : ℕ) : ENat) := by
        rw [Nat.cast_add, add_assoc, add_comm (c2 : ENat) (c1 : ENat)]

/-- Projection gives the other inequality in conditional prefix self-sufficiency.
Blueprint node `FoundationPrefixSelfSufficiency`. -/
theorem prefix_self_sufficiency_interface_lower (B : Base) :
    ∃ c : ℕ, ∀ (a z : BitString) (k : ℕ), KP B.D a z = (k : ENat) →
      KP B.D a z ≤ KP B.D (pairCode a (bits k)) z + c := by
  obtain ⟨cMap, hcMap⟩ := KP_map_le B.D B.optimalD decodeFirst decodeFirst_computable
  use cMap
  intro a z k _hk
  have hMap := hcMap (pairCode a (bits k)) z
  rw [decodeFirst_pairCode] at hMap
  exact hMap

open Classical in
/-- The plain decoder of a raw-suffix description: on input `w` it searches for the unique
prefix `p` of `w` with `D (p, [])` defined, and outputs `f (a, r)` for the output `a` of `D` on
`p` and the remaining suffix `r`. -/
private noncomputable def rawSuffixDecoder
    (B : Base) (f : BitString × BitString →. BitString) : BitString →. BitString :=
  fun w ↦ Nat.rfindOpt (fun n ↦
    if n ≤ w.length then
      let p := w.take n
      let r := w.drop n
      if hp : ∃ a, a ∈ B.D (p, []) then
        let a := Classical.choose hp
        if hf : ∃ z, z ∈ f (a, r) then
          some (Classical.choose hf)
        else none
      else none
    else none)

/-- The dovetailing candidate at search index `n = ⟪i, t⟫`: when `i ≤ w.length`, the output of
the code `c` on `(w.take i, [])` with fuel `t`, together with the split position `i`. -/
private def prefixStage (c : Nat.Partrec.Code) (w : BitString) (n : ℕ) :
    Option (ℕ × BitString) :=
  bif decide (n.unpair.1 ≤ w.length) then (twoStageS1 c w n).map (fun a ↦ (n.unpair.1, a))
  else none

private lemma prefixStage_computable (c : Nat.Partrec.Code) :
    Computable₂ (prefixStage c) := by
  have hsplit : Computable (fun p : BitString × ℕ ↦ p.2.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.snd)
  have hle : Computable (fun p : BitString × ℕ ↦ decide (p.2.unpair.1 ≤ p.1.length)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hsplit
      (Computable.list_length.comp Computable.fst)
  have hmap : Computable (fun p : BitString × ℕ ↦
      (twoStageS1 c p.1 p.2).map (fun a ↦ (p.2.unpair.1, a))) :=
    Computable.option_map (twoStageS1_computable c)
      ((hsplit.comp Computable.fst).pair Computable.snd)
  exact Computable.cond hle hmap (Computable.const none)

/-- Every output of `twoStageS1` for the code of `B.D` is an output of `B.D` on the
corresponding prefix of `w`. -/
private lemma mem_of_twoStageS1_eq_some (B : Base) (w : BitString) (m : ℕ) (a : BitString)
    (h : twoStageS1 B.dCode w m = some a) : a ∈ B.D (w.take m.unpair.1, []) := by
  unfold twoStageS1 at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e, he_eval, he_dec⟩ := h
  have h_eval_sound := Nat.Partrec.Code.evaln_sound he_eval
  rw [B.dCode_eq] at h_eval_sound
  unfold mapToNatFun at h_eval_sound
  rw [Part.mem_bind_iff] at h_eval_sound
  obtain ⟨input', hinput, houtput⟩ := h_eval_sound
  rw [Part.mem_ofOption] at hinput
  have hinput_eq : input' = (w.take m.unpair.1, []) := by
    apply Option.some.inj
    rw [← hinput, Encodable.encodek]
  subst input'
  rw [Part.mem_map_iff] at houtput
  obtain ⟨a', ha', heq⟩ := houtput
  have : a' = a := by
    apply Option.some.inj
    rw [← he_dec, ← heq, Encodable.encodek]
  subst a'
  exact ha'

/-- Every output of `B.D` on a prefix `w.take i` is found by `twoStageS1` for a suitable fuel. -/
private lemma exists_twoStageS1_eq_some (B : Base) (w : BitString) (i : ℕ) (a : BitString)
    (h : a ∈ B.D (w.take i, [])) : ∃ t, twoStageS1 B.dCode w (Nat.pair i t) = some a := by
  have H : (Encodable.encode a) ∈ B.dCode.eval (Encodable.encode (w.take i, ([] : BitString))) := by
    rw [B.dCode_eq]
    unfold mapToNatFun
    rw [Part.mem_bind_iff]
    refine ⟨(w.take i, []), ?_, ?_⟩
    · rw [Part.mem_ofOption, Encodable.encodek]
      exact rfl
    · rw [Part.mem_map_iff]
      exact ⟨a, h, rfl⟩
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp H
  exact ⟨t, by
    unfold twoStageS1
    simp only [Nat.unpair_pair]
    rw [ht]
    simp⟩

/-- Two prefixes of the same word on which the prefix machine `B.D` halts with empty condition
have the same length, because the domain at the empty condition is prefix-free. -/
private lemma eq_of_mem_take_of_mem_take (B : Base) (w : BitString) (i j : ℕ)
    (hi : i ≤ w.length) (hj : j ≤ w.length) (ai aj : BitString)
    (h_i : ai ∈ B.D (w.take i, [])) (h_j : aj ∈ B.D (w.take j, [])) : i = j := by
  have hpre := List.prefix_or_prefix_of_prefix (List.take_prefix i w) (List.take_prefix j w)
  have hpm : IsPrefixMachine B.D := B.optimalD.isPrefixMachine
  have heq : w.take i = w.take j := by
    rcases hpre with h | h
    · exact IsPrefixMachine.eq_of_prefix hpm h_i h_j h
    · exact (IsPrefixMachine.eq_of_prefix hpm h_j h_i h).symm
  have hl := congrArg List.length heq
  simpa [List.length_take, min_eq_left hi, min_eq_left hj] using hl

/-- Soundness of `prefixStage`: a candidate `(i, a)` is a prefix length of `w` together with an
output of `B.D` on that prefix. -/
private theorem prefixStage_sound
    (B : Base) (w : BitString) (m i : ℕ) (a : BitString)
    (h : prefixStage B.dCode w m = some (i, a)) :
    i ≤ w.length ∧ a ∈ B.D (w.take i, []) := by
  unfold prefixStage at h
  revert h
  cases hle : decide (m.unpair.1 ≤ w.length)
  · intro h
    simp only [Bool.cond_false] at h
    contradiction
  · intro h
    simp only [Bool.cond_true] at h
    have h_some : ∃ a', twoStageS1 B.dCode w m = some a' ∧ (m.unpair.1, a') = (i, a) := by
      cases h_ts : twoStageS1 B.dCode w m
      · rw [h_ts] at h
        contradiction
      · rw [h_ts] at h
        injection h with h_eq
        exact ⟨_, rfl, h_eq⟩
    rcases h_some with ⟨a', h1, h2⟩
    injection h2 with hi ha
    subst hi ha
    exact ⟨decide_eq_true_iff.mp hle, mem_of_twoStageS1_eq_some B w m a' h1⟩

/-- If `F n = some z` and `F m = none` for all `m < n`, then `z` is the output of
`Nat.rfindOpt F`. -/
private theorem mem_rfindOpt_of_first_some
    {α : Type} (F : ℕ → Option α) (n : ℕ) (z : α)
    (h : F n = some z) (hmin : ∀ m < n, F m = none) :
    z ∈ Nat.rfindOpt F := by
  unfold Nat.rfindOpt
  apply Part.mem_bind_iff.mpr
  use n
  constructor
  · apply Nat.mem_rfind.mpr
    constructor
    · exact Part.mem_some_iff.mpr (by simp [h])
    · intro m hm
      exact Part.mem_some_iff.mpr (by simp [hmin m hm])
  · rw [h]
    exact Part.mem_some_iff.mpr rfl

/-- If `D (p, [])` outputs `a` and `f (a, r)` outputs `z`, then the raw-suffix decoder outputs
`z` on `p ++ r`. -/
private theorem mem_rawSuffixDecoder_of_mem
    (B : Base) (f : BitString × BitString →. BitString)
    (p r a z : BitString) (hp : a ∈ B.D (p, [])) (hz : z ∈ f (a, r)) :
    z ∈ rawSuffixDecoder B f (p ++ r) := by
  classical
  have hlen : p.length ≤ (p ++ r).length := by simp
  have htake : (p ++ r).take p.length = p := List.take_left' rfl
  have hdrop : (p ++ r).drop p.length = r := List.drop_left' rfl
  have hp' : a ∈ B.D ((p ++ r).take p.length, []) := by
    simpa only [htake] using hp
  unfold rawSuffixDecoder
  apply mem_rfindOpt_of_first_some _ p.length z
  · dsimp only
    rw [ite_eq_left hlen]
    have hex : ∃ a', a' ∈ B.D ((p ++ r).take p.length, []) := ⟨a, hp'⟩
    rw [dite_eq_left hex]
    have ha : Classical.choose hex = a := Part.mem_unique (Classical.choose_spec hex) hp'
    have hz' : z ∈ f (Classical.choose hex, (p ++ r).drop p.length) := by
      simpa only [ha, hdrop] using hz
    have hex2 : ∃ z', z' ∈ f (Classical.choose hex, (p ++ r).drop p.length) := ⟨z, hz'⟩
    rw [dite_eq_left hex2]
    exact congrArg some (Part.mem_unique (Classical.choose_spec hex2) hz')
  · intro m hm
    dsimp only
    have hmlen : m ≤ (p ++ r).length := (Nat.le_of_lt hm).trans hlen
    rw [ite_eq_left hmlen]
    have hno : ¬ ∃ a', a' ∈ B.D ((p ++ r).take m, []) := by
      rintro ⟨a', ha'⟩
      exact (Nat.ne_of_lt hm)
        (eq_of_mem_take_of_mem_take B (p ++ r) m p.length hmlen hlen a' a ha' hp')
    rw [dite_eq_right hno]

/-- The raw-suffix decoder is the dovetailed search `Nat.rfindOpt (prefixStage B.dCode w)` for
the split position and the output `a` of `B.D`, followed by `f` on `a` and the remaining suffix. -/
private lemma rawSuffixDecoder_eq_bind_rfindOpt
    (B : Base) (f : BitString × BitString →. BitString) (w : BitString) :
    rawSuffixDecoder B f w =
      (Nat.rfindOpt (prefixStage B.dCode w)).bind (fun q ↦ f (q.2, w.drop q.1)) := by
  apply Part.ext
  intro z_val
  constructor
  · intro hz
    unfold rawSuffixDecoder at hz
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hz
    dsimp only at hn
    split_ifs at hn with h1 h2 h3
    · have ha_spec : (Classical.choose h2) ∈ B.D (w.take n, []) := Classical.choose_spec h2
      rw [Option.mem_def, Option.some.injEq] at hn
      have hz_val : z_val ∈ f (Classical.choose h2, w.drop n) := by
        rw [← hn]
        exact Classical.choose_spec h3
      obtain ⟨t, ht⟩ := exists_twoStageS1_eq_some B w n (Classical.choose h2) ha_spec
      have h_stage : prefixStage B.dCode w (Nat.pair n t) = some (n, Classical.choose h2) := by
        unfold prefixStage
        simp only [Nat.unpair_pair, h1, decide_true, Bool.cond_true]
        rw [ht]
        simp
      have h_dom : (Nat.rfindOpt (prefixStage B.dCode w)).Dom :=
        Nat.rfindOpt_dom.mpr ⟨Nat.pair n t, ⟨(n, Classical.choose h2), h_stage⟩⟩
      obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp h_dom
      obtain ⟨i, hi⟩ := Nat.rfindOpt_spec hq
      have h_sound := prefixStage_sound B w i q.1 q.2 hi
      have h_unique := eq_of_mem_take_of_mem_take B w q.1 n h_sound.1 h1 q.2
        (Classical.choose h2) h_sound.2 ha_spec
      subst h_unique
      have h_a_eq : q.2 = Classical.choose h2 := Part.mem_unique h_sound.2 ha_spec
      refine Part.mem_bind_iff.mpr ⟨q, hq, ?_⟩
      rw [h_a_eq]
      exact hz_val
    all_goals contradiction
  · intro hz
    obtain ⟨q, hq, hzq⟩ := Part.mem_bind_iff.mp hz
    obtain ⟨i, hi⟩ := Nat.rfindOpt_spec hq
    have h_sound := prefixStage_sound B w i q.1 q.2 hi
    have h_dec := mem_rawSuffixDecoder_of_mem B f (w.take q.1) (w.drop q.1) q.2 z_val
      h_sound.2 hzq
    rwa [List.take_append_drop] at h_dec

private lemma rawSuffixDecoder_partrec
    (B : Base) (f : BitString × BitString →. BitString) (hf : Partrec f) :
    Partrec (fun x : BitString × BitString ↦ rawSuffixDecoder B f x.1) := by
  have h_first : Partrec (fun x : BitString × BitString ↦
      Nat.rfindOpt (prefixStage B.dCode x.1)) :=
    (Partrec.rfindOpt (prefixStage_computable B.dCode)).comp Computable.fst.partrec
  have h_inner : Computable (fun p : (BitString × BitString) × (ℕ × BitString) ↦
      (p.2.2, p.1.1.drop p.2.1)) := by
    have hc_drop : Computable (fun p : (BitString × BitString) × (ℕ × BitString) ↦
        p.1.1.drop p.2.1) :=
      (Primrec.list_drop.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).to_comp
    exact Computable.pair (Computable.snd.comp Computable.snd) hc_drop
  have h_second : Partrec₂ (fun (x : BitString × BitString) (q : ℕ × BitString) ↦
      f (q.2, x.1.drop q.1)) := hf.comp h_inner
  exact (Partrec.bind h_first h_second).of_eq
    (fun x ↦ (rawSuffixDecoder_eq_bind_rfindOpt B f x.1).symm)

/-- To bound the plain complexity of `z` by `KPPlain B.D a + |r| + c` it suffices to do so for
every prefix program `p` of `a`. -/
private lemma plainK_le_KPPlain_add_of_forall_program
    (B : Base) (a r z : BitString) (c : ℕ)
    (hbound : ∀ p : BitString, a ∈ B.D (p, []) →
      plainK B.V z ≤ (p.length : ENat) + (r.length : ENat) + (c : ENat)) :
    plainK B.V z ≤ KPPlain B.D a + (r.length : ENat) + (c : ENat) := by
  by_cases ha : KPPlain B.D a = ⊤
  · rw [ha]
    exact le_top
  obtain ⟨p, hp, hp_len⟩ := exists_program_of_KP_ne_top ha
  have hp_bound := hbound p hp
  rw [hp_len] at hp_bound
  exact hp_bound

/-- A prefix description followed by raw data is a plain description for any fixed decoder.
Blueprint node `FoundationPrefixRaw`. The partial decoder is uniform in both fields. -/
theorem plain_prefix_program_raw_suffix (B : Base)
    (f : BitString × BitString →. BitString) (hf : Partrec f) :
    ∃ c : ℕ, ∀ a r z : BitString, z ∈ f (a, r) →
      plainK B.V z ≤ KPPlain B.D a + (r.length : ENat) + c := by
  let D_dec : Map := fun p ↦ rawSuffixDecoder B f p.1
  obtain ⟨c1, hc1⟩ := B.optimalV.2 D_dec (rawSuffixDecoder_partrec B f hf)
  refine ⟨c1, fun a r z hz ↦ ?_⟩
  apply plainK_le_KPPlain_add_of_forall_program B a r z c1
  intro p hp
  have h_dec : z ∈ D_dec (p ++ r, []) := mem_rawSuffixDecoder_of_mem B f p r a z hp hz
  have hz_D : condK D_dec z [] ≤ (programLength (p ++ r) : ENat) :=
    sInf_le ⟨p ++ r, h_dec, rfl⟩
  calc
    plainK B.V z = condK B.V z [] := rfl
    _ ≤ condK D_dec z [] + c1 := hc1 z []
    _ ≤ (programLength (p ++ r) : ENat) + (c1 : ENat) := add_le_add hz_D le_rfl
    _ = (p.length : ENat) + (r.length : ENat) + c1 := by
      rw [programLength, List.length_append, Nat.cast_add, add_assoc]

/-- Two conditional prefix programs can be composed with a fixed overhead.
Blueprint node `FoundationConditionalComposition`. -/
theorem conditional_prefix_composition (B : Base) :
    ∃ c : ℕ, ∀ x y z : BitString,
      KP B.D x z ≤ KP B.D y z + KP B.D x (pairCode y z) + c := by
  let ctx : BitString → BitString → Nat → BitString := fun z y _ ↦ pairCode y z
  have hargs : Computable (fun p : (BitString × BitString) × ℕ ↦ (p.1.2, p.1.1)) :=
    (Computable.snd.comp Computable.fst).pair (Computable.fst.comp Computable.fst)
  have hctx : Computable (fun p : (BitString × BitString) × ℕ ↦ ctx p.1.1 p.1.2 p.2) :=
    Computable.of_eq (pairCode_computable.comp hargs) (fun _ ↦ rfl)
  have hD_decomp := condTwoStagePairBuilder_isDecompressor B.optimalD.isDecompressor
    B.optimalD.isPrefixMachine hctx
  have hD_prefix := condTwoStagePairBuilder_isPrefixMachine (ctx := ctx) B.optimalD.isPrefixMachine
  let D := condTwoStagePairBuilder B.D ctx
  have hD : IsPrefixDecompressor D := ⟨hD_decomp, hD_prefix⟩
  obtain ⟨c_inv, hc_inv⟩ := B.optimalD.invariance hD
  obtain ⟨c_map, hc_map⟩ := KP_map_le B.D B.optimalD decodeSecond decodeSecond_computable
  use c_inv + c_map
  intro x y z
  by_cases hpx : KP B.D x (pairCode y z) = ⊤
  · rw [hpx]; simp
  by_cases hpy : KP B.D y z = ⊤
  · rw [hpy]; simp
  obtain ⟨q, hq, _⟩ := exists_program_of_KP_ne_top (M := B.D) (x := x) (y := pairCode y z) hpx
  obtain ⟨p, hp, _⟩ := exists_program_of_KP_ne_top (M := B.D) (x := y) (y := z) hpy
  have hq' : produces B.D q (ctx z y p.length) x := hq
  have h_bound := KP_condTwoStagePairBuilder_le_of_produces (U := B.D) (ctx := ctx)
    B.optimalD.isPrefixMachine hp hq'
  have h_bound2 : KP D (pairCode y x) z ≤ KP B.D y z + KP B.D x (pairCode y z) := by
    calc KP D (pairCode y x) z ≤ ((p.length + q.length : Nat) : ENat) := h_bound
      _ = (p.length : ENat) + (q.length : ENat) := by norm_cast
      _ = KP B.D y z + KP B.D x (pairCode y z) := by
        rw [KP_le_programLength_of_produces hp |>.antisymm (by aesop),
            KP_le_programLength_of_produces hq |>.antisymm (by aesop)]
  have h_extract : KP B.D x z ≤ KP D (pairCode y x) z + c_inv + c_map := by
    calc KP B.D x z = KP B.D (decodeSecond (pairCode y x)) z := by rw [decodeSecond_pairCode]
      _ ≤ KP B.D (pairCode y x) z + c_map := hc_map (pairCode y x) z
      _ ≤ KP D (pairCode y x) z + c_inv + c_map := by gcongr; exact hc_inv (pairCode y x) z
  calc KP B.D x z ≤ KP D (pairCode y x) z + c_inv + c_map := h_extract
    _ ≤ KP B.D y z + KP B.D x (pairCode y z) + c_inv + c_map := by gcongr
    _ = KP B.D y z + KP B.D x (pairCode y z) + (c_inv + c_map : ℕ) := by
      rw [ENat.natCast_add, add_assoc]

/-- Removing auxiliary information charges its unconditional prefix complexity.
Blueprint node `FoundationConditionalComposition`. -/
theorem conditional_prefix_composition_remove (B : Base) :
    ∃ c : ℕ, ∀ x z t : BitString,
      KP B.D x z ≤ KP B.D x (pairCode z t) + KPPlain B.D t + c :=
  KP_cond_remove_short_info B.D B.optimalD

/-- Strips the padding `0^j 1` of an index word: drops everything up to and including the first
`true`. -/
private def unpadIndex (w : BitString) : BitString :=
  w.drop (w.findIdx id + 1)

private lemma unpadIndex_computable : Computable unpadIndex := by
  have hidx : Primrec (fun w : BitString ↦ w.findIdx id) :=
    Primrec.list_findIdx Primrec.id
      (Primrec.snd : Primrec₂ (fun (_ : BitString) (b : Bool) ↦ b))
  have h : Primrec (fun w : BitString ↦ w.drop (w.findIdx id + 1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp hidx) Primrec.id
  exact h.to_comp

private lemma unpadIndex_replicate_append (j : ℕ) (p : BitString) :
    unpadIndex (List.replicate j false ++ true :: p) = p := by
  have h : (List.replicate j false ++ true :: p).findIdx id = j := by
    induction j with
    | zero => simp [List.findIdx_cons]
    | succ j ih => simp [List.replicate_succ, List.findIdx_cons, ih]
  unfold unpadIndex
  rw [h]
  simp [List.drop_append]

/-- Fixed-width wrapper: in the condition `bits q` accept exactly the index words of length
`q + 1`, so the domain at each condition is prefix-free. -/
private def fixedWidthWrapper (V : Map) : Map := fun pr ↦
  bif (pr.1.length == decodeBits pr.2.reverse + 1)
    then V (unpadIndex pr.1, [])
    else Part.none

private lemma fixedWidthWrapper_isDecompressor (V : Map) (hV : isDecompressor V) :
    isDecompressor (fixedWidthWrapper V) := by
  unfold fixedWidthWrapper isDecompressor
  have hcond : Computable (fun pr : BitString × BitString ↦
      pr.1.length == decodeBits pr.2.reverse + 1) := by
    apply Primrec.to_comp
    apply Primrec₂.comp Primrec.beq
    · exact Primrec.list_length.comp Primrec.fst
    · exact Primrec.succ.comp (primrec_decodeBits.comp (Primrec.list_reverse.comp Primrec.snd))
  have hbody : Partrec (fun pr : BitString × BitString ↦
      V (unpadIndex pr.1, ([] : BitString))) :=
    hV.comp ((unpadIndex_computable.comp Computable.fst).pair (Computable.const []))
  exact Partrec.cond hcond hbody Partrec.none

private lemma fixedWidthWrapper_isPrefixMachine (V : Map) :
    IsPrefixMachine (fixedWidthWrapper V) := by
  intro y p hp q hq hpre
  unfold domainAt fixedWidthWrapper at hp hq
  dsimp at hp hq
  have hp_cond : p.length == decodeBits y.reverse + 1 := by
    cases h : p.length == decodeBits y.reverse + 1
    · rw [h] at hp; change False at hp; exact False.elim hp
    · rfl
  have hq_cond : q.length == decodeBits y.reverse + 1 := by
    cases h : q.length == decodeBits y.reverse + 1
    · rw [h] at hq; change False at hq; exact False.elim hq
    · rfl
  have hlen : p.length = q.length := by
    have h1 := beq_iff_eq.mp hp_cond
    have h2 := beq_iff_eq.mp hq_cond
    omega
  exact hpre.eq_of_length hlen

/-- A supplied upper bound on plain complexity suffices as prefix length advice.
Blueprint node `FoundationPlainPrefixBounds`. This is an arbitrary threshold, not an equality. -/
theorem plain_prefix_supplied_length_interface (B : Base) :
    ∃ c : ℕ, ∀ (x : BitString) (q : ℕ), plainK B.V x ≤ (q : ENat) →
      KP B.D x (bits q) ≤ (q : ENat) + c := by
  have hM : IsPrefixDecompressor (fixedWidthWrapper B.V) :=
    ⟨fixedWidthWrapper_isDecompressor B.V B.optimalV.1, fixedWidthWrapper_isPrefixMachine B.V⟩
  obtain ⟨c, hc⟩ := B.optimalD.invariance hM
  refine ⟨c + 1, fun x q hq ↦ ?_⟩
  obtain ⟨p, hp, hprod⟩ := (simple_iff_exists_program B.V x q).mp hq
  have hdec : decodeBits (bits q).reverse = q := by
    by_cases hn : q = 0
    · subst hn; rfl
    · simp [bits, hn]
  have hlen : (List.replicate (q - p.length) false ++ true :: p).length = q + 1 := by
    simp; omega
  have hw : produces (fixedWidthWrapper B.V)
      (List.replicate (q - p.length) false ++ true :: p) (bits q) x := by
    unfold produces fixedWidthWrapper
    dsimp
    have hb : ((List.replicate (q - p.length) false ++ true :: p).length ==
        decodeBits (bits q).reverse + 1) = true := by
      rw [hlen, hdec]
      exact beq_self_eq_true _
    rw [hb, Bool.cond_true, unpadIndex_replicate_append]
    exact hprod
  calc
    KP B.D x (bits q)
        ≤ KP (fixedWidthWrapper B.V) x (bits q) + (c : ENat) := hc x (bits q)
    _ ≤ ((List.replicate (q - p.length) false ++ true :: p).length : ENat) + (c : ENat) := by
          gcongr
          exact KP_le_programLength_of_produces hw
    _ = (q : ENat) + ((c + 1 : ℕ) : ENat) := by
          rw [hlen]
          push_cast
          ring

/-- A conditional prefix program `p` for `x` in the condition `bits r.length`, where `p` is a
prefix of `r`, is found by a fixed partial recursive function `f` that dovetails the prefix
machine on the prefixes of `r`. -/
private lemma exists_partrec_of_prefix_produces (B : Base) :
    ∃ (f : BitString × BitString →. BitString), Partrec f ∧
      ∀ (r p x : BitString), p <+: r →
        produces B.D p (bits r.length) x →
        x ∈ f ([], r) := by
  let f : BitString × BitString →. BitString := fun ⟨_, r⟩ ↦
    prefixExtensionMap B.dCode (r, bits r.length)
  have hc : B.dCode.eval = fun n ↦
      (Part.ofOption (Encodable.decode n)).bind fun a ↦
        Part.map Encodable.encode (B.D a) := B.dCode_eq
  have hf : Partrec f := by
    apply (prefixExtensionMap_partrec B.dCode).comp
    apply Computable.pair
    · exact Computable.snd
    · exact bits_computable.1.comp (Computable.list_length.comp Computable.snd)
  use f, hf
  intro r p x hp_pre hp_prod
  have hmem : Encodable.encode x ∈ B.dCode.eval (Encodable.encode (p, bits r.length)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, bits r.length), by simp, Part.mem_map Encodable.encode hp_prod⟩
  obtain ⟨t, ht⟩ : ∃ t, Nat.Partrec.Code.evaln t B.dCode (Encodable.encode (p, bits r.length))
      = some (Encodable.encode x) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    exact ⟨k, Option.mem_def.mp hk⟩
  have hn_out : prefixExtensionOut B.dCode p (bits r.length) (Nat.pair p.length t) = some x := by
    unfold prefixExtensionOut
    simp only [Nat.unpair_pair]
    have hdec : decide (p.length ≤ p.length) = true := decide_eq_true (le_refl _)
    rw [hdec]
    simp only [ite_true, List.take_length, ht, Option.bind_some, Encodable.encodek]
  have hcheck : prefixExtensionCheck B.dCode p (bits r.length) (Nat.pair p.length t) = true := by
    unfold prefixExtensionCheck; rw [hn_out]; rfl
  have hrdom : (Nat.rfind (show ℕ →. Bool from fun m ↦
      Part.some (prefixExtensionCheck B.dCode p (bits r.length) m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p.length t, by rw [Part.mem_some_iff, hcheck], fun {m} _ ↦ Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hcheck' : prefixExtensionCheck B.dCode p (bits r.length) n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hcheck'
  have hmem_p : x' ∈ prefixExtensionMap B.dCode (p, bits r.length) := by
    unfold prefixExtensionMap
    rw [Part.mem_bind_iff]
    exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hx'⟩
  obtain ⟨p', hp'p, hp'prod⟩ := prefixExtensionMap_mem_imp_produces hc hmem_p
  have hp_eq : p' = p :=
    IsPrefixMachine.eq_of_prefix B.optimalD.isPrefixMachine hp'prod hp_prod hp'p
  have hprod_p : produces B.D p (bits r.length) x' := hp_eq ▸ hp'prod
  have hx_eq : x' = x := Part.mem_unique hprod_p hp_prod
  have hmem_p_x : x ∈ prefixExtensionMap B.dCode (p, bits r.length) := hx_eq ▸ hmem_p
  exact prefixExtensionMap_isPrefixStableMachine hc B.optimalD.isPrefixMachine
    (bits r.length) p r x hmem_p_x hp_pre

/-- A conditional prefix program within its supplied length budget yields a plain description.
Blueprint node `FoundationPlainPrefixBounds`. No unbounded slack is hidden in the condition. -/
theorem plain_prefix_supplied_length_interface_reverse (B : Base) :
    ∃ c : ℕ, ∀ (x : BitString) (q : ℕ), KP B.D x (bits q) ≤ (q : ENat) →
      plainK B.V x ≤ (q : ENat) + c := by
  obtain ⟨f, hf_partrec, hf_spec⟩ := exists_partrec_of_prefix_produces B
  obtain ⟨c_raw, hc_raw⟩ := plain_prefix_program_raw_suffix B f hf_partrec
  use literalBound B [] + c_raw
  intro x q hq
  have h_ne_top : KP B.D x (bits q) ≠ ⊤ := (hq.trans_lt (WithTop.coe_lt_top q)).ne
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top h_ne_top
  have hp_len_le : p.length ≤ q := by
    rw [← ENat.natCast_le_natCast]
    change (programLength p : ENat) ≤ q
    rw [hp_len]
    exact hq
  let r : BitString := p ++ List.replicate (q - p.length) false
  have hr_len : r.length = q := by simp [r]; omega
  have hp_pre : p <+: r := ⟨List.replicate (q - p.length) false, rfl⟩
  have hp_prod' : produces B.D p (bits r.length) x := by
    rw [hr_len]
    exact hp_prod
  have h_plain := hc_raw [] r x (hf_spec r p x hp_pre hp_prod')
  calc
    plainK B.V x ≤ KPPlain B.D [] + (r.length : ENat) + (c_raw : ENat) := h_plain
    _ ≤ (literalBound B [] : ENat) + (r.length : ENat) + (c_raw : ENat) := by
      gcongr
      exact B.literal_bound [] []
    _ = (r.length : ENat) + ((literalBound B [] + c_raw : ℕ) : ENat) := by
      rw [add_comm (literalBound B [] : ENat), add_assoc, ← ENat.natCast_add]
    _ = (q : ENat) + ((literalBound B [] + c_raw : ℕ) : ENat) := by rw [hr_len]

end Kolmogorov.Milovanov
