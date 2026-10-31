/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.StoppingComplexity.Words
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.LSCApproximation
import Mathlib.Algebra.Order.Group.Int
import KolmogorovMathlib.RandomStrings.Plain.Basic
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import KolmogorovMathlib.RandomStrings.Plain.PrefixInterface
import KolmogorovMathlib.RandomStrings.Plain.Enumeration
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

/-!
# Extension counts and dyadic crossing descriptions

This module defines the strict and relaxed extension counts and their common density contract
for blueprint node `key:density`. It bounds the number of strict dyadic crossings of a
semimeasure and constructs a uniform partial computable decoder for those crossings. A crossing
is described by its rank in a duplicate-free enumeration, using a raw block whose length
recovers the scale. `ExtensionDensity.Density` uses this decoder to establish the lower density
bound after paying the compiler overhead.
-/

namespace Kolmogorov.Milovanov

open scoped ENNReal

/-- The description budget `H(h) = 2^h` at scale `h`. Blueprint node `key:density`. -/
def extensionScale (h : ℕ) : ℕ := 2 ^ h

/-- The extension indices whose encoded pair has plain complexity at most `H(h) + δ`.
Blueprint node `key:density`. The final coordinate is attached without recoding the base. -/
def extensionSet (B : Base) (h δ : ℕ) (y : BitString) : Set BitString :=
  {s | Simple B.V (pairCode y s) (extensionScale h + δ)}

/-- The semantic relaxed extension count `A_h^δ(y)`. Blueprint node `key:density`. -/
noncomputable def extensionCount (B : Base) (h δ : ℕ) (y : BitString) : ℕ :=
  (extensionSet B h δ y).ncard

/-- The semantic strict extension count `A_h(y)`. Blueprint node `key:density`. -/
noncomputable def strictExtensionCount (B : Base) (h : ℕ) (y : BitString) : ℕ :=
  extensionCount B h 0 y

/-- Every conditional prefix complexity has a natural witness, by the frozen literal bound.
Blueprint node `key:density`. Finite witnesses justify the integer exponents. -/
theorem prefix_complexity_finite_value (B : Base) (a b : BitString) :
    ∃ k : ℕ, KP B.D a b = (k : ENat) := by
  have hfinite : KP B.D a b < ⊤ :=
    (literal_and_tuple_code_interface B a b).trans_lt (ENat.natCast_lt_top _)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfinite)
  exact ⟨k, hk.symm⟩

/-- Every extension set is finite, by injectivity of its last-coordinate encoding.
Blueprint node `key:density`. -/
theorem extension_set_finite (B : Base) (h δ : ℕ) (y : BitString) :
    (extensionSet B h δ y).Finite := by
  apply Set.Finite.preimage (s := {z | Simple B.V z (extensionScale h + δ)})
    (f := fun s ↦ pairCode y s)
  · intro s _ t _ hst
    simpa only [decodeSecond_pairCode] using congrArg decodeSecond hst
  · exact (simple_finite_card_lt B.V (extensionScale h + δ)).1

/-- The common-constant strict and relaxed density contract, with an explicit finite value.
Blueprint node `key:density`. `k` is identified with `KP` before entering an exponent. -/
def ExtensionDensityBounds (B : Base) (c₀ cDen cRel : ℕ) : Prop :=
  ∀ (h : ℕ) (y : BitString) (k : ℕ), KP B.D y (bits h) = (k : ENat) →
    k + c₀ ≤ extensionScale h →
    (2 : ℚ) ^ ((extensionScale h : ℤ) - k - cDen) ≤ strictExtensionCount B h y ∧
    (strictExtensionCount B h y : ℚ) ≤
      (2 : ℚ) ^ ((extensionScale h : ℤ) - k + cDen) ∧
    ∀ δ : ℕ, (extensionCount B h δ y : ℚ) ≤
      (2 : ℚ) ^ ((cRel : ℤ) * (δ + 1)) * strictExtensionCount B h y

/-- Positive integer multiples of the quantum `2⁻ᴸ` strictly below the mass of an output. -/
abbrev dyadicCrossings (m : BitString → ℝ≥0∞) (L : ℕ) : Set (BitString × ℕ) :=
  {p | 1 ≤ p.2 ∧ ((p.2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L)) < m p.1}

/-- The conditional a priori mass with the scale index `h` as the condition. -/
noncomputable abbrev scaleAprioriMass (B : Base) (h : ℕ) (y : BitString) : ℝ≥0∞ :=
  aprioriMeasure B.D y (bits h)

private lemma finset_nat_card_le_max (S : Finset ℕ) (hS : S.Nonempty) (h1 : ∀ x ∈ S, 1 ≤ x) :
    S.card ≤ S.max' hS := by
  have H : S ⊆ Finset.Icc 1 (S.max' hS) := by
    intro x hx
    rw [Finset.mem_Icc]
    exact ⟨h1 x hx, Finset.le_max' S x hx⟩
  calc S.card ≤ (Finset.Icc 1 (S.max' hS)).card := Finset.card_le_card H
  _ = S.max' hS + 1 - 1 := by rw [Nat.card_Icc]
  _ = S.max' hS := rfl

/-- A semimeasure has fewer than `2 ^ L` strict crossings of multiples of `2⁻ᴸ`. -/
private lemma dyadicCrossings_finite_card_lt (m : BitString → ℝ≥0∞)
    (hm : (∑' y, m y) ≤ 1) (L : ℕ) :
    (dyadicCrossings m L).Finite ∧ (dyadicCrossings m L).ncard < 2 ^ L := by
  classical
  have hbound : ∀ E : Finset (BitString × ℕ),
      (E : Set (BitString × ℕ)) ⊆ dyadicCrossings m L → E.card < 2 ^ L := by
    intro E hE
    by_cases hE_empty : E.card = 0
    · rw [hE_empty]; apply Nat.two_pow_pos
    have hE_ne : E.Nonempty := Finset.card_pos.mp (by omega)
    have hfiber : ∀ y ∈ E.image Prod.fst,
        ((E.filter (fun p ↦ p.1 = y)).card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L) < m y := by
      intro y hy
      obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hy
      have hFne : ((E.filter (fun p ↦ p.1 = p0.1)).image Prod.snd).Nonempty :=
        ⟨p0.2, Finset.mem_image.mpr ⟨p0, Finset.mem_filter.mpr ⟨hp0, rfl⟩, rfl⟩⟩
      obtain ⟨pJ, hpJ, hpJ2⟩ := Finset.mem_image.mp (Finset.max'_mem _ hFne)
      have hcardle : (E.filter (fun p ↦ p.1 = p0.1)).card ≤ pJ.2 := by
        have hinj : Set.InjOn Prod.snd
            (↑(E.filter (fun p ↦ p.1 = p0.1)) : Set (BitString × ℕ)) := by
          intro a ha b hb hab
          exact Prod.ext
            (((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2).symm) hab
        calc (E.filter (fun p ↦ p.1 = p0.1)).card
            = ((E.filter (fun p ↦ p.1 = p0.1)).image Prod.snd).card :=
              (Finset.card_image_of_injOn hinj).symm
            _ ≤ ((E.filter (fun p ↦ p.1 = p0.1)).image Prod.snd).max' hFne := by
              apply finset_nat_card_le_max _ hFne
              intro x hx
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
              have hp_mem : p ∈ E := (Finset.mem_filter.mp hp).1
              exact (hE hp_mem).1
            _ = pJ.2 := hpJ2.symm
      have hpJ_mem : pJ ∈ E := (Finset.mem_filter.mp hpJ).1
      have hpJ_cross : pJ ∈ dyadicCrossings m L := hE hpJ_mem
      have h_pJ2_lt : ((pJ.2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L)) < m pJ.1 := hpJ_cross.2
      have hpJ1_eq : pJ.1 = p0.1 := (Finset.mem_filter.mp hpJ).2
      rw [hpJ1_eq] at h_pJ2_lt
      have hcard_cast_le : ((E.filter (fun p ↦ p.1 = p0.1)).card : ℝ≥0∞) ≤ (pJ.2 : ℝ≥0∞) :=
        Nat.cast_le.mpr hcardle
      have h_mul_le : ((E.filter (fun p ↦ p.1 = p0.1)).card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L)
        ≤ (pJ.2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L) := by
        exact mul_le_mul_of_nonneg_right hcard_cast_le zero_le
      exact lt_of_le_of_lt h_mul_le h_pJ2_lt
    have h_sum1 := ENNReal.sum_lt_sum_of_nonempty (hE_ne.image Prod.fst) hfiber
    have hsum : ∑ y ∈ E.image Prod.fst,
        ((E.filter (fun p ↦ p.1 = y)).card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L) =
          (E.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, ← Finset.card_eq_sum_card_image]
    have hmass : (E.card : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L) < 1 := by
      rw [← hsum]
      exact h_sum1.trans_le ((ENNReal.sum_le_tsum _).trans hm)
    have hpow0 : (2 : ℝ≥0∞) ^ L ≠ 0 := by positivity
    have hpowTop : (2 : ℝ≥0∞) ^ L ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    rw [← ENNReal.inv_pow, ← div_eq_mul_inv,
      ENNReal.div_lt_iff (Or.inl hpow0) (Or.inl hpowTop), one_mul] at hmass
    exact_mod_cast hmass
  -- A uniform bound on finite subsets also proves finiteness.
  have h_fin : (dyadicCrossings m L).Finite := by
    by_contra h_inf
    obtain ⟨E, hE1, hE2⟩ := Set.Infinite.exists_subset_card_eq h_inf (2 ^ L)
    have h_lt := hbound E hE1
    omega
  constructor
  · exact h_fin
  · have h_card := hbound h_fin.toFinset (by simp)
    have h_eq : (dyadicCrossings m L).ncard = h_fin.toFinset.card :=
      Set.ncard_eq_toFinset_card _ h_fin
    rwa [h_eq]

/-- Decode a candidate output, crossing index, and approximation stage. -/
private def decodeCrossingCandidate (t : ℕ) : BitString × ℕ × ℕ :=
  match Encodable.decode (α := BitString × ℕ × ℕ) t with
  | some (y, j, s) => (y, j, s)
  | none => (bits 0, 0, 0)

private def crossingEnumeration (B : Base) (args : ℕ × ℕ × ℕ) : Option (BitString × ℕ) :=
  let c := args.1
  let h := args.2.1
  let t := args.2.2
  let (y, j, s) := decodeCrossingCandidate t
  let L := extensionScale h - c
  let numerator := aprioriApprox B.dCode s y (bits h)
  if 1 ≤ j ∧ j * 2^s < numerator * 2^L then
    some (y, j)
  else
    none

private lemma dyadic_mul_lt_iff (j n L s : ℕ) :
    (j : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ L) < dyadicValue n s ↔
      j * 2 ^ s < n * 2 ^ L := by
  have hL0 : (2 : ℝ≥0∞) ^ L ≠ 0 := by positivity
  have hLTop : (2 : ℝ≥0∞) ^ L ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hs0 : (2 : ℝ≥0∞) ^ s ≠ 0 := by positivity
  have hsTop : (2 : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [dyadicValue, ← ENNReal.inv_pow, ← div_eq_mul_inv,
    ENNReal.div_lt_iff (Or.inl hL0) (Or.inl hLTop),
    ← ENNReal.mul_div_right_comm, ENNReal.lt_div_iff_mul_lt (Or.inl hs0) (Or.inl hsTop)]
  exact_mod_cast Iff.rfl

private lemma range_crossingEnumeration (B : Base) (c h : ℕ) :
    {p | ∃ t, crossingEnumeration B (c, h, t) = some p} =
      dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c) := by
  ext ⟨y, j⟩
  constructor
  · rintro ⟨t, ht⟩
    unfold crossingEnumeration at ht
    dsimp only at ht
    split at ht
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj ht)
      refine ⟨hcond.1, (dyadic_mul_lt_iff _ _ _ _).mpr hcond.2 |>.trans_le ?_⟩
      rw [scaleAprioriMass, ← aprioriApprox_iSup B.dCode B.dCode_eq]
      exact le_iSup (fun s ↦ dyadicValue
        (aprioriApprox B.dCode s (decodeCrossingCandidate t).1 (bits h)) s) _
    · contradiction
  · rintro ⟨hj, hlt⟩
    change _ < aprioriMeasure B.D y (bits h) at hlt
    rw [← aprioriApprox_iSup B.dCode B.dCode_eq] at hlt
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hlt
    refine ⟨Encodable.encode (y, j, s), ?_⟩
    have hcond := (dyadic_mul_lt_iff j _ _ s).mp hs
    simp [crossingEnumeration, decodeCrossingCandidate, Encodable.encodek, hj, hcond]

private lemma computable_crossingEnumeration (B : Base) : Computable (crossingEnumeration B) := by
  let D := decodeCrossingCandidate
  have hd : Computable D := by
    have H : Computable (fun t : ℕ ↦
        (Encodable.decode (α := BitString × ℕ × ℕ) t).getD
          (bits 0, 0, 0)) :=
      Computable.option_getD Computable.decode
        (Computable.const (bits 0, 0, 0))
    apply H.of_eq
    intro t
    change _ = decodeCrossingCandidate t
    unfold decodeCrossingCandidate
    cases Encodable.decode (α := BitString × ℕ × ℕ) t with
    | none => rfl
    | some p => rcases p with ⟨y, j, s⟩; rfl
  have hc : Computable (fun q : ℕ × ℕ × ℕ ↦ q.1) := Computable.fst
  have hh : Computable (fun q : ℕ × ℕ × ℕ ↦ q.2.1) :=
    Computable.fst.comp Computable.snd
  have ht : Computable (fun q : ℕ × ℕ × ℕ ↦ q.2.2) :=
    Computable.snd.comp Computable.snd
  have hD := hd.comp ht
  have hy := Computable.fst.comp hD
  have hj := (Computable.fst.comp Computable.snd).comp hD
  have hs := (Computable.snd.comp Computable.snd).comp hD
  have hp : Computable (fun n : ℕ ↦ 2 ^ n) :=
    Kolmogorov.primrec_two_pow_aux.to_comp
  have hL := Primrec.nat_sub.to_comp.comp (hp.comp hh) hc
  have hn := (conditional_coding_interface_approx B).comp
    (hs.pair (hy.pair (bits_computable.1.comp hh)))
  have hlhs := Primrec.nat_mul.to_comp.comp hj (hp.comp hs)
  have hrhs := Primrec.nat_mul.to_comp.comp hn (hp.comp hL)
  have hpos := Primrec.nat_le.decide.to_comp.comp (Computable.const 1) hj
  have hlt := Primrec.nat_lt.decide.to_comp.comp hlhs hrhs
  have hb := Primrec.and.to_comp.comp hpos hlt
  have ho := Computable.option_some.comp (hy.pair hj)
  have h_ite := Computable.cond hb ho (Computable.const none)
  exact h_ite.of_eq (fun args ↦ by
    dsimp only
    unfold crossingEnumeration
    rw [← Bool.decide_and, Bool.cond_decide]
    rfl)

/-- Retain first occurrences among the crossings enumerated before stage `t`. -/
private def crossingList (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ))
    (c h t : ℕ) : List (BitString × ℕ) :=
  ((List.range t).filterMap (fun s ↦ enum (c, h, s))).eraseDups

/-- Recover the scale from the raw block length, then look up its rank at stage `t`. -/
private def crossingDecoderStage (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ))
    (args : BitString × BitString) (t : ℕ) : Option BitString :=
  let a := args.1
  let r := args.2
  match Milovanov.decodeNat a with
  | none => none
  | some c =>
      let sum := r.length + c
      match (List.range (sum + 1)).find? (fun h ↦ extensionScale h == sum) with
      | none => none
      | some h =>
          let idx := decodeBits r.reverse
          let l := crossingList enum c h t
          match l[idx]? with
          | none => none
          | some p => some (pairCode p.1 (bits p.2))

/-- Wait until the crossing at the rank encoded by the raw block has appeared. -/
private def crossingDecoder (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ)) :
    BitString × BitString →. BitString :=
  fun args ↦ Nat.rfindOpt (crossingDecoderStage enum args)

private lemma computable_crossingList
    (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ))
    (henum_comp : Computable enum) :
    Computable (fun p : ℕ × ℕ × ℕ ↦ crossingList enum p.1 p.2.1 p.2.2) := by
  have hmap : Computable (fun p : ℕ × ℕ × ℕ ↦
      (List.range p.2.2).map (fun s ↦ enum (p.1, p.2.1, s))) :=
    Computable.list_map
      (Primrec.list_range.to_comp.comp (Computable.snd.comp Computable.snd))
      (henum_comp.comp ((Computable.fst.comp Computable.fst).pair
        (((Computable.fst.comp Computable.snd).comp Computable.fst).pair Computable.snd)))
  have hfilter : Primrec (fun l : List (Option (BitString × ℕ)) ↦ l.filterMap id) :=
    Primrec.listFilterMap Primrec.id Primrec.snd
  have h := (primrec_eraseDups (α := BitString × ℕ)).to_comp.comp
    (hfilter.to_comp.comp hmap)
  exact h.of_eq (fun p ↦ by simp only [crossingList, List.filterMap_map, Function.comp_def, id_eq])

private lemma computable_find_scale :
    Computable (fun n : ℕ ↦
      (List.range (n + 1)).find? (fun h ↦ extensionScale h == n)) := by
  apply Primrec.to_comp
  apply list_find?_primrec (Primrec.list_range.comp Primrec.succ)
  exact Primrec.beq.comp (primrec_two_pow_aux.comp Primrec.snd) Primrec.fst

private lemma computable_crossingDecoderStage
    (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ))
    (henum_comp : Computable enum) :
    Computable₂ (crossingDecoderStage enum) := by
  have hlist :=
    computable_crossingList
      enum henum_comp
  have hlookup : Computable (fun q : ℕ × ℕ × ℕ × BitString ↦
      ((crossingList enum q.1 q.2.1 q.2.2.1)[decodeBits q.2.2.2.reverse]?).map
        encF) := by
    have hl : Computable (fun q : ℕ × ℕ × ℕ × BitString ↦
        crossingList enum q.1 q.2.1 q.2.2.1) :=
      hlist.comp (g := fun q : ℕ × ℕ × ℕ × BitString ↦ (q.1, q.2.1, q.2.2.1))
        (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
          (Computable.fst.comp (Computable.snd.comp Computable.snd))))
    have hi : Computable (fun q : ℕ × ℕ × ℕ × BitString ↦
        decodeBits q.2.2.2.reverse) :=
      primrec_decodeBits.to_comp.comp (Computable.list_reverse.comp
        (Computable.snd.comp (Computable.snd.comp Computable.snd)))
    exact Computable.option_map (Computable.list_getElem?.comp hl hi)
      (encF_computable.1.comp Computable.snd)
  have hsum : Computable (fun q : ℕ × BitString × ℕ ↦ q.2.1.length + q.1) :=
    Primrec.nat_add.to_comp.comp
      (Computable.list_length.comp (Computable.fst.comp Computable.snd)) Computable.fst
  have hfind : Computable (fun q : ℕ × BitString × ℕ ↦
      (List.range (q.2.1.length + q.1 + 1)).find?
        (fun h ↦ extensionScale h == q.2.1.length + q.1)) :=
    computable_find_scale.comp hsum
  have hbody : Computable₂ (fun (q : ℕ × BitString × ℕ) (h : ℕ) ↦
      ((crossingList enum q.1 h q.2.2)[decodeBits q.2.1.reverse]?).map encF) :=
    hlookup.comp (g := fun q : (ℕ × BitString × ℕ) × ℕ ↦
      (q.1.1, q.2, q.1.2.2, q.1.2.1)) ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
          (Computable.fst.comp (Computable.snd.comp Computable.fst)))))
  have hrun := Computable.option_bind hfind hbody
  have hparse : Computable (fun q : (BitString × BitString) × ℕ ↦
      Milovanov.decodeNat q.1.1) :=
    bits_computable.2.comp (Computable.fst.comp Computable.fst)
  have hrest : Computable₂ (fun (q : (BitString × BitString) × ℕ) (c : ℕ) ↦
      ((List.range (q.1.2.length + c + 1)).find?
        (fun h ↦ extensionScale h == q.1.2.length + c)).bind
        (fun h ↦ ((crossingList enum c h q.2)[decodeBits q.1.2.reverse]?).map encF)) :=
    hrun.comp (g := fun q : ((BitString × BitString) × ℕ) × ℕ ↦
      (q.2, q.1.1.2, q.1.2)) (Computable.snd.pair
    ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
      (Computable.snd.comp Computable.fst)))
  refine (Computable.option_bind hparse hrest).of_eq (fun q ↦ ?_)
  cases hc : Milovanov.decodeNat q.1.1 with
  | none => simp [crossingDecoderStage, hc]
  | some c =>
    cases hh : (List.range (q.1.2.length + c + 1)).find?
        (fun h ↦ extensionScale h == q.1.2.length + c) with
    | none => simp [crossingDecoderStage, hc, hh]
    | some h =>
      cases hi : (crossingList enum c h q.2)[decodeBits q.1.2.reverse]? <;>
        simp [crossingDecoderStage, hc, hh, hi, encF]

private lemma exists_complete_crossingList (B : Base) (c h : ℕ) :
    ∃ T, (crossingList (crossingEnumeration B) c h T).length < 2 ^ (extensionScale h - c) ∧
      ∀ p, p ∈ crossingList (crossingEnumeration B) c h T ↔
        p ∈ dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c) := by
  classical
  obtain ⟨hfin, hcard⟩ := dyadicCrossings_finite_card_lt (scaleAprioriMass B h)
    (conditional_coding_interface_mass B (bits h)) (extensionScale h - c)
  have hex : ∀ p ∈ dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c),
      ∃ t, crossingEnumeration B (c, h, t) = some p := by
    intro p hp
    exact (Set.ext_iff.mp (range_crossingEnumeration B c h) p).mpr hp
  let stage := fun p ↦ if hp : p ∈ dyadicCrossings (scaleAprioriMass B h)
      (extensionScale h - c) then Classical.choose (hex p hp) else 0
  obtain ⟨N, hN⟩ := (hfin.image stage).bddAbove
  have hmem : ∀ p, p ∈ crossingList (crossingEnumeration B) c h (N + 1) ↔
      p ∈ dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c) := by
    intro p
    simp only [crossingList, List.mem_eraseDups, List.mem_filterMap, List.mem_range]
    constructor
    · rintro ⟨t, _, ht⟩
      exact (Set.ext_iff.mp (range_crossingEnumeration B c h) p).mp ⟨t, ht⟩
    · intro hp
      refine ⟨stage p, Nat.lt_succ_of_le (hN (Set.mem_image_of_mem stage hp)), ?_⟩
      simpa only [stage, dite_eq_left hp] using Classical.choose_spec (hex p hp)
  refine ⟨N + 1, ?_, hmem⟩
  have hset : (↑(crossingList (crossingEnumeration B) c h (N + 1)).toFinset : Set _) =
      dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c) := by
    ext p
    simpa only [Finset.mem_coe, List.mem_toFinset] using hmem p
  rw [← hset, Set.ncard_coe_finset, crossingList, List.toFinset_card_of_nodup
    (Kolmogorov.nodup_eraseDups_list _)] at hcard
  exact hcard

private lemma decodeBits_append (l1 l2 : List Bool) :
  decodeBits (l1 ++ l2) = decodeBits l1 + decodeBits l2 * 2 ^ l1.length := by
  induction l1 with
  | nil => simp [decodeBits]
  | cons b t ih =>
    cases b <;> simp only [List.cons_append, decodeBits, ih, List.length_cons, pow_succ] <;> ring

private lemma decodeBits_reverse (l : List Bool) : decodeBits l.reverse = natOfBits l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [List.reverse_cons, decodeBits_append, ih, List.length_reverse]
    cases b
    · simp [decodeBits, natOfBits]
    · simp only [decodeBits, natOfBits, ↓reduceIte]
      ring

private lemma exists_fixed_length_index
    (S : List (BitString × ℕ)) (L : ℕ) (h_len : S.length < 2 ^ L) :
    ∀ x ∈ S, ∃ r : BitString, r.length = L ∧
      ∃ i, decodeBits r.reverse = i ∧ S[i]? = some x := by
  intro x hx
  obtain ⟨idx, hidx_eq⟩ := List.mem_iff_getElem?.mp hx
  have hidx_lt := (List.getElem?_eq_some_iff.mp hidx_eq).1
  have h_idx_lt_L : idx < 2 ^ L := lt_trans hidx_lt h_len
  use bitsOfNatBE L idx
  constructor
  · rw [length_bitsOfNatBE L idx]
  · use idx
    constructor
    · rw [decodeBits_reverse]
      exact natOfBits_bitsOfNatBE h_idx_lt_L
    · exact hidx_eq

private lemma find_scale_eq (h : ℕ) :
    (List.range (extensionScale h + 1)).find?
      (fun k ↦ extensionScale k == extensionScale h) = some h := by
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp, h, ?_, ?_, ?_⟩
  · simpa only [List.length_range, extensionScale] using
      Nat.lt_succ_of_le (Nat.le_of_lt (Nat.lt_two_pow_self (n := h)))
  · simp
  · intro j hj
    simp only [List.getElem_range, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact fun heq ↦ (Nat.ne_of_lt hj) (Nat.pow_right_injective (by omega) heq)

private lemma crossingList_getElem?_mono
    (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ)) (c h i : ℕ)
    {m n : ℕ} (hmn : m ≤ n) {p : BitString × ℕ}
    (hp : (crossingList enum c h m)[i]? = some p) :
    (crossingList enum c h n)[i]? = some p := by
  have hprefix : List.range n = List.range m ++ (List.range n).drop m := by
    have htake : (List.range n).take m = List.range m := by
      rw [List.take_range, Nat.min_eq_left hmn]
    rw [← htake, List.take_append_drop]
  unfold crossingList at hp ⊢
  rw [hprefix, List.filterMap_append, List.eraseDups_append, List.getElem?_append]
  have hi := (List.getElem?_eq_some_iff.mp hp).1
  simpa only [hi, ↓reduceIte] using hp

private lemma pairCode_mem_crossingDecoder
    (enum : ℕ × ℕ × ℕ → Option (BitString × ℕ)) (c h : ℕ)
    (r : BitString) (hr : r.length + c = extensionScale h)
    {T : ℕ} {p : BitString × ℕ}
    (hp : (crossingList enum c h T)[decodeBits r.reverse]? = some p) :
    pairCode p.1 (bits p.2) ∈ crossingDecoder enum (bits c, r) := by
  have hstage : ∀ t, crossingDecoderStage enum (bits c, r) t =
      ((crossingList enum c h t)[decodeBits r.reverse]?).map encF := by
    intro t
    simp only [crossingDecoderStage, decodeNat_bits, hr, find_scale_eq]
    cases (crossingList enum c h t)[decodeBits r.reverse]? <;> rfl
  apply (Nat.rfindOpt_mono _).mpr
  · exact ⟨T, by rw [hstage, hp]; rfl⟩
  · intro a m n hmn hm
    rw [hstage] at hm ⊢
    cases hmidx : (crossingList enum c h m)[decodeBits r.reverse]? with
    | none => simp [hmidx] at hm
    | some p =>
      rw [crossingList_getElem?_mono enum c h _ hmn hmidx]
      simpa only [hmidx] using hm

/-- A uniform partial computable decoder describes every strict dyadic crossing using a block
of length `extensionScale h - c`, given the encoded offset `c`. Blueprint node `key:density`. -/
lemma exists_dyadic_crossing_decoder (B : Base) :
    ∃ f : BitString × BitString →. BitString, Partrec f ∧
    ∀ (c h : ℕ), c ≤ extensionScale h →
      ∃ inj : BitString × ℕ → BitString,
        (∀ p ∈ dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c),
          (inj p).length = extensionScale h - c ∧ pairCode p.1 (bits p.2) ∈ f (bits c, inj p)) := by
  refine ⟨crossingDecoder (crossingEnumeration B),
    Partrec.rfindOpt (computable_crossingDecoderStage _ (computable_crossingEnumeration B)), ?_⟩
  intro c h hc
  obtain ⟨T, hlen, hmem⟩ := exists_complete_crossingList B c h
  have hindex := exists_fixed_length_index (crossingList (crossingEnumeration B) c h T)
    (extensionScale h - c) hlen
  let description := fun p ↦ if hp : p ∈ crossingList (crossingEnumeration B) c h T then
    Classical.choose (hindex p hp) else bitsOfNatBE (extensionScale h - c) 0
  refine ⟨description, ?_⟩
  intro p hp
  have hpmem := (hmem p).mpr hp
  obtain ⟨hrlen, i, hrval, hpval⟩ := Classical.choose_spec (hindex p hpmem)
  simp only [description, dite_eq_left hpmem]
  refine ⟨hrlen, pairCode_mem_crossingDecoder _ c h _ (by omega) (T := T) ?_⟩
  rwa [hrval]

end Kolmogorov.Milovanov
