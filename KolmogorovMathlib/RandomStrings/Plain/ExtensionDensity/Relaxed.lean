/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Density

/-!
# Relaxed extension density and computable projections

For blueprint node `key:density`, normalized relaxed extension counts give a lower
semicomputable conditional semimeasure. Conditional coding bounds these counts, and strict
density then bounds the cost of relaxation by a factor exponential in the added budget.
The common density constants are used to prove the extension-volume bound for partial
computable projections (`key:projection`), which the extension transfer arguments use.
-/

namespace Kolmogorov.Milovanov
open scoped ENNReal
open Kolmogorov

private noncomputable def relaxedExtensionMass (B : Base) (y b : BitString) : ENNReal :=
  match decodeExtensionCondition b with
  | some (h, δ) => (extensionCount B h δ y : ENNReal) * (2 : ENNReal)⁻¹ ^ (extensionScale h + δ + 1)
  | none => 0

private def relaxedExtensionApprox (B : Base) (t : ℕ) (y b : BitString) : ℕ :=
  match decodeExtensionCondition b with
  | some (h, δ) =>
    if extensionScale h + δ + 1 ≤ t then
      let E_nt := stageOutputs B (extensionScale h + δ) t
      let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
      a_t * 2 ^ (t - (extensionScale h + δ + 1))
    else 0
  | none => 0

private lemma decodeExtensionCondition_pairCode (h δ : ℕ) :
    decodeExtensionCondition (pairCode (bits h) (bits δ)) = some (h, δ) := by
  simp [decodeExtensionCondition, decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits]

/-- The paired condition normalizes the count by its plain description budget. -/
private lemma relaxedExtensionMass_pairCode (B : Base) :
    ∀ (h δ : ℕ) (y : BitString),
      relaxedExtensionMass B y (pairCode (bits h) (bits δ)) =
        ((extensionCount B h δ y : ENNReal) / (2 : ENNReal) ^ (extensionScale h + δ + 1)) := by
  intro h δ y
  simp only [relaxedExtensionMass, decodeExtensionCondition_pairCode]
  rw [div_eq_mul_inv, ENNReal.inv_pow]

/-- The sum of extension counts is bounded by the number of short plain programs. -/
private lemma tsum_extensionCount_le (B : Base) (h δ : ℕ) :
    (∑' y : BitString, (extensionCount B h δ y : ℝ≥0∞)) ≤
        (2 : ℝ≥0∞) ^ (extensionScale h + δ + 1) := by
  let S := {z : BitString | Simple B.V z (extensionScale h + δ)}
  have hS_fin_lt := simple_finite_card_lt B.V (extensionScale h + δ)
  have hS_fin : S.Finite := hS_fin_lt.1
  have hS_lt : S.ncard < 2 ^ (extensionScale h + δ + 1) := hS_fin_lt.2
  have hS_card : hS_fin.toFinset.card < 2 ^ (extensionScale h + δ + 1) := by
    rw [← Set.ncard_eq_toFinset_card S hS_fin]
    exact hS_lt
  let T (y : BitString) := (extension_set_finite B h δ y).toFinset.image (fun s ↦ pairCode y s)
  have hT_subset : ∀ y, (T y : Set BitString) ⊆ S := by
    intro y z hz
    simp only [T, Finset.mem_coe, Finset.mem_image, Set.Finite.mem_toFinset, extensionSet] at hz
    obtain ⟨s, hs, hz_eq⟩ := hz
    rw [← hz_eq]
    exact hs
  have hT_card : ∀ y, (T y).card = extensionCount B h δ y := by
    intro y
    rw [Finset.card_image_of_injective]
    · exact (Set.ncard_eq_toFinset_card (extensionSet B h δ y) (extension_set_finite B h δ y)).symm
    · intro s1 s2 hs
      have h1 := congrArg decodeSecond hs
      rw [decodeSecond_pairCode, decodeSecond_pairCode] at h1
      exact h1
  have hT_disj : ∀ y1 y2, y1 ≠ y2 → Disjoint (T y1) (T y2) := by
    intro y1 y2 hneq
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    simp only [T, Finset.mem_image, Set.Finite.mem_toFinset] at ha hb
    obtain ⟨s1, _, ha_eq⟩ := ha
    obtain ⟨s2, _, hb_eq⟩ := hb
    rw [← ha_eq, ← hb_eq] at hab
    have h1 := congrArg decodeFirst hab
    rw [decodeFirst_pairCode, decodeFirst_pairCode] at h1
    exact hneq h1
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  have h_sum : ∑ y ∈ F, (extensionCount B h δ y : ℝ≥0∞) = (∑ y ∈ F, (T y).card : ℕ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [hT_card y]
  have h_union : ∑ y ∈ F, (T y).card = (F.biUnion T).card := by
    rw [Finset.card_biUnion]
    intro x _ y _ hneq
    exact hT_disj x y hneq
  have h_fin_lt : (F.biUnion T).card < 2 ^ (extensionScale h + δ + 1) := by
    apply lt_of_le_of_lt _ hS_card
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨y, _, hz_y⟩ := hz
    have hz_s := hT_subset y hz_y
    rwa [Set.Finite.mem_toFinset]
  rw [h_sum, h_union]
  have h_fin_le : ((F.biUnion T).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (extensionScale h + δ + 1) := by
    exact_mod_cast le_of_lt h_fin_lt
  exact h_fin_le

/-- Normalized relaxed extension counts form a conditional semimeasure. -/
private lemma tsum_relaxedExtensionMass_le_one (B : Base) :
    ∀ b, (∑' a : BitString, relaxedExtensionMass B a b) ≤ 1 := by
  intro b
  dsimp [relaxedExtensionMass]
  cases hb : decodeExtensionCondition b
  · simp
  · rename_i ctx
    rcases ctx with ⟨h, δ⟩
    dsimp only
    have h1 := tsum_extensionCount_le B h δ
    have h2 : (∑' (y : BitString), (extensionCount B h δ y : ℝ≥0∞) *
        (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + δ + 1)) =
        (∑' (y : BitString), (extensionCount B h δ y : ℝ≥0∞)) *
            (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + δ + 1) := by
      exact ENNReal.tsum_mul_right
    rw [h2]
    have h3 : (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + δ + 1) =
        ((2 : ℝ≥0∞) ^ (extensionScale h + δ + 1))⁻¹ := by
      exact ENNReal.inv_pow.symm
    rw [h3]
    have h4 : (∑' (y : BitString), (extensionCount B h δ y : ℝ≥0∞)) *
        ((2 : ℝ≥0∞) ^ (extensionScale h + δ + 1))⁻¹
        ≤ ((2 : ℝ≥0∞) ^ (extensionScale h + δ + 1)) *
            ((2 : ℝ≥0∞) ^ (extensionScale h + δ + 1))⁻¹ := by
      apply mul_le_mul h1 (le_refl _) zero_le zero_le
    apply le_trans h4
    have h5 : ((2 : ℝ≥0∞) ^ (extensionScale h + δ + 1)) *
        ((2 : ℝ≥0∞) ^ (extensionScale h + δ + 1))⁻¹ = 1 := by
      apply ENNReal.mul_inv_cancel
      · exact ENNReal.pow_ne_zero (by simp) _
      · exact ENNReal.pow_ne_top (by simp)
    rw [h5]

/-- The normalized stage counts increase with the enumeration stage. -/
private lemma relaxedExtensionApprox_le_succ (B : Base) :
    ∀ (s : ℕ) (out ctx : BitString),
      dyadicValue (relaxedExtensionApprox B s out ctx) s ≤
        dyadicValue (relaxedExtensionApprox B (s + 1) out ctx) (s + 1) := by
  intro s out ctx
  dsimp [relaxedExtensionApprox]
  cases hctx : decodeExtensionCondition ctx with
  | none =>
    simp [dyadicValue_zero]
  | some hd =>
    obtain ⟨h, δ⟩ := hd
    dsimp only
    split_ifs with h_le_s h_le_s_plus
    · let stage := extensionScale h + δ + 1
      let E_s := stageOutputs B (extensionScale h + δ) s
      let E_sp1 := stageOutputs B (extensionScale h + δ) (s + 1)
      let a_s := (E_s.filter (fun z ↦ z == pairCode out (decodeSecond z))).card
      let a_sp1 := (E_sp1.filter (fun z ↦ z == pairCode out (decodeSecond z))).card
      change dyadicValue (a_s * 2 ^ (s - stage)) s ≤
        dyadicValue (a_sp1 * 2 ^ (s + 1 - stage)) (s + 1)
      rw [dyadicValue_natCast_mul_left, dyadicValue_two_pow_sub h_le_s,
        dyadicValue_natCast_mul_left, dyadicValue_two_pow_sub h_le_s_plus]
      gcongr
      have H_subset : E_s ⊆ E_sp1 :=
        (canonical_enumeration_spec_mono B (extensionScale h + δ) (Nat.le_succ s)).1
      have H_filter : E_s.filter (fun z ↦ z == pairCode out (decodeSecond z)) ⊆
          E_sp1.filter (fun z ↦ z == pairCode out (decodeSecond z)) :=
        Finset.filter_subset_filter _ H_subset
      exact_mod_cast Finset.card_le_card H_filter
    · omega
    · simp [dyadicValue_zero]
    · simp [dyadicValue_zero]

/-- Every extension counted at a finite stage belongs to the full extension set. -/
private lemma stage_relaxed_extension_count_le (B : Base) (h δ t : ℕ) (y : BitString) :
    let E_nt := stageOutputs B (extensionScale h + δ) t
    let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
    a_t ≤ extensionCount B h δ y := by
  let S := (extension_set_finite B h δ y).toFinset
  have heq : (stageOutputs B (extensionScale h + δ) t).filter
      (fun z ↦ z == pairCode y (decodeSecond z)) ⊆
      S.image (fun s ↦ pairCode y s) := by
    intro z hz
    simp only [Finset.mem_filter, beq_iff_eq] at hz
    obtain ⟨hz_mem, hz_eq⟩ := hz
    simp only [Finset.mem_image]
    refine ⟨decodeSecond z, ?_, hz_eq.symm⟩
    simp only [S, Set.Finite.mem_toFinset, extensionSet,
      Set.mem_ofPred_eq]
    rw [← hz_eq]
    exact (canonical_enumeration_spec_union B
      (extensionScale h + δ) z).mpr ⟨t, hz_mem⟩
  have hinj : Function.Injective (fun s : BitString ↦ pairCode y s) := by
    intro s1 s2 he
    simpa only [decodeSecond_pairCode] using congrArg decodeSecond he
  calc ((stageOutputs B (extensionScale h + δ) t).filter (fun z ↦
      z == pairCode y (decodeSecond z))).card
    _ ≤ (S.image (fun s ↦ pairCode y s)).card := Finset.card_le_card heq
    _ = S.card := Finset.card_image_of_injective S hinj
    _ = extensionCount B h δ y := by
      exact (Set.ncard_eq_toFinset_card (extensionSet B h δ y) (extension_set_finite B h δ y)).symm

/-- All extensions have appeared by a common finite stage. -/
private lemma stage_relaxed_extension_count_eventually_eq (B : Base) (h δ : ℕ) (y : BitString) :
    ∃ T, ∀ t, T ≤ t →
      let E_nt := stageOutputs B (extensionScale h + δ) t
      let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
      a_t = extensionCount B h δ y := by
  classical
  let S := (extension_set_finite B h δ y).toFinset
  have hstage : ∀ s : BitString, ∃ n : ℕ,
      s ∈ S → pairCode y s ∈ stageOutputs B (extensionScale h + δ) n := by
    intro s
    by_cases hs : s ∈ S
    · have hsimple : Simple B.V (pairCode y s) (extensionScale h + δ) := by
        simpa only [S, Set.Finite.mem_toFinset, extensionSet,
          Set.mem_ofPred_eq] using hs
      obtain ⟨n, hn⟩ :=
        (canonical_enumeration_spec_union B (extensionScale h + δ)
          (pairCode y s)).mp hsimple
      exact ⟨n, fun _ ↦ hn⟩
    · exact ⟨0, fun hs' ↦ (hs hs').elim⟩
  choose f hf using hstage
  refine ⟨S.sup f, ?_⟩
  intro t ht
  change ((stageOutputs B (extensionScale h + δ) t).filter
    (fun z ↦ z == pairCode y (decodeSecond z))).card =
      extensionCount B h δ y
  have heq : (stageOutputs B (extensionScale h + δ) t).filter
      (fun z ↦ z == pairCode y (decodeSecond z)) =
      S.image (fun s ↦ pairCode y s) := by
    ext z
    simp only [Finset.mem_filter, beq_iff_eq, Finset.mem_image]
    constructor
    · rintro ⟨hz, hz_eq⟩
      refine ⟨decodeSecond z, ?_, hz_eq.symm⟩
      simp only [S, Set.Finite.mem_toFinset, extensionSet,
        Set.mem_ofPred_eq]
      rw [← hz_eq]
      exact (canonical_enumeration_spec_union B
        (extensionScale h + δ) z).mpr ⟨t, hz⟩
    · rintro ⟨s, hs, hsz⟩
      have hz_eq : z = pairCode y s := hsz.symm
      constructor
      · rw [hz_eq]
        have hs_sup : f s ≤ S.sup f := Finset.le_sup hs
        have h_t_ge : f s ≤ t := le_trans hs_sup ht
        exact (canonical_enumeration_spec_mono B
          (extensionScale h + δ) h_t_ge).1 (hf s hs)
      · rw [hz_eq, decodeSecond_pairCode]
  have hinj : Function.Injective (fun s : BitString ↦ pairCode y s) := by
    intro s1 s2 he
    simpa only [decodeSecond_pairCode] using congrArg decodeSecond he
  rw [heq, Finset.card_image_of_injective S hinj]
  exact (Set.ncard_eq_toFinset_card (extensionSet B h δ y)
    (extension_set_finite B h δ y)).symm

/-- The normalized stage counts converge to the full normalized extension count. -/
private lemma iSup_relaxedExtensionApprox (B : Base) :
    ∀ (out ctx : BitString),
      (⨆ s, dyadicValue (relaxedExtensionApprox B s out ctx) s) =
        relaxedExtensionMass B out ctx := by
  intro out ctx
  cases h_decode : decodeExtensionCondition ctx with
  | none =>
      simp [relaxedExtensionApprox,
        relaxedExtensionMass, h_decode, dyadicValue_zero]
  | some hd =>
      obtain ⟨h, δ⟩ := hd
      simp only [relaxedExtensionMass, h_decode]
      let a (t : ℕ) :=
        (stageOutputs B (extensionScale h + δ) t |>.filter
          (fun z ↦ z == pairCode out (decodeSecond z))).card
      have hval (t : ℕ) (ht : extensionScale h + δ + 1 ≤ t) :
          dyadicValue (relaxedExtensionApprox
            B t out ctx) t =
            (a t : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + δ + 1) := by
        have h_eq : relaxedExtensionApprox B t out ctx =
            a t * 2 ^ (t - (extensionScale h + δ + 1)) := by
          unfold relaxedExtensionApprox
          rw [h_decode]
          dsimp only
          exact ite_eq_left ht
        rw [h_eq]
        rw [dyadicValue_natCast_mul_left, dyadicValue_two_pow_sub ht]
      have hzero (t : ℕ) (ht : ¬ (extensionScale h + δ + 1 ≤ t)) :
          dyadicValue (relaxedExtensionApprox
            B t out ctx) t = 0 := by
        have h_eq : relaxedExtensionApprox B t out ctx = 0 := by
          unfold relaxedExtensionApprox
          rw [h_decode]
          dsimp only
          exact ite_eq_right ht
        rw [h_eq]
        exact dyadicValue_zero t
      have hle (t : ℕ) : a t ≤ extensionCount B h δ out := by
        simpa [a] using
          (stage_relaxed_extension_count_le
            B h δ t out)
      obtain ⟨T, hT⟩ :=
        stage_relaxed_extension_count_eventually_eq B h δ out
      apply le_antisymm
      · apply iSup_le
        intro t
        by_cases ht : extensionScale h + δ + 1 ≤ t
        · rw [hval t ht]
          gcongr
          exact_mod_cast hle t
        · rw [hzero t ht]
          exact zero_le
      · let t := max T (extensionScale h + δ + 1)
        have ht : extensionScale h + δ + 1 ≤ t := le_max_right _ _
        have hTt : T ≤ t := le_max_left _ _
        refine le_iSup_of_le t ?_
        have hT_eval : a t = extensionCount B h δ out := by
          simpa [a] using hT t hTt
        rw [hval t ht, hT_eval]

/-- The integer numerators of the normalized stage counts are computable. -/
private lemma computable_relaxedExtensionApprox (B : Base) :
    Computable (fun p : ℕ × BitString × BitString ↦
      relaxedExtensionApprox B p.1 p.2.1 p.2.2) := by
  have hp_t : Computable (fun (p : ℕ × BitString × BitString) ↦ p.1) := Computable.fst
  have hp_y : Computable (fun (p : ℕ × BitString × BitString) ↦ p.2.1) :=
    Computable.fst.comp Computable.snd
  have hp_b : Computable (fun (p : ℕ × BitString × BitString) ↦ p.2.2) :=
    Computable.snd.comp Computable.snd
  have ho_1 : Computable (fun (p : ℕ × BitString × BitString) ↦
      Milovanov.decodeNat (decodeFirst p.2.2)) :=
    bits_computable.2.comp (decodeFirst_computable.comp hp_b)
  have ho_2 : Computable (fun (p : ℕ × BitString × BitString) ↦
      Milovanov.decodeNat (decodeSecond p.2.2)) :=
    bits_computable.2.comp (decodeSecond_computable.comp hp_b)
  have ho : Computable (fun (p : ℕ × BitString × BitString) ↦ decodeExtensionCondition p.2.2) := by
    have h_inner : Computable₂ (fun (p : ℕ × BitString × BitString) (h : ℕ) ↦
        (Milovanov.decodeNat (decodeSecond p.2.2)).map (fun d ↦ (h, d))) := by
      have hd : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
          Milovanov.decodeNat (decodeSecond q.1.2.2)) :=
        ho_2.comp Computable.fst
      have h_map : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
          (Milovanov.decodeNat (decodeSecond q.1.2.2)).map (fun d ↦ (q.2, d))) := by
        have hc : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦ q.2) := Computable.snd
        have h_pair : Computable₂ (fun (q : (ℕ × BitString × BitString) × ℕ) (d : ℕ) ↦ (q.2, d)) :=
          (hc.comp Computable.fst).pair Computable.snd
        exact Computable.option_map hd h_pair
      exact h_map
    exact Computable.option_bind ho_1 h_inner
  have hf : Computable (fun (p : ℕ × BitString × BitString) ↦ (0 : ℕ)) := Computable.const 0
  have ht : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦ q.1.1) :=
    hp_t.comp Computable.fst
  have hy : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦ q.1.2.1) :=
    hp_y.comp Computable.fst
  have hh : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦ q.2.1) :=
    Computable.fst.comp Computable.snd
  have hd : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦ q.2.2) :=
    Computable.snd.comp Computable.snd
  have hext : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦ extensionScale q.2.1) :=
    primrec_two_pow_aux.to_comp.comp hh
  have hext_d : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      extensionScale q.2.1 + q.2.2) :=
    Computable₂.comp Primrec.nat_add.to_comp hext hd
  have hext_succ : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      extensionScale q.2.1 + q.2.2 + 1) :=
    Computable.succ.comp hext_d
  have hcond : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      decide (extensionScale q.2.1 + q.2.2 + 1 ≤ q.1.1)) := by
    have hle : Computable₂ (fun (a b : ℕ) ↦ decide (a ≤ b)) :=
      (PrimrecRel.decide Primrec.nat_le).to_comp
    exact Computable₂.comp hle hext_succ ht
  have hE : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      stageOutputList B (extensionScale q.2.1 + q.2.2) q.1.1) := by
    have hcomp : Computable₂ (fun (a b : ℕ) ↦ stageOutputList B a b) :=
      (canonical_enumeration_spec_outputs B).1
    exact Computable₂.comp hcomp hext_d ht
  have h_pred : Computable₂ (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) (z : BitString) ↦
      z == pairCode q.1.2.1 (decodeSecond z)) := by
    have hz : Computable (fun p : ((ℕ × BitString × BitString) × (ℕ × ℕ)) × BitString ↦
        p.2) := Computable.snd
    have h1 : Computable (fun p : ((ℕ × BitString × BitString) × (ℕ × ℕ)) × BitString ↦
        p.1) := Computable.fst
    have hy_comp : Computable (fun p : ((ℕ × BitString × BitString) × (ℕ × ℕ)) × BitString ↦
        p.1.1.2.1) := hy.comp h1
    have hpair : Computable (fun p : ((ℕ × BitString × BitString) × (ℕ × ℕ)) × BitString ↦
        pairCode p.1.1.2.1 (decodeSecond p.2)) :=
      Computable₂.comp pairCode_computable hy_comp (decodeSecond_computable.comp hz)
    have heq : Computable (fun p : ((ℕ × BitString × BitString) × (ℕ × ℕ)) × BitString ↦
        decide (p.2 = pairCode p.1.1.2.1 (decodeSecond p.2))) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp hz hpair
    exact heq.of_eq (by intro p; simp [beq_eq_decide])
  have h_filter : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      (stageOutputList B (extensionScale q.2.1 + q.2.2) q.1.1).filter
        (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))) := by
    exact Kolmogorov.computable_list_filter hE h_pred
  have ha_t : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      ((stageOutputList B (extensionScale q.2.1 + q.2.2) q.1.1).filter
        (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))).length) := by
    exact Computable.list_length.comp h_filter
  have hsub : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      q.1.1 - (extensionScale q.2.1 + q.2.2 + 1)) := by
    have hsub_fn : Computable₂ (fun (a b : ℕ) ↦ a - b) := Primrec.nat_sub.to_comp
    exact Computable₂.comp hsub_fn ht hext_succ
  have hpow : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      2 ^ (q.1.1 - (extensionScale q.2.1 + q.2.2 + 1))) := by
    have hpow_fn : Computable₂ (fun (a b : ℕ) ↦ a ^ b) :=
      (Primrec.nat_iff.mpr Nat.Primrec.pow).to_comp
    exact Computable₂.comp hpow_fn (Computable.const 2) hsub
  have hmul : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      ((stageOutputList B (extensionScale q.2.1 + q.2.2) q.1.1).filter
        (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))).length *
      2 ^ (q.1.1 - (extensionScale q.2.1 + q.2.2 + 1))) := by
    have hmul_fn : Computable₂ (fun (a b : ℕ) ↦ a * b) := Primrec.nat_mul.to_comp
    exact Computable₂.comp hmul_fn ha_t hpow
  have hg : Computable (fun (q : (ℕ × BitString × BitString) × (ℕ × ℕ)) ↦
      bif decide (extensionScale q.2.1 + q.2.2 + 1 ≤ q.1.1) then
        ((stageOutputList B (extensionScale q.2.1 + q.2.2) q.1.1).filter
          (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))).length *
            2 ^ (q.1.1 - (extensionScale q.2.1 + q.2.2 + 1)) else 0) :=
    @Computable.cond _ _ _ _ _ _ _ hcond hmul (Computable.const 0)
  have hg_comp : Computable₂ (fun (p : ℕ × BitString × BitString) (hd : ℕ × ℕ) ↦
      bif decide (extensionScale hd.1 + hd.2 + 1 ≤ p.1) then
        ((stageOutputList B (extensionScale hd.1 + hd.2) p.1).filter
          (fun z ↦ z == pairCode p.2.1 (decodeSecond z))).length *
            2 ^ (p.1 - (extensionScale hd.1 + hd.2 + 1)) else 0) := hg
  have H : Computable (fun p : ℕ × BitString × BitString ↦
      (decodeExtensionCondition p.2.2).casesOn (motive := fun _ ↦ ℕ) 0 (fun hd ↦
        bif decide (extensionScale hd.1 + hd.2 + 1 ≤ p.1) then
          ((stageOutputList B (extensionScale hd.1 + hd.2) p.1).filter
            (fun z ↦ z == pairCode p.2.1 (decodeSecond z))).length *
              2 ^ (p.1 - (extensionScale hd.1 + hd.2 + 1)) else 0)) :=
    Computable.option_casesOn ho hf hg_comp
  refine H.of_eq (fun p ↦ ?_)
  cases h_opt : decodeExtensionCondition p.2.2 with
  | none => simp only [relaxedExtensionApprox, h_opt]
  | some hd =>
    obtain ⟨h, δ⟩ := hd
    simp only [relaxedExtensionApprox, h_opt, Bool.cond_decide]
    rw [card_filter_stageOutputs_eq_length]

/-- Relaxed extension counts define a lower semicomputable conditional semimeasure. -/
private lemma exists_relaxed_extension_semimeasure (B : Base) :
    ∃ f : BitString → BitString → ENNReal, IsLSC f ∧
      (∀ b, (∑' a : BitString, f a b) ≤ 1) ∧
      ∀ (h δ : ℕ) (y : BitString),
        f y (pairCode (bits h) (bits δ)) =
          ((extensionCount B h δ y : ENNReal) /
            (2 : ENNReal) ^ (extensionScale h + δ + 1)) := by
  use relaxedExtensionMass B
  refine ⟨⟨relaxedExtensionApprox B,
          relaxedExtensionApprox_le_succ B,
          iSup_relaxedExtensionApprox B,
          computable_relaxedExtensionApprox B⟩,
          tsum_relaxedExtensionMass_le_one B,
          relaxedExtensionMass_pairCode B⟩

/-- Coding and conditional composition bound the count in terms of the relaxation complexity. -/
private lemma relaxed_extension_upper_bound_of_coding
    (B : Base) (cKC cComp : ℕ) :
    ∃ cUpper : ℕ, ∀ (h δ : ℕ) (y : BitString) (k : ℕ),
      KP B.D y (bits h) = (k : ENat) →
      (2 : ENNReal)⁻¹ ^ cKC *
        ((extensionCount B h δ y : ENNReal) /
          (2 : ENNReal) ^ (extensionScale h + δ + 1)) ≤
        complexityWeight (KP B.D y (pairCode (bits h) (bits δ))) →
      KP B.D y (bits h) ≤
        KP B.D y (pairCode (bits h) (bits δ)) +
          KPPlain B.D (bits δ) + (cComp : ENat) →
      (extensionCount B h δ y : ℚ) ≤
        (2 : ℚ) ^ ((extensionScale h : ℤ) - k + δ +
          (KP B.D (bits δ) (bits 0)).toNat + cUpper) := by
  obtain ⟨c1, hc1⟩ := KPPlain_le_KPPlain_add_KP B.D B.optimalD
  obtain ⟨m0, hm0⟩ := prefix_complexity_finite_value B (bits 0) []
  use cKC + 1 + cComp + m0 + c1
  intro h δ y k hk Hkc Hcomp
  obtain ⟨n, hn⟩ := prefix_complexity_finite_value B (bits δ) (bits 0)
  obtain ⟨m, hm⟩ := prefix_complexity_finite_value B y (pairCode (bits h) (bits δ))
  have hn_nat : (KP B.D (bits δ) (bits 0)).toNat = n := by
    rw [hn, ENat.toNat_natCast]
  rw [hn_nat]
  have Hc1 := hc1 (bits δ) (bits 0)
  rw [hn] at Hc1
  have Hc1' : KPPlain B.D (bits δ) ≤ (m0 + n + c1 : ENat) := by
    calc KPPlain B.D (bits δ)
      _ ≤ KPPlain B.D (bits 0) + (n : ENat) + c1 := Hc1
      _ ≤ (m0 : ENat) + n + c1 := by
        gcongr
        have h_plain : KPPlain B.D (bits 0) = KP B.D (bits 0) [] := KPPlain_eq_KP B.D (bits 0)
        rw [h_plain, hm0]
  have Hcomp' : (k : ENat) ≤ (m + (m0 + n + c1) + cComp : ENat) := by
    rw [← hk]
    calc KP B.D y (bits h)
      _ ≤ KP B.D y (pairCode (bits h) (bits δ)) + KPPlain B.D (bits δ) + cComp := Hcomp
      _ = (m : ENat) + KPPlain B.D (bits δ) + cComp := by rw [hm]
      _ ≤ (m : ENat) + (m0 + n + c1 : ENat) + cComp := by gcongr
      _ = (m + (m0 + n + c1) + cComp : ENat) := by rfl
  have Hcomp'' : k ≤ m + (m0 + n + c1) + cComp := by
    exact ENat.natCast_le_natCast.mp Hcomp'
  have Hkc' : (1 / 2 : ℝ) ^ cKC *
      ((extensionCount B h δ y : ℝ) / (2 : ℝ) ^ (extensionScale h + δ + 1)) ≤ (1 / 2 : ℝ) ^ m := by
    have h1 : (complexityWeight (KP B.D y (pairCode (bits h) (bits δ)))).toReal =
        ((1 / 2 : ℝ) ^ m) := by
      rw [hm, complexityWeight_coe, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      norm_num
    have h2 : ((2 : ENNReal)⁻¹ ^ cKC * ((extensionCount B h δ y : ENNReal) /
        (2 : ENNReal) ^ (extensionScale h + δ + 1))).toReal =
        (1 / 2 : ℝ) ^ cKC *
          ((extensionCount B h δ y : ℝ) / (2 : ℝ) ^ (extensionScale h + δ + 1)) := by
      have h_two_pow : ((2 : ENNReal) ^ (extensionScale h + δ + 1)).toReal =
          (2 : ℝ) ^ (extensionScale h + δ + 1) := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      have h_inv : ((2 : ENNReal)⁻¹ ^ cKC).toReal = (1 / 2 : ℝ) ^ cKC := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
        norm_num
      rw [ENNReal.toReal_mul, h_inv, ENNReal.toReal_div, h_two_pow]
      rfl
    have h3 := ENNReal.toReal_mono (by simp [hm]) Hkc
    rwa [h1, h2] at h3
  have Hkc'' : (extensionCount B h δ y : ℝ) * (2 : ℝ) ^ m ≤
      (2 : ℝ) ^ cKC * (2 : ℝ) ^ (extensionScale h + δ + 1) := by
    have hdiv : (extensionCount B h δ y : ℝ) /
        ((2 : ℝ) ^ cKC * 2 ^ (extensionScale h + δ + 1)) ≤ 1 / (2 : ℝ) ^ m := by
      simpa only [one_div, inv_pow, div_eq_mul_inv, mul_inv, one_mul, mul_assoc,
        mul_left_comm, mul_comm] using Hkc'
    have hcross := (div_le_div_iff₀ (by positivity) (by positivity)).mp hdiv
    simpa only [one_mul] using hcross
  have Hkc''' : extensionCount B h δ y * 2 ^ m ≤ 2 ^ cKC * 2 ^ (extensionScale h + δ + 1) := by
    exact_mod_cast Hkc''
  have H_final : extensionCount B h δ y * 2 ^ k ≤
      2 ^ (extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1)) := by
    calc extensionCount B h δ y * 2 ^ k
      _ ≤ extensionCount B h δ y * 2 ^ (m + m0 + n + c1 + cComp) := by
        gcongr
        omega
      _ = extensionCount B h δ y * 2 ^ m * 2 ^ (m0 + n + c1 + cComp) := by
        rw [pow_add]
        ring
      _ ≤ 2 ^ cKC * 2 ^ (extensionScale h + δ + 1) * 2 ^ (m0 + n + c1 + cComp) := by
        gcongr
      _ = 2 ^ (extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have H_final_Q : (extensionCount B h δ y : ℚ) * (2 : ℚ) ^ k ≤
      (2 : ℚ) ^ (extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1)) := by
    exact_mod_cast H_final
  have H_final_Q2 : (extensionCount B h δ y : ℚ) ≤
      (2 : ℚ) ^ (extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1)) / (2 : ℚ) ^ k := by
    rwa [le_div_iff₀ (by positivity)]
  have H_final_Q3 : (extensionCount B h δ y : ℚ) ≤
      (2 : ℚ) ^ ((extensionScale h : ℤ) - k + δ + n + (cKC + 1 + cComp + m0 + c1)) := by
    calc (extensionCount B h δ y : ℚ)
      _ ≤ (2 : ℚ) ^ (extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1)) / (2 : ℚ) ^ k :=
          H_final_Q2
      _ = (2 : ℚ) ^ ((extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1) : ℤ)) /
          (2 : ℚ) ^ (k : ℤ) := rfl
      _ = (2 : ℚ) ^ ((extensionScale h + δ + n + (cKC + 1 + cComp + m0 + c1) : ℤ) - k) := by
        rw [← zpow_sub₀ (by norm_num)]
      _ = (2 : ℚ) ^ ((extensionScale h : ℤ) - k + δ + n + (cKC + 1 + cComp + m0 + c1)) := by
        congr 1
        ring
  exact H_final_Q3

/-- The relaxed extension count has a uniform upper bound including the relaxation code cost. -/
private theorem exists_relaxed_extension_upper_bound (B : Base) :
    ∃ cUpper : ℕ, ∀ (h δ : ℕ) (y : BitString) (k : ℕ),
      KP B.D y (bits h) = (k : ENat) →
      (extensionCount B h δ y : ℚ) ≤
        (2 : ℚ) ^ ((extensionScale h : ℤ) - k + δ +
        (KP B.D (bits δ) (bits 0)).toNat + cUpper) := by
  obtain ⟨f, hf_lsc, hf_mass, hf_eq⟩ := exists_relaxed_extension_semimeasure B
  obtain ⟨cKC, hcKC⟩ := conditional_coding_interface_uniform B f hf_lsc hf_mass
  obtain ⟨cComp, hComp⟩ := conditional_prefix_composition_remove B
  obtain ⟨cUpper, hcUpper⟩ := relaxed_extension_upper_bound_of_coding B cKC cComp
  use cUpper
  intro h δ y k hk
  have h_kc :
      (2 : ENNReal)⁻¹ ^ cKC *
        ((extensionCount B h δ y : ENNReal) /
          (2 : ENNReal) ^ (extensionScale h + δ + 1)) ≤
        complexityWeight (KP B.D y (pairCode (bits h) (bits δ))) := by
    simpa only [hf_eq h δ y] using hcKC y (pairCode (bits h) (bits δ))
  exact hcUpper h δ y k hk h_kc (hComp y (bits h) (bits δ))

/-- The relaxation and its conditional code cost are bounded linearly in its size. -/
private theorem exists_linear_relaxation_code_bound (B : Base) :
    ∃ cCode : ℕ, ∀ δ : ℕ,
      (δ : ℤ) + (KP B.D (bits δ) (bits 0)).toNat ≤ (cCode : ℤ) * (δ + 1) := by
  use B.cD + 8
  intro δ
  have h_lit := B.literal_bound (bits δ) (bits 0)
  have h_len : (bits δ).length ≤ δ + 1 := length_bits_le δ
  have h_log : Nat.clog 2 ((bits δ).length + 2) ≤ (bits δ).length + 2 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    apply le_of_lt
    apply Nat.lt_two_pow_self
  have h_bound : (KP B.D (bits δ) (bits 0)).toNat ≤
      (bits δ).length + 2 * Nat.clog 2 ((bits δ).length + 2) + B.cD := by
    apply ENat.toNat_le_of_le_natCast
    exact h_lit
  have h_bound2 : (KP B.D (bits δ) (bits 0)).toNat ≤ (δ + 1) + 2 * ((δ + 1) + 2) + B.cD := by
    omega
  have hsum : (δ : ℤ) + (KP B.D (bits δ) (bits 0)).toNat ≤
      (δ : ℤ) + ((δ + 1) + 2 * ((δ + 1) + 2) + B.cD : ℤ) := by
    omega
  have hlinear : (δ : ℤ) + ((δ + 1) + 2 * ((δ + 1) + 2) + B.cD : ℤ) ≤
      ((B.cD + 8 : ℕ) : ℤ) * (δ + 1) := by
    have h_eq : ((B.cD + 8 : ℕ) : ℤ) * (δ + 1) = (B.cD : ℤ) * (δ + 1) + 8 * (δ + 1) := by
      push_cast
      ring
    rw [h_eq]
    have hcd_pos : (0 : ℤ) ≤ B.cD := by omega
    have hdelta_pos : (0 : ℤ) ≤ δ := by omega
    have hcd_mul : (B.cD : ℤ) ≤ (B.cD : ℤ) * (δ + 1) := by
      calc
        (B.cD : ℤ) = (B.cD : ℤ) * 1 := by ring
        _ ≤ (B.cD : ℤ) * (δ + 1) := by nlinarith
    linarith
  omega

/-- Relaxing the description budget costs at most a fixed multiple of `δ + 1` in the exponent.
Blueprint node `key:density`. The information gap is retained, including for `δ = 0`. -/
theorem extension_density_relaxed (B : Base) :
    ∃ c₀ cRel : ℕ, ∀ (h : ℕ) (y : BitString),
      KP B.D y (bits h) + c₀ ≤ (extensionScale h : ENat) →
      ∀ δ : ℕ, (extensionCount B h δ y : ℚ) ≤
        (2 : ℚ) ^ ((cRel : ℤ) * (δ + 1)) * strictExtensionCount B h y := by
  obtain ⟨cUpper, hUpper⟩ := exists_relaxed_extension_upper_bound B
  obtain ⟨c₀, cDen, hLower⟩ := exists_strict_extension_lower_bound B
  obtain ⟨cCode, hCode⟩ := exists_linear_relaxation_code_bound B
  use c₀, cUpper + cDen + cCode
  intro h y hy δ
  have hk_exists := prefix_complexity_finite_value B y (bits h)
  obtain ⟨k, hk⟩ := hk_exists
  have hy_k : (k : ENat) + c₀ ≤ (extensionScale h : ENat) := by
    rw [← hk]
    exact hy
  have hk_le : k + c₀ ≤ extensionScale h := by
    have h_eq : (k : ENat) + c₀ = (k + c₀ : ENat) := rfl
    rw [h_eq] at hy_k
    exact ENat.natCast_le_natCast.mp hy_k
  have h_u := hUpper h δ y k hk
  have h_l := hLower h y k hk hk_le
  have h_c := hCode δ
  calc
    (extensionCount B h δ y : ℚ)
      ≤ (2 : ℚ) ^ ((extensionScale h : ℤ) - k + δ +
          (KP B.D (bits δ) (bits 0)).toNat + cUpper) := h_u
    _ = (2 : ℚ) ^ (δ + (KP B.D (bits δ) (bits 0)).toNat + (cUpper + cDen : ℤ)) *
          (2 : ℚ) ^ ((extensionScale h : ℤ) - k - cDen) := by
      rw [← zpow_add₀ (by norm_num)]
      congr 1
      omega
    _ ≤ (2 : ℚ) ^ ((cCode : ℤ) * (δ + 1) + (cUpper + cDen : ℤ)) *
          (2 : ℚ) ^ ((extensionScale h : ℤ) - k - cDen) := by
      have h2 : 2 ^ (↑δ + ↑(KP B.D (bits δ) (bits 0)).toNat + (↑cUpper + ↑cDen)) ≤
        (2 : ℚ) ^ (↑cCode * (↑δ + 1) + (↑cUpper + ↑cDen)) := by
        have one_le_two : (1 : ℚ) ≤ 2 := by norm_num
        have : (δ : ℤ) + (KP B.D (bits δ) (bits 0)).toNat + (cUpper + cDen : ℤ) ≤
            (cCode : ℤ) * (δ + 1) + (cUpper + cDen : ℤ) := by omega
        exact zpow_le_zpow_right₀ one_le_two this
      apply mul_le_mul_of_nonneg_right h2
      apply zpow_nonneg (by norm_num)
    _ ≤ (2 : ℚ) ^ ((cCode : ℤ) * (δ + 1) + (cUpper + cDen : ℤ)) *
          (strictExtensionCount B h y : ℚ) := by
      apply mul_le_mul_of_nonneg_left h_l
      apply zpow_nonneg (by norm_num)
    _ ≤ (2 : ℚ) ^ (((cUpper + cDen + cCode : ℕ) : ℤ) * (δ + 1)) *
          strictExtensionCount B h y := by
      have h1 : (2 : ℚ) ^ ((cCode : ℤ) * (δ + 1) + (cUpper + cDen : ℤ)) ≤
          (2 : ℚ) ^ (((cUpper + cDen + cCode : ℕ) : ℤ) * (δ + 1)) := by
        have one_le_two : (1 : ℚ) ≤ 2 := by norm_num
        have : (cCode : ℤ) * (δ + 1) + (cUpper + cDen : ℤ) ≤
            (((cUpper + cDen + cCode : ℕ) : ℤ) * (δ + 1)) := by
          push_cast
          nlinarith
        exact zpow_le_zpow_right₀ one_le_two this
      apply mul_le_mul_of_nonneg_right h1
      exact_mod_cast Nat.zero_le _

/-- One information-gap constant and two loss constants work for all density assertions.
Blueprint node `key:density`. No constant depends on a scale, object, or relaxation. -/
theorem extension_density_common (B : Base) :
    ∃ c₀ cDen cRel : ℕ, ExtensionDensityBounds B c₀ cDen cRel := by
  obtain ⟨c₀₁, cDen, h1⟩ := extension_density B
  obtain ⟨c₀₂, cRel, h2⟩ := extension_density_relaxed B
  use max c₀₁ c₀₂, cDen, cRel
  intro h y k hk hgap
  have hgap1 : k + c₀₁ ≤ extensionScale h := by
    calc k + c₀₁ ≤ k + max c₀₁ c₀₂ := Nat.add_le_add_left (le_max_left _ _) _
    _ ≤ extensionScale h := hgap
  have hgap2 : KP B.D y (bits h) + c₀₂ ≤ (extensionScale h : ENat) := by
    rw [hk]
    have : k + c₀₂ ≤ extensionScale h := by
      calc k + c₀₂ ≤ k + max c₀₁ c₀₂ := Nat.add_le_add_left (le_max_right _ _) _
      _ ≤ extensionScale h := hgap
    exact ENat.natCast_le_natCast.mpr this
  obtain ⟨h1a, h1b⟩ := h1 h y k hk hgap1
  exact ⟨h1a, h1b, h2 h y hgap2⟩

/-- A partial computable map carries extensions into a relaxed extension set
with a fixed additive description overhead. -/
private lemma extensionSet_subset_of_partrec (B : Base)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ cF : ℕ, ∀ (h : ℕ) (z y : BitString), y ∈ f z →
      extensionSet B h 0 z ⊆ extensionSet B h cF y := by
  set g : BitString →. BitString := fun w ↦
      (f (decodeFirst w)).map (fun y' ↦ pairCode y' (decodeSecond w))
  have hg : Partrec g := by
    have h1 : Partrec (fun w ↦ f (decodeFirst w)) := hf.comp decodeFirst_computable
    have h3 : Computable (fun (p : BitString × BitString) ↦ decodeSecond p.1) :=
      decodeSecond_computable.comp Computable.fst
    have hsecond : Computable (fun p : BitString × BitString ↦ p.2) := Computable.snd
    have h5 : Computable₂ (fun w y' ↦ pairCode y' (decodeSecond w)) :=
      Computable₂.comp pairCode_computable hsecond h3
    exact Partrec.map h1 h5
  obtain ⟨cF, hcF⟩ := plainK_partrec_map_le B.V B.optimalV g hg
  use cF
  intro h z y hy s hs
  rw [extensionSet, Set.mem_ofPred_eq] at hs ⊢
  dsimp [Simple] at hs ⊢
  have hmem : pairCode y s ∈ g (pairCode z s) := by
    rw [Part.mem_map_iff]
    use y
    refine ⟨?_, ?_⟩
    · simpa only [decodeFirst_pairCode] using hy
    · simp only [decodeSecond_pairCode]
  change plainK B.V (pairCode y s) ≤ ((extensionScale h + cF : ℕ) : ENat)
  have hc := hcF _ _ hmem
  calc
    plainK B.V (pairCode y s) ≤ plainK B.V (pairCode z s) + cF := hc
    _ ≤ ((extensionScale h + 0 : ℕ) : ENat) + cF := add_le_add hs le_rfl
    _ = ((extensionScale h + cF : ℕ) : ENat) := by push_cast; ring

/-- A fixed partial computable map loses only a constant factor in extension volume.
Blueprint node `key:projection`. The density constants are fixed before the map;
the gap is required only for its output, and domain membership is expressed by `y ∈ f z`. -/
theorem extension_volume_of_computable_projection (B : Base) {c₀ cDen cRel : ℕ}
    (hd : ExtensionDensityBounds B c₀ cDen cRel)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ cF : ℕ, ∀ (h : ℕ) (z y : BitString), y ∈ f z →
      KP B.D y (bits h) + c₀ ≤ (extensionScale h : ENat) →
      (strictExtensionCount B h z : ℚ) ≤
        (2 : ℚ) ^ (cF : ℤ) * strictExtensionCount B h y := by
  obtain ⟨cF, hcF⟩ := extensionSet_subset_of_partrec B f hf
  use cRel * (cF + 1)
  intro h z y hy hgap
  have h_subset := hcF h z y hy
  have h_ncard_le := Set.ncard_le_ncard h_subset (extension_set_finite B h cF y)
  have h_count_le : (strictExtensionCount B h z : ℚ) ≤ (extensionCount B h cF y : ℚ) := by
    calc (strictExtensionCount B h z : ℚ) = ((extensionSet B h 0 z).ncard : ℚ) := rfl
    _ ≤ ((extensionSet B h cF y).ncard : ℚ) := Nat.cast_le.mpr h_ncard_le
    _ = (extensionCount B h cF y : ℚ) := rfl
  obtain ⟨k, hk⟩ := prefix_complexity_finite_value B y (bits h)
  have hgap' : k + c₀ ≤ extensionScale h := by
    rw [hk] at hgap
    exact ENat.natCast_le_natCast.mp hgap
  have h_density := (hd h y k hk hgap').2.2 cF
  exact h_count_le.trans h_density

end Kolmogorov.Milovanov
