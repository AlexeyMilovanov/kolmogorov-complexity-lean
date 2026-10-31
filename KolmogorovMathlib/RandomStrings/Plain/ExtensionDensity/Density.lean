/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.ExtensionDensity.Bounds

/-!
# Strict extension density

For blueprint node `key:density`, this module proves the two dyadic bounds for the strict
extension count under an explicit information gap. The lower bound compiles the crossing decoder
from `ExtensionDensity.Bounds`; the upper bound applies conditional coding to the lower
semicomputable mass obtained by normalizing extension counts. The relaxed density argument uses
these strict bounds as its reference count.
-/

namespace Kolmogorov.Milovanov
open scoped ENNReal

private lemma exists_two_mul_clog_add_le (c_lit cf : ℕ) :
    ∃ c : ℕ, 2 * Nat.clog 2 (c + 2) + c_lit + cf ≤ c := by
  use 2 ^ (c_lit + cf + 4)
  set C := c_lit + cf
  have h2 : Nat.clog 2 (2 ^ (C + 4) + 2) ≤ C + 5 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    have h_pow1 : 2 ^ (C + 4) + 2 ≤ 2 ^ (C + 4) + 2 ^ (C + 4) := by
      apply Nat.add_le_add_left
      calc 2 ≤ 2 ^ 4 := by decide
           _ ≤ 2 ^ (C + 4) := Nat.pow_le_pow_right (by decide) (by omega)
    calc 2 ^ (C + 4) + 2 ≤ 2 ^ (C + 4) + 2 ^ (C + 4) := h_pow1
         _ = 2 * 2 ^ (C + 4) := by ring
         _ = 2 ^ (C + 4 + 1) := by
           have : 2 ^ (C + 4 + 1) = 2 ^ (C + 4) * 2 := rfl
           rw [this]
           ring
  have h3 : 2 * (C + 5) + C ≤ 2 ^ (C + 4) := by
    induction C with
    | zero => decide
    | succ C ih =>
      calc 2 * (C + 1 + 5) + (C + 1) = 2 * (C + 5) + C + 3 := by omega
           _ ≤ 2 ^ (C + 4) + 3 := Nat.add_le_add_right ih 3
           _ ≤ 2 ^ (C + 4) + 2 ^ (C + 4) := by
             apply Nat.add_le_add_left
             calc 3 ≤ 16 := by decide
                  _ = 2 ^ 4 := by decide
                  _ ≤ 2 ^ (C + 4) := Nat.pow_le_pow_right (by decide) (by omega)
           _ = 2 ^ (C + 1 + 4) := by
             have h_eq1 : C + 1 + 4 = C + 4 + 1 := by omega
             have h_eq2 : 2 ^ (C + 4 + 1) = 2 ^ (C + 4) * 2 := rfl
             rw [h_eq1, h_eq2]
             ring
  calc 2 * Nat.clog 2 (2 ^ (C + 4) + 2) + c_lit + cf
    _ = 2 * Nat.clog 2 (2 ^ (C + 4) + 2) + C := by omega
    _ ≤ 2 * (C + 5) + C := Nat.add_le_add_right (Nat.mul_le_mul_left 2 h2) C
    _ ≤ 2 ^ (C + 4) := h3

/-- A parameter can pay for its own prefix description and a fixed compiler overhead. -/
private lemma exists_prefix_complexity_add_le (B : Base) (cf : ℕ) :
    ∃ c : ℕ, KPPlain B.D (bits c) + cf ≤ (c : ENat) := by
  obtain ⟨c_lit, hc_lit⟩ := literal_and_tuple_code_interface_integer B
  obtain ⟨c, hc⟩ := exists_two_mul_clog_add_le c_lit cf
  use c
  have h_bound := hc_lit c
  have h1 : KPPlain B.D (bits c) + cf ≤ (integerLiteralBound c_lit c : ENat) + cf :=
      add_le_add h_bound (le_refl _)
  have h2 : (integerLiteralBound c_lit c : ENat) + cf =
      ((integerLiteralBound c_lit c + cf : ℕ) : ENat) := by
    exact (ENat.natCast_add (integerLiteralBound c_lit c) cf).symm
  have h3 : integerLiteralBound c_lit c + cf = 2 * Nat.clog 2 (c + 2) + c_lit + cf := by
    rfl
  calc KPPlain B.D (bits c) + cf
    _ ≤ (integerLiteralBound c_lit c : ENat) + cf := h1
    _ = ((2 * Nat.clog 2 (c + 2) + c_lit + cf : ℕ) : ENat) := by rw [h2, h3]
    _ ≤ (c : ENat) := ENat.natCast_le_natCast.mpr hc

/-- Short descriptions of dyadic crossings give distinct extensions within the scale budget. -/
private lemma crossing_count_le_strictExtensionCount (B : Base)
    (f : BitString × BitString →. BitString) (c cf : ℕ)
    (hc : ∀ h : ℕ, c ≤ extensionScale h → ∃ inj : BitString × ℕ → BitString,
        (∀ p ∈ dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c),
          (inj p).length = extensionScale h - c ∧ pairCode p.1 (bits p.2) ∈ f (bits c, inj p)))
    (h_cf : ∀ a r z : BitString, z ∈ f (a, r) →
      plainK B.V z ≤ KPPlain B.D a + (r.length : ENat) + cf)
    (h_c : KPPlain B.D (bits c) + cf ≤ (c : ENat)) :
    ∀ (h : ℕ) (y : BitString) (j : ℕ), c ≤ extensionScale h →
      1 ≤ j →
      ((j : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c))) < aprioriMeasure B.D y (bits h) →
      j ≤ strictExtensionCount B h y := by
  intro h y j hc_le hj1 h_j
  obtain ⟨inj, h_inj⟩ := hc h hc_le
  let S := Finset.Icc 1 j
  have hS_card : S.card = j := by
    rw [Nat.card_Icc]
    omega
  let S' := S.image (fun i ↦ bits i)
  have hS'_card : S'.card = j := by
    rw [Finset.card_image_of_injective S bits_injective]
    exact hS_card
  have h_subset : (S' : Set BitString) ⊆ extensionSet B h 0 y := by
    intro s hs
    simp only [S', S, Finset.mem_coe, Finset.mem_image, Finset.mem_Icc] at hs
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hs
    have h_cross : (y, i) ∈ dyadicCrossings (scaleAprioriMass B h) (extensionScale h - c) := by
      simp only [dyadicCrossings, Set.mem_ofPred_eq]
      refine ⟨hi1, ?_⟩
      calc ((i : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c)))
        _ ≤ ((j : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c))) := by
          gcongr
        _ < aprioriMeasure B.D y (bits h) := h_j
    have h_inj_prop := h_inj (y, i) h_cross
    have h_len := h_inj_prop.1
    have h_in := h_inj_prop.2
    have h_plain := h_cf (bits c) (inj (y, i)) (pairCode y (bits i)) h_in
    rw [h_len] at h_plain
    have h_plain2 : plainK B.V (pairCode y (bits i)) ≤ extensionScale h := by
      calc plainK B.V (pairCode y (bits i))
        _ ≤ KPPlain B.D (bits c) + ((extensionScale h - c : ℕ) : ENat) + cf := h_plain
        _ = KPPlain B.D (bits c) + cf + ((extensionScale h - c : ℕ) : ENat) := by
          rw [add_right_comm]
        _ ≤ (c : ENat) + ((extensionScale h - c : ℕ) : ENat) := by
          gcongr
        _ = (c + (extensionScale h - c) : ℕ) := by
          rw [← ENat.natCast_add]
        _ = (extensionScale h : ENat) := by
          congr 1
          omega
    exact h_plain2
  have h_subset_card : S'.card ≤ (extensionSet B h 0 y).ncard := by
    have h1 : (S' : Set BitString).ncard ≤ (extensionSet B h 0 y).ncard := by
      apply Set.ncard_le_ncard h_subset (extension_set_finite B h 0 y)
    have h2 : (S' : Set BitString).ncard = S'.card := by
      exact (Set.ncard_eq_toFinset_card (S' :
          Set BitString) (Finset.finite_toSet S')).trans (by simp)
    rwa [h2] at h1
  have h_fin : strictExtensionCount B h y = (extensionSet B h 0 y).ncard := rfl
  rwa [hS'_card, ← h_fin] at h_subset_card

/-- A dyadic mass lower bound yields a lower bound on the number of strict crossings. -/
private lemma dyadic_lower_bound_of_crossing_count
    (c cCode : ℕ) (h k : ℕ) (m : ℝ≥0∞)
    (h_m : (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) ≤ m)
    (h_k : k + (c + cCode + 1) ≤ extensionScale h)
    (A : ℕ)
    (h_A : ∀ j : ℕ, 1 ≤ j → ((j : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c))) < m → j ≤ A) :
    (2 : ℚ) ^ ((extensionScale h : ℤ) - k - (c + cCode + 1 : ℤ)) ≤ A := by
  have d_eq : (extensionScale h : ℤ) - k - (c + cCode + 1 : ℤ) =
      (extensionScale h - k - (c + cCode + 1) : ℕ) := by omega
  set d := extensionScale h - k - (c + cCode + 1)
  have hd : (extensionScale h : ℤ) - k - (c + cCode + 1 : ℤ) = d := d_eq
  rw [hd]
  have hz : (2 : ℚ) ^ (d : ℤ) = (2 ^ d : ℕ) := by simp
  rw [hz]
  norm_cast
  set j := 2 ^ d
  have hj1 : 1 ≤ j := Nat.one_le_two_pow
  have hj2 : ((j : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c))) < m := by
    calc
      ((j : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c))) =
          (2 : ℝ≥0∞) ^ d * ((2 : ℝ≥0∞)⁻¹ ^ (extensionScale h - c)) := by
        have h_j_cast : (j : ℝ≥0∞) = (2 : ℝ≥0∞) ^ d := by exact_mod_cast rfl
        rw [h_j_cast]
      _ = (2 : ℝ≥0∞) ^ d * ((2 : ℝ≥0∞)⁻¹ ^ d * (2 : ℝ≥0∞)⁻¹ ^ (k + cCode + 1)) := by
        have h_add : extensionScale h - c = d + (k + cCode + 1) := by omega
        rw [h_add, pow_add]
      _ = ((2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d) * (2 : ℝ≥0∞)⁻¹ ^ (k + cCode + 1) := by
        rw [mul_assoc]
      _ = 1 * (2 : ℝ≥0∞)⁻¹ ^ (k + cCode + 1) := by
        have h_inv : (2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d = 1 := by
          rw [← mul_pow]
          have h_mul_inv : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          rw [h_mul_inv, one_pow]
        rw [h_inv]
      _ = (2 : ℝ≥0∞)⁻¹ ^ (k + cCode + 1) := by
        rw [one_mul]
      _ = (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) * (2 : ℝ≥0∞)⁻¹ := by
        have h_add : k + cCode + 1 = (k + cCode) + 1 := by omega
        rw [h_add, pow_add, pow_one]
      _ < (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) := by
        have h1 : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.mpr (by norm_num)
        have h3 : (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) ≠ 0 := by apply ENNReal.pow_ne_zero; norm_num
        have h4 : (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) ≠ ∞ := by apply ENNReal.pow_ne_top; norm_num
        have h_mul_1 : (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) = (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) * 1 :=
          (mul_one _).symm
        nth_rw 2 [h_mul_1]
        exact ENNReal.mul_lt_mul_right h3 h4 h1
      _ ≤ m := h_m
  exact h_A j hj1 hj2

/-- Under an information gap, the strict extension count has a uniform dyadic lower bound. -/
theorem exists_strict_extension_lower_bound (B : Base) :
    ∃ c₀ cDen : ℕ, ∀ (h : ℕ) (y : BitString) (k : ℕ),
      KP B.D y (bits h) = (k : ENat) → k + c₀ ≤ extensionScale h →
      (2 : ℚ) ^ ((extensionScale h : ℤ) - k - cDen) ≤ strictExtensionCount B h y := by
  obtain ⟨f, hf, hdec⟩ := exists_dyadic_crossing_decoder B
  obtain ⟨cf, hcf⟩ := plain_prefix_program_raw_suffix B f hf
  obtain ⟨c, hc⟩ := exists_prefix_complexity_add_le B cf
  obtain ⟨cCode, hcCode⟩ := conditional_coding_interface B
  use c + cCode + 1, c + cCode + 1
  intro h y k hk hgap
  have h_m : (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) ≤ aprioriMeasure B.D y (bits h) := by
    have h1 := (hcCode y (bits h)).1
    have h2 : KP B.D y (bits h) + cCode = ((k + cCode : ℕ) : ENat) := by
      rw [hk]
      have : (k : ENat) + cCode = ((k + cCode : ℕ) : ENat) := ENat.natCast_add k cCode
      exact this
    have h3 : complexityWeight (KP B.D y (bits h) + cCode) = (2 : ℝ≥0∞)⁻¹ ^ (k + cCode) := by
      rw [h2]
      rfl
    rwa [h3] at h1
  have hgap_eq : k + (c + cCode + 1) ≤ extensionScale h := by omega
  have h_glue := crossing_count_le_strictExtensionCount B f c cf (hdec c) hcf hc
  have h_arith := dyadic_lower_bound_of_crossing_count c cCode h k
    (aprioriMeasure B.D y (bits h)) h_m hgap_eq (strictExtensionCount B h y)
  apply h_arith
  intro j hj1 hj2
  have hc_le : c ≤ extensionScale h := by omega
  exact h_glue h y j hc_le hj1 hj2

private noncomputable def strictExtensionMass (B : Base) (y b : BitString) : ℝ≥0∞ :=
  match Milovanov.decodeNat b with
  | some h => (strictExtensionCount B h y : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + 1)
  | none => 0

/-- The sum of all strict extension counts is bounded by the number of short plain programs. -/
private lemma tsum_strictExtensionCount_le (B : Base) (h : ℕ) :
    (∑' y : BitString, (strictExtensionCount B h y : ℝ≥0∞)) ≤ (2 :
        ℝ≥0∞) ^ (extensionScale h + 1) := by
  let S := {z : BitString | Simple B.V z (extensionScale h)}
  have hS_fin_lt := simple_finite_card_lt B.V (extensionScale h)
  have hS_fin : S.Finite := hS_fin_lt.1
  have hS_lt : S.ncard < 2 ^ (extensionScale h + 1) := hS_fin_lt.2
  have hS_card : hS_fin.toFinset.card < 2 ^ (extensionScale h + 1) := by
    rw [← Set.ncard_eq_toFinset_card S hS_fin]
    exact hS_lt
  let T (y : BitString) := (extension_set_finite B h 0 y).toFinset.image (fun s ↦ pairCode y s)
  have hT_subset : ∀ y, (T y : Set BitString) ⊆ S := by
    intro y z hz
    simp only [T, Finset.mem_coe, Finset.mem_image, Set.Finite.mem_toFinset, extensionSet] at hz
    obtain ⟨s, hs, hz_eq⟩ := hz
    rw [← hz_eq]
    exact hs
  have hT_card : ∀ y, (T y).card = strictExtensionCount B h y := by
    intro y
    rw [Finset.card_image_of_injective]
    · exact (Set.ncard_eq_toFinset_card (extensionSet B h 0 y) (extension_set_finite B h 0 y)).symm
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
  have h_sum : ∑ y ∈ F, (strictExtensionCount B h y : ℝ≥0∞) = (∑ y ∈ F, (T y).card : ℕ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [hT_card y]
  have h_union : ∑ y ∈ F, (T y).card = (F.biUnion T).card := by
    rw [Finset.card_biUnion]
    intro y1 hy1 y2 hy2 hneq
    exact hT_disj y1 y2 hneq
  have h_subset_S : F.biUnion T ⊆ hS_fin.toFinset := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨y, _, hy_z⟩ := hz
    rw [Set.Finite.mem_toFinset]
    exact hT_subset y hy_z
  have h_card_le : (F.biUnion T).card ≤ hS_fin.toFinset.card := by
    exact Finset.card_le_card h_subset_S
  have h_fin_lt : (F.biUnion T).card < 2 ^ (extensionScale h + 1) := by
    calc (F.biUnion T).card ≤ hS_fin.toFinset.card := h_card_le
      _ < 2 ^ (extensionScale h + 1) := hS_card
  rw [h_sum, h_union]
  have h_fin_le : ((F.biUnion T).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (extensionScale h + 1) := by
    exact_mod_cast le_of_lt h_fin_lt
  exact h_fin_le

/-- Normalized strict extension counts form a conditional semimeasure. -/
private theorem tsum_strictExtensionMass_le_one (B : Base) (b : BitString) :
    (∑' y : BitString, strictExtensionMass B y b) ≤ 1 := by
  dsimp [strictExtensionMass]
  cases h_eq : Milovanov.decodeNat b
  · simp
  · rename_i h
    have h1 := tsum_strictExtensionCount_le B h
    have h2 : (∑' (y : BitString), (strictExtensionCount B h y : ℝ≥0∞) * (2 :
        ℝ≥0∞)⁻¹ ^ (extensionScale h + 1)) =
        (∑' (y : BitString), (strictExtensionCount B h y : ℝ≥0∞)) * (2 :
            ℝ≥0∞)⁻¹ ^ (extensionScale h + 1) := by
      exact ENNReal.tsum_mul_right
    rw [h2]
    have h3 : (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + 1) = ((2 : ℝ≥0∞) ^ (extensionScale h + 1))⁻¹ := by
      exact ENNReal.inv_pow.symm
    rw [h3]
    have h4 : (∑' (y : BitString), (strictExtensionCount B h y : ℝ≥0∞)) * ((2 :
        ℝ≥0∞) ^ (extensionScale h + 1))⁻¹
        ≤ ((2 : ℝ≥0∞) ^ (extensionScale h + 1)) * ((2 : ℝ≥0∞) ^ (extensionScale h + 1))⁻¹ := by
      apply mul_le_mul h1 (le_refl _) zero_le zero_le
    apply le_trans h4
    have h5 : ((2 : ℝ≥0∞) ^ (extensionScale h + 1)) * ((2 :
        ℝ≥0∞) ^ (extensionScale h + 1))⁻¹ = 1 := by
      apply ENNReal.mul_inv_cancel
      · exact ENNReal.pow_ne_zero (by simp) _
      · exact ENNReal.pow_ne_top (by simp)
    rw [h5]

private def strictExtensionApprox
    (B : Base) (t : ℕ) (y b : BitString) : ℕ :=
  match Milovanov.decodeNat b with
  | some h =>
    if extensionScale h + 1 ≤ t then
      let E_nt := stageOutputs B (extensionScale h) t
      let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
      a_t * 2 ^ (t - (extensionScale h + 1))
    else 0
  | none => 0

/-- Filtering the duplicate-free stage output list computes the corresponding finite-set count. -/
lemma card_filter_stageOutputs_eq_length
    (B : Base) (k t : ℕ) (y : BitString) :
    ((stageOutputs B k t).filter
      (fun z ↦ z == pairCode y (decodeSecond z))).card =
    ((stageOutputList B k t).filter
      (fun z ↦ z == pairCode y (decodeSecond z))).length := by
  unfold stageOutputs
  rw [← List.toFinset_filter]
  apply List.toFinset_card_of_nodup
  exact (Kolmogorov.nodup_eraseDups_list _).filter _

/-- The integer numerators of the normalized extension-count approximation are computable. -/
private lemma computable_strictExtensionApprox (B : Base) :
    Computable (fun p : ℕ × BitString × BitString ↦
      strictExtensionApprox B p.1 p.2.1 p.2.2) := by
  have hp_t : Computable (fun (p : ℕ × BitString × BitString) ↦ p.1) := Computable.fst
  have hp_y : Computable (fun (p : ℕ × BitString × BitString) ↦ p.2.1) :=
      Computable.fst.comp Computable.snd
  have hp_b : Computable (fun (p : ℕ × BitString × BitString) ↦ p.2.2) :=
      Computable.snd.comp Computable.snd
  have ho : Computable (fun (p : ℕ × BitString × BitString) ↦ Milovanov.decodeNat p.2.2) :=
      bits_computable.2.comp hp_b
  have hf : Computable (fun (p : ℕ × BitString × BitString) ↦ (0 : ℕ)) := Computable.const 0
  have ht : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦ q.1.1) :=
      hp_t.comp Computable.fst
  have hy : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦ q.1.2.1) :=
      hp_y.comp Computable.fst
  have hh : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦ q.2) := Computable.snd
  have hext : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦ extensionScale q.2) :=
    primrec_two_pow_aux.to_comp.comp hh
  have hext_succ : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      extensionScale q.2 + 1) :=
    Computable.succ.comp hext
  have hcond : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      decide (extensionScale q.2 + 1 ≤ q.1.1)) := by
    have hle : Computable₂ (fun (a b : ℕ) ↦ decide (a ≤ b)) :=
        (PrimrecRel.decide Primrec.nat_le).to_comp
    exact Computable₂.comp hle hext_succ ht
  have hE : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      stageOutputList B (extensionScale q.2) q.1.1) := by
    have hcomp : Computable₂ (fun (a b : ℕ) ↦ stageOutputList B a b) :=
        (canonical_enumeration_spec_outputs B).1
    exact Computable₂.comp hcomp hext ht
  have h_pred : Computable₂ (fun (q : (ℕ × BitString × BitString) × ℕ) (z : BitString) ↦
      z == pairCode q.1.2.1 (decodeSecond z)) := by
    have hz : Computable (fun p : ((ℕ × BitString × BitString) × ℕ) × BitString ↦ p.2) :=
        Computable.snd
    have h1 : Computable (fun p : ((ℕ × BitString × BitString) × ℕ) × BitString ↦ p.1) :=
        Computable.fst
    have hy_comp : Computable (fun p : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
        p.1.1.2.1) := hy.comp h1
    have hpair : Computable (fun p : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
        pairCode p.1.1.2.1 (decodeSecond p.2)) :=
      Computable₂.comp pairCode_computable hy_comp (decodeSecond_computable.comp hz)
    have heq : Computable (fun p : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
        decide (p.2 = pairCode p.1.1.2.1 (decodeSecond p.2))) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp hz hpair
    exact heq.of_eq (by intro p; simp [beq_eq_decide])
  have h_filter : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      (stageOutputList B (extensionScale q.2) q.1.1).filter
        (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))) := by
    exact Kolmogorov.computable_list_filter hE h_pred
  have ha_t : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      ((stageOutputList B (extensionScale q.2) q.1.1).filter
        (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))).length) := by
    exact Computable.list_length.comp h_filter
  have hsub : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      q.1.1 - (extensionScale q.2 + 1)) := by
    have hsub_fn : Computable₂ (fun (a b : ℕ) ↦ a - b) := Primrec.nat_sub.to_comp
    exact Computable₂.comp hsub_fn ht hext_succ
  have hpow : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      2 ^ (q.1.1 - (extensionScale q.2 + 1))) := by
    have hpow_fn : Computable₂ (fun (a b : ℕ) ↦ a ^ b) :=
        (Primrec.nat_iff.mpr Nat.Primrec.pow).to_comp
    exact Computable₂.comp hpow_fn (Computable.const 2) hsub
  have hmul : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      ((stageOutputList B (extensionScale q.2) q.1.1).filter
        (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))).length *
      2 ^ (q.1.1 - (extensionScale q.2 + 1))) := by
    have hmul_fn : Computable₂ (fun (a b : ℕ) ↦ a * b) := Primrec.nat_mul.to_comp
    exact Computable₂.comp hmul_fn ha_t hpow
  have hg : Computable (fun (q : (ℕ × BitString × BitString) × ℕ) ↦
      bif decide (extensionScale q.2 + 1 ≤ q.1.1) then
        ((stageOutputList B (extensionScale q.2) q.1.1).filter
          (fun z ↦ z == pairCode q.1.2.1 (decodeSecond z))).length *
            2 ^ (q.1.1 - (extensionScale q.2 + 1)) else 0) :=
    @Computable.cond _ _ _ _ _ _ _ hcond hmul (Computable.const 0)
  have hg_comp : Computable₂ (fun (p : ℕ × BitString × BitString) (h : ℕ) ↦
      bif decide (extensionScale h + 1 ≤ p.1) then
        ((stageOutputList B (extensionScale h) p.1).filter
          (fun z ↦ z == pairCode p.2.1 (decodeSecond z))).length *
            2 ^ (p.1 - (extensionScale h + 1)) else 0) := hg
  have H : Computable (fun p : ℕ × BitString × BitString ↦
      (Milovanov.decodeNat p.2.2).casesOn (motive := fun _ ↦ ℕ) 0 (fun h ↦
        bif decide (extensionScale h + 1 ≤ p.1) then
          ((stageOutputList B (extensionScale h) p.1).filter
            (fun z ↦ z == pairCode p.2.1 (decodeSecond z))).length *
              2 ^ (p.1 - (extensionScale h + 1)) else 0)) :=
    Computable.option_casesOn ho hf hg_comp
  refine H.of_eq (fun p ↦ ?_)
  cases h_opt : Milovanov.decodeNat p.2.2 with
  | none => simp only [strictExtensionApprox, h_opt]
  | some h =>
    simp only [strictExtensionApprox, h_opt,
      Bool.cond_decide]
    rw [card_filter_stageOutputs_eq_length]

private lemma dyadicValue_strictExtensionApprox
    (B : Base) (t h : ℕ) (out ctx : BitString)
    (hb : Milovanov.decodeNat ctx = some h)
    (ht : extensionScale h + 1 ≤ t) :
    dyadicValue
      (strictExtensionApprox B t out ctx) t =
      (((stageOutputs B (extensionScale h) t).filter
        (fun z ↦ z == pairCode out (decodeSecond z))).card : ℝ≥0∞) *
        (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + 1) := by
  simp only [strictExtensionApprox, hb,
    ite_eq_left ht]
  rw [dyadicValue_natCast_mul_left, dyadicValue_two_pow_sub ht]

/-- The dyadic values of the extension-count approximation increase with the stage. -/
private lemma strictExtensionApprox_le_succ (B : Base) :
    ∀ (s : ℕ) (out ctx : BitString),
      dyadicValue (strictExtensionApprox B s out ctx) s ≤
        dyadicValue (strictExtensionApprox B (s + 1) out ctx) (s + 1) := by
  intro s out ctx
  cases hb : Milovanov.decodeNat ctx with
  | none =>
    simp [strictExtensionApprox,
      hb, dyadicValue_zero]
  | some h =>
    by_cases ht : extensionScale h + 1 ≤ s
    · have ht_succ : extensionScale h + 1 ≤ s + 1 := by omega
      rw [dyadicValue_strictExtensionApprox B s h out ctx hb ht,
          dyadicValue_strictExtensionApprox B (s + 1) h out ctx hb ht_succ]
      have h_card :
        ((stageOutputs B (extensionScale h) s).filter
          (fun z ↦ z == pairCode out (decodeSecond z))).card ≤
        ((stageOutputs B (extensionScale h) (s + 1)).filter
          (fun z ↦ z == pairCode out (decodeSecond z))).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _
          (canonical_enumeration_spec_mono B (extensionScale h)
            (Nat.le_succ s)).1
      have h_cardENN :
        (((stageOutputs B (extensionScale h) s).filter
          (fun z ↦ z == pairCode out (decodeSecond z))).card : ℝ≥0∞) ≤
        (((stageOutputs B (extensionScale h) (s + 1)).filter
          (fun z ↦ z == pairCode out (decodeSecond z))).card : ℝ≥0∞) := by
        exact_mod_cast h_card
      exact mul_le_mul_of_nonneg_right h_cardENN (zero_le)
    · have hleft : strictExtensionApprox B s out ctx = 0 := by
        simp [strictExtensionApprox, hb, ht]
      rw [hleft, dyadicValue_zero]
      exact zero_le

/-- The stage count of extensions is at most the full strict extension count. -/
private lemma stage_extension_count_le (B : Base) (h t :
    ℕ) (y : BitString) :
    let E_nt := stageOutputs B (extensionScale h) t
    let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
    a_t ≤ strictExtensionCount B h y := by
  let E_nt := stageOutputs B (extensionScale h) t
  let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
  let S := (extension_set_finite B h 0 y).toFinset
  have h_image : (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))) ⊆ S.image (fun s ↦
      pairCode y s) := by
    intro z hz
    simp only [E_nt, Finset.mem_filter, beq_iff_eq] at hz
    have hz_stage := hz.1
    have hz_eq := hz.2
    have h_simple : Simple B.V z (extensionScale h) := by
      have h1 := (canonical_enumeration_spec_union B (extensionScale h) z).mpr
      apply h1
      use t
    have h_s : decodeSecond z ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, extensionSet, Set.mem_ofPred_eq, add_zero]
      rw [← hz_eq]
      exact h_simple
    rw [Finset.mem_image]
    use decodeSecond z
    exact ⟨h_s, hz_eq.symm⟩
  have h_card := Finset.card_le_card h_image
  have h_S_card : S.card = strictExtensionCount B h y := by
    unfold strictExtensionCount extensionCount
    exact (Set.ncard_eq_toFinset_card (extensionSet B h 0 y) (extension_set_finite B h 0 y)).symm
  have h_inj : Function.Injective (fun s : BitString ↦ pairCode y s) := by
    intro s1 s2 heq
    have h1 := congrArg decodeSecond heq
    simp only [decodeSecond_pairCode] at h1
    exact h1
  have h_img_card := Finset.card_image_of_injective S h_inj
  dsimp [a_t]
  rw [← h_S_card, ← h_img_card]
  exact h_card

/-- Every extension has appeared by a common finite stage. -/
private lemma stage_extension_count_eventually_eq (B : Base) (h : ℕ) (y :
    BitString) :
    ∃ T, ∀ t, T ≤ t →
      let E_nt := stageOutputs B (extensionScale h) t
      let a_t := (E_nt.filter (fun z ↦ z == pairCode y (decodeSecond z))).card
      a_t = strictExtensionCount B h y := by
  classical
  let S := (extension_set_finite B h 0 y).toFinset
  have hstage : ∀ s : BitString, ∃ n : ℕ,
      s ∈ S → pairCode y s ∈ stageOutputs B (extensionScale h) n := by
    intro s
    by_cases hs : s ∈ S
    · have hsimple : Simple B.V (pairCode y s) (extensionScale h) := by
        simpa only [S, Set.Finite.mem_toFinset, extensionSet,
          Set.mem_ofPred_eq, add_zero] using hs
      obtain ⟨n, hn⟩ :=
        (canonical_enumeration_spec_union B (extensionScale h)
          (pairCode y s)).mp hsimple
      exact ⟨n, fun _ ↦ hn⟩
    · exact ⟨0, fun hs' ↦ (hs hs').elim⟩
  choose f hf using hstage
  refine ⟨S.sup f, ?_⟩
  intro t ht
  change ((stageOutputs B (extensionScale h) t).filter
    (fun z ↦ z == pairCode y (decodeSecond z))).card =
      strictExtensionCount B h y
  have heq : (stageOutputs B (extensionScale h) t).filter
      (fun z ↦ z == pairCode y (decodeSecond z)) =
      S.image (fun s ↦ pairCode y s) := by
    ext z
    simp only [Finset.mem_filter, beq_iff_eq, Finset.mem_image]
    constructor
    · rintro ⟨hz, hz_eq⟩
      refine ⟨decodeSecond z, ?_, hz_eq.symm⟩
      simp only [S, Set.Finite.mem_toFinset, extensionSet,
        Set.mem_ofPred_eq, add_zero]
      rw [← hz_eq]
      exact (canonical_enumeration_spec_union B
        (extensionScale h) z).mpr ⟨t, hz⟩
    · rintro ⟨s, hs, hsz⟩
      subst z
      constructor
      · have hbound : f s ≤ t := (Finset.le_sup hs).trans ht
        exact (canonical_enumeration_spec_mono B
          (extensionScale h) hbound).1 (hf s hs)
      · simp only [decodeSecond_pairCode]
  have hinj : Function.Injective (fun s ↦ pairCode y s) := by
    intro s₁ s₂ he
    simpa only [decodeSecond_pairCode] using congrArg decodeSecond he
  rw [heq, Finset.card_image_of_injective S hinj]
  exact (Set.ncard_eq_toFinset_card (extensionSet B h 0 y)
    (extension_set_finite B h 0 y)).symm

private lemma iSup_strictExtensionApprox (B : Base) :
    ∀ (out ctx : BitString),
      (⨆ s, dyadicValue (strictExtensionApprox B s out ctx) s) =
        strictExtensionMass B out ctx := by
  intro out ctx
  cases h_decode : Milovanov.decodeNat ctx with
  | none =>
      simp [strictExtensionApprox,
        strictExtensionMass, h_decode, dyadicValue_zero]
  | some h =>
      simp only [strictExtensionMass, h_decode]
      let a (t : ℕ) :=
        (stageOutputs B (extensionScale h) t |>.filter
          (fun z ↦ z == pairCode out (decodeSecond z))).card
      have hval (t : ℕ) (ht : extensionScale h + 1 ≤ t) :
          dyadicValue (strictExtensionApprox
            B t out ctx) t =
            (a t : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + 1) := by
        exact dyadicValue_strictExtensionApprox B t h out ctx h_decode ht
      have hzero (t : ℕ) (ht : ¬ (extensionScale h + 1 ≤ t)) :
          dyadicValue (strictExtensionApprox
            B t out ctx) t = 0 := by
        have h_eq : strictExtensionApprox B t out ctx = 0 := by
          unfold strictExtensionApprox
          rw [h_decode]
          dsimp only
          exact ite_eq_right ht
        rw [h_eq]
        exact dyadicValue_zero t
      have hle (t : ℕ) : a t ≤ strictExtensionCount B h out := by
        simpa [a] using
          (stage_extension_count_le
            B h t out)
      obtain ⟨T, hT⟩ :=
        stage_extension_count_eventually_eq B h out
      apply le_antisymm
      · apply iSup_le
        intro t
        by_cases ht : extensionScale h + 1 ≤ t
        · rw [hval t ht]
          gcongr
          exact_mod_cast hle t
        · rw [hzero t ht]
          exact zero_le
      · let t := max T (extensionScale h + 1)
        have ht : extensionScale h + 1 ≤ t := le_max_right _ _
        have hTt : T ≤ t := le_max_left _ _
        refine le_iSup_of_le t ?_
        have hT_eval : a t = strictExtensionCount B h out := by
          simpa [a] using hT t hTt
        rw [hval t ht, hT_eval]

/-- Normalized strict extension counts are lower semicomputable. -/
private theorem isLSC_strictExtensionMass (B : Base) :
    IsLSC (strictExtensionMass B) :=
  ⟨strictExtensionApprox B,
   strictExtensionApprox_le_succ B,
   iSup_strictExtensionApprox B,
   computable_strictExtensionApprox B⟩

/-- A conditional coding bound for normalized counts yields the dyadic upper density bound. -/
private theorem strict_extension_upper_bound_of_coding (B : Base) (c₀ cDen : ℕ)
    (hcDen : 1 ≤ cDen)
    (hc : ∀ y b, (2 : ℝ≥0∞)⁻¹ ^ (cDen - 1) * strictExtensionMass B y b ≤
      complexityWeight (KP B.D y b)) :
    ∀ (h : ℕ) (y : BitString) (k : ℕ),
      KP B.D y (bits h) = (k : ENat) → k + c₀ ≤ extensionScale h →
      (strictExtensionCount B h y : ℚ) ≤
        (2 : ℚ) ^ ((extensionScale h : ℤ) - k + cDen) := by
  intro h y k hk h_c0
  have h1 := hc y (bits h)
  rw [hk] at h1
  simp only [strictExtensionMass, decodeNat_bits, complexityWeight_coe] at h1
  have h_exp : (cDen - 1 : ℕ) + (extensionScale h + 1) = cDen + extensionScale h := by omega
  have h2 : (strictExtensionCount B h y : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (cDen + extensionScale h) ≤
      (2 : ℝ≥0∞)⁻¹ ^ k := by
    calc (strictExtensionCount B h y : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (cDen + extensionScale h)
      = (2 : ℝ≥0∞)⁻¹ ^ (cDen - 1) * ((strictExtensionCount B h y : ℝ≥0∞) *
        (2 : ℝ≥0∞)⁻¹ ^ (extensionScale h + 1)) := by
          rw [← mul_assoc, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ (cDen - 1)), mul_assoc, ← pow_add, h_exp]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ k := h1
  have h3 : (strictExtensionCount B h y : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (cDen + extensionScale h) *
      (2 : ℝ≥0∞) ^ (cDen + extensionScale h) ≤
      (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ (cDen + extensionScale h) := by
    gcongr
  have h_rhs : (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ (cDen + extensionScale h) =
      (2 : ℝ≥0∞) ^ (cDen + extensionScale h - k) := by
    have h_split : cDen + extensionScale h = (cDen + extensionScale h - k) + k := by omega
    nth_rw 1 [h_split]
    rw [pow_add]
    have h_rw : (2 : ℝ≥0∞)⁻¹ ^ k * ((2 : ℝ≥0∞) ^ (cDen + extensionScale h - k) * (2 : ℝ≥0∞) ^ k) =
      (2 : ℝ≥0∞) ^ (cDen + extensionScale h - k) * ((2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k) := by
      calc (2 : ℝ≥0∞)⁻¹ ^ k * ((2 : ℝ≥0∞) ^ (cDen + extensionScale h - k) * (2 : ℝ≥0∞) ^ k)
        = ((2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ (cDen + extensionScale h - k)) * (2 : ℝ≥0∞) ^ k := by
            rw [mul_assoc]
        _ = ((2 : ℝ≥0∞) ^ (cDen + extensionScale h - k) * (2 : ℝ≥0∞)⁻¹ ^ k) * (2 : ℝ≥0∞) ^ k := by
          congr 1
          rw [mul_comm]
        _ = (2 : ℝ≥0∞) ^ (cDen + extensionScale h - k) * ((2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k) := by
            rw [mul_assoc]
    rw [h_rw]
    have h_inv2 : (2 : ℝ≥0∞)⁻¹ ^ k * (2 : ℝ≥0∞) ^ k = 1 := by
      rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (ENNReal.pow_ne_zero (by simp) _)
          (ENNReal.pow_ne_top (by simp))]
    rw [h_inv2, mul_one]
  rw [h_rhs] at h3
  have h_q : (strictExtensionCount B h y : ℚ) ≤ (2 : ℚ) ^ (cDen + extensionScale h - k) := by
    have h_inv : (2 : ℝ≥0∞)⁻¹ ^ (cDen + extensionScale h) * (2 : ℝ≥0∞) ^ (cDen + extensionScale h) =
        1 := by
      rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (ENNReal.pow_ne_zero (by simp) _)
        (ENNReal.pow_ne_top (by simp))]
    have h_lhs : (strictExtensionCount B h y : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (cDen + extensionScale h) *
        (2 : ℝ≥0∞) ^ (cDen + extensionScale h) = (strictExtensionCount B h y : ℝ≥0∞) := by
      rw [mul_assoc, h_inv, mul_one]
    rw [h_lhs] at h3
    exact_mod_cast h3
  calc (strictExtensionCount B h y : ℚ) ≤ (2 : ℚ) ^ (cDen + extensionScale h - k) := h_q
    _ = (2 : ℚ) ^ ((extensionScale h : ℤ) - k + cDen) := by
      have h_pow_eq : ((cDen + extensionScale h - k : ℕ) : ℤ) =
          (extensionScale h : ℤ) - k + cDen := by omega
      have h_eq2 : (2 : ℚ) ^ (cDen + extensionScale h - k) =
          (2 : ℚ) ^ ((cDen + extensionScale h - k : ℕ) : ℤ) := by
        exact (zpow_natCast (2 : ℚ) (cDen + extensionScale h - k)).symm
      rw [h_eq2, h_pow_eq]

/-- The strict extension count has a uniform dyadic upper bound. -/
private theorem exists_strict_extension_upper_bound (B : Base) :
    ∃ c₀ cDen : ℕ, ∀ (h : ℕ) (y : BitString) (k : ℕ),
      KP B.D y (bits h) = (k : ENat) → k + c₀ ≤ extensionScale h →
      (strictExtensionCount B h y : ℚ) ≤
        (2 : ℚ) ^ ((extensionScale h : ℤ) - k + cDen) := by
  obtain ⟨c, hc⟩ := conditional_coding_interface_uniform B (strictExtensionMass B)
    (isLSC_strictExtensionMass B) (tsum_strictExtensionMass_le_one B)
  use 0, c + 1
  apply strict_extension_upper_bound_of_coding B 0 (c + 1) (by omega)
  intro y b
  have h := hc y b
  have : c + 1 - 1 = c := by omega
  rwa [this]

/-- Strict density has two uniform dyadic bounds under the information gap.
Blueprint node `key:density`. The condition encoding is the binary word `bits h`. -/
theorem extension_density (B : Base) :
    ∃ c₀ cDen : ℕ, ∀ (h : ℕ) (y : BitString) (k : ℕ),
      KP B.D y (bits h) = (k : ENat) → k + c₀ ≤ extensionScale h →
      (2 : ℚ) ^ ((extensionScale h : ℤ) - k - cDen) ≤ strictExtensionCount B h y ∧
      (strictExtensionCount B h y : ℚ) ≤
        (2 : ℚ) ^ ((extensionScale h : ℤ) - k + cDen) := by
  obtain ⟨c₀₁, cDen₁, h1⟩ := exists_strict_extension_lower_bound B
  obtain ⟨c₀₂, cDen₂, h2⟩ := exists_strict_extension_upper_bound B
  use max c₀₁ c₀₂, max cDen₁ cDen₂
  intro h y k hk h_c0
  have hc01 : k + c₀₁ ≤ extensionScale h := by omega
  have hc02 : k + c₀₂ ≤ extensionScale h := by omega
  constructor
  · have h_lower := h1 h y k hk hc01
    apply le_trans _ h_lower
    have h_exp : (extensionScale h : ℤ) - k - max cDen₁ cDen₂ ≤
        (extensionScale h : ℤ) - k - cDen₁ := by omega
    apply zpow_le_zpow_right₀ (by norm_num) h_exp
  · have h_upper := h2 h y k hk hc02
    apply le_trans h_upper
    have h_exp : (extensionScale h : ℤ) - k + cDen₂ ≤
        (extensionScale h : ℤ) - k + max cDen₁ cDen₂ := by omega
    apply zpow_le_zpow_right₀ (by norm_num) h_exp

open Kolmogorov

/-- Decode the scale and relaxation allowance from a paired condition. -/
def decodeExtensionCondition (b : BitString) : Option (ℕ × ℕ) :=
  (Milovanov.decodeNat (decodeFirst b)).bind (fun h ↦
    (Milovanov.decodeNat (decodeSecond b)).map (fun d ↦ (h, d)))

end Kolmogorov.Milovanov
