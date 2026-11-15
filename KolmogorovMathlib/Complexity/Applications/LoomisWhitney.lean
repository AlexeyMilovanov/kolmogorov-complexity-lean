/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

/-!
# A proof of an inequality (SUV Section 8.6, pp. 255-258)

Theorem 164 is the functional form of the Loomis-Whitney inequality for three variables.  The book
gives three proofs: through the triple inequality for prefix complexity (`two_mul_KP_triple_le`,
Problem 114), through Shannon entropy (`two_mul_entropy_triple_le`), and a direct one through the
Cauchy-Schwarz inequality.  The last needs nothing else, and is the one formalised here, so
Theorem 164 has a complete proof.

The set version of Problem 252 is `sq_card_le_card_mul_card_mul_card`, also proved.  The library's
integer-point version is the discrete Loomis-Whitney inequality of
`Entropy/Inequalities/Subtuples.lean`.  The continuous version is `sq_volume_le_volume_projections`,
left as a proof obligation.
-/

namespace Kolmogorov.Applications

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Finset-indexed form of `sq_sum_mul_mul_le`. -/
private lemma sq_sum_mul_mul_le_finset (s : Finset X) (t : Finset Y) (u : Finset Z)
    (f : X → Y → ℝ) (g : Y → Z → ℝ) (h : X → Z → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y * g y z * h x z) ^ 2 ≤
      (∑ x ∈ s, ∑ y ∈ t, f x y ^ 2) * (∑ y ∈ t, ∑ z ∈ u, g y z ^ 2) *
        (∑ x ∈ s, ∑ z ∈ u, h x z ^ 2) := by
  have hrewrite : (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y * g y z * h x z) =
      ∑ p ∈ s ×ˢ t, f p.1 p.2 * ∑ z ∈ u, g p.2 z * h p.1 z := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hF : (∑ x ∈ s, ∑ y ∈ t, f x y ^ 2) = ∑ p ∈ s ×ˢ t, f p.1 p.2 ^ 2 := by
    rw [Finset.sum_product]
  have hinner : ∀ p : X × Y, (∑ z ∈ u, g p.2 z * h p.1 z) ^ 2 ≤
      (∑ z ∈ u, g p.2 z ^ 2) * ∑ z ∈ u, h p.1 z ^ 2 := fun p =>
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : (∑ p ∈ s ×ˢ t, (∑ z ∈ u, g p.2 z * h p.1 z) ^ 2) ≤
      (∑ y ∈ t, ∑ z ∈ u, g y z ^ 2) * ∑ x ∈ s, ∑ z ∈ u, h x z ^ 2 := by
    calc (∑ p ∈ s ×ˢ t, (∑ z ∈ u, g p.2 z * h p.1 z) ^ 2)
        ≤ ∑ p ∈ s ×ˢ t, (∑ z ∈ u, g p.2 z ^ 2) * ∑ z ∈ u, h p.1 z ^ 2 :=
          Finset.sum_le_sum fun p _ => hinner p
      _ = (∑ y ∈ t, ∑ z ∈ u, g y z ^ 2) * ∑ x ∈ s, ∑ z ∈ u, h x z ^ 2 := by
          rw [Finset.sum_product_right, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
  have hnonneg : 0 ≤ ∑ x ∈ s, ∑ y ∈ t, f x y ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  calc (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y * g y z * h x z) ^ 2
      = (∑ p ∈ s ×ˢ t, f p.1 p.2 * ∑ z ∈ u, g p.2 z * h p.1 z) ^ 2 := by rw [hrewrite]
    _ ≤ (∑ p ∈ s ×ˢ t, f p.1 p.2 ^ 2) * ∑ p ∈ s ×ˢ t, (∑ z ∈ u, g p.2 z * h p.1 z) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ x ∈ s, ∑ y ∈ t, f x y ^ 2) * ∑ p ∈ s ×ˢ t, (∑ z ∈ u, g p.2 z * h p.1 z) ^ 2 := by
        rw [hF]
    _ ≤ (∑ x ∈ s, ∑ y ∈ t, f x y ^ 2) *
          ((∑ y ∈ t, ∑ z ∈ u, g y z ^ 2) * ∑ x ∈ s, ∑ z ∈ u, h x z ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hnonneg
    _ = _ := by ring

/-- **SUV Theorem 164, p. 256.**  For non-negative `f`, `g`, `h` on `X × Y`, `Y × Z`, `X × Z`,

`(∑ f(x,y) g(y,z) h(x,z))² ≤ (∑ f(x,y)²) (∑ g(y,z)²) (∑ h(x,z)²)`.

The proof is the Cauchy-Schwarz computation of p. 257, applied first in `(x, y)` and then, for each
`(x, y)`, in `z`.  The sign hypotheses are those of the book; the inequality does not need them. -/
theorem sq_sum_mul_mul_le (f : X → Y → ℝ) (g : Y → Z → ℝ) (h : X → Z → ℝ)
    (_hf : ∀ x y, 0 ≤ f x y) (_hg : ∀ y z, 0 ≤ g y z) (_hh : ∀ x z, 0 ≤ h x z) :
    (∑ x, ∑ y, ∑ z, f x y * g y z * h x z) ^ 2 ≤
      (∑ x, ∑ y, f x y ^ 2) * (∑ y, ∑ z, g y z ^ 2) * (∑ x, ∑ z, h x z ^ 2) :=
  sq_sum_mul_mul_le_finset univ univ univ f g h

/-- The squared characteristic function of a finite set sums to its cardinality. -/
private lemma sum_indicator_sq {α : Type*} [DecidableEq α] (P S : Finset α) (hS : S ⊆ P) :
    (∑ a ∈ P, (if a ∈ S then (1 : ℝ) else 0) ^ 2) = S.card := by
  have h : ∀ a : α, (if a ∈ S then (1 : ℝ) else 0) ^ 2 = if a ∈ S then 1 else 0 := fun a => by
    split_ifs <;> norm_num
  simp only [h, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- **SUV Problem 252, p. 257, discrete case.**  A finite subset of a product `X × Y × Z` satisfies
`|V|² ≤ |π_{xy} V| |π_{yz} V| |π_{xz} V|`, by Theorem 164 applied to the characteristic functions
of the projections. -/
theorem sq_card_le_card_mul_card_mul_card [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (V : Finset (X × Y × Z)) :
    V.card ^ 2 ≤ (V.image fun p => (p.1, p.2.1)).card * (V.image fun p => p.2).card *
      (V.image fun p => (p.1, p.2.2)).card := by
  set A := V.image fun p => (p.1, p.2.1) with hA
  set B := V.image fun p => p.2 with hB
  set C := V.image fun p => (p.1, p.2.2) with hC
  set S := V.image fun p => p.1 with hS
  set T := V.image fun p => p.2.1 with hT
  set U := V.image fun p => p.2.2 with hU
  let f : X → Y → ℝ := fun x y => if (x, y) ∈ A then 1 else 0
  let g : Y → Z → ℝ := fun y z => if (y, z) ∈ B then 1 else 0
  let h : X → Z → ℝ := fun x z => if (x, z) ∈ C then 1 else 0
  have hmain := sq_sum_mul_mul_le_finset S T U f g h
  have hAsub : A ⊆ S ×ˢ T := fun q hq => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hBsub : B ⊆ T ×ˢ U := fun q hq => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hCsub : C ⊆ S ×ˢ U := fun q hq => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hFsum : (∑ x ∈ S, ∑ y ∈ T, f x y ^ 2) = A.card := by
    rw [← sum_indicator_sq (S ×ˢ T) A hAsub, Finset.sum_product]
  have hGsum : (∑ y ∈ T, ∑ z ∈ U, g y z ^ 2) = B.card := by
    rw [← sum_indicator_sq (T ×ˢ U) B hBsub, Finset.sum_product]
  have hHsum : (∑ x ∈ S, ∑ z ∈ U, h x z ^ 2) = C.card := by
    rw [← sum_indicator_sq (S ×ˢ U) C hCsub, Finset.sum_product]
  have hlower : (V.card : ℝ) ≤ ∑ x ∈ S, ∑ y ∈ T, ∑ z ∈ U, f x y * g y z * h x z := by
    have hsumV : (V.card : ℝ) = ∑ p ∈ V, (1 : ℝ) := by simp
    rw [hsumV]
    have hall : (∑ x ∈ S, ∑ y ∈ T, ∑ z ∈ U, f x y * g y z * h x z) =
        ∑ p ∈ S ×ˢ T ×ˢ U, f p.1 p.2.1 * g p.2.1 p.2.2 * h p.1 p.2.2 := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_product]
    rw [hall]
    have hle : ∀ p ∈ V, (1 : ℝ) = f p.1 p.2.1 * g p.2.1 p.2.2 * h p.1 p.2.2 := by
      intro p hp
      have h1 : (p.1, p.2.1) ∈ A := Finset.mem_image_of_mem _ hp
      have h2 : (p.2.1, p.2.2) ∈ B := Finset.mem_image_of_mem (fun p => p.2) hp
      have h3 : (p.1, p.2.2) ∈ C := Finset.mem_image_of_mem _ hp
      simp [f, g, h, h1, h2, h3]
    rw [Finset.sum_congr rfl hle]
    have hVsub : V ⊆ S ×ˢ T ×ˢ U := fun p hp =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩⟩
    refine Finset.sum_le_sum_of_subset_of_nonneg hVsub fun p _ _ => ?_
    simp only [f, g, h]
    split_ifs <;> norm_num
  have hcardnn : (0 : ℝ) ≤ V.card := Nat.cast_nonneg _
  have hsq : (V.card : ℝ) ^ 2 ≤ (A.card : ℝ) * B.card * C.card := by
    calc (V.card : ℝ) ^ 2 ≤ (∑ x ∈ S, ∑ y ∈ T, ∑ z ∈ U, f x y * g y z * h x z) ^ 2 :=
          pow_le_pow_left₀ hcardnn hlower 2
      _ ≤ _ := hmain
      _ = _ := by rw [hFsum, hGsum, hHsum]
  exact_mod_cast hsq

/-- The squared Cauchy-Schwarz inequality for nonnegative extended real-valued functions. -/
private lemma sq_volume_le_volume_projections_integral_cauchy_schwarz
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (u v : α → ENNReal)
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    (∫⁻ a, u a * v a ∂μ) ^ 2 ≤ (∫⁻ a, u a ^ 2 ∂μ) * (∫⁻ a, v a ^ 2 ∂μ) := by
  have h := pow_le_pow_left'
    (ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu hv) 2
  simpa [mul_pow, ← ENNReal.rpow_mul_natCast] using h

/-- Step 1 of the proof of `sq_volume_le_volume_projections`: the continuous analogue
of `sq_sum_mul_mul_le` for integrals, proven for non-negative extended real-valued functions.
This corresponds to the book's hint to "approximate the integral by finite sums." -/
private lemma sq_volume_le_volume_projections_integral
    (f : ℝ × ℝ → ENNReal) (g : ℝ × ℝ → ENNReal) (h : ℝ × ℝ → ENNReal)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ p : ℝ × ℝ × ℝ, f (p.1, p.2.1) * g p.2 * h (p.1, p.2.2)) ^ 2 ≤
    (∫⁻ p : ℝ × ℝ, (f p)^2) * (∫⁻ p : ℝ × ℝ, (g p)^2) * (∫⁻ p : ℝ × ℝ, (h p)^2) := by
  let I : ℝ × ℝ → ENNReal := fun p => ∫⁻ z : ℝ, g (p.2, z) * h (p.1, z)
  let G : ℝ → ENNReal := fun y => ∫⁻ z : ℝ, g (y, z) ^ 2
  let H : ℝ → ENNReal := fun x => ∫⁻ z : ℝ, h (x, z) ^ 2
  have hI : Measurable I :=
    Measurable.lintegral_prod_right' (ν := MeasureTheory.volume)
      (f := fun q : (ℝ × ℝ) × ℝ => g (q.1.2, q.2) * h (q.1.1, q.2)) (by fun_prop)
  have hG : Measurable G :=
    Measurable.lintegral_prod_right' (ν := MeasureTheory.volume)
      (f := fun q : ℝ × ℝ => g q ^ 2) (by fun_prop)
  have hH : Measurable H :=
    Measurable.lintegral_prod_right' (ν := MeasureTheory.volume)
      (f := fun q : ℝ × ℝ => h q ^ 2) (by fun_prop)
  have hrewrite : (∫⁻ p : ℝ × ℝ × ℝ,
      f (p.1, p.2.1) * g p.2 * h (p.1, p.2.2)) =
      ∫⁻ p : ℝ × ℝ, f p * I p := by
    calc
      _ = ∫⁻ x : ℝ, ∫⁻ p : ℝ × ℝ, f (x, p.1) * g p * h (x, p.2) :=
        MeasureTheory.lintegral_prod _ (by fun_prop)
      _ = ∫⁻ x : ℝ, ∫⁻ y : ℝ, f (x, y) * I (x, y) := by
        apply MeasureTheory.lintegral_congr
        intro x
        rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
          MeasureTheory.lintegral_prod _ (by fun_prop)]
        apply MeasureTheory.lintegral_congr
        intro y
        simpa only [I, mul_assoc] using MeasureTheory.lintegral_const_mul (f (x, y))
          (show Measurable (fun z : ℝ => g (y, z) * h (x, z)) by fun_prop)
      _ = _ := (MeasureTheory.lintegral_prod _ (hf.mul hI).aemeasurable).symm
  have hinner (p : ℝ × ℝ) : I p ^ 2 ≤ G p.2 * H p.1 :=
    sq_volume_le_volume_projections_integral_cauchy_schwarz MeasureTheory.volume
      (fun z : ℝ => g (p.2, z)) (fun z : ℝ => h (p.1, z))
      (by fun_prop) (by fun_prop)
  have hbound : (∫⁻ p : ℝ × ℝ, I p ^ 2) ≤
      (∫⁻ p : ℝ × ℝ, g p ^ 2) * (∫⁻ p : ℝ × ℝ, h p ^ 2) := by
    calc
      _ ≤ ∫⁻ p : ℝ × ℝ, G p.2 * H p.1 := MeasureTheory.lintegral_mono hinner
      _ = (∫⁻ x : ℝ, H x) * (∫⁻ y : ℝ, G y) := by
        rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        simpa only [mul_comm] using
          MeasureTheory.lintegral_prod_mul hH.aemeasurable hG.aemeasurable
      _ = (∫⁻ p : ℝ × ℝ, h p ^ 2) * (∫⁻ p : ℝ × ℝ, g p ^ 2) := by
        rw [show (∫⁻ x : ℝ, H x) = ∫⁻ p : ℝ × ℝ, h p ^ 2 from
          (MeasureTheory.lintegral_prod _ (hh.pow_const 2).aemeasurable).symm,
          show (∫⁻ y : ℝ, G y) = ∫⁻ p : ℝ × ℝ, g p ^ 2 from
          (MeasureTheory.lintegral_prod _ (hg.pow_const 2).aemeasurable).symm]
      _ = _ := mul_comm _ _
  calc
    _ = (∫⁻ p : ℝ × ℝ, f p * I p) ^ 2 := by rw [hrewrite]
    _ ≤ (∫⁻ p : ℝ × ℝ, f p ^ 2) * (∫⁻ p : ℝ × ℝ, I p ^ 2) :=
      sq_volume_le_volume_projections_integral_cauchy_schwarz MeasureTheory.volume f I
        hf.aemeasurable hI.aemeasurable
    _ ≤ (∫⁻ p : ℝ × ℝ, f p ^ 2) *
        ((∫⁻ p : ℝ × ℝ, g p ^ 2) * (∫⁻ p : ℝ × ℝ, h p ^ 2)) :=
      mul_le_mul' le_rfl hbound
    _ = _ := (mul_assoc _ _ _).symm

/-- **SUV Problem 252, p. 257, continuous case.**  The bound for the volume of a three-dimensional
body in terms of its two-dimensional projections, for a compact body, so that the projections are
measurable.  The book's hint is to approximate by a cubic grid. -/
theorem sq_volume_le_volume_projections {V : Set (ℝ × ℝ × ℝ)} (hV : IsCompact V) :
    MeasureTheory.volume V ^ 2 ≤
      MeasureTheory.volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) *
        MeasureTheory.volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) *
          MeasureTheory.volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) := by
  have hm1 : MeasurableSet ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) :=
    (hV.image (by fun_prop)).isClosed.measurableSet
  have hm2 : MeasurableSet ((fun p : ℝ × ℝ × ℝ => p.2) '' V) :=
    (hV.image (by fun_prop)).isClosed.measurableSet
  have hm3 : MeasurableSet ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) :=
    (hV.image (by fun_prop)).isClosed.measurableSet
  have h_ind_le : V.indicator (1 : ℝ × ℝ × ℝ → ENNReal) ≤ fun p =>
      ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V).indicator (1 : ℝ × ℝ → ENNReal) (p.1, p.2.1) *
      ((fun p : ℝ × ℝ × ℝ => p.2) '' V).indicator (1 : ℝ × ℝ → ENNReal) p.2 *
      ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V).indicator (1 : ℝ × ℝ → ENNReal) (p.1, p.2.2) := by
    intro p
    by_cases hp : p ∈ V
    · have h1 : (p.1, p.2.1) ∈ (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V := Set.mem_image_of_mem _ hp
      have h2 : p.2 ∈ (fun p : ℝ × ℝ × ℝ => p.2) '' V := Set.mem_image_of_mem _ hp
      have h3 : (p.1, p.2.2) ∈ (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V := Set.mem_image_of_mem _ hp
      simp [Set.indicator, hp, h1, h2, h3]
    · simp [Set.indicator, hp]
  have h_mono := MeasureTheory.lintegral_mono (μ := MeasureTheory.volume) h_ind_le
  have h_sq : (∫⁻ p : ℝ × ℝ × ℝ, V.indicator (1 : ℝ × ℝ × ℝ → ENNReal) p) ^ 2 ≤
    (∫⁻ p : ℝ × ℝ × ℝ, ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V).indicator (1 : ℝ × ℝ → ENNReal)
        (p.1, p.2.1) *
      ((fun p : ℝ × ℝ × ℝ => p.2) '' V).indicator (1 : ℝ × ℝ → ENNReal) p.2 *
      ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V).indicator (1 : ℝ × ℝ → ENNReal) (p.1, p.2.2)) ^ 2
          :=
    pow_le_pow_left' h_mono 2
  have hf_meas : Measurable (((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V).indicator (1 : ℝ × ℝ →
      ENNReal)) :=
    Measurable.indicator measurable_const hm1
  have hg_meas : Measurable (((fun p : ℝ × ℝ × ℝ => p.2) '' V).indicator (1 : ℝ × ℝ → ENNReal)) :=
    Measurable.indicator measurable_const hm2
  have hh_meas : Measurable (((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V).indicator (1 : ℝ × ℝ →
      ENNReal)) :=
    Measurable.indicator measurable_const hm3
  have h_int := sq_volume_le_volume_projections_integral
    (((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V).indicator (1 : ℝ × ℝ → ENNReal))
    (((fun p : ℝ × ℝ × ℝ => p.2) '' V).indicator (1 : ℝ × ℝ → ENNReal))
    (((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V).indicator (1 : ℝ × ℝ → ENNReal))
    hf_meas hg_meas hh_meas
  have h_le := le_trans h_sq h_int
  have hind1 : (fun p => (((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V).indicator
    (1 : ℝ × ℝ → ENNReal) p) ^ 2) = ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V).indicator
    (1 : ℝ × ℝ → ENNReal) := by
    ext p; by_cases h : p ∈ ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) <;> simp [Set.indicator, h]
  have hind2 : (fun p => (((fun p : ℝ × ℝ × ℝ => p.2) '' V).indicator
    (1 : ℝ × ℝ → ENNReal) p) ^ 2) = ((fun p : ℝ × ℝ × ℝ => p.2) '' V).indicator
    (1 : ℝ × ℝ → ENNReal) := by
    ext p; by_cases h : p ∈ ((fun p : ℝ × ℝ × ℝ => p.2) '' V) <;> simp [Set.indicator, h]
  have hind3 : (fun p => (((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V).indicator
    (1 : ℝ × ℝ → ENNReal) p) ^ 2) = ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V).indicator
    (1 : ℝ × ℝ → ENNReal) := by
    ext p; by_cases h : p ∈ ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) <;> simp [Set.indicator, h]
  rw [MeasureTheory.lintegral_indicator hV.isClosed.measurableSet] at h_le
  rw [hind1, hind2, hind3] at h_le
  rw [MeasureTheory.lintegral_indicator hm1, MeasureTheory.lintegral_indicator hm2] at h_le
  rw [MeasureTheory.lintegral_indicator hm3] at h_le
  dsimp only [Pi.one_apply] at h_le
  simpa using h_le

end Kolmogorov.Applications
