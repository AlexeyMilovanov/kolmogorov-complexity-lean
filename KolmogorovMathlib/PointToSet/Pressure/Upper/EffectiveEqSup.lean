/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Upper.UniformNets

/-!
# Effective upper pressure equals the pointwise supremum

For an admissible oracle `A`, the `A`-effective upper pressure of a set `Z` is the supremum, over
`x ∈ Z`, of the `A`-relative pointwise upper pressure of `x`
(`effectiveUpperPressure_eq_iSup_pointwise`, blueprint node
`pressure:effective-upper-equality`).

The inequality `≥` rests on the coding argument for effective uniform nets.  Fixing a slice of an
`A`-enumerable uniform `s`-net, the exponential rate bound makes the request mass of all indices
from some level on finite (`uniformNet_tail_weight_summable_mass`).  The relativized coding
theorem then turns these requests into the bound
`K^A(i) + S_n φ(ιᵢ) ≤ t n + c` for every index `i` of the net at every large level `n`
(`uniformNet_tail_weight_summable`).  Consequently every point covered by the net has pointwise
upper pressure at most `s` (`pointwiseUpper_le_of_effectiveUniformNet`).

The inequality `≤` uses that the upper threshold set, which collects the indices whose oracle
complexity is below the rational slope line, is itself relatively enumerable
(`upperThreshold_isUniformNet_re`).  This module is used by the point-to-set principle for upper
pressure in `KolmogorovMathlib.PointToSet.Pressure.Upper`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- The right-hand side `s n - S_n φ(ιᵢ) + k` of the upper threshold is lower semicomputable
relative to an admissible oracle. -/
private lemma isLowerSemicomputableIn_threshold_bound
    (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 ↦ D.φ) A) (s : ℚ) :
    IsLowerSemicomputableIn A
      (fun t : ℕ × ℕ × ℕ × ℕ ↦
        (s : ℝ) * t.2.1 - birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1) + t.2.2.2) := by
  have hext : (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦ (tq.2 : ℝ) <
        (s : ℝ) * tq.1.2.1 - birkhoffSum D.T D.φ tq.1.2.1 (D.presentation.ι tq.1.1) +
          tq.1.2.2.2) =
      fun tq ↦ birkhoffSum D.T D.φ tq.1.2.1 (D.presentation.ι tq.1.1) <
        ((s * (tq.1.2.1 : ℚ) + (tq.1.2.2.2 : ℚ) - tq.2 : ℚ) : ℝ) := by
    funext tq
    push_cast
    exact propext ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
  have hn : Computable (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦ (tq.1.2.1 : ℚ)) :=
    computable_nat_to_rat.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hk : Computable (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦ (tq.1.2.2.2 : ℚ)) :=
    computable_nat_to_rat.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hlinear : Computable (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦
      s * (tq.1.2.1 : ℚ) + (tq.1.2.2.2 : ℚ)) :=
    computable₂_ratAdd.comp (computable₂_ratMul.comp (Computable.const s) hn) hk
  have hsub : Computable (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦
      s * (tq.1.2.1 : ℚ) + (tq.1.2.2.2 : ℚ) - tq.2) :=
    computable₂_ratSub.comp hlinear Computable.snd
  have hbirkhoff := birkhoff_computableIn D.presentation D.T (fun _ : Fin 1 ↦ D.φ) A hA
  have hv := IsComputableRealFamilyIn.comp A _ hbirkhoff
    (fun t : ℕ × ℕ × ℕ × ℕ ↦ ((0 : Fin 1), t.2.1, t.1))
    ((Computable.const (0 : Fin 1)).pair ((Computable.fst.comp Computable.snd).pair Computable.fst))
  have hlt := (birkhoff_computableIn_lt A _ hv).comp
    (f := fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦ (tq.1, s * (tq.1.2.1 : ℚ) + (tq.1.2.2.2 : ℚ) - tq.2))
    (Computable.fst.pair hsub).computableIn
  unfold IsLowerSemicomputableIn
  have h : IsREIn A (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦ (tq.2 : ℝ) <
      (s : ℝ) * tq.1.2.1 - birkhoffSum D.T D.φ tq.1.2.1 (D.presentation.ι tq.1.1) +
        tq.1.2.2.2) := by
    rw [hext]
    exact hlt
  exact h

/-- For an admissible oracle, the upper threshold set of an `s`-net, which collects the tuples
`(i, n, p, k)` with `n ≥ 1`, `p ≥ p₀` and `K^A(i) + S_n φ(ιᵢ) < s n + k`, is relatively
enumerable. Blueprint node `pressure:upper-threshold`. -/
theorem upperThreshold_isUniformNet_re (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (s : ℚ) :
    IsREIn A (upperPressureThreshold D.presentation D.T D.φ D.p₀ A s) := by
  have hcut : IsREIn A (fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦
      (oracleNatComplexity A tq.1.1 : ℝ) < (tq.2 : ℝ)) :=
    (isREIn_oracleNatComplexity_lt A).comp
      (f := fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦ (tq.1.1, tq.2))
      ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
  have hrhs := isLowerSemicomputableIn_threshold_bound D A hA s
  have hmin : Computable (fun t : ℕ × ℕ × ℕ × ℕ ↦ decide (1 ≤ t.2.1)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd))).to_comp
  have hp₀ : Computable (fun t : ℕ × ℕ × ℕ × ℕ ↦ decide (D.p₀ ≤ t.2.2.1)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp (Primrec.const D.p₀)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).to_comp
  have hrange := IsREIn.and
    (isREIn_of_computableIn_decide A (fun t : ℕ × ℕ × ℕ × ℕ ↦ 1 ≤ t.2.1) hmin.computableIn)
    (isREIn_of_computableIn_decide A (fun t : ℕ × ℕ × ℕ × ℕ ↦ D.p₀ ≤ t.2.2.1)
      hp₀.computableIn)
  have hall := hrange.and
    (IsREIn.exists (F := fun tq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦
      (oracleNatComplexity A tq.1.1 : ℝ) < (tq.2 : ℝ) ∧ (tq.2 : ℝ) <
        (s : ℝ) * tq.1.2.1 - birkhoffSum D.T D.φ tq.1.2.1 (D.presentation.ι tq.1.1) +
          tq.1.2.2.2) (hcut.and hrhs))
  have hset : upperPressureThreshold D.presentation D.T D.φ D.p₀ A s =
      fun t ↦ (1 ≤ t.2.1 ∧ D.p₀ ≤ t.2.2.1) ∧ ∃ q : ℚ,
        (oracleNatComplexity A t.1 : ℝ) < (q : ℝ) ∧ (q : ℝ) <
          (s : ℝ) * t.2.1 - birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1) + t.2.2.2 := by
    ext t
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨⟨h₁, h₂⟩, exists_rat_btwn h₃⟩
    · rintro ⟨⟨h₁, h₂⟩, q, hq₁, hq₂⟩
      exact ⟨h₁, h₂, hq₁.trans hq₂⟩
  rw [hset]
  exact hall

/-- The exponential bound `q n ≤ 2 ^ (b n)` on a slice mass from a rate bound
`pressureRate q n ≤ b` at a positive order `n`. -/
private lemma le_two_rpow_of_pressureRate_le
    (q : ℕ → ℝ≥0∞) (b : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (h : pressureRate q n ≤ (b : EReal)) : q n ≤ (2 : ℝ≥0∞) ^ (b * n) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hr : ENNReal.log (q n) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) ≤ b := by
    simpa only [pressureRate, ite_eq_right hn0, pressureLog, mul_assoc, ← EReal.coe_mul] using h
  apply ENNReal.log_strictMono.le_iff_le.mp
  calc
    ENNReal.log (q n) =
        (ENNReal.log (q n) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal)) *
          (((n : ℝ) * Real.log 2 : ℝ) : EReal) := by
      rw [mul_assoc, ← EReal.coe_mul]
      have he : (Real.log 2)⁻¹ * (n : ℝ)⁻¹ * ((n : ℝ) * Real.log 2) = 1 := by
        field_simp
      rw [he, EReal.coe_one, mul_one]
    _ ≤ (b : EReal) * (((n : ℝ) * Real.log 2 : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_right hr (EReal.coe_nonneg.mpr
        (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))))
    _ = ENNReal.log ((2 : ℝ≥0∞) ^ (b * n)) := by
      rw [ENNReal.log_rpow]
      have he : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
        simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
      rw [he, ← EReal.coe_mul, ← EReal.coe_mul]
      congr 1
      ring

/-- If the limsup of the exponential rates of `q` is at most `s < t`, then the weighted tail sum
`∑ 2 ^ (-t n) q n` over `n ≥ N₀` is finite for a suitable `N₀ ≥ 1`. -/
private lemma tsum_tail_rpow_mul_lt_top
    (q : ℕ → ℝ≥0∞) (s t : ℝ) (hst : s < t)
    (h : limsup (pressureRate q) atTop ≤ (s : EReal)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      (∑' n : {n : ℕ | N₀ ≤ n}, (2 : ℝ≥0∞) ^ (-t * n.val) * q n.val) < ⊤ := by
  obtain ⟨b, hsb, hbt⟩ := exists_between hst
  have hb : limsup (pressureRate q) atTop < (b : EReal) :=
    h.trans_lt (EReal.coe_lt_coe_iff.mpr hsb)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hb)
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  have hgeom : (∑' n : ℕ, (2 : ℝ≥0∞) ^ (-(t - b) * n)) < ⊤ := by
    have hr : (2 : ℝ≥0∞) ^ (-(t - b)) < 1 := by
      calc
        (2 : ℝ≥0∞) ^ (-(t - b)) < (2 : ℝ≥0∞) ^ (0 : ℝ) :=
          ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) (by linarith)
        _ = 1 := ENNReal.rpow_zero
    simp_rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hr)
  apply lt_of_le_of_lt ?_ hgeom
  calc
    (∑' n : {n : ℕ | max 1 N ≤ n}, (2 : ℝ≥0∞) ^ (-t * n.val) * q n.val) ≤
        ∑' n : {n : ℕ | max 1 N ≤ n}, (2 : ℝ≥0∞) ^ (-(t - b) * n.val) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have he := le_two_rpow_of_pressureRate_le q b n.val
        ((le_max_left _ _).trans n.property)
        (hN n.val ((le_max_right _ _).trans n.property)).le
      calc
        (2 : ℝ≥0∞) ^ (-t * n.val) * q n.val ≤
            (2 : ℝ≥0∞) ^ (-t * n.val) * (2 : ℝ≥0∞) ^ (b * n.val) := by
              simpa only [mul_comm] using mul_le_mul_left he ((2 : ℝ≥0∞) ^ (-t * n.val))
        _ = (2 : ℝ≥0∞) ^ (-(t - b) * n.val) := by
          rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
          congr 1
          ring
    _ ≤ ∑' n : ℕ, (2 : ℝ≥0∞) ^ (-(t - b) * n) :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun n : {n : ℕ | max 1 N ≤ n} => (n : ℕ)) Subtype.val_injective
        (fun n : ℕ => (2 : ℝ≥0∞) ^ (-(t - b) * n))

/-- Injecting the canonical pair codes of a tail of the net into the dependent sum of tail slices
bounds the total request mass `∑ 2 ^ (-g w)` over the codes by the weighted slice mass, provided
the cost `g` of the pair code `(i, n)` is `t n - S_n φ(ιᵢ)`. -/
private lemma tsum_rpow_neg_lt_top_of_coded_mass
    (D : PressureData X) (E : Set (ℕ × ℕ × ℕ × ℕ)) (p k N₀ : ℕ) (t : ℚ)
    (F : BitString → Prop)
    (hF : ∀ w, F w → ∃ i n : ℕ,
      w = pairCode (natBits i) (natBits n) ∧ N₀ ≤ n ∧ (i, n, p, k) ∈ E)
    (g : BitString → ℝ)
    (hg : ∀ i n, g (pairCode (natBits i) (natBits n)) =
      (t : ℝ) * n - birkhoffSum D.T D.φ n (D.presentation.ι i))
    (hmass : (∑' n : {n : ℕ | N₀ ≤ n}, (2 : ℝ≥0∞) ^ (-(t : ℝ) * n.val) *
      uniformPressureSum D.presentation D.T D.φ E n.val p k) < ⊤) :
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) < ⊤ := by
  classical
  choose i n hw hn he using (fun w : Subtype F ↦ hF w.val w.property)
  let f : Subtype F → Σ n : {n : ℕ | N₀ ≤ n}, {i : ℕ | (i, n.val, p, k) ∈ E} :=
    fun w ↦ ⟨⟨n w, hn w⟩, ⟨i w, he w⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hnuv : n u = n v := congrArg (fun z ↦ z.1.val) huv
    have hiuv : i u = i v := congrArg (fun z ↦ z.2.val) huv
    apply Subtype.ext
    rw [hw u, hw v, hnuv, hiuv]
  let a : (Σ n : {n : ℕ | N₀ ≤ n}, {i : ℕ | (i, n.val, p, k) ∈ E}) → ℝ≥0∞ :=
    fun z ↦ (2 : ℝ≥0∞) ^ (-(t : ℝ) * z.1.val +
      birkhoffSum D.T D.φ z.1.val (D.presentation.ι z.2.val))
  have hwa : ∀ w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val) = a (f w) := by
    intro w
    rw [hw w, hg]
    dsimp [a, f]
    congr 1
    ring
  apply lt_of_le_of_lt ?_ hmass
  calc
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) = ∑' w : Subtype F, a (f w) := tsum_congr hwa
    _ ≤ ∑' z, a z := ENNReal.tsum_comp_le_tsum_of_injective hf a
    _ = ∑' n : {n : ℕ | N₀ ≤ n}, (2 : ℝ≥0∞) ^ (-(t : ℝ) * n.val) *
        uniformPressureSum D.presentation D.T D.φ E n.val p k := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro n
      dsimp [a, uniformPressureSum]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      exact ENNReal.rpow_add _ _ (by norm_num) (by norm_num)

/-- Exponential-rate slack gives finite total request mass after discarding an initial
segment; early slices need not have finite mass. Blueprint node `pressure:net-tail`. -/
theorem uniformNet_tail_weight_summable_mass (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ))
    (hE : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E) (hRE : IsREIn A E)
    (t : ℚ) (hst : s < (t : ℝ)) (p : ℕ) (hp : D.p₀ ≤ p) (k : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      (∑' n : {n : ℕ | N₀ ≤ n}, (2 : ℝ≥0∞) ^ (-(t : ℝ) * n.val) *
        uniformPressureSum D.presentation D.T D.φ E n.val p k) < ⊤ := by
  have _ := hA
  have _ := hRE
  exact tsum_tail_rpow_mul_lt_top (fun n ↦ uniformPressureSum D.presentation D.T D.φ E n p k)
    s (t : ℝ) hst (hE.2.1 p hp k)

/-- A fixed effective net slice has a tail coding bound with the constant before both
dynamic variables. The cutoff is existential, without an effective search requirement.
Blueprint node `pressure:net-tail`. -/
theorem uniformNet_tail_weight_summable (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ))
    (hE : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E) (hRE : IsREIn A E)
    (t : ℚ) (hst : s < (t : ℝ)) (p : ℕ) (hp : D.p₀ ≤ p) (k : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ c : ℝ, ∀ n ≥ N₀, ∀ i, (i, n, p, k) ∈ E →
      (oracleNatComplexity A i : ℝ) + birkhoffSum D.T D.φ n (D.presentation.ι i) ≤
        (t : ℝ) * n + c := by
  obtain ⟨N₀, hN₀, hmass⟩ :=
    uniformNet_tail_weight_summable_mass D A hA Z s E hE hRE t hst p hp k
  let F : BitString → Prop := fun w ↦ ∃ i n : ℕ,
    w = pairCode (natBits i) (natBits n) ∧ N₀ ≤ n ∧ (i, n, p, k) ∈ E
  let g : BitString → ℝ := fun w ↦ (t : ℝ) * decodeBits (decodeSecond w) -
    birkhoffSum D.T D.φ (decodeBits (decodeSecond w))
      (D.presentation.ι (decodeBits (decodeFirst w)))
  have hF : IsREIn A F := isREIn_pairCode_tail A hRE p k N₀
  have hg : IsUpperSemicomputableOnIn A F (fun w ↦ g w.val) :=
    isUpperSemicomputableOnIn_decodedCost D A hA t F hF
  have hgeval : ∀ i n, g (pairCode (natBits i) (natBits n)) =
      (t : ℝ) * n - birkhoffSum D.T D.φ n (D.presentation.ι i) := by
    intro i n
    simp only [g, decodeFirst_pairCode, decodeSecond_pairCode, natBits, decodeBits_natBits]
  have hcmass := tsum_rpow_neg_lt_top_of_coded_mass D E p k N₀ t F
    (fun _ hw ↦ hw) g hgeval hmass
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F (fun w ↦ g w.val) hF hg
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) le_rfl hcmass
  obtain ⟨d, hd⟩ := oracle_tuple_bounds A
  refine ⟨N₀, hN₀, (c : ℝ) + d, ?_⟩
  intro n hn i hi
  have hw : F (pairCode (natBits i) (natBits n)) := ⟨i, n, rfl, hn, hi⟩
  have hcode := hc ⟨pairCode (natBits i) (natBits n), hw⟩
  change (oracleComplexity A (pairCode (natBits i) (natBits n)) : ℝ) ≤
    g (pairCode (natBits i) (natBits n)) + c at hcode
  rw [hgeval] at hcode
  have hproj : (oracleNatComplexity A i : ℝ) ≤
      (oracleComplexity A (pairCode (natBits i) (natBits n)) : ℝ) + d := by
    exact_mod_cast hd i n
  linarith

/-- Coding each covering slice bounds every point's upper pressure.
Blueprint node `pressure:code-net`. -/
theorem pointwiseUpper_le_of_effectiveUniformNet (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ))
    (hE : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z s E)
    (hRE : IsREIn A E) (x : X) (hx : x ∈ Z) :
    (pointwisePressure D.presentation D.T D.φ A x).2 ≤ (s : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro t ht
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp ht)
  have hscale : ∀ p, D.p₀ ≤ p →
      limsup (fun n ↦ finiteScalePressureRate D.presentation D.T D.φ A x n
        (dyadicRadius p)) atTop ≤ (t : EReal) := by
    intro p hp
    obtain ⟨k, hk⟩ := hE.2.2 p hp x hx
    obtain ⟨N₀, hN₀, c, hc⟩ :=
      uniformNet_tail_weight_summable D A hA Z s E hE hRE q hsq p hp k
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop N₀,
      (tendsto_const_div_atTop_nhds_zero_nat c).eventually
        (gt_mem_nhds (sub_pos.mpr hqt))] with n hn hcn
    have hn1 : 1 ≤ n := hN₀.trans hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hn0 : n ≠ 0 := by omega
    obtain ⟨i, hi, hxi⟩ := hk n hn1
    have hix := (bowen_geometry_symm D n hn1 (D.presentation.ι i) x
      (dyadicRadius p)).mp hxi
    rw [finiteScalePressureRate, ite_eq_right hn0]
    refine iInf_le_of_le i (iInf_le_of_le hix ?_)
    apply EReal.coe_le_coe_iff.mpr
    calc
      ((oracleNatComplexity A i : ℝ) + birkhoffSum D.T D.φ n (D.presentation.ι i)) / n ≤
          ((q : ℝ) * n + c) / n :=
        div_le_div_of_nonneg_right (hc n hn i hi) hnpos.le
      _ = (q : ℝ) + c / n := by field_simp
      _ ≤ t := by linarith
  change (⨆ p, limsup (fun n ↦ finiteScalePressureRate D.presentation D.T D.φ A x n
    (dyadicRadius p)) atTop) ≤ (t : EReal)
  refine iSup_le fun p ↦ ?_
  exact (pointwisePressure_mono_oracle_scale_upper D A x (le_max_left p D.p₀)).trans
    (hscale (max p D.p₀) (le_max_right _ _))

/-- For admissible oracles effective upper pressure is the upper pointwise supremum.
Blueprint node `pressure:effective-upper-equality`. -/
theorem effectiveUpperPressure_eq_iSup_pointwise (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (Z : Set X) :
    effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z =
      ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).2 := by
  apply le_antisymm
  · by_contra h_lt
    rw [not_le] at h_lt
    obtain ⟨r, hr⟩ := EReal.exists_between_coe_real h_lt
    obtain ⟨r', hr'⟩ := EReal.exists_between_coe_real hr.1
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp hr'.2)
    have h_q_lt : ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).2 <
        ((q : ℝ) : EReal) :=
      hr'.1.trans (EReal.coe_lt_coe_iff.mpr hq1)
    have hnet := upperThreshold_isUniformNet D A hA q
    have hnet_Z : IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z (q : ℝ)
        (upperPressureThreshold D.presentation D.T D.φ D.p₀ A q) := by
      refine ⟨hnet.1, hnet.2.1, fun p hp x hx ↦ hnet.2.2 p hp x ?_⟩
      exact lt_of_le_of_lt
        (le_iSup₂ (f := fun x _ ↦ (pointwisePressure D.presentation D.T D.φ A x).2) x hx) h_q_lt
    have h_eff_le : effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z ≤ ((q : ℝ) : EReal) :=
      iInf_le_of_le (q : ℝ) <|
        iInf_le_of_le (upperPressureThreshold D.presentation D.T D.φ D.p₀ A q) <|
        iInf_le_of_le ⟨hnet_Z, upperThreshold_isUniformNet_re D A hA q⟩ le_rfl
    exact lt_irrefl _ (h_eff_le.trans_lt ((EReal.coe_lt_coe_iff.mpr hq2).trans hr.2))
  · refine iSup₂_le fun x hx ↦ ?_
    refine le_iInf fun s ↦ le_iInf fun E ↦ le_iInf fun ⟨hE, hRE⟩ ↦ ?_
    exact pointwiseUpper_le_of_effectiveUniformNet D A hA Z s E hE hRE x hx

end Kolmogorov.PointToSet
