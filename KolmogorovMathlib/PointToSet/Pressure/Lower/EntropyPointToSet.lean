/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyZeroPotentialVariants
import KolmogorovMathlib.PointToSet.Pressure.Lower.EntropyCharacterization

/-!
# Effective entropy for every oracle and lower entropy point-to-set

This module proves the entropy part of the blueprint theorem `pressure:entropy-pts`. For
every oracle `A`, with no admissibility hypothesis, the effective upper entropy of a set `Z`
is the supremum over `Z` of the upper `A`-orbit complexities
(`entropy_effectiveCharacterization_allOracles_upper`).

For the upper bound, a rational `s` above the supremum yields the net of all quadruples
`(i, n, p, k)` with `K^A(i) < s n + k`. It is relatively enumerable, and Kraft's inequality
bounds each slice by `2 ^ (s n + k)`. For the lower bound, the Kraft–Chaitin coding of
relatively enumerable nets turns any net of exponent `a` into the linear bound
`K^A(i) ≤ t n + c` on its tail slices, for every rational `t > a`.

For the lower entropy the module identifies the zero-potential pointwise pressure with the
lower orbit complexity and combines this with the lower pressure point-to-set principle for the
zero potential. This gives an upper cone of oracles that attain the lower entropy
(`entropy_effectiveCharacterization_allOracles_cone`) and the all-oracle infimum formula
(`entropy_effectiveCharacterization_allOracles_pointToSet`). The results feed the upper entropy
corollaries in `KolmogorovMathlib.PointToSet.Pressure.Upper.PointToSetPrinciple`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### Relative enumerability -/

/-! ### The net of cheap indices at zero potential -/

/-- Membership in the zero-potential upper threshold: the order is positive and the oracle
complexity of the index is below the rate `s` times the order plus the slice allowance `k`. -/
private lemma mem_upperPressureThreshold_zero_iff {P : Presentation X} {T : X → X}
    {A : Set ℕ} {s : ℚ} {i n p k : ℕ} :
    (i, n, p, k) ∈ upperPressureThreshold P T (fun _ ↦ 0) 0 A s ↔
      1 ≤ n ∧ (oracleNatComplexity A i : ℝ) < (s : ℝ) * n + k := by
  simp only [upperPressureThreshold, Set.mem_ofPred_eq, birkhoffSum, Finset.sum_const_zero,
    sub_zero, zero_le, true_and]

/-- Each slice of the zero-potential threshold has mass at most `2 ^ (s n + k)`, by Kraft's
inequality for the oracle prefix complexity. -/
private lemma uniformPressureSum_upperThreshold_zero_le (P : Presentation X) (T : X → X)
    (A : Set ℕ) (s : ℚ) (n p k : ℕ) :
    uniformPressureSum P T (fun _ ↦ 0) (upperPressureThreshold P T (fun _ ↦ 0) 0 A s) n p k ≤
      (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) := by
  unfold uniformPressureSum
  simp only [birkhoffSum, Finset.sum_const_zero, ENNReal.rpow_zero]
  calc
    _ ≤ ∑' i : {i : ℕ | (i, n, p, k) ∈ upperPressureThreshold P T (fun _ ↦ 0) 0 A s},
        (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i := by
      refine ENNReal.tsum_le_tsum fun i ↦ ?_
      have hi : (oracleNatComplexity A i : ℝ) < (s : ℝ) * n + k :=
        (mem_upperPressureThreshold_zero_iff.1 i.property).2
      calc
        (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
        _ ≤ (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k - oracleNatComplexity A i) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by
          rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
            ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
    _ ≤ ∑' i : ℕ, (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun i : ℕ ↦ (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i)
    _ = (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i :=
      ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞) ^ ((s : ℝ) * n + k) * 1 := mul_le_mul' le_rfl (oracle_kraft A)
    _ = _ := mul_one _

/-- A bound `pressureRate q n ≤ b` at a positive order bounds the mass by `2 ^ (b n)`. -/
private lemma le_rpow_of_pressureRate_le {q : ℕ → ℝ≥0∞} {b : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : pressureRate q n ≤ (b : EReal)) : q n ≤ (2 : ℝ≥0∞) ^ (b * n) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hr : ENNReal.log (q n) * (((Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) ≤ b := by
    simpa only [pressureRate, ite_eq_right hn0, pressureLog, mul_assoc, ← EReal.coe_mul] using h
  refine ENNReal.log_strictMono.le_iff_le.mp ?_
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

/-- A sequence of extended reals bounded eventually by `s + k / n` has limsup at most `s`. -/
private lemma limsup_le_of_eventually_le_add_div {f : ℕ → EReal} {s : ℝ} {k : ℕ}
    (hf : ∀ᶠ n in atTop, f n ≤ (s : EReal) + ((k : ℝ) / n : ℝ)) :
    limsup f atTop ≤ (s : EReal) := by
  have hlim : Tendsto (fun n : ℕ ↦ s + (k : ℝ) / n) atTop (𝓝 s) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  have hlim' : Tendsto (fun n : ℕ ↦ (s : EReal) + ((k : ℝ) / n : ℝ)) atTop (𝓝 (s : EReal)) := by
    refine ((continuous_coe_real_ereal.tendsto s).comp hlim).congr fun n ↦ ?_
    exact EReal.coe_add _ _
  exact (limsup_le_limsup hf).trans_eq hlim'.limsup_eq

/-- The slices of the zero-potential threshold have logarithmic rate at most `s` in the limit. -/
private lemma limsup_pressureRate_upperThreshold_zero_le (P : Presentation X) (T : X → X)
    (A : Set ℕ) (s : ℚ) (p k : ℕ) :
    limsup (pressureRate fun n ↦
      uniformPressureSum P T (fun _ ↦ 0) (upperPressureThreshold P T (fun _ ↦ 0) 0 A s) n p k)
        atTop ≤ (s : ℝ) := by
  refine limsup_le_of_eventually_le_add_div (k := k) (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have h := pressureRate_le_of_le_rpow hn (q := fun n ↦ uniformPressureSum P T (fun _ ↦ 0)
    (upperPressureThreshold P T (fun _ ↦ 0) 0 A s) n p k)
    (uniformPressureSum_upperThreshold_zero_le P T A s n p k)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdiv : ((s : ℝ) * n + k) / n = s + (k : ℝ) / n := by field_simp
  rwa [hdiv, EReal.coe_add] at h

/-- A finite-scale cost below `s` at a positive order gives an ideal point of oracle
complexity below `s n` whose Bowen ball of order `n` contains `x`. -/
private lemma exists_complexity_lt_of_finiteScaleBSCost_lt {P : Presentation X} {T : X → X}
    {A : Set ℕ} {x : X} {n : ℕ} {ε s : ℝ} (hn : 1 ≤ n)
    (h : finiteScaleBSCost P T (fun _ ↦ 1) A x n ε < ENNReal.ofReal s) :
    ∃ i, (oracleNatComplexity A i : ℝ) < s * n ∧ x ∈ bowenBall T n (P.ι i) ε := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold finiteScaleBSCost at h
  rw [ite_eq_right hn0, iInf_lt_iff] at h
  obtain ⟨i, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨hball, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨-, h⟩ := h
  refine ⟨i, ?_, mem_bowenBall_symm hball⟩
  have hbs : birkhoffSum T (fun _ : X ↦ (1 : ℝ)) n (P.ι i) = n := by simp [birkhoffSum]
  rw [hbs] at h
  have h1 : (oracleNatComplexity A i : ℝ≥0∞) < ENNReal.ofReal s * ENNReal.ofReal n :=
    (ENNReal.div_lt_iff (Or.inl (by simpa using hnpos.ne')) (Or.inl ENNReal.ofReal_ne_top)).mp h
  rw [← ENNReal.ofReal_mul' hnpos.le] at h1
  simpa using (ENNReal.lt_ofReal_iff_toReal_lt (ENNReal.natCast_ne_top _)).mp h1

/-- If the upper orbit complexity of `x` is below `s`, then at every scale and all large
orders there is an ideal point of oracle complexity below `s n` in the Bowen ball of `x`. -/
private lemma eventually_exists_complexity_lt {P : Presentation X} {T : X → X} {A : Set ℕ}
    {x : X} {s : ℚ} (p : ℕ) (hsx : (orbitComplexities P T A x).2 < ENNReal.ofReal s) :
    ∀ᶠ n : ℕ in atTop, ∃ i, (oracleNatComplexity A i : ℝ) < (s : ℝ) * n ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  have hlim : limsup (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p)) atTop <
      ENNReal.ofReal s :=
    lt_of_le_of_lt (le_iSup (fun p ↦ limsup
      (fun n ↦ finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p)) atTop) p) hsx
  have hcost := eventually_lt_of_limsup_lt hlim (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
  filter_upwards [hcost, eventually_ge_atTop 1] with n hn hn1
  exact exists_complexity_lt_of_finiteScaleBSCost_lt hn1 hn

/-- Finitely many positive orders are covered by ideal points whose complexities are
absorbed by one natural allowance `k`. -/
private lemma exists_allowance_covering_small_orders (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (x : X) (p : ℕ) {s : ℚ} (hs : 0 ≤ (s : ℝ)) (N : ℕ) :
    ∃ k : ℕ, ∀ n, 1 ≤ n → n < N → ∃ i, (oracleNatComplexity A i : ℝ) < (s : ℝ) * n + k ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  have hr : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
  have hex : ∀ n : ℕ, ∃ i, 1 ≤ n → P.ι i ∈ bowenBall T n x (dyadicRadius p) := fun n ↦ by
    by_cases hn : 1 ≤ n
    · obtain ⟨i, hi⟩ := bowen_ball_dense P T hT x n hn _ hr
      exact ⟨i, fun _ ↦ hi⟩
    · exact ⟨0, fun h ↦ absurd h hn⟩
  choose i hi using hex
  refine ⟨(Finset.range N).sup (fun n ↦ oracleNatComplexity A (i n)) + 1, fun n hn hlt ↦ ?_⟩
  refine ⟨i n, ?_, mem_bowenBall_symm (hi n hn)⟩
  have hle : (oracleNatComplexity A (i n) : ℝ) ≤
      ((Finset.range N).sup (fun n ↦ oracleNatComplexity A (i n)) : ℕ) :=
    Nat.cast_le.2 (Finset.le_sup (f := fun n ↦ oracleNatComplexity A (i n))
      (Finset.mem_range.2 hlt))
  push_cast
  nlinarith [mul_nonneg hs n.cast_nonneg]

/-- If the upper orbit complexities of all points of `Z` are below `s`, then the
zero-potential upper threshold is a uniform net of exponent `s` covering `Z`. -/
private lemma isUniformPressureNet_upperThreshold_zero (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (Z : Set X) {s : ℚ} (hs0 : 0 ≤ (s : ℝ))
    (hs : ∀ x ∈ Z, (orbitComplexities P T A x).2 < ENNReal.ofReal s) :
    IsUniformPressureNet P T (fun _ ↦ 0) 0 Z (s : ℝ)
      (upperPressureThreshold P T (fun _ ↦ 0) 0 A s) := by
  refine ⟨fun t ht ↦ ⟨ht.1, ht.2.1⟩, fun p _ k ↦
    limsup_pressureRate_upperThreshold_zero_le P T A s p k, fun p _ x hx ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_exists_complexity_lt p (hs x hx))
  obtain ⟨k, hk⟩ := exists_allowance_covering_small_orders P T hT A x p hs0 N
  refine ⟨k, fun n hn ↦ ?_⟩
  rcases lt_or_ge n N with hlt | hge
  · obtain ⟨i, hi, hball⟩ := hk n hn hlt
    exact ⟨i, mem_upperPressureThreshold_zero_iff.2 ⟨hn, hi⟩, hball⟩
  · obtain ⟨i, hi, hball⟩ := hN n hge
    exact ⟨i, mem_upperPressureThreshold_zero_iff.2 ⟨hn, by linarith [k.cast_nonneg (α := ℝ)]⟩,
      hball⟩

/-- The zero-potential upper threshold is relatively enumerable for every oracle: it only
involves rational arithmetic and the enumerable strict cut of the oracle complexity. -/
private lemma isREIn_upperPressureThreshold_zero (P : Presentation X) (T : X → X) (A : Set ℕ)
    (s : ℚ) : IsREIn A (upperPressureThreshold P T (fun _ ↦ 0) 0 A s) := by
  have hE : upperPressureThreshold P T (fun _ ↦ 0) 0 A s =
      {t : ℕ × ℕ × ℕ × ℕ | 1 ≤ t.2.1 ∧
        (oracleComplexity A (natBits t.1) : ℝ) < ((s * t.2.1 + t.2.2.2 : ℚ) : ℝ)} := by
    ext ⟨i, n, p, k⟩
    rw [mem_upperPressureThreshold_zero_iff, Set.mem_ofPred_eq, oracleNatComplexity]
    push_cast
    rfl
  have hq : Computable (fun t : ℕ × ℕ × ℕ × ℕ ↦ s * (t.2.1 : ℚ) + (t.2.2.2 : ℚ)) :=
    computable₂_ratAdd.comp
      (computable₂_ratMul.comp (Computable.const s)
        (computable_nat_to_rat.comp (Computable.fst.comp Computable.snd)))
      (computable_nat_to_rat.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  obtain ⟨f, hf, hdom⟩ := isREIn_oracleComplexity_lt A
  rw [hE]
  refine IsREIn.and (isREIn_of_computable_decide
    (Primrec.nat_le.decide.to_comp.comp (Computable.const 1)
      (Computable.fst.comp Computable.snd))) ?_
  exact ⟨fun t ↦ f (natBits t.1, s * (t.2.1 : ℚ) + (t.2.2.2 : ℚ)),
    hf.comp ((natBits_computable.comp Computable.fst).pair hq).computableIn,
    fun t ↦ hdom (natBits t.1, s * (t.2.1 : ℚ) + (t.2.2.2 : ℚ))⟩

/-! ### Coding the tail of a net -/

/-- A series of rescaled masses is finite when the logarithmic rates have limsup `s < t`. -/
private lemma exists_tsum_rpow_mul_lt_top (q : ℕ → ℝ≥0∞) {s t : ℝ} (hst : s < t)
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
  refine lt_of_le_of_lt ?_ hgeom
  calc
    (∑' n : {n : ℕ | max 1 N ≤ n}, (2 : ℝ≥0∞) ^ (-t * n.val) * q n.val) ≤
        ∑' n : {n : ℕ | max 1 N ≤ n}, (2 : ℝ≥0∞) ^ (-(t - b) * n.val) := by
      refine ENNReal.tsum_le_tsum fun n ↦ ?_
      have he := le_rpow_of_pressureRate_le ((le_max_left _ _).trans n.property)
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
        (f := fun n : {n : ℕ | max 1 N ≤ n} ↦ (n : ℕ)) Subtype.val_injective
        (fun n : ℕ ↦ (2 : ℝ≥0∞) ^ (-(t - b) * n))

/-- The pair codes `(i, n)` of the tail `n ≥ N₀` of the slice `(p, k)` of a net `E` form a
relatively enumerable set of bit strings. -/
theorem isREIn_pairCode_tail (A : Set ℕ) {E : Set (ℕ × ℕ × ℕ × ℕ)} (hRE : IsREIn A E)
    (p k N₀ : ℕ) :
    IsREIn A (fun w : BitString ↦ ∃ i n : ℕ,
      w = pairCode (natBits i) (natBits n) ∧ N₀ ≤ n ∧ (i, n, p, k) ∈ E) := by
  let I : BitString → ℕ := fun w ↦ decodeBits (decodeFirst w)
  let J : BitString → ℕ := fun w ↦ decodeBits (decodeSecond w)
  have hI : Primrec I := primrec_decodeBits.comp CodedFiniteDistribution.decodeFirst_primrec
  have hJ : Primrec J := primrec_decodeBits.comp CodedFiniteDistribution.decodeSecond_primrec
  let C : BitString → Prop := fun w ↦
    w = pairCode (natBits (I w)) (natBits (J w)) ∧ N₀ ≤ J w
  have hC : PrimrecPred C :=
    (PrimrecRel.comp Primrec.eq Primrec.id
      (CodedFiniteDistribution.pairCode_primrec.comp
        (primrec_natBits.comp hI) (primrec_natBits.comp hJ))).and
      (PrimrecRel.comp Primrec.nat_le (Primrec.const N₀) hJ)
  have hEC := hRE.comp (f := fun w ↦ (I w, J w, p, k))
    (hI.to_comp.pair
      (hJ.to_comp.pair ((Computable.const p).pair (Computable.const k)))).computableIn
  have hCE := IsREIn.and (isREIn_of_computable_decide (A := A) hC.decide.to_comp) hEC
  convert hCE using 1
  ext w
  constructor
  · rintro ⟨i, n, rfl, hn, he⟩
    simp only [C, I, J, decodeFirst_pairCode, decodeSecond_pairCode, natBits, decodeBits_natBits]
    exact ⟨⟨True.intro, hn⟩, he⟩
  · rintro ⟨⟨hw, hn⟩, he⟩
    exact ⟨I w, J w, hw, hn, he⟩

/-- On a relatively enumerable domain of bit strings, the rational multiple `t` of the
second component of a pair code is upper semicomputable. -/
private lemma isUpperSemicomputableOnIn_mul_decodeSecond (A : Set ℕ) (t : ℚ)
    {F : BitString → Prop} (hF : IsREIn A F) :
    IsUpperSemicomputableOnIn A F (fun w ↦ (t : ℝ) * decodeBits (decodeSecond w.val)) := by
  let J : BitString → ℕ := fun w ↦ decodeBits (decodeSecond w)
  let g : BitString → ℝ := fun w ↦ (t : ℝ) * J w
  have hJ : Computable J :=
    (primrec_decodeBits.comp CodedFiniteDistribution.decodeSecond_primrec).to_comp
  have hg : IsComputableRealFamilyIn A g := by
    refine ⟨fun wp ↦ t * (J wp.1 : ℚ), ?_, fun w m ↦ ?_⟩
    · exact (computable₂_ratMul.comp (Computable.const t)
        (computable_nat_to_rat.comp (hJ.comp Computable.fst))).computableIn
    · simp only [g, Rat.cast_mul, Rat.cast_natCast, sub_self, abs_zero]
      positivity
  have hdom := hF.comp (f := fun wq : BitString × ℚ ↦ wq.1) Computable.fst.computableIn
  refine ⟨fun wq ↦ F wq.1 ∧ g wq.1 < (wq.2 : ℝ),
    IsREIn.and hdom (birkhoff_computableIn_lt A g hg), fun w q h ↦ ⟨h.1, h.2⟩, ?_⟩
  intro w ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g w.val) hε)
  exact ⟨q, ⟨w.property, hq1⟩, hq2⟩

/-- A relatively enumerable uniform net of exponent `a < t` has tail slices of bounded excess:
beyond some order `N₀`, every index in the slice `(p, k)` at order `n` has oracle complexity
at most `t n + c`. This is the Kraft–Chaitin coding of the tail of the slice. -/
private lemma exists_complexity_le_of_isUniformPressureNet (P : Presentation X) (T : X → X)
    (A : Set ℕ) {E : Set (ℕ × ℕ × ℕ × ℕ)} {a : ℝ} {Z : Set X}
    (hE : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z a E) (hRE : IsREIn A E) (p k : ℕ)
    {t : ℚ} (hat : a < (t : ℝ)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ c : ℝ, ∀ n ≥ N₀, ∀ i, (i, n, p, k) ∈ E →
      (oracleNatComplexity A i : ℝ) ≤ (t : ℝ) * n + c := by
  classical
  obtain ⟨N₀, hN₀, hmass⟩ := exists_tsum_rpow_mul_lt_top
    (fun n ↦ uniformPressureSum P T (fun _ ↦ 0) E n p k) hat (hE.2.1 p (Nat.zero_le p) k)
  let F : BitString → Prop := fun w ↦ ∃ i n : ℕ,
    w = pairCode (natBits i) (natBits n) ∧ N₀ ≤ n ∧ (i, n, p, k) ∈ E
  let g : BitString → ℝ := fun w ↦ (t : ℝ) * decodeBits (decodeSecond w)
  have hF : IsREIn A F := isREIn_pairCode_tail A hRE p k N₀
  have hg : IsUpperSemicomputableOnIn A F (fun w ↦ g w.val) :=
    isUpperSemicomputableOnIn_mul_decodeSecond A t hF
  have hgeval : ∀ i n, g (pairCode (natBits i) (natBits n)) = (t : ℝ) * n := by
    intro i n
    simp only [g, decodeSecond_pairCode, natBits, decodeBits_natBits]
  have hcmass : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) < ⊤ := by
    choose i n hw hn he using fun w : Subtype F ↦ w.property
    let f : Subtype F → Σ n : {n : ℕ | N₀ ≤ n}, {i : ℕ | (i, n.val, p, k) ∈ E} :=
      fun w ↦ ⟨⟨n w, hn w⟩, ⟨i w, he w⟩⟩
    have hf : Function.Injective f := fun u v huv ↦ by
      have hnuv : n u = n v := congrArg (fun z ↦ z.1.val) huv
      have hiuv : i u = i v := congrArg (fun z ↦ z.2.val) huv
      exact Subtype.ext (by rw [hw u, hw v, hnuv, hiuv])
    let a' : (Σ n : {n : ℕ | N₀ ≤ n}, {i : ℕ | (i, n.val, p, k) ∈ E}) → ℝ≥0∞ :=
      fun z ↦ (2 : ℝ≥0∞) ^ (-(t : ℝ) * z.1.val)
    refine lt_of_le_of_lt ?_ hmass
    calc
      (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) = ∑' w : Subtype F, a' (f w) :=
        tsum_congr fun w ↦ by
          rw [hw w, hgeval]
          dsimp only [a', f]
          congr 1
          ring
      _ ≤ ∑' z, a' z := ENNReal.tsum_comp_le_tsum_of_injective hf a'
      _ = ∑' n : {n : ℕ | N₀ ≤ n}, (2 : ℝ≥0∞) ^ (-(t : ℝ) * n.val) *
          uniformPressureSum P T (fun _ ↦ 0) E n.val p k := by
        rw [ENNReal.tsum_sigma']
        refine tsum_congr fun n ↦ ?_
        dsimp only [a', uniformPressureSum]
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i ↦ ?_
        simp only [birkhoffSum, Finset.sum_const_zero, ENNReal.rpow_zero, mul_one]
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F (fun w ↦ g w.val) hg
    (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w.val)) le_rfl hcmass
  obtain ⟨d, hd⟩ := oracle_tuple_bounds A
  refine ⟨N₀, hN₀, (c : ℝ) + d, fun n hn i hi ↦ ?_⟩
  have hcode := hc ⟨pairCode (natBits i) (natBits n), ⟨i, n, rfl, hn, hi⟩⟩
  change (oracleComplexity A (pairCode (natBits i) (natBits n)) : ℝ) ≤
    g (pairCode (natBits i) (natBits n)) + c at hcode
  rw [hgeval] at hcode
  have hproj : (oracleNatComplexity A i : ℝ) ≤
      (oracleComplexity A (pairCode (natBits i) (natBits n)) : ℝ) + d := by
    exact_mod_cast hd i n
  linarith

/-! ### From nets to orbit complexities -/

/-- If every positive order is covered by an index of a net and indices of order at least `N`
have complexity at most `t n + c`, then the orbit complexity is at most `t n + c` for
all orders `n ≥ N`. -/
private lemma orbitComplexityNat_le_of_cover {P : Presentation X} {T : X → X} {A : Set ℕ}
    {E : Set (ℕ × ℕ × ℕ × ℕ)} {x : X} {p k N : ℕ} (hN : 1 ≤ N) {t c : ℝ}
    (hcover : ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ E ∧ x ∈ bowenBall T n (P.ι i) (dyadicRadius p))
    (hcode : ∀ n ≥ N, ∀ i, (i, n, p, k) ∈ E → (oracleNatComplexity A i : ℝ) ≤ t * n + c) :
    ∀ n ≥ N, (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) ≤ t * n + c := by
  intro n hn
  obtain ⟨i, hiE, hiball⟩ := hcover n (hN.trans hn)
  have hle : orbitComplexity P T A x n (dyadicRadius p) ≤ oracleNatComplexity A i :=
    iInf_le_of_le i (iInf_le_of_le (mem_bowenBall_symm hiball) le_rfl)
  have hnat : orbitComplexityNat P T A x n (dyadicRadius p) ≤ oracleNatComplexity A i :=
    ENat.toNat_le_of_le_natCast hle
  exact (Nat.cast_le.2 hnat).trans (hcode n hn i hiE)

/-- A natural-valued sequence eventually bounded by `t n + c` has `u n / n` of limsup at
most `t` in `ℝ≥0∞`. -/
private lemma limsup_natCast_div_le_ofReal {u : ℕ → ℕ} {t c : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, (u n : ℝ) ≤ t * n + c) :
    limsup (fun n : ℕ ↦ (u n : ℝ≥0∞) / n) atTop ≤ ENNReal.ofReal t := by
  have hle : ∀ᶠ n : ℕ in atTop,
      (u n : ℝ≥0∞) / n ≤ ENNReal.ofReal (t + c / n) := by
    filter_upwards [h, eventually_gt_atTop 0] with n hn hpos
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
    have hdiv : (u n : ℝ) / n ≤ t + c / n := by
      rw [← mul_div_cancel_right₀ t hnpos.ne', ← add_div]
      exact div_le_div_of_nonneg_right hn hnpos.le
    rw [← ENNReal.ofReal_natCast (u n), ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_div_of_pos hnpos]
    exact ENNReal.ofReal_le_ofReal hdiv
  have htendsto : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (t + c / n)) atTop
      (𝓝 (ENNReal.ofReal t)) := by
    have hreal : Tendsto (fun n : ℕ ↦ t + c / n) atTop (𝓝 t) := by
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact (limsup_le_limsup hle).trans_eq htendsto.limsup_eq

/-- An extended nonnegative number that is at most every rational above `a` is at most
`ENNReal.ofReal a`. -/
private lemma le_ofReal_of_forall_rat {R : ℝ≥0∞} {a : ℝ}
    (h : ∀ t : ℚ, a < (t : ℝ) → 0 < (t : ℝ) → R ≤ ENNReal.ofReal t) : R ≤ ENNReal.ofReal a := by
  by_contra hn
  obtain ⟨q, -, hlo, hhi⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (lt_of_not_ge hn)
  obtain ⟨haq, hqpos⟩ := ENNReal.ofReal_lt_ofReal_iff'.mp hlo
  exact (not_lt_of_ge (h q haq hqpos)) hhi

/-- Every point of a relatively enumerable uniform net's domain has upper orbit complexity
at most the exponent of the net. -/
private lemma iSup_orbitComplexities_snd_le_of_isUniformPressureNet (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) {E : Set (ℕ × ℕ × ℕ × ℕ)} {a : ℝ}
    (ha : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z a E) (hRE : IsREIn A E) :
    (⨆ x ∈ Z, (orbitComplexities P T A x).2) ≤ ENNReal.ofReal a := by
  refine iSup₂_le fun x hx ↦ ?_
  rw [entropiesAndOrbitComplexities_upper_rate P T hT A x]
  refine iSup_le fun p ↦ le_ofReal_of_forall_rat fun t hat htpos ↦ ?_
  obtain ⟨k, hk⟩ := ha.2.2 p (Nat.zero_le p) x hx
  obtain ⟨N₀, hN₀, c, hc⟩ := exists_complexity_le_of_isUniformPressureNet P T A ha hRE p k hat
  exact limsup_natCast_div_le_ofReal (t := t) (c := c)
    (eventually_atTop.2 ⟨N₀, orbitComplexityNat_le_of_cover hN₀ hk hc⟩)

/-- Effective upper entropy is at most the supremum of the upper orbit complexities: choose a
rational above the supremum and use the zero-potential threshold net. -/
private lemma effectiveUpperEntropy_le_iSup_orbitComplexities_snd (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (Z : Set X) :
    effectiveUpperEntropy P T A Z ≤ ⨆ x ∈ Z, (orbitComplexities P T A x).2 := by
  refine le_of_forall_gt_imp_ge_of_dense fun R hR ↦ ?_
  obtain ⟨q, hq0, hRq, hqR⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hR
  have hq : (0 : ℝ) ≤ q := Rat.cast_nonneg.2 hq0
  have hs : ∀ x ∈ Z, (orbitComplexities P T A x).2 < ENNReal.ofReal q := fun x hx ↦
    lt_of_le_of_lt (le_iSup₂ (f := fun x (_ : x ∈ Z) ↦ (orbitComplexities P T A x).2) x hx) hRq
  have hnet := And.intro (isUniformPressureNet_upperThreshold_zero P T hT A Z hq hs)
    (isREIn_upperPressureThreshold_zero P T A q)
  have hle : effectiveUpperEntropy P T A Z ≤ ENNReal.ofReal q :=
    iInf_le_of_le (q : ℝ) (iInf_le_of_le hq (iInf_le_of_le _ (iInf_le_of_le hnet le_rfl)))
  exact hle.trans hqR.le

/-- Effective upper entropy is the upper orbit-rate supremum without admissibility.
Blueprint node `pressure:entropy-pts`. -/
theorem entropy_effectiveCharacterization_allOracles_upper (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (Z : Set X) :
    effectiveUpperEntropy P T A Z = ⨆ x ∈ Z, (orbitComplexities P T A x).2 :=
  le_antisymm (effectiveUpperEntropy_le_iSup_orbitComplexities_snd P T hT A Z)
    (le_iInf fun _ ↦ le_iInf fun _ ↦ le_iInf fun _ ↦ le_iInf fun hE ↦
      iSup_orbitComplexities_snd_le_of_isUniformPressureNet P T hT A Z hE.1 hE.2)

/-! ### Lower entropy as the zero-potential lower pressure -/

/-- For the zero potential, the lower pointwise pressure is the lower orbit complexity,
viewed in `EReal`. -/
private lemma pointwisePressure_zero_fst (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X) :
    (pointwisePressure P T (fun _ ↦ 0) A x).1 = ((orbitComplexities P T A x).1 : EReal) := by
  unfold pointwisePressure orbitComplexities pointwiseBSDimension
  dsimp only
  rw [EReal.coe_ennreal_iSup]
  refine iSup_congr fun p ↦ ?_
  rw [EReal.coe_ennreal_liminf]
  simp only [finiteScalePressureRate_zero]

/-- Lower entropy attainment holds throughout an upper cone of oracles.
Blueprint node `pressure:entropy-pts`. -/
theorem entropy_effectiveCharacterization_allOracles_cone (P : Presentation X)
    (T : X → X) (hT : Continuous T) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      lowerEntropy T Z = ⨆ x ∈ Z, (orbitComplexities P T A x).1 := by
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · exact ⟨∅, fun A _ ↦ by
      rw [entropiesAndOrbitComplexities_empty, iSup_emptyset, bot_eq_zero]⟩
  · obtain ⟨B, hB⟩ := lowerPressure_pointToSet_cone (zeroPotentialData P T hT) Z
    refine ⟨B, fun A hA ↦ EReal.coe_ennreal_injective ?_⟩
    rw [entropy_eq_zeroPotentialPressure_of_nonempty P T hT Z hZ, EReal.coe_ennreal_biSup hZ]
    exact (hB A hA).trans (iSup_congr fun x ↦ iSup_congr fun _ ↦
      pointwisePressure_zero_fst P T A x)

/-- Classical lower entropy is the all-oracle infimum of lower pointwise orbit suprema.
Blueprint node `pressure:entropy-pts`. -/
theorem entropy_effectiveCharacterization_allOracles_pointToSet (P : Presentation X)
    (T : X → X) (hT : Continuous T) (Z : Set X) :
    lowerEntropy T Z = ⨅ A : Set ℕ, ⨆ x ∈ Z, (orbitComplexities P T A x).1 := by
  apply le_antisymm
  · apply le_iInf
    intro A
    have h1 := entropy_eq_zeroPotentialPressure_of_nonempty_le_effective P T hT A Z
    have h2 := entropy_effectiveCharacterization_allOracles P T hT A Z
    rwa [h2] at h1
  · obtain ⟨B, hB⟩ := entropy_effectiveCharacterization_allOracles_cone P T hT Z
    have h3 := hB B (TuringReducible.refl _)
    have h4 := iInf_le (fun (A : Set ℕ) => ⨆ x ∈ Z, (orbitComplexities P T A x).1) B
    rwa [← h3] at h4

end Kolmogorov.PointToSet
