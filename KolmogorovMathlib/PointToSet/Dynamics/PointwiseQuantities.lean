/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics.BowenBalls

/-!
# Pointwise pressure and changes of presentation

This module defines finite-scale normalized pressure costs, pointwise pressure and
Barreira–Schmeling dimensions, and the lower Birkhoff average. Under a computable comparison
of ideal-point presentations, translating Bowen-ball centers changes pressure costs by a
sublinear complexity overhead and a vanishing oscillation error. Taking time limits and
then scale suprema proves that pointwise pressure is independent of the presentation
(blueprint node `metric:change`). The comparison data and pointwise quantities are also
used to prove Barreira–Schmeling invariance in `Dynamics.PresentationChangeBS`.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-- The infimum of normalized complexity-plus-potential costs of ideal centers in a
Bowen ball. At orbit length zero the value is infinity. Blueprint node `metric:change`. -/
noncomputable def finiteScalePressureRate (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (A : Set ℕ) (x : X) (n : ℕ) (ε : ℝ) : EReal :=
  if n = 0 then ⊤ else
    ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x ε),
      (((oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)) / n : ℝ) : EReal)

/-- At the zero potential, the finite-scale pressure rate is the finite-scale
Barreira–Schmeling cost of the constant function `1`. -/
theorem finiteScalePressureRate_zero (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)
    (n : ℕ) (ε : ℝ) :
    finiteScalePressureRate P T (fun _ ↦ 0) A x n ε =
      ((finiteScaleBSCost P T (fun _ ↦ 1) A x n ε : ℝ≥0∞) : EReal) := by
  unfold finiteScalePressureRate finiteScaleBSCost
  by_cases hn : n = 0
  · simp [hn]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    simp only [hn, ↓reduceIte, EReal.coe_ennreal_iInf, birkhoffSum, Finset.sum_const_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, add_zero, hn_pos, iInf_pos,
      ENNReal.ofReal_natCast]
    refine iInf_congr fun i ↦ iInf_congr fun _ ↦ ?_
    rw [← ENNReal.toReal_natCast n, ← ENNReal.toReal_natCast (oracleNatComplexity A i),
      ← ENNReal.toReal_div, EReal.coe_ennreal_toReal]
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.2 hn)

/-- Lower and upper pointwise pressure use dyadic scale suprema of normalized lower and
upper time limits. Any cofinal small-scale tail has the same supremum.
Blueprint node `metric:change`. -/
noncomputable def pointwisePressure (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (A : Set ℕ) (x : X) : EReal × EReal :=
  (⨆ p, liminf (fun n ↦ finiteScalePressureRate P T φ A x n (dyadicRadius p)) atTop,
    ⨆ p, limsup (fun n ↦ finiteScalePressureRate P T φ A x n (dyadicRadius p)) atTop)

/-- Total lower and upper pointwise BS dimensions use positive-denominator infima and
dyadic scale suprema, including outside the positive-average locus.
Blueprint node `metric:change`. -/
noncomputable def pointwiseBSDimension (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (x : X) : ℝ≥0∞ × ℝ≥0∞ :=
  (⨆ p, liminf (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop,
    ⨆ p, limsup (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop)

/-- The lower Birkhoff average uses `EReal`, so unbounded averages have their actual
extended values. The order-zero term is immaterial. Blueprint node `metric:change`. -/
noncomputable def lowerBirkhoffAverage (T : X → X) (u : X → ℝ) (x : X) : EReal :=
  liminf (fun n ↦ ((birkhoffSum T u n x / n : ℝ) : EReal)) atTop

/-- The effective hypotheses for a dynamical presentation change explicitly include
both metric tables, mixed distances, both representations of the dynamics and mixed
orbit distances. Blueprint node `metric:change`. -/
def DynamicalComparisonIn (P Q : Presentation X) (T : X → X) (A : Set ℕ) : Prop :=
  ComputablePresentationIn P A ∧ ComputablePresentationIn Q A ∧
    IsComputableRealFamilyIn A (fun ij : ℕ × ℕ ↦ dist (P.ι ij.1) (Q.ι ij.2)) ∧
    IsRepresentedMapIn P P A T ∧ IsRepresentedMapIn Q Q A T ∧
    IsComputableRealFamilyIn A
      (fun nij : ℕ × ℕ × ℕ ↦ bowenDist T nij.1 (P.ι nij.2.1) (Q.ι nij.2.2))

/-- Swapping ideal indices reverses the mixed metric and orbit-distance computations. -/
theorem DynamicalComparisonIn.symm {P Q : Presentation X} {T : X → X}
    {A : Set ℕ} (hdata : DynamicalComparisonIn P Q T A) :
    DynamicalComparisonIn Q P T A := by
  rcases hdata with ⟨hP, hQ, hdist, hTP, hTQ, horbit⟩
  refine ⟨hQ, hP, ?_, hTQ, hTP, ?_⟩
  · have h := IsComputableRealFamilyIn.comp A _ hdist
      (fun ij : ℕ × ℕ ↦ (ij.2, ij.1)) (Computable.snd.pair Computable.fst)
    simpa only [Function.comp_def, dist_comm] using h
  · have h := IsComputableRealFamilyIn.comp A _ horbit
      (fun nij : ℕ × ℕ × ℕ ↦ (nij.1, nij.2.2, nij.2.1))
      (Computable.fst.pair ((Computable.snd.comp Computable.snd).pair
        (Computable.fst.comp Computable.snd)))
    simpa only [Function.comp_def, bowen_dist_comm] using h

/-- At any dyadic precision, mixed Bowen-distance computations allow a change of ideal
center with logarithmic complexity overhead in the positive orbit length. The additive
constant is uniform in the source index and orbit length. -/
private lemma exists_close_center_complexity_le (P Q : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A
      (fun nij : ℕ × ℕ × ℕ ↦ bowenDist T nij.1 (P.ι nij.2.1) (Q.ι nij.2.2)))
    (p : ℕ) :
    ∃ c : ℕ, ∀ n i, 1 ≤ n → ∃ j,
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius p ∧
        (oracleNatComplexity A j : ℝ) ≤
          oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c := by
  classical
  obtain ⟨q, hq, hqerr⟩ := hmixed
  let r : ℚ := (2 : ℚ)⁻¹ ^ p
  have hr : (r : ℝ) = dyadicRadius p := by
    norm_num only [r, dyadicRadius, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
  let test : (ℕ × ℕ) → ℕ → Option ℕ := fun v k ↦
    if q ((v.2, v.1, (Nat.unpair k).1), (Nat.unpair k).2) +
        (2 : ℚ)⁻¹ ^ (Nat.unpair k).2 < r then some (Nat.unpair k).1 else none
  let E : ℕ × ℕ →. ℕ := fun v ↦ Nat.rfindOpt (test v)
  have hu : Computable (fun w : (ℕ × ℕ) × ℕ ↦ Nat.unpair w.2) :=
    Primrec.unpair.to_comp.comp Computable.snd
  have hjcomp := Computable.fst.comp hu
  have htcomp := Computable.snd.comp hu
  have harg : Computable (fun w : (ℕ × ℕ) × ℕ ↦
      ((w.1.2, w.1.1, (Nat.unpair w.2).1), (Nat.unpair w.2).2)) :=
    ((Computable.snd.comp Computable.fst).pair
      ((Computable.fst.comp Computable.fst).pair hjcomp)).pair htcomp
  have hqcomp := hq.comp harg.computableIn
  have heps : Computable (fun t : ℕ ↦ (2 : ℚ)⁻¹ ^ t) :=
    computable_rat_inv_two_pow.of_eq (fun t ↦ by simp only [inv_pow])
  have hsum := (Computable₂.computableIn₂ computable₂_ratAdd).comp hqcomp
    (heps.comp htcomp).computableIn
  have hcmp := (Computable₂.computableIn₂ computable₂_ratLt).comp hsum
    (Computable.const r).computableIn
  have htest : ComputableIn {charOracle A}
      (fun w : (ℕ × ℕ) × ℕ ↦ test w.1 w.2) := by
    have h := computable_in_cond hcmp (Computable.option_some.comp hjcomp).computableIn
      (Computable.const (none : Option ℕ)).computableIn
    simpa only [Bool.cond_decide] using h
  have hE : PartrecIn {charOracle A} E := PartrecIn.rfindOpt htest.to₂
  have hsound : ∀ i n j, j ∈ E (i, n) →
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius p := by
    intro i n j hj
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hj
    dsimp [test] at hk
    split_ifs at hk with hcmp
    · simp only [Option.mem_def, Option.some.injEq] at hk
      subst j
      have hcmpR : (q ((n, i, (Nat.unpair k).1), (Nat.unpair k).2) : ℝ) +
          (2 : ℝ)⁻¹ ^ (Nat.unpair k).2 < dyadicRadius p := by
        have h := (Rat.cast_lt (K := ℝ)).mpr hcmp
        push_cast at h
        rwa [hr] at h
      have herr := (abs_lt.mp (hqerr (n, i, (Nat.unpair k).1) (Nat.unpair k).2)).1
      linarith
    · simp at hk
  have htotal : ∀ i n, 1 ≤ n → (E (i, n)).Dom := by
    intro i n hn
    obtain ⟨j, hj⟩ := bowen_ball_dense Q T hT (P.ι i) n hn
      (dyadicRadius p) (by dsimp [dyadicRadius]; positivity)
    have hd := (bowen_ball_dense_iff T n hn (P.ι i) (Q.ι j) _).mp hj
    obtain ⟨t, ht⟩ := exists_two_mul_inv_two_pow_lt
      (dyadicRadius p - bowenDist T n (P.ι i) (Q.ι j)) (sub_pos.mpr hd)
    have hcmp : q ((n, i, j), t) + (2 : ℚ)⁻¹ ^ t < r := by
      apply (Rat.cast_lt (K := ℝ)).mp
      push_cast
      rw [hr]
      have ht' : 2 * (2 : ℝ)⁻¹ ^ t <
          dyadicRadius p - bowenDist T n (P.ι i) (Q.ι j) := by
        simpa only [inv_pow] using ht
      have herr := (abs_lt.mp (hqerr (n, i, j) t)).2
      linarith
    apply Nat.rfindOpt_dom.mpr
    exact ⟨Nat.pair j t, j, by
      simp only [test, Nat.unpair_pair, ite_eq_left hcmp, Option.mem_def]⟩
  let decode : List BitString → ℕ × ℕ := fun ws ↦
    (decodeBits (decodeFirst (ws.getD 0 [])), decodeBits (decodeSecond (ws.getD 0 [])))
  have hget : Computable (fun ws : List BitString ↦ ws.getD 0 []) :=
    Computable₂.comp (f := fun (l : List BitString) (n : ℕ) ↦ l.getD n [])
      (Primrec.list_getD ([] : BitString)).to_comp Computable.id (Computable.const 0)
  have hdecode : Computable decode :=
    (decodeBits_computable.comp (decodeFirst_computable.comp hget)).pair
      (decodeBits_computable.comp (decodeSecond_computable.comp hget))
  let F : List BitString →. BitString := fun ws ↦ (E (decode ws)).map natBits
  have hF : PartrecIn {charOracle A} F :=
    (hE.comp hdecode.computableIn).map
      (natBits_computable.comp Computable.snd).computableIn.to₂
  obtain ⟨c₁, hc₁⟩ := oracle_tuple_bounds_composition A 1 F hF
  obtain ⟨c₂, hc₂⟩ := oracle_tuple_bounds_overhead A
  refine ⟨c₁ + c₂, ?_⟩
  intro n i hn
  have hdom := htotal i n hn
  let j := (E (i, n)).get hdom
  have hj : j ∈ E (i, n) := Part.get_mem hdom
  refine ⟨j, hsound i n j hj, ?_⟩
  have hFout : natBits j ∈ F [pairCode (natBits i) (natBits n)] := by
    dsimp [F, decode]
    simp only [List.getD_cons_zero, decodeFirst_pairCode, decodeSecond_pairCode,
      natBits, decodeBits_natBits]
    rw [Part.mem_map_iff]
    exact ⟨j, hj, rfl⟩
  have hcomp := hc₁ [pairCode (natBits i) (natBits n)] (natBits j) (by simp) hFout
  have hcomp' : oracleNatComplexity A j ≤ oraclePairComplexity A i n + c₁ := by
    simpa only [oracleNatComplexity, oraclePairComplexity, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] using hcomp
  have hcompR : (oracleNatComplexity A j : ℝ) ≤ oraclePairComplexity A i n + c₁ := by
    exact_mod_cast hcomp'
  push_cast
  linarith [hc₂ i n]

/-- Transferring centers at a finer scale bounds the normalized pressure rate by the
source rate, the normalized coding overhead, and the potential oscillation. -/
private lemma finiteScalePressureRate_le_add_of_transfer (P Q : Presentation X)
    (T : X → X) (φ : X → ℝ) (A : Set ℕ) (x : X) (p n c : ℕ)
    (hn : 1 ≤ n) (ω : ℝ)
    (hω : ∀ y z, dist y z < 2 * dyadicRadius p → |φ y - φ z| ≤ ω)
    (htransfer : ∀ i, ∃ j,
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius (p + 2) ∧
        (oracleNatComplexity A j : ℝ) ≤
          oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c) :
    finiteScalePressureRate Q T φ A x n (dyadicRadius p) ≤
      finiteScalePressureRate P T φ A x n (dyadicRadius (p + 2)) +
        (((2 * Real.logb 2 (n + 1) + c) / n + ω : ℝ) : EReal) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold finiteScalePressureRate
  rw [ite_eq_right hn0, ite_eq_right hn0]
  apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp
  refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
  obtain ⟨j, hclose, hcomplex⟩ := htransfer i
  have hradius : dyadicRadius (p + 2) ≤ dyadicRadius p := by
    dsimp [dyadicRadius]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hjball : Q.ι j ∈ bowenBall T n x (dyadicRadius p) := by
    apply (bowen_ball_dense_iff T n hn x (Q.ι j) _).mpr
    have hi' := (bowen_ball_dense_iff T n hn x (P.ι i) _).mp hi
    have htri := bowen_ball_dense_triangle T n x (P.ι i) (Q.ι j)
    have hrad : 2 * dyadicRadius (p + 2) ≤ dyadicRadius p := by
      dsimp [dyadicRadius]
      rw [pow_add]
      norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) p]
    linarith
  have hjold : Q.ι j ∈ bowenBall T n (P.ι i) (dyadicRadius p) :=
    (bowen_ball_dense_iff T n hn (P.ι i) (Q.ι j) _).mpr (hclose.trans_le hradius)
  have hosc := small_scale_oscillation_birkhoff T φ p ω hω n (P.ι i) (Q.ι j) hjold
  apply EReal.sub_le_of_le_add
  refine (iInf₂_le j hjball).trans ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hnum : (oracleNatComplexity A j : ℝ) + birkhoffSum T φ n (Q.ι j) ≤
      (oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)) +
        (2 * Real.logb 2 (n + 1) + c) + n * ω := by
    linarith [(abs_le.mp hosc).2]
  calc
    (oracleNatComplexity A j + birkhoffSum T φ n (Q.ι j)) / n ≤
        ((oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)) +
          (2 * Real.logb 2 (n + 1) + c) + n * ω) / n :=
      div_le_div_of_nonneg_right hnum hnpos.le
    _ = (oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)) / n +
        ((2 * Real.logb 2 (n + 1) + c) / n + ω) := by
      field_simp
      ring

/-- A logarithmic coding overhead vanishes after division by the orbit length. -/
private lemma tendsto_logarithmic_overhead_div_time (c : ℕ) :
    Tendsto (fun n : ℕ ↦ (2 * Real.logb 2 (n + 1) + c) / (n : ℝ))
      atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2)
    1 (-1) 1 one_ne_zero).comp hshift
  have hlog' : Tendsto (fun n : ℕ ↦ Real.logb 2 (n + 1) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlog
  have hc : Tendsto (fun n : ℕ ↦ (c : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [zero_add, mul_zero, add_div, mul_div_assoc] using (hlog'.const_mul 2).add hc

/-- An eventual comparison with a convergent real additive error bounds the lower limits
in `EReal`, including infinite limits. -/
private lemma liminf_le_add_of_eventually_le_add (f g : ℕ → EReal)
    (e : ℕ → ℝ) (ω : ℝ) (he : Tendsto e atTop (𝓝 ω))
    (hfg : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    liminf f atTop ≤ liminf g atTop + (ω : EReal) := by
  have he' : Tendsto (fun n ↦ (e n : EReal)) atTop (𝓝 (ω : EReal)) :=
    EReal.tendsto_coe.mpr he
  have hlimsup := he'.limsup_eq
  calc
    liminf f atTop ≤ liminf (fun n ↦ g n + (e n : EReal)) atTop :=
      liminf_le_liminf hfg
    _ ≤ liminf g atTop + (ω : EReal) := by
      have h := EReal.liminf_add_le (u := fun n ↦ (e n : EReal)) (v := g)
        (f := atTop) (Or.inl (by rw [hlimsup]; exact EReal.coe_ne_bot _))
        (Or.inl (by rw [hlimsup]; exact EReal.coe_ne_top _))
      simpa only [Pi.add_def, add_comm, hlimsup] using h

/-- Shrinking dyadic radii increases the normalized pressure cost. -/
private lemma monotone_finiteScalePressureRate_dyadic (P : Presentation X)
    (T : X → X) (φ : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) :
    Monotone (fun p ↦ finiteScalePressureRate P T φ A x n (dyadicRadius p)) := by
  intro p q hpq
  unfold finiteScalePressureRate
  split_ifs
  · exact le_rfl
  · apply iInf_mono
    intro i
    apply iInf_mono'
    intro hi
    refine ⟨?_, le_rfl⟩
    exact Dynamics.dynEntourage_monotone T n
      (fun z hz ↦ lt_of_lt_of_le hz
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hpq)) hi

/-- A monotone sequence bounded eventually by a fixed extended real plus a vanishing
real error has supremum at most that extended real. -/
private lemma iSup_le_of_monotone_of_eventually_le_add (f : ℕ → EReal)
    (hf : Monotone f) (ω : ℕ → ℝ) (hω : Tendsto ω atTop (𝓝 0)) (b : EReal)
    (hbound : ∀ᶠ p in atTop, f p ≤ b + (ω p : EReal)) :
    (⨆ p, f p) ≤ b := by
  have hzero : Tendsto (fun p ↦ (ω p : EReal)) atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr hω
  have hsum : Tendsto (fun p ↦ b + (ω p : EReal)) atTop (𝓝 b) := by
    have h := (EReal.continuousAt_add (p := (b, 0)) (Or.inr EReal.zero_ne_bot)
      (Or.inr EReal.zero_ne_top)).tendsto.comp (tendsto_const_nhds.prodMk_nhds hzero)
    simpa only [add_zero, Function.comp_def] using h
  exact le_of_tendsto_of_tendsto (tendsto_atTop_iSup hf) hsum hbound

/-- Computable comparison of presentations bounds the lower pointwise pressure in the
target presentation by that in the source presentation. -/
private lemma lower_pressure_le_of_comparison (P Q : Presentation X)
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ)
    (A : Set ℕ) (hdata : DynamicalComparisonIn P Q T A) (x : X) :
    (pointwisePressure Q T φ A x).1 ≤ (pointwisePressure P T φ A x).1 := by
  obtain ⟨ω, _, hωzero, pω, hω⟩ := small_scale_oscillation φ hφ
  apply iSup_le_of_monotone_of_eventually_le_add _
    (fun p q hpq ↦ liminf_le_liminf (Eventually.of_forall fun n ↦
      monotone_finiteScalePressureRate_dyadic Q T φ A x n hpq)) ω hωzero _
  filter_upwards [eventually_ge_atTop pω] with p hp
  obtain ⟨c, hc⟩ :=
    exists_close_center_complexity_le P Q T hT A hdata.2.2.2.2.2 (p + 2)
  have herror : Tendsto (fun n : ℕ ↦
      (2 * Real.logb 2 (n + 1) + c) / n + ω p) atTop (𝓝 (ω p)) := by
    simpa only [zero_add] using
      (tendsto_logarithmic_overhead_div_time c).add_const (ω p)
  have htime := liminf_le_add_of_eventually_le_add
    (fun n ↦ finiteScalePressureRate Q T φ A x n (dyadicRadius p))
    (fun n ↦ finiteScalePressureRate P T φ A x n (dyadicRadius (p + 2)))
    (fun n ↦ (2 * Real.logb 2 (n + 1) + c) / n + ω p) (ω p) herror ?_
  · exact htime.trans (add_le_add
      (le_iSup (fun q ↦ liminf (fun n ↦
        finiteScalePressureRate P T φ A x n (dyadicRadius q)) atTop) (p + 2)) le_rfl)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact finiteScalePressureRate_le_add_of_transfer P Q T φ A x p n c hn (ω p)
      (hω p hp) (fun i ↦ hc n i hn)

/-- Lower pointwise pressure is invariant under a dynamical presentation change for a
uniformly continuous potential. Blueprint node `metric:change`. -/
theorem presentation_change_pressure (P Q : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) (A : Set ℕ)
    (hdata : DynamicalComparisonIn P Q T A) (x : X) :
    (pointwisePressure P T φ A x).1 = (pointwisePressure Q T φ A x).1 := by
  apply le_antisymm
  · exact lower_pressure_le_of_comparison Q P T hT φ hφ A
      hdata.symm x
  · exact lower_pressure_le_of_comparison P Q T hT φ hφ A hdata x

/-- An eventual comparison with a convergent real additive error bounds the upper limits
in `EReal`, including infinite limits. -/
private lemma limsup_le_add_of_eventually_le_add (f g : ℕ → EReal)
    (e : ℕ → ℝ) (ω : ℝ) (he : Tendsto e atTop (𝓝 ω))
    (hfg : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    limsup f atTop ≤ limsup g atTop + (ω : EReal) := by
  have he' : Tendsto (fun n ↦ (e n : EReal)) atTop (𝓝 (ω : EReal)) :=
    EReal.tendsto_coe.mpr he
  have hlimsup := he'.limsup_eq
  calc
    limsup f atTop ≤ limsup (fun n ↦ g n + (e n : EReal)) atTop :=
      limsup_le_limsup hfg
    _ ≤ limsup g atTop + (ω : EReal) := by
      have h := EReal.limsup_add_le (u := g) (v := fun n ↦ (e n : EReal))
        (f := atTop) (Or.inr (by rw [hlimsup]; exact EReal.coe_ne_top _))
        (Or.inr (by rw [hlimsup]; exact EReal.coe_ne_bot _))
      simpa only [Pi.add_def, hlimsup] using h

/-- Computable comparison of presentations bounds the upper pointwise pressure in the
target presentation by that in the source presentation. -/
private lemma upper_pressure_le_of_comparison (P Q : Presentation X)
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ)
    (A : Set ℕ) (hdata : DynamicalComparisonIn P Q T A) (x : X) :
    (pointwisePressure Q T φ A x).2 ≤ (pointwisePressure P T φ A x).2 := by
  obtain ⟨ω, _, hωzero, pω, hω⟩ := small_scale_oscillation φ hφ
  apply iSup_le_of_monotone_of_eventually_le_add _
    (fun p q hpq ↦ limsup_le_limsup (Eventually.of_forall fun n ↦
      monotone_finiteScalePressureRate_dyadic Q T φ A x n hpq)) ω hωzero _
  filter_upwards [eventually_ge_atTop pω] with p hp
  obtain ⟨c, hc⟩ :=
    exists_close_center_complexity_le P Q T hT A hdata.2.2.2.2.2 (p + 2)
  have herror : Tendsto (fun n : ℕ ↦
      (2 * Real.logb 2 (n + 1) + c) / n + ω p) atTop (𝓝 (ω p)) := by
    simpa only [zero_add] using
      (tendsto_logarithmic_overhead_div_time c).add_const (ω p)
  have htime := limsup_le_add_of_eventually_le_add
    (fun n ↦ finiteScalePressureRate Q T φ A x n (dyadicRadius p))
    (fun n ↦ finiteScalePressureRate P T φ A x n (dyadicRadius (p + 2)))
    (fun n ↦ (2 * Real.logb 2 (n + 1) + c) / n + ω p) (ω p) herror ?_
  · exact htime.trans (add_le_add
      (le_iSup (fun q ↦ limsup (fun n ↦
        finiteScalePressureRate P T φ A x n (dyadicRadius q)) atTop) (p + 2)) le_rfl)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact finiteScalePressureRate_le_add_of_transfer P Q T φ A x p n c hn (ω p)
      (hω p hp) (fun i ↦ hc n i hn)

/-- Upper pointwise pressure is invariant under a dynamical presentation change for a
uniformly continuous potential. Blueprint node `metric:change`. -/
theorem presentation_change_pressure_upper (P Q : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : X → ℝ) (hφ : UniformContinuous φ) (A : Set ℕ)
    (hdata : DynamicalComparisonIn P Q T A) (x : X) :
    (pointwisePressure P T φ A x).2 = (pointwisePressure Q T φ A x).2 := by
  apply le_antisymm
  · exact upper_pressure_le_of_comparison Q P T hT φ hφ A
      hdata.symm x
  · exact upper_pressure_le_of_comparison P Q T hT φ hφ A hdata x

end Kolmogorov.PointToSet
