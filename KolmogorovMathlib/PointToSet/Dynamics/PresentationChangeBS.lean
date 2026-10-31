/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics.PointwiseQuantities

/-!
# Presentation independence of pointwise Barreira–Schmeling dimensions

The finite-scale Barreira–Schmeling cost divides oracle complexity by a positive Birkhoff
sum. This module proves that the lower and upper pointwise dimensions are invariant under
computably comparable metric presentations on the positive-average locus
(blueprint node `metric:change`).
Center translation and uniform continuity control the change of numerator and denominator;
sublinear errors disappear in the time and scale limits. The results make the effective
dimensions used in the point-to-set principles independent of these presentation choices.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- A positive lower Birkhoff average supplies one positive linear lower bound on the
Birkhoff sums, uniformly over all points in sufficiently fine Bowen balls around `x` and
all sufficiently late positive orders. -/
private lemma exists_linear_birkhoffSum_lower_bound (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ p₀ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ p ≥ p₀, ∀ n ≥ N₀, ∀ y ∈ bowenBall T n x (dyadicRadius p),
        ρ * (n : ℝ) ≤ birkhoffSum T u n y := by
  obtain ⟨r, hr, hrx⟩ := EReal.exists_between_coe_real hx
  have hrpos : 0 < r := EReal.coe_pos.mp hr
  obtain ⟨ω, hωpos, hωzero, pω, hω⟩ := small_scale_oscillation u hu
  have hevω : ∀ᶠ p in atTop, ω p < r / 2 :=
    hωzero.eventually (gt_mem_nhds (half_pos hrpos))
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp hevω
  have hev := eventually_lt_of_lt_liminf hrx
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨r / 2, half_pos hrpos, max pω p₁, max N 1, le_max_right _ _, ?_⟩
  intro p hp n hn y hy
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hbase : r * (n : ℝ) < birkhoffSum T u n x :=
    (lt_div_iff₀ hnpos).mp (EReal.coe_lt_coe_iff.mp (hN n (by omega)))
  have hosc := small_scale_oscillation_birkhoff T u p (ω p)
    (hω p (by omega)) n x y hy
  have hsmall := hp₁ p (by omega)
  have hdiff := (abs_le.mp hosc).1
  nlinarith

/-- At a fixed dyadic precision, effective search in mixed Bowen distances transfers each
positive-order ideal center of `P` to an ideal center of `Q` with logarithmic time overhead
in the oracle complexity. The constant is uniform in both the old index and the orbit
length. -/
private lemma exists_close_center_with_complexity_bound (P Q : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A
      (fun nij : ℕ × ℕ × ℕ => bowenDist T nij.1 (P.ι nij.2.1) (Q.ι nij.2.2)))
    (p : ℕ) :
    ∃ c : ℕ, ∀ n i, 1 ≤ n → ∃ j,
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius (p + 2) ∧
        (oracleNatComplexity A j : ℝ) ≤
          oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c := by
  classical
  obtain ⟨q, hq, hqerr⟩ := hmixed
  let r : ℚ := (2 : ℚ)⁻¹ ^ (p + 2)
  have hr : (r : ℝ) = dyadicRadius (p + 2) := by
    norm_num only [r, dyadicRadius, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
  let test : (ℕ × ℕ) → ℕ → Option ℕ := fun v k =>
    if q ((v.2, v.1, (Nat.unpair k).1), (Nat.unpair k).2) +
        (2 : ℚ)⁻¹ ^ (Nat.unpair k).2 < r then some (Nat.unpair k).1 else none
  let E : ℕ × ℕ →. ℕ := fun v => Nat.rfindOpt (test v)
  have hu : Computable (fun w : (ℕ × ℕ) × ℕ => Nat.unpair w.2) :=
    Primrec.unpair.to_comp.comp Computable.snd
  have hjcomp := Computable.fst.comp hu
  have htcomp := Computable.snd.comp hu
  have harg : Computable (fun w : (ℕ × ℕ) × ℕ =>
      ((w.1.2, w.1.1, (Nat.unpair w.2).1), (Nat.unpair w.2).2)) :=
    ((Computable.snd.comp Computable.fst).pair
      ((Computable.fst.comp Computable.fst).pair hjcomp)).pair htcomp
  have hqcomp := hq.comp harg.computableIn
  have heps : Computable (fun t : ℕ => (2 : ℚ)⁻¹ ^ t) :=
    computable_rat_inv_two_pow.of_eq (fun t => by simp only [inv_pow])
  have hsum := (Computable₂.computableIn₂ computable₂_ratAdd).comp hqcomp
    (heps.comp htcomp).computableIn
  have hcmp := (Computable₂.computableIn₂ computable₂_ratLt).comp hsum
    (Computable.const r).computableIn
  have htest : ComputableIn {charOracle A}
      (fun w : (ℕ × ℕ) × ℕ => test w.1 w.2) := by
    have h := computable_in_cond hcmp (Computable.option_some.comp hjcomp).computableIn
      (Computable.const (none : Option ℕ)).computableIn
    simpa only [Bool.cond_decide] using h
  have hE : PartrecIn {charOracle A} E := PartrecIn.rfindOpt htest.to₂
  have hsound : ∀ i n j, j ∈ E (i, n) →
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius (p + 2) := by
    intro i n j hj
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hj
    dsimp [test] at hk
    split_ifs at hk with hcmp
    · simp only [Option.mem_def, Option.some.injEq] at hk
      subst j
      have hcmpR : (q ((n, i, (Nat.unpair k).1), (Nat.unpair k).2) : ℝ) +
          (2 : ℝ)⁻¹ ^ (Nat.unpair k).2 < dyadicRadius (p + 2) := by
        have h := (Rat.cast_lt (K := ℝ)).mpr hcmp
        push_cast at h
        rwa [hr] at h
      have herr := (abs_lt.mp (hqerr (n, i, (Nat.unpair k).1) (Nat.unpair k).2)).1
      linarith
    · simp at hk
  have htotal : ∀ i n, 1 ≤ n → (E (i, n)).Dom := by
    intro i n hn
    obtain ⟨j, hj⟩ := bowen_ball_dense Q T hT (P.ι i) n hn
      (dyadicRadius (p + 2)) (by dsimp [dyadicRadius]; positivity)
    have hd := (bowen_ball_dense_iff T n hn (P.ι i) (Q.ι j) _).mp hj
    obtain ⟨t, ht⟩ := exists_two_mul_inv_two_pow_lt
      (dyadicRadius (p + 2) - bowenDist T n (P.ι i) (Q.ι j)) (sub_pos.mpr hd)
    have hcmp : q ((n, i, j), t) + (2 : ℚ)⁻¹ ^ t < r := by
      apply (Rat.cast_lt (K := ℝ)).mp
      push_cast
      rw [hr]
      have ht' : 2 * (2 : ℝ)⁻¹ ^ t <
          dyadicRadius (p + 2) - bowenDist T n (P.ι i) (Q.ι j) := by
        simpa only [inv_pow] using ht
      have herr := (abs_lt.mp (hqerr (n, i, j) t)).2
      linarith
    apply Nat.rfindOpt_dom.mpr
    exact ⟨Nat.pair j t, j, by
      simp only [test, Nat.unpair_pair, ite_eq_left hcmp, Option.mem_def]⟩
  let decode : List BitString → ℕ × ℕ := fun ws =>
    (decodeBits (decodeFirst (ws.getD 0 [])), decodeBits (decodeSecond (ws.getD 0 [])))
  have hget : Computable (fun ws : List BitString => ws.getD 0 []) :=
    Computable₂.comp (f := fun (l : List BitString) (n : ℕ) => l.getD n [])
      (Primrec.list_getD ([] : BitString)).to_comp Computable.id (Computable.const 0)
  have hdecode : Computable decode :=
    (decodeBits_computable.comp (decodeFirst_computable.comp hget)).pair
      (decodeBits_computable.comp (decodeSecond_computable.comp hget))
  let F : List BitString →. BitString := fun ws => (E (decode ws)).map natBits
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

/-- Elementary ratio estimate: if `a ≤ c * b` and `l ≤ k + e`, then `l / b` is bounded by
the multiplicative perturbation `c * (k / a)` plus the additive error `e / d`, where `d` is
a positive lower bound of the common denominator `b`. -/
private lemma div_le_mul_div_add_div (a b k l c d e : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hdb : d ≤ b) (hk : 0 ≤ k) (he : 0 ≤ e)
    (hab : a ≤ c * b) (hkl : l ≤ k + e) :
    l / b ≤ c * (k / a) + e / d := by
  have hb : 0 < b := hd.trans_le hdb
  calc
    l / b ≤ (k + e) / b := div_le_div_of_nonneg_right hkl hb.le
    _ = k / b + e / b := add_div _ _ _
    _ ≤ c * (k / a) + e / d := by
      apply add_le_add
      · rw [← mul_div_assoc, div_le_div_iff₀ hb ha]
        nlinarith [mul_le_mul_of_nonneg_left hab hk]
      · exact div_le_div_of_nonneg_left he hd hdb

/-- Comparison of finite-scale Barreira–Schmeling costs at one orbit length: given a
positive linear denominator bound, an oscillation bound `ω` and a center transfer with
logarithmic overhead, the cost for `Q` at radius `dyadicRadius p` is at most the factor
`1 + ω / ρ` times the cost for `P` at radius `dyadicRadius (p + 2)`, plus the overhead
divided by `ρ * n`. Both the denominator bound and the oscillation bound apply at the
target radius; the source and center-transfer radii are one quarter as large. -/
private lemma finiteScaleBSCost_le_of_center_transfer (P Q : Presentation X)
    (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) (p n c : ℕ)
    (hn : 1 ≤ n) (ρ ω : ℝ) (hρ : 0 < ρ) (hωnonneg : 0 ≤ ω)
    (hdenom : ∀ y ∈ bowenBall T n x (dyadicRadius p),
      ρ * (n : ℝ) ≤ birkhoffSum T u n y)
    (hω : ∀ y z, dist y z < 2 * dyadicRadius p → |u y - u z| ≤ ω)
    (htransfer : ∀ i, ∃ j,
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius (p + 2) ∧
        (oracleNatComplexity A j : ℝ) ≤
          oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c) :
    finiteScaleBSCost Q T u A x n (dyadicRadius p) ≤
      ENNReal.ofReal (1 + ω / ρ) *
          finiteScaleBSCost P T u A x n (dyadicRadius (p + 2)) +
        ENNReal.ofReal ((2 * Real.logb 2 (n + 1) + c) / (ρ * n)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlin : 0 < ρ * (n : ℝ) := mul_pos hρ hnpos
  have hfac : 0 < 1 + ω / ρ := by positivity
  have hfac0 : ENNReal.ofReal (1 + ω / ρ) ≠ 0 := by positivity
  have hlog : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hover : 0 ≤ 2 * Real.logb 2 ((n : ℝ) + 1) + c := by positivity
  unfold finiteScaleBSCost
  rw [ite_eq_right hn0, ite_eq_right hn0]
  simp_rw [ENNReal.mul_iInf_of_ne hfac0 ENNReal.ofReal_ne_top, ENNReal.iInf_add]
  refine le_iInf fun i => le_iInf fun hi => le_iInf fun hpos => ?_
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
  have hjden := hdenom (Q.ι j) hjball
  have hjpos : 0 < birkhoffSum T u n (Q.ι j) := hlin.trans_le hjden
  have hjold : Q.ι j ∈ bowenBall T n (P.ι i) (dyadicRadius p) :=
    (bowen_ball_dense_iff T n hn (P.ι i) (Q.ι j) _).mpr (hclose.trans_le hradius)
  have hosc := small_scale_oscillation_birkhoff T u p ω hω n (P.ι i) (Q.ι j) hjold
  have hperturb : birkhoffSum T u n (P.ι i) ≤
      (1 + ω / ρ) * birkhoffSum T u n (Q.ι j) := by
    have hmult := mul_le_mul_of_nonneg_left hjden (div_nonneg hωnonneg hρ.le)
    have hcancel : ω / ρ * (ρ * (n : ℝ)) = (n : ℝ) * ω := by
      field_simp
    rw [hcancel] at hmult
    have hdiff := (abs_le.mp hosc).1
    nlinarith
  have hratio := div_le_mul_div_add_div
    (birkhoffSum T u n (P.ι i)) (birkhoffSum T u n (Q.ι j))
    (oracleNatComplexity A i) (oracleNatComplexity A j) (1 + ω / ρ)
    (ρ * n) (2 * Real.logb 2 (n + 1) + c) hpos hlin hjden
    (Nat.cast_nonneg _) hover hperturb (by linarith [hcomplex])
  refine (iInf_le_of_le j (iInf_le_of_le hjball (iInf_le_of_le hjpos le_rfl))).trans ?_
  have hcast := ENNReal.ofReal_le_ofReal hratio
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul hfac.le, ENNReal.ofReal_div_of_pos hjpos,
    ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast] at hcast
  exact hcast

/-- Logarithmic coding overhead divided by a positive linear denominator tends to zero in
`ℝ≥0∞`. -/
private lemma tendsto_ofReal_logb_overhead_div_linear (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ =>
      ENNReal.ofReal ((2 * Real.logb 2 (n + 1) + c) / (ρ * n))) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2)
    ρ (-ρ) 1 hρ.ne').comp hshift
  have hlog' : Tendsto (fun n : ℕ => Real.logb 2 (n + 1) / (ρ * n))
      atTop (𝓝 0) := by
    convert hlog using 1
    simp only [pow_one]
    funext n
    congr 1
    ring
  have hc : Tendsto (fun n : ℕ => (c : ℝ) / (ρ * n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hρ)
  have hreal := (hlog'.const_mul 2).add hc
  have hreal' : Tendsto (fun n : ℕ =>
      (2 * Real.logb 2 (n + 1) + c) / (ρ * n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add, mul_zero, add_div, mul_div_assoc] using hreal
  simpa only [ENNReal.ofReal_zero, Function.comp_def] using
    ENNReal.continuous_ofReal.tendsto 0 |>.comp hreal'

/-- Removing a vanishing additive error from a lower limit: if `f ≤ c * g + e` eventually,
with `c` positive and finite and `e → 0`, then `liminf f ≤ c * liminf g`. This is an order
comparison in `ℝ≥0∞`, valid also at infinity. -/
private lemma liminf_le_mul_liminf_of_le_mul_add (f g e : ℕ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (he : Tendsto e atTop (𝓝 0))
    (hfg : ∀ᶠ n in atTop, f n ≤ c * g n + e n) :
    liminf f atTop ≤ c * liminf g atTop := by
  calc
    liminf f atTop ≤ liminf (fun n => c * g n + e n) atTop := liminf_le_liminf hfg
    _ = liminf (fun n => c * g n) atTop :=
      ENNReal.liminf_add_of_right_tendsto_zero he _
    _ ≤ c * liminf g atTop := by
      have h := ENNReal.liminf_mul_le (u := fun _ : ℕ => c) (v := g)
        (f := atTop) (by simpa using Or.inl hc0) (by simpa using Or.inl hctop)
      simpa only [Pi.mul_def, limsup_const] using h

/-- A monotone sequence in `ℝ≥0∞` that is eventually bounded by factors tending to one
times a fixed `b` has supremum at most `b`. -/
private lemma iSup_le_of_tendsto_one_mul_bound (f : ℕ → ℝ≥0∞)
    (hf : Monotone f) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 1)) (b : ℝ≥0∞)
    (hbound : ∀ᶠ p in atTop, f p ≤ ENNReal.ofReal (a p) * b) :
    (⨆ p, f p) ≤ b := by
  have hfactor : Tendsto (fun p => ENNReal.ofReal (a p)) atTop (𝓝 1) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto 1 |>.comp ha
  have hprod := ENNReal.Tendsto.mul_const (b := b) hfactor (Or.inl one_ne_zero)
  have hlim := tendsto_atTop_iSup hf
  simpa only [one_mul] using le_of_tendsto_of_tendsto hlim hprod hbound

/-- The lower time limits of the finite-scale Barreira–Schmeling costs form a monotone
sequence in `p`, as the dyadic radii `dyadicRadius p` decrease. -/
private lemma monotone_liminf_finiteScaleBSCost (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) :
    Monotone (fun p => liminf
      (fun n => finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop) := by
  intro p q hpq
  apply liminf_le_liminf (Eventually.of_forall fun n => ?_)
  unfold finiteScaleBSCost
  split_ifs
  · exact le_rfl
  · apply iInf_mono
    intro i
    apply iInf_mono'
    intro hi
    refine ⟨?_, le_rfl⟩
    exact Dynamics.dynEntourage_monotone T n
      (fun z hz => lt_of_lt_of_le hz
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hpq)) hi

/-- One direction of the invariance of the lower pointwise Barreira–Schmeling dimension:
a uniform linear denominator bound and, at every dyadic precision, a center transfer from
`P` to `Q` with logarithmic overhead give
`(pointwiseBSDimension Q T u A x).1 ≤ (pointwiseBSDimension P T u A x).1`. -/
private lemma pointwiseBSDimension_lower_le_of_transfer (P Q : Presentation X)
    (T : X → X) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) (x : X)
    (ρ : ℝ) (hρ : 0 < ρ) (p₀ N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hdenom : ∀ p ≥ p₀, ∀ n ≥ N₀, ∀ y ∈ bowenBall T n x (dyadicRadius p),
      ρ * (n : ℝ) ≤ birkhoffSum T u n y)
    (htransfer : ∀ p : ℕ, ∃ c : ℕ, ∀ n i, 1 ≤ n → ∃ j,
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius (p + 2) ∧
        (oracleNatComplexity A j : ℝ) ≤
          oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c) :
    (pointwiseBSDimension Q T u A x).1 ≤ (pointwiseBSDimension P T u A x).1 := by
  obtain ⟨ω, hωpos, hωzero, pω, hω⟩ := small_scale_oscillation u hu
  have hfactor : Tendsto (fun p => 1 + ω p / ρ) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hωzero.div_const ρ)
  apply iSup_le_of_tendsto_one_mul_bound _
    (monotone_liminf_finiteScaleBSCost Q T u A x) _ hfactor _
  filter_upwards [eventually_ge_atTop (max p₀ pω)] with p hp
  obtain ⟨c, hc⟩ := htransfer p
  have hωp := hωpos p
  have hfacpos : 0 < 1 + ω p / ρ := by positivity
  have htime := liminf_le_mul_liminf_of_le_mul_add
    (fun n => finiteScaleBSCost Q T u A x n (dyadicRadius p))
    (fun n => finiteScaleBSCost P T u A x n (dyadicRadius (p + 2)))
    (fun n => ENNReal.ofReal ((2 * Real.logb 2 (n + 1) + c) / (ρ * n)))
    (ENNReal.ofReal (1 + ω p / ρ)) (by positivity) ENNReal.ofReal_ne_top
    (tendsto_ofReal_logb_overhead_div_linear c ρ hρ) ?_
  · exact htime.trans (mul_le_mul' le_rfl
      (le_iSup (fun q => liminf (fun n =>
        finiteScaleBSCost P T u A x n (dyadicRadius q)) atTop) (p + 2)))
  · filter_upwards [eventually_ge_atTop N₀] with n hn
    exact finiteScaleBSCost_le_of_center_transfer P Q T u A x p n c (hN₀.trans hn)
      ρ (ω p) hρ (hωpos p).le (hdenom p (by omega) n hn)
      (hω p (by omega)) (fun i => hc n i (hN₀.trans hn))

/-- Lower pointwise BS dimension is presentation invariant on the positive-average locus
of a uniformly continuous potential. Blueprint node `metric:change`. -/
theorem presentation_change_bs (P Q : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hdata : DynamicalComparisonIn P Q T A) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    (pointwiseBSDimension P T u A x).1 = (pointwiseBSDimension Q T u A x).1 := by
  obtain ⟨ρ, hρ, p₀, N₀, hN₀, hdenom⟩ :=
    exists_linear_birkhoffSum_lower_bound T u hu x hx
  have hsymm := hdata.symm
  apply le_antisymm
  · exact pointwiseBSDimension_lower_le_of_transfer Q P T u hu A x ρ hρ p₀ N₀ hN₀ hdenom
      (exists_close_center_with_complexity_bound Q P T hT A hsymm.2.2.2.2.2)
  · exact pointwiseBSDimension_lower_le_of_transfer P Q T u hu A x ρ hρ p₀ N₀ hN₀ hdenom
      (exists_close_center_with_complexity_bound P Q T hT A hdata.2.2.2.2.2)

/-- Removing a vanishing additive error from an upper limit: if `f ≤ c * g + e` eventually,
with `c` positive and finite and `e → 0`, then `limsup f ≤ c * limsup g`. This is an order
comparison in `ℝ≥0∞`, valid also at infinity. -/
private lemma limsup_le_mul_limsup_of_le_mul_add (f g e : ℕ → ℝ≥0∞)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (he : Tendsto e atTop (𝓝 0))
    (hfg : ∀ᶠ n in atTop, f n ≤ c * g n + e n) :
    limsup f atTop ≤ c * limsup g atTop := by
  calc
    limsup f atTop ≤ limsup (fun n => c * g n + e n) atTop := limsup_le_limsup hfg
    _ = limsup (fun n => c * g n) atTop :=
      ENNReal.limsup_add_of_right_tendsto_zero he _
    _ ≤ c * limsup g atTop := by
      have h := ENNReal.limsup_mul_le' (u := fun _ : ℕ => c) (v := g)
        (f := atTop) (by simpa using Or.inl hc0) (by simpa using Or.inl hctop)
      simpa only [Pi.mul_def, limsup_const] using h

/-- The upper time limits of the finite-scale Barreira–Schmeling costs form a monotone
sequence in `p`, as the dyadic radii `dyadicRadius p` decrease. -/
private lemma monotone_limsup_finiteScaleBSCost (P : Presentation X)
    (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) :
    Monotone (fun p => limsup
      (fun n => finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop) := by
  intro p q hpq
  apply limsup_le_limsup (Eventually.of_forall fun n => ?_)
  unfold finiteScaleBSCost
  split_ifs
  · exact le_rfl
  · apply iInf_mono
    intro i
    apply iInf_mono'
    intro hi
    refine ⟨?_, le_rfl⟩
    exact Dynamics.dynEntourage_monotone T n
      (fun z hz => lt_of_lt_of_le hz
        (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hpq)) hi

/-- One direction of the invariance of the upper pointwise Barreira–Schmeling dimension:
a uniform linear denominator bound and, at every dyadic precision, a center transfer from
`P` to `Q` with logarithmic overhead give
`(pointwiseBSDimension Q T u A x).2 ≤ (pointwiseBSDimension P T u A x).2`. -/
private lemma pointwiseBSDimension_upper_le_of_transfer (P Q : Presentation X)
    (T : X → X) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ) (x : X)
    (ρ : ℝ) (hρ : 0 < ρ) (p₀ N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hdenom : ∀ p ≥ p₀, ∀ n ≥ N₀, ∀ y ∈ bowenBall T n x (dyadicRadius p),
      ρ * (n : ℝ) ≤ birkhoffSum T u n y)
    (htransfer : ∀ p : ℕ, ∃ c : ℕ, ∀ n i, 1 ≤ n → ∃ j,
      bowenDist T n (P.ι i) (Q.ι j) < dyadicRadius (p + 2) ∧
        (oracleNatComplexity A j : ℝ) ≤
          oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c) :
    (pointwiseBSDimension Q T u A x).2 ≤ (pointwiseBSDimension P T u A x).2 := by
  obtain ⟨ω, hωpos, hωzero, pω, hω⟩ := small_scale_oscillation u hu
  have hfactor : Tendsto (fun p => 1 + ω p / ρ) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hωzero.div_const ρ)
  apply iSup_le_of_tendsto_one_mul_bound _
    (monotone_limsup_finiteScaleBSCost Q T u A x) _ hfactor _
  filter_upwards [eventually_ge_atTop (max p₀ pω)] with p hp
  obtain ⟨c, hc⟩ := htransfer p
  have hωp := hωpos p
  have hfacpos : 0 < 1 + ω p / ρ := by positivity
  have htime := limsup_le_mul_limsup_of_le_mul_add
    (fun n => finiteScaleBSCost Q T u A x n (dyadicRadius p))
    (fun n => finiteScaleBSCost P T u A x n (dyadicRadius (p + 2)))
    (fun n => ENNReal.ofReal ((2 * Real.logb 2 (n + 1) + c) / (ρ * n)))
    (ENNReal.ofReal (1 + ω p / ρ)) (by positivity) ENNReal.ofReal_ne_top
    (tendsto_ofReal_logb_overhead_div_linear c ρ hρ) ?_
  · exact htime.trans (mul_le_mul' le_rfl
      (le_iSup (fun q => limsup (fun n =>
        finiteScaleBSCost P T u A x n (dyadicRadius q)) atTop) (p + 2)))
  · filter_upwards [eventually_ge_atTop N₀] with n hn
    exact finiteScaleBSCost_le_of_center_transfer P Q T u A x p n c (hN₀.trans hn)
      ρ (ω p) hρ (hωpos p).le (hdenom p (by omega) n hn)
      (hω p (by omega)) (fun i => hc n i (hN₀.trans hn))

/-- Upper pointwise BS dimension is presentation invariant on that positive-average locus.
Blueprint node `metric:change`. -/
theorem presentation_change_bs_upper (P Q : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hdata : DynamicalComparisonIn P Q T A) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) :
    (pointwiseBSDimension P T u A x).2 = (pointwiseBSDimension Q T u A x).2 := by
  obtain ⟨ρ, hρ, p₀, N₀, hN₀, hdenom⟩ :=
    exists_linear_birkhoffSum_lower_bound T u hu x hx
  have hsymm := hdata.symm
  apply le_antisymm
  · exact pointwiseBSDimension_upper_le_of_transfer Q P T u hu A x
      ρ hρ p₀ N₀ hN₀ hdenom
      (exists_close_center_with_complexity_bound Q P T hT A hsymm.2.2.2.2.2)
  · exact pointwiseBSDimension_upper_le_of_transfer P Q T u hu A x
      ρ hρ p₀ N₀ hN₀ hdenom
      (exists_close_center_with_complexity_bound P Q T hT A hdata.2.2.2.2.2)

end Kolmogorov.PointToSet
