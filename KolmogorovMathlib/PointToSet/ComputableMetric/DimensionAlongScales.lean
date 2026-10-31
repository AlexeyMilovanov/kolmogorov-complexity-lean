/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.StaticDimensions

/-!
# Invariance of static point dimensions: scales and presentations

The static lower and upper point dimensions `staticPointDimensions P A x` of a point `x`
relative to an oracle `A` are the `liminf` and `limsup`, as the radius `r` tends to zero from
above, of the normalized precision complexity `K^A_r(x) / (-log₂ r)`, where `K^A_r(x)` is the
least oracle complexity of an ideal point of the presentation `P` within distance `r` of `x`.
This file proves two invariance properties of these dimensions.

* `dimension_along_scales` and `dimension_along_scales_upper` (blueprint node
  `metric:sampling`): both dimensions can be computed along any positive scale sequence
  `δ` tending to zero with `log δ (m + 1) / log δ m → 1`, without assuming monotonicity.
  The precision cost is antitone in the radius, so each radius is bracketed by two
  consecutive scales.
* `presentation_change_packing` (blueprint node `metric:change`): the static upper dimension
  does not depend on the dense sequence, provided the oracle computes the mixed distances
  between the ideal points of the two presentations.  An ideal point of one presentation is
  translated to one of the other at dyadic precision by a search through the mixed
  distances, which costs a logarithmic overhead in the precision.

These facts are the static base of the change-of-presentation results for dynamical
quantities, and of the computation of dimensions along dyadic scales used by the
point-to-set principles.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- Searching the mixed rational distance approximations gives an oracle-computable
translator of an ideal index and a dyadic precision into an index of the other presentation
whose ideal point is closer than that precision. -/
private lemma exists_translator_of_computable_mixed_dist
    (P Q : Presentation X) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A
      (fun ij : ℕ × ℕ => dist (P.ι ij.1) (Q.ι ij.2))) :
    ∃ F : ℕ × ℕ →. ℕ, PartrecIn {charOracle A} F ∧
      ∀ i p, ∃ j ∈ F (i, p), dist (Q.ι j) (P.ι i) < dyadicRadius p := by
  rcases hmixed with ⟨q, hq, hqerr⟩
  have hr : Computable (fun p : ℕ => (2 : ℚ)⁻¹ ^ (p + 1)) := by
    have hc := ComputableReals.computable_invSucc.comp
      ((Primrec.nat_sub.comp
        (primrec_two_pow_aux.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))
        (Primrec.const 1)).to_comp)
    refine hc.of_eq fun p => ?_
    have hpos : 0 < (2 : ℕ) ^ (p + 1) := by positivity
    have heq : ((2 ^ (p + 1) - 1 : ℕ) : ℚ) + 1 = (2 : ℚ) ^ (p + 1) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    change 1 / (((2 ^ (p + 1) - 1 : ℕ) : ℚ) + 1) = _
    rw [heq, one_div, inv_pow]
  let test (ip : ℕ × ℕ) (j : ℕ) : Bool :=
    decide (q ((ip.1, j), ip.2 + 2) < (2 : ℚ)⁻¹ ^ (ip.2 + 1))
  have ht : ComputableIn₂ {charOracle A} test := by
    have hi : Computable (fun z : (ℕ × ℕ) × ℕ => ((z.1.1, z.2), z.1.2 + 2)) :=
      ((Computable.fst.comp Computable.fst).pair Computable.snd).pair
        ((Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 2)).to_comp)
    have hleft := hq.comp hi.computableIn
    have hright : ComputableIn {charOracle A}
        (fun z : (ℕ × ℕ) × ℕ => (2 : ℚ)⁻¹ ^ (z.1.2 + 1)) :=
      hr.computableIn.comp (Computable.snd.comp Computable.fst).computableIn
    exact (ComputableReals.primrec_ratLt.decide.to_comp.computableIn.comp
      (hleft.pair hright)).to₂
  refine ⟨fun ip => Nat.rfind (fun j => Part.some (test ip j)),
    PartrecIn.rfind ht.partrecIn₂, ?_⟩
  intro i p
  have hpos : 0 < dyadicRadius (p + 2) := by
    unfold dyadicRadius
    positivity
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp Q.dense (P.ι i) _ hpos
  have hex : ∃ j, test (i, p) j = true := by
    refine ⟨j, ?_⟩
    dsimp [test]
    rw [decide_eq_true_eq]
    have herr := (abs_lt.mp (hqerr (i, j) (p + 2))).2
    have hlt : (q ((i, j), p + 2) : ℝ) < (2 : ℝ)⁻¹ ^ (p + 1) := by
      dsimp [dyadicRadius] at hj
      simp only [pow_succ] at hj herr ⊢
      norm_num at hj herr ⊢
      linarith
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] using hlt
  obtain ⟨j, hjtest⟩ := hex
  have hdom : (Nat.rfind (fun j => Part.some (test (i, p) j))).Dom := by
    apply Nat.rfind_dom.mpr
    exact ⟨j, by simp [hjtest], fun _ => trivial⟩
  obtain ⟨j, hjmem⟩ := Part.dom_iff_mem.mp hdom
  refine ⟨j, hjmem, ?_⟩
  have htest := Nat.rfind_spec hjmem
  have hlt : (q ((i, j), p + 2) : ℝ) < (2 : ℝ)⁻¹ ^ (p + 1) := by
    have h : q ((i, j), p + 2) < (2 : ℚ)⁻¹ ^ (p + 1) := by
      simpa [test] using htest
    have hh := (Rat.cast_lt (K := ℝ)).mpr h
    simpa only [Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat] using hh
  have herr := (abs_lt.mp (hqerr (i, j) (p + 2))).1
  rw [dist_comm]
  dsimp [dyadicRadius]
  simp only [pow_succ] at hlt herr
  norm_num at hlt herr
  linarith [pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) p]

/-- Applying a fixed relative partial translator to an encoded pair adds at most a constant
to the pair complexity, and supplying the precision costs at most twice its binary
logarithm. -/
private lemma complexity_le_of_mem_translator (A : Set ℕ)
    (F : ℕ × ℕ →. ℕ) (hF : PartrecIn {charOracle A} F) :
    ∃ c : ℕ, ∀ i p j, j ∈ F (i, p) →
      (oracleNatComplexity A j : ℝ) ≤
        oracleNatComplexity A i + 2 * Real.logb 2 (p + 1) + c := by
  let G : List BitString →. BitString := fun ws =>
    (F (decodeBits (decodeFirst (ws.headD [])),
      decodeBits (decodeSecond (ws.headD [])))).map natBits
  have hg : PartrecIn {charOracle A} G := by
    have hd : Computable (fun ws : List BitString => ws.headD []) :=
      (Computable.option_getD Primrec.list_head?.to_comp (Computable.const [])).of_eq
        (fun ws => by cases ws <;> rfl)
    have hi := decodeBits_computable.comp
      (CodedFiniteDistribution.decodeFirst_primrec.to_comp.comp hd)
    have hp := decodeBits_computable.comp
      (CodedFiniteDistribution.decodeSecond_primrec.to_comp.comp hd)
    exact (hF.comp (hi.pair hp).computableIn).map
      (natBits_computable.comp Computable.snd).computableIn.to₂
  obtain ⟨c₁, hc₁⟩ := oracle_tuple_bounds_composition A 1 G hg
  obtain ⟨c₂, hc₂⟩ := oracle_tuple_bounds_overhead A
  refine ⟨c₁ + c₂, ?_⟩
  intro i p j hj
  have hmem : natBits j ∈ G [pairCode (natBits i) (natBits p)] := by
    simpa [G, decodeFirst_pairCode, decodeSecond_pairCode, natBits] using
      Part.mem_map natBits hj
  have hc := hc₁ [pairCode (natBits i) (natBits p)] (natBits j) rfl hmem
  have hn : oracleNatComplexity A j ≤ oraclePairComplexity A i p + c₁ := by
    simpa [oracleNatComplexity, oraclePairComplexity] using hc
  have hr : (oracleNatComplexity A j : ℝ) ≤ oraclePairComplexity A i p + c₁ := by
    exact_mod_cast hn
  have hb := hc₂ i p
  push_cast
  linarith

/-- The precision complexity of a point is antitone in the radius, as a natural number. -/
private lemma precisionComplexityNat_antitone (P : Presentation X) (A : Set ℕ) (x : X)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    precisionComplexityNat P A x s ≤ precisionComplexityNat P A x r := by
  obtain ⟨i, _, hi⟩ := staticPointDimensions_attained P A x r hr
  exact ENat.toNat_le_toNat (staticPointDimensions_antitone P A x hrs)
    (by rw [hi]; exact ENat.natCast_ne_top _)

/-- Translating an attaining center at precision `p + 1` with a translator of logarithmic
cost places its image inside radius `dyadicRadius p`, by the triangle inequality. -/
private lemma precisionComplexityNat_le_of_translation_cost
    (P Q : Presentation X) (A : Set ℕ) (x : X) (c : ℕ)
    (hcost : ∀ i p, ∃ j, dist (Q.ι j) (P.ι i) < dyadicRadius p ∧
      (oracleNatComplexity A j : ℝ) ≤
        oracleNatComplexity A i + 2 * Real.logb 2 (p + 1) + c) :
    ∀ p : ℕ, (precisionComplexityNat Q A x (dyadicRadius p) : ℝ) ≤
      precisionComplexityNat P A x (dyadicRadius (p + 1)) +
        2 * Real.logb 2 (p + 2) + c := by
  intro p
  obtain ⟨i, hi, heq⟩ := staticPointDimensions_attained P A x
    (dyadicRadius (p + 1)) (by unfold dyadicRadius; positivity)
  obtain ⟨j, hj, hjcost⟩ := hcost i (p + 1)
  have hdist : dist (Q.ι j) x < dyadicRadius p := by
    have htri := (dist_triangle (Q.ι j) (P.ι i) x).trans_lt (add_lt_add hj hi)
    dsimp [dyadicRadius] at htri ⊢
    simp only [pow_succ] at htri
    norm_num at htri
    linarith
  have hprec : precisionComplexityNat Q A x (dyadicRadius p) ≤ oracleNatComplexity A j := by
    have hb : precisionComplexity Q A x (dyadicRadius p) ≤
        (oracleNatComplexity A j : ENat) := by
      unfold precisionComplexity
      exact iInf_le_of_le j (iInf_le_of_le hdist le_rfl)
    exact (ENat.toNat_le_toNat hb (ENat.natCast_ne_top _)).trans_eq
      (ENat.toNat_natCast _)
  have hpeq : precisionComplexityNat P A x (dyadicRadius (p + 1)) =
      oracleNatComplexity A i := by
    simp [precisionComplexityNat, heq]
  rw [hpeq]
  have hcast : (precisionComplexityNat Q A x (dyadicRadius p) : ℝ) ≤
      oracleNatComplexity A j := by exact_mod_cast hprec
  norm_num [Nat.cast_add, add_assoc] at hjcost
  simpa only [add_assoc] using hcast.trans hjcost

/-- Rounding a logarithmic precision up changes its ratio by a factor tending to one, and
the logarithmic coding overhead divided by that precision tends to zero. -/
private lemma tendsto_ceil_precision_errors (c : ℕ) :
    Tendsto (fun u : ℝ => ENNReal.ofReal (((⌈u⌉₊ : ℝ) + 1) / u)) atTop (𝓝 1) ∧
      Tendsto (fun u : ℝ =>
        ENNReal.ofReal ((2 * Real.logb 2 ((⌈u⌉₊ : ℝ) + 2) + c) / u)) atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℝ => ⌈u⌉₊) atTop atTop := tendsto_nat_ceil_atTop
  have hinv : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hceil : Tendsto (fun u : ℝ => (⌈u⌉₊ : ℝ) / u) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop
  have haReal : Tendsto (fun u : ℝ => ((⌈u⌉₊ : ℝ) + 1) / u) atTop (𝓝 1) := by
    simpa only [add_div, one_div, add_zero] using hceil.add hinv
  have hratio : Tendsto (fun u : ℝ => ((⌈u⌉₊ : ℝ) + 2) / u) atTop (𝓝 1) := by
    simpa only [add_div, div_eq_mul_inv, add_mul, add_zero, mul_zero] using
      hceil.add (hinv.const_mul 2)
  have hlarge : Tendsto (fun u : ℝ => (⌈u⌉₊ : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hp)
  have hlog : Tendsto (fun u : ℝ =>
      Real.logb 2 ((⌈u⌉₊ : ℝ) + 2) / ((⌈u⌉₊ : ℝ) + 2)) atTop (𝓝 0) := by
    have H : Tendsto (fun u : ℝ => Real.logb 2 u / u) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero
    exact H.comp hlarge
  have hbReal : Tendsto (fun u : ℝ =>
      (2 * Real.logb 2 ((⌈u⌉₊ : ℝ) + 2) + c) / u) atTop (𝓝 0) := by
    have H := ((hlog.mul hratio).const_mul 2).add (hinv.const_mul (c : ℝ))
    simp only [zero_mul, mul_zero, add_zero] at H
    refine H.congr fun u => ?_
    rw [div_mul_div_cancel₀ (by positivity : (⌈u⌉₊ : ℝ) + 2 ≠ 0)]
    ring
  exact ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal haReal,
    by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hbReal⟩

/-- The dyadic cost comparison bounds the normalized `Q` complexity at every radius below
one by the normalized `P` complexity at a dyadic radius, times an explicit multiplicative
factor, plus an additive error. -/
private lemma normalizedPrecisionComplexity_le_of_dyadic_cost
    (P Q : Presentation X) (A : Set ℕ) (x : X) (c : ℕ)
    (hcost : ∀ p : ℕ, (precisionComplexityNat Q A x (dyadicRadius p) : ℝ) ≤
      precisionComplexityNat P A x (dyadicRadius (p + 1)) +
        2 * Real.logb 2 (p + 2) + c)
    (r : ℝ) (n : ℕ) (ht : 0 < -Real.logb 2 r)
    (hscale : dyadicRadius n ≤ r) :
    normalizedPrecisionComplexity Q A x r ≤
      normalizedPrecisionComplexity P A x (dyadicRadius (n + 1)) *
        ENNReal.ofReal (((n : ℝ) + 1) / (-Real.logb 2 r)) +
      ENNReal.ofReal ((2 * Real.logb 2 ((n : ℝ) + 2) + c) / (-Real.logb 2 r)) := by
  have hmono := precisionComplexityNat_antitone Q A x
    (by unfold dyadicRadius; positivity : 0 < dyadicRadius n) hscale
  have hreal : (precisionComplexityNat Q A x r : ℝ) ≤
      precisionComplexityNat P A x (dyadicRadius (n + 1)) +
        (2 * Real.logb 2 ((n : ℝ) + 2) + c) := by
    have hcast : (precisionComplexityNat Q A x r : ℝ) ≤
        precisionComplexityNat Q A x (dyadicRadius n) := by exact_mod_cast hmono
    simpa only [add_assoc] using hcast.trans (hcost n)
  have hE : (precisionComplexityNat Q A x r : ℝ≥0∞) ≤
      (precisionComplexityNat P A x (dyadicRadius (n + 1)) : ℝ≥0∞) +
        ENNReal.ofReal (2 * Real.logb 2 ((n : ℝ) + 2) + c) := by
    have H := (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
    simpa only [ENNReal.ofReal_natCast] using H
  have hfactor : normalizedPrecisionComplexity P A x (dyadicRadius (n + 1)) *
      ENNReal.ofReal (((n : ℝ) + 1) / (-Real.logb 2 r)) =
      (precisionComplexityNat P A x (dyadicRadius (n + 1)) : ℝ≥0∞) /
        ENNReal.ofReal (-Real.logb 2 r) := by
    rw [normalizedPrecisionComplexity, neg_logb_dyadicRadius,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos ht]
    have heq : ENNReal.ofReal ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) := by norm_cast
    rw [heq, ENNReal.div_mul_div_cancel (by simp) (by simp)]
  rw [hfactor, normalizedPrecisionComplexity,
    ENNReal.ofReal_div_of_pos ht, ENNReal.div_add_div_same]
  exact ENNReal.div_le_div_right hE _

/-- If the limit of a family of factors is `1`, multiplying by it does not increase the
`limsup`. -/
private lemma limsup_mul_le_limsup_of_tendsto_one {α : Type*} {F : Filter α} [NeBot F]
    {g a : α → ℝ≥0∞} (ha : Tendsto a F (𝓝 1)) :
    limsup (fun r => g r * a r) F ≤ limsup g F := by
  have hla : limsup a F = 1 := ha.limsup_eq
  have H := ENNReal.limsup_mul_le' (u := g) (v := a) (f := F)
    (Or.inr (by rw [hla]; simp)) (Or.inr (by rw [hla]; simp))
  simpa only [Pi.mul_def, hla, mul_one] using H

/-- Taking the upper limit in the dyadic cost comparison: rounded dyadic centers tend to
zero, the multiplicative factor tends to one and the additive error tends to zero, so the
upper dimension relative to `Q` is at most the one relative to `P`, also for infinite
values. -/
private lemma staticPointDimensions_snd_le_of_dyadic_cost
    (P Q : Presentation X) (A : Set ℕ) (x : X) (c : ℕ)
    (hcost : ∀ p : ℕ, (precisionComplexityNat Q A x (dyadicRadius p) : ℝ) ≤
      precisionComplexityNat P A x (dyadicRadius (p + 1)) +
        2 * Real.logb 2 (p + 2) + c) :
    (staticPointDimensions Q A x).2 ≤ (staticPointDimensions P A x).2 := by
  let L := 𝓝[>] (0 : ℝ)
  let t : ℝ → ℝ := fun r => -Real.logb 2 r
  let p : ℝ → ℕ := fun r => ⌈t r⌉₊
  let s : ℝ → ℝ := fun r => dyadicRadius (p r + 1)
  let g : ℝ → ℝ≥0∞ := fun r => normalizedPrecisionComplexity P A x (s r)
  let a : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (((p r : ℝ) + 1) / t r)
  let b : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal ((2 * Real.logb 2 ((p r : ℝ) + 2) + c) / t r)
  have ht : Tendsto t L atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num))
  have hp : Tendsto p L atTop := tendsto_nat_ceil_atTop.comp ht
  have ha : Tendsto a L (𝓝 1) := (tendsto_ceil_precision_errors c).1.comp ht
  have hb : Tendsto b L (𝓝 0) := (tendsto_ceil_precision_errors c).2.comp ht
  have hdyadic : Tendsto dyadicRadius atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall ?_⟩
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    · intro n
      change 0 < (2 : ℝ)⁻¹ ^ n
      positivity
  have hs : Tendsto s L (𝓝[>] (0 : ℝ)) :=
    hdyadic.comp ((tendsto_add_atTop_nat 1).comp hp)
  have hbound : ∀ᶠ r in L,
      normalizedPrecisionComplexity Q A x r ≤ g r * a r + b r := by
    have hrpos : ∀ᶠ r in L, 0 < r := self_mem_nhdsWithin
    filter_upwards [hrpos, ht.eventually (eventually_gt_atTop 0)] with r hr htpos
    have hsmall : dyadicRadius (p r) ≤ r := by
      apply (Real.logb_le_logb (b := 2) (by norm_num)
        (by unfold dyadicRadius; positivity) hr).mp
      have hle : t r ≤ (p r : ℝ) := Nat.le_ceil (t r)
      have hd := neg_logb_dyadicRadius (p r)
      change -Real.logb 2 r ≤ (p r : ℝ) at hle
      linarith
    exact normalizedPrecisionComplexity_le_of_dyadic_cost P Q A x c hcost r (p r)
      htpos hsmall
  change limsup (normalizedPrecisionComplexity Q A x) L ≤
    limsup (normalizedPrecisionComplexity P A x) L
  calc
    _ ≤ limsup (fun r => g r * a r + b r) L := limsup_le_limsup hbound
    _ = limsup (fun r => g r * a r) L :=
      ENNReal.limsup_add_of_right_tendsto_zero hb _
    _ ≤ limsup g L := limsup_mul_le_limsup_of_tendsto_one ha
    _ ≤ limsup (normalizedPrecisionComplexity P A x) L :=
      hs.limsup_comp_le_limsup (u := normalizedPrecisionComplexity P A x)

/-- Static upper point dimension is independent of a change of presentation with
computable mixed distances. Blueprint node `metric:change`. -/
theorem presentation_change_packing (P Q : Presentation X) (A : Set ℕ)
    (hmixed : IsComputableRealFamilyIn A
      (fun ij : ℕ × ℕ => dist (P.ι ij.1) (Q.ι ij.2))) (x : X) :
    (staticPointDimensions P A x).2 = (staticPointDimensions Q A x).2 := by
  have hle : ∀ P Q : Presentation X,
      IsComputableRealFamilyIn A (fun ij : ℕ × ℕ => dist (P.ι ij.1) (Q.ι ij.2)) →
      (staticPointDimensions Q A x).2 ≤ (staticPointDimensions P A x).2 := by
    intro P Q hmixed
    obtain ⟨F, hF, htrans⟩ := exists_translator_of_computable_mixed_dist P Q A hmixed
    obtain ⟨c, hc⟩ := complexity_le_of_mem_translator A F hF
    apply staticPointDimensions_snd_le_of_dyadic_cost P Q A x c
    apply precisionComplexityNat_le_of_translation_cost P Q A x c
    intro i p
    obtain ⟨j, hj, hdist⟩ := htrans i p
    exact ⟨j, hdist, hc i p j hj⟩
  exact le_antisymm
    (hle Q P (isComputableRealFamilyIn_dist_swap P Q A hmixed))
    (hle P Q hmixed)

/-- The largest index whose scale is at least `r` exists for small positive `r`, brackets
`r` together with its successor, and tends to infinity as `r` tends to zero from above. -/
private lemma exists_last_scale_index
    (δ : ℕ → ℝ) (hpos : ∀ n, 0 < δ n)
    (hzero : Tendsto δ atTop (𝓝 0)) :
    ∃ m : ℝ → ℕ,
      Tendsto m (𝓝[>] (0 : ℝ)) atTop ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        δ (m r + 1) < r ∧ r ≤ δ (m r) := by
  let m : ℝ → ℕ := fun r => sSup {n | r ≤ δ n}
  have hbounded : ∀ r, 0 < r → BddAbove {n | r ≤ δ n} := by
    intro r hr
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero.eventually (gt_mem_nhds hr))
    refine ⟨N, ?_⟩
    intro n hn
    exact le_of_not_gt fun hlt => (not_lt_of_ge hn) (hN n hlt.le)
  refine ⟨m, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro N
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (hpos N))] with r hr hsmall
    exact le_csSup (hbounded r hr) hsmall.le
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (hpos 0))] with r hr hsmall
    have hb := hbounded r hr
    have hne : {n | r ≤ δ n}.Nonempty := ⟨0, hsmall.le⟩
    refine ⟨?_, Nat.sSup_mem hne hb⟩
    apply lt_of_not_ge
    intro h
    have hle : m r + 1 ≤ m r := le_csSup hb h
    omega

/-- The negative binary logarithm of a positive number below one is positive. -/
private lemma neg_logb_pos_of_lt_one {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    0 < -Real.logb 2 r :=
  neg_pos.mpr (Real.logb_neg one_lt_two h0 h1)

/-- The ratio of two natural logarithms is the ratio of the negative binary logarithms. -/
private lemma log_div_log_eq_neg_logb_div_neg_logb (a b : ℝ) :
    Real.log a / Real.log b = (-Real.logb 2 a) / (-Real.logb 2 b) := by
  rw [neg_div_neg_eq, Real.logb, Real.logb,
    div_div_div_cancel_right₀ (Real.log_pos one_lt_two).ne']

/-- If the logarithmic ratios of consecutive scales tend to one, so do the ratios of
logarithms of consecutive scales in the opposite order, as extended reals. -/
private lemma tendsto_ofReal_log_ratio_inv (δ : ℕ → ℝ)
    (hratio : Tendsto (fun n => Real.log (δ (n + 1)) / Real.log (δ n)) atTop (𝓝 1)) :
    Tendsto (fun n => ENNReal.ofReal (Real.log (δ n) / Real.log (δ (n + 1))))
      atTop (𝓝 1) := by
  have h := hratio.inv₀ (by norm_num)
  simp only [inv_one, inv_div] at h
  simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal h

/-- For radii `b < r ≤ a < 1`, the normalized cost at `r` is at least the normalized cost at
the larger radius `a` times the ratio `log a / log b` of logarithms. -/
private lemma ofReal_log_ratio_mul_normalized_le (P : Presentation X) (A : Set ℕ) (x : X)
    (a b r : ℝ) (hb : 0 < b) (hbr : b < r) (hra : r ≤ a) (ha : a < 1) :
    ENNReal.ofReal (Real.log a / Real.log b) *
        normalizedPrecisionComplexity P A x a ≤
      normalizedPrecisionComplexity P A x r := by
  have hr : 0 < r := hb.trans hbr
  have hdena := neg_logb_pos_of_lt_one (hr.trans_le hra) ha
  have hdenb := neg_logb_pos_of_lt_one hb (hbr.trans (hra.trans_lt ha))
  have hcost := precisionComplexityNat_antitone P A x hr hra
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hden_rb : ENNReal.ofReal (-Real.logb 2 r) ≤
      ENNReal.ofReal (-Real.logb 2 b) := by
    apply ENNReal.ofReal_le_ofReal
    apply neg_le_neg
    exact div_le_div_of_nonneg_right (Real.log_le_log hb hbr.le) hlog2.le
  have hfactor : ENNReal.ofReal (Real.log a / Real.log b) *
      normalizedPrecisionComplexity P A x a =
      (precisionComplexityNat P A x a : ENNReal) /
        ENNReal.ofReal (-Real.logb 2 b) := by
    rw [normalizedPrecisionComplexity, log_div_log_eq_neg_logb_div_neg_logb,
      ENNReal.ofReal_div_of_pos hdenb, mul_comm, ← mul_div_assoc]
    rw [ENNReal.div_mul_cancel]
    · exact (ENNReal.ofReal_pos.mpr hdena).ne'
    · exact ENNReal.ofReal_ne_top
  rw [hfactor, normalizedPrecisionComplexity]
  calc (precisionComplexityNat P A x a : ENNReal) / ENNReal.ofReal (-Real.logb 2 b)
    _ ≤ (precisionComplexityNat P A x r : ENNReal) / ENNReal.ofReal (-Real.logb 2 b) :=
      ENNReal.div_le_div (by exact_mod_cast hcost) le_rfl
    _ ≤ (precisionComplexityNat P A x r : ENNReal) / ENNReal.ofReal (-Real.logb 2 r) :=
      ENNReal.div_le_div le_rfl hden_rb

/-- If a sequence `g ∘ m` along a filter, multiplied by factors tending to one, is
eventually bounded by `f`, then the `liminf` of `g` is at most the `liminf` of `f`, provided
`m` tends to infinity. -/
private lemma liminf_le_liminf_of_mul_le
    {α : Type*} (F : Filter α) [NeBot F]
    (f : α → ℝ≥0∞) (g : ℕ → ℝ≥0∞)
    (m : α → ℕ) (q : α → ℝ≥0∞)
    (hm : Tendsto m F atTop)
    (hq : Tendsto q F (𝓝 1))
    (hb : ∀ᶠ r in F, q r * g (m r) ≤ f r) :
    liminf g atTop ≤ liminf f F := by
  calc
    liminf g atTop ≤ liminf (g ∘ m) F := hm.liminf_le_liminf_comp (u := g)
    _ = liminf q F * liminf (g ∘ m) F := by
      rw [Tendsto.liminf_eq hq, one_mul]
    _ ≤ liminf (q * (g ∘ m)) F := ENNReal.le_liminf_mul
    _ ≤ liminf f F := Filter.liminf_le_liminf hb

/-- The lower dimension is at most the `liminf` of the normalized cost along any positive
scale sequence tending to zero. -/
private lemma staticPointDimensions_fst_le_liminf_scales (P : Presentation X) (A : Set ℕ)
    (x : X) (δ : ℕ → ℝ) (hpos : ∀ m, 0 < δ m) (hzero : Tendsto δ atTop (𝓝 0)) :
    (staticPointDimensions P A x).1 ≤
      liminf (fun m => normalizedPrecisionComplexity P A x (δ m)) atTop := by
  have ht : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hpos⟩
  exact ht.liminf_le_liminf_comp (u := normalizedPrecisionComplexity P A x)

/-- The `liminf` of the normalized cost along a scale sequence whose logarithmic ratios tend
to one is at most the lower dimension. -/
private lemma liminf_scales_le_staticPointDimensions_fst (P : Presentation X) (A : Set ℕ)
    (x : X) (δ : ℕ → ℝ) (hpos : ∀ m, 0 < δ m) (hzero : Tendsto δ atTop (𝓝 0))
    (hratio : Tendsto (fun m => Real.log (δ (m + 1)) / Real.log (δ m)) atTop (𝓝 1)) :
    liminf (fun m => normalizedPrecisionComplexity P A x (δ m)) atTop ≤
      (staticPointDimensions P A x).1 := by
  obtain ⟨m, hm, hbr⟩ := exists_last_scale_index δ hpos hzero
  have hq := tendsto_ofReal_log_ratio_inv δ hratio
  have hsmall : ∀ᶠ n in atTop, δ n < 1 := hzero.eventually (gt_mem_nhds zero_lt_one)
  change liminf (fun n => normalizedPrecisionComplexity P A x (δ n)) atTop ≤
    liminf (normalizedPrecisionComplexity P A x) (𝓝[>] (0 : ℝ))
  refine liminf_le_liminf_of_mul_le
    (𝓝[>] (0 : ℝ)) (normalizedPrecisionComplexity P A x)
    (fun n => normalizedPrecisionComplexity P A x (δ n)) m
    (fun r => ENNReal.ofReal (Real.log (δ (m r)) / Real.log (δ (m r + 1))))
    hm (hq.comp hm) ?_
  filter_upwards [hbr, hm.eventually hsmall] with r hr hs
  exact ofReal_log_ratio_mul_normalized_le P A x
    (δ (m r)) (δ (m r + 1)) r (hpos _) hr.1 hr.2 hs

/-- Lower dimension is computed along every positive scale sequence tending to zero with
successive logarithmic ratio tending to one; monotonicity is not assumed.
Blueprint node `metric:sampling`. -/
theorem dimension_along_scales (P : Presentation X) (A : Set ℕ) (x : X) (δ : ℕ → ℝ)
    (hpos : ∀ m, 0 < δ m) (hzero : Tendsto δ atTop (𝓝 0))
    (hratio : Tendsto (fun m => Real.log (δ (m + 1)) / Real.log (δ m)) atTop (𝓝 1)) :
    (staticPointDimensions P A x).1 =
      liminf (fun m => normalizedPrecisionComplexity P A x (δ m)) atTop :=
  le_antisymm (staticPointDimensions_fst_le_liminf_scales P A x δ hpos hzero)
    (liminf_scales_le_staticPointDimensions_fst P A x δ hpos hzero hratio)

/-- For radii `b < r ≤ a < 1`, the normalized cost at `r` is at most the normalized cost at
the smaller radius `b` times the ratio `log b / log a` of logarithms. -/
private lemma normalized_le_mul_ofReal_log_ratio
    (P : Presentation X) (A : Set ℕ) (x : X)
    (a b r : ℝ) (hb : 0 < b) (hbr : b < r)
    (hra : r ≤ a) (ha : a < 1) :
    normalizedPrecisionComplexity P A x r ≤
      normalizedPrecisionComplexity P A x b *
        ENNReal.ofReal (Real.log b / Real.log a) := by
  have hr : 0 < r := hb.trans hbr
  have hdena := neg_logb_pos_of_lt_one (hr.trans_le hra) ha
  have hdenb := neg_logb_pos_of_lt_one hb (hbr.trans (hra.trans_lt ha))
  have hcost := precisionComplexityNat_antitone P A x hb hbr.le
  have hden : ENNReal.ofReal (-Real.logb 2 a) ≤
      ENNReal.ofReal (-Real.logb 2 r) := by
    apply ENNReal.ofReal_le_ofReal
    apply neg_le_neg
    exact div_le_div_of_nonneg_right (Real.log_le_log hr hra) (Real.log_pos one_lt_two).le
  have hfactor : normalizedPrecisionComplexity P A x b *
      ENNReal.ofReal (Real.log b / Real.log a) =
      (precisionComplexityNat P A x b : ℝ≥0∞) /
        ENNReal.ofReal (-Real.logb 2 a) := by
    rw [normalizedPrecisionComplexity, log_div_log_eq_neg_logb_div_neg_logb,
      ENNReal.ofReal_div_of_pos hdena,
      ENNReal.div_mul_div_cancel (ENNReal.ofReal_pos.mpr hdenb).ne' (by simp)]
  rw [hfactor, normalizedPrecisionComplexity]
  exact ENNReal.div_le_div (by exact_mod_cast hcost) hden

/-- Upper dimension has the same sampling invariance for possibly nonmonotone scales.
Blueprint node `metric:sampling`. -/
theorem dimension_along_scales_upper (P : Presentation X) (A : Set ℕ) (x : X)
    (δ : ℕ → ℝ) (hpos : ∀ m, 0 < δ m) (hzero : Tendsto δ atTop (𝓝 0))
    (hratio : Tendsto (fun m => Real.log (δ (m + 1)) / Real.log (δ m)) atTop (𝓝 1)) :
    (staticPointDimensions P A x).2 =
      limsup (fun m => normalizedPrecisionComplexity P A x (δ m)) atTop := by
  have hδ : Tendsto δ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hpos⟩
  apply le_antisymm
  · obtain ⟨m, hm, hbr⟩ := exists_last_scale_index δ hpos hzero
    let u : ℕ → ℝ≥0∞ := fun n => normalizedPrecisionComplexity P A x (δ n)
    let g : ℝ → ℝ≥0∞ := fun r => u (m r + 1)
    let q : ℝ → ℝ≥0∞ := fun r =>
      ENNReal.ofReal (Real.log (δ (m r + 1)) / Real.log (δ (m r)))
    have hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [q, Function.comp_def, ENNReal.ofReal_one] using
        (ENNReal.tendsto_ofReal hratio).comp hm
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        normalizedPrecisionComplexity P A x r ≤ g r * q r := by
      filter_upwards [hbr, hm.eventually (hzero.eventually (gt_mem_nhds zero_lt_one))]
        with r hr hs
      exact normalized_le_mul_ofReal_log_ratio P A x
        (δ (m r)) (δ (m r + 1)) r (hpos _) hr.1 hr.2 hs
    change limsup (normalizedPrecisionComplexity P A x) (𝓝[>] (0 : ℝ)) ≤
      limsup u atTop
    calc
      _ ≤ limsup (fun r => g r * q r) (𝓝[>] (0 : ℝ)) := limsup_le_limsup hbound
      _ ≤ limsup g (𝓝[>] (0 : ℝ)) := limsup_mul_le_limsup_of_tendsto_one hq
      _ ≤ limsup u atTop :=
        ((tendsto_add_atTop_nat 1).comp hm).limsup_comp_le_limsup (u := u)
  · exact hδ.limsup_comp_le_limsup (u := normalizedPrecisionComplexity P A x)

end Kolmogorov.PointToSet
