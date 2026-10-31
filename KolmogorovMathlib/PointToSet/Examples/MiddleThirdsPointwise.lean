/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Examples.MiddleThirds

/-!
# Pointwise static dimensions of the middle-thirds Cantor set

For the canonical computable dense presentation `middleThirdsPresentation` of the
middle-thirds Cantor set, every point `x` has upper static dimension at most `log 2 / log 3`,
for every oracle `A`: a length-`m` binary prefix of the digit sequence of `x` describes `x` at
precision `2 * 3⁻ᵐ`, and a literal description of such a prefix has length `m + O(log (m + 1))`.
Combined with the Hausdorff-dimension lower bound `middleThirds_dimensions` and the static
point-to-set principle, this proves that the supremum of the lower, resp. upper, static point
dimensions over the Cantor set equals `log 2 / log 3` for every oracle
(`middleThirds_dimensions_pointwise`, blueprint node `example:cantor`).
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal
open Kolmogorov

/-- The oracle complexity of the natural number encoding a bit string exceeds the oracle
complexity of the string by at most a constant. -/
private lemma exists_oracleNatComplexity_encode_le (A : Set ℕ) :
    ∃ c : ℕ, ∀ w : BitString,
      oracleNatComplexity A (Encodable.encode w) ≤ oracleComplexity A w + c := by
  let F : List BitString →. BitString :=
    fun ws ↦ Part.some (natBits (Encodable.encode (ws.headD [])))
  have hF : PartrecIn {charOracle A} F := by
    have hd : Computable (fun ws : List BitString ↦ ws.headD []) :=
      (Computable.option_getD Primrec.list_head?.to_comp (Computable.const [])).of_eq
        (fun ws ↦ by cases ws <;> rfl)
    have he : Computable (fun w : BitString ↦ natBits (Encodable.encode w)) :=
      natBits_computable.comp Computable.encode
    exact (he.comp hd).partrecIn
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A 1 F hF
  refine ⟨c, fun w ↦ ?_⟩
  have hmem : natBits (Encodable.encode w) ∈ F [w] := Part.mem_some _
  exact hc [w] (natBits (Encodable.encode w)) rfl hmem

/-- The point of the presentation coded by the length-`m` digit prefix of a Cantor point `x`
is within `2 * 3⁻ᵐ` of `x`. -/
private lemma dist_encode_cantorPrefix_lt (x : cantorSet) (m : ℕ) :
    dist (middleThirdsPresentation.ι
      (Encodable.encode (cantorPrefix (cantorSetHomeomorphNatToBool x) m))) x <
        2 * (3 : ℝ)⁻¹ ^ m := by
  let ξ := cantorSetHomeomorphNatToBool x
  let w := cantorPrefix ξ m
  let i := Encodable.encode w
  have H_dec : (Encodable.decode (α := BitString) i).getD [] = w := by
    dsimp [i]
    rw [Encodable.encodek]
    rfl
  have H_val : (middleThirdsPresentation.ι i : ℝ) = Real.ofDigits
      (fun j ↦ cond (prependCantor ((Encodable.decode (α := BitString) i).getD [])
        (fun _ ↦ false) j) (2 : Fin 3) 0) := rfl
  have H_x : Real.ofDigits (fun j ↦ cond (ξ j) (2 : Fin 3) 0) = (x : ℝ) :=
    congrArg Subtype.val (cantorSetHomeomorphNatToBool.symm_apply_apply x)
  have H_dist : dist (middleThirdsPresentation.ι i) x =
      |Real.ofDigits (fun j ↦ cond (prependCantor w (fun _ ↦ false) j) (2 : Fin 3) 0) -
        Real.ofDigits (fun j ↦ cond (ξ j) (2 : Fin 3) 0)| := by
    rw [Subtype.dist_eq, Real.dist_eq, ← H_x, H_val, H_dec]
  have H_pre : ∀ j < m,
      cond (prependCantor w (fun _ ↦ false) j) (2 : Fin 3) 0 = cond (ξ j) (2 : Fin 3) 0 := by
    intro j hj
    have hj_len : j < w.length := by
      dsimp [w, cantorPrefix]
      simp [hj]
    have H_dite : prependCantor w (fun _ ↦ false) j = w[j] := dite_eq_left hj_len
    rw [H_dite, cantorPrefix_getElem ξ m j hj_len]
  have H_bound := Real.abs_ofDigits_sub_ofDigits_le (b := 3)
    (x := fun j ↦ cond (prependCantor w (fun _ ↦ false) j) (2 : Fin 3) 0)
    (y := fun j ↦ cond (ξ j) (2 : Fin 3) 0) H_pre
  rw [H_dist]
  calc
    _ ≤ (3 : ℝ)⁻¹ ^ m := by rwa [inv_pow]
    _ < 2 * (3 : ℝ)⁻¹ ^ m := by
      have : 0 < (3 : ℝ)⁻¹ ^ m := by positivity
      linarith

/-- The precision complexity at radius `2 * 3⁻ᵐ` is at most the oracle complexity of the
code of the length-`m` digit prefix of `x`. -/
private lemma precisionComplexityNat_le_oracleNatComplexity_encode_cantorPrefix
    (A : Set ℕ) (x : cantorSet) (m : ℕ) :
    precisionComplexityNat middleThirdsPresentation A x (2 * (3 : ℝ)⁻¹ ^ m) ≤
      oracleNatComplexity A
        (Encodable.encode (cantorPrefix (cantorSetHomeomorphNatToBool x) m)) := by
  have H_prec : precisionComplexity middleThirdsPresentation A x (2 * (3 : ℝ)⁻¹ ^ m) ≤
      (oracleNatComplexity A
        (Encodable.encode (cantorPrefix (cantorSetHomeomorphNatToBool x) m)) : ENat) := by
    unfold precisionComplexity
    exact iInf_le_of_le _ (iInf_le_of_le (dist_encode_cantorPrefix_lt x m) le_rfl)
  exact (ENat.toNat_le_toNat H_prec (ENat.natCast_ne_top _)).trans_eq (ENat.toNat_natCast _)

/-- The precision complexity of a Cantor point at radius `2 * 3⁻ᵐ` is at most the complexity of
its length-`m` digit prefix, up to `O(log (m + 2))`. -/
private lemma precisionComplexityNat_le_oracleComplexity_cantorPrefix (A : Set ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : cantorSet) (m : ℕ),
      (precisionComplexityNat middleThirdsPresentation A x
        (2 * (3 : ℝ)⁻¹ ^ m) : ℝ) ≤
      (oracleComplexity A
        (cantorPrefix (cantorSetHomeomorphNatToBool x) m) : ℝ) +
      C * Real.logb 2 ((m : ℝ) + 2) + C := by
  obtain ⟨c, hc⟩ := exists_oracleNatComplexity_encode_le A
  refine ⟨c, by positivity, fun x m ↦ ?_⟩
  set w := cantorPrefix (cantorSetHomeomorphNatToBool x) m
  have h1 := precisionComplexityNat_le_oracleNatComplexity_encode_cantorPrefix A x m
  have h2 : (precisionComplexityNat middleThirdsPresentation A x (2 * (3 : ℝ)⁻¹ ^ m) : ℝ) ≤
      (oracleComplexity A w : ℝ) + c := by exact_mod_cast h1.trans (hc w)
  have h3 : 0 ≤ Real.logb 2 ((m : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have h4 : 0 ≤ (c : ℝ) * Real.logb 2 ((m : ℝ) + 2) := by positivity
  linarith

/-- A prefix machine decoding a pair `(natBits m, w)` with `|w| = m` to `w`. -/
private def litPrefixDecoder : Map := fun pr ↦
  if pr.1 = pairCode (decodeFirst pr.1) (decodeSecond pr.1) ∧
      (decodeSecond pr.1).length = decodeBits (decodeFirst pr.1)
  then Part.some (decodeSecond pr.1) else Part.none

private lemma litPrefixDecoder_produces (m : ℕ) (w y : BitString)
    (h : w.length = m) :
    produces litPrefixDecoder (pairCode (natBits m) w) y w := by
  change _ ∈ (if _ then _ else _)
  have h1 : (pairCode (natBits m) w, y).1 = pairCode (natBits m) w := rfl
  have h2 : decodeBits (natBits m) = m := decodeBits_natBits m
  rw [h1, decodeFirst_pairCode, decodeSecond_pairCode, h2, h]
  simp only [and_self, ↓reduceIte]
  exact ⟨trivial, rfl⟩

private lemma litPrefixDecoder_isPrefixMachine :
    IsPrefixMachine litPrefixDecoder := by
  intro y p hp q hq hpre
  change (litPrefixDecoder (p, y)).Dom at hp
  change (litPrefixDecoder (q, y)).Dom at hq
  dsimp [litPrefixDecoder] at hp hq
  split_ifs at hp with hpvalid
  · split_ifs at hq with hqvalid
    · have hparsed : decodeFirst p = decodeFirst q ∧ decodeSecond p <+: decodeSecond q := by
        obtain ⟨r, hr⟩ := hpre
        have hr2 : p ++ r = q := hr
        rw [hpvalid.1, hqvalid.1] at hr2
        have hn := natCode_append_inj (by simpa [pairCode, List.append_assoc] using hr2)
        obtain ⟨hx, hpq⟩ := List.append_inj hn.2 hn.1
        exact ⟨hx, ⟨r, hpq⟩⟩
      have hlen : (decodeSecond p).length = (decodeSecond q).length := by
        rw [hpvalid.2, hqvalid.2, hparsed.1]
      have hsuffix : decodeSecond p = decodeSecond q := hparsed.2.eq_of_length hlen
      rw [hpvalid.1, hqvalid.1, hparsed.1, hsuffix]
    · exact False.elim hq
  · exact False.elim hp

private lemma litPrefixDecoder_isDecompressorIn (O : ℕ →. ℕ) :
    IsDecompressorIn O litPrefixDecoder := by
  unfold IsDecompressorIn
  rw [RecursiveIn.iff_nat]
  have hfirst : Primrec (fun pr : BitString × BitString ↦ decodeFirst pr.1) :=
    CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst
  have hsecond : Primrec (fun pr : BitString × BitString ↦ decodeSecond pr.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hpair : Primrec (fun pr : BitString × BitString ↦
      pairCode (decodeFirst pr.1) (decodeSecond pr.1)) :=
    CodedFiniteDistribution.pairCode_primrec.comp hfirst hsecond
  have hguard : Computable (fun pr : BitString × BitString ↦
      decide (pr.1 = pairCode (decodeFirst pr.1) (decodeSecond pr.1) ∧
          (decodeSecond pr.1).length = decodeBits (decodeFirst pr.1))) :=
    (PrimrecPred.and (Primrec.eq.comp Primrec.fst hpair)
      (Primrec.eq.comp (Primrec.list_length.comp hsecond)
        (primrec_decodeBits.comp hfirst))).decide.to_comp
  have hrun : PartrecIn {O}
      (fun pr : BitString × BitString ↦ Part.some (decodeSecond pr.1)) :=
    hsecond.to_comp.partrec.partrecIn
  exact (PartrecIn.cond hguard.computableIn hrun PartrecIn.none).of_eq (fun pr ↦ by
    dsimp [litPrefixDecoder]
    simp only [Bool.cond_decide])

/-- The oracle complexity of a length-`m` prefix is at most `m + O(log (m + 2))`, by literal
description. -/
private lemma oracleComplexity_cantorPrefix_le (A : Set ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : CantorSeq) (m : ℕ),
      (oracleComplexity A (cantorPrefix ξ m) : ℝ) ≤
      (m : ℝ) + C * Real.logb 2 ((m : ℝ) + 2) + C := by
  obtain ⟨c, hc⟩ := (exists_optimalOraclePrefix_spec A).2.2 litPrefixDecoder
    (litPrefixDecoder_isDecompressorIn _) litPrefixDecoder_isPrefixMachine
  refine ⟨(c : ℝ) + 3, by positivity, fun ξ m ↦ ?_⟩
  let w := cantorPrefix ξ m
  have h_len : w.length = m := by
    dsimp [w, cantorPrefix]
    simp
  have hprod := litPrefixDecoder_produces m w [] h_len
  have hbound : (oracleComplexity A w : ENat) ≤
      ((2 * (Nat.bits m).length + 1 + m + c : ℕ) : ENat) := by
    calc
      (oracleComplexity A w : ENat) = oraclePrefixComplexity A w [] :=
        oraclePrefixComplexity_coe A w []
      _ ≤ KP litPrefixDecoder w [] + c := hc w []
      _ ≤ ((pairCode (natBits m) w).length : ENat) + c := by
        gcongr
        exact KP_le_programLength_of_produces hprod
      _ = ((2 * (Nat.bits m).length + 1 + m + c : ℕ) : ENat) := by
        rw [length_pairCode, h_len]
        dsimp [natBits]
        push_cast
        ring
  have hreal : (oracleComplexity A w : ℝ) ≤ 2 * ((Nat.bits m).length : ℝ) + 1 + m + c := by
    exact_mod_cast ENat.natCast_le_natCast.mp hbound
  have hlog := length_bits_le_logb_add_one m
  have hm12 : Real.logb 2 ((m : ℝ) + 1) ≤ Real.logb 2 ((m : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have h_nonneg : 0 ≤ Real.logb 2 ((m : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have := mul_nonneg (show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity) h_nonneg
  nlinarith

/-- A sequence bounded by `m + C * log₂ (m + 2) + C` has normalized limsup at most
`log 2 / log 3` at the radii `2 * 3⁻ᵐ`. -/
private lemma limsup_div_le_log_two_div_log_three
    (k : ℕ → ℕ) (C : ℝ)
    (hk : ∀ m : ℕ, (k m : ℝ) ≤
      (m : ℝ) + C * Real.logb 2 ((m : ℝ) + 2) + C) :
    Filter.limsup
      (fun m ↦ (k m : ℝ≥0∞) /
        ENNReal.ofReal (-Real.logb 2 (2 * (3 : ℝ)⁻¹ ^ m)))
      Filter.atTop ≤ ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  let L : ℝ := Real.logb 2 3
  have hL : 1 < L := by
    have H := Real.logb_lt_logb (b := 2) (by norm_num)
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using H
  have hLpos : 0 < L := zero_lt_one.trans hL
  have hlog : Tendsto (fun m : ℕ ↦ Real.logb 2 ((m : ℝ) + 2) / (m : ℝ))
      atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-2) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using H
  have hc : Tendsto (fun m : ℕ ↦ C / (m : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop tendsto_natCast_atTop_atTop C
  have hi : Tendsto (fun m : ℕ ↦ 1 / (m : ℝ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop tendsto_natCast_atTop_atTop 1
  have hreal : Tendsto (fun m : ℕ ↦
      ((m : ℝ) + C * Real.logb 2 ((m : ℝ) + 2) + C) / ((m : ℝ) * L - 1))
      atTop (𝓝 (Real.log 2 / Real.log 3)) := by
    have H := (((tendsto_const_nhds (x := (1 : ℝ))).add (hlog.const_mul C)).add hc).div
      ((tendsto_const_nhds (x := L)).sub hi) (by simpa using hLpos.ne')
    have H' : Tendsto (fun m : ℕ ↦
        (1 + C * (Real.logb 2 ((m : ℝ) + 2) / (m : ℝ)) + C / (m : ℝ)) /
          (L - 1 / (m : ℝ))) atTop (𝓝 (Real.log 2 / Real.log 3)) := by
      simpa only [Pi.div_def, mul_zero, add_zero, sub_zero, L, Real.logb, one_div_div] using H
    apply H'.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    calc
      (1 + C * (Real.logb 2 ((m : ℝ) + 2) / (m : ℝ)) + C / (m : ℝ)) /
          (L - 1 / (m : ℝ)) =
          (((m : ℝ) + C * Real.logb 2 ((m : ℝ) + 2) + C) / (m : ℝ)) /
            (((m : ℝ) * L - 1) / (m : ℝ)) := by
        congr 1 <;> field_simp
      _ = _ := div_div_div_cancel_right₀ hm' _ _
  have he := ENNReal.tendsto_ofReal hreal
  have hnorm : ∀ᶠ m : ℕ in atTop,
      (k m : ℝ≥0∞) / ENNReal.ofReal (-Real.logb 2 (2 * (3 : ℝ)⁻¹ ^ m)) ≤
        ENNReal.ofReal (((m : ℝ) + C * Real.logb 2 ((m : ℝ) + 2) + C) /
          ((m : ℝ) * L - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hdenpos : 0 < (m : ℝ) * L - 1 := by
      have H := mul_le_mul_of_nonneg_right hm' hLpos.le
      linarith
    have hden : -Real.logb 2 (2 * (3 : ℝ)⁻¹ ^ m) = (m : ℝ) * L - 1 := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, Real.logb_inv]
      have h2 : Real.logb 2 2 = 1 := by norm_num
      rw [h2]
      dsimp [L]
      ring
    rw [hden, ENNReal.ofReal_div_of_pos hdenpos]
    apply ENNReal.div_le_div_right
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hk m)
  calc
    _ ≤ limsup (fun m : ℕ ↦ ENNReal.ofReal
        (((m : ℝ) + C * Real.logb 2 ((m : ℝ) + 2) + C) / ((m : ℝ) * L - 1))) atTop :=
      limsup_le_limsup hnorm
    _ = _ := he.limsup_eq

/-- The radii `2 * 3⁻ᵐ` tend to zero. -/
private lemma tendsto_two_mul_inv_three_pow :
    Tendsto (fun m : ℕ ↦ 2 * (3 : ℝ)⁻¹ ^ m) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3⁻¹)
    (by norm_num)).const_mul 2

/-- The logarithms of consecutive radii `2 * 3⁻ᵐ` have ratio tending to one. -/
private lemma tendsto_log_two_mul_inv_three_pow_succ_div :
    Tendsto (fun m : ℕ ↦
      Real.log (2 * (3 : ℝ)⁻¹ ^ (m + 1)) / Real.log (2 * (3 : ℝ)⁻¹ ^ m))
      atTop (𝓝 1) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : ∀ m : ℕ, Real.log (2 * (3 : ℝ)⁻¹ ^ m) = Real.log 2 - m * Real.log 3 := by
    intro m
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv]
    ring
  -- divide numerator and denominator by `m`
  have hlim : Tendsto (fun m : ℕ ↦
      (Real.log 2 / m - (1 + 1 / (m : ℝ)) * Real.log 3) / (Real.log 2 / m - Real.log 3))
      atTop (𝓝 ((0 - (1 + 0) * Real.log 3) / (0 - Real.log 3))) := by
    have h0 := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    refine (h0.sub ((tendsto_const_nhds.add h1).mul tendsto_const_nhds)).div
      (h0.sub tendsto_const_nhds) ?_
    simpa only [zero_sub, ne_eq, neg_eq_zero] using hlog3.ne'
  have hval : (0 - (1 + 0) * Real.log 3) / (0 - Real.log 3) = 1 := by
    rw [zero_sub, zero_sub, add_zero, one_mul, div_self (neg_ne_zero.mpr hlog3.ne')]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [hlog, hlog, ← mul_div_mul_right _ _ hm']
  push_cast
  congr 1 <;> field_simp

/-- For every Cantor point and oracle, the upper static dimension is at most `log 2 / log 3`. -/
private lemma staticPointDimensions_snd_le (A : Set ℕ) (x : cantorSet) :
    (staticPointDimensions middleThirdsPresentation A x).2 ≤
      ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  obtain ⟨C1, hC1_nonneg, hC1⟩ := precisionComplexityNat_le_oracleComplexity_cantorPrefix A
  obtain ⟨C2, hC2_nonneg, hC2⟩ := oracleComplexity_cantorPrefix_le A
  let k := fun m ↦ precisionComplexityNat middleThirdsPresentation A x (2 * (3 : ℝ)⁻¹ ^ m)
  have hk : ∀ m : ℕ, (k m : ℝ) ≤ (m : ℝ) + (C1 + C2) * Real.logb 2 ((m : ℝ) + 2) +
      (C1 + C2) := by
    intro m
    have h1 := hC1 x m
    have h2 := hC2 (cantorSetHomeomorphNatToBool x) m
    calc
      (k m : ℝ) ≤ _ := h1
      _ ≤ (m : ℝ) + C2 * Real.logb 2 ((m : ℝ) + 2) + C2 +
          C1 * Real.logb 2 ((m : ℝ) + 2) + C1 := by linarith
      _ = _ := by ring
  have hpos : ∀ m : ℕ, 0 < 2 * (3 : ℝ)⁻¹ ^ m := fun m ↦ by positivity
  rw [dimension_along_scales_upper middleThirdsPresentation A x _ hpos
    tendsto_two_mul_inv_three_pow tendsto_log_two_mul_inv_three_pow_succ_div]
  exact limsup_div_le_log_two_div_log_three k (C1 + C2) hk

/-- The lower static dimension of every Cantor point is at most its upper static dimension. -/
private lemma staticPointDimensions_fst_le_snd (A : Set ℕ) (x : cantorSet) :
    (staticPointDimensions middleThirdsPresentation A x).1 ≤
      (staticPointDimensions middleThirdsPresentation A x).2 := by
  have hpos : ∀ m : ℕ, 0 < 2 * (3 : ℝ)⁻¹ ^ m := fun m ↦ by positivity
  rw [dimension_along_scales middleThirdsPresentation A x _ hpos
      tendsto_two_mul_inv_three_pow tendsto_log_two_mul_inv_three_pow_succ_div,
    dimension_along_scales_upper middleThirdsPresentation A x _ hpos
      tendsto_two_mul_inv_three_pow tendsto_log_two_mul_inv_three_pow_succ_div]
  exact Filter.liminf_le_limsup (Filter.isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
    (Filter.isBoundedUnder_of ⟨⊥, fun _ ↦ bot_le⟩)

/-- In the canonical presentation, every oracle has the stated supremum of both static
point dimensions; the complex-digit witness supplies the lower bound.
Blueprint node `example:cantor`. -/
theorem middleThirds_dimensions_pointwise (A : Set ℕ) (σ : LimitSide) :
    (⨆ x : cantorSet, σ.choose (staticPointDimensions middleThirdsPresentation A x)) =
      ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  have hd := Isometry.dimH_image (f := (Subtype.val : cantorSet → ℝ)) isometry_subtype_coe
    Set.univ
  rw [Set.image_univ, Subtype.range_coe] at hd
  have h_le := hausdorffLeSupPointDimension middleThirdsPresentation Set.univ A
  rw [hd.symm] at h_le
  have h_le_sup : ENNReal.ofReal (Real.log 2 / Real.log 3) ≤
      ⨆ x : cantorSet, (staticPointDimensions middleThirdsPresentation A x).1 := by
    calc
      ENNReal.ofReal (Real.log 2 / Real.log 3) ≤
          ⨆ x ∈ (Set.univ : Set cantorSet),
            (staticPointDimensions middleThirdsPresentation A x).1 := by
        rw [← middleThirds_dimensions]
        exact h_le
      _ = ⨆ x : cantorSet, (staticPointDimensions middleThirdsPresentation A x).1 := by
        simp only [Set.mem_univ, iSup_pos]
  apply le_antisymm
  · apply iSup_le
    intro x
    cases σ
    · exact (staticPointDimensions_fst_le_snd A x).trans (staticPointDimensions_snd_le A x)
    · exact staticPointDimensions_snd_le A x
  · cases σ
    · exact h_le_sup
    · exact h_le_sup.trans (iSup_mono (staticPointDimensions_fst_le_snd A))

end Kolmogorov.PointToSet
