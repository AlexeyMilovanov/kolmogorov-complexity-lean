/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.NormalSequences

/-!
# Aligned Normality

A sequence is *aligned normal* if every binary word `U` occurs at positions that are multiples
of `|U|` with limiting frequency `2 ^ (-|U|)`.  This module proves that a sequence is normal
if and only if it is aligned normal (`isNormal_iff_isAlignedNormal`): the forward direction uses
sub-Gaussian concentration for independent blocks of fair bits, the converse sums aligned
frequencies over all offsets inside a block of length `M`.
It belongs to the treatment of normal sequences in the formalization of Shen, Uspensky and
Vereshchagin, "Kolmogorov complexity and algorithmic randomness".
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

private def isNormal_iff_isAlignedNormal_mp_chunk (w : CantorSeq) (M i : ℕ) :
    BitString :=
  cantorPrefix (fun j => w (i * M + j)) M

open Classical in
private noncomputable def isNormal_iff_isAlignedNormal_mp_count
    (U V : BitString) (L : ℕ) : ℕ :=
  ((Finset.range L).filter fun j => (V.drop (j * U.length)).take U.length = U).card

open Classical in
private noncomputable def isNormal_iff_isAlignedNormal_mp_bad
    (U : BitString) (L : ℕ) (ε : ℝ) : Finset BitString :=
  (stringsOfLength (U.length * L)).filter fun V =>
    ε * L ≤ |(isNormal_iff_isAlignedNormal_mp_count U V L : ℝ) -
      (2 : ℝ)⁻¹ ^ U.length * L|

open Classical in
private noncomputable def isNormal_iff_isAlignedNormal_mp_chunkFreq
    (w : CantorSeq) (M : ℕ) (B : Finset BitString) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun i =>
    isNormal_iff_isAlignedNormal_mp_chunk w M i ∈ B).card : ℝ) / N

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_mp`: a finite
family of words of the same length has uniform cylinder mass equal to its cardinality
times the mass of one word. -/
private lemma isNormal_iff_isAlignedNormal_prefix_mass
    (M : ℕ) (B : Finset BitString) (hB : ∀ V ∈ B, V.length = M) :
    uniformMeasure.real {w | cantorPrefix w M ∈ B} =
      (B.card : ℝ) * (2 : ℝ)⁻¹ ^ M := by
  classical
  have heq : {w | cantorPrefix w M ∈ B} = ⋃ V ∈ B, cantorCylinder V := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hw
      exact ⟨cantorPrefix w M, hw, mem_cantorCylinder_cantorPrefix w M⟩
    · rintro ⟨V, hV, hwV⟩
      have he := (isCantorPrefix_iff_cantorPrefix_eq V w).mp hwV
      rw [hB V hV] at he
      rwa [he]
  have hd : (B : Set BitString).PairwiseDisjoint cantorCylinder := by
    intro V hV W hW hne
    apply cantorCylinder_disjoint_of_incompatible
    · intro hp
      exact hne (hp.eq_of_length ((hB V hV).trans (hB W hW).symm))
    · intro hp
      exact hne (hp.eq_of_length ((hB W hW).trans (hB V hV).symm)).symm
  rw [heq, measureReal_biUnion_finset hd (fun V _ => measurableSet_cantorCylinder V)]
  calc
    (∑ V ∈ B, uniformMeasure.real (cantorCylinder V)) = ∑ _V ∈ B, (2 : ℝ)⁻¹ ^ M := by
      apply Finset.sum_congr rfl
      intro V hV
      have hm := cantorMass_uniformMeasure V
      unfold cantorMass at hm
      rw [Measure.real, hm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
        hB V hV]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_mp`: grouping fair
bits into disjoint positive-length blocks gives the product of their common block law. -/
private lemma isNormal_iff_isAlignedNormal_group_law
    (m : ℕ) (hm : 0 < m) :
    uniformMeasure.map (fun (w : CantorSeq) (i : ℕ) (j : Fin m) => w (i * m + j)) =
      Measure.infinitePi (fun _i : ℕ =>
        uniformMeasure.map (fun (w : CantorSeq) (j : Fin m) => w j)) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let ν : Measure Bool := ProbabilityTheory.bernoulliMeasure true false
    ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  have hμ : uniformMeasure = Measure.infinitePi (fun _i : ℕ => ν) := rfl
  have hblock : uniformMeasure.map (fun (w : CantorSeq) (j : Fin m) => w j) =
      Measure.infinitePi (fun _j : Fin m => ν) := by
    rw [hμ]
    exact Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective
  let e : ℕ × Fin m ≃ ℕ := (Nat.divModEquiv m).symm
  have hprod : uniformMeasure.map (fun w p => w (e p)) =
      Measure.infinitePi (fun _p : ℕ × Fin m => ν) := by
    rw [hμ]
    exact Measure.map_infinitePi_infinitePi_of_inj e.injective
  rw [hblock]
  change uniformMeasure.map
    ((MeasurableEquiv.curry ℕ (Fin m) Bool) ∘ (fun w p => w (e p))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hprod]
  exact Measure.infinitePi_map_curry (fun (_i : ℕ) (_j : Fin m) => ν)

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_mp`: the indicator
of a prescribed fair block has expectation `2 ^ (-|U|)`. -/
private lemma isNormal_iff_isAlignedNormal_block_mean (U : BitString) :
    ∫ v : Fin U.length → Bool, (if List.ofFn v = U then (1 : ℝ) else 0)
      ∂(uniformMeasure.map (fun (w : CantorSeq) (j : Fin U.length) => w j)) =
        (2 : ℝ)⁻¹ ^ U.length := by
  classical
  have hp : Measurable (fun (w : CantorSeq) (j : Fin U.length) => w j) :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (j : ℕ))
  rw [integral_map hp.aemeasurable
    (measurable_of_countable (fun v : Fin U.length → Bool =>
      if List.ofFn v = U then (1 : ℝ) else 0)).aestronglyMeasurable]
  have heq : (fun w : CantorSeq => if List.ofFn (fun j : Fin U.length => w j) = U
      then (1 : ℝ) else 0) = (cantorCylinder U).indicator 1 := by
    ext w
    change (if cantorPrefix w U.length = U then (1 : ℝ) else 0) =
      if IsCantorPrefix U w then 1 else 0
    simp only [isCantorPrefix_iff_cantorPrefix_eq]
  rw [heq, integral_indicator_one (measurableSet_cantorCylinder U), Measure.real]
  change (cantorMass uniformMeasure U).toReal = _
  rw [cantorMass_uniformMeasure, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]

/-- Step 3 of the proof of `isNormal_iff_isAlignedNormal_mp`: extracting the
`j`-th short block of a long chunk reads the short block at index `i * L + j`. -/
private lemma isNormal_iff_isAlignedNormal_word_eq
    (w : CantorSeq) (U : BitString) (L i j : ℕ) (hj : j < L) :
    ((isNormal_iff_isAlignedNormal_mp_chunk w (U.length * L) i).drop
      (j * U.length)).take U.length = U ↔ BlockIs U w (i * L + j) := by
  have hjm : j * U.length + U.length ≤ U.length * L := by
    have := Nat.mul_le_mul_right U.length (Nat.succ_le_of_lt hj)
    nlinarith
  have hlen : (((isNormal_iff_isAlignedNormal_mp_chunk w (U.length * L) i).drop
      (j * U.length)).take U.length).length = U.length := by
    simp only [List.length_take, List.length_drop,
      isNormal_iff_isAlignedNormal_mp_chunk, cantorPrefix_length]
    exact Nat.min_eq_left (by omega)
  constructor
  · intro he k hk
    have hg : (((isNormal_iff_isAlignedNormal_mp_chunk w (U.length * L) i).drop
        (j * U.length)).take U.length)[k]'(by omega) = U[k] := by
      simp only [he]
    simp only [List.getElem_take, List.getElem_drop,
      isNormal_iff_isAlignedNormal_mp_chunk, cantorPrefix_getElem] at hg
    convert hg using 1; congr 1; ring
  · intro h
    apply List.ext_getElem hlen
    intro k hk hkU
    simp only [List.getElem_take, List.getElem_drop,
      isNormal_iff_isAlignedNormal_mp_chunk, cantorPrefix_getElem]
    convert h k hkU using 1; congr 1; ring

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_mp`: among all words
of length `|U| * L`, the proportion whose aligned `U` count deviates by at least `ε * L`
is at most `2 * exp (-ε² * L / 2)`. Both the short word and the number of blocks are positive. -/
private lemma isNormal_iff_isAlignedNormal_counting
    (U : BitString) (hU : 0 < U.length) (L : ℕ) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) :
    ((isNormal_iff_isAlignedNormal_mp_bad U L ε).card : ℝ) *
        (2 : ℝ)⁻¹ ^ (U.length * L) ≤
      2 * Real.exp (-ε ^ 2 * L / 2) := by
  classical
  let ν := uniformMeasure.map (fun (w : CantorSeq) (j : Fin U.length) => w j)
  let μ := Measure.infinitePi (fun _i : ℕ => ν)
  let Y : (Fin U.length → Bool) → ℝ := fun v => if List.ofFn v = U then 1 else 0
  let q : ℝ := (2 : ℝ)⁻¹ ^ U.length
  let X := fun (i : ℕ) (v : ℕ → Fin U.length → Bool) => Y (v i) - q
  have hY : Measurable Y := measurable_of_countable Y
  have hmean : ∫ v, Y v ∂ν = q :=
    isNormal_iff_isAlignedNormal_block_mean U
  have hsg0 : ProbabilityTheory.HasSubgaussianMGF (fun v => Y v - q) (1 / 4 : NNReal) ν := by
    have hb : ∀ᵐ v ∂ν, Y v ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards with v
      dsimp [Y]
      split_ifs <;> norm_num
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hY.aemeasurable hb
    rw [hmean] at h
    have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : NNReal) := by norm_num
    rwa [hc] at h
  have hind : ProbabilityTheory.iIndepFun X μ :=
    ProbabilityTheory.iIndepFun_infinitePi (fun _i => hY.sub_const q)
  have hsg (i : ℕ) : ProbabilityTheory.HasSubgaussianMGF (X i) (1 / 4 : NNReal) μ := by
    apply ProbabilityTheory.HasSubgaussianMGF.of_map
      (μ := μ) (Y := fun v : ℕ → Fin U.length → Bool => v i)
      (X := fun v => Y v - q)
      (measurable_pi_apply i).aemeasurable
    rw [Measure.infinitePi_map_eval]
    exact hsg0
  have hindneg : ProbabilityTheory.iIndepFun (fun i v => -(X i v)) μ :=
    hind.comp (fun _i x => -x) (fun _i => measurable_neg)
  have hsgneg (i : ℕ) :
      ProbabilityTheory.HasSubgaussianMGF (fun v => -(X i v)) (1 / 4 : NNReal) μ :=
    (hsg i).neg
  have ht : (0 : ℝ) ≤ ε * L := by positivity
  have hupper := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (n := L) hind (fun i _ => hsg i) ht
  have hlower := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (n := L) hindneg (fun i _ => hsgneg i) ht
  have hexp : Real.exp (-(ε * L) ^ 2 / (2 * L * ((1 / 4 : NNReal) : ℝ))) ≤
      Real.exp (-ε ^ 2 * L / 2) := by
    apply Real.exp_le_exp.mpr
    have hLr : (0 : ℝ) < L := by positivity
    have heq : -(ε * L) ^ 2 / (2 * L * ((1 / 4 : NNReal) : ℝ)) =
        -2 * ε ^ 2 * L := by
      norm_num
      field_simp [ne_of_gt hLr]; ring
    rw [heq]
    nlinarith [mul_nonneg (sq_nonneg ε) hLr.le]
  let S := fun v => ∑ i ∈ Finset.range L, X i v
  let E := {v : ℕ → Fin U.length → Bool | ε * L ≤ |S v|}
  have hS : Measurable S :=
    Finset.measurable_sum _ (fun i _ => (hY.comp (measurable_pi_apply i)).sub_const q)
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    simpa only [Real.norm_eq_abs] using hS.norm
  have hsub : E ⊆ {v | ε * L ≤ ∑ i ∈ Finset.range L, X i v} ∪
      {v | ε * L ≤ ∑ i ∈ Finset.range L, -(X i v)} := by
    intro v hv
    change ε * L ≤ |S v| at hv
    rcases le_abs.mp hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (by simpa only [S, Finset.sum_neg_distrib, Set.mem_ofPred_eq] using hv)
  have hprob : μ.real E ≤ 2 * Real.exp (-ε ^ 2 * L / 2) := by
    calc
      μ.real E ≤ μ.real ({v | ε * L ≤ ∑ i ∈ Finset.range L, X i v} ∪
          {v | ε * L ≤ ∑ i ∈ Finset.range L, -(X i v)}) := measureReal_mono hsub
      _ ≤ μ.real {v | ε * L ≤ ∑ i ∈ Finset.range L, X i v} +
          μ.real {v | ε * L ≤ ∑ i ∈ Finset.range L, -(X i v)} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-ε ^ 2 * L / 2) := by
        linarith [hupper.trans hexp, hlower.trans hexp]
  let g := fun (w : CantorSeq) (i : ℕ) (j : Fin U.length) => w (i * U.length + j)
  have hmap : uniformMeasure.map g = μ :=
    isNormal_iff_isAlignedNormal_group_law U.length hU
  have hcount (w : CantorSeq) :
      (∑ i ∈ Finset.range L, Y (g w i)) =
        (isNormal_iff_isAlignedNormal_mp_count U (cantorPrefix w (U.length * L)) L : ℝ) := by
    simp only [isNormal_iff_isAlignedNormal_mp_count, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hfirst : List.ofFn (g w i) = U ↔ BlockIs U w i :=
      (isCantorPrefix_iff_cantorPrefix_eq U (fun j => w (i * U.length + j))).symm
    have hsecond := isNormal_iff_isAlignedNormal_word_eq w U L 0 i hiL
    simp only [isNormal_iff_isAlignedNormal_mp_chunk, zero_mul, zero_add] at hsecond
    simp only [Y, hfirst, hsecond]
  have hsum (w : CantorSeq) : S (g w) =
      (isNormal_iff_isAlignedNormal_mp_count U (cantorPrefix w (U.length * L)) L : ℝ) - q *
          L := by
    dsimp only [S, X]
    rw [Finset.sum_sub_distrib, hcount, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  let B := isNormal_iff_isAlignedNormal_mp_bad U L ε
  have hpre : g ⁻¹' E = {w | cantorPrefix w (U.length * L) ∈ B} := by
    ext w
    change ε * L ≤ |S (g w)| ↔ cantorPrefix w (U.length * L) ∈ B
    rw [hsum]
    simp only [B, isNormal_iff_isAlignedNormal_mp_bad, Finset.mem_filter,
      mem_stringsOfLength, cantorPrefix_length, true_and]
    rfl
  have hmass : μ.real E = (B.card : ℝ) * (2 : ℝ)⁻¹ ^ (U.length * L) := by
    change (μ E).toReal = _
    rw [← hmap, Measure.map_apply (by fun_prop) hE, hpre]
    exact isNormal_iff_isAlignedNormal_prefix_mass _ B
      (fun V hV => (mem_stringsOfLength _ V).mp (Finset.mem_filter.mp hV).1)
  rw [hmass] at hprob
  exact hprob

/-- Step 2 of the proof of `isNormal_iff_isAlignedNormal_mp`: for a finite
family `B` of length-`M` words, normality bounds its aligned frequency by `M` times its uniform
proportion, with arbitrary positive slack. The sampling stride `M` is positive. -/
private lemma isNormal_iff_isAlignedNormal_bad_blocks_rare
    (w : CantorSeq) (hw : IsNormal w) (M : ℕ) (hM : 0 < M)
    (B : Finset BitString) (hB : ∀ V ∈ B, V.length = M) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      isNormal_iff_isAlignedNormal_mp_chunkFreq w M B N <
        M * ((B.card : ℝ) * (2 : ℝ)⁻¹ ^ M) + δ := by
  classical
  have hbound (N : ℕ) :
      isNormal_iff_isAlignedNormal_mp_chunkFreq w M B N ≤
        (M : ℝ) * ∑ V ∈ B, occurrenceFreq V w (N * M) := by
    let A := (Finset.range N).filter fun i =>
      isNormal_iff_isAlignedNormal_mp_chunk w M i ∈ B
    let C := fun V => (Finset.range (N * M)).filter fun k => OccursAt V w k
    have hinj : Function.Injective (fun i : ℕ => i * M) := by
      intro i j hij
      exact Nat.eq_of_mul_eq_mul_right hM hij
    have hsub : A.image (fun i => i * M) ⊆ B.biUnion C := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hiN, hiB⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_biUnion.mpr ⟨_, hiB, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_right
          (Finset.mem_range.mp hiN) hM)
      · intro j hj
        exact (cantorPrefix_getElem (fun j => w (i * M + j)) M j hj).symm
    have hcard : A.card ≤ ∑ V ∈ B, (C V).card := by
      calc A.card = (A.image (fun i => i * M)).card :=
          (Finset.card_image_of_injective A hinj).symm
        _ ≤ (B.biUnion C).card := Finset.card_le_card hsub
        _ ≤ ∑ V ∈ B, (C V).card := Finset.card_biUnion_le
    have hcardR : (A.card : ℝ) ≤ ∑ V ∈ B, ((C V).card : ℝ) := by
      exact_mod_cast hcard
    change (A.card : ℝ) / N ≤ _
    calc (A.card : ℝ) / N ≤ (∑ V ∈ B, ((C V).card : ℝ)) / N :=
        div_le_div_of_nonneg_right hcardR (Nat.cast_nonneg N)
      _ = (M : ℝ) * ∑ V ∈ B, occurrenceFreq V w (N * M) := by
        simp only [occurrenceFreq, ← Finset.sum_div, Nat.cast_mul]
        by_cases hN : N = 0
        · simp [hN, C]
        · have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
          have hMr : (M : ℝ) ≠ 0 := by positivity
          change (∑ V ∈ B, ((C V).card : ℝ)) / N =
            M * ((∑ V ∈ B, ((C V).card : ℝ)) / ((N : ℝ) * M))
          rw [← mul_div_assoc, mul_comm (M : ℝ), mul_div_mul_right _ _ hMr]
  have hNM : Tendsto (fun N : ℕ => N * M) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_right N hM) tendsto_id
  have hsum : Tendsto (fun N : ℕ => ∑ V ∈ B, occurrenceFreq V w (N * M))
      atTop (𝓝 ((B.card : ℝ) * (2 : ℝ)⁻¹ ^ M)) := by
    have ht := tendsto_finsetSum B (fun V _hV => (hw V).comp hNM)
    have hs : (∑ V ∈ B, (2 : ℝ)⁻¹ ^ V.length) =
        (B.card : ℝ) * (2 : ℝ)⁻¹ ^ M := by
      calc
        (∑ V ∈ B, (2 : ℝ)⁻¹ ^ V.length) = (∑ _V ∈ B, (2 : ℝ)⁻¹ ^ M) := by
          apply Finset.sum_congr rfl
          intro V hV
          rw [hB V hV]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rwa [hs] at ht
  have ht := hsum.const_mul (M : ℝ)
  filter_upwards [ht.eventually_lt_const (lt_add_of_pos_right _ hδ)] with N hN
  exact (hbound N).trans_lt hN

open Classical in
/-- Step 3 of the proof of `isNormal_iff_isAlignedNormal_mp`: at a multiple
of the chunk size, the aligned short-word count is the sum of the internal counts. -/
private lemma isNormal_iff_isAlignedNormal_count_sum
    (w : CantorSeq) (U : BitString) (L N : ℕ) :
    (((Finset.range (N * L)).filter fun r => BlockIs U w r).card : ℝ) =
      ∑ i ∈ Finset.range N,
        (isNormal_iff_isAlignedNormal_mp_count U
          (isNormal_iff_isAlignedNormal_mp_chunk w (U.length * L) i) L : ℝ) := by
  classical
  simp only [← Finset.sum_boole]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    simp only [isNormal_iff_isAlignedNormal_mp_count, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [isNormal_iff_isAlignedNormal_word_eq w U L N j
      (Finset.mem_range.mp hj)]

/-- Step 3 of the proof of `isNormal_iff_isAlignedNormal_mp`: the frequency
error at a whole number of chunks is at most `ε` plus the fraction of bad chunks. -/
private lemma isNormal_iff_isAlignedNormal_chunk_error
    (w : CantorSeq) (U : BitString) (L N : ℕ) (hL : 0 < L) (hN : 0 < N)
    (ε : ℝ) (hε : 0 < ε) :
    |alignedFreq U w (N * L) - (2 : ℝ)⁻¹ ^ U.length| ≤
      ε + isNormal_iff_isAlignedNormal_mp_chunkFreq w (U.length * L)
        (isNormal_iff_isAlignedNormal_mp_bad U L ε) N := by
  classical
  let q : ℝ := (2 : ℝ)⁻¹ ^ U.length
  let V := isNormal_iff_isAlignedNormal_mp_chunk w (U.length * L)
  let c := fun i => isNormal_iff_isAlignedNormal_mp_count U (V i) L
  let B := isNormal_iff_isAlignedNormal_mp_bad U L ε
  let D := ((Finset.range N).filter fun i => V i ∈ B).card
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc (i : ℕ) : (c i : ℝ) ≤ L := by
    dsimp [c, isNormal_iff_isAlignedNormal_mp_count]
    exact_mod_cast (Finset.card_filter_le (Finset.range L) _).trans_eq (Finset.card_range L)
  have herr (i : ℕ) : |(c i : ℝ) - q * L| ≤
      ε * L + if V i ∈ B then (L : ℝ) else 0 := by
    by_cases hi : V i ∈ B
    · rw [ite_eq_left hi]
      have habs : |(c i : ℝ) - q * L| ≤ L := by
        apply abs_le.mpr
        constructor <;> nlinarith [hc i, (Nat.cast_nonneg (c i) : (0 : ℝ) ≤ c i),
          (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
      exact habs.trans (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right hi, add_zero]
      apply le_of_lt
      apply lt_of_not_ge
      intro hge
      apply hi
      exact Finset.mem_filter.mpr
        ⟨(mem_stringsOfLength _ _).mpr (cantorPrefix_length _ _), hge⟩
  have hsum : |∑ i ∈ Finset.range N, ((c i : ℝ) - q * L)| ≤
      (N : ℝ) * (ε * L) + (D : ℝ) * L := by
    calc
      |∑ i ∈ Finset.range N, ((c i : ℝ) - q * L)| ≤
          ∑ i ∈ Finset.range N, |(c i : ℝ) - q * L| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N,
          (ε * L + if V i ∈ B then (L : ℝ) else 0) :=
        Finset.sum_le_sum (fun i _ => herr i)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.sum_ite]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
        rfl
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hLr : (L : ℝ) ≠ 0 := by positivity
  have hNL : 0 < (N : ℝ) * L := by positivity
  have heq : alignedFreq U w (N * L) - q =
      (∑ i ∈ Finset.range N, ((c i : ℝ) - q * L)) / ((N : ℝ) * L) := by
    rw [alignedFreq, isNormal_iff_isAlignedNormal_count_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_mul]
    change (∑ i ∈ Finset.range N, (c i : ℝ)) / ((N : ℝ) * L) - q = _
    field_simp [hNr, hLr]
  change |alignedFreq U w (N * L) - q| ≤ ε + (D : ℝ) / N
  rw [heq, abs_div, abs_of_pos hNL]
  apply (div_le_iff₀ hNL).mpr
  calc
    |∑ i ∈ Finset.range N, ((c i : ℝ) - q * L)| ≤
        (N : ℝ) * (ε * L) + (D : ℝ) * L := hsum
    _ = (ε + (D : ℝ) / N) * ((N : ℝ) * L) := by field_simp [hNr]

/-- Step 3 of the proof of `isNormal_iff_isAlignedNormal_mp`: if eventually
fewer than a `2ε` fraction of aligned chunks are bad, summing the internal short-block counts
and discarding the final incomplete chunk gives eventual error less than `4ε`. -/
private lemma isNormal_iff_isAlignedNormal_assembly
    (w : CantorSeq) (U : BitString) (L : ℕ) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ᶠ N : ℕ in atTop,
      isNormal_iff_isAlignedNormal_mp_chunkFreq w (U.length * L)
        (isNormal_iff_isAlignedNormal_mp_bad U L ε) N < 2 * ε) :
    ∀ᶠ K : ℕ in atTop,
      |alignedFreq U w K - (2 : ℝ)⁻¹ ^ U.length| < 4 * ε := by
  classical
  let q : ℝ := (2 : ℝ)⁻¹ ^ U.length
  let c := fun K => ((Finset.range K).filter fun r => BlockIs U w r).card
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hwhole : ∀ᶠ N : ℕ in atTop, |alignedFreq U w (N * L) - q| < 3 * ε := by
    filter_upwards [hbad, eventually_gt_atTop 0] with N hN hNpos
    have he := isNormal_iff_isAlignedNormal_chunk_error w U L N hL
      hNpos ε hε
    exact he.trans_lt (by linarith)
  have hdiv : Tendsto (fun K : ℕ => K / L) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.ne_of_gt hL)
  have hrem : ∀ᶠ K : ℕ in atTop, (L : ℝ) / K < ε :=
    (tendsto_const_div_atTop_nhds_zero_nat (L : ℝ)).eventually_lt_const hε
  filter_upwards [hdiv.eventually hwhole, hrem, eventually_ge_atTop L] with K hK hremK hKL
  let N := K / L
  let R := K % L
  have hN : 0 < N := Nat.div_pos hKL hL
  have hR : R < L := Nat.mod_lt K hL
  have hsplit : N * L + R = K := by
    simpa only [N, R, Nat.mul_comm] using Nat.div_add_mod K L
  have hKr : 0 < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le hL hKL)
  have hNLr : (0 : ℝ) < (N * L : ℕ) := by exact_mod_cast Nat.mul_pos hN hL
  let tail : ℝ := ∑ r ∈ Finset.range R,
    if BlockIs U w (N * L + r) then (1 : ℝ) else 0
  have htail0 : 0 ≤ tail := by
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> norm_num
  have htailR : tail ≤ R := by
    calc
      tail ≤ ∑ _r ∈ Finset.range R, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        split_ifs <;> norm_num
      _ = R := by simp
  have hcounts : (c K : ℝ) = (c (N * L) : ℝ) + tail := by
    dsimp only [c]
    simp only [← Finset.sum_boole]
    rw [← hsplit, Finset.sum_range_add]
  have hsplitR : (K : ℝ) = (N * L : ℕ) + (R : ℝ) := by
    exact_mod_cast hsplit.symm
  have hbase : |(c (N * L) : ℝ) - q * (N * L : ℕ)| <
      3 * ε * (N * L : ℕ) := by
    change |(c (N * L) : ℝ) / (N * L : ℕ) - q| < 3 * ε at hK
    have heq : (c (N * L) : ℝ) / (N * L : ℕ) - q =
        ((c (N * L) : ℝ) - q * (N * L : ℕ)) / (N * L : ℕ) := by
      field_simp [ne_of_gt hNLr]
    rw [heq, abs_div, abs_of_pos hNLr] at hK
    exact (div_lt_iff₀ hNLr).mp hK
  have htail : |tail - q * R| ≤ R := by
    apply abs_le.mpr
    constructor <;> nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have herror : |(c K : ℝ) - q * K| < 4 * ε * K := by
    have heq : (c K : ℝ) - q * K =
        ((c (N * L) : ℝ) - q * (N * L : ℕ)) + (tail - q * R) := by
      rw [hcounts, hsplitR]
      ring
    rw [heq]
    have hsum := abs_add_le ((c (N * L) : ℝ) - q * (N * L : ℕ)) (tail - q * R)
    have hsmall : (L : ℝ) < ε * K := (div_lt_iff₀ hKr).mp hremK
    have hRr : (R : ℝ) < L := by exact_mod_cast hR
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  change |(c K : ℝ) / K - q| < 4 * ε
  have heq : (c K : ℝ) / K - q = ((c K : ℝ) - q * K) / K := by
    field_simp [ne_of_gt hKr]
  rw [heq, abs_div, abs_of_pos hKr]
  exact (div_lt_iff₀ hKr).mpr herror

/-- Step 4 of the proof of `isNormal_iff_isAlignedNormal_mp`: the exponential
tail absorbs the chunk length, with a witness explicitly required to be positive. -/
private lemma isNormal_iff_isAlignedNormal_choose_length
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ 2 * (m : ℝ) * L * Real.exp (-ε ^ 2 * L / 2) < ε := by
  let a : ℝ := ε ^ 2 / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : Tendsto (fun x : ℝ => (x * a) ^ 1 * Real.exp (-(x * a)))
      atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Filter.tendsto_id.atTop_mul_const ha)
  have ht' := (ht.const_mul (2 * (m : ℝ) / a)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq (n : ℕ) :
      2 * (m : ℝ) / a * (((n : ℝ) * a) ^ 1 * Real.exp (-((n : ℝ) * a))) =
        2 * (m : ℝ) * n * Real.exp (-ε ^ 2 * n / 2) := by
    rw [pow_one]
    have hexp : -((n : ℝ) * a) = -ε ^ 2 * n / 2 := by dsimp [a]; ring
    rw [hexp]
    field_simp
  have ht0 : Tendsto (fun n : ℕ =>
      2 * (m : ℝ) * n * Real.exp (-ε ^ 2 * n / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, heq] using ht'
  obtain ⟨L, hL, hbound⟩ :=
    ((eventually_gt_atTop 0).and (ht0.eventually_lt_const hε)).exists
  exact ⟨L, hL, hbound⟩

/-- Step 0 of the proof of `isNormal_iff_isAlignedNormal_mp`: the aligned
frequency of the empty word is one at every positive sample size. -/
private lemma isNormal_iff_isAlignedNormal_empty (w : CantorSeq) :
    Tendsto (alignedFreq [] w) atTop (𝓝 1) := by
  classical
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hf : ((Finset.range N).filter fun i => BlockIs [] w i) = Finset.range N := by
    ext i
    simp [BlockIs, OccursAt]
  simp [alignedFreq, hf, Nat.ne_of_gt hN]

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal`: non-aligned normality implies
aligned normality. -/
private theorem isNormal_iff_isAlignedNormal_mp (w : CantorSeq) : IsNormal w → IsAlignedNormal
    w := by
  intro hw U
  by_cases hU : U.length = 0
  · have he : U = [] := List.length_eq_zero_iff.mp hU
    subst U
    simpa using isNormal_iff_isAlignedNormal_empty w
  have hUpos : 0 < U.length := Nat.pos_of_ne_zero hU
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let ε : ℝ := min (δ / 8) 1
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : 4 * ε < δ := by
    have : ε ≤ δ / 8 := min_le_left _ _
    linarith
  obtain ⟨L, hL, htail⟩ :=
    isNormal_iff_isAlignedNormal_choose_length U.length ε hε
  have hcount :=
    isNormal_iff_isAlignedNormal_counting U hUpos L hL ε hε
  have hrare := isNormal_iff_isAlignedNormal_bad_blocks_rare w hw
    (U.length * L) (Nat.mul_pos hUpos hL)
    (isNormal_iff_isAlignedNormal_mp_bad U L ε)
    (fun V hV => (mem_stringsOfLength _ V).mp (Finset.mem_filter.mp hV).1) ε hε
  have hbad : ∀ᶠ N : ℕ in atTop,
      isNormal_iff_isAlignedNormal_mp_chunkFreq w (U.length * L)
        (isNormal_iff_isAlignedNormal_mp_bad U L ε) N < 2 * ε := by
    filter_upwards [hrare] with N hN
    have hm : (0 : ℝ) ≤ (U.length * L : ℕ) := by positivity
    have hb := mul_le_mul_of_nonneg_left hcount hm
    push_cast at hb hN
    have ht : (U.length : ℝ) * L * (2 * Real.exp (-ε ^ 2 * L / 2)) < ε := by
      nlinarith [htail]
    linarith
  filter_upwards
    [isNormal_iff_isAlignedNormal_assembly w U L hL ε hε hbad]
    with K hK
  rw [Real.dist_eq]
  exact hK.trans hεδ

open Classical in
private noncomputable def isNormal_iff_isAlignedNormal_mpr_f (w : CantorSeq) (U : BitString)
    (M p N : ℕ) : ℝ :=
  (((Finset.range N).filter (fun i => OccursAt U w (i * M + p))).card : ℝ) / N

/-- Step 1 of the proof of
`isNormal_iff_isAlignedNormal_S`: length of elements in S. -/
private lemma isNormal_iff_isAlignedNormal_len
  (U : BitString) (M p : ℕ) (hp : p + U.length ≤ M) :
  ∀ V ∈ (((stringsOfLength p) ×ˢ (stringsOfLength (M - p - U.length))).image fun (A, B) =>
    A ++ U ++ B), V.length = M := by
  intro V hV
  rw [Finset.mem_image] at hV
  rcases hV with ⟨⟨A, B⟩, hAB, rfl⟩
  have hAB_mem : A ∈ stringsOfLength p ∧ B ∈ stringsOfLength (M - p - U.length) :=
      Finset.mem_product.mp hAB
  rcases hAB_mem with ⟨hA, hB⟩
  rw [mem_stringsOfLength] at hA hB
  simp [hA, hB]
  omega

/-- Step 2 of the proof of
`isNormal_iff_isAlignedNormal_S`: cardinality of S. -/
private lemma isNormal_iff_isAlignedNormal_card
  (U : BitString) (M p : ℕ) (hp : p + U.length ≤ M) :
  (((stringsOfLength p) ×ˢ (stringsOfLength (M - p - U.length))).image fun (A, B) =>
    A ++ U ++ B).card = 2 ^ (M - U.length) := by
  rw [Finset.card_image_of_injOn, Finset.card_product, card_stringsOfLength, card_stringsOfLength,
      ← pow_add]
  · congr 1
    omega
  · intro p1 hp1 p2 hp2 heq
    rcases p1 with ⟨A1, B1⟩
    rcases p2 with ⟨A2, B2⟩
    dsimp at heq
    have hAB1_mem : A1 ∈ stringsOfLength p ∧ B1 ∈ stringsOfLength (M - p - U.length) :=
        Finset.mem_product.mp hp1
    have hAB2_mem : A2 ∈ stringsOfLength p ∧ B2 ∈ stringsOfLength (M - p - U.length) :=
        Finset.mem_product.mp hp2
    rw [mem_stringsOfLength] at hAB1_mem hAB2_mem
    have h_lenA : A1.length = A2.length := by omega
    have h_lenU : U.length = U.length := rfl
    have h_lenAU : (A1 ++ U).length = (A2 ++ U).length := by simp [h_lenA]
    have h1 := (List.append_inj heq h_lenAU).1
    have hB := (List.append_inj heq h_lenAU).2
    have hA := (List.append_inj h1 h_lenA).1
    simp only [Prod.mk.injEq]
    exact ⟨hA, hB⟩

/-- Step 3 of the proof of
`isNormal_iff_isAlignedNormal_S`: sum of aligned frequencies
equals the count. -/
private lemma isNormal_iff_isAlignedNormal_sum
  (U : BitString) (M p : ℕ) (hp : p + U.length ≤ M) (w : CantorSeq) (N : ℕ) :
  isNormal_iff_isAlignedNormal_mpr_f w U M p N =
  ∑ V ∈ (((stringsOfLength p) ×ˢ (stringsOfLength (M - p - U.length))).image fun (A, B) =>
    A ++ U ++ B), alignedFreq V w N := by
  classical
  set S := (((stringsOfLength p) ×ˢ (stringsOfLength (M - p - U.length))).image fun (A, B) =>
    A ++ U ++ B) with hS
  let blk : ℕ → BitString := fun i => (List.range M).map (fun j => w (i * M + j))
  have hblk_len : ∀ i, (blk i).length = M := by intro i; simp [blk]
  have hblk_get : ∀ i (j : ℕ) (hj : j < M), (blk i)[j]'(by rw [hblk_len]; exact hj) =
      w (i * M + j) := by
    intro i j hj; simp [blk]
  have hA : ∀ V : BitString, V.length = M → ∀ i, OccursAt V w (i * M) ↔ blk i = V := by
    intro V hV i
    constructor
    · intro h
      apply List.ext_getElem
      · rw [hblk_len, hV]
      · intro j h1 h2
        rw [hblk_get i j (by rw [hblk_len] at h1; exact h1)]
        exact h j (by omega)
    · rintro rfl j hj
      exact (hblk_get i j (by omega)).symm
  have hB : ∀ i, OccursAt U w (i * M + p) ↔ blk i ∈ S := by
    intro i
    constructor
    · intro h
      rw [hS, Finset.mem_image]
      refine ⟨(((List.range p).map (fun j => w (i * M + j))), ((List.range (M - p - U.length)).map
          (fun j => w (i * M + p + U.length + j)))), ?_, ?_⟩
      · rw [Finset.mem_product, mem_stringsOfLength, mem_stringsOfLength]
        simp
      · dsimp only
        apply Eq.symm
        apply List.ext_getElem
        · simp [hblk_len]; omega
        · intro j h1 h2
          rw [hblk_get i j (by rw [hblk_len] at h1; exact h1)]
          simp only [List.getElem_append, List.getElem_map, List.getElem_range, List.length_append,
              List.length_map, List.length_range]
          split_ifs with c1 c2
          · simp
          · have := h (j - p) (by omega)
            exact (congrArg w (by omega)).trans this
          · exact congrArg w (by omega)
    · intro h
      rw [hS, Finset.mem_image] at h
      obtain ⟨⟨A, B⟩, hAB, he⟩ := h
      rw [Finset.mem_product, mem_stringsOfLength, mem_stringsOfLength] at hAB
      intro j hj
      have hjM : p + j < M := by omega
      have h3 := hblk_get i (p + j) hjM
      have key : ∀ (L : BitString) (hL : A ++ U ++ B = L) (hk : p + j < L.length), L[p + j] =
          U[j] := by
        rintro _ rfl hk
        simp [hAB.1, hj]
      simp only at he
      have h4 := key (blk i) he (by rw [hblk_len]; exact hjM)
      rw [h3] at h4
      rw [← h4]
      exact congrArg w (by omega)
  have hlen : ∀ V ∈ S, V.length = M :=
    isNormal_iff_isAlignedNormal_len U M p hp
  have hnat : ((Finset.range N).filter (fun i => OccursAt U w (i * M + p))).card =
      ∑ V ∈ S, ((Finset.range N).filter (fun i => OccursAt V w (i * M))).card := by
    calc ((Finset.range N).filter (fun i => OccursAt U w (i * M + p))).card
        = (((Finset.range N).filter (fun i => blk i ∈ S))).card := by
          congr 1
          apply Finset.filter_congr
          intro i _
          exact hB i
      _ = ∑ V ∈ S, ((((Finset.range N).filter (fun i => blk i ∈ S))).filter
          (fun i => blk i = V)).card :=
          Finset.card_eq_sum_card_fiberwise (f := blk) (t := S)
              (fun i hi => (Finset.mem_filter.1 hi).2)
      _ = ∑ V ∈ S, ((Finset.range N).filter (fun i => OccursAt V w (i * M))).card := by
          apply Finset.sum_congr rfl
          intro V hV
          congr 1
          ext i
          simp only [Finset.mem_filter, hA V (hlen V hV) i]
          constructor
          · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hV⟩, h2⟩
  have hsum : ∑ V ∈ S, alignedFreq V w N =
      (∑ V ∈ S, (((Finset.range N).filter (fun i => OccursAt V w (i * M))).card : ℝ)) / N := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro V hV
    unfold alignedFreq BlockIs
    simp only [hlen V hV]
  rw [hsum]
  unfold isNormal_iff_isAlignedNormal_mpr_f
  rw [hnat]
  push_cast
  rfl

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_fixed_offset`:
define the set of aligned strings. -/
private lemma isNormal_iff_isAlignedNormal_S
  (U : BitString) (M p : ℕ) (hp : p + U.length ≤ M) :
  ∃ S : Finset BitString,
    (∀ V ∈ S, V.length = M) ∧
    S.card = 2 ^ (M - U.length) ∧
    ∀ w : CantorSeq, ∀ N : ℕ,
      isNormal_iff_isAlignedNormal_mpr_f w U M p N =
      ∑ V ∈ S, alignedFreq V w N := by
  use (((stringsOfLength p) ×ˢ (stringsOfLength (M - p - U.length))).image fun (A, B) =>
    A ++ U ++ B)
  refine ⟨isNormal_iff_isAlignedNormal_len U M p hp,
          isNormal_iff_isAlignedNormal_card U M p hp,
          ?_⟩
  intro w N
  exact isNormal_iff_isAlignedNormal_sum U M p hp w N

/-- Step 2 of the proof of `isNormal_iff_isAlignedNormal_fixed_offset`:
limit of the sum. -/
private lemma isNormal_iff_isAlignedNormal_limit
  (w : CantorSeq) (h : IsAlignedNormal w) (M : ℕ) (S : Finset BitString) (hS : ∀ V ∈ S, V.length =
      M) :
  Tendsto (fun N => ∑ V ∈ S, alignedFreq V w N) atTop (𝓝 ((S.card : ℝ) * (2 : ℝ)⁻¹ ^ M)) := by
  have h_lim : Tendsto (fun N => ∑ V ∈ S, alignedFreq V w N) atTop
      (𝓝 (∑ V ∈ S, ((2 : ℝ)⁻¹ ^ V.length))) := by
    exact tendsto_finsetSum S fun V _ => h V
  have h_eq : (∑ V ∈ S, ((2 : ℝ)⁻¹ ^ V.length)) = (S.card : ℝ) * (2 : ℝ)⁻¹ ^ M := by
    calc
      ∑ V ∈ S, ((2 : ℝ)⁻¹ ^ V.length) = ∑ _V ∈ S, ((2 : ℝ)⁻¹ ^ M) := by
        apply Finset.sum_congr rfl
        intro V hV
        rw [hS V hV]
      _ = (S.card : ℝ) * (2 : ℝ)⁻¹ ^ M := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← h_eq]
  exact h_lim

/-- Step 3 of the proof of `isNormal_iff_isAlignedNormal_fixed_offset`:
algebra for the limit. -/
private lemma isNormal_iff_isAlignedNormal_algebra
  (U : BitString) (M p : ℕ) (hp : p + U.length ≤ M) :
  ((2 ^ (M - U.length) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ M = (2 : ℝ)⁻¹ ^ U.length := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [inv_pow]
  have h_pow : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - U.length) * (2 : ℝ) ^ U.length := by
    rw [← pow_add]
    congr 1
    omega
  rw [h_pow]
  push_cast
  calc
    ((2 : ℝ) ^ (M - U.length)) * ((2 : ℝ) ^ (M - U.length) * (2 : ℝ) ^ U.length)⁻¹ =
        ((2 : ℝ) ^ (M - U.length)) * ((2 : ℝ) ^ (M - U.length))⁻¹ * ((2 : ℝ) ^ U.length)⁻¹ := by
      rw [mul_inv, mul_assoc]
    _ = 1 * ((2 : ℝ) ^ U.length)⁻¹ := by
      congr 1
      exact mul_inv_cancel₀ (by positivity)
    _ = (2 : ℝ)⁻¹ ^ U.length := by
      rw [one_mul, inv_pow]

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_mpr`: fixed offset. -/
private lemma isNormal_iff_isAlignedNormal_fixed_offset
  (w : CantorSeq) (h : IsAlignedNormal w) (U : BitString) (M p : ℕ)
      (hp : p + U.length ≤ M) :
  Tendsto (isNormal_iff_isAlignedNormal_mpr_f w U M p) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length)) := by
  obtain ⟨S, hS_len, hS_card, hS_eq⟩ :=
      isNormal_iff_isAlignedNormal_S U M p hp
  have h_eq : isNormal_iff_isAlignedNormal_mpr_f w U M p = fun N =>
    ∑ V ∈ S, alignedFreq V w N := by
    ext N
    rw [hS_eq w N]
  rw [h_eq]
  have h_lim := isNormal_iff_isAlignedNormal_limit w h M S hS_len
  have h_alg := isNormal_iff_isAlignedNormal_algebra U M p hp
  have hS_card_real : (S.card : ℝ) = ((2 ^ (M - U.length) : ℕ) : ℝ) := by
    exact congrArg Nat.cast hS_card
  rw [hS_card_real] at h_lim
  have h_alg_rw : (((2 ^ (M - U.length) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ M) = (2 : ℝ)⁻¹ ^ U.length := h_alg
  rw [h_alg_rw] at h_lim
  exact h_lim


open Classical in
private noncomputable def isNormal_iff_isAlignedNormal_average_lower
  (w : CantorSeq) (U : BitString) (M : ℕ) (N : ℕ) : ℝ :=
  (∑ p ∈ Finset.range (M - U.length + 1), isNormal_iff_isAlignedNormal_mpr_f w U M p N) / M

open Classical in
private noncomputable def isNormal_iff_isAlignedNormal_average_upper
  (w : CantorSeq) (U : BitString) (M : ℕ) (N : ℕ) : ℝ :=
  isNormal_iff_isAlignedNormal_average_lower w U M N + (U.length - 1 : ℝ) / M

/-- Step 1 of the proof of
`isNormal_iff_isAlignedNormal_bound`:
partition a sum over `N * M` positions into `N` consecutive blocks of length `M`. -/
private lemma isNormal_iff_isAlignedNormal_sum_block
    (N M : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (N * M), f k =
      ∑ i ∈ Finset.range N, ∑ p ∈ Finset.range M, f (i * M + p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Step 2 of the proof of
`isNormal_iff_isAlignedNormal_bound`:
every offset frequency lies between zero and one, including when `N = 0`. -/
private lemma isNormal_iff_isAlignedNormal_frequency_bounds
    (w : CantorSeq) (U : BitString) (M p N : ℕ) :
    0 ≤ isNormal_iff_isAlignedNormal_mpr_f w U M p N ∧
      isNormal_iff_isAlignedNormal_mpr_f w U M p N ≤ 1 := by
  classical
  unfold isNormal_iff_isAlignedNormal_mpr_f
  constructor
  · positivity
  · apply div_le_one_of_le₀
    · exact_mod_cast (Finset.card_filter_le (Finset.range N)
        (fun i => OccursAt U w (i * M + p))).trans_eq (Finset.card_range N)
    · positivity

/-- Step 3 of the proof of
`isNormal_iff_isAlignedNormal_bound`:
the occurrence frequency at `N * M` is the average of all `M` offset frequencies. -/
private lemma isNormal_iff_isAlignedNormal_partition
    (w : CantorSeq) (U : BitString) (M N : ℕ) :
    occurrenceFreq U w (N * M) =
      (∑ p ∈ Finset.range M, isNormal_iff_isAlignedNormal_mpr_f w U M p N) / M := by
  classical
  unfold occurrenceFreq isNormal_iff_isAlignedNormal_mpr_f
  rw [← Finset.sum_div, div_div, Nat.cast_mul]
  congr 1
  simp_rw [Finset.natCast_card_filter]
  rw [isNormal_iff_isAlignedNormal_sum_block,
    Finset.sum_comm]

/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_average`: lower
bound. -/
private lemma isNormal_iff_isAlignedNormal_bound
  (w : CantorSeq) (U : BitString) (hU : 1 ≤ U.length) (M : ℕ) (hM : U.length ≤ M) (N : ℕ) :
  isNormal_iff_isAlignedNormal_average_lower w U M N ≤ occurrenceFreq U w (N * M) ∧
  occurrenceFreq U w (N * M) ≤ isNormal_iff_isAlignedNormal_average_upper w U M N :=
      by
  classical
  let f := fun p => isNormal_iff_isAlignedNormal_mpr_f w U M p N
  let L := M - U.length + 1
  let R := U.length - 1
  have hparts : L + R = M := by dsimp [L, R]; omega
  have hnonneg : 0 ≤ ∑ p ∈ Finset.range R, f (L + p) :=
    Finset.sum_nonneg fun p _ =>
      (isNormal_iff_isAlignedNormal_frequency_bounds
        w U M (L + p) N).1
  have hle : (∑ p ∈ Finset.range R, f (L + p)) ≤ (R : ℝ) := by
    calc
      (∑ p ∈ Finset.range R, f (L + p)) ≤ ∑ _p ∈ Finset.range R, (1 : ℝ) :=
        Finset.sum_le_sum fun p _ =>
          (isNormal_iff_isAlignedNormal_frequency_bounds
            w U M (L + p) N).2
      _ = R := by simp
  have hfull : (∑ p ∈ Finset.range M, f p) =
      (∑ p ∈ Finset.range L, f p) + ∑ p ∈ Finset.range R, f (L + p) := by
    rw [← hparts, Finset.sum_range_add]
  have hR : (R : ℝ) = (U.length : ℝ) - 1 := by
    dsimp [R]
    rw [Nat.cast_sub hU, Nat.cast_one]
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  change (∑ p ∈ Finset.range L, f p) / M ≤ occurrenceFreq U w (N * M) ∧
    occurrenceFreq U w (N * M) ≤ (∑ p ∈ Finset.range L, f p) / M + (U.length - 1 : ℝ) / M
  rw [isNormal_iff_isAlignedNormal_partition]
  change (∑ p ∈ Finset.range L, f p) / M ≤ (∑ p ∈ Finset.range M, f p) / M ∧
    (∑ p ∈ Finset.range M, f p) / M ≤
      (∑ p ∈ Finset.range L, f p) / M + (U.length - 1 : ℝ) / M
  rw [hfull, add_div]
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hnonneg hMnonneg)
  · apply add_le_add le_rfl
    rw [← hR]
    exact div_le_div_of_nonneg_right hle hMnonneg

/-- Step 2 of the proof of `isNormal_iff_isAlignedNormal_average`: limits.
-/
private lemma isNormal_iff_isAlignedNormal_limits
  (w : CantorSeq) (h : IsAlignedNormal w) (U : BitString) (M : ℕ)
      (hM : U.length ≤ M) :
  Tendsto (isNormal_iff_isAlignedNormal_average_lower w U M) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) / M)) ∧
  Tendsto (isNormal_iff_isAlignedNormal_average_upper w U M) atTop
      (𝓝 (((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) + (U.length - 1 : ℝ)) / M)) := by
  have hp : ∀ p ∈ Finset.range (M - U.length + 1),
    Tendsto (isNormal_iff_isAlignedNormal_mpr_f w U M p) atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length)) :=
        by
    intro p hp
    rw [Finset.mem_range] at hp
    have hp' : p + U.length ≤ M := by omega
    exact isNormal_iff_isAlignedNormal_fixed_offset w h U M p hp'
  have h_sum := tendsto_finsetSum _ hp
  have h_sum_val : (∑ p ∈ Finset.range (M - U.length + 1), ((2 : ℝ)⁻¹ ^ U.length)) =
      (M - U.length + 1 : ℝ) * (2 : ℝ)⁻¹ ^ U.length := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hm : ((M - U.length + 1 : ℕ) : ℝ) = M - U.length + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hM, Nat.cast_one]
    rw [hm]
  rw [h_sum_val] at h_sum
  have h_lower := Filter.Tendsto.div_const h_sum (M : ℝ)
  refine ⟨?_, ?_⟩
  · have hrw_lower : ((M - U.length + 1 : ℝ) * (2 : ℝ)⁻¹ ^ U.length / (M : ℝ)) =
      ((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) / (M : ℝ)) := by ring
    rw [← hrw_lower]
    exact h_lower
  · have h_upper := Filter.Tendsto.add_const ((U.length - 1 : ℝ) / (M : ℝ)) h_lower
    have hrw_upper : ((M - U.length + 1 : ℝ) * (2 : ℝ)⁻¹ ^ U.length / (M : ℝ) + (U.length - 1 : ℝ) /
        (M : ℝ)) = (((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) + (U.length - 1 : ℝ)) / (M : ℝ))
        := by ring
    rw [← hrw_upper]
    exact h_upper

/-- Step 2 of the proof of `isNormal_iff_isAlignedNormal_mpr`: average over offsets
for K = NM. -/
private lemma isNormal_iff_isAlignedNormal_average
  (w : CantorSeq) (h : IsAlignedNormal w) (U : BitString) (hU : 1 ≤ U.length) (M : ℕ)
      (hM : U.length ≤ M) :
  ∃ (lower upper : ℕ → ℝ),
    (∀ N, lower N ≤ occurrenceFreq U w (N * M) ∧ occurrenceFreq U w (N * M) ≤ upper N) ∧
    Tendsto lower atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) / M)) ∧
    Tendsto upper atTop (𝓝 (((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) + (U.length - 1 : ℝ)) /
        M)) :=
  ⟨isNormal_iff_isAlignedNormal_average_lower w U M,
      isNormal_iff_isAlignedNormal_average_upper w U M,
    isNormal_iff_isAlignedNormal_bound w U hU M hM,
    isNormal_iff_isAlignedNormal_limits w h U M hM⟩


/-- Step 1 of the proof of `isNormal_iff_isAlignedNormal_arbitrary`:
extend block bounds to all lengths. -/
private lemma isNormal_iff_isAlignedNormal_bounds
  (w : CantorSeq) (U : BitString) (M : ℕ)
  (lower_avg upper_avg : ℕ → ℝ)
  (havg : ∀ N, lower_avg N ≤ occurrenceFreq U w (N * M) ∧ occurrenceFreq U w (N * M) ≤ upper_avg N)
      :
  let lower := fun K => if K = 0 then (0 : ℝ) else lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) /
                                                     (K : ℝ)
  let upper := fun K => if K = 0 then (0 : ℝ) else (upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) +
                                                     ((K % M : ℕ) : ℝ)) / (K : ℝ)
  ∀ K, lower K ≤ occurrenceFreq U w K ∧ occurrenceFreq U w K ≤ upper K := by
  classical
  intro lower upper K
  let C : ℕ → ℕ := fun n => ((Finset.range n).filter fun k => OccursAt U w k).card
  have hF : ∀ n, occurrenceFreq U w n = (C n : ℝ) / n := fun n => rfl
  have hFmul : ∀ n, occurrenceFreq U w n * n = C n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [C]
    · rw [hF]
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
  have hmono : ∀ a b, a ≤ b → C a ≤ C b := by
    intro a b hab
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    exact Finset.range_subset_range.mpr hab
  have hstep : ∀ n, C (n + 1) ≤ C n + 1 := by
    intro n
    simp only [C, Finset.range_add_one, Finset.filter_insert]
    split_ifs
    · exact Finset.card_insert_le _ _
    · exact Nat.le_succ _
  have hadd : ∀ a b, C (a + b) ≤ C a + b := by
    intro a b
    induction b with
    | zero => simp
    | succ b ih =>
      calc C (a + (b + 1)) = C ((a + b) + 1) := by rw [Nat.add_assoc]
        _ ≤ C (a + b) + 1 := hstep _
        _ ≤ C a + (b + 1) := by omega
  by_cases hK : K = 0
  · subst hK
    simp [lower, upper, occurrenceFreq]
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
    have hdecomp : K / M * M + K % M = K := Nat.div_add_mod' K M
    obtain ⟨hlo, hhi⟩ := havg (K / M)
    have h1 : lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) ≤ C (K / M * M) := by
      rw [← hFmul]
      exact mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg _)
    have h2 : (C (K / M * M) : ℝ) ≤ upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) := by
      rw [← hFmul]
      exact mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg _)
    have h3 : C (K / M * M) ≤ C K := hmono _ _ (Nat.div_mul_le_self K M)
    have h4 : C K ≤ C (K / M * M) + K % M := by
      have := hadd (K / M * M) (K % M)
      rwa [hdecomp] at this
    constructor
    · change (if K = 0 then (0 : ℝ) else lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) / (K : ℝ)) ≤
        occurrenceFreq U w K
      rw [ite_eq_right hK, hF]
      apply div_le_div_of_nonneg_right _ hKpos.le
      calc lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) ≤ C (K / M * M) := h1
        _ ≤ C K := by exact_mod_cast h3
    · change occurrenceFreq U w K ≤ (if K = 0 then (0 : ℝ) else
        (upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) + ((K % M : ℕ) : ℝ)) / (K : ℝ))
      rw [ite_eq_right hK, hF]
      apply div_le_div_of_nonneg_right _ hKpos.le
      have h4' : (C K : ℝ) ≤ C (K / M * M) + ((K % M : ℕ) : ℝ) := by exact_mod_cast h4
      linarith

/-- Step 2 of the proof of `isNormal_iff_isAlignedNormal_arbitrary`: lower
bound limit. -/
private lemma isNormal_iff_isAlignedNormal_lower_limit
  (M : ℕ) (hM : 0 < M) (lower_avg : ℕ → ℝ) (L : ℝ)
  (h_lower : Tendsto lower_avg atTop (𝓝 L)) :
  Tendsto (fun K => if K = 0 then (0 : ℝ) else lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) / (K : ℝ))
      atTop (𝓝 L) := by
  have h1 : Tendsto (fun K : ℕ => lower_avg (K / M)) atTop (𝓝 L) := by
    apply Tendsto.comp h_lower
    apply tendsto_atTop_atTop_of_monotone'
    · intro a b hab
      exact Nat.div_le_div_right hab
    · intro hb
      rcases hb with ⟨b, hb⟩
      have : ((b + 1) * M) / M ≤ b := by
        apply hb
        exact Set.mem_range_self ((b + 1) * M)
      have : ((b + 1) * M) / M = b + 1 := Nat.mul_div_cancel _ hM
      linarith
  have h2 : Tendsto (fun K : ℕ => ((K / M * M : ℕ) : ℝ) / (K : ℝ)) atTop (𝓝 1) := by
    have h2_eq : (fun K : ℕ => ((K / M * M : ℕ) : ℝ) / (K : ℝ)) =ᶠ[atTop]
        (fun K : ℕ => 1 - ((K % M : ℕ) : ℝ) / (K : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with K hK
      have hK_pos : (K : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hK)
      have h_div_mod_real : ((K / M * M : ℕ) : ℝ) + ((K % M : ℕ) : ℝ) = (K : ℝ) := by
        have : (((K / M * M + K % M : ℕ) : ℝ) = (K : ℝ)) := by
          have h_div_mod : K / M * M + K % M = K := by
            have : K / M * M = M * (K / M) := mul_comm _ _
            rw [this]
            exact Nat.div_add_mod K M
          rw [h_div_mod]
        have h_cast : (((K / M * M + K % M : ℕ) : ℝ) = ((K / M * M : ℕ) : ℝ) + ((K % M : ℕ) : ℝ)) :=
            by
          exact Nat.cast_add _ _
        rw [h_cast] at this
        exact this
      have : ((K / M * M : ℕ) : ℝ) = (K : ℝ) - ((K % M : ℕ) : ℝ) := by linarith
      rw [this]
      rw [sub_div, div_self hK_pos]
    apply Tendsto.congr' h2_eq.symm
    have h_lim_mod : Tendsto (fun K : ℕ => ((K % M : ℕ) : ℝ) / (K : ℝ)) atTop (𝓝 0) := by
      have h_bound : ∀ K : ℕ, 0 < K → |((K % M : ℕ) : ℝ) / (K : ℝ)| ≤ (M : ℝ) / (K : ℝ) := by
        intro K hK_pos
        have hK_real_pos : (K : ℝ) > 0 := by exact_mod_cast hK_pos
        have h_mod_nonneg : (0 : ℝ) ≤ ((K % M : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (K % M))
        rw [abs_div, abs_of_pos hK_real_pos, abs_of_nonneg h_mod_nonneg]
        have : ((K % M : ℕ) : ℝ) ≤ (M : ℝ) := by
          have h_lt : K % M < M := Nat.mod_lt K hM
          exact_mod_cast h_lt.le
        exact div_le_div_of_nonneg_right this hK_real_pos.le
      have h_squeeze : Tendsto (fun K : ℕ => (M : ℝ) / (K : ℝ)) atTop (𝓝 0) := by
        have : (fun K : ℕ => (M : ℝ) / (K : ℝ)) = fun K : ℕ => (M : ℝ) * ((K : ℝ)⁻¹) := by
          ext K; rw [div_eq_mul_inv]
        rw [this]
        have : 0 = (M : ℝ) * 0 := by ring
        rw [this]
        apply Tendsto.const_mul
        exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_squeeze
      · filter_upwards [eventually_ge_atTop 1] with K hK
        have hK_real_pos : (K : ℝ) > 0 := by exact_mod_cast hK
        have h_mod_nonneg : (0 : ℝ) ≤ ((K % M : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (K % M))
        exact div_nonneg h_mod_nonneg hK_real_pos.le
      · filter_upwards [eventually_ge_atTop 1] with K hK
        have hK_pos : 0 < K := by omega
        have : |((K % M : ℕ) : ℝ) / (K : ℝ)| ≤ (M : ℝ) / (K : ℝ) := h_bound K hK_pos
        have hK_real_pos : (K : ℝ) > 0 := by exact_mod_cast hK_pos
        have h_mod_nonneg : (0 : ℝ) ≤ ((K % M : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (K % M))
        have h_div_nonneg : 0 ≤ ((K % M : ℕ) : ℝ) / (K : ℝ) :=
            div_nonneg h_mod_nonneg hK_real_pos.le
        rw [abs_of_nonneg h_div_nonneg] at this
        exact this
    have h_lim : Tendsto (fun K : ℕ => 1 - ((K % M : ℕ) : ℝ) / (K : ℝ)) atTop (𝓝 (1 - 0)) := by
      apply Tendsto.sub tendsto_const_nhds h_lim_mod
    rw [sub_zero] at h_lim
    exact h_lim
  have h3 := Tendsto.mul h1 h2
  rw [mul_one] at h3
  have h_eq2 : (fun K : ℕ => if K = 0 then (0 : ℝ) else lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) /
                                                          (K : ℝ)) =ᶠ[atTop]
                                                          (fun K : ℕ =>
                                                            lower_avg (K / M) *
                                                            (((K / M * M : ℕ) : ℝ) / (K : ℝ))) := by
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hK0 : K ≠ 0 := by omega
    have h_if : (if K = 0 then (0 : ℝ) else lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) / (K : ℝ)) =
        lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) / (K : ℝ) :=
        ite_eq_right_iff.mpr (fun h => (hK0 h).elim)
    rw [h_if]
    rw [mul_div_assoc]
  exact Tendsto.congr' h_eq2.symm h3

/-- Auxiliary for `isNormal_iff_isAlignedNormal_upper_limit`:
a bounded remainder `r K` does not change the limit of the rescaled bound. -/
private lemma isNormal_iff_isAlignedNormal_upper_limit_aux
    (M : ℕ) (hM : 0 < M) (upper_avg : ℕ → ℝ) (L C : ℝ) (r : ℕ → ℝ)
    (h_upper : Tendsto upper_avg atTop (𝓝 L)) (hr : ∀ K, |r K| ≤ C) :
    Tendsto (fun K : ℕ => if K = 0 then (0 : ℝ) else
      (upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) + r K) / (K : ℝ)) atTop (𝓝 L) := by
  have h_main := isNormal_iff_isAlignedNormal_lower_limit M hM
    upper_avg L h_upper
  have h_rem : Tendsto (fun K : ℕ => r K / (K : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hK_pos]
    exact div_le_div_of_nonneg_right (hr K) hK_pos.le
  have h_sum := h_main.add h_rem
  rw [add_zero] at h_sum
  refine h_sum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  have hK0 : K ≠ 0 := by omega
  simp only [hK0, ite_false, add_div]

private lemma isNormal_iff_isAlignedNormal_upper_limit
  (M : ℕ) (hM : 0 < M) (upper_avg : ℕ → ℝ) (L : ℝ)
  (h_upper : Tendsto upper_avg atTop (𝓝 L)) :
  Tendsto (fun K => if K = 0 then (0 : ℝ) else (upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) +
                                                 (K % M : ℝ)) / (K : ℝ)) atTop (𝓝 L) := by
  refine isNormal_iff_isAlignedNormal_upper_limit_aux M hM
    upper_avg L M _ h_upper fun K => ?_
  -- `(K % M : ℝ)` elaborates to the remainder `↑K % ↑M` of the Euclidean domain `ℝ`, which is `0`
  -- as `M ≠ 0`
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [EuclideanDomain.mod_eq_zero.mpr (Dvd.intro _ (mul_div_cancel₀ (K : ℝ) hM')), abs_zero]
  exact Nat.cast_nonneg M

/-- Step 3 of the proof of `isNormal_iff_isAlignedNormal_mpr`: arbitrary length K.
-/
private lemma isNormal_iff_isAlignedNormal_arbitrary
  (w : CantorSeq) (h : IsAlignedNormal w) (U : BitString) (hU : 1 ≤ U.length) (M : ℕ)
      (hM : U.length ≤ M) :
  ∃ (lower upper : ℕ → ℝ),
    (∀ K, lower K ≤ occurrenceFreq U w K ∧ occurrenceFreq U w K ≤ upper K) ∧
    Tendsto lower atTop (𝓝 ((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) / M)) ∧
    Tendsto upper atTop (𝓝 (((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) + (U.length - 1 : ℝ)) /
        M)) := by
  obtain ⟨lower_avg, upper_avg, havg, h_lower, h_upper⟩ :=
    isNormal_iff_isAlignedNormal_average w h U hU M hM
  have hM_pos : 0 < M := by omega
  let lower := fun K => if K = 0 then (0 : ℝ) else lower_avg (K / M) * ((K / M * M : ℕ) : ℝ) /
                                                     (K : ℝ)
  let upper := fun K => if K = 0 then (0 : ℝ) else (upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) +
                                                     ((K % M : ℕ) : ℝ)) / (K : ℝ)
  use lower, upper
  refine ⟨?_, ?_, ?_⟩
  · exact isNormal_iff_isAlignedNormal_bounds w U M lower_avg
      upper_avg havg
  · exact isNormal_iff_isAlignedNormal_lower_limit M hM_pos
      lower_avg _ h_lower
  · -- `step3_upper_limit` is stated with the field remainder `(K % M : ℝ)`, which is `0`;
    -- the natural remainder `K % M < M` only adds `((K % M : ℕ) : ℝ) / K`, which tends to `0`.
    have h3 : Tendsto (fun K => if K = 0 then (0 : ℝ) else
        (upper_avg (K / M) * ((K / M * M : ℕ) : ℝ) + (K % M : ℝ)) / (K : ℝ)) atTop
        (𝓝 (((2 : ℝ)⁻¹ ^ U.length * (M - U.length + 1 : ℝ) + (U.length - 1 : ℝ)) / M)) :=
      isNormal_iff_isAlignedNormal_upper_limit M hM_pos upper_avg _
          h_upper
    have hrem : Tendsto (fun K : ℕ => ((K % M : ℕ) : ℝ) / (K : ℝ)) atTop (𝓝 0) :=
      squeeze_zero (fun K => by positivity)
        (fun K => div_le_div_of_nonneg_right (by exact_mod_cast (Nat.mod_lt K hM_pos).le)
          (Nat.cast_nonneg K))
        (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ))
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM_pos.ne'
    have h4 := h3.add hrem
    rw [add_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hmod : (K : ℝ) % (M : ℝ) = 0 :=
      EuclideanDomain.mod_eq_zero.mpr (Dvd.intro _ (mul_div_cancel₀ (K : ℝ) hM'))
    simp only [upper, hK.ne', ↓reduceIte, hmod, add_zero, add_div]

/-- Step 4 of the proof of `isNormal_iff_isAlignedNormal_mpr`: assembly using
arbitrary M. -/
private lemma isNormal_iff_isAlignedNormal_mpr_assembly
  (w : CantorSeq) (U : BitString) (hU : 1 ≤ U.length) (q : ℝ) :
  (∀ M : ℕ, U.length ≤ M →
    ∃ (lower upper : ℕ → ℝ),
      (∀ K, lower K ≤ occurrenceFreq U w K ∧ occurrenceFreq U w K ≤ upper K) ∧
      Tendsto lower atTop (𝓝 (q * (M - U.length + 1 : ℝ) / M)) ∧
      Tendsto upper atTop (𝓝 ((q * (M - U.length + 1 : ℝ) + (U.length - 1 : ℝ)) / M))) →
  Tendsto (occurrenceFreq U w) atTop (𝓝 q) := by
  intro H
  let m := U.length
  have hm : 1 ≤ m := hU
  have hl : Tendsto (fun M : ℕ => q * (M - m + 1 : ℝ) / M) atTop (𝓝 q) := by
    have h_eq : (fun M : ℕ => q * (M - m + 1 : ℝ) / (M : ℝ)) =ᶠ[atTop] fun M :
        ℕ => q * (1 - (m - 1 : ℝ) / (M : ℝ)) := by
      filter_upwards [eventually_ge_atTop m] with M _hM
      have hM_pos : (M : ℝ) ≠ 0 := by
        intro h
        have : (M : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (hm.trans _hM)
        linarith
      calc q * ((M : ℝ) - m + 1) / (M : ℝ)
        _ = q * (((M : ℝ) - (m - 1 : ℝ)) / (M : ℝ)) := by ring
        _ = q * ((M : ℝ) / (M : ℝ) - (m - 1 : ℝ) / (M : ℝ)) := by rw [sub_div]
        _ = q * (1 - (m - 1 : ℝ) / (M : ℝ)) := by rw [div_self hM_pos]
    refine Tendsto.congr' h_eq.symm ?_
    have h_lim : Tendsto (fun M : ℕ => (m - 1 : ℝ) / (M : ℝ)) atTop (𝓝 0) := by
      exact tendsto_const_div_atTop_nhds_zero_nat (m - 1 : ℝ)
    have h_lim2 : Tendsto (fun M : ℕ => 1 - (m - 1 : ℝ) / (M : ℝ)) atTop (𝓝 (1 - 0)) := by
      exact Tendsto.const_sub 1 h_lim
    have h_lim3 : Tendsto (fun M : ℕ => q * (1 - (m - 1 : ℝ) / (M : ℝ))) atTop (𝓝 (q * (1 - 0))) :=
        by
      exact Tendsto.const_mul q h_lim2
    simpa using h_lim3
  have hu : Tendsto (fun M : ℕ => (q * (M - m + 1 : ℝ) + (m - 1 : ℝ)) / M) atTop (𝓝 q) := by
    have h_eq : (fun M : ℕ => (q * (M - m + 1 : ℝ) + (m - 1 : ℝ)) / (M : ℝ)) =ᶠ[atTop] fun M :
        ℕ => q * (1 - (m - 1 : ℝ) / (M : ℝ)) + (m - 1 : ℝ) / (M : ℝ) := by
      filter_upwards [eventually_ge_atTop m] with M _hM
      have hM_pos : (M : ℝ) ≠ 0 := by
        intro h
        have : (M : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (hm.trans _hM)
        linarith
      calc (q * ((M : ℝ) - m + 1) + (m - 1 : ℝ)) / (M : ℝ)
        _ = (q * (((M : ℝ) - (m - 1 : ℝ))) + (m - 1 : ℝ)) / (M : ℝ) := by ring
        _ = q * (((M : ℝ) - (m - 1 : ℝ))) / (M : ℝ) + (m - 1 : ℝ) / (M : ℝ) := by rw [add_div]
        _ = q * ((((M : ℝ) - (m - 1 : ℝ))) / (M : ℝ)) + (m - 1 : ℝ) / (M : ℝ) := by ring
        _ = q * (((M : ℝ) / (M : ℝ)) - ((m - 1 : ℝ) / (M : ℝ))) + (m - 1 : ℝ) / (M : ℝ) := by
          rw [sub_div]
        _ = q * (1 - (m - 1 : ℝ) / (M : ℝ)) + (m - 1 : ℝ) / (M : ℝ) := by rw [div_self hM_pos]
    refine Tendsto.congr' h_eq.symm ?_
    have h_lim : Tendsto (fun M : ℕ => (m - 1 : ℝ) / (M : ℝ)) atTop (𝓝 0) := by
      exact tendsto_const_div_atTop_nhds_zero_nat (m - 1 : ℝ)
    have h_lim2 : Tendsto (fun M : ℕ => q * (1 - (m - 1 : ℝ) / (M : ℝ))) atTop (𝓝 (q * (1 - 0))) :=
        by
      exact Tendsto.const_mul q (Tendsto.const_sub 1 h_lim)
    have h_lim3 : Tendsto (fun M : ℕ => q * (1 - (m - 1 : ℝ) / (M : ℝ)) + (m - 1 : ℝ) / (M : ℝ))
        atTop (𝓝 (q * (1 - 0) + 0)) := by
      exact Tendsto.add h_lim2 h_lim
    simpa using h_lim3
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hl hu
  obtain ⟨Nl, hNl⟩ := hl (ε / 2) (half_pos hε)
  obtain ⟨Nu, hNu⟩ := hu (ε / 2) (half_pos hε)
  let M := max (max Nl Nu) m
  have hMm : m ≤ M := le_max_right _ _
  obtain ⟨lower, upper, h_bound, h_lim_l, h_lim_u⟩ := H M hMm
  rw [Metric.tendsto_atTop] at h_lim_l h_lim_u
  obtain ⟨Nl2, hNl2⟩ := h_lim_l (ε / 2) (half_pos hε)
  obtain ⟨Nu2, hNu2⟩ := h_lim_u (ε / 2) (half_pos hε)
  use max Nl2 Nu2
  intro K hK
  have hK_l : Nl2 ≤ K := le_trans (le_max_left _ _) hK
  have hK_u : Nu2 ≤ K := le_trans (le_max_right _ _) hK
  have bound_l := h_bound K |>.1
  have bound_u := h_bound K |>.2
  have hlM := hNl M (le_trans (le_max_left _ _) (le_max_left _ _))
  have huM := hNu M (le_trans (le_max_right _ _) (le_max_left _ _))
  have hlK := hNl2 K hK_l
  have huK := hNu2 K hK_u
  rw [Real.dist_eq, abs_lt] at hlM huM hlK huK
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · linarith

/-- Step 2 of the proof of `isNormal_iff_isAlignedNormal`: aligned normality implies
non-aligned normality. -/
private theorem isNormal_iff_isAlignedNormal_mpr (w : CantorSeq) : IsAlignedNormal w →
    IsNormal w := by
  intro hw U
  by_cases h : U.length = 0
  · have h_eq : U = [] := by
      cases U
      · rfl
      · contradiction
    rw [h_eq]
    exact isNormal_of_isMisesChurchRandom_empty w
  · have hU : 1 ≤ U.length := Nat.pos_of_ne_zero h
    apply isNormal_iff_isAlignedNormal_mpr_assembly w U hU ((2 : ℝ)⁻¹ ^ U.length)
    intro M hM
    exact isNormal_iff_isAlignedNormal_arbitrary w hw U hU M hM

/-- **SUV Problem 255, p. 265.**  Aligned and non-aligned normality coincide. -/
theorem isNormal_iff_isAlignedNormal (w : CantorSeq) : IsNormal w ↔ IsAlignedNormal w :=
  ⟨isNormal_iff_isAlignedNormal_mp w, isNormal_iff_isAlignedNormal_mpr w⟩

end Kolmogorov.FrequencyGames
