/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelStage
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Converse
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.FinsetDeficiency
import KolmogorovMathlib.Prefix.Properties

/-!
# SUV Theorem 94(e): the permutation-invariant randomness criterion

SUV p. 151, Theorem 94(e): a sequence `w` is Martin-Löf random with respect to the uniform
measure if and only if `K(F, w(F)) ≥ |F| - c` for one constant `c` and every finite index set
`F ⊆ ℕ`.  This is A. Rumyantsev's index-permutation-invariant criterion.

The two halves are:

* `⇒` is Problem 144 (`problem_144_le_KPPair_of_isMartinLofRandom'`) for the uniform measure,
  together with the elementary computation `finsetEventMass uniformMeasure F Z = 2^(-|F|)`
  proved here (`finsetEventMass_uniformMeasure`);
* `⇐` is the source's own remark that "if `F` is an initial segment of `ℕ`, then `F` is
  determined by `w(F)` and can be eliminated, so we return to the previous statement":
  specialising the hypothesis to `F = Finset.range n` and using
  `KPPair U (finsetCode (range |x|)) x ≤ KPPlain U x + O(1)` reduces it to Theorem 94(d).

Theorem 94(d) itself lives in `LevinSchnorr/Criteria.lean`; to keep this module importable
*by* that file it is taken here as an explicit hypothesis `hd`.

## Main results

* `Kolmogorov.finsetEventMass_uniformMeasure` — `p_{F,Z} = 2^(-|F|)` for the uniform measure;
* `Kolmogorov.restrictSeq_range_eq_cantorPrefix` — `w(range n) = (w)_n`;
* `Kolmogorov.isMartinLofRandom_uniform_iff_le_KPPair_restrictSeq'` — Theorem 94(e).
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ### Counting the strings of a level prescribed on `F` -/

/-- A string of length `N` is determined by its restrictions to `F` and to the complement of
`F` inside `range N`. -/
lemma eq_of_restrictStr_eq {F : Finset ℕ} {N : ℕ} (_hFN : F ⊆ Finset.range N)
    {x y : BitString} (hx : x.length = N) (hy : y.length = N)
    (h1 : restrictStr F x = restrictStr F y)
    (h2 : restrictStr (Finset.range N \ F) x = restrictStr (Finset.range N \ F) y) :
    x = y := by
  simp only [restrictStr] at h1 h2
  have key : ∀ i, i < N → x.getD i false = y.getD i false := by
    intro i hi
    by_cases hiF : i ∈ F
    · exact List.map_inj_left.1 h1 i ((Finset.mem_sort (· ≤ ·)).2 hiF)
    · have hmem : i ∈ Finset.range N \ F := Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hi, hiF⟩
      exact List.map_inj_left.1 h2 i ((Finset.mem_sort (· ≤ ·)).2 hmem)
  refine List.ext_getElem (by rw [hx, hy]) fun i hi₁ hi₂ => ?_
  have hi : i < N := by rw [← hx]; exact hi₁
  have h := key i hi
  rwa [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂] at h

/-- At most `2^(N - |F|)` strings of length `N` restrict to a given `Z` on `F`. -/
lemma card_restrictSlice_le {F : Finset ℕ} {N : ℕ} (hFN : F ⊆ Finset.range N) (Z : BitString) :
    (restrictSlice F Z N).card ≤ 2 ^ (N - F.card) := by
  classical
  have hmem : ∀ x ∈ restrictSlice F Z N, x.length = N ∧ restrictStr F x = Z := by
    intro x hx
    rw [restrictSlice, Finset.mem_filter, mem_levelFinset] at hx
    exact hx
  have hcompl : (Finset.range N \ F).card = N - F.card := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.2 hFN]
  have hmap : Set.MapsTo (fun x => restrictStr (Finset.range N \ F) x)
      (restrictSlice F Z N : Set BitString) (levelFinset (N - F.card) : Set BitString) := by
    intro x _
    simp only [Finset.mem_coe, mem_levelFinset, length_restrictStr, hcompl]
  have hinj : Set.InjOn (fun x => restrictStr (Finset.range N \ F) x)
      (restrictSlice F Z N : Set BitString) := by
    intro x hx y hy h
    have hx' := hmem x (Finset.mem_coe.1 hx)
    have hy' := hmem y (Finset.mem_coe.1 hy)
    exact eq_of_restrictStr_eq hFN hx'.1 hy'.1 (hx'.2.trans hy'.2.symm) h
  have h := Finset.card_le_card_of_injOn _ hmap hinj
  rwa [card_levelFinset] at h

/-- Sorting the strings of level `N` by their restriction to `F` partitions level `N`. -/
lemma sum_card_restrictSlice {F : Finset ℕ} {N : ℕ} :
    ∑ Z ∈ levelFinset F.card, (restrictSlice F Z N).card = 2 ^ N := by
  classical
  have hmaps : Set.MapsTo (fun x => restrictStr F x)
      (levelFinset N : Set BitString) (levelFinset F.card : Set BitString) := by
    intro x _
    simp only [Finset.mem_coe, mem_levelFinset, length_restrictStr]
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [card_levelFinset] at h
  rw [h]
  refine Finset.sum_congr rfl fun Z _ => congrArg Finset.card ?_
  rw [restrictSlice]

/-- Exactly `2^(N - |F|)` strings of length `N` restrict to a given `Z` on `F`. -/
lemma card_restrictSlice {F : Finset ℕ} {N : ℕ} (hFN : F ⊆ Finset.range N)
    {Z : BitString} (hZ : Z.length = F.card) :
    (restrictSlice F Z N).card = 2 ^ (N - F.card) := by
  have hcard : F.card ≤ N := by
    have h := Finset.card_le_card hFN
    rwa [Finset.card_range] at h
  have hle : ∀ Z' ∈ levelFinset F.card, (restrictSlice F Z' N).card ≤ 2 ^ (N - F.card) :=
    fun Z' _ => card_restrictSlice_le hFN Z'
  have hsum : ∑ Z' ∈ levelFinset F.card, (restrictSlice F Z' N).card
      = ∑ _Z' ∈ levelFinset F.card, 2 ^ (N - F.card) := by
    rw [sum_card_restrictSlice, Finset.sum_const, card_levelFinset, smul_eq_mul,
      ← pow_add]
    congr 1
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).1 hsum Z (mem_levelFinset.2 hZ)

/-! ### The uniform mass of the event `w(F) = Z` -/

/-- SUV p. 151 (Theorem 94(e)): for the uniform measure `p_{F,Z} = 2^(-|F|)` whenever the
length of `Z` is the cardinality of `F`. -/
theorem finsetEventMass_uniformMeasure (F : Finset ℕ) {Z : BitString} (hZ : Z.length = F.card) :
    finsetEventMass uniformMeasure F Z = (2 : ℝ≥0∞)⁻¹ ^ F.card := by
  classical
  obtain ⟨N, hFN⟩ := Finset.exists_nat_subset_range F
  have hF : ∀ i ∈ F, i < N := fun i hi => Finset.mem_range.1 (hFN hi)
  have hcard : F.card ≤ N := by
    have h := Finset.card_le_card hFN
    rwa [Finset.card_range] at h
  have hconst : ∀ x ∈ restrictSlice F Z N,
      cantorMass uniformMeasure x = (2 : ℝ≥0∞)⁻¹ ^ N := by
    intro x hx
    rw [restrictSlice, Finset.mem_filter, mem_levelFinset] at hx
    rw [cantorMass_uniformMeasure, hx.1]
  have key : ((2 : ℝ≥0∞) ^ (N - F.card)) * ((2 : ℝ≥0∞)⁻¹) ^ N = ((2 : ℝ≥0∞)⁻¹) ^ F.card := by
    have hN : N = (N - F.card) + F.card := by omega
    calc ((2 : ℝ≥0∞) ^ (N - F.card)) * ((2 : ℝ≥0∞)⁻¹) ^ N
        = ((2 : ℝ≥0∞) ^ (N - F.card))
            * (((2 : ℝ≥0∞)⁻¹) ^ (N - F.card) * ((2 : ℝ≥0∞)⁻¹) ^ F.card) := by
          rw [← pow_add, ← hN]
      _ = (((2 : ℝ≥0∞) ^ (N - F.card)) * ((2 : ℝ≥0∞)⁻¹) ^ (N - F.card))
            * ((2 : ℝ≥0∞)⁻¹) ^ F.card := by ring
      _ = ((2 : ℝ≥0∞)⁻¹) ^ F.card := by
          rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
  rw [finsetEventMass_eq_sum uniformMeasure hF Z, Finset.sum_congr rfl hconst, Finset.sum_const,
    card_restrictSlice hFN hZ, nsmul_eq_mul]
  push_cast
  exact key

/-! ### Initial segments -/

/-- SUV p. 150: the restriction of `w` to an initial segment is the corresponding prefix. -/
lemma restrictSeq_range_eq_cantorPrefix (w : CantorSeq) (n : ℕ) :
    restrictSeq (Finset.range n) w = cantorPrefix w n := by
  rw [restrictSeq, Finset.sort_range]
  refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
  rw [List.getElem_map, List.getElem_range, cantorPrefix_getElem]

/-! ### Theorem 94(e) -/

/-- **SUV Theorem 94(e)** (Section 5.6, p. 151): `w` is Martin-Löf random with respect to the
uniform measure if and only if `K(F, w(F)) ≥ |F| - c` for some `c` and all finite index sets
`F ⊆ ℕ`.

Theorem 94(d) (`isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix` of
`LevinSchnorr/Criteria.lean`) is taken as the hypothesis `hd` so that this module can be
imported by that file. -/
theorem isMartinLofRandom_uniform_iff_le_KPPair_restrictSeq' {U : Map}
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq)
    (hd : IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ KPPlain U (cantorPrefix w n) + c) :
    IsMartinLofRandom uniformMeasure w ↔
      ∃ c : ℕ, ∀ F : Finset ℕ,
        (F.card : ℕ∞) ≤ KPPair U (finsetCode F) (restrictSeq F w) + c := by
  have hinv : ∀ c : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    intro c
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  constructor
  · intro hw
    obtain ⟨c, hc⟩ :=
      problem_144_le_KPPair_of_isMartinLofRandom' isComputableMeasure_uniform hU hw
    refine ⟨c, fun F => ?_⟩
    have hmass := hc F
    rw [finsetEventMass_uniformMeasure F (length_restrictSeq F w)] at hmass
    rcases eq_or_ne (KPPair U (finsetCode F) (restrictSeq F w)) ⊤ with htop | hfin
    · rw [htop]
      exact le_top
    · refine le_add_nat_of_complexityWeight_le hfin ?_
      rw [complexityWeight_coe]
      calc ((2 : ℝ≥0∞)⁻¹) ^ c * complexityWeight (KPPair U (finsetCode F) (restrictSeq F w))
          ≤ ((2 : ℝ≥0∞)⁻¹) ^ c * ((2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹) ^ F.card) := by
            gcongr
        _ = ((2 : ℝ≥0∞)⁻¹) ^ F.card := by rw [← mul_assoc, hinv c, one_mul]
  · rintro ⟨c, hc⟩
    rw [hd]
    have hcomp : Computable fun x : BitString => finsetCode (Finset.range x.length) :=
      computable_finsetCode.comp (computable_finsetRange.comp Computable.list_length)
    obtain ⟨c', hc'⟩ := KPPair_map_left_le_KPPlain U hU
      (fun x => finsetCode (Finset.range x.length)) hcomp
    refine ⟨c' + c, fun n => ?_⟩
    have h1 := hc (Finset.range n)
    rw [Finset.card_range, restrictSeq_range_eq_cantorPrefix] at h1
    have h2 := hc' (cantorPrefix w n)
    rw [cantorPrefix_length] at h2
    calc (n : ℕ∞)
        ≤ KPPair U (finsetCode (Finset.range n)) (cantorPrefix w n) + (c : ℕ∞) := h1
      _ ≤ (KPPlain U (cantorPrefix w n) + (c' : ℕ∞)) + (c : ℕ∞) := add_le_add h2 (le_refl _)
      _ = KPPlain U (cantorPrefix w n) + ((c' + c : ℕ) : ℕ∞) := by
          push_cast
          rw [add_assoc]

/-! ### Problem 145 for the natural exhaustion

SUV Problem 145 (p. 150) asks for an *arbitrary* increasing computable exhaustion `F` of `ℕ`.
The source proof first uses a computable permutation of the indices to make the `F i` initial
segments (transporting `μ` along it) and then appeals to Problem 143.  That permutation step is
a genuinely new construction; what is recorded here is the case where the `F i` already *are*
initial segments, which needs no permutation and where the event `v(range i) = (w)_i` is
literally the cylinder `Ω_{(w)_i}`.
-/

/-- For an initial segment the event `v(F) = w(F)` is exactly a cylinder. -/
lemma finsetEventMass_range (μ : Measure CantorSeq) (w : CantorSeq) (n : ℕ) :
    finsetEventMass μ (Finset.range n) (cantorPrefix w n) = cantorMass μ (cantorPrefix w n) := by
  rw [finsetEventMass, cantorMass]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, cantorCylinder, restrictSeq_range_eq_cantorPrefix]
  constructor
  · intro h
    exact (isCantorPrefix_iff_cantorPrefix_eq _ v).2 (by rw [cantorPrefix_length]; exact h)
  · intro h
    have h' := (isCantorPrefix_iff_cantorPrefix_eq _ v).1 h
    rwa [cantorPrefix_length] at h'

/-- **SUV Problem 145** (Section 5.6, p. 150) for the natural exhaustion `F i = range i`: if
`K(range i, (w)_i) ≥ -log p_{range i, (w)_i} - c` for some `c` and all `i`, then `w` is
Martin-Löf random with respect to `μ`.  (The general case needs the source's permutation of
indices; see the section docstring.) -/
theorem problem_145_range_isMartinLofRandom {μ : Measure CantorSeq} [IsProbabilityMeasure μ]
    (hμ : IsComputableMeasure μ) {U : Map} (hU : IsOptimalPrefixConditional U) {w : CantorSeq}
    (hw : ∃ c : ℕ, ∀ i : ℕ,
      complexityWeight (KPPair U (finsetCode (Finset.range i)) (restrictSeq (Finset.range i) w))
        ≤ (2 : ℝ≥0∞) ^ c
          * finsetEventMass μ (Finset.range i) (restrictSeq (Finset.range i) w)) :
    IsMartinLofRandom μ w := by
  obtain ⟨c, hc⟩ := hw
  have hcomp : Computable fun x : BitString => finsetCode (Finset.range x.length) :=
    computable_finsetCode.comp (computable_finsetRange.comp Computable.list_length)
  obtain ⟨c₀, hc₀⟩ := KPPair_map_left_le_KPPlain U hU
    (fun x => finsetCode (Finset.range x.length)) hcomp
  have hinv : (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞)⁻¹) ^ c₀ = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  refine isMartinLofRandom_of_boundedPrefixDeficiency_core hμ hU ⟨c₀ + c, fun n => ?_⟩
  have h1 := hc n
  rw [restrictSeq_range_eq_cantorPrefix, finsetEventMass_range] at h1
  have h2 := hc₀ (cantorPrefix w n)
  rw [cantorPrefix_length] at h2
  have h3 : complexityWeight (KPPlain U (cantorPrefix w n)) * ((2 : ℝ≥0∞)⁻¹) ^ c₀
      ≤ complexityWeight (KPPair U (finsetCode (Finset.range n)) (cantorPrefix w n)) := by
    have h := complexityWeight_le_of_le h2
    rwa [complexityWeight_add_nat] at h
  calc complexityWeight (KPPlain U (cantorPrefix w n))
      = (2 : ℝ≥0∞) ^ c₀
          * (complexityWeight (KPPlain U (cantorPrefix w n)) * ((2 : ℝ≥0∞)⁻¹) ^ c₀) := by
        rw [show (2 : ℝ≥0∞) ^ c₀
              * (complexityWeight (KPPlain U (cantorPrefix w n)) * ((2 : ℝ≥0∞)⁻¹) ^ c₀)
            = complexityWeight (KPPlain U (cantorPrefix w n))
              * ((2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞)⁻¹) ^ c₀) from by ring, hinv, mul_one]
    _ ≤ (2 : ℝ≥0∞) ^ c₀ * ((2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)) :=
        mul_le_mul' le_rfl (le_trans h3 h1)
    _ = (2 : ℝ≥0∞) ^ (c₀ + c) * cantorMass μ (cantorPrefix w n) := by
        rw [pow_add, mul_assoc]

end Kolmogorov
