/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.IndependentTrials

/-!
# Vovk Dichotomy

Vovk's dichotomy for independent trials, after Shen, Uspensky and Vereshchagin, "Kolmogorov
complexity and algorithmic randomness", Theorems 196 and 197.

* `summable_sq_condOne_sub`: a sequence that is Martin-Löf random for two computable measures has
  square-summable differences of the conditional probabilities of `1`.
* `not_isMartinLofRandom_and_of_not_summable`: for computable product measures with
  `∑ (p_i - p'_i)²` infinite, no sequence is Martin-Löf random for both.
* `kakutani_absolutelyContinuous`, `kakutani_mutuallySingular`: Kakutani's dichotomy for product
  measures with success probabilities bounded away from `0` and `1`.
* `exists_measures_close_along_not_elsewhere`: two computable measures and a sequence random for
  both, although their conditional probabilities along another sequence are not square-summably
  close.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- **SUV Theorem 197, p. 299 (Vovk).**  If `ω` is Martin-Löf random with respect to two computable
measures, then the conditional probabilities of `1` along `ω` have a square-summable difference.

The book assumes that these conditional probabilities are in `(ε, 1 - ε)`.  This is the library's
`vovk_merging_summable`, which does not need that assumption, so the statement here is stronger.
The ratios are well defined along `ω` by `random_prefix_mass_pos`. -/
theorem summable_sq_condOne_sub {μ μ' : Measure CantorSeq} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hμ : IsComputableMeasure μ) (hμ' : IsComputableMeasure μ')
    {w : CantorSeq} (hw : IsMartinLofRandom μ w) (hw' : IsMartinLofRandom μ' w) :
    Summable fun n => (condOne μ (cantorPrefix w n) - condOne μ' (cantorPrefix w n)) ^ 2 := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  have h := MDLPrediction.vovk_merging_summable U hU μ μ' hμ hμ' w hw hw'
  refine h.congr fun n => ?_
  have hm := (MDLPrediction.random_prefix_mass_pos U hU μ hμ w hw n).ne'
  have hm' := (MDLPrediction.random_prefix_mass_pos U hU μ' hμ' w hw' n).ne'
  have h1 := condProb_cantorMass_add_eq_one μ hm
  have h2 := condProb_cantorMass_add_eq_one μ' hm'
  simp only [condOne]
  rw [show condProb (cantorMass μ) (cantorPrefix w n) false =
      1 - condProb (cantorMass μ) (cantorPrefix w n) true by linarith,
    show condProb (cantorMass μ') (cantorPrefix w n) false =
      1 - condProb (cantorMass μ') (cantorPrefix w n) true by linarith]
  ring

/-- **SUV Theorem 196(b), p. 297 (Vovk).**  If `∑ (p_i - p'_i)²` is infinite, the classes of
Martin-Löf random sequences for the two product measures are disjoint.  This strengthens the
printed statement by dropping uniform separation from `0` and `1`; Theorem 197, as proved in the
library, gives the conclusion along a common random sequence without that separation. -/
theorem not_isMartinLofRandom_and_of_not_summable {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1) (hc : IsComputableProbSeq p)
    (hc' : IsComputableProbSeq p')
    (hsum : ¬ Summable fun i => ((p i : ℝ) - p' i) ^ 2) (w : CantorSeq) :
    ¬ (IsMartinLofRandom (independentTrials p hp) w ∧
        IsMartinLofRandom (independentTrials p' hp') w) := by
  rintro ⟨hw, hw'⟩
  have hμ := isComputableMeasure_independentTrials hp hc
  have hμ' := isComputableMeasure_independentTrials hp' hc'
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  refine hsum ((summable_sq_condOne_sub hμ hμ' hw hw').congr fun n => ?_)
  have hm := (MDLPrediction.random_prefix_mass_pos U hU _ hμ w hw n).ne'
  have hm' := (MDLPrediction.random_prefix_mass_pos U hU _ hμ' w hw' n).ne'
  rw [condOne_independentTrials p hp hm, condOne_independentTrials p' hp' hm', cantorPrefix_length]

private lemma kakutani_absolutelyContinuous_massR_append (p : ℕ → NNReal) (hp : ∀ i, p i ≤ 1)
    (x : BitString) (b : Bool) :
    massR (independentTrials p hp) (x ++ [b]) =
      massR (independentTrials p hp) x * (if b then (p x.length : ℝ) else 1 - (p x.length : ℝ)) :=
          by
  rw [massR_independentTrials, massR_independentTrials]
  have hlen : (x ++ [b]).length = x.length + 1 := by simp
  have h1 : (∏ i : Fin (x ++ [b]).length, if (x ++ [b])[i] then (p i : ℝ) else 1 - (p i : ℝ)) =
      ∏ i : Fin (x.length + 1), if (x ++ [b])[i.val]'(by omega) then (p i.val : ℝ)
        else 1 - (p i.val : ℝ) :=
    Fintype.prod_equiv (finCongr hlen) _ _ (fun i => rfl)
  rw [h1, Fin.prod_univ_castSucc]
  congr 1
  · apply Fintype.prod_congr
    intro i
    have h2 : (x ++ [b])[i.castSucc.val]'(by omega) = x[i] := List.getElem_append_left i.isLt
    have hcast : i.castSucc.val = i.val := rfl
    rw [h2, hcast]
  · have h3 : (x ++ [b])[(Fin.last x.length).val]'(by omega) = b := by
      simp
    rw [h3]
    rfl

private lemma kakutani_absolutelyContinuous_sum_levelFinset_succ (n : ℕ) (f : BitString → ℝ) :
    ∑ x ∈ levelFinset (n + 1), f x =
      ∑ x ∈ levelFinset n, (f (x ++ [false]) + f (x ++ [true])) := by
  have H : ∑ x ∈ levelFinset (n + 1), f x = ((levelList (n + 1)).map f).sum := by
    rw [sum_levelFinset_eq_sum_levelList]
  rw [H]
  change (((levelList n).map (fun x => x ++ [false]) ++
    (levelList n).map (fun x => x ++ [true])).map f).sum = _
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  have h1 : (List.map (fun x => f (x ++ [false])) (levelList n)).sum =
    ∑ x ∈ levelFinset n, f (x ++ [false]) := by
    rw [← sum_levelFinset_eq_sum_levelList]
  have h2 : (List.map (fun x => f (x ++ [true])) (levelList n)).sum =
    ∑ x ∈ levelFinset n, f (x ++ [true]) := by
    rw [← sum_levelFinset_eq_sum_levelList]
  have heq1 : (List.map (f ∘ fun x => x ++ [false]) (levelList n)).sum =
    (List.map (fun x => f (x ++ [false])) (levelList n)).sum := rfl
  have heq2 : (List.map (f ∘ fun x => x ++ [true]) (levelList n)).sum =
    (List.map (fun x => f (x ++ [true])) (levelList n)).sum := rfl
  rw [heq1, heq2, h1, h2, ← Finset.sum_add_distrib]

private lemma kakutani_absolutelyContinuous_factor_eq {a b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    a ^ 2 / b + (1 - a) ^ 2 / (1 - b) = 1 + (a - b) ^ 2 / (b * (1 - b)) := by
  have h1 : (1 - b) ≠ 0 := by linarith
  field_simp
  ring

private lemma kakutani_absolutelyContinuous_level_sum_succ {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1)
    (hl' : ∀ i, 0 < (p' i : ℝ)) (hu' : ∀ i, (p' i : ℝ) < 1) (n : ℕ) :
    ∑ x ∈ levelFinset (n + 1), massR (independentTrials p hp) x ^ 2 /
        massR (independentTrials p' hp') x =
      (∑ x ∈ levelFinset n, massR (independentTrials p hp) x ^ 2 /
        massR (independentTrials p' hp') x) *
      ((p n : ℝ) ^ 2 / p' n + (1 - (p n : ℝ)) ^ 2 / (1 - p' n)) := by
  rw [kakutani_absolutelyContinuous_sum_levelFinset_succ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxl : x.length = n := mem_levelFinset.1 hx
  rw [kakutani_absolutelyContinuous_massR_append, kakutani_absolutelyContinuous_massR_append,
    kakutani_absolutelyContinuous_massR_append, kakutani_absolutelyContinuous_massR_append, hxl]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  have h1 : (1 - (p' n : ℝ)) ≠ 0 := by linarith [hu' n]
  have h2 : (p' n : ℝ) ≠ 0 := (hl' n).ne'
  by_cases hm : massR (independentTrials p' hp') x = 0
  · simp [hm]
  · field_simp
    ring

private lemma kakutani_absolutelyContinuous_level_sum_eq_prod {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1)
    (hl' : ∀ i, 0 < (p' i : ℝ)) (hu' : ∀ i, (p' i : ℝ) < 1) (n : ℕ) :
    ∑ x ∈ levelFinset n, massR (independentTrials p hp) x ^ 2 /
        massR (independentTrials p' hp') x =
      ∏ i ∈ Finset.range n, ((p i : ℝ) ^ 2 / p' i + (1 - (p i : ℝ)) ^ 2 / (1 - p' i)) := by
  induction n with
  | zero =>
    have : levelFinset 0 = {[]} := by
      ext y; simp
    rw [this]
    have h1 : massR (independentTrials p hp) [] = 1 := by
      rw [massR_independentTrials]; simp
    have h2 : massR (independentTrials p' hp') [] = 1 := by
      rw [massR_independentTrials]; simp
    simp [h1, h2]
  | succ n ih =>
    rw [kakutani_absolutelyContinuous_level_sum_succ hp hp' hl' hu' n, ih, Finset.prod_range_succ]

private lemma kakutani_absolutelyContinuous_level_sum_bound {ε : ℝ} (hε : 0 < ε)
    {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1)
    (hl' : ∀ i, ε < p' i) (hu' : ∀ i, (p' i : ℝ) < 1 - ε)
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) :
    ∃ C : ℝ, ∀ n : ℕ, ∑ x ∈ levelFinset n, massR (independentTrials p hp) x ^ 2 /
        massR (independentTrials p' hp') x ≤ C := by
  have hl0 : ∀ i, 0 < (p' i : ℝ) := fun i => hε.trans (hl' i)
  have hu1 : ∀ i, (p' i : ℝ) < 1 := fun i => by linarith [hu' i]
  refine ⟨Real.exp ((∑' i, ((p i : ℝ) - p' i) ^ 2) / ε ^ 2), fun n => ?_⟩
  rw [kakutani_absolutelyContinuous_level_sum_eq_prod hp hp' hl0 hu1 n]
  have hfac : ∀ i, ((p i : ℝ) ^ 2 / p' i + (1 - (p i : ℝ)) ^ 2 / (1 - p' i)) ≤
      Real.exp (((p i : ℝ) - p' i) ^ 2 / ε ^ 2) := by
    intro i
    rw [kakutani_absolutelyContinuous_factor_eq (hl0 i) (hu1 i)]
    have hexp := Real.add_one_le_exp (((p i : ℝ) - p' i) ^ 2 / ε ^ 2)
    suffices hd : ((p i : ℝ) - p' i) ^ 2 / ((p' i : ℝ) * (1 - p' i)) ≤
        ((p i : ℝ) - p' i) ^ 2 / ε ^ 2 by
      linarith
    have hden : ε ^ 2 ≤ (p' i : ℝ) * (1 - p' i) := by
      have h1 := hl' i
      have h2 : ε < 1 - (p' i : ℝ) := by linarith [hu' i]
      nlinarith
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  calc ∏ i ∈ Finset.range n, ((p i : ℝ) ^ 2 / p' i + (1 - (p i : ℝ)) ^ 2 / (1 - p' i))
      ≤ ∏ i ∈ Finset.range n, Real.exp (((p i : ℝ) - p' i) ^ 2 / ε ^ 2) := by
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => hfac i)
        have h1 : (0 : ℝ) < 1 - p' i := by linarith [hu1 i]
        have := hl0 i
        positivity
    _ = Real.exp (∑ i ∈ Finset.range n, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp ((∑' i, ((p i : ℝ) - p' i) ^ 2) / ε ^ 2) := by
        apply Real.exp_le_exp.2
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right (hsum.sum_le_tsum _ (fun i _ => sq_nonneg _))
          (by positivity)

private lemma kakutani_absolutelyContinuous_cs {μ μ' : Measure CantorSeq} {C : ℝ}
    (hpos : ∀ x, 0 < massR μ' x)
    (hC : ∀ n, ∑ x ∈ levelFinset n, massR μ x ^ 2 / massR μ' x ≤ C)
    (n : ℕ) (T : Finset BitString) (hT : ∀ x ∈ T, x.length = n) :
    (∑ x ∈ T, massR μ x) ^ 2 ≤ C * ∑ x ∈ T, massR μ' x := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS : 0 < ∑ x ∈ T, massR μ' x := Finset.sum_pos (fun x _ => hpos x) hne
  have h1 := Finset.sq_sum_div_le_sum_sq_div T (massR μ) (g := massR μ') (fun x _ => hpos x)
  have h2 : ∑ x ∈ T, massR μ x ^ 2 / massR μ' x ≤
      ∑ x ∈ levelFinset n, massR μ x ^ 2 / massR μ' x :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => mem_levelFinset.2 (hT x hx))
      (fun x _ _ => div_nonneg (sq_nonneg _) (hpos _).le)
  have h3 := h1.trans (h2.trans (hC n))
  rw [div_le_iff₀ hS] at h3
  exact h3

private lemma kakutani_absolutelyContinuous_open_approx {U : Set CantorSeq} (hU : IsOpen U)
    (w : CantorSeq) (hw : w ∈ U) :
    ∃ m, cantorCylinder (cantorPrefix w m) ⊆ U := by
  obtain ⟨t, ⟨x, rfl⟩, hwt, htU⟩ :=
    isTopologicalBasis_cantorCylinders.mem_nhds_iff.1 (hU.mem_nhds hw)
  refine ⟨x.length, fun v hv => htU ?_⟩
  have := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hwt
  rw [this] at hv
  exact hv

private lemma kakutani_absolutelyContinuous_ac_of_level_bound {μ μ' : Measure CantorSeq}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (n : ℕ) (T : Finset BitString), (∀ x ∈ T, x.length = n) →
      (∑ x ∈ T, massR μ x) ^ 2 ≤ C * ∑ x ∈ T, massR μ' x) :
    μ ≪ μ' := by
  classical
  have key : ∀ U : Set CantorSeq, IsOpen U →
      μ U ≤ ENNReal.ofReal (Real.sqrt (C * (μ' U).toReal)) := by
    intro U hU
    let Un : ℕ → Set CantorSeq := fun n => {w | ∃ m ≤ n, cantorCylinder (cantorPrefix w m) ⊆ U}
    let T : ℕ → Finset BitString := fun n =>
      (levelFinset n).filter (fun x => ∃ m ≤ n, cantorCylinder (x.take m) ⊆ U)
    have hUn : ∀ n, Un n = ⋃ x ∈ T n, cantorCylinder x := by
      intro n
      ext w
      simp only [Un, T, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, mem_levelFinset,
        exists_prop]
      constructor
      · rintro ⟨m, hm, h⟩
        refine ⟨cantorPrefix w n, ⟨cantorPrefix_length w n, m, hm, ?_⟩,
          mem_cantorCylinder_cantorPrefix w n⟩
        rw [cantorPrefix_take w m n hm]
        exact h
      · rintro ⟨x, ⟨hxl, m, hm, h⟩, hw⟩
        have hx : cantorPrefix w n = x := by
          rw [← hxl]; exact (isCantorPrefix_iff_cantorPrefix_eq x w).1 hw
        refine ⟨m, hm, ?_⟩
        rw [← cantorPrefix_take w m n hm, hx]
        exact h
    have hsub : ∀ n, Un n ⊆ U := by
      rintro n w ⟨m, -, h⟩
      exact h (mem_cantorCylinder_cantorPrefix w m)
    have hmono : Monotone Un := fun a b hab w ⟨m, hm, h⟩ => ⟨m, hm.trans hab, h⟩
    have hunion : U = ⋃ n, Un n := by
      refine Set.Subset.antisymm (fun w hw => ?_) (Set.iUnion_subset hsub)
      obtain ⟨m, hm⟩ := kakutani_absolutelyContinuous_open_approx hU w hw
      exact Set.mem_iUnion.2 ⟨m, m, le_rfl, hm⟩
    have hU_eq : μ U = ⨆ n, μ (Un n) := by
      rw [← hmono.measure_iUnion, ← hunion]
    rw [hU_eq]
    refine iSup_le fun n => ?_
    have hmeas : ∀ (ν : Measure CantorSeq), ν (Un n) = ∑ x ∈ T n, cantorMass ν x := by
      intro ν
      rw [hUn n, measure_biUnion_finset
        (cantorCylinder_pairwiseDisjoint n (T n)
          (fun x hx => mem_levelFinset.1 (Finset.mem_filter.1 hx).1))
        (fun x _ => measurableSet_cantorCylinder x)]
      rfl
    have hreal : ∀ (ν : Measure CantorSeq) [IsFiniteMeasure ν],
        (ν (Un n)).toReal = ∑ x ∈ T n, massR ν x := by
      intro ν _
      rw [hmeas ν]
      exact ENNReal.toReal_sum (s := T n) (f := fun x => cantorMass ν x)
        (fun x _ => measure_ne_top _ _)
    have hlev := hC n (T n) (fun x hx => mem_levelFinset.1 (Finset.mem_filter.1 hx).1)
    rw [← hreal μ, ← hreal μ'] at hlev
    have hle : (μ' (Un n)).toReal ≤ (μ' U).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsub n))
    have hX : (μ (Un n)).toReal ^ 2 ≤ C * (μ' U).toReal :=
      hlev.trans (mul_le_mul_of_nonneg_left hle hC0)
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.sqrt_nonneg _)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hX)
  intro A hA
  by_contra hne
  have hfin : μ A ≠ ⊤ := measure_ne_top _ _
  have hapos : 0 < (μ A).toReal := ENNReal.toReal_pos hne hfin
  set a := (μ A).toReal with ha
  set δ := a ^ 2 / (2 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨U, hAU, hUo, hUlt⟩ := Set.exists_isOpen_lt_of_lt A (ENNReal.ofReal δ)
    (by rw [hA]; simpa using hδpos)
  have h1 : μ A ≤ ENNReal.ofReal (Real.sqrt (C * (μ' U).toReal)) :=
    (measure_mono hAU).trans (key U hUo)
  have h2 : (μ' U).toReal ≤ δ :=
    (ENNReal.toReal_le_of_le_ofReal hδpos.le hUlt.le)
  have h3 : a ≤ Real.sqrt (C * (μ' U).toReal) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  have h4 : a ^ 2 ≤ C * (μ' U).toReal := by
    have hX : 0 ≤ C * (μ' U).toReal := mul_nonneg hC0 ENNReal.toReal_nonneg
    calc a ^ 2 ≤ (Real.sqrt (C * (μ' U).toReal)) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt hX
  have h5 : C * δ ≤ a ^ 2 / 2 := by
    rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg a, hC0]
  have h6 : C * (μ' U).toReal ≤ C * δ := mul_le_mul_of_nonneg_left h2 hC0
  nlinarith [sq_pos_of_pos hapos]

/-- **SUV Problem 276, p. 299 (Kakutani).**  For sequences in `(ε, 1 - ε)`, not necessarily
computable:
(a) if `∑ (p_i - p'_i)² < ∞`, the two measures have the same null sets;
(b) if `∑ (p_i - p'_i)² = ∞`, the two measures are orthogonal. -/
theorem kakutani_absolutelyContinuous {ε : ℝ} (hε : 0 < ε) {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1) (hl : ∀ i, ε < p i) (hu : ∀ i, (p i : ℝ) < 1 - ε)
    (hl' : ∀ i, ε < p' i) (hu' : ∀ i, (p' i : ℝ) < 1 - ε)
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) :
    independentTrials p hp ≪ independentTrials p' hp' ∧
      independentTrials p' hp' ≪ independentTrials p hp := by
  have hpos : ∀ (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1), (∀ i, ε < q i) →
      (∀ i, (q i : ℝ) < 1 - ε) → ∀ x, 0 < massR (independentTrials q hq) x := by
    intro q hq hl hu x
    rw [massR_independentTrials]
    refine Finset.prod_pos fun i _ => ?_
    split_ifs
    · exact hε.trans (hl _)
    · have := hu i
      linarith
  obtain ⟨C, hC⟩ := kakutani_absolutelyContinuous_level_sum_bound hε hp hp' hl' hu' hsum
  obtain ⟨C', hC'⟩ := kakutani_absolutelyContinuous_level_sum_bound hε hp' hp hl hu
    (hsum.congr fun i => by ring)
  refine ⟨?_, ?_⟩
  · refine kakutani_absolutelyContinuous_ac_of_level_bound (C := max C 0) (le_max_right _ _) ?_
    intro n T hT
    exact (kakutani_absolutelyContinuous_cs (hpos p' hp' hl' hu') hC n T hT).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Finset.sum_nonneg fun x _ => ENNReal.toReal_nonneg))
  · refine kakutani_absolutelyContinuous_ac_of_level_bound (C := max C' 0) (le_max_right _ _) ?_
    intro n T hT
    exact (kakutani_absolutelyContinuous_cs (hpos p hp hl hu) hC' n T hT).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Finset.sum_nonneg fun x _ => ENNReal.toReal_nonneg))

/-- The Hellinger affinity of the two Bernoulli distributions in coordinate `i`. -/
private noncomputable def kakutani_mutuallySingular_affinity (p p' : ℕ → NNReal) (i : ℕ) : ℝ :=
  Real.sqrt ((p i : ℝ) * p' i) + Real.sqrt ((1 - (p i : ℝ)) * (1 - (p' i : ℝ)))

/-- Step 1 of the proof of `kakutani_mutuallySingular`: the affinity of two Bernoulli
laws is at most one minus a quarter of the squared difference of their parameters. -/
private lemma kakutani_mutuallySingular_affinity_bound {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 - (a - b) ^ 2 / 4 := by
  have hsq (u v : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
      (u - v) ^ 2 ≤ 4 * (Real.sqrt u - Real.sqrt v) ^ 2 := by
    have hs : (Real.sqrt u + Real.sqrt v) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      linarith [Real.sqrt_le_one.mpr hu1, Real.sqrt_le_one.mpr hv1]
    calc
      (u - v) ^ 2 = (Real.sqrt u - Real.sqrt v) ^ 2 *
          (Real.sqrt u + Real.sqrt v) ^ 2 := by
        calc
          (u - v) ^ 2 = ((Real.sqrt u) ^ 2 - (Real.sqrt v) ^ 2) ^ 2 := by
            rw [Real.sq_sqrt hu, Real.sq_sqrt hv]
          _ = _ := by ring
      _ ≤ (Real.sqrt u - Real.sqrt v) ^ 2 * 4 := by
        nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.sqrt u - Real.sqrt v))]
      _ = _ := by ring
  have h1 := hsq a b ha ha1 hb hb1
  have h2 := hsq (1 - a) (1 - b) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [Real.sqrt_mul ha, Real.sqrt_mul (sub_nonneg.mpr ha1)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sq_sqrt (sub_nonneg.mpr ha1), Real.sq_sqrt (sub_nonneg.mpr hb1)]

/-- Step 2 of the proof of `kakutani_mutuallySingular`: nonsummability of the squared
parameter differences forces the finite products of Bernoulli affinities to tend to zero. -/
private lemma kakutani_mutuallySingular_affinity_product {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1)
    (hsum : ¬ Summable fun i => ((p i : ℝ) - p' i) ^ 2) :
    Tendsto (fun n => ∏ i : Fin n, kakutani_mutuallySingular_affinity p p' i)
      atTop (𝓝 0) := by
  have hs := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun i => sq_nonneg ((p i : ℝ) - p' i))).mp hsum
  have hexp : Tendsto (fun n => Real.exp (- (∑ i ∈ Finset.range n,
      ((p i : ℝ) - p' i) ^ 2) / 4)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_neg_atTop_atBot.comp hs).atBot_div_const (by norm_num)
  have hbound (n : ℕ) :
      (∏ i : Fin n, kakutani_mutuallySingular_affinity p p' i) ≤
        Real.exp (- (∑ i ∈ Finset.range n, ((p i : ℝ) - p' i) ^ 2) / 4) := by
    rw [Fin.prod_univ_eq_prod_range]
    calc
      _ ≤ ∏ i ∈ Finset.range n, Real.exp (- ((p i : ℝ) - p' i) ^ 2 / 4) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · intro i hi
          have h := kakutani_mutuallySingular_affinity_bound (p i).coe_nonneg
            (NNReal.coe_le_one.mpr (hp i)) (p' i).coe_nonneg (NNReal.coe_le_one.mpr (hp' i))
          exact h.trans (by linarith [Real.add_one_le_exp (- ((p i : ℝ) - p' i) ^ 2 / 4)])
      _ = _ := by rw [← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
  exact squeeze_zero (fun n => Finset.prod_nonneg fun i hi =>
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hbound hexp

/-- Step 3 of the proof of `kakutani_mutuallySingular`: normalize the geometric means
of the two one-coordinate distributions to obtain a probability measure. Its cylinder masses,
multiplied by the finite affinity product, are the geometric means of the original masses. -/
private lemma kakutani_mutuallySingular_geometric_measure {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1)
    (hl : ∀ i, 0 < (p i : ℝ)) (hl' : ∀ i, 0 < (p' i : ℝ)) :
    ∃ ν : Measure CantorSeq, IsProbabilityMeasure ν ∧ ∀ x : BitString,
      massR ν x * (∏ i : Fin x.length, kakutani_mutuallySingular_affinity p p' i) =
        Real.sqrt (massR (independentTrials p hp) x * massR (independentTrials p' hp') x) := by
  let ρ := kakutani_mutuallySingular_affinity p p'
  have hρ (i : ℕ) : 0 < ρ i :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (mul_pos (hl i) (hl' i))) (Real.sqrt_nonneg _)
  let q : ℕ → NNReal := fun i => ⟨Real.sqrt ((p i : ℝ) * p' i) / ρ i,
    div_nonneg (Real.sqrt_nonneg _) (hρ i).le⟩
  have hq (i : ℕ) : q i ≤ 1 := by
    change Real.sqrt ((p i : ℝ) * p' i) / ρ i ≤ (1 : ℝ)
    rw [div_le_one (hρ i)]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  refine ⟨independentTrials q hq, inferInstance, fun x => ?_⟩
  rw [massR_independentTrials, massR_independentTrials, massR_independentTrials]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [Real.sqrt_prod _ (fun i hi => ?_)]
  · apply Finset.prod_congr rfl
    intro i hi
    cases hbit : x[i]
    · simp only [Bool.false_eq_true, ite_false]
      change (1 - Real.sqrt ((p i : ℝ) * p' i) / ρ i) * ρ i = _
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (hρ i).ne']
      dsimp [ρ, kakutani_mutuallySingular_affinity]
      ring
    · simp only [ite_true]
      exact div_mul_cancel₀ _ (hρ i).ne'
  · apply mul_nonneg
    · split_ifs
      · exact (p i).coe_nonneg
      · exact sub_nonneg.mpr (NNReal.coe_le_one.mpr (hp i))
    · split_ifs
      · exact (p' i).coe_nonneg
      · exact sub_nonneg.mpr (NNReal.coe_le_one.mpr (hp' i))

/-- Step 4 of the proof of `kakutani_mutuallySingular`: a ratio of cylinder masses of
probability measures is a martingale when every denominator cylinder has positive mass. -/
private lemma kakutani_mutuallySingular_ratio_martingale
    {μ ν : Measure CantorSeq} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, 0 < massR μ x) :
    IsMartingale μ (fun x => massR ν x / massR μ x) := by
  apply (isMartingale_iff_exists_measure _).mpr
  refine ⟨fun x => div_nonneg ENNReal.toReal_nonneg (hμ x).le, ν, inferInstance, ?_⟩
  intro x
  exact div_mul_cancel₀ _ (hμ x).ne'

/-- Step 5 of the proof of `kakutani_mutuallySingular`: if the affinity product tends
to zero, the two cylinder-mass ratios for the geometric-mean measure cannot both stay bounded
along any one sequence. -/
private lemma kakutani_mutuallySingular_joint_wins
    {μ μ' ν : Measure CantorSeq} (hμ : ∀ x, 0 < massR μ x)
    (hμ' : ∀ x, 0 < massR μ' x) (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0))
    (hgeom : ∀ x, massR ν x * R x.length = Real.sqrt (massR μ x * massR μ' x))
    (w : CantorSeq) :
    Wins (fun x => massR ν x / massR μ x) w ∨
      Wins (fun x => massR ν x / massR μ' x) w := by
  by_contra h
  rcases not_or.mp h with ⟨h1, h2⟩
  have hb1 : BddAbove (Set.range fun n => massR ν (cantorPrefix w n) /
      massR μ (cantorPrefix w n)) := by simpa only [Wins, not_not] using h1
  have hb2 : BddAbove (Set.range fun n => massR ν (cantorPrefix w n) /
      massR μ' (cantorPrefix w n)) := by simpa only [Wins, not_not] using h2
  obtain ⟨B, hB⟩ := hb1
  obtain ⟨C, hC⟩ := hb2
  have hB0 : 0 ≤ B := (div_nonneg ENNReal.toReal_nonneg (hμ _).le).trans
    (hB (Set.mem_range_self 0))
  have hid (n : ℕ) :
      (massR ν (cantorPrefix w n) / massR μ (cantorPrefix w n) *
        (massR ν (cantorPrefix w n) / massR μ' (cantorPrefix w n))) * R n ^ 2 = 1 := by
    have hg := hgeom (cantorPrefix w n)
    rw [cantorPrefix_length] at hg
    have hsq : massR ν (cantorPrefix w n) ^ 2 * R n ^ 2 =
        massR μ (cantorPrefix w n) * massR μ' (cantorPrefix w n) := by
      rw [← mul_pow, hg, Real.sq_sqrt (mul_nonneg (hμ _).le (hμ' _).le)]
    field_simp [(hμ _).ne', (hμ' _).ne']
    nlinarith [hsq]
  have hbound (n : ℕ) : (1 : ℝ) ≤ B * C * R n ^ 2 := by
    rw [← hid n]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (hB (Set.mem_range_self n)) (hC (Set.mem_range_self n))
      (div_nonneg ENNReal.toReal_nonneg (hμ' _).le) hB0
  have hlim : Tendsto (fun n => B * C * R n ^ 2) atTop (𝓝 0) := by
    simpa using (hR.pow 2).const_mul (B * C)
  have hle : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim hbound
  norm_num at hle

/-- **SUV Problem 276(b), p. 299 (Kakutani).** -/
theorem kakutani_mutuallySingular {ε : ℝ} (hε : 0 < ε) {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1) (hl : ∀ i, ε < p i) (hu : ∀ i, (p i : ℝ) < 1 - ε)
    (hl' : ∀ i, ε < p' i) (hu' : ∀ i, (p' i : ℝ) < 1 - ε)
    (hsum : ¬ Summable fun i => ((p i : ℝ) - p' i) ^ 2) :
    independentTrials p hp ⟂ₘ independentTrials p' hp' := by
  have hpos : ∀ x, 0 < massR (independentTrials p hp) x := by
    intro x
    rw [massR_independentTrials]
    apply Finset.prod_pos
    intro i hi
    split_ifs
    · exact hε.trans (hl i)
    · have := hu i
      linarith
  have hpos' : ∀ x, 0 < massR (independentTrials p' hp') x := by
    intro x
    rw [massR_independentTrials]
    apply Finset.prod_pos
    intro i hi
    split_ifs
    · exact hε.trans (hl' i)
    · have := hu' i
      linarith
  obtain ⟨ν, hν, hgeom⟩ := kakutani_mutuallySingular_geometric_measure hp hp'
    (fun i => hε.trans (hl i)) (fun i => hε.trans (hl' i))
  have hm := kakutani_mutuallySingular_ratio_martingale (ν := ν) hpos
  have hm' := kakutani_mutuallySingular_ratio_martingale (ν := ν) hpos'
  refine Measure.MutuallySingular.mk (measure_wins_eq_zero hm) (measure_wins_eq_zero hm') ?_
  intro w hw
  exact kakutani_mutuallySingular_joint_wins hpos hpos' _
    (kakutani_mutuallySingular_affinity_product hp hp' hsum) hgeom w

/-- Step 1a of the proof of `exists_measures_close_along_not_elsewhere`: there exists a
probability measure `μ'` which is uniform on the left half and biased on the right half. -/
private lemma exists_measures_close_along_not_elsewhere_mu_prime :
    ∃ μ' : Measure CantorSeq,
      IsProbabilityMeasure μ' ∧
      μ'.restrict (cantorCylinder [false]) = uniformMeasure.restrict (cantorCylinder [false]) ∧
      cantorMass μ' [] = 1 ∧
      (∀ t : List Bool, cantorMass μ' (false :: t) = (1/2 : ℝ≥0∞) ^ (t.length + 1)) ∧
      (∀ t : List Bool, cantorMass μ' (true :: t) = if (t = List.replicate t.length true) then
        (1/2 : ℝ≥0∞) else 0) := by
  classical
  let ones : CantorSeq := fun _ => true
  have hC : MeasurableSet (cantorCylinder [false]) := measurableSet_cantorCylinder _
  have hones0 : ones ∉ cantorCylinder [false] := by
    intro h
    have := h 0 (by simp)
    simp [ones] at this
  have hmass : ∀ x : BitString, cantorMass uniformMeasure x = (1/2 : ℝ≥0∞) ^ x.length := by
    intro x
    rw [cantorMass_uniformMeasure, one_div]
  let μ' : Measure CantorSeq :=
    uniformMeasure.restrict (cantorCylinder [false]) + (1/2 : ℝ≥0∞) • Measure.dirac ones
  have happ : ∀ A : Set CantorSeq, MeasurableSet A →
      μ' A = uniformMeasure (A ∩ cantorCylinder [false]) + (1/2 : ℝ≥0∞) * A.indicator 1 ones := by
    intro A hA
    simp only [μ', Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      Measure.dirac_apply' _ hA]
  have hX : ∀ x : BitString, cantorMass μ' x =
      uniformMeasure (cantorCylinder x ∩ cantorCylinder [false]) +
        (1/2 : ℝ≥0∞) * (cantorCylinder x).indicator 1 ones := fun x =>
    happ _ (measurableSet_cantorCylinder x)
  refine ⟨μ', ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [happ _ MeasurableSet.univ]
    have h1 : uniformMeasure (Set.univ ∩ cantorCylinder [false]) = 1/2 := by
      rw [Set.univ_inter]
      have := hmass [false]
      simpa [cantorMass] using this
    rw [h1, Set.indicator_univ, Pi.one_apply, mul_one, one_div]
    exact ENNReal.inv_two_add_inv_two
  · ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs, happ _ (hs.inter hC)]
    have : (s ∩ cantorCylinder [false]).indicator (1 : CantorSeq → ℝ≥0∞) ones = 0 := by
      simp [Set.indicator, hones0]
    rw [this, mul_zero, add_zero, Set.inter_assoc, Set.inter_self]
  · rw [hX]
    have hnil : cantorCylinder ([] : BitString) = Set.univ := by
      ext w; simp [cantorCylinder, IsCantorPrefix]
    rw [hnil, Set.univ_inter, Set.indicator_univ, Pi.one_apply, mul_one]
    have := hmass [false]
    simp only [cantorMass, List.length_singleton, pow_one] at this
    rw [this, one_div]
    exact ENNReal.inv_two_add_inv_two
  · intro t
    have hsub : cantorCylinder (false :: t) ⊆ cantorCylinder [false] := by
      intro w hw i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      exact hw 0 (by simp)
    rw [hX, Set.inter_eq_left.2 hsub]
    have : (cantorCylinder (false :: t)).indicator (1 : CantorSeq → ℝ≥0∞) ones = 0 := by
      refine Set.indicator_of_notMem (fun h => hones0 (hsub h)) _
    have hm := hmass (false :: t)
    simp only [cantorMass, List.length_cons] at hm
    rw [this, mul_zero, add_zero, hm]
  · intro t
    have hdisj : cantorCylinder (true :: t) ∩ cantorCylinder [false] = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      have a : w 0 = true := h1 0 (by simp)
      have b : w 0 = false := h2 0 (by simp)
      rw [a] at b
      exact absurd b (by simp)
    have hones : ones ∈ cantorCylinder (true :: t) ↔ t = List.replicate t.length true := by
      rw [List.eq_replicate_iff]
      constructor
      · intro h
        refine ⟨rfl, fun b hb => ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
        exact (h (i + 1) (by simp; omega)).symm
      · rintro ⟨-, h⟩ i hi
        rcases i with _ | i
        · rfl
        · have := h _ (List.getElem_mem (by simpa using hi))
          simpa [ones] using this
    rw [hX, hdisj]
    simp only [measure_empty, zero_add]
    by_cases ht : t = List.replicate t.length true
    · rw [ite_eq_left ht, Set.indicator_of_mem (hones.2 ht)]
      simp
    · rw [ite_eq_right ht, Set.indicator_of_notMem (fun h => ht (hones.1 h))]
      simp

private lemma exists_measures_close_along_not_elsewhere_computable_foldl (b : Bool)
    (t : List Bool) :
    t.foldl (fun a c => a && c) b = true ↔ b = true ∧ ∀ c ∈ t, c = true := by
  induction t generalizing b with
  | nil => simp
  | cons c t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons, forall_eq_or_imp, Bool.and_eq_true]
    tauto

private def exists_measures_close_along_not_elsewhere_computable_a (x : BitString) (s : ℕ) :
    ℕ :=
  if x.head? = some true then
    (if x.tail.foldl (fun a c => a && c) true = true then uniformApprox [true] s else 0)
  else uniformApprox x s

private lemma exists_measures_close_along_not_elsewhere_computable_a_comp :
    Computable₂ exists_measures_close_along_not_elsewhere_computable_a := by
  have hx : Primrec (fun p : BitString × ℕ => p.1) := Primrec.fst
  have hhead : PrimrecPred (fun p : BitString × ℕ => p.1.head? = some true) :=
    Primrec.eq.comp (Primrec.list_head?.comp hx) (Primrec.const (some true))
  have hfold : Primrec (fun p : BitString × ℕ => p.1.tail.foldl (fun a c => a && c) true) :=
    Primrec.list_foldl (h := fun _ q => q.1 && q.2) (Primrec.list_tail.comp hx) (Primrec.const true)
      (show Primrec (fun r : (BitString × ℕ) × (Bool × Bool) => r.2.1 && r.2.2) from
        Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have hfoldP : PrimrecPred (fun p : BitString × ℕ => p.1.tail.foldl (fun a c => a && c) true =
                                                        true) :=
    Primrec.eq.comp hfold (Primrec.const true)
  have hu : Computable (fun p : BitString × ℕ => uniformApprox p.1 p.2) := uniformApprox_computable
  have hu1 : Computable (fun p : BitString × ℕ => uniformApprox [true] p.2) :=
    uniformApprox_computable.comp (Computable.const [true]) Computable.snd
  have h0 : Computable (fun _ : BitString × ℕ => (0 : ℕ)) := Computable.const 0
  unfold Computable₂ exists_measures_close_along_not_elsewhere_computable_a
  refine (Computable.cond hhead.decide.to_comp
    (Computable.cond hfoldP.decide.to_comp hu1 h0) hu).of_eq ?_
  intro p
  simp only [Bool.cond_decide]

/-- Step 1b of the proof of `exists_measures_close_along_not_elsewhere`: `μ'` is
computable. -/
private lemma exists_measures_close_along_not_elsewhere_computable (μ' : Measure CantorSeq)
    (h_mass_nil : cantorMass μ' [] = 1)
    (h_mass_false : ∀ t : List Bool, cantorMass μ' (false :: t) = (1/2 : ℝ≥0∞) ^ (t.length + 1))
    (h_mass_true : ∀ t : List Bool, cantorMass μ' (true :: t) = if (t = List.replicate t.length
        true) then (1/2 : ℝ≥0∞) else 0) :
    IsComputableMeasure μ' := by
  have hhalf : (1/2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by rw [one_div]
  have key : ∀ x s, ∃ y : BitString,
      (exists_measures_close_along_not_elsewhere_computable_a x s = uniformApprox y s ∧
        cantorMass μ' x = cantorMass uniformMeasure y) ∨
      (exists_measures_close_along_not_elsewhere_computable_a x s = 0 ∧ cantorMass μ' x = 0)
          := by
    intro x s
    rcases x with _ | ⟨b, t⟩
    · refine ⟨[], Or.inl ⟨?_, ?_⟩⟩
      · simp [exists_measures_close_along_not_elsewhere_computable_a]
      · rw [h_mass_nil, cantorMass_uniformMeasure]; simp
    · cases b
      · refine ⟨false :: t, Or.inl ⟨?_, ?_⟩⟩
        · simp [exists_measures_close_along_not_elsewhere_computable_a]
        · rw [h_mass_false, cantorMass_uniformMeasure, hhalf]; simp
      · by_cases ht : t = List.replicate t.length true
        · refine ⟨[true], Or.inl ⟨?_, ?_⟩⟩
          · have : t.foldl (fun a c => a && c) true = true := by
              rw [exists_measures_close_along_not_elsewhere_computable_foldl]
              exact ⟨rfl, fun c hc => (List.eq_replicate_iff.mp ht).2 c hc⟩
            simp [exists_measures_close_along_not_elsewhere_computable_a, this]
          · rw [h_mass_true, ite_eq_left ht, cantorMass_uniformMeasure, hhalf]; simp
        · refine ⟨[], Or.inr ⟨?_, ?_⟩⟩
          · have : ¬ t.foldl (fun a c => a && c) true = true := by
              rw [exists_measures_close_along_not_elsewhere_computable_foldl]
              rintro ⟨-, h⟩
              exact ht (List.eq_replicate_iff.mpr ⟨rfl, h⟩)
            simp [exists_measures_close_along_not_elsewhere_computable_a, this]
          · rw [h_mass_true, ite_eq_right ht]
  refine isComputableMeasure_of_dyadicFloorApprox
    exists_measures_close_along_not_elsewhere_computable_a_comp ?_
  intro x s
  obtain ⟨y, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := key x s
  · rw [h1, h2]
    exact ⟨uniformApprox_le_mass y s, mass_le_uniformApprox_add y s⟩
  · rw [h1, h2]
    simp [dyadicValue]

/-- Cutting a string down to the cylinder of `s`. -/
private def exists_measures_close_along_not_elsewhere_random_transfer_cut
    (s : List Bool) (x : List Bool) : Option (List Bool) :=
  cond (decide (x.take s.length = s)) (some x)
    (cond (decide (s.take x.length = x)) (some s) none)

private lemma exists_measures_close_along_not_elsewhere_random_transfer_cut_primrec
    (s : List Bool) :
    Primrec (exists_measures_close_along_not_elsewhere_random_transfer_cut s) := by
  unfold exists_measures_close_along_not_elsewhere_random_transfer_cut
  have h1 : Primrec fun x : List Bool => decide (x.take s.length = s) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.list_take.comp (Primrec.const s.length) Primrec.id) (Primrec.const s)
  have h2 : Primrec fun x : List Bool => decide (s.take x.length = x) :=
    (PrimrecRel.decide Primrec.eq).comp
      (Primrec.list_take.comp Primrec.list_length (Primrec.const s)) Primrec.id
  exact Primrec.cond h1 (Primrec.option_some.comp Primrec.id)
    (Primrec.cond h2 (Primrec.option_some.comp (Primrec.const s)) (Primrec.const none))

private lemma exists_measures_close_along_not_elsewhere_random_transfer_cut_inter
    (s x : List Bool) :
    cantorCylinder x ∩ cantorCylinder s =
      ((exists_measures_close_along_not_elsewhere_random_transfer_cut s x).elim ∅
        cantorCylinder) := by
  unfold exists_measures_close_along_not_elsewhere_random_transfer_cut
  by_cases h1 : x.take s.length = s
  · have hp : s <+: x := List.prefix_iff_eq_take.mpr h1.symm
    simp only [h1, decide_true, Bool.cond_true, Option.elim_some]
    rw [Set.inter_comm, cantorCylinder_inter_of_prefix hp]
  · by_cases h2 : s.take x.length = x
    · have hp : x <+: s := List.prefix_iff_eq_take.mpr h2.symm
      simp only [h1, h2, decide_false, decide_true, Bool.cond_false, Bool.cond_true,
          Option.elim_some]
      exact cantorCylinder_inter_of_prefix hp
    · have hp1 : ¬ s <+: x := fun h => h1 (List.prefix_iff_eq_take.mp h).symm
      have hp2 : ¬ x <+: s := fun h => h2 (List.prefix_iff_eq_take.mp h).symm
      simp only [h1, h2, decide_false, Bool.cond_false, Option.elim_none]
      exact (cantorCylinder_disjoint_of_incompatible hp2 hp1).inter_eq

private lemma exists_measures_close_along_not_elsewhere_random_transfer_dir
    (μ ν : Measure CantorSeq) (s : List Bool)
    (h_eq : μ.restrict (cantorCylinder s) = ν.restrict (cantorCylinder s))
    (w : CantorSeq) (hw : w ∈ cantorCylinder s)
    (hν : IsMartinLofRandom ν w) : IsMartinLofRandom μ w := by
  intro V hV hwV
  obtain ⟨⟨f, hf, hVf⟩, hVb⟩ := hV
  refine hν (fun n => V n ∩ cantorCylinder s) ⟨⟨fun n i => (f n i).bind
    (exists_measures_close_along_not_elsewhere_random_transfer_cut s), ?_, ?_⟩, ?_⟩ ?_
  · exact Computable.option_bind hf
      (((exists_measures_close_along_not_elsewhere_random_transfer_cut_primrec s).to_comp).comp
        Computable.snd)
  · intro n
    change V n ∩ cantorCylinder s = ⋃ i, ((f n i).bind
      (exists_measures_close_along_not_elsewhere_random_transfer_cut s)).elim ∅
          cantorCylinder
    rw [hVf n, Set.iUnion_inter]
    refine Set.iUnion_congr fun i => ?_
    cases hfi : f n i with
    | none => simp
    | some x =>
      simpa using exists_measures_close_along_not_elsewhere_random_transfer_cut_inter s x
  · intro n
    have hVm : MeasurableSet (V n) := by
      rw [hVf n]
      refine MeasurableSet.iUnion fun i => ?_
      cases f n i
      · exact MeasurableSet.empty
      · exact measurableSet_cantorCylinder _
    have h1 : ν (V n ∩ cantorCylinder s) = μ (V n ∩ cantorCylinder s) := by
      rw [← Measure.restrict_apply' (measurableSet_cantorCylinder s) (μ := ν),
        ← Measure.restrict_apply' (measurableSet_cantorCylinder s) (μ := μ), h_eq]
    rw [h1]
    exact (measure_mono Set.inter_subset_left).trans (hVb n)
  · exact Set.mem_iInter.2 fun n => ⟨Set.mem_iInter.1 hwV n, hw⟩

/-- Step 1c of the proof of `exists_measures_close_along_not_elsewhere`: Martin-Löf
randomness transfers. -/
private lemma exists_measures_close_along_not_elsewhere_random_transfer
    (μ ν : Measure CantorSeq)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (s : List Bool)
    (h_eq : μ.restrict (cantorCylinder s) = ν.restrict (cantorCylinder s))
    (w : CantorSeq) (hw : w ∈ cantorCylinder s) :
    IsMartinLofRandom μ w ↔ IsMartinLofRandom ν w :=
  ⟨exists_measures_close_along_not_elsewhere_random_transfer_dir ν μ s h_eq.symm w hw,
    exists_measures_close_along_not_elsewhere_random_transfer_dir μ ν s h_eq w hw⟩

/-- Step 1d of the proof of `exists_measures_close_along_not_elsewhere`: numerics on `μ'`.
-/
private lemma exists_measures_close_along_not_elsewhere_numerics (μ' : Measure CantorSeq)
    (h_mass_true : ∀ t : List Bool, cantorMass μ' (true :: t) = if (t = List.replicate t.length
        true) then (1/2 : ℝ≥0∞) else 0) :
    (∀ n, 0 < cantorMass μ' (cantorPrefix (fun _ => true) n)) ∧
    (∀ n ≥ 1, condOne μ' (cantorPrefix (fun _ => true) n) = 1) := by
  have hpre : ∀ n, cantorPrefix (fun _ => true) n = List.replicate n true := by
    intro n
    simp [cantorPrefix, List.ofFn_const]
  have hrep : ∀ m, cantorMass μ' (List.replicate (m + 1) true) = 1/2 := by
    intro m
    have h := h_mass_true (List.replicate m true)
    rw [ite_eq_left (by simp)] at h
    simpa [List.replicate_succ] using h
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rw [hpre]
    cases n with
    | zero =>
      have h0 := cantorMass_add μ' []
      have h1 := hrep 0
      have h2 : cantorMass μ' [true] = 1/2 := by simpa using h1
      have h3 : cantorMass μ' ([] ++ [true]) = 1/2 := by simpa using h2
      rw [List.replicate_zero, h0]
      refine lt_of_lt_of_le ?_ le_add_self
      rw [h3]
      simp
    | succ m =>
      rw [hrep m]
      simp
  · rw [hpre]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : List.replicate (m + 1) true ++ [true] = List.replicate (m + 2) true := by
      simp [List.replicate_succ']
    unfold condOne condProb
    rw [hx, hrep m, hrep (m + 1)]
    have h2 : ((1 / 2 : ℝ≥0∞)).toReal ≠ 0 := by
      simp [ENNReal.toReal_inv]
    exact div_self h2

/-- Step 1e of the proof of `exists_measures_close_along_not_elsewhere`: nonsummability.
-/
private lemma exists_measures_close_along_not_elsewhere_not_summable {f : ℕ → ℝ} (c : ℝ)
    (hc : c ≠ 1 / 2) (N : ℕ)
    (hf : ∀ n ≥ N, f n = c) :
    ¬ Summable fun n => ((1/2 : ℝ) - f n) ^ 2 := by
  intro h
  have ht := Summable.tendsto_atTop_zero h
  have ht2 : Tendsto (fun n => ((1/2 : ℝ) - f n) ^ 2) atTop (𝓝 (((1/2 : ℝ) - c) ^ 2)) := by
    apply tendsto_nhds_of_eventually_eq
    rw [Filter.eventually_atTop]
    use N
    intro b hb
    rw [hf b hb]
  have heq := tendsto_nhds_unique ht ht2
  have heq2 : (1/2 : ℝ) - c = 0 := by nlinarith
  exact hc (by linarith)

/-- Step 1f of the proof of `exists_measures_close_along_not_elsewhere`: uniform
condition. -/
private lemma exists_measures_close_along_not_elsewhere_unif_cond (n : ℕ) :
    condOne uniformMeasure (cantorPrefix (fun _ => true) n) = 1/2 := by
  dsimp [condOne, condProb]
  have h1 : cantorMass uniformMeasure (cantorPrefix (fun x => true) n ++ [true]) = 2⁻¹ ^ (n + 1) :=
      by
    rw [cantorMass_uniformMeasure]
    have hlen : (cantorPrefix (fun x => true) n ++ [true]).length = n + 1 := by simp
    rw [hlen]
  rw [h1]
  have h2 : cantorMass uniformMeasure (cantorPrefix (fun x => true) n) = 2⁻¹ ^ n := by
    rw [cantorMass_uniformMeasure]
    have hlen : (cantorPrefix (fun x => true) n).length = n := by simp
    rw [hlen]
  rw [h2]
  have h3 : (2⁻¹ ^ (n + 1) : ℝ≥0∞).toReal = (1/2) ^ (n + 1) := by rw [ENNReal.toReal_pow]; simp
  have h4 : (2⁻¹ ^ n : ℝ≥0∞).toReal = (1/2) ^ n := by rw [ENNReal.toReal_pow]; simp
  rw [h3, h4]
  have h5 : (1/2 : ℝ) ^ (n + 1) = (1/2) ^ n * (1/2) := by ring
  rw [h5, mul_comm]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))

/-- **SUV Problem 277, p. 301.**  Theorem 197 says nothing away from `ω`: there are computable
measures and a sequence random for both, with non-square-summable differences along another
sequence of positive masses.  (Hint of the book: uniform in the left half, different in the right
half.) -/
theorem exists_measures_close_along_not_elsewhere :
    ∃ (μ μ' : Measure CantorSeq) (w y : CantorSeq),
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      IsComputableMeasure μ ∧ IsComputableMeasure μ' ∧
      IsMartinLofRandom μ w ∧ IsMartinLofRandom μ' w ∧
      (∀ n, 0 < cantorMass μ (cantorPrefix y n) ∧ 0 < cantorMass μ' (cantorPrefix y n)) ∧
      ¬ Summable fun n => (condOne μ (cantorPrefix y n) - condOne μ' (cantorPrefix y n)) ^ 2 := by
  obtain ⟨μ', hPμ', hEq, hMassNil, hMassFalse, hMassTrue⟩ :=
      exists_measures_close_along_not_elsewhere_mu_prime
  obtain ⟨w, hw⟩ := exists_isMartinLofRandom_uniform
  let w_cons : CantorSeq := fun i => if i = 0 then false else w (i - 1)
  use uniformMeasure, μ', w_cons, fun _ => true
  have h_comp' := exists_measures_close_along_not_elsewhere_computable μ' hMassNil hMassFalse
      hMassTrue
  have h_w_in_false : w_cons ∈ cantorCylinder [false] := by
    change IsCantorPrefix [false] w_cons
    dsimp [IsCantorPrefix]
    intro i hi
    cases i
    · rfl
    · contradiction
  have h_trans := exists_measures_close_along_not_elsewhere_random_transfer μ' uniformMeasure
      [false] hEq w_cons h_w_in_false
  have h_rand_w : IsMartinLofRandom uniformMeasure w_cons :=
      isMartinLofRandom_cons_of_isMartinLofRandom_uniform false hw
  have h_rand_w' : IsMartinLofRandom μ' w_cons := h_trans.mpr h_rand_w
  have h_num := exists_measures_close_along_not_elsewhere_numerics μ' hMassTrue
  refine ⟨inferInstance, hPμ', isComputableMeasure_uniform, h_comp', h_rand_w, h_rand_w', ?_, ?_⟩
  · intro n
    constructor
    · rw [cantorMass_uniformMeasure]
      exact ENNReal.pow_pos (by norm_num) _
    · exact h_num.1 n
  · have h_num_2 := h_num.2
    have h_c_neq : (1 : ℝ) ≠ 1/2 := by norm_num
    have h_not_sum := exists_measures_close_along_not_elsewhere_not_summable 1 h_c_neq 1
        h_num_2
    apply mt (fun h => Summable.congr h fun n => ?_) h_not_sum
    rw [exists_measures_close_along_not_elsewhere_unif_cond]

end Kolmogorov.FrequencyGames
