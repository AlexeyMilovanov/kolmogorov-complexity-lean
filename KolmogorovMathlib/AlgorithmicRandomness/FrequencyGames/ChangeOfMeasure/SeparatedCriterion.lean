/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.IndependentTrials

/-!
# Separated Criterion

Change of measure for independent trials whose success probabilities are separated from `0`
and `1`, following the discussion of Vovk's theorem in the book of Shen, Uspensky and
Vereshchagin.

The file contains:
* `isComputablyRandom_firstTrialBiased_iff` (Problem 275, p. 297): a sequence is computably
  random for the measure with the first bit biased exactly when it is computably random for the
  uniform measure;
* `IsSeparatedComputable`: the hypotheses of Theorem 196, namely computable probabilities in
  `(ε, 1 - ε)`;
* `isMartinLofRandom_iff_of_summable` (Theorem 196(a), p. 297): if `∑ (p_i - p'_i)²` is finite,
  the Martin-Löf random sequences for the two product measures coincide.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- Step 1 of the proof of `isComputablyRandom_firstTrialBiased_iff`: given a fair capital
for `uniformMeasure`, create an adjusted fair capital for `firstTrialBiased`. -/
private lemma isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_ltr {m : BitString → ℝ}
    (hfair : IsFairCapital uniformMeasure m) :
    IsFairCapital firstTrialBiased (fun x => if x.length = 0 then m x else
                                               m x * (massR uniformMeasure x /
                                               massR firstTrialBiased x)) := by
  have hpos (x : BitString) : 0 < massR firstTrialBiased x := by
    unfold firstTrialBiased
    rw [massR_independentTrials]
    apply Finset.prod_pos
    intro i _
    by_cases hi : (i : ℕ) = 0 <;> cases x[i] <;> norm_num [hi]
  let m' : BitString → ℝ := fun x =>
    if x.length = 0 then m x else m x * (massR uniformMeasure x / massR firstTrialBiased x)
  have hmass (x : BitString) :
      m' x * massR firstTrialBiased x = m x * massR uniformMeasure x := by
    by_cases hx : x.length = 0
    · have hx_nil : x = [] := List.length_eq_zero_iff.mp hx
      subst x
      simp [m', firstTrialBiased, massR_independentTrials, massR_uniformMeasure]
    · dsimp only [m']
      rw [ite_eq_right hx, mul_assoc, div_mul_cancel₀ _ (ne_of_gt (hpos x))]
  change IsFairCapital firstTrialBiased m'
  refine ⟨?_, ?_⟩
  · intro x
    dsimp only [m']
    split_ifs
    · exact hfair.nonneg x
    · exact mul_nonneg (hfair.nonneg x)
        (div_nonneg ENNReal.toReal_nonneg (hpos x).le)
  · intro x
    rw [hmass, hmass, hmass]
    exact hfair.fair x

/-- Step 2 of the proof of `isComputablyRandom_firstTrialBiased_iff`: given a fair capital
for `firstTrialBiased`, create an adjusted fair capital for `uniformMeasure`. -/
private lemma isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_rtl_massR_nonneg
    (π : MeasureTheory.Measure CantorSeq) (x : BitString) : 0 ≤ massR π x := ENNReal.toReal_nonneg

private lemma isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_rtl {m : BitString → ℝ}
    (hfair : IsFairCapital firstTrialBiased m) :
    IsFairCapital uniformMeasure (fun x => if x.length = 0 then m x else
                                             m x * (massR firstTrialBiased x / massR uniformMeasure
                                             x)) := by
  have hm0 := hfair.nonneg
  have hmeq := hfair.fair
  refine ⟨?_, ?_⟩
  · intro x
    by_cases h : x.length = 0
    · simp [h, hm0 x]
    · simp only [h, ↓reduceIte]
      have h1 : 0 ≤ m x := hm0 x
      have h2 : 0 ≤ (massR firstTrialBiased x : ℝ) :=
          isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_rtl_massR_nonneg _ _
      have h3 : 0 ≤ (massR uniformMeasure x : ℝ) :=
          isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_rtl_massR_nonneg _ _
      positivity
  · intro x
    set m' := fun (x : BitString) => if x.length = 0 then m x else
                                       m x * (massR firstTrialBiased x / massR uniformMeasure x)
    have eq1 : ∀ y : BitString, y.length ≠ 0 → m' y * massR uniformMeasure y = m y *
        massR firstTrialBiased y := by
      intro y hy
      dsimp [m']
      rw [ite_eq_right_iff.mpr (fun h' => (hy h').elim)]
      have hu_pos : (0:ℝ) < massR uniformMeasure y := by rw [massR_uniformMeasure]; positivity
      calc
        m y * (massR firstTrialBiased y / massR uniformMeasure y) * massR uniformMeasure y
        _ = m y * ((massR firstTrialBiased y / massR uniformMeasure y) * massR uniformMeasure y) :=
            by ring
        _ = m y * massR firstTrialBiased y := by rw [div_mul_cancel₀ _ (ne_of_gt hu_pos)]
    by_cases h : x.length = 0
    · have hx_nil : x = [] := by
        cases x
        · rfl
        · simp at h
      subst hx_nil
      change m' [] * massR uniformMeasure [] = m' [false] * massR uniformMeasure [false] + m' [true]
          * massR uniformMeasure [true]
      have hm'_nil : m' [] = m [] := rfl
      rw [hm'_nil]
      have hf : ([false]:BitString).length ≠ 0 := by simp
      have hf' := eq1 [false] hf
      have ht : ([true]:BitString).length ≠ 0 := by simp
      have ht' := eq1 [true] ht
      rw [hf', ht']
      have hmeq_nil := hmeq []
      simp only [List.nil_append] at hmeq_nil
      have hu : massR uniformMeasure [] = 1 := by rw [massR_uniformMeasure]; norm_num
      rw [hu, mul_one]
      have hf_nil : massR firstTrialBiased [] = 1 := by
        unfold firstTrialBiased
        rw [massR_independentTrials]
        change (∏ i : Fin 0, _) = 1
        exact Finset.prod_empty
      rw [hf_nil, mul_one] at hmeq_nil
      exact hmeq_nil
    · have hx := eq1 x h
      have hxf : (x ++ [false]).length ≠ 0 := by simp
      have hxf' := eq1 (x ++ [false]) hxf
      have hxt : (x ++ [true]).length ≠ 0 := by simp
      have hxt' := eq1 (x ++ [true]) hxt
      change m' x * massR uniformMeasure x = m' (x ++ [false]) * massR uniformMeasure (x ++ [false])
          + m' (x ++ [true]) * massR uniformMeasure (x ++ [true])
      rw [hx, hxf', hxt']
      exact hmeq x

private def isComputablyRandom_firstTrialBiased_iff_c1 : BitString → ℚ :=
  fun x => match x.head? with | none => (1:ℚ) | some true => 3/4 | some false => 3/2

private def isComputablyRandom_firstTrialBiased_iff_c2 : BitString → ℚ :=
  fun x => match x.head? with | none => (1:ℚ) | some true => 4/3 | some false => 2/3

private lemma isComputablyRandom_firstTrialBiased_iff_comp1 :
    Computable isComputablyRandom_firstTrialBiased_iff_c1 := by
  have h1 : Computable (fun x : BitString => x.head?) := Primrec.list_head?.to_comp
  have h2 : Computable (fun b : Option Bool =>
      match b with | none => (1:ℚ) | some true => 3/4 | some false => 3/2) := by
    apply Primrec.to_comp
    exact Primrec.dom_finite _
  exact (h2.comp h1).of_eq (fun p => by rcases p with _ | _ | _ <;> rfl)

private lemma isComputablyRandom_firstTrialBiased_iff_comp2 :
    Computable isComputablyRandom_firstTrialBiased_iff_c2 := by
  have h1 : Computable (fun x : BitString => x.head?) := Primrec.list_head?.to_comp
  have h2 : Computable (fun b : Option Bool =>
      match b with | none => (1:ℚ) | some true => 4/3 | some false => 2/3) := by
    apply Primrec.to_comp
    exact Primrec.dom_finite _
  exact (h2.comp h1).of_eq (fun p => by rcases p with _ | _ | _ <;> rfl)

private lemma isComputablyRandom_firstTrialBiased_iff_aux_bounds
    (x : BitString) (hx : 0 < x.length) :
  let u := massR uniformMeasure x
  let f := massR firstTrialBiased x
  (u / f = match x.head? with | none => 1 | some true => 3/4 | some false => 3/2) ∧
  (f / u = match x.head? with | none => 1 | some true => 4/3 | some false => 2/3) := by
  intro u f
  have hu : u = (2 : ℝ)⁻¹ ^ x.length := massR_uniformMeasure x
  have hf : f = ∏ i : Fin x.length, if x[i.val] = true then if (i.val : ℕ) = 0 then (2/3:ℝ) else
    1/2 else 1 - if (i.val : ℕ) = 0 then (2/3:ℝ) else 1/2 := by
    dsimp [f, firstTrialBiased]
    rw [massR_independentTrials]
    congr
    ext i
    congr 1
    · split_ifs <;> rfl
    · congr 1
      split_ifs <;> rfl
  have hz : (⟨0, hx⟩ : Fin x.length) ∈ Finset.univ := Finset.mem_univ _
  have hf2 : f = (if x[0]'(hx) = true then (2/3:ℝ) else 1/3) * (1/2:ℝ) ^ (x.length - 1) := by
    rw [hf]
    have hp := @Finset.prod_eq_mul_prod_sdiff_singleton (Fin x.length) ℝ _ _ Finset.univ
        (⟨0, hx⟩ : Fin x.length) (fun i => if x[i.val] = true then
                                             if (i.val : ℕ) = 0 then (2/3:ℝ) else
                                               1/2 else 1 - if (i.val : ℕ) = 0 then (2/3:ℝ) else
                                                          1/2) (by intro hc; exfalso; exact hc hz)
    rw [hp]
    congr 1
    · dsimp
      split_ifs <;> norm_num
    · have h_all : ∏ x_1 ∈ Finset.univ \ {(⟨0, hx⟩ : Fin x.length)},
        (if x[x_1.val] = true then if (x_1.val : ℕ) = 0 then (2 / 3 : ℝ) else
          1 / 2 else 1 - if (x_1.val : ℕ) = 0 then (2 / 3 : ℝ) else
                       1 / 2) = ∏ x_1 ∈ Finset.univ \ {(⟨0, hx⟩ : Fin x.length)}, (1/2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj0 : (j.val : ℕ) ≠ 0 := by
          intro hc
          have hc' : j = ⟨0, hx⟩ := Fin.ext hc
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
          exact hj.2 hc'
        have heq : ((if (j.val : ℕ) = 0 then (2 / 3 : ℝ) else 1 / 2) = 1/2) := by
          rw [ite_eq_right_iff.mpr (by intro hc; exfalso; exact hj0 hc)]
        rw [heq]
        split_ifs <;> norm_num
      rw [h_all]
      rw [Finset.prod_const]
      congr 1
      rw [Finset.card_sdiff]
      have hc : ({⟨0, hx⟩} ∩ Finset.univ : Finset (Fin x.length)).card = 1 := by
        have hc' : ({⟨0, hx⟩} ∩ Finset.univ : Finset (Fin x.length)) = {⟨0, hx⟩} := by
          ext j
          simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_univ, and_true]
        rw [hc']
        exact Finset.card_singleton _
      rw [hc, Finset.card_univ, Fintype.card_fin]
  have hu2 : u = (1/2:ℝ) ^ x.length := by
    rw [hu]
    have h_half : ((2:ℝ)⁻¹) = 1/2 := by norm_num
    rw [h_half]
  have hu3 : u = (1/2:ℝ) * (1/2:ℝ) ^ (x.length - 1) := by
    rw [hu2]
    have hs : x.length = 1 + (x.length - 1) := by omega
    conv =>
      lhs
      rw [hs]
    rw [pow_add]
    simp only [pow_one]
  constructor
  · rw [hu3, hf2]
    have heq : (1 / 2 * (1 / 2) ^ (x.length - 1)) /
        ((if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) * (1 / 2) ^ (x.length - 1)) = (1/2) /
        (if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) := by
      rw [div_eq_div_iff]
      · ring
      · positivity
      · positivity
    rw [heq]
    by_cases h_x0 : x[0]'(hx) = true
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 2/3 := by simp [h_x0]
      rw [heq2]
      have hhead : x.head? = some true := by
        cases x
        · contradiction
        · simp at h_x0
          simp [h_x0]
      rw [hhead]
      norm_num
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 1/3 := by simp [h_x0]
      rw [heq2]
      have hhead : x.head? = some false := by
        cases x
        · contradiction
        · simp at h_x0
          simp [h_x0]
      rw [hhead]
      norm_num
  · rw [hu3, hf2]
    have heq : ((if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) * (1 / 2) ^ (x.length - 1)) /
        (1 / 2 * (1 / 2) ^ (x.length - 1)) = (if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) /
        (1/2) := by
      rw [div_eq_div_iff]
      · ring
      · positivity
      · positivity
    rw [heq]
    by_cases h_x0 : x[0]'(hx) = true
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 2/3 := by simp [h_x0]
      rw [heq2]
      have hhead : x.head? = some true := by
        cases x
        · contradiction
        · simp at h_x0
          simp [h_x0]
      rw [hhead]
      norm_num
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 1/3 := by simp [h_x0]
      rw [heq2]
      have hhead : x.head? = some false := by
        cases x
        · contradiction
        · simp at h_x0
          simp [h_x0]
      rw [hhead]
      norm_num

private lemma isComputablyRandom_firstTrialBiased_iff_ltr (m : BitString → ℝ)
    (hcomp : IsComputableOnStrings m) :
    IsComputableOnStrings (fun x => if x.length = 0 then m x else
                                      m x * (massR uniformMeasure x / massR firstTrialBiased x)) :=
                                      by
  have h_eq : (fun x => if x.length = 0 then m x else m x * (massR uniformMeasure x /
                                                        massR firstTrialBiased x)) = 
              (fun x => m x * (isComputablyRandom_firstTrialBiased_iff_c1 x :
                          ℝ)) := by
    ext x
    by_cases h : x.length = 0
    · have hx_nil : x = [] := by
        cases x
        · rfl
        · simp at h
      subst hx_nil
      simp [isComputablyRandom_firstTrialBiased_iff_c1]
    · simp only [h, ite_false]
      have h_len : 0 < x.length := by omega
      have hb := isComputablyRandom_firstTrialBiased_iff_aux_bounds x h_len
      have heq2 : m x * (massR uniformMeasure x / massR firstTrialBiased x) = m x *
          (isComputablyRandom_firstTrialBiased_iff_c1 x : ℝ) := by
        have hb1 := hb.1
        change massR uniformMeasure x / massR firstTrialBiased x = _ at hb1
        rw [hb1]
        unfold isComputablyRandom_firstTrialBiased_iff_c1
        match hhead : x.head? with
        | none => norm_num
        | some true => norm_num
        | some false => norm_num
      exact heq2
  rw [h_eq]
  obtain ⟨q, hq, hbound⟩ := hcomp
  use fun p => isComputablyRandom_firstTrialBiased_iff_c1 p.1 *
                 q (p.1, p.2 + 1)
  constructor
  · have h1 : Computable (fun p : BitString × ℕ => isComputablyRandom_firstTrialBiased_iff_c1 p.1)
      := isComputablyRandom_firstTrialBiased_iff_comp1.comp Computable.fst
    have h2 : Computable (fun p : BitString × ℕ => p.1) := Computable.fst
    have h3 : Computable (fun p : BitString × ℕ => p.2 + 1) := Primrec.succ.to_comp.comp
        Computable.snd
    have h4 : Computable (fun p : BitString × ℕ => (p.1, p.2 + 1)) := Computable.pair h2 h3
    have h5 : Computable (fun p : BitString × ℕ => q (p.1, p.2 + 1)) := hq.comp h4
    exact computable₂_ratMul.comp h1 h5
  · intro x s
    have h := hbound x (s + 1)
    have heq : ((isComputablyRandom_firstTrialBiased_iff_c1 x * q (x, s + 1)
        : ℚ) : ℝ) - m x * isComputablyRandom_firstTrialBiased_iff_c1 x =
        isComputablyRandom_firstTrialBiased_iff_c1 x * ((q (x, s + 1) : ℝ) -
        m x) := by
      push_cast
      ring
    rw [heq, abs_mul]
    have hc_bound : |(isComputablyRandom_firstTrialBiased_iff_c1 x : ℝ)| ≤
        2 := by
      unfold isComputablyRandom_firstTrialBiased_iff_c1
      match h' : x.head? with
      | none => norm_num
      | some true => norm_num
      | some false => norm_num
    calc
      |(isComputablyRandom_firstTrialBiased_iff_c1 x : ℝ)| *
          |(q (x, s + 1) : ℝ) - m x|
        ≤ 2 * (2 : ℝ)⁻¹ ^ (s + 1) := mul_le_mul hc_bound h (abs_nonneg _) (by norm_num)
      _ = (2 : ℝ)⁻¹ ^ s := by
        rw [pow_add, pow_one]
        have : (2 : ℝ) * ((2 : ℝ)⁻¹ ^ s * (2 : ℝ)⁻¹) = (2 : ℝ) * (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ s := by
          ring
        rw [this, mul_inv_cancel₀ (by norm_num), one_mul]

private lemma isComputablyRandom_firstTrialBiased_iff_rtl (m : BitString → ℝ)
    (hcomp : IsComputableOnStrings m) :
    IsComputableOnStrings (fun x => if x.length = 0 then m x else
                                      m x * (massR firstTrialBiased x / massR uniformMeasure x)) :=
                                      by
  have h_eq : (fun x => if x.length = 0 then m x else m x * (massR firstTrialBiased x /
                                                        massR uniformMeasure x)) = 
              (fun x => m x * (isComputablyRandom_firstTrialBiased_iff_c2 x :
                          ℝ)) := by
    ext x
    by_cases h : x.length = 0
    · have hx_nil : x = [] := by
        cases x
        · rfl
        · simp at h
      subst hx_nil
      simp [isComputablyRandom_firstTrialBiased_iff_c2]
    · simp only [h, ite_false]
      have h_len : 0 < x.length := by omega
      have hb := isComputablyRandom_firstTrialBiased_iff_aux_bounds x h_len
      have heq2 : m x * (massR firstTrialBiased x / massR uniformMeasure x) = m x *
          (isComputablyRandom_firstTrialBiased_iff_c2 x : ℝ) := by
        have hb2 := hb.2
        change massR firstTrialBiased x / massR uniformMeasure x = _ at hb2
        rw [hb2]
        unfold isComputablyRandom_firstTrialBiased_iff_c2
        match hhead : x.head? with
        | none => norm_num
        | some true => norm_num
        | some false => norm_num
      exact heq2
  rw [h_eq]
  obtain ⟨q, hq, hbound⟩ := hcomp
  use fun p => isComputablyRandom_firstTrialBiased_iff_c2 p.1 *
                 q (p.1, p.2 + 1)
  constructor
  · have h1 : Computable (fun p : BitString × ℕ => isComputablyRandom_firstTrialBiased_iff_c2 p.1)
      := isComputablyRandom_firstTrialBiased_iff_comp2.comp Computable.fst
    have h2 : Computable (fun p : BitString × ℕ => p.1) := Computable.fst
    have h3 : Computable (fun p : BitString × ℕ => p.2 + 1) := Primrec.succ.to_comp.comp
        Computable.snd
    have h4 : Computable (fun p : BitString × ℕ => (p.1, p.2 + 1)) := Computable.pair h2 h3
    have h5 : Computable (fun p : BitString × ℕ => q (p.1, p.2 + 1)) := hq.comp h4
    exact computable₂_ratMul.comp h1 h5
  · intro x s
    have h := hbound x (s + 1)
    have heq : ((isComputablyRandom_firstTrialBiased_iff_c2 x * q (x, s + 1)
        : ℚ) : ℝ) - m x * isComputablyRandom_firstTrialBiased_iff_c2 x =
        isComputablyRandom_firstTrialBiased_iff_c2 x * ((q (x, s + 1) : ℝ) -
        m x) := by
      push_cast
      ring
    rw [heq, abs_mul]
    have hc_bound : |(isComputablyRandom_firstTrialBiased_iff_c2 x : ℝ)| ≤
        2 := by
      unfold isComputablyRandom_firstTrialBiased_iff_c2
      match h' : x.head? with
      | none => norm_num
      | some true => norm_num
      | some false => norm_num
    calc
      |(isComputablyRandom_firstTrialBiased_iff_c2 x : ℝ)| *
          |(q (x, s + 1) : ℝ) - m x|
        ≤ 2 * (2 : ℝ)⁻¹ ^ (s + 1) := mul_le_mul hc_bound h (abs_nonneg _) (by norm_num)
      _ = (2 : ℝ)⁻¹ ^ s := by
        rw [pow_add, pow_one]
        have : (2 : ℝ) * ((2 : ℝ)⁻¹ ^ s * (2 : ℝ)⁻¹) = (2 : ℝ) * (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ s := by
          ring
        rw [this, mul_inv_cancel₀ (by norm_num), one_mul]

/-- Step 3 of the proof of `isComputablyRandom_firstTrialBiased_iff`: the adjusted
capitals preserve computability. -/
private lemma isComputablyRandom_firstTrialBiased_iff_computable (m : BitString → ℝ)
    (hcomp : IsComputableOnStrings m) :
    IsComputableOnStrings (fun x => if x.length = 0 then m x else
                                      m x * (massR uniformMeasure x / massR firstTrialBiased x)) ∧
    IsComputableOnStrings (fun x => if x.length = 0 then m x else
                                      m x * (massR firstTrialBiased x / massR uniformMeasure x)) :=
  ⟨isComputablyRandom_firstTrialBiased_iff_ltr m hcomp,
      isComputablyRandom_firstTrialBiased_iff_rtl m hcomp⟩

/-- Step 4 of the proof of `isComputablyRandom_firstTrialBiased_iff`: the adjusted
capitals win if and only if the original capitals win. -/
private lemma isComputablyRandom_firstTrialBiased_iff_wins_aux_bounds (x : BitString)
    (hx : 0 < x.length) :
  let u := massR uniformMeasure x
  let f := massR firstTrialBiased x
  (u / f ∈ Set.Icc (3/4 : ℝ) (3/2) ∧ f / u ∈ Set.Icc (2/3 : ℝ) (4/3)) := by
  intro u f
  have hu : u = (2 : ℝ)⁻¹ ^ x.length := massR_uniformMeasure x
  have hf : f = ∏ i : Fin x.length, if x[i.val] = true then if (i.val : ℕ) = 0 then (2/3:ℝ) else
    1/2 else 1 - if (i.val : ℕ) = 0 then (2/3:ℝ) else 1/2 := by
    dsimp [f, firstTrialBiased]
    rw [massR_independentTrials]
    congr
    ext i
    congr 1
    · split_ifs <;> rfl
    · congr 1
      split_ifs <;> rfl
  have hz : (⟨0, hx⟩ : Fin x.length) ∈ Finset.univ := Finset.mem_univ _
  have hf2 : f = (if x[0]'(hx) = true then (2/3:ℝ) else 1/3) * (1/2:ℝ) ^ (x.length - 1) := by
    rw [hf]
    have hp := @Finset.prod_eq_mul_prod_sdiff_singleton (Fin x.length) ℝ _ _ Finset.univ
        (⟨0, hx⟩ : Fin x.length) (fun i => if x[i.val] = true then
                                             if (i.val : ℕ) = 0 then (2/3:ℝ) else
                                               1/2 else 1 - if (i.val : ℕ) = 0 then (2/3:ℝ) else
                                                          1/2) (by intro hc; exfalso; exact hc hz)
    rw [hp]
    congr 1
    · dsimp
      split_ifs <;> norm_num
    · have h_all : ∏ x_1 ∈ Finset.univ \ {(⟨0, hx⟩ : Fin x.length)},
        (if x[x_1.val] = true then if (x_1.val : ℕ) = 0 then (2 / 3 : ℝ) else
          1 / 2 else 1 - if (x_1.val : ℕ) = 0 then (2 / 3 : ℝ) else
                       1 / 2) = ∏ x_1 ∈ Finset.univ \ {(⟨0, hx⟩ : Fin x.length)}, (1/2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj0 : (j.val : ℕ) ≠ 0 := by
          intro hc
          have hc' : j = ⟨0, hx⟩ := Fin.ext hc
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
          exact hj.2 hc'
        have heq : ((if (j.val : ℕ) = 0 then (2 / 3 : ℝ) else 1 / 2) = 1/2) := by
          rw [ite_eq_right_iff.mpr (by intro hc; exfalso; exact hj0 hc)]
        rw [heq]
        split_ifs <;> norm_num
      rw [h_all]
      rw [Finset.prod_const]
      congr 1
      rw [Finset.card_sdiff]
      have hc : ({⟨0, hx⟩} ∩ Finset.univ : Finset (Fin x.length)).card = 1 := by
        have hc' : ({⟨0, hx⟩} ∩ Finset.univ : Finset (Fin x.length)) = {⟨0, hx⟩} := by
          ext j
          simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_univ, and_true]
        rw [hc']
        exact Finset.card_singleton _
      rw [hc, Finset.card_univ, Fintype.card_fin]
  have hu2 : u = (1/2:ℝ) ^ x.length := by
    rw [hu]
    have h_half : ((2:ℝ)⁻¹) = 1/2 := by norm_num
    rw [h_half]
  have hu3 : u = (1/2:ℝ) * (1/2:ℝ) ^ (x.length - 1) := by
    rw [hu2]
    have hs : x.length = 1 + (x.length - 1) := by omega
    conv =>
      lhs
      rw [hs]
    rw [pow_add]
    simp only [pow_one]
  constructor
  · rw [hu3, hf2]
    have heq : (1 / 2 * (1 / 2) ^ (x.length - 1)) /
        ((if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) * (1 / 2) ^ (x.length - 1)) = (1/2) /
        (if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) := by
      rw [div_eq_div_iff]
      · ring
      · positivity
      · positivity
    rw [heq]
    by_cases h_x0 : x[0]'(hx) = true
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 2/3 := by simp [h_x0]
      rw [heq2]
      constructor <;> norm_num
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 1/3 := by simp [h_x0]
      rw [heq2]
      constructor <;> norm_num
  · rw [hu3, hf2]
    have heq : ((if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) * (1 / 2) ^ (x.length - 1)) /
        (1 / 2 * (1 / 2) ^ (x.length - 1)) = (if x[0]'(hx) = true then (2 / 3 : ℝ) else 1 / 3) /
        (1/2) := by
      rw [div_eq_div_iff]
      · ring
      · positivity
      · positivity
    rw [heq]
    by_cases h_x0 : x[0]'(hx) = true
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 2/3 := by simp [h_x0]
      rw [heq2]
      constructor <;> norm_num
    · have heq2 : (if x[0]'(hx) = true then (2/3 : ℝ) else 1/3) = 1/3 := by simp [h_x0]
      rw [heq2]
      constructor <;> norm_num

private lemma isComputablyRandom_firstTrialBiased_iff_wins_bddAbove_mul
    {c : ℕ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hc : ∀ n, a ≤ c n ∧ c n ≤ b) (f : ℕ → ℝ) :
    BddAbove (Set.range f) ↔
      BddAbove (Set.range fun n => c n * f n) := by
  constructor
  · intro ⟨B, hB⟩
    use b * max B 0
    rintro y ⟨n, rfl⟩
    by_cases hf : 0 ≤ f n
    · have h1 : c n * f n ≤ b * f n := mul_le_mul_of_nonneg_right (hc n).2 hf
      have h2 : b * f n ≤ b * max B 0 := by
        apply mul_le_mul_of_nonneg_left
        · have : f n ≤ B := hB ⟨n, rfl⟩
          exact this.trans (le_max_left B 0)
        · exact le_trans (le_of_lt ha) (le_trans (hc n).1 (hc n).2)
      exact le_trans h1 h2
    · push Not at hf
      have : c n * f n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_trans (le_of_lt ha) (hc n).1)
          (le_of_lt hf)
      have h_zero : (0:ℝ) ≤ b * max B 0 :=
          mul_nonneg (le_trans (le_of_lt ha) (le_trans (hc n).1 (hc n).2)) (le_max_right B 0)
      exact le_trans this h_zero
  · intro ⟨B, hB⟩
    use max B 0 / a
    rintro y ⟨n, rfl⟩
    by_cases hf : 0 ≤ f n
    · have h1 : a * f n ≤ c n * f n := mul_le_mul_of_nonneg_right (hc n).1 hf
      have h2 : c n * f n ≤ B := hB ⟨n, rfl⟩
      have h3 : a * f n ≤ B := le_trans h1 h2
      have h4 : a * f n ≤ max B 0 := le_trans h3 (le_max_left B 0)
      rwa [le_div_iff₀ ha, mul_comm]
    · push Not at hf
      have h_zero : (0:ℝ) ≤ max B 0 / a := div_nonneg (le_max_right B 0) (le_of_lt ha)
      exact le_trans (le_of_lt hf) h_zero

private lemma isComputablyRandom_firstTrialBiased_iff_wins (w : CantorSeq) (m : BitString → ℝ)
    :
    (Wins m w ↔ Wins (fun x => if x.length = 0 then m x else
                                 m x * (massR uniformMeasure x / massR firstTrialBiased x)) w) ∧
    (Wins m w ↔ Wins (fun x => if x.length = 0 then m x else
                                 m x * (massR firstTrialBiased x / massR uniformMeasure x)) w) := by
  constructor
  · rw [Wins, Wins]
    have h1 : (fun n => m (cantorPrefix w n)) =
        (fun n => (if n = 0 then (1:ℝ) else (massR uniformMeasure (cantorPrefix w n) /
                                              massR firstTrialBiased (cantorPrefix w n))⁻¹) *
                                              (if (cantorPrefix w n).length =
                                              0 then m (cantorPrefix w n) else
                                                m (cantorPrefix w n) *
                                                (massR uniformMeasure (cantorPrefix w n) /
                                                massR firstTrialBiased (cantorPrefix w n)))) := by
      ext n
      by_cases hn : n = 0
      · simp [hn, cantorPrefix]
      · have hn_len : (cantorPrefix w n).length ≠ 0 := by simp [cantorPrefix, hn]
        have h_len : (cantorPrefix w n).length > 0 := by exact Nat.pos_of_ne_zero hn_len
        have hu : massR uniformMeasure (cantorPrefix w n) / massR firstTrialBiased
            (cantorPrefix w n) ≠ 0 := by
          have hb := isComputablyRandom_firstTrialBiased_iff_wins_aux_bounds
              (cantorPrefix w n) h_len
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) hb.1.1)
        simp only [hn, ite_false, cantorPrefix_length]
        have : (massR uniformMeasure (cantorPrefix w n) / massR firstTrialBiased
            (cantorPrefix w n))⁻¹ * (m (cantorPrefix w n) * (massR uniformMeasure (cantorPrefix w n)
            / massR firstTrialBiased (cantorPrefix w n))) = m (cantorPrefix w n) := by
          rw [mul_comm (m _), ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
        rw [this]
    rw [h1]
    have h_not : ¬ BddAbove (Set.range fun n =>
          (if n = 0 then 1 else (massR uniformMeasure (cantorPrefix w n) /
            massR firstTrialBiased (cantorPrefix w n))⁻¹) *
          (if (cantorPrefix w n).length = 0 then m (cantorPrefix w n) else
            m (cantorPrefix w n) * (massR uniformMeasure (cantorPrefix w n) /
              massR firstTrialBiased (cantorPrefix w n)))) ↔
        ¬ BddAbove (Set.range fun n =>
          (if (cantorPrefix w n).length = 0 then m (cantorPrefix w n) else
            m (cantorPrefix w n) * (massR uniformMeasure (cantorPrefix w n) /
              massR firstTrialBiased (cantorPrefix w n)))) := by
      have hbdd : ∀ n, (2/3:ℝ) ≤ (if n = 0 then 1 else (massR uniformMeasure (cantorPrefix w n) /
                                                         massR firstTrialBiased (cantorPrefix w
                                                         n))⁻¹) ∧ (if n = 0 then 1 else
                                                           (massR uniformMeasure (cantorPrefix w n)
                                                           / massR firstTrialBiased
                                                           (cantorPrefix w n))⁻¹) ≤ (4/3:ℝ) := by
        intro n
        by_cases hn : n = 0
        · simp only [hn, ↓reduceIte]
          exact ⟨by norm_num, by norm_num⟩
        · have hn_len : (cantorPrefix w n).length ≠ 0 := by simp [cantorPrefix, hn]
          have h_len : (cantorPrefix w n).length > 0 := by exact Nat.pos_of_ne_zero hn_len
          have hb := isComputablyRandom_firstTrialBiased_iff_wins_aux_bounds
              (cantorPrefix w n) h_len
          simp only [hn, ↓reduceIte, inv_div]
          exact hb.2
      have := isComputablyRandom_firstTrialBiased_iff_wins_bddAbove_mul (a := 2/3) (b := 4/3)
          (by norm_num) hbdd (fun n => (if (cantorPrefix w n).length =
                                         0 then m (cantorPrefix w n) else
                                           m (cantorPrefix w n) *
                                           (massR uniformMeasure (cantorPrefix w n) /
                                           massR firstTrialBiased (cantorPrefix w n))))
      exact not_congr this.symm
    rw [h_not]
  · rw [Wins, Wins]
    have h1 : (fun n => m (cantorPrefix w n)) =
        (fun n => (if n = 0 then (1:ℝ) else (massR firstTrialBiased (cantorPrefix w n) /
                                              massR uniformMeasure (cantorPrefix w n))⁻¹) *
                                              (if (cantorPrefix w n).length =
                                              0 then m (cantorPrefix w n) else
                                                m (cantorPrefix w n) *
                                                (massR firstTrialBiased (cantorPrefix w n) /
                                                massR uniformMeasure (cantorPrefix w n)))) := by
      ext n
      by_cases hn : n = 0
      · simp [hn, cantorPrefix]
      · have hn_len : (cantorPrefix w n).length ≠ 0 := by simp [cantorPrefix, hn]
        have h_len : (cantorPrefix w n).length > 0 := by exact Nat.pos_of_ne_zero hn_len
        have hu : massR firstTrialBiased (cantorPrefix w n) / massR uniformMeasure
            (cantorPrefix w n) ≠ 0 := by
          have hb := isComputablyRandom_firstTrialBiased_iff_wins_aux_bounds
              (cantorPrefix w n) h_len
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) hb.2.1)
        simp only [hn, ite_false, cantorPrefix_length]
        have : (massR firstTrialBiased (cantorPrefix w n) / massR uniformMeasure
            (cantorPrefix w n))⁻¹ * (m (cantorPrefix w n) *
            (massR firstTrialBiased (cantorPrefix w n) / massR uniformMeasure (cantorPrefix w n))) =
            m (cantorPrefix w n) := by
          rw [mul_comm (m _), ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
        rw [this]
    rw [h1]
    have h_not : ¬ BddAbove (Set.range fun n =>
          (if n = 0 then 1 else (massR firstTrialBiased (cantorPrefix w n) /
            massR uniformMeasure (cantorPrefix w n))⁻¹) *
          (if (cantorPrefix w n).length = 0 then m (cantorPrefix w n) else
            m (cantorPrefix w n) * (massR firstTrialBiased (cantorPrefix w n) /
              massR uniformMeasure (cantorPrefix w n)))) ↔
        ¬ BddAbove (Set.range fun n =>
          (if (cantorPrefix w n).length = 0 then m (cantorPrefix w n) else
            m (cantorPrefix w n) * (massR firstTrialBiased (cantorPrefix w n) /
              massR uniformMeasure (cantorPrefix w n)))) := by
      have hbdd : ∀ n, (3/4:ℝ) ≤ (if n = 0 then 1 else (massR firstTrialBiased (cantorPrefix w n) /
                                                         massR uniformMeasure (cantorPrefix w n))⁻¹)
                                                         ∧ (if n = 0 then 1 else
                                                           (massR firstTrialBiased (cantorPrefix w
                                                           n) / massR uniformMeasure
                                                           (cantorPrefix w n))⁻¹) ≤ (3/2:ℝ) := by
        intro n
        by_cases hn : n = 0
        · simp only [hn, ↓reduceIte]
          exact ⟨by norm_num, by norm_num⟩
        · have hn_len : (cantorPrefix w n).length ≠ 0 := by simp [cantorPrefix, hn]
          have h_len : (cantorPrefix w n).length > 0 := by exact Nat.pos_of_ne_zero hn_len
          have hb := isComputablyRandom_firstTrialBiased_iff_wins_aux_bounds
              (cantorPrefix w n) h_len
          simp only [hn, ↓reduceIte, inv_div]
          exact hb.1
      have := isComputablyRandom_firstTrialBiased_iff_wins_bddAbove_mul (a := 3/4) (b := 3/2)
          (by norm_num) hbdd (fun n => (if (cantorPrefix w n).length =
                                         0 then m (cantorPrefix w n) else
                                           m (cantorPrefix w n) *
                                           (massR firstTrialBiased (cantorPrefix w n) /
                                           massR uniformMeasure (cantorPrefix w n))))
      exact not_congr this.symm
    rw [h_not]

/-- **SUV Problem 275, p. 297.**  The same sequences are computably random for these two
measures. -/
theorem isComputablyRandom_firstTrialBiased_iff (w : CantorSeq) :
    IsComputablyRandom firstTrialBiased w ↔ IsComputablyRandom uniformMeasure w := by
  constructor
  · intro h m hfair hcomp hwins
    obtain ⟨hcomp1, _⟩ := isComputablyRandom_firstTrialBiased_iff_computable m hcomp
    obtain ⟨hwins1, _⟩ := isComputablyRandom_firstTrialBiased_iff_wins w m
    exact h _ (isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_ltr hfair) hcomp1
        (hwins1.mp hwins)
  · intro h m hfair hcomp hwins
    obtain ⟨_, hcomp2⟩ := isComputablyRandom_firstTrialBiased_iff_computable m hcomp
    obtain ⟨_, hwins2⟩ := isComputablyRandom_firstTrialBiased_iff_wins w m
    exact h _ (isComputablyRandom_firstTrialBiased_iff_fair_capital_adj_rtl hfair) hcomp2
        (hwins2.mp hwins)

/-- The hypotheses of **Theorem 196, p. 297**: both probability sequences are computable and lie in
`(ε, 1 - ε)`. -/
structure IsSeparatedComputable (ε : ℝ) (p : ℕ → NNReal) : Prop where
  computable : IsComputableProbSeq p
  lower : ∀ i, ε < p i
  upper : ∀ i, (p i : ℝ) < 1 - ε

/-- Step 1 of the proof of `isMartinLofRandom_iff_of_summable`: along a sequence that is
Martin-Löf random for `μ`, every computable probability measure `μ'` is dominated by `μ` up to a
constant factor: `μ'(w↾n) ≤ C · μ(w↾n)` for all `n`. (Combine the bounded a priori deficiency of `w`
for `μ` with the domination `c · μ' ≤ M` of the universal semimeasure.) -/
private theorem isMartinLofRandom_iff_of_summable_dominate {μ μ' : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hμ : IsComputableMeasure μ)
    (hμ' : IsComputableMeasure μ') {w : CantorSeq} (hw : IsMartinLofRandom μ w) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, cantorMass μ' (cantorPrefix w n) ≤
      ENNReal.ofReal C * cantorMass μ (cantorPrefix w n) := by
  obtain ⟨c, hc⟩ := boundedAPrioriDeficiency_of_isMartinLofRandom hμ hw
  obtain ⟨c', hc'0, hc'⟩ := exists_pos_mul_cantorMass_le_universal μ' hμ'
  refine ⟨2 ^ c * c'⁻¹, by positivity, fun n => ?_⟩
  have hmul : ENNReal.ofReal c'⁻¹ * ENNReal.ofReal c' = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc'0.le), inv_mul_cancel₀ hc'0.ne', ENNReal.ofReal_one]
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ c) = (2 : ℝ≥0∞) ^ c := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  calc cantorMass μ' (cantorPrefix w n)
      = ENNReal.ofReal c'⁻¹ * (ENNReal.ofReal c' * cantorMass μ' (cantorPrefix w n)) := by
        rw [← mul_assoc, hmul, one_mul]
    _ ≤ ENNReal.ofReal c'⁻¹ * ((2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n)) := by
        exact mul_le_mul' le_rfl ((hc' _).trans (hc n))
    _ = ENNReal.ofReal (2 ^ c * c'⁻¹) * cantorMass μ (cantorPrefix w n) := by
        rw [ENNReal.ofReal_mul (by positivity), h2]
        ring

/-- Step 2 of the proof of `isMartinLofRandom_iff_of_summable`: if `w` is Martin-Löf
random
for `μ` and `μ(w↾n) ≤ C · μ'(w↾n)` for all `n`, then `w` is Martin-Löf random for `μ'`.  (Bounded a
priori deficiency criterion in both directions.) -/
private theorem isMartinLofRandom_iff_of_summable_converse {μ μ' : Measure CantorSeq}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hμ : IsComputableMeasure μ)
    (hμ' : IsComputableMeasure μ') {w : CantorSeq} (hw : IsMartinLofRandom μ w) (C : ℝ)
    (hC : ∀ n, cantorMass μ (cantorPrefix w n) ≤
      ENNReal.ofReal C * cantorMass μ' (cantorPrefix w n)) :
    IsMartinLofRandom μ' w := by
  obtain ⟨c, hc⟩ := boundedAPrioriDeficiency_of_isMartinLofRandom hμ hw
  refine isMartinLofRandom_of_boundedAPrioriDeficiency hμ' ⟨c + ⌈C⌉₊, fun n => ?_⟩
  have hCle : ENNReal.ofReal C ≤ (2 : ℝ≥0∞) ^ ⌈C⌉₊ :=
    calc ENNReal.ofReal C ≤ ENNReal.ofReal (⌈C⌉₊ : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil C)
      _ = (⌈C⌉₊ : ℝ≥0∞) := ENNReal.ofReal_natCast _
      _ ≤ (2 : ℝ≥0∞) ^ ⌈C⌉₊ := by exact_mod_cast (Nat.lt_two_pow_self (n := ⌈C⌉₊)).le
  calc universalContinuousSemimeasure (cantorPrefix w n)
      ≤ (2 : ℝ≥0∞) ^ c * cantorMass μ (cantorPrefix w n) := hc n
    _ ≤ (2 : ℝ≥0∞) ^ c * (ENNReal.ofReal C * cantorMass μ' (cantorPrefix w n)) := by
        gcongr
        exact hC n
    _ ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ ⌈C⌉₊ * cantorMass μ' (cantorPrefix w n)) := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (c + ⌈C⌉₊) * cantorMass μ' (cantorPrefix w n) := by
        rw [pow_add]; ring

/-- Computability of the reflected approximation of Step 3: switch at the index `N` from `q` to
`2 q(·, s + 2) - q'(·, s + 2)`. -/
private lemma isMartinLofRandom_iff_of_summable_computable (N : ℕ) {q q' : ℕ × ℕ → ℚ}
    (hq : Computable q) (hq' : Computable q') :
    Computable (fun a : ℕ × ℕ =>
      if N ≤ a.1 then 2 * q (a.1, a.2 + 2) - q' (a.1, a.2 + 2) else q a) := by
  have hc : Computable (fun a : ℕ × ℕ => decide (N ≤ a.1)) :=
    (Primrec.nat_le.comp (Primrec.const N) Primrec.fst).decide.to_comp
  have hshift : Computable (fun a : ℕ × ℕ => (a.1, a.2 + 2)) :=
    Computable.pair Computable.fst
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)).to_comp
  have h1 : Computable (fun a : ℕ × ℕ => q (a.1, a.2 + 2)) := hq.comp hshift
  have h2 : Computable (fun a : ℕ × ℕ => q' (a.1, a.2 + 2)) := hq'.comp hshift
  have h3 : Computable (fun a : ℕ × ℕ => (2 : ℚ) * q (a.1, a.2 + 2)) :=
    Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul (Computable.const (2 : ℚ)) h1
  have h4 : Computable (fun a : ℕ × ℕ => 2 * q (a.1, a.2 + 2) - q' (a.1, a.2 + 2)) :=
    Computable₂.comp (f := fun a b : ℚ => a - b) computable₂_ratSub h3 h2
  refine (Computable.cond hc h4 hq).of_eq fun a => ?_
  by_cases h : N ≤ a.1 <;> simp [h]

/-- Step 3 of the proof of `isMartinLofRandom_iff_of_summable`: the reflected sequence.
Since `∑ (p_i - p'_i)² < ∞`, from some index `N` on `|p_i - p'_i| < ε/2`; let `p''_i = p_i` for
`i < N` and `p''_i = 2 p_i - p'_i` for `i ≥ N`.  Then `p''` is a computable sequence separated from
`0` and `1` by `ε/2` (for `i ≥ N`, `p''_i = p_i + (p_i - p'_i)` lies within `ε/2` of `p_i`). -/
private theorem isMartinLofRandom_iff_of_summable_reflect {ε : ℝ} (hε : 0 < ε)
    {p p' : ℕ → NNReal} (hps : IsSeparatedComputable ε p) (hps' : IsSeparatedComputable ε p')
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) :
    ∃ (p'' : ℕ → NNReal) (N : ℕ), IsSeparatedComputable (ε / 2) p'' ∧
      (∀ i, i < N → p'' i = p i) ∧
      (∀ i, N ≤ i → |(p i : ℝ) - p' i| < ε / 2 ∧ (p'' i : ℝ) = 2 * p i - p' i) := by
  classical
  have hε2 : 0 < (ε / 2) ^ 2 := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds hε2))
  have hclose : ∀ i, N ≤ i → |(p i : ℝ) - p' i| < ε / 2 := fun i hi =>
    abs_lt_of_sq_lt_sq (hN i hi) (by positivity)
  have hlow : ∀ i, N ≤ i → ε / 2 < 2 * (p i : ℝ) - p' i := fun i hi => by
    have h1 := (abs_lt.mp (hclose i hi)).1
    have h2 := hps.lower i
    linarith
  have hupp : ∀ i, N ≤ i → 2 * (p i : ℝ) - p' i < 1 - ε / 2 := fun i hi => by
    have h1 := (abs_lt.mp (hclose i hi)).2
    have h2 := hps.upper i
    linarith
  obtain ⟨p'', hp''⟩ : ∃ p'' : ℕ → NNReal,
      ∀ i, p'' i = if N ≤ i then Real.toNNReal (2 * p i - p' i) else p i :=
    ⟨_, fun _ => rfl⟩
  have hval1 : ∀ i, N ≤ i → (p'' i : ℝ) = 2 * p i - p' i := fun i hi => by
    rw [hp'' i]
    simp only [hi, ↓reduceIte]
    exact Real.coe_toNNReal _ (by linarith [hlow i hi])
  have hval2 : ∀ i, i < N → p'' i = p i := fun i hi => by
    rw [hp'' i]
    simp only [show ¬ N ≤ i by omega, ↓reduceIte]
  refine ⟨p'', N, ⟨?_, ?_, ?_⟩, hval2, fun i hi => ⟨hclose i hi, hval1 i hi⟩⟩
  · obtain ⟨q, hq, hqerr⟩ := hps.computable
    obtain ⟨q', hq', hqerr'⟩ := hps'.computable
    refine ⟨_, isMartinLofRandom_iff_of_summable_computable N hq hq', fun i s => ?_⟩
    by_cases h : N ≤ i
    · have ha := hqerr i (s + 2)
      have hb := hqerr' i (s + 2)
      have hpow : (2 : ℝ)⁻¹ ^ (s + 2) = (2 : ℝ)⁻¹ ^ s / 4 := by
        rw [pow_add]; norm_num; ring
      have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ s := by positivity
      simp only [h, ↓reduceIte]
      push_cast
      rw [hval1 i h]
      rw [hpow] at ha hb
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    · simp only [h, ↓reduceIte]
      rw [hval2 i (by omega)]
      exact hqerr i s
  · intro i
    by_cases h : N ≤ i
    · rw [hval1 i h]; exact hlow i h
    · rw [hval2 i (by omega)]
      have := hps.lower i
      linarith
  · intro i
    by_cases h : N ≤ i
    · rw [hval1 i h]; exact hupp i h
    · rw [hval2 i (by omega)]
      have := hps.upper i
      linarith

/-- Auxiliary inequality for Step 4: `exp (-(2 t)) ≤ 1 - t` for `0 ≤ t ≤ 1/2`. -/
private lemma isMartinLofRandom_iff_of_summable_exp_le {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1 / 2) : Real.exp (-(2 * t)) ≤ 1 - t := by
  have h := Real.add_one_le_exp (2 * t)
  have hpos : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ hpos]
  have h2 : (1 - t) * (2 * t + 1) ≤ (1 - t) * Real.exp (2 * t) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]

/-- Auxiliary coordinatewise inequality for Step 4.  Here `f, g, h` are the factors of the three
measures at one coordinate (for the bit `1`: `p_i, p'_i, p''_i`; for the bit `0`: `1 - p_i`, etc.),
`d² = (f - g)²`, and `A = log (1/ε)`. -/
private lemma isMartinLofRandom_iff_of_summable_core {ε : ℝ} (hε : 0 < ε) {N : ℕ} {A : ℝ}
    (hA : Real.exp (-A) = ε) {i : ℕ} {f g h d : ℝ} (hf : ε < f) (hf1 : f ≤ 1) (hg : ε < g)
    (hd : d ^ 2 = (f - g) ^ 2) (h1 : i < N → h = f)
    (h2 : N ≤ i → |f - g| < ε / 2 ∧ h = 2 * f - g) :
    Real.exp (-((if i < N then A else 0) + 2 * (d ^ 2 / ε ^ 2))) * f ^ 2 ≤ g * h := by
  have hf0 : 0 < f := hε.trans hf
  have ht0 : 0 ≤ d ^ 2 / ε ^ 2 := by positivity
  by_cases hi : i < N
  · simp only [hi, ↓reduceIte]
    rw [h1 hi]
    have e1 : Real.exp (-(A + 2 * (d ^ 2 / ε ^ 2))) ≤ ε := by
      rw [neg_add, Real.exp_add, hA]
      have h3 : Real.exp (-(2 * (d ^ 2 / ε ^ 2))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h3 hε.le]
    have a1 : ε * f ^ 2 ≤ ε * f := by
      nlinarith [mul_nonneg (mul_nonneg hε.le hf0.le) (sub_nonneg.mpr hf1)]
    have a2 : ε * f ≤ g * f := mul_le_mul_of_nonneg_right hg.le hf0.le
    calc Real.exp (-(A + 2 * (d ^ 2 / ε ^ 2))) * f ^ 2 ≤ ε * f ^ 2 :=
          mul_le_mul_of_nonneg_right e1 (sq_nonneg f)
      _ ≤ g * f := by linarith
  · simp only [hi, ↓reduceIte]
    obtain ⟨hdf, hh⟩ := h2 (not_lt.mp hi)
    rw [hh]
    have hd2 : d ^ 2 < ε ^ 2 / 4 := by
      rw [hd]
      have := abs_lt.mp hdf
      nlinarith [this.1, this.2]
    have ht1 : d ^ 2 / ε ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε]
    have hexp := isMartinLofRandom_iff_of_summable_exp_le ht0 ht1
    have hfe : ε ^ 2 ≤ f ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hf) (add_pos hf0 hε)]
    have hdf2 : d ^ 2 ≤ d ^ 2 / ε ^ 2 * f ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hfe (sq_nonneg d)
    calc Real.exp (-(0 + 2 * (d ^ 2 / ε ^ 2))) * f ^ 2
        ≤ (1 - d ^ 2 / ε ^ 2) * f ^ 2 := by
          rw [zero_add]; exact mul_le_mul_of_nonneg_right hexp (sq_nonneg f)
      _ = f ^ 2 - d ^ 2 / ε ^ 2 * f ^ 2 := by ring
      _ ≤ f ^ 2 - d ^ 2 := by linarith
      _ = g * (2 * f - g) := by rw [hd]; ring

/-- Auxiliary Step 4: the product inequality over the first `n` coordinates, for an arbitrary
choice `b` of bits, with the constant `exp (-(N log (1/ε) + 2 ∑ (p_i - p'_i)²/ε²))`. -/
private lemma isMartinLofRandom_iff_of_summable_prod {ε : ℝ} (hε : 0 < ε)
    {p p' p'' : ℕ → NNReal} (hlow : ∀ i, ε < p i) (hupp : ∀ i, (p i : ℝ) < 1 - ε)
    (hlow' : ∀ i, ε < p' i) (hupp' : ∀ i, (p' i : ℝ) < 1 - ε)
    {N : ℕ} {A : ℝ} (hA : Real.exp (-A) = ε) (hA0 : 0 ≤ A)
    (hN1 : ∀ i, i < N → p'' i = p i)
    (hN2 : ∀ i, N ≤ i → |(p i : ℝ) - p' i| < ε / 2 ∧ (p'' i : ℝ) = 2 * p i - p' i)
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) (n : ℕ) (b : Fin n → Bool) :
    Real.exp (-(N * A + 2 * ∑' i, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2)) *
        (∏ i : Fin n, if b i then (p i : ℝ) else 1 - (p i : ℝ)) ^ 2 ≤
      (∏ i : Fin n, if b i then (p' i : ℝ) else 1 - (p' i : ℝ)) *
        ∏ i : Fin n, if b i then (p'' i : ℝ) else 1 - (p'' i : ℝ) := by
  have key : ∀ i : Fin n,
      Real.exp (-((if (i : ℕ) < N then A else 0) + 2 * (((p i : ℝ) - p' i) ^ 2 / ε ^ 2))) *
        (if b i then (p i : ℝ) else 1 - (p i : ℝ)) ^ 2 ≤
      (if b i then (p' i : ℝ) else 1 - (p' i : ℝ)) *
        (if b i then (p'' i : ℝ) else 1 - (p'' i : ℝ)) := by
    intro i
    have hi1 : (i : ℕ) < N → (p'' i : ℝ) = p i := fun hi => by rw [hN1 i hi]
    have hp1 : (p i : ℝ) ≤ 1 := by linarith [hupp i]
    cases hb : b i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine isMartinLofRandom_iff_of_summable_core hε hA (f := 1 - (p i : ℝ))
        (g := 1 - (p' i : ℝ)) (h := 1 - (p'' i : ℝ)) (d := (p i : ℝ) - p' i) ?_ ?_ ?_ ?_ ?_ ?_
      · linarith [hupp i]
      · linarith [hlow i]
      · linarith [hupp' i]
      · ring
      · intro hi
        rw [hi1 hi]
      · intro hi
        obtain ⟨h2a, h2b⟩ := hN2 i hi
        refine ⟨?_, ?_⟩
        · rw [show (1 - (p i : ℝ)) - (1 - (p' i : ℝ)) = -((p i : ℝ) - p' i) by ring, abs_neg]
          exact h2a
        · rw [h2b]
          ring
    · simp only [↓reduceIte]
      exact isMartinLofRandom_iff_of_summable_core hε hA (f := (p i : ℝ))
        (g := (p' i : ℝ)) (h := (p'' i : ℝ)) (d := (p i : ℝ) - p' i) (hlow i) hp1 (hlow' i) rfl
        hi1 (hN2 i)
  have e1 : ∑ i : Fin n, (if (i : ℕ) < N then A else 0) ≤ N * A := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < N then A else 0) n, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range n).filter (· < N)).card ≤ N := by
      calc _ ≤ (Finset.range N).card :=
            Finset.card_le_card (fun i hi => by simp at hi ⊢; omega)
        _ = N := Finset.card_range N
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hA0
  have e2 : ∑ i : Fin n, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2 ≤
      ∑' i, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ((p i : ℝ) - p' i) ^ 2 / ε ^ 2) n]
    exact Summable.sum_le_tsum _ (fun i _ => by positivity) (hsum.div_const _)
  have hs : ∑ i : Fin n, ((if (i : ℕ) < N then A else 0) +
        2 * (((p i : ℝ) - p' i) ^ 2 / ε ^ 2)) ≤
      N * A + 2 * ∑' i, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  have hprod : ∏ i : Fin n, (Real.exp (-((if (i : ℕ) < N then A else 0) +
        2 * (((p i : ℝ) - p' i) ^ 2 / ε ^ 2))) *
        (if b i then (p i : ℝ) else 1 - (p i : ℝ)) ^ 2) ≤
      ∏ i : Fin n, ((if b i then (p' i : ℝ) else 1 - (p' i : ℝ)) *
        (if b i then (p'' i : ℝ) else 1 - (p'' i : ℝ))) :=
    Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => key i)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib,
    Finset.prod_pow] at hprod
  calc Real.exp (-(N * A + 2 * ∑' i, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2)) *
        (∏ i : Fin n, if b i then (p i : ℝ) else 1 - (p i : ℝ)) ^ 2
      ≤ Real.exp (-∑ i : Fin n, ((if (i : ℕ) < N then A else 0) +
          2 * (((p i : ℝ) - p' i) ^ 2 / ε ^ 2))) *
        (∏ i : Fin n, if b i then (p i : ℝ) else 1 - (p i : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hs)) (sq_nonneg _)
    _ ≤ _ := hprod

/-- Step 4 of the proof of `isMartinLofRandom_iff_of_summable`: the mass inequality
`c₀ · μ(x)² ≤ μ'(x) · μ''(x)` for all strings `x`, where `μ, μ', μ''` are the independent-trials
measures of `p, p', p''`, `p''_i = p_i` for `i < N` and `p''_i = 2 p_i - p'_i` for `i ≥ N`
(where `|p_i - p'_i| < ε/2`), `p, p'` separated from `0` and `1` by `ε` and
`∑ (p_i - p'_i)² < ∞`.  Coordinatewise, with `d_i = p_i - p'_i`: for `i ≥ N` the factors satisfy
`r'_i r''_i = r_i² - d_i²` for both bit values (`r_i ∈ {p_i, 1 - p_i}`, `r_i > ε`), so
`r'_i r''_i ≥ (1 - d_i²/ε²) r_i²`; for `i < N` it is `r'_i r_i ≥ ε r_i²`; and
`∏ (1 - t_i) ≥ exp (-2 ∑ t_i)` for `0 ≤ t_i ≤ 1/2`. -/
private theorem isMartinLofRandom_iff_of_summable_mass_ratio {ε : ℝ} (hε : 0 < ε)
    {p p' p'' : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1) (hp'' : ∀ i, p'' i ≤ 1)
    (hlow : ∀ i, ε < p i) (hupp : ∀ i, (p i : ℝ) < 1 - ε)
    (hlow' : ∀ i, ε < p' i) (hupp' : ∀ i, (p' i : ℝ) < 1 - ε)
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) {N : ℕ}
    (hN1 : ∀ i, i < N → p'' i = p i)
    (hN2 : ∀ i, N ≤ i → |(p i : ℝ) - p' i| < ε / 2 ∧ (p'' i : ℝ) = 2 * p i - p' i) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : BitString, c₀ * massR (independentTrials p hp) x ^ 2 ≤
      massR (independentTrials p' hp') x * massR (independentTrials p'' hp'') x := by
  have hε1 : ε < 1 := lt_of_lt_of_le (hlow 0) (NNReal.coe_le_one.mpr (hp 0))
  obtain ⟨A, hA, hA0⟩ : ∃ A : ℝ, Real.exp (-A) = ε ∧ 0 ≤ A :=
    ⟨-Real.log ε, by rw [neg_neg, Real.exp_log hε], by linarith [Real.log_nonpos hε.le hε1.le]⟩
  refine ⟨Real.exp (-(N * A + 2 * ∑' i, ((p i : ℝ) - p' i) ^ 2 / ε ^ 2)), Real.exp_pos _,
    fun x => ?_⟩
  rw [massR_independentTrials p hp x, massR_independentTrials p' hp' x,
    massR_independentTrials p'' hp'' x]
  exact isMartinLofRandom_iff_of_summable_prod hε hlow hupp hlow' hupp' hA hA0 hN1 hN2 hsum
    x.length (fun i => x[i])

/-- Step 5 of the proof of `isMartinLofRandom_iff_of_summable`: one direction.  If `w` is
Martin-Löf random for the `p`-trials then it is for the `p'`-trials. Assembly of Steps 1-4: with the
reflected `p''` of Step 3, Step 1 for `(μ, μ'')` gives `μ'' ≤ C μ` along `w`; Step 4 gives
`c₀ μ² ≤ μ' μ'' ≤ C μ' μ`, so `μ ≤ (C / c₀) μ'` along `w` (the masses are positive); Step 2
finishes. -/
private theorem isMartinLofRandom_iff_of_summable_direction {ε : ℝ} (hε : 0 < ε)
    {p p' : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1)
    (hps : IsSeparatedComputable ε p) (hps' : IsSeparatedComputable ε p')
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) (w : CantorSeq)
    (hw : IsMartinLofRandom (independentTrials p hp) w) :
    IsMartinLofRandom (independentTrials p' hp') w := by
  obtain ⟨p'', N, hps'', hN1, hN2⟩ :=
    isMartinLofRandom_iff_of_summable_reflect hε hps hps' hsum
  have hp'' : ∀ i, p'' i ≤ 1 := fun i => by
    have := hps''.upper i
    exact NNReal.coe_le_one.mp (by linarith)
  have hμ := isComputableMeasure_independentTrials hp hps.computable
  have hμ' := isComputableMeasure_independentTrials hp' hps'.computable
  have hμ'' := isComputableMeasure_independentTrials hp'' hps''.computable
  obtain ⟨C, hC0, hC⟩ := isMartinLofRandom_iff_of_summable_dominate hμ hμ'' hw
  obtain ⟨c₀, hc₀, hc⟩ := isMartinLofRandom_iff_of_summable_mass_ratio hε hp hp' hp''
    hps.lower hps.upper hps'.lower hps'.upper hsum hN1 hN2
  refine isMartinLofRandom_iff_of_summable_converse hμ hμ' hw (C / c₀) fun n => ?_
  have hCn := hC n
  have hcn := hc (cantorPrefix w n)
  generalize cantorPrefix w n = x at hCn hcn ⊢
  have hfin : ∀ (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1), cantorMass (independentTrials q hq) x ≠ ⊤ :=
    fun q hq => measure_ne_top _ _
  have hpos : 0 < massR (independentTrials p hp) x := by
    rw [massR_independentTrials]
    refine Finset.prod_pos fun i _ => ?_
    split_ifs
    · exact hε.trans (hps.lower _)
    · have := hps.upper i
      linarith
  -- the domination of Step 1, in real numbers
  have hC' : massR (independentTrials p'' hp'') x ≤ C * massR (independentTrials p hp) x := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hfin p hp)) hCn
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0.le] at h1
  have h3 : c₀ * massR (independentTrials p hp) x ^ 2 ≤
      massR (independentTrials p' hp') x * (C * massR (independentTrials p hp) x) :=
    hcn.trans (mul_le_mul_of_nonneg_left hC' ENNReal.toReal_nonneg)
  have h4 : massR (independentTrials p hp) x ≤ C / c₀ * massR (independentTrials p' hp') x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith
  calc cantorMass (independentTrials p hp) x
      = ENNReal.ofReal (massR (independentTrials p hp) x) :=
        (ENNReal.ofReal_toReal (hfin p hp)).symm
    _ ≤ ENNReal.ofReal (C / c₀ * massR (independentTrials p' hp') x) :=
        ENNReal.ofReal_le_ofReal h4
    _ = ENNReal.ofReal (C / c₀) * cantorMass (independentTrials p' hp') x := by
        rw [ENNReal.ofReal_mul (div_nonneg hC0.le hc₀.le)]
        congr 1
        exact ENNReal.ofReal_toReal (hfin p' hp')

/-- **SUV Theorem 196(a), p. 297 (Vovk).**  If `∑ (p_i - p'_i)²` is finite, the classes of
Martin-Löf random sequences for the two product measures coincide. -/
theorem isMartinLofRandom_iff_of_summable {ε : ℝ} (hε : 0 < ε) {p p' : ℕ → NNReal}
    (hp : ∀ i, p i ≤ 1) (hp' : ∀ i, p' i ≤ 1) (hps : IsSeparatedComputable ε p)
    (hps' : IsSeparatedComputable ε p')
    (hsum : Summable fun i => ((p i : ℝ) - p' i) ^ 2) (w : CantorSeq) :
    IsMartinLofRandom (independentTrials p hp) w ↔
      IsMartinLofRandom (independentTrials p' hp') w := by
  constructor
  · intro h
    exact isMartinLofRandom_iff_of_summable_direction hε hp hp' hps hps' hsum w h
  · intro h
    exact isMartinLofRandom_iff_of_summable_direction hε hp' hp hps' hps
      (hsum.congr fun i => by ring) w h

end Kolmogorov.FrequencyGames
