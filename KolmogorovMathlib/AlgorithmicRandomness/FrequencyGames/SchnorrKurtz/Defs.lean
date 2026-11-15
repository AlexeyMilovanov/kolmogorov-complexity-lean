/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeaverOmega
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# Schnorr and Kurtz randomness: definitions and covers

This file defines effective null sets and randomness notions for a measure `π` on Cantor space:
`IsSchnorrNull` and `IsSchnorrRandom` (covers whose total mass is bounded by `2^-n` and
computable), `IsKurtzNull` and `IsKurtzRandom` (finite computable covers), together with
`coverMass`, the mass of an optional interval of a cover, and `IsComputableGrowth`, the
computable non-decreasing unbounded functions.

The main results characterize non-Schnorr-randomness through computable series of covers:
`not_isSchnorrRandom_iff_exists_series_totalize` turns a computable cover by optional intervals
into a total computable cover, and `not_isSchnorrRandom_iff_exists_series_moduli` gives covers
with a computable modulus of convergence. This belongs to the part of the book of Shen, Uspensky
and Vereshchagin on Schnorr and Kurtz randomness.
-/

namespace Kolmogorov.FrequencyGames


open MeasureTheory Filter Topology
open scoped ENNReal

/-- The `π`-mass of an optional interval of a cover. -/
noncomputable def coverMass (π : Measure CantorSeq) (o : Option BitString) : ℝ≥0∞ :=
  o.elim 0 (cantorMass π)

/-- A sequence of reals with rational approximations of prescribed error, uniformly. -/
def IsComputableRealSeq (v : ℕ → ℝ) : Prop :=
  ∃ q : ℕ × ℕ → ℚ, Computable q ∧ ∀ n s, |(q (n, s) : ℝ) - v n| ≤ (2 : ℝ)⁻¹ ^ s

/-- *Schnorr effectively null sets*: for each `n` one enumerates a cover whose sum of masses is
at most `2^{-n}`, and that sum is computable, uniformly in `n`.  This is the dyadic form of
SUV Section 3.4, p. 69, used on p. 282. -/
def IsSchnorrNull (π : Measure CantorSeq) (A : Set CantorSeq) : Prop :=
  ∃ f : ℕ → ℕ → Option BitString, Computable₂ f ∧
    (∀ n, A ⊆ ⋃ i, (f n i).elim ∅ cantorCylinder) ∧
    (∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n) ∧
    IsComputableRealSeq fun n => (∑' i, coverMass π (f n i)).toReal

/-- A sequence is *Schnorr random* when it is in no Schnorr effectively null set. -/
def IsSchnorrRandom (π : Measure CantorSeq) (w : CantorSeq) : Prop := ¬ IsSchnorrNull π {w}

/-- *Kurtz effectively null sets*: for each `n` one computes a finite list of intervals covering
the set, with sum of masses at most `2^{-n}`.  This follows the sum-of-masses wording of
SUV Section 3.4, p. 70, as used in Problem 272. -/
def IsKurtzNull (π : Measure CantorSeq) (A : Set CantorSeq) : Prop :=
  ∃ f : ℕ → List BitString, Computable f ∧ ∀ n,
    A ⊆ (⋃ x ∈ f n, cantorCylinder x) ∧ ((f n).map (cantorMass π)).sum ≤ dyadicValue 1 n

/-- A sequence is *Kurtz random* when it is in no Kurtz effectively null set. -/
def IsKurtzRandom (π : Measure CantorSeq) (w : CantorSeq) : Prop := ¬ IsKurtzNull π {w}

/-- `g` is a computable non-decreasing unbounded function, as in Theorem 183. -/
structure IsComputableGrowth (g : ℕ → ℕ) : Prop where
  computable : Computable g
  monotone : Monotone g
  unbounded : ∀ B, ∃ n, B ≤ g n

private lemma not_isSchnorrRandom_iff_exists_series_sum_aux
    (n : ℕ) (f : BitString → ENNReal) :
    ∑ x ∈ levelFinset (n + 1), f x =
      ∑ x ∈ levelFinset n, (f (x ++ [false]) + f (x ++ [true])) := by
  have H : ∑ x ∈ levelFinset (n + 1), f x = ((levelList (n + 1)).map f).sum := by
    rw [sum_levelFinset_eq_sum_levelList]
  rw [H]
  change (((levelList n).map (fun x => x ++ [false]) ++
    (levelList n).map (fun x => x ++ [true])).map f).sum = _
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  have heq1 : (List.map (f ∘ fun x => x ++ [false]) (levelList n)).sum =
    (List.map (fun x => f (x ++ [false])) (levelList n)).sum := rfl
  have heq2 : (List.map (f ∘ fun x => x ++ [true]) (levelList n)).sum =
    (List.map (fun x => f (x ++ [true])) (levelList n)).sum := rfl
  rw [heq1, heq2]
  have h1 : (List.map (fun x => f (x ++ [false])) (levelList n)).sum =
    ∑ x ∈ levelFinset n, f (x ++ [false]) := by
    rw [← sum_levelFinset_eq_sum_levelList]
  have h2 : (List.map (fun x => f (x ++ [true])) (levelList n)).sum =
    ∑ x ∈ levelFinset n, f (x ++ [true]) := by
    rw [← sum_levelFinset_eq_sum_levelList]
  rw [h1, h2, ← Finset.sum_add_distrib]

private lemma not_isSchnorrRandom_iff_exists_series_sum
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (j : ℕ) :
    ∑ x ∈ levelFinset j, cantorMass π x = 1 := by
  induction j with
  | zero =>
    rw [sum_levelFinset_eq_sum_levelList]
    change cantorMass π [] + 0 = 1
    rw [add_zero, cantorMass, cantorCylinder_nil, measure_univ]
  | succ j ih =>
    rw [not_isSchnorrRandom_iff_exists_series_sum_aux]
    have h_add : ∀ x, cantorMass π (x ++ [false]) + cantorMass π (x ++ [true]) = cantorMass π x :=
        fun x => (cantorMass_add π x).symm
    simp_rw [h_add]
    exact ih

/-- Step 2 of the proof of
`not_isSchnorrRandom_iff_exists_series_t`: there is a string of length
j with mass bounded by 2^-j. -/
private lemma not_isSchnorrRandom_iff_exists_series_exists_small
    {π : Measure CantorSeq} [IsProbabilityMeasure π] (j : ℕ) :
    ∃ x ∈ levelList j, cantorMass π x ≤ (2:ENNReal)⁻¹ ^ j := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have h1 : ∑ x ∈ levelFinset j, (2:ENNReal)⁻¹ ^ j < ∑ x ∈ levelFinset j, cantorMass π x := by
    apply ENNReal.sum_lt_sum_of_nonempty
    · exact ⟨List.replicate j false, mem_levelFinset.mpr (by simp)⟩
    · intro x hx
      exact h x (by simpa [levelFinset] using hx)
  have h2 : ∑ x ∈ levelFinset j, (2:ENNReal)⁻¹ ^ j = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, levelFinset]
    rw [List.toFinset_card_of_nodup (nodup_levelList j), length_levelList j]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [← ENNReal.inv_pow]
    exact ENNReal.mul_inv_cancel (pow_ne_zero j (by simp)) (ENNReal.pow_ne_top (by simp))
  rw [h2] at h1
  rw [not_isSchnorrRandom_iff_exists_series_sum j] at h1
  exact lt_irrefl 1 h1

/-- Step 3 of the proof of
`not_isSchnorrRandom_iff_exists_series_t`: if a string of length j has
mass at most 2^-j, its approximation at stage j+1 is at most 3. -/
private lemma not_isSchnorrRandom_iff_exists_series_approx_le_3
    {π : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (hbound : ∀ x s, dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧ cantorMass π x ≤
        dyadicValue (a x s) s + dyadicValue 1 s)
    {x : BitString} {j : ℕ} (h_mass : cantorMass π x ≤ (2 : ENNReal)⁻¹ ^ j) :
    a x (j + 1) ≤ 3 := by
  have h1 := (hbound x (j + 1)).1
  have h2 : cantorMass π x + dyadicValue 1 (j + 1) ≤ (2:ENNReal)⁻¹ ^ j + dyadicValue 1 (j + 1) := by
    apply add_le_add h_mass le_rfl
  have h3 : dyadicValue (a x (j + 1)) (j + 1) ≤ (2:ENNReal)⁻¹ ^ j + dyadicValue 1 (j + 1) :=
      le_trans h1 h2
  have h4 : dyadicValue (a x (j + 1)) (j + 1) = (a x (j + 1) : ENNReal) * (2:ENNReal)⁻¹^(j+1) := by
    unfold dyadicValue
    rw [div_eq_mul_inv, ENNReal.inv_pow]
  have h5 : (2:ENNReal)⁻¹ ^ j + dyadicValue 1 (j + 1) = (3 : ENNReal) * (2:ENNReal)⁻¹^(j+1) := by
    unfold dyadicValue
    rw [div_eq_mul_inv, ENNReal.inv_pow, Nat.cast_one, one_mul]
    have h6 : (2:ENNReal)⁻¹ ^ (j+1) = (2:ENNReal)⁻¹ ^ j * (2:ENNReal)⁻¹ := by rw [pow_add, pow_one]
    rw [h6]
    have h7 : (3 : ENNReal) = 2 + 1 := by norm_num
    rw [h7, add_mul]
    have h8 : (2 : ENNReal) * ((2:ENNReal)⁻¹ ^ j * (2:ENNReal)⁻¹) = (2 : ENNReal) * (2:ENNReal)⁻¹ *
        (2:ENNReal)⁻¹ ^ j := by
      rw [mul_assoc, mul_comm ((2:ENNReal)⁻¹ ^ j), ← mul_assoc]
    rw [h8]
    have h9 : (2 : ENNReal) * (2:ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num)
        (by norm_num)
    rw [h9, one_mul, one_mul]
  have h9 : (a x (j + 1) : ENNReal) * (2:ENNReal)⁻¹^(j+1) ≤ (3 : ENNReal) * (2:ENNReal)⁻¹^(j+1) :=
      by
    rw [← h4, ← h5]
    exact h3
  have h10 : (a x (j + 1) : ENNReal) ≤ 3 := by
    have h11 : ((2:ENNReal)⁻¹)^(j+1) ≠ 0 := by
      apply ENNReal.pow_ne_zero
      exact ENNReal.inv_ne_zero.mpr (by norm_num)
    have h12 : ((2:ENNReal)⁻¹)^(j+1) ≠ ⊤ := by
      have h12a : ((2:ENNReal)⁻¹) ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
      exact ENNReal.pow_ne_top h12a
    exact (ENNReal.mul_le_mul_iff_left h11 h12).mp (by exact h9)
  have h14 : (a x (j + 1) : ENNReal) ≤ (3 : ℕ) := h10
  exact_mod_cast h14

/-- Step 4 of the proof of
`not_isSchnorrRandom_iff_exists_series_t`: the approximation at stage
j+1 being at most 3 implies the mass is at most 2 * 2^-j. -/
private lemma not_isSchnorrRandom_iff_exists_series_mass_le_2
    {π : Measure CantorSeq} {a : BitString → ℕ → ℕ}
    (hbound : ∀ x s, dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧ cantorMass π x ≤
        dyadicValue (a x s) s + dyadicValue 1 s)
    {x : BitString} {j : ℕ} (h_approx : a x (j + 1) ≤ 3) :
    cantorMass π x ≤ 2 * dyadicValue 1 j := by
  have h2 := (hbound x (j + 1)).2
  have h3 : dyadicValue (a x (j + 1)) (j + 1) ≤ dyadicValue 3 (j + 1) := by
    unfold dyadicValue
    gcongr
  calc cantorMass π x ≤ dyadicValue (a x (j + 1)) (j + 1) + dyadicValue 1 (j + 1) := h2
    _ ≤ dyadicValue 3 (j + 1) + dyadicValue 1 (j + 1) := by
      exact add_le_add h3 le_rfl
    _ = 2 * dyadicValue 1 j := by
      unfold dyadicValue
      have h4 : ((3 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (j + 1) + ((1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (j + 1) =
          ((4 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (j + 1) := by
        rw [← ENNReal.add_div]
        norm_num
      rw [h4]
      have h5 : ((4 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (j + 1) = 2 * (((1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ j) :=
          by
        rw [pow_add, pow_one]
        have h6 : ((4 : ℕ) : ℝ≥0∞) = 2 * 2 := by norm_num
        rw [h6]
        have h7 : (2 : ℝ≥0∞) ^ j * (2 : ℝ≥0∞) = (2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ j := mul_comm _ _
        rw [h7]
        rw [ENNReal.mul_div_mul_left]
        · rw [div_eq_mul_inv]
          norm_num
        · norm_num
        · norm_num
      exact h5

/-- Step 5 of the proof of
`not_isSchnorrRandom_iff_exists_series_t`: computable search over a
list. -/
private lemma not_isSchnorrRandom_iff_exists_series_search
    (l : ℕ → List BitString) (hl_comp : Computable l) (p : ℕ → BitString → Bool)
    (hp_comp : Computable₂ p)
    (h_ex : ∀ j, ∃ x ∈ l j, p j x = true) :
    ∃ f : ℕ → BitString, Computable f ∧ ∀ j, f j ∈ l j ∧ p j (f j) = true := by
  let f : ℕ → BitString := fun j => ((l j).filter (p j)).head?.getD []
  have hf_comp : Computable f := by
    have h1 : Computable (fun j => (l j).filter (p j)) := computable_list_filter hl_comp hp_comp
    have h2 : Computable (fun j => ((l j).filter (p j)).head?) :=
      Primrec.list_head?.to_comp.comp h1
    exact Computable.option_getD h2 (Computable.const [])
  use f
  constructor
  · exact hf_comp
  · intro j
    have ⟨x, hx_mem, hx_p⟩ := h_ex j
    have h_filter : x ∈ (l j).filter (p j) := by
      rw [List.mem_filter]
      exact ⟨hx_mem, hx_p⟩
    dsimp [f]
    cases h_eq : (l j).filter (p j) with
    | nil =>
      rw [h_eq] at h_filter
      contradiction
    | cons y ys =>
      have h_f : (List.cons y ys).head?.getD [] = y := rfl
      rw [h_f]
      have h_y_mem : y ∈ List.cons y ys := List.mem_cons_self
      rw [← h_eq] at h_y_mem
      rw [List.mem_filter] at h_y_mem
      exact h_y_mem

/-- Step 6 of the proof of
`not_isSchnorrRandom_iff_exists_series_t`: computability of the
predicate. -/
private lemma not_isSchnorrRandom_iff_exists_series_p_comp
    {a : BitString → ℕ → ℕ} (h_a_comp : Computable₂ a) :
    Computable₂ (fun (j : ℕ) (x : BitString) => decide (a x (j + 1) ≤ 3)) := by
  have h_eval : Computable (fun p : ℕ × BitString => a p.2 (p.1 + 1)) := by
    exact Computable₂.comp h_a_comp Computable.snd
      (Computable.succ.comp Computable.fst)
  have h_le : Computable (fun n : ℕ => decide (n ≤ 3)) :=
    (Primrec.nat_le.comp Primrec.id (Primrec.const 3)).decide.to_comp
  exact (h_le.comp h_eval).to₂

private lemma not_isSchnorrRandom_iff_exists_series_t
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) :
    ∃ t : ℕ → BitString, Computable t ∧ ∀ j, cantorMass π (t j) ≤ 2 * dyadicValue 1 j := by
  rcases hπ with ⟨a, h_a_comp, h_a_bound⟩
  let p : ℕ → BitString → Bool := fun j x => decide (a x (j + 1) ≤ 3)
  have hp_comp : Computable₂ p :=
      not_isSchnorrRandom_iff_exists_series_p_comp h_a_comp
  have h_ex : ∀ j, ∃ x ∈ levelList j, p j x = true := by
    intro j
    have ⟨x, hx_mem, hx_mass⟩ := not_isSchnorrRandom_iff_exists_series_exists_small (π := π) j
    use x, hx_mem
    dsimp only [p]; rw [decide_eq_true_eq]
    exact not_isSchnorrRandom_iff_exists_series_approx_le_3 h_a_bound hx_mass
  have ⟨t, ht_comp, ht_prop⟩ := not_isSchnorrRandom_iff_exists_series_search levelList
      computable_levelList p hp_comp h_ex
  use t, ht_comp
  intro j
  have h_prop_j := ht_prop j
  have h_approx : a (t j) (j + 1) ≤ 3 := by
    have h1 := h_prop_j.2
    dsimp only [p] at h1
    exact of_decide_eq_true h1
  exact not_isSchnorrRandom_iff_exists_series_mass_le_2 h_a_bound h_approx


/-- A computable cover of `{w}` by optional intervals with small total mass can be totalized
into a computable cover by strings, with total mass at most `5 · 2^-n`, which agrees with the
given cover wherever it is defined. -/
lemma not_isSchnorrRandom_iff_exists_series_totalize {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) {w : CantorSeq} (f : ℕ → ℕ → Option BitString)
    (hf_comp : Computable₂ f) (hf_cover : ∀ n, {w} ⊆ ⋃ i, (f n i).elim ∅ cantorCylinder)
    (hf_bound : ∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n) :
    ∃ g : ℕ → ℕ → BitString, Computable₂ g ∧ (∀ n, {w} ⊆ ⋃ i, cantorCylinder (g n i)) ∧
      (∀ n, ∑' i, cantorMass π (g n i) ≤ 5 * dyadicValue 1 n) ∧
      (∀ n i s, f n i = some s → g n i = s) ∧
      (∀ n i, f n i = none → cantorMass π (g n i) ≤ 2 * dyadicValue 1 (n + i)) := by
  obtain ⟨t, ht_comp, ht_bound⟩ :=
      not_isSchnorrRandom_iff_exists_series_t hπ
  let g : ℕ → ℕ → BitString := fun n i => (f n i).getD (t (n + i))
  use g
  have hg_comp : Computable₂ g := by
    apply Computable.option_getD
    · exact hf_comp
    · exact ht_comp.comp (Primrec.to_comp Primrec.nat_add)
  refine ⟨hg_comp, ?_, ?_, ?_, ?_⟩
  · intro n
    have h1 := hf_cover n
    refine Set.Subset.trans h1 ?_
    apply Set.iUnion_mono
    intro i
    cases hfi : f n i with
    | none =>
      simp only [Option.elim_none, Set.empty_subset]
    | some s =>
      simp only [Option.elim_some]
      have h2 : g n i = s := by
        change (f n i).getD (t (n + i)) = s
        rw [hfi]
        rfl
      rw [h2]
  · intro n
    have hterm (i : ℕ) : cantorMass π (g n i) ≤ coverMass π (f n i) + 2 * dyadicValue 1 (n + i) :=
        by
      cases hfi : f n i with
      | none =>
          simpa [g, hfi, coverMass] using ht_bound (n + i)
      | some s =>
          simp [g, hfi, coverMass]
    calc
      ∑' i, cantorMass π (g n i) ≤ ∑' i, (coverMass π (f n i) + 2 * dyadicValue 1 (n + i)) := by
        exact ENNReal.tsum_le_tsum hterm
      _ = ∑' i, coverMass π (f n i) + ∑' i, 2 * dyadicValue 1 (n + i) := by
        apply ENNReal.tsum_add
      _ ≤ dyadicValue 1 n + ∑' i, 2 * dyadicValue 1 (n + i) := by
        have H1 := hf_bound n
        exact add_le_add H1 le_rfl
      _ = dyadicValue 1 n + ∑' i, 2 * (dyadicValue 1 n * dyadicValue 1 i) := by
        congr 1
        apply tsum_congr
        intro i
        congr 1
        unfold dyadicValue
        have H (k : ℕ) : ((1:ℕ) : ENNReal) / 2 ^ k = (2:ENNReal)⁻¹ ^ k := by
          rw [Nat.cast_one, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_one]
        rw [H (n+i), H n, H i, pow_add]
      _ = dyadicValue 1 n + 2 * dyadicValue 1 n * ∑' i, dyadicValue 1 i := by
        congr 1
        have h_mul : ∑' i, 2 * (dyadicValue 1 n * dyadicValue 1 i) = ∑' i, (2 * dyadicValue 1 n) *
            dyadicValue 1 i := by
          apply tsum_congr
          intro i
          rw [mul_assoc]
        rw [h_mul]
        rw [ENNReal.tsum_mul_left]
      _ = dyadicValue 1 n + 2 * dyadicValue 1 n * 2 := by
        congr 1
        congr 1
        have H_eq : ∑' i, dyadicValue 1 i = ∑' i, (2 : ENNReal)⁻¹ ^ i := by
          apply tsum_congr
          intro i
          unfold dyadicValue
          rw [Nat.cast_one, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_one]
        rw [H_eq]
        have H_geom := ENNReal.tsum_geometric (2 : ENNReal)⁻¹
        have H_sub : (1 : ENNReal) - (2 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
          have h1 : (1 : ENNReal) = (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := by
            have h2 : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = (2 : ENNReal) * (2 : ENNReal)⁻¹ := by
              rw [two_mul]
            rw [h2]
            exact (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm
          rw [h1]
          exact ENNReal.add_sub_cancel_right (by norm_num)
        rw [H_sub] at H_geom
        have H_inv_inv : ((2 : ENNReal)⁻¹)⁻¹ = 2 := by
          exact inv_inv (2 : ENNReal)
        rw [H_inv_inv] at H_geom
        exact H_geom
      _ = 5 * dyadicValue 1 n := by
        have h_comm : 2 * dyadicValue 1 n * 2 = dyadicValue 1 n * (2 * 2) := by
          ring
        rw [h_comm]
        have h_comm2 : dyadicValue 1 n = dyadicValue 1 n * 1 := by
          exact (mul_one (dyadicValue 1 n)).symm
        nth_rw 1 [h_comm2]
        rw [← mul_add]
        have h5 : (1 + 2 * 2 : ENNReal) = 5 := by norm_num
        rw [h5, mul_comm]
  · intro n i s hfi
    change (f n i).getD (t (n + i)) = s
    rw [hfi]
    rfl
  · intro n i hfi
    have h2 : g n i = t (n + i) := by
      change (f n i).getD (t (n + i)) = t (n + i)
      rw [hfi]
      rfl
    rw [h2]
    exact ht_bound (n + i)

/-- Step 1 of the proof of `not_isSchnorrRandom_iff_exists_series_moduli`:
tail bound. -/
private lemma not_isSchnorrRandom_iff_exists_series_tail_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (f : ℕ → ℕ → Option BitString) (g : ℕ → ℕ → BitString)
    (hg_eq : ∀ n i s, f n i = some s → g n i = s)
    (hg_junk : ∀ n i, f n i = none → cantorMass π (g n i) ≤ 2 * dyadicValue 1 (n + i))
    (n k m : ℕ) (hm : k + 3 ≤ m)
    (h_tail : ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 2)) :
    ∑' i, cantorMass π (g n (m + i)) ≤ dyadicValue 1 k := by
  have h_bound : ∀ i, cantorMass π (g n (m + i)) ≤ coverMass π (f n (m + i)) + 2 * dyadicValue 1
      (n + m + i) := by
    intro i
    cases h : f n (m + i) with
    | none =>
      have h1 := hg_junk n (m + i) h
      calc cantorMass π (g n (m + i))
        _ ≤ 2 * dyadicValue 1 (n + (m + i)) := h1
        _ = 2 * dyadicValue 1 (n + m + i) := by rw [← add_assoc]
        _ = 0 + 2 * dyadicValue 1 (n + m + i) := by rw [zero_add]
        _ = coverMass π none + 2 * dyadicValue 1 (n + m + i) := by rfl
        _ = _ := by rw [← h]
    | some s =>
      have h1 := hg_eq n (m + i) s h
      calc cantorMass π (g n (m + i))
        _ = cantorMass π s := by rw [h1]
        _ ≤ cantorMass π s + 2 * dyadicValue 1 (n + m + i) := by exact le_self_add
        _ = coverMass π (some s) + 2 * dyadicValue 1 (n + m + i) := by rfl
        _ = _ := by rw [← h]
  
  have h_sum : ∑' i, cantorMass π (g n (m + i)) ≤ ∑' i, (coverMass π (f n (m + i)) + 2 * dyadicValue
      1 (n + m + i)) := by
    exact ENNReal.tsum_le_tsum h_bound
  
  have h_sum_split : ∑' i, (coverMass π (f n (m + i)) + 2 * dyadicValue 1 (n + m + i)) =
      (∑' i, coverMass π (f n (m + i))) + (∑' i, 2 * dyadicValue 1 (n + m + i)) := by
    exact ENNReal.tsum_add
  rw [h_sum_split] at h_sum
  
  have h_sum2 : ∑' i, cantorMass π (g n (m + i)) ≤ dyadicValue 1 (k + 2) + ∑' i, 2 * dyadicValue 1
      (n + m + i) := by
    apply le_trans h_sum
    exact add_le_add h_tail (le_refl _)
  have h_geom_sum : ∑' i, (2:ENNReal) * dyadicValue 1 (n + m + i) = 4 * dyadicValue 1 (n + m) := by
    calc ∑' i, (2:ENNReal) * dyadicValue 1 (n + m + i)
      _ = ∑' i, (2:ENNReal) * (2⁻¹ ^ (n + m + i)) := by
        congr
        funext i
        rw [dyadicValue_one_eq_inv_two_pow']
      _ = ∑' i, (2:ENNReal) * (2⁻¹ ^ (n + m) * 2⁻¹ ^ i) := by
        congr
        funext i
        rw [pow_add]
      _ = ∑' i, ((2:ENNReal) * 2⁻¹ ^ (n + m)) * 2⁻¹ ^ i := by
        congr
        funext i
        rw [mul_assoc]
      _ = ((2:ENNReal) * 2⁻¹ ^ (n + m)) * ∑' i, (2⁻¹ : ENNReal) ^ i := by
        exact ENNReal.tsum_mul_left
      _ = ((2:ENNReal) * 2⁻¹ ^ (n + m)) * (1 - (2⁻¹ : ENNReal))⁻¹ := by
        rw [ENNReal.tsum_geometric]
      _ = ((2:ENNReal) * 2⁻¹ ^ (n + m)) * 2 := by
        congr 1
        have h_sub : (1:ENNReal) - 2⁻¹ = 2⁻¹ := by
          have h_one : (1:ENNReal) = 2⁻¹ + 2⁻¹ := by exact ENNReal.inv_two_add_inv_two.symm
          nth_rewrite 1 [h_one]
          exact ENNReal.add_sub_cancel_right (by exact ENNReal.inv_ne_top.mpr two_ne_zero)
        rw [h_sub]
        exact _root_.inv_inv (2 : ENNReal)
      _ = 4 * dyadicValue 1 (n + m) := by
        rw [← dyadicValue_one_eq_inv_two_pow']
        have h_mul_comm : ((2:ENNReal) * dyadicValue 1 (n + m)) * 2 = 2 * 2 * dyadicValue 1
            (n + m) := by
          rw [mul_comm, ← mul_assoc]
        rw [h_mul_comm]
        have h_four : (2:ENNReal) * 2 = 4 := by
          norm_cast
        rw [h_four]
  have hnm : k + 3 ≤ n + m := by omega
  have h1 : dyadicValue 1 (k + 2) ≤ dyadicValue 1 (k + 1) :=
    Kolmogorov.dyadicValue_antitone_stage 1 (by omega)
  have h2 : 4 * dyadicValue 1 (n + m) ≤ dyadicValue 1 (k + 1) := by
    calc
      4 * dyadicValue 1 (n + m) = dyadicValue 4 (n + m) := by
        rw [Kolmogorov.dyadicValue_natCast_mul_left 4 1 (n + m)]
        norm_num
      _ ≤ dyadicValue 4 (k + 3) := Kolmogorov.dyadicValue_antitone_stage 4 hnm
      _ = dyadicValue 1 (k + 1) := by
        simpa [Nat.add_assoc] using (Kolmogorov.dyadicValue_two_pow_mul_add 1 (k + 1) 2)
  have h3 : dyadicValue 1 (k + 2) + 4 * dyadicValue 1 (n + m) ≤ dyadicValue 1 k := by
    calc
      dyadicValue 1 (k + 2) + 4 * dyadicValue 1 (n + m)
          ≤ dyadicValue 1 (k + 1) + dyadicValue 1 (k + 1) := add_le_add h1 h2
      _ = dyadicValue 1 k := by
          rw [← Kolmogorov.dyadicValue_add]
          simpa using (Kolmogorov.dyadicValue_two_mul_succ 1 k)
  rw [h_geom_sum] at h_sum2
  exact le_trans h_sum2 h3

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_series_moduli`:
small tail. -/
private lemma not_isSchnorrRandom_iff_exists_series_small_tail
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (f : ℕ → ℕ → Option BitString)
    (hf_bound : ∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n)
    (n k : ℕ) :
    ∃ m, k + 3 ≤ m ∧ ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 4) := by
  have h_bound := hf_bound n
  have h_sum_ne_top : ∑' i, coverMass π (f n i) ≠ ⊤ :=
    ne_top_of_le_ne_top (dyadicValue_ne_top 1 n) h_bound
  have h_tendsto := ENNReal.tendsto_sum_nat_add (fun i => coverMass π (f n i)) h_sum_ne_top
  have h_pos : (0 : ℝ≥0∞) < dyadicValue 1 (k + 4) := by
    rw [dyadicValue]
    apply ENNReal.div_pos_iff.mpr
    constructor
    · norm_num
    · exact ENNReal.pow_ne_top (by norm_num)
  have h_eventually : Filter.Eventually (fun m => ∑' i, coverMass π (f n (m + i)) < dyadicValue 1
      (k + 4)) Filter.atTop := by
    have h1 := (tendsto_order.1 h_tendsto).2 _ h_pos
    exact h1.mono (by
      intro m hm
      have h2 : ∑' i, coverMass π (f n (m + i)) = ∑' (j : ℕ), coverMass π (f n (j + m)) := by
        apply tsum_congr
        intro i
        rw [Nat.add_comm]
      rwa [h2]
    )
  have h_eventually_ge : Filter.Eventually (fun m => k + 3 ≤ m) Filter.atTop :=
      Filter.eventually_ge_atTop (k + 3)
  have h_both := h_eventually.and h_eventually_ge
  obtain ⟨m, hm_both⟩ := h_both.exists
  use m
  exact ⟨hm_both.2, hm_both.1.le⟩

private def not_isSchnorrRandom_iff_exists_series_A
    (a : BitString → ℕ → ℕ) (f : ℕ → ℕ → Option BitString) (n m R : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, match f n i with
    | none => 0
    | some x => a x R

private def not_isSchnorrRandom_iff_exists_series_T
    (q : ℕ × ℕ → ℚ) (a : BitString → ℕ → ℕ) (f : ℕ → ℕ → Option BitString) (n k m : ℕ) : Bool :=
  let R := k + 6 + m
  (q (n, k + 6) : ℚ) * (2 : ℚ)^R <
      (not_isSchnorrRandom_iff_exists_series_A a f n m R : ℚ)
      + (2 : ℚ)^(m + 3)

private lemma not_isSchnorrRandom_iff_exists_series_A_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ (x : BitString) (s : ℕ),
        dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧
          cantorMass π x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (f : ℕ → ℕ → Option BitString) (n m R : ℕ) :
    |((not_isSchnorrRandom_iff_exists_series_A a f n m R : ℝ)
        / (2 ^ R) : ℝ) - (∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal)| ≤ (m : ℝ) /
        (2 ^ R) := by
  classical
  let b : ℕ → ℕ := fun i => match f n i with
    | none => 0
    | some x => a x R
  have hterm (i : ℕ) :
      |(b i : ℝ) / 2 ^ R - (coverMass π (f n i)).toReal| ≤ 1 / 2 ^ R := by
    cases h : f n i with
    | none =>
        simp only [b, h, coverMass, Option.elim_none, Nat.cast_zero, zero_div,
          ENNReal.toReal_zero, sub_zero, abs_zero]
        positivity
    | some x =>
        simp only [b, h, coverMass, Option.elim_some]
        have hmass : cantorMass π x ≠ ⊤ := measure_ne_top π _
        have hd : dyadicValue 1 R ≠ ⊤ := dyadicValue_ne_top 1 R
        have haR : dyadicValue (a x R) R ≠ ⊤ := dyadicValue_ne_top _ R
        obtain ⟨h₁, h₂⟩ := ha x R
        have h₁' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hmass, hd⟩) h₁
        have h₂' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨haR, hd⟩) h₂
        rw [ENNReal.toReal_add hmass hd, toReal_dyadicValue, toReal_dyadicValue] at h₁'
        rw [ENNReal.toReal_add haR hd, toReal_dyadicValue, toReal_dyadicValue] at h₂'
        simp only [Nat.cast_one] at h₁' h₂'
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  change |((∑ i ∈ Finset.range m, b i : ℕ) : ℝ) / 2 ^ R -
    ∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal| ≤ (m : ℝ) / 2 ^ R
  rw [Nat.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range m,
        |(b i : ℝ) / 2 ^ R - (coverMass π (f n i)).toReal| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m, (1 : ℝ) / 2 ^ R :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (m : ℝ) / 2 ^ R := by simp [div_eq_mul_inv]

private lemma not_isSchnorrRandom_iff_exists_series_sound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ (x : BitString) (s : ℕ),
        dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧
          cantorMass π x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (f : ℕ → ℕ → Option BitString) (hf_bound : ∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n)
    (q : ℕ × ℕ → ℚ)
    (hq_bound : ∀ n s, |(q (n, s) : ℝ) - (∑' i, coverMass π (f n i)).toReal| ≤ (2 : ℝ)⁻¹ ^ s)
    (n k m : ℕ) (hT : not_isSchnorrRandom_iff_exists_series_T
        q a f n k m = true) :
    ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 2) := by
  classical
  let R := k + 6 + m
  let A := not_isSchnorrRandom_iff_exists_series_A a f n m R
  -- Finiteness lets us transfer the prefix-tail splitting identity to the reals.
  have htotal : (∑' i, coverMass π (f n i)) ≠ ⊤ :=
    ne_top_of_le_ne_top (dyadicValue_ne_top 1 n) (hf_bound n)
  have hsplit : (∑ i ∈ Finset.range m, coverMass π (f n i)) +
      (∑' i, coverMass π (f n (m + i))) = ∑' i, coverMass π (f n i) := by
    simpa only [Nat.add_comm] using
      (Summable.sum_add_tsum_nat_add' (f := fun i => coverMass π (f n i))
        (k := m) ENNReal.summable)
  have hprefix : (∑ i ∈ Finset.range m, coverMass π (f n i)) ≠ ⊤ :=
    ne_top_of_le_ne_top htotal (by rw [← hsplit]; exact le_self_add)
  have htail : (∑' i, coverMass π (f n (m + i))) ≠ ⊤ :=
    ne_top_of_le_ne_top htotal (by rw [← hsplit]; exact le_add_self)
  have hterm : ∀ i, coverMass π (f n i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top htotal (ENNReal.le_tsum (f := fun j => coverMass π (f n j)) i)
  have hreal := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add hprefix htail, ENNReal.toReal_sum (fun i _ => hterm i)] at hreal
  -- At precision R, the accumulated prefix error is at most 2^(-(k + 6)).
  have hA := not_isSchnorrRandom_iff_exists_series_A_bound a
      ha f n m R
  change |(A : ℝ) / 2 ^ R - ∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal| ≤
    (m : ℝ) / 2 ^ R at hA
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have herror : (m : ℝ) / 2 ^ R ≤ (2 : ℝ)⁻¹ ^ (k + 6) := by
    calc (m : ℝ) / 2 ^ R ≤ (2 : ℝ) ^ m / 2 ^ R := by gcongr
         _ = (2 : ℝ)⁻¹ ^ (k + 6) := by
           dsimp [R]
           rw [pow_add, inv_pow]
           field_simp
  -- Dividing the rational test inequality gives a bound on the estimated tail.
  have htest : (q (n, k + 6) : ℝ) * 2 ^ R < (A : ℝ) + 2 ^ (m + 3) := by
    have hrat : q (n, k + 6) * (2 : ℚ) ^ R < (A : ℚ) + (2 : ℚ) ^ (m + 3) :=
      of_decide_eq_true hT
    exact_mod_cast hrat
  have htest_div : (q (n, k + 6) : ℝ) - (A : ℝ) / 2 ^ R <
      (2 : ℝ) ^ (m + 3) / 2 ^ R := by
    have hdiv := (div_lt_div_iff_of_pos_right (show (0 : ℝ) < 2 ^ R by positivity)).2 htest
    rw [mul_div_cancel_right₀ _ (by positivity), add_div] at hdiv
    linarith
  have hpow : (2 : ℝ) ^ (m + 3) / 2 ^ R = (2 : ℝ)⁻¹ ^ (k + 3) := by
    have hR : R = (m + 3) + (k + 3) := by dsimp [R]; omega
    rw [hR, pow_add, inv_pow]
    field_simp
    simp [pow_add]
  rw [hpow] at htest_div
  have hq := (abs_le.mp (hq_bound n (k + 6))).1
  have hprefix_error := (abs_le.mp hA).2
  -- Add the two approximation errors, then return to the finite ENNReal tail.
  have hreal_bound : (∑' i, coverMass π (f n (m + i))).toReal ≤ (2 : ℝ)⁻¹ ^ (k + 2) := by
    have heps : (2 : ℝ)⁻¹ ^ (k + 6) = (2 : ℝ)⁻¹ ^ (k + 2) / 16 := by
      rw [show k + 6 = (k + 2) + 4 by omega, pow_add]
      norm_num
      ring
    have hthresh : (2 : ℝ)⁻¹ ^ (k + 3) = (2 : ℝ)⁻¹ ^ (k + 2) / 2 := by
      rw [show k + 3 = (k + 2) + 1 by omega, pow_add]
      norm_num
      ring
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (k + 2) := by positivity
    rw [heps] at herror hq
    rw [hthresh] at htest_div
    linarith
  apply (ENNReal.toReal_le_toReal htail (dyadicValue_ne_top 1 (k + 2))).mp
  simpa [toReal_dyadicValue, inv_pow] using hreal_bound

private lemma not_isSchnorrRandom_iff_exists_series_complete_tail_bound
    {π : Measure CantorSeq} (f : ℕ → ℕ → Option BitString) (n m k : ℕ)
    (h_tail : ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 4)) :
    ∑' i, (coverMass π (f n (m + i))).toReal ≤ (2 : ℝ)⁻¹ ^ (k + 4) := by
  have ht : ((∑' i, coverMass π (f n (m + i))) : ℝ≥0∞).toReal ≤ (dyadicValue 1 (k + 4)).toReal :=
    ENNReal.toReal_mono (by dsimp [dyadicValue]; exact ENNReal.div_ne_top (ENNReal.natCast_ne_top 1)
                              (by norm_num)) h_tail
  have h_dyad : (dyadicValue 1 (k + 4)).toReal = (2 : ℝ)⁻¹ ^ (k + 4) := by
    dsimp [dyadicValue]
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow]
    simp
  have h_toReal_tsum : (∑' i, coverMass π (f n (m + i))).toReal = ∑' i,
      (coverMass π (f n (m + i))).toReal := by
    apply ENNReal.tsum_toReal_eq
    intro a
    have H : ∑' i, coverMass π (f n (m + i)) ≠ ∞ :=
        ne_top_of_le_ne_top (by dsimp [dyadicValue]; exact ENNReal.div_ne_top
                                  (ENNReal.natCast_ne_top 1) (by norm_num)) h_tail
    exact ENNReal.ne_top_of_tsum_ne_top H a
  rw [← h_toReal_tsum]
  rw [h_dyad] at ht
  exact ht

private lemma not_isSchnorrRandom_iff_exists_series_complete_split
    {π : Measure CantorSeq} (f : ℕ → ℕ → Option BitString) (n m : ℕ)
    (hf_bound : ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n) :
    ∑' i, (coverMass π (f n i)).toReal = (∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal) +
        ∑' i, (coverMass π (f n (m + i))).toReal := by
  have hf_ne_top : ∑' i, coverMass π (f n i) ≠ ∞ :=
    ne_top_of_le_ne_top (by dsimp [dyadicValue]; exact ENNReal.div_ne_top (ENNReal.natCast_ne_top 1)
                              (by norm_num)) hf_bound
  have h_sum : Summable (fun i => (coverMass π (f n i)).toReal) :=
    ENNReal.summable_toReal hf_ne_top
  have h1 := (Summable.sum_add_tsum_nat_add m h_sum).symm
  rw [h1]
  congr 1
  apply tsum_congr
  intro i
  rw [add_comm]

private lemma not_isSchnorrRandom_iff_exists_series_complete
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha : ∀ (x : BitString) (s : ℕ),
        dyadicValue (a x s) s ≤ cantorMass π x + dyadicValue 1 s ∧
          cantorMass π x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (f : ℕ → ℕ → Option BitString) (hf_bound : ∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n)
    (q : ℕ × ℕ → ℚ)
    (hq_bound : ∀ n s, |(q (n, s) : ℝ) - (∑' i, coverMass π (f n i)).toReal| ≤ (2 : ℝ)⁻¹ ^ s)
    (n k m : ℕ) (h_tail : ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 4)) :
    not_isSchnorrRandom_iff_exists_series_T q a f n k m = true := by
  dsimp [not_isSchnorrRandom_iff_exists_series_T]
  have h_bound := not_isSchnorrRandom_iff_exists_series_A_bound a ha f n m (k + 6 + m)
  have hq := hq_bound n (k + 6)
  have h_tail_real := not_isSchnorrRandom_iff_exists_series_complete_tail_bound f n m k h_tail
  have h_split := not_isSchnorrRandom_iff_exists_series_complete_split f n m (hf_bound n)
  have h_toReal : (∑' i, coverMass π (f n i)).toReal = ∑' i, (coverMass π (f n i)).toReal := by
    apply ENNReal.tsum_toReal_eq
    intro x
    have hdy : dyadicValue 1 n ≠ ⊤ := by
      dsimp [dyadicValue]
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top 1) (by norm_num)
    exact ENNReal.ne_top_of_tsum_ne_top (ne_top_of_le_ne_top hdy (hf_bound n)) x
  have H_final : (q (n, k + 6) : ℝ) <
      ((not_isSchnorrRandom_iff_exists_series_A a f n m
      (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) + 2 ^ (m + 3) / (2 ^ (k + 6 + m) : ℝ) := by
    have h_m_le : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_pow_self (n := m) (a := 2)
                                          (by norm_num)).le
    have h_pow1 : (2 : ℝ) ^ (k + 6 + m) = (2 : ℝ) ^ (k + 6) * (2 : ℝ) ^ m := by rw [pow_add]
    have h_pow2 : (2 : ℝ) ^ (k + 6) = (2 : ℝ) ^ (k + 4) * (2 : ℝ) ^ 2 := by
      have hk : k + 6 = k + 4 + 2 := by omega
      rw [hk, pow_add]
    have h_pow_inv1 : (2 : ℝ)⁻¹ ^ (k + 6) = 1 / (2 : ℝ) ^ (k + 6) := by rw [inv_pow, one_div]
    have h_pow_inv2 : (2 : ℝ)⁻¹ ^ (k + 4) = 1 / (2 : ℝ) ^ (k + 4) := by rw [inv_pow, one_div]
    have h_m_div : (m : ℝ) / (2 ^ (k + 6 + m)) ≤ (2 : ℝ)⁻¹ ^ (k + 6) := by
      rw [h_pow_inv1, h_pow1]
      have h_pos : (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ (k + 6) * (2 : ℝ) ^ m) := by positivity
      calc (m : ℝ) / ((2 : ℝ) ^ (k + 6) * (2 : ℝ) ^ m) = (m : ℝ) *
          (1 / ((2 : ℝ) ^ (k + 6) * (2 : ℝ) ^ m)) := by ring
        _ ≤ (2 ^ m : ℝ) * (1 / ((2 : ℝ) ^ (k + 6) * (2 : ℝ) ^ m)) := by gcongr
        _ = 1 / (2 : ℝ) ^ (k + 6) := by
          have h_2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          calc (2 ^ m : ℝ) * (1 / ((2 : ℝ) ^ (k + 6) * (2 : ℝ) ^ m)) = ((2 : ℝ) ^ m / (2 : ℝ) ^ m) *
              (1 / (2 : ℝ) ^ (k + 6)) := by ring
            _ = 1 / (2 : ℝ) ^ (k + 6) := by rw [div_self h_2m, one_mul]
    have Hq1 : (q (n, k + 6) : ℝ) - (∑' i, coverMass π (f n i)).toReal ≤ (2 : ℝ)⁻¹ ^ (k + 6) :=
        le_trans (le_abs_self _) hq
    have HA1 : (∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal) -
        ((not_isSchnorrRandom_iff_exists_series_A a f n m
        (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) ≤ (m : ℝ) / (2 ^ (k + 6 + m)) := by
      have h_neg : (∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal) -
          ((not_isSchnorrRandom_iff_exists_series_A a f n m
          (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) = -
          (((not_isSchnorrRandom_iff_exists_series_A a f n m
          (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) - (∑ i ∈ Finset.range m,
          (coverMass π (f n i)).toReal)) := by ring
      rw [h_neg]
      exact le_trans (neg_le_abs _) h_bound
    calc (q (n, k + 6) : ℝ)
        ≤ (∑' i, coverMass π (f n i)).toReal + (2 : ℝ)⁻¹ ^ (k + 6) := by linarith [Hq1]
      _ = (∑ i ∈ Finset.range m, (coverMass π (f n i)).toReal) +
          ∑' i, (coverMass π (f n (m + i))).toReal + (2 : ℝ)⁻¹ ^ (k + 6) := by
        rw [h_toReal, h_split]
      _ ≤ ((not_isSchnorrRandom_iff_exists_series_A a f n m
          (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) + (m : ℝ) / (2 ^ (k + 6 + m)) + ∑' i,
          (coverMass π (f n (m + i))).toReal + (2 : ℝ)⁻¹ ^ (k + 6) := by linarith [HA1]
      _ ≤ ((not_isSchnorrRandom_iff_exists_series_A a f n m
          (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) + (2 : ℝ)⁻¹ ^ (k + 6) + (2 : ℝ)⁻¹ ^ (k + 4) +
          (2 : ℝ)⁻¹ ^ (k + 6) := by linarith [h_m_div, h_tail_real]
      _ < ((not_isSchnorrRandom_iff_exists_series_A a f n m
          (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) + 2 ^ (m + 3) / (2 ^ (k + 6 + m) : ℝ) := by
        rw [h_pow_inv1, h_pow_inv2, h_pow1, h_pow2]
        have h_2m : (2 : ℝ) ^ m > 0 := by positivity
        have hp3 : (2 : ℝ) ^ (m + 3) = (2 : ℝ) ^ m * (2 : ℝ) ^ 3 := by rw [pow_add]
        rw [hp3]
        have hd : (2 : ℝ) ^ 2 = 4 := by norm_num
        have hd3 : (2 : ℝ) ^ 3 = 8 := by norm_num
        rw [hd, hd3]
        have h_pos : (2 : ℝ) ^ (k + 4) > 0 := by positivity
        have h_pos2 : (2 : ℝ) ^ m > 0 := by positivity
        have H1 : 1 / ((2 : ℝ) ^ (k + 4) * 4) + 1 / (2 : ℝ) ^ (k + 4) + 1 / ((2 : ℝ) ^ (k + 4) * 4)
            < (2 : ℝ) ^ m * 8 / ((2 : ℝ) ^ (k + 4) * 4 * (2 : ℝ) ^ m) := by
          calc 1 / ((2 : ℝ) ^ (k + 4) * 4) + 1 / (2 : ℝ) ^ (k + 4) + 1 / ((2 : ℝ) ^ (k + 4) * 4) =
              (1 / 4 + 1 + 1 / 4) / (2 : ℝ) ^ (k + 4) := by ring
            _ = (3 / 2) / (2 : ℝ) ^ (k + 4) := by norm_num
            _ < 2 / (2 : ℝ) ^ (k + 4) := by gcongr; norm_num
            _ = (2 : ℝ) ^ m * 8 / ((2 : ℝ) ^ (k + 4) * 4 * (2 : ℝ) ^ m) := by
              calc 2 / (2 : ℝ) ^ (k + 4)
                  = 2 * ((2 : ℝ) ^ m / (2 : ℝ) ^ m) / (2 : ℝ) ^ (k + 4) := by
                    rw [div_self (by positivity), mul_one]
                _ = (2 : ℝ) ^ m * 8 / ((2 : ℝ) ^ (k + 4) * 4 * (2 : ℝ) ^ m) := by ring
        linarith [H1]
  have h_pow3 : (2 : ℝ) ^ (k + 6 + m) > 0 := by positivity
  have h_mul : (q (n, k + 6) : ℝ) * 2 ^ (k + 6 + m) <
      ((not_isSchnorrRandom_iff_exists_series_A a f n m
      (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) * (2 ^ (k + 6 + m) : ℝ) + 2 ^ (m + 3) /
      (2 ^ (k + 6 + m) : ℝ) * (2 ^ (k + 6 + m) : ℝ) := by
    calc (q (n, k + 6) : ℝ) * 2 ^ (k + 6 + m) <
        (((not_isSchnorrRandom_iff_exists_series_A a f n m (k
        + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) + 2 ^ (m + 3) / (2 ^ (k + 6 + m) : ℝ)) *
        2 ^ (k + 6 + m) := mul_lt_mul_of_pos_right H_final h_pow3
      _ = ((not_isSchnorrRandom_iff_exists_series_A a f n m
          (k + 6 + m) : ℝ) / (2 ^ (k + 6 + m))) * (2 ^ (k + 6 + m) : ℝ) + 2 ^ (m + 3) /
          (2 ^ (k + 6 + m) : ℝ) * (2 ^ (k + 6 + m) : ℝ) := by ring
  rw [div_mul_cancel₀ _ (by positivity), div_mul_cancel₀ _ (by positivity)] at h_mul
  have h_final : (q (n, k + 6) : ℚ) * (2 : ℚ) ^ (k + 6 + m) <
      (not_isSchnorrRandom_iff_exists_series_A a f n m
      (k + 6 + m) : ℚ) + (2 : ℚ) ^ (m + 3) := by
    exact_mod_cast h_mul
  change decide ((q (n, k + 6) : ℚ) * (2 : ℚ) ^ (k + 6 + m) <
      (not_isSchnorrRandom_iff_exists_series_A a f n m
      (k + 6 + m) : ℚ) + (2 : ℚ) ^ (m + 3)) = true
  rw [decide_eq_true_eq]
  exact h_final

private lemma not_isSchnorrRandom_iff_exists_series_comp
    (q : ℕ × ℕ → ℚ) (hq_comp : Computable q)
    (a : BitString → ℕ → ℕ) (ha_comp : Computable₂ a)
    (f : ℕ → ℕ → Option BitString) (hf_comp : Computable₂ f) :
    Computable (fun p : ℕ × ℕ ×
        ℕ => not_isSchnorrRandom_iff_exists_series_T q a f
               p.1 p.2.1 p.2.2) := by
  have hk : Computable (fun p : ℕ × ℕ × ℕ => p.2.1 + 6) :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.const 6)
  have hm : Computable (fun p : ℕ × ℕ × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hR : Computable (fun p : ℕ × ℕ × ℕ => p.2.1 + 6 + p.2.2) :=
    Primrec.nat_add.to_comp.comp hk hm
  have hterm : Computable₂ (fun (p : ℕ × ℕ × ℕ) (i : ℕ) =>
      match f p.1 i with
      | none => 0
      | some x => a x (p.2.1 + 6 + p.2.2)) := by
    have ho : Computable (fun r : (ℕ × ℕ × ℕ) × ℕ => f r.1.1 r.2) :=
      hf_comp.comp (Computable.fst.comp Computable.fst) Computable.snd
    have hs : Computable₂ (fun (r : (ℕ × ℕ × ℕ) × ℕ) (x : BitString) =>
        a x (r.1.2.1 + 6 + r.1.2.2)) :=
      ha_comp.comp Computable.snd (hR.comp (Computable.fst.comp Computable.fst))
    refine (Computable.option_casesOn ho (Computable.const 0) hs).of_eq (fun r => ?_)
    dsimp only
    cases f r.1.1 r.2 <;> rfl
  have hA : Computable (fun p : ℕ × ℕ × ℕ =>
      not_isSchnorrRandom_iff_exists_series_A
        a f p.1 p.2.2 (p.2.1 + 6 + p.2.2)) :=
    computable_range_sum _ hterm _ hm
  have hpow : Computable (fun s : ℕ => (2 : ℚ) ^ s) :=
    (computable_nat_to_rat.comp comp_pow).of_eq (fun s => by simp)
  have hlhs : Computable (fun p : ℕ × ℕ × ℕ =>
      q (p.1, p.2.1 + 6) * (2 : ℚ) ^ (p.2.1 + 6 + p.2.2)) :=
    computable₂_ratMul.comp (hq_comp.comp (Computable.pair Computable.fst hk))
      (hpow.comp hR)
  have hrhs : Computable (fun p : ℕ × ℕ × ℕ =>
      (not_isSchnorrRandom_iff_exists_series_A
        a f p.1 p.2.2 (p.2.1 + 6 + p.2.2) : ℚ) + (2 : ℚ) ^ (p.2.2 + 3)) :=
    computable₂_ratAdd.comp (computable_nat_to_rat.comp hA)
      (hpow.comp (Primrec.nat_add.to_comp.comp hm (Computable.const 3)))
  exact (computable₂_ratLt.comp hlhs hrhs).of_eq (fun _ => rfl)

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_series_moduli`:
explicit test. -/
private lemma not_isSchnorrRandom_iff_exists_series_test
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π)
    (f : ℕ → ℕ → Option BitString) (hf_comp : Computable₂ f)
    (hf_bound : ∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n)
    (hf_real : IsComputableRealSeq fun n => (∑' i, coverMass π (f n i)).toReal) :
    ∃ T : ℕ → ℕ → ℕ → Bool,
      Computable (fun p : ℕ × ℕ × ℕ => T p.1 p.2.1 p.2.2) ∧
      (∀ n k m, T n k m = true → ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 2)) ∧
      (∀ n k m, ∑' i, coverMass π (f n (m + i)) ≤ dyadicValue 1 (k + 4) → T n k m = true) := by
  obtain ⟨q, hq_comp, hq_bound⟩ := hf_real
  obtain ⟨a, ha_comp, ha_bound⟩ := hπ
  let T := not_isSchnorrRandom_iff_exists_series_T q a f
  use T
  refine ⟨?_, ?_, ?_⟩
  · exact not_isSchnorrRandom_iff_exists_series_comp q
      hq_comp a ha_comp f hf_comp
  · intro n k m hT
    exact not_isSchnorrRandom_iff_exists_series_sound a
        ha_bound f hf_bound q hq_bound n k m hT
  · intro n k m h_tail
    exact not_isSchnorrRandom_iff_exists_series_complete a
        ha_bound f hf_bound q hq_bound n k m h_tail

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_series_mp`: moduli. -/
lemma not_isSchnorrRandom_iff_exists_series_moduli {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π)
    (f : ℕ → ℕ → Option BitString) (g : ℕ → ℕ → BitString)
    (hf_comp : Computable₂ f)
    (hf_bound : ∀ n, ∑' i, coverMass π (f n i) ≤ dyadicValue 1 n)
    (hf_real : IsComputableRealSeq fun n => (∑' i, coverMass π (f n i)).toReal)
    (hg_eq : ∀ n i s, f n i = some s → g n i = s)
    (hg_junk : ∀ n i, f n i = none → cantorMass π (g n i) ≤ 2 * dyadicValue 1 (n + i)) :
    ∃ M : ℕ → ℕ → ℕ, Computable₂ M ∧ ∀ n k, k + 3 ≤ M n k ∧
      ∑' i, cantorMass π (g n (M n k + i)) ≤ dyadicValue 1 k := by
  obtain ⟨T, hT_comp, hT_sound, hT_complete⟩ :=
      not_isSchnorrRandom_iff_exists_series_test hπ f hf_comp hf_bound
      hf_real
  have h_ex : ∀ p : ℕ × ℕ, ∃ j, T p.1 p.2 (p.2 + 3 + j) = true := by
    intro p
    obtain ⟨m, hm_ge, hm_bound⟩ :=
        not_isSchnorrRandom_iff_exists_series_small_tail f hf_bound p.1
        p.2
    use m - (p.2 + 3)
    have h_eq : p.2 + 3 + (m - (p.2 + 3)) = m := Nat.add_sub_of_le hm_ge
    rw [h_eq]
    exact hT_complete p.1 p.2 m hm_bound
  have h_add_1 : Computable (fun p : (ℕ × ℕ) × ℕ => p.1.2 + 3) :=
    Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp (Computable.snd.comp
        Computable.fst) (Computable.const 3)
  have h_add_2 : Computable (fun p : (ℕ × ℕ) × ℕ => p.1.2 + 3 + p.2) :=
    Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp h_add_1 Computable.snd
  
  have hp_tuple : Computable (fun p : (ℕ × ℕ) × ℕ => (p.1.1, (p.1.2, p.1.2 + 3 + p.2))) :=
    (Computable.fst.comp Computable.fst).pair ((Computable.snd.comp Computable.fst).pair h_add_2)
  have h_T_apply : Computable (fun p : (ℕ × ℕ) × ℕ => T p.1.1 p.1.2 (p.1.2 + 3 + p.2)) :=
    hT_comp.comp hp_tuple
    
  have hP : Computable (fun p : (ℕ × ℕ) × ℕ => decide (T p.1.1 p.1.2 (p.1.2 + 3 + p.2) = true)) :=
      by
    refine Computable.of_eq h_T_apply (fun p => ?_)
    cases T p.1.1 p.1.2 (p.1.2 + 3 + p.2) <;> rfl
  let M_find (p : ℕ × ℕ) := Nat.find (h_ex p)
  have h_find_comp : Computable M_find := Computable.natFind hP h_ex
  let M (n k : ℕ) := k + 3 + M_find (n, k)
  use M
  refine ⟨?_, ?_⟩
  · have h1 : Computable (fun p : ℕ × ℕ => p.2 + 3) :=
      Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp Computable.snd
          (Computable.const 3)
    exact Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp h1 h_find_comp
  · intro n k
    refine ⟨?_, ?_⟩
    · exact Nat.le_add_right (k + 3) (M_find (n, k))
    · have h_true : T n k (M n k) = true := by
        have h_M_eq : M n k = k + 3 + M_find (n, k) := rfl
        rw [h_M_eq]
        exact Nat.find_spec (h_ex (n, k))
      have h_tail := hT_sound n k (M n k) h_true
      exact not_isSchnorrRandom_iff_exists_series_tail_bound f g hg_eq
          hg_junk n k (M n k) (Nat.le_add_right _ _) h_tail

end Kolmogorov.FrequencyGames
