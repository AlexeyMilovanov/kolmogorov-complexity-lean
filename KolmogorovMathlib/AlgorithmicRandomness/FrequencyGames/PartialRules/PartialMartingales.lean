/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.PartialRules.MisesChurchDaley

/-!
# Partial Martingales

Partial martingales, i.e. partial computable functions `BitString →. ℚ` satisfying the
martingale equation wherever it makes sense, and the associated notion of partial-computable
randomness.

Main declarations:

* `exists_isMisesChurchDaleyRandom_plainK_le`: for a non-decreasing unbounded computable `f`
  there is a Mises-Church-Daley random sequence whose `n`-bit prefixes have plain complexity at
  most `f(n) log n + O(1)` (SUV Theorem 189, p. 289, due to Merkle);
* `IsPartialMartingale`, `PartialWins`, `IsPartialComputablyRandom`: partial martingales, their
  winning condition, and partial-computable randomness (SUV p. 290);
* `isMisesChurchDaleyRandom_of_isPartialComputablyRandom`: partial-computable randomness implies
  Mises-Church-Daley randomness;
* `exists_isPartialComputablyRandom_plainK_le`: the complexity bound of Merkle's theorem holds
  for a partial-computably random sequence;
* `isComputablyRandom_of_isPartialComputablyRandom`: partial-computable randomness implies
  computable randomness.

This formalizes the section of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity and
algorithmic randomness", on partial computable martingales and Mises-Church-Daley randomness.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

private structure pm_IsPartialMartingale (m : BitString →. ℚ)
    : Prop where
  nonneg : ∀ x, ∀ q ∈ m x, 0 ≤ q
  fair : ∀ x q q₀ q₁, q ∈ m x → q₀ ∈ m (x ++ [false]) → q₁ ∈ m (x ++ [true]) → q = (q₀ + q₁) / 2

private def pm_PartialWins (m : BitString →. ℚ)
    (w : CantorSeq) : Prop :=
  (∀ n, (m (cantorPrefix w n)).Dom) ∧
    ¬ BddAbove {r : ℝ | ∃ n, ∃ q ∈ m (cantorPrefix w n), (q : ℝ) = r}

private def pm_IsPartialComputablyRandom (w : CantorSeq) :
    Prop :=
  ∀ m : BitString →. ℚ, Partrec m → pm_IsPartialMartingale m
      → ¬ pm_PartialWins m w


/-- Step 1 of the proof of
`pm_of_random`:
A total computable rational martingale winning on every unbalanced sequence. -/
private def pm_unb_d
    (i : ℕ) : ℚ := (-1)^i * (1/2 : ℚ)^(i/2+1)
private def pm_unb_s
    (b : Bool) : ℚ := cond b 1 (-1)
private def pm_unb_B (i : ℕ) (x : List Bool) : ℚ :=
  ((x.drop i).map (fun b => 1 + pm_unb_d i * pm_unb_s b)).prod
private def pm_unb_M (x : List Bool) : ℚ :=
  ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x)).sum + (1/2 : ℚ)^x.length


/-- Step 1a of the proof of
`pm_computable_martingale_wins_unbalanced`:
Computability of M. -/
private lemma pm_comp :
  Computable pm_unb_M := by
  have step1_pow : Computable (fun k : ℕ => (1/2 : ℚ)^k) := by
    apply computable_of_num_den (N := fun _ => 1) (D := fun k => 2^k) (Computable.const 1)
        (Kolmogorov.comp_pow)
    · intro x; positivity
    · intro x; push_cast; exact one_div_pow (2:ℚ) x
  have step2_d : Computable
      pm_unb_d := by
    have H1 : Computable (fun i : ℕ => (1/2 : ℚ)^(i/2+1)) := Computable.comp step1_pow
        (Computable.comp (f := fun i => i + 1) (g := fun i => i / 2) (Primrec.nat_add.comp
        Primrec.id (Primrec.const 1)).to_comp (Primrec.nat_div.comp Primrec.id
        (Primrec.const 2)).to_comp)
    have H2 : Computable (fun i : ℕ => (-1 : ℚ)^i) := by
      have H2a := Computable.cond (c := fun i => decide (i % 2 = 0)) (f := fun i => (1:ℚ))
          (g := fun i => (-1:ℚ)) (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
          (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))).to_comp
          (Computable.const 1) (Computable.const (-1))
      refine H2a.of_eq (fun i => ?_)
      by_cases h : i % 2 = 0
      · simp only [h, decide_true, Bool.cond_true]
        have : Even i := ⟨i/2, by omega⟩
        exact this.neg_one_pow.symm
      · simp only [h, decide_false, Bool.cond_false]
        have : Odd i := ⟨i/2, by omega⟩
        exact this.neg_one_pow.symm
    apply (computable₂_ratMul.comp H2 H1).of_eq
    intro x; rfl
  have step3_s : Computable
      pm_unb_s := by
    have := Computable.cond (c := fun i => i) (f := fun i => (1:ℚ)) (g := fun i => (-1:ℚ))
        Computable.id (Computable.const 1) (Computable.const (-1))
    apply this.of_eq
    intro b
    rfl
  have step4_B : Computable (fun p : ℕ × List Bool =>
    pm_unb_B p.1 p.2) := by
    have H1 : Computable (fun p : ℕ × List Bool => p.2.drop p.1) :=
        (Primrec.list_drop (α := Bool)).comp Primrec.fst Primrec.snd |>.to_comp.of_eq (fun _ => rfl)
    have H2 : Computable₂ (fun (p : ℕ × List Bool) (sb : ℚ × Bool) =>
      sb.1 * (1 + pm_unb_d
      p.1 * pm_unb_s
      sb.2)) := by
      apply computable₂_ratMul.comp
      · exact (Computable.fst.comp (Computable.snd (α := ℕ × List Bool) (β := ℚ × Bool))).of_eq
          (fun _ => rfl)
      · apply computable₂_ratAdd.comp (Computable.const 1)
        apply computable₂_ratMul.comp
        · exact (Computable.comp step2_d (Computable.fst.comp (Computable.fst (α := ℕ × List Bool)
            (β := ℚ × Bool)))).of_eq (fun _ => rfl)
        · exact (Computable.comp step3_s (Computable.snd.comp (Computable.snd (α := ℕ × List Bool)
            (β := ℚ × Bool)))).of_eq (fun _ => rfl)
    have H3 := Computable.list_foldl (l := fun p : ℕ × List Bool => p.2.drop p.1)
        (g := fun p => 1) (h := fun p sb => sb.1 * (1 + pm_unb_d p.1 * pm_unb_s sb.2))
        H1 (Computable.const 1) H2
    apply H3.of_eq
    intro p
    dsimp [pm_unb_B]
    rw [List.prod_eq_foldl, List.foldl_map]
  have H1 : Computable (fun (x : List Bool) => List.range x.length) :=
      (Primrec.list_range.comp Primrec.list_length).to_comp
  have H2 : Computable₂ (fun (x : List Bool) (is : ℚ × ℕ) =>
    is.1 + (1/2 : ℚ)^(is.2+1) *
    pm_unb_B is.2 x) := by
    apply computable₂_ratAdd.comp
    · exact (Computable.fst.comp (Computable.snd (α := List Bool) (β := ℚ × ℕ))).of_eq
        (fun _ => rfl)
    · apply computable₂_ratMul.comp
      · have Hpow : Computable (fun (p : List Bool × ℚ × ℕ) => (1/2 : ℚ)^(p.2.2+1)) :=
          Computable.comp step1_pow (Computable.comp (f := fun i => i + 1) (g := fun p : List Bool ×
          ℚ × ℕ => p.2.2) (Primrec.nat_add.comp Primrec.id (Primrec.const 1)).to_comp
                     (Computable.snd.comp (Computable.snd (α := List Bool) (β := ℚ × ℕ))))
        exact Hpow.of_eq (fun _ => rfl)
      · have H_B : Computable (fun (p : List Bool × ℚ × ℕ) => pm_unb_B p.2.2 p.1) := by
          have H_B1 : Computable (fun (p : List Bool × ℚ × ℕ) => (p.2.2, p.1)) :=
              (Computable.pair (Computable.snd.comp (Computable.snd (α := List Bool) (β := ℚ × ℕ)))
              (Computable.fst (α := List Bool) (β := ℚ × ℕ))).of_eq (fun _ => rfl)
          exact (Computable.comp (f := fun p : ℕ × List Bool => pm_unb_B p.1 p.2)
              step4_B H_B1).of_eq (fun _ => rfl)
        exact H_B.of_eq (fun _ => rfl)
  have H3 := Computable.list_foldl (l := fun x : List Bool => List.range x.length)
      (g := fun x => 0) (h := fun x is => is.1 + (1/2 : ℚ)^(is.2+1) * pm_unb_B is.2 x)
      H1 (Computable.const 0) H2
  apply (computable₂_ratAdd.comp H3 (Computable.comp step1_pow (Primrec.list_length.to_comp))).of_eq
  intro x
  dsimp [pm_unb_M]
  congr 1
  rw [List.sum_eq_foldl, List.foldl_map]


private lemma pm_mart_d_abs_le_half (i : ℕ) :
    |pm_unb_d i| ≤ 1/2 :=
    by
  dsimp [pm_unb_d]
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have H : (1/2 : ℚ)^(i/2+1) ≤ 1/2 := by
    calc
      (1/2 : ℚ)^(i/2+1) ≤ (1/2 : ℚ)^1 := by
        apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
        omega
      _ = 1/2 := by norm_num
  have H2 : |(1/2 : ℚ)^(i/2+1)| = (1/2 : ℚ)^(i/2+1) := by
    apply abs_of_nonneg
    positivity
  rw [H2]
  exact H

private lemma pm_mart_factor_nonneg (i : ℕ) (b : Bool) : 0 ≤
    1 + pm_unb_d i *
    pm_unb_s b := by
  have hd := pm_mart_d_abs_le_half i
  have hs : |pm_unb_s b| =
      1 := by cases b <;> rfl
  have : |pm_unb_d i *
      pm_unb_s b| ≤ 1/2 :=
      by
    rw [abs_mul, hs, mul_one]
    exact hd
  have H2: - (1/2 : ℚ) ≤
      pm_unb_d i *
      pm_unb_s b :=
      neg_le_of_abs_le this
  linarith

private lemma pm_mart_B_nonneg (i : ℕ) (x : List Bool) : 0 ≤
    pm_unb_B i x := by
  dsimp [pm_unb_B]
  apply List.prod_nonneg
  intro y hy
  rw [List.mem_map] at hy
  rcases hy with ⟨b, _, rfl⟩
  exact pm_mart_factor_nonneg i b

private lemma pm_mart_M_nonneg (x : List Bool) : 0 ≤
    pm_unb_M x := by
  dsimp [pm_unb_M]
  apply add_nonneg
  · apply List.sum_nonneg
    intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨i, _, rfl⟩
    apply mul_nonneg
    · positivity
    · exact pm_mart_B_nonneg i x
  · positivity

private lemma pm_mart_B_append (i : ℕ) (x : List Bool)
    (b : Bool) (hi : i ≤ x.length) :
    pm_unb_B i (x ++ [b]) =
    pm_unb_B i x *
    (1 + pm_unb_d i *
    pm_unb_s b) := by
  dsimp [pm_unb_B]
  rw [List.drop_append_of_le_length hi]
  rw [List.map_append, List.prod_append]
  simp

private lemma pm_mart_B_length_append (x : List Bool)
    (b : Bool) : pm_unb_B
    x.length (x ++ [b]) = 1 +
    pm_unb_d x.length *
    pm_unb_s b := by
  dsimp [pm_unb_B]
  have : (x ++ [b]).drop x.length = [b] := by
    rw [List.drop_append_of_le_length (le_refl _)]
    rw [List.drop_length, List.nil_append]
  rw [this]
  simp

private lemma pm_mart_M_append (x : List Bool) (b : Bool) :
    pm_unb_M (x ++ [b]) =
      ((List.range x.length).map
        (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s b))).sum +
      (1/2 : ℚ)^(x.length+1) * (1 + pm_unb_d x.length * pm_unb_s b) +
      (1/2 : ℚ)^(x.length+1) := by
  dsimp [pm_unb_M]
  rw [List.length_append, List.length_singleton]
  have h1 : List.range (x.length + 1) = List.range x.length ++ [x.length] := List.range_succ
  rw [h1]
  rw [List.map_append]
  rw [List.sum_append]
  simp only [List.map_singleton, List.sum_singleton]
  have H1 : (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) * pm_unb_B i (x ++ [b]))
        (List.range x.length)).sum =
      (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s b))
        (List.range x.length)).sum := by
    have : (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) * pm_unb_B i (x ++ [b]))
        (List.range x.length)) =
        (List.map (fun i => (1 / 2 : ℚ) ^ (i + 1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s b))
        (List.range x.length)) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [pm_mart_B_append i x b (le_of_lt hi)]
      ring
    rw [this]
  rw [H1]
  have H2 : (1 / 2 : ℚ) ^ (x.length + 1) *
      pm_unb_B x.length (x
      ++ [b]) = (1 / 2 : ℚ) ^ (x.length + 1) *
      (1 + pm_unb_d
      x.length * pm_unb_s
      b) := by
    rw [pm_mart_B_length_append]
  rw [H2]

/-- Step 1b of the proof of
`pm_computable_martingale_wins_unbalanced`:
Nonnegativity and fairness. -/
private lemma pm_mart :
  (∀ x, 0 ≤ pm_unb_M x) ∧
  (∀ x, pm_unb_M x =
      (pm_unb_M (x ++
      [false]) + pm_unb_M
      (x ++ [true])) / 2) := by
  constructor
  · exact pm_mart_M_nonneg
  · intro x
    have hf : pm_unb_s
        false = -1 := rfl
    have ht : pm_unb_s true
        = 1 := rfl
    have hsum : ((List.range x.length).map
          (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s false))).sum +
        ((List.range x.length).map
          (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s true))).sum =
        2 * ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x)).sum := by
      rw [← List.sum_map_add]
      have : (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s false) +
          (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s true)) =
          fun i => 2 * ((1/2 : ℚ)^(i+1) * pm_unb_B i x) := by
        funext i
        rw [hf, ht]
        ring
      rw [this]
      rw [List.sum_map_mul_left]
    have h2 : (1 / 2 : ℚ) ^ (x.length + 1) = (1 / 2 : ℚ) ^ x.length / 2 := by
      rw [pow_add, pow_one]
      ring
    have H3 : pm_unb_M
        (x ++ [false]) +
        pm_unb_M (x ++
        [true]) = 2 *
        pm_unb_M x := by
      rw [pm_mart_M_append x false,
          pm_mart_M_append x true]
      calc
        ((List.range x.length).map
          (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s false))).sum +
        (1/2 : ℚ)^(x.length+1) * (1 + pm_unb_d x.length * pm_unb_s false) +
        (1/2 : ℚ)^(x.length+1) +
        (((List.range x.length).map
          (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s true))).sum +
        (1/2 : ℚ)^(x.length+1) * (1 + pm_unb_d x.length * pm_unb_s true) +
        (1/2 : ℚ)^(x.length+1))
        _ = ((List.range x.length).map
              (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s false))).sum +
            ((List.range x.length).map
              (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x * (1 + pm_unb_d i * pm_unb_s true))).sum +
            (1/2 : ℚ)^(x.length+1) *
              ((1 + pm_unb_d x.length * pm_unb_s false) + (1 + pm_unb_d x.length * pm_unb_s true)) +
            2 * (1/2 : ℚ)^(x.length+1) := by ring
        _ = 2 * ((List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x)).sum +
            (1/2 : ℚ)^(x.length+1) * 2 + 2 * (1/2 : ℚ)^(x.length+1) := by
          rw [hsum]
          congr 2
          rw [hf, ht]
          ring
        _ = 2 * pm_unb_M
            x := by
          dsimp [pm_unb_M]
          rw [h2]
          ring
    linarith

/-- Step 1 of the proof of
`pm_wins`:
Nonconvergence of the frequency yields a fixed positive deviation toward ones or zeros infinitely
often. -/
private lemma pm_extraction (u : CantorSeq)
    (hu : ¬ HasLimitFreq (1/2) u) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
      ((∃ᶠ n : ℕ in Filter.atTop, (1/2 + ε) * n ≤ (List.count true (cantorPrefix u n) : ℝ)) ∨
       (∃ᶠ n : ℕ in Filter.atTop, (1/2 + ε) * n ≤ (n - List.count true (cantorPrefix u n) : ℝ))) :=
           by
  unfold HasLimitFreq at hu
  rw [Metric.tendsto_atTop] at hu
  push Not at hu
  obtain ⟨ε', hε', hex⟩ := hu
  refine ⟨min ε' (1/2), lt_min hε' (by norm_num), min_le_right _ _, ?_⟩
  by_contra hcon
  rw [not_or, Filter.not_frequently, Filter.not_frequently] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 h1
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 h2
  obtain ⟨n, hn, hdist⟩ := hex (max (max N1 N2) 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hf : ((freqOne u n : ℚ) : ℝ) = ((cantorPrefix u n).count true : ℝ) / n := by
    simp [freqOne]
  rw [Real.dist_eq, hf] at hdist
  have e1 := hN1 n hnN1
  have e2 := hN2 n hnN2
  have hmin : min ε' (1/2) ≤ ε' := min_le_left _ _
  have hcn : (((cantorPrefix u n).count true : ℕ) : ℝ) ≤ n := by
    have := List.count_le_length (a := true) (l := cantorPrefix u n)
    rw [cantorPrefix_length] at this
    exact_mod_cast this
  rcases le_abs'.1 hdist with h | h
  · -- c/n - 1/2 ≤ -ε'  : zeros dominate
    apply e2
    have h' : ((cantorPrefix u n).count true : ℝ) / n ≤ 1/2 - min ε' (1/2) := by linarith
    rw [div_le_iff₀ hnpos] at h'
    nlinarith
  · have h' : 1/2 + min ε' (1/2) ≤ ((cantorPrefix u n).count true : ℝ) / n := by linarith
    rw [le_div_iff₀ hnpos] at h'
    exact e1 h'

/-- Step 2 of the proof of
`pm_wins`:
Choose a positive dyadic stake at most half the frequency deviation. -/
private lemma pm_bettor {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ,
    (2 : ℝ)⁻¹ ^ (k + 1) ≤ ε / 2 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2:ℝ)⁻¹ < 1)
  exact ⟨k, le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)) hk.le⟩

/-- Step 3 of the proof of
`pm_wins`:
Each active bettor, multiplied by its positive account weight, is bounded by the mixture
capital. -/
private lemma pm_dom (x : List Bool) (i : ℕ)
    (hi : i < x.length) :
    (1/2 : ℚ)^(i+1) *
        pm_unb_B i x ≤
        pm_unb_M x := by
  unfold pm_unb_M
  have hmem : ((1/2 : ℚ)^(i+1) * pm_unb_B i x) ∈
      (List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hnn : ∀ a ∈ (List.range x.length).map (fun i => (1/2 : ℚ)^(i+1) * pm_unb_B i x),
      0 ≤ a := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact mul_nonneg (by positivity) (pm_mart_B_nonneg j x)
  have h1 := List.single_le_sum hnn _ hmem
  have h2 : (0:ℚ) ≤ (1/2)^x.length := by positivity
  linarith

/-- Step 4 of the proof of
`pm_wins`:
The counts of a bit and its complement add to the length. -/
private lemma pm_counts (l : List Bool) (b : Bool) : l.count
    b + l.count (!b) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a <;> cases b <;>
      simp only [Bool.not_true, Bool.not_false] at ih ⊢ <;>
      simp <;> omega

/-- Step 4 of the proof of
`pm_wins`:
For a bettor whose signed stake favours the bit β, express its capital as powers indexed by the
counts of β and its complement. -/
private lemma pm_prod_formula (i : ℕ) (β : Bool) (δ : ℝ)
    (hd : ((pm_unb_d i : ℚ)
        : ℝ) = if β then δ else -δ) (y : List Bool) :
    (((y.map (fun b => 1 + pm_unb_d i * pm_unb_s b)).prod : ℚ) : ℝ)
      = (1 + δ)^(y.count β) * (1 - δ)^(y.count (!β)) := by
  induction y with
  | nil => simp
  | cons b y ih =>
    rw [List.map_cons, List.prod_cons, Rat.cast_mul, ih, Rat.cast_add, Rat.cast_one, Rat.cast_mul]
    cases β
    · simp only [Bool.false_eq_true, ite_false] at hd
      cases b <;> simp [pm_unb_s, hd] <;> ring
    · simp only [ite_true] at hd
      cases b <;> simp [pm_unb_s, hd] <;> ring

/-- Step 4 of the proof of
`pm_wins`:
Deleting the first i bits loses at most a factor of 2^i for a bettor whose signed stake favours β.
-/
private lemma pm_one_bettor (x : List Bool) (i : ℕ)
    (β : Bool) (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ ≤ 1)
    (hd : ((pm_unb_d i : ℚ)
        : ℝ) = if β then δ else -δ) :
    (1 + δ)^(x.count β) * (1 - δ)^(x.count (!β)) ≤ 2^i * (pm_unb_B i x : ℝ) := by
  have hB : (pm_unb_B i x :
      ℝ) = (1 + δ)^((x.drop i).count β) * (1 - δ)^((x.drop i).count (!β)) := by
    unfold pm_unb_B; exact
        pm_prod_formula i β δ hd (x.drop i)
  rw [hB]
  have h1 : x.count β ≤ i + (x.drop i).count β := by
    have h0 : (x.take i ++ x.drop i).count β = (x.take i).count β + (x.drop i).count β :=
      List.count_append
    rw [List.take_append_drop] at h0
    have h2 : (x.take i).count β ≤ (x.take i).length := List.count_le_length
    have h3 : (x.take i).length ≤ i := List.length_take_le i x
    omega
  have h2 : (1 + δ)^(x.count β) ≤ 2^i * (1 + δ)^((x.drop i).count β) := by
    calc (1 + δ)^(x.count β) ≤ (1 + δ)^(i + (x.drop i).count β) :=
          pow_le_pow_right₀ (by linarith) h1
      _ = (1 + δ)^i * (1 + δ)^((x.drop i).count β) := pow_add _ _ _
      _ ≤ 2^i * (1 + δ)^((x.drop i).count β) := by
        gcongr
        linarith
  have h3 : (1 - δ)^(x.count (!β)) ≤ (1 - δ)^((x.drop i).count (!β)) :=
    pow_le_pow_of_le_one (by linarith) (by linarith) ((List.drop_sublist i x).count_le (!β))
  calc (1 + δ)^(x.count β) * (1 - δ)^(x.count (!β))
      ≤ (2^i * (1 + δ)^((x.drop i).count β)) * (1 - δ)^((x.drop i).count (!β)) := by
        apply mul_le_mul h2 h3 (pow_nonneg (by linarith) _) (by positivity)
    _ = 2^i * ((1 + δ)^((x.drop i).count β) * (1 - δ)^((x.drop i).count (!β))) := by ring

/-- Step 5 of the proof of
`pm_wins`:
A frequency deviation ε and a positive stake δ at most ε/2 give exponential growth, by lower bounds
on the logarithms of 1+δ and 1-δ. -/
private lemma pm_estimate (ε δ : ℝ) (hδ1 : 0 < δ)
    (hδ2 : δ ≤ ε / 2) (hε : ε ≤ 1 / 2)
    (c d : ℕ) (h_c_large : (1 / 2 + ε) * (c + d) ≤ c) :
    Real.exp (ε * δ * (c + d)) ≤ (1 + δ)^c * (1 - δ)^d := by
  have hδ : δ ≤ 1/4 := by linarith
  have hpos1 : 0 < 1 + δ := by linarith
  have hpos2 : 0 < 1 - δ := by linarith
  have h1 : δ - δ^2 ≤ Real.log (1 + δ) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos1
    have h' : δ - δ^2 ≤ 1 - (1 + δ)⁻¹ := by
      have e : 1 - (1 + δ)⁻¹ - (δ - δ^2) = δ^3 / (1 + δ) := by field_simp; ring
      have : 0 ≤ δ^3 / (1 + δ) := by positivity
      linarith
    linarith
  have h2 : -δ - 2 * δ^2 ≤ Real.log (1 - δ) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos2
    have h' : -δ - 2 * δ^2 ≤ 1 - (1 - δ)⁻¹ := by
      have e : 1 - (1 - δ)⁻¹ - (-δ - 2 * δ^2) = δ^2 * (1 - 2 * δ) / (1 - δ) := by
        field_simp; ring
      have : 0 ≤ δ^2 * (1 - 2 * δ) / (1 - δ) := by
        apply div_nonneg
        · apply mul_nonneg (by positivity); linarith
        · linarith
      linarith
    linarith
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ c + d := add_nonneg hc0 hd0
  have hlog : ε * δ * (c + d) ≤ Real.log ((1 + δ)^c * (1 - δ)^d) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have a1 : (c : ℝ) * (δ - δ^2) ≤ c * Real.log (1 + δ) := mul_le_mul_of_nonneg_left h1 hc0
    have a2 : (d : ℝ) * (-δ - 2 * δ^2) ≤ d * Real.log (1 - δ) :=
      mul_le_mul_of_nonneg_left h2 hd0
    have k1 : (c : ℝ) - d ≥ 2 * ε * (c + d) := by linarith
    nlinarith [mul_nonneg hδ1.le hn0, mul_nonneg hδ1.le (sub_nonneg.2 k1),
      mul_nonneg (mul_nonneg hδ1.le hδ1.le) hc0, mul_nonneg hδ1.le
          (mul_nonneg hn0 (sub_nonneg.2 hδ2))]
  calc Real.exp (ε * δ * (c + d)) ≤ Real.exp (Real.log ((1 + δ)^c * (1 - δ)^d)) :=
        Real.exp_le_exp.2 hlog
    _ = (1 + δ)^c * (1 - δ)^d := Real.exp_log (by positivity)

/-- Step 6 of the proof of
`pm_wins`:
Combine the mixture bound, the loss from the first i bits, and the exponential estimate at every
sufficiently long biased prefix. -/
private lemma pm_M_lower (x : List Bool) (i : ℕ) (β : Bool)
    (δ ε : ℝ) (hδ1 : 0 < δ) (hδ2 : δ ≤ ε / 2)
    (hε : ε ≤ 1 / 2)
        (hd : ((pm_unb_d i
        : ℚ) : ℝ) = if β then δ else -δ)
    (hi : i < x.length) (hx : (1 / 2 + ε) * x.length ≤ (x.count β : ℝ)) :
    (1/2 : ℝ)^(2*i+1) * Real.exp (ε * δ * x.length) ≤
        (pm_unb_M x : ℝ) :=
        by
  have h3 : ((1/2 : ℝ))^(i+1) *
      (pm_unb_B i x : ℝ) ≤
      (pm_unb_M x : ℝ) :=
      by
    have := (Rat.cast_le (K := ℝ)).2 (pm_dom x i hi)
    push_cast at this
    exact this
  have hcount : (x.length : ℝ) = x.count β + x.count (!β) := by
    exact_mod_cast (pm_counts x β).symm
  have hδ1' : δ ≤ 1 := by linarith
  have h4 := pm_one_bettor x i β δ hδ1 hδ1' hd
  have h5 := pm_estimate ε δ hδ1 hδ2 hε (x.count β) (x.count (!β))
      (by rw [← hcount]; exact hx)
  rw [← hcount] at h5
  have hpow : (1/2 : ℝ)^(2*i+1) * 2^i = (1/2)^(i+1) := by
    rw [show 2*i+1 = (i+1) + i by ring, pow_add, mul_assoc, ← mul_pow]
    norm_num
  calc (1/2 : ℝ)^(2*i+1) * Real.exp (ε * δ * x.length)
      ≤ (1/2 : ℝ)^(2*i+1) *
          (2^i * (pm_unb_B
          i x : ℝ)) :=
        mul_le_mul_of_nonneg_left (h5.trans h4) (by positivity)
    _ = (1/2)^(i+1) *
        (pm_unb_B i x : ℝ)
        := by rw [← mul_assoc, hpow]
    _ ≤ pm_unb_M x := h3

/-- Step 7 of the proof of
`pm_wins`:
Infinitely many biased prefixes make the capital of a fixed suitable bettor, and hence the mixture,
unbounded. -/
private lemma pm_unbounded_of_bettor (u : CantorSeq) (i : ℕ)
    (β : Bool) (δ ε : ℝ) (hδ1 : 0 < δ)
    (hδ2 : δ ≤ ε / 2) (hε : ε ≤ 1 / 2) (hd :
        ((pm_unb_d i : ℚ) :
        ℝ) = if β then δ else -δ)
    (hfreq : ∃ᶠ n : ℕ in Filter.atTop,
      (1 / 2 + ε) * n ≤ (((cantorPrefix u n).count β : ℕ) : ℝ)) :
    ¬ BddAbove (Set.range fun n => ((pm_unb_M (cantorPrefix u n) : ℚ) : ℝ)) := by
  rintro ⟨C, hC⟩
  have hε1 : 0 < ε := by linarith
  have hεδ : 0 < ε * δ := mul_pos hε1 hδ1
  obtain ⟨N, hN⟩ := exists_nat_gt (((|C| + 1) * 2^(2*i+1)) / (ε * δ))
  obtain ⟨n, hn, hn1⟩ := (Filter.frequently_atTop.1 hfreq) (max N (i+1))
  have hniN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnii : i + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hM := pm_M_lower (cantorPrefix u n) i β δ ε hδ1 hδ2 hε
      hd
    (by rw [cantorPrefix_length]; omega) (by rw [cantorPrefix_length]; exact hn1)
  rw [cantorPrefix_length] at hM
  have hMC : ((pm_unb_M
      (cantorPrefix u n) : ℚ) : ℝ) ≤ C := hC ⟨n, rfl⟩
  have hP : (0:ℝ) < 2^(2*i+1) := by positivity
  have hq : (1/2 : ℝ)^(2*i+1) * 2^(2*i+1) = 1 := by rw [← mul_pow]; norm_num
  have hbig : (|C| + 1) * 2^(2*i+1) < ε * δ * N := by
    have := (div_lt_iff₀ hεδ).1 hN
    linarith
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hniN
  have h1 : ε * δ * N ≤ ε * δ * n := mul_le_mul_of_nonneg_left hNn hεδ.le
  have hexp : ε * δ * n + 1 ≤ Real.exp (ε * δ * n) := by
    linarith [Real.add_one_le_exp (ε * δ * n)]
  have h2 : (1/2:ℝ)^(2*i+1) * (ε * δ * n + 1) ≤ C :=
    calc (1/2:ℝ)^(2*i+1) * (ε * δ * n + 1)
        ≤ (1/2:ℝ)^(2*i+1) * Real.exp (ε * δ * n) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ ((pm_unb_M
          (cantorPrefix u n) : ℚ) : ℝ) := hM
      _ ≤ C := hMC
  have h3 : ε * δ * n + 1 ≤ 2^(2*i+1) * C := by
    have := mul_le_mul_of_nonneg_left h2 hP.le
    calc ε * δ * n + 1 = 2^(2*i+1) * ((1/2:ℝ)^(2*i+1) * (ε * δ * n + 1)) := by
          rw [← mul_assoc, mul_comm (2^(2*i+1) : ℝ), hq, one_mul]
      _ ≤ 2^(2*i+1) * C := this
  have h4 : (2:ℝ)^(2*i+1) * C ≤ 2^(2*i+1) * |C| :=
    mul_le_mul_of_nonneg_left (le_abs_self C) hP.le
  nlinarith [hbig, h1, h3, h4, hP]

/-- Step 8 of the proof of
`pm_wins`:
Select the even bettor favouring ones or the odd bettor favouring zeros, according to the recurring
deviation. -/
private lemma pm_conclusion (u : CantorSeq) (ε : ℝ)
    (hε1 : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (h_freq :
      (∃ᶠ n : ℕ in Filter.atTop,
        (1 / 2 + ε) * n ≤ (List.count true (cantorPrefix u n) : ℝ)) ∨
      (∃ᶠ n : ℕ in Filter.atTop,
        (1 / 2 + ε) * n ≤ (n - List.count true (cantorPrefix u n) : ℝ))) :
    ¬ BddAbove (Set.range fun n => ((pm_unb_M (cantorPrefix u n) : ℚ) : ℝ)) := by
  obtain ⟨k, hk⟩ := pm_bettor hε1
  have hδ1 : 0 < (2:ℝ)⁻¹ ^ (k+1) := by positivity
  rcases h_freq with h | h
  · refine pm_unbounded_of_bettor u (2*k) true
      ((2:ℝ)⁻¹ ^ (k+1)) ε hδ1 hk hε2 ?_ h
    have e : pm_unb_d (2*k)
        = (1/2 : ℚ)^(k+1) := by
      unfold pm_unb_d
      have h1 : (2*k)/2 = k := by omega
      rw [h1, pow_mul]; simp
    rw [e]; simp
  · refine pm_unbounded_of_bettor u (2*k+1) false
      ((2:ℝ)⁻¹ ^ (k+1)) ε hδ1 hk hε2 ?_ ?_
    · have e : pm_unb_d
        (2*k+1) = -(1/2 : ℚ)^(k+1) := by
        unfold pm_unb_d
        have h1 : (2*k+1)/2 = k := by omega
        rw [h1, pow_succ, pow_mul]; simp
      rw [e]; simp
    · refine h.mono (fun n hn => ?_)
      have h0 : (cantorPrefix u n).count true + (cantorPrefix u n).count false
          = (cantorPrefix u n).length := pm_counts
              (cantorPrefix u n) true
      rw [cantorPrefix_length] at h0
      have h0' : (((cantorPrefix u n).count true : ℕ) : ℝ) + (((cantorPrefix u n).count false : ℕ) :
          ℝ) = n := by
        exact_mod_cast h0
      linarith

/-- Step 1c of the proof of
`pm_computable_martingale_wins_unbalanced`:
Winning estimate. -/
private lemma pm_wins :
  ∀ u, ¬ HasLimitFreq (1/2) u →
    ¬ BddAbove (Set.range fun n => ((pm_unb_M (cantorPrefix u n) : ℚ) : ℝ)) := by
  intro u hu
  obtain ⟨ε, hε1, hε2, h_freq⟩ := pm_extraction u hu
  exact pm_conclusion u ε hε1 hε2 h_freq

/-- Step 1 of the proofs of `pm_of_random` and
`isMisesChurchDaleyRandom_of_isPartialComputablyRandom`: a total computable rational martingale
winning on every unbalanced sequence. -/
private lemma pm_computable_martingale_wins_unbalanced :
  ∃ M : BitString → ℚ,
    Computable M ∧
    (∀ x, 0 ≤ M x) ∧
    (∀ x, M x = (M (x ++ [false]) + M (x ++ [true])) / 2) ∧
    ∀ u, ¬ HasLimitFreq (1/2) u →
      ¬ BddAbove (Set.range fun n => ((M (cantorPrefix u n) : ℚ) : ℝ))
        := by
  refine ⟨pm_unb_M,
          pm_comp,
          pm_mart.1,
          pm_mart.2,
          pm_wins⟩

open Classical Kolmogorov Kolmogorov.FrequencyGames in
private def pm_rule_loop
    (r : BitString →. Bool) (x : BitString) : ℕ → Part BitString
  | 0 => Part.some []
  | k + 1 => (pm_rule_loop r x
               k).bind fun s =>
      (r (x.take k)).map fun b => s ++ cond b [x.getD k false] []

open Classical Kolmogorov Kolmogorov.FrequencyGames in
private def pm_rule_m
    (r : BitString →. Bool) (M : BitString → ℚ) (x : BitString) : Part ℚ :=
  (r x).bind fun _ =>
    (pm_rule_loop r x
    x.length).map M

/-- Step 1 of the proof of
`pm_partialMartingaleOfRule_partrec`:
The partial martingale is partial recursive. -/
private lemma pm_partrec
    {r : BitString →. Bool} (hr : Partrec r)
    {M : BitString → ℚ} (hM_comp : Computable M) :
    Partrec (pm_rule_m r M) := by
  have h_step : Partrec₂ (fun (x : BitString) (p : ℕ × BitString) =>
      (r (x.take p.1)).map fun b => p.2 ++ cond b [x.getD p.1 false] []) := by
    apply Partrec.map
    · exact hr.comp (Primrec.list_take.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).to_comp
    · have h1 : Primrec₂ fun (p : (BitString × ℕ × BitString)) (b : Bool) =>
        p.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      have h2 : Primrec₂ fun (p : (BitString × ℕ × BitString)) (b : Bool) =>
        cond b [p.1.getD p.2.1 false] [] :=
        Primrec.cond (Primrec.snd)
          (Primrec.list_cons.comp (Primrec.list_getD false |>.comp (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const []))
          (Primrec.const [])
      exact (Primrec.list_append.comp h1 h2).to_comp
  have h_init : Partrec (fun _x : BitString => (Part.some [] : Part BitString)) :=
    Computable.ofOption (Computable.const (some []))
  have h_loop : Partrec (fun x : BitString =>
    pm_rule_loop r x x.length) :=
    by
    have H := @Partrec.nat_rec BitString BitString _ _ (fun x => x.length) _ _
        Computable.list_length h_init h_step
    exact H.of_eq <| fun x => by
      have h_ind : ∀ k, (Nat.rec (motive := fun _ => Part BitString) (Part.some [])
          (fun y IH => IH.bind fun a => Part.map
            (fun b => a ++ bif b then [List.getD x y false] else []) (r (List.take y x))) k) =
          pm_rule_loop r x k := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          dsimp only [pm_rule_loop, Nat.rec]
          rw [ih]
      exact h_ind x.length
  have h_loop_map : Partrec (fun x : BitString =>
    (pm_rule_loop r x
    x.length).map M) :=
    Partrec.map h_loop (hM_comp.comp Computable.snd)
  exact (Partrec.bind hr (h_loop_map.comp Computable.fst).to₂).of_eq <| fun x => by rfl

/-- Step 2 of the proof of
`pm_partialMartingaleOfRule_partrec`:
Domain of the loop. -/
private lemma pm_loop_dom
    (r : BitString →. Bool) (x : BitString) (k : ℕ) :
    (pm_rule_loop r x k).Dom ↔
        ∀ j < k, (r (x.take j)).Dom := by
  induction k with
  | zero => simp [pm_rule_loop]
  | succ k ih =>
    change ((pm_rule_loop r x
        k).bind fun s => (r (x.take k)).map fun b => s ++ cond b [x.getD k false] []).Dom ↔ ∀ j <
                                                       k + 1, (r (x.take j)).Dom
    simp only [Part.bind_dom, Part.map, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact h1 j hj'
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)⟩

/-- Step 3 of the proof of
`pm_partialMartingaleOfRule_partrec`:
Value of the loop. -/
private lemma pm_loop_val
    (r : BitString →. Bool) (x : BitString) (k : ℕ) (hk : k ≤ x.length) :
    ∀ q ∈ pm_rule_loop r x k, q =
        selectedBits (partialRuleSet r) (x.take k) := by
  classical
  induction k with
  | zero =>
    intro q hq
    have h : q = [] := Part.mem_some_iff.mp hq
    simp [h, selectedBits, selectedAux]
  | succ k ih =>
    intro q hq
    change q ∈ (pm_rule_loop r x
        k).bind
      (fun s => (r (x.take k)).map fun b => s ++ cond b [x.getD k false] []) at hq
    obtain ⟨s, hs, hmap⟩ := Part.mem_bind_iff.mp hq
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hmap
    rw [ih (by omega) s hs]
    have hr_dom : ∀ j < k, (r (x.take j)).Dom :=
      (pm_loop_dom r x k).mp hs.1
    have hdom : ∀ y, y <+: x.take k → (r y).Dom := by
      intro y hy
      have hy_eq : y = (x.take k).take y.length := List.prefix_iff_eq_take.mp hy
      have hy_le : y.length ≤ k := hy.length_le.trans (List.length_take_le k x)
      rw [hy_eq, List.take_take, Nat.min_eq_left hy_le]
      rcases lt_or_eq_of_le hy_le with hj | hj
      · exact hr_dom y.length hj
      · rw [hj]
        exact hb.1
    have hmem : x.take k ∈ partialRuleSet r ↔ b = true := by
      constructor
      · intro h
        exact Part.mem_unique hb h.2
      · intro h
        exact ⟨hdom, h ▸ hb⟩
    have htake : x.take (k + 1) = x.take k ++ [x.getD k false] := by
      have hk_lt : k < x.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt, Option.toList_some,
        List.getD_eq_getElem x false hk_lt]
    rw [htake, selectedBits_append_singleton, hmem]
    cases b <;> simp

/-- Step 4 of the proof of
`pm_partialMartingaleOfRule_partrec`:
Domain of the partial martingale. -/
private lemma pm_rule_dom
    (r : BitString →. Bool) (M : BitString → ℚ) (x : BitString) :
    (pm_rule_m r M x).Dom ↔ ∀ y,
        y <+: x → (r y).Dom := by
  dsimp [pm_rule_m]
  rw [Part.bind_dom]
  have h_map_dom (f : BitString → ℚ) (p : Part BitString) : (p.map f).Dom ↔ p.Dom := Iff.rfl
  simp only [h_map_dom, pm_loop_dom]
  constructor
  · rintro ⟨hx, hloop⟩ y hy
    have hy2 : y = x.take y.length := List.prefix_iff_eq_take.mp hy
    rw [hy2]
    rcases lt_trichotomy y.length x.length with h | h | h
    · exact hloop y.length h
    · rw [h, List.take_length]
      exact hx
    · rw [List.take_of_length_le (le_of_lt h)]
      exact hx
  · intro h
    refine ⟨?_, ?_⟩
    · exact h x List.prefix_rfl
    · intro j hj
      exact h (x.take j) (List.take_prefix j x)

/-- Step 5 of the proof of
`pm_partialMartingaleOfRule_partrec`:
Value of the partial martingale. -/
private lemma pm_val
    (r : BitString →. Bool) (M : BitString → ℚ) (x : BitString) :
    ∀ q ∈ pm_rule_m r M x,
      (pm_rule_m r M x).Dom ∧ q =
          M (selectedBits (partialRuleSet r) x) := by
  intro q hq
  constructor
  · exact Part.dom_iff_mem.mpr ⟨q, hq⟩
  · dsimp [pm_rule_m] at hq
    rcases Part.mem_bind_iff.mp hq with ⟨b, _, hmap⟩
    rcases (Part.mem_map_iff _).mp hmap with ⟨s, hs, rfl⟩
    have h_loop := pm_loop_val r x x.length le_rfl s hs
    rw [h_loop, List.take_length]

/-- Step 6 of the proof of
`pm_partialMartingaleOfRule_partrec`:
The partial martingale property. -/
private lemma pm_martingale
    (r : BitString →. Bool)
    {M : BitString → ℚ}
    (hM_nonneg : ∀ x, 0 ≤ M x)
    (hM_fair : ∀ x, M x = (M (x ++ [false]) + M (x ++ [true])) / 2) :
    pm_IsPartialMartingale (pm_rule_m r M) := by
  constructor
  · intro x q hq
    have hval := pm_val r M x q hq
    rw [hval.2]
    exact hM_nonneg _
  · intro x q q0 q1 hq hq0 hq1
    have hval_q := pm_val r M x q hq
    have hval_q0 := pm_val r M (x ++ [false]) q0 hq0
    have hval_q1 := pm_val r M (x ++ [true]) q1 hq1
    rw [hval_q.2, hval_q0.2, hval_q1.2]
    open Classical Kolmogorov in
    rw [selectedBits_append_singleton (partialRuleSet r) x false, selectedBits_append_singleton
        (partialRuleSet r) x true]
    by_cases hx : x ∈ partialRuleSet r
    · have h1 : (if x ∈ partialRuleSet r then [false] else []) = [false] := ite_eq_left hx
      have h2 : (if x ∈ partialRuleSet r then [true] else []) = [true] := ite_eq_left hx
      rw [h1, h2]
      exact hM_fair (selectedBits (partialRuleSet r) x)
    · have h1 : (if x ∈ partialRuleSet r then [false] else []) = [] := ite_eq_right hx
      have h2 : (if x ∈ partialRuleSet r then [true] else []) = [] := ite_eq_right hx
      rw [h1, h2]
      simp only [List.append_nil]
      ring

/-- Step 2 of the proof of
`pm_of_random`:
Converting a partial rule and a total rational martingale into a partial martingale. -/
private lemma pm_partialMartingaleOfRule_partrec
    {r : BitString →. Bool} (hr : Partrec r)
    {M : BitString → ℚ} (hM_comp : Computable M)
    (hM_nonneg : ∀ x, 0 ≤ M x)
    (hM_fair : ∀ x, M x = (M (x ++ [false]) + M (x ++ [true])) / 2) :
    ∃ m : BitString →. ℚ, Partrec m ∧ pm_IsPartialMartingale
        m ∧
      (∀ x, (m x).Dom ↔ (∀ y, y <+: x → (r y).Dom)) ∧
      (∀ x q, q ∈ m x → (m x).Dom ∧ q = M (selectedBits (partialRuleSet r) x)) := by
  use pm_rule_m r M
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pm_partrec hr hM_comp
  · exact pm_martingale r hM_nonneg hM_fair
  · exact pm_rule_dom r M
  · exact pm_val r M


/-- Step 1 of the proof of
`pm_partialWins`:
The length of the selected chain is surjective. -/
private lemma pm_lengths
    {r : BitString →. Bool} {w u : CantorSeq}
    (h_sel : selectStream (partialRuleSet r) w = .infinite u) :
    ∀ k : ℕ, ∃ t : ℕ, (selectChain (partialRuleSet r) w t).length = k := by
  intro k
  have hT := isStreamPrefixSet_chainPrefixSet (selectChain_prefix (partialRuleSet r) w)
  have h_iff := BitStream.finite_le_ofPrefixSet_iff hT (cantorPrefix u k)
  have h_sel' : BitStream.ofPrefixSet _ hT = .infinite u := h_sel
  rw [h_sel'] at h_iff
  have h_le : BitStream.finite (cantorPrefix u k) ≤ .infinite u :=
      (isCantorPrefix_iff_cantorPrefix_eq (cantorPrefix u k) u).mpr (by simp)
  have h_mem : cantorPrefix u k ∈ chainPrefixSet (selectChain (partialRuleSet r) w) := h_iff.mp h_le
  have ⟨t, ht⟩ := h_mem
  have h_t_le : k ≤ (selectChain (partialRuleSet r) w t).length := by
    have h_len := ht.length_le
    simp only [cantorPrefix_length] at h_len
    exact h_len
  clear h_iff h_sel' h_le h_mem ht
  induction t with
  | zero =>
    use 0
    have : k ≤ 0 := by
      have h0 : (selectChain (partialRuleSet r) w 0).length = 0 := by
        simp [selectChain, selectedBits, selectedAux, cantorPrefix]
      rw [h0] at h_t_le
      exact h_t_le
    have hk : k = 0 := Nat.eq_zero_of_le_zero this
    rw [hk]
    simp [selectChain, selectedBits, selectedAux, cantorPrefix]
  | succ t ih =>
    by_cases hk : k ≤ (selectChain (partialRuleSet r) w t).length
    · exact ih hk
    · use t + 1
      have hk2 : (selectChain (partialRuleSet r) w t).length < k := not_le.mp hk
      have h_succ : (selectChain (partialRuleSet r) w (t + 1)).length ≤
          (selectChain (partialRuleSet r) w t).length + 1 := by
        unfold selectChain
        rw [cantorPrefix_succ, selectedBits_append_singleton]
        simp only [List.length_append]
        split_ifs
        · simp
        · simp
      linarith

/-- Step 2 of the proof of
`pm_partialWins`:
The selection condition happens infinitely often. -/
private lemma pm_frequently
    {r : BitString →. Bool} {w u : CantorSeq}
    (h_sel : selectStream (partialRuleSet r) w = .infinite u) :
    ∀ n : ℕ, ∃ t ≥ n, cantorPrefix w t ∈ partialRuleSet r := by
  intro n
  by_contra h
  push Not at h
  have ht_len : ∀ t ≥ n, (selectChain (partialRuleSet r) w t).length =
      (selectChain (partialRuleSet r) w n).length := by
    intro t ht
    induction ht with
    | refl => rfl
    | @step t' ht' ih =>
      have h_not_mem := h t' ht'
      unfold selectChain
      rw [cantorPrefix_succ, selectedBits_append_singleton]
      simp only [List.length_append]
      have h_not : ¬ cantorPrefix w t' ∈ partialRuleSet r := h_not_mem
      simp only [h_not, ite_false, List.length_nil, add_zero]
      unfold selectChain at ih
      rw [ih]
  have h_len_bound : ∀ t, (selectChain (partialRuleSet r) w t).length ≤
      (selectChain (partialRuleSet r) w n).length := by
    intro t
    by_cases ht : n ≤ t
    · rw [ht_len t ht]
    · push Not at ht
      have ht_le_n : t ≤ n := by omega
      have ht_prefix : cantorPrefix w t <+: cantorPrefix w n := cantorPrefix_mono w ht_le_n
      have hc_prefix := selectedBits_prefix (partialRuleSet r) ht_prefix
      exact hc_prefix.length_le
  have hk := pm_lengths h_sel
      ((selectChain (partialRuleSet r) w n).length + 1)
  obtain ⟨t, ht_eq⟩ := hk
  have h_bound := h_len_bound t
  omega

/-- Step 3 of the proof of
`pm_partialWins`:
The martingale is defined on all prefixes. -/
private lemma pm_partialWins_dom
    {r : BitString →. Bool} {m : BitString →. ℚ} {w u : CantorSeq}
    (hm_dom : ∀ x, (m x).Dom ↔ (∀ y, y <+: x → (r y).Dom))
    (h_sel : selectStream (partialRuleSet r) w = .infinite u) :
    ∀ n : ℕ, (m (cantorPrefix w n)).Dom := by
  intro n
  rw [hm_dom]
  intro y hy
  obtain ⟨t, ht_le, ht_mem⟩ := pm_frequently h_sel n
  have h_t_dom : ∀ y, y <+: cantorPrefix w t → (r y).Dom := ht_mem.1
  apply h_t_dom
  have h1 : cantorPrefix w n <+: cantorPrefix w t := cantorPrefix_mono w ht_le
  exact List.IsPrefix.trans hy h1

/-- Step 4 of the proof of
`pm_partialWins`:
The selected chain is a prefix of the selected infinite sequence. -/
private lemma pm_prefix
    {r : BitString →. Bool} {w u : CantorSeq}
    (h_sel : selectStream (partialRuleSet r) w = .infinite u) :
    ∀ t : ℕ, IsCantorPrefix (selectChain (partialRuleSet r) w t) u := by
  intro t
  have hc := selectChain_prefix (partialRuleSet r) w
  have h_in : selectChain (partialRuleSet r) w t ∈ chainPrefixSet (selectChain (partialRuleSet r) w)
      := ⟨t, List.prefix_rfl⟩
  have h_le := (BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) _).mpr
      h_in
  have h_eq : selectStream (partialRuleSet r) w = BitStream.ofPrefixSet
      (chainPrefixSet (selectChain (partialRuleSet r) w)) (isStreamPrefixSet_chainPrefixSet hc) :=
      rfl
  rw [h_eq] at h_sel
  rw [h_sel] at h_le
  exact h_le

/-- Step 5 of the proof of
`pm_partialWins`:
The martingale's values are unbounded. -/
private lemma pm_unbdd
    {r : BitString →. Bool} {M : BitString → ℚ}
    {m : BitString →. ℚ} {w u : CantorSeq}
    (hdom : ∀ n, (m (cantorPrefix w n)).Dom)
    (hm_val : ∀ x q, q ∈ m x → (m x).Dom ∧ q = M (selectedBits (partialRuleSet r) x))
    (h_sel : selectStream (partialRuleSet r) w = .infinite u)
    (hM_unbdd : ¬ BddAbove (Set.range fun n => ((M (cantorPrefix u n) : ℚ) : ℝ))) :
    ¬ BddAbove {r' : ℝ | ∃ n, ∃ q ∈ m (cantorPrefix w n), (q : ℝ) = r'} := by
  intro hb
  apply hM_unbdd
  obtain ⟨B, hB⟩ := hb
  use B
  rintro _ ⟨k, rfl⟩
  obtain ⟨t, ht⟩ := pm_lengths h_sel k
  have h_pref := pm_prefix h_sel t
  have ht_eq : cantorPrefix u k = selectChain (partialRuleSet r) w t := by
    rw [← ht]
    exact (isCantorPrefix_iff_cantorPrefix_eq _ u).mp h_pref
  have h_dom_t := hdom t
  obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp h_dom_t
  have hval := (hm_val (cantorPrefix w t) q hq).2
  have H : B ≥ ((q : ℚ) : ℝ) := by
    apply hB
    simp only [Set.mem_ofPred_eq]
    use t, q, hq
  have hq_eq : q = M (cantorPrefix u k) := by
    rw [hval]
    unfold selectChain at ht_eq
    rw [ht_eq]
  rw [hq_eq] at H
  exact H

/-- Step 3 of the proof of
`pm_of_random`:
Selection bookkeeping showing partial wins. -/
private lemma pm_partialWins
    {r : BitString →. Bool} {M : BitString → ℚ}
    {m : BitString →. ℚ} {w u : CantorSeq}
    (hm_dom : ∀ x, (m x).Dom ↔ (∀ y, y <+: x → (r y).Dom))
    (hm_val : ∀ x q, q ∈ m x → (m x).Dom ∧ q = M (selectedBits (partialRuleSet r) x))
    (h_sel : selectStream (partialRuleSet r) w = .infinite u)
    (hM_unbdd : ¬ BddAbove (Set.range fun n => ((M (cantorPrefix u n) : ℚ) : ℝ))) :
    pm_PartialWins m w :=
  ⟨pm_partialWins_dom hm_dom h_sel,
   pm_unbdd (pm_partialWins_dom hm_dom h_sel) hm_val h_sel hM_unbdd⟩

/-- Step 1 of the proof of `exists_isMisesChurchDaleyRandom_plainK_le`: A
partial-computably random sequence is Mises-Church-Daley random. -/
private lemma pm_of_random {w : CantorSeq}
    (hw : pm_IsPartialComputablyRandom w) :
        IsMisesChurchDaleyRandom w := by
  intro r hr
  by_contra h_not_freq
  rcases h_sel : selectStream (partialRuleSet r) w with _ | u
  · exact h_not_freq (by rw [h_sel]; exact trivial)
  · have h_not_freq_u : ¬ HasLimitFreq (1/2) u := fun h => h_not_freq (by rw [h_sel]; exact h)
    obtain ⟨M, hM_comp, hM_nonneg, hM_fair, hM_wins⟩ :=
        pm_computable_martingale_wins_unbalanced
    obtain ⟨m, hm_partrec, hm_mart, hm_dom, hm_val⟩ :=
        pm_partialMartingaleOfRule_partrec hr hM_comp
        hM_nonneg hM_fair
    have h_wins_M := hM_wins u h_not_freq_u
    have h_wins_m := pm_partialWins hm_dom hm_val h_sel
        h_wins_M
    have hm_mart_private : pm_IsPartialMartingale m :=
        ⟨hm_mart.nonneg, hm_mart.fair⟩
    have h_wins_m_private : pm_PartialWins m w := h_wins_m
    exact hw m hm_partrec hm_mart_private h_wins_m_private

/-- Step 1 of the proof of
`pm_exists_random`: A
strong partial martingale has initial capital one, a prefix-closed domain, and both children defined
together. -/
private def pm_Strong (m : BitString →. ℚ) : Prop :=
  pm_IsPartialMartingale m ∧ (1 ∈ m []) ∧
    ∀ x b, (m (x ++ [b])).Dom →
      (m x).Dom ∧ (m (x ++ [false])).Dom ∧ (m (x ++ [true])).Dom

open Classical in
/-- Step 2 of the proof of
`pm_exists_random`:
Complete a partial rational function by zero where it is undefined. -/
private noncomputable def pm_value (m : BitString →. ℚ)
    (x : BitString) : ℚ :=
  (m x).getOrElse 0

/-- Step 2 of the proof of
`pm_exists_random`: The
zero completion agrees with every defined value. -/
private lemma pm_value_eq (m : BitString →. ℚ)
    (x : BitString) {q : ℚ}
    (hq : q ∈ m x) : pm_value m x = q := by
  classical
  rw [pm_value, Part.getOrElse_of_dom _ hq.1]
  exact Part.mem_unique (Part.get_mem hq.1) hq

/-- Step 2 of the proof of
`pm_exists_random`: The
zero completion of a strong partial martingale is nonnegative. -/
private lemma pm_value_nonneg {m : BitString →. ℚ}
    (hm : pm_Strong m) (x : BitString) :
    0 ≤ pm_value m x := by
  classical
  by_cases hd : (m x).Dom
  · rw [pm_value, Part.getOrElse_of_dom _ hd]
    exact hm.1.nonneg x _ (Part.get_mem hd)
  · rw [pm_value, Part.getOrElse_of_not_dom _ hd]

/-- Step 2 of the proof of
`pm_exists_random`: The
zero completion of a strong partial martingale is a supermartingale; stopping can only discard
capital. -/
private lemma pm_value_superfair {m : BitString →. ℚ}
    (hm : pm_Strong m) (x : BitString) :
    pm_value m (x ++ [false]) +
        pm_value m (x ++ [true]) ≤ 2 *
        pm_value m x := by
  classical
  by_cases hd : (m (x ++ [false])).Dom
  · obtain ⟨hx, h0, h1⟩ := hm.2.2 x false hd
    have hfair := hm.1.fair x _ _ _ (Part.get_mem hx) (Part.get_mem h0) (Part.get_mem h1)
    simp only [pm_value, Part.getOrElse_of_dom _ hx,
        Part.getOrElse_of_dom _ h0,
      Part.getOrElse_of_dom _ h1]
    linarith
  · have h1 : ¬ (m (x ++ [true])).Dom := fun ht => hd (hm.2.2 x true ht).2.1
    rw [pm_value, Part.getOrElse_of_not_dom _ hd,
        pm_value, Part.getOrElse_of_not_dom _ h1]
    have := pm_value_nonneg hm x
    linarith

/-- Step 3 of the proof of
`pm_exists_random`:
Computably introduce every index, with at most f(n)/8 indices active at length n; t(i) is the first
activation length. -/
private lemma pm_schedule {f : ℕ → ℕ} (hf : Computable f)
    (hmono : Monotone f)
    (hunb : ∀ B, ∃ n, B ≤ f n) :
    ∃ k t : ℕ → ℕ, Computable k ∧ Computable t ∧ k 0 = 0 ∧
      (∀ i n, t i ≤ n ↔ i < k n) ∧ (∀ n, 8 * k n ≤ f n) := by
  let k : ℕ → ℕ := fun n => min n (f n / 8)
  have hk : Computable k := Primrec.nat_min.to_comp.comp Computable.id
    (Primrec.nat_div.to_comp.comp hf (Computable.const 8))
  have hkm : Monotone k := fun a b hab => min_le_min hab (Nat.div_le_div_right (hmono hab))
  have hex : ∀ i, ∃ n, i < k n := by
    intro i
    obtain ⟨n, hn⟩ := hunb (8 * (i + 1))
    refine ⟨max n (i + 1), ?_⟩
    have hfn : 8 * (i + 1) ≤ f (max n (i + 1)) := hn.trans (hmono (le_max_left _ _))
    have hdiv : i + 1 ≤ f (max n (i + 1)) / 8 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    exact lt_min (by omega) (by omega)
  let t : ℕ → ℕ := fun i => Nat.find (hex i)
  have ht : Computable t := Computable.find
    ((PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.fst
      (hk.comp Computable.snd)).computablePred hex
  refine ⟨k, t, hk, ht, by simp [k], ?_, ?_⟩
  · intro i n
    constructor
    · intro h
      exact lt_of_lt_of_le (Nat.find_spec (hex i)) (hkm h)
    · intro h
      exact Nat.find_min' (hex i) h
  · intro n
    have hk' : k n ≤ f n / 8 := min_le_right _ _
    omega

/-- Step 4 of the proof of
`pm_exists_random`: Fix
the positive weight of account i at its activation prefix, using the dyadic budget 2^(-i-1). -/
private noncomputable def pm_weight (M : ℕ → BitString →. ℚ)
    (t : ℕ → ℕ)
    (i : ℕ) (x : BitString) : ℚ :=
  (1 / 2 : ℚ) ^ (i + 1) / (pm_value (M i) (x.take (t i)) + 1)

/-- Step 4 of the proof of
`pm_exists_random`: Sum
the weighted zero-completed capitals of the accounts active at the current prefix. -/
private noncomputable def pm_potential (M : ℕ → BitString →.
    ℚ) (k t : ℕ → ℕ)
    (x y : BitString) : ℚ :=
  ∑ i ∈ Finset.range (k x.length), pm_weight M t i x *
      pm_value (M i) y

open Classical in
/-- Step 4 of the proof of
`pm_exists_random`: Choose
the child with smaller potential, taking true in a tie. -/
private noncomputable def pm_bit (M : ℕ → BitString →. ℚ)
    (k t : ℕ → ℕ)
    (x : BitString) : Bool :=
  decide (pm_potential M k t x (x ++ [true]) ≤
      pm_potential M k t x (x ++ [false]))

/-- Step 4 of the proof of
`pm_exists_random`: The
canonical prefix construction, with the potential-minimizing bit appended at each stage. -/
private noncomputable def pm_state (M : ℕ → BitString →. ℚ)
    (k t : ℕ → ℕ) : ℕ → BitString
  | 0 => []
  | n + 1 => pm_state M k t n ++
               [pm_bit M k t
               (pm_state M k t n)]

/-- Step 4 of the proof of
`pm_exists_random`: The
infinite sequence specified by the canonical prefix construction. -/
private noncomputable def pm_seq (M : ℕ → BitString →. ℚ)
    (k t : ℕ → ℕ) : CantorSeq :=
  fun n => pm_bit M k t
             (pm_state M k t n)

/-- Step 4 of the proof of
`pm_exists_random`: The
canonical states are exactly the prefixes of the constructed sequence. -/
private lemma pm_random_prefix (M : ℕ → BitString →. ℚ) (k t : ℕ → ℕ) (n : ℕ) :
    cantorPrefix (pm_seq M k t) n =
        pm_state M k t n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cantorPrefix_succ, ih]; rfl

/-- Step 4 of the proof of
`pm_exists_random`: The
state at stage n has length n. -/
private lemma pm_length (M : ℕ → BitString →. ℚ)
    (k t : ℕ → ℕ) (n : ℕ) :
    (pm_state M k t n).length = n := by rw [← pm_random_prefix, cantorPrefix_length]

/-- Step 4 of the proof of
`pm_exists_random`:
Earlier states are initial segments of later states. -/
private lemma pm_take (M : ℕ → BitString →. ℚ) (k t : ℕ → ℕ)
    {n a : ℕ} (ha : a ≤ n) :
    (pm_state M k t n).take a =
        pm_state M k t a := by
  rw [← pm_random_prefix, ← pm_random_prefix, cantorPrefix_take _ a n ha]

/-- Step 4 of the proof of
`pm_exists_random`: Every
account receives a strictly positive weight. -/
private lemma pm_weight_pos {M : ℕ → BitString →. ℚ}
    (hM : ∀ i, pm_Strong (M i))
    (t : ℕ → ℕ) (i : ℕ) (x : BitString) : 0 < pm_weight M t i
        x := by
  have := pm_value_nonneg (hM i) (x.take (t i))
  unfold pm_weight
  positivity

/-- Step 4 of the proof of
`pm_exists_random`: The
finite dyadic budgets sum to at most one. -/
private lemma pm_budget (N : ℕ) : (∑ i ∈ Finset.range N,
    (1 / 2 : ℚ) ^ (i + 1)) ≤ 1 := by
  have h : (∑ i ∈ Finset.range N, (1 / 2 : ℚ) ^ (i + 1)) = 1 - (1 / 2 : ℚ) ^ N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [h]
  linarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) N]

/-- Step 4 of the proof of
`pm_exists_random`: The
potential cannot increase when the potential-minimizing bit is appended. -/
private lemma pm_one_step {M : ℕ → BitString →. ℚ} (hM : ∀ i,
    pm_Strong (M i))
    (k t : ℕ → ℕ) (x : BitString) :
    pm_potential M k t x
        (x ++ [pm_bit M k t x]) ≤
        pm_potential M k t x x := by
  have hs : pm_potential M k t x (x ++ [false]) +
      pm_potential M k t x (x ++ [true]) ≤
      2 * pm_potential M k t x x := by
    unfold pm_potential
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (pm_value_superfair
        (hM i) x)
      (pm_weight_pos hM t i x).le
    nlinarith only [h]
  unfold pm_bit
  by_cases h : pm_potential M k t x (x ++ [true]) ≤
      pm_potential M k t x (x ++ [false])
  · simp only [h, decide_true]
    linarith
  · simp only [h, decide_false]
    have := not_le.1 h
    linarith

/-- Step 4 of the proof of
`pm_exists_random`: After
activation an account keeps the same weight at every later state. -/
private lemma pm_weight_stable (M : ℕ → BitString →. ℚ)
    (k t : ℕ → ℕ)
    {i n a : ℕ} (ht : t i ≤ a) (ha : a ≤ n) :
    pm_weight M t i
        (pm_state M k t n) =
        pm_weight M t i
        (pm_state M k t a) := by
  unfold pm_weight
  rw [pm_take M k t (ht.trans ha),
      pm_take M k t ht]

/-- Step 4 of the proof of
`pm_exists_random`: A
newly activated account contributes at most its dyadic budget. -/
private lemma pm_new_term {M : ℕ → BitString →. ℚ} (hM : ∀ i,
    pm_Strong (M i))
    (t : ℕ → ℕ) (i : ℕ) (x : BitString) (ht : t i = x.length) :
    pm_weight M t i x *
        pm_value (M i) x ≤ (1 / 2 : ℚ) ^ (i + 1) := by
  have hv := pm_value_nonneg (hM i) x
  have hd : 0 < pm_value (M i) x + 1 := by linarith
  unfold pm_weight
  rw [ht, List.take_length, div_mul_eq_mul_div, div_le_iff₀ hd]
  have hp : 0 ≤ (1 / 2 : ℚ) ^ (i + 1) := by positivity
  nlinarith only [hp]

/-- Step 4 of the proof of
`pm_exists_random`: The
potential is bounded by the sum of the budgets of the active accounts. -/
private lemma pm_bounded_potential {M : ℕ → BitString →. ℚ}
    (hM : ∀ i, pm_Strong (M i))
    (k t : ℕ → ℕ) (hk0 : k 0 = 0) (hkt : ∀ i n, t i ≤ n ↔ i < k n) (n : ℕ) :
    pm_potential M k t
        (pm_state M k t n)
        (pm_state M k t n) ≤
      ∑ i ∈ Finset.range (k n), (1 / 2 : ℚ) ^ (i + 1) := by
  have hkm : Monotone k := by
    intro a b hab
    by_contra h
    have hi : k b < k a := Nat.lt_of_not_ge h
    have ht := (hkt (k b) a).2 hi
    have := (hkt (k b) b).1 (ht.trans hab)
    omega
  induction n with
  | zero => simp [pm_potential,
              pm_state, hk0]
  | succ n ih =>
    have hle : k n ≤ k (n + 1) := hkm (Nat.le_succ n)
    have hsplit : pm_potential M k t
        (pm_state M k t (n + 1))
        (pm_state M k t (n + 1)) =
        pm_potential M k t
            (pm_state M k t n)
            (pm_state M k t (n + 1)) +
        ∑ i ∈ Finset.Ico (k n) (k (n + 1)),
          pm_weight M t i
              (pm_state M k t (n + 1)) *
              pm_value (M i)
              (pm_state M k t (n + 1)) := by
      unfold pm_potential
      rw [pm_length, pm_length, ← Finset.sum_range_add_sum_Ico _ hle]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [pm_weight_stable M k t
          ((hkt i n).2 (Finset.mem_range.1 hi)) (Nat.le_succ n)]
    rw [hsplit, ← Finset.sum_range_add_sum_Ico _ hle]
    apply add_le_add
    · exact (pm_one_step hM k t
        (pm_state M k t n)).trans ih
    · apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi0, hi1⟩ := Finset.mem_Ico.1 hi
      apply pm_new_term hM
      rw [pm_length]
      have hupper : t i ≤ n + 1 := (hkt i (n + 1)).2 hi1
      have hlower : ¬ t i ≤ n := fun h => Nat.not_lt_of_ge hi0 ((hkt i n).1 h)
      omega

/-- Step 4 of the proof of
`pm_exists_random`: No
member of the strong family wins on the canonical sequence, since its positive weighted capital
stays bounded after activation. -/
private lemma pm_avoids {M : ℕ → BitString →. ℚ} (hM : ∀ i,
    pm_Strong (M i))
    (k t : ℕ → ℕ) (hk0 : k 0 = 0) (hkt : ∀ i n, t i ≤ n ↔ i < k n) :
    ∀ i, ¬ pm_PartialWins (M i)
        (pm_seq M k t) := by
  intro i hwin
  apply hwin.2
  let w := pm_seq M k t
  let e : ℚ := pm_weight M t i
      (pm_state M k t (t i))
  have he : 0 < e := pm_weight_pos hM t i _
  let B : ℚ := max (1 / e)
    ((Finset.range (t i)).sum fun n => pm_value (M i)
                                         (cantorPrefix w n))
  refine ⟨(B : ℝ), ?_⟩
  rintro r ⟨n, q, hq, rfl⟩
  have hqv : q = pm_value (M i)
      (pm_state M k t n) := by
    rw [← pm_random_prefix]
    exact (pm_value_eq (M i) _ hq).symm
  have hqbound : q ≤ B := by
    by_cases hn : t i ≤ n
    · have hi : i ∈ Finset.range (k n) := Finset.mem_range.2 ((hkt i n).1 hn)
      have hterm : pm_weight M t i
          (pm_state M k t n) *
          pm_value (M i)
          (pm_state M k t n) ≤
          pm_potential M k t
              (pm_state M k t n)
              (pm_state M k t n) := by
        unfold pm_potential
        rw [pm_length]
        exact Finset.single_le_sum (fun j hj =>
          mul_nonneg (pm_weight_pos hM t j _).le
              (pm_value_nonneg (hM j) _)) hi
      have hpot := (pm_bounded_potential hM k t hk0 hkt
          n).trans (pm_budget (k n))
      rw [pm_weight_stable M k t (le_refl (t i)) hn, ← hqv]
          at hterm
      have hqe : q ≤ 1 / e := (le_div_iff₀ he).2 (by nlinarith only [hterm, hpot])
      exact hqe.trans (le_max_left _ _)
    · have hsmall : q ≤ (Finset.range (t i)).sum fun n =>
        pm_value (M i) (cantorPrefix w n) := by
        rw [← pm_value_eq (M i) _ hq]
        exact Finset.single_le_sum (fun j hj =>
          pm_value_nonneg (hM i) _) (Finset.mem_range.2
          (by omega))
      exact hsmall.trans (le_max_right _ _)
  exact_mod_cast hqbound

/-- Step 5 of the proof of
`pm_exists_random`:
Definedness of a strong partial martingale propagates to every shorter prefix. -/
private lemma pm_dom_prefix {m : BitString →. ℚ}
    (hm : pm_Strong m)
    {x y : BitString} (hxy : x <+: y) (hy : (m y).Dom) : (m x).Dom := by
  obtain ⟨z, rfl⟩ := hxy
  induction z using List.reverseRecOn with
  | nil => simpa using hy
  | append_singleton z b ih =>
    apply ih
    apply (hm.2.2 (x ++ z) b ?_).1
    simpa only [List.append_assoc] using hy

/-- Step 5 of the proof of
`pm_exists_random`: For
each active account record its first undefined prefix length, capped at n+1; this advice exactly
describes definedness through length n. -/
private lemma pm_advice {M : ℕ → BitString →. ℚ} (hM : ∀ i,
    pm_Strong (M i))
    (k : ℕ → ℕ) (w : CantorSeq) :
    ∃ adv : ℕ → List ℕ, (∀ n, (adv n).length = k n) ∧
      (∀ n i, i < k n → (adv n).getD i 0 ≤ n + 1) ∧
      ∀ n i, i < k n → ∀ j, j ≤ n →
        ((M i (cantorPrefix w j)).Dom ↔ j < (adv n).getD i 0) := by
  classical
  have hcut : ∀ n i, ∃ a, a ≤ n + 1 ∧ ∀ j, j ≤ n →
      ((M i (cantorPrefix w j)).Dom ↔ j < a) := by
    intro n i
    by_cases h : ∃ j, j ≤ n ∧ ¬ (M i (cantorPrefix w j)).Dom
    · refine ⟨Nat.find h, by have := (Nat.find_spec h).1; omega, fun j hj => ?_⟩
      constructor
      · intro hd
        by_contra hlt
        have hd' := pm_dom_prefix (hM i) (cantorPrefix_mono w
            (Nat.le_of_not_gt hlt)) hd
        exact (Nat.find_spec h).2 hd'
      · intro hlt
        by_contra hnd
        exact Nat.find_min h hlt ⟨hj, hnd⟩
    · refine ⟨n + 1, le_rfl, fun j hj => ?_⟩
      have hd : (M i (cantorPrefix w j)).Dom := by
        by_contra hnd
        exact h ⟨j, hj, hnd⟩
      simp only [hd, true_iff]
      omega
  choose a ha using hcut
  refine ⟨fun n => (List.range (k n)).map (a n), ?_, ?_, ?_⟩
  · intro n
    simp
  · intro n i hi
    simpa [List.getD_map, List.getElem?_range hi] using (ha n i).1
  · intro n i hi j hj
    simpa [List.getD_map, List.getElem?_range hi] using (ha n i).2 j hj

/-- Step 6 of the proof of
`pm_exists_random`: A
computable rational expression agreeing with 1/(q+1) for nonnegative q. -/
private def pm_recip (q : ℚ) : ℚ :=
    (q.den : ℚ) / ((q.num.toNat + q.den : ℕ) : ℚ)

/-- Step 6 of the proof of
`pm_exists_random`: The
rational expression used for normalizing an account is computable with the standard encoding of
rationals. -/
private lemma pm_recip_comp : Computable
    pm_recip := by
  apply computable_of_num_den
    (ComputableReals.primrec_natCastInt.to_comp.comp computable_ratDen)
    (Primrec.nat_add.to_comp.comp
      (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum) computable_ratDen)
  · intro q
    have := q.pos
    omega
  · intro q
    simp [pm_recip]

/-- Step 6 of the proof of
`pm_exists_random`: For
nonnegative capital the computable expression is the required reciprocal. -/
private lemma pm_recip_eq {q : ℚ} (hq : 0 ≤ q) :
    pm_recip q = 1 / (q + 1) := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.2 hq
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hdpos : (0 : ℚ) < q.den := by exact_mod_cast q.pos
  have hnnonneg : (0 : ℚ) ≤ q.num := by exact_mod_cast hn
  unfold pm_recip
  push_cast
  have hncast : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn
  rw [hncast]
  have hqnum := Rat.num_div_den q
  apply (div_eq_iff (by linarith : (q.num : ℚ) + q.den ≠ 0)).2
  rw [one_div_mul_eq_div]
  apply (eq_div_iff (by linarith : q + 1 ≠ 0)).2
  have hqn : (q.num : ℚ) = q * q.den := (div_eq_iff hd).1 hqnum
  linarith

/-- Step 6 of the proof of
`pm_exists_random`: The
dyadic account budgets are computable. -/
private lemma pm_half_pow_comp : Computable
    (fun i : ℕ => (1 / 2 : ℚ) ^ (i + 1)) := by
  apply computable_of_num_den (N := fun _ => 1)
    (D := fun i => 2 ^ (i + 1)) (Computable.const 1)
    (comp_pow.comp Primrec.succ.to_comp)
  · intro i
    positivity
  · intro i
    push_cast
    exact one_div_pow (2 : ℚ) (i + 1)

/-- Step 6 of the proof of
`pm_exists_random`:
Comparison of two rationals is computable with the standard rational encoding. -/
private lemma pm_rat_le_comp : Computable₂
    (fun a b : ℚ => decide (a ≤ b)) := by
  have h : Computable (fun p : ℚ × ℚ => decide (p.1 - p.2 + 1 ≤ 1)) :=
    computable_ratLeOne.comp (computable₂_ratAdd.comp
      (computable₂_ratSub.comp Computable.fst Computable.snd) (Computable.const 1))
  exact h.of_eq fun p => by congr 1; apply propext; constructor <;> intro h <;> linarith

/-- Step 6 of the proof of
`pm_exists_random`: Use
the divergence advice to skip an evaluation after its stopping length; otherwise run the partial
martingale. -/
private def pm_simValue (M : ℕ → BitString →. ℚ) (a : List ℕ)
    (i : ℕ) (x : BitString) : Part ℚ :=
  if x.length < a.getD i 0 then M i x else Part.some 0

/-- Step 6 of the proof of
`pm_exists_random`:
Compute one weighted account from the advice and two partial evaluations. -/
private def pm_simTerm (M : ℕ → BitString →. ℚ) (t : ℕ → ℕ)
    (a : List ℕ)
    (x y : BitString) (i : ℕ) : Part ℚ :=
  (pm_simValue M a i (x.take (t i))).bind fun q0 =>
    (pm_simValue M a i y).map fun qy =>
      (1 / 2 : ℚ) ^ (i + 1) * pm_recip q0 * qy

/-- Step 6 of the proof of
`pm_exists_random`:
Compute the finite sum of the active weighted accounts in the Part monad. -/
private def pm_simPot (M : ℕ → BitString →. ℚ) (k t : ℕ → ℕ)
    (a : List ℕ)
    (x y : BitString) : Part ℚ :=
  Nat.rec (Part.some 0) (fun i ih => ih.bind fun acc =>
    (pm_simTerm M t a x y i).map fun v =>
      acc + v) (k x.length)

/-- Step 6 of the proof of
`pm_exists_random`:
Compute the potential-minimizing bit from the two partial child potentials. -/
private def pm_simBit (M : ℕ → BitString →. ℚ) (k t : ℕ → ℕ)
    (a : List ℕ)
    (x : BitString) : Part Bool :=
  (pm_simPot M k t a x (x ++ [true])).bind fun q1 =>
    (pm_simPot M k t a x (x ++ [false])).map fun q0 =>
      decide (q1 ≤ q0)

/-- Step 6 of the proof of
`pm_exists_random`: Replay
the canonical construction in the Part monad using a finite advice list. -/
private def pm_simState (M : ℕ → BitString →. ℚ)
    (k t : ℕ → ℕ) (a : List ℕ) : ℕ → Part BitString
  | 0 => Part.some []
  | n + 1 => (pm_simState M k t a n).bind fun x =>
      (pm_simBit M k t a x).map fun b => x ++ [b]

/-- Step 6 of the proof of
`pm_exists_random`:
Advice-controlled evaluation is partial recursive uniformly in the advice, index and string. -/
private lemma pm_simValue_partrec {M : ℕ → BitString →. ℚ}
    (hM : Partrec (fun p : ℕ × BitString => M p.1 p.2)) :
    Partrec (fun p : List ℕ × ℕ × BitString => pm_simValue M
                                                 p.1 p.2.1 p.2.2) := by
  have ha : Computable (fun p : List ℕ × ℕ × BitString => p.1.getD p.2.1 0) :=
    (Primrec.list_getD 0).to_comp.comp Computable.fst (Computable.fst.comp Computable.snd)
  have hc : Computable (fun p : List ℕ × ℕ × BitString => decide (p.2.2.length < p.1.getD p.2.1 0))
      :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp
      (Computable.list_length.comp (Computable.snd.comp Computable.snd)) ha
  exact (Partrec.cond hc (hM.comp Computable.snd) (Computable.const 0).partrec).of_eq
    (fun p => by simp [pm_simValue])

/-- Step 6 of the proof of
`pm_exists_random`: The
simulated weighted account is partial recursive. -/
private lemma pm_simTerm_partrec {M : ℕ → BitString →. ℚ}
    (hM : Partrec (fun p : ℕ × BitString => M p.1 p.2))
    {t : ℕ → ℕ} (ht : Computable t) :
    Partrec (fun p : (List ℕ × BitString × BitString) × ℕ =>
      pm_simTerm M t p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let X := (List ℕ × BitString × BitString) × ℕ
  have ha : Computable (fun p : X => p.1.1) := Computable.fst.comp Computable.fst
  have hi : Computable (fun p : X => p.2) := Computable.snd
  have hx : Computable (fun p : X => p.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hy : Computable (fun p : X => p.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hpref : Computable (fun p : X => p.1.2.1.take (t p.2)) :=
    Primrec.list_take.to_comp.comp (ht.comp hi) hx
  have h0 := (pm_simValue_partrec hM).comp
      (ha.pair (hi.pair hpref))
  have h1 := (pm_simValue_partrec hM).comp
      (ha.pair (hi.pair hy))
  have hout : Computable (fun p : (X × ℚ) × ℚ =>
      (1 / 2 : ℚ) ^ (p.1.1.2 + 1) * pm_recip p.1.2 * p.2) :=
    computable₂_ratMul.comp
      (computable₂_ratMul.comp
        (pm_half_pow_comp.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
        (pm_recip_comp.comp (Computable.snd.comp Computable.fst))) Computable.snd
  exact (h0.bind ((h1.comp Computable.fst).map hout.to₂).to₂).of_eq (fun p => rfl)

/-- Step 6 of the proof of
`pm_exists_random`: The
simulated finite potential is partial recursive. -/
private lemma pm_simPot_partrec {M : ℕ → BitString →. ℚ}
    (hM : Partrec (fun p : ℕ × BitString => M p.1 p.2))
    {k t : ℕ → ℕ} (hk : Computable k) (ht : Computable t) :
    Partrec (fun p : List ℕ × BitString × BitString =>
      pm_simPot M k t p.1 p.2.1 p.2.2) := by
  let X := List ℕ × BitString × BitString
  have hpair : Computable (fun p : X × (ℕ × ℚ) => (p.1, p.2.1)) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hterm := (pm_simTerm_partrec hM ht).comp hpair
  have hout : Computable₂ (fun (p : X × (ℕ × ℚ)) (v : ℚ) => p.2.2 + v) :=
    computable₂_ratAdd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd
  have hf : Computable (fun p : X => k p.2.1.length) :=
    hk.comp (Computable.list_length.comp (Computable.fst.comp Computable.snd))
  have hg : Partrec (fun _ : X => Part.some (0 : ℚ)) := (Computable.const 0).partrec
  have hh : Partrec₂ (fun (p : X) (ns : ℕ × ℚ) =>
      (pm_simTerm M t p.1 p.2.1 p.2.2 ns.1).map fun v =>
        ns.2 + v) := (hterm.map hout).to₂
  have H : Partrec (fun p : X => Nat.rec (Part.some (0 : ℚ))
      (fun i ih => ih.bind fun acc =>
        (pm_simTerm M t p.1 p.2.1 p.2.2 i).map fun v =>
          acc + v) (k p.2.1.length)) :=
    Partrec.nat_rec hf hg hh
  exact H.of_eq (fun p => rfl)

/-- Step 6 of the proof of
`pm_exists_random`: The
simulated choice of the next bit is partial recursive. -/
private lemma pm_simBit_partrec {M : ℕ → BitString →. ℚ}
    (hM : Partrec (fun p : ℕ × BitString => M p.1 p.2))
    {k t : ℕ → ℕ} (hk : Computable k) (ht : Computable t) :
    Partrec (fun p : List ℕ × BitString => pm_simBit M k t
                                             p.1 p.2) := by
  have happ (b : Bool) : Computable (fun p : List ℕ × BitString => p.2 ++ [b]) :=
    Primrec.list_append.to_comp.comp Computable.snd (Computable.const [b])
  have hc (b : Bool) := (pm_simPot_partrec hM hk ht).comp
    (Computable.fst.pair (Computable.snd.pair (happ b)))
  have hout : Computable₂ (fun (p : (List ℕ × BitString) × ℚ) (q0 : ℚ) => decide (p.2 ≤ q0)) :=
    pm_rat_le_comp.comp (Computable.snd.comp Computable.fst)
        Computable.snd
  exact ((hc true).bind (((hc false).comp Computable.fst).map hout).to₂).of_eq (fun p => rfl)

/-- Step 6 of the proof of
`pm_exists_random`: The
complete replay is partial recursive jointly in n and the advice list. -/
private lemma pm_simState_partrec {M : ℕ → BitString →. ℚ}
    (hM : Partrec (fun p : ℕ × BitString => M p.1 p.2))
    {k t : ℕ → ℕ} (hk : Computable k) (ht : Computable t) :
    Partrec (fun p : ℕ × List ℕ => pm_simState M k t p.2 p.1)
        := by
  have hpair : Computable (fun p : (ℕ × List ℕ) × (ℕ × BitString) => (p.1.2, p.2.2)) :=
    (Computable.snd.comp Computable.fst).pair (Computable.snd.comp Computable.snd)
  have hb := (pm_simBit_partrec hM hk ht).comp hpair
  have hout : Computable₂ (fun (p : (ℕ × List ℕ) × (ℕ × BitString)) (b : Bool) => p.2.2 ++ [b]) :=
    Primrec.list_append.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (Primrec.list_cons.to_comp.comp Computable.snd (Computable.const []))
  have hf : Computable (fun p : ℕ × List ℕ => p.1) := Computable.fst
  have hg : Partrec (fun _ : ℕ × List ℕ => Part.some ([] : BitString)) :=
    (Computable.const []).partrec
  have hh : Partrec₂ (fun (p : ℕ × List ℕ) (ns : ℕ × BitString) =>
      (pm_simBit M k t p.2 ns.2).map fun b =>
        ns.2 ++ [b]) := (hb.map hout).to₂
  have H : Partrec (fun p : ℕ × List ℕ => Nat.rec (Part.some ([] : BitString))
      (fun _ ih => ih.bind fun x => (pm_simBit M k t p.2
                                      x).map fun b => x ++ [b]) p.1) :=
    Partrec.nat_rec hf hg hh
  refine H.of_eq fun p => ?_
  change Nat.rec _ _ p.1 = pm_simState M k t p.2 p.1
  generalize p.1 = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [pm_simState, ih]

/-- Step 6 of the proof of
`pm_exists_random`: For a
strong partial martingale, either child is defined exactly when the other child is defined. -/
private lemma pm_child_dom {m : BitString →. ℚ}
    (hm : pm_Strong m)
    (x : BitString) (b c : Bool) : (m (x ++ [b])).Dom ↔ (m (x ++ [c])).Dom := by
  constructor <;> intro h
  · have hh := hm.2.2 x b h
    cases c
    · exact hh.2.1
    · exact hh.2.2
  · have hh := hm.2.2 x c h
    cases b
    · exact hh.2.1
    · exact hh.2.2

/-- Step 6 of the proof of
`pm_exists_random`: On
correct domain advice the simulated value equals the zero completion. -/
private lemma pm_simValue_eq (M : ℕ → BitString →. ℚ)
    (a : List ℕ) (i : ℕ) (x : BitString)
    (hd : (M i x).Dom ↔ x.length < a.getD i 0) :
    pm_simValue M a i x = Part.some
        (pm_value (M i) x) := by
  classical
  unfold pm_simValue
  by_cases h : x.length < a.getD i 0
  · rw [ite_eq_left h]
    apply Part.eq_some_iff.2
    rw [pm_value, Part.getOrElse_of_dom _ (hd.2 h)]
    exact Part.get_mem _
  · rw [ite_eq_right h, pm_value, Part.getOrElse_of_not_dom _
      (fun h' => h (hd.1 h'))]

/-- Step 6 of the proof of
`pm_exists_random`:
Correct stopping advice along the canonical path also determines both child evaluations and every
activation value. -/
private lemma pm_simTerm_eq {M : ℕ → BitString →. ℚ}
    (hM : ∀ i, pm_Strong (M i))
    (k t : ℕ → ℕ) (hkt : ∀ i n, t i ≤ n ↔ i < k n)
    (a : List ℕ) (n : ℕ)
    (ha : ∀ i, i < k n → ∀ j, j ≤ n →
      ((M i (cantorPrefix (pm_seq M k t) j)).Dom ↔ j <
          a.getD i 0))
    (j : ℕ) (hj : j + 1 ≤ n) (i : ℕ) (hi : i < k j) (b : Bool) :
    pm_simTerm M t a
        (pm_state M k t j)
        (pm_state M k t j ++ [b]) i =
      Part.some (pm_weight M t i
          (pm_state M k t j) *
          pm_value (M i)
          (pm_state M k t j ++ [b])) := by
  have hti : t i ≤ j := (hkt i j).2 hi
  have hin : i < k n := (hkt i n).1 (by omega)
  have hd0 : (M i ((pm_state M k t j).take (t i))).Dom ↔
      ((pm_state M k t j).take (t i)).length < a.getD i 0 :=
          by
    rw [pm_take M k t hti, pm_length, ← pm_random_prefix]
    exact ha i hin (t i) (by omega)
  have hd1 : (M i (pm_state M k t j ++ [b])).Dom ↔
      (pm_state M k t j ++ [b]).length < a.getD i 0 := by
    rw [List.length_append, List.length_singleton, pm_length]
    rw [pm_child_dom (hM i)
        (pm_state M k t j) b
        (pm_bit M k t
        (pm_state M k t j))]
    change (M i (pm_state M k t (j + 1))).Dom ↔ j + 1 <
        a.getD i 0
    rw [← pm_random_prefix]
    exact ha i hin (j + 1) hj
  unfold pm_simTerm
  rw [pm_simValue_eq M a i _ hd0, Part.bind_some,
      pm_simValue_eq M a i _ hd1, Part.map_some]
  rw [pm_recip_eq (pm_value_nonneg (hM i) _)]
  unfold pm_weight
  congr 1
  ring

/-- Step 6 of the proof of
`pm_exists_random`: On
correct stopping advice the simulated child potential equals the canonical potential. -/
private lemma pm_simPot_eq {M : ℕ → BitString →. ℚ}
    (hM : ∀ i, pm_Strong (M i))
    (k t : ℕ → ℕ) (hkt : ∀ i n, t i ≤ n ↔ i < k n)
    (a : List ℕ) (n : ℕ)
    (ha : ∀ i, i < k n → ∀ j, j ≤ n →
      ((M i (cantorPrefix (pm_seq M k t) j)).Dom ↔ j <
          a.getD i 0))
    (j : ℕ) (hj : j + 1 ≤ n) (b : Bool) :
    pm_simPot M k t a
        (pm_state M k t j)
        (pm_state M k t j ++ [b]) =
      Part.some (pm_potential M k t
          (pm_state M k t j)
          (pm_state M k t j ++ [b])) := by
  have hloop : ∀ m, m ≤ k j → Nat.rec (Part.some 0)
      (fun i ih => ih.bind fun acc =>
        (pm_simTerm M t a
            (pm_state M k t j)
            (pm_state M k t j ++ [b]) i).map fun v =>
              acc + v) m =
      Part.some (∑ i ∈ Finset.range m,
        pm_weight M t i
            (pm_state M k t j) *
            pm_value (M i)
            (pm_state M k t j ++ [b])) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      dsimp only
      rw [ih (by omega), Part.bind_some,
        pm_simTerm_eq hM k t hkt a n ha j hj m (by omega) b,
            Part.map_some]
      congr 1
      rw [Finset.sum_range_succ]
  unfold pm_simPot pm_potential
  rw [pm_length]
  exact hloop (k j) le_rfl

/-- Step 6 of the proof of
`pm_exists_random`: A
fixed partial computable decoder reconstructs each canonical prefix from advice giving the first
divergence lengths; no totality on other advice is required. -/
private lemma pm_decoder {M : ℕ → BitString →. ℚ} (hM : ∀ i,
    pm_Strong (M i))
    (hcM : Partrec (fun p : ℕ × BitString => M p.1 p.2))
    (k t : ℕ → ℕ) (hk : Computable k) (ht : Computable t)
    (hkt : ∀ i n, t i ≤ n ↔ i < k n) :
    ∃ D : ℕ × List ℕ →. BitString, Partrec D ∧
      ∀ n a, (∀ i, i < k n → ∀ j, j ≤ n →
        ((M i (cantorPrefix (pm_seq M k t) j)).Dom ↔ j <
            a.getD i 0)) →
        cantorPrefix (pm_seq M k t) n ∈ D (n, a) := by
  refine ⟨fun p => pm_simState M k t p.2 p.1,
      pm_simState_partrec hcM hk ht, ?_⟩
  intro n a ha
  have hloop : ∀ j, j ≤ n → pm_simState M k t a j = Part.some
      (pm_state M k t j) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [pm_simState, ih (by omega), Part.bind_some]
      unfold pm_simBit
      rw [pm_simPot_eq hM k t hkt a n ha j hj true,
          Part.bind_some,
        pm_simPot_eq hM k t hkt a n ha j hj false,
            Part.map_some, Part.map_some]
      rfl
  change cantorPrefix (pm_seq M k t) n ∈
      pm_simState M k t a n
  rw [hloop n le_rfl,
      pm_random_prefix]
  exact Part.mem_some _

/-- Step 7 of the proof of
`pm_exists_random`: Encode
n and a list of divergence lengths with self-delimiting pair and list codes. -/
private def pm_code (n : ℕ) (a : List ℕ) : BitString :=
  pairCode (natToBitString n) (listCode (a.map natToBitString))

/-- Step 7 of the proof of
`pm_exists_random`: Parse
the natural length and the list of natural advice entries. -/
private def pm_uncode (p : BitString) : ℕ × List ℕ :=
  (bitStringToNat (decodeFirst p), (decodeListCode (decodeSecond p)).map bitStringToNat)

/-- Step 7 of the proof of
`pm_exists_random`:
Parsing the length and the advice is computable. -/
private lemma pm_uncode_comp : Computable
    pm_uncode := by
  have hlist : Computable (fun p : BitString =>
      (decodeListCode (decodeSecond p)).map bitStringToNat) :=
    Computable.list_map (decodeListCode_computable.comp decodeSecond_computable)
      (computable_bitStringToNat.comp Computable.snd).to₂
  exact ((computable_bitStringToNat.comp decodeFirst_computable).pair hlist).of_eq (fun _ => rfl)

/-- Step 7 of the proof of
`pm_exists_random`:
Parsing recovers exactly the encoded length and advice list. -/
private lemma pm_uncode_code (n : ℕ) (a : List ℕ) : pm_uncode (pm_code n a) = (n, a) := by
  simp [pm_uncode, pm_code, decodeFirst_pairCode, decodeSecond_pairCode, List.map_map,
    Function.comp_def]

/-- Step 7 of the proof of
`pm_exists_random`: A
divergence length at most n+1 has a code of length at most floor(log2 n)+2. -/
private lemma pm_nat_code_length (n a : ℕ) (ha : a ≤ n + 1) :
    (natToBitString a).length ≤ Nat.log 2 n + 2 := by
  have hn : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hp : 0 < 2 ^ (Nat.log 2 n + 1) := by positivity
  have hbig : a + 1 < 2 ^ (Nat.log 2 n + 3) := by
    rw [show Nat.log 2 n + 3 = (Nat.log 2 n + 1) + 2 from by omega, pow_add]
    norm_num
    omega
  have hs : Nat.size (a + 1) ≤ Nat.log 2 n + 3 := Nat.size_le.2 hbig
  simpa only [natToBitString, List.length_dropLast, Nat.size_eq_bits_len] using
    (show Nat.size (a + 1) - 1 ≤ Nat.log 2 n + 2 by omega)

/-- Step 7 of the proof of
`pm_exists_random`: The
self-delimiting list code costs at most 2L+1 bits per entry whose code has length at most L. -/
private lemma pm_list_code_length (a : List ℕ) (L : ℕ)
    (ha : ∀ v ∈ a, (natToBitString v).length ≤ L) :
    (listCode (a.map natToBitString)).length ≤ a.length * (2 * L + 1) := by
  induction a with
  | nil => simp
  | cons v a ih =>
    have hv := ha v (by simp)
    have hi := ih (fun v hv => ha v (by simp [hv]))
    simp only [List.map_cons, length_listCode_cons, List.length_cons]
    nlinarith only [hv, hi]

/-- Step 7 of the proof of
`pm_exists_random`: The
full code of n and the advice has length at most (number of entries+1)(2 floor(log2 n)+5). -/
private lemma pm_code_length (n : ℕ) (a : List ℕ)
    (ha : ∀ i, i < a.length → a.getD i 0 ≤ n + 1) :
    (pm_code n a).length ≤ (a.length + 1) *
        (2 * Nat.log 2 n + 5) := by
  have hmem : ∀ v ∈ a, v ≤ n + 1 := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using ha i hi
  have hlist := pm_list_code_length a (Nat.log 2 n + 2)
    (fun v hv => pm_nat_code_length n v (hmem v hv))
  have hhead := pm_nat_code_length n n (by omega)
  unfold pm_code
  rw [length_pairCode]
  nlinarith only [hlist, hhead]

/-- Step 7 of the proof of
`pm_exists_random`: Any
partial computable decoder with at most f(n)/8 bounded natural advice entries yields the required
plain complexity bound; monotonicity and unboundedness absorb the fixed header cost and the finitely
many short prefixes. -/
private lemma pm_coding {f : ℕ → ℕ} (hmono : Monotone f)
    (hunb : ∀ B, ∃ n, B ≤ f n)
    (D : ℕ × List ℕ →. BitString) (hD : Partrec D) (w : CantorSeq) (a : ℕ → List ℕ)
    (hlen : ∀ n, 8 * (a n).length ≤ f n)
    (hval : ∀ n i, i < (a n).length → (a n).getD i 0 ≤ n + 1)
    (hdec : ∀ n, cantorPrefix w n ∈ D (n, a n)) (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℝ, ∀ n : ℕ,
      ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ f n * Real.logb 2 n + c := by
  let F : Map := fun p => D (pm_uncode p.1)
  have hF : isDecompressor F := (hD.comp pm_uncode_comp).comp
      Computable.fst
  obtain ⟨C, hC⟩ := hV.2 F hF
  have hK : ∀ n, (plainK V (cantorPrefix w n)).toNat ≤
      (pm_code n (a n)).length + C := by
    intro n
    have hprod : produces F (pm_code n (a n)) []
        (cantorPrefix w n) := by
      change cantorPrefix w n ∈ D (pm_uncode
          (pm_code n (a n)))
      rw [pm_uncode_code]
      exact hdec n
    have hprog : plainK F (cantorPrefix w n) ≤ ((pm_code n
        (a n)).length : ℕ∞) :=
      (condK_le_iff F _ [] _).2 ⟨pm_code n (a n), le_rfl,
          hprod⟩
    apply ENat.toNat_le_of_le_natCast
    calc
      plainK V (cantorPrefix w n) ≤ plainK F (cantorPrefix w n) + (C : ℕ∞) := hC _ []
      _ ≤ ((pm_code n (a n)).length : ℕ∞) + (C : ℕ∞) :=
          add_le_add hprog le_rfl
      _ = (((pm_code n (a n)).length + C : ℕ) : ℕ∞) := by
        simp
  obtain ⟨N, hN⟩ := hunb 56
  let B : ℕ := ((Finset.range (max N 2)).sum fun n =>
    (pm_code n (a n)).length) + C
  refine ⟨B, fun n => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.logb 2 n :=
    le_trans (Nat.cast_nonneg (Nat.log 2 n)) (Real.natLog_le_logb n 2)
  by_cases hn : max N 2 ≤ n
  · have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hf56 : 56 ≤ f n := hN.trans (hmono ((le_max_left _ _).trans hn))
    have hL : 1 ≤ Nat.log 2 n := by
      have h := Nat.log_monotone (b := 2) hn2
      norm_num at h ⊢
      exact h
    have hcoeff : 7 * ((a n).length + 1) ≤ f n := by have := hlen n; omega
    have hcode : (pm_code n (a n)).length ≤ f n * Nat.log 2
        n := by
      calc
        (pm_code n (a n)).length ≤ ((a n).length + 1) *
            (2 * Nat.log 2 n + 5) := pm_code_length n _
            (hval n)
        _ ≤ ((a n).length + 1) * (7 * Nat.log 2 n) := Nat.mul_le_mul_left _ (by omega)
        _ = (7 * ((a n).length + 1)) * Nat.log 2 n := by ring
        _ ≤ f n * Nat.log 2 n := Nat.mul_le_mul_right _ hcoeff
    have hnat : (plainK V (cantorPrefix w n)).toNat ≤ f n * Nat.log 2 n + B := by
      have := hK n
      have hBC : C ≤ B := Nat.le_add_left _ _
      omega
    have hr : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ (f n : ℝ) * (Nat.log 2 n : ℝ) + B := by
      exact_mod_cast hnat
    exact hr.trans (add_le_add (mul_le_mul_of_nonneg_left
      (Real.natLog_le_logb n 2) (Nat.cast_nonneg _)) le_rfl)
  · have hsmall : (pm_code n (a n)).length ≤
        (Finset.range (max N 2)).sum fun n => (pm_code n
                                                (a n)).length :=
      Finset.single_le_sum (fun j hj => Nat.zero_le ((pm_code
                                          j (a j)).length))
        (Finset.mem_range.2 (Nat.lt_of_not_ge hn))
    have hnat : (plainK V (cantorPrefix w n)).toNat ≤ B := by have := hK n; omega
    exact le_trans (by exact_mod_cast hnat) (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _)
        hlog))

/-- Step 1 of the proof of
`pm_exists_random`: Read
the multiplier for the observed bit from a pair of gambling factors. -/
private def pm_factor (v : ℚ × ℚ) (b : Bool) : ℚ :=
    bif b then v.2 else v.1

/-- Step 1 of the proof of
`pm_exists_random`:
Multiply the partial gambling factors along a finite input, starting with capital one. -/
private def pm_loop (G : BitString →. (ℚ × ℚ))
    (x : BitString) : ℕ → Part ℚ
  | 0 => Part.some 1
  | n + 1 => (pm_loop G x n).bind fun q =>
      (G (x.take n)).map fun v => q * pm_factor v
                                    (x.getD n false)

/-- Step 1 of the proof of
`pm_exists_random`: The
partial capital obtained by multiplying all gambling factors along the input. -/
private def pm_cap (G : BitString →. (ℚ × ℚ)) (x : BitString)
    : Part ℚ := pm_loop G x x.length

/-- Step 1 of the proof of
`pm_exists_random`:
Appending a bit leaves all earlier capital computations unchanged. -/
private lemma pm_loop_append (G : BitString →. (ℚ × ℚ))
    (x : BitString) (b : Bool) :
    ∀ n, n ≤ x.length → pm_loop G (x ++ [b]) n =
        pm_loop G x n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [pm_loop, pm_loop, ih (by omega), List.take_append_of_le_length (by omega),
      List.getD_append _ _ _ _ (by omega)]

/-- Step 1 of the proof of
`pm_exists_random`: The
capital of an appended bit is the old capital times the corresponding partial gambling factor. -/
private lemma pm_cap_append (G : BitString →. (ℚ × ℚ))
    (x : BitString) (b : Bool) :
    pm_cap G (x ++ [b]) =
        (pm_cap G x).bind fun q =>
      (G x).map fun v => q * pm_factor v b := by
  unfold pm_cap
  rw [List.length_append, List.length_singleton, pm_loop,
      pm_loop_append G x b _ le_rfl,
    List.take_append_of_le_length le_rfl, List.take_length,
    List.getD_append_right _ _ _ _ le_rfl]
  simp

/-- Step 1 of the proof of
`pm_exists_random`: Either
child capital is defined exactly when the parent capital and the next pair of factors are defined.
-/
private lemma pm_cap_dom (G : BitString →. (ℚ × ℚ))
    (x : BitString) (b : Bool) :
    (pm_cap G (x ++ [b])).Dom ↔
        (pm_cap G x).Dom ∧ (G x).Dom := by
  rw [pm_cap_append]
  simp only [Part.bind_dom, Part.map]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2⟩

/-- Step 1 of the proof of
`pm_exists_random`:
Nonnegative gambling factors summing to two produce a strong partial martingale, with prefix-closed
domain and simultaneous children. -/
private lemma pm_cap_strong (G : BitString →. (ℚ × ℚ))
    (hG : ∀ x v, v ∈ G x → 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 + v.2 = 2) : pm_Strong (pm_cap G) := by
  have hnonneg : ∀ x, ∀ n, ∀ q ∈ pm_loop G x n, 0 ≤ q := by
    intro x n
    induction n with
    | zero => intro q hq; have h : q = 1 := Part.mem_some_iff.1 hq; rw [h]; norm_num
    | succ n ih =>
      intro q hq
      obtain ⟨a, ha, hv⟩ := Part.mem_bind_iff.1 hq
      obtain ⟨p, hp, rfl⟩ := (Part.mem_map_iff _).1 hv
      have hh := hG _ p hp
      apply mul_nonneg (ih a ha)
      unfold pm_factor
      cases x.getD n false
      · exact hh.1
      · exact hh.2.1
  refine ⟨⟨fun x q hq => hnonneg x x.length q hq, ?_⟩,
      by simp [pm_cap,
           pm_loop], ?_⟩
  · intro x q q0 q1 hq hq0 hq1
    rw [pm_cap_append] at hq0 hq1
    obtain ⟨r0, hr0, hq0⟩ := Part.mem_bind_iff.1 hq0
    obtain ⟨r1, hr1, hq1⟩ := Part.mem_bind_iff.1 hq1
    obtain ⟨v0, hv0, hv0q⟩ := (Part.mem_map_iff _).1 hq0
    obtain ⟨v1, hv1, hv1q⟩ := (Part.mem_map_iff _).1 hq1
    have er0 : r0 = q := Part.mem_unique hr0 hq
    have er1 : r1 = q := Part.mem_unique hr1 hq
    have ev : v1 = v0 := Part.mem_unique hv1 hv0
    have hf := (hG _ v0 hv0).2.2
    simp only [pm_factor, Bool.cond_false, Bool.cond_true,
        er0, er1, ev] at hv0q hv1q
    have hmul := congrArg (fun z : ℚ => q * z) hf
    nlinarith only [hmul, hv0q, hv1q]
  · intro x b hb
    have hh := (pm_cap_dom G x b).1 hb
    exact ⟨hh.1, (pm_cap_dom G x false).2 hh,
        (pm_cap_dom G x true).2 hh⟩

/-- Step 1 of the proof of
`pm_exists_random`: A
uniformly partial recursive family of gambling factors gives a uniformly partial recursive family of
capitals. -/
private lemma pm_cap_partrec {G : ℕ × BitString →. (ℚ × ℚ)}
    (hG : Partrec G) :
    Partrec (fun p : ℕ × BitString => pm_cap
                                        (fun x => G (p.1, x)) p.2) := by
  let X := (ℕ × BitString) × (ℕ × ℚ)
  have hin : Computable (fun p : X => (p.1.1, p.1.2.take p.2.1)) :=
    (Computable.fst.comp Computable.fst).pair
      (Primrec.list_take.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.fst))
  have hget : Computable (fun p : X => p.1.2.getD p.2.1 false) :=
    (Primrec.list_getD false).to_comp.comp (Computable.snd.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hselect : Computable₂ (fun (p : X) (v : ℚ × ℚ) =>
      pm_factor v (p.1.2.getD p.2.1 false)) := by
    have H : Computable (fun p : X × (ℚ × ℚ) =>
        bif p.1.1.2.getD p.1.2.1 false then p.2.2 else p.2.1) :=
      Computable.cond (hget.comp Computable.fst)
        (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd)
    exact H.of_eq (fun p => rfl)
  have hout : Computable₂ (fun (p : X) (v : ℚ × ℚ) =>
      p.2.2 * pm_factor v (p.1.2.getD p.2.1 false)) :=
    computable₂_ratMul.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)) hselect
  have hh := (hG.comp hin).map hout
  have hf : Computable (fun p : ℕ × BitString => p.2.length) :=
    Computable.list_length.comp Computable.snd
  have hg : Partrec (fun _ : ℕ × BitString => Part.some (1 : ℚ)) := (Computable.const 1).partrec
  have H := Partrec.nat_rec hf hg hh.to₂
  refine H.of_eq fun p => ?_
  unfold pm_cap
  generalize p.2.length = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [pm_loop, ih]

/-- Step 1 of the proof of
`pm_exists_random`: For
positive capitals q, boundedness of both the clipped-ratio product and the product doubling at
ratios greater than two forces q to be bounded. The latter product bounds the number of excessive
ratios; after the last one, the former product is proportional to q. -/
private lemma pm_clipped_bounded (q a b : ℕ → ℚ) (hq : ∀ n,
    0 < q n)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ n, a (n + 1) = a n * min (q (n + 1) / q n) 2)
    (hb : ∀ n, b (n + 1) = b n * (if 2 < q (n + 1) / q n then 2 else 1))
    (A B : ℕ) (hA : ∀ n, a n ≤ A) (hB : ∀ n, b n ≤ B) :
    ∃ C : ℚ, ∀ n, q n ≤ C := by
  classical
  let c : ℕ → ℕ := fun n => ((Finset.range n).filter fun j => 2 < q (j + 1) / q j).card
  have hcs : ∀ n, c (n + 1) = c n + (if 2 < q (n + 1) / q n then 1 else 0) := by
    intro n
    by_cases hh : 2 < q (n + 1) / q n
    · simp [c, Finset.range_add_one, Finset.filter_insert, hh]
    · simp [c, Finset.range_add_one, Finset.filter_insert, hh]
  have hcm : Monotone c := monotone_nat_of_le_succ fun n =>
    by have := hcs n; split_ifs at this <;> omega
  have hbp : ∀ n, b n = (2 : ℚ) ^ c n := by
    intro n
    induction n with
    | zero => simp [hb0, c]
    | succ n ih =>
      rw [hb, ih, hcs]
      split_ifs <;> simp [pow_succ]
  have hcb : ∀ n, c n ≤ B := by
    intro n
    have hcq : (c n : ℚ) ≤ (2 : ℚ) ^ c n := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := c n)))
    rw [← hbp n] at hcq
    exact_mod_cast hcq.trans (hB n)
  have hcB : BddAbove (Set.range c) := ⟨B, fun _ hn => by obtain ⟨n, rfl⟩ := hn; exact hcb n⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem (show (Set.range c).Nonempty from ⟨c 0, 0, rfl⟩) hcB
  have hNeq : c N = sSup (Set.range c) := hN
  have hcmax : ∀ n, c n ≤ c N := fun n => by rw [hNeq]; exact le_csSup hcB ⟨n, rfl⟩
  have hstop : ∀ n, N ≤ n → ¬ 2 < q (n + 1) / q n := by
    intro n hn hh
    have hh1 := hcs n
    rw [ite_eq_left hh] at hh1
    have hh2 := hcmax (n + 1)
    have hh3 := hcm hn
    omega
  have hap : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => rw [ha0]; norm_num
    | succ n ih => rw [ha]; exact mul_pos ih (lt_min (div_pos (hq _) (hq _)) (by norm_num))
  have htel : ∀ j, a (N + j) * q N = a N * q (N + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show N + (j + 1) = N + j + 1 from by omega, ha,
        min_eq_left (le_of_not_gt (hstop (N + j) (by omega)))]
      calc
        a (N + j) * (q (N + j + 1) / q (N + j)) * q N =
            (a (N + j) * q N) * q (N + j + 1) / q (N + j) := by ring
        _ = (a N * q (N + j)) * q (N + j + 1) / q (N + j) := by rw [ih]
        _ = a N * q (N + j + 1) := by field_simp [(hq (N + j)).ne']
  refine ⟨max ((A : ℚ) * q N / a N) (∑ n ∈ Finset.range N, q n), fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hnt := htel (n - N)
    rw [show N + (n - N) = n from by omega] at hnt
    have hqeq : q n = a n * q N / a N := (eq_div_iff (hap N).ne').2 (by linarith only [hnt])
    rw [hqeq]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hA n) (hq N).le)
        (hap N).le).trans (le_max_left _ _)
  · exact (Finset.single_le_sum (fun j hj => (hq j).le) (Finset.mem_range.2
      (Nat.lt_of_not_ge hn))).trans (le_max_right _ _)

/-- Step 1 of the proof of
`pm_exists_random`: The
clipped-ratio strategy and the excessive-ratio strategy, with their two factors aligned to the first
halting child. -/
private def pm_pair (s c : Bool) (r : ℚ) : ℚ × ℚ :=
  if s then
    if 2 < r then (if c then (0, 2) else (2, 0)) else (1, 1)
  else
    let z := min (max r 0) 2
    if c then (2 - z, z) else (z, 2 - z)

/-- Step 1 of the proof of
`pm_exists_random`: For
every program output, both normalized strategies have nonnegative factors whose sum is two. -/
private lemma pm_pair_good (s c : Bool) (r : ℚ) :
    0 ≤ (pm_pair s c r).1 ∧ 0 ≤
        (pm_pair s c r).2 ∧
        (pm_pair s c r).1 +
        (pm_pair s c r).2 = 2 := by
  have hz0 : (0 : ℚ) ≤ min (max r 0) 2 := le_min (le_max_right _ _) (by norm_num)
  have hz2 : min (max r 0) 2 ≤ (2 : ℚ) := min_le_right _ _
  cases s
  · cases c
    · exact ⟨hz0, by dsimp [pm_pair]; linarith,
        by dsimp [pm_pair]; ring⟩
    · exact ⟨by dsimp [pm_pair]; linarith, hz0,
        by dsimp [pm_pair]; ring⟩
  · by_cases hh : 2 < r <;> cases c <;> norm_num [pm_pair,
      hh]


/-- Step 1 of the proof of
`pm_exists_random`: The
local ratio calculation: if two child values are defined, fairness determines the other factor; on
the unique defined child the first factor is clipped at two and the second strategy detects
excessive ratios. -/
private lemma pm_pair_path (p q r : ℚ) (c b : Bool)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsame : c = b → q = r) (hdiff : c ≠ b → q + r = 2 * p) :
    pm_factor (pm_pair false c ((r + 1) * pm_recip p)) b = min ((q + 1) / (p + 1)) 2 ∧
    pm_factor (pm_pair true c ((r + 1) * pm_recip p)) b =
      (if 2 < (q + 1) / (p + 1) then 2 else 1) := by
  have hp1 : 0 < p + 1 := by linarith
  have hqr : 0 < (q + 1) / (p + 1) := div_pos (by linarith) hp1
  have hrr : 0 < (r + 1) / (p + 1) := div_pos (by linarith) hp1
  have hratio : (r + 1) * pm_recip p = (r + 1) / (p + 1) :=
      by rw [pm_recip_eq hp]; ring
  rw [hratio]
  by_cases hcb : c = b
  · have h := hsame hcb
    subst c
    subst r
    cases b <;> simp [pm_pair,
        pm_factor, max_eq_left hqr.le] <;> split_ifs <;> rfl
  · have hf := hdiff hcb
    have hsum : (q + 1) / (p + 1) + (r + 1) / (p + 1) = 2 := by
      rw [← add_div]
      apply (div_eq_iff hp1.ne').2
      linarith
    have hq2 : (q + 1) / (p + 1) ≤ 2 := by linarith
    have hr2 : (r + 1) / (p + 1) ≤ 2 := by linarith
    have her : ¬ 2 < (r + 1) / (p + 1) := not_lt.2 hr2
    have heq : ¬ 2 < (q + 1) / (p + 1) := not_lt.2 hq2
    cases c <;> cases b
    all_goals first
      | exact (hcb rfl).elim
      | simp [pm_pair,
          pm_factor, her, heq, max_eq_left hrr.le,
          min_eq_left hr2,
          min_eq_left hq2]; linarith [hsum]

/-- Step 1 of the proof of
`pm_exists_random`: The
two normalized factor pairs are computable from the strategy bit, chosen child, and rational ratio.
-/
private lemma pm_pair_comp : Computable (fun p : Bool ×
    Bool × ℚ => pm_pair p.1 p.2.1 p.2.2) := by
  have hmax : Computable (fun r : ℚ => max r 0) := by
    have H := Computable.cond (pm_rat_le_comp.comp
        Computable.id (Computable.const 0))
      (Computable.const 0) Computable.id
    exact H.of_eq fun r => by by_cases hr : r ≤ 0 <;> simp [hr, le_of_not_ge]
  have hclip : Computable (fun r : ℚ => min (max r 0) 2) := by
    have H := Computable.cond (pm_rat_le_comp.comp hmax
        (Computable.const 2)) hmax (Computable.const 2)
    exact H.of_eq fun r => by by_cases hr : max r 0 ≤ 2 <;> simp [hr, le_of_not_ge]
  let X := Bool × Bool × ℚ
  have hz : Computable (fun p : X => min (max p.2.2 0) 2) :=
      hclip.comp (Computable.snd.comp Computable.snd)
  have hc : Computable (fun p : X => p.2.1) := Computable.fst.comp Computable.snd
  have hother : Computable (fun p : X => 2 - min (max p.2.2 0) 2) :=
    computable₂_ratSub.comp (Computable.const 2) hz
  have hfalse : Computable (fun p : X =>
      if p.2.1 then (2 - min (max p.2.2 0) 2, min (max p.2.2 0) 2)
      else (min (max p.2.2 0) 2, 2 - min (max p.2.2 0) 2)) :=
    (Computable.cond hc (hother.pair hz) (hz.pair hother)).of_eq (fun p => by cases p.2.1 <;> rfl)
  have hlt : Computable (fun p : X => decide (2 < p.2.2)) := by
    have hle : Computable (fun p : X => decide (p.2.2 ≤ 2)) :=
      pm_rat_le_comp.comp (Computable.snd.comp Computable.snd) (Computable.const 2)
    have H := Primrec.not.to_comp.comp hle
    exact H.of_eq fun p => by simp [← not_le]
  have hconc : Computable (fun p : X => if p.2.1 then ((0, 2) : ℚ × ℚ) else (2, 0)) :=
    (Computable.cond hc (Computable.const (0, 2)) (Computable.const (2, 0))).of_eq
        (fun p => by cases p.2.1 <;> rfl)
  have htrue : Computable (fun p : X =>
      if 2 < p.2.2 then (if p.2.1 then ((0, 2) : ℚ × ℚ) else (2, 0)) else (1, 1)) :=
    (Computable.cond hlt hconc (Computable.const (1, 1))).of_eq (fun p => by simp)
  exact (Computable.cond Computable.fst htrue hfalse).of_eq (fun p => by cases p.1 <;> rfl)

/-- Step 1 of the proof of
`pm_exists_random`: Run a
natural program on the encoded input and decode its output into an arbitrary primcodable type. -/
private def pm_eval {α β : Type} [Primcodable α]
    [Primcodable β]
    (c : Nat.Partrec.Code) (a : α) : Part β :=
  (c.eval (Encodable.encode a)).bind fun n => Part.ofOption (Encodable.decode (α := β) n)

/-- Step 1 of the proof of
`pm_exists_random`:
Program evaluation followed by decoding is partial recursive jointly in the program and input. -/
private lemma pm_eval_partrec {α β : Type} [Primcodable α]
    [Primcodable β] :
    Partrec (fun p : Nat.Partrec.Code × α => pm_eval (β := β)
                                               p.1 p.2) := by
  have heval : Partrec (fun p : Nat.Partrec.Code × α => p.1.eval (Encodable.encode p.2)) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd)
  have hdec : Partrec (fun p : (Nat.Partrec.Code × α) ×
      ℕ => Part.ofOption (Encodable.decode (α := β) p.2)) :=
    Computable.ofOption (Computable.decode.comp Computable.snd)
  exact heval.bind hdec.to₂

/-- Step 1 of the proof of
`pm_exists_random`: Every
partial recursive map is exactly represented by an encoded program, with no additional properties
asserted of the chosen code. -/
private lemma pm_eval_complete {α β : Type} [Primcodable α]
    [Primcodable β]
    (m : α →. β) (hm : Partrec m) :
    ∃ c : Nat.Partrec.Code, ∀ a, pm_eval c a = m a := by
  have hnat : Nat.Partrec (fun n => Part.bind (Encodable.decode (α := α) n) fun a =>
                                      (m a).map Encodable.encode) := hm
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hnat
  refine ⟨c, fun a => ?_⟩
  unfold pm_eval
  rw [hc]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
  ext b
  simp only [Part.mem_bind_iff, Part.mem_map_iff, Part.mem_ofOption, Option.mem_def]
  constructor
  · rintro ⟨n, ⟨r, hr, rfl⟩, hdec⟩
    have heq : r = b := by simpa only [Encodable.encodek, Option.some_inj] using hdec
    exact heq ▸ hr
  · intro hb
    exact ⟨Encodable.encode b, ⟨b, hb, rfl⟩, Encodable.encodek b⟩

/-- Step 1 of the proof of
`pm_exists_random`: The
universal enumeration of partial recursive rational functions on binary strings. -/
private def pm_universal (p : ℕ × BitString) : Part ℚ :=
  pm_eval (Denumerable.ofNat Nat.Partrec.Code p.1) p.2

/-- Step 1 of the proof of
`pm_exists_random`: The
universal enumeration is partial recursive jointly in the index and string. -/
private lemma pm_universal_partrec : Partrec
    pm_universal := by
  have hc : Computable (fun p : ℕ × BitString => Denumerable.ofNat Nat.Partrec.Code p.1) :=
    (Primrec.ofNat Nat.Partrec.Code).to_comp.comp Computable.fst
  have hpair : Computable (fun p : ℕ × BitString => (Denumerable.ofNat Nat.Partrec.Code p.1, p.2))
      :=
    hc.pair Computable.snd
  have H := (pm_eval_partrec (α := BitString) (β := ℚ)).comp
      hpair
  exact H.of_eq (fun p => rfl)

/-- Step 1 of the proof of
`pm_exists_random`: Every
partial recursive rational function occurs exactly in the universal enumeration. -/
private lemma pm_universal_complete (m : BitString →. ℚ)
    (hm : Partrec m) :
    ∃ i, ∀ x, pm_universal (i, x) = m x := by
  obtain ⟨c, hc⟩ := pm_eval_complete m hm
  exact ⟨Encodable.encode c, fun x => by
    simpa only [pm_universal, Denumerable.ofNat_encode] using hc x⟩

/-- Step 1 of the proof of
`pm_exists_random`:
Dovetail the two child evaluations uniformly. The selected pair gives an actually defined child
value, and selection halts exactly when at least one child evaluation halts. -/
private lemma pm_select {U : ℕ × BitString →. ℚ}
    (hU : Partrec U) :
    ∃ C : ℕ × BitString →. (Bool × ℚ), Partrec C ∧
      (∀ p v, v ∈ C p → v.2 ∈ U (p.1, p.2 ++ [v.1])) ∧
      ∀ p, (C p).Dom ↔ (U (p.1, p.2 ++ [false])).Dom ∨ (U (p.1, p.2 ++ [true])).Dom := by
  have hu (b : Bool) : Partrec (fun p : ℕ × BitString => U (p.1, p.2 ++ [b])) := by
    have hpair : Computable (fun p : ℕ × BitString => (p.1, p.2 ++ [b])) :=
      Computable.fst.pair (Computable.list_append.comp Computable.snd (Computable.const [b]))
    exact hU.comp hpair
  have hc (b : Bool) : Partrec (fun p : ℕ × BitString =>
      (U (p.1, p.2 ++ [b])).map fun q => (b, q)) :=
    (hu b).map ((Computable.const b).pair Computable.snd).to₂
  obtain ⟨C, hC, hspec⟩ := Partrec.merge' (hc false) (hc true)
  refine ⟨C, hC, ?_, ?_⟩
  · intro p v hv
    rcases (hspec p).1 v hv with h | h
    all_goals obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff _).1 h; exact hq
  · intro p
    simpa only [Part.map] using (hspec p).2

/-- Step 1 of the proof of
`pm_exists_random`: Read
the parent and a dovetailed child value, add one, and form one of the two normalized gambling factor
pairs. -/
private def pm_gamble (U : ℕ × BitString →. ℚ)
    (C : ℕ × BitString →. (Bool × ℚ))
    (s : Bool) (p : ℕ × BitString) : Part (ℚ × ℚ) :=
  (U p).bind fun q => (C p).map fun v => pm_pair s v.1
                                           ((v.2 + 1) *
                                           pm_recip q)

/-- Step 1 of the proof of
`pm_exists_random`: For
either fixed strategy, the normalized partial gambling factors are uniformly partial recursive. -/
private lemma pm_gamble_partrec {U : ℕ × BitString →. ℚ}
    {C : ℕ × BitString →. (Bool × ℚ)}
    (hU : Partrec U) (hC : Partrec C) (s : Bool) : Partrec
        (pm_gamble U C s) := by
  let X := ℕ × BitString
  have hcpair : Computable (fun p : (X × ℚ) × (Bool × ℚ) =>
      (s, p.2.1, (p.2.2 + 1) * pm_recip p.1.2)) :=
    (Computable.const s).pair ((Computable.fst.comp Computable.snd).pair
      (computable₂_ratMul.comp
        (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd) (Computable.const 1))
        (pm_recip_comp.comp (Computable.snd.comp Computable.fst))))
  have hout := pm_pair_comp.comp hcpair
  have H := hU.bind ((hC.comp Computable.fst).map hout.to₂).to₂
  exact H.of_eq (fun p => rfl)

/-- Step 1 of the proof of
`pm_exists_random`: The
normalized partial gambling factors are nonnegative and exactly fair even for programs that do not
compute weak martingales. -/
private lemma pm_gamble_good (U : ℕ × BitString →. ℚ)
    (C : ℕ × BitString →. (Bool × ℚ))
    (s : Bool) (p : ℕ × BitString) (v : ℚ × ℚ)
        (hv : v ∈ pm_gamble U C s p) :
    0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 + v.2 = 2 := by
  obtain ⟨q, hq, hv⟩ := Part.mem_bind_iff.1 hv
  obtain ⟨v', hv', rfl⟩ := (Part.mem_map_iff _).1 hv
  exact pm_pair_good _ _ _

/-- Step 1 of the proof of
`pm_exists_random`: Apply
the local ratio calculation to three defined values of a weak partial martingale. -/
private lemma pm_weak_pair_path {m : BitString →. ℚ}
    (hm : pm_IsPartialMartingale m)
    (x : BitString) (p q r : ℚ) (c b : Bool) (hp : p ∈ m x)
    (hq : q ∈ m (x ++ [b])) (hr : r ∈ m (x ++ [c])) :
    pm_factor (pm_pair false c ((r + 1) * pm_recip p)) b = min ((q + 1) / (p + 1)) 2 ∧
    pm_factor (pm_pair true c ((r + 1) * pm_recip p)) b =
      (if 2 < (q + 1) / (p + 1) then 2 else 1) := by
  refine pm_pair_path p q r c b (hm.nonneg _ _ hp)
      (hm.nonneg _ _ hq) (hm.nonneg _ _ hr) ?_ ?_
  · intro hcb
    subst c
    exact Part.mem_unique hq hr
  · intro hcb
    cases c <;> cases b
    · exact (hcb rfl).elim
    · have hf := hm.fair x p r q hp hr hq
      linarith only [hf]
    · have hf := hm.fair x p q r hp hq hr
      linarith only [hf]
    · exact (hcb rfl).elim

/-- Step 1 of the proof of
`pm_exists_random`: At a
defined input the zero completion is itself a value of the partial function. -/
private lemma pm_value_mem (m : BitString →. ℚ)
    (x : BitString) (hd : (m x).Dom) :
    pm_value m x ∈ m x := by
  classical
  rw [pm_value, Part.getOrElse_of_dom _ hd]
  exact Part.get_mem hd

/-- Step 1 of the proof of
`pm_exists_random`: A
partial capital defined on every prefix that does not win has a natural upper bound on all its
prefix values. -/
private lemma pm_nowin_bound (m : BitString →. ℚ)
    (w : CantorSeq)
    (hd : ∀ n, (m (cantorPrefix w n)).Dom)
        (hnot : ¬ pm_PartialWins m w) :
    ∃ A : ℕ, ∀ n, pm_value m (cantorPrefix w n) ≤ A := by
  have hbd : BddAbove {r : ℝ | ∃ n, ∃ q ∈ m (cantorPrefix w n), (q : ℝ) = r} := by
    by_contra h
    exact hnot ⟨hd, h⟩
  obtain ⟨B, hB⟩ := hbd
  obtain ⟨A, hA⟩ := exists_nat_gt B
  refine ⟨A, fun n => ?_⟩
  have hval : (pm_value m (cantorPrefix w n) : ℝ) ≤ B :=
    hB ⟨n, pm_value m (cantorPrefix w n),
        pm_value_mem m _ (hd n), rfl⟩
  exact_mod_cast hval.trans hA.le

/-- Step 1 of the proof of
`pm_exists_random`: Every
weak martingale win transfers to one of the two strong capital products: along a fully defined path
their multipliers are respectively the true ratio clipped at two and a doubling precisely at
excessive true ratios. -/
private lemma pm_normalizes (U : ℕ × BitString →. ℚ)
    (C : ℕ × BitString →. (Bool × ℚ))
    (hC : ∀ p v, v ∈ C p → v.2 ∈ U (p.1, p.2 ++ [v.1]))
    (hCd : ∀ p, (C p).Dom ↔ (U (p.1, p.2 ++ [false])).Dom ∨ (U (p.1, p.2 ++ [true])).Dom)
    (i : ℕ) (hm : pm_IsPartialMartingale (fun x => U (i, x)))
        (w : CantorSeq)
    (hwin : pm_PartialWins (fun x => U (i, x)) w) :
    pm_PartialWins (pm_cap (fun x => pm_gamble U C false (i, x))) w ∨
      pm_PartialWins (pm_cap (fun x => pm_gamble U C true (i, x))) w := by
  classical
  let m : BitString →. ℚ := fun x => U (i, x)
  let G : Bool → BitString →. (ℚ × ℚ) := fun s x => pm_gamble
                                                      U C s (i, x)
  let S : Bool → BitString →. ℚ := fun s => pm_cap (G s)
  let p := fun n => pm_value m (cantorPrefix w n)
  have hp : ∀ n, p n ∈ m (cantorPrefix w n) :=
      fun n => pm_value_mem m _ (hwin.1 n)
  have hpnext : ∀ n, p (n + 1) ∈ m (cantorPrefix w n ++ [w n]) := by
    intro n
    simpa only [cantorPrefix_succ] using hp (n + 1)
  have hc : ∀ n, (C (i, cantorPrefix w n)).Dom := by
    intro n
    apply (hCd _).2
    cases hb : w n
    · exact Or.inl (by simpa only [cantorPrefix_succ, hb] using hwin.1 (n + 1))
    · exact Or.inr (by simpa only [cantorPrefix_succ, hb] using hwin.1 (n + 1))
  let c := fun n => (C (i, cantorPrefix w n)).get (hc n)
  have hcmem : ∀ n, c n ∈ C (i, cantorPrefix w n) := fun n => Part.get_mem (hc n)
  let v := fun s n => pm_pair s (c n).1 (((c n).2 + 1) *
                        pm_recip (p n))
  have hv : ∀ s n, v s n ∈ G s (cantorPrefix w n) := by
    intro s n
    exact Part.mem_bind_iff.2 ⟨p n, hp n, Part.mem_map _ (hcmem n)⟩
  have hd : ∀ s n, (S s (cantorPrefix w n)).Dom := by
    intro s n
    induction n with
    | zero => simp [S, pm_cap,
                pm_loop, cantorPrefix]
    | succ n ih =>
      rw [cantorPrefix_succ]
      exact (pm_cap_dom (G s) _ _).2 ⟨ih, (hv s n).1⟩
  have hrec : ∀ s n, pm_value (S s) (cantorPrefix w (n + 1))
      =
      pm_value (S s) (cantorPrefix w n) *
          pm_factor (v s n) (w n) := by
    intro s n
    apply pm_value_eq
    rw [cantorPrefix_succ]
    change _ ∈ pm_cap (G s) (cantorPrefix w n ++ [w n])
    rw [pm_cap_append]
    exact Part.mem_bind_iff.2 ⟨pm_value (S s)
        (cantorPrefix w n),
      pm_value_mem (S s) _ (hd s n), Part.mem_map _ (hv s n)⟩
  have hf : ∀ n,
      pm_factor (v false n) (w n) = min ((p (n + 1) + 1) /
          (p n + 1)) 2 ∧
      pm_factor (v true n) (w n) = (if 2 < (p (n + 1) + 1) /
          (p n + 1) then 2 else 1) := by
    intro n
    exact pm_weak_pair_path hm _ _ _ _ _ _ (hp n) (hpnext n)
        (hC _ _ (hcmem n))
  by_contra hnone
  have hno (s : Bool) : ¬ pm_PartialWins (S s) w := by
    intro h
    cases s
    · exact hnone (Or.inl h)
    · exact hnone (Or.inr h)
  obtain ⟨A, hA⟩ := pm_nowin_bound (S false) w (hd false)
      (hno false)
  obtain ⟨B, hB⟩ := pm_nowin_bound (S true) w (hd true)
      (hno true)
  obtain ⟨K, hK⟩ := pm_clipped_bounded (fun n => p n + 1)
    (fun n => pm_value (S false) (cantorPrefix w n))
    (fun n => pm_value (S true) (cantorPrefix w n))
    (fun n => by have := hm.nonneg _ _ (hp n); linarith)
    (by simp [S, pm_value, pm_cap, pm_loop, cantorPrefix])
    (by simp [S, pm_value, pm_cap, pm_loop, cantorPrefix])
    (fun n => by rw [hrec, (hf n).1]) (fun n => by rw [hrec, (hf n).2]) A B hA hB
  apply hwin.2
  refine ⟨(K : ℝ), ?_⟩
  rintro r ⟨n, q, hq, rfl⟩
  have heq : p n = q := pm_value_eq m _ hq
  have hqK : q ≤ K := by have := hK n; rw [heq] at this; linarith
  exact_mod_cast hqK

/-- Step 1 of the proof of
`pm_exists_random`: The
normalized gambling factors are partial recursive jointly in the choice of strategy and the program
input. -/
private lemma pm_gamble_both_partrec {U : ℕ × BitString →. ℚ}
    {C : ℕ × BitString →. (Bool × ℚ)}
    (hU : Partrec U) (hC : Partrec C) :
    Partrec (fun p : Bool × ℕ × BitString => pm_gamble U C
                                               p.1 p.2) := by
  have ht := (pm_gamble_partrec hU hC true).comp
      (Computable.snd (α := Bool))
  have hf := (pm_gamble_partrec hU hC false).comp
      (Computable.snd (α := Bool))
  exact (Partrec.cond Computable.fst ht hf).of_eq (fun p => by cases p.1 <;> rfl)

/-- Step 1 of the proof of
`pm_exists_random`:
Uniformly enumerate strong partial martingales sufficient to detect every win by a weak partial
computable martingale, by normalizing a universal program enumeration and interleaving the two
strategies. The strong property includes prefix closure and simultaneous definedness of the
children. -/
private lemma pm_strong_cover :
    ∃ M : ℕ → BitString →. ℚ,
      Partrec (fun p : ℕ × BitString => M p.1 p.2) ∧
      (∀ i, pm_Strong (M i)) ∧
      ∀ m : BitString →. ℚ, Partrec m →
          pm_IsPartialMartingale m →
        ∀ w, pm_PartialWins m w → ∃ i,
            pm_PartialWins (M i) w := by
  obtain ⟨C, hC, hCv, hCd⟩ := pm_select
      pm_universal_partrec
  let G : ℕ × BitString →. (ℚ × ℚ) := fun p =>
    pm_gamble pm_universal C (decide ((Nat.unpair p.1).2 = 1)) ((Nat.unpair p.1).1, p.2)
  have hidx : Computable (fun p : ℕ × BitString =>
      (decide ((Nat.unpair p.1).2 = 1), (Nat.unpair p.1).1, p.2)) := by
    have hu1 : Computable (fun p : ℕ × BitString => (Nat.unpair p.1).1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).to_comp
    have hu2 : Computable (fun p : ℕ × BitString => (Nat.unpair p.1).2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to_comp
    have hbool : Computable (fun p : ℕ × BitString => decide ((Nat.unpair p.1).2 = 1)) :=
      (Primrec.eq (α := ℕ)).decide.to_comp.comp hu2 (Computable.const 1)
    exact hbool.pair (hu1.pair Computable.snd)
  have hg := (pm_gamble_both_partrec
      pm_universal_partrec hC).comp hidx
  have hG : Partrec G := hg.of_eq (fun _ => rfl)
  let M : ℕ → BitString →. ℚ := fun i => pm_cap
                                           (fun x => G (i, x))
  have hmc := pm_cap_partrec hG
  refine ⟨M, hmc.of_eq (fun _ => rfl), ?_, ?_⟩
  · intro i
    apply pm_cap_strong
    intro x v hv
    exact pm_gamble_good pm_universal C _ _ v hv
  · intro m hm hmart w hwin
    obtain ⟨i, hi⟩ := pm_universal_complete m hm
    have heq : (fun x => pm_universal (i, x)) = m :=
        funext hi
    have hmi : pm_IsPartialMartingale
        (fun x => pm_universal (i, x)) := by
          rw [heq]; exact hmart
    have hwi : pm_PartialWins
        (fun x => pm_universal (i, x)) w := by
          rw [heq]; exact hwin
    rcases pm_normalizes pm_universal C hCv hCd i hmi w hwi with h0 | h1
    · refine ⟨Nat.pair i 0, ?_⟩
      simpa only [M, G, Nat.unpair_pair, show ¬(0 : ℕ) = 1 from by decide, decide_false] using h0
    · refine ⟨Nat.pair i 1, ?_⟩
      simpa only [M, G, Nat.unpair_pair, decide_true] using h1

/-- Step 2 of the proof of `exists_isMisesChurchDaleyRandom_plainK_le`: For a
non-decreasing unbounded computable `f` there is a partial-computably random sequence whose `n`-bit
prefix has complexity at most `f(n) log n + O(1)`. -/
private lemma pm_exists_random
    {f : ℕ → ℕ} (hf : Computable f)
    (hmono : Monotone f) (hunb : ∀ B, ∃ n, B ≤ f n) (V : Map) (hV : isOptimalConditional V) :
    ∃ w, pm_IsPartialComputablyRandom w ∧ ∃ c : ℝ, ∀ n : ℕ,
      ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ f n * Real.logb 2 n + c := by
  obtain ⟨M, hcM, hM, hcover⟩ := pm_strong_cover
  obtain ⟨k, t, hk, ht, hk0, hkt, hkf⟩ :=
    pm_schedule hf hmono hunb
  let w := pm_seq M k t
  have hw : pm_IsPartialComputablyRandom w := by
    intro m hm hmart hwin
    obtain ⟨i, hi⟩ := hcover m hm hmart w hwin
    exact pm_avoids hM k t hk0 hkt i hi
  obtain ⟨a, halen, haval, hacut⟩ :=
    pm_advice hM k w
  obtain ⟨D, hD, hdec⟩ :=
    pm_decoder hM hcM k t hk ht hkt
  refine ⟨w, hw, pm_coding
    hmono hunb D hD w a ?_ ?_ ?_ V hV⟩
  · intro n
    rw [halen n]
    exact hkf n
  · intro n i hi
    exact haval n i (by rwa [halen n] at hi)
  · intro n
    exact hdec n (a n) (hacut n)

/-- **SUV Theorem 189, p. 289 (Merkle).**  For a total non-decreasing unbounded computable `f` there
is a Mises-Church-Daley random sequence whose `n`-bit prefix has complexity at most
`f(n) log n + O(1)`. -/
theorem exists_isMisesChurchDaleyRandom_plainK_le {f : ℕ → ℕ} (hf : Computable f)
    (hmono : Monotone f) (hunb : ∀ B, ∃ n, B ≤ f n) (V : Map) (hV : isOptimalConditional V) :
    ∃ w, IsMisesChurchDaleyRandom w ∧ ∃ c : ℝ, ∀ n : ℕ,
      ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ f n * Real.logb 2 n + c := by
  obtain ⟨w, hw, hc⟩ :=
      pm_exists_random hf hmono
      hunb V hV
  exact ⟨w, pm_of_random hw, hc⟩

/-! ### Partial martingales -/

/-- **SUV p. 290.**  A *partial martingale*, for the uniform measure: a partial function with
rational non-negative values, satisfying the martingale equation whenever all three quantities are
defined. -/
structure IsPartialMartingale (m : BitString →. ℚ) : Prop where
  nonneg : ∀ x, ∀ q ∈ m x, 0 ≤ q
  fair : ∀ x q q₀ q₁, q ∈ m x → q₀ ∈ m (x ++ [false]) → q₁ ∈ m (x ++ [true]) → q = (q₀ + q₁) / 2

/-- **SUV p. 290.**  A partial martingale *wins* on `ω` if it is defined on all prefixes of `ω` and
is unbounded on them. -/
def PartialWins (m : BitString →. ℚ) (w : CantorSeq) : Prop :=
  (∀ n, (m (cantorPrefix w n)).Dom) ∧
    ¬ BddAbove {r : ℝ | ∃ n, ∃ q ∈ m (cantorPrefix w n), (q : ℝ) = r}

/-- **SUV p. 290.**  *Partial-computably random* sequences: no computable partial martingale
wins. -/
def IsPartialComputablyRandom (w : CantorSeq) : Prop :=
  ∀ m : BitString →. ℚ, Partrec m → IsPartialMartingale m → ¬ PartialWins m w

/-- Step 2 of the proof of `isMisesChurchDaleyRandom_of_isPartialComputablyRandom`:
Converting a partial rule and a total rational martingale into a partial martingale. -/
private lemma pm2_partialMartingaleOfRule_partrec
    {r : BitString →. Bool} (hr : Partrec r)
    {M : BitString → ℚ} (hM_comp : Computable M)
    (hM_nonneg : ∀ x, 0 ≤ M x)
    (hM_fair : ∀ x, M x = (M (x ++ [false]) + M (x ++ [true])) / 2) :
    ∃ m : BitString →. ℚ, Partrec m ∧ IsPartialMartingale m ∧
      (∀ x, (m x).Dom ↔ (∀ y, y <+: x → (r y).Dom)) ∧
      (∀ x q, q ∈ m x → (m x).Dom ∧ q = M (selectedBits (partialRuleSet r) x)) := by
  let m : BitString →. ℚ := fun x =>
    (r x).bind (fun _ => (isMisesChurchDaleyRandom_of_selectStream_selPart r x).map M)
  have hsel : ∀ x s, s ∈ isMisesChurchDaleyRandom_of_selectStream_selPart r x ↔
      (∀ n < x.length, (r (x.take n)).Dom) ∧ s = selectedBits (partialRuleSet r) x := by
    intro x s
    have := isMisesChurchDaleyRandom_of_selectStream_stage r x x.length
      (le_refl _) s
    rwa [List.take_length] at this
  have hpre : ∀ x, (∀ y, y <+: x → (r y).Dom) ↔
      ((∀ n < x.length, (r (x.take n)).Dom) ∧ (r x).Dom) := by
    intro x
    constructor
    · intro h
      exact ⟨fun n hn => h _ (List.take_prefix n x), h x (List.prefix_refl x)⟩
    · rintro ⟨h1, h2⟩ y hy
      have hy_eq : y = x.take y.length := List.prefix_iff_eq_take.mp hy
      rw [hy_eq]
      rcases lt_or_eq_of_le (List.IsPrefix.length_le hy) with hlt | heq
      · exact h1 _ hlt
      · rw [heq, List.take_length]; exact h2
  have hmem : ∀ x q, q ∈ m x ↔
      (∀ y, y <+: x → (r y).Dom) ∧ q = M (selectedBits (partialRuleSet r) x) := by
    intro x q
    simp only [m, Part.mem_bind_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨b, hb, s, hs, rfl⟩
      obtain ⟨hd, rfl⟩ := (hsel x s).1 hs
      exact ⟨(hpre x).2 ⟨hd, Part.dom_iff_mem.2 ⟨b, hb⟩⟩, rfl⟩
    · rintro ⟨hd, rfl⟩
      obtain ⟨h1, h2⟩ := (hpre x).1 hd
      obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 h2
      exact ⟨b, hb, _, (hsel x _).2 ⟨h1, rfl⟩, rfl⟩
  have hdom : ∀ x, (m x).Dom ↔ (∀ y, y <+: x → (r y).Dom) := by
    intro x
    constructor
    · intro h
      obtain ⟨q, hq⟩ := Part.dom_iff_mem.1 h
      exact ((hmem x q).1 hq).1
    · intro h
      exact Part.dom_iff_mem.2 ⟨_, (hmem x _).2 ⟨h, rfl⟩⟩
  refine ⟨m, ?_, ⟨?_, ?_⟩, hdom, ?_⟩
  · have h1 := isMisesChurchDaleyRandom_of_selectStream_selPart_partrec
      r hr
    have h2 : Partrec (fun x : BitString =>
        (isMisesChurchDaleyRandom_of_selectStream_selPart r x).map M) :=
      Partrec.map h1 (hM_comp.comp Computable.snd).to₂
    exact Partrec.bind hr (h2.comp Computable.fst)
  · intro x q hq
    rw [((hmem x q).1 hq).2]
    exact hM_nonneg _
  · intro x q q₀ q₁ hq hq₀ hq₁
    rw [((hmem x q).1 hq).2, ((hmem _ q₀).1 hq₀).2, ((hmem _ q₁).1 hq₁).2,
      selectedBits_append_singleton, selectedBits_append_singleton]
    by_cases hx : x ∈ partialRuleSet r
    · simp only [hx, ite_true]
      exact hM_fair _
    · simp only [hx, ite_false, List.append_nil]
      ring
  · intro x q hq
    exact ⟨(hdom x).2 ((hmem x q).1 hq).1, ((hmem x q).1 hq).2⟩

/-- Step 3 of the proof of `isMisesChurchDaleyRandom_of_isPartialComputablyRandom`:
Selection bookkeeping showing partial wins. -/
private lemma pm2_partialWins
    {r : BitString →. Bool} {M : BitString → ℚ}
    {m : BitString →. ℚ} {w u : CantorSeq}
    (hm_dom : ∀ x, (m x).Dom ↔ (∀ y, y <+: x → (r y).Dom))
    (hm_val : ∀ x q, q ∈ m x → (m x).Dom ∧ q = M (selectedBits (partialRuleSet r) x))
    (h_sel : selectStream (partialRuleSet r) w = .infinite u)
    (hM_unbdd : ¬ BddAbove (Set.range fun n => ((M (cantorPrefix u n) : ℚ) : ℝ))) :
    PartialWins m w := by
  classical
  set R := partialRuleSet r with hR
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have hsel : selectStream R w = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  have hb : ¬ ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M := by
    intro hb
    rw [hsel] at h_sel
    unfold BitStream.ofPrefixSet at h_sel
    rw [dite_eq_left_of_eq_true (eq_true hb)] at h_sel
    exact BitStream.noConfusion h_sel
  have hunb : ∀ M : ℕ, ∃ t, M < (selectChain R w t).length := by
    intro M
    obtain ⟨x, ⟨t, hxt⟩, hxM⟩ := exists_mem_length_gt hb M
    exact ⟨t, lt_of_lt_of_le hxM hxt.length_le⟩
  have hsucc : ∀ t, selectChain R w (t + 1)
      = selectChain R w t ++ (if cantorPrefix w t ∈ R then [w t] else []) := by
    intro t
    unfold selectChain
    rw [cantorPrefix_succ, selectedBits_append_singleton]
  have hzero : selectChain R w 0 = [] := by
    simp [selectChain, selectedBits, selectedAux, cantorPrefix]
  have hstep : ∀ t, (selectChain R w (t + 1)).length ≤ (selectChain R w t).length + 1 := by
    intro t
    rw [hsucc]
    split_ifs <;> simp
  have hattain : ∀ n : ℕ, ∃ t, (selectChain R w t).length = n := by
    intro n
    have hex : ∃ t, n ≤ (selectChain R w t).length := by
      obtain ⟨t, ht⟩ := hunb n
      exact ⟨t, ht.le⟩
    obtain ⟨t₀, ht₀, hmin⟩ : ∃ t₀, n ≤ (selectChain R w t₀).length ∧
        ∀ s < t₀, (selectChain R w s).length < n :=
      ⟨Nat.find hex, Nat.find_spec hex, fun s hs => lt_of_not_ge (Nat.find_min hex hs)⟩
    rcases t₀ with _ | t₁
    · refine ⟨0, ?_⟩
      rw [hzero] at ht₀ ⊢
      simp at ht₀ ⊢
      omega
    · refine ⟨t₁ + 1, ?_⟩
      have h1 := hmin t₁ (Nat.lt_succ_self t₁)
      have h2 := hstep t₁
      omega
  have hlen : ∀ s, (selectChain R w s).length ≤ s := by
    intro s
    induction s with
    | zero => rw [hzero]; simp
    | succ s ih => have := hstep s; omega
  have hlate : ∀ n : ℕ, ∃ t, n ≤ t ∧ cantorPrefix w t ∈ R := by
    intro n
    by_contra hcon
    push Not at hcon
    have hconst : ∀ k, selectChain R w (n + k) = selectChain R w n := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← add_assoc, hsucc, ite_eq_right (hcon _ (Nat.le_add_right n k)), List.append_nil, ih]
    obtain ⟨t, ht⟩ := hunb (selectChain R w n).length
    by_cases hnt : n ≤ t
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnt
      rw [hconst] at ht
      exact lt_irrefl _ ht
    · have h1 := (chain_prefix_of_le (selectChain_prefix R w) (le_of_not_ge hnt)).length_le
      omega
  have hdom : ∀ n, (m (cantorPrefix w n)).Dom := by
    intro n
    obtain ⟨t, hnt, htR⟩ := hlate n
    rw [hm_dom]
    intro y hy
    exact htR.1 y (hy.trans (cantorPrefix_mono w hnt))
  refine ⟨hdom, ?_⟩
  rintro ⟨B, hB⟩
  apply hM_unbdd
  refine ⟨B, ?_⟩
  rintro _ ⟨k, rfl⟩
  obtain ⟨t, ht⟩ := hattain k
  have hmem : selectChain R w t ∈ chainPrefixSet (selectChain R w) := ⟨t, List.prefix_rfl⟩
  have hle : BitStream.finite (selectChain R w t) ≤ selectStream R w := by
    rw [hsel]
    exact (BitStream.finite_le_ofPrefixSet_iff hT _).2 hmem
  rw [h_sel] at hle
  have hcp : IsCantorPrefix (selectChain R w t) u := BitStream.finite_le_infinite_iff.1 hle
  have heq : cantorPrefix u k = selectChain R w t := by
    rw [← ht]
    exact (isCantorPrefix_iff_cantorPrefix_eq _ u).1 hcp
  obtain ⟨q, hq⟩ := Part.dom_iff_mem.1 (hdom t)
  have hqv := (hm_val _ _ hq).2
  have hqeq : q = M (cantorPrefix u k) := by
    rw [hqv, heq]; rfl
  have hqB : (q : ℝ) ≤ B := hB ⟨t, q, hq, rfl⟩
  rw [hqeq] at hqB
  exact hqB

/-- **SUV Theorem 190(a), p. 290.**  Every partial-computably random sequence is Mises-Church-Daley
random. -/
theorem isMisesChurchDaleyRandom_of_isPartialComputablyRandom {w : CantorSeq}
    (hw : IsPartialComputablyRandom w) : IsMisesChurchDaleyRandom w := by
  intro r hr
  by_contra h_not_freq
  rcases h_sel : selectStream (partialRuleSet r) w with _ | u
  · exact h_not_freq (by rw [h_sel]; exact trivial)
  · have h_not_freq_u : ¬ HasLimitFreq (1/2) u := fun h => h_not_freq (by rw [h_sel]; exact h)
    obtain ⟨M, hM_comp, hM_nonneg, hM_fair, hM_wins⟩ :=
        pm_computable_martingale_wins_unbalanced
    obtain ⟨m, hm_partrec, hm_mart, hm_dom, hm_val⟩ :=
      pm2_partialMartingaleOfRule_partrec hr hM_comp hM_nonneg hM_fair
    have h_wins_M := hM_wins u h_not_freq_u
    have h_wins_m := pm2_partialWins hm_dom
        hm_val h_sel h_wins_M
    exact hw m hm_partrec hm_mart h_wins_m

/-- **SUV Theorem 190(b), p. 290.**  For a non-decreasing unbounded computable `f` there is a
partial-computably random sequence whose `n`-bit prefix has complexity at most `f(n) log n + O(1)`.
Together with (a) this gives Theorem 189. -/
theorem exists_isPartialComputablyRandom_plainK_le {f : ℕ → ℕ} (hf : Computable f)
    (hmono : Monotone f) (hunb : ∀ B, ∃ n, B ≤ f n) (V : Map) (hV : isOptimalConditional V) :
    ∃ w, IsPartialComputablyRandom w ∧ ∃ c : ℝ, ∀ n : ℕ,
      ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤ f n * Real.logb 2 n + c := by
  obtain ⟨w, hw, hc⟩ :=
      pm_exists_random hf hmono
      hunb V hV
  refine ⟨w, ?_, hc⟩
  intro m hm hmart hwins
  apply hw m hm
  · exact ⟨hmart.1, hmart.2⟩
  · exact hwins

/-- Step 1 of the proof of `isComputablyRandom_of_isPartialComputablyRandom`: the uniform
measure has exactly computable positive rational masses. -/
private lemma isComputablyRandom_of_isPartialComputablyRandom_uniform_rat :
    ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR uniformMeasure x = r x := by
  use fun x => (1 / 2) ^ x.length
  refine ⟨?_, fun x => ?_⟩
  · have hpow : Computable (fun n : ℕ => 2 ^ n) := Primrec.to_comp primrec_two_pow_aux
    have h_den : Computable (fun x : BitString => 2 ^ x.length) := hpow.comp Computable.list_length
    have h_num : Computable (fun x : BitString => (1 : ℤ)) := Computable.const 1
    apply computable_of_num_den h_num h_den
    · intro a
      positivity
    · intro a
      dsimp
      have h1 : ((1 / 2 : ℚ) ^ a.length) = 1 / ((2 : ℚ) ^ a.length) := by
        exact one_div_pow 2 a.length
      rw [h1]
      push_cast
      rfl
  · constructor
    · positivity
    · rw [massR_uniformMeasure]
      dsimp
      push_cast
      norm_num

/-- **SUV Figure 3, p. 310.**  A partial-computably random sequence is computably random: total
rational martingales are partial martingales, and they suffice by Problem 266(b). -/
theorem isComputablyRandom_of_isPartialComputablyRandom {w : CantorSeq}
    (hw : IsPartialComputablyRandom w) : IsComputablyRandom uniformMeasure w := by
  rw [isComputablyRandom_iff_rational isComputablyRandom_of_isPartialComputablyRandom_uniform_rat]
  intro m hm hfair hwins
  apply hw (fun x => Part.some (m x)) hm.partrec
  · constructor
    · intro x q hq
      simp only [Part.mem_some_iff] at hq
      rw [hq]
      exact mod_cast hfair.nonneg x
    · intro x q q0 q1 hq hq0 hq1
      simp only [Part.mem_some_iff] at hq hq0 hq1
      rw [hq, hq0, hq1]
      have hf := hfair.fair x
      have hr0 : massR uniformMeasure (x ++ [false]) = 1 / 2 * massR uniformMeasure x := by
        rw [massR_uniformMeasure, massR_uniformMeasure, List.length_append]
        dsimp
        ring
      have hr1 : massR uniformMeasure (x ++ [true]) = 1 / 2 * massR uniformMeasure x := by
        rw [massR_uniformMeasure, massR_uniformMeasure, List.length_append]
        dsimp
        ring
      have hrpos : 0 < massR uniformMeasure x := by
        rw [massR_uniformMeasure]
        positivity
      have hf' : (m x : ℝ) * massR uniformMeasure x = (m (x ++ [false]) : ℝ) *
          (1 / 2 * massR uniformMeasure x) + (m (x ++ [true]) : ℝ) * (1 / 2 * massR uniformMeasure
          x) := by
        rw [hr0, hr1] at hf
        exact hf
      have hf'' : (m x : ℝ) * massR uniformMeasure x = ((m (x ++ [false]) : ℝ) * (1 / 2) +
          (m (x ++ [true]) : ℝ) * (1 / 2)) * massR uniformMeasure x := by
        calc
          (m x : ℝ) * massR uniformMeasure x = (m (x ++ [false]) : ℝ) *
              (1 / 2 * massR uniformMeasure x) + (m (x ++ [true]) : ℝ) *
              (1 / 2 * massR uniformMeasure x) := hf'
          _ = ((m (x ++ [false]) : ℝ) * (1 / 2) + (m (x ++ [true]) : ℝ) * (1 / 2)) *
              massR uniformMeasure x := by ring
      have hf3 : (m x : ℝ) = (m (x ++ [false]) : ℝ) * (1 / 2) + (m (x ++ [true]) : ℝ) * (1 / 2) :=
          by
        rw [mul_comm ((m (x ++ [false]) : ℝ) * (1 / 2) + (m (x ++ [true]) : ℝ) * (1 / 2)),
            mul_comm (m x : ℝ)] at hf''
        exact (mul_right_inj' (ne_of_gt hrpos)).mp hf''
      have hf4 : (m x : ℝ) = ((m (x ++ [false]) + m (x ++ [true])) / 2 : ℝ) := by
        calc
          (m x : ℝ) = (m (x ++ [false]) : ℝ) * (1 / 2) + (m (x ++ [true]) : ℝ) * (1 / 2) := hf3
          _ = ((m (x ++ [false]) + m (x ++ [true])) / 2 : ℝ) := by ring
      exact mod_cast hf4
  · constructor
    · intro n
      simp only [Part.some_dom]
    · rintro ⟨B, hB⟩
      apply hwins
      use B
      rintro y ⟨n, hn⟩
      rw [← hn]
      apply hB
      simp only [Set.mem_ofPred_eq]
      use n, m (cantorPrefix w n)
      simp only [Part.mem_some_iff, true_and]

end Kolmogorov.FrequencyGames








#print axioms Kolmogorov.FrequencyGames.isMisesChurchDaleyRandom_of_selectStream_stage
