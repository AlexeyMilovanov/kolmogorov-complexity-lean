/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.NormalInBase

/-!
# Computable Normal

This module constructs a computable absolutely normal real number, i.e. a real that is normal in
every integer base `b ≥ 2`.  The construction diagonalizes against the rational intervals
covering the reals whose digit frequencies deviate from the expected value `b ^ (-k)`, and
interpolates the counting function between the sampled lengths `(t + 1) ^ 6`.

The main declaration is `exists_computable_isAbsolutelyNormal` (SUV Problem 260, p. 266).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped BigOperators

/-- Total length of a list of rational intervals, as a real number. -/
private noncomputable def exists_computable_isAbsolutelyNormal_len (l : List (ℚ × ℚ)) : ℝ :=
  (l.map (fun I => ((I.2 - I.1 : ℚ) : ℝ))).sum

/-- Natural number exponentiation is primitive recursive. -/
private lemma exists_computable_isAbsolutelyNormal_primrec_pow :
    Primrec₂ (fun a b : ℕ => a ^ b) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

/-- `win b k N m u j = true` iff the digits `j, …, j + k - 1` of the `(N + k - 1)`-digit base-`b`
numeral `m` (digit `i` counted from the left is `(m / b ^ (N + k - 2 - i)) % b`) are the `k` digits
`(u / b ^ (k - 1 - t)) % b`, `t < k`, of the word number `u`. -/
private def exists_computable_isAbsolutelyNormal_win (b k N m u j : ℕ) : Bool :=
  (List.range k).all (fun t =>
    decide ((m / b ^ (N + k - 2 - (j + t))) % b = (u / b ^ (k - 1 - t)) % b))

/-- The number of windows `j < N` of the numeral `m` that match the word number `u`. -/
private def exists_computable_isAbsolutelyNormal_cnt (b k N m u : ℕ) : ℕ :=
  ((List.range N).filter (fun j => exists_computable_isAbsolutelyNormal_win b k N m u j)).length

/-- The numeral `m` deviates for the word `u`: `|cnt / N - b ^ (-k)| ≥ 1 / R`, written without
division as `N * b ^ k ≤ R * |cnt * b ^ k - N|` (truncated subtractions). -/
private def exists_computable_isAbsolutelyNormal_bad (b k N R m u : ℕ) : Bool :=
  decide (N * b ^ k ≤ R * ((exists_computable_isAbsolutelyNormal_cnt b k N m u * b ^ k - N) +
    (N - exists_computable_isAbsolutelyNormal_cnt b k N m u * b ^ k)))

/-- The padded intervals `((m - 1) / b ^ L, (m + 1) / b ^ L)`, `L = N + k - 1`, over all word
numbers
`u < b ^ k` and all numerals `m < b ^ L` that deviate for `u`. -/
private def exists_computable_isAbsolutelyNormal_cover (b k N R : ℕ) : List (ℚ × ℚ) :=
  (List.range (b ^ k)).flatMap (fun u =>
    (List.range (b ^ (N + k - 1))).flatMap (fun m =>
      if exists_computable_isAbsolutelyNormal_bad b k N R m u = true then
        [(((m : ℚ) - 1) / ((b ^ (N + k - 1) : ℕ) : ℚ), ((m : ℚ) + 1) / ((b ^ (N + k - 1) : ℕ) : ℚ))]
      else []))

/-- Layer `t`: the covers for `N = (t+1)^6`, `R = t + 1` over all active pairs `(b, k)`. -/
private def exists_computable_isAbsolutelyNormal_layer (t : ℕ) : List (ℚ × ℚ) :=
  (List.range ((t + 1) ^ 2 + 1)).flatMap (fun b =>
    (List.range ((t + 1) ^ 2 + 1)).flatMap (fun k =>
      if 2 ≤ b ∧ 1 ≤ k ∧ 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2 then
        exists_computable_isAbsolutelyNormal_cover b k ((t + 1) ^ 6) (t + 1)
      else []))

/-- The overlap of the interval `[l, r]` with the open interval `I`. -/
private def exists_computable_isAbsolutelyNormal_overlap (l r : ℚ) (I : ℚ × ℚ) : ℚ :=
  max 0 (min r I.2 - max l I.1)

/-- The total overlap of `[l, r]` with the intervals of the layers `< n`. -/
private def exists_computable_isAbsolutelyNormal_mu (Lay : ℕ → List (ℚ × ℚ)) (n : ℕ) (l r : ℚ) :
    ℚ :=
  ((List.range n).map (fun i =>
    ((Lay i).map (fun I => exists_computable_isAbsolutelyNormal_overlap l r I)).sum)).sum

/-- The dyadic descent: `J_s = [desc s / 2^(s+1), (desc s + 1) / 2^(s+1)]`; `J_{s+1}` is the child
of `J_s` with the smaller total overlap with the layers `< T (2 s + 5)` (left child on ties). -/
private def exists_computable_isAbsolutelyNormal_desc (Lay : ℕ → List (ℚ × ℚ)) (T : ℕ → ℕ) :
    ℕ → ℕ
  | 0 => 0
  | s + 1 =>
    2 * exists_computable_isAbsolutelyNormal_desc Lay T s +
      (if exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
            ((exists_computable_isAbsolutelyNormal_desc Lay T s : ℚ) / 2 ^ (s + 1))
            (((2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
          ≤ exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
            (((2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
            (((exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 1))
        then 0 else 1)


/-- Auxiliary for `stepA1_descent`: the overlap with an interval is nonnegative. -/
private lemma exists_computable_isAbsolutelyNormal_A1_ov_nonneg (l r : ℚ) (I : ℚ × ℚ) :
    0 ≤ exists_computable_isAbsolutelyNormal_overlap l r I := le_max_left _ _

/-- Auxiliary for `stepA1_descent`: the overlap with an interval is at most its length. -/
private lemma exists_computable_isAbsolutelyNormal_A1_ov_le (l r : ℚ) (I : ℚ × ℚ)
    (hI : I.1 ≤ I.2) :
    exists_computable_isAbsolutelyNormal_overlap l r I ≤ I.2 - I.1 := by
  unfold exists_computable_isAbsolutelyNormal_overlap
  apply max_le (by linarith)
  have h1 : min r I.2 ≤ I.2 := min_le_right _ _
  have h2 : I.1 ≤ max l I.1 := le_max_right _ _
  linarith

/-- Auxiliary for `stepA1_descent`: the overlap is additive over a split of `[l, r]`. -/
private lemma exists_computable_isAbsolutelyNormal_A1_ov_add (l m r : ℚ) (hlm : l ≤ m)
    (hmr : m ≤ r) (I : ℚ × ℚ) :
    exists_computable_isAbsolutelyNormal_overlap l m I +
        exists_computable_isAbsolutelyNormal_overlap m r I
      = exists_computable_isAbsolutelyNormal_overlap l r I := by
  unfold exists_computable_isAbsolutelyNormal_overlap
  rcases I with ⟨a, b⟩
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Auxiliary for `stepA1_descent`: rational total length of a layer. -/
private def exists_computable_isAbsolutelyNormal_A1_lenQ (l : List (ℚ × ℚ)) : ℚ :=
  (l.map (fun I => I.2 - I.1)).sum

/-- Auxiliary for `stepA1_descent`: `len` is the real cast of `lenQ`. -/
private lemma exists_computable_isAbsolutelyNormal_A1_len_eq (l : List (ℚ × ℚ)) :
    exists_computable_isAbsolutelyNormal_len l =
      ((exists_computable_isAbsolutelyNormal_A1_lenQ l : ℚ) : ℝ) := by
  unfold exists_computable_isAbsolutelyNormal_len exists_computable_isAbsolutelyNormal_A1_lenQ
  rw [Rat.cast_list_sum]
  simp [List.map_map, Function.comp_def]

/-- Auxiliary for `stepA1_descent`: `mu` as a finite sum. -/
private lemma exists_computable_isAbsolutelyNormal_A1_mu_eq (Lay : ℕ → List (ℚ × ℚ)) (n : ℕ)
    (l r : ℚ) :
    exists_computable_isAbsolutelyNormal_mu Lay n l r =
      ∑ i ∈ Finset.range n,
        ((Lay i).map (fun I => exists_computable_isAbsolutelyNormal_overlap l r I)).sum := by
  induction n with
  | zero => simp [exists_computable_isAbsolutelyNormal_mu]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [exists_computable_isAbsolutelyNormal_mu, List.range_succ]

/-- Auxiliary for `stepA1_descent`: one layer's total overlap is nonnegative. -/
private lemma exists_computable_isAbsolutelyNormal_A1_layer_ov_nonneg (L : List (ℚ × ℚ)) (l r : ℚ) :
    0 ≤ (L.map (fun I => exists_computable_isAbsolutelyNormal_overlap l r I)).sum := by
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨I, _, rfl⟩ := hx
  exact exists_computable_isAbsolutelyNormal_A1_ov_nonneg l r I

/-- Auxiliary for `stepA1_descent`: one layer's total overlap is at most its total length. -/
private lemma exists_computable_isAbsolutelyNormal_A1_layer_ov_le (L : List (ℚ × ℚ))
    (hL : ∀ I ∈ L, I.1 ≤ I.2) (l r : ℚ) :
    (L.map (fun I => exists_computable_isAbsolutelyNormal_overlap l r I)).sum ≤
      exists_computable_isAbsolutelyNormal_A1_lenQ L := by
  unfold exists_computable_isAbsolutelyNormal_A1_lenQ
  apply List.sum_le_sum
  intro I hI
  exact exists_computable_isAbsolutelyNormal_A1_ov_le l r I (hL I hI)

/-- Auxiliary for `stepA1_descent`: `mu` is monotone in the number of layers. -/
private lemma exists_computable_isAbsolutelyNormal_A1_mu_mono (Lay : ℕ → List (ℚ × ℚ))
    {n n' : ℕ} (h : n' ≤ n) (l r : ℚ) :
    exists_computable_isAbsolutelyNormal_mu Lay n' l r ≤
      exists_computable_isAbsolutelyNormal_mu Lay n l r := by
  rw [exists_computable_isAbsolutelyNormal_A1_mu_eq, exists_computable_isAbsolutelyNormal_A1_mu_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ _
    exact exists_computable_isAbsolutelyNormal_A1_layer_ov_nonneg _ l r

/-- Auxiliary for `stepA1_descent`: adding layers `n ≤ i < n'` increases `mu` by at most their
total length. -/
private lemma exists_computable_isAbsolutelyNormal_A1_mu_Ico (Lay : ℕ → List (ℚ × ℚ))
    (hnn : ∀ n, ∀ I ∈ Lay n, I.1 ≤ I.2) {n n' : ℕ} (h : n ≤ n') (l r : ℚ) :
    exists_computable_isAbsolutelyNormal_mu Lay n' l r ≤
      exists_computable_isAbsolutelyNormal_mu Lay n l r +
        ∑ i ∈ Finset.Ico n n', exists_computable_isAbsolutelyNormal_A1_lenQ (Lay i) := by
  rw [exists_computable_isAbsolutelyNormal_A1_mu_eq, exists_computable_isAbsolutelyNormal_A1_mu_eq,
    ← Finset.sum_range_add_sum_Ico _ h]
  gcongr with i hi
  exact exists_computable_isAbsolutelyNormal_A1_layer_ov_le (Lay i) (hnn i) l r

/-- Auxiliary for `stepA1_descent`: `mu` is bounded by the total length of the layers. -/
private lemma exists_computable_isAbsolutelyNormal_A1_mu_le_len (Lay : ℕ → List (ℚ × ℚ))
    (hnn : ∀ n, ∀ I ∈ Lay n, I.1 ≤ I.2) (n : ℕ) (l r : ℚ) :
    exists_computable_isAbsolutelyNormal_mu Lay n l r ≤
      ∑ i ∈ Finset.range n, exists_computable_isAbsolutelyNormal_A1_lenQ (Lay i) := by
  rw [exists_computable_isAbsolutelyNormal_A1_mu_eq]
  apply Finset.sum_le_sum
  intro i _
  exact exists_computable_isAbsolutelyNormal_A1_layer_ov_le (Lay i) (hnn i) l r

/-- Auxiliary for `stepA1_descent`: additivity of `mu` over a split of `[l, r]`. -/
private lemma exists_computable_isAbsolutelyNormal_A1_mu_add (Lay : ℕ → List (ℚ × ℚ)) (n : ℕ)
    {l m r : ℚ} (hlm : l ≤ m) (hmr : m ≤ r) :
    exists_computable_isAbsolutelyNormal_mu Lay n l m +
        exists_computable_isAbsolutelyNormal_mu Lay n m r =
      exists_computable_isAbsolutelyNormal_mu Lay n l r := by
  rw [exists_computable_isAbsolutelyNormal_A1_mu_eq, exists_computable_isAbsolutelyNormal_A1_mu_eq,
    exists_computable_isAbsolutelyNormal_A1_mu_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro I _
  exact exists_computable_isAbsolutelyNormal_A1_ov_add l m r hlm hmr I

/-- Auxiliary for `stepA1_descent`: `mu` dominates the overlap with any single interval of an
included layer. -/
private lemma exists_computable_isAbsolutelyNormal_A1_mu_ge_term (Lay : ℕ → List (ℚ × ℚ))
    {n N : ℕ} (hn : n < N) {I : ℚ × ℚ} (hI : I ∈ Lay n) (l r : ℚ) :
    exists_computable_isAbsolutelyNormal_overlap l r I ≤
      exists_computable_isAbsolutelyNormal_mu Lay N l r := by
  rw [exists_computable_isAbsolutelyNormal_A1_mu_eq]
  have h1 : exists_computable_isAbsolutelyNormal_overlap l r I ≤
      ((Lay n).map (fun I => exists_computable_isAbsolutelyNormal_overlap l r I)).sum := by
    apply List.single_le_sum
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨J, _, rfl⟩ := hx
      exact exists_computable_isAbsolutelyNormal_A1_ov_nonneg l r J
    · exact List.mem_map_of_mem hI
  refine h1.trans ?_
  apply Finset.single_le_sum (f := fun i =>
    ((Lay i).map (fun I => exists_computable_isAbsolutelyNormal_overlap l r I)).sum)
  · intro i _
    exact exists_computable_isAbsolutelyNormal_A1_layer_ov_nonneg _ l r
  · simpa using hn

/-- Auxiliary for `stepA1_descent`: the endpoints of the three dyadic points of `J_s` are ordered.
-/
private lemma exists_computable_isAbsolutelyNormal_A1_endpoints (c s : ℕ) :
    (c : ℚ) / 2 ^ (s + 1) ≤ ((2 * c + 1 : ℕ) : ℚ) / 2 ^ (s + 2) ∧
      ((2 * c + 1 : ℕ) : ℚ) / 2 ^ (s + 2) ≤ ((c + 1 : ℕ) : ℚ) / 2 ^ (s + 1) := by
  have h2 : (0 : ℚ) < 2 ^ (s + 2) := by positivity
  have e : (2 : ℚ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by ring
  have h1 : (0 : ℚ) < 2 ^ (s + 1) := by positivity
  constructor
  · rw [div_le_div_iff₀ h1 h2]
    push_cast
    rw [e]
    nlinarith
  · rw [div_le_div_iff₀ h2 h1]
    push_cast
    rw [e]
    nlinarith

/-- Auxiliary for `stepA1_descent`: the child chosen by `desc` has at most half of the overlap. -/
private lemma exists_computable_isAbsolutelyNormal_A1_child_bound (Lay : ℕ → List (ℚ × ℚ))
    (T : ℕ → ℕ) (s : ℕ) :
    exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
        ((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) : ℚ) / 2 ^ (s + 2))
        (((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) + 1 : ℕ) : ℚ) / 2 ^ (s + 2)) ≤
      (1 / 2 : ℚ) * exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
        ((exists_computable_isAbsolutelyNormal_desc Lay T s : ℚ) / 2 ^ (s + 1))
        (((exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 1)) := by
  obtain ⟨hlm, hmr⟩ := exists_computable_isAbsolutelyNormal_A1_endpoints
    (exists_computable_isAbsolutelyNormal_desc Lay T s) s
  have hadd := exists_computable_isAbsolutelyNormal_A1_mu_add Lay (T (2 * s + 5)) hlm hmr
  have e : (2 : ℚ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by ring
  have h1 : (0 : ℚ) < 2 ^ (s + 1) := by positivity
  by_cases h : exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
            ((exists_computable_isAbsolutelyNormal_desc Lay T s : ℚ) / 2 ^ (s + 1))
            (((2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
          ≤ exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
            (((2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
            (((exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 1))
  · have hd : exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) =
        2 * exists_computable_isAbsolutelyNormal_desc Lay T s := by
      rw [exists_computable_isAbsolutelyNormal_desc, ite_eq_left h]
      rfl
    rw [hd]
    have hl : (((2 * exists_computable_isAbsolutelyNormal_desc Lay T s : ℕ) : ℚ) / 2 ^ (s + 2)) =
        (exists_computable_isAbsolutelyNormal_desc Lay T s : ℚ) / 2 ^ (s + 1) := by
      push_cast
      rw [e]
      field_simp
    rw [hl]
    linarith
  · have hd : exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) =
        2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 := by
      rw [exists_computable_isAbsolutelyNormal_desc, ite_eq_right h]
    rw [hd]
    have hr : (((2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 + 1 : ℕ) : ℚ) /
        2 ^ (s + 2)) =
        (((exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 1)) := by
      push_cast
      rw [e]
      field_simp
      ring
    rw [hr]
    push Not at h
    linarith

/-- Auxiliary for `stepA1_descent`: the density invariant of the descent (in `ℚ`). -/
private lemma exists_computable_isAbsolutelyNormal_A1_invariant (Lay : ℕ → List (ℚ × ℚ))
    (hnn : ∀ n, ∀ I ∈ Lay n, I.1 ≤ I.2) (T : ℕ → ℕ)
    (htotQ : ∀ K, ∑ n ∈ Finset.range K,
      exists_computable_isAbsolutelyNormal_A1_lenQ (Lay n) ≤ (1 / 8 : ℚ))
    (htailQ : ∀ m K, ∑ n ∈ Finset.Ico (T m) (T m + K),
      exists_computable_isAbsolutelyNormal_A1_lenQ (Lay n) ≤ (1 / 2 : ℚ) ^ m)
    (s : ℕ) :
    exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
        ((exists_computable_isAbsolutelyNormal_desc Lay T s : ℚ) / 2 ^ (s + 1))
        (((exists_computable_isAbsolutelyNormal_desc Lay T s + 1 : ℕ) : ℚ) / 2 ^ (s + 1)) ≤
      (1 / 2 - (1 / 2 : ℚ) ^ (s + 2)) * (1 / 2 : ℚ) ^ (s + 1) := by
  induction s with
  | zero =>
    have h0 : exists_computable_isAbsolutelyNormal_desc Lay T 0 = 0 := by
      rw [exists_computable_isAbsolutelyNormal_desc]
    rw [h0]
    refine (exists_computable_isAbsolutelyNormal_A1_mu_le_len Lay hnn _ _ _).trans ?_
    refine (htotQ _).trans ?_
    norm_num
  | succ s ih =>
    have hchild := exists_computable_isAbsolutelyNormal_A1_child_bound Lay T s
    have hmu : exists_computable_isAbsolutelyNormal_mu Lay (T (2 * (s + 1) + 5))
        ((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) : ℚ) / 2 ^ (s + 2))
        (((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) + 1 : ℕ) : ℚ) / 2 ^ (s + 2)) ≤
      exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
        ((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) : ℚ) / 2 ^ (s + 2))
        (((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
        + (1 / 2 : ℚ) ^ (2 * s + 5) := by
      rcases le_total (T (2 * s + 5)) (T (2 * (s + 1) + 5)) with hle | hle
      · have h1 := exists_computable_isAbsolutelyNormal_A1_mu_Ico Lay hnn hle
          ((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) : ℚ) / 2 ^ (s + 2))
          (((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
        have h2 := htailQ (2 * s + 5) (T (2 * (s + 1) + 5) - T (2 * s + 5))
        rw [Nat.add_sub_cancel' hle] at h2
        linarith
      · have h1 := exists_computable_isAbsolutelyNormal_A1_mu_mono Lay hle
          ((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) : ℚ) / 2 ^ (s + 2))
          (((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) + 1 : ℕ) : ℚ) / 2 ^ (s + 2))
        have h3 : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ (2 * s + 5) := by positivity
        linarith
    obtain ⟨x, hx⟩ : ∃ x : ℚ, x = (1 / 2 : ℚ) ^ (s + 3) := ⟨_, rfl⟩
    have ha : (1 / 2 : ℚ) ^ (s + 2) = 2 * x := by rw [hx]; ring
    have hb : (1 / 2 : ℚ) ^ (s + 1) = 4 * x := by rw [hx]; ring
    have hc : (1 / 2 : ℚ) ^ (2 * s + 5) = 2 * x * x := by rw [hx]; ring
    have hd : (1 / 2 : ℚ) ^ (s + 1 + 2) = x := by rw [hx]
    have he : (1 / 2 : ℚ) ^ (s + 1 + 1) = 2 * x := by rw [hx]; ring
    change exists_computable_isAbsolutelyNormal_mu Lay (T (2 * (s + 1) + 5))
        ((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) : ℚ) / 2 ^ (s + 2))
        (((exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) + 1 : ℕ) : ℚ) / 2 ^ (s + 2)) ≤
      (1 / 2 - (1 / 2 : ℚ) ^ (s + 1 + 2)) * (1 / 2 : ℚ) ^ (s + 1 + 1)
    rw [ha, hb] at ih
    rw [hd, he]
    rw [hc] at hmu
    nlinarith

/-- Auxiliary for `stepA1_descent`: nested dyadic intervals `[c s / 2^(s+1), (c s + 1) / 2^(s+1)]`
(each the left or the right half of the previous one, starting from `[0, 1/2]`) share a point. -/
private lemma exists_computable_isAbsolutelyNormal_A1_limit (c : ℕ → ℕ) (hc0 : c 0 = 0)
    (hsucc : ∀ s, c (s + 1) = 2 * c s ∨ c (s + 1) = 2 * c s + 1) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 / 2 ∧
      ∀ s, (c s : ℝ) / 2 ^ (s + 1) ≤ α ∧ α ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1) := by
  have h2 : ∀ s : ℕ, (0 : ℝ) < 2 ^ (s + 1) := fun s => by positivity
  have hcs : ∀ s, (2 * c s : ℝ) ≤ c (s + 1) := by
    intro s
    rcases hsucc s with h | h <;> rw [h] <;> push_cast <;> linarith
  have hcs' : ∀ s, (c (s + 1) : ℝ) + 1 ≤ 2 * c s + 2 := by
    intro s
    rcases hsucc s with h | h <;> rw [h] <;> push_cast <;> linarith
  have hmono : Monotone (fun s => (c s : ℝ) / 2 ^ (s + 1)) := by
    apply monotone_nat_of_le_succ
    intro s
    change (c s : ℝ) / 2 ^ (s + 1) ≤ (c (s + 1) : ℝ) / 2 ^ (s + 1 + 1)
    rw [div_le_div_iff₀ (h2 s) (h2 (s + 1))]
    have e : (2 : ℝ) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by ring
    rw [e]
    calc (c s : ℝ) * (2 * 2 ^ (s + 1)) = (2 * c s) * 2 ^ (s + 1) := by ring
      _ ≤ c (s + 1) * 2 ^ (s + 1) := mul_le_mul_of_nonneg_right (hcs s) (h2 s).le
  have hanti : Antitone (fun s => ((c s : ℝ) + 1) / 2 ^ (s + 1)) := by
    apply antitone_nat_of_succ_le
    intro s
    change ((c (s + 1) : ℝ) + 1) / 2 ^ (s + 1 + 1) ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1)
    rw [div_le_div_iff₀ (h2 (s + 1)) (h2 s)]
    have e : (2 : ℝ) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by ring
    rw [e]
    calc ((c (s + 1) : ℝ) + 1) * 2 ^ (s + 1) ≤ (2 * c s + 2) * 2 ^ (s + 1) :=
          mul_le_mul_of_nonneg_right (hcs' s) (h2 s).le
      _ = ((c s : ℝ) + 1) * (2 * 2 ^ (s + 1)) := by ring
  have hab : ∀ s, (c s : ℝ) / 2 ^ (s + 1) ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1) := by
    intro s
    exact div_le_div_of_nonneg_right (by linarith) (h2 s).le
  have hb0 : ((c 0 : ℝ) + 1) / 2 ^ (0 + 1) = 1 / 2 := by
    rw [hc0]; norm_num
  have ha0 : (c 0 : ℝ) / 2 ^ (0 + 1) = 0 := by
    rw [hc0]; norm_num
  have hbdd : BddAbove (Set.range (fun s => (c s : ℝ) / 2 ^ (s + 1))) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨s, rfl⟩
    calc (c s : ℝ) / 2 ^ (s + 1) ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1) := hab s
      _ ≤ ((c 0 : ℝ) + 1) / 2 ^ (0 + 1) := hanti (Nat.zero_le s)
      _ = 1 / 2 := hb0
  have hle : ∀ s, (c s : ℝ) / 2 ^ (s + 1) ≤ ⨆ s', (c s' : ℝ) / 2 ^ (s' + 1) :=
    fun s => le_ciSup hbdd s
  have hge : ∀ s, (⨆ s', (c s' : ℝ) / 2 ^ (s' + 1)) ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1) := by
    intro s
    apply ciSup_le
    intro s'
    calc (c s' : ℝ) / 2 ^ (s' + 1) ≤ (c (max s s') : ℝ) / 2 ^ (max s s' + 1) :=
          hmono (le_max_right s s')
      _ ≤ ((c (max s s') : ℝ) + 1) / 2 ^ (max s s' + 1) := hab _
      _ ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1) := hanti (le_max_left s s')
  refine ⟨⨆ s', (c s' : ℝ) / 2 ^ (s' + 1), ?_, ?_, fun s => ⟨hle s, hge s⟩⟩
  · have := hle 0
    rw [ha0] at this
    exact this
  · have := hge 0
    rw [hb0] at this
    exact this

/-- Auxiliary for `stepA1_descent`: the real total length of a layer of nonnegative-length
intervals is nonnegative. -/
private lemma exists_computable_isAbsolutelyNormal_A1_len_nonneg (L : List (ℚ × ℚ))
    (hL : ∀ I ∈ L, I.1 ≤ I.2) : 0 ≤ exists_computable_isAbsolutelyNormal_len L := by
  unfold exists_computable_isAbsolutelyNormal_len
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨I, hI, rfl⟩ := hx
  have h1 : (I.1 : ℝ) ≤ I.2 := by exact_mod_cast hL I hI
  push_cast
  linarith

/-- Auxiliary for `stepA1_descent`: each interval's length is at most the total length. -/
private lemma exists_computable_isAbsolutelyNormal_A1_le_len (L : List (ℚ × ℚ))
    (hL : ∀ I ∈ L, I.1 ≤ I.2) (I : ℚ × ℚ) (hI : I ∈ L) :
    ((I.2 : ℝ) - I.1) ≤ exists_computable_isAbsolutelyNormal_len L := by
  unfold exists_computable_isAbsolutelyNormal_len
  have h : ((I.2 - I.1 : ℚ) : ℝ) ≤ (L.map (fun I => ((I.2 - I.1 : ℚ) : ℝ))).sum := by
    apply List.single_le_sum
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨J, hJ, rfl⟩ := hx
      have h1 : (J.1 : ℝ) ≤ J.2 := by exact_mod_cast hL J hJ
      push_cast
      linarith
    · exact List.mem_map_of_mem hI
  have e : ((I.2 : ℝ) - I.1) = ((I.2 - I.1 : ℚ) : ℝ) := by push_cast; ring
  rw [e]
  exact h

/-- Auxiliary for `stepA1_descent`: a point trapped in all the dyadic intervals `J_s` lies in no
open interval of any layer. -/
private lemma exists_computable_isAbsolutelyNormal_A1_avoid (Lay : ℕ → List (ℚ × ℚ))
    (hnn : ∀ n, ∀ I ∈ Lay n, I.1 ≤ I.2) (T : ℕ → ℕ)
    (htail : ∀ m K, ∑ n ∈ Finset.Ico (T m) (T m + K),
      exists_computable_isAbsolutelyNormal_len (Lay n) ≤ (1 / 2 : ℝ) ^ m)
    (c : ℕ → ℕ)
    (hinv : ∀ s, exists_computable_isAbsolutelyNormal_mu Lay (T (2 * s + 5))
        ((c s : ℚ) / 2 ^ (s + 1)) (((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1)) ≤
      (1 / 2 - (1 / 2 : ℚ) ^ (s + 2)) * (1 / 2 : ℚ) ^ (s + 1))
    (α : ℝ)
    (hα : ∀ s, (c s : ℝ) / 2 ^ (s + 1) ≤ α ∧ α ≤ ((c s : ℝ) + 1) / 2 ^ (s + 1)) :
    ∀ n, ∀ I ∈ Lay n, ¬ ((I.1 : ℝ) < α ∧ α < (I.2 : ℝ)) := by
  intro n I hI ⟨h1, h2⟩
  have hℓ : 0 < (I.2 : ℝ) - I.1 := by linarith
  have hx : 0 < min ((I.2 : ℝ) - I.1) (min (α - I.1) (I.2 - α)) :=
    lt_min hℓ (lt_min (by linarith) (by linarith))
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
  have hs1 : (1 / 2 : ℝ) ^ (s + 1) < min ((I.2 : ℝ) - I.1) (min (α - I.1) (I.2 - α)) :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ s)) hs
  have hs5 : (1 / 2 : ℝ) ^ (2 * s + 5) < min ((I.2 : ℝ) - I.1) (min (α - I.1) (I.2 - α)) :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hs
  have hm1 : (1 / 2 : ℝ) ^ (s + 1) < α - I.1 :=
    lt_of_lt_of_le hs1 ((min_le_right _ _).trans (min_le_left _ _))
  have hm2 : (1 / 2 : ℝ) ^ (s + 1) < I.2 - α :=
    lt_of_lt_of_le hs1 ((min_le_right _ _).trans (min_le_right _ _))
  have hm5 : (1 / 2 : ℝ) ^ (2 * s + 5) < (I.2 : ℝ) - I.1 :=
    lt_of_lt_of_le hs5 (min_le_left _ _)
  -- `I` is longer than `2^-(2s+5)`, which bounds the total length of the layers from
  -- `T (2s+5)` on, so the layer of `I` comes before `T (2s+5)`
  have hn : n < T (2 * s + 5) := by
    by_contra hcon
    have hcon' : T (2 * s + 5) ≤ n := not_lt.mp hcon
    have hK := htail (2 * s + 5) (n + 1 - T (2 * s + 5))
    have hmem : n ∈ Finset.Ico (T (2 * s + 5)) (T (2 * s + 5) + (n + 1 - T (2 * s + 5))) := by
      rw [Finset.mem_Ico]; omega
    have hsum : exists_computable_isAbsolutelyNormal_len (Lay n) ≤
        ∑ i ∈ Finset.Ico (T (2 * s + 5)) (T (2 * s + 5) + (n + 1 - T (2 * s + 5))),
          exists_computable_isAbsolutelyNormal_len (Lay i) :=
      Finset.single_le_sum (f := fun i => exists_computable_isAbsolutelyNormal_len (Lay i))
        (fun i _ => exists_computable_isAbsolutelyNormal_A1_len_nonneg (Lay i) (hnn i)) hmem
    have hlen := exists_computable_isAbsolutelyNormal_A1_le_len (Lay n) (hnn n) I hI
    linarith
  obtain ⟨hl, hr⟩ := hα s
  have h2pos : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have hw : ((c s : ℝ) + 1) / 2 ^ (s + 1) - (c s : ℝ) / 2 ^ (s + 1) = (1 / 2 : ℝ) ^ (s + 1) := by
    rw [one_div_pow]
    ring
  have hIl : (I.1 : ℝ) < ((c s : ℚ) / 2 ^ (s + 1) : ℚ) := by
    push_cast
    linarith
  have hrI : ((((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1) : ℚ) : ℝ) < (I.2 : ℝ) := by
    push_cast
    linarith
  have hIl' : I.1 < (c s : ℚ) / 2 ^ (s + 1) := by exact_mod_cast hIl
  have hrI' : ((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1) < I.2 := by exact_mod_cast hrI
  have hrl : ((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1) - (c s : ℚ) / 2 ^ (s + 1) = (1 / 2 : ℚ) ^ (s + 1) :=
      by
    rw [one_div_pow]
    push_cast
    ring
  have hov : exists_computable_isAbsolutelyNormal_overlap ((c s : ℚ) / 2 ^ (s + 1))
      (((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1)) I = (1 / 2 : ℚ) ^ (s + 1) := by
    unfold exists_computable_isAbsolutelyNormal_overlap
    have hy : (0 : ℚ) ≤ ((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1) - (c s : ℚ) / 2 ^ (s + 1) := by
      rw [hrl]; positivity
    rw [min_eq_left hrI'.le, max_eq_left hIl'.le, max_eq_right hy, hrl]
  have hge := exists_computable_isAbsolutelyNormal_A1_mu_ge_term Lay hn hI
    ((c s : ℚ) / 2 ^ (s + 1)) (((c s + 1 : ℕ) : ℚ) / 2 ^ (s + 1))
  have hbound := hinv s
  rw [hov] at hge
  have hy : (0 : ℚ) < (1 / 2 : ℚ) ^ (s + 1) := by positivity
  have hz : (0 : ℚ) < (1 / 2 : ℚ) ^ (s + 2) := by positivity
  nlinarith [mul_pos hy hz]

/-- Step A1 of the proof of `exists_computable_isAbsolutelyNormal` (dyadic descent, pure
mathematics): for layers of nonnegative-length rational intervals with total length `≤ 1/8` and
tails
`≤ 2^{-m}` beyond `T m`, the nested dyadic intervals `J_s` of `desc` shrink to a point `α ∈ [0,
1/2]`
that lies in no open interval of any layer. -/
private lemma exists_computable_isAbsolutelyNormal_stepA1_descent
    (Lay : ℕ → List (ℚ × ℚ)) (hnn : ∀ n, ∀ I ∈ Lay n, I.1 ≤ I.2) (T : ℕ → ℕ)
    (htot : ∀ K, ∑ n ∈ Finset.range K, exists_computable_isAbsolutelyNormal_len (Lay n) ≤ 1 / 8)
    (htail : ∀ m K, ∑ n ∈ Finset.Ico (T m) (T m + K),
      exists_computable_isAbsolutelyNormal_len (Lay n) ≤ (1 / 2 : ℝ) ^ m) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 / 2 ∧
      (∀ s, ((exists_computable_isAbsolutelyNormal_desc Lay T s : ℕ) : ℝ) / 2 ^ (s + 1) ≤ α ∧
        α ≤ (((exists_computable_isAbsolutelyNormal_desc Lay T s : ℕ) : ℝ) + 1) / 2 ^ (s + 1)) ∧
      ∀ n, ∀ I ∈ Lay n, ¬ ((I.1 : ℝ) < α ∧ α < (I.2 : ℝ)) := by
  have htotQ : ∀ K, ∑ n ∈ Finset.range K,
      exists_computable_isAbsolutelyNormal_A1_lenQ (Lay n) ≤ (1 / 8 : ℚ) := by
    intro K
    have h := htot K
    simp only [exists_computable_isAbsolutelyNormal_A1_len_eq] at h
    rw [← Rat.cast_sum] at h
    have e : (((1 / 8 : ℚ)) : ℝ) = 1 / 8 := by
      norm_num
    have h' : ((∑ n ∈ Finset.range K,
        exists_computable_isAbsolutelyNormal_A1_lenQ (Lay n) : ℚ) : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) := by
      rw [e]; exact h
    exact Rat.cast_le.mp h'
  have htailQ : ∀ m K, ∑ n ∈ Finset.Ico (T m) (T m + K),
      exists_computable_isAbsolutelyNormal_A1_lenQ (Lay n) ≤ (1 / 2 : ℚ) ^ m := by
    intro m K
    have h := htail m K
    simp only [exists_computable_isAbsolutelyNormal_A1_len_eq] at h
    rw [← Rat.cast_sum] at h
    have e : ((((1 / 2 : ℚ) ^ m : ℚ)) : ℝ) = (1 / 2 : ℝ) ^ m := by
      norm_num
    have h' : ((∑ n ∈ Finset.Ico (T m) (T m + K),
        exists_computable_isAbsolutelyNormal_A1_lenQ (Lay n) : ℚ) : ℝ) ≤
        ((((1 / 2 : ℚ) ^ m : ℚ)) : ℝ) := by
      rw [e]; exact h
    exact Rat.cast_le.mp h'
  have hinv := exists_computable_isAbsolutelyNormal_A1_invariant Lay hnn T htotQ htailQ
  have hc0 : exists_computable_isAbsolutelyNormal_desc Lay T 0 = 0 := by
    rw [exists_computable_isAbsolutelyNormal_desc]
  have hsucc : ∀ s, exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) =
        2 * exists_computable_isAbsolutelyNormal_desc Lay T s ∨
      exists_computable_isAbsolutelyNormal_desc Lay T (s + 1) =
        2 * exists_computable_isAbsolutelyNormal_desc Lay T s + 1 := by
    intro s
    rw [exists_computable_isAbsolutelyNormal_desc]
    split_ifs
    · left; rfl
    · right; rfl
  obtain ⟨α, h0, h1, hα⟩ := exists_computable_isAbsolutelyNormal_A1_limit _ hc0 hsucc
  exact ⟨α, h0, h1, hα,
    exists_computable_isAbsolutelyNormal_A1_avoid Lay hnn T htail _ hinv α hα⟩
/-- The sum of a computable list of rationals is computable. -/
private lemma exists_computable_isAbsolutelyNormal_A2_sum {γ : Type*} [Primcodable γ]
    {f : γ → List ℚ} (hf : Computable f) : Computable (fun a => (f a).sum) := by
  have hadd : Computable₂ (fun (_ : γ) (z : ℚ × ℚ) => z.1 + z.2) :=
    (ComputableReals.computable_ratAdd.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  have hfold := Computable.list_foldl hf (Computable.const (0 : ℚ)) hadd
  have key : ∀ (l : List ℚ) (acc : ℚ), l.foldl (fun s b => s + b) acc = acc + l.sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x t ih => intro acc; rw [List.foldl_cons, ih, List.sum_cons]; ring
  refine hfold.of_eq (fun a => ?_)
  simp only
  rw [key]
  simp

/-- The overlap of computable data is computable. -/
private lemma exists_computable_isAbsolutelyNormal_A2_overlap {γ : Type*} [Primcodable γ]
    {l r : γ → ℚ} {I : γ → ℚ × ℚ} (hl : Computable l) (hr : Computable r) (hI : Computable I) :
    Computable (fun c => exists_computable_isAbsolutelyNormal_overlap (l c) (r c) (I c)) := by
  have hmax : Computable₂ (max : ℚ → ℚ → ℚ) := ComputableReals.primrec_ratMax.to_comp
  have hmin : Computable₂ (min : ℚ → ℚ → ℚ) := ComputableReals.primrec_ratMin.to_comp
  have hsub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) := ComputableReals.computable_ratSub
  have hI1 : Computable (fun c => (I c).1) := Computable.fst.comp hI
  have hI2 : Computable (fun c => (I c).2) := Computable.snd.comp hI
  have h1 : Computable (fun c => min (r c) (I c).2) := hmin.comp hr hI2
  have h2 : Computable (fun c => max (l c) (I c).1) := hmax.comp hl hI1
  have h3 : Computable (fun c => min (r c) (I c).2 - max (l c) (I c).1) := hsub.comp h1 h2
  exact hmax.comp (Computable.const (0 : ℚ)) h3

/-- The total overlap `mu` is computable in `(n, l, r)` for computable layers. -/
private lemma exists_computable_isAbsolutelyNormal_A2_mu (Lay : ℕ → List (ℚ × ℚ))
    (hLay : Computable Lay) :
    Computable (fun p : ℕ × ℚ × ℚ =>
      exists_computable_isAbsolutelyNormal_mu Lay p.1 p.2.1 p.2.2) := by
  have hrange : Computable (fun p : ℕ × ℚ × ℚ => List.range p.1) :=
    Primrec.list_range.to_comp.comp Computable.fst
  have hLq : Computable (fun q : (ℕ × ℚ × ℚ) × ℕ => Lay q.2) := hLay.comp Computable.snd
  have hov : Computable₂ (fun (q : (ℕ × ℚ × ℚ) × ℕ) (I : ℚ × ℚ) =>
      exists_computable_isAbsolutelyNormal_overlap q.1.2.1 q.1.2.2 I) :=
    exists_computable_isAbsolutelyNormal_A2_overlap
      (γ := ((ℕ × ℚ × ℚ) × ℕ) × (ℚ × ℚ))
      (l := fun c => c.1.1.2.1) (r := fun c => c.1.1.2.2) (I := fun c => c.2)
      (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
      (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
      Computable.snd
  have hinner : Computable (fun q : (ℕ × ℚ × ℚ) × ℕ =>
      ((Lay q.2).map (fun I =>
        exists_computable_isAbsolutelyNormal_overlap q.1.2.1 q.1.2.2 I)).sum) :=
    exists_computable_isAbsolutelyNormal_A2_sum (Computable.list_map hLq hov)
  have houter : Computable (fun p : ℕ × ℚ × ℚ =>
      (List.range p.1).map (fun i => ((Lay i).map (fun I =>
        exists_computable_isAbsolutelyNormal_overlap p.2.1 p.2.2 I)).sum)) :=
    Computable.list_map hrange hinner.to₂
  exact exists_computable_isAbsolutelyNormal_A2_sum houter

/-- Dyadic rationals `c / 2 ^ e` with computable data are computable. -/
private lemma exists_computable_isAbsolutelyNormal_A2_dyadic {γ : Type*} [Primcodable γ]
    {c e : γ → ℕ} (hc : Computable c) (he : Computable e) :
    Computable (fun a => ((c a : ℕ) : ℚ) / 2 ^ (e a)) := by
  refine Kolmogorov.computable_of_num_den (N := fun a => ((c a : ℕ) : ℤ))
    (D := fun a => 2 ^ (e a)) ?_ ?_ ?_ ?_
  · exact ComputableReals.primrec_natCastInt.to_comp.comp hc
  · exact Kolmogorov.nat_pow_primrec₂.to_comp.comp (Computable.const 2) he
  · intro a; positivity
  · intro a; push_cast; rfl


/-- `mu` of computable data is computable. -/
private lemma exists_computable_isAbsolutelyNormal_A2_mu_comp {γ : Type*} [Primcodable γ]
    (Lay : ℕ → List (ℚ × ℚ)) (hLay : Computable Lay) {n : γ → ℕ} {l r : γ → ℚ}
    (hn : Computable n) (hl : Computable l) (hr : Computable r) :
    Computable (fun a => exists_computable_isAbsolutelyNormal_mu Lay (n a) (l a) (r a)) :=
  Computable.comp (f := fun p : ℕ × ℚ × ℚ =>
      exists_computable_isAbsolutelyNormal_mu Lay p.1 p.2.1 p.2.2)
    (g := fun a => (n a, l a, r a)) (exists_computable_isAbsolutelyNormal_A2_mu Lay hLay)
    (Computable.pair hn (Computable.pair hl hr))

/-- The branch `if x ≤ y then 0 else 1` on computable rationals is computable. -/
private lemma exists_computable_isAbsolutelyNormal_A2_cond_le {γ : Type*} [Primcodable γ]
    {x y : γ → ℚ} (hx : Computable x) (hy : Computable y) :
    Computable (fun a => if x a ≤ y a then (0 : ℕ) else 1) := by
  have h1 : Computable (fun a => decide (x a ≤ y a)) :=
    Computable.comp (f := fun p : ℚ × ℚ => decide (p.1 ≤ p.2)) (g := fun a => (x a, y a))
      ((PrimrecRel.decide ComputableReals.primrec_ratLe).to_comp) (Computable.pair hx hy)
  have h2 : Computable (fun a => cond (decide (x a ≤ y a)) (0 : ℕ) 1) :=
    Computable.cond h1 (Computable.const 0) (Computable.const 1)
  refine h2.of_eq (fun a => ?_)
  by_cases h : x a ≤ y a <;> simp [h]

/-- One step of the descent. -/
private def exists_computable_isAbsolutelyNormal_A2_stepf (Lay : ℕ → List (ℚ × ℚ)) (T : ℕ → ℕ)
    (z : ℕ × ℕ) : ℕ :=
  2 * z.2 +
    (if exists_computable_isAbsolutelyNormal_mu Lay (T (2 * z.1 + 5))
          ((z.2 : ℕ) / (2 : ℚ) ^ (z.1 + 1)) (((2 * z.2 + 1 : ℕ) : ℚ) / 2 ^ (z.1 + 2))
        ≤ exists_computable_isAbsolutelyNormal_mu Lay (T (2 * z.1 + 5))
          (((2 * z.2 + 1 : ℕ) : ℚ) / 2 ^ (z.1 + 2)) (((z.2 + 1 : ℕ) : ℚ) / 2 ^ (z.1 + 1))
      then 0 else 1)

/-- One step of the descent is computable. -/
private lemma exists_computable_isAbsolutelyNormal_A2_stepf_comp (Lay : ℕ → List (ℚ × ℚ))
    (hLay : Computable Lay) (T : ℕ → ℕ) (hT : Computable T) :
    Computable (exists_computable_isAbsolutelyNormal_A2_stepf Lay T) := by
  have hc : Computable (fun a : ℕ × ℕ => a.2) := Computable.snd
  have hs1 : Computable (fun a : ℕ × ℕ => a.1 + 1) := (Primrec.succ.comp Primrec.fst).to_comp
  have hs2 : Computable (fun a : ℕ × ℕ => a.1 + 2) :=
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)).to_comp
  have hc2 : Computable (fun a : ℕ × ℕ => 2 * a.2 + 1) :=
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to_comp
  have hc1 : Computable (fun a : ℕ × ℕ => a.2 + 1) := (Primrec.succ.comp Primrec.snd).to_comp
  have hN : Computable (fun a : ℕ × ℕ => T (2 * a.1 + 5)) :=
    Computable.comp (f := T) (g := fun a : ℕ × ℕ => 2 * a.1 + 5) hT
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
        (Primrec.const 5)).to_comp)
  have he1 : Computable (fun a : ℕ × ℕ => ((a.2 : ℕ) : ℚ) / 2 ^ (a.1 + 1)) :=
    exists_computable_isAbsolutelyNormal_A2_dyadic (c := fun a : ℕ × ℕ => a.2)
      (e := fun a : ℕ × ℕ => a.1 + 1) hc hs1
  have he2 : Computable (fun a : ℕ × ℕ => ((2 * a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 2)) :=
    exists_computable_isAbsolutelyNormal_A2_dyadic (c := fun a : ℕ × ℕ => 2 * a.2 + 1)
      (e := fun a : ℕ × ℕ => a.1 + 2) hc2 hs2
  have he3 : Computable (fun a : ℕ × ℕ => ((a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 1)) :=
    exists_computable_isAbsolutelyNormal_A2_dyadic (c := fun a : ℕ × ℕ => a.2 + 1)
      (e := fun a : ℕ × ℕ => a.1 + 1) hc1 hs1
  have hmu1 := exists_computable_isAbsolutelyNormal_A2_mu_comp Lay hLay
    (n := fun a : ℕ × ℕ => T (2 * a.1 + 5))
    (l := fun a : ℕ × ℕ => ((a.2 : ℕ) : ℚ) / 2 ^ (a.1 + 1))
    (r := fun a : ℕ × ℕ => ((2 * a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 2)) hN he1 he2
  have hmu2 := exists_computable_isAbsolutelyNormal_A2_mu_comp Lay hLay
    (n := fun a : ℕ × ℕ => T (2 * a.1 + 5))
    (l := fun a : ℕ × ℕ => ((2 * a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 2))
    (r := fun a : ℕ × ℕ => ((a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 1)) hN he2 he3
  have hite := exists_computable_isAbsolutelyNormal_A2_cond_le hmu1 hmu2
  have hmul : Computable (fun a : ℕ × ℕ => 2 * a.2) :=
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to_comp
  exact Computable.comp (f := fun p : ℕ × ℕ => p.1 + p.2) (g := fun a : ℕ × ℕ => (2 * a.2,
      if exists_computable_isAbsolutelyNormal_mu Lay (T (2 * a.1 + 5))
          (((a.2 : ℕ) : ℚ) / 2 ^ (a.1 + 1)) (((2 * a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 2))
        ≤ exists_computable_isAbsolutelyNormal_mu Lay (T (2 * a.1 + 5))
          (((2 * a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 2)) (((a.2 + 1 : ℕ) : ℚ) / 2 ^ (a.1 + 1))
      then 0 else 1))
    Primrec.nat_add.to_comp (Computable.pair hmul hite)

/-- The descent `desc` is computable for computable layers and a computable `T`. -/
private lemma exists_computable_isAbsolutelyNormal_A2_desc (Lay : ℕ → List (ℚ × ℚ))
    (hLay : Computable Lay) (T : ℕ → ℕ) (hT : Computable T) :
    Computable (fun s : ℕ => exists_computable_isAbsolutelyNormal_desc Lay T s) := by
  have hstep := exists_computable_isAbsolutelyNormal_A2_stepf_comp Lay hLay T hT
  have hstep2 : Computable₂ (fun (_ : ℕ) (z : ℕ × ℕ) =>
      exists_computable_isAbsolutelyNormal_A2_stepf Lay T z) :=
    Computable.comp (f := exists_computable_isAbsolutelyNormal_A2_stepf Lay T)
      (g := fun p : ℕ × (ℕ × ℕ) => p.2) hstep Computable.snd
  have hrec := Computable.nat_rec (f := fun s : ℕ => s) (g := fun _ : ℕ => (0 : ℕ))
    (h := fun (_ : ℕ) (z : ℕ × ℕ) => exists_computable_isAbsolutelyNormal_A2_stepf Lay T z)
    Computable.id (Computable.const 0) hstep2
  refine hrec.of_eq (fun s => ?_)
  induction s with
  | zero => rfl
  | succ s ih =>
    change exists_computable_isAbsolutelyNormal_A2_stepf Lay T
      (s, Nat.rec (motive := fun _ => ℕ) 0 _ s) = _
    rw [ih]
    rfl

/-- Step A2 of the proof of `exists_computable_isAbsolutelyNormal` (computability of the
descent): for computable layers and a computable `T`, a real trapped in all the nested dyadic
intervals `J_s` of `desc` is a computable real. -/
private lemma exists_computable_isAbsolutelyNormal_stepA2_computable
    (Lay : ℕ → List (ℚ × ℚ)) (hLay : Computable Lay) (T : ℕ → ℕ) (hT : Computable T) (α : ℝ)
    (hα : ∀ s, ((exists_computable_isAbsolutelyNormal_desc Lay T s : ℕ) : ℝ) / 2 ^ (s + 1) ≤ α ∧
        α ≤ (((exists_computable_isAbsolutelyNormal_desc Lay T s : ℕ) : ℝ) + 1) / 2 ^ (s + 1)) :
    ComputableReals.IsComputableReal α := by
  have hdesc := exists_computable_isAbsolutelyNormal_A2_desc Lay hLay T hT
  refine ⟨fun e => ((exists_computable_isAbsolutelyNormal_desc Lay T e.den : ℕ) : ℚ) /
    2 ^ (e.den + 1), ?_, ?_⟩
  · exact exists_computable_isAbsolutelyNormal_A2_dyadic
      (c := fun e : ℚ => exists_computable_isAbsolutelyNormal_desc Lay T e.den)
      (e := fun e : ℚ => e.den + 1)
      (hdesc.comp Kolmogorov.computable_ratDen)
      ((Primrec.succ.comp ComputableReals.primrec_ratDen).to_comp)
  · intro e he
    have hs := hα e.den
    have hden : 0 < e.den := e.pos
    have hnum : 0 < e.num := Rat.num_pos.mpr he
    have hnum1 : (1 : ℚ) ≤ (e.num : ℚ) := by exact_mod_cast hnum
    have hden_le : (e.den : ℚ) ≤ 2 ^ (e.den + 1) := by
      have h1 : e.den < 2 ^ e.den := Nat.lt_two_pow_self
      have h2 : 2 ^ e.den ≤ 2 ^ (e.den + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
      exact_mod_cast (le_trans h1.le h2)
    have hdenpos : (0 : ℚ) < (e.den : ℚ) := by exact_mod_cast hden
    have hq : (1 : ℚ) / 2 ^ (e.den + 1) ≤ e := by
      calc (1 : ℚ) / 2 ^ (e.den + 1) ≤ 1 / (e.den : ℚ) :=
            one_div_le_one_div_of_le hdenpos hden_le
        _ ≤ (e.num : ℚ) / (e.den : ℚ) := by gcongr
        _ = e := Rat.num_div_den e
    have hr : (1 : ℝ) / 2 ^ (e.den + 1) ≤ (e : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at h
      exact h
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
    have hcast : ((((exists_computable_isAbsolutelyNormal_desc Lay T e.den : ℕ) : ℚ) /
        2 ^ (e.den + 1) : ℚ) : ℝ) =
        ((exists_computable_isAbsolutelyNormal_desc Lay T e.den : ℕ) : ℝ) / 2 ^ (e.den + 1) := by
      push_cast; rfl
    have hsplit : (((exists_computable_isAbsolutelyNormal_desc Lay T e.den : ℕ) : ℝ) + 1) /
        2 ^ (e.den + 1) =
        ((exists_computable_isAbsolutelyNormal_desc Lay T e.den : ℕ) : ℝ) / 2 ^ (e.den + 1) +
          1 / 2 ^ (e.den + 1) := by ring
    rw [hcast, abs_le]
    constructor
    · linarith [hs.1]
    · linarith [hs.2, hsplit]
/-- Step A of the proof of `exists_computable_isAbsolutelyNormal`: a computable real in
`[0, 1/2]` outside all the open intervals of a computable family of layers of rational intervals
with total length `≤ 1/8` and a computable tail modulus. -/
private lemma exists_computable_isAbsolutelyNormal_stepA_avoid
    (Lay : ℕ → List (ℚ × ℚ)) (hLay : Computable Lay) (hnn : ∀ n, ∀ I ∈ Lay n, I.1 ≤ I.2)
    (T : ℕ → ℕ) (hT : Computable T)
    (htot : ∀ K, ∑ n ∈ Finset.range K, exists_computable_isAbsolutelyNormal_len (Lay n) ≤ 1 / 8)
    (htail : ∀ m K, ∑ n ∈ Finset.Ico (T m) (T m + K),
      exists_computable_isAbsolutelyNormal_len (Lay n) ≤ (1 / 2 : ℝ) ^ m) :
    ∃ α : ℝ, ComputableReals.IsComputableReal α ∧ 0 ≤ α ∧ α ≤ 1 / 2 ∧
      ∀ n, ∀ I ∈ Lay n, ¬ ((I.1 : ℝ) < α ∧ α < (I.2 : ℝ)) := by
  obtain ⟨α, h0, h1, hα, hav⟩ :=
    exists_computable_isAbsolutelyNormal_stepA1_descent Lay hnn T htot htail
  exact ⟨α, exists_computable_isAbsolutelyNormal_stepA2_computable Lay hLay T hT α hα, h0, h1, hav⟩

/-- Splitting a sum over `range (n * b)` into blocks of length `b`. -/
private lemma exists_computable_isAbsolutelyNormal_B_sum_block (b : ℕ) (F : ℕ → ℕ) :
    ∀ n : ℕ, ∑ m ∈ Finset.range (n * b), F m =
      ∑ q ∈ Finset.range n, ∑ d ∈ Finset.range b, F (q * b + d) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

open Classical in
/-- General counting of numerals with prescribed digits: `g e = some c` prescribes digit `e`
(counted from the right) to be `c`. -/
private lemma exists_computable_isAbsolutelyNormal_B_count (b : ℕ) (hb : 0 < b) :
    ∀ (L : ℕ) (g : ℕ → Option ℕ), (∀ e c, g e = some c → c < b) →
      (∑ m ∈ Finset.range (b ^ L),
        if (∀ e < L, ∀ c, g e = some c → (m / b ^ e) % b = c) then 1 else 0) *
          b ^ (∑ e ∈ Finset.range L, if (g e).isSome = true then 1 else 0) = b ^ L := by
  intro L
  induction L with
  | zero =>
    intro g _
    simp
  | succ L ih =>
    intro g hg
    have hg' : ∀ e c, (fun e => g (e + 1)) e = some c → c < b := fun e c h => hg (e + 1) c h
    have ih' : (∑ q ∈ Finset.range (b ^ L),
        if (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) then 1 else 0) *
          b ^ (∑ e ∈ Finset.range L, if (g (e + 1)).isSome = true then 1 else 0) = b ^ L :=
      ih (fun e => g (e + 1)) hg'
    -- per-summand factorisation
    have hfac : ∀ q d : ℕ, d < b →
        (if (∀ e < L + 1, ∀ c, g e = some c → ((q * b + d) / b ^ e) % b = c) then 1 else 0)
          = (if (∀ c, g 0 = some c → d = c) then 1 else 0) *
            (if (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) then 1 else 0) := by
      intro q d hd
      have h1 : (q * b + d) / b = q := by
        rw [add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hd, zero_add]
      have hdiv : ∀ e : ℕ, ((q * b + d) / b ^ (e + 1)) % b = (q / b ^ e) % b := by
        intro e
        rw [pow_succ', ← Nat.div_div_eq_div_mul, h1]
      have hd0 : ((q * b + d) / b ^ 0) % b = d := by
        rw [pow_zero, Nat.div_one, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
      have hiff : (∀ e < L + 1, ∀ c, g e = some c → ((q * b + d) / b ^ e) % b = c) ↔
          (∀ c, g 0 = some c → d = c) ∧
            (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) := by
        constructor
        · intro h
          refine ⟨fun c hc => ?_, fun e he c hc => ?_⟩
          · have := h 0 (Nat.succ_pos L) c hc
            rw [hd0] at this
            exact this
          · have := h (e + 1) (Nat.succ_lt_succ he) c hc
            rw [hdiv e] at this
            exact this
        · rintro ⟨h0, h1'⟩ e he c hc
          cases e with
          | zero =>
            rw [hd0]
            exact h0 c hc
          | succ e =>
            rw [hdiv e]
            exact h1' e (Nat.lt_of_succ_lt_succ he) c hc
      by_cases hA : ∀ c, g 0 = some c → d = c
      · by_cases hB : ∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c
        · simp only [ite_eq_left (hiff.mpr ⟨hA, hB⟩), ite_eq_left hA, ite_eq_left hB, mul_one]
        · simp only [ite_eq_right (fun h => hB (hiff.mp h).2), ite_eq_left hA, ite_eq_right hB,
            mul_zero]
      · simp only [ite_eq_right (fun h => hA (hiff.mp h).1), ite_eq_right hA, zero_mul]
    have hsum : ∑ m ∈ Finset.range (b ^ (L + 1)),
        (if (∀ e < L + 1, ∀ c, g e = some c → (m / b ^ e) % b = c) then 1 else 0)
        = (∑ d ∈ Finset.range b, if (∀ c, g 0 = some c → d = c) then 1 else 0) *
          (∑ q ∈ Finset.range (b ^ L),
            if (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) then 1 else 0) := by
      rw [pow_succ, exists_computable_isAbsolutelyNormal_B_sum_block]
      calc _ = ∑ q ∈ Finset.range (b ^ L), ∑ d ∈ Finset.range b,
              (if (∀ c, g 0 = some c → d = c) then 1 else 0) *
              (if (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) then 1 else 0) :=
            Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl
              (fun d hd => hfac q d (Finset.mem_range.mp hd)))
        _ = ∑ d ∈ Finset.range b, ∑ q ∈ Finset.range (b ^ L),
              (if (∀ c, g 0 = some c → d = c) then 1 else 0) *
              (if (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) then 1 else 0) :=
            Finset.sum_comm
        _ = _ := by rw [Finset.sum_mul_sum]
    have hd0 : (∑ d ∈ Finset.range b, if (∀ c, g 0 = some c → d = c) then 1 else 0)
        = if (g 0).isSome = true then 1 else b := by
      cases h0 : g 0 with
      | none => simp
      | some c =>
        have hc : c < b := hg 0 c h0
        simp [hc]
    have hn : (∑ e ∈ Finset.range (L + 1), if (g e).isSome = true then 1 else 0)
        = (∑ e ∈ Finset.range L, if (g (e + 1)).isSome = true then 1 else 0) +
          (if (g 0).isSome = true then 1 else 0) := Finset.sum_range_succ' _ _
    rw [hsum, hd0, hn, pow_add]
    generalize (∑ q ∈ Finset.range (b ^ L),
        if (∀ e < L, ∀ c, g (e + 1) = some c → (q / b ^ e) % b = c) then 1 else 0) = A at ih' ⊢
    generalize (∑ e ∈ Finset.range L, if (g (e + 1)).isSome = true then 1 else 0) = n at ih' ⊢
    by_cases hs : (g 0).isSome = true
    · simp only [hs, ↓reduceIte]
      calc 1 * A * (b ^ n * b ^ 1) = (A * b ^ n) * b := by ring
        _ = b ^ (L + 1) := by rw [ih', pow_succ]
    · simp only [hs]
      calc b * A * (b ^ n * b ^ 0) = b * (A * b ^ n) := by ring
        _ = b ^ (L + 1) := by rw [ih', pow_succ']

/-- Prescription of the digits with exponents `s, …, s + k - 1` (counted from the right) to be the
little-endian digits `(u / b ^ r) % b`, `r < k`, of `u`. -/
private def exists_computable_isAbsolutelyNormal_B_gw (b k s u : ℕ) (e : ℕ) : Option ℕ :=
  if s ≤ e ∧ e < s + k then some ((u / b ^ (e - s)) % b) else none

private lemma exists_computable_isAbsolutelyNormal_B_gw_lt (b k s u : ℕ) (hb : 0 < b) (e c : ℕ)
    (h : exists_computable_isAbsolutelyNormal_B_gw b k s u e = some c) : c < b := by
  unfold exists_computable_isAbsolutelyNormal_B_gw at h
  by_cases hin : s ≤ e ∧ e < s + k
  · rw [ite_eq_left hin] at h
    rw [← Option.some.inj h]
    exact Nat.mod_lt _ hb
  · rw [ite_eq_right hin] at h
    exact absurd h (by simp)

private lemma exists_computable_isAbsolutelyNormal_B_gw_isSome (b k s u e : ℕ) :
    (exists_computable_isAbsolutelyNormal_B_gw b k s u e).isSome = true ↔ (s ≤ e ∧ e < s + k) := by
  unfold exists_computable_isAbsolutelyNormal_B_gw
  by_cases hin : s ≤ e ∧ e < s + k
  · simp [hin]
  · simp [hin]

/-- The digits `j, …, j + k - 1` of `m` match `u` iff the prescription `gw` (exponents
`N - 1 - j, …`) is satisfied. -/
private lemma exists_computable_isAbsolutelyNormal_B_win_iff (b k N m u j : ℕ) (hk : 1 ≤ k)
    (hj : j < N) :
    exists_computable_isAbsolutelyNormal_win b k N m u j = true ↔
      ∀ e < N + k - 1, ∀ c,
        exists_computable_isAbsolutelyNormal_B_gw b k (N - 1 - j) u e = some c →
          (m / b ^ e) % b = c := by
  unfold exists_computable_isAbsolutelyNormal_win
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h e he c hc
    unfold exists_computable_isAbsolutelyNormal_B_gw at hc
    by_cases hin : N - 1 - j ≤ e ∧ e < N - 1 - j + k
    · rw [ite_eq_left hin] at hc
      have hc' := Option.some.inj hc
      have ht : k - 1 - (e - (N - 1 - j)) < k := by omega
      have h1 := h (k - 1 - (e - (N - 1 - j))) ht
      have e1 : N + k - 2 - (j + (k - 1 - (e - (N - 1 - j)))) = e := by omega
      have e2 : k - 1 - (k - 1 - (e - (N - 1 - j))) = e - (N - 1 - j) := by omega
      rw [e1, e2] at h1
      exact h1.trans hc'
    · rw [ite_eq_right hin] at hc
      exact absurd hc (by simp)
  · intro h t ht
    have he : N + k - 2 - (j + t) < N + k - 1 := by omega
    have hin : N - 1 - j ≤ N + k - 2 - (j + t) ∧ N + k - 2 - (j + t) < N - 1 - j + k := by omega
    have h1 := h (N + k - 2 - (j + t)) he ((u / b ^ (N + k - 2 - (j + t) - (N - 1 - j))) % b)
      (by unfold exists_computable_isAbsolutelyNormal_B_gw; rw [ite_eq_left hin])
    have e2 : N + k - 2 - (j + t) - (N - 1 - j) = k - 1 - t := by omega
    rw [e2] at h1
    exact h1

/-- The number of exponents `< L` in the window `[s, s + k)` is `k`. -/
private lemma exists_computable_isAbsolutelyNormal_B_card_window (s k L : ℕ) (h : s + k ≤ L) :
    (∑ e ∈ Finset.range L, if (s ≤ e ∧ e < s + k) then 1 else 0) = k := by
  rw [← Finset.card_filter]
  have : (Finset.range L).filter (fun e => s ≤ e ∧ e < s + k) = Finset.Ico s (s + k) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  omega

/-- Two disjoint windows: the first one (exponents `[s, s + k)`) takes precedence. -/
private def exists_computable_isAbsolutelyNormal_B_gw2 (b k s s' u : ℕ) (e : ℕ) : Option ℕ :=
  if s ≤ e ∧ e < s + k then some ((u / b ^ (e - s)) % b)
  else if s' ≤ e ∧ e < s' + k then some ((u / b ^ (e - s')) % b) else none

private lemma exists_computable_isAbsolutelyNormal_B_gw2_iff (b k s s' u : ℕ) (hss : s' + k ≤ s)
    (e c : ℕ) :
    exists_computable_isAbsolutelyNormal_B_gw2 b k s s' u e = some c ↔
      (exists_computable_isAbsolutelyNormal_B_gw b k s u e = some c ∨
        exists_computable_isAbsolutelyNormal_B_gw b k s' u e = some c) := by
  unfold exists_computable_isAbsolutelyNormal_B_gw2 exists_computable_isAbsolutelyNormal_B_gw
  by_cases h1 : s ≤ e ∧ e < s + k
  · have h2 : ¬ (s' ≤ e ∧ e < s' + k) := by omega
    simp [h1, h2]
  · by_cases h2 : s' ≤ e ∧ e < s' + k
    · simp [h1, h2]
    · simp [h1, h2]

private lemma exists_computable_isAbsolutelyNormal_B_gw2_lt (b k s s' u : ℕ) (hb : 0 < b)
    (hss : s' + k ≤ s) (e c : ℕ)
    (h : exists_computable_isAbsolutelyNormal_B_gw2 b k s s' u e = some c) : c < b := by
  rcases (exists_computable_isAbsolutelyNormal_B_gw2_iff b k s s' u hss e c).mp h with h | h
  · exact exists_computable_isAbsolutelyNormal_B_gw_lt b k s u hb e c h
  · exact exists_computable_isAbsolutelyNormal_B_gw_lt b k s' u hb e c h

private lemma exists_computable_isAbsolutelyNormal_B_gw2_isSome (b k s s' u e : ℕ)
    (hss : s' + k ≤ s) :
    (if (exists_computable_isAbsolutelyNormal_B_gw2 b k s s' u e).isSome = true then 1 else 0)
      = (if (s ≤ e ∧ e < s + k) then 1 else 0) + (if (s' ≤ e ∧ e < s' + k) then 1 else 0) := by
  unfold exists_computable_isAbsolutelyNormal_B_gw2
  by_cases h1 : s ≤ e ∧ e < s + k
  · have h2 : ¬ (s' ≤ e ∧ e < s' + k) := by omega
    simp [h1, h2]
  · by_cases h2 : s' ≤ e ∧ e < s' + k
    · simp [h1, h2]
    · simp [h1, h2]

/-- Step B of the proof of `exists_computable_isAbsolutelyNormal`: counting numerals with
prescribed digits in one window, and in two disjoint windows (independence of the digits). -/
private lemma exists_computable_isAbsolutelyNormal_stepB_window_count
    (b k N u : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    (∀ j < N, ((Finset.range (b ^ (N + k - 1))).filter
        (fun m => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card * b ^ k
          = b ^ (N + k - 1)) ∧
    (∀ j < N, ∀ j' < N, j + k ≤ j' →
      ((Finset.range (b ^ (N + k - 1))).filter
        (fun m => exists_computable_isAbsolutelyNormal_win b k N m u j = true ∧
                  exists_computable_isAbsolutelyNormal_win b k N m u j' = true)).card * b ^ (2 * k)
          = b ^ (N + k - 1)) := by
  have hb0 : 0 < b := by omega
  refine ⟨?_, ?_⟩
  · intro j hj
    have hG := exists_computable_isAbsolutelyNormal_B_count b hb0 (N + k - 1)
      (exists_computable_isAbsolutelyNormal_B_gw b k (N - 1 - j) u)
      (fun e c h => exists_computable_isAbsolutelyNormal_B_gw_lt b k (N - 1 - j) u hb0 e c h)
    have hn : (∑ e ∈ Finset.range (N + k - 1),
        if (exists_computable_isAbsolutelyNormal_B_gw b k (N - 1 - j) u e).isSome = true
          then 1 else 0) = k := by
      have : ∀ e ∈ Finset.range (N + k - 1),
          (if (exists_computable_isAbsolutelyNormal_B_gw b k (N - 1 - j) u e).isSome = true
            then 1 else 0)
          = (if (N - 1 - j ≤ e ∧ e < N - 1 - j + k) then 1 else 0) := by
        intro e _
        exact if_congr (exists_computable_isAbsolutelyNormal_B_gw_isSome b k (N - 1 - j) u e)
          rfl rfl
      rw [Finset.sum_congr rfl this]
      exact exists_computable_isAbsolutelyNormal_B_card_window (N - 1 - j) k (N + k - 1)
        (by omega)
    rw [hn] at hG
    rw [Finset.card_filter]
    refine Eq.trans (congrArg (· * b ^ k) ?_) hG
    exact Finset.sum_congr rfl (fun m _ =>
      if_congr (exists_computable_isAbsolutelyNormal_B_win_iff b k N m u j hk hj) rfl rfl)
  · intro j hj j' hj' hjj'
    have hss : (N - 1 - j') + k ≤ N - 1 - j := by omega
    have hG := exists_computable_isAbsolutelyNormal_B_count b hb0 (N + k - 1)
      (exists_computable_isAbsolutelyNormal_B_gw2 b k (N - 1 - j) (N - 1 - j') u)
      (fun e c h => exists_computable_isAbsolutelyNormal_B_gw2_lt b k _ _ u hb0 hss e c h)
    have hn : (∑ e ∈ Finset.range (N + k - 1),
        if (exists_computable_isAbsolutelyNormal_B_gw2 b k (N - 1 - j) (N - 1 - j') u e).isSome
          = true then 1 else 0) = 2 * k := by
      have : ∀ e ∈ Finset.range (N + k - 1),
          (if (exists_computable_isAbsolutelyNormal_B_gw2 b k (N - 1 - j) (N - 1 - j') u e).isSome
            = true then 1 else 0)
          = (if (N - 1 - j ≤ e ∧ e < N - 1 - j + k) then 1 else 0) +
            (if (N - 1 - j' ≤ e ∧ e < N - 1 - j' + k) then 1 else 0) := fun e _ =>
        exists_computable_isAbsolutelyNormal_B_gw2_isSome b k _ _ u e hss
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib,
        exists_computable_isAbsolutelyNormal_B_card_window (N - 1 - j) k (N + k - 1) (by omega),
        exists_computable_isAbsolutelyNormal_B_card_window (N - 1 - j') k (N + k - 1) (by omega)]
      ring
    rw [hn] at hG
    rw [Finset.card_filter]
    refine Eq.trans (congrArg (· * b ^ (2 * k)) ?_) hG
    refine Finset.sum_congr rfl (fun m _ => if_congr ?_ rfl rfl)
    rw [exists_computable_isAbsolutelyNormal_B_win_iff b k N m u j hk hj,
      exists_computable_isAbsolutelyNormal_B_win_iff b k N m u j' hk hj']
    constructor
    · rintro ⟨h1, h2⟩ e he c hc
      rcases (exists_computable_isAbsolutelyNormal_B_gw2_iff b k _ _ u hss e c).mp hc with hc | hc
      · exact h1 e he c hc
      · exact h2 e he c hc
    · intro h
      exact ⟨fun e he c hc => h e he c
          ((exists_computable_isAbsolutelyNormal_B_gw2_iff b k _ _ u hss e c).mpr (Or.inl hc)),
        fun e he c hc => h e he c
          ((exists_computable_isAbsolutelyNormal_B_gw2_iff b k _ _ u hss e c).mpr (Or.inr hc))⟩

/-- Step C of the proof of `exists_computable_isAbsolutelyNormal` (second-moment
Chebyshev bound for events that are independent at distance `≥ k`). -/
private lemma exists_computable_isAbsolutelyNormal_stepC_chebyshev
    {ι : Type*} (Ω : Finset ι) (N k : ℕ) (hk : 1 ≤ k) (X : ℕ → ι → Prop)
    [∀ j x, Decidable (X j x)] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsingle : ∀ j < N, ((Ω.filter (fun x => X j x)).card : ℝ) = p * Ω.card)
    (hpair : ∀ j < N, ∀ j' < N, j + k ≤ j' →
      ((Ω.filter (fun x => X j x ∧ X j' x)).card : ℝ) = p ^ 2 * Ω.card)
    (δ : ℝ) (hδ : 0 < δ) :
    ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ)
      ≤ Ω.card * (2 * k * N / δ ^ 2) := by
  classical
  -- centred indicators
  let Y : ℕ → ι → ℝ := fun j x => (if X j x then (1 : ℝ) else 0) - p
  have hS : ∀ x, (((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p
      = ∑ j ∈ Finset.range N, Y j x := by
    intro x
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  let E : ℕ → ℕ → ℝ := fun j j' => ∑ x ∈ Ω, Y j x * Y j' x
  have hYabs : ∀ j x, |Y j x| ≤ 1 := by
    intro j x
    simp only [Y]
    split_ifs
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  -- far pairs are uncorrelated
  have hfar : ∀ j < N, ∀ j' < N, j + k ≤ j' → E j j' = 0 := by
    intro j hj j' hj' hjj'
    have h1 := hsingle j hj
    have h2 := hsingle j' hj'
    have h3 := hpair j hj j' hj' hjj'
    have hexp : ∀ x, Y j x * Y j' x
        = (if X j x ∧ X j' x then (1 : ℝ) else 0) - p * (if X j x then (1 : ℝ) else 0)
          - p * (if X j' x then (1 : ℝ) else 0) + p ^ 2 := by
      intro x
      simp only [Y]
      by_cases a : X j x <;> by_cases c : X j' x <;> simp [a, c] <;> ring
    simp only [E, hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, h3]
    ring
  have hnear : ∀ j j', E j j' ≤ Ω.card := by
    intro j j'
    calc E j j' ≤ ∑ x ∈ Ω, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          have h1 := hYabs j x
          have h2 := hYabs j' x
          calc Y j x * Y j' x ≤ |Y j x * Y j' x| := le_abs_self _
            _ = |Y j x| * |Y j' x| := abs_mul _ _
            _ ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
      _ = Ω.card := by simp
  have hV : ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2
      = ∑ j ∈ Finset.range N, ∑ j' ∈ Finset.range N, E j j' := by
    simp only [E, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
  have hrow : ∀ j ∈ Finset.range N,
      ∑ j' ∈ Finset.range N, E j j' ≤ 2 * k * Ω.card := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hsub : ∑ j' ∈ Finset.range N, E j j'
        = ∑ j' ∈ (Finset.range N) ∩ Finset.Ico (j - k) (j + k), E j j' := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j' hj'N hj'not
      have hj'N' : j' < N := Finset.mem_range.mp hj'N
      have hnot : ¬ (j' ∈ Finset.Ico (j - k) (j + k)) :=
        fun h => hj'not (Finset.mem_inter.mpr ⟨hj'N, h⟩)
      rw [Finset.mem_Ico] at hnot
      by_cases h1 : j + k ≤ j'
      · exact hfar j hjN j' hj'N' h1
      · have h2 : j' + k ≤ j := by omega
        have h4 := hfar j' hj'N' j hjN h2
        have h5 : E j j' = E j' j :=
          Finset.sum_congr rfl (fun x _ => mul_comm _ _)
        rw [h5]
        exact h4
    rw [hsub]
    calc ∑ j' ∈ (Finset.range N) ∩ Finset.Ico (j - k) (j + k), E j j'
        ≤ ∑ j' ∈ (Finset.range N) ∩ Finset.Ico (j - k) (j + k), (Ω.card : ℝ) :=
          Finset.sum_le_sum (fun j' _ => hnear j j')
      _ = (((Finset.range N) ∩ Finset.Ico (j - k) (j + k)).card : ℝ) * Ω.card := by
          simp [Finset.sum_const]
      _ ≤ (2 * k : ℝ) * Ω.card := by
          have h1 : ((Finset.range N) ∩ Finset.Ico (j - k) (j + k)).card
              ≤ (Finset.Ico (j - k) (j + k)).card :=
            Finset.card_le_card Finset.inter_subset_right
          have h2 : (Finset.Ico (j - k) (j + k)).card ≤ 2 * k := by
            rw [Nat.card_Ico]; omega
          have h3 : ((((Finset.range N) ∩ Finset.Ico (j - k) (j + k)).card : ℕ) : ℝ)
              ≤ (2 * k : ℝ) := by
            exact_mod_cast h1.trans h2
          exact mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
  have hVle : ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 ≤ N * (2 * k * Ω.card) := by
    rw [hV]
    calc ∑ j ∈ Finset.range N, ∑ j' ∈ Finset.range N, E j j'
        ≤ ∑ j ∈ Finset.range N, (2 * k * Ω.card : ℝ) := Finset.sum_le_sum hrow
      _ = N * (2 * k * Ω.card) := by simp
  -- Chebyshev
  have hcheb : ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ) * δ ^ 2
      ≤ ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 := by
    calc ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ) * δ ^ 2
        = ∑ x ∈ Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|), δ ^ 2 := by
          simp [Finset.sum_const]
      _ ≤ ∑ x ∈ Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|),
          (∑ j ∈ Finset.range N, Y j x) ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          have hx2 := hx.2
          rw [hS x] at hx2
          calc δ ^ 2 ≤ |∑ j ∈ Finset.range N, Y j x| ^ 2 := by
                have h0 : 0 ≤ δ := hδ.le
                gcongr
            _ = (∑ j ∈ Finset.range N, Y j x) ^ 2 := sq_abs _
      _ ≤ ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro x _ _
            positivity
  have hδ2 : 0 < δ ^ 2 := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hδ2]
  calc ((Ω.filter (fun x =>
        δ ≤ |(((Finset.range N).filter (fun j => X j x)).card : ℝ) - N * p|)).card : ℝ) * δ ^ 2
      ≤ ∑ x ∈ Ω, (∑ j ∈ Finset.range N, Y j x) ^ 2 := hcheb
    _ ≤ N * (2 * k * Ω.card) := hVle
    _ = Ω.card * (2 * k * N) := by ring


/-- Auxiliary for Step D: the length of a filtered `List.range` is the card of the filtered
`Finset.range`. -/
private lemma exists_computable_isAbsolutelyNormal_CD_card_eq (P : ℕ → Bool) (N : ℕ) :
    ((List.range N).filter P).length = ((Finset.range N).filter (fun j => P j = true)).card := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    cases h : P n
    · simp [h]
    · simp [h]

/-- Auxiliary for Step D: the cast of the symmetric truncated difference is the absolute value. -/
private lemma exists_computable_isAbsolutelyNormal_CD_natabs (a N : ℕ) :
    (((a - N) + (N - a) : ℕ) : ℝ) = |(a : ℝ) - N| := by
  rcases le_total a N with h | h
  · have h1 : a - N = 0 := Nat.sub_eq_zero_of_le h
    have h2 : (a : ℝ) ≤ N := by exact_mod_cast h
    rw [h1, zero_add, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (by linarith)]
  · have h1 : N - a = 0 := Nat.sub_eq_zero_of_le h
    have h2 : (N : ℝ) ≤ a := by exact_mod_cast h
    rw [h1, add_zero, Nat.cast_sub h, abs_of_nonneg (by linarith)]

/-- Step D of the proof of `exists_computable_isAbsolutelyNormal`: the number of
numerals deviating for a fixed word number (from Steps B and C with `p = b ^ (-k)`,
`δ = N / R`). -/
private lemma exists_computable_isAbsolutelyNormal_stepD_count_bad
    (b k N R u : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (hN : 1 ≤ N) (hR : 1 ≤ R) :
    (((Finset.range (b ^ (N + k - 1))).filter
        (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)).card : ℝ)
      ≤ (b : ℝ) ^ (N + k - 1) * (2 * k * R ^ 2 / N) := by
  classical
  obtain ⟨hB1, hB2⟩ := exists_computable_isAbsolutelyNormal_stepB_window_count b k N u hb hk hN
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hN' : (N : ℝ) ≠ 0 := hN0.ne'
  have hR' : (R : ℝ) ≠ 0 := hR0.ne'
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hb0 k
  -- the probability `p = b ^ (-k)`
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ((b : ℝ)⁻¹) ^ k := ⟨_, rfl⟩
  have hp_mul : p * (b : ℝ) ^ k = 1 := by
    rw [hp, inv_pow]; exact inv_mul_cancel₀ hbk.ne'
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hb1)
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset ℕ, Ω = Finset.range (b ^ (N + k - 1)) := ⟨_, rfl⟩
  rw [← hΩ] at hB1 hB2 ⊢
  have hΩcard : (Ω.card : ℝ) = (b : ℝ) ^ (N + k - 1) := by
    rw [hΩ]; simp
  have hsingle : ∀ j < N,
      (((Ω.filter (fun m => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card
        : ℕ) : ℝ) = p * Ω.card := by
    intro j hj
    have h := hB1 j hj
    generalize (Ω.filter (fun m => exists_computable_isAbsolutelyNormal_win b k N m u j =
                                     true)).card
      = c at h ⊢
    have h' : (c : ℝ) * (b : ℝ) ^ k = (b : ℝ) ^ (N + k - 1) := by exact_mod_cast h
    rw [hΩcard]
    calc (c : ℝ) = ((c : ℝ) * (b : ℝ) ^ k) * p := by
          rw [mul_assoc, mul_comm ((b : ℝ) ^ k) p, hp_mul, mul_one]
      _ = (b : ℝ) ^ (N + k - 1) * p := by rw [h']
      _ = p * (b : ℝ) ^ (N + k - 1) := mul_comm _ _
  have hpair : ∀ j < N, ∀ j' < N, j + k ≤ j' →
      (((Ω.filter (fun m => exists_computable_isAbsolutelyNormal_win b k N m u j = true ∧
          exists_computable_isAbsolutelyNormal_win b k N m u j' = true)).card : ℕ) : ℝ)
        = p ^ 2 * Ω.card := by
    intro j hj j' hj' hjj'
    have h := hB2 j hj j' hj' hjj'
    generalize (Ω.filter (fun m => exists_computable_isAbsolutelyNormal_win b k N m u j = true ∧
          exists_computable_isAbsolutelyNormal_win b k N m u j' = true)).card = c at h ⊢
    have h' : (c : ℝ) * ((b : ℝ) ^ k) ^ 2 = (b : ℝ) ^ (N + k - 1) := by
      have : (b : ℝ) ^ (2 * k) = ((b : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [← this]; exact_mod_cast h
    rw [hΩcard]
    have hp2 : (p * (b : ℝ) ^ k) ^ 2 = 1 := by rw [hp_mul]; norm_num
    calc (c : ℝ) = (c : ℝ) * (p * (b : ℝ) ^ k) ^ 2 := by rw [hp2, mul_one]
      _ = ((c : ℝ) * ((b : ℝ) ^ k) ^ 2) * p ^ 2 := by ring
      _ = (b : ℝ) ^ (N + k - 1) * p ^ 2 := by rw [h']
      _ = p ^ 2 * (b : ℝ) ^ (N + k - 1) := mul_comm _ _
  have hδ : 0 < (N : ℝ) / R := div_pos hN0 hR0
  have hC : ((Ω.filter (fun m =>
        (N : ℝ) / R ≤ |(((Finset.range N).filter
          (fun j => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card : ℝ)
            - N * p|)).card : ℝ) ≤ Ω.card * (2 * k * N / ((N : ℝ) / R) ^ 2) :=
    exists_computable_isAbsolutelyNormal_stepC_chebyshev Ω N k hk
      (fun j m => exists_computable_isAbsolutelyNormal_win b k N m u j = true) p hp0 hp1
      hsingle hpair ((N : ℝ) / R) hδ
  have hsubset : Ω.filter (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)
      ⊆ Ω.filter (fun m =>
        (N : ℝ) / R ≤ |(((Finset.range N).filter
          (fun j => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card : ℝ)
            - N * p|) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    have hbad := hm.2
    unfold exists_computable_isAbsolutelyNormal_bad at hbad
    rw [decide_eq_true_eq] at hbad
    have hcnt : exists_computable_isAbsolutelyNormal_cnt b k N m u
        = ((Finset.range N).filter
          (fun j => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card :=
      exists_computable_isAbsolutelyNormal_CD_card_eq _ N
    rw [hcnt] at hbad
    generalize ((Finset.range N).filter
      (fun j => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card = c at hbad ⊢
    have hbadR : (N : ℝ) * (b : ℝ) ^ k ≤ (R : ℝ) * |(c : ℝ) * (b : ℝ) ^ k - N| := by
      have h1 := (Nat.cast_le (α := ℝ)).mpr hbad
      simp only [Nat.cast_mul, exists_computable_isAbsolutelyNormal_CD_natabs, Nat.cast_pow] at h1
      exact h1
    have habs : |(c : ℝ) - N * p| * (b : ℝ) ^ k = |(c : ℝ) * (b : ℝ) ^ k - N| := by
      have e1 : ((c : ℝ) - N * p) * (b : ℝ) ^ k = (c : ℝ) * (b : ℝ) ^ k - N := by
        have : (N : ℝ) * p * (b : ℝ) ^ k = N := by rw [mul_assoc, hp_mul, mul_one]
        calc ((c : ℝ) - N * p) * (b : ℝ) ^ k
            = (c : ℝ) * (b : ℝ) ^ k - N * p * (b : ℝ) ^ k := by ring
          _ = (c : ℝ) * (b : ℝ) ^ k - N := by rw [this]
      rw [← e1, abs_mul, abs_of_pos hbk]
    rw [div_le_iff₀ hR0]
    have h2 : (N : ℝ) * (b : ℝ) ^ k ≤ (|(c : ℝ) - N * p| * R) * (b : ℝ) ^ k := by
      calc (N : ℝ) * (b : ℝ) ^ k ≤ R * |(c : ℝ) * (b : ℝ) ^ k - N| := hbadR
        _ = R * (|(c : ℝ) - N * p| * (b : ℝ) ^ k) := by rw [habs]
        _ = (|(c : ℝ) - N * p| * R) * (b : ℝ) ^ k := by ring
    exact le_of_mul_le_mul_right h2 hbk
  calc ((Ω.filter (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)).card : ℝ)
      ≤ ((Ω.filter (fun m =>
        (N : ℝ) / R ≤ |(((Finset.range N).filter
          (fun j => exists_computable_isAbsolutelyNormal_win b k N m u j = true)).card : ℝ)
            - N * p|)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ Ω.card * (2 * k * N / ((N : ℝ) / R) ^ 2) := hC
    _ = (b : ℝ) ^ (N + k - 1) * (2 * k * R ^ 2 / N) := by
        rw [hΩcard]
        field_simp
/-- Auxiliary for `exists_computable_isAbsolutelyNormal_stepE_cover_cover`: the word number
`U.foldl (fun acc d => acc * b + d) 0` of a word of length `k` with digits `< b` is `< b ^ k` and
has
the digits of `U`. -/
private lemma exists_computable_isAbsolutelyNormal_E_foldl (b : ℕ) (hb : 0 < b) (U : List ℕ)
    (hU : ∀ d ∈ U, d < b) (k : ℕ) (hk : U.length = k) :
    U.foldl (fun acc d => acc * b + d) 0 < b ^ k ∧
    ∀ t (ht : t < U.length),
      (U.foldl (fun acc d => acc * b + d) 0 / b ^ (k - 1 - t)) % b = U[t] := by
  subst hk
  induction U using List.reverseRecOn with
  | nil => simp
  | append_singleton U d ih =>
    have hd : d < b := hU d (by simp)
    have hU' : ∀ e ∈ U, e < b := fun e he => hU e (by simp [he])
    obtain ⟨ih1, ih2⟩ := ih hU'
    have hfold : (U ++ [d]).foldl (fun acc e => acc * b + e) 0
        = U.foldl (fun acc e => acc * b + e) 0 * b + d := by
      simp [List.foldl_append]
    have hlen : (U ++ [d]).length = U.length + 1 := by simp
    rw [hfold]
    generalize U.foldl (fun acc e => acc * b + e) 0 = V at ih1 ih2 ⊢
    constructor
    · rw [hlen, pow_succ]
      nlinarith
    · intro t ht
      have ht' : t < U.length + 1 := by rw [hlen] at ht; exact ht
      by_cases htU : t < U.length
      · rw [List.getElem_append_left htU]
        have e1 : (U ++ [d]).length - 1 - t = (U.length - 1 - t) + 1 := by rw [hlen]; omega
        rw [e1, pow_succ', ← Nat.div_div_eq_div_mul]
        have e2 : (V * b + d) / b = V := by
          rw [mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hd, add_zero]
        rw [e2]
        exact ih2 t htU
      · have ht'' : t = U.length := by omega
        subst ht''
        simp [Nat.mod_eq_of_lt hd]

/-- Auxiliary for `exists_computable_isAbsolutelyNormal_stepE_cover_cover`: digit `i` of
`α ∈ [0, 1)` in base `b` is digit `i` of the `L`-digit cell numeral `⌊b ^ L α⌋₊`. -/
private lemma exists_computable_isAbsolutelyNormal_E_cell_digit (b : ℕ) (hb : 2 ≤ b) (L : ℕ)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (i : ℕ) (hi : i < L) :
    baseDigit b α i = (⌊(b : ℝ) ^ L * α⌋₊ / b ^ (L - 1 - i)) % b := by
  unfold baseDigit
  rw [Int.fract_eq_self.mpr ⟨hα0, hα1⟩]
  congr 1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hpos : (0 : ℝ) < (b : ℝ) ^ (L - 1 - i) := by positivity
  have key : (b : ℝ) ^ (i + 1) * α = ((b : ℝ) ^ L * α) / ((b ^ (L - 1 - i) : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    rw [eq_div_iff hpos.ne']
    have hL : L = (i + 1) + (L - 1 - i) := by omega
    conv_rhs => rw [hL, pow_add]
    ring
  rw [key, Nat.floor_div_natCast]

/-- Auxiliary for `exists_computable_isAbsolutelyNormal_stepE_cover_cover`: cardinality of a
`Finset` filter of a range equals the length of the corresponding `List` filter. -/
private lemma exists_computable_isAbsolutelyNormal_E_card_eq (p : ℕ → Prop) [DecidablePred p]
    (N : ℕ) :
    ((Finset.range N).filter p).card = ((List.range N).filter (fun j => decide (p j))).length := by
  rfl

/-- Auxiliary for `exists_computable_isAbsolutelyNormal_stepE_cover_cover`: the two truncated
subtractions add up to the absolute difference. -/
private lemma exists_computable_isAbsolutelyNormal_E_natabs (x N : ℕ) :
    (((x - N) + (N - x) : ℕ) : ℝ) = |(x : ℝ) - N| := by
  rcases le_total x N with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
    rw [abs_of_nonpos (by exact_mod_cast (by omega : (x : ℤ) - N ≤ 0))]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]
    rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ (x : ℤ) - N))]

/-- Step E of the proof of `exists_computable_isAbsolutelyNormal`: if `α ∈ [0, 1)` has a
nonempty word `U` whose frequency in the first `N` positions deviates from `b ^ (-|U|)` by at
least `1 / R`, then `α` lies in an open interval of the cover for words of length `|U|`. -/
private lemma exists_computable_isAbsolutelyNormal_stepE_cover_cover
    (b N R : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (hR : 1 ≤ R)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (U : List ℕ) (hk : 1 ≤ U.length)
    (hU : ∀ d ∈ U, d < b)
    (hdev : (1 : ℝ) / R ≤ |digitOccurrenceFreq b α U N - (b : ℝ)⁻¹ ^ U.length|) :
    ∃ I ∈ exists_computable_isAbsolutelyNormal_cover b U.length N R,
      (I.1 : ℝ) < α ∧ α < (I.2 : ℝ) := by
  classical
  generalize hUlen : U.length = k at hk hdev ⊢
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbL : (0 : ℝ) < (b : ℝ) ^ (N + k - 1) := by positivity
  have hx0 : 0 ≤ (b : ℝ) ^ (N + k - 1) * α := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊(b : ℝ) ^ (N + k - 1) * α⌋₊ := ⟨_, rfl⟩
  have hm1 : (m : ℝ) ≤ (b : ℝ) ^ (N + k - 1) * α := by rw [hm]; exact Nat.floor_le hx0
  have hm2 : (b : ℝ) ^ (N + k - 1) * α < (m : ℝ) + 1 := by rw [hm]; exact Nat.lt_floor_add_one _
  have hmlt : m < b ^ (N + k - 1) := by
    have h1 : (m : ℝ) < (b : ℝ) ^ (N + k - 1) := by
      calc (m : ℝ) ≤ (b : ℝ) ^ (N + k - 1) * α := hm1
        _ < (b : ℝ) ^ (N + k - 1) * 1 := mul_lt_mul_of_pos_left hα1 hbL
        _ = (b : ℝ) ^ (N + k - 1) := mul_one _
    exact_mod_cast h1
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = U.foldl (fun acc d => acc * b + d) 0 := ⟨_, rfl⟩
  obtain ⟨hu1, hu2⟩ := exists_computable_isAbsolutelyNormal_E_foldl b (by omega) U hU k hUlen
  rw [← hu] at hu1 hu2
  -- digit match
  have hmatch : ∀ j < N, DigitOccursAt b α U j ↔
      exists_computable_isAbsolutelyNormal_win b k N m u j = true := by
    intro j hj
    unfold DigitOccursAt exists_computable_isAbsolutelyNormal_win
    rw [List.all_eq_true]
    constructor
    · intro h t ht
      rw [List.mem_range] at ht
      have htU : t < U.length := by omega
      have h1 := h t htU
      have h2 := exists_computable_isAbsolutelyNormal_E_cell_digit b hb (N + k - 1) α hα0 hα1
        (j + t) (by omega)
      have h3 := hu2 t htU
      rw [← hm] at h2
      rw [decide_eq_true_iff]
      have e1 : N + k - 1 - 1 - (j + t) = N + k - 2 - (j + t) := by omega
      rw [e1] at h2
      rw [← h2, h1, h3]
    · intro h t htU
      have ht : t < k := by omega
      have h1 := h t (List.mem_range.mpr ht)
      rw [decide_eq_true_iff] at h1
      have h2 := exists_computable_isAbsolutelyNormal_E_cell_digit b hb (N + k - 1) α hα0 hα1
        (j + t) (by omega)
      have h3 := hu2 t htU
      rw [← hm] at h2
      have e1 : N + k - 1 - 1 - (j + t) = N + k - 2 - (j + t) := by omega
      rw [e1] at h2
      rw [h2, h1, h3]
  have hfreq : digitOccurrenceFreq b α U N
      = (exists_computable_isAbsolutelyNormal_cnt b k N m u : ℝ) / N := by
    unfold digitOccurrenceFreq exists_computable_isAbsolutelyNormal_cnt
    congr 2
    rw [exists_computable_isAbsolutelyNormal_E_card_eq]
    congr 1
    apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hmatch j hj
  have hbad : exists_computable_isAbsolutelyNormal_bad b k N R m u = true := by
    unfold exists_computable_isAbsolutelyNormal_bad
    rw [decide_eq_true_iff]
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = exists_computable_isAbsolutelyNormal_cnt b k N m u := ⟨_, rfl⟩
    rw [← hc]
    rw [hfreq, ← hc] at hdev
    have hBpos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    have habs : |(c : ℝ) / N - (b : ℝ)⁻¹ ^ k|
        = |((c * b ^ k : ℕ) : ℝ) - N| / (N * (b : ℝ) ^ k) := by
      rw [inv_pow]
      have h1 : (c : ℝ) / N - ((b : ℝ) ^ k)⁻¹
          = (((c * b ^ k : ℕ) : ℝ) - N) / (N * (b : ℝ) ^ k) := by
        push_cast
        field_simp
      rw [h1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N * (b : ℝ) ^ k)]
    rw [habs, le_div_iff₀ (by positivity)] at hdev
    have h2 : (N : ℝ) * (b : ℝ) ^ k ≤ R * |((c * b ^ k : ℕ) : ℝ) - N| := by
      have h3 : (1 : ℝ) / R * (N * (b : ℝ) ^ k) * R ≤ |((c * b ^ k : ℕ) : ℝ) - N| * R :=
        mul_le_mul_of_nonneg_right hdev hRpos.le
      have h4 : (1 : ℝ) / R * (N * (b : ℝ) ^ k) * R = N * (b : ℝ) ^ k := by
        field_simp
      rw [h4] at h3
      linarith
    have h5 : ((N * b ^ k : ℕ) : ℝ)
        ≤ ((R * ((c * b ^ k - N) + (N - c * b ^ k)) : ℕ) : ℝ) := by
      rw [Nat.cast_mul R, exists_computable_isAbsolutelyNormal_E_natabs]
      push_cast at h2 ⊢
      linarith
    exact_mod_cast h5
  refine ⟨(((m : ℚ) - 1) / ((b ^ (N + k - 1) : ℕ) : ℚ),
    ((m : ℚ) + 1) / ((b ^ (N + k - 1) : ℕ) : ℚ)), ?_, ?_, ?_⟩
  · unfold exists_computable_isAbsolutelyNormal_cover
    rw [List.mem_flatMap]
    refine ⟨u, List.mem_range.mpr hu1, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨m, List.mem_range.mpr hmlt, ?_⟩
    simp [hbad]
  · push_cast
    rw [div_lt_iff₀ hbL]
    linarith
  · push_cast
    rw [lt_div_iff₀ hbL]
    linarith


/-- A `flatMap` of a computable family over a computable list is computable. -/
private lemma exists_computable_isAbsolutelyNormal_F_computable_flatMap
    {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    {l : α → List β} {f : α → β → List σ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable fun a => (l a).flatMap (f a) :=
  (Primrec.list_flatten.to_comp.comp (Computable.list_map hl hf)).of_eq fun a => by
    rw [List.flatMap_def]

/-- `win` is primitive recursive (with primitive recursive parameters). -/
private lemma exists_computable_isAbsolutelyNormal_F_pr_win {γ : Type} [Primcodable γ]
    {b k N m u j : γ → ℕ} (hb : Primrec b) (hk : Primrec k) (hN : Primrec N)
    (hm : Primrec m) (hu : Primrec u) (hj : Primrec j) :
    Primrec fun a => exists_computable_isAbsolutelyNormal_win (b a) (k a) (N a) (m a) (u a)
      (j a) := by
  unfold exists_computable_isAbsolutelyNormal_win
  have hb' : Primrec fun q : γ × ℕ => b q.1 := hb.comp Primrec.fst
  have hk' : Primrec fun q : γ × ℕ => k q.1 := hk.comp Primrec.fst
  have hN' : Primrec fun q : γ × ℕ => N q.1 := hN.comp Primrec.fst
  have hm' : Primrec fun q : γ × ℕ => m q.1 := hm.comp Primrec.fst
  have hu' : Primrec fun q : γ × ℕ => u q.1 := hu.comp Primrec.fst
  have hj' : Primrec fun q : γ × ℕ => j q.1 := hj.comp Primrec.fst
  have ht : Primrec fun q : γ × ℕ => q.2 := Primrec.snd
  have e1 : Primrec fun q : γ × ℕ => m q.1 / b q.1 ^ (N q.1 + k q.1 - 2 - (j q.1 + q.2)) :=
    Primrec.nat_div.comp hm' (exists_computable_isAbsolutelyNormal_primrec_pow.comp hb'
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp hN' hk')
        (Primrec.const 2)) (Primrec.nat_add.comp hj' ht)))
  have e2 : Primrec fun q : γ × ℕ =>
      (m q.1 / b q.1 ^ (N q.1 + k q.1 - 2 - (j q.1 + q.2))) % b q.1 :=
    Primrec.nat_mod.comp e1 hb'
  have e3 : Primrec fun q : γ × ℕ => u q.1 / b q.1 ^ (k q.1 - 1 - q.2) :=
    Primrec.nat_div.comp hu' (exists_computable_isAbsolutelyNormal_primrec_pow.comp hb'
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp hk' (Primrec.const 1)) ht))
  have e4 : Primrec fun q : γ × ℕ => (u q.1 / b q.1 ^ (k q.1 - 1 - q.2)) % b q.1 :=
    Primrec.nat_mod.comp e3 hb'
  exact Kolmogorov.list_all_primrec (f := fun a => List.range (k a))
    (p := fun a t => decide ((m a / b a ^ (N a + k a - 2 - (j a + t))) % b a
      = (u a / b a ^ (k a - 1 - t)) % b a))
    (Primrec.list_range.comp hk) (PrimrecRel.comp Primrec.eq e2 e4).decide

/-- `cnt` is primitive recursive. -/
private lemma exists_computable_isAbsolutelyNormal_F_pr_cnt {γ : Type} [Primcodable γ]
    {b k N m u : γ → ℕ} (hb : Primrec b) (hk : Primrec k) (hN : Primrec N)
    (hm : Primrec m) (hu : Primrec u) :
    Primrec fun a => exists_computable_isAbsolutelyNormal_cnt (b a) (k a) (N a) (m a) (u a) := by
  unfold exists_computable_isAbsolutelyNormal_cnt
  refine Primrec.list_length.comp ?_
  exact Kolmogorov.list_filter_primrec (f := fun a => List.range (N a))
    (p := fun a j => exists_computable_isAbsolutelyNormal_win (b a) (k a) (N a) (m a) (u a) j)
    (Primrec.list_range.comp hN)
    (exists_computable_isAbsolutelyNormal_F_pr_win (hb.comp Primrec.fst) (hk.comp Primrec.fst)
      (hN.comp Primrec.fst) (hm.comp Primrec.fst) (hu.comp Primrec.fst) Primrec.snd)

/-- `bad` is primitive recursive. -/
private lemma exists_computable_isAbsolutelyNormal_F_pr_bad {γ : Type} [Primcodable γ]
    {b k N R m u : γ → ℕ} (hb : Primrec b) (hk : Primrec k) (hN : Primrec N)
    (hR : Primrec R) (hm : Primrec m) (hu : Primrec u) :
    Primrec fun a => exists_computable_isAbsolutelyNormal_bad (b a) (k a) (N a) (R a) (m a)
      (u a) := by
  unfold exists_computable_isAbsolutelyNormal_bad
  have hc := exists_computable_isAbsolutelyNormal_F_pr_cnt hb hk hN hm hu
  have hbk : Primrec fun a => b a ^ k a :=
    exists_computable_isAbsolutelyNormal_primrec_pow.comp hb hk
  have hcb := Primrec.nat_mul.comp hc hbk
  have h1 := Primrec.nat_sub.comp hcb hN
  have h2 := Primrec.nat_sub.comp hN hcb
  have h3 := Primrec.nat_add.comp h1 h2
  have h4 := Primrec.nat_mul.comp hR h3
  have h5 := Primrec.nat_mul.comp hN hbk
  exact (PrimrecRel.comp Primrec.nat_le h5 h4).decide

/-- The padded interval around the numeral `m` at denominator `D` is computable (division by
zero gives `0`, as in `ℚ`). -/
private lemma exists_computable_isAbsolutelyNormal_F_computable_interval :
    Computable (fun p : ℕ × ℕ =>
      (((p.1 : ℚ) - 1) / (p.2 : ℚ), ((p.1 : ℚ) + 1) / (p.2 : ℚ))) := by
  have hD : Computable (fun p : ℕ × ℕ => max p.2 1) :=
    (Primrec.nat_max.comp Primrec.snd (Primrec.const 1)).to_comp
  have hDpos : ∀ p : ℕ × ℕ, 0 < max p.2 1 := fun p => lt_max_of_lt_right Nat.one_pos
  have hcast : Primrec (fun p : ℕ × ℕ => (p.1 : ℤ)) :=
    ComputableReals.primrec_natCastInt.comp Primrec.fst
  have hn1 : Computable (fun p : ℕ × ℕ => (p.1 : ℤ) - 1) :=
    (Kolmogorov.primrec_intSub.comp hcast (Primrec.const 1)).to_comp
  have hn2 : Computable (fun p : ℕ × ℕ => (p.1 : ℤ) + 1) :=
    (Kolmogorov.primrec_intAdd.comp hcast (Primrec.const 1)).to_comp
  have hg1 : Computable (fun p : ℕ × ℕ => ((p.1 : ℚ) - 1) / ((max p.2 1 : ℕ) : ℚ)) :=
    Kolmogorov.computable_of_num_den hn1 hD hDpos (fun p => by push_cast; ring)
  have hg2 : Computable (fun p : ℕ × ℕ => ((p.1 : ℚ) + 1) / ((max p.2 1 : ℕ) : ℚ)) :=
    Kolmogorov.computable_of_num_den hn2 hD hDpos (fun p => by push_cast; ring)
  have hz : Computable (fun p : ℕ × ℕ => decide (p.2 = 0)) :=
    (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0)).decide.to_comp
  have hA : Computable (fun p : ℕ × ℕ => ((p.1 : ℚ) - 1) / (p.2 : ℚ)) :=
    (Computable.cond hz (Computable.const (0 : ℚ)) hg1).of_eq fun p => by
      by_cases h : p.2 = 0
      · simp [h]
      · have hm : max p.2 1 = p.2 := max_eq_left (Nat.one_le_iff_ne_zero.mpr h)
        simp only [h, decide_false, Bool.cond_false]
        rw [hm]
  have hB : Computable (fun p : ℕ × ℕ => ((p.1 : ℚ) + 1) / (p.2 : ℚ)) :=
    (Computable.cond hz (Computable.const (0 : ℚ)) hg2).of_eq fun p => by
      by_cases h : p.2 = 0
      · simp [h]
      · have hm : max p.2 1 = p.2 := max_eq_left (Nat.one_le_iff_ne_zero.mpr h)
        simp only [h, decide_false, Bool.cond_false]
        rw [hm]
  exact Computable.pair hA hB

/-- The padded interval is computable (abstract parameters). -/
private lemma exists_computable_isAbsolutelyNormal_F_computable_intervalPair {γ : Type}
    [Primcodable γ] {m D : γ → ℕ} (hm : Computable m) (hD : Computable D) :
    Computable fun a =>
      (((((m a : ℕ) : ℚ) - 1) / ((D a : ℕ) : ℚ)), ((((m a : ℕ) : ℚ) + 1) / ((D a : ℕ) : ℚ))) := by
  have := exists_computable_isAbsolutelyNormal_F_computable_interval.comp (Computable.pair hm hD)
  exact this

/-- A singleton list of a computable pair of rationals is computable. -/
private lemma exists_computable_isAbsolutelyNormal_F_computable_singleton0 {γ : Type}
    [Primcodable γ] {x : γ → ℚ × ℚ} (hx : Computable x) :
    Computable fun a => [x a] := by
  have h0 : Computable fun _ : γ => ([] : List (ℚ × ℚ)) := Computable.const []
  exact Computable.list_cons.comp hx h0

/-- The singleton list holding the padded interval is computable (abstract parameters). -/
private lemma exists_computable_isAbsolutelyNormal_F_computable_singleton {γ : Type}
    [Primcodable γ] {m D : γ → ℕ} (hm : Computable m) (hD : Computable D) :
    Computable fun a =>
      [((((m a : ℕ) : ℚ) - 1) / ((D a : ℕ) : ℚ), (((m a : ℕ) : ℚ) + 1) / ((D a : ℕ) : ℚ))] :=
  exists_computable_isAbsolutelyNormal_F_computable_singleton0
    (exists_computable_isAbsolutelyNormal_F_computable_intervalPair hm hD)

/-- The cover is computable (with primitive recursive parameters). -/
private lemma exists_computable_isAbsolutelyNormal_F_computable_cover {γ : Type} [Primcodable γ]
    {b k N R : γ → ℕ} (hb : Primrec b) (hk : Primrec k) (hN : Primrec N) (hR : Primrec R) :
    Computable fun a =>
      exists_computable_isAbsolutelyNormal_cover (b a) (k a) (N a) (R a) := by
  unfold exists_computable_isAbsolutelyNormal_cover
  have hD : Primrec fun a => b a ^ (N a + k a - 1) :=
    exists_computable_isAbsolutelyNormal_primrec_pow.comp hb
      (Primrec.nat_sub.comp (Primrec.nat_add.comp hN hk) (Primrec.const 1))
  refine exists_computable_isAbsolutelyNormal_F_computable_flatMap
    (l := fun a => List.range (b a ^ k a))
    (f := fun a u => (List.range (b a ^ (N a + k a - 1))).flatMap (fun m =>
      if exists_computable_isAbsolutelyNormal_bad (b a) (k a) (N a) (R a) m u = true then
        [(((m : ℚ) - 1) / ((b a ^ (N a + k a - 1) : ℕ) : ℚ),
          ((m : ℚ) + 1) / ((b a ^ (N a + k a - 1) : ℕ) : ℚ))]
      else [])) ?_ ?_
  · exact (Primrec.list_range.comp
      (exists_computable_isAbsolutelyNormal_primrec_pow.comp hb hk)).to_comp
  · refine exists_computable_isAbsolutelyNormal_F_computable_flatMap
      (l := fun q : γ × ℕ => List.range (b q.1 ^ (N q.1 + k q.1 - 1)))
      (f := fun (q : γ × ℕ) (m : ℕ) =>
        if exists_computable_isAbsolutelyNormal_bad (b q.1) (k q.1) (N q.1) (R q.1) m q.2
            = true then
          [(((m : ℚ) - 1) / ((b q.1 ^ (N q.1 + k q.1 - 1) : ℕ) : ℚ),
            ((m : ℚ) + 1) / ((b q.1 ^ (N q.1 + k q.1 - 1) : ℕ) : ℚ))]
        else []) ?_ ?_
    · exact (Primrec.list_range.comp (hD.comp Primrec.fst)).to_comp
    · have hbad : Primrec fun r : (γ × ℕ) × ℕ =>
          exists_computable_isAbsolutelyNormal_bad (b r.1.1) (k r.1.1) (N r.1.1) (R r.1.1) r.2
            r.1.2 :=
        exists_computable_isAbsolutelyNormal_F_pr_bad
          (hb.comp (Primrec.fst.comp Primrec.fst)) (hk.comp (Primrec.fst.comp Primrec.fst))
          (hN.comp (Primrec.fst.comp Primrec.fst)) (hR.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd (Primrec.snd.comp Primrec.fst)
      have hI := exists_computable_isAbsolutelyNormal_F_computable_singleton
        (m := fun r : (γ × ℕ) × ℕ => r.2)
        (D := fun r : (γ × ℕ) × ℕ => b r.1.1 ^ (N r.1.1 + k r.1.1 - 1))
        Computable.snd (hD.comp (Primrec.fst.comp Primrec.fst)).to_comp
      exact (Computable.cond hbad.to_comp hI (Computable.const [])).of_eq fun r => by
        cases h : exists_computable_isAbsolutelyNormal_bad (b r.1.1) (k r.1.1) (N r.1.1)
          (R r.1.1) r.2 r.1.2 <;> simp [h]

/-- Step F of the proof of `exists_computable_isAbsolutelyNormal`: the layers form a
computable family. -/
private lemma exists_computable_isAbsolutelyNormal_stepF_layer_computable :
    Computable (fun t : ℕ => exists_computable_isAbsolutelyNormal_layer t) := by
  unfold exists_computable_isAbsolutelyNormal_layer
  have hpow2 : Primrec fun t : ℕ => (t + 1) ^ 2 + 1 :=
    Primrec.nat_add.comp (exists_computable_isAbsolutelyNormal_primrec_pow.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1)) (Primrec.const 2)) (Primrec.const 1)
  refine exists_computable_isAbsolutelyNormal_F_computable_flatMap
    (l := fun t : ℕ => List.range ((t + 1) ^ 2 + 1))
    (f := fun (t b : ℕ) => (List.range ((t + 1) ^ 2 + 1)).flatMap (fun k =>
      if 2 ≤ b ∧ 1 ≤ k ∧ 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2 then
        exists_computable_isAbsolutelyNormal_cover b k ((t + 1) ^ 6) (t + 1)
      else [])) ?_ ?_
  · exact (Primrec.list_range.comp hpow2).to_comp
  · refine exists_computable_isAbsolutelyNormal_F_computable_flatMap
      (l := fun q : ℕ × ℕ => List.range ((q.1 + 1) ^ 2 + 1))
      (f := fun (q : ℕ × ℕ) (k : ℕ) =>
        if 2 ≤ q.2 ∧ 1 ≤ k ∧ 64 * k * q.2 ^ k * 2 ^ (q.2 + k) ≤ (q.1 + 1) ^ 2 then
          exists_computable_isAbsolutelyNormal_cover q.2 k ((q.1 + 1) ^ 6) (q.1 + 1)
        else []) ?_ ?_
    · exact (Primrec.list_range.comp (hpow2.comp Primrec.fst)).to_comp
    · -- the guarded cover
      have ht : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.1 := Primrec.fst.comp Primrec.fst
      have hb : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.2 := Primrec.snd.comp Primrec.fst
      have hk : Primrec fun r : (ℕ × ℕ) × ℕ => r.2 := Primrec.snd
      have ht1 : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.1 + 1 :=
        Primrec.nat_add.comp ht (Primrec.const 1)
      have hbk : Primrec fun r : (ℕ × ℕ) × ℕ => r.1.2 ^ r.2 :=
        exists_computable_isAbsolutelyNormal_primrec_pow.comp hb hk
      have hlhs : Primrec fun r : (ℕ × ℕ) × ℕ => 64 * r.2 * r.1.2 ^ r.2 * 2 ^ (r.1.2 + r.2) :=
        Primrec.nat_mul.comp
          (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 64) hk) hbk)
          (exists_computable_isAbsolutelyNormal_primrec_pow.comp (Primrec.const 2)
            (Primrec.nat_add.comp hb hk))
      have hrhs : Primrec fun r : (ℕ × ℕ) × ℕ => (r.1.1 + 1) ^ 2 :=
        exists_computable_isAbsolutelyNormal_primrec_pow.comp ht1 (Primrec.const 2)
      have hcond : Primrec fun r : (ℕ × ℕ) × ℕ =>
          decide (2 ≤ r.1.2 ∧ 1 ≤ r.2 ∧ 64 * r.2 * r.1.2 ^ r.2 * 2 ^ (r.1.2 + r.2)
            ≤ (r.1.1 + 1) ^ 2) :=
        ((PrimrecRel.comp Primrec.nat_le (Primrec.const 2) hb).and
          ((PrimrecRel.comp Primrec.nat_le (Primrec.const 1) hk).and
            (PrimrecRel.comp Primrec.nat_le hlhs hrhs))).decide
      have hN6 : Primrec fun r : (ℕ × ℕ) × ℕ => (r.1.1 + 1) ^ 6 :=
        exists_computable_isAbsolutelyNormal_primrec_pow.comp ht1 (Primrec.const 6)
      have hcov : Computable fun r : (ℕ × ℕ) × ℕ =>
          exists_computable_isAbsolutelyNormal_cover r.1.2 r.2 ((r.1.1 + 1) ^ 6) (r.1.1 + 1) :=
        exists_computable_isAbsolutelyNormal_F_computable_cover hb hk hN6 ht1
      exact (Computable.cond hcond.to_comp hcov (Computable.const [])).of_eq fun r => by
        rw [Bool.cond_decide]
private lemma exists_computable_isAbsolutelyNormal_G_len_append (l l' : List (ℚ × ℚ)) :
    exists_computable_isAbsolutelyNormal_len (l ++ l') =
      exists_computable_isAbsolutelyNormal_len l + exists_computable_isAbsolutelyNormal_len l' := by
  unfold exists_computable_isAbsolutelyNormal_len
  rw [List.map_append, List.sum_append]

private lemma exists_computable_isAbsolutelyNormal_G_len_flatMap {α : Type*} (l : List α)
    (f : α → List (ℚ × ℚ)) :
    exists_computable_isAbsolutelyNormal_len (l.flatMap f) =
      (l.map (fun x => exists_computable_isAbsolutelyNormal_len (f x))).sum := by
  induction l with
  | nil => simp [exists_computable_isAbsolutelyNormal_len]
  | cons x t ih =>
    rw [List.flatMap_cons, exists_computable_isAbsolutelyNormal_G_len_append, ih,
      List.map_cons, List.sum_cons]

private lemma exists_computable_isAbsolutelyNormal_G_sum_range (n : ℕ) (g : ℕ → ℝ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The `u`-th inner list of the cover has total length `(# bad numerals) * (2 / b ^ L)`. -/
private lemma exists_computable_isAbsolutelyNormal_G_inner_len (b k N R u : ℕ) :
    exists_computable_isAbsolutelyNormal_len
      ((List.range (b ^ (N + k - 1))).flatMap (fun m =>
        if exists_computable_isAbsolutelyNormal_bad b k N R m u = true then
          [(((m : ℚ) - 1) / ((b ^ (N + k - 1) : ℕ) : ℚ),
            ((m : ℚ) + 1) / ((b ^ (N + k - 1) : ℕ) : ℚ))]
        else []))
    = (((Finset.range (b ^ (N + k - 1))).filter
        (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)).card : ℝ) *
      (2 / ((b : ℝ) ^ (N + k - 1))) := by
  rw [exists_computable_isAbsolutelyNormal_G_len_flatMap,
    exists_computable_isAbsolutelyNormal_G_sum_range]
  have hterm : ∀ m : ℕ,
      exists_computable_isAbsolutelyNormal_len
        (if exists_computable_isAbsolutelyNormal_bad b k N R m u = true then
          [(((m : ℚ) - 1) / ((b ^ (N + k - 1) : ℕ) : ℚ),
            ((m : ℚ) + 1) / ((b ^ (N + k - 1) : ℕ) : ℚ))]
        else [])
      = (if exists_computable_isAbsolutelyNormal_bad b k N R m u = true then (1 : ℝ) else 0) *
        (2 / ((b : ℝ) ^ (N + k - 1))) := by
    intro m
    by_cases h : exists_computable_isAbsolutelyNormal_bad b k N R m u = true
    · simp only [h, ↓reduceIte, one_mul]
      unfold exists_computable_isAbsolutelyNormal_len
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      push_cast
      ring
    · simp only [h, Bool.false_eq_true, ↓reduceIte, zero_mul]
      unfold exists_computable_isAbsolutelyNormal_len
      simp
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole]

/-- Step G of the proof of `exists_computable_isAbsolutelyNormal`: the intervals of a
cover have nonnegative length, and the total length of a cover is `≤ 4 k b^k R² / N`. -/
private lemma exists_computable_isAbsolutelyNormal_stepG_cover_len
    (b k N R : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (hN : 1 ≤ N) (hR : 1 ≤ R) :
    (∀ I ∈ exists_computable_isAbsolutelyNormal_cover b k N R, I.1 ≤ I.2) ∧
    exists_computable_isAbsolutelyNormal_len (exists_computable_isAbsolutelyNormal_cover b k N R)
      ≤ 4 * k * (b : ℝ) ^ k * R ^ 2 / N := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hDpos : (0 : ℝ) < (b : ℝ) ^ (N + k - 1) := pow_pos hbpos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro I hI
    unfold exists_computable_isAbsolutelyNormal_cover at hI
    rw [List.mem_flatMap] at hI
    obtain ⟨u, _, hI⟩ := hI
    rw [List.mem_flatMap] at hI
    obtain ⟨m, _, hI⟩ := hI
    by_cases h : exists_computable_isAbsolutelyNormal_bad b k N R m u = true
    · simp only [h, ↓reduceIte] at hI
      rw [List.mem_singleton] at hI
      subst hI
      have hD : (0 : ℚ) < ((b ^ (N + k - 1) : ℕ) : ℚ) := by
        exact_mod_cast pow_pos (by omega : 0 < b) _
      exact div_le_div_of_nonneg_right (by linarith) hD.le
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hI
      simp at hI
  · unfold exists_computable_isAbsolutelyNormal_cover
    rw [exists_computable_isAbsolutelyNormal_G_len_flatMap,
      exists_computable_isAbsolutelyNormal_G_sum_range]
    simp_rw [exists_computable_isAbsolutelyNormal_G_inner_len]
    have hu : ∀ u ∈ Finset.range (b ^ k),
        (((Finset.range (b ^ (N + k - 1))).filter
          (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)).card : ℝ) *
            (2 / ((b : ℝ) ^ (N + k - 1))) ≤ 4 * k * (R : ℝ) ^ 2 / N := by
      intro u _
      have hD := exists_computable_isAbsolutelyNormal_stepD_count_bad b k N R u hb hk hN hR
      calc (((Finset.range (b ^ (N + k - 1))).filter
          (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)).card : ℝ) *
            (2 / ((b : ℝ) ^ (N + k - 1)))
          ≤ ((b : ℝ) ^ (N + k - 1) * (2 * k * R ^ 2 / N)) * (2 / ((b : ℝ) ^ (N + k - 1))) := by
            gcongr
        _ = 4 * k * (R : ℝ) ^ 2 / N := by
            field_simp
            ring
    calc ∑ u ∈ Finset.range (b ^ k),
          (((Finset.range (b ^ (N + k - 1))).filter
            (fun m => exists_computable_isAbsolutelyNormal_bad b k N R m u = true)).card : ℝ) *
              (2 / ((b : ℝ) ^ (N + k - 1)))
        ≤ ∑ _u ∈ Finset.range (b ^ k), 4 * k * (R : ℝ) ^ 2 / N := Finset.sum_le_sum hu
      _ = 4 * k * (b : ℝ) ^ k * R ^ 2 / N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

/-- Auxiliary for Step H: the total length of a concatenation is the sum of the total lengths. -/
private lemma exists_computable_isAbsolutelyNormal_HI_len_append (l₁ l₂ : List (ℚ × ℚ)) :
    exists_computable_isAbsolutelyNormal_len (l₁ ++ l₂) =
      exists_computable_isAbsolutelyNormal_len l₁ + exists_computable_isAbsolutelyNormal_len l₂ :=
          by
  simp [exists_computable_isAbsolutelyNormal_len, List.map_append, List.sum_append]

/-- Auxiliary for Step H: the total length of a `flatMap` is the sum of the total lengths. -/
private lemma exists_computable_isAbsolutelyNormal_HI_len_flatMap {α : Type*} (l : List α)
    (f : α → List (ℚ × ℚ)) :
    exists_computable_isAbsolutelyNormal_len (l.flatMap f) =
      (l.map (fun x => exists_computable_isAbsolutelyNormal_len (f x))).sum := by
  induction l with
  | nil => simp [exists_computable_isAbsolutelyNormal_len]
  | cons a l ih =>
    rw [List.flatMap_cons, exists_computable_isAbsolutelyNormal_HI_len_append, ih,
      List.map_cons, List.sum_cons]

/-- Auxiliary for Step H: the sum of a mapped `List.range` as a `Finset` sum. -/
private lemma exists_computable_isAbsolutelyNormal_HI_sum_range_map (n : ℕ) (g : ℕ → ℝ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Auxiliary for Step H: `∑_{b ≥ 2} 2^{-b} ≤ 1/2`, finite version. -/
private lemma exists_computable_isAbsolutelyNormal_HI_geom2 (B : ℕ) :
    ∑ b ∈ Finset.range B, (if 2 ≤ b then (1 / 2 : ℝ) ^ b else 0) ≤ 1 / 2 := by
  have hgeom := sum_geometric_two_le B
  rcases B with _ | _ | B
  · simp
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h1 : ∀ i ∈ Finset.range B, (if 2 ≤ i + 1 + 1 then (1 / 2 : ℝ) ^ (i + 1 + 1) else 0)
        = (1 / 4 : ℝ) * (1 / 2) ^ i := by
      intro i _
      rw [ite_eq_left (by omega)]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    simp only [show ¬ (2 ≤ 0 + 1) by omega, show ¬ (2 ≤ 0) by omega, ite_false, add_zero]
    have := sum_geometric_two_le B
    linarith

/-- Auxiliary for Step H: `∑_{k ≥ 1} 2^{-k} ≤ 1`, finite version. -/
private lemma exists_computable_isAbsolutelyNormal_HI_geom1 (B : ℕ) :
    ∑ k ∈ Finset.range B, (if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0) ≤ 1 := by
  rcases B with _ | B
  · simp
  · rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ Finset.range B, (if 1 ≤ i + 1 then (1 / 2 : ℝ) ^ (i + 1) else 0)
        = (1 / 2 : ℝ) * (1 / 2) ^ i := by
      intro i _
      rw [ite_eq_left (by omega)]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    simp only [show ¬ (1 ≤ 0) by omega, ite_false, add_zero]
    have := sum_geometric_two_le B
    linarith

/-- Auxiliary for Step H: the length of the cover of an active pair `(b, k)` in layer `t`. -/
private lemma exists_computable_isAbsolutelyNormal_HI_term_le (t b k : ℕ) (hb : 2 ≤ b)
    (hk : 1 ≤ k) (hact : 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2) :
    exists_computable_isAbsolutelyNormal_len
        (exists_computable_isAbsolutelyNormal_cover b k ((t + 1) ^ 6) (t + 1))
      ≤ 1 / (16 * ((t : ℝ) + 1) ^ 2) * ((1 / 2 : ℝ) ^ b * (1 / 2 : ℝ) ^ k) := by
  have hG := (exists_computable_isAbsolutelyNormal_stepG_cover_len b k ((t + 1) ^ 6) (t + 1) hb hk
    (Nat.one_le_pow _ _ (by omega)) (by omega)).2
  refine hG.trans ?_
  have hx : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hact' : (64 : ℝ) * k * (b : ℝ) ^ k * 2 ^ (b + k) ≤ ((t : ℝ) + 1) ^ 2 := by
    exact_mod_cast hact
  have hP : (0 : ℝ) < 2 ^ (b + k) := by positivity
  have hrhs : 1 / (16 * ((t : ℝ) + 1) ^ 2) * ((1 / 2 : ℝ) ^ b * (1 / 2 : ℝ) ^ k)
      = 1 / (16 * ((t : ℝ) + 1) ^ 2 * 2 ^ (b + k)) := by
    rw [← pow_add]
    field_simp
    rw [← mul_pow]
    norm_num
  rw [hrhs]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hx4 : (0 : ℝ) ≤ ((t : ℝ) + 1) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hact' hx4]

/-- Step H of the proof of `exists_computable_isAbsolutelyNormal`: the intervals of a
layer have nonnegative length, and the total length of layer `t` is `≤ 1 / (32 (t + 1)²)`. -/
private lemma exists_computable_isAbsolutelyNormal_stepH_layer_len (t : ℕ) :
    (∀ I ∈ exists_computable_isAbsolutelyNormal_layer t, I.1 ≤ I.2) ∧
    exists_computable_isAbsolutelyNormal_len (exists_computable_isAbsolutelyNormal_layer t)
      ≤ 1 / (32 * ((t : ℝ) + 1) ^ 2) := by
  refine ⟨?_, ?_⟩
  · intro I hI
    unfold exists_computable_isAbsolutelyNormal_layer at hI
    rw [List.mem_flatMap] at hI
    obtain ⟨b, _, hI⟩ := hI
    rw [List.mem_flatMap] at hI
    obtain ⟨k, _, hI⟩ := hI
    split_ifs at hI with hact
    · exact (exists_computable_isAbsolutelyNormal_stepG_cover_len b k ((t + 1) ^ 6) (t + 1)
        hact.1 hact.2.1 (Nat.one_le_pow _ _ (by omega)) (by omega)).1 I hI
    · simp at hI
  · unfold exists_computable_isAbsolutelyNormal_layer
    simp only [exists_computable_isAbsolutelyNormal_HI_len_flatMap,
      exists_computable_isAbsolutelyNormal_HI_sum_range_map]
    set B := (t + 1) ^ 2 + 1 with hB
    have hc : (0 : ℝ) ≤ 1 / (16 * ((t : ℝ) + 1) ^ 2) := by positivity
    have hterm : ∀ b k : ℕ,
        exists_computable_isAbsolutelyNormal_len
            (if 2 ≤ b ∧ 1 ≤ k ∧ 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2 then
              exists_computable_isAbsolutelyNormal_cover b k ((t + 1) ^ 6) (t + 1) else [])
          ≤ 1 / (16 * ((t : ℝ) + 1) ^ 2) *
            ((if 2 ≤ b then (1 / 2 : ℝ) ^ b else 0) * (if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0)) := by
      intro b k
      by_cases hact : 2 ≤ b ∧ 1 ≤ k ∧ 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2
      · rw [ite_eq_left hact, ite_eq_left hact.1, ite_eq_left hact.2.1]
        exact exists_computable_isAbsolutelyNormal_HI_term_le t b k hact.1 hact.2.1 hact.2.2
      · rw [ite_eq_right hact]
        have hz : exists_computable_isAbsolutelyNormal_len ([] : List (ℚ × ℚ)) = 0 := by
          simp [exists_computable_isAbsolutelyNormal_len]
        rw [hz]
        refine mul_nonneg hc (mul_nonneg ?_ ?_) <;> split_ifs <;> positivity
    have hg2 : 0 ≤ ∑ b ∈ Finset.range B, (if 2 ≤ b then (1 / 2 : ℝ) ^ b else 0) :=
      Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity)
    have hg1 : 0 ≤ ∑ k ∈ Finset.range B, (if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0) :=
      Finset.sum_nonneg (fun k _ => by split_ifs <;> positivity)
    calc _ ≤ ∑ b ∈ Finset.range B, ∑ k ∈ Finset.range B,
          1 / (16 * ((t : ℝ) + 1) ^ 2) *
            ((if 2 ≤ b then (1 / 2 : ℝ) ^ b else 0) * (if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0)) :=
          Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun k _ => hterm b k))
      _ = 1 / (16 * ((t : ℝ) + 1) ^ 2) *
          ((∑ b ∈ Finset.range B, (if 2 ≤ b then (1 / 2 : ℝ) ^ b else 0)) *
            (∑ k ∈ Finset.range B, (if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0))) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ 1 / (16 * ((t : ℝ) + 1) ^ 2) * ((1 / 2) * 1) := by
          gcongr
          · exact exists_computable_isAbsolutelyNormal_HI_geom2 B
          · exact exists_computable_isAbsolutelyNormal_HI_geom1 B
      _ = 1 / (32 * ((t : ℝ) + 1) ^ 2) := by
          have hx : (0 : ℝ) < (t : ℝ) + 1 := by positivity
          field_simp
          ring

/-- Auxiliary for Step I1: `∑_{n ≤ K} 1/(n+1)² ≤ 2 - 1/(K+1)`. -/
private lemma exists_computable_isAbsolutelyNormal_HI_inv_sq_aux (K : ℕ) :
    ∑ n ∈ Finset.range (K + 1), 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have h1 : 1 / (((K + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((K : ℝ) + 1) - 1 / (((K + 1 : ℕ) : ℝ) + 1) :=
        by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
      nlinarith
    push_cast at h1 ⊢
    linarith

/-- Step I1 of the proof of `exists_computable_isAbsolutelyNormal`: total length of the
first `K` layers is `≤ 1/8`. -/
private lemma exists_computable_isAbsolutelyNormal_stepI1_total (K : ℕ) :
    ∑ n ∈ Finset.range K,
      exists_computable_isAbsolutelyNormal_len (exists_computable_isAbsolutelyNormal_layer n)
        ≤ 1 / 8 := by
  have h1 : ∀ n ∈ Finset.range K,
      exists_computable_isAbsolutelyNormal_len (exists_computable_isAbsolutelyNormal_layer n)
        ≤ (1 / 32 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n _
    refine (exists_computable_isAbsolutelyNormal_stepH_layer_len n).2.trans (le_of_eq ?_)
    have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hmono : ∑ n ∈ Finset.range K, 1 / ((n : ℝ) + 1) ^ 2
      ≤ ∑ n ∈ Finset.range (K + 1), 1 / ((n : ℝ) + 1) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ K))
      (fun n _ _ => by positivity)
  have haux := exists_computable_isAbsolutelyNormal_HI_inv_sq_aux K
  have hpos : (0 : ℝ) ≤ 1 / ((K : ℝ) + 1) := by positivity
  linarith

/-- Auxiliary for Step I2: telescoping bound `∑_{n ∈ [a, a+K)} 1/(n+1)² ≤ 1/a - 1/(a+K)`. -/
private lemma exists_computable_isAbsolutelyNormal_HI_tail_aux (a : ℕ) (ha : 1 ≤ a) (K : ℕ) :
    ∑ n ∈ Finset.Ico a (a + K), 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (a : ℝ) - 1 / ((a : ℝ) + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have h1 : 1 / (((a + K : ℕ) : ℝ) + 1) ^ 2
        ≤ 1 / ((a : ℝ) + K) - 1 / ((a : ℝ) + ((K + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
      nlinarith
    linarith

/-- Step I2 of the proof of `exists_computable_isAbsolutelyNormal`: the layers from
`2 ^ m` on have total length `≤ 2 ^ (-m)`. -/
private lemma exists_computable_isAbsolutelyNormal_stepI2_tail (m K : ℕ) :
    ∑ n ∈ Finset.Ico (2 ^ m) (2 ^ m + K),
      exists_computable_isAbsolutelyNormal_len (exists_computable_isAbsolutelyNormal_layer n)
        ≤ (1 / 2 : ℝ) ^ m := by
  have h1 : ∀ n ∈ Finset.Ico (2 ^ m) (2 ^ m + K),
      exists_computable_isAbsolutelyNormal_len (exists_computable_isAbsolutelyNormal_layer n)
        ≤ (1 / 32 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n _
    refine (exists_computable_isAbsolutelyNormal_stepH_layer_len n).2.trans (le_of_eq ?_)
    have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have ha : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have haux := exists_computable_isAbsolutelyNormal_HI_tail_aux (2 ^ m) ha K
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hpos : (0 : ℝ) ≤ 1 / (((2 ^ m : ℕ) : ℝ) + K) := by positivity
  have hcast : (((2 ^ m : ℕ)) : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
  rw [hcast] at haux hpos
  have hhalf : (1 / 2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by
    rw [one_div, one_div, inv_pow]
  rw [hhalf]
  have h3 : 1 / (2 : ℝ) ^ m - 1 / ((2 : ℝ) ^ m + K) ≤ 1 / (2 : ℝ) ^ m := by linarith
  have h4 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ m := by positivity
  calc (1 / 32 : ℝ) * ∑ n ∈ Finset.Ico (2 ^ m) (2 ^ m + K), 1 / ((n : ℝ) + 1) ^ 2
      ≤ (1 / 32 : ℝ) * (1 / (2 : ℝ) ^ m) := by
        refine mul_le_mul_of_nonneg_left (haux.trans h3) (by norm_num)
    _ ≤ 1 / (2 : ℝ) ^ m := by linarith
/-- Auxiliary for Step J: two-sided bound for `c N / N` on `[(t+1)^6, (t+2)^6)` for a monotone `c`.
-/
private lemma exists_computable_isAbsolutelyNormal_JK_bounds (c : ℕ → ℕ) (hc : Monotone c)
    (t N : ℕ) (h1 : (t + 1) ^ 6 ≤ N) (h2 : N < (t + 2) ^ 6) :
    (c ((t + 1) ^ 6) : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ) ≤ (c N : ℝ) / N ∧
    (c N : ℝ) / N ≤ (c ((t + 2) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (by positivity) h1
    exact_mod_cast this
  have hp1 : (0 : ℝ) < (((t + 1) ^ 6 : ℕ) : ℝ) := by positivity
  have hp2 : (0 : ℝ) < (((t + 2) ^ 6 : ℕ) : ℝ) := by positivity
  have hc1 : (c ((t + 1) ^ 6) : ℝ) ≤ c N := by exact_mod_cast hc h1
  have hc2 : (c N : ℝ) ≤ c ((t + 2) ^ 6) := by exact_mod_cast hc h2.le
  have hN1 : (((t + 1) ^ 6 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
  have hN2 : (N : ℝ) ≤ (((t + 2) ^ 6 : ℕ) : ℝ) := by exact_mod_cast h2.le
  have hc0 : (0 : ℝ) ≤ c N := Nat.cast_nonneg _
  have hc0' : (0 : ℝ) ≤ c ((t + 2) ^ 6) := Nat.cast_nonneg _
  constructor
  · calc (c ((t + 1) ^ 6) : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ)
        ≤ (c N : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right hc1 hp2.le
      _ ≤ (c N : ℝ) / N := by
          exact div_le_div_of_nonneg_left hc0 hNpos hN2
  · calc (c N : ℝ) / N ≤ (c ((t + 2) ^ 6) : ℝ) / N := by
          exact div_le_div_of_nonneg_right hc2 hNpos.le
      _ ≤ (c ((t + 2) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_left hc0' hp1 hN1

/-- Auxiliary for Step J: the lower envelope tends to `p`. -/
private lemma exists_computable_isAbsolutelyNormal_JK_tendsto_lo (p : ℝ) :
    Tendsto (fun t : ℕ =>
      (p - 1 / ((t : ℝ) + 1)) * (1 - 1 / (((t + 1 : ℕ) : ℝ) + 1)) ^ 6) atTop (𝓝 p) := by
  have ha : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ha1 : Tendsto (fun t : ℕ => 1 / (((t + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    ha.comp (tendsto_add_atTop_nat 1)
  have := (tendsto_const_nhds (x := p)).sub ha |>.mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub ha1 |>.pow 6)
  simpa using this

/-- Auxiliary for Step J: the upper envelope tends to `p`. -/
private lemma exists_computable_isAbsolutelyNormal_JK_tendsto_hi (p : ℝ) :
    Tendsto (fun t : ℕ =>
      (p + 1 / (((t + 1 : ℕ) : ℝ) + 1)) * (1 + 1 / ((t : ℝ) + 1)) ^ 6) atTop (𝓝 p) := by
  have ha : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ha1 : Tendsto (fun t : ℕ => 1 / (((t + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    ha.comp (tendsto_add_atTop_nat 1)
  have := (tendsto_const_nhds (x := p)).add ha1 |>.mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add ha |>.pow 6)
  simpa using this

/-- Auxiliary for Step J: on `[(t+1)^6, (t+2)^6)` the ratio `c N / N` lies between the two
envelopes, for `t ≥ t0`. -/
private lemma exists_computable_isAbsolutelyNormal_JK_two_sided (c : ℕ → ℕ) (hc : Monotone c)
    (p : ℝ) (t0 : ℕ)
    (ht0 : ∀ t ≥ t0,
      |(c ((t + 1) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) - p| < 1 / ((t : ℝ) + 1))
    (t : ℕ) (ht : t0 ≤ t) (N : ℕ) (h1 : (t + 1) ^ 6 ≤ N) (h2 : N < (t + 2) ^ 6) :
    (p - 1 / ((t : ℝ) + 1)) * (1 - 1 / (((t + 1 : ℕ) : ℝ) + 1)) ^ 6 ≤ (c N : ℝ) / N ∧
    (c N : ℝ) / N ≤ (p + 1 / (((t + 1 : ℕ) : ℝ) + 1)) * (1 + 1 / ((t : ℝ) + 1)) ^ 6 := by
  obtain ⟨hl, hu⟩ := exists_computable_isAbsolutelyNormal_JK_bounds c hc t N h1 h2
  have hA := abs_lt.1 (ht0 t ht)
  have hB := abs_lt.1 (ht0 (t + 1) (by omega))
  rw [show t + 1 + 1 = t + 2 from rfl] at hB
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have ht2 : (0 : ℝ) < (t : ℝ) + 2 := by positivity
  have hcast : (((t + 1 : ℕ) : ℝ) + 1) = (t : ℝ) + 2 := by push_cast; ring
  have hcast1 : (((t + 1) ^ 6 : ℕ) : ℝ) = ((t : ℝ) + 1) ^ 6 := by push_cast; ring
  have hcast2 : (((t + 2) ^ 6 : ℕ) : ℝ) = ((t : ℝ) + 2) ^ 6 := by push_cast; ring
  constructor
  · -- lower bound
    have hr : (c ((t + 1) ^ 6) : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ)
        = (c ((t + 1) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) *
          (1 - 1 / (((t + 1 : ℕ) : ℝ) + 1)) ^ 6 := by
      rw [hcast, hcast1, hcast2]
      field_simp
      ring
    have hr0 : (0 : ℝ) ≤ (1 - 1 / (((t + 1 : ℕ) : ℝ) + 1)) ^ 6 := by
      rw [hcast]
      have : (0 : ℝ) ≤ 1 - 1 / ((t : ℝ) + 2) := by
        rw [sub_nonneg, div_le_one ht2]
        linarith
      positivity
    calc (p - 1 / ((t : ℝ) + 1)) * (1 - 1 / (((t + 1 : ℕ) : ℝ) + 1)) ^ 6
        ≤ (c ((t + 1) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) *
          (1 - 1 / (((t + 1 : ℕ) : ℝ) + 1)) ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ hr0
          linarith [hA.1]
      _ = (c ((t + 1) ^ 6) : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ) := hr.symm
      _ ≤ (c N : ℝ) / N := hl
  · -- upper bound
    have hr : (c ((t + 2) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ)
        = (c ((t + 2) ^ 6) : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ) *
          (1 + 1 / ((t : ℝ) + 1)) ^ 6 := by
      rw [hcast1, hcast2]
      field_simp
      ring
    have hr0 : (0 : ℝ) ≤ (1 + 1 / ((t : ℝ) + 1)) ^ 6 := by positivity
    calc (c N : ℝ) / N ≤ (c ((t + 2) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) := hu
      _ = (c ((t + 2) ^ 6) : ℝ) / (((t + 2) ^ 6 : ℕ) : ℝ) *
          (1 + 1 / ((t : ℝ) + 1)) ^ 6 := hr
      _ ≤ (p + 1 / (((t + 1 : ℕ) : ℝ) + 1)) * (1 + 1 / ((t : ℝ) + 1)) ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ hr0
          have hh : ((t + 1 : ℕ) : ℝ) + 1 = (((t + 1 : ℕ) : ℝ) + 1) := rfl
          have : (1 : ℝ) / (((t + 1 : ℕ) : ℝ) + 1) = 1 / (((t + 1 : ℕ) : ℝ) + 1) := rfl
          linarith [hB.2]

/-- Step J of the proof of `exists_computable_isAbsolutelyNormal` (interpolation): a
nondecreasing counting function whose values at `(t+1)^6` are within `1/(t+1)` of the expected
proportion `p` for all large `t` has asymptotic proportion `p`. -/
private lemma exists_computable_isAbsolutelyNormal_stepJ_interp (c : ℕ → ℕ) (hc : Monotone c)
    (p : ℝ)
    (h : ∃ t0 : ℕ, ∀ t ≥ t0,
      |(c ((t + 1) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) - p| < 1 / ((t : ℝ) + 1)) :
    Tendsto (fun N : ℕ => (c N : ℝ) / N) atTop (𝓝 p) := by
  obtain ⟨t0, ht0⟩ := h
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlo := (exists_computable_isAbsolutelyNormal_JK_tendsto_lo p).eventually_const_lt
    (show p - ε < p by linarith)
  have hhi := (exists_computable_isAbsolutelyNormal_JK_tendsto_hi p).eventually_lt_const
    (show p < p + ε by linarith)
  obtain ⟨t1, ht1⟩ := eventually_atTop.1 (hlo.and (hhi.and (eventually_ge_atTop t0)))
  refine ⟨(t1 + 1) ^ 6, fun N hN => ?_⟩
  classical
  have hex : ∃ t : ℕ, N < (t + 2) ^ 6 :=
    ⟨N, calc N < N + 2 := by omega
      _ ≤ (N + 2) ^ 6 := Nat.le_self_pow (by norm_num) _⟩
  have hspec : N < (Nat.find hex + 2) ^ 6 := Nat.find_spec hex
  have hNpos : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (Nat.succ_pos t1)) hN
  have hlow : (Nat.find hex + 1) ^ 6 ≤ N := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      simpa using hNpos
    · have hm := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push Not at hm
      have e : Nat.find hex - 1 + 2 = Nat.find hex + 1 := by omega
      rwa [e] at hm
  have ht_ge : t1 ≤ Nat.find hex := by
    by_contra hlt
    push Not at hlt
    have : (Nat.find hex + 2) ^ 6 ≤ (t1 + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    omega
  obtain ⟨hlo', hhi', ht0'⟩ := ht1 (Nat.find hex) ht_ge
  obtain ⟨hl, hu⟩ := exists_computable_isAbsolutelyNormal_JK_two_sided c hc p t0 ht0
    (Nat.find hex) ht0' N hlow hspec
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Auxiliary for Step K: the cover of an active pair `(b, k)` is contained in layer `t`. -/
private lemma exists_computable_isAbsolutelyNormal_JK_mem_layer (b k t : ℕ) (hb : 2 ≤ b)
    (hk : 1 ≤ k) (hact : 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2) (I : ℚ × ℚ)
    (hI : I ∈ exists_computable_isAbsolutelyNormal_cover b k ((t + 1) ^ 6) (t + 1)) :
    I ∈ exists_computable_isAbsolutelyNormal_layer t := by
  have hpos : 0 < 64 * k * b ^ k * 2 ^ (b + k) := by
    have hk0 : 0 < k := hk
    have hb0 : 0 < b := by omega
    positivity
  have hbk : b ≤ (t + 1) ^ 2 := by
    refine le_trans ?_ hact
    refine Nat.le_of_dvd hpos ?_
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    exact dvd_pow_self b (by omega)
  have hkk : k ≤ (t + 1) ^ 2 := by
    refine le_trans ?_ hact
    refine Nat.le_of_dvd hpos ?_
    exact ⟨64 * b ^ k * 2 ^ (b + k), by ring⟩
  unfold exists_computable_isAbsolutelyNormal_layer
  rw [List.mem_flatMap]
  refine ⟨b, List.mem_range.2 (by omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨k, List.mem_range.2 (by omega), ?_⟩
  rw [ite_eq_left ⟨hb, hk, hact⟩]
  exact hI

/-- Step K of the proof of `exists_computable_isAbsolutelyNormal`: a real in `[0, 1/2]`
outside all the open intervals of all the layers is absolutely normal. -/
private lemma exists_computable_isAbsolutelyNormal_stepK_normal_of_avoid (α : ℝ) (h0 : 0 ≤ α)
    (h1 : α ≤ 1 / 2)
    (havoid : ∀ n, ∀ I ∈ exists_computable_isAbsolutelyNormal_layer n,
      ¬ ((I.1 : ℝ) < α ∧ α < (I.2 : ℝ))) :
    IsAbsolutelyNormal α := by
  classical
  intro b hb U hU
  by_cases hk0 : U.length = 0
  · have hU0 : U = [] := List.length_eq_zero_iff.mp hk0
    subst hU0
    have hfreq1 : ∀ N : ℕ, 1 ≤ N → digitOccurrenceFreq b α [] N = 1 := by
      intro N hN
      unfold digitOccurrenceFreq
      have hfilt : ((Finset.range N).filter fun k => DigitOccursAt b α [] k) = Finset.range N := by
        apply Finset.filter_true_of_mem
        intro k _ j hj
        exact absurd hj (by simp)
      rw [hfilt, Finset.card_range]
      have hN' : (N : ℝ) ≠ 0 := by
        have : 0 < N := hN
        positivity
      exact div_self hN'
    simp only [List.length_nil, pow_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hfreq1 N hN).symm
  · have hk : 1 ≤ U.length := Nat.pos_of_ne_zero hk0
    set k := U.length with hkdef
    have hp : (0 : ℝ) ≤ (b : ℝ)⁻¹ ^ k := by positivity
    let c : ℕ → ℕ := fun N => ((Finset.range N).filter fun j => DigitOccursAt b α U j).card
    have hc : Monotone c := by
      intro M N hMN
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hMN))
    have hfreq : ∀ N : ℕ, digitOccurrenceFreq b α U N = (c N : ℝ) / N := fun N => rfl
    have key : ∃ t0 : ℕ, ∀ t ≥ t0,
        |(c ((t + 1) ^ 6) : ℝ) / (((t + 1) ^ 6 : ℕ) : ℝ) - (b : ℝ)⁻¹ ^ k| < 1 / ((t : ℝ) + 1) := by
      refine ⟨64 * k * b ^ k * 2 ^ (b + k), fun t ht => ?_⟩
      by_contra hcon
      push Not at hcon
      have hact : 64 * k * b ^ k * 2 ^ (b + k) ≤ (t + 1) ^ 2 := by
        calc 64 * k * b ^ k * 2 ^ (b + k) ≤ t := ht
          _ ≤ t + 1 := Nat.le_succ t
          _ ≤ (t + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      have hcastR : (((t + 1 : ℕ)) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
      have hdev : (1 : ℝ) / ((t + 1 : ℕ) : ℝ) ≤
          |digitOccurrenceFreq b α U ((t + 1) ^ 6) - (b : ℝ)⁻¹ ^ k| := by
        rw [hfreq, hcastR]
        exact hcon
      obtain ⟨I, hI, hIα⟩ := exists_computable_isAbsolutelyNormal_stepE_cover_cover b
        ((t + 1) ^ 6) (t + 1) hb (Nat.one_le_pow _ _ (Nat.succ_pos t)) (Nat.succ_pos t) α h0
        (by linarith) U hk hU hdev
      exact havoid t I (exists_computable_isAbsolutelyNormal_JK_mem_layer b k t hb hk hact I hI) hIα
    exact exists_computable_isAbsolutelyNormal_stepJ_interp c hc _ key
/-- **SUV Problem 260, p. 266.**  There is a computable absolutely normal real. -/
theorem exists_computable_isAbsolutelyNormal :
    ∃ α : ℝ, IsAbsolutelyNormal α ∧ ComputableReals.IsComputableReal α := by
  have hT : Computable (fun m : ℕ => 2 ^ m) :=
    (exists_computable_isAbsolutelyNormal_primrec_pow.comp (Primrec.const 2) Primrec.id).to_comp
  obtain ⟨α, hcomp, h0, h1, havoid⟩ :=
    exists_computable_isAbsolutelyNormal_stepA_avoid
      (fun t => exists_computable_isAbsolutelyNormal_layer t)
      exists_computable_isAbsolutelyNormal_stepF_layer_computable
      (fun n => (exists_computable_isAbsolutelyNormal_stepH_layer_len n).1)
      (fun m => 2 ^ m) hT
      exists_computable_isAbsolutelyNormal_stepI1_total
      exists_computable_isAbsolutelyNormal_stepI2_tail
  exact ⟨α, exists_computable_isAbsolutelyNormal_stepK_normal_of_avoid α h0 h1 havoid, hcomp⟩

end Kolmogorov.FrequencyGames
