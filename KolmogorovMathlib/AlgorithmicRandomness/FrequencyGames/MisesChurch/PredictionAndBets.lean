/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch.Defs

/-!
# Prediction And Bets

Prediction strategies and bounded betting strategies against Mises-Church random sequences.

The main declarations are `correctPredictions`, the number of correct guesses of a predictor on a
prefix, and the theorems stating that a Mises-Church random sequence cannot be predicted with
frequency of success different from `1/2`, and that every computable bounded betting strategy has
gain `o(n)` on it.  This is the part of the book by Shen, Uspensky and Vereshchagin concerning
the prediction and betting characterizations of Mises-Church randomness.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped BigOperators

/-! ### Prediction and bounded bets -/

open Classical in
/-- The number of correct predictions among the first `n` bits for the predictor `P`, which sees
`ω_0 … ω_{i-1}` before guessing `ω_i`. -/
noncomputable def correctPredictions (P : BitString → Bool) (w : CantorSeq) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => P (cantorPrefix w i) = w i).card


/-- Step 1 of the proof of `tendsto_correctPredictions_of_isMisesChurchRandom`: the number
of correct predictions can be split into two sums depending on the prediction. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_split
    (P : BitString → Bool) (w : CantorSeq) (n : ℕ) :
    correctPredictions P w n =
    (selectChain {x | P x = false} w n).count false +
    (selectChain {x | P x = true} w n).count true := by
  induction n with
  | zero =>
    have e0 : ∀ R : Set BitString, selectChain R w 0 = [] := fun R => by
      simp [selectChain, cantorPrefix, selectedBits, selectedAux]
    rw [e0, e0]
    unfold correctPredictions
    rw [Finset.range_zero, Finset.filter_empty]
    simp
  | succ n ih =>
    have hc : correctPredictions P w (n + 1) =
        correctPredictions P w n + (if P (cantorPrefix w n) = w n then 1 else 0) := by
      unfold correctPredictions
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : P (cantorPrefix w n) = w n
      · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      · rw [ite_eq_right h, ite_eq_right h]; simp
    have h0 : selectChain {x | P x = false} w (n + 1) =
        selectChain {x | P x = false} w n ++
          (if P (cantorPrefix w n) = false then [w n] else []) := by
      unfold selectChain
      rw [cantorPrefix_succ, selectedBits_append_singleton]
      simp
    have h1 : selectChain {x | P x = true} w (n + 1) =
        selectChain {x | P x = true} w n ++
          (if P (cantorPrefix w n) = true then [w n] else []) := by
      unfold selectChain
      rw [cantorPrefix_succ, selectedBits_append_singleton]
      simp
    rw [hc, h0, h1, List.count_append, List.count_append, ← add_assoc, ih]
    cases hp : P (cantorPrefix w n) <;> cases hw : w n <;> simp
    omega

/-- Step 2 of the proof of `tendsto_correctPredictions_of_isMisesChurchRandom`: the length
of the original sequence is the sum of the lengths of the two subsequences. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_length
    (P : BitString → Bool) (w : CantorSeq) (n : ℕ) :
    n = (selectChain {x | P x = false} w n).length +
        (selectChain {x | P x = true} w n).length := by
  classical
  induction n with
  | zero => simp [selectChain, selectedBits, selectedAux, cantorPrefix]
  | succ n ih =>
    have hs : ∀ R : Set BitString, selectChain R w (n + 1) =
        selectChain R w n ++ (if cantorPrefix w n ∈ R then [w n] else []) := by
      intro R
      unfold selectChain
      rw [cantorPrefix_succ, selectedBits_append_singleton]
    rw [hs, hs]
    cases h : P (cantorPrefix w n) <;> simp [h] <;> omega

/-- Step 3 of the proof of `tendsto_correctPredictions_of_isMisesChurchRandom`: the sets
of strings where the prediction is false or true are decidable. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_decidable
    {P : BitString → Bool} (hP : Computable P) :
    IsDecidableSet {x | P x = false} ∧ IsDecidableSet {x | P x = true} := by
  refine ⟨⟨fun x => !P x, Primrec.not.to_comp.comp hP, fun x => ?_⟩, ⟨P, hP, fun x => ?_⟩⟩
  · simp
  · simp

/-- The numbers of ones and zeros in a string add up to its length. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_count_add
    (l : List Bool) : l.count true + l.count false = l.length := by
  induction l with
  | nil => simp
  | cons b l ih => cases b <;> simp <;> omega

/-- If `u` has limit frequency `1/2`, the counts in its prefixes are `k/2` up to `ε k + M`. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_count_bound
    {u : CantorSeq} (hu : HasLimitFreq (1 / 2) u) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ (k : ℕ) (a : Bool),
      |((cantorPrefix u k).count a : ℝ) - (k : ℝ) / 2| ≤ ε * k + M := by
  unfold HasLimitFreq at hu
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hu ε hε
  refine ⟨K + 1, fun k a => ?_⟩
  have hsum := tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_count_add
    (cantorPrefix u k)
  have hlen : (cantorPrefix u k).length = k := by simp
  rw [hlen] at hsum
  have hsumR : (((cantorPrefix u k).count true : ℕ) : ℝ) +
      (((cantorPrefix u k).count false : ℕ) : ℝ) = k := by exact_mod_cast hsum
  have hct0 : (0 : ℝ) ≤ (((cantorPrefix u k).count true : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcf0 : (0 : ℝ) ≤ (((cantorPrefix u k).count false : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  by_cases hk : K + 1 ≤ k
  · have hd := hK k (by omega)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hfreq : (freqOne u k : ℝ) = (((cantorPrefix u k).count true : ℕ) : ℝ) / k := by
      unfold freqOne; push_cast; rfl
    rw [Real.dist_eq, hfreq, abs_lt] at hd
    obtain ⟨h1, h2⟩ := hd
    have h3 : -(ε * k) < (((cantorPrefix u k).count true : ℕ) : ℝ) - k / 2 := by
      have : (((cantorPrefix u k).count true : ℕ) : ℝ) / k - 1 / 2 =
          ((((cantorPrefix u k).count true : ℕ) : ℝ) - k / 2) / k := by field_simp
      rw [this, lt_div_iff₀ hkpos] at h1
      linarith
    have h4 : (((cantorPrefix u k).count true : ℕ) : ℝ) - k / 2 < ε * k := by
      have : (((cantorPrefix u k).count true : ℕ) : ℝ) / k - 1 / 2 =
          ((((cantorPrefix u k).count true : ℕ) : ℝ) - k / 2) / k := by field_simp
      rw [this, div_lt_iff₀ hkpos] at h2
      linarith
    have hM : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    cases a <;> rw [abs_le] <;> constructor <;> linarith
  · have hk' : (k : ℝ) ≤ K := by exact_mod_cast (by omega : k ≤ K)
    have hεk : 0 ≤ ε * k := by positivity
    cases a <;> rw [abs_le] <;> constructor <;> linarith

/-- Prefixes of a chain are prefixes of the stream it determines (finite or infinite). -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_chain
    (c : ℕ → BitString) (hc : ∀ t, c t <+: c (t + 1)) (t : ℕ) :
    (∃ y, streamOfChain c hc = .finite y ∧ (c t).length ≤ y.length) ∨
    (∃ u, streamOfChain c hc = .infinite u ∧ c t = cantorPrefix u (c t).length) := by
  have key := BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet hc) (c t)
  have hmem : c t ∈ chainPrefixSet c := ⟨t, List.prefix_rfl⟩
  have key' : BitStream.finite (c t) ≤ streamOfChain c hc := key.mpr hmem
  rcases hs : streamOfChain c hc with y | u
  · left
    rw [hs] at key'
    exact ⟨y, rfl, (BitStream.finite_le_finite_iff.mp key').length_le⟩
  · right
    rw [hs] at key'
    exact ⟨u, rfl, ((isCantorPrefix_iff_cantorPrefix_eq _ u).mp
      (BitStream.finite_le_infinite_iff.mp key')).symm⟩

/-- Counts in the members of a chain whose stream is finite or balanced. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_chain_bound
    (c : ℕ → BitString) (hc : ∀ t, c t <+: c (t + 1))
    (hf : FiniteOrFreq (1 / 2) (streamOfChain c hc)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ (t : ℕ) (a : Bool),
      |((c t).count a : ℝ) - ((c t).length : ℝ) / 2| ≤ ε * (c t).length + M := by
  rcases hs : streamOfChain c hc with y | u
  · refine ⟨y.length, fun t a => ?_⟩
    rcases tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_chain c hc t with
      ⟨y', hy', hl⟩ | ⟨u, hu, _⟩
    · rw [hs] at hy'
      cases hy'
      have hca : (c t).count a ≤ (c t).length := List.count_le_length
      have hca' : ((c t).count a : ℝ) ≤ (c t).length := by exact_mod_cast hca
      have hl' : ((c t).length : ℝ) ≤ y.length := by exact_mod_cast hl
      have h0 : (0 : ℝ) ≤ ((c t).count a : ℝ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ ε * (c t).length := by positivity
      rw [abs_le]; constructor <;> linarith
    · rw [hs] at hu; cases hu
  · rw [hs] at hf
    obtain ⟨M, hM⟩ :=
      tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_count_bound hf hε
    refine ⟨M, fun t a => ?_⟩
    rcases tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_chain c hc t with
      ⟨y', hy', _⟩ | ⟨u', hu', hpre⟩
    · rw [hs] at hy'; cases hy'
    · rw [hs] at hu'
      cases hu'
      have := hM (c t).length a
      rw [← hpre] at this
      exact this

/-- Step 4 of the proof of `tendsto_correctPredictions_of_isMisesChurchRandom`: if the two
subsequences are balanced (or finite), the overall frequency of correct predictions tends to 1/2. -/
private lemma tendsto_correctPredictions_of_isMisesChurchRandom_limit
    (P : BitString → Bool) (w : CantorSeq)
    (h_split : ∀ n, correctPredictions P w n =
      (selectChain {x | P x = false} w n).count false +
      (selectChain {x | P x = true} w n).count true)
    (h_len : ∀ n, n = (selectChain {x | P x = false} w n).length +
      (selectChain {x | P x = true} w n).length)
    (h_freq0 : FiniteOrFreq (1 / 2) (selectStream {x | P x = false} w))
    (h_freq1 : FiniteOrFreq (1 / 2) (selectStream {x | P x = true} w)) :
    Tendsto (fun n => (correctPredictions P w n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hε : 0 < δ / 2 := by positivity
  obtain ⟨M0, hM0⟩ :=
    tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_chain_bound
      (selectChain {x | P x = false} w) (selectChain_prefix _ w) h_freq0 hε
  obtain ⟨M1, hM1⟩ :=
    tendsto_correctPredictions_of_isMisesChurchRandom_limit_aux_chain_bound
      (selectChain {x | P x = true} w) (selectChain_prefix _ w) h_freq1 hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((M0 + M1) / (δ / 2))
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
  have hlen : (n : ℝ) = ((selectChain {x | P x = false} w n).length : ℝ) +
      ((selectChain {x | P x = true} w n).length : ℝ) := by
    exact_mod_cast h_len n
  have hC : (correctPredictions P w n : ℝ) =
      ((selectChain {x | P x = false} w n).count false : ℝ) +
      ((selectChain {x | P x = true} w n).count true : ℝ) := by
    exact_mod_cast h_split n
  have b0 := hM0 n false
  have b1 := hM1 n true
  rw [abs_le] at b0 b1
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound : |(correctPredictions P w n : ℝ) - n / 2| < δ * n := by
    have hlt : M0 + M1 < δ / 2 * n := by
      have := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hN hnN)
      linarith
    rw [abs_lt]; constructor <;> nlinarith [b0.1, b0.2, b1.1, b1.2]
  have heq : (correctPredictions P w n : ℝ) / n - 1 / 2 =
      ((correctPredictions P w n : ℝ) - n / 2) / n := by field_simp
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  exact hbound

/-- **SUV Theorem 169, p. 266.**  For every total algorithm that predicts the next bit from the
previous ones, the fraction of correct predictions on a Mises-Church random sequence tends to
`1/2`. -/
theorem tendsto_correctPredictions_of_isMisesChurchRandom {P : BitString → Bool}
    (hP : Computable P) {w : CantorSeq} (hw : IsMisesChurchRandom w) :
    Tendsto (fun n => (correctPredictions P w n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have hdec := tendsto_correctPredictions_of_isMisesChurchRandom_decidable hP
  have hf0 := hw {x | P x = false} hdec.1
  have hf1 := hw {x | P x = true} hdec.2
  exact tendsto_correctPredictions_of_isMisesChurchRandom_limit P w
    (tendsto_correctPredictions_of_isMisesChurchRandom_split P w)
    (tendsto_correctPredictions_of_isMisesChurchRandom_length P w)
    hf0 hf1

/-- The total gain of the strategy `S`, in the convention of **SUV p. 266**: a positive value is a
bet on `0`, so the gain at step `i` is `S(ω_0 … ω_{i-1}) · (-1)^{ω_i}`.  Losses may go below
zero. -/
noncomputable def betGain (S : BitString → ℚ) (w : CantorSeq) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (S (cantorPrefix w i) : ℝ) * (if w i then -1 else 1)

/-- Step 1 of the proof of `betGain_isLittleO_of_isMisesChurchRandom`: the difference in
gain between two strategies is bounded by their pointwise difference. -/
private lemma betGain_isLittleO_of_isMisesChurchRandom_diff (S S' : BitString → ℚ) (ε : ℝ)
    (hdiff : ∀ x, |(S x : ℝ) - (S' x : ℝ)| ≤ ε) (w : CantorSeq) (n : ℕ) :
    |betGain S w n - betGain S' w n| ≤ ε * n := by
  unfold betGain
  rw [← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range n, ((S (cantorPrefix w i) : ℝ) * (if w i then -1 else 1)
        - (S' (cantorPrefix w i) : ℝ) * (if w i then -1 else 1))|
      ≤ ∑ i ∈ Finset.range n, |((S (cantorPrefix w i) : ℝ) * (if w i then -1 else 1)
        - (S' (cantorPrefix w i) : ℝ) * (if w i then -1 else 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε := by
        apply Finset.sum_le_sum
        intro i _
        have h := hdiff (cantorPrefix w i)
        have e : (S (cantorPrefix w i) : ℝ) * (if w i then -1 else 1)
            - (S' (cantorPrefix w i) : ℝ) * (if w i then -1 else 1)
            = ((S (cantorPrefix w i) : ℝ) - (S' (cantorPrefix w i) : ℝ)) * (if w i then -1 else 1)
                := by ring
        rw [e, abs_mul]
        split_ifs <;> simpa using h
    _ = ε * n := by simp [mul_comm]

/-- Counting step of `betGain_isLittleO_of_isMisesChurchRandom_approx`: for a rational `s`
in `[-1, 1]`, the average of the `k` threshold signs approximates `s` within `1 / k`. -/
private lemma betGain_isLittleO_of_isMisesChurchRandom_approx_count (k : ℕ) (hk : 0 < k)
    (s : ℚ) (hs : |s| ≤ 1) :
    |s - (∑ i : Fin k, if decide (s ≤ 1 - (2 * (i : ℚ) + 1) / k) = true then (-1 : ℚ) else 1) / k|
      ≤ 1 / k := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  set y : ℚ := ((1 - s) * k + 1) / 2 with hy
  have hy0 : 0 ≤ y := by
    have : 0 ≤ (1 - s) * k := mul_nonneg (by linarith) hkq.le
    rw [hy]; linarith
  set j : ℕ := ⌊y⌋₊ with hj
  have hjy : (j : ℚ) ≤ y := Nat.floor_le hy0
  have hyj : y < j + 1 := Nat.lt_floor_add_one y
  have hjk : j ≤ k := by
    have : (j : ℚ) < k + 1 := by
      have : (1 - s) * k ≤ 2 * k := by nlinarith
      rw [hy] at hjy; linarith
    have : j < k + 1 := by exact_mod_cast this
    omega
  have hiff : ∀ i : ℕ, (s ≤ 1 - (2 * (i : ℚ) + 1) / k) ↔ i < j := by
    intro i
    rw [hj, ← Nat.add_one_le_iff, Nat.le_floor_iff hy0]
    push_cast
    have e : s ≤ 1 - (2 * (i : ℚ) + 1) / k ↔ (2 * (i : ℚ) + 1) / k ≤ 1 - s := by
      constructor <;> intro h <;> linarith
    rw [e, div_le_iff₀ hkq, hy]
    constructor <;> intro h <;> linarith
  have hsum : (∑ i : Fin k, if decide (s ≤ 1 - (2 * (i : ℚ) + 1) / k) = true then (-1 : ℚ) else 1)
      = (k : ℚ) - 2 * j := by
    have h1 : (∑ i : Fin k, if decide (s ≤ 1 - (2 * (i : ℚ) + 1) / k) = true then (-1 : ℚ) else 1)
        = ∑ i ∈ Finset.range k, if i < j then (-1 : ℚ) else 1 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => if i < j then (-1 : ℚ) else 1) k]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [decide_eq_true_eq, hiff]
    rw [h1, ← Finset.sum_range_add_sum_Ico _ hjk]
    have h2 : ∑ i ∈ Finset.range j, (if i < j then (-1 : ℚ) else 1) = -(j : ℚ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℚ))
        (fun i hi => ite_eq_left (Finset.mem_range.mp hi))]
      simp
    have h3 : ∑ i ∈ Finset.Ico j k, (if i < j then (-1 : ℚ) else 1) = ((k : ℚ) - j) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ))
        (fun i hi => ite_eq_right (by have := (Finset.mem_Ico.mp hi).1; omega))]
      simp [Nat.cast_sub hjk]
    rw [h2, h3]; ring
  have hkey : s - ((k : ℚ) - 2 * j) / k = (2 * j - (1 - s) * k) / k := by
    field_simp; ring
  rw [hsum, hkey, abs_le]
  constructor
  · rw [show -(1 / (k : ℚ)) = (-1) / k by ring, div_le_div_iff_of_pos_right hkq]
    rw [hy] at hyj; linarith
  · rw [div_le_div_iff_of_pos_right hkq]
    rw [hy] at hjy; linarith

/-- Step 2 of the proof of `betGain_isLittleO_of_isMisesChurchRandom`: any computable
strategy `S` with values in `[-1, 1]` can be approximated by an average of computable Boolean
strategies. -/
private lemma betGain_isLittleO_of_isMisesChurchRandom_approx (S : BitString → ℚ)
    (hS : Computable S)
    (hbound : ∀ x, |S x| ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (_hk : 0 < k) (P : Fin k → BitString → Bool), (∀ i, Computable (P i)) ∧
      ∀ x, |(S x : ℝ) - ((fun x => (∑ i : Fin k, if P i x then (-1 : ℚ) else 1) / (k : ℚ)) x : ℝ)| ≤
          ε := by
  have hinv : 0 < 1 / ε := by positivity
  set k : ℕ := ⌈1 / ε⌉₊ with hkdef
  have hk : 0 < k := Nat.ceil_pos.mpr hinv
  have hkε : (1 : ℝ) / k ≤ ε := by
    have hk1 : 1 / ε ≤ k := Nat.le_ceil _
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    rw [div_le_iff₀ hkr]
    rw [div_le_iff₀ hε] at hk1
    linarith
  refine ⟨k, hk, fun i x => decide (S x ≤ 1 - (2 * (i : ℚ) + 1) / k), ?_, ?_⟩
  · intro i
    have hc : Computable (fun x => S x + (1 - (1 - (2 * (i : ℚ) + 1) / k))) :=
      computable₂_ratAdd.comp hS (Computable.const _)
    refine (computable_ratLeOne.comp hc).of_eq fun x => ?_
    simp only [decide_eq_decide]
    constructor <;> intro h <;> linarith
  · intro x
    have h := betGain_isLittleO_of_isMisesChurchRandom_approx_count k hk (S x) (hbound x)
    have h' : |(S x : ℝ) - ((∑ i : Fin k, if decide (S x ≤ 1 - (2 * (i : ℚ) + 1) / k) = true
        then (-1 : ℚ) else 1) / (k : ℚ) : ℚ)| ≤ ((1 / k : ℚ) : ℝ) := by
      rw [← Rat.cast_sub, ← Rat.cast_abs]
      exact_mod_cast h
    refine h'.trans ?_
    push_cast
    exact hkε

/-- Step 3 of the proof of `betGain_isLittleO_of_isMisesChurchRandom`: the gain is `o(n)`
for strategies that are an average of Boolean predictors. -/
private lemma betGain_isLittleO_of_isMisesChurchRandom_bool (k : ℕ) (_hk : 0 < k)
    (P : Fin k → BitString → Bool) (hP : ∀ i, Computable (P i))
    (w : CantorSeq) (hw : IsMisesChurchRandom w) :
    betGain (fun x => (∑ i : Fin k, if P i x then (-1:ℚ) else 1) / k) w =o[atTop]
        (fun n : ℕ => (n : ℝ)) := by
  classical
  have hone : ∀ (Q : BitString → Bool) (n : ℕ),
      ∑ j ∈ Finset.range n, ((if Q (cantorPrefix w j) then (-1:ℝ) else 1) * (if w j then -1 else 1))
        = 2 * (correctPredictions Q w n : ℝ) - n := by
    intro Q n
    have hc : (correctPredictions Q w n : ℝ)
        = ∑ j ∈ Finset.range n, (if Q (cantorPrefix w j) = w j then (1:ℝ) else 0) := by
      unfold correctPredictions
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hc, Finset.mul_sum]
    have : (n : ℝ) = ∑ j ∈ Finset.range n, (1:ℝ) := by simp
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases hq : Q (cantorPrefix w j) <;> cases hw' : w j <;> simp <;> norm_num
  have hsm : ∀ i : Fin k, (fun n : ℕ => 2 * (correctPredictions (P i) w n : ℝ) - n)
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    intro i
    have ht := tendsto_correctPredictions_of_isMisesChurchRandom (hP i) hw
    have ht2 : Tendsto (fun n : ℕ => (2 * (correctPredictions (P i) w n : ℝ) - n) / n) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 2 * ((correctPredictions (P i) w n : ℝ) / n) - 1) atTop
          (𝓝 (2 * (1 / 2) - 1)) := (ht.const_mul 2).sub_const 1
      have h2 : (2 * (1 / 2 : ℝ) - 1) = 0 := by norm_num
      rw [h2] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    exact (Asymptotics.isLittleO_iff_tendsto' (by
      filter_upwards [eventually_gt_atTop 0] with n hn h
      exact absurd h (by positivity))).mpr ht2
  have hsum := Asymptotics.IsLittleO.sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => hsm i)
  have hmul := hsum.const_mul_left (1 / (k : ℝ))
  refine hmul.congr_left ?_
  intro n
  rw [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => (hone (P i) n).symm)]
  unfold betGain
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  push_cast
  simp only [apply_ite ((↑) : ℚ → ℝ), Rat.cast_neg, Rat.cast_one]
  ring

/-- **SUV Theorem 170, p. 267.**  A total computable strategy with values in `[-1, 1]` has gain
`o(n)` after `n` steps on a Mises-Church random sequence. -/
theorem betGain_isLittleO_of_isMisesChurchRandom {S : BitString → ℚ} (hS : Computable S)
    (hbound : ∀ x, |S x| ≤ 1) {w : CantorSeq} (hw : IsMisesChurchRandom w) :
    (betGain S w) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨k, hk, P, hP_comp, hP_approx⟩ := betGain_isLittleO_of_isMisesChurchRandom_approx S
      hS hbound (ε / 2) (half_pos hε)
  have H := betGain_isLittleO_of_isMisesChurchRandom_bool k hk P hP_comp w hw
  have H_O := Asymptotics.isLittleO_iff.mp H (half_pos hε)
  filter_upwards [H_O] with n hn
  have H_diff := betGain_isLittleO_of_isMisesChurchRandom_diff S
      (fun x => (∑ i : Fin k, if P i x then (-1:ℚ) else 1) / k) (ε / 2) hP_approx w n
  calc
    |betGain S w n|
        = |betGain S w n -
            betGain (fun x => (∑ i : Fin k, if P i x then (-1:ℚ) else 1) / k) w n +
            betGain (fun x => (∑ i : Fin k, if P i x then (-1:ℚ) else 1) / k) w n| := by
      congr 1
      ring
    _ ≤ |betGain S w n - betGain (fun x => (∑ i : Fin k, if P i x then (-1:ℚ) else 1) / k) w n| +
        |betGain (fun x => (∑ i : Fin k, if P i x then (-1:ℚ) else 1) / k) w n| := abs_add_le _ _
    _ ≤ ε / 2 * n + ε / 2 * |(n : ℝ)| := by
      have hn' : |betGain (fun x => (∑ i : Fin k, if P i x = true then -1 else 1) / ↑k) w n| ≤ ε /
          2 * |(n : ℝ)| := hn
      linarith
    _ ≤ ε / 2 * |(n : ℝ)| + ε / 2 * |(n : ℝ)| := by
      gcongr
      exact le_abs_self (n : ℝ)
    _ = ε * |(n : ℝ)| := by ring

/-- Step 1 of the proof of `isMisesChurchRandom_of_selectStream`: 
The composed selection rule `selectStream R'` after `selectStream R` is just `selectStream` for
another decidable set. -/
private lemma isMisesChurchRandom_of_selectStream_compose_decidable
    {R : Set BitString} (hR : IsDecidableSet R) {R' : Set BitString} (hR' : IsDecidableSet R') :
    IsDecidableSet {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'} := by
  obtain ⟨f, hf, hfR⟩ := hR
  obtain ⟨g, hg, hgR⟩ := hR'
  have hsel := isEffectivelyNull_selectPreimage_computable_selectedBits ⟨f, hf, hfR⟩
  refine ⟨fun x => f x && g (selectedBits R x), ?_, fun x => ?_⟩
  · exact Primrec.and.to_comp.comp hf (hg.comp hsel)
  · simp [Bool.and_eq_true, hfR, hgR]

/-- String level of step 2: selecting by the composed set is selecting twice. -/
private lemma isMisesChurchRandom_of_selectStream_compose_eq_aux_string
    (R R' : Set BitString) (x : BitString) :
    selectedBits {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'} x =
      selectedBits R' (selectedBits R x) := by
  classical
  induction x using List.reverseRecOn with
  | nil => simp [selectedBits, selectedAux]
  | append_singleton x b ih =>
    rw [selectedBits_append_singleton, selectedBits_append_singleton, ih]
    by_cases hx : x ∈ R
    · by_cases hy : selectedBits R x ∈ R'
      · have : x ∈ {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'} := ⟨hx, hy⟩
        simp [this, hx, hy, selectedBits_append_singleton]
      · have : x ∉ {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'} := fun h => hy h.2
        simp [this, hx, hy, selectedBits_append_singleton]
    · have : x ∉ {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'} := fun h => hx h.1
      simp [this, hx]

/-- Equal chain prefix sets give equal streams. -/
private lemma isMisesChurchRandom_of_selectStream_compose_eq_aux_stream
    {c c' : ℕ → BitString} (hc : ∀ t, c t <+: c (t + 1)) (hc' : ∀ t, c' t <+: c' (t + 1))
    (h : chainPrefixSet c = chainPrefixSet c') : streamOfChain c hc = streamOfChain c' hc' := by
  unfold streamOfChain
  generalize isStreamPrefixSet_chainPrefixSet hc = h1
  generalize isStreamPrefixSet_chainPrefixSet hc' = h2
  generalize chainPrefixSet c = T at *
  generalize chainPrefixSet c' = T' at *
  subst h
  rfl

/-- Step 2 of the proof of `isMisesChurchRandom_of_selectStream`:
The composed selection matches selecting from the original sequence. -/
private lemma isMisesChurchRandom_of_selectStream_compose_eq
    {w : CantorSeq} {R : Set BitString} {u : CantorSeq}
    (hu : selectStream R w = .infinite u) {R' : Set BitString} :
    selectStream R' u = selectStream {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'} w := by
  have key : ∀ x, BitStream.finite x ≤ selectStream R w ↔ x ∈ chainPrefixSet (selectChain R w) :=
    fun x => BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x
  have hT : ∀ x, x ∈ chainPrefixSet (selectChain R w) ↔ IsCantorPrefix x u := by
    intro x
    rw [← key, hu]
    exact Iff.rfl
  unfold selectStream
  apply isMisesChurchRandom_of_selectStream_compose_eq_aux_stream
  ext y
  simp only [chainPrefixSet, selectChain, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hs⟩
    have hmem : cantorPrefix u s ∈ chainPrefixSet (selectChain R w) :=
      (hT _).2 ((isCantorPrefix_iff_cantorPrefix_eq _ _).2 (by simp))
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, hs.trans ?_⟩
    rw [isMisesChurchRandom_of_selectStream_compose_eq_aux_string]
    exact selectedBits_prefix R' ht
  · rintro ⟨t, ht⟩
    rw [isMisesChurchRandom_of_selectStream_compose_eq_aux_string] at ht
    have hmem : selectedBits R (cantorPrefix w t) ∈ chainPrefixSet (selectChain R w) :=
      ⟨t, List.prefix_rfl⟩
    have h2 := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 ((hT _).1 hmem)
    refine ⟨(selectedBits R (cantorPrefix w t)).length, ?_⟩
    rw [h2]
    exact ht

/-- **SUV Theorem 171, p. 267.**  Applying a Church-admissible rule to a Mises-Church random
sequence gives a finite or a Mises-Church random sequence. -/
theorem isMisesChurchRandom_of_selectStream {w : CantorSeq} (hw : IsMisesChurchRandom w)
    {R : Set BitString} (hR : IsDecidableSet R) {u : CantorSeq}
    (hu : selectStream R w = .infinite u) : IsMisesChurchRandom u := by
  intro R' hR'
  have H := hw {x : BitString | x ∈ R ∧ selectedBits R x ∈ R'}
      (isMisesChurchRandom_of_selectStream_compose_decidable hR hR')
  rw [← isMisesChurchRandom_of_selectStream_compose_eq hu] at H
  exact H

end Kolmogorov.FrequencyGames
