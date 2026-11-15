/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Data.Bool.Count
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.LowerSemicomputable
import KolmogorovMathlib.Interface.ComputableReals.Part01
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.VilleExample

/-!
# Zeros Dominate Win

A computable uniform martingale that wins on every sequence in which each prefix contains at
least as many zeros as ones.  The martingale is a rational-valued mixture of a capital-walk
strategy and of countably many strategies that bet on the balance of zeros over ones returning
to a given level after a given time.  The main result is `exists_computable_wins_zerosDominate`
(SUV Problem 267), which uses the martingale of the proof of Theorem 182(d) of the book by
Shen, Uspensky and Vereshchagin.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology ComputableReals

private def exists_computable_wins_zerosDominate_M0 (x : BitString) : ℚ :=
  x.foldl (fun cap b => if cap > 0 then if b == false then cap + 1 else cap - 1 else 0) (1 : ℚ)

private def exists_computable_wins_zerosDominate_Mtl (t l : ℕ) (x : BitString) : ℚ :=
  let bets := (List.range x.length).filter (fun i =>
    decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l))
  let wrong := bets.any (fun i => (x.drop i).head? == some true)
  if wrong then 0 else 2 ^ bets.length

private def exists_computable_wins_zerosDominate_M (x : BitString) : ℚ :=
  (exists_computable_wins_zerosDominate_M0 x) / 2 +
  (List.range (x.length + 1)).foldl (fun acc t =>
    acc + (List.range (x.length + 1)).foldl (fun acc2 l =>
      acc2 + (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x
    ) (0 : ℚ)
  ) (0 : ℚ) +
  (1 / 2 - (1 / 8 : ℚ) * (2 - (1 / 2 : ℚ) ^ x.length) ^ 2)

private lemma exists_computable_wins_zerosDominate_fair_M0_nat (x : BitString) :
    ∃ n : ℕ, exists_computable_wins_zerosDominate_M0 x = n := by
  induction x using List.reverseRecOn with
  | nil => exact ⟨1, by simp [exists_computable_wins_zerosDominate_M0]⟩
  | append_singleton x b ih =>
    obtain ⟨n, hn⟩ := ih
    unfold exists_computable_wins_zerosDominate_M0 at hn ⊢
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, hn]
    by_cases h0 : (0 : ℚ) < n
    · cases b
      · exact ⟨n + 1, by simp [h0]⟩
      · refine ⟨n - 1, ?_⟩
        have : 1 ≤ n := by exact_mod_cast h0
        simp [h0, Nat.cast_sub this]
    · exact ⟨0, by simp [h0]⟩

private lemma exists_computable_wins_zerosDominate_fair_M0_snoc (x : BitString) (b : Bool) :
    exists_computable_wins_zerosDominate_M0 (x ++ [b]) =
      if exists_computable_wins_zerosDominate_M0 x > 0 then
        (if b == false then exists_computable_wins_zerosDominate_M0 x + 1
          else exists_computable_wins_zerosDominate_M0 x - 1) else 0 := by
  unfold exists_computable_wins_zerosDominate_M0
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

private lemma exists_computable_wins_zerosDominate_fair_M0_pair (x : BitString) :
    exists_computable_wins_zerosDominate_M0 (x ++ [false]) +
      exists_computable_wins_zerosDominate_M0 (x ++ [true]) =
      2 * exists_computable_wins_zerosDominate_M0 x := by
  rw [exists_computable_wins_zerosDominate_fair_M0_snoc,
    exists_computable_wins_zerosDominate_fair_M0_snoc]
  by_cases h : exists_computable_wins_zerosDominate_M0 x > 0
  · simp only [h, ite_true]; simp; ring
  · simp only [h, ite_false]
    have := h; push Not at this
    obtain ⟨n, hn⟩ := exists_computable_wins_zerosDominate_fair_M0_nat x
    rw [hn] at this ⊢
    have : (n : ℚ) = 0 := le_antisymm this (Nat.cast_nonneg _)
    simp [this]

private lemma exists_computable_wins_zerosDominate_fair_M0_nonneg (x : BitString) :
    0 ≤ exists_computable_wins_zerosDominate_M0 x := by
  obtain ⟨n, hn⟩ := exists_computable_wins_zerosDominate_fair_M0_nat x
  rw [hn]; exact Nat.cast_nonneg _

private lemma exists_computable_wins_zerosDominate_fair_Mtl_nonneg (t l : ℕ) (x : BitString) :
    0 ≤ exists_computable_wins_zerosDominate_Mtl t l x := by
  unfold exists_computable_wins_zerosDominate_Mtl
  simp only []
  split_ifs <;> positivity

private lemma exists_computable_wins_zerosDominate_fair_Mtl_snoc (t l : ℕ) (x : BitString)
    (b : Bool) :
    exists_computable_wins_zerosDominate_Mtl t l (x ++ [b]) =
      if t ≤ x.length ∧ x.count false - x.count true = l then
        (if b then 0 else 2 * exists_computable_wins_zerosDominate_Mtl t l x)
      else exists_computable_wins_zerosDominate_Mtl t l x := by
  have hb : (List.range (x ++ [b]).length).filter (fun i =>
      decide (t ≤ i) && (((x ++ [b]).take i).count false - ((x ++ [b]).take i).count true == l)) =
      (List.range x.length).filter (fun i =>
        decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l)) ++
      (if t ≤ x.length ∧ x.count false - x.count true = l then [x.length] else []) := by
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
    have h1 : (List.range x.length).filter (fun i =>
        decide (t ≤ i) && (((x ++ [b]).take i).count false - ((x ++ [b]).take i).count true == l)) =
        (List.range x.length).filter (fun i =>
        decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l)) := by
      apply List.filter_congr
      intro i hi
      have hi' : i < x.length := List.mem_range.1 hi
      rw [List.take_append_of_le_length hi'.le]
    rw [h1]
    congr 1
    by_cases hc : t ≤ x.length ∧ x.count false - x.count true = l
    · simp [hc]
    · simp [hc]
  unfold exists_computable_wins_zerosDominate_Mtl
  simp only []
  rw [hb]
  rw [List.any_append]
  have hany : ((List.range x.length).filter (fun i =>
        decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l))).any
        (fun i => ((x ++ [b]).drop i).head? == some true) =
      ((List.range x.length).filter (fun i =>
        decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l))).any
        (fun i => (x.drop i).head? == some true) := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true]
    have key : ∀ i ∈ (List.range x.length).filter (fun i =>
        decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l)),
        ((x ++ [b]).drop i).head? = (x.drop i).head? := by
      intro i hi
      have hi' : i < x.length := List.mem_range.1 (List.mem_filter.1 hi).1
      rw [List.drop_append_of_le_length hi'.le]
      cases h : x.drop i with
      | nil => simp [List.drop_eq_nil_iff] at h; omega
      | cons a r => simp
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by rwa [key i hi] at h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by rwa [← key i hi] at h⟩
  rw [hany]
  generalize ((List.range x.length).filter (fun i =>
        decide (t ≤ i) && ((x.take i).count false - (x.take i).count true == l))).any
        (fun i => (x.drop i).head? == some true) = w
  by_cases hc : t ≤ x.length ∧ x.count false - x.count true = l
  · simp only [hc, and_self, ite_true, List.any_cons, List.any_nil, List.length_append,
      List.length_singleton]
    cases b <;> cases w <;> simp [pow_succ]
    ring
  · simp only [hc, ite_false, List.any_nil, List.length_append, List.length_nil]
    cases b <;> cases w <;> simp

private lemma exists_computable_wins_zerosDominate_fair_Mtl_pair (t l : ℕ) (x : BitString) :
    exists_computable_wins_zerosDominate_Mtl t l (x ++ [false]) +
      exists_computable_wins_zerosDominate_Mtl t l (x ++ [true]) =
      2 * exists_computable_wins_zerosDominate_Mtl t l x := by
  rw [exists_computable_wins_zerosDominate_fair_Mtl_snoc,
    exists_computable_wins_zerosDominate_fair_Mtl_snoc]
  by_cases hc : t ≤ x.length ∧ x.count false - x.count true = l
  · simp [hc]
  · simp [hc, two_mul]

private lemma exists_computable_wins_zerosDominate_fair_Mtl_one (t l : ℕ) (y : BitString)
    (h : y.length ≤ t ∨ y.length ≤ l) :
    exists_computable_wins_zerosDominate_Mtl t l y = 1 := by
  unfold exists_computable_wins_zerosDominate_Mtl
  simp only []
  have hnil : (List.range y.length).filter (fun i =>
      decide (t ≤ i) && ((y.take i).count false - (y.take i).count true == l)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi
    have hi' : i < y.length := List.mem_range.1 hi
    have hc : (y.take i).count false ≤ i := by
      calc (y.take i).count false ≤ (y.take i).length := List.count_le_length
        _ ≤ i := by simp
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]
    intro h1
    omega
  rw [hnil]
  simp

private lemma exists_computable_wins_zerosDominate_fair_fold (F : ℕ → ℚ) (a : ℚ) (k : ℕ) :
    (List.range k).foldl (fun acc i => acc + F i) a = a + ∑ i ∈ Finset.range k, F i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

private lemma exists_computable_wins_zerosDominate_fair_geom (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / 2 : ℚ) ^ i = 2 - (1 / 2) ^ n := by
  induction n with
  | zero => simp; norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private lemma exists_computable_wins_zerosDominate_fair_E (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), (1 / 2 : ℚ) ^ (t + l + 3) =
      (1 / 8 : ℚ) * (2 - (1 / 2 : ℚ) ^ n) ^ 2 := by
  have h : ∀ t l : ℕ, (1 / 2 : ℚ) ^ (t + l + 3) = (1 / 8) * ((1 / 2) ^ t * (1 / 2) ^ l) := by
    intro t l
    rw [pow_add, pow_add, show (3 : ℕ) = 3 from rfl]
    norm_num
    ring
  simp only [h]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [exists_computable_wins_zerosDominate_fair_geom]
  ring

private lemma exists_computable_wins_zerosDominate_fair_box (F : ℕ → ℕ → ℚ) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1 + 1), ∑ l ∈ Finset.range (n + 1 + 1), F t l =
      ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), F t l +
        (∑ t ∈ Finset.range (n + 1), F t (n + 1) + ∑ l ∈ Finset.range (n + 1), F (n + 1) l +
          F (n + 1) (n + 1)) := by
  simp only [Finset.sum_range_succ (n := n + 1), Finset.sum_add_distrib]
  ring

private lemma exists_computable_wins_zerosDominate_fair_M_eq (x : BitString) :
    exists_computable_wins_zerosDominate_M x =
      exists_computable_wins_zerosDominate_M0 x / 2 +
      ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x +
      (1 / 2 - ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3)) := by
  rw [exists_computable_wins_zerosDominate_fair_E]
  unfold exists_computable_wins_zerosDominate_M
  simp only [exists_computable_wins_zerosDominate_fair_fold, zero_add]

private lemma exists_computable_wins_zerosDominate_fair_T_pair (n : ℕ) (x : BitString) :
    ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l (x ++ [false]) +
      ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l (x ++ [true]) =
      2 * ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := exists_computable_wins_zerosDominate_fair_Mtl_pair t l x
  linear_combination (1 / 2 : ℚ) ^ (t + l + 3) * this

private lemma exists_computable_wins_zerosDominate_fair_T_step (n : ℕ) (y : BitString)
    (hy : y.length ≤ n + 1) :
    ∑ t ∈ Finset.range (n + 1 + 1), ∑ l ∈ Finset.range (n + 1 + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l y =
      ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l y +
      (∑ t ∈ Finset.range (n + 1 + 1), ∑ l ∈ Finset.range (n + 1 + 1), (1 / 2 : ℚ) ^ (t + l + 3) -
        ∑ t ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), (1 / 2 : ℚ) ^ (t + l + 3)) := by
  rw [exists_computable_wins_zerosDominate_fair_box
      (fun t l => (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l y),
    exists_computable_wins_zerosDominate_fair_box (fun t l => (1 / 2 : ℚ) ^ (t + l + 3))]
  have h1 : ∀ t, exists_computable_wins_zerosDominate_Mtl t (n + 1) y = 1 := fun t =>
    exists_computable_wins_zerosDominate_fair_Mtl_one t (n + 1) y (Or.inr hy)
  have h2 : ∀ l, exists_computable_wins_zerosDominate_Mtl (n + 1) l y = 1 := fun l =>
    exists_computable_wins_zerosDominate_fair_Mtl_one (n + 1) l y (Or.inl hy)
  simp only [h1, h2, mul_one]
  ring

private lemma exists_computable_wins_zerosDominate_fair_M_snoc (x : BitString) (b : Bool) :
    exists_computable_wins_zerosDominate_M (x ++ [b]) =
      exists_computable_wins_zerosDominate_M0 (x ++ [b]) / 2 +
      ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l (x ++ [b]) +
      (1 / 2 - ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3)) := by
  rw [exists_computable_wins_zerosDominate_fair_M_eq]
  simp only [List.length_append, List.length_singleton]
  rw [exists_computable_wins_zerosDominate_fair_T_step x.length (x ++ [b])
    (by simp)]
  ring

private lemma exists_computable_wins_zerosDominate_fair_M_nonneg (x : BitString) :
    0 ≤ exists_computable_wins_zerosDominate_M x := by
  rw [exists_computable_wins_zerosDominate_fair_M_eq,
    exists_computable_wins_zerosDominate_fair_E]
  have h0 := exists_computable_wins_zerosDominate_fair_M0_nonneg x
  have hT : 0 ≤ ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x := by
    refine Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ => ?_
    have := exists_computable_wins_zerosDominate_fair_Mtl_nonneg t l x
    positivity
  have hq0 : (0 : ℚ) < (1 / 2) ^ x.length := by positivity
  have hq1 : (1 / 2 : ℚ) ^ x.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

private lemma exists_computable_wins_zerosDominate_fair_M_pair (x : BitString) :
    exists_computable_wins_zerosDominate_M x =
      (exists_computable_wins_zerosDominate_M (x ++ [false]) +
        exists_computable_wins_zerosDominate_M (x ++ [true])) / 2 := by
  rw [exists_computable_wins_zerosDominate_fair_M_snoc,
    exists_computable_wins_zerosDominate_fair_M_snoc,
    exists_computable_wins_zerosDominate_fair_M_eq x]
  have h1 := exists_computable_wins_zerosDominate_fair_M0_pair x
  have h2 := exists_computable_wins_zerosDominate_fair_T_pair x.length x
  linarith

/-- Step 1 -/
private lemma exists_computable_wins_zerosDominate_fair :
    IsFairCapital uniformMeasure (fun x => (exists_computable_wins_zerosDominate_M x : ℝ)) := by
  rw [isFairCapital_uniform_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact_mod_cast exists_computable_wins_zerosDominate_fair_M_nonneg x
  · exact_mod_cast exists_computable_wins_zerosDominate_fair_M_pair x

private def exists_computable_wins_zerosDominate_comp_natStep (cap : ℕ) (b : Bool) : ℕ :=
  if cap > 0 then (bif (b == false) then cap + 1 else cap - 1) else 0

private lemma exists_computable_wins_zerosDominate_comp_M0_aux (x : BitString) :
    ∀ c : ℕ,
    x.foldl (fun cap b => if cap > 0 then if b == false then cap + 1 else cap - 1 else 0)
      (c : ℚ) =
      ((x.foldl exists_computable_wins_zerosDominate_comp_natStep c : ℕ) : ℚ) := by
  induction x with
  | nil => intro c; rfl
  | cons b t ih =>
    intro c
    simp only [List.foldl_cons]
    have : (if (c : ℚ) > 0 then if b == false then (c : ℚ) + 1 else (c : ℚ) - 1 else 0)
        = ((exists_computable_wins_zerosDominate_comp_natStep c b : ℕ) : ℚ) := by
      unfold exists_computable_wins_zerosDominate_comp_natStep
      by_cases hc : c > 0
      · have hc' : (c : ℚ) > 0 := by exact_mod_cast hc
        simp only [hc, hc', ite_true]
        cases b <;> simp [Nat.cast_sub (Nat.succ_le_of_lt hc)]
      · have hc' : ¬ (c : ℚ) > 0 := by exact_mod_cast hc
        simp [hc, hc']
    rw [this]
    exact ih _

private lemma exists_computable_wins_zerosDominate_comp_primrec_natFold :
    Primrec (fun x : BitString =>
      x.foldl exists_computable_wins_zerosDominate_comp_natStep 1) := by
  refine Primrec.list_foldl (f := fun x : BitString => x) (g := fun _ => (1:ℕ))
    (h := fun (_ : BitString) (p : ℕ × Bool) =>
      exists_computable_wins_zerosDominate_comp_natStep p.1 p.2)
    Primrec.id (Primrec.const 1) ?_
  unfold exists_computable_wins_zerosDominate_comp_natStep
  have key : Primrec (fun a : BitString × (ℕ × Bool) =>
      if a.2.1 > 0 then (bif (a.2.2 == false) then a.2.1 + 1 else a.2.1 - 1) else 0) := by
    refine Primrec.ite (c := fun a : BitString × (ℕ × Bool) => a.2.1 > 0) ?_ ?_ (Primrec.const 0)
    · exact Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)
    · refine Primrec.cond ?_ ?_ ?_
      · exact (Primrec.beq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const false))
      · exact Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
      · exact Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  exact key.to₂

private lemma exists_computable_wins_zerosDominate_comp_computable_M0 :
    Computable exists_computable_wins_zerosDominate_M0 := by
  have h := computable_nat_to_rat.comp
    exists_computable_wins_zerosDominate_comp_primrec_natFold.to_comp
  refine h.of_eq (fun x => ?_)
  have := exists_computable_wins_zerosDominate_comp_M0_aux x 1
  simpa [exists_computable_wins_zerosDominate_M0] using this.symm

private def exists_computable_wins_zerosDominate_comp_bets (a : ℕ × ℕ × BitString) :
    List ℕ :=
  (List.range a.2.2.length).filter (fun i =>
    decide (a.1 ≤ i) && ((a.2.2.take i).count false - (a.2.2.take i).count true == a.2.1))

private lemma exists_computable_wins_zerosDominate_comp_primrec_bets :
    Primrec exists_computable_wins_zerosDominate_comp_bets := by
  have hx : Primrec (fun a : ℕ × ℕ × BitString => a.2.2) := Primrec.snd.comp Primrec.snd
  have hf : Primrec (fun p : (ℕ × ℕ × BitString) × ℕ => p.1.2.2.take p.2) :=
    Primrec.list_take.comp
      (Primrec.snd : Primrec fun p : (ℕ × ℕ × BitString) × ℕ => p.2) (hx.comp Primrec.fst)
  have hcount : ∀ b : Bool,
      Primrec (fun p : (ℕ × ℕ × BitString) × ℕ => (p.1.2.2.take p.2).count b) :=
    fun b => (list_countP_primrec (f := fun p : (ℕ × ℕ × BitString) × ℕ => p.1.2.2.take p.2)
      (p := fun _ c => c == b) hf
      (Primrec.beq.comp Primrec.snd (Primrec.const b))).of_eq (fun p => by simp [List.count])
  have hp : Primrec₂ (fun (a : ℕ × ℕ × BitString) (i : ℕ) =>
      decide (a.1 ≤ i) && ((a.2.2.take i).count false - (a.2.2.take i).count true == a.2.1)) := by
    refine Primrec.and.comp ?_ ?_
    · exact (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd : Primrec fun p : (ℕ × ℕ × BitString) × ℕ => p.2)).decide
    · exact Primrec.beq.comp (Primrec.nat_sub.comp (hcount false) (hcount true))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.list_filter (Primrec.list_range.comp (Primrec.list_length.comp hx)) hp

private lemma exists_computable_wins_zerosDominate_comp_computable_Mtl :
    Computable (fun a : ℕ × ℕ × BitString =>
      exists_computable_wins_zerosDominate_Mtl a.1 a.2.1 a.2.2) := by
  have hx : Primrec (fun a : ℕ × ℕ × BitString => a.2.2) := Primrec.snd.comp Primrec.snd
  have hwrong : Primrec (fun a : ℕ × ℕ × BitString =>
      (exists_computable_wins_zerosDominate_comp_bets a).any
        (fun i => (a.2.2.drop i).head? == some true)) := by
    refine list_any_primrec (f := exists_computable_wins_zerosDominate_comp_bets)
      (p := fun a i => (a.2.2.drop i).head? == some true)
      exists_computable_wins_zerosDominate_comp_primrec_bets ?_
    have hi : Primrec (fun q : (ℕ × ℕ × BitString) × ℕ => q.2) := Primrec.snd
    have hd : Primrec (fun q : (ℕ × ℕ × BitString) × ℕ => (q.1.2.2.drop q.2).head?) :=
      Primrec.list_head?.comp (Primrec.list_drop.comp hi (hx.comp Primrec.fst))
    exact (Primrec.beq.comp hd (Primrec.const (some true))).of_eq (fun q => by simp)
  have hpow : Computable (fun a : ℕ × ℕ × BitString =>
      ((2 ^ (exists_computable_wins_zerosDominate_comp_bets a).length : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp ((nat_pow_primrec₂.comp (Primrec.const 2)
      (Primrec.list_length.comp
        exists_computable_wins_zerosDominate_comp_primrec_bets)).to_comp)
  refine (Computable.cond hwrong.to_comp (Computable.const 0) hpow).of_eq (fun a => ?_)
  have e : exists_computable_wins_zerosDominate_Mtl a.1 a.2.1 a.2.2 =
      if (exists_computable_wins_zerosDominate_comp_bets a).any
        (fun i => (a.2.2.drop i).head? == some true) = true then 0
      else 2 ^ (exists_computable_wins_zerosDominate_comp_bets a).length := rfl
  rw [e]
  generalize (exists_computable_wins_zerosDominate_comp_bets a).any
    (fun i => (a.2.2.drop i).head? == some true) = w
  cases w <;> simp

private lemma exists_computable_wins_zerosDominate_comp_computable_halfpow :
    Computable (fun k : ℕ => (1 / 2 : ℚ) ^ k) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun k : ℕ => 2 ^ k)
    (Computable.const 1) comp_pow (fun k => by positivity) (fun k => ?_)
  simp

private lemma exists_computable_wins_zerosDominate_comp_computable_doubleFold
    (F : ℕ → ℕ → BitString → ℚ)
    (hF : Computable (fun a : ℕ × ℕ × BitString => F a.1 a.2.1 a.2.2)) :
    Computable (fun x : BitString =>
      (List.range (x.length + 1)).foldl (fun acc t =>
        acc + (List.range (x.length + 1)).foldl (fun acc2 l =>
          acc2 + (1 / 2 : ℚ) ^ (t + l + 3) * F t l x) (0 : ℚ)) (0 : ℚ)) := by
  have hlen : Computable (fun x : BitString => (List.range (x.length + 1))) :=
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length)).to_comp
  have inner : Computable (fun p : BitString × ℕ =>
      (List.range (p.1.length + 1)).foldl (fun acc2 l =>
        acc2 + (1 / 2 : ℚ) ^ (p.2 + l + 3) * F p.2 l p.1) (0 : ℚ)) := by
    have hl : Computable (fun p : BitString × ℕ => List.range (p.1.length + 1)) :=
      hlen.comp Computable.fst
    have hg : Computable (fun _ : BitString × ℕ => (0 : ℚ)) := Computable.const 0
    have hh : Computable₂ (fun (p : BitString × ℕ) (q : ℚ × ℕ) =>
        q.1 + (1 / 2 : ℚ) ^ (p.2 + q.2 + 3) * F p.2 q.2 p.1) := by
      have h1 : Computable (fun r : (BitString × ℕ) × (ℚ × ℕ) =>
          (1 / 2 : ℚ) ^ (r.1.2 + r.2.2 + 3)) :=
        Computable.comp (f := fun k : ℕ => (1 / 2 : ℚ) ^ k)
          (g := fun r : (BitString × ℕ) × (ℚ × ℕ) => r.1.2 + r.2.2 + 3)
          exists_computable_wins_zerosDominate_comp_computable_halfpow
          (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
            (Primrec.snd.comp Primrec.snd)) (Primrec.const 3)).to_comp
      have h2 : Computable (fun r : (BitString × ℕ) × (ℚ × ℕ) => F r.1.2 r.2.2 r.1.1) :=
        Computable.comp (f := fun a : ℕ × ℕ × BitString => F a.1 a.2.1 a.2.2)
          (g := fun r : (BitString × ℕ) × (ℚ × ℕ) => (r.1.2, r.2.2, r.1.1)) hF
          (Computable.pair (Computable.snd.comp Computable.fst)
            (Computable.pair (Computable.snd.comp Computable.snd)
              (Computable.fst.comp Computable.fst)))
      have h3 : Computable (fun r : (BitString × ℕ) × (ℚ × ℕ) =>
          (1 / 2 : ℚ) ^ (r.1.2 + r.2.2 + 3) * F r.1.2 r.2.2 r.1.1) :=
        Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul h1 h2
      exact Computable₂.comp (f := fun a b : ℚ => a + b) computable₂_ratAdd
        (Computable.fst.comp Computable.snd) h3
    exact Computable.list_foldl (l := fun p : BitString × ℕ => List.range (p.1.length + 1))
      (g := fun _ : BitString × ℕ => (0 : ℚ))
      (h := fun (p : BitString × ℕ) (q : ℚ × ℕ) =>
        q.1 + (1 / 2 : ℚ) ^ (p.2 + q.2 + 3) * F p.2 q.2 p.1) hl hg hh
  have hh : Computable₂ (fun (x : BitString) (q : ℚ × ℕ) =>
      q.1 + (List.range (x.length + 1)).foldl (fun acc2 l =>
        acc2 + (1 / 2 : ℚ) ^ (q.2 + l + 3) * F q.2 l x) (0 : ℚ)) := by
    have h1 : Computable (fun r : BitString × (ℚ × ℕ) =>
        (List.range (r.1.length + 1)).foldl (fun acc2 l =>
          acc2 + (1 / 2 : ℚ) ^ (r.2.2 + l + 3) * F r.2.2 l r.1) (0 : ℚ)) :=
      Computable.comp (f := fun p : BitString × ℕ =>
        (List.range (p.1.length + 1)).foldl (fun acc2 l =>
          acc2 + (1 / 2 : ℚ) ^ (p.2 + l + 3) * F p.2 l p.1) (0 : ℚ))
        (g := fun r : BitString × (ℚ × ℕ) => (r.1, r.2.2)) inner
        (Computable.pair Computable.fst (Computable.snd.comp Computable.snd))
    exact Computable₂.comp (f := fun a b : ℚ => a + b) computable₂_ratAdd
      (Computable.fst.comp Computable.snd) h1
  exact Computable.list_foldl (l := fun x : BitString => List.range (x.length + 1))
    (g := fun _ : BitString => (0 : ℚ))
    (h := fun (x : BitString) (q : ℚ × ℕ) =>
      q.1 + (List.range (x.length + 1)).foldl (fun acc2 l =>
        acc2 + (1 / 2 : ℚ) ^ (q.2 + l + 3) * F q.2 l x) (0 : ℚ)) hlen (Computable.const 0) hh

private lemma exists_computable_wins_zerosDominate_comp_computable_M :
    Computable exists_computable_wins_zerosDominate_M := by
  have h0 : Computable (fun x : BitString => exists_computable_wins_zerosDominate_M0 x / 2) :=
    computable_ratHalf.comp exists_computable_wins_zerosDominate_comp_computable_M0
  have hd := exists_computable_wins_zerosDominate_comp_computable_doubleFold
    exists_computable_wins_zerosDominate_Mtl
    exists_computable_wins_zerosDominate_comp_computable_Mtl
  have hp : Computable (fun x : BitString => (1 / 2 : ℚ) ^ x.length) :=
    Computable.comp (f := fun k : ℕ => (1 / 2 : ℚ) ^ k) (g := fun x : BitString => x.length)
      exists_computable_wins_zerosDominate_comp_computable_halfpow Computable.list_length
  have hc : Computable (fun x : BitString =>
      (1 / 2 - (1 / 8 : ℚ) * (2 - (1 / 2 : ℚ) ^ x.length) ^ 2)) := by
    have h1 : Computable (fun x : BitString => 2 - (1 / 2 : ℚ) ^ x.length) :=
      Computable₂.comp (f := fun a b : ℚ => a - b) computable₂_ratSub (Computable.const 2) hp
    have h2 : Computable (fun x : BitString => (2 - (1 / 2 : ℚ) ^ x.length) ^ 2) :=
      (Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul h1 h1).of_eq
        (fun x => by ring)
    have h3 : Computable (fun x : BitString => (1 / 8 : ℚ) * (2 - (1 / 2 : ℚ) ^ x.length) ^ 2) :=
      Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul (Computable.const _) h2
    exact Computable₂.comp (f := fun a b : ℚ => a - b) computable₂_ratSub (Computable.const _) h3
  have h01 : Computable (fun x : BitString => exists_computable_wins_zerosDominate_M0 x / 2 +
      (List.range (x.length + 1)).foldl (fun acc t =>
        acc + (List.range (x.length + 1)).foldl (fun acc2 l =>
          acc2 + (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x)
          (0 : ℚ)) (0 : ℚ)) :=
    Computable₂.comp (f := fun a b : ℚ => a + b) computable₂_ratAdd h0 hd
  exact (Computable₂.comp (f := fun a b : ℚ => a + b) computable₂_ratAdd h01 hc).of_eq
    (fun x => rfl)

/-- Step 2 -/
private lemma exists_computable_wins_zerosDominate_comp :
    IsComputableOnStrings (fun x => (exists_computable_wins_zerosDominate_M x : ℝ)) := by
  refine ⟨fun p => exists_computable_wins_zerosDominate_M p.1,
    exists_computable_wins_zerosDominate_comp_computable_M.comp Computable.fst, ?_⟩
  intro x s
  simp

private lemma exists_computable_wins_zerosDominate_wins_foldl_range (F : ℕ → ℚ) (k : ℕ)
    (a : ℚ) :
    (List.range k).foldl (fun acc i => acc + F i) a = a + ∑ i ∈ Finset.range k, F i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp
                   [add_assoc]

private lemma exists_computable_wins_zerosDominate_wins_M_eq (x : BitString) :
    exists_computable_wins_zerosDominate_M x =
      exists_computable_wins_zerosDominate_M0 x / 2 +
      ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x +
      (1 / 2 - (1 / 8 : ℚ) * (2 - (1 / 2 : ℚ) ^ x.length) ^ 2) := by
  unfold exists_computable_wins_zerosDominate_M
  simp only [exists_computable_wins_zerosDominate_wins_foldl_range, zero_add]

private lemma exists_computable_wins_zerosDominate_wins_Mtl_nonneg (t l : ℕ) (x : BitString) :
    0 ≤ exists_computable_wins_zerosDominate_Mtl t l x := by
  unfold exists_computable_wins_zerosDominate_Mtl
  dsimp only
  split_ifs <;> positivity

private lemma exists_computable_wins_zerosDominate_wins_E_nonneg (n : ℕ) : 0 ≤ (1 / 2 : ℚ) -
    (1 / 8 : ℚ) * (2 - (1 / 2 : ℚ) ^ n) ^ 2 := by
  have h1 : (1 / 2 : ℚ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : 0 < (1 / 2 : ℚ) ^ n := by positivity
  nlinarith

private lemma exists_computable_wins_zerosDominate_wins_S_nonneg (x : BitString) :
    0 ≤ ∑ t ∈ Finset.range (x.length + 1), ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x := by
  refine Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ => ?_
  have := exists_computable_wins_zerosDominate_wins_Mtl_nonneg t l x
  positivity

private lemma exists_computable_wins_zerosDominate_wins_M_ge_half (x : BitString) :
    exists_computable_wins_zerosDominate_M0 x / 2 ≤ exists_computable_wins_zerosDominate_M x := by
  rw [exists_computable_wins_zerosDominate_wins_M_eq]
  have := exists_computable_wins_zerosDominate_wins_S_nonneg x
  have := exists_computable_wins_zerosDominate_wins_E_nonneg x.length
  linarith

private lemma exists_computable_wins_zerosDominate_wins_M_ge_term (x : BitString)
    (h0 : 0 ≤ exists_computable_wins_zerosDominate_M0 x)
    (t l : ℕ) (ht : t ≤ x.length) (hl : l ≤ x.length) :
    (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x ≤
      exists_computable_wins_zerosDominate_M x := by
  rw [exists_computable_wins_zerosDominate_wins_M_eq]
  have hE := exists_computable_wins_zerosDominate_wins_E_nonneg x.length
  have hnn : ∀ t' ∈ Finset.range (x.length + 1), 0 ≤ ∑ l ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t' + l + 3) * exists_computable_wins_zerosDominate_Mtl t' l x := by
    intro t' _
    refine Finset.sum_nonneg fun l _ => ?_
    have := exists_computable_wins_zerosDominate_wins_Mtl_nonneg t' l x
    positivity
  have h1 : (1 / 2 : ℚ) ^ (t + l + 3) * exists_computable_wins_zerosDominate_Mtl t l x ≤
      ∑ l' ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t + l' + 3) * exists_computable_wins_zerosDominate_Mtl t l' x := by
    refine Finset.single_le_sum (f := fun l' => (1 / 2 : ℚ) ^ (t + l' + 3) *
                                                  exists_computable_wins_zerosDominate_Mtl t l' x)
                                                  (fun l' _ => ?_) (Finset.mem_range.mpr (by omega))
    have := exists_computable_wins_zerosDominate_wins_Mtl_nonneg t l' x
    positivity
  have h2 := Finset.single_le_sum (f := fun t' => ∑ l' ∈ Finset.range (x.length + 1),
        (1 / 2 : ℚ) ^ (t' + l' + 3) * exists_computable_wins_zerosDominate_Mtl t' l' x) hnn
            (Finset.mem_range.mpr (show t < x.length + 1 by omega))
  linarith

private lemma exists_computable_wins_zerosDominate_wins_finite_lt (D : ℕ → ℕ) (L : ℕ)
    (h : ∀ l < L, {i | D i = l}.Finite) :
    {i | D i < L}.Finite := by
  have : {i | D i < L} = ⋃ l ∈ Set.Iio L, {i | D i = l} := by ext i; simp
  rw [this]
  exact (Set.finite_Iio L).biUnion h

private lemma exists_computable_wins_zerosDominate_wins_M0_append (x : BitString) (b : Bool) :
    exists_computable_wins_zerosDominate_M0 (x ++ [b]) =
      if exists_computable_wins_zerosDominate_M0 x > 0 then
        (if b == false then exists_computable_wins_zerosDominate_M0 x + 1
          else exists_computable_wins_zerosDominate_M0 x - 1) else 0 := by
  unfold exists_computable_wins_zerosDominate_M0
  rw [List.foldl_append]
  rfl

private lemma exists_computable_wins_zerosDominate_wins_counts_false (w : CantorSeq) (i : ℕ)
    (h : w i = false) :
    zerosCount w (i + 1) = zerosCount w i + 1 ∧ onesCount w (i + 1) = onesCount w i := by
  simp [zerosCount, onesCount, cantorPrefix_succ, h, List.count_append]

private lemma exists_computable_wins_zerosDominate_wins_counts_true (w : CantorSeq) (i : ℕ)
    (h : w i = true) :
    zerosCount w (i + 1) = zerosCount w i ∧ onesCount w (i + 1) = onesCount w i + 1 := by
  simp [zerosCount, onesCount, cantorPrefix_succ, h, List.count_append]

private lemma exists_computable_wins_zerosDominate_wins_M0_prefix (w : CantorSeq)
    (hw : ZerosDominate w) (n : ℕ) :
    exists_computable_wins_zerosDominate_M0 (cantorPrefix w n) =
      1 + (zerosCount w n : ℚ) - (onesCount w n : ℚ) := by
  induction n with
  | zero => simp [exists_computable_wins_zerosDominate_M0, cantorPrefix, zerosCount, onesCount]
  | succ n ih =>
    rw [cantorPrefix_succ, exists_computable_wins_zerosDominate_wins_M0_append, ih]
    have h1 : ((onesCount w n : ℕ) : ℚ) ≤ (zerosCount w n : ℕ) := by exact_mod_cast hw n
    have hpos : (1 + (zerosCount w n : ℚ) - (onesCount w n : ℚ)) > 0 := by linarith
    rw [ite_eq_left hpos]
    cases h : w n
    · obtain ⟨a, b⟩ := exists_computable_wins_zerosDominate_wins_counts_false w n h
      rw [a, b]; simp; ring
    · obtain ⟨a, b⟩ := exists_computable_wins_zerosDominate_wins_counts_true w n h
      rw [a, b]; simp; ring

private lemma exists_computable_wins_zerosDominate_wins_Mtl_prefix (w : CantorSeq) (t l n : ℕ)
    (hb : ∀ i, t ≤ i → zerosCount w i - onesCount w i = l → w i = false) :
    exists_computable_wins_zerosDominate_Mtl t l (cantorPrefix w n) =
      2 ^ ((List.range n).filter (fun i => decide (t ≤ i) &&
        (zerosCount w i - onesCount w i == l))).length := by
  have hfil : (List.range (cantorPrefix w n).length).filter (fun i => decide (t ≤ i) &&
      (((cantorPrefix w n).take i).count false - ((cantorPrefix w n).take i).count true == l)) =
      (List.range n).filter (fun i => decide (t ≤ i) &&
        (zerosCount w i - onesCount w i == l)) := by
    rw [cantorPrefix_length]
    apply List.filter_congr
    intro i hi
    have := List.mem_range.mp hi
    rw [cantorPrefix_take w i n this.le]; rfl
  unfold exists_computable_wins_zerosDominate_Mtl
  dsimp only
  rw [hfil]
  have hwrong : ((List.range n).filter (fun i => decide (t ≤ i) &&
        (zerosCount w i - onesCount w i == l))).any
        (fun i => ((cantorPrefix w n).drop i).head? == some true) = false := by
    rw [List.any_eq_false]
    intro i hi
    rw [List.mem_filter] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have hin := List.mem_range.mp hi1
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi2
    have := hb i hi2.1 hi2.2
    simp [List.head?_drop, this, hin]
  rw [hwrong]
  simp

private lemma exists_computable_wins_zerosDominate_wins_caseA (w : CantorSeq)
    (hw : ZerosDominate w)
    (hfin : ∀ l, {i | zerosCount w i - onesCount w i = l}.Finite) (C : ℚ) :
    ∃ n, C < exists_computable_wins_zerosDominate_M (cantorPrefix w n) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * C)
  obtain ⟨N, hN⟩ := (exists_computable_wins_zerosDominate_wins_finite_lt
      (fun i => zerosCount w i - onesCount w i) (K + 1)
    (fun l _ => hfin l)).bddAbove
  refine ⟨N + 1, ?_⟩
  have hNot : ¬ (zerosCount w (N + 1) - onesCount w (N + 1) < K + 1) := fun h => by
    have := hN (show N + 1 ∈ {i | zerosCount w i - onesCount w i < K + 1} from h)
    omega
  have h0 := exists_computable_wins_zerosDominate_wins_M0_prefix w hw (N + 1)
  have hle : onesCount w (N + 1) ≤ zerosCount w (N + 1) := hw _
  have hge := exists_computable_wins_zerosDominate_wins_M_ge_half (cantorPrefix w (N + 1))
  have h1 : K + 1 ≤ zerosCount w (N + 1) - onesCount w (N + 1) := by omega
  have h2 : ((K + 1 : ℕ) : ℚ) ≤ ((zerosCount w (N + 1) - onesCount w (N + 1) : ℕ) : ℚ) := by
    exact_mod_cast h1
  rw [Nat.cast_sub hle] at h2
  push_cast at h2
  rw [h0] at hge
  linarith

private lemma exists_computable_wins_zerosDominate_wins_caseB (w : CantorSeq)
    (hw : ZerosDominate w) (l : ℕ)
    (hinf : {i | zerosCount w i - onesCount w i = l}.Infinite)
    (hfin : ∀ l' < l, {i | zerosCount w i - onesCount w i = l'}.Finite) (C : ℚ) :
    ∃ n, C < exists_computable_wins_zerosDominate_M (cantorPrefix w n) := by
  obtain ⟨t, ht⟩ : ∃ t, ∀ i, t ≤ i → l ≤ zerosCount w i - onesCount w i := by
    obtain ⟨N, hN⟩ := (exists_computable_wins_zerosDominate_wins_finite_lt
        (fun i => zerosCount w i - onesCount w i) l hfin).bddAbove
    refine ⟨N + 1, fun i hi => ?_⟩
    by_contra h
    push Not at h
    have := hN (show i ∈ {i | zerosCount w i - onesCount w i < l} from h)
    omega
  have hb : ∀ i, t ≤ i → zerosCount w i - onesCount w i = l → w i = false := by
    intro i hi hDi
    by_contra hwi
    have hwi' : w i = true := by simpa using hwi
    obtain ⟨a, b⟩ := exists_computable_wins_zerosDominate_wins_counts_true w i hwi'
    have h1 := hw (i + 1)
    have h2 := ht (i + 1) (by omega)
    have h3 := hw i
    omega
  have hT : {i | t ≤ i ∧ zerosCount w i - onesCount w i = l}.Infinite :=
    (hinf.sdiff (Set.finite_Iio t)).mono (fun i hi => ⟨by simpa using hi.2, hi.1⟩)
  obtain ⟨K, hK⟩ := exists_nat_gt (C * 2 ^ (t + l + 3))
  obtain ⟨s, hs, hcard⟩ := hT.exists_subset_card_eq K
  obtain ⟨n0, hn0⟩ := Finset.exists_nat_subset_range s
  refine ⟨n0 + t + l, ?_⟩
  have h0 : 0 ≤ exists_computable_wins_zerosDominate_M0 (cantorPrefix w (n0 + t + l)) := by
    rw [exists_computable_wins_zerosDominate_wins_M0_prefix w hw]
    have : (onesCount w (n0 + t + l) : ℚ) ≤ zerosCount w (n0 + t + l) := by
      exact_mod_cast hw _
    linarith
  have hterm := exists_computable_wins_zerosDominate_wins_M_ge_term
      (cantorPrefix w (n0 + t + l)) h0 t l (by simp; omega)
    (by simp)
  rw [exists_computable_wins_zerosDominate_wins_Mtl_prefix w t l (n0 + t + l) hb] at hterm
  have hlen : K ≤ ((List.range (n0 + t + l)).filter (fun i => decide (t ≤ i) &&
      (zerosCount w i - onesCount w i == l))).length := by
    have hsub : s ⊆ ((List.range (n0 + t + l)).filter (fun i => decide (t ≤ i) &&
        (zerosCount w i - onesCount w i == l))).toFinset := by
      intro i hi
      have h1 := hs hi
      simp only [Set.mem_ofPred_eq] at h1
      have h2 := hn0 hi
      rw [Finset.mem_range] at h2
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq]
      exact ⟨by omega, h1.1, h1.2⟩
    calc K = s.card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := List.toFinset_card_le _
  have h2K : (K : ℚ) < 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self
  have h2len := pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num) hlen
  have hpos : (0 : ℚ) < (1 / 2) ^ (t + l + 3) := by positivity
  have e : (1 / 2 : ℚ) ^ (t + l + 3) * 2 ^ (t + l + 3) = 1 := by
    rw [← mul_pow]; norm_num
  have h3 : C < (1 / 2 : ℚ) ^ (t + l + 3) * K := by
    calc C = (1 / 2 : ℚ) ^ (t + l + 3) * (C * 2 ^ (t + l + 3)) := by
          rw [mul_left_comm, e, mul_one]
      _ < _ := mul_lt_mul_of_pos_left hK hpos
  have h4 : (1 / 2 : ℚ) ^ (t + l + 3) * K ≤ (1 / 2 : ℚ) ^ (t + l + 3) * 2 ^ _ :=
    mul_le_mul_of_nonneg_left (h2K.le.trans h2len) hpos.le
  linarith

private lemma exists_computable_wins_zerosDominate_wins_exists_big (w : CantorSeq)
    (hw : ZerosDominate w) (C : ℚ) :
    ∃ n, C < exists_computable_wins_zerosDominate_M (cantorPrefix w n) := by
  classical
  by_cases h : ∀ l, {i | zerosCount w i - onesCount w i = l}.Finite
  · exact exists_computable_wins_zerosDominate_wins_caseA w hw h C
  · push Not at h
    refine exists_computable_wins_zerosDominate_wins_caseB w hw (Nat.find h) (Nat.find_spec h)
        (fun l' hl' => ?_) C
    have := Nat.find_min h hl'
    exact not_not.mp this

/-- Step 3 -/
private lemma exists_computable_wins_zerosDominate_wins (w : CantorSeq) (hw : ZerosDominate w)
    :
    Wins (fun x => (exists_computable_wins_zerosDominate_M x : ℝ)) w := by
  rintro ⟨C, hC⟩
  obtain ⟨C', hC'⟩ := exists_rat_gt C
  obtain ⟨n, hn⟩ := exists_computable_wins_zerosDominate_wins_exists_big w hw C'
  have h1 := hC ⟨n, rfl⟩
  have h3 : (C' : ℝ) < (exists_computable_wins_zerosDominate_M (cantorPrefix w n) : ℝ) := by
    exact_mod_cast hn
  simp only at h1
  linarith

/-- **SUV Problem 267, p. 281.**  There is a computable uniform martingale winning on all sequences
each prefix of which has at least as many zeros as ones: the explicit martingale of the proof of
Theorem 182(d). -/
theorem exists_computable_wins_zerosDominate :
    ∃ m, IsFairCapital uniformMeasure m ∧ IsComputableOnStrings m ∧
      ∀ w, ZerosDominate w → Wins m w := by
  refine ⟨fun x => (exists_computable_wins_zerosDominate_M x : ℝ), ?_, ?_, ?_⟩
  · exact exists_computable_wins_zerosDominate_fair
  · exact exists_computable_wins_zerosDominate_comp
  · intro w hw
    exact exists_computable_wins_zerosDominate_wins w hw

end Kolmogorov.FrequencyGames
