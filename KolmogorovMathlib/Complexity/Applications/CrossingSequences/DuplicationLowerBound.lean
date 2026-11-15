/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.CrossingSequences.CrossingSequenceBound

/-!
# Duplication Lower Bound

A one-tape Turing machine that duplicates its input needs quadratically many steps.

The module bounds the plain complexity of the right part of the tape after `t` steps by the
length of a crossing sequence (`rightComplexity_le`, Theorem 152 of the book by Shen, Uspensky
and Vereshchagin, and its refinement `rightComplexity_le_two_mul`, Problem 242).  From this it
derives the main result `exists_duplication_lower_bound` (Theorem 153): for a machine that
duplicates its input there is `ε > 0` such that for every `n` some `n`-bit string requires at
least `ε n²` steps to be duplicated.
-/

namespace Kolmogorov.Applications
open TuringMachine
variable {Q Γ : Type*}

private lemma rightComplexity_le_crossingSequence_length (M : TuringMachine Q Γ) (c :
    TapeConfig Q Γ) (p : ℤ) (t : ℕ) :
    (M.crossingSequence c p t).length = (M.crossingSteps c p t).card := by
  classical
  unfold crossingSequence crossingSteps
  simp only [List.length_map]
  have hfilter : ((List.range t).filter (M.CrossesAt c p)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hfilter]
  congr 1
  ext x
  simp

private lemma rightComplexity_le_exists_crossingSequence_length_short (M : TuringMachine Q Γ)
    (c : TapeConfig Q Γ) (a : ℤ) (b t : ℕ) :
    ∃ k ≤ b, (b + 1) * (M.crossingSequence c (a + k) t).length ≤ t := by
  have := M.exists_crossingSteps_short c a b t
  rcases this with ⟨k, hk, h⟩
  use k, hk
  rw [rightComplexity_le_crossingSequence_length]
  exact h

section CrossingBound

variable [Fintype Q] [Fintype Γ] [Encodable Γ]

/-- **SUV Theorem 152, p. 234.**  Let `M` be a Turing machine with `m` states.  There is a constant
`c` such that for any `b ≥ 1` and any computation that starts with an empty buffer zone of size `b`
and an empty tape on the right of it, with the head on the left of the buffer, the complexity of the
content `R(t)` of the right part of the tape after `t` steps is at most
`t log m / b + 4 log t + c`.

For `b = 0` the bound is false: nothing prevents a machine from copying its left zone to the
right. -/
theorem rightComplexity_le (V : Map) (hV : isOptimalConditional V)
    (M : TuringMachine Q Γ) :
    ∃ c : ℝ, ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ c₀ : TapeConfig Q Γ, c₀.head ≤ a →
      (∀ i, a < i → c₀.tape i = M.blank) → ∀ t : ℕ,
        rightComplexity V M (M.run c₀ t).tape (a + b) ≤
          t * Real.logb 2 (Fintype.card Q) / b + 4 * Real.logb 2 t + c := by
  obtain ⟨c, hc⟩ := rightComplexity_le_crossingSequence V hV M
  use c
  intro a b hb c₀ hc₀ h_empty t
  obtain ⟨k, hk, hlen⟩ := rightComplexity_le_exists_crossingSequence_length_short M c₀ a b t
  have h_bound := hc a b k hk c₀ hc₀ h_empty t
  apply le_trans h_bound
  gcongr
  by_cases hQ : Fintype.card Q = 0
  · rw [hQ]
    norm_num
  · have hQ_pos : 1 ≤ Fintype.card Q := Nat.pos_of_ne_zero hQ
    have h_log_nonneg : 0 ≤ Real.logb 2 (Fintype.card Q) := by
      apply Real.logb_nonneg
      · norm_num
      · exact_mod_cast hQ_pos
    have h_len_le : (M.crossingSequence c₀ (a + ↑k) t).length ≤ (t : ℝ) / (b + 1 : ℝ) := by
      have h_b_pos : (0 : ℝ) < b + 1 := by exact_mod_cast Nat.succ_pos b
      rw [le_div_iff₀ h_b_pos]
      have : (b + 1 : ℝ) * (M.crossingSequence c₀ (a + ↑k) t).length = ((b + 1) *
          (M.crossingSequence c₀ (a + ↑k) t).length : ℕ) := by
        push_cast; ring
      rw [mul_comm]
      rw [this]
      exact_mod_cast hlen
    have h_b_le : (t : ℝ) / (b + 1 : ℝ) ≤ (t : ℝ) / (b : ℝ) := by
      apply div_le_div_of_nonneg_left
      · exact_mod_cast (Nat.zero_le t)
      · exact_mod_cast hb
      · exact_mod_cast (Nat.le_succ b)
    have : ((M.crossingSequence c₀ (a + ↑k) t).length : ℝ) * Real.logb 2 (Fintype.card Q) ≤ (t : ℝ)
        / (b : ℝ) * Real.logb 2 (Fintype.card Q) := by
      apply mul_le_mul_of_nonneg_right
      · exact h_len_le.trans h_b_le
      · exact h_log_nonneg
    have hz : (t : ℝ) / (b : ℝ) * Real.logb 2 (Fintype.card Q) = ↑t * Real.logb 2 ↑(Fintype.card Q)
        / ↑b := by
      ring
    rw [← hz]
    exact this

end CrossingBound

private def rightComplexity_le_two_mul_CrossesLeftAt (M : TuringMachine Q Γ) (c : TapeConfig Q
    Γ) (p : ℤ) (s : ℕ) : Prop :=
  (M.run c s).head = p + 1 ∧ (M.run c (s + 1)).head = p

open Classical in
private noncomputable def rightComplexity_le_two_mul_crossingLeftSteps (M : TuringMachine Q Γ)
    (c : TapeConfig Q Γ) (p : ℤ) (t : ℕ) :
    Finset ℕ :=
  (Finset.range t).filter (rightComplexity_le_two_mul_CrossesLeftAt M c p)

private lemma rightComplexity_le_two_mul_crossesLeftAt_unique (M : TuringMachine Q Γ) (c :
    TapeConfig Q Γ) {p p' : ℤ} {s : ℕ}
    (h : rightComplexity_le_two_mul_CrossesLeftAt M c p s) (h' :
        rightComplexity_le_two_mul_CrossesLeftAt M c p' s) : p = p' := by
  have h1 := h.1
  have h2 := h'.1
  omega


private lemma rightComplexity_le_two_mul_crossesRight_left_disjoint (M : TuringMachine Q Γ) (c
    : TapeConfig Q Γ) {p p' : ℤ} {s : ℕ}
    (h : M.CrossesAt c p s) (h' : rightComplexity_le_two_mul_CrossesLeftAt M c p' s) : False
        := by
  dsimp [TuringMachine.CrossesAt, rightComplexity_le_two_mul_CrossesLeftAt] at h h'
  omega

private lemma rightComplexity_le_two_mul_sum_card_le (M : TuringMachine Q Γ) (c : TapeConfig Q
    Γ) (a : ℤ) (b t : ℕ) :
    ∑ k ∈ Finset.range (b + 1), ((M.crossingSteps c (a + k) t).card +
        (rightComplexity_le_two_mul_crossingLeftSteps M c (a + k) t).card) ≤ t := by
  classical
  rw [Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.range (b + 1), (M.crossingSteps c (a + k) t).card = ((Finset.range (b +
      1)).biUnion fun k => M.crossingSteps c (a + k) t).card := by
    rw [Finset.card_biUnion]
    intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun s hs hs' => hkl ?_
    have h := M.crossesAt_unique c (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hs').2
    exact_mod_cast add_left_cancel h
  have h2 : ∑ k ∈ Finset.range (b + 1), (rightComplexity_le_two_mul_crossingLeftSteps M c (a +
      k) t).card = ((Finset.range (b + 1)).biUnion fun k =>
      rightComplexity_le_two_mul_crossingLeftSteps M c (a + k) t).card := by
    rw [Finset.card_biUnion]
    intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun s hs hs' => hkl ?_
    have hk_mem : rightComplexity_le_two_mul_CrossesLeftAt M c (a + k) s := by
      exact (Finset.mem_filter.mp hs).2
    have hl_mem : rightComplexity_le_two_mul_CrossesLeftAt M c (a + l) s := by
      exact (Finset.mem_filter.mp hs').2
    have h := rightComplexity_le_two_mul_crossesLeftAt_unique M c hk_mem hl_mem
    exact_mod_cast add_left_cancel h
  rw [h1, h2]
  rw [← Finset.card_union_of_disjoint]
  · calc (((Finset.range (b + 1)).biUnion fun k => M.crossingSteps c (a + k) t) ∪ ((Finset.range (b
      + 1)).biUnion fun k => rightComplexity_le_two_mul_crossingLeftSteps M c (a + k) t)).card
        ≤ (Finset.range t).card := by
          refine Finset.card_le_card fun s hs => ?_
          rcases Finset.mem_union.mp hs with hs1 | hs2
          · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hs1
            exact (Finset.mem_filter.mp hk).1
          · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hs2
            exact (Finset.mem_filter.mp hk).1
      _ = t := Finset.card_range t
  · refine Finset.disjoint_left.mpr fun s hs hs' => ?_
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp hs'
    have hl_mem : rightComplexity_le_two_mul_CrossesLeftAt M c (a + l) s := by
      exact (Finset.mem_filter.mp hl).2
    exact rightComplexity_le_two_mul_crossesRight_left_disjoint M c (Finset.mem_filter.mp
        hk).2 hl_mem


private lemma rightComplexity_le_two_mul_filter_range_succ_card
    (P : ℕ → Prop) [DecidablePred P] (s : ℕ) :
    ((Finset.range (s + 1)).filter P).card =
      ((Finset.range s).filter P).card + (if P s then 1 else 0) := by
  have h : Finset.range (s + 1) = insert s (Finset.range s) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  rw [h, Finset.filter_insert]
  split
  · have h1 : s ∉ Finset.filter P (Finset.range s) := by
      intro h_mem
      have h2 := Finset.mem_filter.mp h_mem
      have h3 := Finset.mem_range.mp h2.1
      omega
    have h2 : Finset.card (insert s (Finset.filter P (Finset.range s))) = Finset.card (Finset.filter
        P (Finset.range s)) + 1 := Finset.card_insert_of_notMem h1
    rw [h2]
  · rfl

private lemma rightComplexity_le_two_mul_head_bound
    (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (s : ℕ) :
    (M.run c (s + 1)).head ≤ (M.run c s).head + 1 ∧
    (M.run c s).head ≤ (M.run c (s + 1)).head + 1 := by
  have h : M.run c (s + 1) = M.next (M.run c s) := Function.iterate_succ_apply' M.next s c
  rw [h]
  unfold TuringMachine.next
  split
  · exact ⟨by omega, by omega⟩
  · rename_i move _
    cases move
    · simp [TapeMove.delta]
    · simp [TapeMove.delta]
    · simp [TapeMove.delta]
      omega

open Classical in
private lemma rightComplexity_le_two_mul_invariant
    (M : TuringMachine Q Γ) (c : TapeConfig Q Γ) (p : ℤ) :
    ∀ s,
      ((M.run c s).head ≤ p →
        (M.crossingSteps c p s).card ≤
          (rightComplexity_le_two_mul_crossingLeftSteps M c p s).card) ∧
      ((M.run c s).head > p →
        (M.crossingSteps c p s).card ≤
          (rightComplexity_le_two_mul_crossingLeftSteps M c p s).card + 1) := by
  intro s
  induction s with
  | zero =>
    have h1 : M.crossingSteps c p 0 = ∅ := rfl
    have h2 : rightComplexity_le_two_mul_crossingLeftSteps M c p 0 = ∅ := rfl
    rw [h1, h2, Finset.card_empty]
    constructor
    · intro _h; exact le_rfl
    · intro _h; exact zero_le_one
  | succ t ih =>
    have h1 : (M.crossingSteps c p (t + 1)).card = (M.crossingSteps c p t).card + (if M.CrossesAt c
        p t then 1 else 0) := by
      unfold crossingSteps
      rw [rightComplexity_le_two_mul_filter_range_succ_card]
    have h2 : (rightComplexity_le_two_mul_crossingLeftSteps M c p (t + 1)).card =
        (rightComplexity_le_two_mul_crossingLeftSteps M c p t).card + (if
        rightComplexity_le_two_mul_CrossesLeftAt M c p t then 1 else 0) := by
      unfold rightComplexity_le_two_mul_crossingLeftSteps
      rw [rightComplexity_le_two_mul_filter_range_succ_card]
    have hb := rightComplexity_le_two_mul_head_bound M c t
    rw [h1, h2]
    by_cases htp : (M.run c t).head ≤ p
    · have ih1 := ih.1 htp
      constructor
      · intro htp_succ
        by_cases ht_cross : M.CrossesAt c p t
        · unfold CrossesAt at ht_cross
          omega
        · by_cases ht_cross_left : rightComplexity_le_two_mul_CrossesLeftAt M c p t
          · simp [ht_cross_left, ht_cross]
            omega
          · simp [ht_cross_left, ht_cross]
            omega
      · intro htp_succ
        by_cases ht_cross : M.CrossesAt c p t
        · by_cases ht_cross_left : rightComplexity_le_two_mul_CrossesLeftAt M c p t
          · simp [ht_cross_left, ht_cross]
            omega
          · simp [ht_cross_left, ht_cross]
            omega
        · by_cases ht_cross_left : rightComplexity_le_two_mul_CrossesLeftAt M c p t
          · simp [ht_cross_left, ht_cross]
            omega
          · simp [ht_cross_left, ht_cross]
            omega
    · have htp_gt : (M.run c t).head > p := by omega
      have ih2 := ih.2 htp_gt
      constructor
      · intro htp_succ
        by_cases ht_cross : M.CrossesAt c p t
        · unfold CrossesAt at ht_cross
          omega
        · by_cases ht_cross_left : rightComplexity_le_two_mul_CrossesLeftAt M c p t
          · simp [ht_cross_left, ht_cross]
            omega
          · unfold rightComplexity_le_two_mul_CrossesLeftAt at ht_cross_left
            omega
      · intro htp_succ
        by_cases ht_cross : M.CrossesAt c p t
        · by_cases ht_cross_left : rightComplexity_le_two_mul_CrossesLeftAt M c p t
          · simp [ht_cross_left, ht_cross]
            omega
          · simp [ht_cross_left, ht_cross]
            unfold CrossesAt at ht_cross
            omega
        · by_cases ht_cross_left : rightComplexity_le_two_mul_CrossesLeftAt M c p t
          · simp [ht_cross_left, ht_cross]
            omega
          · simp [ht_cross_left, ht_cross]
            omega

private lemma rightComplexity_le_two_mul_return_trip (M : TuringMachine Q Γ) (c : TapeConfig Q
    Γ) (p : ℤ) (t : ℕ) :
    (M.crossingSteps c p t).card ≤ (rightComplexity_le_two_mul_crossingLeftSteps M c p t).card
        + 1 := by
  have h := rightComplexity_le_two_mul_invariant M c p t
  by_cases htp : (M.run c t).head ≤ p
  · have h_le := h.1 htp
    omega
  · have h_gt := h.2 (by omega)
    omega

private lemma rightComplexity_le_two_mul_exists_short (M : TuringMachine Q Γ) (c : TapeConfig
    Q Γ) (a : ℤ) (b t : ℕ) (hb : 0 < b) :
    ∃ k ≤ b, (2 * b) * (M.crossingSteps c (a + k) t).card ≤ t + b := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have h_sum1 : ∑ k ∈ Finset.range (b + 1), 2 * (M.crossingSteps c (a + k) t).card ≤ t + b + 1 := by
    calc
      ∑ k ∈ Finset.range (b + 1), 2 * (M.crossingSteps c (a + k) t).card ≤ ∑ k ∈ Finset.range (b +
          1), ((M.crossingSteps c (a + k) t).card +
          (rightComplexity_le_two_mul_crossingLeftSteps M c (a + k) t).card + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ b := by
          rw [Finset.mem_range] at hi
          omega
        have h4i := rightComplexity_le_two_mul_return_trip M c (a + i) t
        omega
      _ = ∑ k ∈ Finset.range (b + 1), ((M.crossingSteps c (a + k) t).card +
          (rightComplexity_le_two_mul_crossingLeftSteps M c (a + k) t).card) + ∑ k ∈
          Finset.range (b + 1), 1 := Finset.sum_add_distrib
      _ ≤ t + (b + 1) := by
        have : ∑ k ∈ Finset.range (b + 1), 1 = b + 1 := by
          simp
        have h3 := rightComplexity_le_two_mul_sum_card_le M c a b t
        omega
  have h_sum2 : (b + 1) * (t + b) < ∑ k ∈ Finset.range (b + 1), 2 * b * (M.crossingSteps c (a + k)
      t).card := by
    have h_nonempty : (Finset.range (b + 1)).Nonempty := by
      exact ⟨0, Finset.mem_range.mpr (by omega)⟩
    calc (b + 1) * (t + b) = ∑ k ∈ Finset.range (b + 1), (t + b) := by simp [mul_comm]
      _ < ∑ k ∈ Finset.range (b + 1), 2 * b * (M.crossingSteps c (a + k) t).card := by
          apply Finset.sum_lt_sum_of_nonempty h_nonempty
          intro i hi
          have hi_le : i ≤ b := by
            rw [Finset.mem_range] at hi
            omega
          exact h i hi_le
  have h_sum3 : ∑ k ∈ Finset.range (b + 1), 2 * b * (M.crossingSteps c (a + k) t).card = b * ∑ k ∈
      Finset.range (b + 1), 2 * (M.crossingSteps c (a + k) t).card := by
    have : ∀ k, 2 * b * (M.crossingSteps c (a + k) t).card = b * (2 * (M.crossingSteps c (a + k)
        t).card) := by intro k; ring
    simp_rw [this, ← Finset.mul_sum]
  nlinarith


private lemma rightComplexity_le_two_mul_crossingSequence_length (M : TuringMachine Q Γ) (c :
    TapeConfig Q Γ) (p : ℤ) (t : ℕ) :
    (M.crossingSequence c p t).length = (M.crossingSteps c p t).card := by
  classical
  unfold crossingSequence crossingSteps
  simp only [List.length_map]
  have hfilter : ((List.range t).filter (M.CrossesAt c p)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hfilter]
  congr 1
  ext x
  simp

section CrossingBoundTwo

variable [Fintype Q] [Fintype Γ] [Encodable Γ]

/-- **SUV Problem 242, p. 235.**  In Theorem 152, `b` in the denominator can be replaced by `2b`:
the return trips need almost the same time, the difference being at most `b`. -/
theorem rightComplexity_le_two_mul (V : Map) (hV : isOptimalConditional V)
    (M : TuringMachine Q Γ) :
    ∃ c : ℝ, ∀ (a : ℤ) (b : ℕ), 0 < b → ∀ c₀ : TapeConfig Q Γ, c₀.head ≤ a →
      (∀ i, a < i → c₀.tape i = M.blank) → ∀ t : ℕ,
        rightComplexity V M (M.run c₀ t).tape (a + b) ≤
          t * Real.logb 2 (Fintype.card Q) / (2 * b) + 4 * Real.logb 2 t + c := by
  obtain ⟨c, hc⟩ := rightComplexity_le_crossingSequence V hV M
  use c + Real.logb 2 (Fintype.card Q) / 2
  intro a b hb c₀ hc₀ h_empty t
  obtain ⟨k, hk, hlen⟩ := rightComplexity_le_two_mul_exists_short M c₀ a b t hb
  have h_bound := hc a b k hk c₀ hc₀ h_empty t
  apply le_trans h_bound
  have h_log_nonneg : 0 ≤ Real.logb 2 (Fintype.card Q) := by
    by_cases hQ : Fintype.card Q = 0
    · rw [hQ]
      norm_num
    · apply Real.logb_nonneg
      · norm_num
      · exact_mod_cast Nat.pos_of_ne_zero hQ
  have h_len_le : (M.crossingSequence c₀ (a + ↑k) t).length ≤ ((t : ℝ) + b) / (2 * b) := by
    have h_2b_pos : (0 : ℝ) < 2 * b := by exact_mod_cast mul_pos (by norm_num) hb
    rw [le_div_iff₀ h_2b_pos]
    have : (2 * b : ℝ) * (M.crossingSequence c₀ (a + ↑k) t).length = ((2 * b) * (M.crossingSequence
        c₀ (a + ↑k) t).length : ℕ) := by
      push_cast; ring
    rw [mul_comm]
    rw [this]
    rw [rightComplexity_le_two_mul_crossingSequence_length]
    exact_mod_cast hlen
  have h_b_div : ((t : ℝ) + b) / (2 * b) = (t : ℝ) / (2 * b) + 1 / 2 := by
    calc ((t : ℝ) + b) / (2 * b) = (t : ℝ) / (2 * b) + (b : ℝ) / (2 * b) := by ring
      _ = (t : ℝ) / (2 * b) + 1 / 2 := by
        congr 1
        have h_b_ne_zero : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
        have h2 : (2 * b : ℝ) = 2 * (b : ℝ) := by norm_cast
        rw [h2]
        calc (b : ℝ) / (2 * (b : ℝ)) = (b : ℝ) / (b : ℝ) / 2 := by ring
          _ = 1 / 2 := by rw [div_self h_b_ne_zero]
  have h_mul_le : ((M.crossingSequence c₀ (a + ↑k) t).length : ℝ) * Real.logb 2 (Fintype.card Q) ≤
      ((t : ℝ) / (2 * b) + 1 / 2) * Real.logb 2 (Fintype.card Q) := by
    apply mul_le_mul_of_nonneg_right
    · exact h_len_le.trans (le_of_eq h_b_div)
    · exact h_log_nonneg
  have hz : ((t : ℝ) / (2 * b) + 1 / 2) * Real.logb 2 (Fintype.card Q) + 4 * Real.logb 2 t + c =
            (t : ℝ) * Real.logb 2 (Fintype.card Q) / (2 * b) + 4 * Real.logb 2 t + (c + Real.logb 2
                (Fintype.card Q) / 2) := by
    have : ((t : ℝ) / (2 * b) + 1 / 2) * Real.logb 2 ↑(Fintype.card Q) = (t : ℝ) * Real.logb 2
        (Fintype.card Q) / (2 * b) + Real.logb 2 ↑(Fintype.card Q) / 2 := by ring
    rw [this]
    ring
  rw [← hz]
  gcongr

end CrossingBoundTwo

private lemma exists_duplication_lower_bound_card_Q_nonneg [Fintype Q] :
    0 ≤ Real.logb 2 (Fintype.card Q) := by
  by_cases hQ : Fintype.card Q = 0
  · rw [hQ]
    norm_num
  · apply Real.logb_nonneg
    · norm_num
    · exact_mod_cast Nat.pos_of_ne_zero hQ

/-- For an injective `g` and every `m` some string `u` of length `m` has `g u` of complexity at
least `m` (pigeonhole, as in `exists_incompressible_string`). -/
private lemma exists_duplication_lower_bound_rightComplexity_lower_bound_aux_image
    (V : Map) (g : BitString → BitString) (hg : Function.Injective g) (m : ℕ) :
    ∃ u : BitString, u.length = m ∧ (m : ENat) ≤ plainK V (g u) := by
  classical
  cases m with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ m =>
    by_contra h_contra
    push Not at h_contra
    have h_sub : (stringsOfLength (m + 1)).image g ⊆ compressibleWords V [] m := by
      intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      rw [mem_stringsOfLength] at hu
      have h_lt : condK V (g u) [] < ((m + 1 : ℕ) : ENat) := h_contra u hu
      rw [compressibleWords, Finset.mem_filter]
      obtain ⟨len_enat, h_mem_len, h_val_lt⟩ := (sInf_lt_iff).mp h_lt
      obtain ⟨p, hp_prod, rfl⟩ := h_mem_len
      have h_len_le : programLength p ≤ m := by
        have : (programLength p : ENat) < ((m + 1 : ℕ) : ENat) := h_val_lt
        exact Nat.lt_succ_iff.mp (ENat.natCast_lt_natCast.mp this)
      refine ⟨?_, ?_⟩
      · rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
        exact ⟨p, mem_programsLe m p h_len_le, progToOut_eq_some.mpr hp_prod⟩
      · have hmem : (programLength p : ENat) ∈ candidateLengths V (g u) [] := ⟨p, hp_prod, rfl⟩
        calc condK V (g u) [] ≤ (programLength p : ENat) := sInf_le hmem
          _ ≤ (m : ENat) := by exact_mod_cast h_len_le
    have h_card := Finset.card_le_card h_sub
    rw [Finset.card_image_of_injective _ hg, card_stringsOfLength] at h_card
    have h_lt := card_compressibleWordsLt V [] m
    omega

/-- The content `R` after the first `n + n / 2` cells of the tape of a machine that duplicated
`replicate (n / 2) false ++ u` is `u.map sym`. -/
private lemma exists_duplication_lower_bound_rightComplexity_lower_bound_aux_content
    [Finite Q] [Finite Γ] [Encodable Γ]
    {M : TuringMachine Q Γ} {sym : Bool → Γ} (hsym : M.IsInputEncoding sym)
    (τ : ℤ → Γ) (k : ℕ) (u : List Bool)
    (hτ : ∀ i : ℕ, τ i = ((((List.replicate k false ++ u) ++ (List.replicate k false ++ u))[i]?).map
      sym).getD M.blank) :
    M.rightContents τ ((((k + u.length : ℕ) : ℤ) - 1) + k) = u.map sym := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite Γ
  set x := List.replicate k false ++ u with hx
  have hxlen : x.length = k + u.length := by simp [hx]
  have hcell : ∀ j : ℕ, τ (((k + u.length : ℕ) : ℤ) - 1 + k + 1 + j) = ((u[j]?).map sym).getD
      M.blank := by
    intro j
    have : (((k + u.length : ℕ) : ℤ) - 1 + k + 1 + j) = ((x.length + (k + j) : ℕ) : ℤ) := by
      rw [hxlen]; push_cast; ring
    rw [this, hτ, List.getElem?_append_right (by omega)]
    have h1 : x.length + (k + j) - x.length = k + j := by omega
    rw [h1, hx, List.getElem?_append_right (by simp)]
    simp
  have hlen : M.contentLength τ (((k + u.length : ℕ) : ℤ) - 1 + k) = u.length := by
    unfold TuringMachine.contentLength
    have hex : ∃ K : ℕ, ∀ j : ℕ, K ≤ j → τ (((k + u.length : ℕ) : ℤ) - 1 + k + 1 + j) = M.blank :=
      ⟨u.length, fun j hj => by rw [hcell, List.getElem?_eq_none (by omega)]; simp⟩
    rw [dite_eq_left hex]
    refine le_antisymm (Nat.find_min' hex fun j hj => by
      rw [hcell, List.getElem?_eq_none (by omega)]; simp) ?_
    by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec hex
    have := hspec (Nat.find hex) le_rfl
    rw [hcell, List.getElem?_eq_getElem hlt] at this
    exact hsym.ne_blank _ this
  rw [rightComplexity_le_crossingSequence_aux_rightContents, hlen]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [hcell, List.getElem?_eq_getElem (by simpa using h2)]
  simp

private lemma exists_duplication_lower_bound_rightComplexity_lower_bound
    [Finite Q] [Fintype Γ] [Encodable Γ]
    {M : TuringMachine Q Γ} {q₀ : Q} {sym : Bool → Γ}
    (hsym : M.IsInputEncoding sym) (hdup : M.Duplicates q₀ sym)
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℝ, ∀ n : ℕ, ∃ x : List Bool, x.length = n ∧
      ∀ t, M.HaltsAt (M.initial q₀ sym x) t →
        (n : ℝ) / 2 - c ≤ rightComplexity V M (M.run (M.initial q₀ sym x) t).tape ((n : ℤ) - 1 + (n
            / 2 : ℕ)) := by
  classical
  refine ⟨0, fun n => ?_⟩
  have hinj : Function.Injective (fun u : BitString => wordBits Γ (u.map sym)) :=
    fun a b h => List.map_injective_iff.mpr hsym.injective (wordBits_injective h)
  obtain ⟨u, hulen, hu⟩ :=
    exists_duplication_lower_bound_rightComplexity_lower_bound_aux_image V _ hinj (n - n / 2)
  refine ⟨List.replicate (n / 2) false ++ u, by simp [hulen]; omega, fun t ht => ?_⟩
  obtain ⟨t', ht', htape⟩ := hdup (List.replicate (n / 2) false ++ u)
  have htt : t = t' := by
    rcases lt_trichotomy t t' with h | h | h
    · exact absurd ht.1 (ht'.2 t h)
    · exact h
    · exact absurd ht'.1 (ht.2 t' h)
  subst htt
  have hn : n / 2 + u.length = n := by omega
  have hc := exists_duplication_lower_bound_rightComplexity_lower_bound_aux_content
    hsym (M.run (M.initial q₀ sym (List.replicate (n / 2) false ++ u)) t).tape (n / 2) u htape
  rw [hn] at hc
  unfold rightComplexity
  rw [hc]
  have hfin : plainK V (wordBits Γ (u.map sym)) ≠ ⊤ := by
    obtain ⟨c, hc'⟩ := plainK_le_length V hV
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc' _)
  have h1 : ((n - n / 2 : ℕ) : ENat) ≤ plainK V (wordBits Γ (u.map sym)) := hu
  have h2 : n - n / 2 ≤ (plainK V (wordBits Γ (u.map sym))).toNat := by
    have := ENat.toNat_le_toNat h1 hfin
    rwa [ENat.toNat_natCast] at this
  have h3 : (n : ℝ) / 2 ≤ ((n - n / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.div_le_self _ _)]
    have : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 * (n / 2) ≤ n)
    linarith
  have h4 : ((n - n / 2 : ℕ) : ℝ) ≤ (((plainK V (wordBits Γ (u.map sym))).toNat : ℕ) : ℝ) := by
    exact_mod_cast h2
  linarith

private lemma exists_duplication_lower_bound_apply_upper_bound
    [Fintype Q] [Fintype Γ] [Encodable Γ]
    {M : TuringMachine Q Γ} {q₀ : Q} {sym : Bool → Γ}
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℝ, ∀ x : List Bool, 1 < x.length → ∀ t : ℕ,
      rightComplexity V M (M.run (M.initial q₀ sym x) t).tape ((x.length : ℤ) - 1 + (x.length / 2 :
          ℕ)) ≤
        (t : ℝ) * Real.logb 2 (Fintype.card Q) / (2 * (x.length / 2 : ℕ)) + 4 * Real.logb 2 t + c :=
            by
  obtain ⟨c, hc⟩ := rightComplexity_le_two_mul V hV M
  refine ⟨c, fun x hx t => ?_⟩
  have hb : 0 < x.length / 2 := by omega
  have h := hc ((x.length : ℤ) - 1) (x.length / 2) hb (M.initial q₀ sym x)
    (by change (0 : ℤ) ≤ _; omega) (by
      intro i hi
      change M.inputTape sym x i = M.blank
      unfold TuringMachine.inputTape
      cases i with
      | ofNat n =>
        have hi' : (x.length : ℤ) - 1 < (n : ℤ) := hi
        have hn : x.length ≤ n := by omega
        simp [List.getElem?_eq_none hn]
      | negSucc n => rfl) t
  exact h

private lemma exists_duplication_lower_bound_log :
    ∃ K : ℝ, ∀ n t : ℕ, 1 ≤ t → t ≤ n^2 → 4 * Real.logb 2 t ≤ (n : ℝ) / 8 + K := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := 64 / Real.log 2 with ha_def
  have ha : 0 < a := by positivity
  refine ⟨(8 / Real.log 2) * Real.log a, fun n t ht1 htn => ?_⟩
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    simp at htn
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have h1 : Real.log (n / a) ≤ n / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hnpos.ne' ha.ne'] at h1
  have h2 : Real.log t ≤ 2 * Real.log n := by
    have : (t : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast htn
    calc Real.log t ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log htpos this
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have h8 : 0 ≤ 8 / Real.log 2 := by positivity
  have h3 : (8 / Real.log 2) * (n / a) = (n : ℝ) / 8 := by
    rw [ha_def]; field_simp; norm_num
  unfold Real.logb
  calc 4 * (Real.log t / Real.log 2) = (4 / Real.log 2) * Real.log t := by ring
    _ ≤ (4 / Real.log 2) * (2 * Real.log n) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (8 / Real.log 2) * Real.log n := by ring
    _ ≤ (8 / Real.log 2) * (Real.log a + n / a - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) h8
    _ ≤ (8 / Real.log 2) * (Real.log a + n / a) :=
        mul_le_mul_of_nonneg_left (by linarith) h8
    _ = (n : ℝ) / 8 + (8 / Real.log 2) * Real.log a := by rw [mul_add, h3]; ring

private lemma exists_duplication_lower_bound_half :
    ∀ n : ℕ, 2 ≤ n → (n : ℝ) / 3 ≤ ((n / 2 : ℕ) : ℝ) := by
  intro n hn
  rw [div_le_iff₀ (by norm_num)]
  exact_mod_cast (by omega : n ≤ (n / 2) * 3)

private lemma exists_duplication_lower_bound_ineq
    (c_lower c_upper cQ : ℝ) (hcQ : 0 ≤ cQ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∀ t : ℕ, 2 ≤ n → 1 ≤ t →
      (n : ℝ) / 2 - c_lower ≤ (t : ℝ) * cQ / (2 * ((n / 2 : ℕ) : ℝ)) + 4 * Real.logb 2 t + c_upper →
      ε * (n : ℝ) ^ 2 ≤ t := by
  obtain ⟨K, hK⟩ := exists_duplication_lower_bound_log
  set B : ℝ := 4 * (|c_lower| + |c_upper| + |K|) + 1 with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ |c_lower| + |c_upper| + |K| := by positivity
    rw [hB]; linarith
  have hBpos : 0 < B ^ 2 := by positivity
  have hQpos : 0 < 12 * cQ + 12 := by linarith
  refine ⟨min (1 / (12 * cQ + 12)) (1 / B ^ 2), lt_min (by positivity) (by positivity), ?_⟩
  intro n t hn ht hineq
  set ε : ℝ := min (1 / (12 * cQ + 12)) (1 / B ^ 2) with hε
  have hε1 : ε ≤ 1 / (12 * cQ + 12) := min_le_left _ _
  have hε2 : ε ≤ 1 / B ^ 2 := min_le_right _ _
  have hε1' : ε * (12 * cQ + 12) ≤ 1 := by
    rw [le_div_iff₀ hQpos] at hε1; exact hε1
  have hε2' : ε * B ^ 2 ≤ 1 := by
    rw [le_div_iff₀ hBpos] at hε2; exact hε2
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hεcQ : ε * cQ ≤ 1 / 12 := by nlinarith
  have hε_le : ε ≤ 1 := by nlinarith
  by_contra hcon
  push Not at hcon
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have htn : (t : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have htn' : t ≤ n ^ 2 := by exact_mod_cast htn
  have hlog := hK n t ht htn'
  have hh := exists_duplication_lower_bound_half n hn
  have hhpos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by linarith
  have hfrac : (t : ℝ) * cQ / (2 * ((n / 2 : ℕ) : ℝ)) ≤ (n : ℝ) / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (t : ℝ) * cQ ≤ ε * (n : ℝ) ^ 2 * cQ :=
      mul_le_mul_of_nonneg_right hcon.le hcQ
    have h2 : ε * (n : ℝ) ^ 2 * cQ ≤ (n : ℝ) ^ 2 / 12 := by
      have := mul_le_mul_of_nonneg_left hεcQ hn2
      nlinarith
    have h3 : (n : ℝ) * (n : ℝ) / 3 ≤ (n : ℝ) * ((n / 2 : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℝ) ≤ n)
      nlinarith
    nlinarith
  have hnB : (n : ℝ) ≤ B := by
    have h1 := le_abs_self c_lower
    have h2 := le_abs_self c_upper
    have h3 := le_abs_self K
    rw [hB]
    linarith
  have hnB2 : (n : ℝ) ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) hnB
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have : ε * (n : ℝ) ^ 2 ≤ 1 := by
    calc ε * (n : ℝ) ^ 2 ≤ ε * B ^ 2 := mul_le_mul_of_nonneg_left hnB2 hεpos.le
      _ ≤ 1 := hε2'
  linarith

private lemma exists_duplication_lower_bound_t_ge_1_aux_ne_nil
    {M : TuringMachine Q Γ} {q₀ : Q} {sym : Bool → Γ}
    (hsym : M.IsInputEncoding sym) (hdup : M.Duplicates q₀ sym)
    (x : List Bool) (hx : x ≠ []) (t : ℕ) (ht : M.HaltsAt (M.initial q₀ sym x) t) : 1 ≤ t := by
  by_contra h0
  have ht0 : t = 0 := by omega
  obtain ⟨t', ht', htape⟩ := hdup x
  have htt : t' = t := by
    rcases lt_trichotomy t' t with h | h | h
    · exact absurd ht'.1 (ht.2 t' h)
    · exact h
    · exact absurd ht.1 (ht'.2 t h)
  subst htt
  subst ht0
  obtain ⟨a, xs, rfl⟩ := List.exists_cons_of_ne_nil hx
  have h1 := htape (a :: xs).length
  have h2 : (M.run (M.initial q₀ sym (a :: xs)) 0).tape ((a :: xs).length : ℕ) = M.blank := by
    change (((a :: xs)[(a :: xs).length]?).map sym).getD M.blank = M.blank
    simp
  rw [h2] at h1
  have h3 : ((a :: xs) ++ (a :: xs))[(a :: xs).length]? = some a := by
    simp
  rw [h3] at h1
  exact hsym.ne_blank a (by simpa using h1.symm)

private lemma exists_duplication_lower_bound_t_ge_1
    {M : TuringMachine Q Γ} {q₀ : Q} {sym : Bool → Γ}
    (hsym : M.IsInputEncoding sym) (hdup : M.Duplicates q₀ sym) :
    ∀ n x t, x.length = n → 1 < n → M.HaltsAt (M.initial q₀ sym x) t → 1 ≤ t := by
  intro n x t hx hn ht
  have hne : x ≠ [] := by
    rintro rfl
    simp at hx
    omega
  exact exists_duplication_lower_bound_t_ge_1_aux_ne_nil hsym hdup x hne t ht

private lemma exists_duplication_lower_bound_n_le_1
    {M : TuringMachine Q Γ} {q₀ : Q} {sym : Bool → Γ}
    (hsym : M.IsInputEncoding sym) (hdup : M.Duplicates q₀ sym) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n ≤ 1 → ∃ x : List Bool, x.length = n ∧
      ∀ t, M.HaltsAt (M.initial q₀ sym x) t → c * (n : ℝ) ^ 2 ≤ t := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact ⟨[], rfl, fun t _ => by simp⟩
  · refine ⟨[false], rfl, fun t ht => ?_⟩
    obtain ⟨t', ht', htape⟩ := hdup [false]
    have htt : t = t' := by
      rcases lt_trichotomy t t' with h | h | h
      · exact (ht'.2 t h ht.1).elim
      · exact h
      · exact (ht.2 t' h ht'.1).elim
    subst htt
    by_contra hlt
    have h0 : t = 0 := by
      have : (t : ℝ) < 1 := by simpa using hlt
      have : t < 1 := by exact_mod_cast this
      omega
    subst h0
    have h1 := htape 1
    simp [TuringMachine.run, TuringMachine.initial, TuringMachine.inputTape] at h1
    exact hsym.ne_blank false h1.symm

/-- **SUV Theorem 153, p. 235.**  For a one-tape machine duplicating its input there is `ε > 0` such
that for every `n` some `n`-bit string requires at least `εn²` steps to duplicate.  The constant `ε`
depends on the machine, as in the book.  The output convention is `Duplicates`: `x x` starts at
cell `0` and is followed by blanks.  Thus this statement covers that fixed output convention;
it does not formalize an arbitrary shifted copy or an output with trailing work symbols. -/
theorem exists_duplication_lower_bound [Finite Q] [Finite Γ] [Encodable Γ]
    {M : TuringMachine Q Γ} {q₀ : Q} {sym : Bool → Γ}
    (hsym : M.IsInputEncoding sym) (hdup : M.Duplicates q₀ sym) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∃ x : List Bool, x.length = n ∧
      ∀ t, M.HaltsAt (M.initial q₀ sym x) t → ε * (n : ℝ) ^ 2 ≤ t := by
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite Γ
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨c_lower, hlower⟩ := exists_duplication_lower_bound_rightComplexity_lower_bound hsym
      hdup V hV
  obtain ⟨c_upper, hupper⟩ := exists_duplication_lower_bound_apply_upper_bound (M := M) (q₀ :=
      q₀) (sym := sym) V hV
  have hcQ : 0 ≤ Real.logb 2 (Fintype.card Q) := exists_duplication_lower_bound_card_Q_nonneg
  obtain ⟨ε1, hε1_pos, hε1_ineq⟩ := exists_duplication_lower_bound_ineq c_lower c_upper
      (Real.logb 2 (Fintype.card Q)) hcQ
  obtain ⟨ε2, hε2_pos, hε2_ineq⟩ := exists_duplication_lower_bound_n_le_1 hsym hdup
  use min ε1 ε2
  refine ⟨lt_min hε1_pos hε2_pos, fun n => ?_⟩
  by_cases hn : 1 < n
  · obtain ⟨x, hx_len, hx_time⟩ := hlower n
    use x
    refine ⟨hx_len, fun t ht => ?_⟩
    apply le_trans (mul_le_mul_of_nonneg_right (min_le_left ε1 ε2) (sq_nonneg (n : ℝ)))
    have ht_ge_1 := exists_duplication_lower_bound_t_ge_1 hsym hdup n x t hx_len hn ht
    have hn2 : 2 ≤ n := by omega
    apply hε1_ineq n t hn2 ht_ge_1
    have hl := hx_time t ht
    have hu := hupper x (hx_len.symm ▸ hn) t
    rw [hx_len] at hu
    linarith
  · have hn : n ≤ 1 := by omega
    obtain ⟨x, hx_len, hx_time⟩ := hε2_ineq n hn
    use x
    refine ⟨hx_len, fun t ht => ?_⟩
    apply le_trans (mul_le_mul_of_nonneg_right (min_le_right ε1 ε2) (sq_nonneg (n : ℝ)))
    apply hx_time t ht

end Kolmogorov.Applications
