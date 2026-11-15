/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.MisesChurch
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison

/-!
# Logarithmic Complexity

This file proves Theorem 173 of Shen, Uspensky and Vereshchagin, *Kolmogorov complexity and
algorithmic randomness*: there is a Mises-Church random binary sequence whose prefixes have
logarithmic plain complexity, `C(ω_0 … ω_{n-1}) = O(log n)`.

The sequence is built by the vertex-activation construction of Theorem 172 for the countable family
of all partial recursive selection rules, run with `Nat.size n` bits of advice (which rules are
total) for a prefix of length `n`.  The main declaration is
`exists_isMisesChurchRandom_plainK_log`.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-! ### Theorem 173: the construction of Theorem 172, run with advice

The explicit construction of the book (pp. 280-282) for a countable family of rules `R 0, R 1, …`.
A *vertex* is a bit string `x` (the answers of the first `|x|` rules); a vertex of height `h` may be
active at most `4 ^ h` times.  At step `j` (when `j` terms are constructed) the active vertex is the
shortest prefix `u.take h` of the pattern `u` of the rules `R 0, …, R (act j - 1)` that was active
fewer than `4 ^ h` times so far, and the new term is the parity of the number of earlier activations
of that vertex, so that every vertex produces `0101…`.  Only the first `act j` rules are consulted
at step `j`, where `act j = Nat.size j`, so a prefix of length `n` needs `Nat.size n` bits of advice
(which rules are total) when the family is the list of all partial recursive rules. -/

/-- The number of activations allowed for a vertex of height `h` (the book's `k_h`). -/
private def exists_isMisesChurchRandom_plainK_log_cap (h : ℕ) : ℕ := 4 ^ h

/-- The number of rules taken into account at step `j`; `j < 2 ^ act j`. -/
private def exists_isMisesChurchRandom_plainK_log_act (j : ℕ) : ℕ := Nat.size j

open Classical in
/-- The selection pattern of `p` under the first `m` rules. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_pat (R : ℕ → Set BitString)
    (p : BitString) (m : ℕ) : List Bool :=
  (List.range m).map fun i => decide (p ∈ R i)

/-- Height of the active vertex: the least `h ≤ |u|` such that `u.take h` was active fewer than
`k_h` times in the history `H`. -/
private def exists_isMisesChurchRandom_plainK_log_height (H : List (List Bool)) (u : List Bool) :
    ℕ :=
  (List.range (u.length + 1)).findIdx fun h =>
    decide (H.count (u.take h) < exists_isMisesChurchRandom_plainK_log_cap h)

/-- One step: the new term is the parity of the number of earlier activations of the active vertex,
and the active vertex is appended to the history. -/
private def exists_isMisesChurchRandom_plainK_log_stepFun (s : BitString × List (List Bool))
    (u : List Bool) : BitString × List (List Bool) :=
  (s.1 ++ [decide (s.2.count (u.take (exists_isMisesChurchRandom_plainK_log_height s.2 u)) % 2 =
      1)],
   s.2 ++ [u.take (exists_isMisesChurchRandom_plainK_log_height s.2 u)])

/-- The state (string constructed so far, history of active vertices) after `j` steps. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_state (R : ℕ → Set BitString) :
    ℕ → BitString × List (List Bool)
  | 0 => ([], [])
  | j + 1 => exists_isMisesChurchRandom_plainK_log_stepFun
      (exists_isMisesChurchRandom_plainK_log_state R j)
      (exists_isMisesChurchRandom_plainK_log_pat R
        (exists_isMisesChurchRandom_plainK_log_state R j).1
        (exists_isMisesChurchRandom_plainK_log_act j))

/-- The sequence constructed. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_seq (R : ℕ → Set BitString) :
    CantorSeq :=
  fun n => ((exists_isMisesChurchRandom_plainK_log_state R (n + 1)).1).getD n false

/-- The rule coded by `i` under the advice `b`: the set decided by the program `i` if the advice
says that `i` is total with Boolean outputs, and `∅` otherwise. -/
private def exists_isMisesChurchRandom_plainK_log_rule (b : ℕ → Bool) (i : ℕ) : Set BitString :=
  {x | b i = true ∧
    (Nat.Partrec.Code.ofNatCode i).eval (Encodable.encode x) = Part.some (Encodable.encode true)}

/-- The advice `b` is correct: `b i = 1` exactly when the program `i` is total with Boolean outputs.
-/
private def exists_isMisesChurchRandom_plainK_log_Good (b : ℕ → Bool) : Prop :=
  ∀ i, b i = true ↔ ∀ x : BitString, ∃ y : Bool,
    (Nat.Partrec.Code.ofNatCode i).eval (Encodable.encode x) = Part.some (Encodable.encode y)

/-- The active vertex at step `j`. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_vtx (R : ℕ → Set BitString)
    (j : ℕ) : List Bool :=
  (exists_isMisesChurchRandom_plainK_log_pat R (exists_isMisesChurchRandom_plainK_log_state R j).1
      (exists_isMisesChurchRandom_plainK_log_act j)).take
    (exists_isMisesChurchRandom_plainK_log_height
      (exists_isMisesChurchRandom_plainK_log_state R j).2
      (exists_isMisesChurchRandom_plainK_log_pat R
        (exists_isMisesChurchRandom_plainK_log_state R j).1
        (exists_isMisesChurchRandom_plainK_log_act j)))

/-- Step 1 of the proof of `exists_isMisesChurchRandom_plainK_log`: correct advice
exists (it is the classical characteristic function of the set of total Boolean programs). -/
private lemma exists_isMisesChurchRandom_plainK_log_good_exists :
    ∃ b : ℕ → Bool, exists_isMisesChurchRandom_plainK_log_Good b := by
  classical
  refine ⟨fun i => decide (∀ x : BitString, ∃ y : Bool,
    (Nat.Partrec.Code.ofNatCode i).eval (Encodable.encode x) = Part.some (Encodable.encode y)), ?_⟩
  intro i
  simp

/-- Step 2 of the proof of `exists_isMisesChurchRandom_plainK_log`: with correct advice,
every decidable set of strings is one of the rules `rule b i`. -/
private lemma exists_isMisesChurchRandom_plainK_log_rule_of_decidable
    {b : ℕ → Bool} (hb : exists_isMisesChurchRandom_plainK_log_Good b) {S : Set BitString}
    (hS : IsDecidableSet S) : ∃ i, exists_isMisesChurchRandom_plainK_log_rule b i = S := by
  obtain ⟨f, hf, hfS⟩ := hS
  unfold Computable Partrec at hf
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  have hev : ∀ x : BitString, c.eval (Encodable.encode x) = Part.some (Encodable.encode (f x)) := by
    intro x
    rw [hc]
    simp
  have hcode : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c :=
    Denumerable.ofNat_encode c
  have htot : b (Encodable.encode c) = true :=
    (hb _).2 (by rw [hcode]; intro x; exact ⟨f x, hev x⟩)
  refine ⟨Encodable.encode c, ?_⟩
  ext x
  simp only [exists_isMisesChurchRandom_plainK_log_rule, hcode, hev, htot, true_and,
    Set.mem_ofPred_eq, Part.some_inj]
  rw [← hfS x]
  constructor
  · intro h
    exact Encodable.encode_injective h
  · intro h
    rw [h]

/-- Step 3 aux: the number of ones among the uses of a vertex `x` is half the number of uses. -/
private lemma exists_isMisesChurchRandom_plainK_log_ones_fiber
    (v : ℕ → List Bool) (bit : ℕ → Bool)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (x : List Bool) (t : ℕ) :
    ((Finset.range t).filter fun j => v j = x ∧ bit j = true).card
      = ((Finset.range t).filter fun j => v j = x).card / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases hx : v t = x
    · subst hx
      have hb := hpar t
      have hnot : t ∉ (Finset.range t).filter fun j => v j = v t := by simp
      have hnot2 : t ∉ (Finset.range t).filter fun j => v j = v t ∧ bit j = true := by simp
      by_cases hbt : bit t = true
      · rw [ite_eq_left ⟨rfl, hbt⟩, ite_eq_left rfl, Finset.card_insert_of_notMem hnot2,
          Finset.card_insert_of_notMem hnot]
        rw [hbt] at hb
        have hmod : (((Finset.range t).filter fun j' => v j' = v t).card) % 2 = 1 := by
          simpa using hb.symm
        omega
      · rw [ite_eq_right (fun h => hbt h.2), ite_eq_left rfl, Finset.card_insert_of_notMem hnot]
        have hbf : bit t = false := by simpa using hbt
        rw [hbf] at hb
        have hmod : ¬ (((Finset.range t).filter fun j' => v j' = v t).card) % 2 = 1 := by
          simpa using hb.symm
        omega
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx h.1)]
      exact ih

/-- Step 3 aux: a vertex `x` is used at most `4 ^ |x|` times. -/
private lemma exists_isMisesChurchRandom_plainK_log_fiber_le
    (v : ℕ → List Bool)
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 4 ^ (v j).length)
    (x : List Bool) (t : ℕ) :
    ((Finset.range t).filter fun j => v j = x).card ≤ 4 ^ x.length := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hx : v t = x
    · subst hx
      have := hcap t
      rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [ite_eq_right hx]
      exact ih

/-- Step 3 aux: a finite set containing all bit strings of length at most `n`, with fewer than
`2 ^ (n + 1)` elements, all of length at most `n`. -/
private lemma exists_isMisesChurchRandom_plainK_log_lists (n : ℕ) :
    ∃ W : Finset (List Bool), W.card + 1 ≤ 2 ^ (n + 1) ∧ (∀ x : List Bool, x.length ≤ n → x ∈ W) ∧
      ∀ x ∈ W, x.length ≤ n := by
  induction n with
  | zero =>
    refine ⟨{[]}, by simp, ?_, ?_⟩
    · intro x hx
      have : x = [] := List.length_eq_zero_iff.mp (by omega)
      simp [this]
    · intro x hx
      simp at hx
      simp [hx]
  | succ n ih =>
    obtain ⟨W, hW, hmem, hlen⟩ := ih
    refine ⟨insert [] ((W.image (List.cons true)) ∪ (W.image (List.cons false))), ?_, ?_, ?_⟩
    · have h1 := Finset.card_insert_le ([] : List Bool)
        ((W.image (List.cons true)) ∪ (W.image (List.cons false)))
      have h2 := Finset.card_union_le (W.image (List.cons true)) (W.image (List.cons false))
      have h3 := Finset.card_image_le (s := W) (f := List.cons true)
      have h4 := Finset.card_image_le (s := W) (f := List.cons false)
      have h5 : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      rw [h5]
      omega
    · intro x hx
      cases x with
      | nil => simp
      | cons b y =>
        have hy : y.length ≤ n := by simpa using hx
        have hyW := hmem y hy
        cases b
        · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inr ⟨y, hyW, rfl⟩)
        · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inl ⟨y, hyW, rfl⟩)
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · simp
      · have := hlen y hy
        simp only [List.length_cons]
        omega
      · have := hlen y hy
        simp only [List.length_cons]
        omega

/-- Step 3 aux: the terms whose vertex has length at most `i` are few. -/
private lemma exists_isMisesChurchRandom_plainK_log_type1
    (v : ℕ → List Bool)
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 4 ^ (v j).length)
    (i t : ℕ) :
    ((Finset.range t).filter fun j => (v j).length ≤ i).card ≤ 2 ^ (i + 1) * 4 ^ i := by
  obtain ⟨W, hW, hmem, hlen⟩ := exists_isMisesChurchRandom_plainK_log_lists i
  have hmaps : ∀ j ∈ (Finset.range t).filter fun j => (v j).length ≤ i, v j ∈ W := by
    intro j hj
    exact hmem _ (Finset.mem_filter.mp hj).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ x ∈ W, (((Finset.range t).filter fun j => (v j).length ≤ i).filter fun j => v j = x).card
      ≤ ∑ _x ∈ W, 4 ^ i := by
        apply Finset.sum_le_sum
        intro x hx
        have hsub : (((Finset.range t).filter fun j => (v j).length ≤ i).filter fun j => v j = x)
            ⊆ (Finset.range t).filter fun j => v j = x := by
          intro j hj
          simp only [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1.1, hj.2⟩
        calc _ ≤ ((Finset.range t).filter fun j => v j = x).card := Finset.card_le_card hsub
          _ ≤ 4 ^ x.length :=
            exists_isMisesChurchRandom_plainK_log_fiber_le v hcap x t
          _ ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) (hlen x hx)
    _ = W.card * 4 ^ i := by simp
    _ ≤ 2 ^ (i + 1) * 4 ^ i := Nat.mul_le_mul_right _ (by omega)

/-- Step 3 aux: the numerical estimate. -/
private lemma exists_isMisesChurchRandom_plainK_log_numeric (ε : ℝ) (hε : 0 < ε) (C : ℕ) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → (C : ℝ) + 2 ^ (m + 2) ≤ 2 * ε * 4 ^ m := by
  refine ⟨⌈((C : ℝ) + 4) / (2 * ε)⌉₊, fun m hm => ?_⟩
  have h1 : ((C : ℝ) + 4) / (2 * ε) ≤ (m : ℝ) := by
    calc ((C : ℝ) + 4) / (2 * ε) ≤ (⌈((C : ℝ) + 4) / (2 * ε)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have h3 : (C : ℝ) + 4 ≤ 2 * ε * 2 ^ m := by
    have := le_trans h1 h2
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have ha : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have e1 : (2 : ℝ) ^ (m + 2) = 4 * 2 ^ m := by ring
  have e2 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 ^ m),
    mul_nonneg (sub_nonneg.2 ha) hC]

/-- Step 3 aux: a vertex of length `≥ i + 2` that selects forces many selected terms. -/
private lemma exists_isMisesChurchRandom_plainK_log_parent
    (v : ℕ → List Bool) (sel : ℕ → Bool) (i : ℕ)
    (htired : ∀ j l, l < (v j).length →
      4 ^ l ≤ ((Finset.range j).filter fun j' => v j' = (v j).take l).card)
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true))
    (t j0 : ℕ) (hj0 : j0 < t) (hlen : i + 2 ≤ (v j0).length) (hx : (v j0)[i]? = some true) :
    4 ^ ((v j0).length - 1) ≤ ((Finset.range t).filter fun j => sel j = true).card := by
  have h1 := htired j0 ((v j0).length - 1) (by omega)
  refine le_trans h1 (Finset.card_le_card ?_)
  intro j' hj'
  simp only [Finset.mem_filter, Finset.mem_range] at hj' ⊢
  obtain ⟨hj'0, hv⟩ := hj'
  have hlen' : (v j').length = (v j0).length - 1 := by
    rw [hv]
    simp only [List.length_take]
    omega
  have hil : i < (v j').length := by omega
  refine ⟨by omega, (hsel j' hil).2 ?_⟩
  rw [hv, List.getElem?_take]
  rw [ite_eq_left (by omega)]
  exact hx

/-- Step 3 aux: the terms whose vertex is longer than `i` are balanced up to the number of used
vertices. -/
private lemma exists_isMisesChurchRandom_plainK_log_type2
    (v : ℕ → List Bool) (bit sel : ℕ → Bool) (i : ℕ)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true))
    (t : ℕ) (Y : Finset (List Bool))
    (hY : Y = ((Finset.range t).image v).filter fun x => i < x.length ∧ x[i]? = some true) :
    2 * ((Finset.range t).filter fun j => (sel j = true ∧ bit j = true) ∧ i < (v j).length).card
      ≤ ((Finset.range t).filter fun j => sel j = true ∧ i < (v j).length).card ∧
    ((Finset.range t).filter fun j => sel j = true ∧ i < (v j).length).card
      ≤ 2 * ((Finset.range t).filter fun j =>
          (sel j = true ∧ bit j = true) ∧ i < (v j).length).card + Y.card := by
  have hmemY : ∀ j, j < t → (v j ∈ Y ↔ i < (v j).length ∧ (v j)[i]? = some true) := by
    intro j hj
    rw [hY, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨⟨j, Finset.mem_range.mpr hj, rfl⟩, h⟩
  have hS2 : ((Finset.range t).filter fun j => sel j = true ∧ i < (v j).length)
      = (Finset.range t).filter fun j => v j ∈ Y := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hs, hl⟩
      exact ⟨hj, (hmemY j hj).2 ⟨hl, (hsel j hl).1 hs⟩⟩
    · rintro ⟨hj, hy⟩
      obtain ⟨hl, hx⟩ := (hmemY j hj).1 hy
      exact ⟨hj, (hsel j hl).2 hx, hl⟩
  have hO2 : ((Finset.range t).filter fun j => (sel j = true ∧ bit j = true) ∧ i < (v j).length)
      = (Finset.range t).filter fun j => v j ∈ Y ∧ bit j = true := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, ⟨hs, hb⟩, hl⟩
      exact ⟨hj, (hmemY j hj).2 ⟨hl, (hsel j hl).1 hs⟩, hb⟩
    · rintro ⟨hj, hy, hb⟩
      obtain ⟨hl, hx⟩ := (hmemY j hj).1 hy
      exact ⟨hj, ⟨(hsel j hl).2 hx, hb⟩, hl⟩
  rw [hS2, hO2]
  have hmaps1 : ∀ j ∈ (Finset.range t).filter (fun j => v j ∈ Y), v j ∈ Y :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hmaps2 : ∀ j ∈ (Finset.range t).filter (fun j => v j ∈ Y ∧ bit j = true), v j ∈ Y :=
    fun j hj => (Finset.mem_filter.mp hj).2.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps1, Finset.card_eq_sum_card_fiberwise hmaps2]
  have e1 : ∀ x ∈ Y, (((Finset.range t).filter fun j => v j ∈ Y).filter fun j => v j = x).card
      = ((Finset.range t).filter fun j => v j = x).card := by
    intro x hx
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, _⟩, h⟩
      exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩
      exact ⟨⟨hj, by rw [h]; exact hx⟩, h⟩
  have e2 : ∀ x ∈ Y,
      (((Finset.range t).filter fun j => v j ∈ Y ∧ bit j = true).filter fun j => v j = x).card
      = ((Finset.range t).filter fun j => v j = x).card / 2 := by
    intro x hx
    rw [← exists_isMisesChurchRandom_plainK_log_ones_fiber v bit hpar x t]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hj, _, hb⟩, h⟩
      exact ⟨hj, h, hb⟩
    · rintro ⟨hj, h, hb⟩
      exact ⟨⟨hj, by rw [h]; exact hx, hb⟩, h⟩
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    omega
  · calc ∑ x ∈ Y, ((Finset.range t).filter fun j => v j = x).card
        ≤ ∑ x ∈ Y, (2 * (((Finset.range t).filter fun j => v j = x).card / 2) + 1) := by
          apply Finset.sum_le_sum
          intro x _
          omega
      _ = 2 * (∑ x ∈ Y, ((Finset.range t).filter fun j => v j = x).card / 2) + Y.card := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp

/-- Step 3 aux: the natural-number form of the balance estimate. -/
private lemma exists_isMisesChurchRandom_plainK_log_nat_bounds
    (v : ℕ → List Bool) (bit sel : ℕ → Bool) (i : ℕ)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 4 ^ (v j).length)
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true))
    (t : ℕ) (Y : Finset (List Bool))
    (hY : Y = ((Finset.range t).image v).filter fun x => i < x.length ∧ x[i]? = some true) :
    2 * ((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card
        ≤ ((Finset.range t).filter fun j => sel j = true).card + 2 ^ (i + 1) * 4 ^ i ∧
      ((Finset.range t).filter fun j => sel j = true).card
        ≤ 2 * ((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card
          + 2 ^ (i + 1) * 4 ^ i + Y.card := by
  obtain ⟨hT2a, hT2b⟩ :=
    exists_isMisesChurchRandom_plainK_log_type2 v bit sel i hpar hsel t Y hY
  have hT1 := exists_isMisesChurchRandom_plainK_log_type1 v hcap i t
  have hS := Finset.card_filter_add_card_filter_not
    (s := (Finset.range t).filter fun j => sel j = true) (fun j => i < (v j).length)
  have hO := Finset.card_filter_add_card_filter_not
    (s := (Finset.range t).filter fun j => sel j = true ∧ bit j = true)
    (fun j => i < (v j).length)
  simp only [Finset.filter_filter] at hS hO
  have hS1 : ((Finset.range t).filter fun a => sel a = true ∧ ¬ i < (v a).length).card
      ≤ 2 ^ (i + 1) * 4 ^ i := by
    refine le_trans (Finset.card_le_card ?_) hT1
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, not_lt.mp hj.2.2⟩
  have hO1 : ((Finset.range t).filter fun a =>
        (sel a = true ∧ bit a = true) ∧ ¬ i < (v a).length).card
      ≤ ((Finset.range t).filter fun a => sel a = true ∧ ¬ i < (v a).length).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.1.1, hj.2.2⟩
  generalize 2 ^ (i + 1) * 4 ^ i = C at *
  omega

/-- Step 3 of the proof of `exists_isMisesChurchRandom_plainK_log`: the counting core of
the balance argument of the book (p. 281).  The terms `j = 0, 1, 2, …` are labelled by *vertices*
`v j` (bit strings) and carry bits `bit j`; `sel j` says whether the rule number `i` selects term
`j`.  Assume: the bit of term `j` is the parity of the number of earlier terms with the same vertex
(`hpar`; every vertex yields `0101…`); a vertex `x` labels at most `4 ^ |x|` terms (`hcap`); a
vertex `x` labels a term only after each of its proper prefixes `y` has labelled `4 ^ |y|` terms
(`htired`); and for `i < |v j|` the term `j` is selected iff the `i`-th letter of `v j` is `1`
(`hsel`).  Then the selected subsequence is asymptotically balanced: for every `ε > 0` there is `L`
such that whenever at least `L` of the first `t` terms are selected, the number of selected ones
differs from half the number of selected terms by at most `ε` times that number. -/
private lemma exists_isMisesChurchRandom_plainK_log_abs
    (v : ℕ → List Bool) (bit sel : ℕ → Bool) (i : ℕ)
    (hpar : ∀ j, bit j = decide ((((Finset.range j).filter fun j' => v j' = v j).card) % 2 = 1))
    (hcap : ∀ j, ((Finset.range j).filter fun j' => v j' = v j).card < 4 ^ (v j).length)
    (htired : ∀ j l, l < (v j).length →
      4 ^ l ≤ ((Finset.range j).filter fun j' => v j' = (v j).take l).card)
    (hsel : ∀ j, i < (v j).length → (sel j = true ↔ (v j)[i]? = some true)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ t : ℕ,
      L ≤ ((Finset.range t).filter fun j => sel j = true).card →
      |(((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card : ℝ)
          - (((Finset.range t).filter fun j => sel j = true).card : ℝ) / 2|
        ≤ ε * (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by
  intro ε hε
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ (i + 1) * 4 ^ i := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ := exists_isMisesChurchRandom_plainK_log_numeric ε hε C
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = max K' (i + 1) := ⟨_, rfl⟩
  have hK1 : K' ≤ K := by rw [hK]; exact le_max_left _ _
  have hK2 : i + 1 ≤ K := by rw [hK]; exact le_max_right _ _
  refine ⟨⌈((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)⌉₊, fun t ht => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Finset (List Bool), Y = ((Finset.range t).image v).filter
      fun x => i < x.length ∧ x[i]? = some true := ⟨_, rfl⟩
  obtain ⟨ha, hb⟩ := exists_isMisesChurchRandom_plainK_log_nat_bounds v bit sel i hpar hcap
    hsel t Y hY
  rw [← hCdef] at ha hb
  have hclaim : (C : ℝ) + (Y.card : ℝ)
      ≤ 2 * ε * (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by
    by_cases hcase : ∀ y ∈ Y, y.length ≤ K
    · obtain ⟨W, hW, hmem, hlen⟩ := exists_isMisesChurchRandom_plainK_log_lists K
      have hYW : Y ⊆ W := fun y hy => hmem y (hcase y hy)
      have hYc : Y.card + 1 ≤ 2 ^ (K + 1) :=
        le_trans (Nat.succ_le_succ (Finset.card_le_card hYW)) hW
      have hYc' : Y.card ≤ 2 ^ (K + 1) := by omega
      have hYr : (Y.card : ℝ) ≤ 2 ^ (K + 1) := by exact_mod_cast hYc'
      have hL : ((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)
          ≤ (⌈((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)⌉₊ : ℝ) := Nat.le_ceil _
      have hLS : (⌈((C : ℝ) + 2 ^ (K + 1)) / (2 * ε)⌉₊ : ℝ)
          ≤ (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by exact_mod_cast ht
      have h3 := le_trans hL hLS
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
    · have hcase' : ∃ y ∈ Y, K < y.length := by
        by_contra hcon
        exact hcase fun y hy => not_lt.mp fun hlt => hcon ⟨y, hy, hlt⟩
      obtain ⟨y0, hy0, hy0len⟩ := hcase'
      obtain ⟨y, hyY, hymax⟩ := Finset.exists_max_image Y List.length ⟨y0, hy0⟩
      have hMK : K < y.length := lt_of_lt_of_le hy0len (hymax y0 hy0)
      have hyY' := hyY
      rw [hY, Finset.mem_filter, Finset.mem_image] at hyY'
      obtain ⟨⟨j0, hj0, hvj0⟩, hiy, hxy⟩ := hyY'
      rw [Finset.mem_range] at hj0
      rw [← hvj0] at hMK hxy hiy
      have hpar' := exists_isMisesChurchRandom_plainK_log_parent v sel i htired hsel t j0 hj0
        (by omega) hxy
      obtain ⟨W, hW, hmem, hlen⟩ :=
        exists_isMisesChurchRandom_plainK_log_lists (v j0).length
      have hYW : Y ⊆ W := fun z hz => hmem z (by rw [hvj0]; exact hymax z hz)
      have hYc : Y.card + 1 ≤ 2 ^ ((v j0).length + 1) :=
        le_trans (Nat.succ_le_succ (Finset.card_le_card hYW)) hW
      obtain ⟨m, hm⟩ : ∃ m, (v j0).length = m + 1 := ⟨(v j0).length - 1, by omega⟩
      have hnum := hK' m (by omega)
      rw [hm] at hYc hpar'
      rw [Nat.add_sub_cancel] at hpar'
      have hYc' : Y.card ≤ 2 ^ (m + 1 + 1) := by omega
      have hYr : (Y.card : ℝ) ≤ 2 ^ (m + 2) := by exact_mod_cast hYc'
      have h4 : (4 : ℝ) ^ m
          ≤ (((Finset.range t).filter fun j => sel j = true).card : ℝ) := by exact_mod_cast hpar'
      have hε2 : (0 : ℝ) ≤ 2 * ε := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 hε2]
  have ha' : (2 * ((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card : ℝ)
      ≤ (((Finset.range t).filter fun j => sel j = true).card : ℝ) + C := by exact_mod_cast ha
  have hb' : (((Finset.range t).filter fun j => sel j = true).card : ℝ)
      ≤ 2 * (((Finset.range t).filter fun j => sel j = true ∧ bit j = true).card : ℝ) + C
        + Y.card := by exact_mod_cast hb
  have hY0 : (0 : ℝ) ≤ (Y.card : ℝ) := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · linarith
  · linarith

open Classical in
/-- One more step of the chain of selected prefixes: the new term is selected iff the string
read so far lies in `R`. -/
private lemma exists_isMisesChurchRandom_plainK_log_selectChain_succ (R : Set BitString)
    (w : CantorSeq) (t : ℕ) :
    selectChain R w (t + 1)
      = selectChain R w t ++ (if cantorPrefix w t ∈ R then [w t] else []) := by
  unfold selectChain
  rw [cantorPrefix_succ, selectedBits_append_singleton]

/-- The chain of selected prefixes starts with the empty string. -/
private lemma exists_isMisesChurchRandom_plainK_log_selectChain_zero (R : Set BitString)
    (w : CantorSeq) : selectChain R w 0 = [] := by
  simp [selectChain, selectedBits, selectedAux, cantorPrefix]

/-- A stream prefix set of unbounded length determines an infinite sequence of which every member
is an initial segment. -/
private lemma exists_isMisesChurchRandom_plainK_log_ofPrefixSet_infinite {T : Set BitString}
    (hT : IsStreamPrefixSet T) (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) :
    ∃ u : CantorSeq, BitStream.ofPrefixSet T hT = .infinite u ∧ ∀ x ∈ T, IsCantorPrefix x u := by
  classical
  refine ⟨fun i => (Classical.choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (Classical.choose_spec (exists_mem_length_gt h_unbdd i)).2⟩, ?_,
    isCantorPrefix_of_mem hT h_unbdd⟩
  unfold BitStream.ofPrefixSet
  rw [dite_eq_right h_unbdd]

open Classical in
/-- Step 5 of the proof of `exists_isMisesChurchRandom_plainK_log`: the length of the
selected prefix, and the number of ones in it, are cardinalities of sets of positions. -/
private lemma exists_isMisesChurchRandom_plainK_log_selectChain_counts (R : Set BitString)
    (w : CantorSeq) (t : ℕ) :
    (selectChain R w t).length
        = ((Finset.range t).filter fun j => decide (cantorPrefix w j ∈ R) = true).card ∧
      (selectChain R w t).count true
        = ((Finset.range t).filter fun j =>
            decide (cantorPrefix w j ∈ R) = true ∧ w j = true).card := by
  induction t with
  | zero =>
    rw [exists_isMisesChurchRandom_plainK_log_selectChain_zero]
    simp
  | succ t ih =>
    rw [exists_isMisesChurchRandom_plainK_log_selectChain_succ, Finset.range_add_one,
      Finset.filter_insert, Finset.filter_insert]
    by_cases hR : cantorPrefix w t ∈ R
    · cases hw : w t <;> simp [hR, ih.1, ih.2]
    · simp [hR, ih.1, ih.2]

/-- Step 4 of the proof of `exists_isMisesChurchRandom_plainK_log`: if the numbers of
ones in the selected prefixes are asymptotically half their lengths, uniformly in `t`, then the
selected stream is finite or has limit frequency `1/2`. -/
private lemma exists_isMisesChurchRandom_plainK_log_chain_freq (R : Set BitString)
    (w : CantorSeq)
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ t : ℕ, L ≤ (selectChain R w t).length →
      |((selectChain R w t).count true : ℝ) - ((selectChain R w t).length : ℝ) / 2|
        ≤ ε * ((selectChain R w t).length : ℝ)) :
    FiniteOrFreq (1 / 2) (selectStream R w) := by
  classical
  have hT : IsStreamPrefixSet (chainPrefixSet (selectChain R w)) :=
    isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)
  have hsel : selectStream R w
      = BitStream.ofPrefixSet (chainPrefixSet (selectChain R w)) hT := rfl
  rw [hsel]
  by_cases hb : ∃ M, ∀ x ∈ chainPrefixSet (selectChain R w), x.length ≤ M
  · unfold BitStream.ofPrefixSet
    rw [dite_eq_left hb]
    trivial
  · obtain ⟨u, hu, hpre⟩ :=
      exists_isMisesChurchRandom_plainK_log_ofPrefixSet_infinite hT hb
    rw [hu]
    change Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 (1 / 2))
    -- the lengths of the chain are unbounded
    have hunb : ∀ M : ℕ, ∃ t, M < (selectChain R w t).length := by
      intro M
      obtain ⟨x, ⟨t, hxt⟩, hxM⟩ := exists_mem_length_gt hb M
      exact ⟨t, lt_of_lt_of_le hxM hxt.length_le⟩
    -- ... and grow by at most one at a time, so every length is attained
    have hstep : ∀ t, (selectChain R w (t + 1)).length ≤ (selectChain R w t).length + 1 := by
      intro t
      rw [exists_isMisesChurchRandom_plainK_log_selectChain_succ]
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
        rw [exists_isMisesChurchRandom_plainK_log_selectChain_zero] at ht₀ ⊢
        simp at ht₀ ⊢
        omega
      · refine ⟨t₁ + 1, ?_⟩
        have h1 := hmin t₁ (Nat.lt_succ_self t₁)
        have h2 := hstep t₁
        omega
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L, hL⟩ := h (ε / 2) (by positivity)
    refine ⟨max L 1, fun n hn => ?_⟩
    obtain ⟨t, ht⟩ := hattain n
    have hcp : cantorPrefix u n = selectChain R w t := by
      have hmem : selectChain R w t ∈ chainPrefixSet (selectChain R w) := ⟨t, List.prefix_rfl⟩
      have := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (hpre _ hmem)
      rw [ht] at this
      exact this
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hnL : L ≤ (selectChain R w t).length := by
      rw [ht]
      exact le_trans (le_max_left _ _) hn
    have hbound := hL t hnL
    rw [ht] at hbound
    have hfreq : (freqOne u n : ℝ) = ((selectChain R w t).count true : ℝ) / n := by
      unfold freqOne
      rw [hcp]
      push_cast
      rfl
    rw [Real.dist_eq, hfreq]
    have halg : ((selectChain R w t).count true : ℝ) / n - 1 / 2
        = (((selectChain R w t).count true : ℝ) - (n : ℝ) / 2) / n := by
      field_simp
    rw [halg, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
    have := mul_pos hε hnpos
    linarith

/-- Counting the occurrences of a vertex in the history of a mapped range. -/
private lemma exists_isMisesChurchRandom_plainK_log_count_map (f : ℕ → List Bool)
    (x : List Bool) (j : ℕ) :
    ((List.range j).map f).count x = ((Finset.range j).filter fun j' => f j' = x).card := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : f j = x
    · simp [h]
    · simp [h]

/-- The unfolding of the state after `j + 1` steps. -/
private lemma exists_isMisesChurchRandom_plainK_log_state_succ (R : ℕ → Set BitString)
    (j : ℕ) :
    exists_isMisesChurchRandom_plainK_log_state R (j + 1) =
      ((exists_isMisesChurchRandom_plainK_log_state R j).1 ++
          [decide ((exists_isMisesChurchRandom_plainK_log_state R j).2.count
              (exists_isMisesChurchRandom_plainK_log_vtx R j) % 2 = 1)],
        (exists_isMisesChurchRandom_plainK_log_state R j).2 ++
          [exists_isMisesChurchRandom_plainK_log_vtx R j]) := rfl

/-- The string and the history after `j` steps have length `j`. -/
private lemma exists_isMisesChurchRandom_plainK_log_length (R : ℕ → Set BitString)
    (j : ℕ) :
    (exists_isMisesChurchRandom_plainK_log_state R j).1.length = j ∧
      (exists_isMisesChurchRandom_plainK_log_state R j).2.length = j := by
  induction j with
  | zero => simp [exists_isMisesChurchRandom_plainK_log_state]
  | succ j ih =>
    rw [exists_isMisesChurchRandom_plainK_log_state_succ]
    simp [ih.1, ih.2]

/-- The history after `j` steps is the list of the first `j` active vertices. -/
private lemma exists_isMisesChurchRandom_plainK_log_history (R : ℕ → Set BitString)
    (j : ℕ) :
    (exists_isMisesChurchRandom_plainK_log_state R j).2 =
      (List.range j).map (exists_isMisesChurchRandom_plainK_log_vtx R) := by
  induction j with
  | zero => simp [exists_isMisesChurchRandom_plainK_log_state]
  | succ j ih =>
    rw [exists_isMisesChurchRandom_plainK_log_state_succ, List.range_succ,
      List.map_append]
    simp only [ih]
    simp

private lemma exists_isMisesChurchRandom_plainK_log_getD_append (p : List Bool) (b : Bool)
    (n : ℕ) (h : p.length = n) : (p ++ [b]).getD n false = b := by
  subst h
  simp

/-- The `j`-th term is the parity of the number of earlier activations of the active vertex. -/
private lemma exists_isMisesChurchRandom_plainK_log_seq_eq (R : ℕ → Set BitString)
    (j : ℕ) :
    exists_isMisesChurchRandom_plainK_log_seq R j =
      decide ((exists_isMisesChurchRandom_plainK_log_state R j).2.count
        (exists_isMisesChurchRandom_plainK_log_vtx R j) % 2 = 1) := by
  unfold exists_isMisesChurchRandom_plainK_log_seq
  rw [exists_isMisesChurchRandom_plainK_log_state_succ]
  exact exists_isMisesChurchRandom_plainK_log_getD_append _ _ _
    (exists_isMisesChurchRandom_plainK_log_length R j).1

/-- The prefixes of the constructed sequence are the strings of the state. -/
private lemma exists_isMisesChurchRandom_plainK_log_cantorPrefix (R : ℕ → Set BitString)
    (j : ℕ) :
    cantorPrefix (exists_isMisesChurchRandom_plainK_log_seq R) j =
      (exists_isMisesChurchRandom_plainK_log_state R j).1 := by
  induction j with
  | zero => simp [cantorPrefix, exists_isMisesChurchRandom_plainK_log_state]
  | succ j ih =>
    rw [cantorPrefix_succ, ih, exists_isMisesChurchRandom_plainK_log_state_succ,
      exists_isMisesChurchRandom_plainK_log_seq_eq]

/-- The specification of the height of the active vertex when a vertex of full height is
available. -/
private lemma exists_isMisesChurchRandom_plainK_log_height_spec (H : List (List Bool))
    (u : List Bool) (hex : H.count u < 4 ^ u.length) :
    exists_isMisesChurchRandom_plainK_log_height H u ≤ u.length ∧
      H.count (u.take (exists_isMisesChurchRandom_plainK_log_height H u))
        < 4 ^ exists_isMisesChurchRandom_plainK_log_height H u ∧
      ∀ l, l < exists_isMisesChurchRandom_plainK_log_height H u →
        4 ^ l ≤ H.count (u.take l) := by
  have hmem : u.length ∈ List.range (u.length + 1) := List.mem_range.2 (Nat.lt_succ_self _)
  have hp : (fun h => decide (H.count (u.take h) < exists_isMisesChurchRandom_plainK_log_cap h))
      u.length = true := by
    simp [exists_isMisesChurchRandom_plainK_log_cap, hex]
  have hlt := List.findIdx_lt_length_of_exists
    (p := fun h => decide (H.count (u.take h) < exists_isMisesChurchRandom_plainK_log_cap h))
    (xs := List.range (u.length + 1)) ⟨u.length, hmem, hp⟩
  have hle : exists_isMisesChurchRandom_plainK_log_height H u ≤ u.length := by
    have : exists_isMisesChurchRandom_plainK_log_height H u < u.length + 1 := by
      simpa [exists_isMisesChurchRandom_plainK_log_height] using hlt
    omega
  refine ⟨hle, ?_, ?_⟩
  · have := List.findIdx_getElem
      (p := fun h => decide (H.count (u.take h) < exists_isMisesChurchRandom_plainK_log_cap h))
      (xs := List.range (u.length + 1)) (w := hlt)
    simpa [List.getElem_range, exists_isMisesChurchRandom_plainK_log_cap,
      exists_isMisesChurchRandom_plainK_log_height] using this
  · intro l hl
    have := List.not_of_lt_findIdx
      (p := fun h => decide (H.count (u.take h) < exists_isMisesChurchRandom_plainK_log_cap h))
      (xs := List.range (u.length + 1)) (i := l) hl
    simpa [List.getElem_range, exists_isMisesChurchRandom_plainK_log_cap] using this

open Classical in
/-- The properties of the active vertex at step `j`: height, capacity, tiredness of its prefixes
and its letters. -/
private lemma exists_isMisesChurchRandom_plainK_log_vtx_spec (R : ℕ → Set BitString)
    (j : ℕ) :
    ∃ h : ℕ, (exists_isMisesChurchRandom_plainK_log_vtx R j).length = h ∧
      (exists_isMisesChurchRandom_plainK_log_state R j).2.count
          (exists_isMisesChurchRandom_plainK_log_vtx R j) < 4 ^ h ∧
      (∀ l, l < h → 4 ^ l ≤ (exists_isMisesChurchRandom_plainK_log_state R j).2.count
          ((exists_isMisesChurchRandom_plainK_log_vtx R j).take l)) ∧
      (∀ i, i < h → (exists_isMisesChurchRandom_plainK_log_vtx R j)[i]? =
          some (decide ((exists_isMisesChurchRandom_plainK_log_state R j).1 ∈ R i))) := by
  obtain ⟨hp, hH⟩ := exists_isMisesChurchRandom_plainK_log_length R j
  obtain ⟨u, hu_def⟩ : ∃ u, u = exists_isMisesChurchRandom_plainK_log_pat R
      (exists_isMisesChurchRandom_plainK_log_state R j).1
      (exists_isMisesChurchRandom_plainK_log_act j) := ⟨_, rfl⟩
  have hvtx : exists_isMisesChurchRandom_plainK_log_vtx R j = u.take
      (exists_isMisesChurchRandom_plainK_log_height
        (exists_isMisesChurchRandom_plainK_log_state R j).2 u) := by
    rw [hu_def]
    rfl
  have hulen : u.length = Nat.size j := by
    rw [hu_def]
    simp [exists_isMisesChurchRandom_plainK_log_pat, exists_isMisesChurchRandom_plainK_log_act]
  have hex : (exists_isMisesChurchRandom_plainK_log_state R j).2.count u < 4 ^ u.length := by
    calc (exists_isMisesChurchRandom_plainK_log_state R j).2.count u
        ≤ (exists_isMisesChurchRandom_plainK_log_state R j).2.length := List.count_le_length
      _ = j := hH
      _ < 2 ^ Nat.size j := Nat.lt_size_self j
      _ ≤ 4 ^ Nat.size j := Nat.pow_le_pow_left (by norm_num) _
      _ = 4 ^ u.length := by rw [hulen]
  obtain ⟨hle, hlt, hmin⟩ := exists_isMisesChurchRandom_plainK_log_height_spec
    (exists_isMisesChurchRandom_plainK_log_state R j).2 u hex
  refine ⟨exists_isMisesChurchRandom_plainK_log_height
    (exists_isMisesChurchRandom_plainK_log_state R j).2 u, ?_, ?_, ?_, ?_⟩
  · rw [hvtx, List.length_take, min_eq_left hle]
  · rw [hvtx]
    exact hlt
  · intro l hl
    rw [hvtx, List.take_take, min_eq_left hl.le]
    exact hmin l hl
  · intro i hi
    rw [hvtx, List.getElem?_take_of_lt hi]
    have hi' : i < exists_isMisesChurchRandom_plainK_log_act j := by
      unfold exists_isMisesChurchRandom_plainK_log_act
      omega
    rw [hu_def]
    simp [exists_isMisesChurchRandom_plainK_log_pat, hi']

open Classical in
/-- Step 6 of the proof of `exists_isMisesChurchRandom_plainK_log`: the construction has
the four properties used in step 3, with `v = vtx R`, `bit = seq R` and `sel j = [prefix_j ∈ R i]`.
-/
private lemma exists_isMisesChurchRandom_plainK_log_interface (R : ℕ → Set BitString)
    (i : ℕ) :
    (∀ j, exists_isMisesChurchRandom_plainK_log_seq R j = decide
        ((((Finset.range j).filter fun j' =>
          exists_isMisesChurchRandom_plainK_log_vtx R j' =
            exists_isMisesChurchRandom_plainK_log_vtx R j).card) % 2 = 1)) ∧
    (∀ j, ((Finset.range j).filter fun j' =>
          exists_isMisesChurchRandom_plainK_log_vtx R j' =
            exists_isMisesChurchRandom_plainK_log_vtx R j).card
        < 4 ^ (exists_isMisesChurchRandom_plainK_log_vtx R j).length) ∧
    (∀ j l, l < (exists_isMisesChurchRandom_plainK_log_vtx R j).length →
      4 ^ l ≤ ((Finset.range j).filter fun j' =>
          exists_isMisesChurchRandom_plainK_log_vtx R j' =
            (exists_isMisesChurchRandom_plainK_log_vtx R j).take l).card) ∧
    (∀ j, i < (exists_isMisesChurchRandom_plainK_log_vtx R j).length →
      (decide (cantorPrefix (exists_isMisesChurchRandom_plainK_log_seq R) j ∈ R i) = true
        ↔ (exists_isMisesChurchRandom_plainK_log_vtx R j)[i]? = some true)) := by
  have hcnt : ∀ (j : ℕ) (x : List Bool), ((Finset.range j).filter fun j' =>
      exists_isMisesChurchRandom_plainK_log_vtx R j' = x).card
        = (exists_isMisesChurchRandom_plainK_log_state R j).2.count x := by
    intro j x
    rw [exists_isMisesChurchRandom_plainK_log_history R j,
      exists_isMisesChurchRandom_plainK_log_count_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rw [hcnt, exists_isMisesChurchRandom_plainK_log_seq_eq]
  · intro j
    rw [hcnt]
    obtain ⟨h, hlen, hc, -, -⟩ := exists_isMisesChurchRandom_plainK_log_vtx_spec R j
    rw [hlen]
    exact hc
  · intro j l hl
    rw [hcnt]
    obtain ⟨h, hlen, -, ht, -⟩ := exists_isMisesChurchRandom_plainK_log_vtx_spec R j
    rw [hlen] at hl
    exact ht l hl
  · intro j hij
    obtain ⟨h, hlen, -, -, hs⟩ := exists_isMisesChurchRandom_plainK_log_vtx_spec R j
    rw [hlen] at hij
    rw [hs i hij, exists_isMisesChurchRandom_plainK_log_cantorPrefix R j]
    simp

/-- Step 7 of the proof of `exists_isMisesChurchRandom_plainK_log`: every rule selects
from the constructed sequence a finite or balanced stream (steps 3-6). -/
private lemma exists_isMisesChurchRandom_plainK_log_random (R : ℕ → Set BitString) (i : ℕ) :
    FiniteOrFreq (1 / 2) (selectStream (R i) (exists_isMisesChurchRandom_plainK_log_seq R)) := by
  classical
  obtain ⟨hpar, hcap, htired, hsel⟩ := exists_isMisesChurchRandom_plainK_log_interface R i
  have habs := exists_isMisesChurchRandom_plainK_log_abs
    (exists_isMisesChurchRandom_plainK_log_vtx R) (exists_isMisesChurchRandom_plainK_log_seq R)
    (fun j => decide (cantorPrefix (exists_isMisesChurchRandom_plainK_log_seq R) j ∈ R i)) i
    hpar hcap htired hsel
  apply exists_isMisesChurchRandom_plainK_log_chain_freq
  intro ε hε
  obtain ⟨L, hL⟩ := habs ε hε
  refine ⟨L, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := exists_isMisesChurchRandom_plainK_log_selectChain_counts (R i)
    (exists_isMisesChurchRandom_plainK_log_seq R) t
  rw [h1] at ht
  rw [h2, h1]
  exact hL t ht

/-- The `Primrec` computation of the height of the active vertex. -/
private lemma exists_isMisesChurchRandom_plainK_log_primrec_height :
    Primrec (fun x : List (List Bool) × List Bool =>
      exists_isMisesChurchRandom_plainK_log_height x.1 x.2) := by
  unfold exists_isMisesChurchRandom_plainK_log_height
  refine Primrec.list_findIdx
    (f := fun x : List (List Bool) × List Bool => List.range (x.2.length + 1))
    (p := fun x h => decide (x.1.count (x.2.take h) < exists_isMisesChurchRandom_plainK_log_cap h))
    ?_ ?_
  · exact Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd))
  · have hcount : Primrec (fun y : (List (List Bool) × List Bool) × ℕ =>
        y.1.1.count (y.1.2.take y.2)) := by
      have h := list_countP_primrec
        (f := fun y : (List (List Bool) × List Bool) × ℕ => y.1.1)
        (p := fun y z => decide (z = y.1.2.take y.2))
        (Primrec.fst.comp Primrec.fst)
        (Primrec.eq.decide.comp Primrec.snd
          (Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      exact h.of_eq (fun y => by simp [List.count_eq_countP, beq_eq_decide])
    have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    have hcap : Primrec (fun y : (List (List Bool) × List Bool) × ℕ =>
        exists_isMisesChurchRandom_plainK_log_cap y.2) :=
      (hpow.comp (Primrec.const 4) Primrec.snd).of_eq (fun y => rfl)
    exact Primrec.nat_lt.decide.comp hcount hcap

/-- The `Primrec` computation of one step of the construction. -/
private lemma exists_isMisesChurchRandom_plainK_log_primrec_stepFun :
    Primrec (fun x : (BitString × List (List Bool)) × List Bool =>
      exists_isMisesChurchRandom_plainK_log_stepFun x.1 x.2) := by
  have hh : Primrec (fun x : (BitString × List (List Bool)) × List Bool =>
      exists_isMisesChurchRandom_plainK_log_height x.1.2 x.2) :=
    exists_isMisesChurchRandom_plainK_log_primrec_height.comp
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hv : Primrec (fun x : (BitString × List (List Bool)) × List Bool =>
      x.2.take (exists_isMisesChurchRandom_plainK_log_height x.1.2 x.2)) :=
    Primrec.list_take.comp hh Primrec.snd
  have hcnt : Primrec (fun x : (BitString × List (List Bool)) × List Bool =>
      x.1.2.count (x.2.take (exists_isMisesChurchRandom_plainK_log_height x.1.2 x.2))) := by
    have h := list_countP_primrec
      (f := fun x : (BitString × List (List Bool)) × List Bool => x.1.2)
      (p := fun x z => decide (z = x.2.take (exists_isMisesChurchRandom_plainK_log_height x.1.2
                         x.2)))
      (Primrec.snd.comp Primrec.fst)
      (Primrec.eq.decide.comp Primrec.snd (hv.comp Primrec.fst))
    exact h.of_eq (fun x => by simp [List.count_eq_countP, beq_eq_decide])
  have hbit : Primrec (fun x : (BitString × List (List Bool)) × List Bool =>
      decide (x.1.2.count (x.2.take (exists_isMisesChurchRandom_plainK_log_height x.1.2 x.2)) % 2
        = 1)) :=
    Primrec.eq.decide.comp (Primrec.nat_mod.comp hcnt (Primrec.const 2)) (Primrec.const 1)
  exact (Primrec.pair
    (Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) hbit)
    (Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst) hv)).of_eq (fun x => rfl)

/-- The letter `i` of the pattern of `p` under the advice `adv`: run the code `i` if the advice
trusts it, otherwise answer `false`. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_ruleBit
    (adv : List Bool) (p : BitString) (i : ℕ) : Part Bool :=
  ((cond (adv.getD i false) (Nat.Partrec.Code.ofNatCode i) Nat.Partrec.Code.zero).eval
    (Encodable.encode p)).map fun v => decide (v = Encodable.encode true)

private lemma exists_isMisesChurchRandom_plainK_log_partrec_ruleBit :
    Partrec (fun x : List Bool × BitString × ℕ =>
      exists_isMisesChurchRandom_plainK_log_ruleBit x.1 x.2.1 x.2.2) := by
  have hb : Computable (fun x : List Bool × BitString × ℕ => x.1.getD x.2.2 false) :=
    ((Primrec.list_getD false).comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to_comp
  have hcode : Computable (fun x : List Bool × BitString × ℕ =>
      cond (x.1.getD x.2.2 false) (Nat.Partrec.Code.ofNatCode x.2.2) Nat.Partrec.Code.zero) := by
    refine Computable.cond hb ?_ (Computable.const _)
    exact ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.snd.comp Primrec.snd)).to_comp
  have hev : Partrec (fun x : List Bool × BitString × ℕ =>
      (cond (x.1.getD x.2.2 false) (Nat.Partrec.Code.ofNatCode x.2.2) Nat.Partrec.Code.zero).eval
        (Encodable.encode x.2.1)) :=
    Nat.Partrec.Code.eval_part.comp hcode
      (Computable.encode.comp (Computable.fst.comp Computable.snd))
  exact hev.map (g := fun _ v => decide (v = Encodable.encode true))
    (Primrec.eq.decide.comp Primrec.snd (Primrec.const _)).to_comp

/-- The pattern of `p` under the first `m` rules, computed from the advice. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_partPat
    (adv : List Bool) (p : BitString) (m : ℕ) : Part (List Bool) :=
  Nat.rec (Part.some [])
    (fun i IH => IH.bind fun u =>
      (exists_isMisesChurchRandom_plainK_log_ruleBit adv p i).map fun bt => u ++ [bt]) m

private lemma exists_isMisesChurchRandom_plainK_log_partrec_partPat :
    Partrec (fun x : List Bool × BitString × ℕ =>
      exists_isMisesChurchRandom_plainK_log_partPat x.1 x.2.1 x.2.2) := by
  have hh : Partrec₂ (fun (x : List Bool × BitString × ℕ) (iu : ℕ × List Bool) =>
      (exists_isMisesChurchRandom_plainK_log_ruleBit x.1 x.2.1 iu.1).map
        fun bt => iu.2 ++ [bt]) := by
    refine Partrec.map ?_ ?_
    · exact exists_isMisesChurchRandom_plainK_log_partrec_ruleBit.comp
        ((Computable.fst.comp Computable.fst).pair
          ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
            (Computable.fst.comp Computable.snd)))
    · exact (Primrec.list_concat.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd).to_comp
  have h := Partrec.nat_rec
    (f := fun x : List Bool × BitString × ℕ => x.2.2)
    (g := fun _ => Part.some ([] : List Bool))
    (h := fun (x : List Bool × BitString × ℕ) (iu : ℕ × List Bool) =>
      (exists_isMisesChurchRandom_plainK_log_ruleBit x.1 x.2.1 iu.1).map
        fun bt => iu.2 ++ [bt])
    (Computable.snd.comp Computable.snd)
    (Partrec.const' (Part.some ([] : List Bool)))
    hh
  exact h.of_eq fun x => rfl

/-- The iteration of the construction, in the `Part` monad, driven by the advice `adv`. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_iter
    (adv : List Bool) (n : ℕ) : Part (BitString × List (List Bool)) :=
  Nat.rec (Part.some (([] : BitString), ([] : List (List Bool))))
    (fun j IH => IH.bind fun s =>
      (exists_isMisesChurchRandom_plainK_log_partPat adv s.1
        (exists_isMisesChurchRandom_plainK_log_act j)).map
        fun u => exists_isMisesChurchRandom_plainK_log_stepFun s u) n

/-- `Nat.size` is computable. -/
private lemma exists_isMisesChurchRandom_plainK_log_computable_act :
    Computable exists_isMisesChurchRandom_plainK_log_act :=
  (Computable.list_length.comp natBits_computable).of_eq fun n => Nat.size_eq_bits_len n

private lemma exists_isMisesChurchRandom_plainK_log_partrec_iter :
    Partrec (fun x : List Bool × ℕ => exists_isMisesChurchRandom_plainK_log_iter x.1 x.2) :=
        by
  have hpat : Partrec (fun p : (List Bool × ℕ) × (ℕ × (BitString × List (List Bool))) =>
      exists_isMisesChurchRandom_plainK_log_partPat p.1.1 p.2.2.1
        (exists_isMisesChurchRandom_plainK_log_act p.2.1)) := by
    have hg : Computable (fun p : (List Bool × ℕ) × (ℕ × (BitString × List (List Bool))) =>
        ((p.1.1, p.2.2.1, exists_isMisesChurchRandom_plainK_log_act p.2.1) :
          List Bool × BitString × ℕ)) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (exists_isMisesChurchRandom_plainK_log_computable_act.comp
            (Computable.fst.comp Computable.snd)))
    have h1 := Partrec.comp
      (f := fun x : List Bool × BitString × ℕ =>
        exists_isMisesChurchRandom_plainK_log_partPat x.1 x.2.1 x.2.2)
      (g := fun p : (List Bool × ℕ) × (ℕ × (BitString × List (List Bool))) =>
        ((p.1.1, p.2.2.1, exists_isMisesChurchRandom_plainK_log_act p.2.1) :
          List Bool × BitString × ℕ))
      exists_isMisesChurchRandom_plainK_log_partrec_partPat hg
    exact h1
  have hst : Computable₂ (fun (p : (List Bool × ℕ) × (ℕ × (BitString × List (List Bool))))
      (u : List Bool) => exists_isMisesChurchRandom_plainK_log_stepFun p.2.2 u) :=
    (exists_isMisesChurchRandom_plainK_log_primrec_stepFun.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to_comp
  have hh : Partrec₂ (fun (x : List Bool × ℕ) (js : ℕ × (BitString × List (List Bool))) =>
      (exists_isMisesChurchRandom_plainK_log_partPat x.1 js.2.1
        (exists_isMisesChurchRandom_plainK_log_act js.1)).map
        fun u => exists_isMisesChurchRandom_plainK_log_stepFun js.2 u) :=
    Partrec.map (f := fun p : (List Bool × ℕ) × (ℕ × (BitString × List (List Bool))) =>
        exists_isMisesChurchRandom_plainK_log_partPat p.1.1 p.2.2.1
          (exists_isMisesChurchRandom_plainK_log_act p.2.1))
      (g := fun (p : (List Bool × ℕ) × (ℕ × (BitString × List (List Bool)))) (u : List Bool) =>
        exists_isMisesChurchRandom_plainK_log_stepFun p.2.2 u) hpat hst
  have h := Partrec.nat_rec
    (f := fun x : List Bool × ℕ => x.2)
    (g := fun _ => Part.some (([] : BitString), ([] : List (List Bool))))
    (h := fun (x : List Bool × ℕ) (js : ℕ × (BitString × List (List Bool))) =>
      (exists_isMisesChurchRandom_plainK_log_partPat x.1 js.2.1
        (exists_isMisesChurchRandom_plainK_log_act js.1)).map
        fun u => exists_isMisesChurchRandom_plainK_log_stepFun js.2 u)
    Computable.snd
    (Partrec.const' (Part.some (([] : BitString), ([] : List (List Bool)))))
    hh
  exact h.of_eq fun x => rfl

/-- The program: decode `n` and the advice from the input, run the construction. -/
private noncomputable def exists_isMisesChurchRandom_plainK_log_prog (a : BitString) :
    Part BitString :=
  (exists_isMisesChurchRandom_plainK_log_iter (decodeSecond a)
    (bitStringToNat (decodeFirst a))).map Prod.fst

private lemma exists_isMisesChurchRandom_plainK_log_partrec_prog :
    Partrec exists_isMisesChurchRandom_plainK_log_prog := by
  have hg : Computable (fun a : BitString =>
      ((decodeSecond a, bitStringToNat (decodeFirst a)) : List Bool × ℕ)) :=
    decodeSecond_computable.pair (computable_bitStringToNat.comp decodeFirst_computable)
  have hin : Partrec (fun a : BitString =>
      exists_isMisesChurchRandom_plainK_log_iter (decodeSecond a)
        (bitStringToNat (decodeFirst a))) :=
    Partrec.comp
      (f := fun x : List Bool × ℕ => exists_isMisesChurchRandom_plainK_log_iter x.1 x.2)
      (g := fun a : BitString =>
        ((decodeSecond a, bitStringToNat (decodeFirst a)) : List Bool × ℕ))
      exists_isMisesChurchRandom_plainK_log_partrec_iter hg
  exact Partrec.map (f := fun a : BitString =>
      exists_isMisesChurchRandom_plainK_log_iter (decodeSecond a)
        (bitStringToNat (decodeFirst a)))
    (g := fun (_ : BitString) (s : BitString × List (List Bool)) => s.1) hin
    (Computable.fst.comp Computable.snd)

/-! ### Correctness of the program -/

private lemma exists_isMisesChurchRandom_plainK_log_getD_map_range (b : ℕ → Bool) {M i : ℕ}
    (hi : i < M) : ((List.range M).map b).getD i false = b i := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma exists_isMisesChurchRandom_plainK_log_ruleBit_spec {b : ℕ → Bool}
    (hb : exists_isMisesChurchRandom_plainK_log_Good b) {M i : ℕ} (hi : i < M) (p : BitString) :
    ∃ bt : Bool,
      exists_isMisesChurchRandom_plainK_log_ruleBit ((List.range M).map b) p i
        = Part.some bt ∧ (bt = true ↔ p ∈ exists_isMisesChurchRandom_plainK_log_rule b i) := by
  unfold exists_isMisesChurchRandom_plainK_log_ruleBit
  rw [exists_isMisesChurchRandom_plainK_log_getD_map_range b hi]
  cases hbi : b i
  · refine ⟨false, ?_, ?_⟩
    · have h0 : Nat.Partrec.Code.eval Nat.Partrec.Code.zero (Encodable.encode p)
          = Part.some 0 := Nat.Partrec.Code.eval_const 0 _
      simp only [Bool.cond_false, h0, Part.map_some]
      simp
    · simp [exists_isMisesChurchRandom_plainK_log_rule, hbi]
  · obtain ⟨y, hy⟩ := (hb i).1 hbi p
    refine ⟨y, ?_, ?_⟩
    · simp only [Bool.cond_true, hy, Part.map_some]
      cases y <;> simp
    · simp only [exists_isMisesChurchRandom_plainK_log_rule, hbi, hy, true_and,
        Set.mem_ofPred_eq, Part.some_inj]
      cases y <;> simp

private lemma exists_isMisesChurchRandom_plainK_log_partPat_eq {b : ℕ → Bool}
    (hb : exists_isMisesChurchRandom_plainK_log_Good b) {M : ℕ} (p : BitString) :
    ∀ m, m ≤ M →
      exists_isMisesChurchRandom_plainK_log_partPat ((List.range M).map b) p m
        = Part.some (exists_isMisesChurchRandom_plainK_log_pat
            (exists_isMisesChurchRandom_plainK_log_rule b) p m) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [exists_isMisesChurchRandom_plainK_log_partPat,
      exists_isMisesChurchRandom_plainK_log_pat]
  | succ m ih =>
    intro hm
    obtain ⟨bt, hbt, hiff⟩ :=
      exists_isMisesChurchRandom_plainK_log_ruleBit_spec hb (Nat.lt_of_succ_le hm) p
    have hstep : exists_isMisesChurchRandom_plainK_log_partPat ((List.range M).map b) p
          (m + 1)
        = (exists_isMisesChurchRandom_plainK_log_partPat ((List.range M).map b) p m).bind
          (fun u => (exists_isMisesChurchRandom_plainK_log_ruleBit
            ((List.range M).map b) p m).map fun bt => u ++ [bt]) := rfl
    rw [hstep, ih (Nat.le_of_succ_le hm), Part.bind_some, hbt, Part.map_some]
    congr 1
    classical
    simp only [exists_isMisesChurchRandom_plainK_log_pat, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]
    congr 1
    simp only [List.cons.injEq, and_true]
    by_cases hp : p ∈ exists_isMisesChurchRandom_plainK_log_rule b m
    · simp [hp, hiff.2 hp]
    · have : bt = false := by
        cases bt
        · rfl
        · exact absurd (hiff.1 rfl) hp
      simp [hp, this]

private lemma exists_isMisesChurchRandom_plainK_log_iter_eq {b : ℕ → Bool}
    (hb : exists_isMisesChurchRandom_plainK_log_Good b) {M : ℕ} (n : ℕ)
    (hn : ∀ j < n, exists_isMisesChurchRandom_plainK_log_act j ≤ M) :
    exists_isMisesChurchRandom_plainK_log_iter ((List.range M).map b) n
      = Part.some (exists_isMisesChurchRandom_plainK_log_state
          (exists_isMisesChurchRandom_plainK_log_rule b) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (fun j hj => hn j (Nat.lt_succ_of_lt hj))
    have hstep : exists_isMisesChurchRandom_plainK_log_iter ((List.range M).map b) (n + 1)
        = (exists_isMisesChurchRandom_plainK_log_iter ((List.range M).map b) n).bind
          (fun s => (exists_isMisesChurchRandom_plainK_log_partPat ((List.range M).map b)
            s.1 (exists_isMisesChurchRandom_plainK_log_act n)).map
            fun u => exists_isMisesChurchRandom_plainK_log_stepFun s u) := rfl
    rw [hstep, h1, Part.bind_some,
      exists_isMisesChurchRandom_plainK_log_partPat_eq hb _
        (exists_isMisesChurchRandom_plainK_log_act n) (hn n (Nat.lt_succ_self n)), Part.map_some]
    rfl

/-- Step 8 of the proof of `exists_isMisesChurchRandom_plainK_log`: the prefix of length
`n` is computed by a fixed partial recursive function from the pair (code of `n`, the advice bits
`b 0, …, b (act n - 1)`), provided the advice is correct. -/
private lemma exists_isMisesChurchRandom_plainK_log_partrec :
    ∃ F : BitString →. BitString, Partrec F ∧
      ∀ b : ℕ → Bool, exists_isMisesChurchRandom_plainK_log_Good b → ∀ n : ℕ,
        F (pairCode (natToBitString n)
            ((List.range (exists_isMisesChurchRandom_plainK_log_act n)).map b))
          = Part.some (cantorPrefix (exists_isMisesChurchRandom_plainK_log_seq
              (exists_isMisesChurchRandom_plainK_log_rule b)) n) := by
  refine ⟨exists_isMisesChurchRandom_plainK_log_prog,
    exists_isMisesChurchRandom_plainK_log_partrec_prog, ?_⟩
  intro b hb n
  have hiter := exists_isMisesChurchRandom_plainK_log_iter_eq (b := b) hb
    (M := exists_isMisesChurchRandom_plainK_log_act n) n
    (fun j hj => Nat.size_le_size hj.le)
  unfold exists_isMisesChurchRandom_plainK_log_prog
  rw [decodeSecond_pairCode, decodeFirst_pairCode, bitStringToNat_natToBitString, hiter,
    Part.map_some, exists_isMisesChurchRandom_plainK_log_cantorPrefix]

/-- The length of the advice string for `n` is logarithmic. -/
private lemma exists_isMisesChurchRandom_plainK_log_len_le (b : ℕ → Bool) (n : ℕ) :
    (pairCode (natToBitString n)
      ((List.range (exists_isMisesChurchRandom_plainK_log_act n)).map b)).length
      ≤ 3 * Nat.log 2 n + 5 := by
  have hsize : Nat.size (n + 1) ≤ Nat.log 2 n + 2 := by
    rw [Nat.size_le]
    have h1 : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
    calc n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := h1
      _ < 2 ^ (Nat.log 2 n + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnat : (natToBitString n).length ≤ Nat.size (n + 1) - 1 := by
    simp [natToBitString, List.length_dropLast, Nat.size_eq_bits_len]
  have hact : exists_isMisesChurchRandom_plainK_log_act n ≤ Nat.size (n + 1) :=
    Nat.size_le_size (Nat.le_succ n)
  have hpos : 1 ≤ Nat.size (n + 1) := Nat.size_pos.mpr (Nat.succ_pos n)
  rw [length_pairCode, List.length_map, List.length_range]
  omega

/-- **SUV Theorem 173, p. 270.**  There is a Mises-Church random sequence whose prefixes have
logarithmic complexity, `C(ω_0 … ω_{n-1}) = O(log n)`.  The `+ c` covers `n = 0, 1`. -/
theorem exists_isMisesChurchRandom_plainK_log (V : Map) (hV : isOptimalConditional V) :
    ∃ w, IsMisesChurchRandom w ∧ ∃ c : ℕ, ∀ n : ℕ,
      plainK V (cantorPrefix w n) ≤ ((c * Nat.log 2 n + c : ℕ) : ℕ∞) := by
  obtain ⟨b, hb⟩ := exists_isMisesChurchRandom_plainK_log_good_exists
  obtain ⟨F, hF, hFb⟩ := exists_isMisesChurchRandom_plainK_log_partrec
  obtain ⟨c1, hc1⟩ := plainK_le_length V hV
  obtain ⟨c2, hc2⟩ := plainK_partrec_map_le V hV F hF
  refine ⟨exists_isMisesChurchRandom_plainK_log_seq
    (exists_isMisesChurchRandom_plainK_log_rule b), ?_, c1 + c2 + 5, fun n => ?_⟩
  · intro S hS
    obtain ⟨i, rfl⟩ := exists_isMisesChurchRandom_plainK_log_rule_of_decidable hb hS
    exact exists_isMisesChurchRandom_plainK_log_random _ i
  · have h1 := hc2 _ _ (show _ ∈ F _ by rw [hFb b hb n]; exact Part.mem_some _)
    have h2 := hc1 (pairCode (natToBitString n)
      ((List.range (exists_isMisesChurchRandom_plainK_log_act n)).map b))
    have h3 := exists_isMisesChurchRandom_plainK_log_len_le b n
    refine h1.trans ?_
    have h4 : (plainK V (pairCode (natToBitString n)
        ((List.range (exists_isMisesChurchRandom_plainK_log_act n)).map b)) : ℕ∞)
        ≤ (((c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) - c2 : ℕ) : ℕ∞) := by
      refine h2.trans ?_
      have : programLength (pairCode (natToBitString n)
          ((List.range (exists_isMisesChurchRandom_plainK_log_act n)).map b)) + c1
            ≤ (c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) - c2 := by
        unfold programLength
        have : 3 * Nat.log 2 n ≤ (c1 + c2 + 5) * Nat.log 2 n :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      exact_mod_cast this
    calc plainK V (pairCode (natToBitString n)
        ((List.range (exists_isMisesChurchRandom_plainK_log_act n)).map b)) + (c2 : ℕ∞)
        ≤ (((c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) - c2 : ℕ) : ℕ∞) + (c2 : ℕ∞) := by
          gcongr
      _ = (((c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add]
          congr 1
          have : 5 + c1 + c2 ≤ (c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) := by omega
          omega

end Kolmogorov.FrequencyGames
