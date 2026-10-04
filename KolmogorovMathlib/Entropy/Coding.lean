/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Entropy.Basic
import KolmogorovMathlib.Entropy.Codes.Kraft

/-!
# The entropy bound for the average length of a code

SUV Section 7.1.2, pp. 214–216, and the second proof of the McMillan inequality on p. 222.

Shannon entropy was introduced in the book as a lower bound for the average length of a uniquely
decodable code, and this file states that bound and its companions:

* the **Gibbs inequality** `H(p) ≤ ∑_i p_i (−log q_i)` for every `q` with positive entries and
  `∑ q_i ≤ 1`, together with the non-negativity and the equality case of the **Kullback–Leibler
  divergence** `klDiv` (p. 215).  `klDiv` is the finite real formula, which models the book's
  quantity only where the book uses it, namely for a strictly positive `q`; every statement about
  it below carries `0 < q a`;
* **Theorem 138**: the average length of a prefix code is at least the entropy, and some prefix
  code has average length below `H + 1` (p. 214).  Part (b) needs two letters of positive
  probability: as printed it fails for `p = (1, 0)`, where every prefix code for the two letters
  has average length `1 = H + 1`;
* **Problem 219**: the reading of Theorem 143 in terms of the minimal average length of a code
  (p. 221) — merging the letters of a fibre turns a prefix code for `ξ` into a prefix code for
  `f(ξ)` that is no longer;
* **Theorem 139**: `H ≤ log n` for a distribution with `n` values, with equality only for the
  uniform distribution (p. 216);
* the two statements of p. 222 that give the second proof of the McMillan inequality: an
  injective code whose codewords are shorter than `c` has average length at least `H − log c`,
  and a uniquely decodable code has average length at least `H`.

All entropies are base two (`entropyDist`), and all distributions are given as a non-negative
weight function on a `Fintype` summing to one.
-/

namespace Kolmogorov

open Finset

variable {α : Type*}

/-! ### The Gibbs inequality and the Kullback–Leibler divergence -/

/-- The summand of the Gibbs inequality: `p · log (q / p) ≤ q − p`, also at `p = 0`, where the
convention `log 0 = 0` makes the left side vanish. -/
private theorem mul_log_div_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log (q / p) ≤ q - p := by
  rcases hp.lt_or_eq with hp | hp
  · have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    calc p * Real.log (q / p) ≤ p * (q / p - 1) := by gcongr
      _ = q - p := by field_simp
  · subst hp
    simpa using hq.le

/-- The equality case of `mul_log_div_le`: `p · log (q / p) = q − p` forces `p = q`. -/
private theorem eq_of_mul_log_div_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (h : p * Real.log (q / p) = q - p) : p = q := by
  rcases hp.lt_or_eq with hp | hp
  · by_contra hne
    have hx : q / p ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq hp.ne').1 h1).symm
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hq hp) hx
    have h2 : p * Real.log (q / p) < p * (q / p - 1) := by gcongr
    have h3 : p * (q / p - 1) = q - p := by field_simp
    linarith
  · subst hp
    simp at h
    linarith

/-- The entropy summand against a positive weight, in terms of `log (q / p)`. -/
private theorem negMulLog2_add_mul_logb {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    negMulLog2 p + p * Real.logb 2 q = p * Real.log (q / p) / Real.log 2 := by
  rcases hp.lt_or_eq with hp | hp
  · rw [Real.log_div hq.ne' hp.ne']
    unfold negMulLog2 Real.negMulLog Real.logb
    ring
  · subst hp
    simp

/-- The difference between the entropy and the Gibbs sum, as a single sum. -/
private theorem entropyDist_sub_sum_eq [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 < q a) :
    entropyDist p - ∑ a, p a * (-Real.logb 2 (q a)) =
      (∑ a, p a * Real.log (q a / p a)) / Real.log 2 := by
  rw [entropyDist, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← negMulLog2_add_mul_logb (hp a) (hq a)]
  ring

/-- The Gibbs sum is bounded by the difference of the total weights. -/
private theorem sum_mul_log_div_le [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 < q a) :
    ∑ a, p a * Real.log (q a / p a) ≤ ∑ a, q a - ∑ a, p a := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun a _ => mul_log_div_le (hp a) (hq a)

/-- **The Gibbs inequality.**  For a distribution `p` and non-negative reals `q_i > 0` with
`∑_i q_i ≤ 1`, the quantity `∑_i p_i(−log q_i)` is minimal at `q = p`, where it equals the
entropy.  SUV Section 7.1.2, p. 215. -/
theorem entropyDist_le_sum_mul_neg_logb [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (hq : ∀ a, 0 < q a) (hqsum : ∑ a, q a ≤ 1) :
    entropyDist p ≤ ∑ a, p a * (-Real.logb 2 (q a)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := sum_mul_log_div_le hp hq
  rw [hpsum] at h
  have h2 : (∑ a, p a * Real.log (q a / p a)) / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hlog.le
  have h3 := entropyDist_sub_sum_eq hp hq
  linarith

/-- The Kullback–Leibler divergence `∑_i p_i log (p_i / q_i)` of two distributions, in bits.

This is the finite real formula, and it models the book's quantity **only for a strictly positive
`q`**, which is the domain on which the book introduces it (it is read off the Gibbs inequality,
where `q_i > 0`).  Outside that domain the real formula is not the divergence: for `p a > 0` and
`q a = 0` the true value is `+∞`, while `Real.logb 2 (p a / 0) = 0` makes the summand vanish.
Every theorem about `klDiv` below therefore carries the hypothesis `0 < q a`, and no statement of
the chapter uses the value at `q a = 0`.  SUV Section 7.1.2, p. 215. -/
noncomputable def klDiv [Fintype α] (p q : α → ℝ) : ℝ := ∑ a, p a * Real.logb 2 (p a / q a)

/-- The divergence as the Gibbs sum with the opposite sign. -/
private theorem klDiv_eq_neg_div [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 < q a) :
    klDiv p q = -(∑ a, p a * Real.log (q a / p a)) / Real.log 2 := by
  rw [klDiv, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases (hp a).lt_or_eq with h | h
  · rw [Real.logb, Real.log_div h.ne' (hq a).ne', Real.log_div (hq a).ne' h.ne']
    ring
  · rw [← h]
    simp

/-- The divergence is the excess of the Gibbs sum over the entropy. -/
private theorem klDiv_eq_sub [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 < q a) :
    klDiv p q = ∑ a, p a * (-Real.logb 2 (q a)) - entropyDist p := by
  rw [klDiv_eq_neg_div hp hq, neg_div, ← entropyDist_sub_sum_eq hp hq]
  ring

/-- **The Kullback–Leibler divergence is non-negative.**  SUV Section 7.1.2, p. 215. -/
theorem klDiv_nonneg [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) : 0 ≤ klDiv p q := by
  rw [klDiv_eq_neg_div hp hq]
  have h := sum_mul_log_div_le hp hq
  rw [hpsum, hqsum] at h
  exact div_nonneg (by linarith) (Real.log_pos (by norm_num)).le

/-- **The Kullback–Leibler divergence vanishes only on the diagonal**: it is zero exactly when
the two distributions coincide.  SUV Section 7.1.2, p. 215. -/
theorem klDiv_eq_zero_iff [Fintype α] {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) : klDiv p q = 0 ↔ ∀ a, p a = q a := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [klDiv_eq_neg_div hp hq, div_eq_zero_iff, neg_eq_zero, or_iff_left hlog.ne']
  constructor
  · intro h
    have hsum : ∑ a, (q a - p a - p a * Real.log (q a / p a)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hpsum, hqsum, h]
      ring
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
      sub_nonneg.2 (mul_log_div_le (hp a) (hq a))).1 hsum
    intro a
    exact eq_of_mul_log_div_eq (hp a) (hq a) (by linarith [hterm a (Finset.mem_univ a)])
  · intro h
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [h a, div_self (hq a).ne', Real.log_one, mul_zero]

/-! ### Theorem 138: entropy bounds the average code length -/

/-- **The average length of a prefix code is at least the entropy.**
SUV Theorem 138(a), p. 214. -/
theorem entropyDist_le_avgLength_of_isPrefixFree [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) {c : Code α} (hc : c.IsPrefixFree) :
    entropyDist p ≤ c.avgLength p := by
  have hk : ∑ a, (2 : ℝ)⁻¹ ^ (c a).length ≤ 1 :=
    ((Code.exists_isPrefixFree_lengths_iff_kraft fun a => (c a).length).1
      ⟨c, fun _ => rfl, hc⟩).2
  refine (entropyDist_le_sum_mul_neg_logb hp hpsum (q := fun a => (2 : ℝ)⁻¹ ^ (c a).length)
    (fun a => by positivity) hk).trans (le_of_eq ?_)
  unfold Code.avgLength
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

/-- Shannon's length `⌈−log p⌉` of a letter of probability `p` has weight `2^{-n} ≤ p` in the
Kraft sum. -/
private theorem inv_pow_ceil_neg_logb_le {x : ℝ} (hx : 0 < x) :
    (2 : ℝ)⁻¹ ^ ⌈-Real.logb 2 x⌉₊ ≤ x := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  calc (2 : ℝ) ^ (-(⌈-Real.logb 2 x⌉₊ : ℝ)) ≤ (2 : ℝ) ^ Real.logb 2 x :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith [Nat.le_ceil (-Real.logb 2 x)])
    _ = x := Real.rpow_logb (by norm_num) (by norm_num) hx

/-- A prefix code with prescribed positive lengths on a set of letters whose Kraft sum is
strictly below one: the remaining letters get a common length so large that they fit into the
room left.  This is the step of Theorem 138(b) that handles the letters of probability zero.
SUV Section 7.1.2, p. 215. -/
private theorem exists_isPrefixFree_lengths_of_sum_lt_one [Finite α]
    (S : Finset α) (n : α → ℕ) (hn : ∀ a ∈ S, 0 < n a)
    (hK : ∑ a ∈ S, (2 : ℝ)⁻¹ ^ n a < 1) :
    ∃ c : Code α, c.IsPrefixFree ∧ ∀ a ∈ S, (c a).length = n a := by
  classical
  have := Fintype.ofFinite α
  set K := ∑ a ∈ S, (2 : ℝ)⁻¹ ^ n a with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun a _ => by positivity
  set m : ℕ := (Finset.univ.filter fun a => a ∉ S).card with hm
  have hpos : (0 : ℝ) < (1 - K) / (m + 1) := div_pos (by linarith) (by positivity)
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with rfl | h
    · exfalso
      rw [pow_zero] at hL
      have : (1 - K) / (m + 1) ≤ 1 - K := div_le_self (by linarith) (by linarith)
      linarith
    · exact h
  have hmL : (m : ℝ) * (2 : ℝ)⁻¹ ^ L ≤ 1 - K := by
    calc (m : ℝ) * (2 : ℝ)⁻¹ ^ L ≤ (m + 1) * (2 : ℝ)⁻¹ ^ L := by
          gcongr
          linarith
      _ ≤ (m + 1) * ((1 - K) / (m + 1)) := by gcongr
      _ = 1 - K := by field_simp
  have hpos' : ∀ a, 0 < (if a ∈ S then n a else L) := fun a => by
    split_ifs with h
    · exact hn a h
    · exact hL0
  have hkraft : ∑ a, (2 : ℝ)⁻¹ ^ (if a ∈ S then n a else L) ≤ 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => a ∈ S)]
    have h1 : ∑ a ∈ Finset.univ.filter (fun a => a ∈ S),
        (2 : ℝ)⁻¹ ^ (if a ∈ S then n a else L) = K := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun a ha => by rw [ite_eq_left ha]
    have h2 : ∑ a ∈ Finset.univ.filter (fun a => a ∉ S),
        (2 : ℝ)⁻¹ ^ (if a ∈ S then n a else L) = m * (2 : ℝ)⁻¹ ^ L := by
      rw [Finset.sum_congr rfl fun a ha => by rw [ite_eq_right (Finset.mem_filter.1 ha).2],
        Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2]
    linarith
  obtain ⟨c, hlen, hc⟩ := (Code.exists_isPrefixFree_lengths_iff_kraft
    (fun a => if a ∈ S then n a else L)).2 ⟨hpos', hkraft⟩
  exact ⟨c, hc, fun a ha => by rw [hlen a, ite_eq_left ha]⟩

/-- **There is a prefix code of average length below `H + 1`.**

The hypothesis `h2` — two letters of positive probability — is not printed, and it cannot be
dropped: the book's "without loss of generality we may assume that all `p_i` are strictly
positive (since null values do not change Shannon entropy and average code length)" (p. 215) is
not valid for part (b), because deleting a null letter enlarges the set of available prefix
codes.  For `p = (1, 0)` on two letters one has `H = 0`, while every prefix code has average
length at least `1 = H + 1`, so the printed statement fails.  With two positive letters the
Shannon lengths `n_i = ⌈−log p_i⌉` are all positive and leave room for the null letters, and the
printed bound holds.  SUV Theorem 138(b), p. 214. -/
theorem exists_isPrefixFree_avgLength_lt_entropyDist_add_one [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (h2 : ∃ a b : α, a ≠ b ∧ 0 < p a ∧ 0 < p b) :
    ∃ c : Code α, c.IsPrefixFree ∧ c.avgLength p < entropyDist p + 1 := by
  classical
  obtain ⟨a₀, b₀, hab, ha₀, hb₀⟩ := h2
  set S := Finset.univ.filter fun a => 0 < p a with hS
  have hmemS : ∀ a, a ∈ S ↔ 0 < p a := fun a => by simp [hS]
  have hle1 : ∀ a, p a ≤ 1 := fun a => by
    rw [← hpsum]
    exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
  have hlt1 : ∀ a ∈ S, p a < 1 := by
    intro a ha
    have key : ∀ b, b ≠ a → 0 < p b → p a < 1 := fun b hb hpb => by
      have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {a, b})
        (fun x _ _ => hp x) (f := p)
      rw [Finset.sum_pair (Ne.symm hb), hpsum] at h
      linarith
    by_cases h : a₀ = a
    · exact key b₀ (h ▸ hab.symm) hb₀
    · exact key a₀ h ha₀
  set n : α → ℕ := fun a => ⌈-Real.logb 2 (p a)⌉₊ with hn
  have hn_pos : ∀ a ∈ S, 0 < n a := fun a ha =>
    Nat.ceil_pos.2 (by linarith [Real.logb_neg (b := 2) (by norm_num) ((hmemS a).1 ha) (hlt1 a ha)])
  have hpow_le : ∀ a ∈ S, (2 : ℝ)⁻¹ ^ n a ≤ p a := fun a ha =>
    inv_pow_ceil_neg_logb_le ((hmemS a).1 ha)
  have hn_lt : ∀ a ∈ S, (n a : ℝ) < -Real.logb 2 (p a) + 1 := fun a ha =>
    Nat.ceil_lt_add_one (by linarith [Real.logb_nonpos (b := 2) (by norm_num) (hp a) (hle1 a)])
  have hsumS : ∑ a ∈ S, p a = 1 := by
    rw [← hpsum]
    exact Finset.sum_filter_of_ne fun a _ h => lt_of_le_of_ne (hp a) (Ne.symm h)
  have hK : ∑ a ∈ S, (2 : ℝ)⁻¹ ^ n a ≤ 1 := hsumS ▸ Finset.sum_le_sum hpow_le
  have hH : entropyDist p = ∑ a ∈ S, p a * (-Real.logb 2 (p a)) := by
    rw [entropyDist, ← Finset.sum_filter_of_ne (p := fun a => 0 < p a)
      (fun a _ h => lt_of_le_of_ne (hp a) fun h0 => h (by rw [← h0, negMulLog2_zero]))]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold negMulLog2 Real.negMulLog Real.logb
    ring
  have ha₀S : a₀ ∈ S := (hmemS a₀).2 ha₀
  have havg0 : ∑ a ∈ S, p a * (n a : ℝ) < entropyDist p + 1 := by
    rw [hH, ← hsumS, ← Finset.sum_add_distrib]
    refine Finset.sum_lt_sum_of_nonempty ⟨a₀, ha₀S⟩ fun a ha => ?_
    have := mul_lt_mul_of_pos_left (hn_lt a ha) ((hmemS a).1 ha)
    linarith
  have hzero_avg : ∀ c : Code α, c.avgLength p = ∑ a ∈ S, p a * ((c a).length : ℝ) :=
    fun c => (Finset.sum_filter_of_ne fun a _ h =>
      lt_of_le_of_ne (hp a) fun h0 => h (by rw [← h0, zero_mul])).symm
  rcases hK.lt_or_eq with hK | hK
  · obtain ⟨c, hc, hlen⟩ := exists_isPrefixFree_lengths_of_sum_lt_one S n hn_pos hK
    refine ⟨c, hc, ?_⟩
    rw [hzero_avg]
    calc ∑ a ∈ S, p a * ((c a).length : ℝ) = ∑ a ∈ S, p a * (n a : ℝ) :=
          Finset.sum_congr rfl fun a ha => by rw [hlen a ha]
      _ < _ := havg0
  · have hdy : ∀ a ∈ S, p a = (2 : ℝ)⁻¹ ^ n a := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun a ha => sub_nonneg.2 (hpow_le a ha)).1
        (by rw [Finset.sum_sub_distrib, hsumS, hK, sub_self])
      exact fun a ha => sub_eq_zero.1 (this a ha)
    have hHeq : entropyDist p = ∑ a ∈ S, p a * (n a : ℝ) := by
      rw [hH]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hdy a ha, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
      ring
    set n' : α → ℕ := fun a => if a = a₀ then n a + 1 else n a with hn'
    have hn'_erase : ∀ a ∈ S.erase a₀, n' a = n a := fun a ha => by
      simp [hn', Finset.ne_of_mem_erase ha]
    have hK' : ∑ a ∈ S, (2 : ℝ)⁻¹ ^ n' a < 1 := by
      rw [← Finset.add_sum_erase S _ ha₀S] at hK ⊢
      rw [Finset.sum_congr rfl fun a ha => by rw [hn'_erase a ha]]
      have : n' a₀ = n a₀ + 1 := by simp [hn']
      rw [this, pow_succ]
      have : (0 : ℝ) < 2⁻¹ ^ n a₀ := by positivity
      linarith
    obtain ⟨c, hc, hlen⟩ := exists_isPrefixFree_lengths_of_sum_lt_one S n' (fun a ha => by
      simp only [hn']
      split_ifs
      · exact Nat.succ_pos _
      · exact hn_pos a ha) hK'
    refine ⟨c, hc, ?_⟩
    rw [hzero_avg, hHeq]
    have hlt : p a₀ < 1 := hlt1 a₀ ha₀S
    calc ∑ a ∈ S, p a * ((c a).length : ℝ) = ∑ a ∈ S, p a * (n' a : ℝ) :=
          Finset.sum_congr rfl fun a ha => by rw [hlen a ha]
      _ = ∑ a ∈ S, p a * (n a : ℝ) + p a₀ := by
          rw [← Finset.add_sum_erase S _ ha₀S, ← Finset.add_sum_erase S _ ha₀S,
            Finset.sum_congr rfl fun a ha => by rw [hn'_erase a ha]]
          have : n' a₀ = n a₀ + 1 := by simp [hn']
          rw [this]
          push_cast
          ring
      _ < _ := by linarith

/-! ### Theorem 139: the entropy of a distribution with `n` values -/

/-- **The entropy of a distribution with `n` possible values does not exceed `log n`.**
SUV Theorem 139, p. 216. -/
theorem entropyDist_le_logb_card [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) : entropyDist p ≤ Real.logb 2 (Fintype.card α) := by
  rcases isEmpty_or_nonempty α with _ | _
  · simp [entropyDist]
  · have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    refine (entropyDist_le_sum_mul_neg_logb hp hpsum (q := fun _ => 1 / Fintype.card α)
      (fun _ => by positivity) (le_of_eq ?_)).trans (le_of_eq ?_)
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hcard.ne']
    · simp only [one_div, Real.logb_inv, neg_neg, ← Finset.sum_mul, hpsum, one_mul]

/-- **The bound `H ≤ log n` is attained only by the uniform distribution.**
SUV Theorem 139, p. 216. -/
theorem eq_inv_card_of_entropyDist_eq_logb_card [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (h : entropyDist p = Real.logb 2 (Fintype.card α)) (a : α) :
    p a = 1 / Fintype.card α := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hq : ∀ _ : α, (0 : ℝ) < 1 / Fintype.card α := fun _ => by positivity
  have hqsum : ∑ _a : α, (1 : ℝ) / Fintype.card α = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hcard.ne']
  refine (klDiv_eq_zero_iff hp hpsum hq hqsum).1 ?_ a
  rw [klDiv_eq_sub hp hq]
  simp only [one_div, Real.logb_inv, neg_neg, ← Finset.sum_mul, hpsum, one_mul]
  rw [← h, sub_self]

/-! ### Problem 219: Theorem 143 in terms of code length -/

/-- **Coarsening a random variable does not make coding harder.**  This is the reading of
Theorem 143 (`H(f(ξ)) ≤ H(ξ)`) in terms of the minimal average length of a prefix code, together
with the direct proof, that the problem asks for: if `c` is a prefix code for the letters of `ξ`
and `f` is defined on the range of `ξ`, so that every value of `f(ξ)` comes from a letter
(`hf`), then `f(ξ)`, whose distribution is the pushforward `b ↦ ∑_{f a = b} p a`, has a prefix
code of average length **at most** that of `c`.  Applied to an optimal `c`, this says that the
minimal average length for `f(ξ)` is at most the minimal average length for `ξ`.

The direct proof is the merging of letters: give the value `b` a shortest codeword among the
codewords of the letters of the fibre `f⁻¹(b)`, which is non-empty by `hf`.  Distinct values use
codewords of distinct letters, so the result is again a prefix code, and every letter is coded by
a string no longer than its old codeword, whence the inequality between the average lengths.

The problem prints no statement (it asks for "an interpretation ... and the direct proof"), so
this is a reconstruction.  SUV Problem 219, p. 221. -/
theorem exists_isPrefixFree_avgLength_map_le [Fintype α] {β : Type*} [Fintype β]
    [DecidableEq β] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1) {f : α → β}
    (hf : Function.Surjective f) {c : Code α} (hc : c.IsPrefixFree) :
    ∃ d : Code β, d.IsPrefixFree ∧
      d.avgLength (fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a) ≤
        c.avgLength p := by
  have _ := hpsum
  have hne : ∀ b, (Finset.univ.filter fun a => f a = b).Nonempty := fun b => by
    obtain ⟨a, ha⟩ := hf b
    exact ⟨a, by simp [ha]⟩
  choose g hg hmin using fun b =>
    Finset.exists_min_image _ (fun a => (c a).length) (hne b)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg hmin
  refine ⟨fun b => c (g b), ⟨fun b => hc.ne_nil _, fun b b' hbb' => hc.2 _ _ ?_⟩, ?_⟩
  · intro h
    exact hbb' (by rw [← hg b, ← hg b', h])
  · unfold Code.avgLength
    calc ∑ b, (∑ a ∈ Finset.univ.filter (fun a => f a = b), p a) * ((c (g b)).length : ℝ)
        = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
            p a * ((c (g b)).length : ℝ) := by
          simp only [Finset.sum_mul]
      _ ≤ ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a * ((c a).length : ℝ) := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a ha => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmin b a ha) (hp a)
      _ = ∑ a, p a * ((c a).length : ℝ) := Finset.sum_fiberwise _ _ _

/-- The entropy summand is subadditive on a finite family of non-negative weights: merging
the weights of a fibre does not increase the entropy contributed by the fibre, because every
weight `p a` of the fibre satisfies `-log p a ≥ -log (∑ p)`. -/
private theorem negMulLog2_sum_le {ι : Type*} (s : Finset ι) {p : ι → ℝ}
    (hp : ∀ a, 0 ≤ p a) : negMulLog2 (∑ a ∈ s, p a) ≤ ∑ a ∈ s, negMulLog2 (p a) := by
  have hT : ∀ a ∈ s, p a ≤ ∑ b ∈ s, p b := fun a ha =>
    Finset.single_le_sum (fun b _ => hp b) ha
  have hrepr : ∀ x : ℝ, negMulLog2 x = x * (-Real.logb 2 x) := fun x => by
    unfold negMulLog2 Real.negMulLog Real.logb
    ring
  rw [hrepr, Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [hrepr]
  rcases (hp a).lt_or_eq with h | h
  · have := Real.logb_le_logb_of_le (b := 2) (by norm_num) h (hT a ha)
    nlinarith
  · rw [← h]
    simp

/-- The pushforward of a distribution along a map has no larger entropy: Theorem 143 read on
distributions, proved by merging the letters of each fibre. -/
private theorem entropyDist_map_le [Fintype α] {β : Type*} [Fintype β] [DecidableEq β]
    {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (f : α → β) :
    entropyDist (fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a) ≤
      entropyDist p := by
  unfold entropyDist
  rw [← Finset.sum_fiberwise Finset.univ f]
  exact Finset.sum_le_sum fun b _ => negMulLog2_sum_le _ hp

/-- A prefix code on `β` in which a chosen letter has a codeword of length one: `0` for that
letter, and `1` followed by a fixed-width block for every other letter. -/
private theorem exists_isPrefixFree_length_eq_one {β : Type*} [Finite β]
    (b₀ : β) : ∃ d : Code β, d.IsPrefixFree ∧ (d b₀).length = 1 := by
  classical
  have := Fintype.ofFinite β
  have := Fintype.toEncodable β
  refine ⟨fun b => if b = b₀ then [false] else true :: alphabetCode β b, ⟨?_, ?_⟩, by simp⟩
  · intro b
    dsimp only
    split_ifs <;> simp
  · intro b b' hbb'
    dsimp only
    split_ifs with hb hb'
    · exact absurd (hb.trans hb'.symm) hbb'
    · intro h
      simpa using (List.cons_prefix_cons.1 h).1
    · intro h
      simpa using (List.cons_prefix_cons.1 h).1
    · intro h
      exact (alphabetCode_isPrefixFree (α := β)).2 b b' hbb' (List.cons_prefix_cons.1 h).2

/-- **The same for an arbitrary codomain, with the loss of one bit.**  The corollary that
survives when `f` is not onto `β`: some prefix code for `f(ξ)` has average length below that of
`c` plus one.  The merging construction of `exists_isPrefixFree_avgLength_map_le` can fail here,
because the merged codewords may already form a complete prefix code and leave nothing for a
value outside the range of `f` (for `c = (0, 1)` on two letters and an injective `f` into three
values, no non-empty third codeword can be added), so only the rounding bound of Theorem 138
remains: the pushforward has entropy at most `H(p) ≤ avgLength c`, and a prefix code for it of
average length below `H + 1` exists by Theorem 138(b) when two of its letters have positive
probability, while a code of average length `1 ≤ avgLength c` does when only one has.
SUV Problem 219, p. 221. -/
theorem exists_isPrefixFree_avgLength_map_lt_add_one [Fintype α] {β : Type*} [Fintype β]
    [DecidableEq β] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1) (f : α → β)
    {c : Code α} (hc : c.IsPrefixFree) :
    ∃ d : Code β, d.IsPrefixFree ∧
      d.avgLength (fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a) <
        c.avgLength p + 1 := by
  set p' : β → ℝ := fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a with hp'
  have hp'0 : ∀ b, 0 ≤ p' b := fun b => Finset.sum_nonneg fun a _ => hp a
  have hp'sum : ∑ b, p' b = 1 := by
    rw [← hpsum]
    exact Finset.sum_fiberwise _ _ _
  have hH : entropyDist p' ≤ entropyDist p := entropyDist_map_le hp f
  have hHc : entropyDist p ≤ c.avgLength p :=
    entropyDist_le_avgLength_of_isPrefixFree hp hpsum hc
  by_cases h2 : ∃ b b' : β, b ≠ b' ∧ 0 < p' b ∧ 0 < p' b'
  · obtain ⟨d, hd, hlt⟩ :=
      exists_isPrefixFree_avgLength_lt_entropyDist_add_one hp'0 hp'sum h2
    exact ⟨d, hd, by linarith⟩
  · obtain ⟨b₀, hb₀⟩ : ∃ b, 0 < p' b := by
      by_contra hcon
      push Not at hcon
      have : ∑ b, p' b = 0 := Finset.sum_eq_zero fun b _ => le_antisymm (hcon b) (hp'0 b)
      linarith
    have hzero : ∀ b, b ≠ b₀ → p' b = 0 := fun b hb => by
      by_contra hne
      exact h2 ⟨b₀, b, hb.symm, hb₀, lt_of_le_of_ne (hp'0 b) (Ne.symm hne)⟩
    obtain ⟨d, hd, hd1⟩ := exists_isPrefixFree_length_eq_one b₀
    refine ⟨d, hd, ?_⟩
    have havg : d.avgLength p' = p' b₀ := by
      unfold Code.avgLength
      rw [Finset.sum_eq_single b₀ (fun b _ hb => by rw [hzero b hb, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), hd1]
      simp
    have hb₀1 : p' b₀ ≤ 1 := by
      rw [← hp'sum]
      exact Finset.single_le_sum (fun b _ => hp'0 b) (Finset.mem_univ b₀)
    have hc1 : 1 ≤ c.avgLength p := by
      unfold Code.avgLength
      calc (1 : ℝ) = ∑ a, p a * 1 := by simp [hpsum]
        _ ≤ ∑ a, p a * ((c a).length : ℝ) := by
          refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hp a)
          exact_mod_cast List.length_pos_of_ne_nil (hc.ne_nil a)
    rw [havg]
    linarith

/-! ### The entropy bound for uniquely decodable codes -/

/-- The Kraft sum of an injective code whose codewords are shorter than `b` is at most `b`:
each length `ℓ < b` carries at most `2^ℓ` codewords, each of weight `2^{-ℓ}`. -/
private theorem sum_inv_pow_length_le_of_injective [Fintype α] {c : Code α}
    (hinj : Function.Injective c) {b : ℕ} (hb : ∀ a, (c a).length < b) :
    ∑ a, (2 : ℝ)⁻¹ ^ (c a).length ≤ b := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range b) (g := fun a => (c a).length)
    (fun a _ => Finset.mem_range.2 (hb a))]
  calc ∑ ℓ ∈ Finset.range b, ∑ a ∈ Finset.univ.filter (fun a => (c a).length = ℓ),
          (2 : ℝ)⁻¹ ^ (c a).length
      = ∑ ℓ ∈ Finset.range b, ((Finset.univ.filter fun a => (c a).length = ℓ).card : ℝ) *
          (2 : ℝ)⁻¹ ^ ℓ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ ℓ ∈ Finset.range b, (1 : ℝ) := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        have hcard : (Finset.univ.filter fun a => (c a).length = ℓ).card ≤ 2 ^ ℓ := by
          rw [← card_stringsOfLength ℓ]
          refine Finset.card_le_card_of_injOn c ?_ (hinj.injOn)
          intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
          exact (mem_stringsOfLength ℓ (c a)).2 ha
        calc ((Finset.univ.filter fun a => (c a).length = ℓ).card : ℝ) * (2 : ℝ)⁻¹ ^ ℓ
            ≤ (2 : ℝ) ^ ℓ * (2 : ℝ)⁻¹ ^ ℓ := by
              gcongr
              exact_mod_cast hcard
          _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
    _ = b := by simp

/-- **An injective code with short codewords is almost as long as the entropy.**  If all the
codewords of an injective code have length less than `b`, then its average length is at least
`H(p) − log b`.  SUV Section 7.2.3, p. 222. -/
theorem entropyDist_sub_logb_le_avgLength_of_injective [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1) {c : Code α} (hinj : Function.Injective c)
    {b : ℕ} (hb : ∀ a, (c a).length < b) :
    entropyDist p - Real.logb 2 b ≤ c.avgLength p := by
  have _hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hpsum
  have hb0 : (0 : ℝ) < b := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) (hb (Classical.arbitrary α))
  have hk := sum_inv_pow_length_le_of_injective hinj hb
  have h := entropyDist_le_sum_mul_neg_logb hp hpsum
    (q := fun a => (2 : ℝ)⁻¹ ^ (c a).length / b) (fun a => by positivity)
    (by rw [← Finset.sum_div]; exact (div_le_one hb0).2 hk)
  have h1 : Real.logb 2 b = (∑ a, p a) * Real.logb 2 b := by rw [hpsum, one_mul]
  have h2 : ∑ a, p a * (-Real.logb 2 ((2 : ℝ)⁻¹ ^ (c a).length / b)) =
      c.avgLength p + Real.logb 2 b := by
    unfold Code.avgLength
    rw [h1, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.logb_div (by positivity) hb0.ne', Real.logb_pow, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num)]
    ring
  linarith

/-- The product distribution `w ↦ ∏_i p (w_i)` of `N` independent copies of `p` sums to one.
SUV Section 7.2.3, p. 222. -/
private theorem sum_prod_pi_eq_one [Fintype α] {p : α → ℝ} (hpsum : ∑ a, p a = 1) (N : ℕ) :
    ∑ w : Fin N → α, ∏ i, p (w i) = 1 := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [hpsum]

/-- Marginalising an additive functional against the product distribution: the expectation of
`∑_i g (w_i)` under `N` independent copies of `p` is `N` times the expectation of `g`.  This is
the computation behind both `entropyDist_prod_eq` and `avgLength_prodCode_eq`.
SUV Section 7.2.3, p. 222. -/
private theorem sum_prod_mul_sum_eq [Fintype α] {p : α → ℝ} (hpsum : ∑ a, p a = 1)
    (g : α → ℝ) (N : ℕ) :
    ∑ w : Fin N → α, (∏ i, p (w i)) * ∑ i, g (w i) = N * ∑ a, p a * g a := by
  have key : ∀ i : Fin N, ∑ w : Fin N → α, (∏ j, p (w j)) * g (w i) = ∑ a, p a * g a := by
    intro i
    have hw : ∀ w : Fin N → α, (∏ j, p (w j)) * g (w i) =
        ∏ j, (if j = i then p (w j) * g (w j) else p (w j)) := fun w => by
      have hsplit : ∀ j, (if j = i then p (w j) * g (w j) else p (w j)) =
          p (w j) * (if j = i then g (w j) else 1) := fun j => by split_ifs <;> ring
      simp_rw [hsplit]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i (fun j => g (w j)),
        ite_eq_left (Finset.mem_univ i)]
    simp_rw [hw]
    rw [← Fintype.piFinset_univ,
      Finset.sum_prod_piFinset Finset.univ (fun j a => if j = i then p a * g a else p a),
      Fintype.prod_eq_single i fun j hj => by simp [hj, hpsum]]
    simp
  rw [Finset.sum_congr rfl fun w _ => Finset.mul_sum .., Finset.sum_comm,
    Finset.sum_congr rfl fun i _ => key i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The entropy of `N` independent copies of a distribution is `N` times its entropy.
SUV Section 7.2.3, p. 222 (the property `H(ξ^N) = N·H(ξ)` used by the second proof of the
McMillan inequality). -/
theorem entropyDist_prod_eq [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (N : ℕ) :
    entropyDist (fun w : Fin N → α => ∏ i, p (w i)) = N * entropyDist p := by
  have _ := hp
  have hrepr : ∀ x : ℝ, negMulLog2 x = x * (-Real.logb 2 x) := fun x => by
    unfold negMulLog2 Real.negMulLog Real.logb
    ring
  have hw : ∀ w : Fin N → α, negMulLog2 (∏ i, p (w i)) =
      (∏ i, p (w i)) * ∑ i, -Real.logb 2 (p (w i)) := fun w => by
    by_cases h0 : ∃ i, p (w i) = 0
    · obtain ⟨i, hi⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, negMulLog2_zero, zero_mul]
    · push Not at h0
      rw [hrepr, Real.logb_prod _ _ fun i _ => h0 i, Finset.sum_neg_distrib]
  unfold entropyDist
  rw [Finset.sum_congr rfl fun w _ => hw w,
    sum_prod_mul_sum_eq hpsum (fun a => -Real.logb 2 (p a)) N]
  congr 1
  exact Finset.sum_congr rfl fun a _ => (hrepr (p a)).symm

/-- The encoding of a word of length `N` is the concatenation of the codewords of its letters,
so its length is the sum of their lengths.  SUV Section 7.1.1, p. 213. -/
private theorem length_encodeWord_ofFn (c : Code α) {N : ℕ} (w : Fin N → α) :
    (c.encodeWord (List.ofFn w)).length = ∑ i, (c (w i)).length := by
  simp [Code.encodeWord, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp]

/-- The average length of the concatenated code on words of length `N`, against the product
distribution, is `N` times the average length of the code.  SUV Section 7.2.3, p. 222. -/
private theorem avgLength_prodCode_eq [Fintype α] {p : α → ℝ} (hpsum : ∑ a, p a = 1)
    (c : Code α) (N : ℕ) :
    Code.avgLength (fun w : Fin N → α => c.encodeWord (List.ofFn w))
        (fun w => ∏ i, p (w i)) = N * c.avgLength p := by
  unfold Code.avgLength
  rw [← sum_prod_mul_sum_eq hpsum (fun a => ((c a).length : ℝ))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [length_encodeWord_ofFn]
  push_cast
  rfl

/-- The book's estimate for `N` copies: the concatenated code is injective on words of length
`N` because the code is uniquely decodable, and its codewords are shorter than `N·M + 1` when
every codeword of `c` has length at most `M`, so the bound for injective codes gives
`N·H − log (N·M + 1) ≤ N·(average length)`.  SUV Section 7.2.3, p. 222. -/
private theorem mul_entropyDist_sub_avgLength_le [Fintype α] {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) {c : Code α} (hc : c.IsUniquelyDecodable) {M : ℕ}
    (hM : ∀ a, (c a).length ≤ M) (N : ℕ) :
    (N : ℝ) * (entropyDist p - c.avgLength p) ≤ Real.logb 2 (N * M + 1) := by
  have hinj : Function.Injective fun w : Fin N → α => c.encodeWord (List.ofFn w) :=
    fun w w' h => List.ofFn_injective (hc h)
  have hb : ∀ w : Fin N → α, (c.encodeWord (List.ofFn w)).length < N * M + 1 := fun w => by
    rw [length_encodeWord_ofFn, Nat.lt_succ_iff]
    calc ∑ i, (c (w i)).length ≤ ∑ _i : Fin N, M := Finset.sum_le_sum fun i _ => hM (w i)
      _ = N * M := by simp
  have h := entropyDist_sub_logb_le_avgLength_of_injective
    (p := fun w : Fin N → α => ∏ i, p (w i)) (fun w => Finset.prod_nonneg fun i _ => hp _)
    (sum_prod_pi_eq_one hpsum N) hinj hb
  rw [entropyDist_prod_eq hp hpsum N, avgLength_prodCode_eq hpsum c N] at h
  push_cast at h
  linarith

/-- A real `x` with `N·x ≤ log (N·M + 1)` for every `N` is non-positive: the right-hand side
grows only logarithmically in `N`.  SUV Section 7.2.3, p. 222 (the passage to the limit
`N → ∞`). -/
private theorem nonpos_of_mul_le_logb {x : ℝ} {M : ℕ}
    (h : ∀ N : ℕ, (N : ℝ) * x ≤ Real.logb 2 (N * M + 1)) : x ≤ 0 := by
  by_contra hx
  push Not at hx
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Filter.Tendsto (fun N : ℕ => Real.log N ^ 1 / (1 * (N : ℝ) + 0) +
      Real.log (M + 1) / N) Filter.atTop (nhds (0 + 0)) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).add (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [add_zero] at hlim
  obtain ⟨N, hN1, hN2⟩ := ((hlim.eventually (gt_mem_nhds (mul_pos hx hlog))).and
    (Filter.eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN2
  have hkey := h N
  rw [Real.logb, le_div_iff₀ hlog] at hkey
  have hle : Real.log ((N : ℝ) * M + 1) ≤ Real.log N + Real.log (M + 1) := by
    rw [← Real.log_mul hNpos.ne' (by positivity)]
    exact Real.log_le_log (by positivity) (by rw [mul_add, mul_one]; linarith)
  simp only [pow_one, one_mul, add_zero] at hN1
  rw [← add_div, div_lt_iff₀ hNpos] at hN1
  linarith

/-- **The average length of a uniquely decodable code is at least the entropy.**  This is the
statement whose proof, through `N` independent copies of the random variable, gives the book's
second proof of the McMillan inequality.  SUV Section 7.2.3, p. 222. -/
theorem entropyDist_le_avgLength_of_isUniquelyDecodable [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1) {c : Code α} (hc : c.IsUniquelyDecodable) :
    entropyDist p ≤ c.avgLength p := by
  have hM : ∀ a, (c a).length ≤ Finset.univ.sup fun a => (c a).length := fun a =>
    Finset.le_sup (f := fun a => (c a).length) (Finset.mem_univ a)
  have := nonpos_of_mul_le_logb fun N => mul_entropyDist_sub_avgLength_le hp hpsum hc hM N
  linarith

end Kolmogorov
