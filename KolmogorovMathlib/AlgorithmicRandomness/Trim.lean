import KolmogorovMathlib.AlgorithmicRandomness.Disjointify

/-!
# Trimming an enumeration of intervals

Given a computable measure `μ` (with dyadic approximation `a`) and an
enumeration `e` of intervals, we build a subenumeration
`trimEnum e (trimWeight a e n)` such that

* the union of the selected intervals has measure at most `2⁻ⁿ`;
* if the total mass of the original intervals is at most `2⁻⁽ⁿ⁺²⁾`, then no
  interval is discarded.

This is the key construction behind the existence of a universal Martin-Lof
test (SUV Theorem 28).
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ## Dyadic arithmetic in multiplicative form -/

/-- `2^i · 2^{-i} = 1` in the extended nonnegative reals. -/
lemma nat_two_pow_mul_inv_two_pow (i : ℕ) :
    ((2 ^ i : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ i = 1 := by
  have hcast : ((2 ^ i : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ i := by
    push_cast
    rfl
  rw [hcast, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

/-- Doubling `2^{-(s+1)}` gives `2^{-s}`. -/
lemma two_mul_inv_two_pow_succ (s : ℕ) :
    (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (s + 1) = (2 : ℝ≥0∞)⁻¹ ^ s := by
  rw [pow_succ]
  rw [show (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ s * (2 : ℝ≥0∞)⁻¹)
      = ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * (2 : ℝ≥0∞)⁻¹ ^ s by ring]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Cancellation of a natural power of two against the dyadic denominator. -/
lemma nat_two_pow_mul_inv_two_pow_add (i j : ℕ) :
    ((2 ^ i : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (i + j) = (2 : ℝ≥0∞)⁻¹ ^ j := by
  rw [pow_add, ← mul_assoc, nat_two_pow_mul_inv_two_pow, one_mul]

/-- Two natural numbers scaled by the same negative power of two compare as they do. -/
lemma nat_le_of_mul_inv_two_pow_le {m M s : ℕ}
    (h : (m : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ s ≤ (M : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ s) : m ≤ M := by
  have hc : (2 : ℝ≥0∞)⁻¹ ^ s * (m : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ s * (M : ℝ≥0∞) := by
    rw [mul_comm ((2 : ℝ≥0∞)⁻¹ ^ s) (m : ℝ≥0∞), mul_comm ((2 : ℝ≥0∞)⁻¹ ^ s) (M : ℝ≥0∞)]
    exact h
  have h' : (m : ℝ≥0∞) ≤ (M : ℝ≥0∞) :=
    (ENNReal.mul_le_mul_iff_right (by simp) (ENNReal.pow_ne_top (by simp))).1 hc
  exact_mod_cast h'

/-- The geometric series `∑ₖ 2^{-(N+k+1)}` sums to `2^{-N}`. -/
lemma tsum_inv_two_pow_shift (N : ℕ) :
    ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (N + k + 1) = (2 : ℝ≥0∞)⁻¹ ^ N := by
  have hgeom : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (N + k + 1)
      = (2 : ℝ≥0∞)⁻¹ ^ (N + 1) * ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k := by
    rw [ENNReal.tsum_mul_left.symm]
    refine tsum_congr fun k => ?_
    rw [← pow_add]
    ring_nf
  rw [hgeom, ENNReal.tsum_geometric]
  have h2 : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by simp) ?_]
    · rw [ENNReal.inv_two_add_inv_two]
  rw [h2, pow_succ, mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

/-! ## The numerical trimming recursion -/

/-- Partial sums of the accepted approximate masses, as numerators over the
denominator `2 ^ (n + k + 2)` (the level `n` is implicit in the weights `w`). -/
def trimPartial (w : ℕ → ℕ) : ℕ → ℕ := fun k =>
  Nat.rec 0 (fun j IH => bif decide (2 * IH + w j ≤ 2 ^ (j + 2)) then 2 * IH + w j else 2 * IH) k

/-- The `k`-th interval is accepted if adding its approximate mass keeps the
running total below the threshold. -/
def trimAccept (w : ℕ → ℕ) (k : ℕ) : Bool :=
  decide (2 * trimPartial w k + w k ≤ 2 ^ (k + 2))

/-- The trimmed enumeration. -/
def trimEnum (e : ℕ → Option BitString) (w : ℕ → ℕ) (k : ℕ) : Option BitString :=
  bif trimAccept w k then e k else none

/-- Weights used for trimming: the approximate mass of the `j`-th interval,
computed with precision `n + j + 3`. -/
def trimWeight (a : BitString → ℕ → ℕ) (e : ℕ → Option BitString) (n : ℕ) (j : ℕ) : ℕ :=
  ((e j).map (fun u => a u (n + j + 3))).getD 0

/-- The trimming accumulator starts at zero. -/
lemma trimPartial_zero (w : ℕ → ℕ) : trimPartial w 0 = 0 := rfl

/-- A weight is accepted at stage `k` exactly when adding it keeps the accumulated mass below
the budget `2^{k+2}`. -/
lemma trimAccept_iff (w : ℕ → ℕ) (k : ℕ) :
    trimAccept w k = true ↔ 2 * trimPartial w k + w k ≤ 2 ^ (k + 2) := by
  unfold trimAccept
  simp

/-- The accumulator doubles at each stage and additionally absorbs the new weight when it is
accepted. -/
lemma trimPartial_succ (w : ℕ → ℕ) (k : ℕ) :
    trimPartial w (k + 1)
      = bif trimAccept w k then 2 * trimPartial w k + w k else 2 * trimPartial w k := rfl

/-- On an accepted stage the accumulator doubles and absorbs the new weight. -/
lemma trimPartial_succ_of_accept {w : ℕ → ℕ} {k : ℕ} (h : trimAccept w k = true) :
    trimPartial w (k + 1) = 2 * trimPartial w k + w k := by
  rw [trimPartial_succ, h, cond_true]

/-- On a rejected stage the accumulator merely doubles. -/
lemma trimPartial_succ_of_not_accept {w : ℕ → ℕ} {k : ℕ} (h : trimAccept w k = false) :
    trimPartial w (k + 1) = 2 * trimPartial w k := by
  rw [trimPartial_succ, h, cond_false]

/-- The accumulator stays below the budget `2^{k+1}`, which is what makes trimming keep the
total mass finite. -/
lemma trimPartial_le (w : ℕ → ℕ) (k : ℕ) : trimPartial w k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp [trimPartial_zero]
  | succ k ih =>
    cases hacc : trimAccept w k with
    | true =>
      rw [trimPartial_succ_of_accept hacc]
      exact (trimAccept_iff w k).1 hacc
    | false =>
      rw [trimPartial_succ_of_not_accept hacc]
      calc 2 * trimPartial w k ≤ 2 * 2 ^ (k + 1) := by omega
        _ = 2 ^ (k + 2) := by ring

/-- The accepted approximate mass of the `j`-th interval. -/
noncomputable def trimTerm (w : ℕ → ℕ) (n j : ℕ) : ℝ≥0∞ :=
  if trimAccept w j then (w j : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) else 0

/-- Splitting the numerator of the running total after one step. -/
lemma trim_step_value (w : ℕ → ℕ) (n k : ℕ) :
    ((2 * trimPartial w k + w k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
      = (trimPartial w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
        + (w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) := by
  have hshift : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) = (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2) := by
    have h := two_mul_inv_two_pow_succ (n + k + 2)
    rwa [show n + k + 2 + 1 = n + k + 3 by ring] at h
  have hcast : ((2 * trimPartial w k + w k : ℕ) : ℝ≥0∞)
      = 2 * (trimPartial w k : ℝ≥0∞) + (w k : ℝ≥0∞) := by
    push_cast
    ring
  calc ((2 * trimPartial w k + w k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
      = (trimPartial w k : ℝ≥0∞) * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3))
          + (w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) := by
        rw [hcast]; ring
    _ = (trimPartial w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
          + (w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) := by rw [hshift]

/-- The first `k` trimmed terms sum to the accumulator scaled by `2^{-(n+k+2)}`. -/
lemma sum_trimTerm (w : ℕ → ℕ) (n k : ℕ) :
    ∑ j ∈ Finset.range k, trimTerm w n j
      = (trimPartial w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2) := by
  induction k with
  | zero => simp [trimPartial_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show n + (k + 1) + 2 = n + k + 3 by ring]
    cases hacc : trimAccept w k with
    | true =>
      rw [trimPartial_succ_of_accept hacc, trim_step_value]
      unfold trimTerm
      rw [hacc]
      simp
    | false =>
      rw [trimPartial_succ_of_not_accept hacc]
      unfold trimTerm
      rw [hacc]
      simp only [Bool.false_eq_true, if_false, add_zero]
      have hshift : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) = (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2) := by
        have h := two_mul_inv_two_pow_succ (n + k + 2)
        rwa [show n + k + 2 + 1 = n + k + 3 by ring] at h
      have hcast : ((2 * trimPartial w k : ℕ) : ℝ≥0∞) = 2 * (trimPartial w k : ℝ≥0∞) := by
        push_cast
        ring
      rw [hcast, show (2 : ℝ≥0∞) * (trimPartial w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
        = (trimPartial w k : ℝ≥0∞) * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)) by ring, hshift]

/-- The scaled accumulator never exceeds `2^{-(n+1)}`. -/
lemma trimPartial_mul_le (w : ℕ → ℕ) (n k : ℕ) :
    (trimPartial w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  have hcast : ((trimPartial w k : ℕ) : ℝ≥0∞) ≤ ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast trimPartial_le w k
  have hidx : n + k + 2 = (k + 1) + (n + 1) := by ring
  calc (trimPartial w k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
      ≤ ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2) := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
        rw [hidx, nat_two_pow_mul_inv_two_pow_add]

/-- The trimmed terms have total mass at most `2^{-(n+1)}`. -/
lemma tsum_trimTerm_le (w : ℕ → ℕ) (n : ℕ) :
    ∑' j, trimTerm w n j ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun k => ?_
  rw [sum_trimTerm]
  exact trimPartial_mul_le w n k

/-! ## The measure of the trimmed union -/

variable {μ : Measure CantorSeq}

/-- Each set of the trimmed enumeration has measure at most its trimmed weight plus the
approximation error `2^{-(n+k+3)}`. -/
lemma measure_coverSet_trimEnum_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (e : ℕ → Option BitString) (n k : ℕ) :
    μ (coverSet (trimEnum e (trimWeight a e n)) k)
      ≤ trimTerm (trimWeight a e n) n k + (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) := by
  set w := trimWeight a e n with hw
  rw [measure_coverSet]
  unfold trimEnum
  cases hacc : trimAccept w k with
  | false => simp
  | true =>
    simp only [cond_true]
    unfold trimTerm
    rw [hacc]
    simp only [if_true]
    cases hek : e k with
    | none => simp
    | some u =>
      simp only [Option.elim_some]
      have hwk : w k = a u (n + k + 3) := by
        rw [hw]
        simp [trimWeight, hek]
      have hub := (ha u (n + k + 3)).2
      rw [dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow] at hub
      rw [hwk]
      simpa using hub

/-- The trimmed union always has measure at most `2⁻ⁿ`. -/
theorem measure_iUnion_trimEnum_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (e : ℕ → Option BitString) (n : ℕ) :
    μ (⋃ k, coverSet (trimEnum e (trimWeight a e n)) k) ≤ dyadicValue 1 n := by
  set w := trimWeight a e n with hw
  refine (measure_iUnion_le _).trans ?_
  refine (ENNReal.tsum_le_tsum (fun k => measure_coverSet_trimEnum_le ha e n k)).trans ?_
  rw [ENNReal.tsum_add]
  have hgeom : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) = (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
    have h := tsum_inv_two_pow_shift (n + 2)
    have hidx : ∀ k : ℕ, n + 2 + k + 1 = n + k + 3 := fun k => by ring
    calc ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
        = ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + k + 1) := by
          exact tsum_congr fun k => by rw [hidx k]
      _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := h
  rw [hgeom]
  have hbound : ∑' j, trimTerm w n j + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
    gcongr
    exact tsum_trimTerm_le w n
  refine hbound.trans ?_
  rw [dyadicValue_one_eq_inv_two_pow']
  have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      = (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) := by
    rw [pow_succ, pow_succ, pow_succ]
    ring
  rw [hsplit]
  have hle : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ 1 := by
    have h1 : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := by
      calc (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ 1 * (2 : ℝ≥0∞)⁻¹ := by
            gcongr
            exact ENNReal.inv_le_one.2 (by norm_num)
        _ = (2 : ℝ≥0∞)⁻¹ := one_mul _
    calc (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by gcongr
      _ = 1 := ENNReal.inv_two_add_inv_two
  calc (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ n * 1 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := mul_one _

/-! ## Nothing is discarded when the total mass is small -/

/-- The scaled trimming weight of an enumerated string is bounded by the measure of its cylinder
plus the approximation error. -/
lemma trimWeight_mul_le_mass {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (e : ℕ → Option BitString) (n j : ℕ) :
    (trimWeight a e n j : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)
      ≤ (e j).elim 0 (cantorMass μ) + (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
  cases hej : e j with
  | none => simp [trimWeight, hej]
  | some u =>
    have hwj : trimWeight a e n j = a u (n + j + 3) := by
      simp [trimWeight, hej]
    have hlb := (ha u (n + j + 3)).1
    rw [dyadicValue_eq_mul_inv_pow, dyadicValue_one_eq_inv_two_pow'] at hlb
    rw [hwj]
    simpa using hlb

/-- The step of the trimming recursion: if the accepted mass so far is bounded by
the true mass of the first `k` intervals, then the `k`-th interval is accepted
too, and the bound propagates. -/
lemma trimAccept_of_partial_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {e : ℕ → Option BitString} {n : ℕ}
    (hsmall : (∑' j, (e j).elim 0 (cantorMass μ)) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) {k : ℕ}
    (hpart : (trimPartial (trimWeight a e n) k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
      ≤ ∑ j ∈ Finset.range k, (e j).elim 0 (cantorMass μ)
        + ∑ j ∈ Finset.range k, (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)) :
    trimAccept (trimWeight a e n) k = true ∧
      ((2 * trimPartial (trimWeight a e n) k + trimWeight a e n k : ℕ) : ℝ≥0∞)
        * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
        ≤ ∑ j ∈ Finset.range (k + 1), (e j).elim 0 (cantorMass μ)
          + ∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
  set w := trimWeight a e n with hw
  have hstep : ((2 * trimPartial w k + w k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
      ≤ ∑ j ∈ Finset.range (k + 1), (e j).elim 0 (cantorMass μ)
        + ∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
    rw [trim_step_value, Finset.sum_range_succ, Finset.sum_range_succ, add_add_add_comm]
    exact add_le_add hpart (trimWeight_mul_le_mass ha e n k)
  refine ⟨?_, hstep⟩
  rw [trimAccept_iff]
  refine nat_le_of_mul_inv_two_pow_le (s := n + k + 3) ?_
  refine hstep.trans ?_
  have hmass : (∑ j ∈ Finset.range (k + 1), (e j).elim 0 (cantorMass μ))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2) :=
    (ENNReal.sum_le_tsum _).trans hsmall
  have hslack : (∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
    refine (ENNReal.sum_le_tsum _).trans ?_
    have hidx : ∀ j : ℕ, n + 2 + j + 1 = n + j + 3 := fun j => by ring
    calc ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)
        = ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + j + 1) := tsum_congr fun j => by rw [hidx j]
      _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := tsum_inv_two_pow_shift (n + 2)
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := le_rfl
  have hsum2 : (2 : ℝ≥0∞)⁻¹ ^ (n + 2) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
    have h := two_mul_inv_two_pow_succ (n + 1)
    rw [show n + 1 + 1 = n + 2 by ring] at h
    rw [← h]
    ring
  have hcancel : ((2 ^ (k + 2) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
      = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
    rw [show n + k + 3 = (k + 2) + (n + 1) by ring, nat_two_pow_mul_inv_two_pow_add]
  rw [hcancel]
  calc ∑ j ∈ Finset.range (k + 1), (e j).elim 0 (cantorMass μ)
        + ∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := add_le_add hmass hslack
    _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := hsum2

/-- For an enumeration of small total mass, the scaled accumulator is bounded by the mass of the
first `k` sets plus the accumulated approximation errors. -/
lemma trimPartial_mul_le_sum_mass {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {e : ℕ → Option BitString} {n : ℕ}
    (hsmall : (∑' j, (e j).elim 0 (cantorMass μ)) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) (k : ℕ) :
    (trimPartial (trimWeight a e n) k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
      ≤ ∑ j ∈ Finset.range k, (e j).elim 0 (cantorMass μ)
        + ∑ j ∈ Finset.range k, (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
  induction k with
  | zero => simp [trimPartial_zero]
  | succ k ih =>
    obtain ⟨hacc, hstep⟩ := trimAccept_of_partial_le ha hsmall ih
    rw [trimPartial_succ_of_accept hacc, show n + (k + 1) + 2 = n + k + 3 by ring]
    exact hstep

/-- If the total mass of the intervals is at most `2⁻⁽ⁿ⁺²⁾`, trimming discards
nothing. -/
theorem trimEnum_eq_self_of_tsum_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {e : ℕ → Option BitString} {n : ℕ}
    (hsmall : (∑' j, (e j).elim 0 (cantorMass μ)) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) (k : ℕ) :
    trimEnum e (trimWeight a e n) k = e k := by
  have hacc := (trimAccept_of_partial_le ha hsmall
    (trimPartial_mul_le_sum_mass ha hsmall k)).1
  unfold trimEnum
  rw [hacc, cond_true]

/-! ## Computability of the trimmed enumeration -/

/-- The trimming accumulator is computable in the weight family and the stage. -/
lemma computable_trimPartial {W : ℕ → ℕ → ℕ} (hW : Computable₂ W) :
    Computable₂ (fun m k => trimPartial (W m) k) := by
  have hstep : Computable₂ (fun (q : ℕ × ℕ) (p : ℕ × ℕ) =>
      bif decide (2 * p.2 + W q.1 p.1 ≤ 2 ^ (p.1 + 2)) then 2 * p.2 + W q.1 p.1 else 2 * p.2) := by
    have hW' : Computable (fun r : (ℕ × ℕ) × (ℕ × ℕ) => W r.1.1 r.2.1) :=
      hW.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
    have htwice : Computable (fun r : (ℕ × ℕ) × (ℕ × ℕ) => 2 * r.2.2) :=
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to_comp
    have hsum : Computable (fun r : (ℕ × ℕ) × (ℕ × ℕ) => 2 * r.2.2 + W r.1.1 r.2.1) :=
      Primrec.nat_add.to_comp.comp htwice hW'
    have hpow : Computable (fun r : (ℕ × ℕ) × (ℕ × ℕ) => 2 ^ (r.2.1 + 2)) :=
      (primrec_two_pow_aux.comp
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))).to_comp
    have hcond : Computable (fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
        decide (2 * r.2.2 + W r.1.1 r.2.1 ≤ 2 ^ (r.2.1 + 2))) :=
      computable₂_decide_le.comp hsum hpow
    exact Computable.cond hcond hsum htwice
  exact Computable.nat_rec Computable.snd (Computable.const 0) hstep

/-- The trimming weights are computable in the measure approximation, the enumeration and the
level. -/
lemma computable_trimWeight {a : BitString → ℕ → ℕ} (ha : Computable₂ a)
    {E : ℕ → ℕ → Option BitString} (hE : Computable₂ E) {L : ℕ → ℕ} (hL : Computable L) :
    Computable₂ (fun m j => trimWeight a (E m) (L m) j) := by
  have hidx : Computable (fun r : (ℕ × ℕ) × BitString => L r.1.1 + r.1.2 + 3) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (hL.comp (Computable.fst.comp Computable.fst))
        (Computable.snd.comp Computable.fst))
      (Computable.const 3)
  have hval : Computable₂ (fun (q : ℕ × ℕ) (u : BitString) => a u (L q.1 + q.2 + 3)) :=
    ha.comp Computable.snd hidx
  have hmap : Computable (fun q : ℕ × ℕ =>
      (E q.1 q.2).map (fun u => a u (L q.1 + q.2 + 3))) :=
    Computable.option_map hE hval
  exact Computable.option_getD hmap (Computable.const 0)

/-- The trimming acceptance test is computable. -/
lemma computable_trimAccept {W : ℕ → ℕ → ℕ} (hW : Computable₂ W) :
    Computable₂ (fun m k => trimAccept (W m) k) := by
  have hP : Computable (fun q : ℕ × ℕ => trimPartial (W q.1) q.2) := computable_trimPartial hW
  have htwice : Computable (fun q : ℕ × ℕ => 2 * trimPartial (W q.1) q.2) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) hP
  have hsum : Computable (fun q : ℕ × ℕ => 2 * trimPartial (W q.1) q.2 + W q.1 q.2) :=
    Primrec.nat_add.to_comp.comp htwice hW
  have hpow : Computable (fun q : ℕ × ℕ => 2 ^ (q.2 + 2)) :=
    (primrec_two_pow_aux.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))).to_comp
  exact computable₂_decide_le.comp hsum hpow

/-- The trimmed enumeration is computable in the original enumeration and the weights. -/
lemma computable_trimEnum {E : ℕ → ℕ → Option BitString} (hE : Computable₂ E)
    {W : ℕ → ℕ → ℕ} (hW : Computable₂ W) :
    Computable₂ (fun m k => trimEnum (E m) (W m) k) :=
  Computable.cond (computable_trimAccept hW) hE (Computable.const none)

end Kolmogorov
