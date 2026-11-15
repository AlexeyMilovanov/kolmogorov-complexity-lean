/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.Defs

/-!
# Schnorr Series

A sequence `ω` is not Schnorr random for a computable probability measure `π` exactly when
there is a computable sequence of strings `x_i` whose masses `π(x_i)` have a computably
convergent sum and infinitely many of which are prefixes of `ω`.

The main declarations are `not_isSchnorrRandom_iff_exists_series_mp`, the forward implication,
and `not_isSchnorrRandom_iff_exists_series`, the equivalence (SUV Problem 90 of Section 3.4,
used on p. 282).  The remaining lemmas are private auxiliary steps, including the approximation
of the masses by computable dyadic rationals.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

private lemma not_isSchnorrRandom_iff_exists_series_sum_computable
    (M : ℕ → ℕ → ℕ) (hM : Computable₂ M) :
    Computable₂ (fun k t => ∑ n ∈ Finset.range t, M n (2*k+6)) := by
  have hp : Computable (fun p : ℕ × ℕ => 2*p.1+6) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable₂.comp Primrec.nat_mul.to_comp
        (Computable.const 2) Computable.fst)
      (Computable.const 6)
  have ht : Computable
      (fun r : (ℕ × ℕ) × (ℕ × ℕ) => M r.2.1 (2*r.1.1+6)) :=
    Computable₂.comp hM (Computable.fst.comp Computable.snd)
      (hp.comp Computable.fst)
  have hs : Computable₂
      (fun (p : ℕ × ℕ) (u : ℕ × ℕ) => u.2 + M u.1 (2*p.1+6)) :=
    Computable₂.comp Primrec.nat_add.to_comp
      (Computable.snd.comp Computable.snd) ht
  have hr := Computable.nat_rec
    (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ => (0 : ℕ))
    (h := fun p u => u.2 + M u.1 (2*p.1+6))
    Computable.snd (Computable.const 0) hs
  have key : ∀ k t : ℕ,
      Nat.rec (motive := fun _ => ℕ) 0
        (fun n s => s + M n (2*k+6)) t =
          ∑ n ∈ Finset.range t, M n (2*k+6) := by
    intro k t
    induction t with
    | zero => simp
    | succ t ih => simp [Finset.sum_range_succ, ih, add_comm]
  exact hr.of_eq (fun p => key p.1 p.2)

/-- Step 2 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: computable. -/
private lemma not_isSchnorrRandom_iff_exists_series_computable
    (M : ℕ → ℕ → ℕ) (hM_comp : Computable₂ M) :
    Computable (fun k : ℕ =>
      (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2) := by
  have hk4 : Computable (fun k : ℕ => k + 4) :=
    Computable₂.comp Primrec.nat_add.to_comp Computable.id (Computable.const 4)
  have h_sum_base : Computable₂ (fun (k t : ℕ) => ∑ n ∈ Finset.range t, M n (2 * k + 6)) :=
    not_isSchnorrRandom_iff_exists_series_sum_computable M hM_comp
  have h_sum : Computable (fun k : ℕ => ∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) :=
    h_sum_base.comp Computable.id hk4
  have h_add1 : Computable (fun k : ℕ => k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6))) :=
    Computable₂.comp Primrec.nat_add.to_comp hk4 h_sum
  have h_add2 : Computable (fun k : ℕ => k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1)
      :=
    Computable₂.comp Primrec.nat_add.to_comp h_add1 (Computable.const 1)
  have h_sq : Computable (fun k : ℕ => (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^
                                         2) := by
    have h_sq_comp : Computable (fun x : ℕ => x ^ 2) :=
      (Computable₂.comp Primrec.nat_mul.to_comp Computable.id Computable.id).of_eq
          (fun x => by simp [sq])
    exact h_sq_comp.comp h_add2
  exact h_sq

/-- Step 3 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: unpair injectivity. -/
private lemma not_isSchnorrRandom_iff_exists_series_unpair (N : ℕ) :
    Function.Injective (fun i => Nat.unpair (N + i)) := by
  intro a b hab
  have h1 := congr_arg (fun p => Nat.pair p.1 p.2) hab
  simp at h1
  omega

/-- Step 4 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: bound. -/
private lemma not_isSchnorrRandom_iff_exists_series_bound
    (M : ℕ → ℕ → ℕ) (k : ℕ) (n i : ℕ)
    (h_pair : (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2 ≤ Nat.pair n i) :
    k + 4 ≤ n ∨ M n (2 * k + 6) ≤ i := by
  by_contra! h
  rcases h with ⟨hn, hi⟩
  have h_max : max n i < k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) := by
    rw [max_lt_iff]
    constructor
    · exact hn.trans_le (Nat.le_add_right _ _)
    · apply hi.trans_le
      have h1 : M n (2 * k + 6) ≤ ∑ x ∈ Finset.range (k + 4), M x (2 * k + 6) := by
        exact @Finset.single_le_sum _ _ _ _ (fun x => M x (2 * k + 6)) _ _
            (fun _ _ => Nat.zero_le _) _ (Finset.mem_range.mpr hn)
      exact h1.trans (Nat.le_add_left _ _)
  have h_sq : (max n i + 1) ^ 2 ≤ (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2 :=
      by
    apply Nat.pow_le_pow_left
    omega
  have h_pair_lt : Nat.pair n i < (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2 :=
      by
    calc Nat.pair n i < (max n i + 1) ^ 2 := Nat.pair_lt_max_add_one_sq n i
         _            ≤ (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2 := h_sq
  omega

/-- Step 5 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: row tail. -/
private theorem not_isSchnorrRandom_iff_exists_series_row_tail
    (a : ℕ → ℝ≥0∞) (L : ℕ) :
    (∑' i, if L ≤ i then a i else 0) =
      ∑' i, a (L+i) := by
  have h2 := Summable.sum_add_tsum_nat_add' (k := L) (f := fun i => if L ≤ i then a i else 0)
      ENNReal.summable
  rw [← h2]
  have h4 : (∑ i ∈ Finset.range L, (if L ≤ i then a i else 0 : ℝ≥0∞)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h5 : ¬(L ≤ i) := by
      have : i < L := Finset.mem_range.mp hi
      omega
    simp [h5]
  rw [h4, zero_add]
  exact congr_arg tsum (funext fun i => by
    have h5 : L ≤ i + L := Nat.le_add_left L i
    simp [add_comm])


/-- Step 6 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: split. -/
private theorem not_isSchnorrRandom_iff_exists_series_split
    (a : ℕ → ℕ → ℝ≥0∞) (L : ℕ → ℕ) (K J : ℕ)
    (hescape : ∀ j, J ≤ j →
      K ≤ (Nat.unpair j).1 ∨
      L (Nat.unpair j).1 ≤ (Nat.unpair j).2) :
    (∑' i, a (Nat.unpair (J + i)).1 (Nat.unpair (J + i)).2) ≤
      (∑ n ∈ Finset.range K, ∑' i, a n (L n + i)) +
      ∑' n, ∑' i, a (K + n) i := by
  have H : (∑' (p : ℕ × ℕ), (if K ≤ p.1 ∨ L p.1 ≤ p.2 then a p.1 p.2 else 0 : ENNReal)) =
           ∑' (n : ℕ) (i : ℕ), (if K ≤ n ∨ L n ≤ i then a n i else 0 : ENNReal) :=
    ENNReal.tsum_prod (f := fun (n : ℕ) (i : ℕ) => if K ≤ n ∨ L n ≤ i then a n i else 0)
  have hinj : Function.Injective (fun i => Nat.unpair (J + i)) := by
    intro u v huv
    have h1 := congr_arg (fun p => Nat.pair p.1 p.2) huv
    simp at h1
    omega
  have H2 := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun p : ℕ ×
      ℕ => if K ≤ p.1 ∨ L p.1 ≤ p.2 then a p.1 p.2 else 0)
  have H3 : (∑' i, a (Nat.unpair (J + i)).1 (Nat.unpair (J + i)).2) ≤ ∑' i,
      (if K ≤ (Nat.unpair (J + i)).1 ∨ L (Nat.unpair (J + i)).1 ≤ (Nat.unpair (J + i)).2 then
        a (Nat.unpair (J + i)).1 (Nat.unpair (J + i)).2 else 0 : ENNReal) := by
    apply ENNReal.tsum_le_tsum
    intro i
    have h4 : K ≤ (Nat.unpair (J + i)).1 ∨ L (Nat.unpair (J + i)).1 ≤ (Nat.unpair (J + i)).2 :=
        hescape (J + i) (Nat.le_add_right J i)
    exact ite_eq_left_iff.mpr (fun h_not => False.elim (h_not h4)) ▸ le_rfl
  have H4 := H3.trans H2
  have h_split : (∑' (n : ℕ) (i : ℕ), (if K ≤ n ∨ L n ≤ i then a n i else 0 : ENNReal))
    = (∑ n ∈ Finset.range K, ∑' (i : ℕ), if L n ≤ i then a n i else 0) +
      (∑' (n : ℕ), ∑' (i : ℕ), a (K + n) i) := by
    have h2 := Summable.sum_add_tsum_nat_add' (k := K) (f := fun n => ∑' (i : ℕ),
        (if K ≤ n ∨ L n ≤ i then a n i else 0 : ENNReal)) ENNReal.summable
    rw [← h2]
    apply congr_arg₂
    · apply Finset.sum_congr rfl
      intro n hn
      have hn_lt : n < K := Finset.mem_range.mp hn
      have h3 : ∀ i, (if K ≤ n ∨ L n ≤ i then a n i else 0 : ENNReal) = if L n ≤ i then a n i else
        0 := by
        intro i
        have h4 : ¬ (K ≤ n) := by omega
        have h5 : (K ≤ n ∨ L n ≤ i) ↔ L n ≤ i := or_iff_right h4
        simp only [h5]
      apply tsum_congr
      exact h3
    · have h4 : (fun n => ∑' (i : ℕ), (if K ≤ K + n ∨ L (K + n) ≤ i then a (K + n) i else
        0 : ENNReal)) = fun n => ∑' (i : ℕ), a (K + n) i := by
        funext n
        have h5 : (fun i => (if K ≤ K + n ∨ L (K + n) ≤ i then a (K + n) i else 0 : ENNReal)) =
            fun i => a (K + n) i := by
          funext i
          have h6 : K ≤ K + n := Nat.le_add_right K n
          simp [h6]
        rw [h5]
      apply tsum_congr
      intro n
      apply tsum_congr
      intro i
      have hnK : K ≤ n + K := Nat.le_add_left K n
      have h_or : K ≤ n + K ∨ L (n + K) ≤ i := Or.inl hnK
      have hk_n : K + n = n + K := Nat.add_comm K n
      rw [hk_n]
      exact ite_eq_left_iff.mpr (fun h => False.elim (h h_or))
  have h_bound_1 : (∑ n ∈ Finset.range K, ∑' (i : ℕ), if L n ≤ i then a n i else 0) = ∑ n ∈
      Finset.range K, ∑' (i : ℕ), a n (L n + i) := by
    apply Finset.sum_congr rfl
    intro n _
    exact not_isSchnorrRandom_iff_exists_series_row_tail (a n) (L n)
  rw [← h_bound_1, ← h_split, ← H]
  exact H4

/-- Step 7 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: numeric. -/
private theorem not_isSchnorrRandom_iff_exists_series_numeric (k : ℕ)
    :
    (k+4 : ℝ≥0∞) * dyadicValue 1 (2*k+6) +
      (∑' n, (5 : ℝ≥0∞) * dyadicValue 1 (k+4+n)) ≤
      dyadicValue 1 k := by
  simp only [dyadicValue_one_eq_inv_two_pow']
  have h_nat : k + 4 ≤ 3 * 2 ^ (k + 3) := by
    have hk := Kolmogorov.k_le_two_pow_k k
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc k + 4 ≤ 2 ^ k + 4 * 1 := by omega
      _ ≤ 2 ^ k + 4 * 2 ^ k := by omega
      _ = 5 * 2 ^ k := by ring
      _ ≤ 24 * 2 ^ k := by omega
      _ = 3 * (8 * 2 ^ k) := by ring
      _ = 3 * (2 ^ 3 * 2 ^ k) := by norm_num
      _ = 3 * 2 ^ (3 + k) := by
        congr 2
        exact (pow_add 2 3 k).symm
      _ = 3 * 2 ^ (k + 3) := by
        congr 2
        rw [add_comm]
  have H_bound_1 : (k + 4 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (2 * k + 6) ≤ 6 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by
    calc (k + 4 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (2 * k + 6) ≤ (3 * 2 ^ (k + 3) : ℕ) * (2:ℝ≥0∞)⁻¹ ^
        (2 * k + 6) := by
          gcongr
          exact_mod_cast h_nat
      _ = (3:ℝ≥0∞) * ((2:ℝ≥0∞) ^ (k + 3) * (2:ℝ≥0∞)⁻¹ ^ (k + 3 + (k + 3))) := by
        have H_power : 2 * k + 6 = k + 3 + (k + 3) := by omega
        rw [H_power]
        push_cast
        ring
      _ = (3:ℝ≥0∞) * ((2:ℝ≥0∞) ^ (k + 3) * ((2:ℝ≥0∞)⁻¹ ^ (k + 3) * (2:ℝ≥0∞)⁻¹ ^ (k + 3))) := by
        congr 2
        rw [pow_add]
      _ = (3:ℝ≥0∞) * (((2:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹) ^ (k + 3) * (2:ℝ≥0∞)⁻¹ ^ (k + 3)) := by
        congr 1
        rw [← mul_assoc]
        congr 1
        rw [mul_pow]
      _ = (3:ℝ≥0∞) * (1 ^ (k + 3) * (2:ℝ≥0∞)⁻¹ ^ (k + 3)) := by
        congr 2
        congr 1
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      _ = (3:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 3) := by simp
      _ = (3:ℝ≥0∞) * ((2:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹) * (2:ℝ≥0∞)⁻¹ ^ (k + 3) := by
        congr 1
        have H_one : (2:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [H_one, mul_one]
      _ = ((3:ℝ≥0∞) * (2:ℝ≥0∞)) * ((2:ℝ≥0∞)⁻¹ * (2:ℝ≥0∞)⁻¹ ^ (k + 3)) := by ring
      _ = 6 * ((2:ℝ≥0∞)⁻¹ ^ 1 * (2:ℝ≥0∞)⁻¹ ^ (k + 3)) := by
        congr 1
        · norm_num
        · rw [pow_one]
      _ = 6 * (2:ℝ≥0∞)⁻¹ ^ (1 + (k + 3)) := by
        congr 1
        exact (pow_add (2:ℝ≥0∞)⁻¹ 1 (k + 3)).symm
      _ = 6 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by
        congr 2
        omega
  have H_sum : ∑' n, (5 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4 + n) = (5:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4) *
      (2:ℝ≥0∞) := by
    calc
      ∑' n, (5 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4 + n) = ∑' n, (5 : ℝ≥0∞) * ((2:ℝ≥0∞)⁻¹ ^ (k + 4) *
          (2:ℝ≥0∞)⁻¹ ^ n) := by
        congr 1
        ext n
        rw [pow_add]
      _ = ∑' n, ((5 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4)) * (2:ℝ≥0∞)⁻¹ ^ n := by
        congr 1
        ext n
        rw [mul_assoc]
      _ = ((5 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4)) * ∑' n, (2:ℝ≥0∞)⁻¹ ^ n := by
        rw [ENNReal.tsum_mul_left]
      _ = ((5 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4)) * (2:ℝ≥0∞) := by
        congr 2
        exact ENNReal.tsum_geometric_two
  rw [H_sum]
  have H_sum_2 : (5:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4) * (2:ℝ≥0∞) = 10 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by
    calc
      (5:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4) * (2:ℝ≥0∞) = (5:ℝ≥0∞) * (2:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by
        ring
      _ = 10 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by norm_num
  rw [H_sum_2]
  have H_final : 6 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) + 10 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) ≤ (2:ℝ≥0∞)⁻¹ ^ k := by
    calc
      6 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) + 10 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) = 16 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by ring
      _ = 2 ^ 4 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by norm_num
      _ = (2:ℝ≥0∞) ^ 4 * (2:ℝ≥0∞)⁻¹ ^ (k + 4) := by norm_num
      _ = (2:ℝ≥0∞) ^ 4 * ((2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ 4) := by
        congr 1
        rw [pow_add]
      _ = (2:ℝ≥0∞) ^ 4 * (2:ℝ≥0∞)⁻¹ ^ 4 * (2:ℝ≥0∞)⁻¹ ^ k := by ring
      _ = ((2:ℝ≥0∞) * (2:ℝ≥0∞)⁻¹) ^ 4 * (2:ℝ≥0∞)⁻¹ ^ k := by
        rw [mul_pow]
      _ = 1 ^ 4 * (2:ℝ≥0∞)⁻¹ ^ k := by
        congr 2
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      _ = (2:ℝ≥0∞)⁻¹ ^ k := by norm_num
      _ ≤ (2:ℝ≥0∞)⁻¹ ^ k := by exact le_rfl
  exact (add_le_add H_bound_1 (le_refl _)).trans H_final

/-- Step 8 of the proof of
`not_isSchnorrRandom_iff_exists_series_enumerate`: mass bound. -/
private lemma not_isSchnorrRandom_iff_exists_series_mass_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (g : ℕ → ℕ → BitString) (M : ℕ → ℕ → ℕ)
    (hg_bound : ∀ n, ∑' i, cantorMass π (g n i) ≤ 5 * dyadicValue 1 n)
    (hM_bound : ∀ n k, ∑' i, cantorMass π (g n (M n k + i)) ≤ dyadicValue 1 k)
    (k : ℕ) :
    ∑' i, cantorMass π
      (g (Nat.unpair ((k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2 + i)).1
        (Nat.unpair ((k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2 + i)).2)
      ≤ dyadicValue 1 k := by
  let J := (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2
  have H := not_isSchnorrRandom_iff_exists_series_split
      (fun n i => cantorMass π (g n i)) (fun n => M n (2 * k + 6)) (k + 4) J
      (fun j hj => not_isSchnorrRandom_iff_exists_series_bound M k
                     (Nat.unpair j).1 (Nat.unpair j).2 (by
    have h1 : Nat.pair (Nat.unpair j).1 (Nat.unpair j).2 = j := Nat.pair_unpair j
    rw [h1]
    exact hj))
  have h_bound_1 : (∑ n ∈ Finset.range (k + 4), ∑' (i : ℕ), cantorMass π
      (g n (M n (2 * k + 6) + i))) ≤ (k + 4 : ENNReal) * dyadicValue 1 (2 * k + 6) := by
    calc (∑ n ∈ Finset.range (k + 4), ∑' (i : ℕ), cantorMass π (g n (M n (2 * k + 6) + i)))
           ≤ ∑ n ∈ Finset.range (k + 4), dyadicValue 1 (2 * k + 6) := by
               apply Finset.sum_le_sum
               intro n _
               exact hM_bound n (2 * k + 6)
         _ = (k + 4 : ENNReal) * dyadicValue 1 (2 * k + 6) := by
               simp
  have h_bound_2 : (∑' (n : ℕ), ∑' (i : ℕ), cantorMass π (g (k + 4 + n) i)) ≤ ∑' n, (5 : ℝ≥0∞) *
      dyadicValue 1 (k + 4 + n) := by
    apply ENNReal.tsum_le_tsum
    intro n
    exact hg_bound (k + 4 + n)
  have h_bound_3 : (∑ n ∈ Finset.range (k + 4), ∑' i, cantorMass π (g n (M n (2 * k + 6) + i))) +
      ∑' (n : ℕ), ∑' (i : ℕ), cantorMass π (g (k + 4 + n) i) ≤ dyadicValue 1 k := by
    have h1 := add_le_add h_bound_1 h_bound_2
    exact h1.trans (not_isSchnorrRandom_iff_exists_series_numeric k)
  exact H.trans h_bound_3

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_series_mp`: enumerate. -/
private lemma not_isSchnorrRandom_iff_exists_series_enumerate {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (g : ℕ → ℕ → BitString) (M : ℕ → ℕ → ℕ) (hM_comp : Computable₂ M)
    (hg_bound : ∀ n, ∑' i, cantorMass π (g n i) ≤ 5 * dyadicValue 1 n)
    (hM_bound : ∀ n k, ∑' i, cantorMass π (g n (M n k + i)) ≤ dyadicValue 1 k) :
    ∃ N : ℕ → ℕ, Computable N ∧ ∀ k, ∑' i, cantorMass π
      (g (Nat.unpair (N k + i)).1 (Nat.unpair (N k + i)).2) ≤ dyadicValue 1 k := by
  use fun k => (k + 4 + (∑ n ∈ Finset.range (k + 4), M n (2 * k + 6)) + 1) ^ 2
  refine ⟨not_isSchnorrRandom_iff_exists_series_computable M hM_comp,
      ?_⟩
  intro k
  exact not_isSchnorrRandom_iff_exists_series_mass_bound g M hg_bound
      hM_bound k


/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_series_mp`: prefixes. -/
private lemma not_isSchnorrRandom_iff_exists_series_prefixes {w : CantorSeq}
    (g : ℕ → ℕ → BitString) (hg_cover : ∀ n, {w} ⊆ ⋃ i, cantorCylinder (g n i)) :
    ∃ᶠ i in atTop, IsCantorPrefix (g (Nat.unpair i).1 (Nat.unpair i).2) w := by
  rw [Filter.frequently_atTop]
  intro a
  have h_mem := hg_cover a (Set.mem_singleton w)
  have h_union := Set.mem_iUnion.mp h_mem
  obtain ⟨i, hi⟩ := h_union
  use Nat.pair a i
  refine ⟨Nat.left_le_pair a i, ?_⟩
  simp only [Nat.unpair_pair]
  exact hi

/-- Step 5 of the proof of `not_isSchnorrRandom_iff_exists_series_mp`: computable.
-/
private lemma not_isSchnorrRandom_iff_exists_series_mp_computable (g : ℕ → ℕ →
    BitString)
    (hg_comp : Computable₂ g) : Computable fun i => g (Nat.unpair i).1 (Nat.unpair i).2 := by
  have H : Computable (fun (i : ℕ) => Nat.unpair i) := Computable.unpair
  have h1 : Computable (fun (i : ℕ) => (Nat.unpair i).1) := Computable.fst.comp H
  have h2 : Computable (fun (i : ℕ) => (Nat.unpair i).2) := Computable.snd.comp H
  exact (hg_comp.comp h1 h2 : _)

/-- If `ω` is not Schnorr random for the computable measure `π`, then there is a computable
sequence of strings with computably convergent mass sum and infinitely many prefixes of `ω`. -/
theorem not_isSchnorrRandom_iff_exists_series_mp {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (w : CantorSeq) :
    ¬ IsSchnorrRandom π w → ∃ x : ℕ → BitString, Computable x ∧
      (∃ N : ℕ → ℕ, Computable N ∧ ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) ∧
      ∃ᶠ i in atTop, IsCantorPrefix (x i) w := by
  intro hnotschnorr
  have h_null : IsSchnorrNull π {w} := not_not.mp hnotschnorr
  obtain ⟨f, hf_comp, hf_cover, hf_bound, hf_real⟩ := h_null
  obtain ⟨g, hg_comp, hg_cover, hg_bound, hg_eq, hg_junk⟩ :=
      not_isSchnorrRandom_iff_exists_series_totalize hπ f hf_comp hf_cover hf_bound
  obtain ⟨M, hM_comp, hM_bound⟩ := not_isSchnorrRandom_iff_exists_series_moduli hπ f
      g hf_comp hf_bound hf_real hg_eq hg_junk
  obtain ⟨N, hN_comp, hN_bound⟩ := not_isSchnorrRandom_iff_exists_series_enumerate g
      M hM_comp hg_bound (fun n k ↦ (hM_bound n k).2)
  use fun i ↦ g (Nat.unpair i).1 (Nat.unpair i).2
  refine ⟨not_isSchnorrRandom_iff_exists_series_mp_computable g hg_comp, ?_⟩
  refine ⟨⟨N, hN_comp, hN_bound⟩, ?_⟩
  exact not_isSchnorrRandom_iff_exists_series_prefixes g hg_cover


/-- Step 1 of the proof of `not_isSchnorrRandom_iff_exists_series_mpr`: f is
computable -/
private theorem not_isSchnorrRandom_iff_exists_series_f_comp {x : ℕ → BitString}
    {N : ℕ → ℕ} (hx : Computable x) (hN : Computable N) :
    Computable₂ (fun n i => (some (x (N n + i)) : Option BitString)) := by
  have H : Computable₂ (fun n i => N n + i) :=
    Computable₂.comp Primrec.nat_add.to_comp (hN.comp Computable.fst) Computable.snd
  exact Computable.option_some.comp (hx.comp H)

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_series_mpr`: the
cylinders cover w -/
private theorem not_isSchnorrRandom_iff_exists_series_cover {w : CantorSeq}
    {x : ℕ → BitString} {N : ℕ → ℕ}
    (hfreq : ∃ᶠ i in atTop, IsCantorPrefix (x i) w) (n : ℕ) :
    ({w} : Set CantorSeq) ⊆ ⋃ i, ((some (x (N n + i)) : Option BitString).elim ∅ cantorCylinder) :=
        by
  have h_freq_top : ∃ i ≥ N n, IsCantorPrefix (x i) w := Filter.frequently_atTop.mp hfreq (N n)
  rcases h_freq_top with ⟨i, hi_ge, hi_prefix⟩
  rw [Set.singleton_subset_iff, Set.mem_iUnion]
  use i - N n
  have h_eq : N n + (i - N n) = i := Nat.add_sub_of_le hi_ge
  rw [h_eq]
  exact hi_prefix

/-- Step 3 of the proof of `not_isSchnorrRandom_iff_exists_series_mpr`: the sum is
bounded -/
private theorem not_isSchnorrRandom_iff_exists_series_mpr_sum {π : Measure CantorSeq}
    {x : ℕ → BitString} {N : ℕ → ℕ}
    (hsum : ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) (n : ℕ) :
    ∑' i, Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i))) ≤ dyadicValue 1 n := by
  have hs : (fun (i : ℕ) => Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))) = fun i =>
    cantorMass π (x (N n + i)) := by
    ext i
    rfl
  rw [hs]
  exact hsum n

/-- Step 4 of the proof of `not_isSchnorrRandom_iff_exists_series_mpr`: the sum is a
computable real sequence -/
private def not_isSchnorrRandom_iff_exists_series_real_seq_q
    (a : BitString → ℕ → ℕ) (x : ℕ → BitString) (N : ℕ → ℕ) (p : ℕ × ℕ) : ℚ :=
  let n := p.1
  let s := p.2
  let L := N (s + 1)
  let t := s + 1 + L
  (∑ i ∈ Finset.range L, (a (x (N n + i)) t : ℚ)) / (2 ^ t : ℚ)

/-- Step 1 of the proof of
`not_isSchnorrRandom_iff_exists_series_real_seq`: computability of the rational
sequence q -/
private lemma not_isSchnorrRandom_iff_exists_series_real_seq_computable
    (a : BitString → ℕ → ℕ) (ha : Computable₂ a)
    (x : ℕ → BitString) (hx : Computable x)
    (N : ℕ → ℕ) (hN : Computable N) :
    Computable (not_isSchnorrRandom_iff_exists_series_real_seq_q a x N) := by
  have hs1 : Computable fun p : ℕ × ℕ => p.2 + 1 :=
    Computable₂.comp Primrec.nat_add.to_comp Computable.snd (Computable.const 1)
  have hL : Computable fun p : ℕ × ℕ => N (p.2 + 1) := hN.comp hs1
  have hs' : Computable fun p : ℕ × ℕ => p.2 + 1 + N (p.2 + 1) :=
    Computable₂.comp Primrec.nat_add.to_comp hs1 hL
  have hterm : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      a (x (N (p.1.1) + p.2.1)) (p.1.2 + 1 + N (p.1.2 + 1)) := by
    have hn_plus_i : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => N (p.1.1) + p.2.1 :=
      Computable₂.comp Primrec.nat_add.to_comp (hN.comp (Computable.fst.comp Computable.fst))
        (Computable.fst.comp Computable.snd)
    have hx_val : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => x (N (p.1.1) + p.2.1) :=
      hx.comp hn_plus_i
    have ht_val : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2 + 1 + N (p.1.2 + 1) :=
      hs'.comp Computable.fst
    exact Computable₂.comp ha hx_val ht_val
  have hsum : Computable fun p : ℕ × ℕ =>
      ∑ i ∈ Finset.range (N (p.2 + 1)), a (x (N p.1 + i)) (p.2 + 1 + N (p.2 + 1)) := by
    have hrec := Computable.nat_rec (σ := ℕ) hL (Computable.const 0)
      (h := fun (p : ℕ × ℕ) (r : ℕ × ℕ) => r.2 + a (x (N p.1 + r.1)) (p.2 + 1 + N (p.2 + 1)))
      (Computable₂.comp Primrec.nat_add.to_comp (Computable.snd.comp Computable.snd) hterm)
    refine hrec.of_eq fun p => ?_
    have key : ∀ (S L : ℕ), Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => (y, IH).2 + a (x (N p.1 + (y, IH).1)) S) L
        = ∑ i ∈ Finset.range L, a (x (N p.1 + i)) S := by
      intro S L
      induction L with
      | zero => simp
      | succ k ih => simp [Finset.sum_range_succ, ih]
    exact key _ _
  have hnum : Computable fun p : ℕ × ℕ =>
      ((∑ i ∈ Finset.range (N (p.2 + 1)), a (x (N p.1 + i)) (p.2 + 1 + N (p.2 + 1)) : ℕ) : ℤ) :=
    ComputableReals.primrec_natCastInt.to_comp.comp hsum
  have hden : Computable fun p : ℕ × ℕ => 2 ^ (p.2 + 1 + N (p.2 + 1)) := comp_pow.comp hs'
  refine computable_of_num_den hnum hden (fun p => by positivity) (fun p => ?_)
  push_cast
  rfl



private lemma not_isSchnorrRandom_iff_exists_series_head_aux1 {ι : Type} (s : Finset ι)
    (f g : ι → ℝ) :
    |∑ i ∈ s, f i - ∑ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

private lemma not_isSchnorrRandom_iff_exists_series_head_aux2 (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc n + 1 < 2 ^ n + 1 := Nat.add_lt_add_right ih 1
      _ ≤ 2 ^ n + 2 ^ n :=
        Nat.add_le_add_left (Nat.pos_of_ne_zero (pow_ne_zero n (by decide))) _
      _ = 2 ^ (n + 1) := by ring

private lemma not_isSchnorrRandom_iff_exists_series_head_aux3 (s L : ℕ) : (L : ℝ) * (2 : ℝ)⁻¹ ^
    (s + 1 + L) ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
  rw [pow_add]
  calc (L : ℝ) * ((2 : ℝ)⁻¹ ^ (s + 1) * (2 : ℝ)⁻¹ ^ L)
    _ = (2 : ℝ)⁻¹ ^ (s + 1) * ((L : ℝ) * (2 : ℝ)⁻¹ ^ L) := by ring
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h : (2 : ℝ)⁻¹ ^ L = (2 ^ L : ℝ)⁻¹ := by rw [inv_pow]
      rw [h, mul_inv_le_iff₀ (by positivity)]
      have ht : 1 * (2 ^ L : ℝ) = (2 ^ L : ℝ) := by ring
      rw [ht]
      norm_cast
      exact (not_isSchnorrRandom_iff_exists_series_head_aux2 L).le
    _ = (2 : ℝ)⁻¹ ^ (s + 1) := by rw [mul_one]

/-- Step 1 of the proof of
`not_isSchnorrRandom_iff_exists_series_approx`: head bound -/
private lemma not_isSchnorrRandom_iff_exists_series_head
    (π : Measure CantorSeq) [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha_approx : ∀ y s, dyadicValue (a y s) s ≤ cantorMass π y + dyadicValue 1 s ∧
      cantorMass π y ≤ dyadicValue (a y s) s + dyadicValue 1 s)
    (x : ℕ → BitString) (N : ℕ → ℕ) (n s : ℕ) :
    let L := N (s + 1)
    |(not_isSchnorrRandom_iff_exists_series_real_seq_q a x N (n, s) : ℝ) - ∑ i ∈
        Finset.range L, (cantorMass π (x (N n + i))).toReal| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
  intro L
  let t := s + 1 + L
  have h_q : (not_isSchnorrRandom_iff_exists_series_real_seq_q a x N (n, s) : ℝ) =
      ∑ i ∈ Finset.range L, (a (x (N n + i)) t : ℝ) / (2 ^ t : ℝ) := by
    unfold not_isSchnorrRandom_iff_exists_series_real_seq_q
    simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, Rat.cast_pow]
    have : ((∑ i ∈ Finset.range (N (s + 1)), (a (x (N n + i)) (s + 1 + N (s + 1)) : ℝ)) : ℝ) /
        ((2 : ℝ) ^ (s + 1 + N (s + 1))) =
      ∑ i ∈ Finset.range L, (a (x (N n + i)) t : ℝ) / (2 ^ t : ℝ) := by
      change (∑ i ∈ Finset.range L, (a (x (N n + i)) t : ℝ)) / (2 ^ t : ℝ) = _
      rw [Finset.sum_div]
    exact this
  
  rw [h_q]
  have h_abs := not_isSchnorrRandom_iff_exists_series_head_aux1 (Finset.range L)
      (fun i => (a (x (N n + i)) t : ℝ) / (2 ^ t : ℝ))
      (fun i => (cantorMass π (x (N n + i))).toReal)
  
  have h_each : ∀ i ∈ Finset.range L, |(a (x (N n + i)) t : ℝ) / (2 ^ t : ℝ) -
      (cantorMass π (x (N n + i))).toReal| ≤ (2 : ℝ)⁻¹ ^ t := by
    intro i _
    have h1 := (ha_approx (x (N n + i)) t).1
    have h2 := (ha_approx (x (N n + i)) t).2
    
    have h_d1 : (dyadicValue 1 t).toReal = (2 : ℝ)⁻¹ ^ t := by
      rw [Kolmogorov.dyadicValue_one_eq_inv_two_pow']
      simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    
    have h_da : (dyadicValue (a (x (N n + i)) t) t).toReal = (a (x (N n + i)) t : ℝ) /
        (2 ^ t : ℝ) := by
      unfold dyadicValue
      simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat]
    have h_ne_top1 : cantorMass π (x (N n + i)) ≠ ⊤ :=
        measure_ne_top π (cantorCylinder (x (N n + i)))
    have h_ne_top2 : dyadicValue 1 t ≠ ⊤ := by
      rw [Kolmogorov.dyadicValue_one_eq_inv_two_pow']
      exact ENNReal.pow_ne_top (by simp)
    have h_sum_ne_top : cantorMass π (x (N n + i)) + dyadicValue 1 t ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨h_ne_top1, h_ne_top2⟩
    
    have h_ne_top3 : dyadicValue (a (x (N n + i)) t) t ≠ ⊤ := ne_top_of_le_ne_top h_sum_ne_top h1
    have h1' := ENNReal.toReal_mono h_sum_ne_top h1
    have h2' := ENNReal.toReal_mono (by
      have h_sum_ne_top2 : dyadicValue (a (x (N n + i)) t) t + dyadicValue 1 t ≠ ⊤ :=
          ENNReal.add_ne_top.mpr ⟨h_ne_top3, h_ne_top2⟩
      exact h_sum_ne_top2
    ) h2
    
    rw [ENNReal.toReal_add h_ne_top1 h_ne_top2] at h1'
    rw [ENNReal.toReal_add h_ne_top3 h_ne_top2] at h2'
    rw [h_d1, h_da] at h1' h2'
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  calc |∑ i ∈ Finset.range L, (a (x (N n + i)) t : ℝ) / (2 ^ t : ℝ) - ∑ i ∈ Finset.range L,
      (cantorMass π (x (N n + i))).toReal|
    _ ≤ ∑ i ∈ Finset.range L, |(a (x (N n + i)) t : ℝ) / (2 ^ t : ℝ) -
        (cantorMass π (x (N n + i))).toReal| := h_abs
    _ ≤ ∑ i ∈ Finset.range L, (2 : ℝ)⁻¹ ^ t := by apply Finset.sum_le_sum; exact h_each
    _ = (L : ℝ) * (2 : ℝ)⁻¹ ^ t := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (L : ℝ) * (2 : ℝ)⁻¹ ^ (s + 1 + L) := by rfl
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) := not_isSchnorrRandom_iff_exists_series_head_aux3 s L

/-- Step 2 of the proof of
`not_isSchnorrRandom_iff_exists_series_approx`: real tail bound -/
private lemma not_isSchnorrRandom_iff_exists_series_tail
    (π : Measure CantorSeq) [IsProbabilityMeasure π]
    (x : ℕ → BitString) (N : ℕ → ℕ)
    (hsum : ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) (n s : ℕ) :
    let L := N (s + 1)
    |(∑' i, Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))).toReal - ∑ i ∈ Finset.range
        L, (cantorMass π (x (N n + i))).toReal| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
  intro L
  have h1 : (fun (i : ℕ) => Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))) = fun i =>
    cantorMass π (x (N n + i)) := by
    ext i
    rfl
  rw [h1]
  
  have H_eq1 : ∑' i, (cantorMass π (x (N n + i))).toReal = (∑' i, cantorMass π (x (N n + i))).toReal
      := by
    rw [ENNReal.tsum_toReal_eq]
    intro i
    exact measure_ne_top π _
    
  have h_sum1 : (∑' (i : ℕ), cantorMass π (x (N n + i))).toReal - ∑ i ∈ Finset.range L,
      (cantorMass π (x (N n + i))).toReal = (∑' i, (cantorMass π (x (N n + L + i))).toReal) := by
    have h_eq : ∑' i, (cantorMass π (x (N n + i))).toReal = ∑ i ∈ Finset.range L,
        (cantorMass π (x (N n + i))).toReal + ∑' i, (cantorMass π (x (N n + L + i))).toReal := by
      have h_summable : Summable (fun i => (cantorMass π (x (N n + i))).toReal) := by
        apply ENNReal.summable_toReal
        have hs : ∑' i, cantorMass π (x (N n + i)) ≠ ⊤ := by
          have H := hsum n
          have h_dyadic : dyadicValue 1 n ≠ ⊤ := by
            unfold dyadicValue
            have : ((1:ℕ) : ENNReal) / (2 : ENNReal) ^ n = (2 : ENNReal)⁻¹ ^ n := by
              rw [Nat.cast_one, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_one]
            rw [this]
            apply ENNReal.pow_ne_top
            exact ENNReal.inv_ne_top.mpr (by norm_num)
          intro H_top
          rw [H_top] at H
          exact h_dyadic (top_le_iff.mp H)
        exact hs
      have H := Summable.sum_add_tsum_nat_add L h_summable
      rw [← H]
      congr 1
      apply tsum_congr
      intro i
      have h3 : N n + (i + L) = N n + L + i := by omega
      rw [h3]
    rw [← H_eq1, h_eq]
    exact add_sub_cancel_left (∑ i ∈ Finset.range L, (cantorMass π (x (N n + i))).toReal)
        (∑' i, (cantorMass π (x (N n + L + i))).toReal)
  
  rw [h_sum1]
  have h_abs : |∑' i, (cantorMass π (x (N n + L + i))).toReal| = ∑' i,
      (cantorMass π (x (N n + L + i))).toReal := by
    apply abs_of_nonneg
    apply tsum_nonneg
    intro i
    exact ENNReal.toReal_nonneg
  rw [h_abs]
  
  have H_eq2 : ∑' i, (cantorMass π (x (N n + L + i))).toReal =
      (∑' i, cantorMass π (x (N n + L + i))).toReal := by
    rw [ENNReal.tsum_toReal_eq]
    intro i
    exact measure_ne_top π _
  rw [H_eq2]
  
  have h_subseries : ∑' i, cantorMass π (x (N n + L + i)) ≤ ∑' j, cantorMass π (x (L + j)) := by
    have h_comm : (fun i => cantorMass π (x (N n + L + i))) = fun i =>
      cantorMass π (x (L + (N n + i))) := by
      ext i
      have : N n + L + i = L + (N n + i) := by omega
      rw [this]
    rw [h_comm]
    have h_comp : (fun i => cantorMass π (x (L + (N n + i)))) = (fun j => cantorMass π (x (L + j)))
        ∘ (fun i => N n + i) := rfl
    rw [h_comp]
    exact ENNReal.tsum_comp_le_tsum_of_injective (fun a b hab => by omega)
        (fun j => cantorMass π (x (L + j)))
  have h_bound : ∑' j, cantorMass π (x (L + j)) ≤ dyadicValue 1 (s + 1) := by
    exact hsum (s + 1)
  have h_le := le_trans h_subseries h_bound
  have H_toReal : (∑' (i : ℕ), cantorMass π (x (N n + L + i))).toReal ≤
      (dyadicValue 1 (s + 1)).toReal := by
    exact ENNReal.toReal_mono (by
      unfold dyadicValue
      have : ((1:ℕ) : ENNReal) / (2 : ENNReal) ^ (s + 1) = (2 : ENNReal)⁻¹ ^ (s + 1) := by
        rw [Nat.cast_one, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_one]
      rw [this]
      apply ENNReal.pow_ne_top
      exact ENNReal.inv_ne_top.mpr (by norm_num)
    ) h_le
  have h_dyadic_toReal : (dyadicValue 1 (s + 1)).toReal = (2 : ℝ)⁻¹ ^ (s + 1) := by
    unfold dyadicValue
    have H (k : ℕ) : ((1:ℕ) : ENNReal) / 2 ^ k = (2:ENNReal)⁻¹ ^ k := by
      rw [Nat.cast_one, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_one]
    rw [H (s + 1)]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [← h_dyadic_toReal]
  exact H_toReal

/-- Step 2 of the proof of
`not_isSchnorrRandom_iff_exists_series_real_seq`: approximation bound -/
private lemma not_isSchnorrRandom_iff_exists_series_approx
    (π : Measure CantorSeq) [IsProbabilityMeasure π]
    (a : BitString → ℕ → ℕ)
    (ha_approx : ∀ y s, dyadicValue (a y s) s ≤ cantorMass π y + dyadicValue 1 s ∧
      cantorMass π y ≤ dyadicValue (a y s) s + dyadicValue 1 s)
    (x : ℕ → BitString) (N : ℕ → ℕ)
    (hsum : ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) (n s : ℕ) :
    |(not_isSchnorrRandom_iff_exists_series_real_seq_q a x N (n, s) : ℝ) - 
     (∑' i, Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))).toReal| ≤ (2 : ℝ)⁻¹ ^ s :=
         by
  have h1 := not_isSchnorrRandom_iff_exists_series_head
      π a ha_approx x N n s
  have h2 := not_isSchnorrRandom_iff_exists_series_tail
      π x N hsum n s
  have h3 : (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) = (2 : ℝ)⁻¹ ^ s := by
    calc (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1)
      _ = 2 * (2 : ℝ)⁻¹ ^ (s + 1) := by ring
      _ = 2 * ((2 : ℝ)⁻¹ ^ s * (2 : ℝ)⁻¹) := by rw [pow_add, pow_one]
      _ = 2 * (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ s := by
        rw [mul_comm ((2 : ℝ)⁻¹ ^ s) (2 : ℝ)⁻¹, ← mul_assoc]
      _ = (2 : ℝ)⁻¹ ^ s := by
        have : 2 * (2 : ℝ)⁻¹ = (1 : ℝ) := mul_inv_cancel₀ (by norm_num)
        rw [this, one_mul]
  calc |(not_isSchnorrRandom_iff_exists_series_real_seq_q a x N (n, s) : ℝ) -
      (∑' (i : ℕ), Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))).toReal|
    _ ≤ |(not_isSchnorrRandom_iff_exists_series_real_seq_q a x N (n, s) : ℝ) - ∑ i ∈
        Finset.range (N (s + 1)), (cantorMass π (x (N n + i))).toReal| + |∑ i ∈ Finset.range
        (N (s + 1)), (cantorMass π (x (N n + i))).toReal -
        (∑' (i : ℕ), Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))).toReal| :=
        abs_sub_le _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) := by
      refine add_le_add h1 ?_
      rw [abs_sub_comm]
      exact h2
    _ = (2 : ℝ)⁻¹ ^ s := h3

private theorem not_isSchnorrRandom_iff_exists_series_real_seq
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) {x : ℕ → BitString} {N : ℕ → ℕ} (hx : Computable x)
        (hN : Computable N)
    (hsum : ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) :
    Kolmogorov.FrequencyGames.IsComputableRealSeq fun n =>
      (∑' i, Kolmogorov.FrequencyGames.coverMass π (some (x (N n + i)))).toReal := by
  rcases hπ with ⟨a, ha, ha_approx⟩
  use not_isSchnorrRandom_iff_exists_series_real_seq_q a x N
  constructor
  · exact not_isSchnorrRandom_iff_exists_series_real_seq_computable a ha x hx
      N hN
  · exact not_isSchnorrRandom_iff_exists_series_approx π a ha_approx
      x N hsum

/-- Step 2 of the proof of `not_isSchnorrRandom_iff_exists_series`: the backward
implication. -/
private theorem not_isSchnorrRandom_iff_exists_series_mpr {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (w : CantorSeq) :
    (∃ x : ℕ → BitString, Computable x ∧
      (∃ N : ℕ → ℕ, Computable N ∧ ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) ∧
      ∃ᶠ i in atTop, IsCantorPrefix (x i) w) → ¬ IsSchnorrRandom π w := by
  rintro ⟨x, hx_comp, ⟨N, hN_comp, h_sum⟩, h_freq⟩
  have hnull : IsSchnorrNull π {w} := by
    unfold IsSchnorrNull
    refine Exists.intro
      (fun n i => (some (x (N n + i)) : Option BitString)) ?_
    refine And.intro
      (not_isSchnorrRandom_iff_exists_series_f_comp
        hx_comp hN_comp) ?_
    refine And.intro
      (fun n =>
        not_isSchnorrRandom_iff_exists_series_cover
          (w := w) (x := x) (N := N) h_freq n) ?_
    exact And.intro
      (fun n =>
        not_isSchnorrRandom_iff_exists_series_mpr_sum
          (π := π) (x := x) (N := N) h_sum n)
      (not_isSchnorrRandom_iff_exists_series_real_seq
        (π := π) (x := x) (N := N) hπ hx_comp hN_comp h_sum)
  intro hw
  exact hw hnull

/-- **SUV Problem 90 of Section 3.4, used on p. 282.**  `ω` is not Schnorr random exactly when there
is a computable sequence of strings `x_i` with `∑ π(x_i)` computably convergent and infinitely many
`x_i` prefixes of `ω`. -/
theorem not_isSchnorrRandom_iff_exists_series {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (w : CantorSeq) :
    ¬ IsSchnorrRandom π w ↔ ∃ x : ℕ → BitString, Computable x ∧
      (∃ N : ℕ → ℕ, Computable N ∧ ∀ k, ∑' i, cantorMass π (x (N k + i)) ≤ dyadicValue 1 k) ∧
      ∃ᶠ i in atTop, IsCantorPrefix (x i) w := by
  exact ⟨not_isSchnorrRandom_iff_exists_series_mp hπ w,
      not_isSchnorrRandom_iff_exists_series_mpr hπ w⟩

end Kolmogorov.FrequencyGames
