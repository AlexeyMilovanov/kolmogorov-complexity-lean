/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.Defs

/-!
# Kurtz Martingales

Characterization of the failure of Kurtz randomness for a computable positive probability measure
on Cantor space by computable martingales (fair capitals) whose values on the prefixes of a
sequence are bounded below by a computable monotone unbounded function.

The main result is `not_isKurtzRandom_iff_exists_growth` (SUV Problem 272, p. 284).  The forward
direction builds a martingale from a computable sequence of finite unions of cylinders of
small measure, using the uniform computability of the masses `π(Ω_y ∩ U_n)`; the reverse direction
bounds the measure of the set where the capital reaches a given level by the Ville inequality.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-- `π(Ω_y ∩ U)` as a real number. -/
private noncomputable def not_isKurtzRandom_iff_exists_growth_ltr_nuR (π : Measure CantorSeq)
    (U : Set CantorSeq) (y : BitString) : ℝ :=
  (π (cantorCylinder y ∩ U)).toReal

private lemma not_isKurtzRandom_iff_exists_growth_ltr_ratDiv {α : Type*} [Primcodable α]
    {f g : α → ℚ}
    (hf : Computable f) (hg : Computable g) (hgpos : ∀ a, 0 < g a) :
    Computable (fun a => f a / g a) := by
  refine computable_of_num_den (N := fun a => (f a).num * ((g a).den : ℤ))
    (D := fun a => (f a).den * (g a).num.toNat) ?_ ?_ ?_ ?_
  · exact Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp hf)
      (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp hg))
  · exact Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp hf)
      (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp hg))
  · intro a
    exact Nat.mul_pos (f a).pos (by have := Rat.num_pos.mpr (hgpos a); omega)
  · intro a
    have hx : ((f a).num : ℚ) = f a * ((f a).den : ℚ) := (Rat.mul_den_eq_num (f a)).symm
    have hy : ((g a).num : ℚ) = g a * ((g a).den : ℚ) := (Rat.mul_den_eq_num (g a)).symm
    have hy0 : 0 < (g a).num := Rat.num_pos.mpr (hgpos a)
    have hy1 : (((g a).num.toNat : ℕ) : ℚ) = ((g a).num : ℚ) := by
      have : (((g a).num.toNat : ℕ) : ℤ) = (g a).num := Int.toNat_of_nonneg hy0.le
      exact_mod_cast this
    have hdx : ((f a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f a).den_nz
    have hdy : ((g a).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (g a).den_nz
    have hga : g a ≠ 0 := (hgpos a).ne'
    push_cast
    rw [hy1, hx, hy]
    field_simp

private lemma not_isKurtzRandom_iff_exists_growth_ltr_massR_comp {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) : IsComputableOnStrings (fun y => massR π y) := by
  obtain ⟨a, ha, hab⟩ := hπ
  refine ⟨fun p => ((a p.1 p.2 : ℕ) : ℚ) / ((2 ^ p.2 : ℕ) : ℚ), ?_, ?_⟩
  · refine computable_of_num_den (N := fun p : BitString × ℕ => ((a p.1 p.2 : ℕ) : ℤ))
      (D := fun p : BitString × ℕ => 2 ^ p.2) ?_ ?_ (fun p => Nat.two_pow_pos _) (fun p => by simp)
    · exact ComputableReals.primrec_natCastInt.to_comp.comp ha
    · exact comp_pow.comp Computable.snd
  · intro y s
    obtain ⟨h1, h2⟩ := hab y s
    have hne : ∀ n s : ℕ, dyadicValue n s ≠ ⊤ := fun n s => by
      unfold dyadicValue
      exact (ENNReal.div_lt_top (by simp) (by simp)).ne
    have hdv : ∀ n s : ℕ, (dyadicValue n s).toReal = (n : ℝ) / 2 ^ s := fun n s => by
      simp [dyadicValue, ENNReal.toReal_div, ENNReal.toReal_pow]
    have hne2 : cantorMass π y ≠ ⊤ := measure_ne_top _ _
    have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne2, hne 1 s⟩) h1
    have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne _ _, hne 1 s⟩) h2
    rw [ENNReal.toReal_add hne2 (hne 1 s), hdv, hdv] at e1
    rw [ENNReal.toReal_add (hne _ _) (hne 1 s), hdv, hdv] at e2
    change |(((a y s : ℕ) : ℚ) / ((2 ^ s : ℕ) : ℚ) : ℚ) - massR π y| ≤ (2 : ℝ)⁻¹ ^ s
    have hq : ((((a y s : ℕ) : ℚ) / ((2 ^ s : ℕ) : ℚ) : ℚ) : ℝ) = (a y s : ℝ) / 2 ^ s := by
      push_cast; rfl
    rw [hq]
    have h2s : (1 : ℝ) / 2 ^ s = (2 : ℝ)⁻¹ ^ s := by rw [one_div, inv_pow]
    have hm : (cantorMass π y).toReal = massR π y := rfl
    rw [hm] at e1 e2
    simp only [Nat.cast_one] at e1 e2
    rw [abs_le]
    constructor <;> linarith [h2s]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_sum_rec_eq (q : ℕ → ℚ) (N : ℕ) :
    (Nat.rec (0 : ℚ) (fun n IH => IH + q n) N : ℚ) = ∑ n ∈ Finset.range N, q n := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← ih]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_tsum_comp {a : ℕ → BitString → ℝ}
    (hq : ∃ q : ℕ × BitString × ℕ → ℚ, Computable q ∧
      ∀ n y s, |(q (n, y, s) : ℝ) - a n y| ≤ (2 : ℝ)⁻¹ ^ s)
    (hnn : ∀ n y, 0 ≤ a n y) (hb : ∀ n y, a n y ≤ (2 : ℝ)⁻¹ ^ n) :
    IsComputableOnStrings (fun y => ∑' n, a n y) := by
  obtain ⟨q, hqc, hqe⟩ := hq
  have hQ : Computable (fun p : BitString × ℕ =>
      (Nat.rec (0 : ℚ) (fun n IH => IH + q (n, p.1, 2 * p.2 + 3)) (p.2 + 2) : ℚ)) := by
    refine Computable.nat_rec (f := fun p : BitString × ℕ => p.2 + 2) (g := fun _ => (0 : ℚ))
      (h := fun (p : BitString × ℕ) (r : ℕ × ℚ) => r.2 + q (r.1, p.1, 2 * p.2 + 3)) ?_ ?_ ?_
    · exact Computable₂.comp Primrec.nat_add.to_comp Computable.snd (Computable.const 2)
    · exact Computable.const 0
    · have h1 : Computable (fun x : (BitString × ℕ) × (ℕ × ℚ) => x.2.2) :=
        Computable.snd.comp Computable.snd
      have h3 : Computable (fun x : (BitString × ℕ) × (ℕ × ℚ) => 2 * x.1.2 + 3) :=
        Computable₂.comp Primrec.nat_add.to_comp
          (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2)
            (Computable.snd.comp Computable.fst)) (Computable.const 3)
      have h2 : Computable (fun x : (BitString × ℕ) × (ℕ × ℚ) =>
          q (x.2.1, x.1.1, 2 * x.1.2 + 3)) :=
        hqc.comp (Computable.pair (Computable.fst.comp Computable.snd)
          (Computable.pair (Computable.fst.comp Computable.fst) h3))
      exact Computable₂.comp computable₂_ratAdd h1 h2
  refine ⟨_, hQ, fun y s => ?_⟩
  have hq1 : ((Nat.rec (0 : ℚ) (fun n IH => IH + q (n, y, 2 * s + 3)) (s + 2) : ℚ)) =
      ∑ n ∈ Finset.range (s + 2), q (n, y, 2 * s + 3) :=
    not_isKurtzRandom_iff_exists_growth_ltr_sum_rec_eq (fun n => q (n, y, 2 * s + 3)) (s + 2)
  change |((Nat.rec (0 : ℚ) (fun n IH => IH + q (n, y, 2 * s + 3)) (s + 2) : ℚ) : ℝ) -
    ∑' n, a n y| ≤ (2 : ℝ)⁻¹ ^ s
  rw [hq1]
  push_cast
  have hsumm : Summable (fun n => a n y) :=
    Summable.of_nonneg_of_le (hnn · y) (hb · y)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
  have hsplit := hsumm.sum_add_tsum_nat_add (s + 2)
  have htail_nn : 0 ≤ ∑' n, a (n + (s + 2)) y := tsum_nonneg fun n => hnn _ y
  have htail_le : ∑' n, a (n + (s + 2)) y ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
    have hgeo : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + (s + 2))) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right
        ((2 : ℝ)⁻¹ ^ (s + 2)) |>.congr (fun n => (pow_add _ _ _).symm)
    calc ∑' n, a (n + (s + 2)) y ≤ ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + (s + 2)) :=
          Summable.tsum_le_tsum (fun n => hb _ y) (hsumm.comp_injective (add_left_injective _)) hgeo
      _ = (2 : ℝ)⁻¹ ^ (s + 1) := by
          have : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ (n + (s + 2)) = (2 : ℝ)⁻¹ ^ (s + 2) * (2 : ℝ)⁻¹ ^ n :=
              fun n => by
            rw [pow_add, mul_comm]
          simp_rw [this]
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num [pow_succ]
          ring
  have hfin : |∑ n ∈ Finset.range (s + 2), ((q (n, y, 2 * s + 3) : ℚ) : ℝ) -
      ∑ n ∈ Finset.range (s + 2), a n y| ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range (s + 2), |((q (n, y, 2 * s + 3) : ℚ) : ℝ) - a n y|
        ≤ ∑ n ∈ Finset.range (s + 2), (2 : ℝ)⁻¹ ^ (2 * s + 3) :=
          Finset.sum_le_sum fun n _ => hqe n y _
      _ = ((s + 2 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (2 * s + 3) := by simp
      _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) := by
          have h1 : ((s + 2 : ℕ) : ℝ) ≤ 2 ^ (s + 2) := by
            exact_mod_cast (Nat.lt_two_pow_self (n := s + 2)).le
          have h3 : (2 : ℝ) ^ (s + 2) * (2 : ℝ)⁻¹ ^ (2 * s + 3) = (2 : ℝ)⁻¹ ^ (s + 1) := by
            simp only [inv_pow]
            rw [show 2 * s + 3 = (s + 2) + (s + 1) by ring, pow_add]
            field_simp
            ring
          calc ((s + 2 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (2 * s + 3)
              ≤ 2 ^ (s + 2) * (2 : ℝ)⁻¹ ^ (2 * s + 3) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (2 : ℝ)⁻¹ ^ (s + 1) := h3
  have e : ∑ n ∈ Finset.range (s + 2), ((q (n, y, 2 * s + 3) : ℚ) : ℝ) - ∑' n, a n y =
      (∑ n ∈ Finset.range (s + 2), ((q (n, y, 2 * s + 3) : ℚ) : ℝ) -
        ∑ n ∈ Finset.range (s + 2), a n y) - ∑' n, a (n + (s + 2)) y := by
    linarith
  rw [e, abs_le]
  have h2s : (2 : ℝ)⁻¹ ^ s = (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [pow_succ]; ring
  rw [abs_le] at hfin
  constructor <;> linarith [hfin.1, hfin.2]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_div_comp {A B : BitString → ℝ}
    (hA : IsComputableOnStrings A) (hB : IsComputableOnStrings B)
    (hA2 : ∀ y, |A y| ≤ 2) (hB1 : ∀ y, B y ≤ 1) (hBpos : ∀ y, 0 < B y) :
    IsComputableOnStrings (fun y => A y / B y) := by
  obtain ⟨qA, hqAc, hqA⟩ := hA
  obtain ⟨qB, hqBc, hqB⟩ := hB
  have hex : ∀ y, ∃ t : ℕ, ¬ (qB (y, t) * ((2 ^ t : ℕ) : ℚ) / 2 ≤ 1) := by
    intro y
    obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show 0 < B y / 3 by linarith [hBpos y])
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    refine ⟨t, ?_⟩
    have h1 := hqB y t
    rw [abs_le] at h1
    have h2 : (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ t = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by norm_num),
                                                      one_pow]
    have h3 : (1 : ℝ) < (qB (y, t) : ℝ) * 2 ^ t / 2 := by
      have h4 : 3 * (2 : ℝ)⁻¹ ^ t < B y := by linarith
      have h5 : (2 : ℝ) * (2 : ℝ)⁻¹ ^ t < (qB (y, t) : ℝ) := by linarith [h1.1, h1.2]
      have h6 : (0 : ℝ) < 2 ^ t := by positivity
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc (1 : ℝ) * 2 = 2 * ((2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ t) := by rw [h2]; ring
        _ = (2 * (2 : ℝ)⁻¹ ^ t) * 2 ^ t := by ring
        _ < (qB (y, t) : ℝ) * 2 ^ t := mul_lt_mul_of_pos_right h5 h6
    exact not_le.mpr (by exact_mod_cast h3)
  have hPc : Computable (fun p : BitString × ℕ =>
      decide (¬ (qB (p.1, p.2) * ((2 ^ p.2 : ℕ) : ℚ) / 2 ≤ 1))) := by
    have hx : Computable (fun p : BitString × ℕ => qB (p.1, p.2) * ((2 ^ p.2 : ℕ) : ℚ) / 2) :=
      computable_ratHalf.comp (Computable₂.comp computable₂_ratMul (hqBc.comp Computable.id)
        (computable_nat_to_rat.comp (comp_pow.comp Computable.snd)))
    exact (Primrec.not.to_comp.comp (computable_ratLeOne.comp hx)).of_eq
      (fun p => decide_not.symm)
  have htc : Computable (fun y : BitString => Nat.find (hex y)) :=
    Computable.natFind (P := fun (y : BitString) (t : ℕ) =>
      ¬ (qB (y, t) * ((2 ^ t : ℕ) : ℚ) / 2 ≤ 1)) hPc hex
  -- the two facts about the search result
  have haux : ∀ (y : BitString) (s : ℕ), ((2 : ℝ)⁻¹ ^ (Nat.find (hex y)) < B y) ∧
      ((2 : ℝ)⁻¹ ^ (Nat.find (hex y)) / 2 < (qB (y, s + 2 * Nat.find (hex y) + 4) : ℝ)) := by
    intro y s
    have hspec := Nat.find_spec (hex y)
    generalize Nat.find (hex y) = tt at hspec ⊢
    have h1 : (1 : ℚ) < qB (y, tt) * ((2 ^ tt : ℕ) : ℚ) / 2 := not_le.mp hspec
    have h1' : (1 : ℝ) < (qB (y, tt) : ℝ) * 2 ^ tt / 2 := by exact_mod_cast h1
    have hq := hqB y tt
    rw [abs_le] at hq
    have h2 : (2 : ℝ) ^ tt * (2 : ℝ)⁻¹ ^ tt = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
    have hlt : (2 : ℝ)⁻¹ ^ tt < B y := by
      have h6 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ tt := by positivity
      have h7 : 2 < (qB (y, tt) : ℝ) * 2 ^ tt := by linarith
      have h8 := mul_lt_mul_of_pos_right h7 h6
      have h9 : 2 * (2 : ℝ)⁻¹ ^ tt < (qB (y, tt) : ℝ) := by
        calc 2 * (2 : ℝ)⁻¹ ^ tt < (qB (y, tt) : ℝ) * 2 ^ tt * (2 : ℝ)⁻¹ ^ tt := h8
          _ = (qB (y, tt) : ℝ) := by rw [mul_assoc, h2, mul_one]
      linarith [hq.1, hq.2]
    refine ⟨hlt, ?_⟩
    have hqU := hqB y (s + 2 * tt + 4)
    rw [abs_le] at hqU
    have heU : (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) ≤ (2 : ℝ)⁻¹ ^ tt / 2 := by
      calc (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) ≤ (2 : ℝ)⁻¹ ^ (tt + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = (2 : ℝ)⁻¹ ^ tt / 2 := by rw [pow_succ]; ring
    linarith [hqU.1]
  refine ⟨fun p : BitString × ℕ =>
      qA (p.1, p.2 + 2 * Nat.find (hex p.1) + 4) / qB (p.1, p.2 + 2 * Nat.find (hex p.1) + 4),
    ?_, ?_⟩
  · have hu : Computable (fun p : BitString × ℕ => p.2 + 2 * Nat.find (hex p.1) + 4) :=
      Computable₂.comp Primrec.nat_add.to_comp
        (Computable₂.comp Primrec.nat_add.to_comp Computable.snd
          (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2)
            (htc.comp Computable.fst)))
        (Computable.const 4)
    refine not_isKurtzRandom_iff_exists_growth_ltr_ratDiv (hqAc.comp
        (Computable.pair Computable.fst hu))
      (hqBc.comp (Computable.pair Computable.fst hu)) ?_
    intro p
    have h := (haux p.1 p.2).2
    have h0 : (0 : ℝ) < (qB (p.1, p.2 + 2 * Nat.find (hex p.1) + 4) : ℝ) :=
      lt_trans (by positivity) h
    exact_mod_cast h0
  · intro y s
    obtain ⟨hlt, hlow⟩ := haux y s
    change |((qA (y, s + 2 * Nat.find (hex y) + 4) / qB (y, s + 2 * Nat.find (hex y) + 4) : ℚ) : ℝ)
      - A y / B y| ≤ (2 : ℝ)⁻¹ ^ s
    generalize Nat.find (hex y) = tt at hlt hlow ⊢
    have hqAU := hqA y (s + 2 * tt + 4)
    have hqBU := hqB y (s + 2 * tt + 4)
    have hBy := hBpos y
    have hB' : (0 : ℝ) < (qB (y, s + 2 * tt + 4) : ℝ) := lt_trans (by positivity) hlow
    push_cast
    generalize hA' : (qA (y, s + 2 * tt + 4) : ℝ) = A' at hqAU ⊢
    generalize hB'' : (qB (y, s + 2 * tt + 4) : ℝ) = B' at hqBU hB' hlow ⊢
    have hdiff : A' / B' - A y / B y = (A' * B y - B' * A y) / (B' * B y) := by
      rw [div_sub_div _ _ hB'.ne' hBy.ne']
    rw [hdiff, abs_div, abs_of_pos (mul_pos hB' hBy), div_le_iff₀ (mul_pos hB' hBy)]
    have hnum : |A' * B y - B' * A y| ≤ 3 * (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) := by
      have e1 : A' * B y - B' * A y = (A' - A y) * B y + A y * (B y - B') := by ring
      rw [e1]
      have habs2 : |B y - B'| ≤ (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) := by
        rw [abs_sub_comm]; exact hqBU
      calc |(A' - A y) * B y + A y * (B y - B')|
          ≤ |(A' - A y) * B y| + |A y * (B y - B')| := abs_add_le _ _
        _ = |A' - A y| * B y + |A y| * |B y - B'| := by rw [abs_mul, abs_mul, abs_of_pos hBy]
        _ ≤ (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) * 1 + 2 * (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) := by
            apply add_le_add
            · exact mul_le_mul hqAU (hB1 y) hBy.le (by positivity)
            · exact mul_le_mul (hA2 y) habs2 (abs_nonneg _) (by norm_num)
        _ = 3 * (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) := by ring
    have hprod : (2 : ℝ)⁻¹ ^ tt / 2 * (2 : ℝ)⁻¹ ^ tt ≤ B' * B y :=
      mul_le_mul hlow.le hlt.le (by positivity) hB'.le
    have h3 : 3 / 16 * ((2 : ℝ)⁻¹ ^ tt) ^ 2 ≤ B' * B y := by
      nlinarith [hprod, sq_nonneg ((2 : ℝ)⁻¹ ^ tt)]
    have hs0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ s := by positivity
    calc |A' * B y - B' * A y| ≤ 3 * (2 : ℝ)⁻¹ ^ (s + 2 * tt + 4) := hnum
      _ = (2 : ℝ)⁻¹ ^ s * (3 / 16 * ((2 : ℝ)⁻¹ ^ tt) ^ 2) := by ring
      _ ≤ (2 : ℝ)⁻¹ ^ s * (B' * B y) := mul_le_mul_of_nonneg_left h3 hs0

private lemma not_isKurtzRandom_iff_exists_growth_ltr_listUnion_le (π : Measure CantorSeq)
    (l : List BitString) :
    π (⋃ x ∈ l, cantorCylinder x) ≤ (l.map (cantorMass π)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have : (⋃ x ∈ a :: t, cantorCylinder x) = cantorCylinder a ∪ ⋃ x ∈ t, cantorCylinder x := by
      ext v; simp
    rw [this, List.map_cons, List.sum_cons]
    exact (measure_union_le _ _).trans (add_le_add_right ih _)

private lemma not_isKurtzRandom_iff_exists_growth_ltr_dv1_toReal (n : ℕ) :
    (dyadicValue 1 n).toReal = (2 : ℝ)⁻¹ ^ n := by
  simp [dyadicValue, ENNReal.toReal_pow]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_dv1_ne_top (n : ℕ) : dyadicValue 1 n ≠
    ⊤ := by
  unfold dyadicValue
  exact (ENNReal.div_lt_top (by simp) (by simp)).ne

/-- A level at which `y` and all intervals of the list `l` are cylinders of the level. -/
private def not_isKurtzRandom_iff_exists_growth_ltr_lvl (l : List BitString) (y : BitString) :
    ℕ := y.length + (l.map List.length).sum

private def not_isKurtzRandom_iff_exists_growth_ltr_condZ (l : List BitString)
    (y z : BitString) : Bool :=
  y.isPrefixOf z && l.any (fun x => x.isPrefixOf z)

private lemma not_isKurtzRandom_iff_exists_growth_ltr_condZ_iff (l : List BitString)
    (y z : BitString) :
    not_isKurtzRandom_iff_exists_growth_ltr_condZ l y z = true ↔ y <+: z ∧ ∃ x ∈ l, x <+: z :=
        by
  simp [not_isKurtzRandom_iff_exists_growth_ltr_condZ, List.isPrefixOf_iff_prefix]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_inter_eq_biUnion (l : List BitString)
    (y : BitString) :
    cantorCylinder y ∩ (⋃ x ∈ l, cantorCylinder x) =
      ⋃ z ∈ (levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
          (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y), cantorCylinder z := by
  ext w
  constructor
  · rintro ⟨hy, hU⟩
    obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.mp hU
    have hy' : cantorPrefix w y.length = y := (isCantorPrefix_iff_cantorPrefix_eq y w).mp hy
    have hx' : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).mp hwx
    have hxl : x.length ≤ not_isKurtzRandom_iff_exists_growth_ltr_lvl l y := by
      have : x.length ≤ (l.map List.length).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)
      unfold not_isKurtzRandom_iff_exists_growth_ltr_lvl; omega
    have hyl : y.length ≤ not_isKurtzRandom_iff_exists_growth_ltr_lvl l y := by
      unfold not_isKurtzRandom_iff_exists_growth_ltr_lvl; omega
    have hypre : y <+: cantorPrefix w (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) := by
      have := cantorPrefix_mono w hyl
      rwa [hy'] at this
    have hxpre : x <+: cantorPrefix w (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) := by
      have := cantorPrefix_mono w hxl
      rwa [hx'] at this
    refine Set.mem_iUnion₂.mpr ⟨cantorPrefix w (not_isKurtzRandom_iff_exists_growth_ltr_lvl l
        y),
      List.mem_filter.mpr ⟨mem_levelList.mpr (cantorPrefix_length _ _),
        (not_isKurtzRandom_iff_exists_growth_ltr_condZ_iff _ _ _).mpr ⟨hypre, x, hx, hxpre⟩⟩,
            ?_⟩
    exact (isCantorPrefix_iff_cantorPrefix_eq _ w).mpr (by rw [cantorPrefix_length])
  · intro hw
    obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨-, hcond⟩ := List.mem_filter.mp hz
    obtain ⟨hyz, x, hx, hxz⟩ := (not_isKurtzRandom_iff_exists_growth_ltr_condZ_iff _ _ _).mp
        hcond
    exact ⟨cantorCylinder_subset_of_prefix hyz hwz,
      Set.mem_iUnion₂.mpr ⟨x, hx, cantorCylinder_subset_of_prefix hxz hwz⟩⟩

private lemma not_isKurtzRandom_iff_exists_growth_ltr_nuR_eq_sum (π : Measure CantorSeq)
    [IsProbabilityMeasure π] (l : List BitString)
    (y : BitString) :
    not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ l, cantorCylinder x) y =
      (((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
          (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).map (massR π)).sum := by
  unfold not_isKurtzRandom_iff_exists_growth_ltr_nuR
  rw [not_isKurtzRandom_iff_exists_growth_ltr_inter_eq_biUnion]
  have hnd : ((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).Nodup := (nodup_levelList _).filter
      _
  have hdisj : Set.PairwiseDisjoint
      (↑((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
          (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).toFinset : Set BitString)
          cantorCylinder := by
    intro a ha b hb hab
    have ha' := List.mem_filter.mp (List.mem_toFinset.mp (Finset.mem_coe.mp ha))
    have hb' := List.mem_filter.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hb))
    have hla : a.length = not_isKurtzRandom_iff_exists_growth_ltr_lvl l y :=
        mem_levelList.mp ha'.1
    have hlb : b.length = not_isKurtzRandom_iff_exists_growth_ltr_lvl l y :=
        mem_levelList.mp hb'.1
    exact cantorCylinder_disjoint_of_incompatible
      (fun h => hab (List.IsPrefix.eq_of_length h (by rw [hla, hlb])))
      (fun h => hab (List.IsPrefix.eq_of_length h (by rw [hla, hlb])).symm)
  have hset : (⋃ z ∈ (levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y), cantorCylinder z) =
      ⋃ z ∈ ((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
          (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).toFinset, cantorCylinder z :=
          by
    ext w; simp
  rw [hset, measure_biUnion_finset hdisj (fun z _ => measurableSet_cantorCylinder z),
    ENNReal.toReal_sum (fun z _ => measure_ne_top _ _), List.sum_toFinset _ hnd]
  rfl

private lemma not_isKurtzRandom_iff_exists_growth_ltr_abs_sum_map_sub_le {α : Type*}
    (Zl : List α) (r : α → ℚ) (m : α → ℝ) (ε : ℝ)
    (h : ∀ z ∈ Zl, |(r z : ℝ) - m z| ≤ ε) :
    |(((Zl.map r).sum : ℚ) : ℝ) - (Zl.map m).sum| ≤ Zl.length * ε := by
  induction Zl with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    rw [Rat.cast_add]
    calc |(r a : ℝ) + (((t.map r).sum : ℚ) : ℝ) - (m a + (t.map m).sum)|
        = |((r a : ℝ) - m a) + ((((t.map r).sum : ℚ) : ℝ) - (t.map m).sum)| := by ring_nf
      _ ≤ |(r a : ℝ) - m a| + |(((t.map r).sum : ℚ) : ℝ) - (t.map m).sum| := abs_add_le _ _
      _ ≤ ε + t.length * ε := add_le_add h1 h2
      _ = ((t.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

private lemma not_isKurtzRandom_iff_exists_growth_ltr_length_levelList (n : ℕ) :
    (levelList n).length = 2 ^ n := by
  induction n with
  | zero => simp [levelList]
  | succ n ih => simp [levelList, ih, pow_succ]; ring

/-- The rational approximation of `π(Ω_y ∩ U_n)`: the finite sum of the approximations. -/
private def not_isKurtzRandom_iff_exists_growth_ltr_qdef (a : BitString → ℕ → ℕ)
    (l : List BitString) (y : BitString) (s : ℕ) : ℚ :=
  (((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).map
    (fun z => ((a z (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) : ℕ) : ℚ) /
                ((2 ^ (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) : ℕ) : ℚ))).sum

private lemma not_isKurtzRandom_iff_exists_growth_ltr_qdef_error {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, |((a x s : ℕ) : ℝ) / 2 ^ s - massR π x| ≤ (2 : ℝ)⁻¹ ^ s)
    (l : List BitString) (y : BitString) (s : ℕ) :
    |(not_isKurtzRandom_iff_exists_growth_ltr_qdef a l y s : ℝ) -
        not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ l, cantorCylinder x) y| ≤
        (2 : ℝ)⁻¹ ^ s := by
  rw [not_isKurtzRandom_iff_exists_growth_ltr_nuR_eq_sum]
  have key := not_isKurtzRandom_iff_exists_growth_ltr_abs_sum_map_sub_le
      ((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y))
    (fun z => ((a z (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) : ℕ) : ℚ) /
                ((2 ^ (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) : ℕ) : ℚ))
                (massR π)
    ((2 : ℝ)⁻¹ ^ (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)) (fun z _ => by
      have := ha z (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)
      push_cast
      exact this)
  have hlen : (((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).length : ℝ) ≤
      2 ^ not_isKurtzRandom_iff_exists_growth_ltr_lvl l y := by
    have := List.length_filter_le (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)
        (levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y))
    rw [not_isKurtzRandom_iff_exists_growth_ltr_length_levelList] at this
    exact_mod_cast this
  calc |(not_isKurtzRandom_iff_exists_growth_ltr_qdef a l y s : ℝ) -
      (((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).map (massR π)).sum|
      ≤ _ := key
    _ ≤ 2 ^ not_isKurtzRandom_iff_exists_growth_ltr_lvl l y * (2 : ℝ)⁻¹ ^
        (s + not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = (2 : ℝ)⁻¹ ^ s := by
        rw [pow_add, mul_left_comm, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, mul_one]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_lvl_eq (l : List BitString)
    (y : BitString) :
    not_isKurtzRandom_iff_exists_growth_ltr_lvl l y = y.length + l.foldr
        (fun x acc => x.length + acc) 0 := by
  unfold not_isKurtzRandom_iff_exists_growth_ltr_lvl
  congr 1
  induction l with
  | nil => simp
  | cons x t ih => simp [ih]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_isPrefixOf_eq (x z : BitString) :
    x.isPrefixOf z = decide (z.take x.length = x) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.isPrefixOf_iff_prefix, decide_eq_true_iff, List.prefix_iff_eq_take, eq_comm]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_any_eq_foldr {α : Type*} (p : α → Bool)
    (l : List α) :
    l.any p = l.foldr (fun x acc => p x || acc) false := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [List.any_cons, ih]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_condZ_eq (l : List BitString)
    (y z : BitString) :
    not_isKurtzRandom_iff_exists_growth_ltr_condZ l y z = (decide (z.take y.length = y) &&
      l.foldr (fun x acc => decide (z.take x.length = x) || acc) false) := by
  unfold not_isKurtzRandom_iff_exists_growth_ltr_condZ
  rw [not_isKurtzRandom_iff_exists_growth_ltr_isPrefixOf_eq,
    not_isKurtzRandom_iff_exists_growth_ltr_any_eq_foldr]
  simp only [not_isKurtzRandom_iff_exists_growth_ltr_isPrefixOf_eq]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_primrec_condZ : Primrec
    (fun p : List BitString × BitString × BitString =>
    not_isKurtzRandom_iff_exists_growth_ltr_condZ p.1 p.2.1 p.2.2) := by
  have hy : Primrec (fun p : List BitString × BitString × BitString => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hz : Primrec (fun p : List BitString × BitString × BitString => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have h1 : Primrec (fun p : List BitString × BitString × BitString =>
      decide (p.2.2.take p.2.1.length = p.2.1)) :=
    (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp hy) hz) hy).decide
  have h2 : Primrec (fun p : List BitString × BitString × BitString =>
      p.1.foldr (fun x acc => decide (p.2.2.take x.length = x) || acc) false) :=
    Primrec.list_foldr
      (h := fun (p : List BitString × BitString × BitString) (r : BitString × Bool) =>
        decide (p.2.2.take r.1.length = r.1) || r.2)
      Primrec.fst (Primrec.const false)
      (Primrec.or.comp
        (Primrec.eq.comp (Primrec.list_take.comp
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) (hz.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)).decide
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.and.comp h1 h2).of_eq (fun p =>
    (not_isKurtzRandom_iff_exists_growth_ltr_condZ_eq _ _ _).symm)

/-- `qdef` with the precision `t` as a free parameter. -/
private def not_isKurtzRandom_iff_exists_growth_ltr_qdef' (a : BitString → ℕ → ℕ)
    (l : List BitString) (y : BitString) (t : ℕ) : ℚ :=
  (((levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).filter
      (not_isKurtzRandom_iff_exists_growth_ltr_condZ l y)).map
    (fun z => ((a z t : ℕ) : ℚ) / ((2 ^ t : ℕ) : ℚ))).sum

private lemma not_isKurtzRandom_iff_exists_growth_ltr_qdef'_eq_foldr (a : BitString → ℕ → ℕ)
    (l : List BitString) (y : BitString) (t : ℕ) :
    not_isKurtzRandom_iff_exists_growth_ltr_qdef' a l y t =
        (levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y)).foldr (fun z acc =>
      bif not_isKurtzRandom_iff_exists_growth_ltr_condZ l y z then
        ((a z t : ℕ) : ℚ) / ((2 ^ t : ℕ) : ℚ) + acc else acc) 0 := by
  unfold not_isKurtzRandom_iff_exists_growth_ltr_qdef'
  generalize levelList (not_isKurtzRandom_iff_exists_growth_ltr_lvl l y) = L
  induction L with
  | nil => simp
  | cons z t' ih =>
    cases hc : not_isKurtzRandom_iff_exists_growth_ltr_condZ l y z
    · rw [List.filter_cons_of_neg (by simp [hc]), List.foldr_cons]
      simp only [hc, Bool.cond_false]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [hc]), List.map_cons, List.sum_cons, List.foldr_cons]
      simp only [hc, Bool.cond_true]
      rw [ih]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_primrec_lvl : Primrec
    (fun p : List BitString × BitString => not_isKurtzRandom_iff_exists_growth_ltr_lvl p.1
                                             p.2) := by
  have hfold : Primrec (fun p : List BitString × BitString =>
      p.1.foldr (fun x acc => x.length + acc) 0) :=
    Primrec.list_foldr
      (h := fun (p : List BitString × BitString) (r : BitString × ℕ) => r.1.length + r.2)
      Primrec.fst (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.snd) hfold).of_eq
    (fun p => (not_isKurtzRandom_iff_exists_growth_ltr_lvl_eq _ _).symm)

/-- The step function of the right fold that computes `qdef'` is computable. -/
private lemma not_isKurtzRandom_iff_exists_growth_ltr_computable_step {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) :
    Computable₂ (fun (p : List BitString × BitString × ℕ) (r : BitString × ℚ) =>
      bif not_isKurtzRandom_iff_exists_growth_ltr_condZ p.1 p.2.1 r.1 then
        ((a r.1 p.2.2 : ℕ) : ℚ) / ((2 ^ p.2.2 : ℕ) : ℚ) + r.2
      else r.2) := by
  have hg : Computable (fun x : (List BitString × BitString × ℕ) × (BitString × ℚ) =>
      (x.1.1, x.1.2.1, x.2.1)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.fst.comp Computable.snd))
  have hcond := not_isKurtzRandom_iff_exists_growth_ltr_primrec_condZ.to_comp.comp hg
  have hterm : Computable (fun x : (List BitString × BitString × ℕ) × (BitString × ℚ) =>
      ((a x.2.1 x.1.2.2 : ℕ) : ℚ) / ((2 ^ x.1.2.2 : ℕ) : ℚ)) := by
    refine computable_of_num_den
      (N := fun x : (List BitString × BitString × ℕ) × (BitString × ℚ) =>
        ((a x.2.1 x.1.2.2 : ℕ) : ℤ))
      (D := fun x : (List BitString × BitString × ℕ) × (BitString × ℚ) => 2 ^ x.1.2.2)
      ?_ ?_ (fun x => Nat.two_pow_pos _) (fun x => by simp)
    · exact ComputableReals.primrec_natCastInt.to_comp.comp
        (ha.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    · exact comp_pow.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  exact Computable.cond hcond
    (Computable₂.comp computable₂_ratAdd hterm (Computable.snd.comp Computable.snd))
    (Computable.snd.comp Computable.snd)

private lemma not_isKurtzRandom_iff_exists_growth_ltr_computable_qdef' {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) :
    Computable (fun p : List BitString × BitString × ℕ =>
      not_isKurtzRandom_iff_exists_growth_ltr_qdef' a p.1 p.2.1 p.2.2) := by
  have hg : Computable (fun p : List BitString × BitString × ℕ => (p.1, p.2.1)) :=
    Computable.pair Computable.fst (Computable.fst.comp Computable.snd)
  have hlvl := not_isKurtzRandom_iff_exists_growth_ltr_primrec_lvl.to_comp.comp hg
  exact (Computable.list_foldr (computable_levelList.comp hlvl) (Computable.const (0 : ℚ))
    (not_isKurtzRandom_iff_exists_growth_ltr_computable_step ha)).of_eq
    (fun p => (not_isKurtzRandom_iff_exists_growth_ltr_qdef'_eq_foldr a p.1 p.2.1 p.2.2).symm)

private lemma not_isKurtzRandom_iff_exists_growth_ltr_exists_massR_approx
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) : ∃ a : BitString → ℕ → ℕ, Computable₂ a ∧
      ∀ x s, |((a x s : ℕ) : ℝ) / 2 ^ s - massR π x| ≤ (2 : ℝ)⁻¹ ^ s := by
  obtain ⟨a, ha, hab⟩ := hπ
  refine ⟨a, ha, fun y s => ?_⟩
  obtain ⟨h1, h2⟩ := hab y s
  have hne : ∀ n s : ℕ, dyadicValue n s ≠ ⊤ := fun n s => by
    unfold dyadicValue
    exact (ENNReal.div_lt_top (by simp) (by simp)).ne
  have hdv : ∀ n s : ℕ, (dyadicValue n s).toReal = (n : ℝ) / 2 ^ s := fun n s => by
    simp [dyadicValue, ENNReal.toReal_div, ENNReal.toReal_pow]
  have hne2 : cantorMass π y ≠ ⊤ := measure_ne_top _ _
  have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne2, hne 1 s⟩) h1
  have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne _ _, hne 1 s⟩) h2
  rw [ENNReal.toReal_add hne2 (hne 1 s), hdv, hdv] at e1
  rw [ENNReal.toReal_add (hne _ _) (hne 1 s), hdv, hdv] at e2
  have h2s : (1 : ℝ) / 2 ^ s = (2 : ℝ)⁻¹ ^ s := by rw [one_div, inv_pow]
  have hm : (cantorMass π y).toReal = massR π y := rfl
  rw [hm] at e1 e2
  simp only [Nat.cast_one] at e1 e2
  rw [abs_le]
  constructor <;> linarith [h2s]

/-- Uniform computability of `π(Ω_y ∩ U_n)`: the identity, the error analysis and the
computability of the explicit finite sum. -/
private lemma not_isKurtzRandom_iff_exists_growth_ltr_nuR_uniform {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (f : ℕ → List BitString) (hfc : Computable f) :
    ∃ q : ℕ × BitString × ℕ → ℚ, Computable q ∧ ∀ n y s,
      |(q (n, y, s) : ℝ) - not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n,
          cantorCylinder x) y| ≤ (2 : ℝ)⁻¹ ^ s := by
  obtain ⟨a, ha, hab⟩ := not_isKurtzRandom_iff_exists_growth_ltr_exists_massR_approx hπ
  refine ⟨fun p => not_isKurtzRandom_iff_exists_growth_ltr_qdef' a (f p.1) p.2.1
                     (p.2.2 + not_isKurtzRandom_iff_exists_growth_ltr_lvl (f p.1) p.2.1), ?_,
                     ?_⟩
  · have h1 : Computable (fun p : ℕ × BitString × ℕ => f p.1) := hfc.comp Computable.fst
    have h2 : Computable (fun p : ℕ × BitString × ℕ => p.2.1) :=
      Computable.fst.comp Computable.snd
    have h3 : Computable (fun p : ℕ × BitString × ℕ => p.2.2) :=
      Computable.snd.comp Computable.snd
    have h12 : Computable (fun p : ℕ × BitString × ℕ => ((f p.1, p.2.1) : List BitString ×
                                                          BitString)) :=
      Computable.pair h1 h2
    have hlv : Computable (fun p : ℕ × BitString ×
        ℕ => not_isKurtzRandom_iff_exists_growth_ltr_lvl (f p.1) p.2.1) :=
      Computable.comp (g := fun p : ℕ × BitString × ℕ => ((f p.1, p.2.1) : List BitString ×
                                                           BitString))
        (f := fun q : List BitString × BitString =>
          not_isKurtzRandom_iff_exists_growth_ltr_lvl q.1 q.2)
          not_isKurtzRandom_iff_exists_growth_ltr_primrec_lvl.to_comp h12
    have h4 : Computable (fun p : ℕ × BitString × ℕ =>
        p.2.2 + not_isKurtzRandom_iff_exists_growth_ltr_lvl (f p.1) p.2.1) :=
      Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp h3 hlv
    have hg : Computable (fun p : ℕ × BitString × ℕ =>
        ((f p.1, p.2.1, p.2.2 + not_isKurtzRandom_iff_exists_growth_ltr_lvl (f p.1) p.2.1) :
            List BitString × BitString × ℕ)) :=
      Computable.pair h1 (Computable.pair h2 h4)
    exact Computable.comp (g := fun p : ℕ × BitString × ℕ =>
        ((f p.1, p.2.1, p.2.2 + not_isKurtzRandom_iff_exists_growth_ltr_lvl (f p.1) p.2.1) :
            List BitString × BitString × ℕ))
      (f := fun p : List BitString × BitString ×
          ℕ => not_isKurtzRandom_iff_exists_growth_ltr_qdef' a p.1 p.2.1 p.2.2)
                 (not_isKurtzRandom_iff_exists_growth_ltr_computable_qdef' ha) hg
  · intro n y s
    exact not_isKurtzRandom_iff_exists_growth_ltr_qdef_error hab (f n) y s

private theorem not_isKurtzRandom_iff_exists_growth_ltr_ltr_computable {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x)
    (f : ℕ → List BitString) (hfc : Computable f)
    (hf : ∀ n, ((f n).map (cantorMass π)).sum ≤ dyadicValue 1 n) :
    IsComputableOnStrings
      (fun y => ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n, cantorCylinder
          x) y / massR π y) := by
  have hnn : ∀ n y, 0 ≤ not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n,
      cantorCylinder x) y := fun n y => ENNReal.toReal_nonneg
  have hbound : ∀ n y, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n,
      cantorCylinder x) y ≤ (2 : ℝ)⁻¹ ^ n := by
    intro n y
    have h1 : π (cantorCylinder y ∩ ⋃ x ∈ f n, cantorCylinder x) ≤ dyadicValue 1 n :=
      calc π (cantorCylinder y ∩ ⋃ x ∈ f n, cantorCylinder x)
          ≤ π (⋃ x ∈ f n, cantorCylinder x) := measure_mono Set.inter_subset_right
        _ ≤ ((f n).map (cantorMass π)).sum :=
            not_isKurtzRandom_iff_exists_growth_ltr_listUnion_le π (f n)
        _ ≤ dyadicValue 1 n := hf n
    have h2 := ENNReal.toReal_mono (not_isKurtzRandom_iff_exists_growth_ltr_dv1_ne_top n) h1
    rw [not_isKurtzRandom_iff_exists_growth_ltr_dv1_toReal] at h2
    exact h2
  have hgeo : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) :=
    summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
  have hsumm : ∀ y, Summable (fun n => not_isKurtzRandom_iff_exists_growth_ltr_nuR π
                                         (⋃ x ∈ f n, cantorCylinder x) y) := fun y =>
    Summable.of_nonneg_of_le (hnn · y) (hbound · y) hgeo
  have hA : IsComputableOnStrings
      (fun y => ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n, cantorCylinder
          x) y) :=
    not_isKurtzRandom_iff_exists_growth_ltr_tsum_comp
      (not_isKurtzRandom_iff_exists_growth_ltr_nuR_uniform hπ f hfc) hnn hbound
  have hB := not_isKurtzRandom_iff_exists_growth_ltr_massR_comp hπ
  have hBpos : ∀ y, 0 < massR π y := fun y =>
    ENNReal.toReal_pos (hpos y).ne' (measure_ne_top _ _)
  have hB1 : ∀ y, massR π y ≤ 1 := fun y => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := π) (s := cantorCylinder y))
    simpa [massR, cantorMass] using this
  have hA2 : ∀ y, |∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n,
      cantorCylinder x) y| ≤ 2 := by
    intro y
    rw [abs_of_nonneg (tsum_nonneg fun n => hnn n y)]
    calc ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n, cantorCylinder x) y ≤
        ∑' n : ℕ, (2 : ℝ)⁻¹ ^ n :=
          Summable.tsum_le_tsum (hbound · y) (hsumm y) hgeo
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hdiv := not_isKurtzRandom_iff_exists_growth_ltr_div_comp hA hB hA2 hB1 hBpos
  have heq : (fun y => ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n,
      cantorCylinder x) y / massR π y) =
      fun y => (∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n, cantorCylinder
                 x) y) / massR π y :=
    funext fun y => tsum_div_const
  rw [heq]
  exact hdiv

/-- The mixed capital of a Kurtz cover `f`. -/
private noncomputable def not_isKurtzRandom_iff_exists_growth_ltr_mixCap
    (π : Measure CantorSeq) (f : ℕ → List BitString) (y : BitString) : ℝ :=
  ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (⋃ x ∈ f n, cantorCylinder x) y /
      massR π y

/-- The growth function of a Kurtz cover `f`. -/
private def not_isKurtzRandom_iff_exists_growth_ltr_growthFn (f : ℕ → List BitString) (k : ℕ)
    : ℕ :=
  ((Finset.range (k + 1)).filter (fun n => ∀ x ∈ f n, x.length ≤ k)).card

private lemma not_isKurtzRandom_iff_exists_growth_ltr_nuR_add {π : Measure CantorSeq}
    [IsProbabilityMeasure π] {U : Set CantorSeq}
    (y : BitString) :
    not_isKurtzRandom_iff_exists_growth_ltr_nuR π U y =
        not_isKurtzRandom_iff_exists_growth_ltr_nuR π U (y ++ [false]) +
        not_isKurtzRandom_iff_exists_growth_ltr_nuR π U (y ++ [true]) := by
  have h := cantorMass_add (π.restrict U) y
  simp only [cantorMass, Measure.restrict_apply (measurableSet_cantorCylinder _)] at h
  unfold not_isKurtzRandom_iff_exists_growth_ltr_nuR
  rw [h, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

private theorem not_isKurtzRandom_iff_exists_growth_ltr_mixCap_spec {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hpos : ∀ x, 0 < cantorMass π x) (w : CantorSeq) (f : ℕ → List BitString)
    (hf : ∀ n, {w} ⊆ (⋃ x ∈ f n, cantorCylinder x) ∧
      ((f n).map (cantorMass π)).sum ≤ dyadicValue 1 n) :
    IsFairCapital π (not_isKurtzRandom_iff_exists_growth_ltr_mixCap π f) ∧
      ∀ k, ((not_isKurtzRandom_iff_exists_growth_ltr_growthFn f k : ℕ) : ℝ) ≤
          not_isKurtzRandom_iff_exists_growth_ltr_mixCap π f (cantorPrefix w k) := by
  classical
  unfold not_isKurtzRandom_iff_exists_growth_ltr_mixCap
    not_isKurtzRandom_iff_exists_growth_ltr_growthFn
  set U : ℕ → Set CantorSeq := fun n => ⋃ x ∈ f n, cantorCylinder x with hUdef
  have hmass_pos : ∀ y, 0 < massR π y := fun y =>
    ENNReal.toReal_pos (hpos y).ne' (measure_ne_top _ _)
  have hbound : ∀ n y, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) y ≤ (2 : ℝ)⁻¹ ^
      n := by
    intro n y
    have h1 : π (cantorCylinder y ∩ U n) ≤ dyadicValue 1 n :=
      calc π (cantorCylinder y ∩ U n) ≤ π (U n) := measure_mono Set.inter_subset_right
        _ ≤ ((f n).map (cantorMass π)).sum :=
            not_isKurtzRandom_iff_exists_growth_ltr_listUnion_le π (f n)
        _ ≤ dyadicValue 1 n := (hf n).2
    have h2 := ENNReal.toReal_mono (not_isKurtzRandom_iff_exists_growth_ltr_dv1_ne_top n) h1
    rw [not_isKurtzRandom_iff_exists_growth_ltr_dv1_toReal] at h2
    exact h2
  have hnn : ∀ n y, 0 ≤ not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) y :=
      fun n y => ENNReal.toReal_nonneg
  have hsum : ∀ y, Summable (fun n => not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) y)
      := fun y =>
    Summable.of_nonneg_of_le (hnn · y) (hbound · y)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
  have key : ∀ y, (∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) y / massR π y) *
      massR π y = ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) y := by
    intro y
    rw [← tsum_mul_right]
    exact tsum_congr fun n => div_mul_cancel₀ _ (hmass_pos y).ne'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y
    exact tsum_nonneg fun n => div_nonneg (hnn n y) (hmass_pos y).le
  · intro y
    change (∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) y / massR π y) * massR π
        y = _
    rw [key, key, key, ← Summable.tsum_add (hsum _) (hsum _)]
    exact tsum_congr fun n => not_isKurtzRandom_iff_exists_growth_ltr_nuR_add y
  · intro k
    set S := (Finset.range (k + 1)).filter (fun n => ∀ x ∈ f n, x.length ≤ k) with hS
    have hone : ∀ n ∈ S, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n)
        (cantorPrefix w k) / massR π (cantorPrefix w k) = 1 := by
      intro n hn
      have hlen : ∀ x ∈ f n, x.length ≤ k := (Finset.mem_filter.mp hn).2
      have hsub : cantorCylinder (cantorPrefix w k) ⊆ U n := by
        obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.mp ((hf n).1 (Set.mem_singleton w))
        intro v hv
        refine Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
        have hxw : x = cantorPrefix w x.length := ((isCantorPrefix_iff_cantorPrefix_eq x w).mp
            hwx).symm
        have hpre : x <+: cantorPrefix w k := by
          rw [hxw]; exact cantorPrefix_mono w (hlen x hx)
        exact cantorCylinder_subset_of_prefix hpre hv
      have : cantorCylinder (cantorPrefix w k) ∩ U n = cantorCylinder (cantorPrefix w k) :=
        Set.inter_eq_left.mpr hsub
      unfold not_isKurtzRandom_iff_exists_growth_ltr_nuR
      rw [this]
      exact div_self (hmass_pos _).ne'
    calc (S.card : ℝ)
        = ∑ n ∈ S, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) (cantorPrefix w k) /
            massR π (cantorPrefix w k) := by
          rw [Finset.sum_congr rfl hone]; simp
      _ ≤ ∑' n, not_isKurtzRandom_iff_exists_growth_ltr_nuR π (U n) (cantorPrefix w k) /
            massR π (cantorPrefix w k) :=
          Summable.sum_le_tsum S (fun n _ => div_nonneg (hnn n _) (hmass_pos _).le)
            ((hsum _).div_const _)

private lemma not_isKurtzRandom_iff_exists_growth_ltr_growthFn_monotone
    (f : ℕ → List BitString) : Monotone (not_isKurtzRandom_iff_exists_growth_ltr_growthFn f)
    := by
  intro k k' hkk'
  unfold not_isKurtzRandom_iff_exists_growth_ltr_growthFn
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, fun x hx => (hn.2 x hx).trans hkk'⟩

private lemma not_isKurtzRandom_iff_exists_growth_ltr_growthFn_unbounded
    (f : ℕ → List BitString) : ∀ B, ∃ k, B ≤ not_isKurtzRandom_iff_exists_growth_ltr_growthFn
    f k := by
  intro B
  obtain ⟨K, hK⟩ : ∃ K, ∀ n < B, ∀ x ∈ f n, x.length ≤ K := by
    refine ⟨(Finset.range B).sup (fun n => ((f n).map List.length).sum), fun n hn x hx => ?_⟩
    have h1 : x.length ≤ ((f n).map List.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hx)
    exact h1.trans (Finset.le_sup (f := fun n => ((f n).map List.length).sum)
      (Finset.mem_range.mpr hn))
  refine ⟨max B K, ?_⟩
  unfold not_isKurtzRandom_iff_exists_growth_ltr_growthFn
  have hsub : Finset.range B ⊆
      (Finset.range (max B K + 1)).filter (fun n => ∀ x ∈ f n, x.length ≤ max B K) := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, fun x hx => (hK n hn x hx).trans (le_max_right _ _)⟩
  simpa using Finset.card_le_card hsub

private lemma not_isKurtzRandom_iff_exists_growth_ltr_growthFn_eq (f : ℕ → List BitString)
    (k : ℕ) :
    not_isKurtzRandom_iff_exists_growth_ltr_growthFn f k = ((List.range (k + 1)).filter
      (fun n => decide (((f n).filter (fun x => decide (k < x.length))).length = 0))).length := by
  unfold not_isKurtzRandom_iff_exists_growth_ltr_growthFn
  rw [← List.toFinset_range, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext n
  simp [List.filter_eq_nil_iff]

private lemma not_isKurtzRandom_iff_exists_growth_ltr_growthFn_computable
    (f : ℕ → List BitString) (hfc : Computable f) :
    Computable (not_isKurtzRandom_iff_exists_growth_ltr_growthFn f) := by
  have hinner : Computable₂ (fun (k : ℕ) (n : ℕ) =>
      decide (((f n).filter (fun x => decide (k < x.length))).length = 0)) := by
    have h1 : Computable (fun p : ℕ × ℕ => ((f p.2).filter (fun x => decide (p.1 < x.length)))) :=
        by
      refine computable_list_filter (f := fun p : ℕ × ℕ => f p.2) (p := fun (p : ℕ × ℕ)
          (x : BitString) => decide (p.1 < x.length)) (hfc.comp Computable.snd) ?_
      exact (PrimrecRel.decide Primrec.nat_lt |>.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_length.comp Primrec.snd)).to_comp
    have h2 : Computable (fun p : ℕ × ℕ =>
      (((f p.2).filter (fun x => decide (p.1 < x.length))).length)) :=
      Computable.list_length.comp h1
    exact (PrimrecRel.decide (Primrec.eq : PrimrecRel (fun a b : ℕ => a = b)) |>.to_comp.comp h2
        (Computable.const 0)).to₂
  have h3 : Computable (fun k : ℕ => (List.range (k + 1)).filter
      (fun n => decide (((f n).filter (fun x => decide (k < x.length))).length = 0))) :=
    computable_list_filter (Primrec.list_range.to_comp.comp (Primrec.succ.to_comp)) hinner
  exact (Computable.list_length.comp h3).of_eq fun k =>
    (not_isKurtzRandom_iff_exists_growth_ltr_growthFn_eq f k).symm

private theorem not_isKurtzRandom_iff_exists_growth_ltr_growthFn_isComputableGrowth
    (f : ℕ → List BitString) (hfc : Computable f) :
    IsComputableGrowth (not_isKurtzRandom_iff_exists_growth_ltr_growthFn f) :=
  ⟨not_isKurtzRandom_iff_exists_growth_ltr_growthFn_computable f hfc,
    not_isKurtzRandom_iff_exists_growth_ltr_growthFn_monotone f,
    not_isKurtzRandom_iff_exists_growth_ltr_growthFn_unbounded f⟩

/-- Step 1 of the proof of `not_isKurtzRandom_iff_exists_growth`: the forward direction.
-/
private theorem not_isKurtzRandom_iff_exists_growth_ltr {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) (w : CantorSeq) :
    ¬ IsKurtzRandom π w → ∃ m g, IsFairCapital π m ∧ IsComputableOnStrings m ∧
      IsComputableGrowth g ∧ ∀ n, (g n : ℝ) ≤ m (cantorPrefix w n) := by
  intro h
  obtain ⟨f, hfc, hf⟩ := not_not.mp h
  obtain ⟨hfair, hgrow⟩ := not_isKurtzRandom_iff_exists_growth_ltr_mixCap_spec hpos w f hf
  exact ⟨not_isKurtzRandom_iff_exists_growth_ltr_mixCap π f,
    not_isKurtzRandom_iff_exists_growth_ltr_growthFn f, hfair,
    not_isKurtzRandom_iff_exists_growth_ltr_ltr_computable hπ hpos f hfc (fun n => (hf n).2),
    not_isKurtzRandom_iff_exists_growth_ltr_growthFn_isComputableGrowth f hfc, hgrow⟩

/-- Step 1 of the proof of `not_isKurtzRandom_iff_exists_growth_rtl`: the total
mass of a duplicate-free list of equal-length strings on which the capital is at least `K > 0` is
at most `m(Λ) / K` (the cylinders are disjoint and contained in the Ville set). -/
private lemma not_isKurtzRandom_iff_exists_growth_mass
    {π : Measure CantorSeq} [IsProbabilityMeasure π] {m : BitString → ℝ}
    (hm : IsFairCapital π m) (L : List BitString) (hnd : L.Nodup) (l : ℕ)
    (hlen : ∀ x ∈ L, x.length = l) {K : ℝ} (hK : 0 < K) (hLK : ∀ x ∈ L, K ≤ m x) :
    (L.map (cantorMass π)).sum ≤ ENNReal.ofReal (m [] / K) := by
  classical
  have hdisj : (L.toFinset : Set BitString).PairwiseDisjoint cantorCylinder := by
    intro x hx y hy hxy
    have hx' := hlen x (List.mem_toFinset.1 hx)
    have hy' := hlen y (List.mem_toFinset.1 hy)
    have hlength : x.length = y.length := hx'.trans hy'.symm
    refine cantorCylinder_disjoint_of_incompatible ?_ ?_
    · intro hp
      exact hxy (hp.eq_of_length hlength)
    · intro hp
      exact hxy (hp.eq_of_length hlength.symm).symm
  have hsum : (L.map (cantorMass π)).sum = π (⋃ x ∈ L.toFinset, cantorCylinder x) := by
    rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_cantorCylinder x),
      List.sum_toFinset _ hnd]
    rfl
  rw [hsum]
  refine le_trans (measure_mono ?_) (measure_exists_ge_le hm hK)
  intro w hw
  simp only [Set.mem_iUnion] at hw
  obtain ⟨x, hx, hwx⟩ := hw
  have hxl := hlen x (List.mem_toFinset.1 hx)
  refine ⟨l, ?_⟩
  have hpre : x = cantorPrefix w l := by
    have h1 : IsCantorPrefix x w := hwx
    have := (isCantorPrefix_iff_cantorPrefix_eq x w).1 h1
    rw [hxl] at this
    exact this.symm
  rw [← hpre]
  exact hLK x (List.mem_toFinset.1 hx)

/-- Step 2 of the proof of `not_isKurtzRandom_iff_exists_growth`: the reverse direction.
-/
private theorem not_isKurtzRandom_iff_exists_growth_rtl {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (w : CantorSeq) :
    (∃ m g, IsFairCapital π m ∧ IsComputableOnStrings m ∧
      IsComputableGrowth g ∧ ∀ n, (g n : ℝ) ≤ m (cantorPrefix w n)) → ¬ IsKurtzRandom π w := by
  classical
  rintro ⟨m, g, hm, ⟨q, hqc, hqe⟩, hg, hgm⟩ hrand
  apply hrand
  set M : ℕ := ⌈m []⌉₊ with hM
  have hex : ∀ k, ∃ l, (M + 1) * 2 ^ k + 2 ≤ g l := fun k => hg.unbounded _
  have hcc : Computable (fun k : ℕ => (M + 1) * 2 ^ k + 2) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const (M + 1))
      Computable.pow2) (Computable.const 2)
  have hdc : Computable (fun k : ℕ => (M + 1) * 2 ^ k + 1) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const (M + 1))
      Computable.pow2) (Computable.const 1)
  have hlk : Computable (fun k => Nat.find (hex k)) := by
    apply Computable.natFind (P := fun k l => (M + 1) * 2 ^ k + 2 ≤ g l) ?_ hex
    exact (PrimrecRel.decide Primrec.nat_le).to_comp.comp (hcc.comp Computable.fst)
      (hg.computable.comp Computable.snd)
  have hp : Computable₂ (fun (k : ℕ) (x : BitString) =>
      decide ((((M + 1) * 2 ^ k + 1 : ℕ) : ℚ) ≤ q (x, 0))) := by
    exact ComputableReals.primrec_ratLe.decide.to_comp.comp
      (ComputableReals.computable_natCastRat.comp (hdc.comp Computable.fst))
      (hqc.comp (Computable.pair Computable.snd (Computable.const 0)))
  refine ⟨fun k => (levelList (Nat.find (hex k))).filter
    (fun x => decide ((((M + 1) * 2 ^ k + 1 : ℕ) : ℚ) ≤ q (x, 0))),
    computable_list_filter (computable_levelList.comp hlk) hp, fun k => ?_⟩
  dsimp only
  have hspec := Nat.find_spec (hex k)
  generalize Nat.find (hex k) = l at hspec
  have hKpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) * 2 ^ k := by positivity
  have hmem : ∀ x ∈ (levelList l).filter
      (fun x => decide ((((M + 1) * 2 ^ k + 1 : ℕ) : ℚ) ≤ q (x, 0))),
      x.length = l ∧ ((M + 1 : ℕ) : ℝ) * 2 ^ k ≤ m x := by
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxl := mem_levelList.1 hx1
    refine ⟨hxl, ?_⟩
    have h1 : ((((M + 1) * 2 ^ k + 1 : ℕ) : ℚ)) ≤ q (x, 0) := of_decide_eq_true hx2
    have h2 : (((M + 1) * 2 ^ k + 1 : ℕ) : ℝ) ≤ (q (x, 0) : ℝ) := by exact_mod_cast h1
    have h3 := (abs_le.1 (hqe x 0)).2
    push_cast at h2
    simp only [pow_zero] at h3
    push_cast
    linarith
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    simp only [Set.mem_iUnion]
    refine ⟨cantorPrefix v l, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨mem_levelList.2 (by simp), ?_⟩
      apply decide_eq_true
      have h1 : (((M + 1) * 2 ^ k + 2 : ℕ) : ℝ) ≤ (g l : ℝ) := by exact_mod_cast hspec
      have h2 := hgm l
      have h3 := (abs_le.1 (hqe (cantorPrefix v l) 0)).1
      simp only [pow_zero] at h3
      have h4 : (((M + 1) * 2 ^ k + 1 : ℕ) : ℝ) ≤ (q (cantorPrefix v l, 0) : ℝ) := by
        push_cast at h1 ⊢
        linarith
      exact_mod_cast h4
    · change IsCantorPrefix (cantorPrefix v l) v
      rw [isCantorPrefix_iff_cantorPrefix_eq]
      simp
  · have hnd : ((levelList l).filter
        (fun x => decide ((((M + 1) * 2 ^ k + 1 : ℕ) : ℚ) ≤ q (x, 0)))).Nodup :=
      List.Nodup.filter _ (nodup_levelList l)
    refine le_trans (not_isKurtzRandom_iff_exists_growth_mass hm _ hnd l
      (fun x hx => (hmem x hx).1) hKpos (fun x hx => (hmem x hx).2)) ?_
    rw [dyadicValue_one_eq_inv_two_pow']
    have hm0 : m [] ≤ ((M + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (m [])
      push_cast
      linarith
    have h5 : m [] / (((M + 1 : ℕ) : ℝ) * 2 ^ k) ≤ ((2 : ℝ)⁻¹) ^ k := by
      rw [div_le_iff₀ hKpos, inv_pow]
      have : ((2 : ℝ) ^ k)⁻¹ * (((M + 1 : ℕ) : ℝ) * 2 ^ k) = ((M + 1 : ℕ) : ℝ) := by
        field_simp
      rw [this]
      exact hm0
    calc ENNReal.ofReal (m [] / (((M + 1 : ℕ) : ℝ) * 2 ^ k))
        ≤ ENNReal.ofReal (((2 : ℝ)⁻¹) ^ k) := ENNReal.ofReal_le_ofReal h5
      _ = (2 : ℝ≥0∞)⁻¹ ^ k := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

/-- **SUV Problem 272, p. 284.**  `ω` is not Kurtz random exactly when some computable martingale
tends to infinity computably on the prefixes of `ω`, i.e., has a computable monotone unbounded lower
bound along `ω`.  Positivity is the standing assumption of this section. -/
theorem not_isKurtzRandom_iff_exists_growth {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) (w : CantorSeq) :
    ¬ IsKurtzRandom π w ↔ ∃ m g, IsFairCapital π m ∧ IsComputableOnStrings m ∧
      IsComputableGrowth g ∧ ∀ n, (g n : ℝ) ≤ m (cantorPrefix w n) := by
  exact ⟨not_isKurtzRandom_iff_exists_growth_ltr hπ hpos w,
      not_isKurtzRandom_iff_exists_growth_rtl w⟩

end Kolmogorov.FrequencyGames
