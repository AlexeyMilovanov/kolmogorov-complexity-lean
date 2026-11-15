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
# Randomness Basics

Computable randomness of a sequence with respect to a computable measure `π`: no computable
`π`-martingale is unbounded on its prefixes.

Main declarations:

* `IsComputablyRandom`: the definition, in terms of computable fair capitals that do not win;
* `isComputablyRandom_iff_ge_half`, `isComputablyRandom_iff_rational`: equivalent formulations
  using martingales separated from zero, resp. exactly computable rational-valued martingales
  (SUV Problem 266);
* `isComputablyRandom_of_isMartinLofRandom`: Martin-Löf randomness implies computable randomness
  (SUV Theorem 182(a));
* `exists_computable_seq_bounded`, `not_isComputablyRandom_of_computable`,
  `not_exists_largest_computable_capital`: a computable martingale is bounded on some computable
  sequence, so computable sequences are not computably random and there is no largest computable
  martingale (SUV p. 280).

This formalizes the discussion of computable randomness in Shen, Uspensky and Vereshchagin,
*Kolmogorov complexity and algorithmic randomness* (pp. 279-280).
-/

namespace Kolmogorov.FrequencyGames

open MeasureTheory Filter Topology ComputableReals

/-- **SUV p. 279.**  `ω` is *computably random* with respect to `π`: every computable `π`-martingale
is bounded on its prefixes. -/
def IsComputablyRandom (π : Measure CantorSeq) (w : CantorSeq) : Prop :=
  ∀ m, IsFairCapital π m → IsComputableOnStrings m → ¬ Wins m w

private lemma isComputablyRandom_iff_ge_half_isFairCapital {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    {m : BitString → ℝ} (hm : IsFairCapital π m) :
    IsFairCapital π (fun x => 1 / 2 + 1 / 2 * m x) where
  nonneg x := by
    have h1 := hm.nonneg x
    positivity
  fair x := by
    have h1 := hm.fair x
    have h2 := massR_add (π := π) x
    linarith

private lemma isComputablyRandom_iff_ge_half_isComputableOnStrings {m : BitString → ℝ}
    (hm : IsComputableOnStrings m) :
    IsComputableOnStrings (fun x => 1 / 2 + 1 / 2 * m x) := by
  rcases hm with ⟨q, hq, hbound⟩
  use fun p => 1 / 2 + 1 / 2 * q (p.1, p.2 + 1)
  constructor
  · have h1 : Computable (fun p : BitString × ℕ => p.1) := Computable.fst
    have h2 : Computable (fun p : BitString × ℕ => p.2 + 1) := (Primrec.succ.to_comp).comp
        Computable.snd
    have h3 : Computable (fun p : BitString × ℕ => (p.1, p.2 + 1)) := Computable.pair h1 h2
    have h4 : Computable (fun p : BitString × ℕ => q (p.1, p.2 + 1)) := hq.comp h3
    have h5 : Computable (fun p : BitString × ℕ => 1 / 2 * q (p.1, p.2 + 1)) :=
      computable₂_ratMul.comp (Computable.const (1 / 2)) h4
    have h6 : Computable (fun p : BitString × ℕ => 1 / 2 + 1 / 2 * q (p.1, p.2 + 1)) :=
      computable₂_ratAdd.comp (Computable.const (1 / 2)) h5
    exact h6
  · intro x s
    have h := hbound x (s + 1)
    dsimp only
    have this4 : ((1 / 2 + 1 / 2 * q (x, s + 1) : ℚ) : ℝ) - (1 / 2 + 1 / 2 * m x) = 1 / 2 *
        ((q (x, s + 1) : ℝ) - m x) := by push_cast; ring
    rw [this4, abs_mul, abs_of_pos (by positivity)]
    calc
      (1 / 2 : ℝ) * |(q (x, s + 1) : ℝ) - m x| ≤ (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ (s + 1) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (2 : ℝ)⁻¹ ^ (s + 2) := by
        have : (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ (s + 1) = (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ (s + 1) := by norm_num
        rw [this]
        exact (pow_succ' (2 : ℝ)⁻¹ (s + 1)).symm
      _ ≤ (2 : ℝ)⁻¹ ^ s := by
        apply pow_le_pow_of_le_one (by positivity) (by norm_num) (by linarith)

private lemma isComputablyRandom_iff_ge_half_not_wins {m : BitString → ℝ} {w : CantorSeq}
    (hnotwin : ¬ Wins (fun x => 1 / 2 + 1 / 2 * m x) w) :
    ¬ Wins m w := by
  intro hwin
  apply hnotwin
  intro ⟨B, hB⟩
  apply hwin
  use 2 * B - 1
  rintro _ ⟨n, rfl⟩
  have := hB ⟨n, rfl⟩
  linarith

/-- **SUV Problem 266(a), p. 279.**  One gets the same notion from martingales separated from zero,
with values at least `1/2`. -/
theorem isComputablyRandom_iff_ge_half {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : IsComputableMeasure π) (_hpos : ∀ x, 0 < cantorMass π x) (w : CantorSeq) :
    IsComputablyRandom π w ↔ ∀ m, IsFairCapital π m → IsComputableOnStrings m →
      (∀ x, 1 / 2 ≤ m x) → ¬ Wins m w := by
  constructor
  · intro h m hm hc _
    exact h m hm hc
  · intro h m hm hc
    have h1 : IsFairCapital π (fun x => 1 / 2 + 1 / 2 * m x) :=
        isComputablyRandom_iff_ge_half_isFairCapital hm
    have h2 : IsComputableOnStrings (fun x => 1 / 2 + 1 / 2 * m x) :=
        isComputablyRandom_iff_ge_half_isComputableOnStrings hc
    have h3 : ∀ x, 1 / 2 ≤ 1 / 2 + 1 / 2 * m x := by
      intro x
      have := hm.nonneg x
      linarith
    have h4 := h _ h1 h2 h3
    exact isComputablyRandom_iff_ge_half_not_wins h4


/-- A rational martingale induces a real computable martingale. -/
lemma isComputablyRandom_iff_rational_aux (m : BitString → ℚ) (hm : Computable m) :
    IsComputableOnStrings (fun x => (m x : ℝ)) := by
  dsimp [IsComputableOnStrings]
  use fun p => m p.1
  constructor
  · exact hm.comp Computable.fst
  · intro x s
    simp [abs_zero, inv_nonneg]

/-- Step 1 of the proof of `isComputablyRandom_iff_rational`:
Forward direction. -/
private lemma isComputablyRandom_iff_rational_fwd
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR π x = r x) (w : CantorSeq)
    (hw : IsComputablyRandom π w) :
    ∀ m : BitString → ℚ, Computable m →
      IsFairCapital π (fun x => (m x : ℝ)) → ¬ Wins (fun x => (m x : ℝ)) w := by
  intro m hm hfair
  apply hw (fun x => (m x : ℝ)) hfair (isComputablyRandom_iff_rational_aux m hm)

/-- Step 1 of the backward proof hint of `isComputablyRandom_iff_rational`: Average with the
constant 1.
For a computable fair capital `m`, `(m+1)/2` is a computable fair capital `≥ 1/2` that wins wherever
`m` wins. -/
private lemma isComputablyRandom_iff_rational_avg
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (m : BitString → ℝ) (hm : IsComputableOnStrings m) (hfair : IsFairCapital π m) :
    IsComputableOnStrings (fun x => (m x + 1) / 2) ∧
    IsFairCapital π (fun x => (m x + 1) / 2) ∧
    (∀ x, 1 / 2 ≤ (m x + 1) / 2) ∧
    (∀ w, Wins m w → Wins (fun x => (m x + 1) / 2) w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq, hqerr⟩ := hm
    refine ⟨fun p => (q p + 1) / 2, ?_, ?_⟩
    · have h1 : Computable (fun p : BitString × ℕ => q p + 1) :=
        Computable₂.comp computable₂_ratAdd hq (Computable.const 1)
      exact computable_ratHalf.comp h1
    · intro x s
      have h := hqerr x s
      have h2 : (2:ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h3 : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ s := by positivity
      have h4 : |((q (x, s) : ℝ) + 1) / 2 - (m x + 1) / 2| = |(q (x, s) : ℝ) - m x| / 2 := by
        rw [show (((q (x, s) : ℝ) + 1) / 2 - (m x + 1) / 2) = ((q (x, s) : ℝ) - m x) / 2 by ring,
          abs_div]
        norm_num
      push_cast
      rw [h4]
      linarith
  · refine ⟨fun x => ?_, fun x => ?_⟩
    · have := hfair.nonneg x
      change 0 ≤ (m x + 1) / 2
      linarith
    · have h := hfair.fair x
      have hadd := massR_add (π := π) x
      change (m x + 1) / 2 * massR π x = (m (x ++ [false]) + 1) / 2 * massR π (x ++ [false]) +
        (m (x ++ [true]) + 1) / 2 * massR π (x ++ [true])
      linear_combination (1 / 2 : ℝ) * h + (1 / 2 : ℝ) * hadd
  · intro x
    have := hfair.nonneg x
    linarith
  · intro w hw hb
    apply hw
    obtain ⟨B, hB⟩ := hb
    refine ⟨2 * B - 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 := hB ⟨n, rfl⟩
    simp only at h1 ⊢
    linarith


/-- Step 1 of the proof of `isComputablyRandom_iff_rational_prop`: Q approximation
-/
private def isComputablyRandom_iff_rational_Q
    (r : BitString → ℚ) (q : BitString × ℕ → ℚ) (x : BitString) : ℚ :=
  let a := q (x ++ [false], x.length + 7)
  let b' := q (x, x.length + 7)
  a * r (x ++ [false]) / (b' * r x)

/-- Step 2 of the proof of `isComputablyRandom_iff_rational_prop`: p witness -/
private def isComputablyRandom_iff_rational_p
    (r : BitString → ℚ) (q : BitString × ℕ → ℚ) (xb : BitString × Bool) : ℚ :=
  let x := xb.1
  let b := xb.2
  let ε : ℚ := (1 / 2) ^ (x.length + 2)
  let Q := isComputablyRandom_iff_rational_Q r q x
  let p0 := (1 - ε) * Q + ε / 2
  if b = false then p0 else 1 - p0

/-- Step 3 of the proof of `isComputablyRandom_iff_rational_prop`: Q is computable
-/
private def rcRatSign (t : ℤ) : ℤ :=
    (min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ)

private lemma rcRatSign_comp : Computable
    rcRatSign := by
  have hs1_nat : Computable (fun t : ℤ => min 1 t.toNat) :=
    Primrec.nat_min.to_comp.comp (Computable.const 1) ComputableReals.primrec_intToNat.to_comp
  have hs1 : Computable (fun t : ℤ => (min 1 t.toNat : ℤ)) :=
    (ComputableReals.primrec_natCastInt.to_comp.comp hs1_nat).of_eq (fun t => by push_cast; rfl)
  have hs2_nat : Computable (fun t : ℤ => min 1 (-t).toNat) :=
    Primrec.nat_min.to_comp.comp (Computable.const 1) ComputableReals.primrec_intNegToNat.to_comp
  have hs2 : Computable (fun t : ℤ => (min 1 (-t).toNat : ℤ)) :=
    (ComputableReals.primrec_natCastInt.to_comp.comp hs2_nat).of_eq (fun t => by push_cast; rfl)
  have hss : Computable (fun t : ℤ => (min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ)) :=
    (Computable₂.comp primrec_intSub.to_comp hs1 hs2)
  exact hss.of_eq (fun t => by rfl)

private lemma rcRatSign_eq (t : ℤ) :
    (rcRatSign t : ℚ) = if t < 0 then -1 else
      if 0 < t then 1 else 0 := by
  unfold rcRatSign
  cases lt_trichotomy t 0 with
  | inl h => 
    have h1 : t.toNat = 0 := Int.toNat_of_nonpos h.le
    have ht1 : (min 1 t.toNat : ℤ) = 0 := by rw [h1]; rfl
    have ht2 : (min 1 (-t).toNat : ℤ) = 1 := by 
      have h2 : 1 ≤ (-t).toNat := by omega
      have h3 : min 1 (-t).toNat = 1 := by omega
      have hh : (min 1 (-t).toNat : ℤ) = (1 : ℤ) := by exact_mod_cast h3
      exact hh
    have heq : ((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℚ) = -1 := by
      rw [ht1, ht2]
      norm_num
    have h_cast : (((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℤ) : ℚ) = ((min 1 t.toNat : ℤ) -
        (min 1 (-t).toNat : ℤ) : ℚ) := by push_cast; rfl
    rw [h_cast, heq]
    have h_if : (if t < 0 then (-1 : ℚ) else if 0 < t then (1 : ℚ) else 0) = -1 := by simp [h]
    rw [h_if]
  | inr h =>
    cases h with
    | inl h => 
      have h1 : t.toNat = 0 := by rw [h]; rfl
      have h2 : (-t).toNat = 0 := by rw [h]; rfl
      have ht1 : (min 1 t.toNat : ℤ) = 0 := by rw [h1]; rfl
      have ht2 : (min 1 (-t).toNat : ℤ) = 0 := by rw [h2]; rfl
      have heq : ((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℚ) = 0 := by
        rw [ht1, ht2]
        norm_num
      have h_cast : (((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℤ) : ℚ) =
          ((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℚ) := by push_cast; rfl
      rw [h_cast, heq]
      have hl1 : ¬(t < 0) := by rw [h]; decide
      have hl2 : ¬(0 < t) := by rw [h]; decide
      have h_if : (if t < 0 then (-1 : ℚ) else if 0 < t then (1 : ℚ) else 0) = 0 := by
        simp [hl1, hl2]
      rw [h_if]
    | inr h =>
      have h1 : (-t).toNat = 0 := Int.toNat_of_nonpos (by omega)
      have ht1 : (min 1 t.toNat : ℤ) = 1 := by 
        have h2 : 1 ≤ t.toNat := by omega
        have h3 : min 1 t.toNat = 1 := by omega
        have hh : (min 1 t.toNat : ℤ) = (1 : ℤ) := by exact_mod_cast h3
        exact hh
      have ht2 : (min 1 (-t).toNat : ℤ) = 0 := by rw [h1]; rfl
      have heq : ((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℚ) = 1 := by
        rw [ht1, ht2]
        norm_num
      have h_cast : (((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℤ) : ℚ) =
          ((min 1 t.toNat : ℤ) - (min 1 (-t).toNat : ℤ) : ℚ) := by push_cast; rfl
      rw [h_cast, heq]
      have hl1 : ¬(t < 0) := by omega
      have h_if : (if t < 0 then (-1 : ℚ) else if 0 < t then (1 : ℚ) else 0) = 1 := by simp [hl1, h]
      rw [h_if]

private lemma rcRatDiv_num_comp :
    Computable (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) * rcRatSign p.2.num) := by
  have h1 : Computable (fun p : ℚ × ℚ => p.1.num) := computable_ratNum.comp Computable.fst
  have h2 : Computable (fun p : ℚ × ℚ => (p.2.den : ℤ)) :=
    (ComputableReals.primrec_natCastInt.to_comp.comp
      (computable_ratDen.comp Computable.snd)).of_eq (fun _ => by rfl)
  have hs : Computable (fun p : ℚ × ℚ => rcRatSign p.2.num) :=
    rcRatSign_comp.comp (computable_ratNum.comp Computable.snd)
  exact Computable₂.comp primrec_intMul.to_comp
    (Computable₂.comp primrec_intMul.to_comp h1 h2) hs

private lemma rcRatDiv_den_comp :
    Computable (fun p : ℚ × ℚ => p.1.den * max 1 p.2.num.natAbs) := by
  have hd1 : Computable (fun p : ℚ × ℚ => p.1.den) := computable_ratDen.comp Computable.fst
  have hm : Computable (fun p : ℚ × ℚ => max 1 p.2.num.natAbs) :=
    Primrec.nat_max.to_comp.comp (Computable.const 1)
      (ComputableReals.primrec_intNatAbs.to_comp.comp (computable_ratNum.comp Computable.snd))
  exact Computable₂.comp Primrec.nat_mul.to_comp hd1 hm

private lemma rcRatDiv : Computable₂
    (fun (p q : ℚ) => p / q) := by
  have hnum := rcRatDiv_num_comp
  have hden := rcRatDiv_den_comp
  refine computable_of_num_den (f := fun p : ℚ × ℚ => p.1 / p.2) hnum hden (fun p => ?_)
      (fun p => ?_)
  · have h1 := p.1.den_pos
    have hm : 0 < max 1 p.2.num.natAbs := by exact Nat.le_max_left 1 p.2.num.natAbs
    exact Nat.mul_pos h1 hm
  · have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
    have ht2 : (p.2.num : ℚ) = p.2 * (p.2.den : ℚ) := (Rat.mul_den_eq_num p.2).symm
    have heq : ((p.1.num * (p.2.den : ℤ) *
        rcRatSign p.2.num : ℤ) : ℚ) /
        ((p.1.den * max 1 p.2.num.natAbs : ℕ) : ℚ) =
      ((p.1.num : ℚ) * (p.2.den : ℚ) *
          (rcRatSign p.2.num : ℚ)) /
          ((p.1.den : ℚ) * ((max 1 p.2.num.natAbs : ℕ) : ℚ)) := by
      push_cast
      rfl
    rw [heq]
    rw [rcRatSign_eq]
    by_cases h2 : p.2 = 0
    · rw [h2]
      simp
    · have hp2 : p.2.num ≠ 0 := by
        intro hp20
        have hp2_0 : p.2 = 0 := by
          have hh1 : p.2.num = (0 : ℚ).num := hp20
          have H_red : p.2.num.natAbs.Coprime p.2.den := p.2.reduced
          rw [hp20] at H_red
          have hh2 : p.2.den = 1 := by 
            have H_coprime : (0 : ℕ).Coprime p.2.den := H_red
            have H_gcd : Nat.gcd 0 p.2.den = 1 := H_coprime
            rw [Nat.gcd_zero_left] at H_gcd
            exact H_gcd
          have H_den0 : (0 : ℚ).den = 1 := rfl
          have hh3 : p.2.den = (0 : ℚ).den := by rw [hh2, H_den0]
          exact Rat.ext hh1 hh3
        exact h2 hp2_0
      cases lt_trichotomy p.2.num 0 with
      | inl hlt =>
        have h_if : (if p.2.num < 0 then (-1 : ℚ) else if 0 < p.2.num then (1 : ℚ) else 0) = -1 :=
            by simp [hlt]
        rw [h_if]
        have hmax_nat : max 1 p.2.num.natAbs = p.2.num.natAbs := by
          have hh1 : 1 ≤ (-p.2.num).toNat := by omega
          omega
        have hmax : ((max 1 p.2.num.natAbs : ℕ) : ℚ) = ((p.2.num.natAbs : ℕ) : ℚ) := by
          rw [hmax_nat]
        rw [hmax]
        have hnatabs : ((p.2.num.natAbs : ℕ) : ℚ) = -(p.2.num : ℚ) := by
          have hcast : (p.2.num.natAbs : ℤ) = -p.2.num := Int.ofNat_natAbs_of_nonpos hlt.le
          have H : ((p.2.num.natAbs : ℕ) : ℤ) = -p.2.num := hcast
          have H2 : (((p.2.num.natAbs : ℕ) : ℤ) : ℚ) = (-p.2.num : ℚ) := by exact_mod_cast H
          have h_eq_2 : (((p.2.num.natAbs : ℕ) : ℤ) : ℚ) = ((p.2.num.natAbs : ℕ) : ℚ) := by rfl
          rw [h_eq_2] at H2
          exact H2
        have hh : ((p.2.num.natAbs : ℕ) : ℚ) = -(p.2.num : ℚ) := hnatabs
        rw [hh, h1, ht2]
        have hpd1 : (p.1.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
        have hpd2 : (p.2.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
        have hp20_q : (p.2 : ℚ) ≠ 0 := by exact_mod_cast h2
        have h_neg1 : (p.1 * (p.1.den : ℚ)) * (p.2.den : ℚ) * -1 = -((p.1 * (p.1.den : ℚ)) *
            (p.2.den : ℚ)) := by ring
        rw [h_neg1]
        field_simp
      | inr h =>
        cases h with
        | inl heq =>
          exfalso
          exact hp2 heq
        | inr hgt =>
          have hlnot : ¬(p.2.num < 0) := by omega
          have h_if : (if p.2.num < 0 then (-1 : ℚ) else if 0 < p.2.num then (1 : ℚ) else 0) = 1 :=
              by simp [hlnot, hgt]
          rw [h_if]
          have hmax_nat : max 1 p.2.num.natAbs = p.2.num.natAbs := by
            have hh1 : 1 ≤ p.2.num.toNat := by omega
            omega
          have hmax : ((max 1 p.2.num.natAbs : ℕ) : ℚ) = ((p.2.num.natAbs : ℕ) : ℚ) := by
            rw [hmax_nat]
          rw [hmax]
          have hnatabs : ((p.2.num.natAbs : ℕ) : ℚ) = (p.2.num : ℚ) := by
            have hcast : (p.2.num.natAbs : ℤ) = p.2.num := Int.ofNat_natAbs_of_nonneg hgt.le
            have H : ((p.2.num.natAbs : ℕ) : ℤ) = p.2.num := hcast
            have H2 : (((p.2.num.natAbs : ℕ) : ℤ) : ℚ) = (p.2.num : ℚ) := by exact_mod_cast H
            have h_eq_2 : (((p.2.num.natAbs : ℕ) : ℤ) : ℚ) = ((p.2.num.natAbs : ℕ) : ℚ) := by rfl
            rw [h_eq_2] at H2
            exact H2
          have hh : ((p.2.num.natAbs : ℕ) : ℚ) = (p.2.num : ℚ) := hnatabs
          rw [hh, h1, ht2]
          have hpd1 : (p.1.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
          have hpd2 : (p.2.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
          have hp20_q : (p.2 : ℚ) ≠ 0 := by exact_mod_cast h2
          have h_pos1 : (p.1 * (p.1.den : ℚ)) * (p.2.den : ℚ) * 1 = (p.1 * (p.1.den : ℚ)) *
              (p.2.den : ℚ) := by ring
          rw [h_pos1]
          field_simp

private lemma isComputablyRandom_iff_rational_Q_comp
    (r : BitString → ℚ) (q : BitString × ℕ → ℚ) (hr : Computable r) (hq : Computable q) :
    Computable (fun x => isComputablyRandom_iff_rational_Q r q x) := by
  have hl7 : Computable (fun (x : BitString) => x.length + 7) :=
    Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp Computable.list_length
        (Computable.const 7)
  have hc_false : Computable (fun (x : BitString) => [false]) := Computable.const [false]
  have h_append : Computable (fun (x : BitString) => x ++ [false]) :=
    Computable₂.comp (f := fun (x y : List Bool) => x ++ y) Computable.list_append Computable.id
        hc_false
  have ha_arg : Computable (fun (x : BitString) => (x ++ [false], x.length + 7)) :=
    Computable.pair h_append hl7
  have hb_arg : Computable (fun (x : BitString) => (x, x.length + 7)) :=
    Computable.pair Computable.id hl7
  have ha : Computable (fun (x : BitString) => q (x ++ [false], x.length + 7)) := hq.comp ha_arg
  have hb : Computable (fun (x : BitString) => q (x, x.length + 7)) := hq.comp hb_arg
  have hrx0 : Computable (fun (x : BitString) => r (x ++ [false])) := hr.comp h_append
  have hrx : Computable (fun (x : BitString) => r x) := hr
  have hnum : Computable (fun (x : BitString) => q (x ++ [false], x.length + 7) * r (x ++ [false]))
      :=
    Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul ha hrx0
  have hden : Computable (fun (x : BitString) => q (x, x.length + 7) * r x) :=
    Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul hb hrx
  exact Computable₂.comp (f := fun a b : ℚ => a / b)
      rcRatDiv hnum hden


/-- Step 4 of the proof of `isComputablyRandom_iff_rational_prop`: p is computable
-/
private lemma isComputablyRandom_iff_rational_p_comp
    (r : BitString → ℚ) (q : BitString × ℕ → ℚ) (hr : Computable r) (hq : Computable q) :
    Computable (isComputablyRandom_iff_rational_p r q) := by
  have hl : Computable (fun xb : BitString × Bool => xb.1.length) :=
    Computable.list_length.comp Computable.fst
  have hε : Computable (fun xb : BitString × Bool => (1 / 2 : ℚ) ^ (xb.1.length + 2)) := by
    have hpow : Computable (fun n : ℕ => (1 / 2 : ℚ) ^ n) := by
      have h_num : Computable (fun n : ℕ => (1 : ℤ)) := Computable.const 1
      have h_den : Computable (fun n : ℕ => 2 ^ n) := comp_pow
      apply computable_of_num_den h_num h_den
      · intro a; positivity
      · intro a; dsimp; rw [one_div_pow]; push_cast; rfl
    have hadd : Computable (fun xb : BitString × Bool => xb.1.length + 2) :=
      Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp hl (Computable.const 2)
    exact hpow.comp hadd
  have hQ : Computable (fun xb : BitString × Bool =>
    isComputablyRandom_iff_rational_Q r q xb.1) :=
    (isComputablyRandom_iff_rational_Q_comp r q hr hq).comp Computable.fst
  have hp0 : Computable (fun xb : BitString × Bool => (1 - (1 / 2 : ℚ) ^ (xb.1.length + 2)) *
                                                        isComputablyRandom_iff_rational_Q r q xb.1 +
                                                        (1 / 2 : ℚ) ^ (xb.1.length + 2) / 2) := by
    have h1 : Computable (fun xb : BitString × Bool => 1 - (1 / 2 : ℚ) ^ (xb.1.length + 2)) :=
      computable₂_ratSub.comp (Computable.const 1) hε
    have h2 : Computable (fun xb : BitString × Bool => (1 - (1 / 2 : ℚ) ^ (xb.1.length + 2)) *
                                                         isComputablyRandom_iff_rational_Q r q
                                                         xb.1) :=
      computable₂_ratMul.comp h1 hQ
    have h3 : Computable (fun xb : BitString × Bool => (1 / 2 : ℚ) ^ (xb.1.length + 2) / 2) :=
      computable_ratHalf.comp hε
    exact computable₂_ratAdd.comp h2 h3
  exact (Computable.cond Computable.snd (computable₂_ratSub.comp (Computable.const 1) hp0)
      hp0).of_eq (fun xb => by
    dsimp [isComputablyRandom_iff_rational_p]
    cases xb.2 <;> simp)

/-- A quotient estimate when the denominator capital is at least `1/2` and the weighted
numerator capital does not exceed the weighted denominator capital. -/
private lemma isComputablyRandom_iff_rational_Q_bound_ratio_err
    (A B a b ρ0 ρ δ : ℝ) (hB : 1 / 2 ≤ B) (hA : 0 ≤ A) (hρ0 : 0 < ρ0)
    (hρ : ρ0 ≤ ρ) (hAB : A * ρ0 ≤ B * ρ) (hδ : δ ≤ 1 / 4)
    (ha : |a - A| ≤ δ) (hb : |b - B| ≤ δ) :
    |a * ρ0 / (b * ρ) - A * ρ0 / (B * ρ)| ≤ 8 * δ := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) ha
  have hb4 : 1 / 4 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have hBpos : 0 < B := by linarith
  have hρpos : 0 < ρ := lt_of_lt_of_le hρ0 hρ
  have hden : 0 < ρ * b * B := by positivity
  have hrw : a * ρ0 / (b * ρ) - A * ρ0 / (B * ρ) =
      ρ0 * (a * B - A * b) / (ρ * b * B) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul, abs_of_pos hρ0]
  have hnum : |a * B - A * b| ≤ δ * (B + A) := by
    rw [abs_le]
    constructor <;> nlinarith
  have hkey : ρ * B ≤ 4 * (ρ * b * B) := by
    nlinarith [mul_nonneg (mul_pos hρpos hBpos).le
      (show 0 ≤ 4 * b - 1 by linarith)]
  have h1 : ρ0 * B ≤ 4 * (ρ * b * B) := by
    have : ρ0 * B ≤ ρ * B := by gcongr
    linarith
  have h2 : A * ρ0 ≤ 4 * (ρ * b * B) := by
    have : B * ρ = ρ * B := by ring
    linarith
  calc
    ρ0 * |a * B - A * b| ≤ ρ0 * (δ * (B + A)) := by gcongr
    _ = δ * (ρ0 * B) + δ * (A * ρ0) := by ring
    _ ≤ δ * (4 * (ρ * b * B)) + δ * (4 * (ρ * b * B)) := by gcongr
    _ = 8 * δ * (ρ * b * B) := by ring

/-- Step 5 of the proof of `isComputablyRandom_iff_rational_prop`: Q approximation
bound -/
private lemma isComputablyRandom_iff_rational_Q_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (q : BitString × ℕ → ℚ) (hq : ∀ x s, |(q (x, s) : ℝ) - m x| ≤ (2 : ℝ)⁻¹ ^ s)
    (hfair : IsFairCapital π m) (hhalf : ∀ x, 1 / 2 ≤ m x) (x : BitString) :
    let Q := isComputablyRandom_iff_rational_Q r q x
    let q0 := m (x ++ [false]) * massR π (x ++ [false]) / (m x * massR π x)
    |(Q : ℝ) - q0| ≤ ((1/2 : ℝ) ^ (x.length + 2)) / 4 := by
  have hmr : ∀ y, massR π y = (r y : ℝ) := fun y => (hr y).2
  have hrpos : ∀ y, (0 : ℝ) < (r y : ℝ) := fun y => by exact_mod_cast (hr y).1
  have hadd := massR_add (π := π) x
  have hfx := hfair.fair x
  rw [hmr, hmr, hmr] at hadd hfx
  have hρ : (r (x ++ [false]) : ℝ) ≤ (r x : ℝ) := by
    linarith [hrpos (x ++ [true])]
  have hAB : m (x ++ [false]) * (r (x ++ [false]) : ℝ) ≤ m x * (r x : ℝ) := by
    linarith [mul_nonneg (hfair.nonneg (x ++ [true])) (hrpos (x ++ [true])).le]
  have hδ : (2 : ℝ)⁻¹ ^ (x.length + 7) ≤ 1 / 4 := by
    have hle : (2 : ℝ)⁻¹ ^ (x.length + 7) ≤ (2 : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact hle.trans (by norm_num)
  have herr := isComputablyRandom_iff_rational_Q_bound_ratio_err
    (m (x ++ [false])) (m x) (q (x ++ [false], x.length + 7) : ℝ)
    (q (x, x.length + 7) : ℝ) (r (x ++ [false]) : ℝ) (r x : ℝ)
    ((2 : ℝ)⁻¹ ^ (x.length + 7)) (hhalf x) (hfair.nonneg (x ++ [false]))
    (hrpos (x ++ [false])) hρ hAB hδ
    (hq (x ++ [false]) (x.length + 7)) (hq x (x.length + 7))
  have hεeq : ((1 / 2 : ℝ) ^ (x.length + 2)) / 4 =
      8 * (2 : ℝ)⁻¹ ^ (x.length + 7) := by
    rw [show x.length + 7 = (x.length + 2) + 5 by omega, pow_add]
    norm_num
    ring
  dsimp only
  rw [hεeq, hmr, hmr]
  simpa only [isComputablyRandom_iff_rational_Q,
    Rat.cast_div, Rat.cast_mul] using herr

private lemma isComputablyRandom_iff_rational_p_bound_ic_pointwise (q0 Q ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hQ : |Q - q0| ≤ ε / 4) :
    (1 - ε) * q0 ≤ (1 - ε) * Q + ε / 2 ∧
      (1 - ε) * (1 - q0) ≤ 1 - ((1 - ε) * Q + ε / 2) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hQ
  have h3 : 0 ≤ 1 - ε := by linarith
  constructor <;> nlinarith [mul_nonneg h3 (show 0 ≤ Q - q0 + ε / 4 by linarith),
    mul_nonneg h3 (show 0 ≤ ε / 4 - (Q - q0) by linarith)]

/-- Step 6 of the proof of `isComputablyRandom_iff_rational_prop`: bounds on p -/
private lemma isComputablyRandom_iff_rational_p_bound
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (q : BitString × ℕ → ℚ) (hq : ∀ x s, |(q (x, s) : ℝ) - m x| ≤ (2 : ℝ)⁻¹ ^ s)
    (hfair : IsFairCapital π m) (hhalf : ∀ x, 1 / 2 ≤ m x) (x : BitString) (b : Bool) :
    let p := isComputablyRandom_iff_rational_p r q
    p (x, false) + p (x, true) = 1 ∧
    (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (m (x ++ [b]) * massR π (x ++ [b]) / (m x * massR π x)) ≤
        (p (x, b) : ℝ) := by
  let p := isComputablyRandom_iff_rational_p r q
  let ε : ℚ := (1 / 2) ^ (x.length + 2)
  let Q := isComputablyRandom_iff_rational_Q r q x
  let p0 := (1 - ε) * Q + ε / 2
  have hp0 : p (x, false) = p0 := rfl
  have hp1 : p (x, true) = 1 - p0 := rfl
  have hsum : p (x, false) + p (x, true) = 1 := by
    rw [hp0, hp1]
    ring
  refine ⟨hsum, ?_⟩
  let q0 := m (x ++ [false]) * massR π (x ++ [false]) / (m x * massR π x)
  let q1 := m (x ++ [true]) * massR π (x ++ [true]) / (m x * massR π x)
  have hQerr := isComputablyRandom_iff_rational_Q_bound r hr m q hq hfair hhalf x
  have hε0 : (0 : ℝ) < (ε : ℝ) := by
    have : (ε : ℝ) = (1 / 2 : ℝ) ^ (x.length + 2) := by dsimp [ε]; push_cast; rfl
    rw [this]
    positivity
  have hε1 : (ε : ℝ) ≤ 1 / 4 := by
    have h2 : (ε : ℝ) = (1 / 2 : ℝ) ^ (x.length + 2) := by dsimp [ε]; push_cast; rfl
    rw [h2]
    have h1 : (1 / 2 : ℝ) ^ (x.length + 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact h1.trans (by norm_num)
  have hQerr_real : |(Q : ℝ) - q0| ≤ (ε : ℝ) / 4 := by
    have h2 : (ε : ℝ) = (1 / 2 : ℝ) ^ (x.length + 2) := by dsimp [ε]; push_cast; rfl
    rw [h2]
    exact hQerr
  obtain ⟨hpt1, hpt2⟩ := isComputablyRandom_iff_rational_p_bound_ic_pointwise q0
      (Q : ℝ) (ε : ℝ) hε0 hε1 hQerr_real
  have hp0_real : (p0 : ℝ) = (1 - (ε : ℝ)) * (Q : ℝ) + (ε : ℝ) / 2 := by
    dsimp [p0]
    push_cast
    ring
  cases b
  · have hfalse_real : (p (x, false) : ℝ) = (1 - (ε : ℝ)) * (Q : ℝ) + (ε : ℝ) / 2 := by
      calc
        (p (x, false) : ℝ) = (p0 : ℝ) := congrArg (fun z : ℚ => (z : ℝ)) hp0
        _ = (1 - (ε : ℝ)) * (Q : ℝ) + (ε : ℝ) / 2 := by rw [hp0_real]
    rw [hfalse_real]
    have : (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * q0 ≤ (1 - ↑ε) * ↑Q + ↑ε / 2 := by
      have hε : (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) = (1 - (ε : ℝ)) := by
        have : (ε : ℝ) = (1 / 2 : ℝ) ^ (x.length + 2) := by dsimp [ε]; push_cast; rfl
        have h1 : ((1 / 2 : ℝ) ^ (x.length + 2)) = (2 : ℝ)⁻¹ ^ (x.length + 2) := by ring
        rw [this, h1]
      rw [hε]
      exact hpt1
    exact this
  · have htrue_real : (p (x, true) : ℝ) = 1 - ((1 - (ε : ℝ)) * (Q : ℝ) + (ε : ℝ) / 2) := by
      calc
        (p (x, true) : ℝ) = ((1 - p0 : ℚ) : ℝ) := congrArg (fun z : ℚ => (z : ℝ)) hp1
        _ = 1 - (p0 : ℝ) := by norm_num
        _ = 1 - ((1 - (ε : ℝ)) * (Q : ℝ) + (ε : ℝ) / 2) := by rw [hp0_real]
    rw [htrue_real]
    have hq1 : q1 = 1 - q0 := by
      dsimp [q0, q1]
      have hmpos : 0 < m x := by linarith [hhalf x]
      have hmasspos : (0 : ℝ) < massR π x := by
        have := (hr x).1
        have h2 := (hr x).2
        rw [h2]
        exact_mod_cast this
      have hdenom : m x * massR π x ≠ 0 := mul_ne_zero (ne_of_gt hmpos) (ne_of_gt hmasspos)
      have : m (x ++ [false]) * massR π (x ++ [false]) + m (x ++ [true]) * massR π (x ++ [true]) =
          m x * massR π x := by
        exact (hfair.fair x).symm
      have h3 : m (x ++ [false]) * massR π (x ++ [false]) / (m x * massR π x) + m (x ++ [true]) *
          massR π (x ++ [true]) / (m x * massR π x) = 1 := by
        rw [← add_div, this, div_self hdenom]
      linarith
    have : (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * q1 ≤ 1 - ((1 - ↑ε) * ↑Q + ↑ε / 2) := by
      rw [hq1]
      have hε : (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) = (1 - (ε : ℝ)) := by
        have h2 : (ε : ℝ) = (1 / 2 : ℝ) ^ (x.length + 2) := by dsimp [ε]; push_cast; rfl
        rw [h2]
        have h3 : (1 / 2 : ℝ) ^ (x.length + 2) = (2 : ℝ)⁻¹ ^ (x.length + 2) := by ring
        rw [h3]
      rw [hε]
      exact hpt2
    exact this


/-- Step 2a of the backward proof hint of `isComputablyRandom_iff_rational`: Computable rational
proportion rule with relative accuracy. -/
private lemma isComputablyRandom_iff_rational_prop
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (hm : IsComputableOnStrings m) (hfair : IsFairCapital π m) (hhalf : ∀ x, 1 /
        2 ≤ m x) :
    ∃ p : BitString × Bool → ℚ, Computable p ∧ ∀ x, p (x, false) + p (x, true) = 1 ∧
      ∀ b, (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (m (x ++ [b]) * massR π (x ++ [b]) /
          (m x * massR π x)) ≤ (p (x, b) : ℝ) := by
  obtain ⟨q, hq_comp, hq_bound⟩ := hm
  obtain ⟨r, hrc, hrpos⟩ := hπ
  let p := isComputablyRandom_iff_rational_p r q
  use p
  refine ⟨isComputablyRandom_iff_rational_p_comp r q hrc hq_comp, fun x => ?_⟩
  have hbound := isComputablyRandom_iff_rational_p_bound r hrpos m q hq_bound hfair
      hhalf x
  exact ⟨(hbound false).1, fun b => (hbound b).2⟩

/-- Step 2b of the backward proof hint of `isComputablyRandom_iff_rational`: Computability of the
recursively defined M. -/
private lemma isComputablyRandom_iff_rational_M
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : Computable r)
    (p : BitString × Bool → ℚ) (hp : Computable p) :
    ∃ M : BitString → ℚ, Computable M ∧ M [] = 1 ∧
      ∀ x b, M (x ++ [b]) = p (x, b) * M x * r x / r (x ++ [b]) := by
  let F : BitString → ℕ × ℚ → ℚ := fun x iv =>
    p (x.take iv.1, x.getD iv.1 false) * iv.2 * r (x.take iv.1) / r (x.take (iv.1 + 1))
  let Mseq : BitString → ℕ → ℚ := fun x n =>
    Nat.rec (motive := fun _ => ℚ) 1 (fun i v => F x (i, v)) n
  have hMsucc : ∀ x n, Mseq x (n + 1) = F x (n, Mseq x n) := fun _ _ => rfl
  have hF : Computable₂ F := by
    have hx : Computable (fun z : BitString × (ℕ × ℚ) => z.1) := Computable.fst
    have hi : Computable (fun z : BitString × (ℕ × ℚ) => z.2.1) :=
        Computable.fst.comp Computable.snd
    have hv : Computable (fun z : BitString × (ℕ × ℚ) => z.2.2) :=
        Computable.snd.comp Computable.snd
    have ht1 : Computable (fun z : BitString × (ℕ × ℚ) => z.1.take z.2.1) :=
      Computable₂.comp Primrec.list_take.to_comp hi hx
    have ht2 : Computable (fun z : BitString × (ℕ × ℚ) => z.1.getD z.2.1 false) :=
      Computable₂.comp (f := fun (l : BitString) (n : ℕ) => l.getD n false)
        (Primrec.list_getD false).to_comp hx hi
    have ht3 : Computable (fun z : BitString × (ℕ × ℚ) => z.1.take (z.2.1 + 1)) :=
      Computable₂.comp Primrec.list_take.to_comp (Primrec.succ.to_comp.comp hi) hx
    have hp1 : Computable (fun z : BitString × (ℕ × ℚ) => p (z.1.take z.2.1, z.1.getD z.2.1 false))
        :=
      hp.comp (ht1.pair ht2)
    have hr1 : Computable (fun z : BitString × (ℕ × ℚ) => r (z.1.take z.2.1)) := hr.comp ht1
    have hr3 : Computable (fun z : BitString × (ℕ × ℚ) => r (z.1.take (z.2.1 + 1))) := hr.comp ht3
    have hnum : Computable (fun z : BitString × (ℕ × ℚ) =>
        p (z.1.take z.2.1, z.1.getD z.2.1 false) * z.2.2 * r (z.1.take z.2.1)) :=
      Computable₂.comp computable₂_ratMul (Computable₂.comp computable₂_ratMul hp1 hv) hr1
    have hquot := Computable₂.comp (f := fun a b : ℚ => a / b)
      rcRatDiv hnum hr3
    exact hquot.of_eq (fun _ => rfl)
  refine ⟨fun x => Mseq x x.length, ?_, rfl, ?_⟩
  · exact Computable.nat_rec (f := fun x : BitString => x.length) (g := fun _ => (1 : ℚ))
      (h := fun x iv => F x iv) Computable.list_length (Computable.const 1) hF
  · intro x b
    have hagree : ∀ n, n ≤ x.length → Mseq (x ++ [b]) n = Mseq x n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [hMsucc, hMsucc, ih (by omega)]
        simp only [F]
        have e1 : (x ++ [b]).take n = x.take n := List.take_append_of_le_length (by omega)
        have e2 : (x ++ [b]).take (n + 1) = x.take (n + 1) :=
          List.take_append_of_le_length (by omega)
        have e3 : (x ++ [b]).getD n false = x.getD n false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show n < x.length by omega)]
        rw [e1, e2, e3]
    have hlen : (x ++ [b]).length = x.length + 1 := by simp
    change Mseq (x ++ [b]) (x ++ [b]).length = p (x, b) * Mseq x x.length * r x / r (x ++ [b])
    rw [hlen, hMsucc, hagree x.length le_rfl]
    simp only [F]
    have e1 : (x ++ [b]).take x.length = x := List.take_left
    have e2 : (x ++ [b]).take (x.length + 1) = x ++ [b] := by
      rw [List.take_of_length_le (by simp)]
    have e3 : (x ++ [b]).getD x.length false = b := by
      simp [List.getD_eq_getElem?_getD]
    rw [e1, e2, e3]

/-- Step 1 of the proof of `isComputablyRandom_iff_rational_ind`: domination by the
product bound `∏_{i<n} (1 - 2^{-(i+2)}) ≥ 1/2 + 2^{-(n+1)}`, proved by induction on `x`
(strings grow on the right). -/
private lemma isComputablyRandom_iff_rational_ind_dom
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (hhalf : ∀ x, 1 / 2 ≤ m x)
    (p : BitString × Bool → ℚ)
    (hpb : ∀ x b, (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (m (x ++ [b]) * massR π (x ++ [b]) /
        (m x * massR π x)) ≤ (p (x, b) : ℝ))
    (M : BitString → ℚ) (hM0 : M [] = 1) (hMrec : ∀ x b, M (x ++ [b]) = p (x, b) * M x * r x /
        r (x ++ [b])) :
    ∀ x, (1 / 2 + (2 : ℝ)⁻¹ ^ (x.length + 1)) * (m x / m []) ≤ (M x : ℝ) := by
  intro x
  have hm0 : 0 < m [] := by have := hhalf []; linarith
  induction x using List.reverseRecOn with
  | nil =>
    rw [List.length_nil, div_self hm0.ne', hM0]
    norm_num
  | append_singleton x b ih =>
    have hr_x := hr x
    have hr_xb := hr (x ++ [b])
    have hm_x : 0 < m x := by have := hhalf x; linarith
    have hm_xb : 0 < m (x ++ [b]) := by have := hhalf (x ++ [b]); linarith
    have hrx : (0 : ℝ) < (r x : ℝ) := by exact_mod_cast hr_x.1
    have hrxb : (0 : ℝ) < (r (x ++ [b]) : ℝ) := by exact_mod_cast hr_xb.1
    have hpb' := hpb x b
    rw [hr_x.2, hr_xb.2] at hpb'
    have hMrec' : (M (x ++ [b]) : ℝ) = (p (x, b) : ℝ) * (M x : ℝ) * (r x : ℝ) / (r (x ++ [b]) : ℝ)
        := by
      rw [hMrec x b]; push_cast; rfl
    have hu0 : 0 < (2 : ℝ)⁻¹ ^ (x.length + 1) := by positivity
    have hu1 : (2 : ℝ)⁻¹ ^ (x.length + 1) ≤ 1 / 2 := by
      calc (2 : ℝ)⁻¹ ^ (x.length + 1) ≤ (2 : ℝ)⁻¹ ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    have hε : (2 : ℝ)⁻¹ ^ (x.length + 2) = (2 : ℝ)⁻¹ ^ (x.length + 1) / 2 := by
      rw [pow_succ]; ring
    have hε' : (2 : ℝ)⁻¹ ^ ((x ++ [b]).length + 1) = (2 : ℝ)⁻¹ ^ (x.length + 1) / 2 := by
      rw [← hε]; simp
    rw [hε] at hpb'
    rw [hε', hMrec']
    generalize (2 : ℝ)⁻¹ ^ (x.length + 1) = u at *
    generalize m x = a at *
    generalize m (x ++ [b]) = a' at *
    generalize m [] = m0 at *
    generalize (r x : ℝ) = ρ at *
    generalize (r (x ++ [b]) : ℝ) = ρ' at *
    generalize (p (x, b) : ℝ) = P at *
    generalize (M x : ℝ) = Mx at *
    have hMx : 0 < Mx := lt_of_lt_of_le (by positivity) ih
    have e : (1 - u / 2) * (a' * ρ' / (a * ρ)) * Mx * ρ / ρ' = (1 - u / 2) * a' * Mx / a := by
      field_simp
    have h1 : (1 / 2 + u / 2) ≤ (1 - u / 2) * (1 / 2 + u) := by nlinarith
    have h2 : 0 ≤ (1 - u / 2) * a' := by
      have : 0 ≤ 1 - u / 2 := by linarith
      positivity
    calc (1 / 2 + u / 2) * (a' / m0)
        ≤ (1 - u / 2) * (a' * ρ' / (a * ρ)) * Mx * ρ / ρ' := by
          rw [e, le_div_iff₀ hm_x]
          calc (1 / 2 + u / 2) * (a' / m0) * a = (1 / 2 + u / 2) * (a' * a / m0) := by ring
            _ ≤ (1 - u / 2) * (1 / 2 + u) * (a' * a / m0) := by
              apply mul_le_mul_of_nonneg_right h1; positivity
            _ = (1 - u / 2) * a' * ((1 / 2 + u) * (a / m0)) := by ring
            _ ≤ (1 - u / 2) * a' * Mx := mul_le_mul_of_nonneg_left ih h2
      _ ≤ P * Mx * ρ / ρ' := by
          apply div_le_div_of_nonneg_right _ hrxb.le
          apply mul_le_mul_of_nonneg_right _ hrx.le
          exact mul_le_mul_of_nonneg_right hpb' hMx.le

/-- Step 2c of the backward proof hint of `isComputablyRandom_iff_rational`: Induction giving
fairness and M x ≥ c * m x. -/
private lemma isComputablyRandom_iff_rational_ind
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (r : BitString → ℚ) (hr : ∀ x, 0 < r x ∧ massR π x = r x)
    (m : BitString → ℝ) (hhalf : ∀ x, 1 / 2 ≤ m x)
    (p : BitString × Bool → ℚ) (hps : ∀ x, p (x, false) + p (x, true) = 1)
    (hpb : ∀ x b, (1 - (2 : ℝ)⁻¹ ^ (x.length + 2)) * (m (x ++ [b]) * massR π (x ++ [b]) /
        (m x * massR π x)) ≤ (p (x, b) : ℝ))
    (M : BitString → ℚ) (hM0 : M [] = 1) (hMrec : ∀ x b, M (x ++ [b]) = p (x, b) * M x * r x /
        r (x ++ [b])) :
    IsFairCapital π (fun x => (M x : ℝ)) ∧ ∃ c : ℝ, 0 < c ∧ ∀ x, c * m x ≤ (M x : ℝ) := by
  have hdom := isComputablyRandom_iff_rational_ind_dom r hr m hhalf p hpb M hM0 hMrec
  have hm0 : 0 < m [] := by have := hhalf []; linarith
  have hmx : ∀ x, 0 ≤ m x := fun x => by have := hhalf x; linarith
  refine ⟨⟨fun x => ?_, fun x => ?_⟩, 1 / (2 * m []), by positivity, fun x => ?_⟩
  · -- non-negativity of `M` comes from the domination bound
    have h := hdom x
    have : 0 ≤ (1 / 2 + (2 : ℝ)⁻¹ ^ (x.length + 1)) * (m x / m []) := by
      have := hmx x
      positivity
    exact this.trans h
  · -- fairness: `M (x ++ [b]) * r (x ++ [b]) = p (x, b) * M x * r x`
    have e : ∀ b, (M (x ++ [b]) : ℝ) * (r (x ++ [b]) : ℝ) = (p (x, b) : ℝ) * (M x : ℝ) *
        (r x : ℝ) := by
      intro b
      have hne : (r (x ++ [b]) : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (r (x ++ [b]) : ℝ) := by exact_mod_cast (hr (x ++ [b])).1
        exact this.ne'
      rw [hMrec x b]
      push_cast
      field_simp
    have hps' : (p (x, false) : ℝ) + (p (x, true) : ℝ) = 1 := by exact_mod_cast hps x
    rw [(hr x).2, (hr (x ++ [false])).2, (hr (x ++ [true])).2, e false, e true]
    linear_combination (-(M x : ℝ) * (r x : ℝ)) * hps'
  · -- domination with `c = 1 / (2 * m [])`
    have h := hdom x
    have hu : 0 ≤ (2 : ℝ)⁻¹ ^ (x.length + 1) := by positivity
    calc 1 / (2 * m []) * m x = 1 / 2 * (m x / m []) := by field_simp
      _ ≤ (1 / 2 + (2 : ℝ)⁻¹ ^ (x.length + 1)) * (m x / m []) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (hmx x) hm0.le)
      _ ≤ (M x : ℝ) := h

/-- Step 2 of the proof of `isComputablyRandom_iff_rational`: Putting it all together for
the reverse direction. -/
private lemma isComputablyRandom_iff_rational_bwd
    {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR π x = r x) (w : CantorSeq)
    (hrat : ∀ m : BitString → ℚ, Computable m →
      IsFairCapital π (fun x => (m x : ℝ)) → ¬ Wins (fun x => (m x : ℝ)) w) :
    IsComputablyRandom π w := by
  intro m hfair hm
  obtain ⟨r, hrc, hrpos⟩ := hπ
  have havg := isComputablyRandom_iff_rational_avg (π := π) m hm hfair
  obtain ⟨hm'_comp, hm'_fair, hm'_half, hm'_wins⟩ := havg
  have hprop := isComputablyRandom_iff_rational_prop (π := π) ⟨r, hrc, hrpos⟩
      (fun x => (m x + 1) / 2) hm'_comp hm'_fair hm'_half
  obtain ⟨p, hp_comp, hp_rest⟩ := hprop
  have hM := isComputablyRandom_iff_rational_M (π := π) r hrc p hp_comp
  obtain ⟨M, hM_comp, hM0, hMrec⟩ := hM
  have hind := isComputablyRandom_iff_rational_ind (π := π) r hrpos (fun x => (m x + 1) / 2)
      hm'_half p (fun x => (hp_rest x).1) (fun x b => (hp_rest x).2 b) M hM0 hMrec
  obtain ⟨hM_fair, c, hcpos, hc_le⟩ := hind
  intro hwins
  have hm'_wins_w := hm'_wins w hwins
  have hM_wins : Wins (fun x => (M x : ℝ)) w := by
    -- if m' wins, and c * m' <= M, then M wins
    intro hB
    apply hm'_wins_w
    rcases hB with ⟨B, hB⟩
    use B / c
    rintro _ ⟨n, rfl⟩
    have h1 := hc_le (cantorPrefix w n)
    have h2 := hB ⟨n, rfl⟩
    dsimp at h2
    rw [mul_comm] at h1
    exact (le_div_iff₀ hcpos).mpr (h1.trans h2)
  exact hrat M hM_comp hM_fair hM_wins

/-- **SUV Problem 266(b), p. 279.**  If the masses are positive rationals, exactly computable from
`x`, one gets the same notion from exactly computable rational-valued martingales. -/
theorem isComputablyRandom_iff_rational {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : ∃ r : BitString → ℚ, Computable r ∧ ∀ x, 0 < r x ∧ massR π x = r x) (w : CantorSeq) :
    IsComputablyRandom π w ↔ ∀ m : BitString → ℚ, Computable m →
      IsFairCapital π (fun x => (m x : ℝ)) → ¬ Wins (fun x => (m x : ℝ)) w := by
  constructor
  · exact isComputablyRandom_iff_rational_fwd hπ w
  · exact isComputablyRandom_iff_rational_bwd hπ w


/-- Step 1 of the proof of `isComputablyRandom_of_isMartinLofRandom`: a computable real
function on strings is lower semicomputable. -/
private theorem isComputablyRandom_of_isMartinLofRandom_lsc {m : BitString → ℝ}
    (hm : IsComputableOnStrings m) : IsLowerSemicomputableOnStrings m := by
  obtain ⟨q, hq, hbound⟩ := hm
  have hhalf : Computable (fun s : ℕ => (1 / 2 : ℚ) ^ s) := by
    refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun a : ℕ => 2 ^ a)
      (Computable.const 1)
      ((nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id).to_comp)
      (fun a => by positivity) (fun a => ?_)
    push_cast
    rw [div_pow, one_pow]
  let check : (ℚ × BitString) × ℕ → Bool := fun p =>
    decide (p.1.1 + (1 / 2 : ℚ) ^ p.2 < q (p.1.2, p.2))
  have hcheck : Computable check := by
    have h1 : Computable (fun p : (ℚ × BitString) × ℕ => p.1.1 + (1 / 2 : ℚ) ^ p.2) :=
      computable₂_ratAdd.comp (Computable.fst.comp Computable.fst)
        (hhalf.comp Computable.snd)
    have h2 : Computable (fun p : (ℚ × BitString) × ℕ => q (p.1.2, p.2)) :=
      hq.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)
    exact computable₂_ratLt.comp h1 h2
  have hRE : IsRE (fun p : (ℚ × BitString) × ℕ =>
      p.1.1 + (1 / 2 : ℚ) ^ p.2 < q (p.1.2, p.2)) :=
    isRE_of_computable_bool _ check (fun p => by simp [check]) hcheck
  refine (IsRE.exists_encodable
    (R := fun (a : ℚ × BitString) (s : ℕ) => a.1 + (1 / 2 : ℚ) ^ s < q (a.2, s)) hRE).of_iff ?_
  rintro ⟨r, x⟩
  constructor
  · rintro ⟨s, hs⟩
    have hs' : (r : ℝ) + (2 : ℝ)⁻¹ ^ s < q (x, s) := by
      have : ((r + (1 / 2 : ℚ) ^ s : ℚ) : ℝ) < ((q (x, s) : ℚ) : ℝ) := by exact_mod_cast hs
      push_cast at this
      simpa using this
    have := (abs_le.mp (hbound x s)).2
    change (r : ℝ) < m x
    linarith
  · intro h
    have h' : (r : ℝ) < m x := h
    obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (m x - r) / 2)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨s, ?_⟩
    have := (abs_le.mp (hbound x s)).1
    have key : (r : ℝ) + (2 : ℝ)⁻¹ ^ s < q (x, s) := by linarith
    have : ((r + (1 / 2 : ℚ) ^ s : ℚ) : ℝ) < ((q (x, s) : ℚ) : ℝ) := by
      push_cast; simpa using key
    exact_mod_cast this

/-- **SUV Theorem 182(a), p. 279.**  Every Martin-Löf random sequence is computably random, for a
computable `π`.  We allow null cylinders, extending the section's standing positivity convention;
the lower semicomputable test argument does not need positivity. -/
theorem isComputablyRandom_of_isMartinLofRandom {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (hπ : IsComputableMeasure π) {w : CantorSeq} (hw : IsMartinLofRandom π w) :
    IsComputablyRandom π w := by
  intro m hm hc
  have hlsc := isComputablyRandom_of_isMartinLofRandom_lsc hc
  exact (isMartinLofRandom_iff_forall_lsc_not_wins hπ w).mp hw m hm hlsc


/-- Step 1 of the proof of `exists_computable_seq_bounded`: if `m` is computable, there
exists a computable choice function that bounds the increase. -/
private lemma exists_computable_seq_bounded_computable_choice {π : Measure CantorSeq}
    [IsProbabilityMeasure π]
    (hpos : ∀ x, 0 < cantorMass π x) {m : BitString → ℝ}
    (hm : IsFairCapital π m) (hc : IsComputableOnStrings m) :
    ∃ f : BitString → Bool, Computable f ∧ ∀ x, m (x ++ [f x]) ≤ m x + (2 : ℝ)⁻¹ ^ x.length := by
  obtain ⟨q, hq, hb⟩ := hc
  have hA : Computable (fun x : BitString => q (x ++ [false], x.length + 1)) :=
    hq.comp ((Computable.list_concat.comp Computable.id (Computable.const false)).pair
      (Primrec.succ.to_comp.comp Computable.list_length))
  have hB : Computable (fun x : BitString => q (x ++ [true], x.length + 1)) :=
    hq.comp ((Computable.list_concat.comp Computable.id (Computable.const true)).pair
      (Primrec.succ.to_comp.comp Computable.list_length))
  have hcmp : Computable₂ (fun a b : ℚ => decide (a ≤ b)) :=
    (PrimrecRel.decide ComputableReals.primrec_ratLe).to_comp
  refine ⟨fun x => !decide (q (x ++ [false], x.length + 1) ≤ q (x ++ [true], x.length + 1)),
    Primrec.not.to_comp.comp (hcmp.comp hA hB), ?_⟩
  intro x
  have hadd := massR_add (π := π) x
  have hfair := hm.fair x
  have h0 : 0 ≤ massR π (x ++ [false]) := ENNReal.toReal_nonneg
  have h1 : 0 ≤ massR π (x ++ [true]) := ENNReal.toReal_nonneg
  have hP : 0 < massR π x := ENNReal.toReal_pos (hpos x).ne' (measure_ne_top _ _)
  have hb0 := abs_le.mp (hb (x ++ [false]) (x.length + 1))
  have hb1 := abs_le.mp (hb (x ++ [true]) (x.length + 1))
  have he : (2 : ℝ)⁻¹ ^ x.length = 2 * (2 : ℝ)⁻¹ ^ (x.length + 1) := by
    rw [pow_succ]; ring
  have hd : 0 ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
  have hmx : m x * massR π x =
      m (x ++ [false]) * massR π (x ++ [false]) + m (x ++ [true]) * massR π (x ++ [true]) := hfair
  by_cases hle : q (x ++ [false], x.length + 1) ≤ q (x ++ [true], x.length + 1)
  · have hle' : (q (x ++ [false], x.length + 1) : ℝ) ≤ q (x ++ [true], x.length + 1) := by
      exact_mod_cast hle
    have hab : m (x ++ [false]) - (2 : ℝ)⁻¹ ^ x.length ≤ m (x ++ [true]) := by
      rw [he]; linarith
    have : (m (x ++ [false]) - (2 : ℝ)⁻¹ ^ x.length) * massR π x ≤ m x * massR π x := by
      rw [hmx, hadd]; nlinarith
    have := le_of_mul_le_mul_right this hP
    simp only [hle, decide_true, Bool.not_true]
    linarith
  · have hle' : (q (x ++ [true], x.length + 1) : ℝ) ≤ q (x ++ [false], x.length + 1) := by
      exact_mod_cast (not_le.mp hle).le
    have hab : m (x ++ [true]) - (2 : ℝ)⁻¹ ^ x.length ≤ m (x ++ [false]) := by
      rw [he]; linarith
    have : (m (x ++ [true]) - (2 : ℝ)⁻¹ ^ x.length) * massR π x ≤ m x * massR π x := by
      rw [hmx, hadd]; nlinarith
    have := le_of_mul_le_mul_right this hP
    simp only [hle, decide_false, Bool.not_false]
    linarith

/-- Step 2 of the proof of `exists_computable_seq_bounded`: given a sequence generated by
such a choice function, `m` does not win on it. -/
private lemma exists_computable_seq_bounded_bounded {m : BitString → ℝ}
    {f : BitString → Bool} (hf : ∀ x, m (x ++ [f x]) ≤ m x + (2 : ℝ)⁻¹ ^ x.length)
    (w : CantorSeq) (hw : ∀ n, w n = f (cantorPrefix w n)) :
    ¬ Wins m w := by
  have key : ∀ n, m (cantorPrefix w n) ≤ m [] + 2 - 2 * (2:ℝ)⁻¹ ^ n := by
    intro n
    induction n with
    | zero =>
      have : cantorPrefix w 0 = [] := by simp [cantorPrefix]
      rw [this]; norm_num
    | succ n ih =>
      have h1 := hf (cantorPrefix w n)
      rw [cantorPrefix_length, ← hw n, ← cantorPrefix_succ] at h1
      rw [pow_succ]
      nlinarith [h1, ih]
  intro hwin
  apply hwin
  refine ⟨m [] + 2, ?_⟩
  rintro _ ⟨n, rfl⟩
  have : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ n := by positivity
  have := key n
  change m (cantorPrefix w n) ≤ m [] + 2
  linarith

/-- Step 3 of the proof of `exists_computable_seq_bounded`: a computable choice function
defines a computable sequence. -/
private lemma exists_computable_seq_bounded_seq {f : BitString → Bool} (hf : Computable f) :
    ∃ w : CantorSeq, Computable w ∧ ∀ n, w n = f (cantorPrefix w n) := by
  let g : ℕ → BitString := fun n => Nat.rec ([] : BitString) (fun _ u => u ++ [f u]) n
  have hg : Computable g := by
    have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × BitString) => p.2 ++ [f p.2]) := by
      have h1 : Computable (fun p : ℕ × (ℕ × BitString) => f p.2.2) :=
        hf.comp (Computable.snd.comp Computable.snd)
      exact Computable.list_concat.comp (Computable.snd.comp Computable.snd) h1
    have := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ : ℕ => ([] : BitString))
      (h := fun (_ : ℕ) (p : ℕ × BitString) => p.2 ++ [f p.2]) Computable.id
      (Computable.const _) hstep
    exact this
  refine ⟨fun n => f (g n), hf.comp hg, ?_⟩
  have key : ∀ n, g n = cantorPrefix (fun n => f (g n)) n := by
    intro n
    induction n with
    | zero => simp [g, cantorPrefix]
    | succ n ih =>
      rw [cantorPrefix_succ, ← ih]
  intro n
  simp only [← key]

/-- **Proof of Theorem 182(b), SUV p. 280.**  For a computable martingale there is a computable
sequence on which it is bounded: go where it increases at most by `2^{-n}`. -/
theorem exists_computable_seq_bounded {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) {m : BitString → ℝ}
    (hm : IsFairCapital π m) (hc : IsComputableOnStrings m) :
    ∃ w, Computable w ∧ ¬ Wins m w := by
  obtain ⟨f, hf_comp, hf_bound⟩ := exists_computable_seq_bounded_computable_choice hpos hm
      hc
  obtain ⟨w, hw_comp, hw_eq⟩ := exists_computable_seq_bounded_seq hf_comp
  use w, hw_comp
  exact exists_computable_seq_bounded_bounded hf_bound w hw_eq

/-- The prefix of length `|x| + 1` of `w` is `x ++ [b]` iff the prefix of length `|x|` is `x`
and the next bit of `w` is `b`. -/
private lemma not_isComputablyRandom_of_computable_prefix_append (w : CantorSeq) (x : BitString)
    (b : Bool) :
    cantorPrefix w (x.length + 1) = x ++ [b] ↔ (cantorPrefix w x.length = x ∧ w x.length = b) := by
  rw [cantorPrefix_succ]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact ⟨h1, List.singleton_inj.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- The capital betting everything on the next bit of `w`: it is `2 ^ |x|` on the prefixes of `w`
and `0` elsewhere. -/
private noncomputable def not_isComputablyRandom_of_computable_M (w : CantorSeq) (x : BitString) :
    ℝ :=
  if cantorPrefix w x.length = x then (2 : ℝ) ^ x.length else 0

/-- The value of the all-in capital at a one-bit extension. -/
private lemma not_isComputablyRandom_of_computable_M_append (w : CantorSeq) (x : BitString)
    (b : Bool) :
    not_isComputablyRandom_of_computable_M w (x ++ [b]) =
      if cantorPrefix w x.length = x ∧ w x.length = b then (2 : ℝ) ^ (x.length + 1) else 0 := by
  unfold not_isComputablyRandom_of_computable_M
  simp only [List.length_append, List.length_singleton,
    not_isComputablyRandom_of_computable_prefix_append]

/-- The all-in capital on the next bit of any sequence is fair for the uniform measure. -/
private lemma not_isComputablyRandom_of_computable_M_fair (w : CantorSeq) :
    IsFairCapital uniformMeasure (not_isComputablyRandom_of_computable_M w) := by
  rw [isFairCapital_uniform_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · unfold not_isComputablyRandom_of_computable_M
    split_ifs <;> positivity
  · rw [not_isComputablyRandom_of_computable_M_append,
      not_isComputablyRandom_of_computable_M_append]
    unfold not_isComputablyRandom_of_computable_M
    by_cases hP : cantorPrefix w x.length = x
    · cases hb : w x.length <;> simp [hP, pow_succ]
    · simp [hP]

/-- The all-in capital on the next bit of `w` wins on `w`: it is `2 ^ n` on the prefix of length
`n`. -/
private lemma not_isComputablyRandom_of_computable_M_wins (w : CantorSeq) :
    Wins (not_isComputablyRandom_of_computable_M w) w := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  have h := hB ⟨n, rfl⟩
  have hd : not_isComputablyRandom_of_computable_M w (cantorPrefix w n) = 2 ^ n := by
    simp [not_isComputablyRandom_of_computable_M, cantorPrefix_length]
  dsimp only at h
  rw [hd] at h
  linarith

/-- For a computable `w` the all-in capital is computable (with error `0`). -/
private lemma not_isComputablyRandom_of_computable_M_comp (w : CantorSeq) (hw : Computable w) :
    IsComputableOnStrings (not_isComputablyRandom_of_computable_M w) := by
  have hlen : Computable (fun p : BitString × ℕ => p.1.length) :=
    Computable.list_length.comp Computable.fst
  have hcp : Computable (fun p : BitString × ℕ => cantorPrefix w p.1.length) :=
    ((computable_prefixList hw).comp hlen).of_eq fun p => prefixList_eq_cantorPrefix w _
  have hdec : Computable (fun p : BitString × ℕ => decide (cantorPrefix w p.1.length = p.1)) :=
    Computable₂.comp (Primrec.eq (α := BitString)).decide.to_comp hcp Computable.fst
  have hpow : Computable (fun p : BitString × ℕ => ((2 ^ p.1.length : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp (comp_pow.comp hlen)
  have hq := Computable.cond hdec hpow (Computable.const (0 : ℚ))
  refine ⟨_, hq, fun x s => ?_⟩
  have key : ((cond (decide (cantorPrefix w x.length = x)) ((2 ^ x.length : ℕ) : ℚ) 0 : ℚ) : ℝ) =
      not_isComputablyRandom_of_computable_M w x := by
    unfold not_isComputablyRandom_of_computable_M
    by_cases h : cantorPrefix w x.length = x <;> simp [h]
  dsimp only
  rw [key, sub_self, abs_zero]
  positivity

/-- **SUV p. 280.**  On a computable sequence one can win: a computable sequence is not computably
random, for the uniform measure. -/
theorem not_isComputablyRandom_of_computable {w : CantorSeq} (hw : Computable w) :
    ¬ IsComputablyRandom uniformMeasure w := by
  intro h
  exact h _ (not_isComputablyRandom_of_computable_M_fair w)
    (not_isComputablyRandom_of_computable_M_comp w hw)
    (not_isComputablyRandom_of_computable_M_wins w)

/-- **SUV p. 280, a corollary of the above.**  There is no largest computable martingale, up to a
constant factor. -/
theorem not_exists_largest_computable_capital :
    ¬ ∃ M, IsFairCapital uniformMeasure M ∧ IsComputableOnStrings M ∧
      ∀ m, IsFairCapital uniformMeasure m → IsComputableOnStrings m →
        ∃ c : ℝ, ∀ x, m x ≤ c * M x := by
  rintro ⟨M, hM_fair, hM_comp, hM_max⟩
  have h_pi_comp := isComputableMeasure_uniform
  have h_pi_pos : ∀ x, 0 < cantorMass uniformMeasure x := by
    intro x
    rw [cantorMass_uniformMeasure]
    exact ENNReal.pow_pos (by norm_num) _
  obtain ⟨w, hw_comp, hw_not_wins⟩ := exists_computable_seq_bounded h_pi_comp h_pi_pos hM_fair
      hM_comp
  have hw_not_rand := not_isComputablyRandom_of_computable hw_comp
  rw [IsComputablyRandom] at hw_not_rand
  push Not at hw_not_rand
  obtain ⟨m, hm_fair, hm_comp, hm_wins⟩ := hw_not_rand
  obtain ⟨c, hc⟩ := hM_max m hm_fair hm_comp
  rw [Wins] at hw_not_wins hm_wins
  push Not at hw_not_wins
  apply hm_wins
  obtain ⟨K, hK⟩ := hw_not_wins
  use max c 0 * K
  rintro _ ⟨n, rfl⟩
  have h1 := hc (cantorPrefix w n)
  have h2 := hK ⟨n, rfl⟩
  have h3 : 0 ≤ M (cantorPrefix w n) := hM_fair.nonneg _
  calc
    m (cantorPrefix w n) ≤ c * M (cantorPrefix w n) := h1
    _ ≤ max c 0 * M (cantorPrefix w n) := mul_le_mul_of_nonneg_right (le_max_left c 0) h3
    _ ≤ max c 0 * K := mul_le_mul_of_nonneg_left h2 (le_max_right c 0)

end Kolmogorov.FrequencyGames
