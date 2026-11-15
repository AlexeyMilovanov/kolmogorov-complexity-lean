/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.Gales.GalesAndNullSets

/-!
# Lower Semicomputable Gales

Lower semicomputable gales and effective `α`-null sets (Shen–Uspensky–Vereshchagin, the part
on gales and effective dimension).  The module builds, from effective `α`-null sets, lower
semicomputable `2^α`-gales that win on them (`exists_lsc_isGale_wins_of_isEffectiveAlphaNull`),
and shows the converse direction for sequences that are not effectively `α`-null
(`exists_lsc_isGale_not_isEffectiveAlphaNull`).  The proofs use elementary gales of single
strings, enumerable greedy packings of trees, and mixtures of gales weighted by prefix-free
complexity.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- Exponentiation of a rational base by a natural exponent is computable in both arguments. -/
lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_ratPow :
    Computable (fun z : ℚ × ℕ => z.1 ^ z.2) := by
  let step : ℚ × ℕ → ℕ × ℚ → ℚ := fun z q => q.2 * z.1
  have hstep : Computable (fun z : (ℚ × ℕ) × (ℕ × ℚ) => step z.1 z.2) :=
    computable₂_ratMul.comp (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.fst)
  have hrec := Computable.nat_rec (h := step) Computable.snd
    (Computable.const 1) hstep.to₂
  exact hrec.of_eq fun z => by
    induction z.2 with
    | zero => simp
    | succ n ih => simp only [step, ih, pow_succ, mul_comm]

/-- Step 1, computable test `r ^ (q + 1) * 2 ^ (p * j) < 1` on the data `((r, j), (p, q))`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test :
    Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) =>
      decide (a.1.1 ^ (a.2.2 + 1) * 2 ^ (a.2.1 * a.1.2) < 1)) := by
  have hq : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.1.1) :=
    Computable.fst.comp Computable.fst
  have hj : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.1.2) :=
    Computable.snd.comp Computable.fst
  have hp : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hq' : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.2) :=
    Computable.snd.comp Computable.snd
  have hq1 : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.2 + 1) :=
    Computable.succ.comp hq'
  have hpj : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.1 * a.1.2) :=
    Primrec.nat_mul.to_comp.comp hp hj
  have hp1 : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.1.1 ^ (a.2.2 + 1)) :=
    Computable.comp (f := fun z : ℚ × ℕ => z.1 ^ z.2)
      (g := fun a : (ℚ × ℕ) × (ℕ × ℕ) => (a.1.1, a.2.2 + 1))
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_ratPow (hq.pair hq1)
  have hp2 : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => (2 : ℚ) ^ (a.2.1 * a.1.2)) :=
    Computable.comp (f := fun z : ℚ × ℕ => z.1 ^ z.2)
      (g := fun a : (ℚ × ℕ) × (ℕ × ℕ) => ((2 : ℚ), a.2.1 * a.1.2))
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_ratPow
      ((Computable.const (2 : ℚ)).pair hpj)
  have hprod : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) =>
      a.1.1 ^ (a.2.2 + 1) * 2 ^ (a.2.1 * a.1.2)) :=
    Computable₂.comp (f := fun x y : ℚ => x * y) computable₂_ratMul hp1 hp2
  exact Computable.comp (f := fun q : ℚ => decide (q < 1)) (computable_ratLtConst 1) hprod

/-- Step 1, the enumerable form: `r ≤ 0`, or there are naturals `p`, `q` with `β < p / (q + 1)`
and `r ^ (q + 1) * 2 ^ (p * j) < 1`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_re {β : ℝ}
    (hβ : ComputableReals.IsComputableReal β) :
    IsRE (fun x : ℚ × ℕ => x.1 ≤ 0 ∨ ∃ pq : ℕ × ℕ,
      decide (x.1 ^ (pq.2 + 1) * 2 ^ (pq.1 * x.2) < 1) = true ∧
        β < (((pq.1 : ℚ) / ((pq.2 : ℚ) + 1) : ℚ) : ℝ)) := by
  have hREb : IsRE (fun b : ℚ => β < (b : ℝ)) := by
    have h1 : IsRE (fun r : ℚ => (r : ℝ) < -β) :=
      ComputableReals.isRE_rat_lt_of_isLowerSemicomputableReal hβ.neg.isLowerSemicomputableReal
    refine (h1.comp_computable ComputableReals.computable_ratNeg).of_iff (fun b => ?_)
    simp only [Rat.cast_neg, neg_lt_neg_iff]
  have hdiv : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) =>
      ((a.2.1 : ℚ) / ((a.2.2 : ℚ) + 1) : ℚ)) := by
    have hp : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.1) :=
      Computable.fst.comp Computable.snd
    have hq' : Computable (fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.2) :=
      Computable.snd.comp Computable.snd
    refine computable_of_num_den (N := fun a => ((a.2.1 : ℕ) : ℤ)) (D := fun a => a.2.2 + 1)
      ?_ ?_ ?_ ?_
    · exact Computable.comp (f := fun n : ℕ => (n : ℤ)) (g := fun a : (ℚ × ℕ) × (ℕ × ℕ) => a.2.1)
        ComputableReals.primrec_natCastInt.to_comp hp
    · exact Computable.succ.comp hq'
    · intro a
      exact Nat.succ_pos _
    · intro a
      push_cast
      rfl
  have hA : IsRE (fun a : (ℚ × ℕ) × (ℕ × ℕ) =>
      β < (((a.2.1 : ℚ) / ((a.2.2 : ℚ) + 1) : ℚ) : ℝ)) := hREb.comp_computable hdiv
  have hB := hA.and_computable exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test
  have hC := IsRE.exists_encodable
    (R := fun (x : ℚ × ℕ) (pq : ℕ × ℕ) =>
      decide (x.1 ^ (pq.2 + 1) * 2 ^ (pq.1 * x.2) < 1) = true ∧
        β < (((pq.1 : ℚ) / ((pq.2 : ℚ) + 1) : ℚ) : ℝ)) hB
  have hle : IsRE (fun x : ℚ × ℕ => x.1 ≤ 0) := by
    refine isRE_of_computable_bool _ (fun x : ℚ × ℕ => decide (x.1 ≤ 0)) (fun x => by simp) ?_
    exact Computable₂.comp (f := fun a b : ℚ => decide (a ≤ b))
      ((PrimrecRel.decide ComputableReals.primrec_ratLe).to_comp)
      (Computable.fst : Computable (fun x : ℚ × ℕ => x.1)) (Computable.const (0 : ℚ))
  exact hle.or hC

/-- Step 1, backward direction (real analysis): if `β < p / (q + 1)` and
`r ^ (q + 1) * 2 ^ (p * j) < 1`, then `r < 2 ^ (-(β j))`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mpr {β : ℝ} (r : ℚ)
    (j p q : ℕ) (hdec : r ^ (q + 1) * 2 ^ (p * j) < 1)
    (hlt : β < (((p : ℚ) / ((q : ℚ) + 1) : ℚ) : ℝ)) :
    (r : ℝ) < (2 : ℝ) ^ (-(β * (j : ℝ))) := by
  by_contra hcon
  rw [not_lt] at hcon
  have hs : (0 : ℝ) < (2 : ℝ) ^ (-(β * (j : ℝ))) := by positivity
  have h1 : ((2 : ℝ) ^ (-(β * (j : ℝ)))) ^ (q + 1) ≤ (r : ℝ) ^ (q + 1) :=
    pow_le_pow_left₀ hs.le hcon _
  have h2 : ((2 : ℝ) ^ (-(β * (j : ℝ)))) ^ (q + 1) =
      (2 : ℝ) ^ (-(β * (j : ℝ)) * ((q + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h3 : β * ((q : ℝ) + 1) < p := by
    have h : β < (p : ℝ) / ((q : ℝ) + 1) := by
      push_cast at hlt
      exact hlt
    rwa [lt_div_iff₀ (by positivity)] at h
  have h4 : (2 : ℝ) ^ (-((p : ℝ) * j)) ≤ (2 : ℝ) ^ (-(β * (j : ℝ)) * ((q + 1 : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have h5 : (r : ℝ) ^ (q + 1) * (2 : ℝ) ^ (p * j) < 1 := by exact_mod_cast hdec
  have h6 : (2 : ℝ) ^ (p * j) * (2 : ℝ) ^ (-((p : ℝ) * j)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    push_cast
    simp
  have hA : (0 : ℝ) < (2 : ℝ) ^ (p * j) := by positivity
  have h7 : (2 : ℝ) ^ (-((p : ℝ) * j)) ≤ (r : ℝ) ^ (q + 1) := by
    rw [h2] at h1
    exact h4.trans h1
  nlinarith [mul_le_mul_of_nonneg_left h7 hA.le]

/-- Step 1, forward direction (real analysis): if `0 < r < 2 ^ (-(β j))` and `β ≥ 0`, there are
naturals `p`, `q` with `β < p / (q + 1)` and `r ^ (q + 1) * 2 ^ (p * j) < 1`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mp {β : ℝ} (hβ0 : 0 ≤ β)
    (r : ℚ) (j : ℕ) (hr : 0 < r) (h : (r : ℝ) < (2 : ℝ) ^ (-(β * (j : ℝ)))) :
    ∃ pq : ℕ × ℕ, r ^ (pq.2 + 1) * 2 ^ (pq.1 * j) < 1 ∧
      β < (((pq.1 : ℚ) / ((pq.2 : ℚ) + 1) : ℚ) : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    refine ⟨(⌊β⌋₊ + 1, 0), ?_, ?_⟩
    · simp only [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero] at h
      simp only [zero_add, pow_one, mul_zero, pow_zero, mul_one]
      exact_mod_cast h
    · simp only [Nat.cast_zero, zero_add, div_one, Nat.cast_add, Nat.cast_one]
      push_cast
      exact Nat.lt_floor_add_one β
  · have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
    have hlog : Real.logb 2 (r : ℝ) < -(β * j) :=
      (Real.logb_lt_iff_lt_rpow (by norm_num) hr').mpr h
    have hγ : β < -(Real.logb 2 (r : ℝ)) / j := by
      rw [lt_div_iff₀ hjpos]
      linarith
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hγ
    have hbpos : (0 : ℚ) < b := by
      have : (0 : ℝ) < b := lt_of_le_of_lt hβ0 hb1
      exact_mod_cast this
    have hnum : 0 < b.num := Rat.num_pos.mpr hbpos
    have hq : b.den - 1 + 1 = b.den := Nat.sub_add_cancel b.den_pos
    have hp : ((b.num.toNat : ℕ) : ℤ) = b.num := Int.toNat_of_nonneg hnum.le
    have hden : ((b.den - 1 : ℕ) : ℚ) + 1 = (b.den : ℚ) := by
      have := congrArg (Nat.cast : ℕ → ℚ) hq
      rwa [Nat.cast_add, Nat.cast_one] at this
    have hnumq : ((b.num.toNat : ℕ) : ℚ) = (b.num : ℚ) := by
      rw [← Int.cast_natCast, hp]
    have hbq : ((b.num.toNat : ℕ) : ℚ) / (((b.den - 1 : ℕ) : ℚ) + 1) = b := by
      rw [hden, hnumq]
      exact Rat.num_div_den b
    refine ⟨(b.num.toNat, b.den - 1), ?_, ?_⟩
    · have hbj : Real.logb 2 (r : ℝ) < -((b : ℝ) * j) := by
        have := (lt_div_iff₀ hjpos).mp hb2
        linarith
      have hrb : (r : ℝ) < (2 : ℝ) ^ (-((b : ℝ) * j)) :=
        (Real.logb_lt_iff_lt_rpow (by norm_num) hr').mp hbj
      have hq0 : b.den ≠ 0 := b.den_nz
      have h1 : (r : ℝ) ^ b.den < ((2 : ℝ) ^ (-((b : ℝ) * j))) ^ b.den :=
        pow_lt_pow_left₀ hrb hr'.le hq0
      have hbden : (b : ℝ) * (b.den : ℝ) = (b.num.toNat : ℝ) := by
        have h2 : (b : ℚ) * (b.den : ℚ) = ((b.num.toNat : ℕ) : ℚ) := by
          rw [Rat.mul_den_eq_num b, hnumq]
        exact_mod_cast h2
      have h2 : ((2 : ℝ) ^ (-((b : ℝ) * j))) ^ b.den =
          (2 : ℝ) ^ (-((b.num.toNat : ℝ) * j)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← hbden]
        congr 1
        ring
      have h6 : (2 : ℝ) ^ (b.num.toNat * j) * (2 : ℝ) ^ (-((b.num.toNat : ℝ) * j)) = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        push_cast
        simp
      have hA : (0 : ℝ) < (2 : ℝ) ^ (b.num.toNat * j) := by positivity
      have h3 : (r : ℝ) ^ b.den * (2 : ℝ) ^ (b.num.toNat * j) < 1 := by
        rw [h2] at h1
        nlinarith [mul_lt_mul_of_pos_right h1 hA]
      rw [hq]
      exact_mod_cast h3
    · rw [hbq]
      exact hb1

/-- Step 1 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
for a computable `β ≥ 0`, the set of rationals `r` below `2^(-β j)` is enumerable, uniformly in `j`.
(For `r ≤ 0` it holds trivially; for `r > 0` it holds iff there are naturals `p`, `q > 0` with
`β < p / q` and `r ^ q * 2 ^ (p * j) < 1`; the condition `β < p / q` is enumerable because `β` is
computable.) -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc_exp
    {β : ℝ} (hβ : ComputableReals.IsComputableReal β) (hβ0 : 0 ≤ β) :
    IsRE (fun p : ℚ × ℕ => (p.1 : ℝ) < (2 : ℝ) ^ (-(β * (p.2 : ℝ)))) := by
  refine (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_re hβ).of_iff (fun x => ?_)
  constructor
  · rintro (hr | ⟨⟨p, q⟩, hdec, hlt⟩)
    · have : (x.1 : ℝ) ≤ 0 := by exact_mod_cast hr
      exact lt_of_le_of_lt this (by positivity)
    · exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mpr x.1 x.2 p q
        (decide_eq_true_eq.mp hdec) hlt
  · intro h
    rcases le_or_gt x.1 0 with hr | hr
    · exact Or.inl hr
    · obtain ⟨pq, hdec, hlt⟩ :=
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mp hβ0 x.1 x.2 hr h
      exact Or.inr ⟨pq, decide_eq_true_eq.mpr hdec, hlt⟩
/-- The elementary `α`-gale of a cover element `o`: for `o = some x` it equals
`2^{-α (|x| - |y|)}` on the prefixes `y` of `x`, `2^{-(1-α)(|y| - |x|)}` on the proper extensions
`y` of `x`, and `0` on strings incomparable with `x`; for `o = none` it vanishes. -/
private noncomputable def exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (α : ℝ) :
    Option BitString → BitString → ℝ
  | none, _ => 0
  | some x, y =>
      if y <+: x then (2 : ℝ) ^ (-(α * ((x.length - y.length : ℕ) : ℝ)))
      else if x <+: y then (2 : ℝ) ^ (-((1 - α) * ((y.length - x.length : ℕ) : ℝ)))
      else 0

/-- Value of the elementary gale of `x` on a prefix `y` of `x`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix (α : ℝ)
    {x y : BitString} (h : y <+: x) :
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) y =
      (2 : ℝ) ^ (-(α * ((x.length - y.length : ℕ) : ℝ))) := by
  simp only [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale, h, ↓reduceIte]

/-- Value of the elementary gale of `x` on a proper extension `y` of `x`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ext (α : ℝ)
    {x y : BitString} (h1 : ¬ y <+: x) (h2 : x <+: y) :
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) y =
      (2 : ℝ) ^ (-((1 - α) * ((y.length - x.length : ℕ) : ℝ))) := by
  simp only [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale, h1, h2, ↓reduceIte]

/-- Value of the elementary gale of `x` on a string incomparable with `x`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_incomp (α : ℝ)
    {x y : BitString} (h1 : ¬ y <+: x) (h2 : ¬ x <+: y) :
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) y = 0 := by
  simp only [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale, h1, h2, ↓reduceIte]

/-- Value of the elementary gale of `x` on an extension `y` of `x` (possibly `y = x`). -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ge (α : ℝ)
    {x y : BitString} (h : x <+: y) :
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) y =
      (2 : ℝ) ^ (-((1 - α) * ((y.length - x.length : ℕ) : ℝ))) := by
  by_cases h1 : y <+: x
  · have hyx : y = x := h1.eq_of_length (le_antisymm h1.length_le h.length_le)
    subst hyx
    rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix α h1]
    simp
  · exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ext α h1 h

/-- Elementary gales are non-negative. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_nonneg (α : ℝ)
    (o : Option BitString) (y : BitString) :
    0 ≤ exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α o y := by
  cases o with
  | none => simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale]
  | some x =>
    by_cases h1 : y <+: x
    · rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix α h1]
      positivity
    · by_cases h2 : x <+: y
      · rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ext α h1 h2]
        positivity
      · rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_incomp α h1 h2]

/-- The children of a string incomparable with `x` are incomparable with `x`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_children_incomp {x y : BitString}
    (h1 : ¬ y <+: x) (h2 : ¬ x <+: y) (b : Bool) :
    ¬ (y ++ [b]) <+: x ∧ ¬ x <+: (y ++ [b]) := by
  refine ⟨fun h => h1 ((List.prefix_append y [b]).trans h), fun h => ?_⟩
  rcases List.prefix_concat_iff.mp h with h | h
  · exact h1 (h ▸ List.prefix_append y [b])
  · exact h2 h

/-- If `x = y ++ c :: t`, the child `y ++ [b]` with `b ≠ c` is incomparable with `x`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_wrong_child {y t : BitString}
    {b c : Bool} (h : b ≠ c) :
    ¬ (y ++ [b]) <+: (y ++ c :: t) ∧ ¬ (y ++ c :: t) <+: (y ++ [b]) := by
  constructor
  · intro hp
    rw [List.prefix_append_right_inj, List.cons_prefix_cons] at hp
    exact h hp.1
  · intro hp
    rcases List.prefix_concat_iff.mp hp with hp | hp
    · have := List.append_cancel_left hp
      simp only [List.cons.injEq] at this
      exact h this.1.symm
    · have := hp.length_le
      simp at this

/-- The gale equation for the elementary gale of `x`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_gale_eq (α : ℝ)
    (x y : BitString) :
    (2 : ℝ) ^ α * exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) y =
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) (y ++ [false]) +
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) (y ++ [true]) := by
  by_cases hxy : x <+: y
  · have hc : ∀ b : Bool, x <+: y ++ [b] := fun b => hxy.trans (List.prefix_append y [b])
    have hlen : x.length ≤ y.length := hxy.length_le
    have e : ∀ b : Bool, (y ++ [b]).length - x.length = (y.length - x.length) + 1 := by
      intro b
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ge α hxy,
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ge α (hc false),
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_ge α (hc true), e, e]
    have h2 : (2 : ℝ) ^ (-((1 - α) * (((y.length - x.length) + 1 : ℕ) : ℝ))) =
        (2 : ℝ) ^ (-((1 - α) * ((y.length - x.length : ℕ) : ℝ))) * (2 : ℝ) ^ (α - 1) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have h3 : (2 : ℝ) ^ α = 2 * (2 : ℝ) ^ (α - 1) := by
      rw [Real.rpow_sub_one (by norm_num)]
      ring
    rw [h2, h3]
    ring
  · by_cases hyx : y <+: x
    · obtain ⟨t, rfl⟩ := hyx
      cases t with
      | nil => exact absurd (by simp) hxy
      | cons c t' =>
        have hp : y <+: y ++ c :: t' := List.prefix_append y _
        have hpc : (y ++ [c]) <+: (y ++ c :: t') := by
          rw [List.prefix_append_right_inj]
          simp
        have hsum : exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some (y ++ c :: t'))
              (y ++ [false]) +
            exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some (y ++ c :: t'))
              (y ++ [true]) =
            exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some (y ++ c :: t'))
              (y ++ [c]) +
            exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some (y ++ c :: t'))
              (y ++ [!c]) := by
          cases c <;> simp [add_comm]
        have hw := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_wrong_child (y := y) (t := t')
          (b := !c) (c := c) (by cases c <;> simp)
        rw [hsum,
          exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_incomp α hw.1 hw.2,
          exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix α hpc,
          exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix α hp, add_zero]
        have e1 : (y ++ c :: t').length - (y ++ [c]).length = t'.length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have e2 : (y ++ c :: t').length - y.length = t'.length + 1 := by
          simp only [List.length_append, List.length_cons]
          omega
        rw [e1, e2, ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring
    · have h0 := fun b : Bool =>
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_children_incomp hyx hxy b
      rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_incomp α hyx hxy,
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_incomp α (h0 false).1
          (h0 false).2,
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_incomp α (h0 true).1
          (h0 true).2]
      simp

/-- Step 2a of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`: every
elementary gale is an `α`-gale (for every real `α`; the gale equation is checked on the three
cases `y ≺ x` or `y = x`, `x ≺ y`, `y` incomparable with `x`). -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_gale (α : ℝ)
    (o : Option BitString) :
    IsGale α (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α o) := by
  refine ⟨exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_nonneg α o, fun y => ?_⟩
  cases o with
  | none => simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale]
  | some x => exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_gale_eq α x y

/-- Step 2b of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`: the
elementary gale of `x` equals `1` at `x`, and the initial capital of the elementary gale of `o` is
the (real value of the) `α`-mass `coverAlphaMass α o = μ(Ω_x)^α = 2^{-α |x|}` (or `0` for `none`).
-/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_self_init (α : ℝ) :
    (∀ x : BitString, exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α (some x) x = 1) ∧
    (∀ o : Option BitString,
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α o [] =
        (coverAlphaMass α o).toReal) := by
  refine ⟨fun x => ?_, fun o => ?_⟩
  · rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix α (List.prefix_refl x)]
    simp
  · cases o with
    | none => simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale]
    | some x =>
      rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix α List.nil_prefix,
        coverAlphaMass_some, intervalAlphaMass_eq_inv_two_pow, ← ENNReal.toReal_rpow,
        ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      simp only [List.length_nil, Nat.sub_zero]
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num),
        ← Real.rpow_mul (by norm_num)]
      congr 1
      ring

/-- Step 2c, auxiliary: the prefix test on bit strings is primitive recursive. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_prefix :
    Primrec₂ (fun l1 l2 : BitString => decide (l1 <+: l2)) := by
  have htake : Primrec (fun p : BitString × BitString => p.2.take p.1.length) :=
    Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd
  have h : Primrec (fun p : BitString × BitString => decide (p.2.take p.1.length = p.1)) :=
    primrec_decideEq.comp htake Primrec.fst
  refine h.of_eq (fun p => ?_)
  by_cases hp : p.1 <+: p.2
  · have h' : p.2.take p.1.length = p.1 := (List.prefix_iff_eq_take.mp hp).symm
    simp [hp, h']
  · have h' : ¬ p.2.take p.1.length = p.1 := fun h' => hp (List.prefix_iff_eq_take.mpr h'.symm)
    simp [hp, h']

/-- Step 2c, auxiliary: the case analysis defining the elementary gale, as a disjunction of
decidable tests and the two exponential comparisons of Step 1. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_iff (α : ℝ) (r : ℚ)
    (o : Option BitString) (y : BitString) :
    (r : ℝ) < exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α o y ↔
      ((o.isSome && decide (y <+: o.getD [])) = true ∧
        (r : ℝ) < (2 : ℝ) ^ (-(α * (((o.getD []).length - y.length : ℕ) : ℝ)))) ∨
      (((o.isSome && (!decide (y <+: o.getD []) && decide (o.getD [] <+: y))) = true ∧
        (r : ℝ) < (2 : ℝ) ^ (-((1 - α) * ((y.length - (o.getD []).length : ℕ) : ℝ)))) ∨
      (((!o.isSome || (!decide (y <+: o.getD []) && !decide (o.getD [] <+: y))) &&
        decide (r < 0)) = true)) := by
  cases o with
  | none =>
    simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale]
  | some x =>
    by_cases h1 : y <+: x
    · simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale, h1]
    · by_cases h2 : x <+: y
      · simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale, h1, h2]
      · simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale, h1, h2]

/-- Step 2c of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`: for a
computable `α ∈ [0, 1]` the elementary gales are uniformly lower semicomputable.  (Use Step 1 with
`β = α` and `β = 1 - α` for the values `2^{-α j}`, `2^{-(1-α) j}`; prefix tests are computable.) -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc {α : ℝ}
    (hα : ComputableReals.IsComputableReal α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsRE (fun p : ℚ × Option BitString × BitString =>
      (p.1 : ℝ) < exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α p.2.1 p.2.2) := by
  have h1 : ComputableReals.IsComputableReal (1 : ℝ) := by
    simpa using ComputableReals.isComputableReal_ratCast 1
  have hS1 := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc_exp hα hα0
  have hS2 :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc_exp (h1.sub hα) (sub_nonneg.2 hα1)
  have hpo : Primrec (fun p : ℚ × Option BitString × BitString => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hpy : Primrec (fun p : ℚ × Option BitString × BitString => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hpx : Primrec (fun p : ℚ × Option BitString × BitString => p.2.1.getD []) :=
    Primrec.option_getD.comp hpo (Primrec.const [])
  have hlx : Primrec (fun p : ℚ × Option BitString × BitString => (p.2.1.getD []).length) :=
    Primrec.list_length.comp hpx
  have hly : Primrec (fun p : ℚ × Option BitString × BitString => p.2.2.length) :=
    Primrec.list_length.comp hpy
  have hsome : Primrec (fun p : ℚ × Option BitString × BitString => p.2.1.isSome) :=
    Primrec.option_isSome.comp hpo
  have hyx : Primrec (fun p : ℚ × Option BitString × BitString =>
      decide (p.2.2 <+: p.2.1.getD [])) :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_prefix.comp hpy hpx
  have hxy : Primrec (fun p : ℚ × Option BitString × BitString =>
      decide (p.2.1.getD [] <+: p.2.2)) :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_prefix.comp hpx hpy
  have hneg : Primrec (fun p : ℚ × Option BitString × BitString => decide (p.1 < 0)) :=
    PrimrecPred.decide (ComputableReals.primrec_ratLt.comp Primrec.fst (Primrec.const 0))
  have hg1 : Computable (fun p : ℚ × Option BitString × BitString =>
      (p.1, (p.2.1.getD []).length - p.2.2.length)) :=
    (Primrec.fst.pair (Primrec.nat_sub.comp hlx hly)).to_comp
  have hg2 : Computable (fun p : ℚ × Option BitString × BitString =>
      (p.1, p.2.2.length - (p.2.1.getD []).length)) :=
    (Primrec.fst.pair (Primrec.nat_sub.comp hly hlx)).to_comp
  have hA : IsRE (fun p : ℚ × Option BitString × BitString =>
      (p.2.1.isSome && decide (p.2.2 <+: p.2.1.getD [])) = true ∧
        (p.1 : ℝ) < (2 : ℝ) ^ (-(α * (((p.2.1.getD []).length - p.2.2.length : ℕ) : ℝ)))) :=
    (hS1.comp_computable hg1).and_computable (Primrec.and.comp hsome hyx).to_comp
  have hB : IsRE (fun p : ℚ × Option BitString × BitString =>
      (p.2.1.isSome && (!decide (p.2.2 <+: p.2.1.getD []) &&
        decide (p.2.1.getD [] <+: p.2.2))) = true ∧
        (p.1 : ℝ) < (2 : ℝ) ^ (-((1 - α) * ((p.2.2.length - (p.2.1.getD []).length : ℕ) : ℝ)))) :=
    (hS2.comp_computable hg2).and_computable
      (Primrec.and.comp hsome (Primrec.and.comp (Primrec.not.comp hyx) hxy)).to_comp
  have hC : IsRE (fun p : ℚ × Option BitString × BitString =>
      ((!p.2.1.isSome || (!decide (p.2.2 <+: p.2.1.getD []) &&
        !decide (p.2.1.getD [] <+: p.2.2))) && decide (p.1 < 0)) = true) :=
    isRE_of_computable_bool _
      (fun p : ℚ × Option BitString × BitString =>
        (!p.2.1.isSome || (!decide (p.2.2 <+: p.2.1.getD []) &&
          !decide (p.2.1.getD [] <+: p.2.2))) && decide (p.1 < 0))
      (fun _ => Iff.rfl)
      (Primrec.and.comp
        (Primrec.or.comp (Primrec.not.comp hsome)
          (Primrec.and.comp (Primrec.not.comp hyx) (Primrec.not.comp hxy))) hneg).to_comp
  exact (hA.or (hB.or hC)).of_iff (fun p =>
    (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_iff α p.1 p.2.1 p.2.2).symm)

/-- Auxiliary bound for Step 3: an `α`-gale satisfies `m y ≤ 2^(α |y|) m(Λ)`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux1 {α : ℝ}
    {m : BitString → ℝ} (hm : IsGale α m) (y : BitString) :
    m y ≤ (2 : ℝ) ^ (α * (y.length : ℝ)) * m [] := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton y b ih =>
    have h := hm.gale y
    have h0 := hm.nonneg (y ++ [false])
    have h1 := hm.nonneg (y ++ [true])
    have hb : m (y ++ [b]) ≤ (2 : ℝ) ^ α * m y := by
      cases b <;> linarith
    have h2 : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
    calc m (y ++ [b]) ≤ (2 : ℝ) ^ α * m y := hb
      _ ≤ (2 : ℝ) ^ α * ((2 : ℝ) ^ (α * (y.length : ℝ)) * m []) :=
          mul_le_mul_of_nonneg_left ih h2.le
      _ = (2 : ℝ) ^ (α * ((y ++ [b]).length : ℝ)) * m [] := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
          congr 2
          simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
            Nat.cast_one]
          ring

/-- Step 3 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
infinite non-negative combinations of `α`-gales with summable initial capitals are `α`-gales
(use `g i y ≤ 2^(α |y|) g i []`). -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mix_gale
    {α : ℝ} (g : ℕ → BitString → ℝ) (c : ℕ → ℝ)
    (hg : ∀ i, IsGale α (g i)) (hc : ∀ i, 0 ≤ c i)
    (hsum : Summable (fun i => c i * g i [])) :
    (∀ y, Summable (fun i => c i * g i y)) ∧
    IsGale α (fun y => ∑' i, c i * g i y) := by
  have hsumm : ∀ y, Summable (fun i => c i * g i y) := by
    intro y
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hc i) ((hg i).nonneg y))
      (fun i => ?_) (hsum.mul_left ((2 : ℝ) ^ (α * (y.length : ℝ))))
    calc c i * g i y ≤ c i * ((2 : ℝ) ^ (α * (y.length : ℝ)) * g i []) :=
          mul_le_mul_of_nonneg_left
            (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux1 (hg i) y) (hc i)
      _ = (2 : ℝ) ^ (α * (y.length : ℝ)) * (c i * g i []) := by ring
  refine ⟨hsumm, ⟨?_, ?_⟩⟩
  · intro y
    exact tsum_nonneg (fun i => mul_nonneg (hc i) ((hg i).nonneg y))
  · intro y
    show (2 : ℝ) ^ α * ∑' i, c i * g i y =
      (∑' i, c i * g i (y ++ [false])) + ∑' i, c i * g i (y ++ [true])
    rw [← Summable.tsum_add (hsumm _) (hsumm _), ← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    have := (hg i).gale y
    calc (2 : ℝ) ^ α * (c i * g i y) = c i * ((2 : ℝ) ^ α * g i y) := by ring
      _ = c i * (g i (y ++ [false]) + g i (y ++ [true])) := by rw [this]
      _ = c i * g i (y ++ [false]) + c i * g i (y ++ [true]) := by ring

/-- Left fold of the witness test: the state is (all checks passed so far, partial sum, next
index). -/
private def exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run
    (chk : ℚ × ℕ × BitString → ℕ → Bool) (y : BitString) (s : ℕ) (l : List ℚ)
    (st : Bool × ℚ × ℕ) : Bool × ℚ × ℕ :=
  l.foldl (fun st q => (st.1 && chk (q, st.2.2, y) s, st.2.1 + q, st.2.2 + 1)) st

private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run_spec
    (chk : ℚ × ℕ × BitString → ℕ → Bool) (y : BitString) (s : ℕ) :
    ∀ (l : List ℚ) (st : Bool × ℚ × ℕ),
      ((exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk y s l st).1 = true ↔
        (st.1 = true ∧ ∀ j (hj : j < l.length), chk (l[j], st.2.2 + j, y) s = true)) ∧
      (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk y s l st).2.1 =
        st.2.1 + l.sum := by
  intro l
  induction l with
  | nil => intro st; simp [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run]
  | cons q t ih =>
    intro st
    have h := ih (st.1 && chk (q, st.2.2, y) s, st.2.1 + q, st.2.2 + 1)
    have e : exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk y s (q :: t) st =
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk y s t
          (st.1 && chk (q, st.2.2, y) s, st.2.1 + q, st.2.2 + 1) := rfl
    rw [e]
    refine ⟨h.1.trans ?_, by rw [h.2, List.sum_cons]; ring⟩
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun j hj => ?_⟩
      cases j with
      | zero => simpa using h2
      | succ j =>
        have := h3 j (by simpa using hj)
        simpa [add_assoc, add_comm, add_left_comm] using this
    · rintro ⟨h1, h3⟩
      have h30 := h3 0 (by simp)
      simp only [List.getElem_cons_zero, add_zero] at h30
      refine ⟨⟨h1, h30⟩, fun j hj => ?_⟩
      have := h3 (j + 1) (by simpa using hj)
      simpa [add_assoc, add_comm, add_left_comm] using this

/-- The Boolean test on a witness `(l, s)` for the pair `(r, y)`. -/
private def exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test
    (chk : ℚ × ℕ × BitString → ℕ → Bool) (a : (ℚ × BitString) × (List ℚ × ℕ)) : Bool :=
  (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk a.1.2 a.2.2 a.2.1
      (true, 0, 0)).1 &&
    decide (a.1.1 <
      (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk a.1.2 a.2.2 a.2.1
        (true, 0, 0)).2.1)

private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test_iff
    (chk : ℚ × ℕ × BitString → ℕ → Bool) (r : ℚ) (y : BitString) (l : List ℚ) (s : ℕ) :
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test chk ((r, y), (l, s)) = true ↔
      r < l.sum ∧ ∀ j (hj : j < l.length), chk (l[j], j, y) s = true := by
  have h := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run_spec chk y s l (true, 0, 0)
  unfold exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [h.1, h.2]
  simp only [true_and, zero_add]
  exact and_comm

private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test_computable
    (chk : ℚ × ℕ × BitString → ℕ → Bool) (hchk : Computable₂ chk) :
    Computable (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test chk) := by
  have hfold : Computable (fun a : (ℚ × BitString) × (List ℚ × ℕ) =>
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk a.1.2 a.2.2 a.2.1
        (true, 0, 0)) := by
    refine computable_list_foldl (f := fun a : (ℚ × BitString) × (List ℚ × ℕ) => a.2.1)
      (g := fun _ => ((true, 0, 0) : Bool × ℚ × ℕ))
      (h := fun a u => (u.1.1 && chk (u.2, u.1.2.2, a.1.2) a.2.2, u.1.2.1 + u.2, u.1.2.2 + 1))
      ?_ ?_ ?_
    · exact Computable.fst.comp Computable.snd
    · exact Computable.const _
    · have hst : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.1) := Computable.fst.comp Computable.snd
      have hb : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.2) := Computable.snd.comp Computable.snd
      have hy : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.1.1.2) := Computable.snd.comp (Computable.fst.comp Computable.fst)
      have hs : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.1.2.2) := Computable.snd.comp (Computable.snd.comp Computable.fst)
      have hok : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.1.1) := Computable.fst.comp hst
      have hsum : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.1.2.1) := Computable.fst.comp (Computable.snd.comp hst)
      have hidx : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.1.2.2) := Computable.snd.comp (Computable.snd.comp hst)
      have hchkterm : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) ×
          ((Bool × ℚ × ℕ) × ℚ) => chk (p.2.2, p.2.1.2.2, p.1.1.2) p.1.2.2) :=
        hchk.comp (hb.pair (hidx.pair hy)) hs
      have hand : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          (p.2.1.1 && chk (p.2.2, p.2.1.2.2, p.1.1.2) p.1.2.2)) :=
        Primrec.and.to_comp.comp hok hchkterm
      have hadd : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.1.2.1 + p.2.2) := computable₂_ratAdd.comp hsum hb
      have hsucc : Computable (fun p : ((ℚ × BitString) × (List ℚ × ℕ)) × ((Bool × ℚ × ℕ) × ℚ) =>
          p.2.1.2.2 + 1) := Primrec.succ.to_comp.comp hidx
      exact hand.pair (hadd.pair hsucc)
  have h1 : Computable (fun a : (ℚ × BitString) × (List ℚ × ℕ) =>
      (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk a.1.2 a.2.2 a.2.1
        (true, 0, 0)).1) := Computable.fst.comp hfold
  have h2 : Computable (fun a : (ℚ × BitString) × (List ℚ × ℕ) =>
      decide (a.1.1 < (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_run chk a.1.2 a.2.2
        a.2.1 (true, 0, 0)).2.1)) :=
    computable₂_ratLt.comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp (Computable.snd.comp hfold))
  exact Primrec.and.to_comp.comp h1 h2

private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_list_sum_le :
    ∀ (l : List ℚ) (g : ℕ → ℝ), (∀ j (hj : j < l.length), ((l[j] : ℚ) : ℝ) ≤ g j) →
      ((l.sum : ℚ) : ℝ) ≤ ∑ j ∈ Finset.range l.length, g j := by
  intro l
  induction l with
  | nil => intro g _; simp
  | cons q t ih =>
    intro g hg
    have h0 : ((q : ℚ) : ℝ) ≤ g 0 := by
      have := hg 0 (by simp)
      simpa only [List.getElem_cons_zero] using this
    have ht : ((t.sum : ℚ) : ℝ) ≤ ∑ j ∈ Finset.range t.length, g (j + 1) :=
      ih (fun j => g (j + 1)) (fun j hj => by
        have := hg (j + 1) (by simpa using hj)
        simpa only [List.getElem_cons_succ] using this)
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, Rat.cast_add]
    linarith

/-- Step 4 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
a pointwise summable series of non-negative uniformly lower semicomputable functions is lower
semicomputable.  (`q < ∑' f i y` iff for some `N` and rationals `q_i < f i y`, `i < N`, one has
`q < ∑ q_i`; use `IsRE.exists_stageApprox` and `IsRE.exists_encodable`.) -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc_tsum
    (f : ℕ → BitString → ℝ) (hf_nonneg : ∀ i y, 0 ≤ f i y)
    (hf_lsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < f p.2.1 p.2.2))
    (hf_sum : ∀ y, Summable (fun i => f i y)) :
    IsLowerSemicomputableOnStrings (fun y => ∑' i, f i y) := by
  obtain ⟨chk, hchk, hmono, hiff⟩ := hf_lsc.exists_stageApprox
  have hRE : IsRE (fun a : (ℚ × BitString) × (List ℚ × ℕ) =>
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test chk a = true) :=
    isRE_of_computable_bool _ _ (fun _ => Iff.rfl)
      (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test_computable chk hchk)
  have hEx : IsRE (fun p : ℚ × BitString => ∃ w : List ℚ × ℕ,
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test chk (p, w) = true) :=
    IsRE.exists_encodable (R := fun (p : ℚ × BitString) (w : List ℚ × ℕ) =>
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step4_test chk (p, w) = true) hRE
  refine IsRE.of_iff hEx ?_
  rintro ⟨r, y⟩
  dsimp only
  constructor
  · rintro ⟨⟨l, s⟩, hw⟩
    rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test_iff] at hw
    obtain ⟨hr, hall⟩ := hw
    have hlt : ∀ j (hj : j < l.length), ((l[j] : ℚ) : ℝ) ≤ f j y := fun j hj =>
      ((hiff (l[j], j, y)).mpr ⟨s, hall j hj⟩).le
    have h1 := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_list_sum_le l (fun j => f j y)
      hlt
    have h2 : ∑ j ∈ Finset.range l.length, f j y ≤ ∑' j, f j y :=
      (hf_sum y).sum_le_tsum _ (fun j _ => hf_nonneg j y)
    have h3 : (r : ℝ) < ((l.sum : ℚ) : ℝ) := by exact_mod_cast hr
    linarith
  · intro hr
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (r : ℝ) < ∑ i ∈ Finset.range N, f i y :=
      ((hf_sum y).hasSum.tendsto_sum_nat.eventually_const_lt hr).exists
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range N, f i y := ⟨_, rfl⟩
    rw [← hS] at hN
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (S - r) / ((N : ℝ) + 1) := ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; exact div_pos (by linarith) (by positivity)
    have hεN : ε * ((N : ℝ) + 1) = S - r := by rw [hε]; field_simp
    have hq : ∀ i : ℕ, ∃ q : ℚ, f i y - ε < (q : ℝ) ∧ (q : ℝ) < f i y :=
      fun i => exists_rat_btwn (by linarith)
    choose q hq1 hq2 using hq
    have hs : ∀ i : ℕ, ∃ s : ℕ, chk (q i, i, y) s = true :=
      fun i => (hiff (q i, i, y)).mp (hq2 i)
    choose s hs using hs
    have hsum : ∀ n : ℕ, (((List.range n).map q).sum : ℚ) = ∑ i ∈ Finset.range n, q i := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [List.range_succ, List.map_append, List.sum_append, ihn, Finset.sum_range_succ]
        simp
    refine ⟨((List.range N).map q, (Finset.range N).sup s), ?_⟩
    rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_test_iff]
    refine ⟨?_, ?_⟩
    · rw [hsum N]
      have hle : ∑ i ∈ Finset.range N, (f i y - ε) ≤ ∑ i ∈ Finset.range N, (q i : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hq1 i).le)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hS] at hle
      have : (r : ℝ) < ((∑ i ∈ Finset.range N, q i : ℚ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast this
    · intro j hj
      have hjN : j < N := by simpa using hj
      simp only [List.getElem_map, List.getElem_range]
      exact hmono _ _ _ (Finset.le_sup (Finset.mem_range.mpr hjN)) (hs j)
/-- Step 5 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
extract a computable sequence of covers `J k` of `A` with total `α`-mass `< 2^{-(k+1)}` from the
enumerator of an effectively `α`-null set (take `ε = 2^{-(k+1)}`; the rational `ε` is computable
from `k` by `computable_of_num_den`). -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_extract
    {α : ℝ} {A : Set CantorSeq} (hA : IsEffectiveAlphaNull α A) :
    ∃ J : ℕ → ℕ → Option BitString, Computable₂ J ∧
      (∀ k, A ⊆ ⋃ n, (J k n).elim ∅ cantorCylinder) ∧
      ∀ k, (∑' n, coverAlphaMass α (J k n)) < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (k + 1)) := by
  obtain ⟨I, hI_comp, hI⟩ := hA
  have hε : Computable (fun k : ℕ => ((1 : ℚ) / 2) ^ (k + 1)) := by
    have hD : Computable (fun k : ℕ => 2 ^ (k + 1)) := comp_pow.comp Primrec.succ.to_comp
    refine computable_of_num_den (N := fun _ => (1 : ℤ)) (D := fun k => 2 ^ (k + 1))
      (Computable.const 1) hD (fun k => by positivity) (fun k => ?_)
    push_cast
    rw [one_div_pow]
  have hεpos : ∀ k : ℕ, (0 : ℚ) < ((1 : ℚ) / 2) ^ (k + 1) := fun k => by positivity
  refine ⟨fun k n => I (((1 : ℚ) / 2) ^ (k + 1)) n, ?_, fun k => (hI _ (hεpos k)).1, fun k => ?_⟩
  · exact Computable₂.comp hI_comp (hε.comp Computable.fst) Computable.snd
  · have hcast : ((((1 : ℚ) / 2) ^ (k + 1) : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ (k + 1) := by
      push_cast
      rw [one_div]
    rw [← hcast]
    exact (hI _ (hεpos k)).2

/-- Auxiliary for Step 6: `∑_{k ≥ 0} (k+1)/2 * 2^{-(k+1)} = 1`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step6_aux1 :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) / 2 * (2 : ℝ)⁻¹ ^ (k + 1)) 1 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (2 : ℝ)⁻¹)
    (by rw [norm_inv, Real.norm_ofNat]; norm_num)
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  have h3 := h2.mul_left (1 / 2 : ℝ)
  convert h3 using 1
  · ext k
    push_cast
    ring
  · norm_num [Finset.sum_range_one]

/-- Step 6 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
the total initial capital of the weighted family `((k+1)/2) * g (J k n)` is summable and at most
`1`, since `∑_k (k+1)/2 * 2^{-(k+1)} = 1`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mass
    {α : ℝ} (J : ℕ → ℕ → Option BitString)
    (hJ_mass : ∀ k, (∑' n, coverAlphaMass α (J k n)) < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (k + 1)))
    (g : Option BitString → BitString → ℝ)
    (hg_init : ∀ o, g o [] = (coverAlphaMass α o).toReal) :
    Summable (fun i : ℕ => ((i.unpair.1 + 1 : ℝ) / 2) * g (J i.unpair.1 i.unpair.2) []) ∧
    (∑' i : ℕ, ((i.unpair.1 + 1 : ℝ) / 2) * g (J i.unpair.1 i.unpair.2) []) ≤ 1 := by
  have hgeom := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step6_aux1
  obtain ⟨F, hF⟩ : ∃ F : ℕ × ℕ → ENNReal,
      ∀ p, F p = ENNReal.ofReal (((p.1 : ℝ) + 1) / 2) * coverAlphaMass α (J p.1 p.2) :=
    ⟨_, fun _ => rfl⟩
  have hterm : ∀ i : ℕ, ((i.unpair.1 + 1 : ℝ) / 2) * g (J i.unpair.1 i.unpair.2) [] =
      (F i.unpair).toReal := by
    intro i
    rw [hg_init, hF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hS : ∑' i : ℕ, F i.unpair ≤ 1 := by
    calc ∑' i : ℕ, F i.unpair = ∑' p : ℕ × ℕ, F p := Nat.pairEquiv.symm.tsum_eq F
      _ = ∑' k : ℕ, ∑' n : ℕ, F (k, n) := ENNReal.tsum_prod'
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 1) / 2 * (2 : ℝ)⁻¹ ^ (k + 1)) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          calc ∑' n : ℕ, F (k, n)
              = ∑' n : ℕ, ENNReal.ofReal (((k : ℝ) + 1) / 2) * coverAlphaMass α (J k n) :=
                tsum_congr (fun n => hF (k, n))
            _ = ENNReal.ofReal (((k : ℝ) + 1) / 2) * ∑' n : ℕ, coverAlphaMass α (J k n) :=
                ENNReal.tsum_mul_left
            _ ≤ ENNReal.ofReal (((k : ℝ) + 1) / 2) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (k + 1)) :=
                mul_le_mul' le_rfl (hJ_mass k).le
            _ = ENNReal.ofReal (((k : ℝ) + 1) / 2 * (2 : ℝ)⁻¹ ^ (k + 1)) :=
                (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (∑' k : ℕ, ((k : ℝ) + 1) / 2 * (2 : ℝ)⁻¹ ^ (k + 1)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom.summable).symm
      _ = 1 := by rw [hgeom.tsum_eq]; simp
  have hS_ne : ∑' i : ℕ, F i.unpair ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hS
  have hF_ne : ∀ i : ℕ, F i.unpair ≠ ⊤ := fun i => ENNReal.ne_top_of_tsum_ne_top hS_ne i
  simp_rw [hterm]
  refine ⟨ENNReal.summable_toReal hS_ne, ?_⟩
  rw [← ENNReal.tsum_toReal_eq (f := fun i : ℕ => F i.unpair) hF_ne]
  have h := ENNReal.toReal_mono ENNReal.one_ne_top hS
  simpa using h

/-- Auxiliary identity for Step 7: `2 q / (k + 1) = (2 num q) / (den q * (k + 1))`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_div (q : ℚ) (k : ℕ) :
    2 * q / ((k : ℚ) + 1) = ((2 * q.num : ℤ) : ℚ) / ((q.den * (k + 1) : ℕ) : ℚ) := by
  have hq : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  rw [hq]
  field_simp

/-- Auxiliary computability for Step 7: the rescaled threshold `2 r / (k + 1)` where
`k = (Nat.unpair i).1` is computable from `(r, i, y)`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_comp :
    Computable (fun p : ℚ × ℕ × BitString => 2 * p.1 / ((p.2.1.unpair.1 : ℚ) + 1)) := by
  have hk : Computable (fun p : ℚ × ℕ × BitString => p.2.1.unpair.1) :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd))
  have hN : Computable (fun p : ℚ × ℕ × BitString => 2 * p.1.num) :=
    Computable₂.comp primrec_intMul.to_comp (Computable.const (2 : ℤ))
      (computable_ratNum.comp Computable.fst)
  have hD : Computable (fun p : ℚ × ℕ × BitString => p.1.den * (p.2.1.unpair.1 + 1)) :=
    Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp Computable.fst)
      (Primrec.succ.to_comp.comp hk)
  refine computable_of_num_den (N := fun p : ℚ × ℕ × BitString => 2 * p.1.num)
    (D := fun p : ℚ × ℕ × BitString => p.1.den * (p.2.1.unpair.1 + 1)) hN hD
    (fun p => Nat.mul_pos p.1.den_pos (Nat.succ_pos _)) ?_
  intro p
  exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_div p.1 p.2.1.unpair.1

/-- Step 7 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
the rescaled elementary gales `((k+1)/2) * g (J k n)` (indexed by `i = Nat.pair k n`) are uniformly
lower semicomputable (`r < ((k+1)/2) * s` iff `2 r/(k+1) < s`; the rational `2 r/(k+1)` is
computable from `(r, k)` by `computable_of_num_den`). -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step7_lsc
    (J : ℕ → ℕ → Option BitString) (hJ_comp : Computable₂ J)
    (g : Option BitString → BitString → ℝ)
    (hg_lsc : IsRE (fun p : ℚ × Option BitString × BitString => (p.1 : ℝ) < g p.2.1 p.2.2)) :
    IsRE (fun p : ℚ × ℕ × BitString =>
      (p.1 : ℝ) < ((p.2.1.unpair.1 + 1 : ℝ) / 2) * g (J p.2.1.unpair.1 p.2.1.unpair.2) p.2.2) := by
  have hu : Computable (fun p : ℚ × ℕ × BitString => p.2.1.unpair) :=
    Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)
  have hJ' : Computable (fun p : ℚ × ℕ × BitString => J p.2.1.unpair.1 p.2.1.unpair.2) :=
    Computable₂.comp hJ_comp (Computable.fst.comp hu) (Computable.snd.comp hu)
  have hG : Computable (fun p : ℚ × ℕ × BitString =>
      ((2 * p.1 / ((p.2.1.unpair.1 : ℚ) + 1) : ℚ), J p.2.1.unpair.1 p.2.1.unpair.2, p.2.2)) :=
    Computable.pair exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_comp
      (Computable.pair hJ' (Computable.snd.comp Computable.snd))
  refine (hg_lsc.comp_computable hG).of_iff (fun p => ?_)
  have hk : (0 : ℝ) < (p.2.1.unpair.1 : ℝ) + 1 := by positivity
  push_cast
  rw [div_lt_iff₀ hk]
  constructor <;> intro h <;> nlinarith

/-- Step 8 of the proof of `exists_lsc_isGale_wins_of_isEffectiveAlphaNull`:
the mixed capital wins on `A`: if `w ∈ A` and `k` is large, some `J k n` is a prefix `x` of `w`,
and the `(k, n)`-th term of the series is `((k+1)/2) * g (some x) x = (k+1)/2`. -/
private lemma exists_lsc_isGale_wins_of_isEffectiveAlphaNull_wins
    {A : Set CantorSeq}
    (J : ℕ → ℕ → Option BitString)
    (hJ_cov : ∀ k, A ⊆ ⋃ n, (J k n).elim ∅ cantorCylinder)
    (g : Option BitString → BitString → ℝ)
    (hg_self : ∀ x, g (some x) x = 1)
    (hg_nonneg : ∀ o x, 0 ≤ g o x)
    (hg_sum : ∀ y, Summable
      (fun i : ℕ => ((i.unpair.1 + 1 : ℝ) / 2) * g (J i.unpair.1 i.unpair.2) y))
    (m : BitString → ℝ)
    (hm_eq : ∀ y, m y = ∑' i : ℕ, ((i.unpair.1 + 1 : ℝ) / 2) * g (J i.unpair.1 i.unpair.2) y) :
    ∀ w ∈ A, Wins m w := by
  intro w hw
  simp only [Wins, not_bddAbove_iff]
  intro M
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M)
  have hcov := hJ_cov k hw
  rw [Set.mem_iUnion] at hcov
  obtain ⟨n, hn⟩ := hcov
  cases hJ : J k n with
  | none =>
    rw [hJ] at hn
    simp at hn
  | some x =>
    rw [hJ] at hn
    have hn' : w ∈ cantorCylinder x := hn
    have hpre : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hn'
    refine ⟨m x, ⟨x.length, ?_⟩, ?_⟩
    · change m (cantorPrefix w x.length) = m x
      rw [hpre]
    rw [hm_eq x]
    have h1 : ((((Nat.pair k n).unpair.1 : ℕ) + 1 : ℝ) / 2) *
        g (J (Nat.pair k n).unpair.1 (Nat.pair k n).unpair.2) x ≤
        ∑' i : ℕ, ((i.unpair.1 + 1 : ℝ) / 2) * g (J i.unpair.1 i.unpair.2) x :=
      (hg_sum x).le_tsum (Nat.pair k n)
        (fun j _ => mul_nonneg (by positivity) (hg_nonneg _ _))
    rw [Nat.unpair_pair, hJ, hg_self x] at h1
    simp only at h1
    linarith

/-- **SUV Theorem 185, p. 286.**  For computable `α ∈ (0, 1]` and an effectively `α`-null set `A`
there is a lower semicomputable `α`-gale with `m(Λ) ≤ 1`, unbounded on the prefixes of every
`ω ∈ A`.  The normalisation `m(Λ) ≤ 1` is the book's convention for the effective case, p. 285. -/
theorem exists_lsc_isGale_wins_of_isEffectiveAlphaNull {α : ℝ}
    (hαc : ComputableReals.IsComputableReal α) (hα0 : 0 < α) (hα1 : α ≤ 1) {A : Set CantorSeq}
    (hA : IsEffectiveAlphaNull α A) :
    ∃ m, IsGale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧ ∀ w ∈ A, Wins m w := by
  obtain ⟨J, hJ_comp, hJ_cov, hJ_mass⟩ :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_extract hA
  let g := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale α
  have hg_gale : ∀ o, IsGale α (g o) :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_gale α
  obtain ⟨hg_self, hg_init⟩ := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_self_init α
  have hg_lsc : IsRE (fun p : ℚ × Option BitString × BitString => (p.1 : ℝ) < g p.2.1 p.2.2) :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc hαc hα0.le hα1
  let c (i : ℕ) : ℝ := (i.unpair.1 + 1 : ℝ) / 2
  have hc_nonneg (i : ℕ) : 0 ≤ c i := by positivity
  let f (i : ℕ) (y : BitString) : ℝ := c i * g (J i.unpair.1 i.unpair.2) y
  have hf_nonneg (i : ℕ) (y : BitString) : 0 ≤ f i y :=
    mul_nonneg (hc_nonneg i) ((hg_gale (J i.unpair.1 i.unpair.2)).nonneg y)
  obtain ⟨hsum_init, h_init_le⟩ :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mass J hJ_mass g hg_init
  obtain ⟨hsum_all, hm_gale⟩ :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mix_gale
      (fun i => g (J i.unpair.1 i.unpair.2)) c (fun i => hg_gale _) hc_nonneg hsum_init
  have hf_lsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < f p.2.1 p.2.2) :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step7_lsc J hJ_comp g hg_lsc
  have hm_lsc : IsLowerSemicomputableOnStrings (fun y => ∑' i, f i y) :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc_tsum f hf_nonneg hf_lsc hsum_all
  have hm_wins : ∀ w ∈ A, Wins (fun y => ∑' i, f i y) w :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_wins J hJ_cov g hg_self
      (fun o x => (hg_gale o).nonneg x) hsum_all (fun y => ∑' i, f i y) (fun _ => rfl)
  exact ⟨fun y => ∑' i, f i y, hm_gale, hm_lsc, h_init_le, hm_wins⟩

/-- Step 1 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
realize the profile `K(w↾n) = ⌊n/2⌋ + O(1)` using the prefix-complexity profile theorem.
Both bounds belong to the contract: the upper bound supplies the enumerable tree, while the
lower bound will exclude effective half-nullity. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_profile
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ (w : CantorSeq) (c : ℕ), ∀ n : ℕ,
      KPPlain U (cantorPrefix w n) ≤ ((n / 2 + c : ℕ) : ℕ∞) ∧
        ((n / 2 : ℕ) : ℕ∞) ≤ KPPlain U (cantorPrefix w n) + (c : ℕ∞) := by
  apply Applications.exists_seq_KP_profile U hU (fun n => n / 2)
    (eps := (1 / 4 : ℝ)) (by norm_num) 4
  · intro n h hh
    have hnat : 4 * (n / 2) + h ≤ 4 * ((n + h) / 2) := by omega
    have hr : 4 * ((n / 2 : ℕ) : ℝ) + (h : ℝ) ≤
        4 * (((n + h) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  · intro n h hh
    have hnat : 4 * ((n + h) / 2) ≤ 4 * (n / 2) + 3 * h := by omega
    have hr : 4 * (((n + h) / 2 : ℕ) : ℝ) ≤
        4 * ((n / 2 : ℕ) : ℝ) + 3 * (h : ℝ) := by exact_mod_cast hnat
    linarith

/-- Step 2 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
the lower half of the profile prevents effective half-nullity, by the prefix-complexity
criterion for effective null sets. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_not_null
    (U : Map) (hU : IsOptimalPrefixConditional U) (w : CantorSeq) (c : ℕ)
    (hlow : ∀ n : ℕ, ((n / 2 : ℕ) : ℕ∞) ≤
      KPPlain U (cantorPrefix w n) + (c : ℕ∞)) :
    ¬ IsEffectiveAlphaNull (1 / 2 : ℝ) {w} := by
  intro hnull
  have hnull' : IsEffectiveAlphaNull ((1 / 2 : ℚ) : ℝ) {w} := by
    norm_num
    exact hnull
  obtain ⟨n, hn⟩ := exists_lt_alpha_mul_sub_KPPlain_of_isEffectiveAlphaNull U hU
    (1 / 2 : ℚ) (by norm_num) hnull' ((c : ℝ) + 1)
  have hK := KPPlain_ne_top_of_isOptimalPrefixConditional hU (cantorPrefix w n)
  have hlow' : n / 2 ≤ (KPPlain U (cantorPrefix w n)).toNat + c := by
    have h := hlow n
    rw [← ENat.natCast_toNat hK, ← Nat.cast_add] at h
    exact_mod_cast h
  have hreal : ((n / 2 : ℕ) : ℝ) ≤
      ((KPPlain U (cantorPrefix w n)).toNat : ℝ) + (c : ℝ) := by
    exact_mod_cast hlow'
  have hnlt : n < 2 * (n / 2 + 1) := by omega
  have hnreal : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by exact_mod_cast hnlt
  rw [show ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) by norm_num] at hn
  linarith

/-- Step 3 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
the strings whose prefix complexity is at most `⌊|x|/2⌋ + c` form an enumerable set. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_low_re
    (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ) :
    IsRE (fun x : BitString => KPPlain U x ≤ ((x.length / 2 + c : ℕ) : ℕ∞)) := by
  have hb : Computable (fun x : BitString => (x, x.length / 2 + c + 1)) :=
    Computable.id.pair
      (Primrec.succ.comp (Primrec.nat_add.comp
        (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))
        (Primrec.const c))).to_comp
  refine ((isRE_KPPlain_lt hU.isDecompressor).comp_computable hb).of_iff fun x => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  exact ENat.lt_add_one_iff (by simp)

/-- Step 4 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
Kraft's inequality bounds the sum of `2⁻⌊|x|/2⌋` over any finite set of low-complexity
strings by `2^c`.  The bound counts strings at all lengths together. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_kraft_bound
    (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ) (T : Finset BitString)
    (hT : ∀ x ∈ T, KPPlain U x ≤ ((x.length / 2 + c : ℕ) : ℕ∞)) :
    ∑ x ∈ T, (2 : ℝ)⁻¹ ^ (x.length / 2) ≤ (2 : ℝ) ^ c := by
  have hsum : ∑ x ∈ T, complexityWeight (KPPlain U x) ≤ 1 :=
    (ENNReal.sum_le_tsum T).trans (KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor)
  have hsumR : ∑ x ∈ T, (complexityWeight (KPPlain U x)).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hsum
    rw [ENNReal.toReal_sum (fun x _ => complexityWeight_ne_top _)] at h
    simpa using h
  have hterm : ∀ x ∈ T, (2 : ℝ)⁻¹ ^ (x.length / 2) ≤
      (2 : ℝ) ^ c * (complexityWeight (KPPlain U x)).toReal := by
    intro x hx
    have h := ENNReal.toReal_mono (complexityWeight_ne_top _)
      (complexityWeight_le_of_le (hT x hx))
    simp only [complexityWeight_coe, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat] at h
    have heq : (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ (x.length / 2 + c) =
        (2 : ℝ)⁻¹ ^ (x.length / 2) := by
      rw [pow_add, mul_left_comm, ← mul_pow]
      norm_num
    exact heq ▸ mul_le_mul_of_nonneg_left h (by positivity)
  calc ∑ x ∈ T, (2 : ℝ)⁻¹ ^ (x.length / 2)
      ≤ ∑ x ∈ T, (2 : ℝ) ^ c * (complexityWeight (KPPlain U x)).toReal :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ c * ∑ x ∈ T, (complexityWeight (KPPlain U x)).toReal :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ c := by
      simpa using mul_le_mul_of_nonneg_left hsumR (show (0 : ℝ) ≤ 2 ^ c by positivity)

/-- Step 5 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
uniform finite greedy packing in an enumerable tree.  At horizon `2 L(i)`, accept a leaf
only while every prefix `x` has fewer than `2^(L(i) - ⌊|x|/2⌋)` accepted extensions.  The
accepted leaves remain enumerable, every prefix obeys its capacity, and every eligible leaf
has a saturated prefix.  The conclusion applies also to empty trees and to horizon zero. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_greedy
    (P : BitString → Prop) (hP : IsRE P) (L : ℕ → ℕ) (hL : Computable L) :
    ∃ S : ℕ → Finset BitString,
      IsRE (fun p : ℕ × BitString => p.2 ∈ S p.1) ∧
      (∀ (i : ℕ) (x : BitString), x ∈ S i →
        x.length = 2 * L i ∧ ∀ n ≤ x.length, P (x.take n)) ∧
      (∀ (i : ℕ) (x : BitString), x.length ≤ 2 * L i →
        ((S i).filter (fun y => x <+: y)).card ≤ 2 ^ (L i - x.length / 2)) ∧
      (∀ (i : ℕ) (x : BitString), x.length = 2 * L i →
        (∀ n ≤ x.length, P (x.take n)) →
        ∃ n ≤ x.length,
          ((S i).filter (fun y => x.take n <+: y)).card = 2 ^ (L i - n / 2)) := by
  classical
  obtain ⟨chk, hchk, hmono, hchkP⟩ := hP.exists_stageApprox
  let ready (x : BitString) (s : ℕ) : Bool :=
    !((List.range (x.length + 1)).any (fun n => !(chk (x.take n) s)))
  have hready : Computable₂ ready := by
    apply Primrec.not.to_comp.comp
    apply computable_list_any
    · exact Primrec.list_range.to_comp.comp
        (Primrec.succ.to_comp.comp (Primrec.list_length.to_comp.comp Computable.fst))
    · exact Primrec.not.to_comp.comp (hchk.comp
        (Primrec.list_take.to_comp.comp Computable.snd
          (Computable.fst.comp Computable.fst))
        (Computable.snd.comp Computable.fst))
  have hready_iff (x : BitString) (s : ℕ) : ready x s = true ↔
      ∀ n ≤ x.length, chk (x.take n) s = true := by
    simp [ready, List.any_eq_false]
  have hready_sound (x : BitString) (s : ℕ) (h : ready x s = true) :
      ∀ n ≤ x.length, P (x.take n) := by
    intro n hn
    exact (hchkP _).mpr ⟨s, (hready_iff x s).mp h n hn⟩
  have hready_complete (x : BitString) (h : ∀ n ≤ x.length, P (x.take n)) :
      ∃ s, ready x s = true := by
    have h : ∀ n : Fin (x.length + 1), ∃ s, chk (x.take n.val) s = true :=
      fun n => (hchkP _).mp (h n.val (by omega))
    choose s hs using h
    refine ⟨Finset.univ.sup s, (hready_iff x _).mpr ?_⟩
    intro n hn
    let j : Fin (x.length + 1) := ⟨n, by omega⟩
    exact hmono _ (s j) _ (Finset.le_sup (Finset.mem_univ j)) (hs j)
  let count (A : List BitString) (x : BitString) : ℕ :=
    (A.filter (fun y => decide (x <+: y))).length
  have hcount : Computable₂ count := by
    apply Primrec.list_length.to_comp.comp
    apply computable_list_filter Computable.fst
    exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull_aux_prefix.to_comp.comp
      (Computable.snd.comp Computable.fst) Computable.snd
  let good (d : ℕ) (A : List BitString) (x : BitString) : Bool :=
    !((List.range (x.length + 1)).any
      (fun n => decide (2 ^ (d - n / 2) ≤ count A (x.take n))))
  have hgood : Computable (fun p : ℕ × List BitString × BitString => good p.1 p.2.1 p.2.2) := by
    apply Primrec.not.to_comp.comp
    apply computable_list_any
    · exact Primrec.list_range.to_comp.comp (Primrec.succ.to_comp.comp
        (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.snd)))
    · have hd : Computable (fun p : (ℕ × List BitString × BitString) × ℕ => p.1.1) :=
        Computable.fst.comp Computable.fst
      have hA : Computable (fun p : (ℕ × List BitString × BitString) × ℕ => p.1.2.1) :=
        Computable.fst.comp (Computable.snd.comp Computable.fst)
      have hx : Computable (fun p : (ℕ × List BitString × BitString) × ℕ => p.1.2.2) :=
        Computable.snd.comp (Computable.snd.comp Computable.fst)
      exact Primrec.nat_le.decide.to_comp.comp
        (comp_pow.comp (Primrec.nat_sub.to_comp.comp hd
          (Primrec.nat_div.to_comp.comp Computable.snd (Computable.const 2))))
        (hcount.comp hA (Primrec.list_take.to_comp.comp Computable.snd hx))
  have hgood_iff (d : ℕ) (A : List BitString) (x : BitString) :
      good d A x = true ↔ ∀ n ≤ x.length, count A (x.take n) < 2 ^ (d - n / 2) := by
    simp [good, List.any_eq_false]
  let leaf (s : ℕ) : BitString := natToBitString s.unpair.1
  let accept (i s : ℕ) (A : List BitString) : Bool :=
    decide ((leaf s).length = 2 * L i) && ready (leaf s) s.unpair.2 && good (L i) A (leaf s)
  have haccept : Computable (fun p : ℕ × ℕ × List BitString => accept p.1 p.2.1 p.2.2) := by
    have hi : Computable (fun p : ℕ × ℕ × List BitString => L p.1) := hL.comp Computable.fst
    have hu : Computable (fun p : ℕ × ℕ × List BitString => p.2.1.unpair) :=
      Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)
    have hx : Computable (fun p : ℕ × ℕ × List BitString => leaf p.2.1) :=
      computable_natToBitString.comp (Computable.fst.comp hu)
    have heq : Computable (fun p : ℕ × ℕ × List BitString =>
        decide ((leaf p.2.1).length = 2 * L p.1)) :=
      primrec_decideEq.to_comp.comp (Primrec.list_length.to_comp.comp hx)
        (Primrec.nat_mul.to_comp.comp (Computable.const 2) hi)
    have hr : Computable (fun p : ℕ × ℕ × List BitString => ready (leaf p.2.1) p.2.1.unpair.2) :=
      hready.comp hx (Computable.snd.comp hu)
    have hA : Computable (fun p : ℕ × ℕ × List BitString => p.2.2) :=
      Computable.snd.comp Computable.snd
    have hg : Computable (fun p : ℕ × ℕ × List BitString => good (L p.1) p.2.2 (leaf p.2.1)) := by
      have h := Computable.comp hgood (hi.pair (hA.pair hx))
      exact h
    exact Primrec.and.to_comp.comp (Primrec.and.to_comp.comp heq hr) hg
  let run (i t : ℕ) : List BitString := Nat.rec []
    (fun s A => bif accept i s A then leaf s :: A else A) t
  have hrun0 (i : ℕ) : run i 0 = [] := rfl
  have hrunsucc (i s : ℕ) : run i (s + 1) =
      (bif accept i s (run i s) then leaf s :: run i s else run i s) := rfl
  have hrun : Computable₂ run := by
    refine Computable.nat_rec (f := fun p : ℕ × ℕ => p.2)
      (g := fun _ => ([] : List BitString))
      (h := fun p u => bif accept p.1 u.1 u.2 then leaf u.1 :: u.2 else u.2)
      Computable.snd (Computable.const []) ?_
    have hi : Computable (fun p : (ℕ × ℕ) × (ℕ × List BitString) => p.1.1) :=
      Computable.fst.comp Computable.fst
    have hs : Computable (fun p : (ℕ × ℕ) × (ℕ × List BitString) => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hA : Computable (fun p : (ℕ × ℕ) × (ℕ × List BitString) => p.2.2) :=
      Computable.snd.comp Computable.snd
    have ha := Computable.comp haccept (hi.pair (hs.pair hA))
    exact Computable.cond ha
      (Computable.list_cons.comp
        (computable_natToBitString.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp hs))) hA)
            hA
  have haccept_iff (i s : ℕ) (A : List BitString) : accept i s A = true ↔
      (leaf s).length = 2 * L i ∧ ready (leaf s) s.unpair.2 = true ∧
        ∀ n ≤ (leaf s).length, count A ((leaf s).take n) < 2 ^ (L i - n / 2) := by
    simp only [accept, Bool.and_eq_true, decide_eq_true_eq, hgood_iff, and_assoc]
  have hrun_inv (i t : ℕ) :
      (run i t).Nodup ∧
      (∀ x ∈ run i t, x.length = 2 * L i ∧ ∀ n ≤ x.length, P (x.take n)) ∧
      (∀ x : BitString, x.length ≤ 2 * L i → count (run i t) x ≤ 2 ^ (L i - x.length / 2)) := by
    induction t with
    | zero => simp [hrun0, count]
    | succ t ih =>
      rw [hrunsucc]
      cases ha : accept i t (run i t) with
      | false => simpa only [Bool.cond_false] using ih
      | true =>
        simp only [Bool.cond_true]
        obtain ⟨hlen, hreadyt, hgoodt⟩ := (haccept_iff i t _).mp ha
        have hnotmem : leaf t ∉ run i t := by
          intro hx
          have hc := hgoodt (leaf t).length le_rfl
          rw [List.take_length] at hc
          simp only [hlen, Nat.mul_div_right _ (by decide : 0 < 2),
            Nat.sub_self, pow_zero] at hc
          have hm : leaf t ∈ (run i t).filter (fun y => decide (leaf t <+: y)) := by
            simp [hx]
          have hp := List.length_pos_of_mem hm
          dsimp [count] at hc
          exact (Nat.not_lt_of_ge hp) hc
        refine ⟨List.nodup_cons.mpr ⟨hnotmem, ih.1⟩, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hlen, hready_sound _ _ hreadyt⟩
          · exact ih.2.1 x hx
        · intro x hx
          by_cases hpre : x <+: leaf t
          · have htake : (leaf t).take x.length = x := (List.prefix_iff_eq_take.mp hpre).symm
            have hc := hgoodt x.length hpre.length_le
            rw [htake] at hc
            simp only [count, List.filter_cons, decide_eq_true_eq, hpre, ite_true,
              List.length_cons]
            exact hc
          · simpa [count, hpre] using ih.2.2 x hx
  have hmono_run (i : ℕ) : Monotone (fun t => (run i t).toFinset) := by
    apply monotone_nat_of_le_succ
    intro t x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [hrunsucc]
    cases accept i t (run i t) <;> simp_all
  let S (i : ℕ) : Finset BitString :=
    @Finset.filter BitString (fun x => ∃ t, x ∈ run i t)
      (fun _ => Classical.propDecidable _) (stringsOfLength (2 * L i))
  have hSmem (i : ℕ) (x : BitString) : x ∈ S i ↔ ∃ t, x ∈ run i t := by
    simp only [S, Finset.mem_filter, mem_stringsOfLength]
    exact ⟨And.right, fun h => ⟨by obtain ⟨t, ht⟩ := h; exact (hrun_inv i t).2.1 x ht |>.1, h⟩⟩
  have hsubset (i t : ℕ) : (run i t).toFinset ⊆ S i := by
    intro x hx
    exact (hSmem i x).mpr ⟨t, List.mem_toFinset.mp hx⟩
  have hstable (i : ℕ) : ∃ t, (run i t).toFinset = S i := by
    have h : ∀ x ∈ S i, ∃ t, x ∈ run i t := fun x hx => (hSmem i x).mp hx
    choose t ht using h
    let f : BitString → ℕ := fun x => if hx : x ∈ S i then t x hx else 0
    refine ⟨(S i).sup f, Finset.Subset.antisymm (hsubset i _) ?_⟩
    intro x hx
    have hle : t x hx ≤ (S i).sup f := by
      simpa only [f, dite_eq_left hx] using (Finset.le_sup (f := f) hx)
    exact hmono_run i hle (List.mem_toFinset.mpr (ht x hx))
  have hcard (i t : ℕ) (x : BitString) :
      (((run i t).toFinset).filter (fun y => x <+: y)).card = count (run i t) x := by
    dsimp only [count]
    rw [← List.toFinset_card_of_nodup ((hrun_inv i t).1.filter (fun y => decide (x <+: y)))]
    simp [List.toFinset_filter]
  have hScap (i : ℕ) (x : BitString) (hx : x.length ≤ 2 * L i) :
      ((S i).filter (fun y => x <+: y)).card ≤ 2 ^ (L i - x.length / 2) := by
    obtain ⟨t, ht⟩ := hstable i
    rw [← ht, hcard]
    exact (hrun_inv i t).2.2 x hx
  refine ⟨S, ?_, ?_, hScap, ?_⟩
  · have hc : Computable (fun p : (ℕ × BitString) × ℕ =>
        (run p.1.1 p.2).any (fun y => decide (p.1.2 = y))) := by
      apply computable_list_any
        (hrun.comp (Computable.fst.comp Computable.fst) Computable.snd)
      exact primrec_decideEq.to_comp.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd
    have hre : IsRE (fun p : (ℕ × BitString) × ℕ => p.1.2 ∈ run p.1.1 p.2) :=
      isRE_of_computable_bool _ _ (fun p => by simp [List.any_eq_true]) hc
    exact (IsRE.exists_encodable hre).of_iff
      (fun p => (hSmem p.1 p.2).symm)
  · intro i x hx
    obtain ⟨t, ht⟩ := (hSmem i x).mp hx
    exact (hrun_inv i t).2.1 x ht
  · intro i x hlen hPall
    obtain ⟨s, hs⟩ := hready_complete x hPall
    let t := Nat.pair (bitStringToNat x) s
    have hleaf : leaf t = x := by simp [leaf, t]
    have hstage : t.unpair.2 = s := by simp [t]
    by_cases ha : accept i t (run i t) = true
    · have hx : x ∈ S i := by
        apply (hSmem i x).mpr
        refine ⟨t + 1, ?_⟩
        simp [hrunsucc, ha, hleaf]
      refine ⟨x.length, le_rfl, ?_⟩
      simp only [List.take_length]
      have hbound := hScap i x hlen.le
      have hpos : 0 < ((S i).filter (fun y => x <+: y)).card :=
        Finset.card_pos.mpr ⟨x, by simp [hx]⟩
      have hcapone : 2 ^ (L i - x.length / 2) = 1 := by simp [hlen]
      omega
    · have hbad : ¬ ∀ n ≤ x.length, count (run i t) (x.take n) < 2 ^ (L i - n / 2) := by
        intro h
        apply ha
        apply (haccept_iff i t _).mpr
        simpa only [hleaf, hstage] using And.intro hlen (And.intro hs h)
      push Not at hbad
      obtain ⟨n, hn, hcountge⟩ := hbad
      refine ⟨n, hn, le_antisymm ?_ ?_⟩
      · simpa [List.length_take, Nat.min_eq_left hn] using
          hScap i (x.take n) (by simp [List.length_take, hlen])
      · apply hcountge.trans
        rw [← hcard]
        apply Finset.card_le_card
        intro y hy
        exact Finset.mem_filter.mpr ⟨hsubset i t (Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2⟩

/-- Step 6 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
finite cost accounting for the greedy packing.  Partition the accepted leaves at each of
the `2 L + 1` levels and use the capacity bound there; these levels are disjoint sets of
strings, so their weights together are bounded by `B`. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_cost
    (P : BitString → Prop) (B : ℝ)
    (hB : ∀ T : Finset BitString, (∀ x ∈ T, P x) →
      ∑ x ∈ T, (2 : ℝ)⁻¹ ^ (x.length / 2) ≤ B)
    (L : ℕ) (S : Finset BitString)
    (hS : ∀ x ∈ S, x.length = 2 * L ∧ ∀ n ≤ x.length, P (x.take n))
    (hcap : ∀ x : BitString, x.length ≤ 2 * L →
      (S.filter (fun y => x <+: y)).card ≤ 2 ^ (L - x.length / 2)) :
    ((2 * L + 1 : ℕ) : ℝ) * ((S.card : ℝ) * (2 : ℝ)⁻¹ ^ L) ≤ B := by
  classical
  let F (n : ℕ) : Finset BitString := S.image (List.take n)
  have hlen : ∀ n ≤ 2 * L, ∀ x ∈ F n, x.length = n := by
    intro n hn x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [List.length_take, (hS y hy).1, Nat.min_eq_left hn]
  have hlevel : ∀ n ≤ 2 * L,
      (S.card : ℝ) * (2 : ℝ)⁻¹ ^ L ≤ ∑ x ∈ F n, (2 : ℝ)⁻¹ ^ (x.length / 2) := by
    intro n hn
    have hcard : (S.card : ℝ) =
        ∑ x ∈ F n, ((S.filter (fun y => y.take n = x)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image (List.take n) S
    rw [hcard, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x hx
    have hxlen := hlen n hn x hx
    have heq : S.filter (fun y => y.take n = x) = S.filter (fun y => x <+: y) := by
      ext y
      simp only [Finset.mem_filter, List.prefix_iff_eq_take, hxlen]
      exact and_congr_right fun _ => eq_comm
    have hc := hcap x (by omega)
    rw [hxlen] at hc
    rw [heq, hxlen]
    have hcR : ((S.filter (fun y => x <+: y)).card : ℝ) ≤ (2 : ℝ) ^ (L - n / 2) := by
      exact_mod_cast hc
    have hpow : (2 : ℝ) ^ (L - n / 2) * (2 : ℝ)⁻¹ ^ L =
        (2 : ℝ)⁻¹ ^ (n / 2) := by
      have hd : n / 2 ≤ L := by omega
      nth_rw 2 [← Nat.sub_add_cancel hd]
      rw [pow_add, ← mul_assoc, ← mul_pow]
      norm_num
    exact hpow ▸ mul_le_mul_of_nonneg_right hcR (by positivity)
  have hdisj : (↑(Finset.range (2 * L + 1)) : Set ℕ).PairwiseDisjoint F := by
    intro n hn k hk hnk
    apply Finset.disjoint_left.mpr
    intro x hxn hxk
    have hn' : n ≤ 2 * L := by simpa using hn
    have hk' : k ≤ 2 * L := by simpa using hk
    exact hnk ((hlen n hn' x hxn).symm.trans (hlen k hk' x hxk))
  have htotal : (∑ n ∈ Finset.range (2 * L + 1),
      ∑ x ∈ F n, (2 : ℝ)⁻¹ ^ (x.length / 2)) ≤ B := by
    rw [← Finset.sum_biUnion hdisj]
    apply hB
    intro x hx
    obtain ⟨n, hn, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (hS y hy).2 n (by have := Finset.mem_range.mp hn; rw [(hS y hy).1]; omega)
  calc ((2 * L + 1 : ℕ) : ℝ) * ((S.card : ℝ) * (2 : ℝ)⁻¹ ^ L)
      = ∑ _n ∈ Finset.range (2 * L + 1), (S.card : ℝ) * (2 : ℝ)⁻¹ ^ L := by simp
    _ ≤ ∑ n ∈ Finset.range (2 * L + 1),
        ∑ x ∈ F n, (2 : ℝ)⁻¹ ^ (x.length / 2) :=
      Finset.sum_le_sum fun n hn => hlevel n (by have := Finset.mem_range.mp hn; omega)
    _ ≤ B := htotal

/-- Step 7 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
the finite capital associated with a packing is the sum of its elementary half-gales. -/
private noncomputable def exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale
    (S : Finset BitString) (x : BitString) : ℝ :=
  ∑ y ∈ S, exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (1 / 2) (some y) x

/-- Step 7 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
the finite capital satisfies the exact gale equation. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_gale (S : Finset BitString) :
    IsGale (1 / 2) (exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale S) := by
  constructor
  · intro x
    exact Finset.sum_nonneg fun y _ =>
      (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_gale (1 / 2) (some y)).nonneg x
  · intro x
    simp only [exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ =>
      (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_gale (1 / 2) (some y)).gale x

/-- Step 7 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
every accepted leaf of length `2 L` has initial cost `2⁻ᴸ`. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_mass (L : ℕ)
    (S : Finset BitString) (hlen : ∀ x ∈ S, x.length = 2 * L) :
    ∑ x ∈ S, intervalAlphaMass (1 / 2 : ℝ) x =
      ENNReal.ofReal ((S.card : ℝ) * (2 : ℝ)⁻¹ ^ L) := by
  have heq : ∀ x ∈ S, intervalAlphaMass (1 / 2 : ℝ) x =
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ L) := by
    intro x hx
    rw [intervalAlphaMass_eq_inv_two_pow, hlen x hx, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    have hexp : ((2 * L : ℕ) : ℝ) * (1 / 2 : ℝ) = (L : ℝ) := by push_cast; ring
    rw [hexp, ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  rw [Finset.sum_congr rfl heq]
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast]

/-- Step 7 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
a saturated prefix has capital at least one.  At odd lengths the rounded dyadic capacity
is larger than the exact half-dimensional weight, which only improves this inequality. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_hit
    (L : ℕ) (S : Finset BitString) (hlen : ∀ y ∈ S, y.length = 2 * L)
    (x : BitString) (hx : x.length ≤ 2 * L)
    (hfull : (S.filter (fun y => x <+: y)).card = 2 ^ (L - x.length / 2)) :
    1 ≤ exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale S x := by
  have hsum : (∑ y ∈ S.filter (fun y => x <+: y),
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (1 / 2) (some y) x) =
      (2 : ℝ) ^ (L - x.length / 2) *
        (2 : ℝ) ^ (-((1 / 2 : ℝ) * ((2 * L - x.length : ℕ) : ℝ))) := by
    calc (∑ y ∈ S.filter (fun y => x <+: y),
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (1 / 2) (some y) x)
        = ∑ _y ∈ S.filter (fun y => x <+: y),
            (2 : ℝ) ^ (-((1 / 2 : ℝ) * ((2 * L - x.length : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_of_prefix (1 / 2)
            (Finset.mem_filter.mp hy).2, hlen y (Finset.mem_filter.mp hy).1]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hfull]; norm_cast
  have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (L - x.length / 2) *
      (2 : ℝ) ^ (-((1 / 2 : ℝ) * ((2 * L - x.length : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    apply Real.one_le_rpow (by norm_num)
    rw [Nat.cast_sub (by omega : x.length / 2 ≤ L), Nat.cast_sub hx]
    have hd : 2 * (x.length / 2) ≤ x.length := by omega
    have hdR : 2 * ((x.length / 2 : ℕ) : ℝ) ≤ (x.length : ℝ) := by exact_mod_cast hd
    push_cast
    linarith
  rw [← hsum] at hge
  refine hge.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
  intro y _ _
  exact (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_gale (1 / 2) (some y)).nonneg x

/-- Step 8 of the proof of `exists_lsc_isGale_not_isEffectiveAlphaNull`:
mix uniformly enumerable finite packings of costs at most `2⁻⁽ᵏ⁺¹⁾`, with coefficients
`(k+1)/2`.  Their total initial capital is at most one.  If each packing reaches one on
a prefix of `w`, the mixture is unbounded there.  Enumerability of membership, rather than
computability of the finite sets themselves, suffices for lower semicomputability. -/
private theorem exists_lsc_isGale_not_isEffectiveAlphaNull_mix
    (S : ℕ → Finset BitString) (hS : IsRE (fun p : ℕ × BitString => p.2 ∈ S p.1))
    (hmass : ∀ k : ℕ, (∑ x ∈ S k, intervalAlphaMass (1 / 2 : ℝ) x) ≤
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (k + 1)))
    (w : CantorSeq)
    (hhit : ∀ k : ℕ, ∃ n : ℕ,
      1 ≤ exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale (S k) (cantorPrefix w n)) :
    ∃ m : BitString → ℝ, IsGale (1 / 2) m ∧ IsLowerSemicomputableOnStrings m ∧
      m [] ≤ 1 ∧ Wins m w := by
  classical
  let g (i : ℕ) (y : BitString) : ℝ :=
    if natToBitString i.unpair.2 ∈ S i.unpair.1 then
      exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (1 / 2)
        (some (natToBitString i.unpair.2)) y
    else 0
  let c (i : ℕ) : ℝ := (i.unpair.1 + 1 : ℝ) / 2
  have hc : ∀ i, 0 ≤ c i := fun i => by dsimp [c]; positivity
  have hg : ∀ i, IsGale (1 / 2) (g i) := by
    intro i
    by_cases hi : natToBitString i.unpair.2 ∈ S i.unpair.1
    · simpa only [g, hi, ↓reduceIte] using
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_gale (1 / 2)
          (some (natToBitString i.unpair.2))
    · simp only [g, hi, ↓reduceIte]
      exact ⟨fun _ => le_rfl, fun _ => by simp⟩
  let F (p : ℕ × ℕ) : ENNReal := ENNReal.ofReal (((p.1 : ℝ) + 1) / 2) *
    if natToBitString p.2 ∈ S p.1 then intervalAlphaMass (1 / 2) (natToBitString p.2) else 0
  have hterm : ∀ i : ℕ, c i * g i [] = (F i.unpair).toReal := by
    intro i
    have hinit := (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_self_init (1 / 2)).2
      (some (natToBitString i.unpair.2))
    by_cases hi : natToBitString i.unpair.2 ∈ S i.unpair.1
    · simp only [g, F, c, hi, ↓reduceIte, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (i.unpair.1 + 1 : ℝ) / 2)]
      rw [hinit, coverAlphaMass_some]
    · simp [g, F, hi]
  have hgeom := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step6_aux1
  have hFsum : ∑' i : ℕ, F i.unpair ≤ 1 := by
    calc ∑' i : ℕ, F i.unpair = ∑' p : ℕ × ℕ, F p := Nat.pairEquiv.symm.tsum_eq F
      _ = ∑' k : ℕ, ∑' j : ℕ, F (k, j) := ENNReal.tsum_prod'
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 1) / 2 * (2 : ℝ)⁻¹ ^ (k + 1)) := by
          apply ENNReal.tsum_le_tsum
          intro k
          have hsumS : (∑' j : ℕ, if natToBitString j ∈ S k then
              intervalAlphaMass (1 / 2) (natToBitString j) else 0) =
              ∑ x ∈ S k, intervalAlphaMass (1 / 2) x := by
            rw [tsum_comp_natToBitString (fun x =>
              if x ∈ S k then intervalAlphaMass (1 / 2) x else 0)]
            rw [tsum_eq_sum (s := S k) (fun x hx => ite_eq_right hx)]
            exact Finset.sum_congr rfl fun x hx => ite_eq_left hx
          calc ∑' j : ℕ, F (k, j)
              = ENNReal.ofReal (((k : ℝ) + 1) / 2) *
                ∑ x ∈ S k, intervalAlphaMass (1 / 2) x := by
                  simp only [F, ENNReal.tsum_mul_left]
                  rw [hsumS]
            _ ≤ ENNReal.ofReal (((k : ℝ) + 1) / 2) *
                ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (k + 1)) := mul_le_mul' le_rfl (hmass k)
            _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (∑' k : ℕ, ((k : ℝ) + 1) / 2 * (2 : ℝ)⁻¹ ^ (k + 1)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom.summable).symm
      _ = 1 := by rw [hgeom.tsum_eq]; simp
  have hFtop : ∑' i : ℕ, F i.unpair ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hFsum
  have hsum : Summable (fun i => c i * g i []) := by
    simp_rw [hterm]
    exact ENNReal.summable_toReal hFtop
  have hinit : (∑' i, c i * g i []) ≤ 1 := by
    simp_rw [hterm]
    rw [← ENNReal.tsum_toReal_eq (fun i => ENNReal.ne_top_of_tsum_ne_top hFtop i)]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hFsum
  obtain ⟨hsumall, hmgale⟩ :=
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_mix_gale g c hg hc hsum
  have hhalf : ComputableReals.IsComputableReal (1 / 2 : ℝ) := by
    convert ComputableReals.isComputableReal_ratCast (1 / 2 : ℚ) using 1
    norm_num
  have helem := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc
    hhalf (by norm_num) (by norm_num)
  have hJ : Computable₂ (fun (_k : ℕ) (j : ℕ) => some (natToBitString j)) :=
    Primrec.option_some.to_comp.comp (computable_natToBitString.comp Computable.snd)
  have hpos := exists_lsc_isGale_wins_of_isEffectiveAlphaNull_step7_lsc
    (fun (_k : ℕ) (j : ℕ) => some (natToBitString j)) hJ
    (exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (1 / 2)) helem
  have hu : Computable (fun p : ℚ × ℕ × BitString => p.2.1.unpair) :=
    Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)
  have hmem : IsRE (fun p : ℚ × ℕ × BitString =>
      natToBitString p.2.1.unpair.2 ∈ S p.2.1.unpair.1) :=
    hS.comp_computable ((Computable.fst.comp hu).pair
      (computable_natToBitString.comp (Computable.snd.comp hu)))
  have hneg : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < 0) :=
    isRE_of_computable_bool _ (fun p => decide (p.1 < 0)) (fun p => by simp)
      ((computable_ratLtConst 0).comp Computable.fst)
  have hlsc : IsRE (fun p : ℚ × ℕ × BitString => (p.1 : ℝ) < c p.2.1 * g p.2.1 p.2.2) := by
    refine (hneg.or (hmem.and hpos)).of_iff fun p => ?_
    by_cases hp : natToBitString p.2.1.unpair.2 ∈ S p.2.1.unpair.1
    · simp only [g, hp, ↓reduceIte, true_and]
      change (p.1 : ℝ) < 0 ∨ (p.1 : ℝ) < c p.2.1 *
        exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale (1 / 2)
          (some (natToBitString p.2.1.unpair.2)) p.2.2 ↔ _
      constructor
      · rintro (h | h)
        · exact h.trans_le (mul_nonneg (hc _) (by
            exact exists_lsc_isGale_wins_of_isEffectiveAlphaNull_elemGale_nonneg _ _ _))
        · exact h
      · exact Or.inr
    · simp [g, hp]
  refine ⟨fun y => ∑' i, c i * g i y, hmgale,
    exists_lsc_isGale_wins_of_isEffectiveAlphaNull_lsc_tsum
      (fun i y => c i * g i y) (fun i y => mul_nonneg (hc i) ((hg i).nonneg y)) hlsc hsumall,
    hinit, ?_⟩
  rw [Wins, not_bddAbove_iff]
  intro M
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M)
  obtain ⟨n, hn⟩ := hhit k
  refine ⟨∑' i, c i * g i (cantorPrefix w n), ⟨n, rfl⟩, ?_⟩
  have hsub : ((k : ℝ) + 1) / 2 *
      exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale (S k) (cantorPrefix w n) ≤
      ∑' i, c i * g i (cantorPrefix w n) := by
    let A := (S k).image (fun x => Nat.pair k (bitStringToNat x))
    have hle := (hsumall (cantorPrefix w n)).sum_le_tsum A
      (fun i _ => mul_nonneg (hc i) ((hg i).nonneg _))
    have heq : (∑ i ∈ A, c i * g i (cantorPrefix w n)) =
        ((k : ℝ) + 1) / 2 *
          exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale (S k) (cantorPrefix w n) := by
      rw [Finset.sum_image]
      · simp only [c, g, Nat.unpair_pair, natToBitString_bitStringToNat]
        rw [exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x hx => by rw [ite_eq_left hx]
      · intro x _ y _ hxy
        exact bitStringToNat_injective (Nat.pair_eq_pair.mp hxy).2
    rwa [heq] at hle
  have hcpos : (0 : ℝ) ≤ ((k : ℝ) + 1) / 2 := by positivity
  have hlow := mul_le_mul_of_nonneg_left hn hcpos
  linarith

/-- **SUV Section 9.10, p. 286**, the unnumbered assertion before Theorem 186: the winning set
of a lower semicomputable `α`-gale need not be effectively `α`-null.  We retain the book's
computable exponent and initial-capital convention.  The witness has `α < 1`, since for `α = 1`
Theorem 181 gives effective nullity. -/
theorem exists_lsc_isGale_not_isEffectiveAlphaNull :
    ∃ α : ℝ, ComputableReals.IsComputableReal α ∧ 0 < α ∧ α < 1 ∧
      ∃ m : BitString → ℝ, IsGale α m ∧ IsLowerSemicomputableOnStrings m ∧ m [] ≤ 1 ∧
        ¬ IsEffectiveAlphaNull α {w | Wins m w} := by
  classical
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨w, c, hw⟩ := exists_lsc_isGale_not_isEffectiveAlphaNull_profile U hU
  let P : BitString → Prop := fun x => KPPlain U x ≤ ((x.length / 2 + c : ℕ) : ℕ∞)
  let L : ℕ → ℕ := fun k => 2 ^ (c + (k + 1))
  have hL : Computable L := comp_pow.comp
    ((Primrec.nat_add.comp (Primrec.const c) Primrec.succ).to_comp)
  obtain ⟨S, hSre, hS, hcap, hfull⟩ :=
    exists_lsc_isGale_not_isEffectiveAlphaNull_greedy P
      (exists_lsc_isGale_not_isEffectiveAlphaNull_low_re U hU c) L hL
  have hlen : ∀ k x, x ∈ S k → x.length = 2 * L k := fun k x hx => (hS k x hx).1
  have hmass : ∀ k : ℕ, (∑ x ∈ S k, intervalAlphaMass (1 / 2 : ℝ) x) ≤
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (k + 1)) := by
    intro k
    rw [exists_lsc_isGale_not_isEffectiveAlphaNull_mass (L k) (S k) (hlen k)]
    apply ENNReal.ofReal_le_ofReal
    have hc := exists_lsc_isGale_not_isEffectiveAlphaNull_cost P ((2 : ℝ) ^ c)
      (fun T hT => exists_lsc_isGale_not_isEffectiveAlphaNull_kraft_bound U hU c T hT)
      (L k) (S k) (hS k) (hcap k)
    have heq : (L k : ℝ) * (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ) ^ c := by
      change ((2 ^ (c + (k + 1)) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (k + 1) = _
      push_cast
      rw [pow_add]
      rw [mul_assoc, ← mul_pow]
      norm_num
    have hpos : (0 : ℝ) < (2 * L k + 1 : ℕ) := by positivity
    have hD : (L k : ℝ) ≤ (2 * L k + 1 : ℕ) := by
      exact_mod_cast (by omega : L k ≤ 2 * L k + 1)
    have hB := mul_le_mul_of_nonneg_right hD
      (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (k + 1) by positivity)
    rw [heq] at hB
    nlinarith
  have hhit : ∀ k : ℕ, ∃ n : ℕ,
      1 ≤ exists_lsc_isGale_not_isEffectiveAlphaNull_finiteGale (S k)
        (cantorPrefix w n) := by
    intro k
    obtain ⟨n, hn, hnfull⟩ := hfull k (cantorPrefix w (2 * L k)) (by simp)
      (fun n hn => by
        rw [cantorPrefix_length] at hn
        rw [cantorPrefix_take w n (2 * L k) hn]
        simpa only [P, cantorPrefix_length] using (hw n).1)
    rw [cantorPrefix_length] at hn
    rw [cantorPrefix_take w n (2 * L k) hn] at hnfull
    refine ⟨n, exists_lsc_isGale_not_isEffectiveAlphaNull_hit
      (L k) (S k) (hlen k) (cantorPrefix w n) (by simpa using hn) ?_⟩
    simpa only [cantorPrefix_length] using hnfull
  obtain ⟨m, hm, hlsc, hinit, hwin⟩ :=
    exists_lsc_isGale_not_isEffectiveAlphaNull_mix S hSre hmass w hhit
  refine ⟨1 / 2, ?_, by norm_num, by norm_num, m, hm, hlsc, hinit, ?_⟩
  · convert ComputableReals.isComputableReal_ratCast (1 / 2 : ℚ) using 1
    norm_num
  · intro hnull
    exact exists_lsc_isGale_not_isEffectiveAlphaNull_not_null U hU w c
      (fun n => (hw n).2) (hnull.mono_set (Set.singleton_subset_iff.mpr hwin))

end Kolmogorov.FrequencyGames
