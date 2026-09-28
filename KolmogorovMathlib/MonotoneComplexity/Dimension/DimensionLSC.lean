/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.Basic
import KolmogorovMathlib.MonotoneComplexity.Dimension.Dilution
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic.Part01
import KolmogorovMathlib.MonotoneComplexity.Omega.Basic

/-!
# SUV Theorem 118, converse direction (§5.8, pp. 173-174, A. Khodyrev)

> "On the other hand, let us assume that for some `α` there exists the largest
> effectively `α`-null set.  Consider the algorithm that generates covers for it.
> This algorithm can be used to obtain lower bounds for `α`.  Indeed, if for some
> rational `ε` the algorithm produces a finite family of intervals (at some step)
> and `β`-powers of the measures of these intervals exceed `ε`, this means that
> `β < α`.  It remains to prove that these bounds can be arbitrarily close to
> `α`.  Assume that this is not the case and all of them are less than some
> `α' < α`.  In this case every effectively `α'`-null set would be at the same
> time an effectively `α`-null set, which is not true (there exist sets of any
> effective Hausdorff dimension; see Problem 170, p. 175)."  (SUV pp. 173-174)

## The printed statement is false for `α > 1`

For every `α > 1` *every* subset of `Ω` is an effective `α`-null set
(`isEffectiveAlphaNull_of_one_lt`, SUV p. 172, remark (3)), so `Set.univ` is the
largest effectively `α`-null set and the hypothesis of the converse direction
holds for **every** real `α > 1`, while only countably many reals are lower
semicomputable.  The converse is therefore not provable as printed; the
counterexample is `exists_largest_isEffectiveAlphaNull_of_one_lt` below.  The
corrected statement adds `α ≤ 1` — the only case the source uses, since the effective
Hausdorff dimension lives in `[0,1]` — and is proved here.

## What replaces Problem 170

The source's "there exist sets of any effective Hausdorff dimension" is invoked
only to separate two exponents `β < γ < α`, and for that a *set* of dimension
`γ` suffices: the singleton of Problem 170 is not needed.  The witness is the
dilution set `dilSet p q` of `Dimension/Dilution.lean` (SUV Problem 173's set of
sequences with zeros at specified places), which is an effective `α`-null set for
every `α > p/q` and is not even a classical `β`-null set for `β ≤ p/q`.  The
whole proof therefore stays inside the elementary layer: no Kolmogorov
complexity, no Martin-Löf randomness, no compactness, no mass-distribution
principle.

## The certificates

`α` is lower semicomputable because `{r : ℚ | r < α}` is enumerable
(`isLowerSemicomputableReal_iff_re_lt`).  The certificate for `r < α` is a finite
initial segment of the cover produced at accuracy `1/8` whose `r`-weight exceeds
`1/8`.  The weight `2^{-r·l}` is irrational, so the *rational* under-approximation
`2^{-⌈r·l⌉}` is used; `⌈r·l⌉` is `dilCount r.num.toNat r.den l`, and the
approximation loses at most a factor of `2`, which is harmless because the true
weight of a genuine certificate is at least `1`.
-/

namespace Kolmogorov

open MeasureTheory Encodable
open scoped ENNReal

/-! ## `ℝ≥0∞` powers of `2` -/

private lemma dilTwoRpowNeg (m : ℕ) : (2 : ℝ≥0∞) ^ (-(m : ℝ)) = (2 : ℝ≥0∞)⁻¹ ^ m := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]

private lemma dilTwoPowMul (d n : ℕ) (α : ℝ) :
    (2 : ℝ≥0∞) ^ d * (((2 : ℝ≥0∞)⁻¹ ^ n) ^ α) = (2 : ℝ≥0∞) ^ ((d : ℝ) - (n : ℝ) * α) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have e1 : ((2 : ℝ≥0∞)⁻¹ ^ n) = ((2 : ℝ≥0∞)⁻¹) ^ ((n : ℕ) : ℝ) :=
    (ENNReal.rpow_natCast _ _).symm
  have e2 : (((2 : ℝ≥0∞)⁻¹) ^ ((n : ℕ) : ℝ)) ^ α = ((2 : ℝ≥0∞)⁻¹) ^ ((n : ℝ) * α) :=
    (ENNReal.rpow_mul _ _ _).symm
  have e3 : ((2 : ℝ≥0∞)⁻¹) ^ ((n : ℝ) * α) = (2 : ℝ≥0∞) ^ (-((n : ℝ) * α)) := by
    rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  have e4 : (2 : ℝ≥0∞) ^ d = (2 : ℝ≥0∞) ^ ((d : ℕ) : ℝ) := (ENNReal.rpow_natCast _ _).symm
  rw [e1, e2, e3, e4, ← ENNReal.rpow_add _ _ h2 h2']
  ring_nf

/-- The interval weight as an `ℝ≥0∞` power of `2`. -/
lemma intervalAlphaMass_eq_two_rpow (β : ℝ) (x : BitString) :
    intervalAlphaMass β x = (2 : ℝ≥0∞) ^ (-(x.length : ℝ) * β) := by
  have h := dilTwoPowMul 0 x.length β
  rw [intervalAlphaMass_eq_inv_two_pow]
  simpa using h

/-! ## The dilution set in the `α`-null vocabulary -/

/-- The `α`-weight of the length-`M·(t+2)` cover of the dilution set is below
`2^{-(t+1)}`, when `1/M ≤ α - p/q`. -/
private lemma dilCoverWeightLe (p q : ℕ) {α : ℝ} {M : ℕ} (hq : 0 < q) (hMpos : 0 < M)
    (hMle : (1 : ℝ) / (M : ℝ) ≤ α - (p : ℝ) / (q : ℝ)) (t : ℕ) :
    (∑' k, coverAlphaMass α (dilCover p q (M * (t + 2)) k)) ≤ (2 : ℝ≥0∞)⁻¹ ^ (t + 1) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hsum : (∑' k, coverAlphaMass α (dilCover p q (M * (t + 2)) k))
      = (2 : ℝ≥0∞) ^ (dilCount p q (M * (t + 2)))
        * (((2 : ℝ≥0∞)⁻¹ ^ (M * (t + 2))) ^ α) := by
    simp only [coverAlphaMass_eq_elim]
    exact tsum_dilCover_rpow p q α (M * (t + 2))
  have hdnat : q * dilCount p q (M * (t + 2)) ≤ p * (M * (t + 2)) + q :=
    dilCount_mul_le p q (M * (t + 2))
  have hdR : ((dilCount p q (M * (t + 2)) : ℕ) : ℝ)
      ≤ (p : ℝ) * ((M * (t + 2) : ℕ) : ℝ) / (q : ℝ) + 1 := by
    have h1 : (q : ℝ) * ((dilCount p q (M * (t + 2)) : ℕ) : ℝ)
        ≤ (p : ℝ) * ((M * (t + 2) : ℕ) : ℝ) + (q : ℝ) := by exact_mod_cast hdnat
    have h2 : ((dilCount p q (M * (t + 2)) : ℕ) : ℝ) - 1
        ≤ (p : ℝ) * ((M * (t + 2) : ℕ) : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hqR]
      nlinarith
    linarith
  have hnM : ((M * (t + 2) : ℕ) : ℝ) = (M : ℝ) * ((t : ℝ) + 2) := by push_cast; ring
  have hα' : (p : ℝ) / (q : ℝ) + 1 / (M : ℝ) ≤ α := by linarith
  have hnpos : (0 : ℝ) ≤ ((M * (t + 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2' : ((M * (t + 2) : ℕ) : ℝ) * ((p : ℝ) / (q : ℝ))
      + ((M * (t + 2) : ℕ) : ℝ) * (1 / (M : ℝ)) ≤ ((M * (t + 2) : ℕ) : ℝ) * α := by
    have h := mul_le_mul_of_nonneg_left hα' hnpos
    rwa [mul_add] at h
  have h3 : ((M * (t + 2) : ℕ) : ℝ) * (1 / (M : ℝ)) = (t : ℝ) + 2 := by
    rw [hnM]; field_simp
  have h4 : ((M * (t + 2) : ℕ) : ℝ) * ((p : ℝ) / (q : ℝ))
      = (p : ℝ) * ((M * (t + 2) : ℕ) : ℝ) / (q : ℝ) := by ring
  have hexp : ((dilCount p q (M * (t + 2)) : ℕ) : ℝ)
      - ((M * (t + 2) : ℕ) : ℝ) * α ≤ -((t : ℝ) + 1) := by linarith
  calc (∑' k, coverAlphaMass α (dilCover p q (M * (t + 2)) k))
      = (2 : ℝ≥0∞) ^ (((dilCount p q (M * (t + 2)) : ℕ) : ℝ)
          - ((M * (t + 2) : ℕ) : ℝ) * α) := by rw [hsum, dilTwoPowMul]
    _ ≤ (2 : ℝ≥0∞) ^ (-((t : ℝ) + 1)) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ≥0∞)⁻¹ ^ (t + 1) := by
        rw [show -((t : ℝ) + 1) = -(((t + 1 : ℕ) : ℝ)) by push_cast; ring, dilTwoRpowNeg]

/-- **The dilution set is an effective `α`-null set above its density.** -/
theorem isEffectiveAlphaNull_dilSet (p q : ℕ) (hq : 0 < q) {α : ℝ}
    (hα : (p : ℝ) / (q : ℝ) < α) : IsEffectiveAlphaNull α (dilSet p q) := by
  obtain ⟨M0, hM0⟩ := exists_nat_one_div_lt (sub_pos.2 hα)
  have hMpos : 0 < M0 + 1 := Nat.succ_pos M0
  have hMle : (1 : ℝ) / ((M0 + 1 : ℕ) : ℝ) ≤ α - (p : ℝ) / (q : ℝ) := by
    have hcast : ((M0 + 1 : ℕ) : ℝ) = (M0 : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact hM0.le
  refine ⟨fun ε k => dilCover p q ((M0 + 1) * (ε.den + 2)) k, ?_, fun ε hε => ⟨?_, ?_⟩⟩
  · have hn : Computable (fun r : ℚ × ℕ => (M0 + 1) * (r.1.den + 2)) :=
      Primrec.nat_mul.to_comp.comp (Computable.const (M0 + 1))
        (Primrec.nat_add.to_comp.comp (computable_ratDen.comp Computable.fst)
          (Computable.const 2))
    exact (computable₂_dilCover p q).comp hn Computable.snd
  · exact subset_iUnion_dilCover p q hq _
  · refine lt_of_le_of_lt (dilCoverWeightLe p q hq hMpos hMle ε.den) ?_
    have hle : (2 : ℝ≥0∞)⁻¹ ^ ε.den ≤ ENNReal.ofReal (ε : ℝ) := by
      rw [← dyadicValue_one_eq_inv_two_pow']
      exact dyadicValue_den_le_rat hε
    refine lt_of_lt_of_le ?_ hle
    rw [pow_succ]
    have hne0 : (2 : ℝ≥0∞)⁻¹ ^ ε.den ≠ 0 :=
      pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num))
    have hnetop : (2 : ℝ≥0∞)⁻¹ ^ ε.den ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by norm_num))
    have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
    calc (2 : ℝ≥0∞)⁻¹ ^ ε.den * (2 : ℝ≥0∞)⁻¹
        < (2 : ℝ≥0∞)⁻¹ ^ ε.den * 1 := ENNReal.mul_lt_mul_right hne0 hnetop hhalf
      _ = (2 : ℝ≥0∞)⁻¹ ^ ε.den := mul_one _

/-- Every interval is at least as heavy for the exponent `β ≤ p/q` as
`2^{-⌈p·l/q⌉}`. -/
lemma inv_two_pow_dilCount_le_intervalAlphaMass (p q : ℕ) (hq : 0 < q) {β : ℝ}
    (hβ : β ≤ (p : ℝ) / (q : ℝ)) (x : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ (dilCount p q x.length) ≤ intervalAlphaMass β x := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnat : p * x.length ≤ q * dilCount p q x.length := le_dilCount p q x.length hq
  have hR : (p : ℝ) * (x.length : ℝ) ≤ (q : ℝ) * ((dilCount p q x.length : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hlen : (0 : ℝ) ≤ (x.length : ℝ) := Nat.cast_nonneg _
  have h1 : (x.length : ℝ) * β ≤ (x.length : ℝ) * ((p : ℝ) / (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hβ hlen
  have h2 : (x.length : ℝ) * ((p : ℝ) / (q : ℝ)) ≤ ((dilCount p q x.length : ℕ) : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ hqR]
    nlinarith
  rw [intervalAlphaMass_eq_two_rpow, ← dilTwoRpowNeg]
  refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  nlinarith

/-- **The dilution set is not a `β`-null set at or below its density** — not
even classically.  This is the separating fact that replaces Problem 170. -/
theorem not_isAlphaNull_dilSet (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) {β : ℝ}
    (hβ : β ≤ (p : ℝ) / (q : ℝ)) : ¬ IsAlphaNull β (dilSet p q) := by
  intro hnull
  obtain ⟨I, hcov, hsum⟩ := hnull (1 / 2) (by norm_num)
  have hge : (1 : ℝ≥0∞) ≤ ∑' k, coverAlphaMass β (I k) := by
    refine le_trans (one_le_tsum_dilPull p q hq hpq I hcov) (ENNReal.tsum_le_tsum ?_)
    intro k
    cases hIk : I k with
    | none => simp
    | some x =>
        simpa using inv_two_pow_dilCount_le_intervalAlphaMass p q hq hβ x
  have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    norm_num
  exact absurd hsum (not_lt.2 (le_trans hhalf hge))

/-- The `p/q`-diluted sequences are not effectively `β`-null for any `β ≤ p/q`, so their effective
dimension is at least `p/q`. -/
theorem not_isEffectiveAlphaNull_dilSet (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) {β : ℝ}
    (hβ : β ≤ (p : ℝ) / (q : ℝ)) : ¬ IsEffectiveAlphaNull β (dilSet p q) :=
  fun h => not_isAlphaNull_dilSet p q hq hpq hβ h.isAlphaNull

/-! ## The counterexample above `1` -/

/-- For `α > 1` the largest effectively `α`-null set exists — it is the whole
space — so the hypothesis of SUV Theorem 118's converse direction carries no
information about `α`.  This is why the converse needs `α ≤ 1`. -/
theorem exists_largest_isEffectiveAlphaNull_of_one_lt {α : ℝ} (hα : 1 < α) :
    ∃ A : Set CantorSeq, IsEffectiveAlphaNull α A ∧
      ∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → B ⊆ A :=
  ⟨Set.univ, isEffectiveAlphaNull_of_one_lt hα _, fun B _ => Set.subset_univ B⟩

/-! ## The certificates -/

/-- The rational under-approximation `2^{-⌈r·l(x)⌉}` of the `r`-weight of the
`k`-th interval of the cover `J`. -/
def alphaCertTerm (J : ℕ → Option BitString) (r : ℚ) (k : ℕ) : ℚ :=
  ((J k).map (fun x =>
    (1 : ℚ) / ((2 ^ dilCount r.num.toNat r.den x.length : ℕ) : ℚ))).getD 0

/-- The certified weight of the first `N` intervals of the cover `J`. -/
def alphaCertSum (J : ℕ → Option BitString) (r : ℚ) (N : ℕ) : ℚ :=
  (List.range N).foldl (fun s k => s + alphaCertTerm J r k) 0

/-- The certificate sum after `N` steps is the sum of the first `N` certificate terms. -/
lemma alphaCertSum_eq_sum (J : ℕ → Option BitString) (r : ℚ) (N : ℕ) :
    alphaCertSum J r N = ∑ k ∈ Finset.range N, alphaCertTerm J r k := by
  induction N with
  | zero => simp [alphaCertSum]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih, alphaCertSum, alphaCertSum, List.range_succ,
        List.foldl_append]
      simp

/-- Certificate terms are nonnegative. -/
lemma alphaCertTerm_nonneg (J : ℕ → Option BitString) (r : ℚ) (k : ℕ) :
    0 ≤ alphaCertTerm J r k := by
  unfold alphaCertTerm
  cases J k with
  | none => simp
  | some x =>
      simp only [Option.map_some, Option.getD_some]
      positivity

/-- The certified term, in `ℝ≥0∞`. -/
lemma ofReal_alphaCertTerm (J : ℕ → Option BitString) (r : ℚ) (k : ℕ) :
    ENNReal.ofReal ((alphaCertTerm J r k : ℚ) : ℝ)
      = (J k).elim 0 (fun x => (2 : ℝ≥0∞)⁻¹ ^ dilCount r.num.toNat r.den x.length) := by
  unfold alphaCertTerm
  cases J k with
  | none => simp
  | some x =>
      simp only [Option.map_some, Option.getD_some, Option.elim_some]
      have hcast : (((1 : ℚ) / ((2 ^ dilCount r.num.toNat r.den x.length : ℕ) : ℚ) : ℚ) : ℝ)
          = ((2 : ℝ)⁻¹) ^ dilCount r.num.toNat r.den x.length := by
        push_cast
        rw [inv_pow]
        simp
      rw [hcast, ENNReal.ofReal_pow (by norm_num)]
      congr 1
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num

/-- The ceiling bound `l·r ≤ ⌈l·r⌉`, in the `dilCount` presentation. -/
lemma mul_le_dilCount_num (r : ℚ) (l : ℕ) :
    (l : ℝ) * (r : ℝ) ≤ ((dilCount r.num.toNat r.den l : ℕ) : ℝ) := by
  have hden : 0 < r.den := r.pos
  have hdenR : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast hden
  by_cases hr : 0 < r
  · have hnat := le_dilCount r.num.toNat r.den l hden
    have hnumpos : 0 < r.num := Rat.num_pos.2 hr
    have htoNat : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnumpos.le
    have hR : ((r.num.toNat : ℕ) : ℝ) * (l : ℝ)
        ≤ (r.den : ℝ) * ((dilCount r.num.toNat r.den l : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [htoNat] at hR
    have hrdef : ((r : ℚ) : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by rw [Rat.cast_def]
    rw [hrdef, ← mul_div_assoc, div_le_iff₀ hdenR]
    nlinarith
  · push_neg at hr
    have hle : (l : ℝ) * (r : ℝ) ≤ 0 := by
      have hrR : ((r : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hr
      have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact hle.trans (Nat.cast_nonneg _)

/-- The ceiling bound, upper half: `⌈l·r⌉ ≤ l·r + 1` for `0 < r`. -/
lemma dilCount_num_le (r : ℚ) (hr : 0 < r) (l : ℕ) :
    ((dilCount r.num.toNat r.den l : ℕ) : ℝ) ≤ (l : ℝ) * (r : ℝ) + 1 := by
  have hden : 0 < r.den := r.pos
  have hdenR : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast hden
  have hnat := dilCount_mul_le r.num.toNat r.den l
  have hnumpos : 0 < r.num := Rat.num_pos.2 hr
  have htoNat : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnumpos.le
  have hR : (r.den : ℝ) * ((dilCount r.num.toNat r.den l : ℕ) : ℝ)
      ≤ ((r.num.toNat : ℕ) : ℝ) * (l : ℝ) + (r.den : ℝ) := by exact_mod_cast hnat
  rw [htoNat] at hR
  have hrdef : ((r : ℚ) : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by rw [Rat.cast_def]
  have hstep : ((dilCount r.num.toNat r.den l : ℕ) : ℝ) - 1
      ≤ (l : ℝ) * (r.num : ℝ) / (r.den : ℝ) := by
    rw [le_div_iff₀ hdenR]
    nlinarith
  rw [hrdef, ← mul_div_assoc]
  linarith

/-- **Soundness of the certificate weight**: it never exceeds the true weight. -/
lemma ofReal_alphaCertSum_le (J : ℕ → Option BitString) (r : ℚ) (N : ℕ) :
    ENNReal.ofReal ((alphaCertSum J r N : ℚ) : ℝ)
      ≤ ∑ k ∈ Finset.range N, coverAlphaMass ((r : ℚ) : ℝ) (J k) := by
  have hnn : ∀ k ∈ Finset.range N, 0 ≤ ((alphaCertTerm J r k : ℚ) : ℝ) := by
    intro k _
    exact_mod_cast alphaCertTerm_nonneg J r k
  have hcast : ((∑ k ∈ Finset.range N, alphaCertTerm J r k : ℚ) : ℝ)
      = ∑ k ∈ Finset.range N, ((alphaCertTerm J r k : ℚ) : ℝ) := by push_cast; ring
  rw [alphaCertSum_eq_sum, hcast, ENNReal.ofReal_sum_of_nonneg hnn]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [ofReal_alphaCertTerm]
  cases hJ : J k with
  | none => simp
  | some x =>
      simp only [Option.elim_some, coverAlphaMass_some]
      rw [intervalAlphaMass_eq_two_rpow, ← dilTwoRpowNeg]
      refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h := mul_le_dilCount_num r x.length
      nlinarith

/-- **Completeness of the certificate weight**: it loses at most a factor `2`. -/
lemma sum_le_two_mul_ofReal_alphaCertSum (J : ℕ → Option BitString) {r : ℚ} (hr : 0 < r)
    (N : ℕ) :
    (∑ k ∈ Finset.range N, coverAlphaMass ((r : ℚ) : ℝ) (J k))
      ≤ 2 * ENNReal.ofReal ((alphaCertSum J r N : ℚ) : ℝ) := by
  have hnn : ∀ k ∈ Finset.range N, 0 ≤ ((alphaCertTerm J r k : ℚ) : ℝ) := by
    intro k _
    exact_mod_cast alphaCertTerm_nonneg J r k
  have hcast : ((∑ k ∈ Finset.range N, alphaCertTerm J r k : ℚ) : ℝ)
      = ∑ k ∈ Finset.range N, ((alphaCertTerm J r k : ℚ) : ℝ) := by push_cast; ring
  rw [alphaCertSum_eq_sum, hcast, ENNReal.ofReal_sum_of_nonneg hnn, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [ofReal_alphaCertTerm]
  cases hJ : J k with
  | none => simp
  | some x =>
      simp only [Option.elim_some, coverAlphaMass_some]
      have hrhs : (2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
            (-((dilCount r.num.toNat r.den x.length : ℕ) : ℝ))
          = (2 : ℝ≥0∞) ^ ((1 : ℝ) - ((dilCount r.num.toNat r.den x.length : ℕ) : ℝ)) := by
        rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
          ENNReal.rpow_one]
      rw [intervalAlphaMass_eq_two_rpow, ← dilTwoRpowNeg, hrhs]
      refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h := dilCount_num_le r hr x.length
      nlinarith

/-! ## The enumeration of the rationals below `α` -/

/-- The certificate test at the index `j`: either the rational is nonpositive
(hence below the positive `α`), or the first `j.unpair.2` intervals of the cover
already carry `r`-weight above `1/8`. -/
def alphaCertTest (J : ℕ → Option BitString) (j : ℕ) : Bool :=
  cond (!ratLtPair (0, ratOfCode j.unpair.1)) true
    (ratLtPair ((1 : ℚ) / 8, alphaCertSum J (ratOfCode j.unpair.1) j.unpair.2))

/-- The enumeration of `{r : ℚ | r < α}` extracted from the cover algorithm. -/
def alphaCertEnum (J : ℕ → Option BitString) (j : ℕ) : Option ℚ :=
  cond (alphaCertTest J j) (some (ratOfCode j.unpair.1)) none

/-- The `((num, den), length)` triple that `dilCount` is applied to.  Naming it
(with its type written out) keeps the `Computable.pair` nest from being
elaborated against a metavariable-headed target. -/
private lemma computable_alphaCertArg :
    Computable (fun v : (ℚ × ℕ) × BitString =>
      (((v.1.1.num.toNat, v.1.1.den), v.2.length) : (ℕ × ℕ) × ℕ)) := by
  have hnum : Computable (fun v : (ℚ × ℕ) × BitString => v.1.1.num.toNat) :=
    ComputableReals.primrec_intToNat.to_comp.comp
      (computable_ratNum.comp (Computable.fst.comp Computable.fst))
  have hden : Computable (fun v : (ℚ × ℕ) × BitString => v.1.1.den) :=
    computable_ratDen.comp (Computable.fst.comp Computable.fst)
  have hlen : Computable (fun v : (ℚ × ℕ) × BitString => v.2.length) :=
    Primrec.list_length.to_comp.comp Computable.snd
  exact Computable.pair (Computable.pair hnum hden) hlen

/-- The denominator `2^{dilCount …}` of an `alphaCertTerm` summand. -/
private lemma computable_alphaCertPow :
    Computable (fun v : (ℚ × ℕ) × BitString =>
      (2 ^ dilCount v.1.1.num.toNat v.1.1.den v.2.length : ℕ)) :=
  comp_pow.comp ((computable_dilCount₃.comp computable_alphaCertArg).of_eq fun _ => rfl)

/-- The value `2^{-dilCount …}` attached to an emitted string.  Kept as its own
declaration: assembling it and the `Option.map`/`getD` layer inside a single
declaration is what made `computable₂_alphaCertTerm` expensive. -/
private lemma computable_alphaCertVal :
    Computable (fun v : (ℚ × ℕ) × BitString =>
      (1 : ℚ) / ((2 ^ dilCount v.1.1.num.toNat v.1.1.den v.2.length : ℕ) : ℚ)) :=
  computable_of_num_den (Computable.const (1 : ℤ)) computable_alphaCertPow
    (fun _ => Nat.two_pow_pos _) (fun _ => by push_cast; ring)

/-- For a computable cover enumeration the certificate terms are computable in the exponent and the
index. -/
lemma computable₂_alphaCertTerm {J : ℕ → Option BitString} (hJ : Computable J) :
    Computable₂ (alphaCertTerm J) := by
  have hJk : Computable (fun a : ℚ × ℕ => J a.2) := hJ.comp Computable.snd
  exact (Computable.option_getD (Computable.option_map hJk computable_alphaCertVal.to₂)
    (Computable.const 0)).to₂

-- the fold's step function is a four-fold composition over three product types
/-- For a computable cover enumeration the certificate sums are computable in the exponent and the
number of steps. -/
lemma computable₂_alphaCertSum {J : ℕ → Option BitString} (hJ : Computable J) :
    Computable₂ (alphaCertSum J) := by
  have hterm := computable₂_alphaCertTerm hJ
  have hf : Computable (fun a : ℚ × ℕ => List.range a.2) :=
    Primrec.list_range.to_comp.comp Computable.snd
  have hg : Computable (fun _ : ℚ × ℕ => (0 : ℚ)) := Computable.const 0
  have hh : Computable₂ (fun (a : ℚ × ℕ) (u : ℚ × ℕ) => u.1 + alphaCertTerm J a.1 u.2) :=
    Computable₂.comp computable₂_ratAdd
      (Computable.fst.comp Computable.snd)
      (hterm.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.snd))
  exact (computable_list_foldl hf hg hh).of_eq (fun a => rfl)

-- the test is a `cond` over two rational comparisons, each a composition
/-- For a computable cover enumeration the certificate enumeration is computable. -/
lemma computable_alphaCertEnum {J : ℕ → Option BitString} (hJ : Computable J) :
    Computable (alphaCertEnum J) := by
  have hr : Computable (fun j : ℕ => ratOfCode j.unpair.1) :=
    computable_ratOfCode.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have hN : Computable (fun j : ℕ => j.unpair.2) := (Primrec.snd.comp Primrec.unpair).to_comp
  have h1 : Computable (fun j : ℕ => !ratLtPair (0, ratOfCode j.unpair.1)) :=
    (Primrec.dom_bool (fun b => !b)).to_comp.comp
      (computable_ratLtPair.comp (Computable.pair (Computable.const 0) hr))
  have h2 : Computable (fun j : ℕ =>
      ratLtPair ((1 : ℚ) / 8, alphaCertSum J (ratOfCode j.unpair.1) j.unpair.2)) :=
    computable_ratLtPair.comp
      (Computable.pair (Computable.const ((1 : ℚ) / 8))
        ((computable₂_alphaCertSum hJ).comp hr hN))
  have htest : Computable (alphaCertTest J) :=
    Computable.cond h1 (Computable.const true) h2
  exact Computable.cond htest (Computable.option_some.comp hr) (Computable.const none)

/-! ## SUV Theorem 118, converse direction, corrected -/

/-- Nonpositive rationals are always enumerated by `alphaCertEnum`. -/
private lemma alphaCertEnum_of_nonpos (J : ℕ → Option BitString) (r : ℚ) (hr : r ≤ 0) :
    alphaCertEnum J (Nat.pair (ratCode r) 0) = some r := by
  have hlt : ratLtPair (0, r) = false := by
    simp only [ratLtPair, decide_eq_false_iff_not, not_lt]
    exact hr
  have htest : alphaCertTest J (Nat.pair (ratCode r) 0) = true := by
    unfold alphaCertTest
    rw [Nat.unpair_pair]
    simp [ratOfCode_ratCode, hlt]
  unfold alphaCertEnum
  rw [htest, Nat.unpair_pair]
  simp only [ratOfCode_ratCode]
  rfl

/-- If the certificate sum exceeds `1/8`, `alphaCertEnum` enumerates `r`. -/
private lemma alphaCertEnum_of_cert (J : ℕ → Option BitString) {r : ℚ} (N : ℕ)
    (hcert : (1 : ℚ) / 8 < alphaCertSum J r N) :
    alphaCertEnum J (Nat.pair (ratCode r) N) = some r := by
  have hlt : ratLtPair ((1 : ℚ) / 8, alphaCertSum J r N) = true := by
    simp only [ratLtPair, decide_eq_true_eq]
    exact hcert
  have htest : alphaCertTest J (Nat.pair (ratCode r) N) = true := by
    unfold alphaCertTest
    rw [Nat.unpair_pair]
    simp only [ratOfCode_ratCode, hlt]
    cases hb : (!ratLtPair ((0 : ℚ), r)) <;> rfl
  unfold alphaCertEnum
  rw [htest, Nat.unpair_pair]
  simp only [ratOfCode_ratCode]
  rfl

/-- An enumerated positive rational has a certificate sum exceeding `1/8`. -/
private lemma alphaCertSum_gt_of_alphaCertEnum {J : ℕ → Option BitString} {i : ℕ} {r : ℚ}
    (hi : alphaCertEnum J i = some r) (hr : 0 < r) :
    (1 : ℚ) / 8 < alphaCertSum J r i.unpair.2 := by
  have htest : alphaCertTest J i = true := by
    unfold alphaCertEnum at hi
    cases htb : alphaCertTest J i with
    | false => rw [htb] at hi; simp at hi
    | true => rfl
  have hreq : ratOfCode i.unpair.1 = r := by
    unfold alphaCertEnum at hi
    rw [htest] at hi
    simpa using hi
  have hneg : (!ratLtPair (0, ratOfCode i.unpair.1)) = false := by
    have hlt : ratLtPair (0, ratOfCode i.unpair.1) = true := by
      rw [hreq]
      simp only [ratLtPair, decide_eq_true_eq]
      exact hr
    simp [hlt]
  have hpos : ratLtPair ((1 : ℚ) / 8,
      alphaCertSum J (ratOfCode i.unpair.1) i.unpair.2) = true := by
    unfold alphaCertTest at htest
    rw [hneg] at htest
    exact htest
  simp only [ratLtPair, decide_eq_true_eq] at hpos
  rwa [hreq] at hpos

/-- If `r < α ≤ 1` and `J` covers the largest `α`-null set, some certificate sum exceeds `1/8`. -/
private lemma exists_alphaCertSum_gt (α : ℝ) (hα1 : α ≤ 1)
    (A : Set CantorSeq) (hmax : ∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → B ⊆ A)
    (J : ℕ → Option BitString) (hsub : A ⊆ ⋃ k, (J k).elim ∅ cantorCylinder)
    {r : ℚ} (hr0 : 0 < r) (hrα : (r : ℝ) < α) :
    ∃ N : ℕ, (1 : ℚ) / 8 < alphaCertSum J r N := by
  obtain ⟨γ, hrγ, hγα⟩ := exists_rat_btwn hrα
  have hγpos : 0 < γ := by
    have : ((0 : ℚ) : ℝ) < ((γ : ℚ) : ℝ) := lt_trans (by exact_mod_cast hr0) hrγ
    exact_mod_cast this
  have hγ1 : ((γ : ℚ) : ℝ) < 1 := lt_of_lt_of_le hγα hα1
  have hqqpos : 0 < γ.den := γ.pos
  have hnumpos : 0 < γ.num := Rat.num_pos.2 hγpos
  have hppR : ((γ.num.toNat : ℕ) : ℝ) = (γ.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnumpos.le
  have hqqR : (0 : ℝ) < ((γ.den : ℕ) : ℝ) := by exact_mod_cast hqqpos
  have hratio : ((γ.num.toNat : ℕ) : ℝ) / ((γ.den : ℕ) : ℝ) = ((γ : ℚ) : ℝ) := by
    rw [hppR, Rat.cast_def]
  have hppqq : γ.num.toNat ≤ γ.den := by
    have h1 : ((γ.num.toNat : ℕ) : ℝ) / ((γ.den : ℕ) : ℝ) < 1 := by rw [hratio]; exact hγ1
    rw [div_lt_one hqqR] at h1
    exact le_of_lt (by exact_mod_cast h1)
  have hdilnull : IsEffectiveAlphaNull α (dilSet γ.num.toNat γ.den) :=
    isEffectiveAlphaNull_dilSet γ.num.toNat γ.den hqqpos (by rw [hratio]; exact hγα)
  have hsub' : dilSet γ.num.toNat γ.den ⊆ ⋃ k, (J k).elim ∅ cantorCylinder :=
    Set.Subset.trans (hmax _ hdilnull) hsub
  have hone : (1 : ℝ≥0∞) ≤ ∑' k, (J k).elim 0
      (fun x => (2 : ℝ≥0∞)⁻¹ ^ (dilCount γ.num.toNat γ.den x.length)) :=
    one_le_tsum_dilPull γ.num.toNat γ.den hqqpos hppqq _ hsub'
  have hrle : ((r : ℚ) : ℝ) ≤ ((γ.num.toNat : ℕ) : ℝ) / ((γ.den : ℕ) : ℝ) := by
    rw [hratio]; exact hrγ.le
  have hweight : (1 : ℝ≥0∞) ≤ ∑' k, coverAlphaMass ((r : ℚ) : ℝ) (J k) := by
    refine le_trans hone (ENNReal.tsum_le_tsum (fun k => ?_))
    cases hJk : J k with
    | none => simp
    | some x =>
        simpa using
          inv_two_pow_dilCount_le_intervalAlphaMass γ.num.toNat γ.den hqqpos hrle x
  have hsup : (∑' k, coverAlphaMass ((r : ℚ) : ℝ) (J k))
      = ⨆ N : ℕ, ∑ k ∈ Finset.range N, coverAlphaMass ((r : ℚ) : ℝ) (J k) :=
    ENNReal.tsum_eq_iSup_nat
  have hhalfone : ENNReal.ofReal ((1 : ℝ) / 2) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    norm_num
  have hhalflt : ENNReal.ofReal ((1 : ℝ) / 2)
      < ⨆ N : ℕ, ∑ k ∈ Finset.range N, coverAlphaMass ((r : ℚ) : ℝ) (J k) := by
    rw [← hsup]
    exact lt_of_lt_of_le hhalfone hweight
  obtain ⟨N, hN⟩ := lt_iSup_iff.1 hhalflt
  refine ⟨N, ?_⟩
  have hle := sum_le_two_mul_ofReal_alphaCertSum J hr0 N
  have h3 : ((1 : ℝ) / 4) < ((alphaCertSum J r N : ℚ) : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h4 : (2 : ℝ≥0∞) * ENNReal.ofReal ((alphaCertSum J r N : ℚ) : ℝ)
        ≤ ENNReal.ofReal ((1 : ℝ) / 2) := by
      have e : (2 : ℝ≥0∞) * ENNReal.ofReal ((alphaCertSum J r N : ℚ) : ℝ)
          = ENNReal.ofReal (2 * ((alphaCertSum J r N : ℚ) : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [e]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact absurd (lt_of_lt_of_le hN hle) (not_lt.2 h4)
  have hq4 : (1 : ℚ) / 4 < alphaCertSum J r N := by
    have hcast : (((1 : ℚ) / 4 : ℚ) : ℝ) < ((alphaCertSum J r N : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  linarith

/-- If a cover of mass `< 1/8` has a certificate sum exceeding `1/8`, then `r < α`. -/
private lemma lt_alpha_of_alphaCertSum (α : ℝ) (J : ℕ → Option BitString)
    (hmass : ∑' k, coverAlphaMass α (J k) < ENNReal.ofReal (((1 : ℚ) / 8 : ℚ) : ℝ))
    {r : ℚ} {N : ℕ} (hcert : (1 : ℚ) / 8 < alphaCertSum J r N) :
    ((r : ℚ) : ℝ) < α := by
  by_contra hcon
  push_neg at hcon
  have hmono : ∀ k, coverAlphaMass ((r : ℚ) : ℝ) (J k) ≤ coverAlphaMass α (J k) :=
    fun k => coverAlphaMass_mono hcon (J k)
  have hbig : ENNReal.ofReal (((1 : ℚ) / 8 : ℚ) : ℝ)
      < ∑ k ∈ Finset.range N, coverAlphaMass ((r : ℚ) : ℝ) (J k) := by
    refine lt_of_lt_of_le ?_ (ofReal_alphaCertSum_le J r N)
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2 ?_
    exact_mod_cast hcert
  have hchain : ∑ k ∈ Finset.range N, coverAlphaMass ((r : ℚ) : ℝ) (J k)
      ≤ ∑' k, coverAlphaMass α (J k) :=
    le_trans (Finset.sum_le_sum (fun k _ => hmono k)) (ENNReal.sum_le_tsum _)
  exact absurd hmass (not_lt.2 (le_trans hbig.le hchain))

/-- **SUV Theorem 118, converse direction (§5.8, pp. 173-174), in its corrected
form.**  If the largest effectively `α`-null set exists and `α ≤ 1`, then `α` is
lower semicomputable.  See above for why `α ≤ 1` cannot be dropped. -/
theorem isLowerSemicomputable_of_exists_largest_isEffectiveAlphaNull
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ∃ A : Set CantorSeq, IsEffectiveAlphaNull α A ∧
      ∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → B ⊆ A) :
    IsLowerSemicomputableENNReal (ENNReal.ofReal α) := by
  rw [← isLowerSemicomputableReal_iff_ofReal hα.le, isLowerSemicomputableReal_iff_re_lt]
  obtain ⟨A, ⟨I, hIcomp, hI⟩, hmax⟩ := h
  have hJcomp : Computable (I ((1 : ℚ) / 8)) :=
    hIcomp.comp (Computable.const ((1 : ℚ) / 8)) Computable.id
  have hspec := hI ((1 : ℚ) / 8) (by norm_num)
  refine ⟨alphaCertEnum (I ((1 : ℚ) / 8)), computable_alphaCertEnum hJcomp, fun r => ⟨?_, ?_⟩⟩
  · intro hr
    by_cases hr0 : 0 < r
    · obtain ⟨N, hN⟩ := exists_alphaCertSum_gt α hα1 A hmax (I ((1 : ℚ) / 8)) hspec.1 hr0 hr
      refine ⟨Nat.pair (ratCode r) N, alphaCertEnum_of_cert (I ((1 : ℚ) / 8)) N hN⟩
    · push_neg at hr0
      exact ⟨Nat.pair (ratCode r) 0, alphaCertEnum_of_nonpos (I ((1 : ℚ) / 8)) r hr0⟩
  · rintro ⟨i, hi⟩
    by_cases hr0 : 0 < r
    swap
    · push_neg at hr0
      exact lt_of_le_of_lt (by exact_mod_cast hr0) hα
    have hcert := alphaCertSum_gt_of_alphaCertEnum hi hr0
    exact lt_alpha_of_alphaCertSum α (I ((1 : ℚ) / 8)) hspec.2 hcert

/-- **SUV Theorem 118 (§5.8, pp. 173-174), corrected form.**  For `0 < α ≤ 1` the
largest effectively `α`-null set exists if and only if `α` is lower
semicomputable.  The forward direction is `Dimension/Basic.lean`'s
`exists_largest_isEffectiveAlphaNull_of_isLowerSemicomputable` (which holds for
every `α > 0`); the converse needs `α ≤ 1`, since for `α > 1` the whole space is
effectively `α`-null. -/
theorem exists_largest_isEffectiveAlphaNull_iff_isLowerSemicomputable
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∃ A : Set CantorSeq, IsEffectiveAlphaNull α A ∧
        ∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → B ⊆ A) ↔
      IsLowerSemicomputableENNReal (ENNReal.ofReal α) :=
  ⟨isLowerSemicomputable_of_exists_largest_isEffectiveAlphaNull α hα hα1,
    exists_largest_isEffectiveAlphaNull_of_isLowerSemicomputable α hα⟩

alias isLowerSemicomputable_of_exists_largest_isEffectiveAlphaNull_of_le_one :=
  isLowerSemicomputable_of_exists_largest_isEffectiveAlphaNull

alias exists_largest_isEffectiveAlphaNull_iff_isLowerSemicomputable_of_le_one :=
  exists_largest_isEffectiveAlphaNull_iff_isLowerSemicomputable

end Kolmogorov
