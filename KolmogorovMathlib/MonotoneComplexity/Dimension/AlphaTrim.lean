/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.AlgorithmicRandomness.Trim
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveOpenNormalForm
import KolmogorovMathlib.MonotoneComplexity.CylinderMass
import KolmogorovMathlib.MonotoneComplexity.Dimension.Counting

/-!
# The `α`-weighted trimming engine (SUV §5.8, p. 173, proof of Theorem 117)

> "The proof goes in the same way as for effectively null (=1-null) sets
> (Chapter 3). … we can enumerate all effectively `α`-null sets (or, better, the
> algorithms that serve these sets) by enumerating all algorithms and changing
> them when too large intervals are generated." (p. 173)

"Changing them when too large intervals are generated" is Chapter 3's trimming
(`AlgorithmicRandomness/Trim.lean`).  Chapter 3's engine is hard-wired to the
weight `μ(Ω_x)` of a computable measure; this module reruns the same recursion
for the `α`-weight `μ(Ω_x)^α = 2^{-α l(x)}`.

## How the `α`-weight is made effectively comparable

`2^{-α l}` is an algebraic irrational, and Chapter 3's recursion needs *integer*
approximations of the weights.  Instead of approximating `2^{-α l}` itself (which
would require `q`-th roots for `α = p/q`), the engine is run with the **dyadic
floor weight**

`alphaFloorMass α x = 2^{-⌊α l(x)⌋}`,

which sandwiches the true weight within a factor of two,

`μ(Ω_x)^α ≤ alphaFloorMass α x ≤ 2 · μ(Ω_x)^α`

(`intervalAlphaMass_le_alphaFloorMass`, `alphaFloorMass_le_two_mul`), and whose
Chapter-3 dyadic approximation is *exact*: `alphaApprox α x s = 2^{s-⌊α l(x)⌋}`
is a power of two, exactly as `uniformApprox` is for the uniform measure.  The
factor two is absorbed by one extra halving of the "nothing is discarded"
threshold, which is why `exists_computable₂_trim_alphaCover_dyadic` has `2^{-n}`
in the bound and `2^{-(n+3)}` in the hypothesis where Chapter 3's
`trimEnum_eq_self_of_tsum_le` has `2^{-(n+2)}`.

## Contents

* `alphaFloor`, `alphaFloorMass`, `alphaApprox` — the dyadic floor weight and its
  exact integer approximation, with computability.
* A weight-generic copy of Chapter 3's trimming bounds
  (`tsum_trimEnum_weight_le`, `trimEnum_eq_self_of_tsum_weight_le`): the proofs
  of `Trim.lean` never use that `cantorMass μ` comes from a measure, only that it
  is an `ℝ≥0∞`-valued function of a string with a two-sided dyadic approximation,
  so they are reproduced here for an arbitrary weight `W`.
* `exists_computable₂_trim_alphaCover_dyadic` and
  `exists_computable₂_trim_alphaCover_rat` — the engine itself.  A gap between
  the threshold in the bound and the threshold in the hypothesis is unavoidable
  on this route, which is why both variants carry two thresholds.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## The dyadic floor weight `2^{-⌊α l⌋}` -/

/-- `⌊α · l⌋` for a positive rational `α`, computed by natural division. -/
def alphaFloor (α : ℚ) (l : ℕ) : ℕ := α.num.toNat * l / α.den

/-- The dyadic weight `2^{-⌊α l(x)⌋}` used to run Chapter 3's trimming recursion
at the exponent `α`. -/
noncomputable def alphaFloorMass (α : ℚ) (x : BitString) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ alphaFloor α x.length

/-- The extended real `1/2` is at most `1`. -/
lemma inv_two_le_one : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)

/-- Every power `2 ^ (-j)` is at most `1`. -/
lemma inv_two_pow_le_one (j : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ j ≤ 1 := by
  calc (2 : ℝ≥0∞)⁻¹ ^ j ≤ 1 ^ j := by gcongr; exact inv_two_le_one
    _ = 1 := one_pow _

/-- For positive `α` the value `alphaFloor α l` is the integer part of `α * l`. -/
lemma alphaFloor_spec (α : ℚ) (hα : 0 < α) (l : ℕ) :
    ((alphaFloor α l : ℕ) : ℝ) ≤ (α : ℝ) * l ∧ (α : ℝ) * l < ((alphaFloor α l : ℕ) : ℝ) + 1 := by
  have hD : 0 < α.den := α.pos
  have hDR : (0 : ℝ) < (α.den : ℝ) := by exact_mod_cast hD
  have hnum : ((α.num.toNat : ℕ) : ℤ) = α.num := Int.toNat_of_nonneg (Rat.num_pos.2 hα).le
  have hnumR : ((α.num.toNat : ℕ) : ℝ) = (α.num : ℝ) := by exact_mod_cast hnum
  have hcast : (α : ℝ) * l = ((α.num.toNat * l : ℕ) : ℝ) / (α.den : ℝ) := by
    have hmul : ((α.num.toNat * l : ℕ) : ℝ) = (α.num : ℝ) * (l : ℝ) := by
      push_cast [hnumR]
      ring
    rw [hmul, Rat.cast_def]
    field_simp
  have h1 : alphaFloor α l * α.den ≤ α.num.toNat * l := Nat.div_mul_le_self _ _
  have h2 : α.num.toNat * l < (alphaFloor α l + 1) * α.den :=
    (Nat.div_lt_iff_lt_mul hD).1 (Nat.lt_succ_self _)
  constructor
  · rw [hcast, le_div_iff₀ hDR]
    calc ((alphaFloor α l : ℕ) : ℝ) * (α.den : ℝ) = ((alphaFloor α l * α.den : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ ((α.num.toNat * l : ℕ) : ℝ) := by exact_mod_cast h1
  · rw [hcast, div_lt_iff₀ hDR]
    calc ((α.num.toNat * l : ℕ) : ℝ) < (((alphaFloor α l + 1) * α.den : ℕ) : ℝ) := by
          exact_mod_cast h2
      _ = (((alphaFloor α l : ℕ) : ℝ) + 1) * (α.den : ℝ) := by push_cast; ring

/-- The true `α`-weight is below the dyadic floor weight. -/
lemma intervalAlphaMass_le_alphaFloorMass (α : ℚ) (hα : 0 < α) (x : BitString) :
    uniformMeasure (cantorCylinder x) ^ (α : ℝ) ≤ alphaFloorMass α x := by
  rw [uniformMeasure_cantorCylinder, alphaFloorMass,
    ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) x.length, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) (alphaFloor α x.length)]
  refine ENNReal.rpow_le_rpow_of_exponent_ge inv_two_le_one ?_
  have := (alphaFloor_spec α hα x.length).1
  linarith [this]

/-- The dyadic floor weight overshoots the true `α`-weight by at most a factor
of two. -/
lemma alphaFloorMass_le_two_mul (α : ℚ) (hα : 0 < α) (x : BitString) :
    alphaFloorMass α x ≤ 2 * uniformMeasure (cantorCylinder x) ^ (α : ℝ) := by
  have hne : ((2 : ℝ≥0∞)⁻¹) ≠ 0 := ENNReal.inv_ne_zero.2 (by norm_num)
  have htop : ((2 : ℝ≥0∞)⁻¹) ≠ ⊤ := ENNReal.inv_ne_top.2 (by norm_num)
  rw [uniformMeasure_cantorCylinder, alphaFloorMass,
    ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) x.length, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) (alphaFloor α x.length)]
  have hstep : ((2 : ℝ≥0∞)⁻¹) ^ (((x.length : ℕ) : ℝ) * (α : ℝ) - 1)
      = 2 * ((2 : ℝ≥0∞)⁻¹) ^ (((x.length : ℕ) : ℝ) * (α : ℝ)) := by
    rw [ENNReal.rpow_sub _ _ hne htop, ENNReal.rpow_one, div_eq_mul_inv, inv_inv, mul_comm]
  calc ((2 : ℝ≥0∞)⁻¹) ^ ((alphaFloor α x.length : ℕ) : ℝ)
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ (((x.length : ℕ) : ℝ) * (α : ℝ) - 1) := by
        refine ENNReal.rpow_le_rpow_of_exponent_ge inv_two_le_one ?_
        have := (alphaFloor_spec α hα x.length).2
        linarith [this]
    _ = 2 * ((2 : ℝ≥0∞)⁻¹) ^ (((x.length : ℕ) : ℝ) * (α : ℝ)) := hstep

/-! ## The exact dyadic approximation of the floor weight -/

/-- The Chapter-3 dyadic approximation of `alphaFloorMass`; it is *exact* as soon
as the precision `s` exceeds `⌊α l(x)⌋`, exactly as `uniformApprox` is for the
uniform measure. -/
def alphaApprox (α : ℚ) (x : BitString) (s : ℕ) : ℕ :=
  if alphaFloor α x.length ≤ s then 2 ^ (s - alphaFloor α x.length) else 0

/-- The dyadic approximation of the `α`-scaled mass is computable in the string and the stage. -/
lemma computable₂_alphaApprox (α : ℚ) : Computable₂ (alphaApprox α) := by
  have hfloor : Primrec (fun p : BitString × ℕ => alphaFloor α p.1.length) :=
    Primrec.nat_div.comp
      (Primrec.nat_mul.comp (Primrec.const α.num.toNat)
        (Primrec.list_length.comp Primrec.fst))
      (Primrec.const α.den)
  have hle : PrimrecPred (fun p : BitString × ℕ => alphaFloor α p.1.length ≤ p.2) :=
    PrimrecRel.comp Primrec.nat_le hfloor Primrec.snd
  have hpow : Primrec (fun p : BitString × ℕ => 2 ^ (p.2 - alphaFloor α p.1.length)) :=
    nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.snd hfloor)
  exact (Primrec.ite hle hpow (Primrec.const 0)).to_comp

/-- The stage-`s` approximation of the `α`-scaled mass is within `2 ^ (-s)` of the true value on
both
sides. -/
lemma alphaApprox_bound (α : ℚ) (x : BitString) (s : ℕ) :
    dyadicValue (alphaApprox α x s) s ≤ alphaFloorMass α x + dyadicValue 1 s ∧
      alphaFloorMass α x ≤ dyadicValue (alphaApprox α x s) s + dyadicValue 1 s := by
  unfold alphaApprox alphaFloorMass
  by_cases h : alphaFloor α x.length ≤ s
  · rw [if_pos h, dyadicValue_two_pow_sub h]
    exact ⟨le_self_add, le_self_add⟩
  · rw [if_neg h]
    have hs : s ≤ alphaFloor α x.length := le_of_not_ge h
    have hsplit : (2 : ℝ≥0∞)⁻¹ ^ alphaFloor α x.length
        ≤ (2 : ℝ≥0∞)⁻¹ ^ s := by
      rw [show alphaFloor α x.length = s + (alphaFloor α x.length - s) from
        (Nat.add_sub_cancel' hs).symm, pow_add]
      calc (2 : ℝ≥0∞)⁻¹ ^ s * (2 : ℝ≥0∞)⁻¹ ^ (alphaFloor α x.length - s)
          ≤ (2 : ℝ≥0∞)⁻¹ ^ s * 1 := by gcongr; exact inv_two_pow_le_one _
        _ = (2 : ℝ≥0∞)⁻¹ ^ s := mul_one _
    have h0 : dyadicValue 0 s = 0 := by simp [dyadicValue]
    refine ⟨by rw [h0]; exact zero_le, ?_⟩
    rw [h0, zero_add, dyadicValue_one_eq_inv_two_pow']
    exact hsplit

/-! ## Chapter 3's trimming bounds for an arbitrary weight -/

section GeneralWeight

variable {W : BitString → ℝ≥0∞} {a : BitString → ℕ → ℕ}

/-- The per-index bound of `Trim.lean`'s `measure_coverSet_trimEnum_le`, for an
arbitrary weight `W`: the proof there never uses that the weight is a measure. -/
lemma weight_trimEnum_le
    (ha : ∀ x s, dyadicValue (a x s) s ≤ W x + dyadicValue 1 s ∧
      W x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (e : ℕ → Option BitString) (n k : ℕ) :
    (trimEnum e (trimWeight a e n) k).elim 0 W
      ≤ trimTerm (trimWeight a e n) n k + (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) := by
  set w := trimWeight a e n with hw
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
      rw [dyadicValue_eq_mul_inv_pow, dyadicValue_one_eq_inv_two_pow'] at hub
      rw [hwk]
      exact hub

/-- The trimmed enumeration has total `W`-weight at most `2^{-n}`. -/
theorem tsum_trimEnum_weight_le
    (ha : ∀ x s, dyadicValue (a x s) s ≤ W x + dyadicValue 1 s ∧
      W x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (e : ℕ → Option BitString) (n : ℕ) :
    (∑' k, (trimEnum e (trimWeight a e n) k).elim 0 W) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  set w := trimWeight a e n with hw
  refine (ENNReal.tsum_le_tsum (fun k => weight_trimEnum_le ha e n k)).trans ?_
  rw [ENNReal.tsum_add]
  have hidx : ∀ j : ℕ, n + 2 + j + 1 = n + j + 3 := fun j => by ring
  have hgeom : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3) = (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
    have h := tsum_inv_two_pow_shift (n + 2)
    calc ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
        = ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + 2 + k + 1) := tsum_congr fun k => by rw [hidx k]
      _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := h
  rw [hgeom]
  have hbound : ∑' j, trimTerm w n j + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
    gcongr
    exact tsum_trimTerm_le w n
  refine hbound.trans ?_
  have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2)
      = (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) := by
    rw [pow_succ, pow_succ, pow_succ]
    ring
  rw [hsplit]
  have hle : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ 1 := by
    have h1 : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := by
      calc (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ 1 * (2 : ℝ≥0∞)⁻¹ := by
            gcongr
            exact inv_two_le_one
        _ = (2 : ℝ≥0∞)⁻¹ := one_mul _
    calc (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by gcongr
      _ = 1 := ENNReal.inv_two_add_inv_two
  calc (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ n * 1 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := mul_one _

/-- The integer weight assigned to the `j`-th cover element overestimates its true weight by at most
`2 ^ (-(n + j + 3))`. -/
lemma trimWeight_mul_le_weight
    (ha : ∀ x s, dyadicValue (a x s) s ≤ W x + dyadicValue 1 s ∧
      W x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (e : ℕ → Option BitString) (n j : ℕ) :
    (trimWeight a e n j : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)
      ≤ (e j).elim 0 W + (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
  cases hej : e j with
  | none => simp [trimWeight, hej]
  | some u =>
    have hwj : trimWeight a e n j = a u (n + j + 3) := by
      simp [trimWeight, hej]
    have hlb := (ha u (n + j + 3)).1
    rw [dyadicValue_eq_mul_inv_pow, dyadicValue_one_eq_inv_two_pow'] at hlb
    rw [hwj]
    simpa using hlb

/-- If the accumulated weight up to step `k` stays within the budget then the trimmer accepts step
`k`, and the bound propagates to step `k + 1`. -/
lemma trimAccept_of_partial_le_weight
    (ha : ∀ x s, dyadicValue (a x s) s ≤ W x + dyadicValue 1 s ∧
      W x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {e : ℕ → Option BitString} {n : ℕ}
    (hsmall : (∑' j, (e j).elim 0 W) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) {k : ℕ}
    (hpart : (trimPartial (trimWeight a e n) k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
      ≤ ∑ j ∈ Finset.range k, (e j).elim 0 W
        + ∑ j ∈ Finset.range k, (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)) :
    trimAccept (trimWeight a e n) k = true ∧
      ((2 * trimPartial (trimWeight a e n) k + trimWeight a e n k : ℕ) : ℝ≥0∞)
        * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
        ≤ ∑ j ∈ Finset.range (k + 1), (e j).elim 0 W
          + ∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
  set w := trimWeight a e n with hw
  have hstep : ((2 * trimPartial w k + w k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 3)
      ≤ ∑ j ∈ Finset.range (k + 1), (e j).elim 0 W
        + ∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
    rw [trim_step_value, Finset.sum_range_succ, Finset.sum_range_succ, add_add_add_comm]
    exact add_le_add hpart (trimWeight_mul_le_weight ha e n k)
  refine ⟨?_, hstep⟩
  rw [trimAccept_iff]
  refine nat_le_of_mul_inv_two_pow_le (s := n + k + 3) ?_
  refine hstep.trans ?_
  have hmass : (∑ j ∈ Finset.range (k + 1), (e j).elim 0 W)
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
  calc ∑ j ∈ Finset.range (k + 1), (e j).elim 0 W
        + ∑ j ∈ Finset.range (k + 1), (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2) + (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := add_le_add hmass hslack
    _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := hsum2

/-- The accumulated integer weight after `k` steps is bounded by the true weight of the first `k`
cover elements plus the accumulated rounding errors. -/
lemma trimPartial_mul_le_sum_weight
    (ha : ∀ x s, dyadicValue (a x s) s ≤ W x + dyadicValue 1 s ∧
      W x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {e : ℕ → Option BitString} {n : ℕ}
    (hsmall : (∑' j, (e j).elim 0 W) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) (k : ℕ) :
    (trimPartial (trimWeight a e n) k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + k + 2)
      ≤ ∑ j ∈ Finset.range k, (e j).elim 0 W
        + ∑ j ∈ Finset.range k, (2 : ℝ≥0∞)⁻¹ ^ (n + j + 3) := by
  induction k with
  | zero => simp [trimPartial_zero]
  | succ k ih =>
    obtain ⟨hacc, hstep⟩ := trimAccept_of_partial_le_weight ha hsmall ih
    rw [trimPartial_succ_of_accept hacc, show n + (k + 1) + 2 = n + k + 3 by ring]
    exact hstep

/-- If the total `W`-weight is at most `2^{-(n+2)}`, the trimming discards
nothing (`Trim.lean`'s `trimEnum_eq_self_of_tsum_le` for an arbitrary weight). -/
theorem trimEnum_eq_self_of_tsum_weight_le
    (ha : ∀ x s, dyadicValue (a x s) s ≤ W x + dyadicValue 1 s ∧
      W x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {e : ℕ → Option BitString} {n : ℕ}
    (hsmall : (∑' j, (e j).elim 0 W) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) (k : ℕ) :
    trimEnum e (trimWeight a e n) k = e k := by
  have hacc := (trimAccept_of_partial_le_weight ha hsmall
    (trimPartial_mul_le_sum_weight ha hsmall k)).1
  unfold trimEnum
  rw [hacc, cond_true]

end GeneralWeight

/-! ## The `α`-trimming of a single enumeration -/

/-- The `α`-weight of a trimmed enumeration is at most `2^{-n}`. -/
lemma tsum_alphaTrim_le (α : ℚ) (hα : 0 < α) (e : ℕ → Option BitString) (n : ℕ) :
    (∑' k, (trimEnum e (trimWeight (alphaApprox α) e n) k).elim 0
        (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ))) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hmono : ∀ o : Option BitString,
      o.elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ))
        ≤ o.elim 0 (alphaFloorMass α) := by
    intro o
    cases o with
    | none => simp
    | some x => exact intervalAlphaMass_le_alphaFloorMass α hα x
  refine (ENNReal.tsum_le_tsum fun k => hmono _).trans ?_
  exact tsum_trimEnum_weight_le (alphaApprox_bound α) e n

/-- An enumeration whose `α`-weight is at most `2^{-(n+3)}` is not trimmed at all. -/
lemma alphaTrim_eq_self (α : ℚ) (hα : 0 < α) {e : ℕ → Option BitString} {n : ℕ}
    (h : (∑' k, (e k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 3)) (k : ℕ) :
    trimEnum e (trimWeight (alphaApprox α) e n) k = e k := by
  have hle2 : ∀ o : Option BitString,
      o.elim 0 (alphaFloorMass α)
        ≤ 2 * o.elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)) := by
    intro o
    cases o with
    | none => simp
    | some x => exact alphaFloorMass_le_two_mul α hα x
  refine trimEnum_eq_self_of_tsum_weight_le (alphaApprox_bound α) ?_ k
  calc (∑' j, (e j).elim 0 (alphaFloorMass α))
      ≤ ∑' j, 2 * (e j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)) :=
        ENNReal.tsum_le_tsum fun j => hle2 _
    _ = 2 * ∑' j, (e j).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)) :=
        ENNReal.tsum_mul_left
    _ ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ (n + 3) := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
        have h2 := two_mul_inv_two_pow_succ (n + 2)
        rw [show n + 2 + 1 = n + 3 from by ring] at h2
        exact h2

/-! ## The `α`-weighted trimming engine -/

/-- **The `α`-weighted trimming engine**, the `α`-analogue of `Trim.lean`'s
`measure_iUnion_trimEnum_le` (the bound) together with `trimEnum_eq_self_of_tsum_le`
("nothing is discarded"), which is what the proof of SUV Theorem 117 (p. 173)
reuses from Chapter 3: a uniformly computable family `E` of candidate covers is
trimmed, uniformly and computably, into a sub-family whose `α`-weights obey
`2^{-n}`, without touching a row whose `α`-weight already obeys `2^{-(n+3)}`.

The thresholds are dyadic, exactly as in Chapter 3, and the gap between `2^{-n}`
and `2^{-(n+3)}` is one power of two larger than Chapter 3's gap because the
recursion is run on the dyadic floor weight `2^{-⌊α l⌋}`, which overshoots the
true `α`-weight by at most a factor of two.  A gap between the two thresholds is
*unavoidable* on this route. -/
theorem exists_computable₂_trim_alphaCover_dyadic (α : ℚ) (hα : 0 < α)
    (E : ℕ → ℕ → Option BitString) (hE : Computable₂ E) (n : ℕ) :
    ∃ T : ℕ → ℕ → Option BitString, Computable₂ T ∧
      (∀ m k, T m k = E m k ∨ T m k = none) ∧
      (∀ m, (∑' k, (T m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ n) ∧
      (∀ m, (∑' k, (E m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
          ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 3) →
        ∀ k, T m k = E m k) := by
  refine ⟨fun m k => trimEnum (E m) (trimWeight (alphaApprox α) (E m) n) k, ?_, ?_, ?_, ?_⟩
  · exact computable_trimEnum hE
      (computable_trimWeight (computable₂_alphaApprox α) hE (Computable.const n))
  · intro m k
    by_cases hacc : trimAccept (trimWeight (alphaApprox α) (E m) n) k = true
    · exact Or.inl (by simp [trimEnum, hacc])
    · simp only [Bool.not_eq_true] at hacc
      exact Or.inr (by simp [trimEnum, hacc])
  · intro m
    exact tsum_alphaTrim_le α hα (E m) n
  · intro m hm k
    exact alphaTrim_eq_self α hα hm k

/-- The rational-threshold form of the engine: the bound is `≤ β`, and the
"nothing is discarded" hypothesis is the explicit dyadic threshold
`2^{-(den β + 3)} ≤ β/8`. -/
theorem exists_computable₂_trim_alphaCover_rat (α : ℚ) (hα : 0 < α)
    (E : ℕ → ℕ → Option BitString) (hE : Computable₂ E) (β : ℚ) (hβ : 0 < β) :
    ∃ T : ℕ → ℕ → Option BitString, Computable₂ T ∧
      (∀ m k, T m k = E m k ∨ T m k = none) ∧
      (∀ m, (∑' k, (T m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
        ≤ ENNReal.ofReal (β : ℝ)) ∧
      (∀ m, (∑' k, (E m k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
          ≤ (2 : ℝ≥0∞)⁻¹ ^ (β.den + 3) →
        ∀ k, T m k = E m k) := by
  obtain ⟨T, hTc, hTsub, hTbound, hTself⟩ :=
    exists_computable₂_trim_alphaCover_dyadic α hα E hE β.den
  refine ⟨T, hTc, hTsub, fun m => (hTbound m).trans ?_, hTself⟩
  rw [← dyadicValue_one_eq_inv_two_pow']
  exact dyadicValue_den_le_rat hβ

end Kolmogorov
