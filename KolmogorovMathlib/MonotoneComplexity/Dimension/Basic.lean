/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.CylinderMass
import KolmogorovMathlib.MonotoneComplexity.Dimension.Counting
import KolmogorovMathlib.MonotoneComplexity.Dimension.AlphaTrim
import KolmogorovMathlib.MonotoneComplexity.Dimension.UniversalAlphaTest
import KolmogorovMathlib.MonotoneComplexity.Dimension.PostponeTrim
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof

/-!
# Effective Hausdorff dimension: `α`-null sets (SUV §5.8, pp. 172-175)

This module renders the definitions of SUV §5.8 and the two existence theorems
about largest effectively `α`-null sets.

## Source definitions

* (p. 172) A set `A` is an **`α`-null set** (`α > 0` real) if for every `ε > 0`
  there is a sequence of intervals `I_k` covering `A` with `∑_k μ(I_k)^α < ε`.
  Intervals are the cylinders `Ω_x`, and `μ(Ω_x) = 2^{-l(x)}` is the uniform
  measure (`intervalAlphaMass`).
* (p. 173) `A ⊆ Ω` is an **effective `α`-null set** if there is an algorithm
  that, for any given `ε > 0`, enumerates a set `I_0, I_1, I_2, …` of intervals
  covering `A` with `∑ (μ(I_k))^α < ε`.
* (p. 174) The **effective Hausdorff dimension** of `A ⊆ Ω` is the infimum of
  the `α` for which `A` is an effective `α`-null set; it lies in `[0,1]`.

## Rendering decisions (do not change without re-reading the source)

* The `ε` of the source is a *rational* parameter of one algorithm, matching
  "for any given `ε > 0`" literally; the enumeration is `Computable₂` jointly in
  `ε` and the index, which is the source's "there exists an algorithm that, for
  any given `ε`, enumerates …".  The Chapter 3 dyadic normal form
  (`IsEffectivelyNull`, `ε = 2^{-n}`) is the same notion at `α = 1`; the
  equivalence is `isEffectiveAlphaNull_one_iff_isEffectivelyNull_uniform`.
* The interval weight is *literally* `μ(Ω_x) ^ α` (`ENNReal.rpow`), not the
  arithmetically simplified `2^{-α l(x)}`; `intervalAlphaMass_eq_inv_two_pow`
  records the simplification.
* `effectiveHausdorffDim` is a total `sInf` over the reals, so it is a `def`
  with no `sorry`; the source facts about it are theorem leaves.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ## `α`-powers of interval measures -/

/-- The `α`-weight `μ(Ω_x)^α` of the interval `Ω_x`, where `μ` is the uniform
measure on Cantor space (SUV §5.8, p. 172: "the measure of the interval `Ω_x`
equals `2^{-l(x)}`", and the covers are weighted by `μ(I_k)^α`). -/
noncomputable def intervalAlphaMass (α : ℝ) (x : BitString) : ℝ≥0∞ :=
  uniformMeasure (cantorCylinder x) ^ α

/-- The simplified form `μ(Ω_x)^α = (2^{-l(x)})^α` of `intervalAlphaMass`. -/
lemma intervalAlphaMass_eq_inv_two_pow (α : ℝ) (x : BitString) :
    intervalAlphaMass α x = ((2 : ℝ≥0∞)⁻¹ ^ x.length) ^ α := by
  rw [intervalAlphaMass, uniformMeasure_cantorCylinder]

/-- The `α`-weight of an optional interval; a missing interval contributes `0`.
This is the summand of the source's `∑ (μ(I_k))^α`, in the partial-enumeration
presentation of covers used throughout Chapter 3. -/
noncomputable def coverAlphaMass (α : ℝ) (o : Option BitString) : ℝ≥0∞ :=
  o.elim 0 (intervalAlphaMass α)

/-- A missing cover element contributes no `α`-mass. -/
@[simp] lemma coverAlphaMass_none (α : ℝ) : coverAlphaMass α none = 0 := rfl

/-- A present cover element contributes the `α`-mass of its interval. -/
@[simp] lemma coverAlphaMass_some (α : ℝ) (x : BitString) :
    coverAlphaMass α (some x) = intervalAlphaMass α x := rfl

/-! ## `α`-null sets, classical and effective -/

/-- **SUV §5.8, p. 172.** A set `A ⊆ Ω` is an *`α`-null set* if for every
`ε > 0` there is a sequence of intervals covering `A` whose `α`-weights sum to
less than `ε`.  This is the classical (non-effective) notion; it is recorded
because the source's remarks (1)-(4) and the classical Hausdorff dimension are
phrased with it. -/
def IsAlphaNull (α : ℝ) (A : Set CantorSeq) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ I : ℕ → Option BitString,
    A ⊆ (⋃ k, (I k).elim ∅ cantorCylinder) ∧
      (∑' k, coverAlphaMass α (I k)) < ENNReal.ofReal ε

/-- **SUV §5.8, p. 173.** A set `A ⊆ Ω` is an *effective `α`-null set* if there
is an algorithm that, for any given rational `ε > 0`, enumerates a sequence of
intervals `I_0, I_1, I_2, …` covering `A` with `∑ (μ(I_k))^α < ε`.

The single `Computable₂` enumerator is the source's "there exists an algorithm
that, for any given `ε > 0`, enumerates …": one algorithm, uniform in `ε`. -/
def IsEffectiveAlphaNull (α : ℝ) (A : Set CantorSeq) : Prop :=
  ∃ I : ℚ → ℕ → Option BitString, Computable₂ I ∧ ∀ ε : ℚ, 0 < ε →
    A ⊆ (⋃ k, (I ε k).elim ∅ cantorCylinder) ∧
      (∑' k, coverAlphaMass α (I ε k)) < ENNReal.ofReal (ε : ℝ)

/-- **SUV §5.8, p. 173** (monotonicity in the set: "the property is monotone …
if `A` decreases").  A subset of an effective `α`-null set is an effective
`α`-null set; the same enumerator works. -/
theorem IsEffectiveAlphaNull.mono_set {α : ℝ} {A B : Set CantorSeq}
    (h : IsEffectiveAlphaNull α B) (hAB : A ⊆ B) : IsEffectiveAlphaNull α A := by
  obtain ⟨I, hIcomp, hI⟩ := h
  exact ⟨I, hIcomp, fun ε hε => ⟨hAB.trans (hI ε hε).1, (hI ε hε).2⟩⟩

/-- Every interval has measure at most `1`: `μ(Ω_x) = 2^{-l(x)} ≤ 1`. -/
lemma uniformMeasure_cantorCylinder_le_one (x : BitString) :
    uniformMeasure (cantorCylinder x) ≤ 1 := by
  rw [uniformMeasure_cantorCylinder]
  calc (2 : ℝ≥0∞)⁻¹ ^ x.length ≤ 1 ^ x.length := by
        gcongr
        exact ENNReal.inv_le_one.2 (by norm_num)
    _ = 1 := one_pow _

/-- The `α`-weight of an interval decreases as `α` grows (SUV §5.8, p. 172,
remark (4): "the measure `μ(I)` of each interval `I` does not exceed `1` and
therefore `μ(I)^{α'} ≤ μ(I)^α`"). -/
lemma intervalAlphaMass_mono {α α' : ℝ} (hαα' : α ≤ α') (x : BitString) :
    intervalAlphaMass α' x ≤ intervalAlphaMass α x :=
  ENNReal.rpow_le_rpow_of_exponent_ge (uniformMeasure_cantorCylinder_le_one x) hαα'

/-- The cover weight of an option decreases as `α` grows. -/
lemma coverAlphaMass_mono {α α' : ℝ} (hαα' : α ≤ α') (o : Option BitString) :
    coverAlphaMass α' o ≤ coverAlphaMass α o := by
  cases o with
  | none => simp
  | some x => exact intervalAlphaMass_mono hαα' x

/-- **SUV §5.8, p. 173** (monotonicity in the exponent: "the property is
monotone (it remains true if `α` increases …)").  Uses `μ(I) ≤ 1`, so that
`μ(I)^{α'} ≤ μ(I)^α` for `α ≤ α'`. -/
theorem IsEffectiveAlphaNull.mono_alpha {α α' : ℝ} {A : Set CantorSeq}
    (h : IsEffectiveAlphaNull α A) (hα : 0 < α) (hαα' : α ≤ α') :
    IsEffectiveAlphaNull α' A := by
  have _ := hα
  obtain ⟨I, hIcomp, hI⟩ := h
  refine ⟨I, hIcomp, fun ε hε => ⟨(hI ε hε).1, lt_of_le_of_lt ?_ (hI ε hε).2⟩⟩
  exact ENNReal.tsum_le_tsum fun k => coverAlphaMass_mono hαα' (I ε k)

/-! ## Remark (3) of p. 172: for `α > 1` every set is an effective `α`-null set -/

/-- The cover weight in the raw form used by `Dimension/Counting.lean`. -/
lemma coverAlphaMass_eq_elim (α : ℝ) (o : Option BitString) :
    coverAlphaMass α o = o.elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) := rfl

/-- **SUV §5.8, p. 172, remark (3)**, in the *effective* form, for the exponents
`α = (m+1)/m`.

> "For `α > 1` any subset `A ⊆ Ω` is an `α`-null set.  Indeed, one can cover `A`
> by `2^n` intervals that correspond to `2^n` strings of length `n`, and the sum
> of their `α`-measures tends to `0` as `n → ∞`."  (p. 172)

Effectivity needs the length `n` to be computable from `ε`, which is why the
exponent is taken in the special form `(m+1)/m`: the cover by all strings of
length `n = (den ε + 1)·m` then has `α`-weight exactly
`2^n · (2^{-n})^{(m+1)/m} = 2^{-(den ε + 1)}`, which is below `ε` because
`2^{-den ε} ≤ ε` for every positive rational `ε`
(`dyadicValue_den_le_rat`).  These exponents are cofinal in `(1, ∞)` from
above, which is all that `isEffectiveAlphaNull_of_one_lt` needs. -/
theorem isEffectiveAlphaNull_succ_div (m : ℕ) (hm : 0 < m) (A : Set CantorSeq) :
    IsEffectiveAlphaNull (((m : ℝ) + 1) / (m : ℝ)) A := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  refine ⟨fun ε k => levelEnum ((ε.den + 1) * m) k, ?_, fun ε hε => ⟨?_, ?_⟩⟩
  · have hlen : Computable (fun p : ℚ × ℕ => (p.1.den + 1) * m) :=
      Primrec.nat_mul.to_comp.comp
        (Primrec.nat_add.to_comp.comp (computable_ratDen.comp Computable.fst)
          (Computable.const 1))
        (Computable.const m)
    exact computable₂_levelEnum.comp hlen Computable.snd
  · exact subset_iUnion_levelEnum _ A
  · have hsum : (∑' k, coverAlphaMass (((m : ℝ) + 1) / (m : ℝ))
          (levelEnum ((ε.den + 1) * m) k))
        = (2 : ℝ≥0∞) ^ ((ε.den + 1) * m)
          * (((2 : ℝ≥0∞)⁻¹ ^ ((ε.den + 1) * m)) ^ (((m : ℝ) + 1) / (m : ℝ))) := by
      simp only [coverAlphaMass_eq_elim]
      exact tsum_levelEnum_rpow _ _
    have hcast : (((ε.den + 1) * m : ℕ) : ℝ) * (((m : ℝ) + 1) / (m : ℝ))
        = (((ε.den + 1) * (m + 1) : ℕ) : ℝ) := by
      push_cast
      field_simp
    have hexp : (((2 : ℝ≥0∞)⁻¹ ^ ((ε.den + 1) * m)) ^ (((m : ℝ) + 1) / (m : ℝ)))
        = (2 : ℝ≥0∞)⁻¹ ^ ((ε.den + 1) * (m + 1)) := by
      rw [← ENNReal.rpow_natCast ((2 : ℝ≥0∞)⁻¹) ((ε.den + 1) * m), ← ENNReal.rpow_mul, hcast]
      exact ENNReal.rpow_natCast _ _
    have hpow : (2 : ℝ≥0∞) ^ ((ε.den + 1) * m) * (2 : ℝ≥0∞)⁻¹ ^ ((ε.den + 1) * m) = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow]
    have hcancel : (2 : ℝ≥0∞) ^ ((ε.den + 1) * m)
          * (2 : ℝ≥0∞)⁻¹ ^ ((ε.den + 1) * (m + 1)) = (2 : ℝ≥0∞)⁻¹ ^ (ε.den + 1) := by
      rw [show (ε.den + 1) * (m + 1) = (ε.den + 1) * m + (ε.den + 1) by ring, pow_add,
        ← mul_assoc, hpow, one_mul]
    rw [hsum, hexp, hcancel]
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

/-- **SUV §5.8, p. 172, remark (3)**, effective form: for every real `α > 1`
every subset of `Ω` is an effective `α`-null set.  Obtained from
`isEffectiveAlphaNull_succ_div` at a rational exponent `(m+1)/m ≤ α` and the
monotonicity `IsEffectiveAlphaNull.mono_alpha` in the exponent. -/
theorem isEffectiveAlphaNull_of_one_lt {α : ℝ} (hα : 1 < α) (A : Set CantorSeq) :
    IsEffectiveAlphaNull α A := by
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (α - 1))
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hmR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hm
  have hmne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hmR
  have hmgt : 1 / (α - 1) < ((n + 1 : ℕ) : ℝ) := by
    refine hn.trans_le ?_
    push_cast
    linarith
  have hmul : 1 < ((n + 1 : ℕ) : ℝ) * (α - 1) := by
    have h := mul_lt_mul_of_pos_right hmgt hα1
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hα1)] at h
  have hkey : (((n + 1 : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) ≤ α := by
    rw [div_le_iff₀ hmR]
    nlinarith
  exact (isEffectiveAlphaNull_succ_div (n + 1) hm A).mono_alpha (by positivity) hkey

/-! ## Bridges to Chapter 3's effective-null layer (`α = 1`) -/

/-- At `α = 1` the interval weight is the interval measure itself. -/
@[simp] lemma intervalAlphaMass_one (x : BitString) :
    intervalAlphaMass 1 x = uniformMeasure (cantorCylinder x) := by
  rw [intervalAlphaMass, ENNReal.rpow_one]

/-- At `α = 1` the cover weight is the interval measure itself. -/
@[simp] lemma coverAlphaMass_one (o : Option BitString) :
    coverAlphaMass 1 o = o.elim 0 (fun x => uniformMeasure (cantorCylinder x)) := by
  cases o with
  | none => rfl
  | some x => exact intervalAlphaMass_one x

/-- **SUV §5.8, p. 172** ("For `α = 1` we get the standard definition of a null
set"), the easy direction of the bridge to Chapter 3.

An effective `1`-null set is effectively null for the uniform measure in the
sense of `AlgorithmicRandomness/EffectiveOpen.lean`.  Three conventions have to
be reconciled and this leaf absorbs all three: the weight at `α = 1` is the
cylinder mass itself (`intervalAlphaMass_one`); the source bounds the *sum* of
the interval masses whereas `IsEffectivelyNull` bounds the *measure of the
union*, which in this direction is countable subadditivity; and the accuracy
parameter is an arbitrary positive rational here and the dyadic `2^{-n}` there
(Chapter 3's `isEffectivelyNull_iff_rational_bound`). -/
theorem isEffectivelyNull_uniform_of_isEffectiveAlphaNull_one {A : Set CantorSeq}
    (h : IsEffectiveAlphaNull 1 A) : IsEffectivelyNull uniformMeasure A := by
  obtain ⟨I, hIcomp, hI⟩ := h
  refine (isEffectivelyNull_iff_rational_bound uniformMeasure A).2
    ⟨fun q => ⋃ i, (I q i).elim ∅ cantorCylinder, ⟨I, hIcomp, fun _ => rfl⟩,
      fun q hq => (hI q hq).1, fun q hq => ?_⟩
  calc uniformMeasure (⋃ i, (I q i).elim ∅ cantorCylinder)
      ≤ ∑' i, uniformMeasure ((I q i).elim ∅ cantorCylinder) := measure_iUnion_le _
    _ = ∑' i, coverAlphaMass 1 (I q i) := by
        refine tsum_congr fun i => ?_
        cases I q i <;> simp
    _ ≤ ENNReal.ofReal (q : ℝ) := (hI q hq).2.le

/-- **SUV §5.8, p. 172**, the converse direction of the `α = 1` bridge.

Here the *measure of the union* has to be turned back into a *sum* of interval
masses, which is Chapter 3's disjointification
(`AlgorithmicRandomness/Disjointify.lean`: a uniformly effectively open set is
the union of a computable sequence of pairwise disjoint intervals, whose masses
therefore add up to the measure of the union), together with the rational normal
form `isEffectivelyNull_iff_rational_bound` and one strictness step
(`isEffectivelyNull_iff_strict_bound`). -/
theorem isEffectiveAlphaNull_one_of_isEffectivelyNull_uniform {A : Set CantorSeq}
    (h : IsEffectivelyNull uniformMeasure A) : IsEffectiveAlphaNull 1 A := by
  obtain ⟨U, ⟨f, hfcomp, hfU⟩, hAU, hmeas⟩ :=
    (isEffectivelyNull_iff_rational_bound uniformMeasure A).1 h
  -- Chapter 3's `computable_disjEnum` is stated for `ℕ`-indexed families, so the
  -- rational parameter is routed through the concrete coding `ratCode`/`ratOfCode`.
  have hgcomp : Computable₂ (fun n i => f (ratOfCode n) i) :=
    Computable₂.comp hfcomp (computable_ratOfCode.comp Computable.fst) Computable.snd
  have hcomp : Computable₂ (fun (q : ℚ) (i : ℕ) => disjEnum (f (q / 2)) i) := by
    have hbase : Computable₂ (fun m i => disjEnum (fun j => f (ratOfCode m) j) i) :=
      computable_disjEnum hgcomp
    have hcode : Computable (fun p : ℚ × ℕ => ratCode (p.1 / 2)) :=
      computable_ratCode.comp (computable_ratHalf.comp Computable.fst)
    exact (hbase.comp hcode Computable.snd).of_eq fun p => by rw [ratOfCode_ratCode]
  refine ⟨fun q i => disjEnum (f (q / 2)) i, hcomp, fun ε hε => ⟨?_, ?_⟩⟩
  · have hcov := hAU (ε / 2) (by linarith)
    rw [hfU (ε / 2)] at hcov
    exact hcov.trans (subset_of_eq (coverSet_disjEnum_iUnion (f (ε / 2))).symm)
  · have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hval : (∑' i, coverAlphaMass 1 (disjEnum (f (ε / 2)) i))
        = uniformMeasure (⋃ j, coverSet (f (ε / 2)) j) := by
      rw [← tsum_measure_disjEnum uniformMeasure (f (ε / 2))]
      refine tsum_congr fun i => ?_
      cases disjEnum (f (ε / 2)) i <;> simp [cantorMass]
    have hUeq : uniformMeasure (⋃ j, coverSet (f (ε / 2)) j) = uniformMeasure (U (ε / 2)) := by
      rw [hfU (ε / 2)]
      rfl
    change (∑' i, coverAlphaMass 1 (disjEnum (f (ε / 2)) i)) < ENNReal.ofReal (ε : ℝ)
    calc (∑' i, coverAlphaMass 1 (disjEnum (f (ε / 2)) i))
        = uniformMeasure (U (ε / 2)) := by rw [hval, hUeq]
      _ ≤ ENNReal.ofReal ((ε / 2 : ℚ) : ℝ) := hmeas (ε / 2) (by linarith)
      _ < ENNReal.ofReal (ε : ℝ) := by
          refine (ENNReal.ofReal_lt_ofReal_iff hεR).2 ?_
          push_cast
          linarith

/-- **SUV §5.8, p. 172.**  "For `α = 1` we get the standard definition of a null
set": effective `1`-nullity is exactly effective nullity with respect to the
uniform measure.  Assembled from the two directions, which have different
content. -/
theorem isEffectiveAlphaNull_one_iff_isEffectivelyNull_uniform (A : Set CantorSeq) :
    IsEffectiveAlphaNull 1 A ↔ IsEffectivelyNull uniformMeasure A :=
  ⟨fun h => isEffectivelyNull_uniform_of_isEffectiveAlphaNull_one h,
    fun h => isEffectiveAlphaNull_one_of_isEffectivelyNull_uniform h⟩

/-! ## The `α`-parametric trimming engine

The engine lives in `Dimension/AlphaTrim.lean`:
`exists_computable₂_trim_alphaCover_dyadic` and `exists_computable₂_trim_alphaCover_rat`.
Both carry two thresholds, one in the bound and one in the "nothing is discarded"
hypothesis: the single-threshold form is not provable by this route, because the
recursion runs on the dyadic floor weight and overshoots the true `α`-weight by up
to a factor of two. -/

/-! ## Largest effectively `α`-null sets -/

/-- **SUV Theorem 117, the enumeration step (§5.8, p. 173).**

> "we can enumerate all effectively `α`-null sets (or, better, the algorithms
> that serve these sets) by enumerating all algorithms and changing them when
> too large intervals are generated."

There is a *universal* effective `α`-test: one algorithm which, for every
rational `ε > 0`, enumerates intervals of total `α`-weight at most `ε` whose
union covers **every** effective `α`-null set.  Constructed and proved in
`Dimension/UniversalAlphaTest.lean`: Chapter 3's numbering `candEnum` of all
partial computable enumerations, made multiplicity-faithful by `firstCand`
(emit the value of an index only at the first `Code.evaln` convergence, so the
`α`-weight cannot grow -- for `α = 1` Chapter 3 instead disjointifies and uses
additivity of the measure), then the proved `α`-trimming engine of
`Dimension/AlphaTrim.lean` at the dyadic level `den ε + c + 1`, the `c`-th
algorithm being asked for the accuracy `2^{-(den ε + c + 5)}`. -/
theorem exists_universal_alphaTest (α : ℚ) (hα : 0 < α) :
    ∃ I : ℚ → ℕ → Option BitString, Computable₂ I ∧
      (∀ ε : ℚ, 0 < ε → (∑' k, coverAlphaMass (α : ℝ) (I ε k)) ≤ ENNReal.ofReal (ε : ℝ)) ∧
      (∀ B : Set CantorSeq, IsEffectiveAlphaNull (α : ℝ) B → ∀ ε : ℚ, 0 < ε →
        B ⊆ ⋃ k, (I ε k).elim ∅ cantorCylinder) :=
  exists_universal_alphaTest_raw α hα

/-- **SUV §5.8, p. 173** ("The countable union of `α`-null sets (in the classical
sense) is an `α`-null set.  In the same way the union of an enumerable family of
effectively `α`-null sets is an `α`-null set").

A uniformly computable family `J` of covers, the `c`-th of which has `α`-weight
at most `ε · 2^{-(c+1)}`, yields an effective `α`-null cover of the union: run
the family at accuracy `ε/2` and interleave the covers along Cantor's pairing,
so that the total weight is at most `ε/2 · ∑_c 2^{-(c+1)} = ε/2 < ε`. -/
theorem isEffectiveAlphaNull_iUnion {α : ℝ} {A : ℕ → Set CantorSeq}
    (J : ℚ → ℕ → ℕ → Option BitString)
    (hJ : Computable (fun p : (ℚ × ℕ) × ℕ => J p.1.1 p.1.2 p.2))
    (hcov : ∀ (c : ℕ) (ε : ℚ), 0 < ε → A c ⊆ ⋃ k, (J ε c k).elim ∅ cantorCylinder)
    (hsum : ∀ (c : ℕ) (ε : ℚ), 0 < ε →
      (∑' k, coverAlphaMass α (J ε c k)) ≤ ENNReal.ofReal (ε : ℝ) * (2 : ℝ≥0∞)⁻¹ ^ (c + 1)) :
    IsEffectiveAlphaNull α (⋃ c, A c) := by
  have hgeom : (∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (c + 1)) = 1 := by
    have h := tsum_inv_two_pow_shift 0
    simpa using h
  refine ⟨fun ε n => J (ε / 2) (Nat.unpair n).1 (Nat.unpair n).2, ?_, fun ε hε => ⟨?_, ?_⟩⟩
  · refine hJ.comp (Computable.pair (Computable.pair
      (computable_ratHalf.comp Computable.fst)
      ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd))
      ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd))
  · refine Set.iUnion_subset fun c w hw => ?_
    obtain ⟨k, hwS⟩ := Set.mem_iUnion.1 (hcov c (ε / 2) (by linarith) hw)
    refine Set.mem_iUnion.2 ⟨Nat.pair c k, ?_⟩
    simpa [Nat.unpair_pair] using hwS
  · have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hreindex : (∑' n : ℕ, coverAlphaMass α
          (J (ε / 2) (Nat.unpair n).1 (Nat.unpair n).2))
        = ∑' p : ℕ × ℕ, coverAlphaMass α (J (ε / 2) p.1 p.2) := by
      rw [← Equiv.tsum_eq Nat.pairEquiv
        (fun n : ℕ => coverAlphaMass α (J (ε / 2) (Nat.unpair n).1 (Nat.unpair n).2))]
      exact tsum_congr fun p => by simp [Nat.pairEquiv, Function.uncurry]
    have hbound : (∑' p : ℕ × ℕ, coverAlphaMass α (J (ε / 2) p.1 p.2))
        ≤ ENNReal.ofReal ((ε / 2 : ℚ) : ℝ) := by
      rw [show (∑' p : ℕ × ℕ, coverAlphaMass α (J (ε / 2) p.1 p.2))
            = ∑' (c : ℕ) (k : ℕ), coverAlphaMass α (J (ε / 2) c k) from
          ENNReal.tsum_prod (f := fun c k => coverAlphaMass α (J (ε / 2) c k))]
      calc (∑' c : ℕ, ∑' k : ℕ, coverAlphaMass α (J (ε / 2) c k))
          ≤ ∑' c : ℕ, ENNReal.ofReal ((ε / 2 : ℚ) : ℝ) * (2 : ℝ≥0∞)⁻¹ ^ (c + 1) :=
            ENNReal.tsum_le_tsum fun c => hsum c (ε / 2) (by linarith)
        _ = ENNReal.ofReal ((ε / 2 : ℚ) : ℝ) * ∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (c + 1) :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal ((ε / 2 : ℚ) : ℝ) := by rw [hgeom, mul_one]
    change (∑' n : ℕ, coverAlphaMass α (J (ε / 2) (Nat.unpair n).1 (Nat.unpair n).2))
      < ENNReal.ofReal (ε : ℝ)
    rw [hreindex]
    refine lt_of_le_of_lt hbound ((ENNReal.ofReal_lt_ofReal_iff hεR).2 ?_)
    push_cast
    linarith

/-- **The assembly step of Theorems 117 and 118 (§5.8, pp. 173-174).**  A
universal effective `α`-test yields the largest effectively `α`-null set: the
set is the intersection of its covers over all positive rational accuracies, it
is itself an effective `α`-null set (run the test at `ε/2`, which turns the
non-strict bound of the test into the strict bound required by the definition),
and it contains every effective `α`-null set by universality. -/
theorem exists_largest_of_isUniversalAlphaTest {α : ℝ}
    (h : ∃ I : ℚ → ℕ → Option BitString, Computable₂ I ∧
      (∀ ε : ℚ, 0 < ε → (∑' k, coverAlphaMass α (I ε k)) ≤ ENNReal.ofReal (ε : ℝ)) ∧
      (∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → ∀ ε : ℚ, 0 < ε →
        B ⊆ ⋃ k, (I ε k).elim ∅ cantorCylinder)) :
    ∃ A : Set CantorSeq, IsEffectiveAlphaNull α A ∧
      ∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → B ⊆ A := by
  obtain ⟨I, hIc, hIsum, hIcov⟩ := h
  refine ⟨⋂ q : {q : ℚ // 0 < q}, ⋃ k, (I q.1 k).elim ∅ cantorCylinder, ?_, ?_⟩
  · refine ⟨fun ε k => I (ε / 2) k,
      hIc.comp (computable_ratHalf.comp Computable.fst) Computable.snd, fun ε hε => ⟨?_, ?_⟩⟩
    · exact Set.iInter_subset
        (fun q : {q : ℚ // 0 < q} => ⋃ k, (I q.1 k).elim ∅ cantorCylinder)
        ⟨ε / 2, by linarith⟩
    · have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      change (∑' k, coverAlphaMass α (I (ε / 2) k)) < ENNReal.ofReal (ε : ℝ)
      refine lt_of_le_of_lt (hIsum (ε / 2) (by linarith)) ?_
      refine (ENNReal.ofReal_lt_ofReal_iff hεR).2 ?_
      push_cast
      linarith
  · intro B hB
    exact Set.subset_iInter fun q => hIcov B hB q.1 q.2

/-- **SUV Theorem 117 (§5.8, p. 173).** For every rational `α > 0` there exists
the largest (with respect to inclusion) effectively `α`-null set. -/
theorem exists_largest_isEffectiveAlphaNull (α : ℚ) (hα : 0 < α) :
    ∃ A : Set CantorSeq, IsEffectiveAlphaNull (α : ℝ) A ∧
      ∀ B : Set CantorSeq, IsEffectiveAlphaNull (α : ℝ) B → B ⊆ A :=
  exists_largest_of_isUniversalAlphaTest (exists_universal_alphaTest α hα)

/-- For a lower semicomputable `α > 0` there is a computable family of covers `I ε k` whose total
`α`-mass is at most `ε` for every positive rational `ε`, and which covers every effectively
`α`-null set.  SUV Theorem 118, §5.8, p. 173. -/
theorem exists_universal_alphaTest_of_isLowerSemicomputable (α : ℝ) (hα : 0 < α)
    (h : IsLowerSemicomputableENNReal (ENNReal.ofReal α)) :
    ∃ I : ℚ → ℕ → Option BitString, Computable₂ I ∧
      (∀ ε : ℚ, 0 < ε → (∑' k, coverAlphaMass α (I ε k)) ≤ ENNReal.ofReal (ε : ℝ)) ∧
      (∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → ∀ ε : ℚ, 0 < ε →
        B ⊆ ⋃ k, (I ε k).elim ∅ cantorCylinder) :=
  exists_universal_alphaTest_real_raw α hα h

/-- **SUV Theorem 118, forward direction (§5.8, p. 173, A. Khodyrev).** If `α`
is lower semicomputable, then the largest effectively `α`-null set exists. -/
theorem exists_largest_isEffectiveAlphaNull_of_isLowerSemicomputable (α : ℝ) (hα : 0 < α)
    (h : IsLowerSemicomputableENNReal (ENNReal.ofReal α)) :
    ∃ A : Set CantorSeq, IsEffectiveAlphaNull α A ∧
      ∀ B : Set CantorSeq, IsEffectiveAlphaNull α B → B ⊆ A :=
  exists_largest_of_isUniversalAlphaTest
    (exists_universal_alphaTest_of_isLowerSemicomputable α hα h)

-- SUV Theorem 118, converse direction and the `iff`, are stated in
-- `Dimension/DimensionLSC.lean` with the standing hypothesis `α ≤ 1`: the forms
-- without it are false, since every `α > 1` makes the whole space effectively
-- `α`-null, so the largest set exists for non-lower-semicomputable `α` as well.

/-! ## Effective Hausdorff dimension -/

/-- **SUV §5.8, p. 174.** The *effective Hausdorff dimension* of `A ⊆ Ω` is the
infimum of the `α > 0` for which `A` is an effective `α`-null set.

The set is nonempty (every `A` is an effective `α`-null set for `α > 1`, by the
cover of all `2^n` strings of length `n`) and bounded below by `0`, so the
`sInf` is the source's infimum and lies in `[0,1]`
(`effectiveHausdorffDim_mem_Icc`). -/
noncomputable def effectiveHausdorffDim (A : Set CantorSeq) : ℝ :=
  sInf {α : ℝ | 0 < α ∧ IsEffectiveAlphaNull α A}

/-- **SUV §5.8, p. 172.** The (classical) *Hausdorff dimension* of `A ⊆ Ω`: the
threshold `d ∈ [0,1]` such that `A` is an `α`-null set for `α > d` and is not
one for `α < d`, presented -- as for the effective notion -- as the infimum of
the `α > 0` for which `A` is an `α`-null set. -/
noncomputable def hausdorffDim (A : Set CantorSeq) : ℝ :=
  sInf {α : ℝ | 0 < α ∧ IsAlphaNull α A}

/-! ### The infimum is over a nonempty set bounded below -/

/-- The exponents witnessing effective `α`-nullity are bounded below by `0`. -/
lemma bddBelow_effectiveAlphaSet (A : Set CantorSeq) :
    BddBelow {α : ℝ | 0 < α ∧ IsEffectiveAlphaNull α A} :=
  ⟨0, fun _ hy => hy.1.le⟩

/-- The exponents witnessing (classical) `α`-nullity are bounded below by `0`. -/
lemma bddBelow_alphaSet (A : Set CantorSeq) :
    BddBelow {α : ℝ | 0 < α ∧ IsAlphaNull α A} :=
  ⟨0, fun _ hy => hy.1.le⟩

/-- Every `α > 1` is an exponent for which `A` is an effective `α`-null set
(SUV §5.8, p. 172, remark (3)). -/
lemma mem_effectiveAlphaSet_of_one_lt {α : ℝ} (hα : 1 < α) (A : Set CantorSeq) :
    α ∈ {β : ℝ | 0 < β ∧ IsEffectiveAlphaNull β A} :=
  ⟨zero_lt_one.trans hα, isEffectiveAlphaNull_of_one_lt hα A⟩

/-- The infimum defining `effectiveHausdorffDim` is over a nonempty set. -/
lemma nonempty_effectiveAlphaSet (A : Set CantorSeq) :
    {α : ℝ | 0 < α ∧ IsEffectiveAlphaNull α A}.Nonempty :=
  ⟨2, mem_effectiveAlphaSet_of_one_lt (by norm_num) A⟩

/-- An effective `α`-null set is an `α`-null set: forget the algorithm and
replace a real `ε` by a smaller rational one. -/
theorem IsEffectiveAlphaNull.isAlphaNull {α : ℝ} {A : Set CantorSeq}
    (h : IsEffectiveAlphaNull α A) : IsAlphaNull α A := by
  obtain ⟨I, -, hI⟩ := h
  intro ε hε
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq : (0 : ℚ) < q := by exact_mod_cast hq0
  exact ⟨I q, (hI q hq).1,
    lt_of_lt_of_le (hI q hq).2 (ENNReal.ofReal_le_ofReal hqε.le)⟩

/-- **SUV §5.8, p. 174.** The effective Hausdorff dimension "is obviously
greater than or equal to the (classical) Hausdorff dimension". -/
theorem hausdorffDim_le_effectiveHausdorffDim (A : Set CantorSeq) :
    hausdorffDim A ≤ effectiveHausdorffDim A :=
  csInf_le_csInf (bddBelow_alphaSet A) (nonempty_effectiveAlphaSet A)
    (fun _ hβ => ⟨hβ.1, hβ.2.isAlphaNull⟩)

/-- **SUV §5.8, p. 174.** "By effective Hausdorff dimension of a point `ω ∈ Ω`
we mean the effective Hausdorff dimension of the singleton `{ω}`." -/
noncomputable def effectiveHausdorffDimPoint (w : CantorSeq) : ℝ :=
  effectiveHausdorffDim {w}

/-- The effective dimension of a sequence is the effective Hausdorff dimension of the singleton it
forms. -/
@[simp] lemma effectiveHausdorffDimPoint_eq (w : CantorSeq) :
    effectiveHausdorffDimPoint w = effectiveHausdorffDim {w} := rfl

/-- **SUV §5.8, p. 174.** "This number belongs to `[0,1]`." -/
theorem effectiveHausdorffDim_mem_Icc (A : Set CantorSeq) :
    effectiveHausdorffDim A ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨le_csInf (nonempty_effectiveAlphaSet A) fun b hb => hb.1.le, ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 : (1 : ℝ) < (1 + effectiveHausdorffDim A) / 2 := by linarith
  have h2 : (1 + effectiveHausdorffDim A) / 2 < effectiveHausdorffDim A := by linarith
  exact absurd (csInf_le (bddBelow_effectiveAlphaSet A)
    (mem_effectiveAlphaSet_of_one_lt h1 A)) (not_le.2 h2)

/-- **SUV §5.8, p. 172** (the threshold property, effective form): above the
dimension the set is an effective `α`-null set. -/
theorem isEffectiveAlphaNull_of_effectiveHausdorffDim_lt {A : Set CantorSeq} {α : ℝ}
    (hα : 0 < α) (h : effectiveHausdorffDim A < α) : IsEffectiveAlphaNull α A := by
  have _ := hα
  obtain ⟨β, hβmem, hβα⟩ := exists_lt_of_csInf_lt (nonempty_effectiveAlphaSet A) h
  exact hβmem.2.mono_alpha hβmem.1 hβα.le

/-- **SUV §5.8, p. 172** (the threshold property, effective form): below the
dimension the set is not an effective `α`-null set.  This half is immediate from
the definition of `effectiveHausdorffDim` as an infimum. -/
theorem not_isEffectiveAlphaNull_of_lt_effectiveHausdorffDim {A : Set CantorSeq} {α : ℝ}
    (hα : 0 < α) (h : α < effectiveHausdorffDim A) : ¬ IsEffectiveAlphaNull α A := by
  intro hnull
  have hbdd : BddBelow {β : ℝ | 0 < β ∧ IsEffectiveAlphaNull β A} :=
    ⟨0, fun y hy => le_of_lt hy.1⟩
  have hmem : α ∈ {β : ℝ | 0 < β ∧ IsEffectiveAlphaNull β A} := ⟨hα, hnull⟩
  exact absurd (csInf_le hbdd hmem) (not_le.mpr h)

end Kolmogorov
