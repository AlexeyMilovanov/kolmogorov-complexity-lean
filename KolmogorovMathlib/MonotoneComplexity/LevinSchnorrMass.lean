/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.AntichainSum
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.CylinderMass

/-!
# The measure bound behind the Levin-Schnorr criterion

This module proves the measure-theoretic core of the Levin-Schnorr criterion: the set of
sequences having *some* prefix on which a continuous tree semimeasure exceeds `2^c` times
the uniform mass of that prefix has uniform measure at most `2^(-c)`.

The proof replaces an arbitrary set of strings by its set of prefix-minimal elements, which
is a prefix-free set generating the same union of cylinders, and then applies the Kraft-type
inequality `IsContinuousTreeSemimeasure.tsum_antichain_le`.

Specialised to the universal continuous semimeasure this reads: for each `c`, the set of
sequences with a prefix of length `n` whose a priori complexity is below `n - c` has uniform
measure at most `2^(-c)`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The prefix-minimal elements of a set of strings. -/
def minimalPrefixElements (S : Set BitString) : Set BitString :=
  {x | x ∈ S ∧ ∀ y ∈ S, y <+: x → y = x}

/-- The prefix-minimal members of a set of strings belong to that set. -/
lemma minimalPrefixElements_subset (S : Set BitString) : minimalPrefixElements S ⊆ S :=
  fun _ hx => hx.1

/-- The prefix-minimal elements of a set form a prefix-free set. -/
lemma minimalPrefixElements_antichain (S : Set BitString) :
    ∀ y ∈ minimalPrefixElements S, ∀ z ∈ minimalPrefixElements S, y <+: z → y = z :=
  fun _ hy _ hz hyz => hz.2 _ hy.1 hyz

/-- Every element of a set of strings extends a prefix-minimal element of that set. -/
lemma exists_minimalPrefixElement {S : Set BitString} {x : BitString} (hx : x ∈ S) :
    ∃ y ∈ minimalPrefixElements S, y <+: x := by
  classical
  have hne : ∃ n, ∃ y, y ∈ S ∧ y <+: x ∧ y.length = n := ⟨x.length, x, hx, List.prefix_refl x, rfl⟩
  obtain ⟨y, hyS, hyx, hylen⟩ := Nat.find_spec hne
  refine ⟨y, ⟨hyS, ?_⟩, hyx⟩
  intro z hzS hzy
  have hzx : z <+: x := hzy.trans hyx
  have hle : Nat.find hne ≤ z.length := Nat.find_le ⟨z, hzS, hzx, rfl⟩
  have hlen : z.length = y.length := le_antisymm hzy.length_le (by omega)
  exact hzy.eq_of_length hlen

/-- Passing to prefix-minimal elements does not change the union of the cylinders. -/
lemma iUnion_cantorCylinder_minimalPrefixElements (S : Set BitString) :
    (⋃ x ∈ minimalPrefixElements S, cantorCylinder x) = ⋃ x ∈ S, cantorCylinder x := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun x hx => Set.subset_iUnion₂ (s := fun x (_ : x ∈ S) =>
      cantorCylinder x) x hx.1
  · refine Set.iUnion₂_subset fun x hx => ?_
    obtain ⟨y, hy, hyx⟩ := exists_minimalPrefixElement hx
    exact (cantorCylinder_subset_of_prefix hyx).trans
      (Set.subset_iUnion₂ (s := fun x (_ : x ∈ minimalPrefixElements S) => cantorCylinder x) y hy)

/-- The uniform mass of a union of cylinders is bounded by the sum of the masses of the
prefix-minimal generators. -/
lemma uniformMeasure_iUnion_cantorCylinder_le (S : Set BitString) :
    uniformMeasure (⋃ x ∈ S, cantorCylinder x)
      ≤ ∑' x : minimalPrefixElements S, (2 : ℝ≥0∞)⁻¹ ^ (x : BitString).length := by
  rw [← iUnion_cantorCylinder_minimalPrefixElements S]
  refine le_trans (measure_biUnion_le uniformMeasure (Set.to_countable _) cantorCylinder) ?_
  exact le_of_eq (tsum_congr fun x => uniformMeasure_cantorCylinder _)

/-- **Levin-Schnorr mass bound.** For a continuous tree semimeasure `a`, the set of sequences
having a prefix of length `n` with `a`-mass exceeding `2^c · 2^(-n)` has uniform measure at
most `2^(-c)`. -/
theorem uniformMeasure_setOf_exists_prefix_mass_gt_le {a : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (c : ℕ) :
    uniformMeasure {w : CantorSeq | ∃ n, (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n < a (cantorPrefix w n)}
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  classical
  set S : Set BitString := {x | (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ x.length < a x} with hS
  have hset : {w : CantorSeq |
      ∃ n, (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n < a (cantorPrefix w n)}
      = ⋃ x ∈ S, cantorCylinder x := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨cantorPrefix w n, ?_, ?_⟩
      · simpa [hS, cantorPrefix_length] using hn
      · exact (isCantorPrefix_iff_cantorPrefix_eq _ w).2 (by simp [cantorPrefix_length])
    · rintro ⟨x, hx, hw⟩
      refine ⟨x.length, ?_⟩
      rw [(isCantorPrefix_iff_cantorPrefix_eq x w).1 hw]
      exact hx
  have hinv : ((2 : ℝ≥0∞)⁻¹) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    simp
  have hterm : ∀ x : minimalPrefixElements S,
      (2 : ℝ≥0∞)⁻¹ ^ (x : BitString).length ≤ (2 : ℝ≥0∞)⁻¹ ^ c * a (x : BitString) := by
    rintro ⟨x, hx⟩
    have hxS : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ x.length < a x := hx.1
    calc (2 : ℝ≥0∞)⁻¹ ^ x.length
        = (2 : ℝ≥0∞)⁻¹ ^ c * ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ x.length) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * a x := by gcongr
  calc uniformMeasure {w : CantorSeq |
        ∃ n, (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ n < a (cantorPrefix w n)}
      = uniformMeasure (⋃ x ∈ S, cantorCylinder x) := by rw [hset]
    _ ≤ ∑' x : minimalPrefixElements S, (2 : ℝ≥0∞)⁻¹ ^ (x : BitString).length :=
        uniformMeasure_iUnion_cantorCylinder_le S
    _ ≤ ∑' x : minimalPrefixElements S, (2 : ℝ≥0∞)⁻¹ ^ c * a (x : BitString) :=
        ENNReal.tsum_le_tsum hterm
    _ = (2 : ℝ≥0∞)⁻¹ ^ c * ∑' x : minimalPrefixElements S, a (x : BitString) :=
        ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c * 1 := by
        gcongr
        exact ha.tsum_antichain_le _ (minimalPrefixElements_antichain S)
    _ = (2 : ℝ≥0∞)⁻¹ ^ c := mul_one _

/-- A complexity deficiency `KA x + c < l(x)` means that the universal continuous semimeasure
exceeds `2^c · 2^(-l(x))` at `x`. -/
lemma mass_gt_of_KA_add_lt {x : BitString} {c : ℕ} (h : KA x + c < x.length) :
    (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ x.length < universalContinuousSemimeasure x := by
  have hx_top : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hx_pos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne' hx_top
  have hlog : (c : ℝ) - x.length < Real.logb 2 (universalContinuousSemimeasure x).toReal := by
    have := h
    unfold KA at this
    linarith
  have hrpow : (2 : ℝ) ^ ((c : ℝ) - x.length)
      < (universalContinuousSemimeasure x).toReal := by
    have hbase : (1 : ℝ) < 2 := by norm_num
    have := Real.rpow_lt_rpow_left_iff (x := (2 : ℝ))
      (y := (c : ℝ) - x.length)
      (z := Real.logb 2 (universalContinuousSemimeasure x).toReal) hbase |>.2 hlog
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hx_pos] at this
  have hleft : ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ x.length).toReal
      = (2 : ℝ) ^ ((c : ℝ) - x.length) := by
    rw [ENNReal.toReal_mul]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    rw [_root_.eq_div_iff (by positivity), mul_assoc, ← mul_pow]
    norm_num
  have hne : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ x.length ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ENNReal.pow_ne_top (by norm_num))
  rw [← ENNReal.toReal_lt_toReal hne hx_top, hleft]
  exact hrpow

/-- **Levin-Schnorr mass bound for a priori complexity.** For each `c`, the set of sequences
having a prefix of length `n` with `KA` below `n - c` has uniform measure at most `2^(-c)`. -/
theorem uniformMeasure_setOf_exists_prefix_KA_add_lt_le (c : ℕ) :
    uniformMeasure {w : CantorSeq | ∃ n, KA (cantorPrefix w n) + c < n} ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  refine le_trans (measure_mono ?_)
    (uniformMeasure_setOf_exists_prefix_mass_gt_le
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1 c)
  rintro w ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have h := mass_gt_of_KA_add_lt (x := cantorPrefix w n) (c := c) (by
    rw [cantorPrefix_length]; exact hn)
  rwa [cantorPrefix_length] at h

end Kolmogorov
