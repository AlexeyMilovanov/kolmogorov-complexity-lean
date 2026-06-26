/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# The Counting Bound for Prefix Complexity (SUV Theorem 63(b))

This module isolates the analytic ingredients behind the SUV Theorem 63(b)
counting bound:

> among the strings of length `n`, the number with `K(x) < n + K(n) - d`
> is at most `2^{n-d}`.

The textbook proof is a Kraft/coding argument. Writing `m_U(x) = 2^{-K(x)}` for the
prefix-complexity weight, the key fact is the *length marginal* bound

```
∑_{|x| = n} 2^{-K(x)} ≤ 2^{c} · 2^{-K(n)},
```

which says the total a priori probability concentrated on length-`n` strings is,
up to a constant, the a priori probability of the *number* `n`.  This is the
coding theorem (domination of a lower-semicomputable semimeasure by `2^{-K}`)
applied to the **length-projection machine** `lenMap U`: run `U` and output the
binary code of the length of its output.  The construction and the marginal bound
mirror the pair-output `projMap` development in
`KolmogorovMathlib.AlgorithmicProbability.PairProjection`.

Once the marginal bound is in hand, the counting bound is elementary: each string
in the bad set carries weight at least `2^{-(n+K(n)-c-d)}`, so the bad set has at
most `2^{c} · 2^{-K(n)} / 2^{-(n+K(n)-c-d)} = 2^{n-d-?}` elements.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### A pure `ℝ≥0∞` exponent lemma -/

/-
`2^n · 2^{-d}` never exceeds the (truncated) natural power `2^{n-d}`. When
`d ≤ n` it is an equality; when `d > n` the left side is `≤ 1 = 2^0`.
-/
theorem two_pow_mul_inv_pow_le_cast_pow_sub (n d : ℕ) :
    (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d ≤ ((2 ^ (n - d) : ℕ) : ℝ≥0∞) := by
  by_cases h : n ≤ d
  · have h_sub : n - d = 0 := Nat.sub_eq_zero_of_le h
    rw [h_sub, pow_zero, Nat.cast_one]
    have h_pow_le : (2 : ℝ≥0∞) ^ n ≤ (2 : ℝ≥0∞) ^ d :=
      pow_le_pow_right₀ (by norm_num) h
    calc
      (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞)⁻¹ ^ d ≤ (2 : ℝ≥0∞) ^ d * (2 : ℝ≥0∞)⁻¹ ^ d := by
        gcongr
      _ = (2 * (2 : ℝ≥0∞)⁻¹) ^ d := by rw [← mul_pow]
      _ = 1 ^ d := by rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
      _ = 1 := one_pow d
  · push Not at h
    have h_le : d ≤ n := h.le
    rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) (by norm_num)) (by norm_num)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv, Nat.cast_pow, Nat.cast_ofNat]
    refine le_of_eq ?_
    calc
      (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ d = (2 : ℝ) ^ (n - d + d) * (2 : ℝ)⁻¹ ^ d := by
        rw [Nat.sub_add_cancel h_le]
      _ = (2 : ℝ) ^ (n - d) * (2 : ℝ) ^ d * (2 : ℝ)⁻¹ ^ d := by rw [pow_add]
      _ = (2 : ℝ) ^ (n - d) * ((2 : ℝ) ^ d * (2 : ℝ)⁻¹ ^ d) := by rw [mul_assoc]
      _ = (2 : ℝ) ^ (n - d) * 1 := by rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
      _ = (2 : ℝ) ^ (n - d) := mul_one _

/-! ### The length-projection machine -/

/-- The **length-projection machine**: run `U` on the program (empty context) and
return the binary code `Nat.bits` of the length of its output. -/
def lenMap (U : Map) : Map :=
  fun pr => (U (pr.1, [])).map (fun z => Nat.bits z.length)

/-- Membership characterization of the length-projection machine: it produces the
code `w` from a program `p` exactly when `U` produces, in the empty context, some
output `z` whose length code is `w`. The output context `y` is ignored. -/
theorem produces_lenMap_iff (U : Map) (p y w : BitString) :
    produces (lenMap U) p y w ↔ ∃ z, produces U p [] z ∧ Nat.bits z.length = w := by
  change w ∈ Part.map (fun z => Nat.bits z.length) (U (p, [])) ↔
    ∃ z, produces U p [] z ∧ Nat.bits z.length = w
  rw [Part.mem_map_iff]

/-- The halting domain of the length-projection machine in any context is the
halting domain of `U` in the empty context. -/
theorem domainAt_lenMap (U : Map) (y : BitString) :
    domainAt (lenMap U) y = domainAt U [] := rfl

/-- **The length-projection machine is a prefix decompressor** whenever `U` is. -/
theorem lenMap_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (lenMap U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString => U (pr.1, [])) :=
      hU.isDecompressor.comp (Computable.fst.pair (Computable.const []))
    have hg : Computable₂
        (fun (_ : BitString × BitString) (z : BitString) => Nat.bits z.length) :=
      (natBitsComputable.comp (Computable.list_length.comp Computable.snd)).to₂
    exact (hf.map hg).of_eq (fun pr => rfl)
  · intro y
    rw [domainAt_lenMap]
    exact hU.isPrefixMachine []

/-! ### The length marginal -/

/-- The **length marginal**: the total a priori probability concentrated on the
strings of length `n`. -/
noncomputable def lengthMarginal (U : Map) (n : ℕ) : ℝ≥0∞ :=
  ∑ x ∈ stringsOfLength n, aprioriMeasure U x []

/-- Swap a finite `Finset.sum` with a `tsum` over `ℝ≥0∞` (always valid, as every
`ℝ≥0∞`-valued family is summable). -/
theorem tsum_finset_sum_comm (s : Finset BitString)
    (f : BitString → BitString → ℝ≥0∞) :
    (∑ x ∈ s, ∑' p, f x p) = ∑' p, ∑ x ∈ s, f x p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih, ← ENNReal.tsum_add]
      simp [Finset.sum_insert ha]

/-- **The length marginal is bounded by the length-projection machine's a priori
semimeasure.** Every length-`n` output of `U` has length code `Nat.bits n`; since
`U` is deterministic, distinct length-`n` outputs come from distinct programs, so
the (finite) length-marginal sum injects into the projection-machine sum. This
mirrors `pairMarginal_le_aprioriMeasure_projMap`. -/
theorem lengthMarginal_le_aprioriMeasure_lenMap (U : Map) (n : ℕ) :
    lengthMarginal U n ≤ aprioriMeasure (lenMap U) (Nat.bits n) [] := by
  classical
  rw [lengthMarginal]
  simp only [aprioriMeasure]
  rw [tsum_finset_sum_comm]
  refine ENNReal.tsum_le_tsum (fun p => ?_)
  by_cases hp : ∃ x ∈ stringsOfLength n, produces U p [] x
  · obtain ⟨x₀, hx₀mem, hx₀⟩ := hp
    have hx₀len : x₀.length = n := (memStringsOfLength n x₀).mp hx₀mem
    have hsum : (∑ x ∈ stringsOfLength n, if produces U p [] x then progWeight p else 0)
        = progWeight p := by
      rw [Finset.sum_eq_single x₀]
      · rw [if_pos hx₀]
      · intro x _ hxne
        by_cases hpx : produces U p [] x
        · exact absurd (Part.mem_unique hpx hx₀) hxne
        · rw [if_neg hpx]
      · intro hnot; exact absurd hx₀mem hnot
    rw [hsum]
    have hproj : produces (lenMap U) p [] (Nat.bits n) :=
      (produces_lenMap_iff U p [] (Nat.bits n)).mpr ⟨x₀, hx₀, by rw [hx₀len]⟩
    rw [if_pos hproj]
  · push Not at hp
    have hzero : (∑ x ∈ stringsOfLength n, if produces U p [] x then progWeight p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hxmem
      rw [if_neg (hp x hxmem)]
    rw [hzero]
    exact zero_le

/-! ### The crux: the length-marginal coding bound -/

/-- **Length-marginal coding bound (the crux of SUV 63(b)).** The total a priori
weight of the length-`n` strings is, up to a uniform constant `2^{c}`, at most
`2^{-K(n)}`. This is the coding theorem applied to the length-projection machine
`lenMap U`. -/
theorem sum_complexityWeight_stringsOfLength_le (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kn : ℕ), HasPrefixComplexityValue U (Nat.bits n) kn →
      (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x))
        ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := by
  obtain ⟨c, hc⟩ :=
    aprioriMeasure_le_complexityWeight_optimal hU
      (lenMap_isPrefixDecompressor U hU.isPrefixDecompressor)
  refine ⟨c, fun n kn hkn => ?_⟩
  -- The length marginal dominates the sum of complexity weights.
  have hsum_le : (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x))
      ≤ aprioriMeasure (lenMap U) (Nat.bits n) [] := by
    refine le_trans (Finset.sum_le_sum (fun x _ => ?_))
      (lengthMarginal_le_aprioriMeasure_lenMap U n)
    exact complexityWeight_KP_le_aprioriMeasure U x []
  -- The coding theorem at the code `Nat.bits n` gives `2^{-c}·marginal ≤ 2^{-kn}`.
  have hcode : (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure (lenMap U) (Nat.bits n) []
      ≤ (2 : ℝ≥0∞)⁻¹ ^ kn := by
    have h := hc (Nat.bits n) []
    have hval : complexityWeight (KP U (Nat.bits n) []) = (2 : ℝ≥0∞)⁻¹ ^ kn := by
      have : KP U (Nat.bits n) [] = (kn : ENat) := by
        rw [← KPPlain_eq_KP]; exact hkn.symm
      rw [this, complexityWeight_coe]
    rwa [hval] at h
  -- Multiply through by `2^c` and combine.
  have hcc : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc
    (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x))
        = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c *
            (∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x))) := by
      rw [← mul_assoc, hcc, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure (lenMap U) (Nat.bits n) []) := by
      gcongr
    _ ≤ (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kn := by
      gcongr

end Kolmogorov
