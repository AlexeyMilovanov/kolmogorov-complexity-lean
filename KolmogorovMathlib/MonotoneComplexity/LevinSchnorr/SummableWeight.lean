/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.SharedCoding
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic

/-!
# `K(n) ≤ f(n) + O(1)` for a computable `f` with a convergent series

SUV Section 5.6, p. 154, opening line of the proof of Theorem 98: "If `∑ₙ 2^(−f(n))`
converges for a computable `f`, then `K(n) ⩽ f(n) + O(1)`."  This is the one ingredient that
makes the prefix-complexity criterion of Theorem 98 *stronger* than the criterion of
Theorem 97, and hence lets Theorem 98 ⇐ be deduced from Theorem 97 ⇐.

The proof is the coding theorem: rescaling `2^(−f(n))` by a power of two turns it into a
(lower semicomputable, in fact computable) semimeasure on strings, and
`lowerSemicomputableSemimeasure_le_prefixComplexityWeight` bounds `K` by its negative
logarithm.

## Main results

* `summableWeight_isLowerSemicomputableSemimeasure` — the rescaled weight is a lower
  semicomputable semimeasure;
* `exists_const_KPNat_le_of_computable_summable` — `K(n) ≤ f(n) + O(1)`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The rescaled weight -/

/-- `2^(−d−f(n))`, read as a function of the string coding `n`.  For a suitable `d` this is a
semimeasure whenever `∑ₙ 2^(−f(n))` converges. -/
noncomputable def summableWeight (f : ℕ → ℕ) (d : ℕ) (x : BitString) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ (d + f (bitStringToNat x))

/-- The stage-`s` numerator of `summableWeight f d`: `2^(s−d−f(n))` once the stage is large
enough, and `0` before that. -/
def summableWeightApprox (f : ℕ → ℕ) (d : ℕ) (s : ℕ) (x : BitString) (_ctx : BitString) : ℕ :=
  if s < d + f (bitStringToNat x) then 0 else 2 ^ (s - (d + f (bitStringToNat x)))

/-- The stage-`s` approximation of the summable weight is `0` before stage `d + f n` and exact
afterwards. -/
lemma dyadicValue_summableWeightApprox (f : ℕ → ℕ) (d s : ℕ) (x ctx : BitString) :
    dyadicValue (summableWeightApprox f d s x ctx) s
      = if s < d + f (bitStringToNat x) then 0 else summableWeight f d x := by
  rw [summableWeightApprox]
  split_ifs with h
  · simp [dyadicValue]
  · rw [summableWeight]
    exact dyadicValue_two_pow_sub (by omega)

/-- For a computable exponent function the staged approximation of the summable weight is
computable. -/
lemma computable_summableWeightApprox {f : ℕ → ℕ} (hf : Computable f) (d : ℕ) :
    Computable fun p : ℕ × BitString × BitString =>
      summableWeightApprox f d p.1 p.2.1 p.2.2 := by
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hsub : Computable₂ (fun a b : ℕ => a - b) := Primrec.nat_sub.to_comp
  have hlt : Computable₂ (fun a b : ℕ => decide (a < b)) := primrec_decide_nat_lt.to_comp
  have hk : Computable fun p : ℕ × BitString × BitString =>
      d + f (bitStringToNat p.2.1) :=
    hadd.comp (Computable.const d)
      (hf.comp (computable_bitStringToNat.comp (Computable.fst.comp Computable.snd)))
  have hcond : Computable fun p : ℕ × BitString × BitString =>
      decide (p.1 < d + f (bitStringToNat p.2.1)) := hlt.comp Computable.fst hk
  have hpow : Computable fun p : ℕ × BitString × BitString =>
      2 ^ (p.1 - (d + f (bitStringToNat p.2.1))) :=
    primrec_two_pow_aux.to_comp.comp (hsub.comp Computable.fst hk)
  refine (Computable.cond hcond (Computable.const 0) hpow).of_eq fun p => ?_
  by_cases h : p.1 < d + f (bitStringToNat p.2.1) <;> simp [summableWeightApprox, h]

/-- For a computable exponent function the summable weight is lower semicomputable. -/
lemma isLSC_summableWeight {f : ℕ → ℕ} (hf : Computable f) (d : ℕ) :
    IsLSC fun (x : BitString) (_ : BitString) => summableWeight f d x := by
  refine ⟨summableWeightApprox f d, ?_, ?_, computable_summableWeightApprox hf d⟩
  · intro s out ctx
    rw [dyadicValue_summableWeightApprox, dyadicValue_summableWeightApprox]
    split_ifs with h1 h2
    · exact le_rfl
    · exact zero_le
    · omega
    · exact le_rfl
  · intro out ctx
    refine le_antisymm (iSup_le fun s => ?_) ?_
    · rw [dyadicValue_summableWeightApprox]
      split_ifs
      · exact zero_le
      · exact le_rfl
    · refine le_iSup_of_le (d + f (bitStringToNat out)) ?_
      rw [dyadicValue_summableWeightApprox, ite_eq_right (by omega)]

/-- The summable weights add up to `2 ^ (-d)` times the series `∑ 2 ^ (-f n)`. -/
lemma tsum_summableWeight {f : ℕ → ℕ} (d : ℕ) :
    (∑' x : BitString, summableWeight f d x)
      = (2 : ℝ≥0∞)⁻¹ ^ d * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n := by
  have h1 : (∑' x : BitString, summableWeight f d x)
      = ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (d + f n) :=
    tsum_comp_bitStringToNat (fun n => (2 : ℝ≥0∞)⁻¹ ^ (d + f n))
  rw [h1, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => by rw [pow_add]

/-- The rescaled weight `2^(−d−f(n))` is a lower semicomputable semimeasure, provided the
rescaling `d` absorbs the total mass of the series. -/
theorem summableWeight_isLowerSemicomputableSemimeasure {f : ℕ → ℕ} (hf : Computable f)
    {d : ℕ} (hd : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≤ (2 : ℝ≥0∞) ^ d) :
    IsLowerSemicomputableSemimeasure (summableWeight f d) := by
  refine ⟨?_, isLSC_summableWeight hf d⟩
  rw [IsSemimeasure, tsum_summableWeight]
  have hinv : ((2 : ℝ≥0∞)⁻¹) ^ d * (2 : ℝ≥0∞) ^ d = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ d * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n
      ≤ (2 : ℝ≥0∞)⁻¹ ^ d * (2 : ℝ≥0∞) ^ d := by gcongr
    _ = 1 := hinv

/-- **SUV p. 154** (first line of the proof of Theorem 98): if `f : ℕ → ℕ` is total computable
and `∑ₙ 2^(−f(n))` converges, then `K(n) ≤ f(n) + O(1)`.

This is the coding theorem applied to the semimeasure `2^(−d−f(n))`, where `2^d` bounds the
total mass of the series. -/
theorem exists_const_KPNat_le_of_computable_summable {U : Map}
    (hU : IsOptimalPrefixConditional U) {f : ℕ → ℕ} (hf : Computable f)
    (hconv : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤) :
    ∃ c : ℕ, ∀ n : ℕ, KPNat U n ≤ (f n : ℕ∞) + c := by
  obtain ⟨d, hd⟩ := ENNReal.exists_nat_gt hconv
  have hd' : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≤ (2 : ℝ≥0∞) ^ d := by
    refine le_trans hd.le ?_
    have hn2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc (d : ℝ≥0∞) ≤ ((2 ^ d : ℕ) : ℝ≥0∞) := by exact_mod_cast hn2.le
      _ = (2 : ℝ≥0∞) ^ d := by push_cast; ring
  obtain ⟨c, hc⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight
    (summableWeight_isLowerSemicomputableSemimeasure hf hd') hU
  refine ⟨c + d, fun n => ?_⟩
  refine le_add_nat_of_complexityWeight_le (ENat.natCast_ne_top _) ?_
  have h := hc (natToBitString n)
  rw [summableWeight, bitStringToNat_natToBitString] at h
  rw [complexityWeight_coe]
  calc (2 : ℝ≥0∞)⁻¹ ^ (c + d) * (2 : ℝ≥0∞)⁻¹ ^ f n
      = (2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞)⁻¹ ^ (d + f n) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
    _ ≤ complexityWeight (KPNat U n) := h

end Kolmogorov
