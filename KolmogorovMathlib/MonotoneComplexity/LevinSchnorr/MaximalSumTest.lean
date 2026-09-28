/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.ExpectationTests
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.SummableWeight
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations
import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelStage

/-!
# Maximality of `∑_{x ⊑ ω} m(x)/p(x)` (SUV Problem 146, p. 150)

The source's argument, verbatim:

> a lower semicomputable function on Cantor space is a sum of characteristic functions of
> intervals with non-negative coefficients; collecting the coefficients at each vertex `x` of
> the binary tree gives a lower semicomputable `u` on strings with `∑_x p(x)·u(x) ≤ 1`, and
> the maximal such `u` is `m(x)/p(x)` up to a `Θ(1)` factor.

In Lean: SUV Theorem 40 (`lowerSemicomputableFun_characterizations`) writes an
expectation-bounded test `v` as `v ω = ∑_s dyadicValue (term s ((ω)_s)) s`, so
`v ω = ∑_s u((ω)_s)` for the *vertex weight* `u x = dyadicValue (term |x| x) |x|`.  Then
`x ↦ u(x)·p(x)` is a lower semicomputable semimeasure — the crucial point being that `u` is an
exactly known dyadic rational at a *known* scale `|x|`, so multiplying the stage
approximations of `p` by it needs no rounding at all, only a shift of the scale by `|x|`.
Universality of `m` gives `2^(-k)·u(x)·p(x) ≤ m(x)`, i.e. `u(x) ≤ 2^k · m(x)/p(x)`, and
summing along the prefixes of `ω` gives `v ω ≤ 2^k · ∑_{x ⊑ ω} m(x)/p(x)`.

At a null cylinder the argument needs `m(x) ≠ 0`, which holds because a universal semimeasure
dominates the strictly positive computable semimeasure `2^(-1-2|x|)`
(`universalSemimeasure_pos`).

## Main results

* `tsum_eq_tsum_sum_levelFinset` — the level partition of a sum over all strings;
* `universalSemimeasure_pos` — a universal semimeasure is strictly positive;
* `vertexWeight`, `isLSC_vertexWeight_mul_cantorMass`;
* `maximal_prefixSumRatio` — Problem 146's maximality.
-/

namespace Kolmogorov

open MeasureTheory

open scoped ENNReal NNReal

/-! ### The level partition -/

/-- A sum over all bit strings may be computed level by level. -/
theorem tsum_eq_tsum_sum_levelFinset (g : BitString → ℝ≥0∞) :
    ∑' x : BitString, g x = ∑' n : ℕ, ∑ y ∈ levelFinset n, g y := by
  classical
  have hfib := (Equiv.sigmaFiberEquiv (fun x : BitString => x.length)).tsum_eq g
  have hsimp : ∀ c : (y : ℕ) × {x : BitString // x.length = y},
      g ((Equiv.sigmaFiberEquiv (fun x : BitString => x.length)) c) = g (c.2 : BitString) :=
    fun _ => rfl
  rw [← hfib, tsum_congr hsimp,
    ENNReal.tsum_sigma (fun (n : ℕ) (x : {x : BitString // x.length = n}) => g (x : BitString))]
  refine tsum_congr fun n => ?_
  have hsub : (∑' x : {x : BitString // x.length = n}, g (x : BitString))
      = ∑' x : {x : BitString // x ∈ levelFinset n}, g (x : BitString) :=
    (Equiv.subtypeEquivRight fun x => (mem_levelFinset (n := n) (y := x)).symm).tsum_eq
      (fun x : {x : BitString // x ∈ levelFinset n} => g (x : BitString))
  rw [hsub]
  exact (levelFinset n).tsum_subtype g

/-! ### A universal semimeasure is strictly positive -/

/-- The strictly positive computable semimeasure `2^(-1-2|x|)`. -/
noncomputable def lengthWeight (x : BitString) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (1 + 2 * x.length)

/-- The length weights `2 ^ (-(1 + 2|x|))` form a discrete semimeasure: they sum to at most `1`. -/
lemma tsum_lengthWeight : (∑' x : BitString, lengthWeight x) ≤ 1 := by
  have hlevel : ∀ n : ℕ, ∑ y ∈ levelFinset n, lengthWeight y = (2 : ℝ≥0∞)⁻¹ ^ (1 + n) := by
    intro n
    have hconst : ∀ y ∈ levelFinset n, lengthWeight y = (2 : ℝ≥0∞)⁻¹ ^ (1 + 2 * n) := by
      intro y hy
      rw [lengthWeight, mem_levelFinset.mp hy]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_levelFinset, nsmul_eq_mul]
    have hpow : ((2 ^ n : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ n := by push_cast; ring
    rw [hpow, show 1 + 2 * n = (1 + n) + n by omega, pow_add, ← mul_assoc,
      mul_comm ((2 : ℝ≥0∞) ^ n) ((2 : ℝ≥0∞)⁻¹ ^ (1 + n)), mul_assoc, ← mul_pow,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, mul_one]
  rw [tsum_eq_tsum_sum_levelFinset, tsum_congr hlevel]
  have hgeo : ∀ n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (1 + n) = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    rw [pow_add, pow_one]
  rw [tsum_congr hgeo, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hhalf : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.sub_eq_of_eq_add (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ⊤)]
    rw [ENNReal.inv_two_add_inv_two]
  have hval : (2 : ℝ≥0∞)⁻¹ * ((1 : ℝ≥0∞) - 2⁻¹)⁻¹ = 1 := by
    rw [hhalf, inv_inv, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  exact le_of_eq hval

/-- The stage numerators of `lengthWeight`. -/
def lengthWeightApprox (s : ℕ) (x : BitString) (_ctx : BitString) : ℕ :=
  if s < 1 + 2 * x.length then 0 else 2 ^ (s - (1 + 2 * x.length))

/-- The stage-`s` approximation of the length weight is `0` before stage `1 + 2|x|` and exact
afterwards. -/
lemma dyadicValue_lengthWeightApprox (s : ℕ) (x ctx : BitString) :
    dyadicValue (lengthWeightApprox s x ctx) s
      = if s < 1 + 2 * x.length then 0 else lengthWeight x := by
  rw [lengthWeightApprox]
  split_ifs with h
  · simp [dyadicValue]
  · rw [lengthWeight]
    exact dyadicValue_two_pow_sub (by omega)

/-- The length weight is lower semicomputable. -/
lemma isLSC_lengthWeight : IsLSC fun (x : BitString) (_ : BitString) => lengthWeight x := by
  refine ⟨lengthWeightApprox, ?_, ?_, ?_⟩
  · intro s out ctx
    rw [dyadicValue_lengthWeightApprox, dyadicValue_lengthWeightApprox]
    split_ifs with h1 h2
    · exact le_rfl
    · exact zero_le _
    · omega
    · exact le_rfl
  · intro out ctx
    refine le_antisymm (iSup_le fun s => ?_) ?_
    · rw [dyadicValue_lengthWeightApprox]
      split_ifs
      · exact zero_le _
      · exact le_rfl
    · refine le_iSup_of_le (1 + 2 * out.length) ?_
      rw [dyadicValue_lengthWeightApprox, if_neg (by omega)]
  · have hadd : Computable₂ (fun u v : ℕ => u + v) := Primrec.nat_add.to_comp
    have hmul : Computable₂ (fun u v : ℕ => u * v) := Primrec.nat_mul.to_comp
    have hsub : Computable₂ (fun u v : ℕ => u - v) := Primrec.nat_sub.to_comp
    have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
    have hk : Computable fun p : ℕ × BitString × BitString => 1 + 2 * p.2.1.length :=
      hadd.comp (Computable.const 1)
        (hmul.comp (Computable.const 2)
          (Computable.list_length.comp (Computable.fst.comp Computable.snd)))
    have hcond : Computable fun p : ℕ × BitString × BitString =>
        decide (p.1 < 1 + 2 * p.2.1.length) := hlt.comp Computable.fst hk
    have hpow : Computable fun p : ℕ × BitString × BitString =>
        2 ^ (p.1 - (1 + 2 * p.2.1.length)) :=
      primrec_two_pow_aux.to_comp.comp (hsub.comp Computable.fst hk)
    refine (Computable.cond hcond (Computable.const 0) hpow).of_eq fun p => ?_
    by_cases h : p.1 < 1 + 2 * p.2.1.length <;> simp [lengthWeightApprox, h]

/-- Every string carries strictly positive length weight. -/
lemma lengthWeight_pos (x : BitString) : 0 < lengthWeight x := by
  rw [lengthWeight]
  exact ENNReal.pow_pos (by simp) _

/-- A universal semimeasure is strictly positive on every string. -/
theorem universalSemimeasure_pos {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m)
    (x : BitString) : 0 < m x := by
  obtain ⟨c, hc, hdom⟩ := hm.2 lengthWeight ⟨tsum_lengthWeight, isLSC_lengthWeight⟩
  exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' (lengthWeight_pos x).ne') (hdom x)

/-! ### The vertex weights of a lower semicomputable function -/

/-- The weight that a sum-of-basic-functions representation of a lower semicomputable
function puts at the vertex `x` of the binary tree (SUV p. 150, "collecting the coefficients
at each vertex `x`"). -/
noncomputable def vertexWeight (term : ℕ → BitString → ℕ) (x : BitString) : ℝ≥0∞ :=
  dyadicValue (term x.length x) x.length

/-- At the length-`s` prefix of a sequence the vertex weight is the dyadic value of the stage-`s`
term. -/
lemma vertexWeight_cantorPrefix (term : ℕ → BitString → ℕ) (w : CantorSeq) (s : ℕ) :
    vertexWeight term (cantorPrefix w s) = dyadicValue (term s (cantorPrefix w s)) s := by
  rw [vertexWeight, cantorPrefix_length]

/-- Vertex weights are finite. -/
lemma vertexWeight_ne_top (term : ℕ → BitString → ℕ) (x : BitString) :
    vertexWeight term x ≠ ⊤ := dyadicValue_ne_top _ _

/-- The stage numerators of `x ↦ u(x)·p(x)`.  No rounding is needed: `u(x)` is an exactly
known dyadic rational at the known scale `|x|`, so the stage-`s` numerator is just the
stage-`(s − |x|)` numerator of the cylinder mass scaled by the numerator of `u(x)`. -/
def vertexMassApprox (term : ℕ → BitString → ℕ) (A : ℕ → BitString → BitString → ℕ)
    (s : ℕ) (x ctx : BitString) : ℕ :=
  if s < x.length then 0 else term x.length x * A (s - x.length) x ctx

/-- The staged vertex mass at stage `|x| + t` is the vertex weight of `x` times the stage-`t`
approximation of the mass. -/
lemma dyadicValue_vertexMassApprox (term : ℕ → BitString → ℕ)
    (A : ℕ → BitString → BitString → ℕ) (x ctx : BitString) (t : ℕ) :
    dyadicValue (vertexMassApprox term A (x.length + t) x ctx) (x.length + t)
      = vertexWeight term x * dyadicValue (A t x ctx) t := by
  have ht : x.length + t - x.length = t := by omega
  rw [vertexMassApprox, if_neg (by omega), ht, vertexWeight, dyadicValue, dyadicValue,
    dyadicValue]
  have hbd : ((2 : ℝ≥0∞) ^ x.length)⁻¹ * ((2 : ℝ≥0∞) ^ t)⁻¹
      = ((2 : ℝ≥0∞) ^ x.length * (2 : ℝ≥0∞) ^ t)⁻¹ :=
    (ENNReal.mul_inv (Or.inl (by positivity))
      (Or.inl (ENNReal.pow_ne_top (by norm_num)))).symm
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, pow_add, ← hbd]
  push_cast
  ring

/-- For a computable measure and computable weights the product of vertex weight and cylinder mass
is
lower semicomputable. -/
lemma isLSC_vertexWeight_mul_cantorMass {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) {term : ℕ → BitString → ℕ}
    (hterm : Computable fun p : ℕ × BitString => term p.1 p.2) :
    IsLSC fun (x : BitString) (_ : BitString) => vertexWeight term x * cantorMass μ x := by
  obtain ⟨A, hAmono, hAsup, hAcomp⟩ := isLSC_cantorMass hμ
  refine ⟨vertexMassApprox term A, ?_, ?_, ?_⟩
  · intro s out ctx
    by_cases h : s < out.length
    · rw [vertexMassApprox, if_pos h]
      simp [dyadicValue]
    · obtain ⟨t, rfl⟩ : ∃ t, s = out.length + t := ⟨s - out.length, by omega⟩
      rw [show out.length + t + 1 = out.length + (t + 1) by omega,
        dyadicValue_vertexMassApprox, dyadicValue_vertexMassApprox]
      exact mul_le_mul_right (hAmono t out ctx) _
  · intro out ctx
    have hkey : (⨆ s : ℕ, dyadicValue (vertexMassApprox term A s out ctx) s)
        = ⨆ t : ℕ, vertexWeight term out * dyadicValue (A t out ctx) t := by
      refine le_antisymm (iSup_le fun s => ?_) (iSup_le fun t => ?_)
      · by_cases h : s < out.length
        · rw [vertexMassApprox, if_pos h]
          simp [dyadicValue]
        · obtain ⟨t, rfl⟩ : ∃ t, s = out.length + t := ⟨s - out.length, by omega⟩
          rw [dyadicValue_vertexMassApprox]
          exact le_iSup (fun t => vertexWeight term out * dyadicValue (A t out ctx) t) t
      · refine le_iSup_of_le (out.length + t) ?_
        rw [dyadicValue_vertexMassApprox]
    rw [hkey, ← ENNReal.mul_iSup, hAsup out ctx]
  · have hlen : Computable fun p : ℕ × BitString × BitString => p.2.1.length :=
      Computable.list_length.comp (Computable.fst.comp Computable.snd)
    have hsub : Computable₂ (fun u v : ℕ => u - v) := Primrec.nat_sub.to_comp
    have hmul : Computable₂ (fun u v : ℕ => u * v) := Primrec.nat_mul.to_comp
    have hlt : Computable₂ (fun u v : ℕ => decide (u < v)) := primrec_decide_nat_lt.to_comp
    have hcond : Computable fun p : ℕ × BitString × BitString =>
        decide (p.1 < p.2.1.length) := hlt.comp Computable.fst hlen
    have hterm' : Computable fun p : ℕ × BitString × BitString =>
        term p.2.1.length p.2.1 := hterm.comp (Computable.pair hlen
          (Computable.fst.comp Computable.snd))
    have hAval : Computable fun p : ℕ × BitString × BitString =>
        A (p.1 - p.2.1.length) p.2.1 p.2.2 :=
      hAcomp.comp (Computable.pair (hsub.comp Computable.fst hlen)
        (Computable.pair (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.snd)))
    refine (Computable.cond hcond (Computable.const 0)
      (hmul.comp hterm' hAval)).of_eq fun p => ?_
    by_cases h : p.1 < p.2.1.length <;> simp [vertexMassApprox, h]

/-! ### Maximality -/

/-- **SUV Problem 146 (Section 5.6, p. 150)**: `ω ↦ ∑_{x ⊑ ω} m(x)/p(x)` dominates every
expectation-bounded randomness test for `μ` up to a constant factor. -/
theorem maximal_prefixSumRatio {μ : Measure CantorSeq} [IsFiniteMeasure μ]
    (hμ : IsComputableMeasure μ)
    {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m) (v : CantorSeq → ℝ≥0∞)
    (hv : IsExpectationBoundedRandomnessTest μ v) :
    ∃ c : NNReal, ∀ w : CantorSeq, v w ≤ c * prefixSumRatio m μ w := by
  obtain ⟨term, hterm, hvterm⟩ := ((lowerSemicomputableFun_characterizations v).2.2).mp hv.1
  have hv_u : ∀ w : CantorSeq, v w = ∑' s : ℕ, vertexWeight term (cantorPrefix w s) := by
    intro w
    rw [hvterm w]
    exact tsum_congr fun s => (vertexWeight_cantorPrefix term w s).symm
  have hmeas : ∀ n : ℕ,
      AEMeasurable (fun w : CantorSeq => vertexWeight term (cantorPrefix w n)) μ :=
    fun n => (measurable_comp_cantorPrefix n (vertexWeight term)).aemeasurable
  have hmass : (∑' x : BitString, vertexWeight term x * cantorMass μ x) ≤ 1 := by
    calc (∑' x : BitString, vertexWeight term x * cantorMass μ x)
        = ∑' n : ℕ, ∑ y ∈ levelFinset n, vertexWeight term y * cantorMass μ y :=
          tsum_eq_tsum_sum_levelFinset _
      _ = ∑' n : ℕ, ∫⁻ w, vertexWeight term (cantorPrefix w n) ∂μ :=
          tsum_congr fun n => (lintegral_comp_cantorPrefix μ n (vertexWeight term)).symm
      _ = ∫⁻ w, ∑' n : ℕ, vertexWeight term (cantorPrefix w n) ∂μ := (lintegral_tsum hmeas).symm
      _ = ∫⁻ w, v w ∂μ := lintegral_congr fun w => (hv_u w).symm
      _ ≤ 1 := hv.2
  obtain ⟨c, hc, hdom⟩ := hm.2 (fun x => vertexWeight term x * cantorMass μ x)
    ⟨hmass, isLSC_vertexWeight_mul_cantorMass hμ hterm⟩
  obtain ⟨k, hk⟩ := exists_inv_two_pow_lt hc.ne'
  have hbound : ∀ y : BitString,
      vertexWeight term y ≤ (2 : ℝ≥0∞) ^ k * (m y / cantorMass μ y) := by
    intro y
    have hkey : (2 : ℝ≥0∞)⁻¹ ^ k * (vertexWeight term y * cantorMass μ y) ≤ m y :=
      le_trans (mul_le_mul_left hk.le _) (hdom y)
    rcases eq_or_ne (cantorMass μ y) 0 with h0 | h0
    · have hmy : m y ≠ 0 := (universalSemimeasure_pos hm y).ne'
      rw [h0, ENNReal.div_zero hmy, ENNReal.mul_top (by positivity)]
      exact le_top
    · have hdivle : (2 : ℝ≥0∞)⁻¹ ^ k * vertexWeight term y ≤ m y / cantorMass μ y := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (measure_ne_top μ _)), mul_assoc]
        exact hkey
      calc vertexWeight term y
          = (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹ ^ k * vertexWeight term y) := by
            rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
              one_pow, one_mul]
        _ ≤ (2 : ℝ≥0∞) ^ k * (m y / cantorMass μ y) := by gcongr
  refine ⟨(2 : NNReal) ^ k, fun w => ?_⟩
  have hcast : (((2 : NNReal) ^ k : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by
    push_cast
    ring
  rw [hcast, hv_u w, prefixSumRatio, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun s => hbound _

end Kolmogorov
