/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.AlgorithmicRandomness.BlockMap
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveLaws
import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison
import KolmogorovMathlib.Entropy.Complexity.ShannonCoding.RealProbabilities
import KolmogorovMathlib.CommonInformation.FixedFrequency
import KolmogorovMathlib.Complexity.CanonicalObjects.Counting
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Complexity of the prefixes of a random sequence, and complexity deviations

SUV Sections 7.3.3 and 7.3.4, pp. 229–230.

Theorem 148 says that for a Martin-Löf random sequence `ω` with respect to the Bernoulli measure
with parameters `p₁, …, p_k` the complexity of the length-`N` prefix of `ω`, divided by `N`, tends
to the Shannon entropy `H = ∑_i p_i(−log p_i)`.  Theorem 149 is its finite counterpart: the
complexity of an i.i.d. word of length `N` stays within `c√N` of `N H` with probability at least
`1 − ε`.

**The alphabet of Theorems 148 and the problems around it.**  The book defines Martin-Löf
randomness for the binary alphabet and remarks that "essentially the same definition" works for
any finite alphabet.  The library's `IsMartinLofRandom` is likewise binary, on
`CantorSeq = ℕ → Bool`, and the Bernoulli measures available are the binary ones
(`bernoulliMeasure p hp`).  Theorems 148 and Problems 238–239 are therefore stated for `k = 2`;
the entropy is `H = −p log p − (1−p) log (1−p)`, written `negMulLog2 p + negMulLog2 (1 − p)`.
The `k`-letter generality of the book is not formalised, because it would need the `k`-ary product
measure on `A^∞` and a transport of Martin-Löf randomness through the block encoding.

Theorem 149 is about finite words and needs no randomness notion, so it is stated for a general
`k`-letter alphabet, with the block encoding `finWordBits` and the probability `probOfPred` of
`KolmogorovMathlib.Entropy.Complexity.Basic`.

Complexities are plain (`plainK`), as in the book, and `ENat.toNat` is faithful because an optimal
decompressor gives every string a finite complexity.
-/

namespace Kolmogorov

open Filter Finset

/-! ### Theorem 148: prefixes of a random sequence -/

private noncomputable def bernoulliCrossEntropy (p q : ℝ) : ℝ :=
  q * (-Real.logb 2 p) + (1 - q) * (-Real.logb 2 (1 - p))

private lemma tendsto_bernoulliCrossEntropy_freqOne {p : NNReal} (hp : p ≤ 1)
    (hcomp : ComputableReals.IsComputableReal (p : ℝ)) {ω : CantorSeq}
    (hω : IsMartinLofRandom (bernoulliMeasure p hp) ω) :
    Tendsto (fun N => bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ)) atTop
      (nhds (negMulLog2 (p : ℝ) + negMulLog2 (1 - (p : ℝ)))) := by
  have hfreq := tendsto_freqOne_of_isMartinLofRandom_bernoulli hp hcomp hω
  have hcont : Continuous (bernoulliCrossEntropy (p : ℝ)) := by
    unfold bernoulliCrossEntropy; fun_prop
  have h := hcont.continuousAt.tendsto.comp hfreq
  have heq : bernoulliCrossEntropy (p : ℝ) (p : ℝ) =
      negMulLog2 (p : ℝ) + negMulLog2 (1 - (p : ℝ)) := by
    simp only [bernoulliCrossEntropy, negMulLog2, Real.negMulLog, Real.logb]
    ring
  rwa [← heq]

private lemma neg_log_cantorMass_bernoulli_cantorPrefix {p : NNReal} (hp : p ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) (ω : CantorSeq) {N : ℕ} (hN : 0 < N) :
    -Real.logb 2
        (cantorMass (bernoulliMeasure p hp) (cantorPrefix ω N)).toReal =
      (N : ℝ) * bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
  have hpR1 : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hqR : 0 < 1 - (p : ℝ) := sub_pos.mpr hpR1
  have hpENN : (p : ENNReal) ≤ 1 := by exact_mod_cast hp
  rw [cantorMass_bernoulliMeasure_prod, prod_map_ite_bool, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hpENN (by simp)]
  simp only [ENNReal.coe_toReal, ENNReal.toReal_one]
  rw [Real.logb_mul (pow_ne_zero _ hpR.ne') (pow_ne_zero _ hqR.ne'),
    Real.logb_pow, Real.logb_pow]
  have hfreq : (freqOne ω N : ℝ) =
      ((cantorPrefix ω N).count true : ℝ) / N := by
    rw [freqOne]
    push_cast
    rfl
  have hcount := count_true_add_count_false (cantorPrefix ω N)
  rw [cantorPrefix_length] at hcount
  have hcountR : ((cantorPrefix ω N).count true : ℝ) +
      ((cantorPrefix ω N).count false : ℝ) = N := by exact_mod_cast hcount
  have hfalse : ((cantorPrefix ω N).count false : ℝ) =
      N - ((cantorPrefix ω N).count true : ℝ) := by linarith [hcountR]
  rw [hfreq]
  unfold bernoulliCrossEntropy
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  rw [hfalse]
  ring

private def bernoulliParamApprox (f : ℚ → ℚ) (x : BitString) (s : ℕ) : ℚ :=
  max 0 (min 1 (f ((2 : ℚ)⁻¹ ^ (s + x.length + 2))))

private def bernoulliMassRatApprox (f : ℚ → ℚ) (x : BitString) (s : ℕ) : ℚ :=
  (bernoulliParamApprox f x s) ^ x.count true *
    (1 - bernoulliParamApprox f x s) ^ x.count false

private def bernoulliMassApprox (f : ℚ → ℚ) (x : BitString) (s : ℕ) : ℕ :=
  (ratDyadicFloor (bernoulliMassRatApprox f x s) (s + 1) + 1) / 2

private lemma computable_rat_pow : Computable (fun z : ℚ × ℕ => z.1 ^ z.2) := by
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

private lemma bernoulliParamApprox_computable {f : ℚ → ℚ} (hf : Computable f) :
    Computable₂ (bernoulliParamApprox f) := by
  have hexp : Computable (fun z : BitString × ℕ => z.2 + z.1.length + 2) :=
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))
      (Primrec.const 2)).to_comp
  have hε : Computable (fun z : BitString × ℕ =>
      (2 : ℚ)⁻¹ ^ (z.2 + z.1.length + 2)) := computable_pow_half.comp hexp
  exact ((ComputableReals.primrec_ratMax.to_comp).comp (Computable.const 0)
    ((ComputableReals.primrec_ratMin.to_comp).comp
      (Computable.const 1) (hf.comp hε))).to₂.of_eq fun _ => rfl

private lemma bitString_count_false_computable :
    Computable (fun x : BitString => x.count false) := by
  have hsub : Computable (fun x : BitString => x.length - x.count true) :=
    Primrec.nat_sub.to_comp.comp Primrec.list_length.to_comp primrec_count_true.to_comp
  exact hsub.of_eq fun x => by
    rw [← count_true_add_count_false x, Nat.add_sub_cancel_left]

private lemma bernoulliMassRatApprox_truePow_computable {f : ℚ → ℚ}
    (hf : Computable f) : Computable₂ (fun x s =>
      bernoulliParamApprox f x s ^ x.count true) := by
  have hparam : Computable (fun z : BitString × ℕ =>
      bernoulliParamApprox f z.1 z.2) := bernoulliParamApprox_computable hf
  have hcount : Computable (fun z : BitString × ℕ => z.1.count true) :=
    primrec_count_true.to_comp.comp Computable.fst
  exact (computable_rat_pow.comp (hparam.pair hcount)).to₂

private lemma bernoulliMassRatApprox_falsePow_computable {f : ℚ → ℚ}
    (hf : Computable f) : Computable₂ (fun x s =>
      (1 - bernoulliParamApprox f x s) ^ x.count false) := by
  have hparam : Computable (fun z : BitString × ℕ =>
      bernoulliParamApprox f z.1 z.2) := bernoulliParamApprox_computable hf
  have hcomplement : Computable (fun z : BitString × ℕ =>
      1 - bernoulliParamApprox f z.1 z.2) :=
    computable₂_ratSub.comp (Computable.const 1) hparam
  have hcount : Computable (fun z : BitString × ℕ => z.1.count false) :=
    bitString_count_false_computable.comp Computable.fst
  exact (computable_rat_pow.comp (hcomplement.pair hcount)).to₂

private lemma bernoulliMassRatApprox_computable {f : ℚ → ℚ} (hf : Computable f) :
    Computable₂ (bernoulliMassRatApprox f) := by
  exact (computable₂_ratMul.comp₂
    (bernoulliMassRatApprox_truePow_computable hf)
    (bernoulliMassRatApprox_falsePow_computable hf)).of_eq fun ⟨_, _⟩ => rfl

private lemma bernoulliMassApprox_computable {f : ℚ → ℚ} (hf : Computable f) :
    Computable₂ (bernoulliMassApprox f) := by
  have hr := bernoulliMassRatApprox_computable hf
  change Computable (fun z : BitString × ℕ =>
    bernoulliMassRatApprox f z.1 z.2) at hr
  have hs : Computable (fun z : BitString × ℕ => z.2 + 1) :=
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).to_comp
  have hfloor : Computable (fun z : BitString × ℕ =>
      ratDyadicFloor (bernoulliMassRatApprox f z.1 z.2) (z.2 + 1)) :=
    computable_ratDyadicFloor.comp hr hs
  have hadd : Computable (fun z : BitString × ℕ =>
      ratDyadicFloor (bernoulliMassRatApprox f z.1 z.2) (z.2 + 1) + 1) :=
    Primrec.nat_add.to_comp.comp hfloor (Computable.const 1)
  exact (Primrec.nat_div.to_comp.comp hadd (Computable.const 2)).to₂.of_eq fun _ => rfl

private lemma abs_sub_clamp_le_abs_sub {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    |a - max 0 (min 1 b)| ≤ |a - b| := by
  by_cases hb₀ : b ≤ 0
  · rw [min_eq_right (hb₀.trans zero_le_one), max_eq_left hb₀, sub_zero, abs_of_nonneg ha₀,
      abs_of_nonneg (sub_nonneg.mpr (hb₀.trans ha₀))]
    linarith
  · have hb₀' : 0 ≤ b := le_of_not_ge hb₀
    by_cases hb₁ : b ≤ 1
    · rw [min_eq_right hb₁, max_eq_right hb₀']
    · have hb₁' : 1 ≤ b := le_of_not_ge hb₁
      rw [min_eq_left hb₁', max_eq_right zero_le_one, abs_of_nonpos (sub_nonpos.mpr ha₁),
        abs_of_nonpos (sub_nonpos.mpr (ha₁.trans hb₁'))]
      linarith

private lemma bernoulliParamApprox_error {p : NNReal} (hp : p ≤ 1)
    {f : ℚ → ℚ} (hf : ∀ e : ℚ, 0 < e → |(p : ℝ) - (f e : ℝ)| ≤ (e : ℝ))
    (x : BitString) (s : ℕ) :
    |(p : ℝ) - (bernoulliParamApprox f x s : ℝ)| ≤
      ((2 : ℚ)⁻¹ ^ (s + x.length + 2) : ℚ) := by
  let e : ℚ := (2 : ℚ)⁻¹ ^ (s + x.length + 2)
  have he : 0 < e := by positivity
  have hraw := hf e he
  have hp₀ : (0 : ℝ) ≤ p := by positivity
  have hp₁ : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hclip := abs_sub_clamp_le_abs_sub hp₀ hp₁ (b := (f e : ℝ))
  simpa [bernoulliParamApprox, e, Rat.cast_max, Rat.cast_min] using hclip.trans hraw

private lemma abs_pow_sub_pow_le_nat_mul {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (n : ℕ) :
    |a ^ n - b ^ n| ≤ n * |a - b| := by
  have habs : max |a| |b| ≤ 1 := by
    rw [abs_of_nonneg ha₀, abs_of_nonneg hb₀]
    exact max_le ha₁ hb₁
  calc
    |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) :=
      abs_pow_sub_pow_le a b n
    _ ≤ |a - b| * n * 1 := by
      gcongr
      exact pow_le_one₀ ((abs_nonneg a).trans (le_max_left _ _)) habs
    _ = n * |a - b| := by ring

private lemma bernoulli_monomial_stable {a b : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (m n : ℕ) :
    |a ^ m * (1 - a) ^ n - b ^ m * (1 - b) ^ n| ≤
      (m + n) * |a - b| := by
  have hpowA : |a ^ m| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg ha₀ _)]
    exact pow_le_one₀ ha₀ ha₁
  have hpowB : |b ^ m| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hb₀ _)]
    exact pow_le_one₀ hb₀ hb₁
  have hcompA₀ : 0 ≤ 1 - a := sub_nonneg.mpr ha₁
  have hcompA₁ : 1 - a ≤ 1 := by linarith
  have hcompB₀ : 0 ≤ 1 - b := sub_nonneg.mpr hb₁
  have hcompB₁ : 1 - b ≤ 1 := by linarith
  have hpowCompA : |(1 - a) ^ n| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hcompA₀ _)]
    exact pow_le_one₀ hcompA₀ hcompA₁
  have hm := abs_pow_sub_pow_le_nat_mul ha₀ ha₁ hb₀ hb₁ m
  have hn := abs_pow_sub_pow_le_nat_mul hcompA₀ hcompA₁ hcompB₀ hcompB₁ n
  calc
    |a ^ m * (1 - a) ^ n - b ^ m * (1 - b) ^ n|
        ≤ |(a ^ m - b ^ m) * (1 - a) ^ n| +
            |b ^ m * ((1 - a) ^ n - (1 - b) ^ n)| := by
          rw [show a ^ m * (1 - a) ^ n - b ^ m * (1 - b) ^ n =
            (a ^ m - b ^ m) * (1 - a) ^ n +
              b ^ m * ((1 - a) ^ n - (1 - b) ^ n) by ring]
          exact abs_add_le _ _
    _ = |a ^ m - b ^ m| * |(1 - a) ^ n| +
          |b ^ m| * |(1 - a) ^ n - (1 - b) ^ n| := by rw [abs_mul, abs_mul]
    _ ≤ m * |a - b| * 1 + 1 * (n * |(1 - a) - (1 - b)|) := by
      gcongr
    _ = (m + n) * |a - b| := by
      rw [show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg]
      ring

private lemma nat_mul_inv_two_pow_add_le (n s : ℕ) :
    (n : ℝ) * (2 : ℝ)⁻¹ ^ (s + n + 2) ≤ (2 : ℝ)⁻¹ ^ (s + 2) := by
  have hnNat : n ≤ 2 ^ n := by
    simpa using Nat.choose_le_two_pow n 1
  have hnReal : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hnNat
  calc
    (n : ℝ) * (2 : ℝ)⁻¹ ^ (s + n + 2)
        ≤ (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ (s + n + 2) := by gcongr
    _ = (2 : ℝ)⁻¹ ^ (s + 2) := by
      rw [show s + n + 2 = (s + 2) + n by omega, pow_add]
      calc
        (2 : ℝ) ^ n * ((2 : ℝ)⁻¹ ^ (s + 2) * (2 : ℝ)⁻¹ ^ n) =
            (2 : ℝ)⁻¹ ^ (s + 2) * ((2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n) :=
          by ring
        _ = (2 : ℝ)⁻¹ ^ (s + 2) := by rw [← mul_pow]; norm_num

private lemma bernoulliMassRatApprox_error {p : NNReal} (hp : p ≤ 1)
    {f : ℚ → ℚ} (hf : ∀ e : ℚ, 0 < e → |(p : ℝ) - (f e : ℝ)| ≤ (e : ℝ))
    (x : BitString) (s : ℕ) :
    |(bernoulliMassRatApprox f x s : ℝ) -
        (cantorMass (bernoulliMeasure p hp) x).toReal| ≤
      (2 : ℝ)⁻¹ ^ (s + 2) := by
  let q : ℝ := bernoulliParamApprox f x s
  have hp₀ : (0 : ℝ) ≤ p := by positivity
  have hp₁ : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hq₀ : 0 ≤ q := by
    dsimp [q, bernoulliParamApprox]
    norm_cast
    exact le_max_left _ _
  have hq₁ : q ≤ 1 := by
    dsimp [q, bernoulliParamApprox]
    norm_cast
    exact max_le zero_le_one (min_le_left _ _)
  have hstable := bernoulli_monomial_stable hq₀ hq₁ hp₀ hp₁
    (x.count true) (x.count false)
  have hparam := bernoulliParamApprox_error hp hf x s
  have hcountR : (x.count true : ℝ) + x.count false = x.length := by
    exact_mod_cast count_true_add_count_false x
  have hpoly :
      |q ^ x.count true * (1 - q) ^ x.count false -
          (p : ℝ) ^ x.count true * (1 - (p : ℝ)) ^ x.count false| ≤
        (x.length : ℝ) * (2 : ℝ)⁻¹ ^ (s + x.length + 2) := by
    calc
      _ ≤ (x.count true + x.count false) * |q - (p : ℝ)| := hstable
      _ = (x.length : ℝ) * |(p : ℝ) - q| := by
        rw [abs_sub_comm, hcountR]
      _ ≤ (x.length : ℝ) *
          ((2 : ℚ)⁻¹ ^ (s + x.length + 2) : ℚ) := by gcongr
      _ = (x.length : ℝ) * (2 : ℝ)⁻¹ ^ (s + x.length + 2) := by
        norm_num
  have hmassReal : (cantorMass (bernoulliMeasure p hp) x).toReal =
      (p : ℝ) ^ x.count true * (1 - (p : ℝ)) ^ x.count false := by
    have hpENN : (p : ENNReal) ≤ 1 := by exact_mod_cast hp
    rw [cantorMass_bernoulliMeasure_prod, prod_map_ite_bool,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hpENN (by simp)]
    simp
  rw [hmassReal]
  have hratReal : (bernoulliMassRatApprox f x s : ℝ) =
      q ^ x.count true * (1 - q) ^ x.count false := by
    dsimp [q, bernoulliMassRatApprox]
    norm_cast
  rw [hratReal]
  exact hpoly.trans (nat_mul_inv_two_pow_add_le x.length s)

private lemma bernoulliMassApprox_rounding_error (f : ℚ → ℚ) (x : BitString) (s : ℕ) :
    |(dyadicValue (bernoulliMassApprox f x s) s).toReal -
        (bernoulliMassRatApprox f x s : ℝ)| ≤
      (2 : ℝ)⁻¹ ^ (s + 1) := by
  let q := bernoulliMassRatApprox f x s
  let A := ratDyadicFloor q (s + 1)
  let B := (A + 1) / 2
  have hq₀ : (0 : ℚ) ≤ q := by
    have hparam₀ : (0 : ℚ) ≤ bernoulliParamApprox f x s := le_max_left _ _
    have hparam₁ : bernoulliParamApprox f x s ≤ 1 := max_le zero_le_one (min_le_left _ _)
    dsimp [q, bernoulliMassRatApprox]
    exact mul_nonneg (pow_nonneg hparam₀ _) (pow_nonneg (sub_nonneg.mpr hparam₁) _)
  have hAB : A ≤ 2 * B ∧ 2 * B ≤ A + 1 := by
    have hmod := Nat.mod_lt (A + 1) (by omega : 0 < 2)
    have hdivmod := Nat.div_add_mod (A + 1) 2
    dsimp [B]
    omega
  have hfloor : (A : ℝ) ≤ (q : ℝ) * (2 : ℝ) ^ (s + 1) := by
    dsimp [A]
    rw [ratDyadicFloor_eq_floor]
    exact_mod_cast Nat.floor_le (mul_nonneg (by exact_mod_cast hq₀) (by positivity))
  have hceil : (q : ℝ) * (2 : ℝ) ^ (s + 1) ≤ A + 1 := by
    have hceilQ : q * (2 ^ (s + 1) : ℕ) ≤
        ⌊q * (2 ^ (s + 1) : ℕ)⌋₊ + 1 := (Nat.lt_floor_add_one (q * (2 ^ (s + 1) : ℕ))).le
    dsimp [A]
    rw [ratDyadicFloor_eq_floor]
    exact_mod_cast hceilQ
  have hscaled : |(2 * B : ℕ) - (q : ℝ) * (2 : ℝ) ^ (s + 1)| ≤ 1 := by
    have hABR : (A : ℝ) ≤ 2 * B ∧ 2 * (B : ℝ) ≤ (A : ℝ) + 1 := by exact_mod_cast hAB
    rw [abs_le]
    norm_num at ⊢
    constructor <;> linarith [hfloor, hceil, hABR.1, hABR.2]
  have happ : bernoulliMassApprox f x s = B := by rfl
  rw [happ]
  simp only [dyadicValue, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  change |(B : ℝ) / (2 : ℝ) ^ s - (q : ℝ)| ≤ (2 : ℝ)⁻¹ ^ (s + 1)
  have heq : (B : ℝ) / (2 : ℝ) ^ s - (q : ℝ) =
      ((2 * B : ℕ) - (q : ℝ) * (2 : ℝ) ^ (s + 1)) /
        (2 : ℝ) ^ (s + 1) := by
    field_simp
    norm_num [pow_succ]
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (s + 1))]
  calc
    |(2 * B : ℕ) - (q : ℝ) * (2 : ℝ) ^ (s + 1)| /
          (2 : ℝ) ^ (s + 1)
        ≤ 1 / (2 : ℝ) ^ (s + 1) := by gcongr
    _ = (2 : ℝ)⁻¹ ^ (s + 1) := by rw [inv_pow, one_div]

private lemma bernoulliMassApprox_toReal_error {p : NNReal} (hp : p ≤ 1)
    {f : ℚ → ℚ} (hf : ∀ e : ℚ, 0 < e → |(p : ℝ) - (f e : ℝ)| ≤ (e : ℝ))
    (x : BitString) (s : ℕ) :
    |(dyadicValue (bernoulliMassApprox f x s) s).toReal -
        (cantorMass (bernoulliMeasure p hp) x).toReal| ≤
      (dyadicValue 1 s).toReal := by
  have hround := bernoulliMassApprox_rounding_error f x s
  have hmass := bernoulliMassRatApprox_error hp hf x s
  calc
    |(dyadicValue (bernoulliMassApprox f x s) s).toReal -
        (cantorMass (bernoulliMeasure p hp) x).toReal|
        ≤ |(dyadicValue (bernoulliMassApprox f x s) s).toReal -
              (bernoulliMassRatApprox f x s : ℝ)| +
            |(bernoulliMassRatApprox f x s : ℝ) -
              (cantorMass (bernoulliMeasure p hp) x).toReal| := by
          exact abs_sub_le _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (s + 1) + (2 : ℝ)⁻¹ ^ (s + 2) :=
      add_le_add hround hmass
    _ ≤ (dyadicValue 1 s).toReal := by
      norm_num [dyadicValue, pow_succ]
      rw [← inv_pow]
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) s]

private lemma ennreal_pair_bounds_of_toReal_abs_le {a b e : ENNReal}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (he : e ≠ ⊤)
    (h : |a.toReal - b.toReal| ≤ e.toReal) : a ≤ b + e ∧ b ≤ a + e := by
  rw [abs_le] at h
  constructor
  · rw [← ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hb, he⟩),
      ENNReal.toReal_add hb he]
    linarith
  · rw [← ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.mpr ⟨ha, he⟩),
      ENNReal.toReal_add ha he]
    linarith

private lemma bernoulliMassApprox_bounds {p : NNReal} (hp : p ≤ 1)
    {f : ℚ → ℚ} (hf : ∀ e : ℚ, 0 < e → |(p : ℝ) - (f e : ℝ)| ≤ (e : ℝ))
    (x : BitString) (s : ℕ) :
    dyadicValue (bernoulliMassApprox f x s) s ≤
        cantorMass (bernoulliMeasure p hp) x + dyadicValue 1 s ∧
      cantorMass (bernoulliMeasure p hp) x ≤
        dyadicValue (bernoulliMassApprox f x s) s + dyadicValue 1 s := by
  exact ennreal_pair_bounds_of_toReal_abs_le (dyadicValue_lt_top _ _).ne
    (MeasureTheory.measure_lt_top _ _).ne (dyadicValue_lt_top _ _).ne
    (bernoulliMassApprox_toReal_error hp hf x s)

private lemma isComputableMeasure_bernoulli_of_isComputableReal {p : NNReal}
    (hp : p ≤ 1) (hcomp : ComputableReals.IsComputableReal (p : ℝ)) :
    IsComputableMeasure (bernoulliMeasure p hp) := by
  obtain ⟨f, hf, hbound⟩ := hcomp
  exact ⟨bernoulliMassApprox f, bernoulliMassApprox_computable hf,
    bernoulliMassApprox_bounds hp hbound⟩

private lemma cantorMass_bernoulli_ne_zero {p : NNReal} (hp : p ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) (x : BitString) :
    cantorMass (bernoulliMeasure p hp) x ≠ 0 := by
  rw [cantorMass_bernoulliMeasure_prod]
  apply List.prod_ne_zero
  simp only [List.mem_map, not_exists, not_and]
  intro a ha
  split
  · exact ENNReal.coe_ne_zero.mpr hp0.ne'
  · exact (tsub_pos_of_lt (by exact_mod_cast hp1)).ne'

private lemma abs_toNat_add_logb_toReal_le_of_weight_bounds {k : ENat} (hk : k ≠ ⊤)
    {m : ENNReal} (hm0 : m ≠ 0) (hmtop : m ≠ ⊤) {a b : ℕ}
    (hlow : (2 : ENNReal)⁻¹ ^ a * m ≤ complexityWeight k)
    (hupp : complexityWeight k ≤ (2 : ENNReal) ^ b * m) :
    |(k.toNat : ℝ) + Real.logb 2 m.toReal| ≤ max a b := by
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
  have hweight : complexityWeight k = (2 : ENNReal)⁻¹ ^ k.toNat := by
    conv_lhs => rw [← ENat.natCast_toNat hk]
    rw [complexityWeight_coe]
  rw [hweight] at hlow hupp
  have hlowR := ENNReal.toReal_mono (by finiteness :
    (2 : ENNReal)⁻¹ ^ k.toNat ≠ ⊤) hlow
  have huppR := ENNReal.toReal_mono (by finiteness :
    (2 : ENNReal) ^ b * m ≠ ⊤) hupp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat] at hlowR huppR
  have hpowInv : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := fun n => by positivity
  have hpow : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  have hlogLow := (Real.logb_le_logb (b := 2) (by norm_num)
    (mul_pos (hpowInv a) hmR) (hpowInv k.toNat)).mpr hlowR
  have hlogUpp := (Real.logb_le_logb (b := 2) (by norm_num)
    (hpowInv k.toNat) (mul_pos (hpow b) hmR)).mpr huppR
  rw [Real.logb_mul (hpowInv a).ne' hmR.ne', Real.logb_pow,
    Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at hlogLow
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by norm_num),
    Real.logb_mul (hpow b).ne' hmR.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at hlogUpp
  rw [abs_le]
  constructor
  · have hbmax : (b : ℝ) ≤ max a b := by exact_mod_cast Nat.le_max_right a b
    linarith
  · have hamax : (a : ℝ) ≤ max a b := by exact_mod_cast Nat.le_max_left a b
    linarith

private lemma exists_const_abs_KMOf_sub_neg_log_cantorMass_le
    (M : BitStream → BitStream) (hM : IsOptimalMonotoneDecompressor M) {p : NNReal}
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hcomp : ComputableReals.IsComputableReal (p : ℝ)) {ω : CantorSeq}
    (hω : IsMartinLofRandom (bernoulliMeasure p hp) ω) :
    ∃ c : ℕ, ∀ N : ℕ,
      |((KMOf M (cantorPrefix ω N)).toNat : ℝ) +
        Real.logb 2
          (cantorMass (bernoulliMeasure p hp) (cantorPrefix ω N)).toReal| ≤ c := by
  have hμ := isComputableMeasure_bernoulli_of_isComputableReal hp hcomp
  obtain ⟨a, ha⟩ :=
    exists_const_cantorMass_mul_le_complexityWeight_KMOf
      (bernoulliMeasure p hp) hμ hM
  obtain ⟨b, hb⟩ := boundedMonotoneDeficiency_of_isMartinLofRandom hμ hM hω
  exact ⟨max a b, fun N => abs_toNat_add_logb_toReal_le_of_weight_bounds
    (KMOf_ne_top_of_isOptimal hM _) (cantorMass_bernoulli_ne_zero hp hp0 hp1 _)
    (MeasureTheory.measure_ne_top _ _) (ha _) (hb N)⟩

private lemma tendsto_KMOf_div_sub_bernoulliCrossEntropy_freqOne
    (M : BitStream → BitStream) (hM : IsOptimalMonotoneDecompressor M) {p : NNReal}
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hcomp : ComputableReals.IsComputableReal (p : ℝ)) {ω : CantorSeq}
    (hω : IsMartinLofRandom (bernoulliMeasure p hp) ω) :
    Tendsto (fun N => ((KMOf M (cantorPrefix ω N)).toNat : ℝ) / N -
      bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ)) atTop (nhds 0) := by
  obtain ⟨c, hc⟩ := exists_const_abs_KMOf_sub_neg_log_cantorMass_le
    M hM hp hp0 hp1 hcomp hω
  have hbound : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmass := neg_log_cantorMass_bernoulli_cantorPrefix hp hp0 hp1 ω hN
  rw [Real.norm_eq_abs]
  calc
    |((KMOf M (cantorPrefix ω N)).toNat : ℝ) / N -
        bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ)| =
        |(((KMOf M (cantorPrefix ω N)).toNat : ℝ) +
          Real.logb 2
            (cantorMass (bernoulliMeasure p hp) (cantorPrefix ω N)).toReal) / N| := by
      congr 1
      have hlog :
          Real.logb 2
              (cantorMass (bernoulliMeasure p hp) (cantorPrefix ω N)).toReal =
            -(N : ℝ) * bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ) := by
        linarith [hmass]
      rw [hlog]
      field_simp
      ring
    _ =
        |((KMOf M (cantorPrefix ω N)).toNat : ℝ) +
          Real.logb 2
            (cantorMass (bernoulliMeasure p hp) (cantorPrefix ω N)).toReal| / N := by
      rw [abs_div, abs_of_pos hNreal]
    _ ≤ c / N := div_le_div_of_nonneg_right (hc N) hNreal.le

private lemma tendsto_plainK_sub_KMOf_div (D : Map) (hD : isOptimalConditional D)
    (M : BitStream → BitStream) (hM : IsOptimalMonotoneDecompressor M) (ω : CantorSeq) :
    Tendsto (fun N => (((plainK D (cantorPrefix ω N)).toNat : ℝ) -
      ((KMOf M (cantorPrefix ω N)).toNat : ℝ)) / N) atTop (nhds 0) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := exists_const_abs_plainK_sub_KMOf_le_log D U hD hU hM
  have hshift : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) / N) atTop
      (nhds 0) := by
    have h :=
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-1) 1 one_ne_zero).comp hshift
    refine h.congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hconst : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hbound : Tendsto
      (fun N : ℕ => (2 * Real.logb 2 ((N : ℝ) + 1) + c) / N) atTop (nhds 0) := by
    have h := (hlog.const_mul 2).add hconst
    have h' : Tendsto
        (fun N : ℕ => 2 * (Real.logb 2 ((N : ℝ) + 1) / N) + c / N) atTop
        (nhds 0) := by simpa using h
    refine h'.congr' ?_
    filter_upwards with N
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have h := hc (cantorPrefix ω N)
  rw [cantorPrefix_length] at h
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hNreal]
  exact (div_le_div_iff_of_pos_right hNreal).2 h

/-- **The complexity per letter of the prefixes of a random sequence tends to the entropy.**  For
a computable parameter `p` strictly between `0` and `1` and a sequence `ω` that is Martin-Löf
random with respect to the Bernoulli measure with parameter `p`, the ratio `C((ω)_N)/N` tends to
`H = −p log p − (1−p) log(1−p)`.

**Weaker than the printed statement**: the book states this for every finite alphabet, and this is
the binary case, which is the one the library's Martin-Löf randomness and Bernoulli measures
cover; the `k`-letter case would need the `k`-ary product measure on `A^∞` and a transport of
Martin-Löf randomness through the block encoding.  SUV Theorem 148, p. 229. -/
theorem tendsto_plainK_cantorPrefix_div (D : Map) (hD : isOptimalConditional D) {p : NNReal}
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hcomp : ComputableReals.IsComputableReal (p : ℝ))
    {ω : CantorSeq} (hω : IsMartinLofRandom (bernoulliMeasure p hp) ω) :
    Tendsto (fun N : ℕ => ((plainK D (cantorPrefix ω N)).toNat : ℝ) / N) atTop
      (nhds (negMulLog2 (p : ℝ) + negMulLog2 (1 - (p : ℝ)))) := by
  obtain ⟨M, hM⟩ := exists_optimalMonotoneDecompressor
  have hplain := tendsto_plainK_sub_KMOf_div D hD M hM ω
  have hmono :=
    tendsto_KMOf_div_sub_bernoulliCrossEntropy_freqOne M hM hp hp0 hp1 hcomp hω
  have hcross := tendsto_bernoulliCrossEntropy_freqOne hp hcomp hω
  convert (hplain.add hmono).add hcross using 1 <;> ring_nf

private lemma tendsto_KMOf_cantorPrefix_div_uniform
    (M : BitStream → BitStream) (hM : IsOptimalMonotoneDecompressor M) {ω : CantorSeq}
    (hω : IsMartinLofRandom uniformMeasure ω) :
    Tendsto (fun N : ℕ => ((KMOf M (cantorPrefix ω N)).toNat : ℝ) / N) atTop
      (nhds 1) := by
  obtain ⟨c, hc⟩ :=
    (isMartinLofRandom_uniform_iff_KA_KMOf_eq_length hM ω).mp hω
  have hbound : Tendsto (fun N : ℕ => |c| / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hzero : Tendsto
      (fun N : ℕ => ((KMOf M (cantorPrefix ω N)).toNat : ℝ) / N - 1) atTop
      (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    rw [Real.norm_eq_abs]
    calc
      |((KMOf M (cantorPrefix ω N)).toNat : ℝ) / N - 1| =
          |(((KMOf M (cantorPrefix ω N)).toNat : ℝ) - N) / N| := by
        congr 1
        field_simp
      _ = |((KMOf M (cantorPrefix ω N)).toNat : ℝ) - N| / N := by
        rw [abs_div, abs_of_pos hNreal]
      _ ≤ |c| / N := by
        apply div_le_div_of_nonneg_right _ hNreal.le
        exact (hc N).2.trans (le_abs_self c)
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1

/-- **The uniform case of Theorem 148.**  For the uniform distribution the negated logarithm of
the probability of a prefix of length `N` is exactly `N log k`, so the randomness criterion gives
the limit at once.

**Weaker than the printed statement**: the book states this for the uniform distribution on `k`
letters, with limit `log k`, and this is the binary case `k = 2`, with limit `1`, for the same
reason as in Theorem 148.  SUV Problem 238, p. 229. -/
theorem tendsto_plainK_cantorPrefix_div_uniform (D : Map) (hD : isOptimalConditional D)
    (hp : (1 / 2 : NNReal) ≤ 1) {ω : CantorSeq}
    (hω : IsMartinLofRandom (bernoulliMeasure (1 / 2) hp) ω) :
    Tendsto (fun N : ℕ => ((plainK D (cantorPrefix ω N)).toNat : ℝ) / N) atTop (nhds 1) := by
  obtain ⟨M, hM⟩ := exists_optimalMonotoneDecompressor
  have hω' : IsMartinLofRandom uniformMeasure ω := by
    simpa only [uniformMeasure] using hω
  have hplain := tendsto_plainK_sub_KMOf_div D hD M hM ω
  have hmono := tendsto_KMOf_cantorPrefix_div_uniform M hM hω'
  simpa only [sub_div, sub_add_cancel, zero_add] using hplain.add hmono

/-! ### Problem 239: an arbitrary parameter -/

open MeasureTheory in
/-- For every parameter, including the endpoints, the negated logarithm of the mass of a prefix
is `N` times the cross entropy of the parameter against the frequency of ones. -/
private lemma neg_logb_cantorMass_bernoulli_cantorPrefix_eq {p : NNReal} (hp : p ≤ 1)
    (ω : CantorSeq) {N : ℕ} (hN : 0 < N) :
    -Real.logb 2
        (cantorMass (bernoulliMeasure p hp) (cantorPrefix ω N)).toReal =
      (N : ℝ) * bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ) := by
  rcases eq_or_lt_of_le (zero_le : (0 : NNReal) ≤ p) with rfl | hp0
  · simp [cantorMass_bernoulliMeasure_prod, prod_map_ite_bool, bernoulliCrossEntropy,
      Real.logb_pow]
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp [cantorMass_bernoulliMeasure_prod, prod_map_ite_bool, bernoulliCrossEntropy,
      Real.logb_pow]
  exact neg_log_cantorMass_bernoulli_cantorPrefix hp hp0 hp1 ω hN

open MeasureTheory in
/-- The strong law of large numbers for an arbitrary parameter, transported through the
continuity of the cross entropy: almost surely the cross entropy of `p` against the frequency of
ones tends to the entropy. -/
private lemma ae_tendsto_bernoulliCrossEntropy_freqOne {p : NNReal} (hp : p ≤ 1) :
    ∀ᵐ ω ∂(bernoulliMeasure p hp),
      Tendsto (fun N => bernoulliCrossEntropy (p : ℝ) (freqOne ω N : ℝ)) atTop
        (nhds (negMulLog2 (p : ℝ) + negMulLog2 (1 - (p : ℝ)))) := by
  have hae := ProbabilityTheory.strong_law_ae_real (μ := bernoulliMeasure p hp)
    (fun (i : ℕ) (w : CantorSeq) => bitVal (w i))
    (bernoulli_integrable_coord p hp)
    (fun i j hij => (bernoulli_iIndepFun p hp).indepFun hij)
    (bernoulli_identDistrib p hp)
  rw [bernoulli_integral_coord p hp] at hae
  filter_upwards [hae] with ω hω
  have hfreq : Tendsto (fun n => (freqOne ω n : ℝ)) atTop (nhds (p : ℝ)) := by
    simpa only [freqOne_eq] using hω
  have hcont : Continuous (bernoulliCrossEntropy (p : ℝ)) := by
    unfold bernoulliCrossEntropy; fun_prop
  have h := hcont.continuousAt.tendsto.comp hfreq
  have heq : bernoulliCrossEntropy (p : ℝ) (p : ℝ) =
      negMulLog2 (p : ℝ) + negMulLog2 (1 - (p : ℝ)) := by
    simp only [bernoulliCrossEntropy, negMulLog2, Real.negMulLog, Real.logb]
    ring
  rwa [← heq]

open MeasureTheory in
/-- Almost surely no prefix of the sequence has mass zero: the cylinders of mass zero are
countably many null sets. -/
private lemma ae_cantorMass_cantorPrefix_ne_zero (μ : Measure CantorSeq) :
    ∀ᵐ ω ∂μ, ∀ N, cantorMass μ (cantorPrefix ω N) ≠ 0 := by
  refine ae_all_iff.2 fun N => ?_
  rw [ae_iff]
  simp only [not_not]
  apply measure_mono_null (t := ⋃ x ∈ {x : BitString | cantorMass μ x = 0}, cantorCylinder x)
  · intro ω hω
    exact Set.mem_biUnion (x := cantorPrefix ω N) hω
      (fun i h => (cantorPrefix_getElem ω N i h).symm)
  · exact (measure_biUnion_null_iff (Set.to_countable _)).mpr (fun x hx => hx)

/-- The binomial coefficient times the Bernoulli mass of a word is at most one: it is one term
of the binomial expansion of `(p + (1 - p))^N`. -/
private lemma choose_mul_cantorMass_bernoulli_toReal_le_one {p : NNReal} (hp : p ≤ 1)
    (x : BitString) :
    ((x.length.choose (x.count true) : ℕ) : ℝ) *
      (cantorMass (bernoulliMeasure p hp) x).toReal ≤ 1 := by
  have hpENN : (p : ENNReal) ≤ 1 := by exact_mod_cast hp
  rw [cantorMass_bernoulliMeasure_prod, prod_map_ite_bool, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hpENN (by simp)]
  simp only [ENNReal.coe_toReal, ENNReal.toReal_one]
  have hcount := count_true_add_count_false x
  have hfalse : x.count false = x.length - x.count true := by omega
  rw [hfalse]
  have hp1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hq : (0 : ℝ) ≤ 1 - p := by linarith
  have hk : x.count true ∈ Finset.range (x.length + 1) :=
    Finset.mem_range.mpr (by omega)
  calc _ = (p : ℝ) ^ x.count true * (1 - p) ^ (x.length - x.count true) *
        (x.length.choose (x.count true)) := by ring
    _ ≤ ∑ m ∈ Finset.range (x.length + 1),
        (p : ℝ) ^ m * (1 - p) ^ (x.length - m) * (x.length.choose m) :=
      Finset.single_le_sum (f := fun m => (p : ℝ) ^ m * (1 - p) ^ (x.length - m) *
        (x.length.choose m)) (fun m _ => by positivity) hk
    _ = ((p : ℝ) + (1 - p)) ^ x.length := (add_pow _ _ _).symm
    _ = 1 := by simp

/-- The binary length of a positive integer `m` is at most `log₂ m + 1`. -/
private lemma nat_size_le_logb_add_one {m : ℕ} (hm : m ≠ 0) :
    (Nat.size m : ℝ) ≤ Real.logb 2 m + 1 := by
  have h1 : Nat.size m ≤ Nat.log 2 m + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) m)
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm
  have h3 : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hm),
      Real.rpow_natCast]
    exact_mod_cast h2
  have h4 : (Nat.size m : ℝ) ≤ Nat.log 2 m + 1 := by exact_mod_cast h1
  linarith

/-- **Upper bound.**  A word is described by its number of ones and its rank among the words
with that number of ones, so its complexity is at most `log₂ (N choose k) + O(log N)`, and the
binomial coefficient is at most the inverse of the Bernoulli mass of the word, whatever the
parameter. -/
private lemma exists_plainK_toNat_le_neg_logb_cantorMass_bernoulli (D : Map)
    (hD : isOptimalConditional D) {p : NNReal} (hp : p ≤ 1) :
    ∃ c : ℕ, ∀ x : BitString, cantorMass (bernoulliMeasure p hp) x ≠ 0 →
      ((plainK D x).toNat : ℝ) ≤
        -Real.logb 2 (cantorMass (bernoulliMeasure p hp) x).toReal +
          4 * Real.logb 2 (x.length + 1) + c := by
  obtain ⟨c, hc⟩ := plainK_fixedWeight_le_size_choose_add_length D hD
  refine ⟨c + 5, fun x hx => ?_⟩
  have hK := hc x.length (x.count true) x rfl rfl
  have hKnat : (plainK D x).toNat ≤
      Nat.size (x.length.choose (x.count true)) + 4 * Nat.size x.length + c :=
    ENat.toNat_le_of_le_natCast hK
  have hchoose : x.length.choose (x.count true) ≠ 0 :=
    (Nat.choose_pos List.count_le_length).ne'
  have hsize1 := nat_size_le_logb_add_one hchoose
  have hsize2 : (Nat.size x.length : ℝ) ≤ Real.logb 2 (x.length + 1) + 1 := by
    have h := nat_size_le_logb_add_one (m := x.length + 1) (by omega)
    have hmono : Nat.size x.length ≤ Nat.size (x.length + 1) := Nat.size_le_size (by omega)
    have hmonoR : (Nat.size x.length : ℝ) ≤ Nat.size (x.length + 1) := by exact_mod_cast hmono
    push_cast at h
    linarith
  have hmassR : 0 < (cantorMass (bernoulliMeasure p hp) x).toReal :=
    ENNReal.toReal_pos hx (MeasureTheory.measure_ne_top _ _)
  have hcpos : (0 : ℝ) < ((x.length.choose (x.count true) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hchoose
  have hlog : Real.logb 2 ((x.length.choose (x.count true) : ℕ) : ℝ) ≤
      -Real.logb 2 (cantorMass (bernoulliMeasure p hp) x).toReal := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hcpos hmassR)
      (choose_mul_cantorMass_bernoulli_toReal_le_one hp x)
    rw [Real.logb_mul hcpos.ne' hmassR.ne', Real.logb_one] at h
    linarith
  have hKR : ((plainK D x).toNat : ℝ) ≤
      Nat.size (x.length.choose (x.count true)) + 4 * Nat.size x.length + c := by
    exact_mod_cast hKnat
  push_cast
  linarith

open MeasureTheory Classical in
/-- **Counting.**  There are at most `2^l` words of complexity `l`, so the words of length `N`
whose mass is below `2^{-C(x)} (N+1)^{-3}` carry total mass at most `(N+c+1)/(N+1)^3`, for any
finite measure. -/
private lemma measure_cantorMass_mul_two_pow_plainK_lt_le (D : Map)
    (hD : isOptimalConditional D) (μ : Measure CantorSeq) {c : ℕ}
    (hc : ∀ x : BitString, plainK D x ≤ (x.length : ENat) + c) (N : ℕ) :
    μ {ω | cantorMass μ (cantorPrefix ω N) * 2 ^ (plainK D (cantorPrefix ω N)).toNat *
        ((N : ENNReal) + 1) ^ 3 < 1} ≤
      ((N + c + 1 : ℕ) : ENNReal) * (((N : ENNReal) + 1) ^ 3)⁻¹ := by
  set bad : BitString → Prop := fun x =>
    cantorMass μ x * 2 ^ (plainK D x).toNat * ((N : ENNReal) + 1) ^ 3 < 1 with hbad
  let T : ℕ → Finset BitString := fun l =>
    (card_plainK_eq_le_pow D hD l).1.toFinset.filter (fun x => x.length = N ∧ bad x)
  have hsub : {ω : CantorSeq | bad (cantorPrefix ω N)} ⊆
      ⋃ l ∈ Finset.range (N + c + 1), ⋃ x ∈ T l, cantorCylinder x := by
    intro ω hω
    set x := cantorPrefix ω N
    have hxlen : x.length = N := cantorPrefix_length ω N
    have hle : plainK D x ≤ ((N + c : ℕ) : ENat) := by
      have := hc x
      rw [hxlen] at this
      exact_mod_cast this
    have hne : plainK D x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
    have hl : (plainK D x).toNat ≤ N + c := ENat.toNat_le_of_le_natCast hle
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨(plainK D x).toNat, Finset.mem_range.mpr (by omega), x, ?_,
      fun i h => (cantorPrefix_getElem ω N i h).symm⟩
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨(ENat.natCast_toNat hne).symm, hxlen, hω⟩
  have hterm : ∀ l, μ (⋃ x ∈ T l, cantorCylinder x) ≤ (((N : ENNReal) + 1) ^ 3)⁻¹ := by
    intro l
    have hmass : ∀ x ∈ T l, cantorMass μ x ≤ (2 ^ l * ((N : ENNReal) + 1) ^ 3)⁻¹ := by
      intro x hx
      simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx
      obtain ⟨hxl, -, hxbad⟩ := hx
      have hxbad' : cantorMass μ x * 2 ^ (plainK D x).toNat * ((N : ENNReal) + 1) ^ 3 < 1 :=
        hxbad
      rw [hxl, ENat.toNat_natCast] at hxbad'
      rw [ENNReal.le_inv_iff_mul_le, ← mul_assoc]
      exact hxbad'.le
    have hcard : (T l).card ≤ 2 ^ l := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [← Set.ncard_eq_toFinset_card _ (card_plainK_eq_le_pow D hD l).1]
      exact (card_plainK_eq_le_pow D hD l).2
    calc μ (⋃ x ∈ T l, cantorCylinder x) ≤ ∑ x ∈ T l, μ (cantorCylinder x) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _x ∈ T l, (2 ^ l * ((N : ENNReal) + 1) ^ 3)⁻¹ :=
          Finset.sum_le_sum hmass
      _ = ((T l).card : ENNReal) * (2 ^ l * ((N : ENNReal) + 1) ^ 3)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 ^ l : ENNReal) * (2 ^ l * ((N : ENNReal) + 1) ^ 3)⁻¹ := by
          gcongr
          exact_mod_cast hcard
      _ = (((N : ENNReal) + 1) ^ 3)⁻¹ := by
          rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
            ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  calc μ {ω | bad (cantorPrefix ω N)}
      ≤ μ (⋃ l ∈ Finset.range (N + c + 1), ⋃ x ∈ T l, cantorCylinder x) := measure_mono hsub
    _ ≤ ∑ l ∈ Finset.range (N + c + 1), μ (⋃ x ∈ T l, cantorCylinder x) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _l ∈ Finset.range (N + c + 1), (((N : ENNReal) + 1) ^ 3)⁻¹ :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = ((N + c + 1 : ℕ) : ENNReal) * (((N : ENNReal) + 1) ^ 3)⁻¹ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The bounds `(N+c+1)/(N+1)^3` of the counting step are summable. -/
private lemma tsum_natCast_mul_inv_pow_three_ne_top (c : ℕ) :
    ∑' N : ℕ, ((N + c + 1 : ℕ) : ENNReal) * (((N : ENNReal) + 1) ^ 3)⁻¹ ≠ ⊤ := by
  have hterm : ∀ N : ℕ, ((N + c + 1 : ℕ) : ENNReal) * (((N : ENNReal) + 1) ^ 3)⁻¹ =
      ENNReal.ofReal (((N + c + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) ^ 3) := by
    intro N
    rw [ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv]
    congr 2
    · exact (ENNReal.ofReal_natCast _).symm
    · rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one]
      simp
  have hsum2 : Summable (fun N : ℕ => 1 / ((N : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hsum : Summable (fun N : ℕ => ((N + c + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) ^ 3) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
      (hsum2.mul_left ((c : ℝ) + 1))
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (by positivity)]
    push_cast
    field_simp
    nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N), (c.cast_nonneg : (0 : ℝ) ≤ c)]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

open MeasureTheory in
/-- **Lower bound (Borel–Cantelli).**  For any finite measure, almost surely, for all large `N`,
the complexity of the length-`N` prefix is at least the negated logarithm of its mass minus
`3 log₂ (N + 1)`.  No computability of the measure is needed. -/
private lemma ae_eventually_neg_logb_cantorMass_le_plainK (D : Map)
    (hD : isOptimalConditional D) (μ : Measure CantorSeq) [IsFiniteMeasure μ] :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, cantorMass μ (cantorPrefix ω N) ≠ 0 →
      -Real.logb 2 (cantorMass μ (cantorPrefix ω N)).toReal ≤
        ((plainK D (cantorPrefix ω N)).toNat : ℝ) + 3 * Real.logb 2 ((N : ℝ) + 1) := by
  obtain ⟨c, hc⟩ := plainK_le_length D hD
  have hae := ae_eventually_notMem (μ := μ) (s := fun N => {ω : CantorSeq |
      cantorMass μ (cantorPrefix ω N) * 2 ^ (plainK D (cantorPrefix ω N)).toNat *
        ((N : ENNReal) + 1) ^ 3 < 1}) (ne_top_of_le_ne_top
    (tsum_natCast_mul_inv_pow_three_ne_top c)
    (ENNReal.tsum_le_tsum fun N => measure_cantorMass_mul_two_pow_plainK_lt_le D hD μ hc N))
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with N hN hmass0
  simp only [not_lt] at hN
  set m := cantorMass μ (cantorPrefix ω N)
  set l := (plainK D (cantorPrefix ω N)).toNat
  have hmtop : m ≠ ⊤ := measure_ne_top _ _
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hmass0 hmtop
  have hR := ENNReal.toReal_mono (by finiteness) hN
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at hR
  rw [ENNReal.toReal_add (by simp) (by simp)] at hR
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_one] at hR
  have hlog := Real.logb_nonneg (b := 2) one_lt_two hR
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
    (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two] at hlog
  push_cast at hlog
  linarith

/-- A sequence within `O(log N)` of `N e_N`, where `e_N → H`, divided by `N` tends to `H`. -/
private lemma tendsto_div_of_abs_sub_mul_le_logb {a e : ℕ → ℝ} {H c : ℝ}
    (he : Tendsto e atTop (nhds H))
    (hbound : ∀ᶠ N : ℕ in atTop, |a N - N * e N| ≤ 7 * Real.logb 2 ((N : ℝ) + 1) + c) :
    Tendsto (fun N => a N / N) atTop (nhds H) := by
  have hlog : Tendsto (fun N : ℕ => Real.logb 2 ((N : ℝ) + 1) / N) atTop (nhds 0) := by
    refine ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hconst : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun N : ℕ => (7 * Real.logb 2 ((N : ℝ) + 1) + c) / N) atTop (nhds 0) := by
    simpa [add_div, mul_div_assoc] using (hlog.const_mul 7).add hconst
  have hdiff : Tendsto (fun N : ℕ => (a N - N * e N) / N) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsmall
    filter_upwards [eventually_gt_atTop 0, hbound] with N hN hb
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (a := (N : ℝ)) (Nat.cast_pos.mpr hN)]
    exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
  have h := hdiff.add he
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- **Without computability of the parameter, the limit still holds almost everywhere.**  If `p`
is an arbitrary parameter — Martin-Löf randomness is then unavailable — the set of sequences whose
prefix complexities per letter do not converge to the entropy has measure zero for the Bernoulli
measure with parameter `p`.

**Weaker than the printed statement**: the book states this for `k` letters, and this is the
binary case, for the same reason as in Theorem 148.  Within the binary case it is **stronger**
than the printed statement in one respect: the parameter is an arbitrary `p ≤ 1`, so the
degenerate endpoints `p = 0` and `p = 1` are included, where the printed statement assumes
`0 < p_i`.  SUV Problem 239, pp. 229–230. -/
theorem measure_setOf_not_tendsto_plainK_cantorPrefix_div (D : Map)
    (hD : isOptimalConditional D) {p : NNReal} (hp : p ≤ 1) :
    (bernoulliMeasure p hp) {ω : CantorSeq | ¬ Tendsto
        (fun N : ℕ => ((plainK D (cantorPrefix ω N)).toNat : ℝ) / N) atTop
        (nhds (negMulLog2 (p : ℝ) + negMulLog2 (1 - (p : ℝ))))} = 0 := by
  obtain ⟨cU, hcU⟩ := exists_plainK_toNat_le_neg_logb_cantorMass_bernoulli D hD hp
  have hlow := ae_eventually_neg_logb_cantorMass_le_plainK D hD (bernoulliMeasure p hp)
  have hne := ae_cantorMass_cantorPrefix_ne_zero (bernoulliMeasure p hp)
  have hce := ae_tendsto_bernoulliCrossEntropy_freqOne hp
  refine MeasureTheory.ae_iff.mp ?_
  filter_upwards [hlow, hne, hce] with ω hlowω hneω hceω
  refine tendsto_div_of_abs_sub_mul_le_logb (c := cU) hceω ?_
  filter_upwards [hlowω, eventually_gt_atTop 0] with N hN hNpos
  have hmass := neg_logb_cantorMass_bernoulli_cantorPrefix_eq hp ω hNpos
  have hup := hcU (cantorPrefix ω N) (hneω N)
  have hdown := hN (hneω N)
  rw [cantorPrefix_length] at hup
  have hlog0 : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  rw [abs_le]
  constructor <;> linarith

/-! ### Theorem 149: complexity deviations -/

/-- **The complexity of an i.i.d. word concentrates around `N H` at scale `√N`.**  For every
`ε > 0` there is a `c` such that, for every `N`, the word formed by `N` independent copies of `ξ`
satisfies `N H(ξ) − c√N < C(x) < N H(ξ) + c√N` with probability at least `1 − ε`.  The constant is
quantified before `N`, as in the book.  Rationality of the `p_i` is the "for simplicity we assume
that `p_i` are rational (or at least computable)" of p. 230; Problem 240 removes it.  The book
says "for all `N`"; the length `N = 0` is excluded, since for it the open interval
`(N H − c√N, N H + c√N)` is empty and the event has probability zero.  The complexity is the
plain complexity of the block encoding `finWordBits` of the word.
SUV Theorem 149, p. 230. -/
theorem exists_const_prob_plainK_near_mul_entropyDist (A : Type*) [Fintype A]
    [Encodable A] (μ : FiniteProbSpace A) (hrat : ∀ a, ∃ r : ℚ, μ.prob a = (r : ℝ))
    (D : Map) (hD : isOptimalConditional D) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N : ℕ, 0 < N →
      1 - ε ≤ (μ.power N).probOfPred fun w =>
        (N : ℝ) * entropyDist μ.prob - c * Real.sqrt N <
            ((plainK D (finWordBits A w)).toNat : ℝ) ∧
          ((plainK D (finWordBits A w)).toNat : ℝ) <
            (N : ℝ) * entropyDist μ.prob + c * Real.sqrt N := by
  have _ := hrat
  exact exists_const_prob_plainK_near_mul_entropyDist_of_real A μ D hD hε


end Kolmogorov
