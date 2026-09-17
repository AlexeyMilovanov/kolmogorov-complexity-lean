import KolmogorovMathlib.MonotoneComplexity.AntichainSum
import KolmogorovMathlib.MonotoneComplexity.BranchRecovery
import KolmogorovMathlib.MonotoneComplexity.MaximalSemimeasure
import KolmogorovMathlib.MonotoneComplexity.PrefixFreeEnvelope
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import KolmogorovMathlib.Prefix.Properties.StableAliasesSUVTheorem
import KolmogorovMathlib.Prefix.Properties

/-!
# The a priori probability on the tree and a priori complexity

The a priori probability `universalContinuousSemimeasure`: a lower semicomputable continuous
tree semimeasure that dominates every other one up to a multiplicative constant
(`universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure`,
`universalContinuousSemimeasure_isMaximal`), together with the complexity `KA x = -log₂ a(x)` it
defines and the two concrete semimeasures used to bound it.

### Outline

* the maximal semimeasure and its positivity (`universalContinuousSemimeasure_pos`);
* the uniform tree measure `lengthMeasure`, `x ↦ 2 ^ -|x|`, with its semimeasure and lower
  semicomputability proofs, which bound `KA` by the length;
* `KA` and its comparisons with plain and prefix complexity: `KP_le_KA`,
  `KPPlain_le_KA_add_KPPlain_length`, `KPPlain_le_KA_add_two_mul_log_length`, and
  `KA_eq_KPPlain_of_incompatible` along a computable sequence of pairwise incomparable strings;
* the `branchMeasure` of a computable sequence, used for
  `computable_iff_KA_prefixes_bounded`: a sequence is computable exactly when the a priori
  complexities of its prefixes stay bounded.

Source: SUV, chapter on a priori probability and monotone complexity.
-/

open ENNReal

namespace Kolmogorov

/-- The a priori probability on the tree: a maximal lower semicomputable continuous semimeasure. -/
noncomputable def universalContinuousSemimeasure : BitString → ℝ≥0∞ :=
  Classical.choose exists_maximal_lowerSemicomputableContinuousSemimeasure

/-- The a priori probability is itself a lower semicomputable continuous semimeasure. -/
theorem universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure :
    IsLowerSemicomputableContinuousSemimeasure universalContinuousSemimeasure :=
  (Classical.choose_spec exists_maximal_lowerSemicomputableContinuousSemimeasure).1

/-- Every lower semicomputable continuous semimeasure is dominated by the a priori probability up
to a finite factor. -/
theorem universalContinuousSemimeasure_isMaximal :
    ∀ a', IsLowerSemicomputableContinuousSemimeasure a' →
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * universalContinuousSemimeasure x :=
  (Classical.choose_spec exists_maximal_lowerSemicomputableContinuousSemimeasure).2

/-- The uniform tree measure `x ↦ 2 ^ -|x|`. -/
noncomputable def lengthMeasure (x : BitString) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ x.length

/-- The uniform tree measure is a continuous tree semimeasure. -/
theorem lengthMeasure_isContinuousTreeSemimeasure :
    IsContinuousTreeSemimeasure lengthMeasure := by
  constructor
  · rw [lengthMeasure, List.length_nil, pow_zero]
  · intro x
    rw [lengthMeasure, lengthMeasure, lengthMeasure]
    simp only [List.length_append, List.length_singleton, pow_add, pow_one]
    have h :
        ((2 : ℝ≥0∞)⁻¹ ^ x.length) * (2 : ℝ≥0∞)⁻¹ +
          ((2 : ℝ≥0∞)⁻¹ ^ x.length) * (2 : ℝ≥0∞)⁻¹ =
            (2 : ℝ≥0∞)⁻¹ ^ x.length := by
      calc
        _ = ((2 : ℝ≥0∞)⁻¹ ^ x.length) * ((2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹) := by rw [mul_add]
        _ = ((2 : ℝ≥0∞)⁻¹ ^ x.length) * 1 := by
          congr 1
          rw [← two_mul]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        _ = _ := mul_one _
    exact h.le

/-- The stage-`s` numerator of the uniform tree measure. -/
def lengthMeasureApprox (s : ℕ) (out : BitString) (_ctx : BitString) : ℕ :=
  if out.length ≤ s then 2 ^ (s - out.length) else 0

/-- The uniform tree measure is lower semicomputable. -/
theorem lengthMeasure_isLSC_core :
    IsLSC (fun out _ => lengthMeasure out) := by
  use lengthMeasureApprox
  constructor
  · intro s out ctx
    unfold lengthMeasureApprox dyadicValue
    by_cases h : out.length ≤ s
    · have h2 : out.length ≤ s + 1 := by omega
      simp only [h, h2, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
      have : (2 : ℝ≥0∞) ^ (s - out.length) / (2 : ℝ≥0∞) ^ s =
          (2 : ℝ≥0∞) ^ (s + 1 - out.length) /
            (2 : ℝ≥0∞) ^ (s + 1) := by
        rw [ENNReal.div_eq_div_iff]
        · rw [← pow_add, ← pow_add]
          congr 1
          omega
        · exact pow_ne_zero _ (by norm_num)
        · exact ENNReal.pow_ne_top (by norm_num)
        · exact pow_ne_zero _ (by norm_num)
        · exact ENNReal.pow_ne_top (by norm_num)
      exact this.le
    · simp only [h, ↓reduceIte, Nat.cast_zero]
      have : (0 : ℝ≥0∞) / 2 ^ s = 0 := by simp
      rw [this]
      exact bot_le
  · constructor
    · intro out ctx
      unfold lengthMeasure dyadicValue lengthMeasureApprox
      have H : ∀ s, out.length ≤ s →
          (2 : ℝ≥0∞) ^ (s - out.length) / (2 : ℝ≥0∞) ^ s =
            (2 : ℝ≥0∞)⁻¹ ^ out.length := by
        intro s h
        have : (2:ℝ≥0∞)^(s - out.length) / (2:ℝ≥0∞)^s = 1 / (2:ℝ≥0∞)^out.length := by
          rw [ENNReal.div_eq_div_iff]
          · rw [← pow_add, mul_one]
            congr 1
            omega
          · exact pow_ne_zero _ (by norm_num)
          · exact ENNReal.pow_ne_top (by norm_num)
          · exact pow_ne_zero _ (by norm_num)
          · exact ENNReal.pow_ne_top (by norm_num)
        rw [this, div_eq_mul_inv, one_mul, ENNReal.inv_pow]
      apply le_antisymm
      · apply iSup_le
        intro s
        by_cases h : out.length ≤ s
        · simp only [h, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
          change (2:ℝ≥0∞)^(s - out.length) / (2:ℝ≥0∞)^s ≤ (2:ℝ≥0∞)⁻¹ ^ out.length
          rw [H s h]
        · simp only [h, ↓reduceIte, Nat.cast_zero]
          have : (0 : ℝ≥0∞) / 2 ^ s = 0 := by simp
          rw [this]
          exact bot_le
      · have H2 : (2 : ℝ≥0∞)⁻¹ ^ out.length =
            dyadicValue (lengthMeasureApprox out.length out ctx) out.length := by
          unfold dyadicValue lengthMeasureApprox
          have H_app := H out.length (le_refl _)
          simp only [le_refl, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
          exact H_app.symm
        change (2:ℝ≥0∞)⁻¹ ^ out.length ≤ _
        rw [H2]
        exact le_iSup (fun s => dyadicValue (lengthMeasureApprox s out ctx) s) out.length
    · have h_len : Primrec (fun p : ℕ × BitString × BitString => p.2.1.length) :=
        Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
      have h_stage : Primrec (fun p : ℕ × BitString × BitString => p.1) :=
        Primrec.fst
      have h_le : PrimrecPred (fun p : ℕ × BitString × BitString =>
          p.2.1.length ≤ p.1) :=
        Primrec.nat_le.comp h_len h_stage
      have h_sub : Primrec (fun p : ℕ × BitString × BitString =>
          p.1 - p.2.1.length) :=
        Primrec.nat_sub.comp h_stage h_len
      have h_pow : Primrec (fun p : ℕ × BitString × BitString =>
          2 ^ (p.1 - p.2.1.length)) :=
        primrec_two_pow_aux.comp h_sub
      have h_zero : Primrec (fun _p : ℕ × BitString × BitString => 0) :=
        Primrec.const 0
      have h_ite : Primrec (fun p : ℕ × BitString × BitString =>
          if p.2.1.length ≤ p.1 then 2 ^ (p.1 - p.2.1.length) else 0) :=
        Primrec.ite h_le h_pow h_zero
      simpa [lengthMeasureApprox] using h_ite.to_comp

/-- The a priori probability is strictly positive at every string. -/
theorem universalContinuousSemimeasure_pos (x : BitString) :
    0 < universalContinuousSemimeasure x := by
  have H3 : IsLowerSemicomputableContinuousSemimeasure lengthMeasure :=
    ⟨lengthMeasure_isContinuousTreeSemimeasure, lengthMeasure_isLSC_core⟩
  obtain ⟨c, hc_top, hc⟩ := universalContinuousSemimeasure_isMaximal _ H3
  have H4 := hc x
  have H_pos : lengthMeasure x ≠ 0 := by
    unfold lengthMeasure
    exact pow_ne_zero x.length (by norm_num)
  have H_pos2 : 0 < lengthMeasure x := pos_iff_ne_zero.mpr H_pos
  by_contra h_not
  push Not at h_not
  have h_zero : universalContinuousSemimeasure x = 0 := le_antisymm h_not bot_le
  rw [h_zero, mul_zero] at H4
  exact (not_le.mpr H_pos2) H4

/-- The exact a priori complexity KA(x) = -log_2 a(x), unrounded, as a real number. -/
noncomputable def KA (x : BitString) : ℝ :=
  - Real.logb 2 (universalContinuousSemimeasure x).toReal

private lemma logb_inv_two_pow (n : ℕ) :
    Real.logb 2 ((2 : ℝ)⁻¹ ^ n) = -(n : ℝ) := by
  unfold Real.logb
  rw [Real.log_pow, Real.log_inv]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- The base-two logarithm of `2 ^ n` is `n`. -/
lemma logb_two_pow (n : ℕ) :
    Real.logb 2 ((2 : ℝ) ^ n) = (n : ℝ) := by
  unfold Real.logb
  rw [Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- The number of binary digits of `n` is at most `log₂ n + 1`. -/
lemma natBits_length_le_logb_add_one (n : ℕ) :
    ((Nat.bits n).length : ℝ) ≤ Real.logb 2 n + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hsize_pos : 0 < n.size := Nat.size_pos.mpr (Nat.pos_iff_ne_zero.mpr hn)
  have hpow_nat : 2 ^ (n.size - 1) ≤ n :=
    Nat.lt_size.mp (by omega)
  have hpow_real : (2 : ℝ) ^ (n.size - 1) ≤ (n : ℝ) := by
    exact_mod_cast hpow_nat
  have hlog : Real.logb 2 ((2 : ℝ) ^ (n.size - 1)) ≤ Real.logb 2 n :=
    (Real.logb_le_logb (by norm_num) (by positivity)
      (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hpow_real
  rw [logb_two_pow] at hlog
  rw [Nat.size_eq_bits_len]
  push_cast [Nat.cast_sub (by omega : 1 ≤ n.size)] at hlog
  linarith

/-- If the universal continuous semimeasure dominates `2^(-n)` at `x` (up to the finite
factor `c`), then `KA x ≤ n + log₂ c`. -/
lemma KA_le_nat_add_log_of_inv_two_pow_le (x : BitString)
    (n : ℕ) (c : ℝ≥0∞) (hc_top : c ≠ ⊤)
    (hdom : (2 : ℝ≥0∞)⁻¹ ^ n ≤ c * universalContinuousSemimeasure x) :
    KA x ≤ (n : ℝ) + Real.logb 2 c.toReal := by
  unfold KA
  have ha_top : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hmul_top : c * universalContinuousSemimeasure x ≠ ⊤ :=
    ENNReal.mul_ne_top hc_top ha_top
  have hpow_top : (2 : ℝ≥0∞)⁻¹ ^ n ≠ ⊤ :=
    ENNReal.pow_ne_top (by norm_num)
  have hdom_real := (ENNReal.toReal_le_toReal hpow_top hmul_top).mpr hdom
  have hpow_real : ((2 : ℝ≥0∞)⁻¹ ^ n).toReal = (2 : ℝ)⁻¹ ^ n := by
    simp
  rw [hpow_real, ENNReal.toReal_mul] at hdom_real
  have hc_pos : 0 < c.toReal := by
    by_contra hc
    push Not at hc
    have hc_zero : c.toReal = 0 := le_antisymm hc ENNReal.toReal_nonneg
    rw [hc_zero, zero_mul] at hdom_real
    exact (not_le_of_gt (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n)) hdom_real
  have ha_pos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos (universalContinuousSemimeasure_pos x).ne' ha_top
  have hlog : Real.logb 2 ((2 : ℝ)⁻¹ ^ n) ≤
      Real.logb 2 (c.toReal * (universalContinuousSemimeasure x).toReal) :=
    (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity) (mul_pos hc_pos ha_pos)).mpr hdom_real
  rw [Real.logb_mul hc_pos.ne' ha_pos.ne', logb_inv_two_pow] at hlog
  linarith

-- Theorem 79
/-- A priori complexity is monotone along extensions. -/
theorem KA_mono {x y : BitString} (h : x <+: y) : KA x ≤ KA y := by
  unfold KA
  have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have h_le := ha.antitone_of_prefix h
  have pos_x := universalContinuousSemimeasure_pos x
  have pos_y := universalContinuousSemimeasure_pos y
  have top_x := ha.ne_top x
  have top_y := ha.ne_top y
  have h_le_real : (universalContinuousSemimeasure y).toReal ≤
      (universalContinuousSemimeasure x).toReal := by
    exact (ENNReal.toReal_le_toReal top_y top_x).mpr h_le
  have pos_y_real : 0 < (universalContinuousSemimeasure y).toReal := by
    exact (ENNReal.toReal_pos (ne_of_gt pos_y) top_y)
  have pos_x_real : 0 < (universalContinuousSemimeasure x).toReal := by
    exact (ENNReal.toReal_pos (ne_of_gt pos_x) top_x)
  have log_le : Real.logb 2 (universalContinuousSemimeasure y).toReal ≤
      Real.logb 2 (universalContinuousSemimeasure x).toReal := by
    exact (Real.logb_le_logb (by norm_num) pos_y_real pos_x_real).mpr h_le_real
  exact neg_le_neg log_le

/-- A priori complexity is at most the length of the string, up to an additive constant. -/
theorem KA_le_length : ∃ c : ℝ, ∀ x : BitString, KA x ≤ x.length + c := by
  have hlength : IsLowerSemicomputableContinuousSemimeasure lengthMeasure :=
    ⟨lengthMeasure_isContinuousTreeSemimeasure, lengthMeasure_isLSC_core⟩
  obtain ⟨c, hc_top, hc⟩ :=
    universalContinuousSemimeasure_isMaximal lengthMeasure hlength
  refine ⟨Real.logb 2 c.toReal, fun x => ?_⟩
  apply KA_le_nat_add_log_of_inv_two_pow_le x x.length c hc_top
  simpa only [lengthMeasure] using hc x

/-- A priori complexity is at most the prefix complexity, up to an additive constant. -/
theorem KA_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ, ∀ x : BitString, KA x ≤ ((KPPlain U x).toNat : ℝ) + c := by
  let m : BitString → ℝ≥0∞ := fun x => aprioriMeasure U x []
  have hm_lsc : IsLSC (fun x _ => m x) :=
    (aprioriMeasure_isLSC U hU.isPrefixDecompressor).fix_context []
  have hm_free : ∀ S : Finset BitString,
      IsPrefixFree (S : Set BitString) → ∑ x ∈ S, m x ≤ 1 := by
    intro S _
    exact (ENNReal.sum_le_tsum S).trans
      (tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine)
  obtain ⟨b, hb, hmb⟩ :=
    exists_lsc_continuousTreeSemimeasure_dominating_prefixFree m hm_lsc hm_free
  obtain ⟨c, hc_top, hbc⟩ := universalContinuousSemimeasure_isMaximal b hb
  obtain ⟨c_len, h_len⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨Real.logb 2 c.toReal, fun x => ?_⟩
  have hbound_top : 2 * (x.length : ENat) + (c_len : ENat) ≠ ⊤ := by
    have heq : 2 * (x.length : ENat) + (c_len : ENat) =
        ((2 * x.length + c_len : ℕ) : ENat) := by norm_cast
    rw [heq]
    exact ENat.natCast_ne_top _
  have hk_top : KPPlain U x ≠ ⊤ :=
    ne_top_of_le_ne_top hbound_top (h_len x)
  apply KA_le_nat_add_log_of_inv_two_pow_le x (KPPlain U x).toNat c hc_top
  calc
    (2 : ℝ≥0∞)⁻¹ ^ (KPPlain U x).toNat
        = complexityWeight (KPPlain U x) := by
            calc
              _ = complexityWeight ((KPPlain U x).toNat : ENat) :=
                (complexityWeight_coe _).symm
              _ = complexityWeight (KPPlain U x) :=
                congrArg complexityWeight (ENat.natCast_toNat hk_top)
    _ ≤ m x := complexityWeight_KP_le_aprioriMeasure U x []
    _ ≤ b x := hmb x
    _ ≤ c * universalContinuousSemimeasure x := hbc x

/-- Reading a multiplicative coding bound `2^{-c₀} · a(x) ≤ 2^{-n}` back as the
additive bound `n ≤ KA(x) + c₀`. -/
lemma toNat_le_KA_add_of_complexityWeight_ge (x : BitString) (n : ENat) (c₀ : ℕ)
    (h : (2 : ℝ≥0∞)⁻¹ ^ c₀ * universalContinuousSemimeasure x ≤ complexityWeight n) :
    ((n.toNat : ℝ)) ≤ KA x + c₀ := by
  have hA_pos := universalContinuousSemimeasure_pos x
  have hA_top :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hpos : 0 < (2 : ℝ≥0∞)⁻¹ ^ c₀ * universalContinuousSemimeasure x :=
    ENNReal.mul_pos (pow_ne_zero _ (by simp)) hA_pos.ne'
  have hn : n ≠ ⊤ := (complexityWeight_pos_iff n).mp (lt_of_lt_of_le hpos h)
  lift n to ℕ using hn with k
  rw [complexityWeight_coe] at h
  rw [ENat.toNat_natCast]
  have hlhs_top : (2 : ℝ≥0∞)⁻¹ ^ c₀ * universalContinuousSemimeasure x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hA_top
  have hrhs_top : ((2 : ℝ≥0∞)⁻¹ ^ k) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have h' : (2 : ℝ)⁻¹ ^ c₀ * (universalContinuousSemimeasure x).toReal ≤ (2 : ℝ)⁻¹ ^ k := by
    have hcast := (ENNReal.toReal_le_toReal hlhs_top hrhs_top).mpr h
    simpa [ENNReal.toReal_mul] using hcast
  have hApos : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos hA_pos.ne' hA_top
  have hlhs_pos : 0 < (2 : ℝ)⁻¹ ^ c₀ * (universalContinuousSemimeasure x).toReal := by
    positivity
  have hlog :=
    (Real.logb_le_logb (b := 2) (by norm_num) hlhs_pos
      (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k)).mpr h'
  rw [Real.logb_mul (by positivity) hApos.ne', logb_inv_two_pow, logb_inv_two_pow] at hlog
  unfold KA
  linarith

/-- The **length section** of the universal continuous semimeasure: the
conditional function that, on the context `natCode |x|`, returns `a(x)`, and is
zero on every other context. -/
noncomputable def lengthSection (x ctx : BitString) : ℝ≥0∞ :=
  if ctx = natCode x.length then universalContinuousSemimeasure x else 0

/-- The section of the a priori probability that lives on the context coding the length is lower
semicomputable. -/
theorem lengthSection_isLSC : IsLSC lengthSection := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  refine ⟨fun s out ctx => if ctx = natCode out.length then approx s out ctx else 0, ?_, ?_, ?_⟩
  · intro s out ctx
    dsimp only
    by_cases h : ctx = natCode out.length
    · rw [if_pos h, if_pos h]
      exact hmono s out ctx
    · simp [h, dyadicValue]
  · intro out ctx
    dsimp only
    by_cases h : ctx = natCode out.length
    · rw [lengthSection, if_pos h]
      simp only [if_pos h]
      simpa using hsup out ctx
    · simp [h, lengthSection, dyadicValue]
  · have hdec : Computable (fun p : ℕ × BitString × BitString =>
        decide (p.2.2 = natCode p.2.1.length)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.snd.comp Computable.snd)
        (natCode_computable.comp
          (Computable.list_length.comp (Computable.fst.comp Computable.snd)))
    exact (Computable.cond hdec hcomp (Computable.const 0)).of_eq
      (fun p => by by_cases h : p.2.2 = natCode p.2.1.length <;> simp [h])

/-- Every string occurs in the list of programs of its own length. -/
lemma mem_exactLengthPrograms_length (p : BitString) :
    p ∈ exactLengthPrograms p.length := by
  induction p with
  | nil => simp [exactLengthPrograms]
  | cons b tail ih =>
    simp only [exactLengthPrograms, List.length_cons, List.mem_flatMap]
    exact ⟨tail, ih, by cases b <;> simp⟩

/-- That section is a semimeasure in its first argument: its total mass is at most one. -/
theorem tsum_lengthSection_le_one (ctx : BitString) :
    ∑' x : BitString, lengthSection x ctx ≤ 1 := by
  by_cases hctx : ∃ n, ctx = natCode n
  · obtain ⟨n, rfl⟩ := hctx
    have hzero : ∀ x : BitString, x ∉ (exactLengthPrograms n).toFinset →
        lengthSection x (natCode n) = 0 := by
      intro x hx
      have hlen : x.length ≠ n := by
        intro h
        refine hx (List.mem_toFinset.mpr ?_)
        rw [← h]
        exact mem_exactLengthPrograms_length x
      have hne : natCode n ≠ natCode x.length := by
        intro h
        exact hlen (natCode_injective h).symm
      simp [lengthSection, hne]
    rw [tsum_eq_sum hzero]
    refine le_trans (Finset.sum_le_sum ?_)
      (universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.sum_level_le_one
        n)
    intro x _
    unfold lengthSection
    split <;> simp
  · push Not at hctx
    have hz : ∀ x : BitString, lengthSection x ctx = 0 :=
      fun x => if_neg (fun h => hctx x.length h)
    simp [hz]

/-- A sequence whose distinct members are pairwise non-prefixes has prefix-free
range. -/
theorem isPrefixFree_range_of_pairwise_not_prefix {x : ℕ → BitString}
    (h : ∀ i j, i ≠ j → ¬ x i <+: x j) :
    IsPrefixFree (Set.range x) := by
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ hpre
  by_cases hij : i = j
  · rw [hij]
  · exact absurd hpre (h i j hij)

/-- Bounded search: `y` occurs among `x 0, …, x s`. -/
def hitUpTo (x : ℕ → BitString) : ℕ → BitString → Bool
  | 0, y => decide (x 0 = y)
  | (s + 1), y => hitUpTo x s y || decide (x (s + 1) = y)

/-- The bounded search succeeds exactly when `y` is one of `x 0, …, x s`. -/
lemma hitUpTo_iff (x : ℕ → BitString) (s : ℕ) (y : BitString) :
    hitUpTo x s y = true ↔ ∃ i ≤ s, x i = y := by
  induction s with
  | zero =>
    simp only [hitUpTo, decide_eq_true_eq]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨i, hi, h⟩ => by
      rw [Nat.le_zero.mp hi] at h; exact h⟩
  | succ s ih =>
    simp only [hitUpTo, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, hi.trans (Nat.le_succ s), h⟩
      · exact ⟨s + 1, le_rfl, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i (s + 1) with hlt | hge
      · exact Or.inl ⟨i, Nat.lt_succ_iff.mp hlt, h⟩
      · have : i = s + 1 := le_antisymm hi hge
        exact Or.inr (this ▸ h)

/-- The bounded search is monotone in the stage: a hit at stage `s` is a hit at `s + 1`. -/
lemma hitUpTo_succ_of_true {x : ℕ → BitString} {s : ℕ} {y : BitString}
    (h : hitUpTo x s y = true) : hitUpTo x (s + 1) y = true := by
  simp [hitUpTo, h]

/-- For a computable sequence the bounded search is computable in the stage and the string. -/
lemma hitUpTo_computable {x : ℕ → BitString} (hx : Computable x) :
    Computable (fun p : ℕ × BitString × BitString => hitUpTo x p.1 p.2.1) := by
  have hbase : Computable (fun p : ℕ × BitString × BitString => decide (x 0 = p.2.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp (Computable.const (x 0))
      (Computable.fst.comp Computable.snd)
  have hdec : Computable (fun q : (ℕ × BitString × BitString) × (ℕ × Bool) =>
      decide (x (q.2.1 + 1) = q.1.2.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp
      (hx.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hstep : Computable (fun q : (ℕ × BitString × BitString) × (ℕ × Bool) =>
      q.2.2 || decide (x (q.2.1 + 1) = q.1.2.1)) :=
    (Computable.cond (Computable.snd.comp Computable.snd)
      (Computable.const true) hdec).of_eq (fun q => by cases q.2.2 <;> simp)
  refine (Computable.nat_rec Computable.fst hbase hstep.to₂).of_eq (fun p => ?_)
  induction p.1 with
  | zero => rfl
  | succ s ih =>
    exact congrArg (fun b : Bool => b || decide (x (s + 1) = p.2.1)) ih

/-- The universal continuous semimeasure restricted to the range of a sequence. -/
noncomputable def rangeSection (x : ℕ → BitString) (y : BitString) (_ctx : BitString) : ℝ≥0∞ :=
  Set.indicator (Set.range x) universalContinuousSemimeasure y

/-- The restriction of the a priori probability to the range of a computable sequence is lower
semicomputable. -/
theorem rangeSection_isLSC {x : ℕ → BitString} (hx : Computable x) :
    IsLSC (rangeSection x) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  refine ⟨fun s out ctx => if hitUpTo x s out then approx s out ctx else 0, ?_, ?_, ?_⟩
  · intro s out ctx
    dsimp only
    by_cases h : hitUpTo x s out = true
    · rw [if_pos h, if_pos (hitUpTo_succ_of_true h)]
      exact hmono s out ctx
    · simp [h, dyadicValue]
  · intro out ctx
    dsimp only
    have hd_mono : Monotone (fun s => dyadicValue (approx s out ctx) s) :=
      monotone_nat_of_le_succ (fun s => hmono s out ctx)
    by_cases hmem : out ∈ Set.range x
    · obtain ⟨i, hi⟩ := hmem
      have hhit : ∀ s, i ≤ s → hitUpTo x s out = true :=
        fun s hs => (hitUpTo_iff x s out).mpr ⟨i, hs, hi⟩
      have hval : (⨆ s, dyadicValue (if hitUpTo x s out then approx s out ctx else 0) s)
          = ⨆ s, dyadicValue (approx s out ctx) s := by
        apply le_antisymm
        · refine iSup_le fun s => ?_
          by_cases h : hitUpTo x s out = true
          · rw [if_pos h]
            exact le_iSup (fun s => dyadicValue (approx s out ctx) s) s
          · simp [h, dyadicValue]
        · refine iSup_le fun s => ?_
          have hle : dyadicValue (approx s out ctx) s
              ≤ dyadicValue (approx (max s i) out ctx) (max s i) :=
            hd_mono (le_max_left s i)
          refine hle.trans ?_
          have := hhit (max s i) (le_max_right s i)
          calc dyadicValue (approx (max s i) out ctx) (max s i)
              = dyadicValue (if hitUpTo x (max s i) out then approx (max s i) out ctx else 0)
                  (max s i) := by rw [if_pos this]
            _ ≤ _ := le_iSup
                  (fun s => dyadicValue (if hitUpTo x s out then approx s out ctx else 0) s)
                  (max s i)
      rw [hval, hsup out ctx]
      rw [rangeSection,
        Set.indicator_of_mem (Set.mem_range.mpr ⟨i, hi⟩) universalContinuousSemimeasure]
    · have hfalse : ∀ s, hitUpTo x s out ≠ true := by
        intro s hs
        obtain ⟨i, _, hi⟩ := (hitUpTo_iff x s out).mp hs
        exact hmem ⟨i, hi⟩
      have hzero : ∀ s, dyadicValue (if hitUpTo x s out then approx s out ctx else 0) s = 0 := by
        intro s
        rw [if_neg (hfalse s), dyadicValue]
        simp
      rw [rangeSection, Set.indicator_of_notMem hmem]
      simp [hzero]
  · refine (Computable.cond (hitUpTo_computable hx) hcomp (Computable.const 0)).of_eq
      (fun p => ?_)
    dsimp only
    cases h : hitUpTo x p.1 p.2.1 <;> simp

/-- On a pairwise incomparable range, the restricted a priori probability has total mass at most
one. -/
theorem tsum_rangeSection_le_one {x : ℕ → BitString}
    (h_incomp : ∀ i j, i ≠ j → ¬ x i <+: x j) (ctx : BitString) :
    ∑' y : BitString, rangeSection x y ctx ≤ 1 := by
  have hanti : ∀ y ∈ Set.range x, ∀ z ∈ Set.range x, y <+: z → y = z :=
    fun y hy z hz hyz => isPrefixFree_range_of_pairwise_not_prefix h_incomp hy hz hyz
  have h :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.tsum_antichain_le
      (Set.range x) hanti
  rwa [tsum_subtype] at h

/-- Along a computable sequence of pairwise incomparable strings, a priori complexity and prefix
complexity differ by at most a constant. -/
theorem KA_eq_KPPlain_of_incompatible (U : Map) (hU : IsOptimalPrefixConditional U)
    {x : ℕ → BitString} (hx : Computable x) (h_incomp : ∀ i j, i ≠ j → ¬ (x i <+: x j)) :
    ∃ c : ℝ, ∀ i, |KA (x i) - ((KPPlain U (x i)).toNat : ℝ)| ≤ c := by
  obtain ⟨c_upper, h_upper⟩ := KA_le_KPPlain U hU
  have h_lower : ∃ c : ℝ, ∀ i,
      ((KPPlain U (x i)).toNat : ℝ) ≤ KA (x i) + c := by
    obtain ⟨M', hM', c₀, hc₀⟩ :=
      kraftChaitin_realization_bound_unit (rangeSection_isLSC hx)
        (tsum_rangeSection_le_one h_incomp)
    obtain ⟨cI, hI⟩ := hU.invariance hM'
    refine ⟨((c₀ + cI : ℕ) : ℝ), fun i => ?_⟩
    have hsec : rangeSection x (x i) [] = universalContinuousSemimeasure (x i) := by
      rw [rangeSection,
        Set.indicator_of_mem (Set.mem_range.mpr ⟨i, rfl⟩) universalContinuousSemimeasure]
    have h1 := hc₀ (x i) []
    rw [hsec] at h1
    have h2 : complexityWeight (KP M' (x i) [] + (cI : ENat)) ≤
        complexityWeight (KP U (x i) []) :=
      complexityWeight_le_of_le (hI (x i) [])
    rw [complexityWeight_add_nat] at h2
    have hkey : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + cI) * universalContinuousSemimeasure (x i) ≤
        complexityWeight (KP U (x i) []) := by
      calc
        (2 : ℝ≥0∞)⁻¹ ^ (c₀ + cI) * universalContinuousSemimeasure (x i)
            = ((2 : ℝ≥0∞)⁻¹ ^ c₀ * universalContinuousSemimeasure (x i)) *
                (2 : ℝ≥0∞)⁻¹ ^ cI := by rw [pow_add]; ring
        _ ≤ complexityWeight (KP M' (x i) []) * (2 : ℝ≥0∞)⁻¹ ^ cI := by gcongr
        _ ≤ complexityWeight (KP U (x i) []) := h2
    have := toNat_le_KA_add_of_complexityWeight_ge (x i) _ _ hkey
    rwa [KPPlain_eq_KP]
  obtain ⟨c_lower, h_lower⟩ := h_lower
  refine ⟨max 0 (max c_upper c_lower), fun i => ?_⟩
  rw [abs_le]
  constructor
  · have hc : c_lower ≤ max 0 (max c_upper c_lower) :=
      le_max_of_le_right (le_max_right _ _)
    linarith [h_lower i]
  · have hc : c_upper ≤ max 0 (max c_upper c_lower) :=
      le_max_of_le_right (le_max_left _ _)
    linarith [h_upper (x i)]

/-- Prefix complexity conditional on the length is at most a priori complexity, up to a constant. -/
theorem KP_le_KA (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ, ∀ x : BitString,
      ((KP U x (natCode x.length)).toNat : ℝ) ≤ KA x + c := by
  obtain ⟨M', hM', c₀, hc₀⟩ :=
    kraftChaitin_realization_bound_unit lengthSection_isLSC tsum_lengthSection_le_one
  obtain ⟨cI, hI⟩ := hU.invariance hM'
  refine ⟨((c₀ + cI : ℕ) : ℝ), fun x => ?_⟩
  have hsec : lengthSection x (natCode x.length) = universalContinuousSemimeasure x := by
    simp [lengthSection]
  have h1 := hc₀ x (natCode x.length)
  rw [hsec] at h1
  have h2 : complexityWeight (KP M' x (natCode x.length) + (cI : ENat)) ≤
      complexityWeight (KP U x (natCode x.length)) :=
    complexityWeight_le_of_le (hI x (natCode x.length))
  rw [complexityWeight_add_nat] at h2
  have hkey : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + cI) * universalContinuousSemimeasure x ≤
      complexityWeight (KP U x (natCode x.length)) := by
    calc
      (2 : ℝ≥0∞)⁻¹ ^ (c₀ + cI) * universalContinuousSemimeasure x
          = ((2 : ℝ≥0∞)⁻¹ ^ c₀ * universalContinuousSemimeasure x) * (2 : ℝ≥0∞)⁻¹ ^ cI := by
            rw [pow_add]; ring
      _ ≤ complexityWeight (KP M' x (natCode x.length)) * (2 : ℝ≥0∞)⁻¹ ^ cI := by gcongr
      _ ≤ complexityWeight (KP U x (natCode x.length)) := h2
  exact toNat_le_KA_add_of_complexityWeight_ge x _ _ hkey

/-- Prefix complexity is at most a priori complexity plus the prefix complexity of the length, up
to a constant. -/
theorem KPPlain_le_KA_add_KPPlain_length (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ, ∀ x : BitString, ((KPPlain U x).toNat : ℝ) ≤
      KA x + ((KPPlain U (natCode x.length)).toNat : ℝ) + c := by
  obtain ⟨c_KA, h_KA⟩ := KP_le_KA U hU
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨c_drop, h_drop⟩ := KP_le_KPPlain U hU
  have hplain_top : ∀ z : BitString, KPPlain U z ≠ ⊤ := by
    intro z
    have hbound_top : 2 * (z.length : ENat) + (c_len : ENat) ≠ ⊤ := by
      have heq : 2 * (z.length : ENat) + (c_len : ENat) =
          ((2 * z.length + c_len : ℕ) : ENat) := by norm_cast
      rw [heq]
      exact ENat.natCast_ne_top _
    exact ne_top_of_le_ne_top hbound_top (h_len z)
  have hkp_top : ∀ z ctx : BitString, KP U z ctx ≠ ⊤ := by
    intro z ctx
    apply ne_top_of_le_ne_top
      (WithTop.add_ne_top.mpr ⟨hplain_top z, ENat.natCast_ne_top c_drop⟩)
    exact h_drop z ctx
  refine ⟨c_KA + c_sub, fun x => ?_⟩
  let code := natCode x.length
  have hpair_top : KPPlain U code + KP U x code ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hplain_top code, hkp_top x code⟩
  have hrhs_top : KPPlain U code + KP U x code + (c_sub : ENat) ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hpair_top, ENat.natCast_ne_top c_sub⟩
  have hnat := ENat.toNat_le_toNat (h_sub x code) hrhs_top
  rw [ENat.toNat_add hpair_top (ENat.natCast_ne_top c_sub),
    ENat.toNat_add (hplain_top code) (hkp_top x code),
    ENat.toNat_natCast] at hnat
  have hreal : ((KPPlain U x).toNat : ℝ) ≤
      ((KPPlain U code).toNat : ℝ) + ((KP U x code).toNat : ℝ) + c_sub := by
    exact_mod_cast hnat
  dsimp [code] at hreal ⊢
  linarith [h_KA x]

/-- Prefix complexity is at most a priori complexity plus `2 log₂ |x|`, up to a constant. -/
theorem KPPlain_le_KA_add_two_mul_log_length (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ, ∀ x : BitString,
      ((KPPlain U x).toNat : ℝ) ≤ KA x + 2 * Real.logb 2 x.length + c := by
  obtain ⟨c_KA, h_KA⟩ := KPPlain_le_KA_add_KPPlain_length U hU
  obtain ⟨c_log, h_log⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c_KA + c_log + 2, fun x => ?_⟩
  have hcode_bound : KPPlain U (natCode x.length) ≤
      ((2 * (Nat.bits x.length).length + c_log : ℕ) : ENat) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h_log x.length
  have hcode_nat : (KPPlain U (natCode x.length)).toNat ≤
      2 * (Nat.bits x.length).length + c_log := by
    have h := ENat.toNat_le_toNat hcode_bound (ENat.natCast_ne_top _)
    simpa only [ENat.toNat_natCast] using h
  have hcode_real : ((KPPlain U (natCode x.length)).toNat : ℝ) ≤
      2 * ((Nat.bits x.length).length : ℝ) + c_log := by
    exact_mod_cast hcode_nat
  have hbits := natBits_length_le_logb_add_one x.length
  linarith [h_KA x]

/-- The prefixes of a computable sequence are computable. -/
lemma computable_cantorPrefix (w : CantorSeq) (hw : Computable w) :
    Computable (cantorPrefix w) := by
  have hstep : Computable (fun p : ℕ × (ℕ × BitString) =>
      p.2.2 ++ [w p.2.1]) :=
    Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hw.comp (Computable.fst.comp Computable.snd))
  have hrec :=
    Computable.nat_rec (f := @id ℕ) (g := fun _ => ([] : BitString))
      (h := fun _ (k, ih) => ih ++ [w k]) Computable.id
      (Computable.const []) hstep.to₂
  apply hrec.of_eq
  intro n
  change Nat.rec ([] : BitString) (fun k ih => ih ++ [w k]) n = cantorPrefix w n
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.rec ([] : BitString) (fun k ih => ih ++ [w k]) n ++ [w n] =
        cantorPrefix w (n + 1)
      rw [ih, cantorPrefix_succ]

/-- The tree measure concentrated on a single branch: mass one along the prefixes of `w` and zero
elsewhere. -/
noncomputable def branchMeasure (w : CantorSeq) (x : BitString) : ℝ≥0∞ :=
  if cantorPrefix w x.length = x then 1 else 0

/-- The branch measure is a continuous tree semimeasure. -/
theorem branchMeasure_isContinuousTreeSemimeasure (w : CantorSeq) :
    IsContinuousTreeSemimeasure (branchMeasure w) := by
  constructor
  · simp [branchMeasure, cantorPrefix]
  · intro x
    by_cases hx : cantorPrefix w x.length = x
    · cases hbit : w x.length <;>
        simp [branchMeasure, cantorPrefix_succ, hx, hbit]
    · have hchild : ∀ b : Bool,
          cantorPrefix w (x ++ [b]).length ≠ x ++ [b] := by
        intro b hb
        apply hx
        have hb_prefix : IsCantorPrefix (x ++ [b]) w :=
          (isCantorPrefix_iff_cantorPrefix_eq (x ++ [b]) w).mpr hb
        have hx_prefix : IsCantorPrefix x w := by
          intro i hi
          have hi' : i < (x ++ [b]).length := by simp; omega
          calc
            w i = (x ++ [b])[i] := hb_prefix i hi'
            _ = x[i] := List.getElem_append_left hi
        exact (isCantorPrefix_iff_cantorPrefix_eq x w).mp hx_prefix
      simp [branchMeasure, hx, cantorPrefix_succ]

/-- The stage-`s` numerator of the branch measure. -/
def branchMeasureApprox (w : CantorSeq) (s : ℕ)
    (out : BitString) (_ctx : BitString) : ℕ :=
  if out.length ≤ s ∧ cantorPrefix w out.length = out then 2 ^ s else 0

/-- The branch measure of a computable sequence is lower semicomputable. -/
theorem branchMeasure_isLSC (w : CantorSeq) (hw : Computable w) :
    IsLSC (fun out _ => branchMeasure w out) := by
  refine ⟨branchMeasureApprox w, ?_, ?_, ?_⟩
  · intro s out _
    by_cases hp : cantorPrefix w out.length = out
    · by_cases hs : out.length ≤ s
      · simp [branchMeasureApprox, hp, hs, Nat.le_succ_of_le hs,
          dyadicValue_two_pow_self]
      · by_cases hs' : out.length ≤ s + 1
        · simp [branchMeasureApprox, hp, hs, hs', dyadicValue_zero,
            dyadicValue_two_pow_self]
        · simp [branchMeasureApprox, hp, hs, hs', dyadicValue_zero]
    · simp [branchMeasureApprox, hp, dyadicValue_zero]
  · intro out _
    change (⨆ s, dyadicValue (branchMeasureApprox w s out []) s) =
      branchMeasure w out
    by_cases hp : cantorPrefix w out.length = out
    · rw [branchMeasure, if_pos hp]
      apply le_antisymm
      · refine iSup_le fun s => ?_
        by_cases hs : out.length ≤ s
        · simp [branchMeasureApprox, hp, hs, dyadicValue_two_pow_self]
        · simp [branchMeasureApprox, hs, dyadicValue_zero]
      · have hstage : dyadicValue
            (branchMeasureApprox w out.length out []) out.length = 1 := by
          simp [branchMeasureApprox, hp, dyadicValue_two_pow_self]
        rw [← hstage]
        exact le_iSup (fun s =>
          dyadicValue (branchMeasureApprox w s out []) s) out.length
    · simp [branchMeasure, branchMeasureApprox, hp, dyadicValue_zero]
  · have hprefix : Computable (fun p : ℕ × BitString × BitString =>
        cantorPrefix w p.2.1.length) := by
      exact (computable_cantorPrefix w hw).comp
        ((Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)).to_comp)
    have hout : Computable (fun p : ℕ × BitString × BitString => p.2.1) :=
      Computable.fst.comp Computable.snd
    have heq : Computable (fun p : ℕ × BitString × BitString =>
        decide (cantorPrefix w p.2.1.length = p.2.1)) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp hprefix hout
    have hlen : Computable (fun p : ℕ × BitString × BitString =>
        decide (p.2.1.length ≤ p.1)) := by
      exact (PrimrecRel.decide Primrec.nat_le).to_comp.comp
        ((Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)).to_comp)
        Computable.fst
    have hand : Computable (fun p : ℕ × BitString × BitString =>
        decide (p.2.1.length ≤ p.1 ∧
          cantorPrefix w p.2.1.length = p.2.1)) := by
      exact (Computable.cond hlen heq (Computable.const false)).of_eq
        (fun p => by by_cases h : p.2.1.length ≤ p.1 <;> simp [h])
    have hpow : Computable (fun p : ℕ × BitString × BitString => 2 ^ p.1) :=
      primrec_two_pow_aux.to_comp.comp Computable.fst
    exact (Computable.cond hand hpow (Computable.const 0)).of_eq
      (fun p => by
        by_cases h : p.2.1.length ≤ p.1 ∧
          cantorPrefix w p.2.1.length = p.2.1 <;>
          simp [branchMeasureApprox, h])

/-- A sequence is computable exactly when the a priori complexities of its prefixes are bounded. -/
theorem computable_iff_KA_prefixes_bounded (w : CantorSeq) :
    Computable w ↔ ∃ c : ℝ, ∀ n, KA (cantorPrefix w n) ≤ c := by
  constructor
  · intro hw
    have hbranch : IsLowerSemicomputableContinuousSemimeasure (branchMeasure w) :=
      ⟨branchMeasure_isContinuousTreeSemimeasure w, branchMeasure_isLSC w hw⟩
    obtain ⟨c, hc_top, hc⟩ :=
      universalContinuousSemimeasure_isMaximal (branchMeasure w) hbranch
    refine ⟨Real.logb 2 c.toReal, fun n => ?_⟩
    have hdom : (2 : ℝ≥0∞)⁻¹ ^ 0 ≤
        c * universalContinuousSemimeasure (cantorPrefix w n) := by
      simpa [branchMeasure] using hc (cantorPrefix w n)
    simpa using KA_le_nat_add_log_of_inv_two_pow_le
      (cantorPrefix w n) 0 c hc_top hdom
  · rintro ⟨c, hc⟩
    have ha := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
    have hεpos : 0 < ENNReal.ofReal ((2 : ℝ) ^ (-c : ℝ)) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    refine computable_of_branch_lower_bound ha hεpos (fun n => ?_)
    have hA_top := ha.1.ne_top (cantorPrefix w n)
    have hA_pos := universalContinuousSemimeasure_pos (cantorPrefix w n)
    have hApos : 0 < (universalContinuousSemimeasure (cantorPrefix w n)).toReal :=
      ENNReal.toReal_pos hA_pos.ne' hA_top
    have hlog : -c ≤ Real.logb 2 (universalContinuousSemimeasure (cantorPrefix w n)).toReal := by
      have hKA := hc n
      unfold KA at hKA
      linarith
    have hpow : (2 : ℝ) ^ (-c : ℝ) ≤
        (universalContinuousSemimeasure (cantorPrefix w n)).toReal := by
      calc (2 : ℝ) ^ (-c : ℝ)
          ≤ (2 : ℝ) ^ (Real.logb 2 (universalContinuousSemimeasure (cantorPrefix w n)).toReal) :=
            (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hlog
        _ = _ := Real.rpow_logb (by norm_num) (by norm_num) hApos
    exact (ENNReal.ofReal_le_iff_le_toReal hA_top).mpr hpow

-- Theorem 80
/-- A lower semicomputable weight whose sum over every prefix-free finite set is at most one is
dominated by the a priori probability. -/
theorem lsc_prefixFreeWeight_dominated_by_universal
    (m : BitString → ℝ≥0∞)
    (hlsc : IsLSC (fun x _ => m x))
    (h_prefix_free : ∀ S : Finset BitString, IsPrefixFree (S : Set BitString) → ∑ x ∈ S, m x ≤ 1) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, m x ≤ c * universalContinuousSemimeasure x := by
  obtain ⟨a, ha, hma⟩ :=
    exists_lsc_continuousTreeSemimeasure_dominating_prefixFree m hlsc h_prefix_free
  obtain ⟨c, hc_top, hca⟩ := universalContinuousSemimeasure_isMaximal a ha
  exact ⟨c, hc_top, fun x => (hma x).trans (hca x)⟩

end Kolmogorov
