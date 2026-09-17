import KolmogorovMathlib.MonotoneComplexity.GacsDayRequestFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDaySeparationReduction
import KolmogorovMathlib.MonotoneComplexity.SubSemimeasureDomination
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Mixing the request families into one semimeasure

The level-`c` request families are combined into a single lower semicomputable semimeasure
`gacsDayMixture`, weighting level `c` by `gacsDayWeight c = 2 ^ c / ((c + 1) * (c + 2))`. The
factor `2 ^ c` cancels the root budget `2 ^ (-c)` of level `c`
(`gacsDayWeight_mul_invTwoPow`) while the remaining series still converges
(`sum_range_one_div_succ_mul_succ_succ`, `tsum_inv_succ_mul_succ_succ_le_one`,
`tsum_gacsDayWeight_mul_invTwoPow_le_one`), so the mixture is a semimeasure. Dominating it by the
universal continuous semimeasure then transfers the deficit of a single level
(`gacsDay_gap_of_domination`), and with the estimate `gacsDay_loglog_arith_eventually` this gives
`gacsDayQuantitative_of_requestFamily`, the analytic form of the separation with its `log log`
gap.
-/

namespace Kolmogorov
open MeasureTheory ENNReal Real Filter Asymptotics

/-- The weight `2 ^ c / ((c + 1) * (c + 2))` the mixture gives to the level-`c` request family. -/
noncomputable def gacsDayWeight (c : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ c / ((c + 1) * (c + 2) : ℕ)

/-- The weighted mixture `∑ c, gacsDayWeight c * μ c x` of a family of semimeasures. -/
noncomputable def gacsDayMixture (μ : ℕ → BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' c, gacsDayWeight c * μ c x

/-- The factor `2^c` in `gacsDayWeight` cancels the root budget `2⁻ᶜ`. -/
lemma gacsDayWeight_mul_invTwoPow (c : ℕ) :
    gacsDayWeight c * (2⁻¹ : ℝ≥0∞) ^ c =
      (((c + 1) * (c + 2) : ℕ) : ℝ≥0∞)⁻¹ := by
  have h2 : (2⁻¹ : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
  have hrw : gacsDayWeight c * (2⁻¹ : ℝ≥0∞) ^ c =
      ((2⁻¹ : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ c) *
        (((c + 1) * (c + 2) : ℕ) : ℝ≥0∞)⁻¹ := by
    unfold gacsDayWeight
    rw [ENNReal.div_eq_inv_mul]
    ring
  rw [hrw, h2, one_mul]

/-- Finite telescoping identity for `1 / ((c+1)(c+2))`. -/
lemma sum_range_one_div_succ_mul_succ_succ (N : ℕ) :
    (∑ c ∈ Finset.range N,
      (1 : ℝ) / (((c + 1) * (c + 2) : ℕ) : ℝ)) = 1 - 1 / (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- The corresponding `ENNReal` series is bounded by one. -/
lemma tsum_inv_succ_mul_succ_succ_le_one :
    (∑' c : ℕ, (((c + 1) * (c + 2) : ℕ) : ℝ≥0∞)⁻¹) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have hterm : ∀ c : ℕ,
      (((c + 1) * (c + 2) : ℕ) : ℝ≥0∞)⁻¹ =
        ENNReal.ofReal (1 / (((c + 1) * (c + 2) : ℕ) : ℝ)) := by
    intro c
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  calc
    (∑ c ∈ Finset.range N, (((c + 1) * (c + 2) : ℕ) : ℝ≥0∞)⁻¹) =
        ENNReal.ofReal (∑ c ∈ Finset.range N,
          (1 : ℝ) / (((c + 1) * (c + 2) : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)]
      exact Finset.sum_congr rfl fun c _ => hterm c
    _ ≤ 1 := by
      rw [sum_range_one_div_succ_mul_succ_succ N,
        show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      apply ENNReal.ofReal_le_ofReal
      have hpos : (0 : ℝ) < 1 / (N + 1) := by positivity
      linarith

/-- The weights are summable against `2 ^ (-c)`, with total at most `1`. -/
lemma tsum_gacsDayWeight_mul_invTwoPow_le_one :
    ∑' c, gacsDayWeight c * (2 : ℝ≥0∞)⁻¹ ^ c ≤ 1 := by
  simpa only [gacsDayWeight_mul_invTwoPow] using
    tsum_inv_succ_mul_succ_succ_le_one

/-- The weight is at least `2 ^ c / ((c + 2) * (c + 2))`. -/
lemma gacsDayWeight_lower (c : ℕ) :
    (2 : ℝ≥0∞) ^ c / ((c + 2) * (c + 2)) ≤ gacsDayWeight c := by
  dsimp [gacsDayWeight]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_right
  apply ENNReal.inv_le_inv.mpr
  norm_cast
  nlinarith

/-- A mixture of semimeasures is a semimeasure: the two children never exceed their parent. -/
lemma gacsDayMixture_children_le (μ : ℕ → BitString → ℝ≥0∞)
    (h_child : ∀ c x, μ c (x ++ [false]) + μ c (x ++ [true]) ≤ μ c x) (x : BitString) :
    gacsDayMixture μ (x ++ [false]) + gacsDayMixture μ (x ++ [true]) ≤ gacsDayMixture μ x := by
  dsimp [gacsDayMixture]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro c
  rw [← mul_add]
  gcongr
  exact h_child c x

/-- If the level-`c` family requests at most `2 ^ (-c)` at the root, the mixture has root mass at
most `1`. -/
lemma gacsDayMixture_root_le_one (μ : ℕ → BitString → ℝ≥0∞)
    (h_root : ∀ c, μ c [] ≤ (2 : ℝ≥0∞)⁻¹ ^ c) :
    gacsDayMixture μ [] ≤ 1 := by
  dsimp [gacsDayMixture]
  calc
    ∑' c, gacsDayWeight c * μ c [] ≤ ∑' c, gacsDayWeight c * (2 : ℝ≥0∞)⁻¹ ^ c := by
      apply ENNReal.tsum_le_tsum
      intro c
      gcongr
      exact h_root c
    _ ≤ 1 := tsum_gacsDayWeight_mul_invTwoPow_le_one

/-- The rational stage value of the rescaled `i`-th component of the Gács–Day
mixture: the stage-`s` dyadic approximation of `μ i` scaled by `2^(2i+1)/((i+1)(i+2))`. -/
noncomputable def gacsDayCompRat (A : ℕ → ℕ → BitString → ℕ) (i s : ℕ) (out : BitString) : ℚ :=
  ((A i s out * 2 ^ (2 * i + 1) : ℕ) : ℚ) / ((((i + 1) * (i + 2)) * 2 ^ s : ℕ) : ℚ)

/-- The rational stage approximations of the mixture are nondecreasing in the stage. -/
lemma gacsDayCompRat_mono (A : ℕ → ℕ → BitString → ℕ)
    (hmono : ∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1))
    (i : ℕ) (out : BitString) (s : ℕ) :
    gacsDayCompRat A i s out ≤ gacsDayCompRat A i (s + 1) out := by
  have hA : 2 * A i s out ≤ A i (s + 1) out :=
    two_mul_le_of_dyadicValue_le (hmono i s out)
  have hAq : (2 : ℚ) * (A i s out : ℚ) ≤ (A i (s + 1) out : ℚ) := by exact_mod_cast hA
  unfold gacsDayCompRat
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  have hp : (2 : ℚ) ^ (s + 1) = 2 * 2 ^ s := by ring
  rw [hp]
  have hPQ : (0 : ℚ) ≤ 2 ^ (2 * i + 1) * (((i : ℚ) + 1) * ((i : ℚ) + 2)) * 2 ^ s := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hAq hPQ]

/-- The stage approximation of the mixture is the weight `2 ^ (2i+1) / ((i+1)(i+2))` times the
stage value of the approximated family. -/
lemma ofReal_gacsDayCompRat (A : ℕ → ℕ → BitString → ℕ) (i s : ℕ) (out : BitString) :
    ENNReal.ofReal ((gacsDayCompRat A i s out : ℚ) : ℝ) =
      ((2 ^ (2 * i + 1) : ℕ) : ℝ≥0∞) / (((i + 1) * (i + 2) : ℕ) : ℝ≥0∞) *
        dyadicValue (A i s out) s := by
  unfold gacsDayCompRat dyadicValue
  have hDpos : (0 : ℝ) < ((((i + 1) * (i + 2)) * 2 ^ s : ℕ) : ℝ) := by positivity
  rw [Rat.cast_div]
  rw [Rat.cast_natCast, Rat.cast_natCast]
  rw [ENNReal.ofReal_div_of_pos hDpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (by simp) (by simp)]
  ring

/-- Passing to the supremum over stages, the mixture approximations converge to the weight times
the limit of the family. -/
lemma iSup_dyadicValue_gacsDayCompRat (A : ℕ → ℕ → BitString → ℕ)
    (hmono : ∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1))
    (i : ℕ) (out : BitString) :
    (⨆ s, dyadicValue (ratDyadicFloor (gacsDayCompRat A i s out) s) s) =
      ((2 ^ (2 * i + 1) : ℕ) : ℝ≥0∞) / (((i + 1) * (i + 2) : ℕ) : ℝ≥0∞) *
        ⨆ s, dyadicValue (A i s out) s := by
  have hmonoR : Monotone (fun s => gacsDayCompRat A i s out) :=
    monotone_nat_of_le_succ (fun s => gacsDayCompRat_mono A hmono i out s)
  rw [iSup_dyadicValue_ratDyadicFloor hmonoR]
  rw [ENNReal.mul_iSup]
  exact iSup_congr (fun s => ofReal_gacsDayCompRat A i s out)

/-- The dyadic floors of the stage approximations are computable when the approximated family is. -/
lemma computable_gacsDayCompApprox {A : ℕ → ℕ → BitString → ℕ}
    (hcomp : Computable fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      ratDyadicFloor (gacsDayCompRat A p.1 p.2.1 p.2.2.1) p.2.1) := by
  have hproj : Computable (fun p : ℕ × ℕ × BitString × BitString => (p.1, p.2.1, p.2.2.1)) :=
    Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hA := hcomp.comp hproj
  have hnum : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      ((A p.1 p.2.1 p.2.2.1 * 2 ^ (2 * p.1 + 1) : ℕ) : ℤ)) := by
    have hpow : Computable (fun p : ℕ × ℕ × BitString × BitString =>
        (2 ^ (2 * p.1 + 1) : ℕ)) :=
      (nat_pow_primrec₂.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))).to_comp
    exact ComputableReals.primrec_natCastInt.to_comp.comp (Primrec.nat_mul.to_comp.comp hA hpow)
  have hden : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      (((p.1 + 1) * (p.1 + 2)) * 2 ^ p.2.1 : ℕ)) := by
    have h1 : Computable (fun p : ℕ × ℕ × BitString × BitString => ((p.1 + 1) * (p.1 + 2) : ℕ)) :=
      (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.succ.comp Primrec.fst))).to_comp
    have h2 : Computable (fun p : ℕ × ℕ × BitString × BitString => (2 ^ p.2.1 : ℕ)) :=
      (nat_pow_primrec₂.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)).to_comp
    exact Primrec.nat_mul.to_comp.comp h1 h2
  have hrat : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      gacsDayCompRat A p.1 p.2.1 p.2.2.1) := by
    refine computable_of_num_den hnum hden (fun p => by positivity) (fun p => ?_)
    unfold gacsDayCompRat
    push_cast
    ring
  exact computable_ratDyadicFloor.comp hrat (Computable.fst.comp Computable.snd)

/-- The Gács–Day weight is the dyadic mixture weight times the rescaling factor
`2^(2i+1)/((i+1)(i+2))`. -/
lemma gacsDayWeight_eq_dyadicWeight_mul (i : ℕ) :
    gacsDayWeight i =
      dyadicWeight i *
        (((2 ^ (2 * i + 1) : ℕ) : ℝ≥0∞) / (((i + 1) * (i + 2) : ℕ) : ℝ≥0∞)) := by
  have hpow : ((2 ^ (2 * i + 1) : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (i + 1) * (2 : ℝ≥0∞) ^ i := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  have h2 : ((2 : ℝ≥0∞)⁻¹) ^ (i + 1) * (2 : ℝ≥0∞) ^ (i + 1) = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
  unfold gacsDayWeight dyadicWeight
  rw [hpow, div_eq_mul_inv, div_eq_mul_inv]
  rw [show ((2 : ℝ≥0∞)⁻¹) ^ (i + 1) *
      (((2 : ℝ≥0∞) ^ (i + 1) * (2 : ℝ≥0∞) ^ i) * ((((i + 1) * (i + 2) : ℕ) : ℝ≥0∞))⁻¹) =
      (((2 : ℝ≥0∞)⁻¹) ^ (i + 1) * (2 : ℝ≥0∞) ^ (i + 1)) *
        ((2 : ℝ≥0∞) ^ i * ((((i + 1) * (i + 2) : ℕ) : ℝ≥0∞))⁻¹) from by ring, h2, one_mul]

/-- A mixture of uniformly computably approximable semimeasures is lower semicomputable. -/
lemma gacsDayMixture_isLSC (μ : ℕ → BitString → ℝ≥0∞)
    (h_unif : ∃ (A : ℕ → ℕ → BitString → ℕ),
      (∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1)) ∧
      (∀ m x, ⨆ s, dyadicValue (A m s x) s = μ m x) ∧
      (Computable fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2)) :
    IsLSC fun x _ => gacsDayMixture μ x := by
  obtain ⟨A, hmono, hsup, hcomp⟩ := h_unif
  have key := isLSC_unaryMixture_dyadicWeight_of_uniform
    (fun i out _ => ((2 ^ (2 * i + 1) : ℕ) : ℝ≥0∞) /
      (((i + 1) * (i + 2) : ℕ) : ℝ≥0∞) * μ i out)
    (fun i s out _ => ratDyadicFloor (gacsDayCompRat A i s out) s)
    (fun i s out _ =>
      dyadicValue_ratDyadicFloor_mono_of_le (gacsDayCompRat_mono A hmono i out s) s)
    (fun i out _ => by rw [iSup_dyadicValue_gacsDayCompRat A hmono i out, hsup])
    (computable_gacsDayCompApprox hcomp)
  have hfun : (fun (x : BitString) (_ : BitString) => gacsDayMixture μ x) =
      fun out (_ : BitString) => ∑' i, dyadicWeight i *
        (((2 ^ (2 * i + 1) : ℕ) : ℝ≥0∞) / (((i + 1) * (i + 2) : ℕ) : ℝ≥0∞) * μ i out) := by
    funext out ctx
    refine tsum_congr (fun i => ?_)
    rw [← mul_assoc, ← gacsDayWeight_eq_dyadicWeight_mul i]
  rw [hfun]
  exact key

/-- Turning the domination of a weighted term into a complexity inequality:
`KA x + c - 2 log(c + 2) ≤ KM x + log K`. -/
lemma KA_add_logWeight_le_KMOf (c : ℕ) (KM_x KA_x K : ℝ)
    (h_dom : (2 : ℝ) ^ c / ((c + 1) * (c + 2)) * (2 : ℝ)⁻¹ ^ KM_x ≤ K * (2 : ℝ)⁻¹ ^ KA_x) :
    KA_x + c - 2 * Real.logb 2 (c + 2) ≤ KM_x + Real.logb 2 K := by
  have hleft_pos : 0 < (2 : ℝ) ^ c / ((c + 1) * (c + 2)) *
      (2 : ℝ)⁻¹ ^ KM_x := by positivity
  have hright_pos : 0 < K * (2 : ℝ)⁻¹ ^ KA_x :=
    lt_of_lt_of_le hleft_pos h_dom
  have hpow_pos : 0 < (2 : ℝ)⁻¹ ^ KA_x := by positivity
  have hK : 0 < K := by
    rcases (mul_pos_iff.mp hright_pos) with hp | hn
    · exact hp.1
    · exact (not_lt_of_ge hpow_pos.le hn.2).elim
  have hlog := (Real.logb_le_logb (b := 2)
    (x := (2 : ℝ) ^ c / ((c + 1) * (c + 2)) * (2 : ℝ)⁻¹ ^ KM_x)
    (y := K * (2 : ℝ)⁻¹ ^ KA_x)
    (by norm_num) hleft_pos hright_pos).mpr h_dom
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_div (by positivity) (by positivity),
    Real.logb_pow, Real.logb_mul (by positivity) (by positivity)] at hlog
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity),
    Real.logb_inv, Real.logb_self_eq_one (by norm_num),
    Real.logb_mul hK.ne' (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity),
    Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at hlog
  simp only [mul_neg_one] at hlog
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  have hc2 : (0 : ℝ) < c + 2 := by positivity
  have hmono : Real.logb 2 (c + 1) ≤ Real.logb 2 (c + 2) := by
    exact (Real.logb_le_logb (by norm_num) hc1 hc2).mpr (by norm_cast; omega)
  linarith

/-- For a string no longer than `(C 2^c) ^ (C 2^c)`, the double logarithm of its length is at
most `c + log C + log (c + log C)`. -/
lemma loglog_length_le_parameter (C c : ℕ) (x : BitString)
    (hx : (x.length : ℝ) ≤ ((C : ℝ) * 2 ^ c) ^ ((C : ℝ) * 2 ^ c))
    (h_len : 1 < x.length) (h_C : 0 < C) :
    Real.logb 2 (Real.logb 2 x.length) ≤ c + Real.logb 2 C + Real.logb 2 (c + Real.logb 2 C) := by
  have hN : (1 : ℝ) < x.length := by exact_mod_cast h_len
  have hApos : (0 : ℝ) < (C : ℝ) * 2 ^ c := by positivity
  have hAone : (1 : ℝ) ≤ (C : ℝ) * 2 ^ c := by
    have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast h_C
    have hp : (1 : ℝ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le hC1 hp
  have hAne : (C : ℝ) * 2 ^ c ≠ 1 := by
    intro heq
    rw [heq, Real.one_rpow] at hx
    linarith
  have hAgt : (1 : ℝ) < (C : ℝ) * 2 ^ c :=
    lt_of_le_of_ne hAone (Ne.symm hAne)
  have hlogApos : 0 < Real.logb 2 ((C : ℝ) * 2 ^ c) :=
    Real.logb_pos (by norm_num) hAgt
  have hpowpos : 0 < ((C : ℝ) * 2 ^ c) ^ ((C : ℝ) * 2 ^ c) := by
    positivity
  have hlog1 := (Real.logb_le_logb (b := 2) (by norm_num)
    (by positivity : (0 : ℝ) < x.length) hpowpos).mpr hx
  rw [Real.logb_rpow_eq_mul_logb_of_pos hApos] at hlog1
  have hlogNpos : 0 < Real.logb 2 (x.length : ℝ) :=
    Real.logb_pos (by norm_num) hN
  have hprodpos : 0 < ((C : ℝ) * 2 ^ c) *
      Real.logb 2 ((C : ℝ) * 2 ^ c) := mul_pos hApos hlogApos
  have hlog2 := (Real.logb_le_logb (b := 2) (by norm_num)
    hlogNpos hprodpos).mpr hlog1
  rw [Real.logb_mul hApos.ne' hlogApos.ne',
    Real.logb_mul (by positivity : (C : ℝ) ≠ 0)
      (by positivity : (2 : ℝ) ^ c ≠ 0),
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog2
  norm_num at hlog2 ⊢
  simpa [add_comm, add_left_comm, add_assoc] using hlog2

/-- There are only finitely many binary strings below any fixed length. -/
lemma finite_bitStrings_length_lt (B : ℕ) :
    ({x : BitString | x.length < B} : Set BitString).Finite := by
  induction B with
  | zero => simp
  | succ B ih =>
      have hf := ih.image (fun x : BitString => false :: x)
      have ht := ih.image (fun x : BitString => true :: x)
      refine ((Set.finite_singleton ([] : BitString)).union (hf.union ht)).subset ?_
      intro x hx
      cases x with
      | nil => simp
      | cons a x =>
          have htail : x.length < B := by simpa using hx
          cases a
          · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨x, htail, rfl⟩)
          · exact Set.mem_union_right _ (Set.mem_union_right _ ⟨x, htail, rfl⟩)

/-- If the witnesses realise the complexity gap at unbounded levels, their lengths are unbounded. -/
lemma gacsDay_witness_lengths_unbounded (D : BitStream → BitStream) (K : ℝ)
    (c_seq : ℕ → ℕ) (x_seq : ℕ → BitString)
    (h_unbounded : Filter.Tendsto c_seq Filter.atTop Filter.atTop)
    (h_gap : ∀ n, (KA (x_seq n) : ℝ) + c_seq n -
      2 * Real.logb 2 (c_seq n + 2) ≤
        ((KMOf D (x_seq n)).toNat : ℝ) + K) :
    Filter.Tendsto (fun n => (x_seq n).length) Filter.atTop Filter.atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  have hfin := (finite_bitStrings_length_lt B).image
    (fun x => (KMOf D x).toNat)
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hcReal : Tendsto (fun n => (c_seq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp h_unbounded
  have hcPlus : Tendsto (fun n => (c_seq n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 hcReal
  have hgrowth : Tendsto (fun n => (c_seq n : ℝ) -
      2 * Real.logb 2 (c_seq n + 2)) atTop atTop := by
    have hmain : Tendsto (fun n : ℕ => ((c_seq n : ℝ) + 2) -
        2 * Real.logb 2 ((c_seq n : ℝ) + 2)) atTop atTop := by
      exact
        (tendsto_sub_const_mul_logb_atTop 2).comp hcPlus
    have hsub := tendsto_atTop_add_const_right atTop (-2 : ℝ) hmain
    convert hsub using 1
    ext n
    ring
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hgrowth.eventually_gt_atTop ((M : ℝ) + K))
  refine ⟨N, fun n hn => ?_⟩
  by_contra hlen
  have hxlt : (x_seq n).length < B := Nat.lt_of_not_ge hlen
  have hKM : (KMOf D (x_seq n)).toNat ≤ M :=
    hM ⟨x_seq n, hxlt, rfl⟩
  have hKA : (0 : ℝ) ≤ KA (x_seq n) := by
    unfold KA
    have hle : (universalContinuousSemimeasure (x_seq n)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp) <|
        universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.le_one
          (x_seq n)
    have hnonneg : (0 : ℝ) ≤
        (universalContinuousSemimeasure (x_seq n)).toReal :=
      ENNReal.toReal_nonneg
    have hlog := Real.logb_nonpos (b := 2) (by norm_num) hnonneg hle
    linarith
  have hgap := h_gap n
  have hKMreal : ((KMOf D (x_seq n)).toNat : ℝ) ≤ M := by
    exact_mod_cast hKM
  linarith [hN n hn]

/-- The universal continuous semimeasure written as `2^(-KA x)`. -/
lemma toReal_universalContinuousSemimeasure_eq_rpow (x : BitString) :
    (universalContinuousSemimeasure x).toReal = (2 : ℝ)⁻¹ ^ (KA x) := by
  have hpos : 0 < universalContinuousSemimeasure x := universalContinuousSemimeasure_pos x
  have htop : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hposR : 0 < (universalContinuousSemimeasure x).toReal :=
    ENNReal.toReal_pos hpos.ne' htop
  rw [Real.inv_rpow (by norm_num), KA, Real.rpow_neg (by norm_num), inv_inv,
    Real.rpow_logb (by norm_num) (by norm_num) hposR]

/-- The mixture weight is finite. -/
lemma gacsDayWeight_ne_top (c : ℕ) : gacsDayWeight c ≠ ⊤ := by
  unfold gacsDayWeight
  refine ENNReal.div_ne_top (by finiteness) ?_
  simp

/-- The mixture weight, as a real number, is `2 ^ c / ((c + 1) * (c + 2))`. -/
lemma toReal_gacsDayWeight (c : ℕ) :
    (gacsDayWeight c).toReal = (2 : ℝ) ^ c / (((c : ℝ) + 1) * ((c : ℝ) + 2)) := by
  unfold gacsDayWeight
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  push_cast
  norm_num

/-- Domination of the mixture by the universal continuous semimeasure turns a single
component witness into a quantitative gap between `KA` and `KM_D`. -/
lemma gacsDay_gap_of_domination (D : BitStream → BitStream) (μ : ℕ → BitString → ℝ≥0∞)
    (Kc : ℝ≥0∞) (hKtop : Kc ≠ ⊤)
    (hdom : ∀ x, gacsDayMixture μ x ≤ Kc * universalContinuousSemimeasure x)
    (c : ℕ) (x : BitString)
    (hx : (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat < μ c x) :
    KA x + c - 2 * Real.logb 2 ((c : ℝ) + 2) ≤
      ((KMOf D x).toNat : ℝ) + Real.logb 2 Kc.toReal := by
  have hU : universalContinuousSemimeasure x ≠ ⊤ :=
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top x
  have hE : gacsDayWeight c * (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat ≤
      Kc * universalContinuousSemimeasure x :=
    le_trans (by gcongr) (le_trans (ENNReal.le_tsum c) (hdom x))
  have hRtop : Kc * universalContinuousSemimeasure x ≠ ⊤ := ENNReal.mul_ne_top hKtop hU
  have hLtop : gacsDayWeight c * (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat ≠ ⊤ :=
    ENNReal.mul_ne_top (gacsDayWeight_ne_top c) (by finiteness)
  have hR := (ENNReal.toReal_le_toReal hLtop hRtop).mpr hE
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_gacsDayWeight,
    toReal_universalContinuousSemimeasure_eq_rpow] at hR
  apply KA_add_logWeight_le_KMOf
  have hpow : ((2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat).toReal
      = (2 : ℝ)⁻¹ ^ (((KMOf D x).toNat : ℝ)) := by
    rw [Real.rpow_natCast]
    simp
  rw [hpow] at hR
  exact hR

/-- The elementary asymptotic estimate behind the `log log` gap: for all large parameters
`c`, every `L ≥ 1` bounded by `c + log₂ C + log₂ (c + log₂ C)` satisfies
`L - 4 log₂ L ≤ c - 2 log₂ (c + 2) - log₂ K`. -/
lemma gacsDay_loglog_arith_eventually (C : ℕ) (hC : 0 < C) (logK : ℝ) :
    ∀ᶠ c : ℕ in Filter.atTop, ∀ L : ℝ, 1 ≤ L →
      L ≤ (c : ℝ) + Real.logb 2 C + Real.logb 2 ((c : ℝ) + Real.logb 2 C) →
        L - 4 * Real.logb 2 L ≤ (c : ℝ) - 2 * Real.logb 2 ((c : ℝ) + 2) - logK := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hA0 : 0 ≤ Real.logb 2 C := Real.logb_nonneg hb (by exact_mod_cast hC)
  have hcast : Tendsto (fun c : ℕ => (c : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun c : ℕ => Real.logb 2 c) atTop atTop :=
    (Real.tendsto_logb_atTop hb).comp hcast
  have hshift : Tendsto (fun c : ℕ => (c : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 hcast
  have hgrow : Tendsto (fun c : ℕ => ((c : ℝ) + 2) - 4 * Real.logb 2 ((c : ℝ) + 2))
      atTop atTop := by
    exact (tendsto_sub_const_mul_logb_atTop 4).comp hshift
  have hgrow2 : Tendsto (fun c : ℕ =>
      (((c : ℝ) + 2) - 4 * Real.logb 2 ((c : ℝ) + 2)) / 2) atTop atTop :=
    hgrow.atTop_div_const (by norm_num)
  filter_upwards [hcast.eventually_ge_atTop (2 : ℝ),
    hcast.eventually_ge_atTop (Real.logb 2 C),
    hlogT.eventually_ge_atTop (Real.logb 2 C + 7 + logK),
    hgrow2.eventually_ge_atTop (logK + 1)] with c hc2 hcA hclog hcb
  intro L hL1 hLle
  have hcpos : (0 : ℝ) < c := by linarith
  have hlogc2 : Real.logb 2 ((c : ℝ) + 2) ≤ 1 + Real.logb 2 c := by
    have h1 : Real.logb 2 ((c : ℝ) + 2) ≤ Real.logb 2 (2 * c) :=
      (Real.logb_le_logb hb (by linarith) (by linarith)).mpr (by linarith)
    rwa [Real.logb_mul (by norm_num) (by positivity),
      Real.logb_self_eq_one (by norm_num)] at h1
  have hhalf : 2 * Real.logb 2 ((c : ℝ) + 2) + logK ≤ (c : ℝ) / 2 := by linarith
  by_cases hcase : (c : ℝ) / 2 ≤ L
  · have hlogL : Real.logb 2 c - 1 ≤ Real.logb 2 L := by
      have h1 : Real.logb 2 ((c : ℝ) / 2) ≤ Real.logb 2 L :=
        (Real.logb_le_logb hb (by positivity) (by linarith)).mpr hcase
      rwa [Real.logb_div (by positivity) (by norm_num),
        Real.logb_self_eq_one (by norm_num)] at h1
    have hlogcA : Real.logb 2 ((c : ℝ) + Real.logb 2 C) ≤ 1 + Real.logb 2 c := by
      have h1 : Real.logb 2 ((c : ℝ) + Real.logb 2 C) ≤ Real.logb 2 (2 * c) :=
        (Real.logb_le_logb hb (by linarith) (by linarith)).mpr (by linarith)
      rwa [Real.logb_mul (by norm_num) (by positivity),
        Real.logb_self_eq_one (by norm_num)] at h1
    linarith
  · push Not at hcase
    have hlogL : 0 ≤ Real.logb 2 L := Real.logb_nonneg hb hL1
    linarith

/-- Quantitative extraction from the explicit request family. This is the
analytic bridge between the request family and Theorem 87: form the weighted mixture,
apply universal-semimeasure domination, convert the resulting multiplicative
bound to a complexity gap, and use the witness-length estimates to obtain an
unbounded sequence of exact lengths. -/
theorem gacsDayQuantitative_of_requestFamily
    (D : BitStream → BitStream) (C : ℕ)
    (μ : ℕ → BitString → ℝ≥0∞)
    (h_child : ∀ c x, μ c (x ++ [false]) + μ c (x ++ [true]) ≤ μ c x)
    (h_root : ∀ c, μ c [] ≤ (2 : ℝ≥0∞)⁻¹ ^ c)
    (h_witness : ∀ c, ∃ x,
      x.length ≤ (C * 2 ^ c) ^ (C * 2 ^ c) ∧
        (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat < μ c x)
    (h_lsc : IsLSC fun x _ => gacsDayMixture μ x) :
    ∃ c : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ x : BitString,
      x.length = n ∧
        KA x + Real.logb 2 (Real.logb 2 n) -
            c * Real.logb 2 (Real.logb 2 (Real.logb 2 n)) ≤
          ((KMOf D x).toNat : ℝ) := by
  choose xs hxs_len hxs_gap using h_witness
  obtain ⟨Kc, hKtop, hdom⟩ := exists_const_mul_universalContinuousSemimeasure_ge
    (gacsDayMixture_children_le μ h_child) (gacsDayMixture_root_le_one μ h_root) h_lsc
  set logK := Real.logb 2 Kc.toReal with hlogK
  have hgap : ∀ c : ℕ, KA (xs c) + (c : ℝ) - 2 * Real.logb 2 ((c : ℝ) + 2)
      ≤ ((KMOf D (xs c)).toNat : ℝ) + logK :=
    fun c => gacsDay_gap_of_domination D μ Kc hKtop hdom c (xs c) (hxs_gap c)
  have hlen : Tendsto (fun c : ℕ => (xs c).length) atTop atTop :=
    gacsDay_witness_lengths_unbounded D logK (fun c => c) xs tendsto_id hgap
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h
    · exfalso
      subst h0
      obtain ⟨c, hc⟩ := (hlen.eventually_ge_atTop 2).exists
      have hb := hxs_len c
      simp at hb
      omega
    · exact h
  refine ⟨4, fun N => ?_⟩
  obtain ⟨c, hc16, harith⟩ := ((hlen.eventually_ge_atTop (max N 16)).and
    (gacsDay_loglog_arith_eventually C hC logK)).exists
  refine ⟨(xs c).length, le_trans (le_max_left _ _) hc16, xs c, rfl, ?_⟩
  have hn16 : 16 ≤ (xs c).length := le_trans (le_max_right _ _) hc16
  have hn1 : 1 < (xs c).length := by omega
  have hnR : (16 : ℝ) ≤ ((xs c).length : ℝ) := by exact_mod_cast hn16
  have hb2 : (1 : ℝ) < 2 := by norm_num
  have hlogn : (4 : ℝ) ≤ Real.logb 2 ((xs c).length : ℝ) := by
    have h1 : Real.logb 2 (16 : ℝ) ≤ Real.logb 2 ((xs c).length : ℝ) :=
      (Real.logb_le_logb hb2 (by norm_num) (by linarith)).mpr hnR
    have h16 : Real.logb 2 (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    linarith [h16 ▸ h1]
  have hL1 : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((xs c).length : ℝ)) := by
    have h1 : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((xs c).length : ℝ)) :=
      (Real.logb_le_logb hb2 (by norm_num) (by linarith)).mpr (by linarith)
    rwa [Real.logb_self_eq_one (by norm_num)] at h1
  have hcast : (((C * 2 ^ c) ^ (C * 2 ^ c) : ℕ) : ℝ)
      = ((C : ℝ) * 2 ^ c) ^ ((C : ℝ) * 2 ^ c) := by
    have hM : ((C : ℝ) * 2 ^ c) = ((C * 2 ^ c : ℕ) : ℝ) := by push_cast; ring
    rw [hM, show (((C * 2 ^ c : ℕ) : ℝ)) ^ (((C * 2 ^ c : ℕ) : ℝ))
        = (((C * 2 ^ c : ℕ) : ℝ)) ^ ((C * 2 ^ c : ℕ)) from Real.rpow_natCast _ _]
    push_cast
    ring
  have hlenR : ((xs c).length : ℝ) ≤ ((C : ℝ) * 2 ^ c) ^ ((C : ℝ) * 2 ^ c) := by
    rw [← hcast]
    exact_mod_cast hxs_len c
  have hLle := loglog_length_le_parameter C c (xs c) hlenR hn1 hC
  have hstep := harith (Real.logb 2 (Real.logb 2 ((xs c).length : ℝ))) hL1 hLle
  have hg := hgap c
  linarith

end Kolmogorov
