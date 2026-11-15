/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.VovkDichotomy
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.BookmakerGame
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.VanLambalgen
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ChangeOfMeasure.KLRandomness

/-!
# Separations

Separation results between notions of frequency randomness and effective randomness.

We construct sequences that are random with respect to one notion but not another:

* `exists_isMisesKLRandom_not_isMartinLofRandom`: a Mises–Kolmogorov–Loveland random sequence
  that is not Martin-Löf random;
* `exists_isMisesKLRandom_zerosStrictlyDominate`: a Mises–Kolmogorov–Loveland random sequence
  in which zeros strictly dominate;
* `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`: a Mises–Kolmogorov–Loveland random
  sequence from which a Church-admissible rule selects a sequence that is not
  Mises–Kolmogorov–Loveland random;
* `exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom`: a
  Mises–Church–Daley random sequence that stops being Mises–Church random after a computable
  permutation of its terms;
* `exists_isMisesKLRandom_not_isKurtzRandom`: a Mises–Kolmogorov–Loveland random sequence
  that is not Kurtz random.

The constructions use the change-of-measure machinery of the preceding modules (independent
trials, the bookmaker game, the van Lambalgen theorem and the Vovk dichotomy). They formalize
Theorem 203 and Problem 280 of the book by Shen, Uspensky and Vereshchagin
("Kolmogorov complexity and algorithmic randomness").
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Examples -/


private noncomputable def klNotML_my_p (i : ℕ) : NNReal :=
  Real.toNNReal (1 / 2 - 1 / Real.sqrt (i + 5))

private lemma klNotML_my_p_le_one (i : ℕ) :
    klNotML_my_p i ≤ 1 := by
  unfold klNotML_my_p
  rw [Real.toNNReal_le_iff_le_coe]
  have h : (0 : ℝ) ≤ 1 / Real.sqrt ((i : ℝ) + 5) := by positivity
  push_cast
  linarith

/-- Step 1 of the proof of `exists_isMisesKLRandom_not_isMartinLofRandom`: the sequence is
computable. -/
private lemma klNotML_computable :
    IsComputableProbSeq klNotML_my_p := by
  have hN : Computable (fun a : ℕ × ℕ =>
      (((2 ^ a.2 * (a.1 + 5) : ℕ) : ℤ) - ((2 * Nat.sqrt ((a.1 + 5) * 4 ^ a.2) : ℕ) : ℤ))) := by
    have h2s : Primrec (fun a : ℕ × ℕ => 2 ^ a.2) :=
      nat_pow_primrec₂.comp (Primrec.const 2) Primrec.snd
    have h4s : Primrec (fun a : ℕ × ℕ => 4 ^ a.2) :=
      nat_pow_primrec₂.comp (Primrec.const 4) Primrec.snd
    have hn : Primrec (fun a : ℕ × ℕ => a.1 + 5) :=
      Primrec.nat_add.comp Primrec.fst (Primrec.const 5)
    have h1 : Primrec (fun a : ℕ × ℕ => 2 ^ a.2 * (a.1 + 5)) := Primrec.nat_mul.comp h2s hn
    have h2 : Primrec (fun a : ℕ × ℕ => 2 * Nat.sqrt ((a.1 + 5) * 4 ^ a.2)) :=
      Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sqrt.comp (Primrec.nat_mul.comp hn h4s))
    exact (primrec_intSubNat.comp h1 h2).to_comp
  have hD : Computable (fun a : ℕ × ℕ => 2 * (2 ^ a.2 * (a.1 + 5))) := by
    have h2s : Primrec (fun a : ℕ × ℕ => 2 ^ a.2) :=
      nat_pow_primrec₂.comp (Primrec.const 2) Primrec.snd
    have hn : Primrec (fun a : ℕ × ℕ => a.1 + 5) :=
      Primrec.nat_add.comp Primrec.fst (Primrec.const 5)
    exact (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_mul.comp h2s hn)).to_comp
  refine ⟨_, computable_of_num_den hN hD (fun a => by positivity) (fun a => rfl), fun i s => ?_⟩
  set n : ℕ := i + 5 with hn
  set m : ℕ := Nat.sqrt (n * 4 ^ s) with hm
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by rw [hn]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤
                                       i)]
  have hS : (2 : ℝ) < Real.sqrt n := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  set S : ℝ := Real.sqrt n with hSdef
  have hSsq : S * S = n := Real.mul_self_sqrt (by linarith)
  have hS0 : 0 < S := by linarith
  have ht : (0 : ℝ) < 2 ^ s := by positivity
  have h4 : (4 : ℝ) ^ s = (2 ^ s) * (2 ^ s) := by
    rw [← mul_pow]; norm_num
  have hm1 : (m : ℝ) ^ 2 ≤ n * (2 ^ s * 2 ^ s) := by
    have := Nat.sqrt_le' (n * 4 ^ s)
    rw [← hm] at this
    have h : ((m ^ 2 : ℕ) : ℝ) ≤ ((n * 4 ^ s : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    rw [h4] at h
    exact h
  have hm2 : (n : ℝ) * (2 ^ s * 2 ^ s) < ((m : ℝ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' (n * 4 ^ s)
    rw [← hm] at this
    have h : ((n * 4 ^ s : ℕ) : ℝ) < (((m + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    rw [h4] at h
    exact h
  have hts : (m : ℝ) ≤ 2 ^ s * S := by
    apply le_of_sq_le_sq _ (by positivity)
    calc (m : ℝ) ^ 2 ≤ n * (2 ^ s * 2 ^ s) := hm1
      _ = (2 ^ s * S) ^ 2 := by rw [← hSsq]; ring
  have hts2 : 2 ^ s * S < (m : ℝ) + 1 := by
    have hlt : (2 ^ s * S) ^ 2 < ((m : ℝ) + 1) ^ 2 := by
      calc (2 ^ s * S) ^ 2 = n * (2 ^ s * 2 ^ s) := by rw [← hSsq]; ring
        _ < _ := hm2
    by_contra hc
    push Not at hc
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hp : ((klNotML_my_p i : NNReal) : ℝ) = 1 / 2 - 1 / S :=
      by
    unfold klNotML_my_p
    rw [Real.coe_toNNReal _ ?_]
    · have h5 : (i : ℝ) + 5 = n := by rw [hn]; push_cast; ring
      rw [h5]
    · have : 1 / S < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hS
      have h5 : (i : ℝ) + 5 = n := by rw [hn]; push_cast; ring
      rw [h5]
      linarith
  rw [hp]
  have hnpos : (0 : ℝ) < n := by linarith
  have hq2 : ((((((2 ^ s * n : ℕ) : ℤ) - ((2 * m : ℕ) : ℤ) : ℤ) : ℚ) /
      ((2 * (2 ^ s * n) : ℕ) : ℚ) : ℚ) : ℝ) = 1 / 2 - m / (2 ^ s * n) := by
    push_cast
    field_simp
  have hd : (1 / 2 - (m : ℝ) / (2 ^ s * n)) - (1 / 2 - 1 / S) = (2 ^ s * S - m) / (2 ^ s * n) := by
    have : (1 : ℝ) / S = S / n := by
      rw [eq_div_iff hnpos.ne', ← hSsq]; field_simp
    rw [this]
    field_simp
    ring
  change |((((((2 ^ s * n : ℕ) : ℤ) - ((2 * m : ℕ) : ℤ) : ℤ) : ℚ) /
      ((2 * (2 ^ s * n) : ℕ) : ℚ) : ℚ) : ℝ) - _| ≤ _
  rw [hq2, hd, abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
    div_le_iff₀ (by positivity), inv_pow]
  have h1 : (1 : ℝ) ≤ n := by linarith
  have h3 : ((2 : ℝ) ^ s)⁻¹ * (2 ^ s * n) = n := by field_simp
  rw [h3]
  linarith

private lemma klNotML_converges_aux (i : ℕ) :
    |(klNotML_my_p i : ℝ) - (1 / 2 : ℝ)| =
      1 / Real.sqrt (i + 5) := by
  have h5 : (5 : ℝ) ≤ i + 5 := by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
  have hs2 : (2 : ℝ) < Real.sqrt (i + 5) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have hpos : 0 < 1 / Real.sqrt (i + 5) := by positivity
  have hlt : 1 / Real.sqrt (i + 5) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  unfold klNotML_my_p
  rw [Real.coe_toNNReal _ (by linarith)]
  rw [show 1 / 2 - 1 / Real.sqrt (i + 5) - 1 / 2 = -(1 / Real.sqrt (i + 5)) by ring,
    abs_neg, abs_of_pos hpos]

/-- Step 2 of the proof of `exists_isMisesKLRandom_not_isMartinLofRandom`: the sequence
converges computably to `1/2`. -/
private lemma klNotML_converges :
    ∃ N : ℚ → ℕ, Computable N ∧
      ∀ ε : ℚ, 0 < ε → ∀ i, N ε ≤ i → |(klNotML_my_p i : ℝ) -
          (1 / 2 : ℝ)| < ε := by
  refine ⟨fun ε => ε.den * ε.den / (ε.num.natAbs * ε.num.natAbs) + 1, ?_, ?_⟩
  · have hnum : Computable (fun ε : ℚ => ε.num.natAbs) :=
      (ComputableReals.primrec_intNatAbs.to_comp).comp computable_ratNum
    have hden : Computable (fun ε : ℚ => ε.den) := computable_ratDen
    exact Computable.succ.comp
      (Computable₂.comp Primrec.nat_div.to_comp
        (Computable₂.comp Primrec.nat_mul.to_comp hden hden)
        (Computable₂.comp Primrec.nat_mul.to_comp hnum hnum))
  · intro ε hε i hi
    rw [klNotML_converges_aux]
    have hnumpos : 0 < ε.num := Rat.num_pos.mpr hε
    set a : ℕ := ε.num.natAbs with ha
    set b : ℕ := ε.den with hb
    have hapos : 0 < a := by rw [ha]; omega
    have hbpos : 0 < b := ε.den_pos
    have hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ) := by
      rw [Rat.cast_def]
      congr 1
      have : (ε.num : ℝ) = ((ε.num.natAbs : ℤ) : ℝ) := by
        rw [Int.natAbs_of_nonneg hnumpos.le]
      rw [this]; simp [ha]
    have h1 : b * b < a * a * i := by
      have := Nat.lt_mul_div_succ (b * b) (show 0 < a * a from Nat.mul_pos hapos hapos)
      calc b * b < a * a * (b * b / (a * a) + 1) := by
            simpa [mul_comm] using this
        _ ≤ a * a * i := Nat.mul_le_mul_left _ hi
    have h2 : ((b : ℝ) / a) ^ 2 < i + 5 := by
      have h1' : (b : ℝ) * b < a * a * i := by exact_mod_cast h1
      have hapos' : (0 : ℝ) < a := by exact_mod_cast hapos
      rw [div_pow, div_lt_iff₀ (by positivity)]
      nlinarith
    have h3 : (b : ℝ) / a < Real.sqrt (i + 5) := Real.lt_sqrt_of_sq_lt h2
    have hapos' : (0 : ℝ) < a := by exact_mod_cast hapos
    have hbpos' : (0 : ℝ) < b := by exact_mod_cast hbpos
    rw [hεab, div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [div_lt_iff₀ hapos'] at h3
    linarith

/-- Step 3 of the proof of `exists_isMisesKLRandom_not_isMartinLofRandom`: the square
differences are not summable. -/
private lemma klNotML_not_summable :
    ¬ Summable fun i => ((klNotML_my_p i : ℝ) - (1 / 2 : ℝ)) ^
                          2 := by
  intro hs
  have heq : ∀ i : ℕ,
      ((klNotML_my_p i : ℝ) - (1 / 2 : ℝ)) ^ 2
        = 1 / ((i : ℝ) + 5) := by
    intro i
    have hpos : (0 : ℝ) < (i : ℝ) + 5 := by positivity
    have hs2 : (2 : ℝ) ≤ Real.sqrt ((i : ℝ) + 5) := by
      apply Real.le_sqrt_of_sq_le
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      nlinarith
    have hspos : (0 : ℝ) < Real.sqrt ((i : ℝ) + 5) := by linarith
    have hle : 1 / Real.sqrt ((i : ℝ) + 5) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hspos (by norm_num)]
      linarith
    have hc : (klNotML_my_p i : ℝ)
        = 1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) := by
      unfold klNotML_my_p
      rw [Real.coe_toNNReal _ (by linarith)]
    rw [hc]
    have : (1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) - 1 / 2) ^ 2
        = ((Real.sqrt ((i : ℝ) + 5)) ^ 2)⁻¹ := by
      rw [show (1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) - 1 / 2) = -(1 / Real.sqrt ((i : ℝ) + 5)) by
        ring]
      rw [neg_sq, div_pow, one_pow, one_div]
    rw [this, Real.sq_sqrt hpos.le, one_div]
  have hs' : Summable fun i : ℕ => 1 / ((i : ℝ) + 5) := by
    simpa only [heq] using hs
  have h5 : Summable fun n : ℕ => 1 / (n : ℝ) := by
    rw [← summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 5]
    simpa [Nat.cast_add, Nat.cast_ofNat] using hs'
  exact Real.not_summable_one_div_natCast h5

/-- Step 4 of the proof of `exists_isMisesKLRandom_not_isMartinLofRandom`: there exists a
random witness. -/
private lemma klNotML_random_witness :
    ∃ w, IsMartinLofRandom (independentTrials klNotML_my_p
        klNotML_my_p_le_one) w := by
  have hμ := isComputableMeasure_independentTrials
    klNotML_my_p_le_one
    klNotML_computable
  rcases exists_universal_martinLof_test hμ with ⟨U, hU⟩
  have h_eff : IsEffectivelyNull (independentTrials
      klNotML_my_p
      klNotML_my_p_le_one) (⋂ n, U n) :=
    ⟨U, hU.1.1, Set.Subset.refl _, hU.1.2⟩
  have h_meas_zero : independentTrials klNotML_my_p
      klNotML_my_p_le_one (⋂ n, U n) = 0 :=
    h_eff.measure_eq_zero
  have h_compl_nonempty : (⋂ n, U n)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h_eq
    rw [h_eq] at h_meas_zero
    simp at h_meas_zero
  rcases h_compl_nonempty with ⟨x, hx⟩
  refine ⟨x, fun V hV hx_in_V => ?_⟩
  have h_null_V : IsEffectivelyNull (independentTrials
      klNotML_my_p
      klNotML_my_p_le_one) (⋂ n, V n) :=
    ⟨V, hV.1, Set.Subset.refl _, hV.2⟩
  exact hx (hU.2 _ h_null_V hx_in_V)

/-- Step 5 of the proof of `exists_isMisesKLRandom_not_isMartinLofRandom`: the witness is
not Martin-Lof random for the uniform measure. -/
private lemma klNotML_not_uniform
    {w : CantorSeq}
    (hw : IsMartinLofRandom (independentTrials klNotML_my_p
        klNotML_my_p_le_one) w) :
    ¬ IsMartinLofRandom uniformMeasure w := by
  intro hu
  have hhalf : ∀ _ : ℕ, ((1 / 2 : NNReal)) ≤ 1 := fun _ => by
    rw [one_div]; exact inv_le_one_of_one_le₀ (by norm_num)
  have hunif : independentTrials (fun _ : ℕ => (1 / 2 : NNReal)) hhalf = uniformMeasure := rfl
  have hc' : IsComputableProbSeq (fun _ : ℕ => (1 / 2 : NNReal)) :=
    ⟨fun _ => (1 / 2 : ℚ), Computable.const _, fun i s => by
      simp⟩
  refine not_isMartinLofRandom_and_of_not_summable
    klNotML_my_p_le_one hhalf
    klNotML_computable hc' ?_ w ⟨hw, hunif ▸ hu⟩
  simpa using klNotML_not_summable

/-- **SUV Theorem 203(a), p. 307.**  There is a Mises-Kolmogorov-Loveland random sequence with
frequency `1/2` that is not Martin-Löf random with respect to the uniform measure. -/
theorem exists_isMisesKLRandom_not_isMartinLofRandom :
    ∃ w, IsMisesKLRandom w ∧ ¬ IsMartinLofRandom uniformMeasure w := by
  obtain ⟨w, hw⟩ := klNotML_random_witness
  refine ⟨w, ?_, klNotML_not_uniform hw⟩
  have hconv : ConvergesComputably klNotML_my_p (1 / 2) :=
    ⟨klNotML_computable, klNotML_converges⟩
  exact isMisesKLRandomAt_of_isMartinLofRandom klNotML_my_p_le_one
    (by norm_num) (by norm_num) hconv hw

/-- The slowly growing integers `g i = ⌊(i + 16)^(1/4)⌋` (an iterated integer square root) used in
the
proof of `exists_isMisesKLRandom_zerosStrictlyDominate`. -/
private def zsd_g (i : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (i + 16))

private lemma zsd_g_ge_two (i : ℕ) :
    2 ≤ zsd_g i := by
  unfold zsd_g
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  omega

private lemma zsd_g_pow_four_le (i : ℕ) :
    zsd_g i ^ 4 ≤ i + 16 := by
  unfold zsd_g
  have h1 : Nat.sqrt (Nat.sqrt (i + 16)) ^ 2 ≤ Nat.sqrt (i + 16) := Nat.sqrt_le' _
  have h2 : Nat.sqrt (i + 16) ^ 2 ≤ i + 16 := Nat.sqrt_le' _
  calc Nat.sqrt (Nat.sqrt (i + 16)) ^ 4 = (Nat.sqrt (Nat.sqrt (i + 16)) ^ 2) ^ 2 := by ring
    _ ≤ Nat.sqrt (i + 16) ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ i + 16 := h2

/-- The probabilities of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: `pM M i = 0`
for `i < M` (the first `M` terms are zeros) and `pM M i = 1/2 - 1/(2 g i) ∈ [1/4, 1/2)` for
`i ≥ M`, a sequence converging slowly to `1/2`. -/
private noncomputable def zsd_pM (M i : ℕ) : NNReal :=
  if i < M then 0
  else Real.toNNReal (1 / 2 - 1 / (2 * (zsd_g i : ℝ)))

private lemma zsd_pM_coe_of_lt {M i : ℕ} (h : i < M) :
    (zsd_pM M i : ℝ) = 0 := by
  simp [zsd_pM, h]

private lemma zsd_pM_coe_of_ge {M i : ℕ} (h : M ≤ i) :
    (zsd_pM M i : ℝ) =
      1 / 2 - 1 / (2 * (zsd_g i : ℝ)) := by
  have hg : (2 : ℝ) ≤ (zsd_g i : ℝ) := by
    exact_mod_cast zsd_g_ge_two i
  have h1 : 1 / (2 * (zsd_g i : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  unfold zsd_pM
  rw [ite_eq_right (not_lt.mpr h), Real.coe_toNNReal _ (by linarith)]

private lemma zsd_pM_mem {M i : ℕ} (h : M ≤ i) :
    1 / 4 ≤ (zsd_pM M i : ℝ) ∧
      (zsd_pM M i : ℝ) < 1 / 2 := by
  have hg : (2 : ℝ) ≤ (zsd_g i : ℝ) := by
    exact_mod_cast zsd_g_ge_two i
  rw [zsd_pM_coe_of_ge h]
  have h1 : 1 / (2 * (zsd_g i : ℝ)) ≤ 1 / 4 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
        (by linarith : (4 : ℝ) ≤ 2 * (zsd_g i : ℝ))
    exact this
  have h2 : 0 < 1 / (2 * (zsd_g i : ℝ)) := by positivity
  constructor <;> linarith

private lemma zsd_pM_le_one (M : ℕ) :
    ∀ i, zsd_pM M i ≤ 1 := by
  intro i
  by_cases h : i < M
  · simp [zsd_pM, h]
  · have := zsd_pM_mem (not_lt.mp h)
    exact NNReal.coe_le_one.mp (by linarith [this.2])

/-- The sequences whose first `M` terms are all zero. -/
private def zsd_F (M : ℕ) : Set CantorSeq :=
  {w | ∀ i, i < M → w i = false}

private lemma zsd_primrec_g :
    Primrec zsd_g := by
  unfold zsd_g
  exact Primrec.nat_sqrt.comp (Primrec.nat_sqrt.comp
    (Primrec.nat_add.comp Primrec.id (Primrec.const 16)))

/-- Step 2 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: the sequence
`pM M` is a computable sequence of computable reals (its values are rational). -/
private lemma zsd_computable (M : ℕ) :
    IsComputableProbSeq (zsd_pM M) := by
  have hg := zsd_primrec_g
  have hg2 := zsd_g_ge_two
  have hlt : PrimrecPred (fun a : ℕ × ℕ => a.1 < M) :=
    Primrec.nat_lt.comp Primrec.fst (Primrec.const M)
  have hN : Primrec (fun a : ℕ × ℕ =>
      ((if a.1 < M then 0 else zsd_g a.1 - 1 : ℕ) : ℤ)) :=
    ComputableReals.primrec_natCastInt.comp
      (Primrec.ite hlt (Primrec.const 0)
        (Primrec.nat_sub.comp (hg.comp Primrec.fst) (Primrec.const 1)))
  have hD : Primrec (fun a : ℕ × ℕ =>
      (if a.1 < M then 1 else 2 * zsd_g a.1 : ℕ)) :=
    Primrec.ite hlt (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.const 2) (hg.comp Primrec.fst))
  let f : ℕ × ℕ → ℚ := fun a => if a.1 < M then 0 else
    (((zsd_g a.1 : ℕ) : ℚ) - 1) /
      (2 * ((zsd_g a.1 : ℕ) : ℚ))
  have hf : Computable f := by
    refine computable_of_num_den
      (N := fun a : ℕ × ℕ =>
        ((if a.1 < M then 0 else zsd_g a.1 - 1 : ℕ) : ℤ))
      (D := fun a : ℕ × ℕ =>
        (if a.1 < M then 1 else 2 * zsd_g a.1 : ℕ))
      hN.to_comp hD.to_comp ?_ ?_
    · intro a
      by_cases h : a.1 < M
      · simp [h]
      · have := hg2 a.1
        simp only [h, ite_false]
        omega
    · intro a
      by_cases h : a.1 < M
      · simp [f, h]
      · have h2 := hg2 a.1
        have h1 : 1 ≤ zsd_g a.1 := by omega
        simp only [f, h, ite_false]
        push_cast [Nat.cast_sub h1]
        ring
  refine ⟨f, hf, fun i s => ?_⟩
  have key : ((f (i, s) : ℚ) : ℝ) = (zsd_pM M i : ℝ) := by
    by_cases h : i < M
    · rw [zsd_pM_coe_of_lt h]
      simp [f, h]
    · rw [zsd_pM_coe_of_ge (not_lt.mp h)]
      have h2 : (2 : ℝ) ≤ (zsd_g i : ℝ) := by
        exact_mod_cast hg2 i
      have h3 : (zsd_g i : ℝ) ≠ 0 := by linarith
      simp only [f, h, ite_false]
      push_cast
      field_simp
  rw [key, sub_self, abs_zero]
  positivity

private lemma zsd_le_g (d i : ℕ)
    (h : d ^ 4 ≤ i + 16) : d ≤ zsd_g i := by
  unfold zsd_g
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  calc d * d * (d * d) = d ^ 4 := by ring
    _ ≤ i + 16 := h

private lemma zsd_inv_den_le (ε : ℚ) (hε : 0 < ε) :
    1 / (ε.den : ℝ) ≤ (ε : ℝ) := by
  have hnum : (1 : ℝ) ≤ (ε.num : ℝ) := by
    have h1 : 0 < ε.num := Rat.num_pos.mpr hε
    have h2 : (1 : ℤ) ≤ ε.num := by omega
    exact_mod_cast h2
  have hden : (0 : ℝ) < (ε.den : ℝ) := by exact_mod_cast ε.den_pos
  rw [Rat.cast_def]
  gcongr

/-- Step 3 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: `pM M`
converges to `1/2` with a computable rate. -/
private lemma zsd_rate (M : ℕ) :
    ∃ N : ℚ → ℕ, Computable N ∧ ∀ ε : ℚ, 0 < ε → ∀ i, N ε ≤ i →
      |(zsd_pM M i : ℝ) - 1 / 2| < ε := by
  refine ⟨fun ε => M + ε.den ^ 4, ?_, ?_⟩
  · have hpow : Computable (fun ε : ℚ => ε.den ^ 4) :=
      Computable₂.comp (f := fun a b : ℕ => a ^ b) nat_pow_primrec₂.to_comp computable_ratDen
        (Computable.const 4)
    exact Computable₂.comp (f := fun a b : ℕ => a + b) Primrec.nat_add.to_comp
      (Computable.const M) hpow
  · intro ε hε i hi
    have hi' : M + ε.den ^ 4 ≤ i := hi
    have hMi : M ≤ i := by omega
    have hden4 : ε.den ^ 4 ≤ i + 16 := by omega
    have hg : ε.den ≤ zsd_g i :=
      zsd_le_g _ _ hden4
    have hdpos : (0 : ℝ) < (ε.den : ℝ) := by exact_mod_cast ε.den_pos
    have hgR : (ε.den : ℝ) ≤ (zsd_g i : ℝ) := by
      exact_mod_cast hg
    have hgpos : (0 : ℝ) < (zsd_g i : ℝ) :=
      lt_of_lt_of_le hdpos hgR
    rw [zsd_pM_coe_of_ge hMi]
    have h1 : 1 / 2 - 1 / (2 * (zsd_g i : ℝ)) - 1 / 2
        = -(1 / (2 * (zsd_g i : ℝ))) := by ring
    have h2 : 0 < 1 / (2 * (zsd_g i : ℝ)) :=
      one_div_pos.mpr (by linarith)
    rw [h1, abs_neg, abs_of_pos h2]
    calc 1 / (2 * (zsd_g i : ℝ))
        ≤ 1 / (2 * (ε.den : ℝ)) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
      _ < 1 / (ε.den : ℝ) := one_div_lt_one_div_of_lt hdpos (by linarith)
      _ ≤ (ε : ℝ) := zsd_inv_den_le ε hε

private lemma zsd_F_eq (M : ℕ) :
    zsd_F M = cantorCylinder (List.replicate M false) := by
  ext w
  simp only [zsd_F, cantorCylinder, IsCantorPrefix,
    Set.mem_ofPred_eq, List.length_replicate, List.getElem_replicate]

private lemma zsd_massR (M : ℕ) :
    massR (independentTrials (zsd_pM M)
      (zsd_pM_le_one M)) (List.replicate M false) = 1 := by
  rw [massR_independentTrials]
  apply Finset.prod_eq_one
  intro i _
  have hi : (i : ℕ) < M := by simpa using i.2
  simp [zsd_pM_coe_of_lt hi]

/-- Step 4 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: under
independent trials with probabilities `pM M`, the first `M` terms are zeros almost surely (`pM M i =
0`
for `i < M`). -/
private lemma zsd_null (M : ℕ) :
    independentTrials (zsd_pM M)
      (zsd_pM_le_one M)
      (zsd_F M)ᶜ = 0 := by
  have h1 := zsd_massR M
  have h2 : cantorMass (independentTrials (zsd_pM M)
      (zsd_pM_le_one M)) (List.replicate M false) = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp h1
  rw [zsd_F_eq]
  exact (prob_compl_eq_zero_iff (measurableSet_cantorCylinder _)).mpr h2

/-- Every prefix of a sequence whose first `M` terms are zeros has positive mass under independent
trials with probabilities `pM M`. -/
private lemma zsd_mass_ne_zero (M k : ℕ)
    {w : CantorSeq} (hw : w ∈ zsd_F M) :
    cantorMass (independentTrials (zsd_pM M)
      (zsd_pM_le_one M)) (cantorPrefix w k) ≠ 0 := by
  intro h0
  have hm := massR_independentTrials (zsd_pM M)
    (zsd_pM_le_one M) (cantorPrefix w k)
  have hR : massR (independentTrials (zsd_pM M)
      (zsd_pM_le_one M)) (cantorPrefix w k) = 0 := by
    simp [massR, h0]
  rw [hm] at hR
  have hne : (∏ i : Fin (cantorPrefix w k).length,
      if (cantorPrefix w k)[i] then (zsd_pM M i : ℝ)
        else 1 - (zsd_pM M i : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hget : (cantorPrefix w k)[i] = w i := by simp
    rw [hget]
    by_cases hlt : (i : ℕ) < M
    · have h1 : w i = false := hw i hlt
      have h2 := zsd_pM_coe_of_lt hlt
      simp [h1, h2]
    · have h3 := zsd_pM_mem (not_lt.mp hlt)
      cases hb : w i
      · simp only [Bool.false_eq_true, ite_false]
        linarith [h3.2]
      · simp only [ite_true]
        linarith [h3.1]
  exact hne hR

/-- Step 5 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: on a sequence
whose first `M` terms are zeros all prefixes have positive mass for `pM M` (the probabilities are
`0` only for `i < M`, and `pM M i ∈ [1/4, 1/2)` for `i ≥ M`), so the conditional probabilities are
the
`pM M i` and `condSum` is the sum of the `pM M i`. -/
private lemma zsd_condSum (M n : ℕ) {w : CantorSeq}
    (hw : w ∈ zsd_F M) :
    condSum (independentTrials (zsd_pM M)
      (zsd_pM_le_one M)) w n =
      ∑ i ∈ Finset.range n, (zsd_pM M i : ℝ) := by
  unfold condSum
  apply Finset.sum_congr rfl
  intro k _
  rw [condOne_independentTrials _ _
    (zsd_mass_ne_zero M k hw)]
  simp

/-- Auxiliary for step 6: `r = √√(n+16)` satisfies `1 ≤ r` and `r ^ 4 = n + 16`. -/
private lemma zsd_root (n : ℕ) :
    1 ≤ Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ∧
      Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ^ 4 = (n : ℝ) + 16 := by
  have hx : (0 : ℝ) ≤ (n : ℝ) + 16 := by positivity
  have hx1 : (1 : ℝ) ≤ (n : ℝ) + 16 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 16) := Real.one_le_sqrt.mpr hx1
  have h2 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt ((n : ℝ) + 16)) := Real.one_le_sqrt.mpr h1
  refine ⟨h2, ?_⟩
  have h3 : Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ^ 2 = Real.sqrt ((n : ℝ) + 16) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : Real.sqrt ((n : ℝ) + 16) ^ 2 = (n : ℝ) + 16 := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ^ 4
      = (Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ^ 2) ^ 2 := by ring
    _ = (n : ℝ) + 16 := by rw [h3, h4]

/-- Auxiliary for step 6: each of the first `n` probabilities lies below
`1/2 - 1/(2 r)`, `r = √√(n+16)`. -/
private lemma zsd_term_le (M n i : ℕ) (hi : i < n) :
    (zsd_pM M i : ℝ) ≤
      1 / 2 - 1 / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) := by
  obtain ⟨hr1, hr4⟩ := zsd_root n
  have hr0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt ((n : ℝ) + 16)) := Real.sqrt_nonneg _
  by_cases hiM : i < M
  · rw [zsd_pM_coe_of_lt hiM]
    have h1 : 1 / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · rw [zsd_pM_coe_of_ge (not_lt.mp hiM)]
    have hg2 : 2 ≤ zsd_g i :=
      zsd_g_ge_two i
    have hg : (2 : ℝ) ≤ (zsd_g i : ℝ) := by
      exact_mod_cast hg2
    have hg4 : (zsd_g i : ℝ) ^ 4 ≤ (i : ℝ) + 16 := by
      exact_mod_cast zsd_g_pow_four_le i
    have hin : (i : ℝ) + 16 ≤ (n : ℝ) + 16 := by
      have : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.le
      linarith
    have hle : (zsd_g i : ℝ) ≤
        Real.sqrt (Real.sqrt ((n : ℝ) + 16)) := by
      by_contra hcon
      have hlt : Real.sqrt (Real.sqrt ((n : ℝ) + 16)) <
          (zsd_g i : ℝ) := not_le.mp hcon
      have hpow : Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ^ 4 <
          (zsd_g i : ℝ) ^ 4 :=
        pow_lt_pow_left₀ hlt hr0 (by norm_num)
      linarith
    have h1 : 1 / (2 * (zsd_g i : ℝ)) ≥
        1 / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

/-- Step 6 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: the sum of the
first `n` probabilities lies below `n/2` by `n / (2 (n+16)^(1/4))` at least (every term lies below
`1/2 - 1/(2 (n+16)^(1/4))`, since `g i ^ 4 ≤ i + 16 < n + 16`). -/
private lemma zsd_sum_le (M n : ℕ) :
    ∑ i ∈ Finset.range n, (zsd_pM M i : ℝ) ≤
      n / 2 - n / (2 * Real.sqrt (Real.sqrt (n + 16))) := by
  calc ∑ i ∈ Finset.range n, (zsd_pM M i : ℝ)
      ≤ ∑ i ∈ Finset.range n, (1 / 2 - 1 / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16)))) :=
        Finset.sum_le_sum (fun i hi =>
          zsd_term_le M n i (Finset.mem_range.mp hi))
    _ = n / 2 - n / (2 * Real.sqrt (Real.sqrt (n + 16))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

private lemma zsd_count_add (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b <;> simp <;> omega

private lemma zsd_ones_add_zeros
    (w : CantorSeq) (n : ℕ) : onesCount w n + zerosCount w n = n := by
  unfold onesCount zerosCount
  rw [zsd_count_add]
  exact cantorPrefix_length w n

private lemma zsd_exponent (n r : ℝ) (hn : 0 < n)
    (hr : 0 < r) : -(n / (2 * r) / 2) ^ 2 / (4 * n) = -(n / (64 * r ^ 2)) := by
  field_simp
  ring

/-- Step 7 for an arbitrary probability measure `μ`, set `F` and bound `S` on `condSum` over `F`. -/
private lemma zsd_aux (μ : Measure CantorSeq)
    [IsProbabilityMeasure μ] (F : Set CantorSeq) (n : ℕ) (hn : 0 < n) (S : ℝ)
    (hS : ∀ w ∈ F, condSum μ w n = S)
    (hSle : S ≤ n / 2 - n / (2 * Real.sqrt (Real.sqrt (n + 16)))) :
    μ ({w | zerosCount w n ≤ onesCount w n} ∩ F) ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16))))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 16) := Real.one_le_sqrt.mpr (by linarith)
  have hr1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt ((n : ℝ) + 16)) := Real.one_le_sqrt.mpr hs1
  have hr2 : Real.sqrt (Real.sqrt ((n : ℝ) + 16)) ^ 2 = Real.sqrt ((n : ℝ) + 16) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hrpos : (0 : ℝ) < Real.sqrt (Real.sqrt ((n : ℝ) + 16)) := by linarith
  have hsub : ({w | zerosCount w n ≤ onesCount w n} ∩ F) ⊆
      {w | (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) / 2 <
        |onesR w n - condSum μ w n|} := by
    rintro w ⟨hz, hF⟩
    have hz' : zerosCount w n ≤ onesCount w n := hz
    have hsum := zsd_ones_add_zeros w n
    have h1 : (n : ℝ) ≤ 2 * onesR w n := by
      have h2 : n ≤ 2 * onesCount w n := by omega
      have h3 : (n : ℝ) ≤ 2 * (onesCount w n : ℝ) := by exact_mod_cast h2
      exact h3
    have h4 : (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) ≤ onesR w n - S := by
      linarith
    have hpos : 0 < (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) := by positivity
    change (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) / 2 < |onesR w n - condSum μ w n|
    rw [hS w hF]
    calc (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) / 2
        < (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) := by linarith
      _ ≤ onesR w n - S := h4
      _ ≤ |onesR w n - S| := le_abs_self _
  have hd : (0 : ℝ) ≤ (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) / 2 := by positivity
  calc μ ({w | zerosCount w n ≤ onesCount w n} ∩ F)
      ≤ μ {w | (n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) / 2 <
          |onesR w n - condSum μ w n|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / (2 * Real.sqrt (Real.sqrt ((n : ℝ) + 16))) / 2) ^
        2
          / (4 * n))) := measure_abs_ones_sub_condSum_gt_le μ hn hd
    _ = ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt ((n : ℝ) + 16))))) := by
        rw [zsd_exponent _ _ hnR hrpos, hr2]

/-- Step 7 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: the tail bound
(Theorem 198): the probability that a sequence with `M` leading zeros has at least as many ones as
zeros among its first `n` terms is at most `2 exp (-n / (64 √(n+16)))`. -/
private lemma zsd_bound (M n : ℕ) (hn : 0 < n) :
    independentTrials (zsd_pM M)
      (zsd_pM_le_one M)
      ({w | zerosCount w n ≤ onesCount w n} ∩ zsd_F M) ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16))))) :=
  zsd_aux
    (independentTrials (zsd_pM M)
      (zsd_pM_le_one M))
    (zsd_F M) n hn
    (∑ i ∈ Finset.range n, (zsd_pM M i : ℝ))
    (fun _ hw => zsd_condSum M n hw)
    (zsd_sum_le M n)

private lemma zsd_step8_bound (n : ℕ) (hn : 16 ≤ n) :
    2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16)))) ≤ (192 * 64 ^ 4) * (1 / (n : ℝ) ^ 2) := by
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hs : 0 < Real.sqrt ((n : ℝ) + 16) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt ((n : ℝ) + 16) ^ 2 = (n : ℝ) + 16 := Real.sq_sqrt (by linarith)
  have hs4 : Real.sqrt ((n : ℝ) + 16) ^ 4 = ((n : ℝ) + 16) ^ 2 := by
    calc Real.sqrt ((n : ℝ) + 16) ^ 4 = (Real.sqrt ((n : ℝ) + 16) ^ 2) ^ 2 := by ring
      _ = ((n : ℝ) + 16) ^ 2 := by rw [hs2]
  generalize Real.sqrt ((n : ℝ) + 16) = s at hs hs2 hs4 ⊢
  have hy : 0 < (n : ℝ) / (64 * s) := by positivity
  generalize hy_def : (n : ℝ) / (64 * s) = y at hy ⊢
  have hexp : y ^ 4 / 24 ≤ Real.exp y := by
    have := Real.pow_div_factorial_le_exp y hy.le 4
    simpa [Nat.factorial] using this
  have hy4 : y ^ 4 = (n : ℝ) ^ 4 / (64 ^ 4 * ((n : ℝ) + 16) ^ 2) := by
    rw [← hy_def, div_pow, mul_pow, hs4]
  have h16 : ((n : ℝ) + 16) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  have hlow : (n : ℝ) ^ 2 / (4 * 64 ^ 4) ≤ y ^ 4 := by
    rw [hy4, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left h16 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * 64 ^ 4)
    nlinarith [h1]
  have hy4pos : 0 < y ^ 4 := by positivity
  have hexpneg : Real.exp (-y) ≤ 24 / y ^ 4 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) hy4pos]
    linarith [hexp]
  have hfinal : 24 / y ^ 4 ≤ 96 * 64 ^ 4 / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hy4pos (by positivity)]
    have := hlow
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith [this]
  calc 2 * Real.exp (-y) ≤ 2 * (96 * 64 ^ 4 / (n : ℝ) ^ 2) := by
        gcongr
        exact hexpneg.trans hfinal
    _ = (192 * 64 ^ 4) * (1 / (n : ℝ) ^ 2) := by ring

private lemma zsd_summable_real :
    Summable (fun n : ℕ => 2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16))))) := by
  have hg : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine summable_of_isBigO_nat hg ?_
  refine Asymptotics.IsBigO.of_bound (192 * 64 ^ 4) ?_
  filter_upwards [Filter.eventually_ge_atTop 16] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact zsd_step8_bound n hn

/-- Step 8 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: the bounds of
step 7 are summable (they are `O(1/n²)`: `exp (-y) ≤ 24 / y⁴`). -/
private lemma zsd_summable :
    (∑' n : ℕ, ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16)))))) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    zsd_summable_real]
  exact ENNReal.ofReal_ne_top

/-- Step 9 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: the first
Borel-Cantelli lemma in tail form (no measurability needed): if `μ Fᶜ = 0`, `μ (E n ∩ F) ≤ b n` for
`n > M` and the tail sum of `b` after `M` is below `1`, then `F` minus the events `E n` (`n > M`)
has positive measure. -/
private lemma zsd_borelCantelli
    (μ : Measure CantorSeq) [IsProbabilityMeasure μ] (F : Set CantorSeq) (E : ℕ → Set CantorSeq)
    (b : ℕ → ℝ≥0∞) (M : ℕ) (hF : μ Fᶜ = 0) (hE : ∀ n, M < n → μ (E n ∩ F) ≤ b n)
    (hb : ∑' k, b (k + (M + 1)) < 1) :
    0 < μ {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} := by
  have hcov : (Set.univ : Set CantorSeq) ⊆
      {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} ∪ (Fᶜ ∪ ⋃ k, (E (k + (M + 1)) ∩ F)) := by
    intro w _
    by_cases hwF : w ∈ F
    · by_cases h : ∀ n, M < n → w ∉ E n
      · exact Or.inl ⟨hwF, h⟩
      · push Not at h
        obtain ⟨n, hn, hwn⟩ := h
        refine Or.inr (Or.inr (Set.mem_iUnion.2 ⟨n - (M + 1), ?_⟩))
        have : n - (M + 1) + (M + 1) = n := Nat.sub_add_cancel hn
        rw [this]
        exact ⟨hwn, hwF⟩
    · exact Or.inr (Or.inl hwF)
  have h1 : (1 : ℝ≥0∞) ≤ μ {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} + ∑' k, b (k + (M + 1)) := by
    calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ ≤ μ ({w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} ∪ (Fᶜ ∪ ⋃ k, (E (k + (M + 1)) ∩ F))) :=
          measure_mono hcov
      _ ≤ μ {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} + μ (Fᶜ ∪ ⋃ k, (E (k + (M + 1)) ∩ F)) :=
          measure_union_le _ _
      _ ≤ μ {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} + (μ Fᶜ + μ (⋃ k, (E (k + (M + 1)) ∩ F))) := by
          gcongr
          exact measure_union_le _ _
      _ ≤ μ {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n} + ∑' k, b (k + (M + 1)) := by
          rw [hF, zero_add]
          gcongr
          calc μ (⋃ k, (E (k + (M + 1)) ∩ F)) ≤ ∑' k, μ (E (k + (M + 1)) ∩ F) :=
                measure_iUnion_le _
            _ ≤ ∑' k, b (k + (M + 1)) :=
                ENNReal.tsum_le_tsum (fun k => hE _ (by omega))
  rcases eq_zero_or_pos (μ {w | w ∈ F ∧ ∀ n, M < n → w ∉ E n}) with hz | hpos
  · rw [hz, zero_add] at h1
    exact absurd hb (not_lt.2 h1)
  · exact hpos

/-- Step 10 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: a set of
positive
measure for a computable measure contains a Martin-Löf random point. -/
private lemma zsd_random {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) {A : Set CantorSeq} (hA : 0 < μ A) :
    ∃ w ∈ A, IsMartinLofRandom μ w := by
  by_contra hcon
  push Not at hcon
  exact absurd ((isEffectivelyNull_iff_forall_not_random hμ A).2 hcon).measure_eq_zero (ne_of_gt hA)

/-- Step 11 of the proof of `exists_isMisesKLRandom_zerosStrictlyDominate`: if the first
`n`
terms of `w` are zeros then `w` has no ones and `n` zeros among them. -/
private lemma zsd_prefix {w : CantorSeq} {n : ℕ}
    (h : ∀ i, i < n → w i = false) : onesCount w n = 0 ∧ zerosCount w n = n := by
  have hp : cantorPrefix w n = List.replicate n false := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n := by simpa using h1
      simp [h i hi]
  unfold onesCount zerosCount
  rw [hp]
  exact ⟨List.count_eq_zero.mpr (by simp [List.mem_replicate]), List.count_replicate_self⟩

/-- **SUV Theorem 203(b), p. 307.**  There is a Mises-Kolmogorov-Loveland random sequence with
frequency `1/2` where each non-empty prefix has more zeros than ones. -/
theorem exists_isMisesKLRandom_zerosStrictlyDominate :
    ∃ w, IsMisesKLRandom w ∧ ZerosStrictlyDominate w := by
  have hsum := zsd_summable
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∑' k, (fun n : ℕ => ENNReal.ofReal
      (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16)))))) (k + (M + 1)) < 1 := by
    have ht := ENNReal.tendsto_sum_nat_add (fun n : ℕ => ENNReal.ofReal
      (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16)))))) hsum
    have hev := ht.eventually (gt_mem_nhds zero_lt_one)
    obtain ⟨i, hi, hi1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    exact ⟨i - 1, by rwa [Nat.sub_add_cancel hi1]⟩
  have hp := zsd_pM_le_one M
  have hcs := zsd_computable M
  have hcomp := isComputableMeasure_independentTrials hp hcs
  have hpos := zsd_borelCantelli
    (independentTrials (zsd_pM M) hp)
    (zsd_F M)
    (fun n => {w | zerosCount w n ≤ onesCount w n})
    (fun n => ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / (64 * Real.sqrt (n + 16)))))) M
    (zsd_null M)
    (fun n hn => zsd_bound M n (by omega)) hM
  obtain ⟨w, ⟨hwF, hwE⟩, hwML⟩ :=
    zsd_random hcomp hpos
  refine ⟨w, isMisesKLRandomAt_of_isMartinLofRandom hp (by norm_num) (by norm_num)
    ⟨hcs, zsd_rate M⟩ hwML, ?_⟩
  intro n hn
  by_cases hnM : n ≤ M
  · obtain ⟨h1, h2⟩ := zsd_prefix
      (w := w) (n := n) (fun i hi => hwF i (by omega))
    omega
  · exact not_le.mp (hwE n (by omega))

private def selKL_blockLen (k : ℕ) : ℕ :=
  2 ^ (k + 5) * (k + 3) ^ 2

private def selKL_blockStart : ℕ → ℕ
| 0 => 0
| k + 1 => selKL_blockStart k + 2 *
             selKL_blockLen k + 1

private def selKL_blockIdx (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => selKL_blockStart k ≤
                               n) n

private noncomputable def selKL_pSeq (i : ℕ) :
    NNReal :=
  let k := selKL_blockIdx i
  let start := selKL_blockStart k
  if i = start then 1 / 2
  else if i ≤ start + selKL_blockLen k then
    Real.toNNReal (1 / 2 + 1 / (k + 3 : ℝ))
  else
    Real.toNNReal (1 / 2 - 1 / (k + 3 : ℝ))

private def selKL_selR : Set BitString :=
  {x |
    let k := selKL_blockIdx x.length
    let start := selKL_blockStart k
    x.length = start ∨
    (x.length > start ∧ x.length ≤ start +
        selKL_blockLen k ∧ List.getD
        (x : List Bool) start false = true) ∨
    (x.length > start + selKL_blockLen k ∧
        List.getD (x : List Bool) start false = false)
  }

private def selKL_goodSet : Set CantorSeq :=
  {w | ∀ k,
    let start := selKL_blockStart k
    let len := selKL_blockLen k
    let leftOnes := ((List.range len).map (fun i => w (start + 1 + i))).count true
    let rightOnes := ((List.range len).map (fun i => w (start + 1 + len + i))).count true
    len < 2 * leftOnes ∧ 2 * rightOnes < len}

private def selKL_chunkStart (m : ℕ → ℕ) (k : ℕ) :
    ℕ :=
  (List.range k).foldl (fun acc j => acc + m j + 1) 0

private def selKL_KeyPredictable (m : ℕ → ℕ)
    (u : CantorSeq) : Prop :=
  ∀ k, u (selKL_chunkStart m k) =
    decide (m k < 2 * ((List.range (m k)).map
        (fun t => u (selKL_chunkStart m k + 1 +
                    t))).count true)

/-- Step 1 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
probability sequence is bounded by 1. -/
private lemma selKL_pSeq_le_one (i : ℕ) :
    selKL_pSeq i ≤ 1 := by
  unfold selKL_pSeq
  have hk : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 3) ∧ 1 / ((k : ℝ) + 3) ≤ 1 / 3 := by
    intro k
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine ⟨by positivity, ?_⟩
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  simp only []
  split_ifs
  · rw [one_div]
    exact inv_le_one_of_one_le₀ (by norm_num)
  · refine Real.toNNReal_le_one.2 ?_
    have := hk (selKL_blockIdx i)
    linarith [this.1, this.2]
  · refine Real.toNNReal_le_one.2 ?_
    have := hk (selKL_blockIdx i)
    linarith [this.1, this.2]

/-- Step 2 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
block length is computable. -/
private lemma selKL_blockLen_comp :
    Computable selKL_blockLen := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  unfold selKL_blockLen
  exact (Primrec.nat_mul.comp
    (hpow.comp (Primrec.const 2) (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp
      (Primrec.succ.comp (Primrec.succ.comp Primrec.id))))))
    (hpow.comp (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp Primrec.id)))
      (Primrec.const 2))).to_comp

private lemma selKL_conv_blockLen_primrec :
    Primrec selKL_blockLen := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  unfold selKL_blockLen
  exact Primrec.nat_mul.comp
    (hpow.comp (Primrec.const 2) (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp
      (Primrec.succ.comp (Primrec.succ.comp Primrec.id))))))
    (hpow.comp (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp Primrec.id)))
      (Primrec.const 2))

private lemma selKL_conv_blockStart_primrec
    :
    Primrec selKL_blockStart := by
  have h : Primrec (Nat.rec (motive := fun _ => ℕ) 0 (fun y IH =>
      IH + 2 * selKL_blockLen y + 1)) :=
    Primrec.nat_rec₁ (0 : ℕ)
      (Primrec.succ.comp (Primrec.nat_add.comp Primrec.snd
        (Primrec.nat_mul.comp (Primrec.const 2)
          (selKL_conv_blockLen_primrec.comp
            Primrec.fst)))).to₂
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [selKL_blockStart]
    rw [← ih]

private lemma selKL_conv_blockIdx_primrec :
    Primrec selKL_blockIdx := by
  unfold selKL_blockIdx
  exact Primrec.nat_findGreatest (p := fun n k =>
      selKL_blockStart k ≤ n) Primrec.id
    (Primrec.nat_le.comp
      (selKL_conv_blockStart_primrec.comp
        Primrec.snd) Primrec.fst)

private def selKL_conv_num (i : ℕ) : ℕ :=
  if i = selKL_blockStart
      (selKL_blockIdx i) then 1
  else if i ≤ selKL_blockStart
      (selKL_blockIdx i) +
      selKL_blockLen
        (selKL_blockIdx i) then
    selKL_blockIdx i + 5
  else selKL_blockIdx i + 1

private def selKL_conv_den (i : ℕ) : ℕ :=
  if i = selKL_blockStart
      (selKL_blockIdx i) then 2
  else 2 * selKL_blockIdx i + 6

private lemma selKL_conv_num_primrec :
    Primrec selKL_conv_num := by
  have hI := selKL_conv_blockIdx_primrec
  have hS := selKL_conv_blockStart_primrec
  have hL := selKL_conv_blockLen_primrec
  unfold selKL_conv_num
  refine Primrec.ite (Primrec.eq.comp Primrec.id (hS.comp hI)) (Primrec.const 1)
    (Primrec.ite (Primrec.nat_le.comp Primrec.id
      (Primrec.nat_add.comp (hS.comp hI) (hL.comp hI)))
      (Primrec.nat_add.comp hI (Primrec.const 5)) (Primrec.nat_add.comp hI (Primrec.const 1)))

private lemma selKL_conv_den_primrec :
    Primrec selKL_conv_den := by
  have hI := selKL_conv_blockIdx_primrec
  have hS := selKL_conv_blockStart_primrec
  unfold selKL_conv_den
  refine Primrec.ite (Primrec.eq.comp Primrec.id (hS.comp hI)) (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hI) (Primrec.const 6))

private lemma selKL_conv_den_pos (i : ℕ) :
    0 < selKL_conv_den i := by
  unfold selKL_conv_den
  split_ifs <;> omega

private lemma selKL_conv_pSeq_eq (i : ℕ) :
    (selKL_pSeq i : ℝ) =
      (selKL_conv_num i : ℝ) /
      (selKL_conv_den i : ℝ) := by
  unfold selKL_pSeq
    selKL_conv_num
    selKL_conv_den
  dsimp only
  generalize selKL_blockIdx i = k
  have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  have hk1 : 1 / (k + 3 : ℝ) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hk2 : 0 < 1 / (k + 3 : ℝ) := by positivity
  split_ifs with h1 h2
  · simp
  · rw [Real.coe_toNNReal _ (by linarith)]
    push_cast
    field_simp
    ring
  · rw [Real.coe_toNNReal _ (by linarith)]
    push_cast
    field_simp
    ring

private lemma selKL_conv_blockStart_ge
    (k : ℕ) :
    k ≤ selKL_blockStart k := by
  induction k with
  | zero => simp [selKL_blockStart]
  | succ k ih =>
    simp only [selKL_blockStart]
    omega

/-- Step 3 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
probability sequence converges computably to 1/2. -/
private lemma selKL_conv :
    ConvergesComputably selKL_pSeq ((1 : ℝ) / 2)
        := by
  have hI := selKL_conv_blockIdx_primrec
  have hS := selKL_conv_blockStart_primrec
  refine ⟨?_, ?_⟩
  · refine ⟨fun p => ((selKL_conv_num p.1 :
                       ℤ) : ℚ) /
        (selKL_conv_den p.1 : ℚ), ?_, ?_⟩
    · refine computable_of_num_den
        (N := fun p => (selKL_conv_num p.1 :
                         ℤ))
        (D := fun p => selKL_conv_den p.1)
        ?_ ?_ (fun p => selKL_conv_den_pos
                          p.1)
        (fun p => rfl)
      · exact (ComputableReals.primrec_natCastInt.to_comp.comp
          (selKL_conv_num_primrec.to_comp.comp
            Computable.fst))
      · exact selKL_conv_den_primrec.to_comp.comp
          Computable.fst
    · intro i s
      rw [selKL_conv_pSeq_eq]
      push_cast
      rw [sub_self, abs_zero]
      positivity
  · refine ⟨fun ε => selKL_blockStart ε.den,
      (hS.to_comp.comp computable_ratDen), ?_⟩
    intro ε hε i hi
    set d := ε.den with hd
    have hdpos : 0 < d := ε.den_pos
    have hdi : d ≤ i :=
      (selKL_conv_blockStart_ge d).trans hi
    have hkd : d ≤ selKL_blockIdx i :=
      Nat.le_findGreatest hdi hi
    have hε1 : 1 / (d : ℝ) ≤ (ε : ℝ) := by
      have hnum : (1 : ℤ) ≤ ε.num := Rat.num_pos.mpr hε
      have : (1 : ℚ) / d ≤ ε := by
        rw [← Rat.num_div_den ε, div_le_div_iff_of_pos_right (by exact_mod_cast hdpos)]
        exact_mod_cast hnum
      have h := (Rat.cast_le (K := ℝ)).mpr this
      push_cast at h
      exact h
    unfold selKL_pSeq
    dsimp only
    generalize selKL_blockIdx i = k at hkd
    have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hkr : (d : ℝ) ≤ k := by exact_mod_cast hkd
    have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    have hk1 : 1 / (k + 3 : ℝ) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    have hk2 : 0 < 1 / (k + 3 : ℝ) := by positivity
    have hlt : 1 / (k + 3 : ℝ) < ε := by
      refine lt_of_lt_of_le ?_ hε1
      apply one_div_lt_one_div_of_lt hdr
      linarith
    split_ifs with h1 h2
    · simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      rw [show (1 : ℝ) / 2 - 1 / 2 = 0 by ring, abs_zero]
      exact_mod_cast hε
    · rw [Real.coe_toNNReal _ (by linarith)]
      rw [show (1 : ℝ) / 2 + 1 / (k + 3) - 1 / 2 = 1 / (k + 3) by ring, abs_of_pos hk2]
      exact hlt
    · rw [Real.coe_toNNReal _ (by linarith)]
      rw [show (1 : ℝ) / 2 - 1 / (k + 3) - 1 / 2 = -(1 / (k + 3)) by ring, abs_neg, abs_of_pos hk2]
      exact hlt

/-- Step 4 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
selection rule is decidable. -/
private lemma selKL_selR_dec :
    IsDecidableSet selKL_selR := by
  classical
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hlen : Primrec selKL_blockLen := by
    change Primrec (fun k : ℕ => 2 ^ (k + 5) * (k + 3) ^ 2)
    exact Primrec.nat_mul.comp
      (hpow.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.id (Primrec.const 5)))
      (hpow.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 3)) (Primrec.const 2))
  have hstart : Primrec selKL_blockStart := by
    have h₂ : Primrec₂ (fun (k s : ℕ) => s + 2 * selKL_blockLen k + 1) :=
      Primrec.nat_add.comp
        (Primrec.nat_add.comp Primrec.snd
          (Primrec.nat_mul.comp (Primrec.const 2) (hlen.comp Primrec.fst)))
        (Primrec.const 1)
    refine (Primrec.nat_rec₁ (0 : ℕ) h₂).of_eq fun k => ?_
    induction k with
    | zero => rfl
    | succ k ih =>
      change _ = selKL_blockStart k + _ + 1
      rw [← ih]
  have hidx : Primrec selKL_blockIdx :=
    Primrec.nat_findGreatest Primrec.id
      (Primrec.nat_le.comp (hstart.comp Primrec.snd) Primrec.fst)
  have hL : Primrec (fun x : BitString => x.length) := Primrec.list_length
  have hs : Primrec (fun x : BitString =>
      selKL_blockStart
        (selKL_blockIdx x.length)) :=
    hstart.comp (hidx.comp hL)
  have hk : Primrec (fun x : BitString =>
      selKL_blockLen
        (selKL_blockIdx x.length)) :=
    hlen.comp (hidx.comp hL)
  have hg : Primrec (fun x : BitString =>
      List.getD (x : List Bool) (selKL_blockStart
        (selKL_blockIdx x.length)) false) :=
    (Primrec.list_getD false).comp Primrec.id hs
  have hsk : Primrec (fun x : BitString =>
      selKL_blockStart
        (selKL_blockIdx x.length) +
      selKL_blockLen
        (selKL_blockIdx x.length)) :=
    Primrec.nat_add.comp hs hk
  have hP : PrimrecPred (fun x : BitString =>
      x.length = selKL_blockStart
        (selKL_blockIdx x.length) ∨
      (x.length > selKL_blockStart
          (selKL_blockIdx x.length) ∧
        x.length ≤ selKL_blockStart
          (selKL_blockIdx x.length) +
          selKL_blockLen
            (selKL_blockIdx x.length) ∧
        List.getD (x : List Bool)
            (selKL_blockStart
          (selKL_blockIdx x.length)) false =
              true) ∨
      (x.length > selKL_blockStart
          (selKL_blockIdx x.length) +
          selKL_blockLen
            (selKL_blockIdx x.length) ∧
        List.getD (x : List Bool)
            (selKL_blockStart
          (selKL_blockIdx x.length)) false =
              false)) := by
    have hbt : Primrec (fun _ : BitString => true) := Primrec.const true
    have hbf : Primrec (fun _ : BitString => false) := Primrec.const false
    exact (Primrec.eq.comp hL hs).or
      (((Primrec.nat_lt.comp hs hL).and
        ((Primrec.nat_le.comp hL hsk).and (Primrec.eq.comp hg hbt))).or
      ((Primrec.nat_lt.comp hsk hL).and (Primrec.eq.comp hg hbf)))
  refine ⟨fun x => decide (x.length =
                     selKL_blockStart
        (selKL_blockIdx x.length) ∨
      (x.length > selKL_blockStart
          (selKL_blockIdx x.length) ∧
        x.length ≤ selKL_blockStart
          (selKL_blockIdx x.length) +
          selKL_blockLen
            (selKL_blockIdx x.length) ∧
        List.getD (x : List Bool)
            (selKL_blockStart
          (selKL_blockIdx x.length)) false =
              true) ∨
      (x.length > selKL_blockStart
          (selKL_blockIdx x.length) +
          selKL_blockLen
            (selKL_blockIdx x.length) ∧
        List.getD (x : List Bool)
            (selKL_blockStart
          (selKL_blockIdx x.length)) false =
              false)),
    hP.decide.to_comp, fun x => ?_⟩
  simp only [decide_eq_true_eq]
  rfl

/-- Step 1 of the proof of
`selKL_half_fail`: the number of `true`s in
a mapped range list is a sum of bit values. -/
private lemma selKL_half_fail_count_eq
    (f : ℕ → Bool) (n : ℕ) :
    ((((List.range n).map f).count true : ℕ) : ℝ) = ∑ t ∈ Finset.range n, bitVal (f t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.sum_range_succ]
    push_cast
    rw [ih]
    cases h : f n <;> simp [bitVal, h]

/-- Step 2 of the proof of
`selKL_half_fail`: Hoeffding for a window
of independent trials. -/
private lemma selKL_half_fail_hoeffding
    {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (c n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (independentTrials p hp).real
        {w | ε ≤ ∑ t ∈ Finset.range n, (bitVal (w (c + t)) - (p (c + t) : ℝ))} ≤
      Real.exp (-ε ^ 2 / (2 * n * (1 / 4 : ℝ))) ∧
    (independentTrials p hp).real
        {w | ε ≤ ∑ t ∈ Finset.range n, ((p (c + t) : ℝ) - bitVal (w (c + t)))} ≤
      Real.exp (-ε ^ 2 / (2 * n * (1 / 4 : ℝ))) := by
  set μ := independentTrials p hp with hμ
  have hmeas : ∀ i, Measurable (fun w : CantorSeq => bitVal (w i)) :=
    fun i => measurable_bitVal.comp (measurable_pi_apply i)
  have hind0 : ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (w : CantorSeq) => bitVal (w i) - (p i : ℝ)) μ := by
    have h := isMisesKLRandomAt_of_isMartinLofRandom_aux_iIndep hp
    exact h.comp (fun i (b : Bool) => bitVal b - (p i : ℝ)) (fun i => measurable_from_top)
  have hind : ProbabilityTheory.iIndepFun
      (fun (t : ℕ) (w : CantorSeq) => bitVal (w (c + t)) - (p (c + t) : ℝ)) μ :=
    hind0.precomp (g := fun t => c + t) (add_right_injective c)
  have hmean : ∀ i, ∫ w, bitVal (w i) ∂μ = (p i : ℝ) := by
    intro i
    have h1 : (fun w : CantorSeq => bitVal (w i)) =
        Set.indicator {w : CantorSeq | w i = true} 1 := by
      funext w; cases h : w i <;> simp [bitVal, Set.indicator, h]
    have hms : MeasurableSet {w : CantorSeq | w i = true} :=
      measurableSet_eq_fun (measurable_pi_apply i) measurable_const
    rw [h1, integral_indicator_one hms, measureReal_def]
    have h2 := isMisesKLRandomAt_of_isMartinLofRandom_aux_coord_mass hp i true
    simp only [ite_true] at h2
    rw [hμ, h2, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  have hsg0 : ∀ i, ProbabilityTheory.HasSubgaussianMGF
      (fun w : CantorSeq => bitVal (w i) - (p i : ℝ)) (1 / 4 : NNReal) μ := by
    intro i
    have hb : ∀ᵐ w ∂μ, bitVal (w i) ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards with w
      cases w i <;> simp [bitVal]
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ)
      (X := fun w : CantorSeq => bitVal (w i)) (hmeas i).aemeasurable hb
    rw [hmean i] at h
    have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : NNReal) := by
      simp
      norm_num
    rwa [hc] at h
  have hindneg : ProbabilityTheory.iIndepFun
      (fun (t : ℕ) (w : CantorSeq) => -(bitVal (w (c + t)) - (p (c + t) : ℝ))) μ :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hupper := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (n := n) hind (fun i _ => hsg0 (c + i)) hε
  have hlower := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (n := n) hindneg (fun i _ => (hsg0 (c + i)).neg) hε
  have hq : (((1 / 4 : NNReal)) : ℝ) = 1 / 4 := by norm_num
  rw [hq] at hupper hlower
  refine ⟨hupper, ?_⟩
  simpa only [neg_sub] using hlower

/-- Step 3 of the proof of
`selKL_half_fail`: block starts are
strictly increasing. -/
private lemma selKL_half_fail_start_mono :
    StrictMono selKL_blockStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  change selKL_blockStart k <
    selKL_blockStart k +
      2 * selKL_blockLen k + 1
  omega

/-- Step 4 of the proof of
`selKL_half_fail`: the block index inside
block `k`. -/
private lemma selKL_half_fail_blockIdx_eq
    (k i : ℕ)
    (h1 : selKL_blockStart k ≤ i)
    (h2 : i < selKL_blockStart (k + 1)) :
    selKL_blockIdx i = k := by
  have hmono := selKL_half_fail_start_mono
  have hk : k ≤ selKL_blockStart k :=
    hmono.id_le k
  unfold selKL_blockIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hk.trans h1, fun _ => h1, ?_⟩
  intro m hkm _ hm
  have : selKL_blockStart (k + 1) ≤
      selKL_blockStart m :=
    hmono.monotone (by omega)
  omega

/-- Step 5 of the proof of
`selKL_half_fail`: the exact value of the
probabilities inside block `k`. -/
private lemma selKL_half_fail_pSeq_val
    (k t : ℕ) (ht : t < selKL_blockLen k) :
    ((selKL_pSeq
        (selKL_blockStart k + 1 + t) : NNReal) :
            ℝ)
      = 1 / 2 + 1 / ((k : ℝ) + 3) ∧
    ((selKL_pSeq
        (selKL_blockStart k + 1 +
          selKL_blockLen k + t) : NNReal) : ℝ)
      = 1 / 2 - 1 / ((k : ℝ) + 3) := by
  have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 3) := by positivity
  have hle : 1 / ((k : ℝ) + 3) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hsucc : selKL_blockStart (k + 1) =
      selKL_blockStart k +
        2 * selKL_blockLen k + 1 := rfl
  constructor
  · rw [selKL_pSeq]
    rw [selKL_half_fail_blockIdx_eq k _
      (by omega) (by omega)]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    exact Real.coe_toNNReal _ (by linarith)
  · rw [selKL_pSeq]
    rw [selKL_half_fail_blockIdx_eq k _
      (by omega) (by omega)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact Real.coe_toNNReal _ (by linarith)

/-- Step 6 of the proof of
`selKL_half_fail`: the Hoeffding exponent
is small enough. -/
private lemma selKL_half_fail_exp_le
    (k : ℕ) :
    Real.exp (-((selKL_blockLen k : ℝ) *
        (1 / ((k : ℝ) + 3))) ^ 2 /
      (2 * (selKL_blockLen k : ℝ) * (1 / 4 : ℝ)))
      ≤ 2 ^ (-((k : ℝ) + 7)) := by
  have hk3 : ((k : ℝ) + 3) ≠ 0 := by positivity
  have hL : (selKL_blockLen k : ℝ) =
      2 ^ (k + 5) * ((k : ℝ) + 3) ^ 2 := by
    unfold selKL_blockLen
    push_cast
    ring
  have hexp : -((selKL_blockLen k : ℝ) *
        (1 / ((k : ℝ) + 3))) ^ 2 /
      (2 * (selKL_blockLen k : ℝ) * (1 / 4 : ℝ))
      = -((2 ^ (k + 6) : ℕ) : ℝ) := by
    rw [hL]
    push_cast
    field_simp
    ring
  rw [hexp]
  have hrpow : (2 : ℝ) ^ (-((k : ℝ) + 7)) = (((2 : ℝ) ^ (k + 7))⁻¹) := by
    rw [Real.rpow_neg (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [hrpow, Real.exp_neg]
  apply inv_anti₀ (by positivity)
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : k + 7 ≤ 2 ^ (k + 6) := Nat.lt_two_pow_self (n := k + 6)
  calc (2 : ℝ) ^ (k + 7) ≤ 2 ^ (2 ^ (k + 6)) :=
        pow_le_pow_right₀ (by norm_num) h2
    _ ≤ Real.exp 1 ^ (2 ^ (k + 6)) := pow_le_pow_left₀ (by norm_num) h1 _
    _ = Real.exp (((2 ^ (k + 6) : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul]
        simp

/-- Step 5a of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
failure probability per half block is bounded. -/
private lemma selKL_half_fail (k : ℕ) :
    independentTrials selKL_pSeq selKL_pSeq_le_one
      {w | ¬ (selKL_blockLen k < 2 *
          ((List.range (selKL_blockLen k)).map
          (fun i => w (selKL_blockStart k + 1 +
                      i))).count true)} ≤ ENNReal.ofReal (2 ^ (- ((k : ℝ) + 7))) ∧
    independentTrials selKL_pSeq selKL_pSeq_le_one
      {w | ¬ (2 * ((List.range (selKL_blockLen
          k)).map (fun i => w (selKL_blockStart k
                              + 1 + selKL_blockLen
                              k + i))).count true <
                              selKL_blockLen k)} ≤
                              ENNReal.ofReal (2 ^ (- ((k : ℝ) + 7))) := by
  have hp := selKL_pSeq_le_one
  have hexp := selKL_half_fail_exp_le k
  have hval := selKL_half_fail_pSeq_val k
  have hδ : (0 : ℝ) < 1 / ((k : ℝ) + 3) := by positivity
  have hε : (0 : ℝ) ≤ (selKL_blockLen k : ℝ) *
      (1 / ((k : ℝ) + 3)) := by positivity
  have hmeasle : ∀ A S : Set CantorSeq, A ⊆ S →
      (independentTrials selKL_pSeq hp).real S ≤
        2 ^ (-((k : ℝ) + 7)) →
      independentTrials selKL_pSeq hp A ≤
        ENNReal.ofReal (2 ^ (-((k : ℝ) + 7))) := by
    intro A S hAS hS
    calc independentTrials selKL_pSeq hp A
        ≤ independentTrials selKL_pSeq hp S :=
          measure_mono hAS
      _ = ENNReal.ofReal
          ((independentTrials selKL_pSeq hp).real
              S) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hS
  constructor
  · obtain ⟨-, hH⟩ :=
      selKL_half_fail_hoeffding hp
      (selKL_blockStart k + 1)
      (selKL_blockLen k) _ hε
    refine hmeasle _ _ ?_ (hH.trans hexp)
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    have hw' := not_lt.mp hw
    have hc := selKL_half_fail_count_eq
      (fun i => w (selKL_blockStart k + 1 + i))
      (selKL_blockLen k)
    beta_reduce at hc
    have hsumP : ∑ t ∈ Finset.range
        (selKL_blockLen k),
        ((selKL_pSeq
          (selKL_blockStart k + 1 + t) : NNReal) :
              ℝ)
        = (selKL_blockLen k : ℝ) *
          (1 / 2 + 1 / ((k : ℝ) + 3)) := by
      rw [Finset.sum_congr rfl (fun t ht => (hval t (Finset.mem_range.mp ht)).1)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, hsumP, ← hc]
    have h2 : (2 * ((((List.range (selKL_blockLen
        k)).map
        (fun i => w (selKL_blockStart k + 1 +
                    i))).count true : ℕ) : ℝ))
        ≤ (selKL_blockLen k : ℝ) := by
      exact_mod_cast hw'
    nlinarith
  · obtain ⟨hH, -⟩ :=
      selKL_half_fail_hoeffding hp
      (selKL_blockStart k + 1 +
        selKL_blockLen k)
      (selKL_blockLen k) _ hε
    refine hmeasle _ _ ?_ (hH.trans hexp)
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    have hw' := not_lt.mp hw
    have hc := selKL_half_fail_count_eq
      (fun i => w (selKL_blockStart k + 1 +
        selKL_blockLen k + i))
      (selKL_blockLen k)
    beta_reduce at hc
    have hsumP : ∑ t ∈ Finset.range
        (selKL_blockLen k),
        ((selKL_pSeq
          (selKL_blockStart k + 1 +
            selKL_blockLen k + t) : NNReal) : ℝ)
        = (selKL_blockLen k : ℝ) *
          (1 / 2 - 1 / ((k : ℝ) + 3)) := by
      rw [Finset.sum_congr rfl (fun t ht => (hval t (Finset.mem_range.mp ht)).2)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, hsumP, ← hc]
    have h2 : (selKL_blockLen k : ℝ) ≤
        2 * ((((List.range (selKL_blockLen k)).map
        (fun i => w (selKL_blockStart k + 1 +
          selKL_blockLen k + i))).count true :
              ℕ) : ℝ) := by
      exact_mod_cast hw'
    nlinarith

/-- Step 5 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`: good
set has positive measure. -/
private lemma selKL_measure_pos :
    0 < independentTrials selKL_pSeq selKL_pSeq_le_one selKL_goodSet := by
  set μ := independentTrials selKL_pSeq
      selKL_pSeq_le_one with hμ
  have hcov : (selKL_goodSet)ᶜ ⊆ ⋃ k : ℕ,
      ({w : CantorSeq | ¬ (selKL_blockLen k < 2 *
          ((List.range (selKL_blockLen k)).map
          (fun i => w (selKL_blockStart k + 1 +
                      i))).count true)} ∪
       {w : CantorSeq | ¬ (2 * ((List.range
           (selKL_blockLen k)).map (fun i =>
             w (selKL_blockStart k + 1 +
             selKL_blockLen k + i))).count true <
             selKL_blockLen k)}) := by
    intro w hw
    simp only [Set.mem_compl_iff, selKL_goodSet,
        Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨k, hk⟩ := hw
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨k, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hk ⟨hcon.1, hcon.2⟩
  have hbound : μ (selKL_goodSet)ᶜ ≤ ∑' k : ℕ,
      ENNReal.ofReal (2 * (1 / 128) * (1 / 2 : ℝ) ^ k) := by
    refine (measure_mono hcov).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k =>
      ?_))
    obtain ⟨h1, h2⟩ := selKL_half_fail k
    refine (measure_union_le _ _).trans ?_
    have heq : ENNReal.ofReal (2 ^ (-((k : ℝ) + 7))) = ENNReal.ofReal ((1 / 128) * (1 / 2 : ℝ) ^ k)
        := by
      congr 1
      rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast]
      norm_num
      rw [one_div, inv_pow]
    rw [heq] at h1 h2
    calc _ ≤ ENNReal.ofReal ((1 / 128) * (1 / 2 : ℝ) ^ k) + ENNReal.ofReal ((1 / 128) * (1 / 2 : ℝ)
        ^ k) := add_le_add h1 h2
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hsum : ∑' k : ℕ, ENNReal.ofReal (2 * (1 / 128) * (1 / 2 : ℝ) ^ k) = ENNReal.ofReal
      (1 / 32) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
    · congr 1
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  rw [hsum] at hbound
  have hlt : ENNReal.ofReal (1 / 32) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  rw [pos_iff_ne_zero]
  intro h0
  have := measure_univ_le_add_compl (μ := μ)
      (selKL_goodSet)
  rw [measure_univ, h0, zero_add] at this
  exact absurd (this.trans hbound) (not_le.2 hlt)

open Classical in
/-- The selected prefixes of `w`: the bits of `w` at the first `count P t` positions where the
prefix lies in `R`. -/
private lemma selKL_select_aux_chain
    (R : Set BitString) (w : CantorSeq) (t : ℕ) :
    selectChain R w t =
      (List.range (Nat.count (fun i => cantorPrefix w i ∈ R) t)).map
        (fun j => w (Nat.nth (fun i => cantorPrefix w i ∈ R) j)) := by
  induction t with
  | zero =>
    have h0 : cantorPrefix w 0 = [] := by simp [cantorPrefix]
    simp [selectChain, selectedBits, h0, selectedAux]
  | succ t ih =>
    have h1 : selectChain R w (t + 1) =
        selectChain R w t ++ (if cantorPrefix w t ∈ R then [w t] else []) := by
      unfold selectChain
      rw [cantorPrefix_succ, selectedBits_append_singleton]
    rw [h1, ih, Nat.count_succ]
    by_cases hP : cantorPrefix w t ∈ R
    · simp only [hP, ite_true, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [Nat.nth_count hP]
    · simp [hP]

open Classical in
/-- If `R` contains infinitely many prefixes of `w`, the selected stream is infinite and equals
`w ∘ nth P`. -/
private lemma selKL_select_aux_stream
    (R : Set BitString) (w : CantorSeq)
    (hinf : ∀ n, ∃ i ≥ n, cantorPrefix w i ∈ R) :
    selectStream R w = .infinite (fun j => w (Nat.nth (fun i => cantorPrefix w i ∈ R) j)) := by
  set P : ℕ → Prop := fun i => cantorPrefix w i ∈ R with hPdef
  have hInf : (Set.ofPred P).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨i, hi, hiP⟩ := hinf (n + 1)
    exact ⟨i, hiP, by omega⟩
  have hmem : ∀ y, BitStream.finite y ≤ selectStream R w ↔ ∃ t, y <+: selectChain R w t := fun y =>
    BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w))
        y
  apply BitStream.eq_of_forall_finite_le_iff
  intro y
  rw [hmem]
  change _ ↔ IsCantorPrefix y (fun j => w (Nat.nth P j))
  constructor
  · rintro ⟨t, ht⟩
    rw [selKL_select_aux_chain] at ht
    intro i hi
    have := ht.getElem hi
    rw [this, List.getElem_map, List.getElem_range]
  · intro h
    refine ⟨Nat.nth P y.length, ?_⟩
    rw [selKL_select_aux_chain,
      Nat.count_nth_of_infinite hInf]
    have hy : y = List.map (fun j => w (Nat.nth P j)) (List.range y.length) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        rw [List.getElem_map, List.getElem_range]
        exact (h i h1).symm
    exact ⟨[], by rw [List.append_nil]; exact hy⟩

/-- The block starts are monotone. -/
private lemma selKL_select_aux_blockStart_mono :
    Monotone selKL_blockStart := by
  apply monotone_nat_of_le_succ
  intro k
  change _ ≤ selKL_blockStart k +
    2 * selKL_blockLen k + 1
  omega

/-- Positions inside block `k` have block index `k`. -/
private lemma selKL_select_aux_blockIdx
    (k o : ℕ)
    (ho : o ≤ 2 * selKL_blockLen k) :
    selKL_blockIdx
      (selKL_blockStart k + o) = k := by
  have hge := selKL_conv_blockStart_ge k
  unfold selKL_blockIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => by omega, ?_⟩
  intro m hkm hm hP
  have hP' : selKL_blockStart m ≤
      selKL_blockStart k + o := hP
  have h1 := selKL_select_aux_blockStart_mono
    (show k + 1 ≤ m from hkm)
  have h2 : selKL_blockStart (k + 1) =
      selKL_blockStart k +
        2 * selKL_blockLen k + 1 := rfl
  omega

/-- The position `i` is selected by `selR` from `w`. -/
private def selKL_select_selP
    (w : CantorSeq) (i : ℕ) : Prop :=
  cantorPrefix w i ∈ selKL_selR

/-- Inside block `k`, offset `o` is selected iff it is the key, or it lies in the left half and
the key is `1`, or it lies in the right half and the key is `0`. -/
private lemma selKL_select_aux_selP_iff
    (w : CantorSeq) (k o : ℕ)
    (ho : o ≤ 2 * selKL_blockLen k) :
    selKL_select_selP w
        (selKL_blockStart k + o) ↔
      (o = 0 ∨ (0 < o ∧ o ≤ selKL_blockLen k ∧
          w (selKL_blockStart k) = true) ∨
        (selKL_blockLen k < o ∧
          w (selKL_blockStart k) = false)) := by
  unfold selKL_select_selP
    selKL_selR
  simp only [Set.mem_ofPred_eq, cantorPrefix_length]
  rw [selKL_select_aux_blockIdx k o ho]
  by_cases ho0 : o = 0
  · simp [ho0]
  · have hget : (cantorPrefix w (selKL_blockStart
      k + o)).getD
        (selKL_blockStart k) false =
        w (selKL_blockStart k) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
      simp
    rw [hget]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
      · omega
      · exact Or.inr (Or.inl ⟨by omega, by omega, h3⟩)
      · exact Or.inr (Or.inr ⟨by omega, h2⟩)
    · rintro (h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
      · omega
      · exact Or.inr (Or.inl ⟨by omega, by omega, h3⟩)
      · exact Or.inr (Or.inr ⟨by omega, h2⟩)

open Classical in
/-- The number of selected positions among the first `m` offsets of block `k`. -/
private lemma selKL_select_aux_countQ
    (w : CantorSeq) (k : ℕ) :
    ∀ m, m ≤ 2 * selKL_blockLen k + 1 →
    Nat.count (fun o => selKL_select_selP w
        (selKL_blockStart k + o)) m =
      if w (selKL_blockStart k) = true then
        min m (selKL_blockLen k + 1)
      else (if m = 0 then 0 else 1 + (m - (selKL_blockLen k + 1))) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Nat.count_succ, ih (by omega)]
    have hQ := selKL_select_aux_selP_iff w k
        m (by omega)
    by_cases hk : w (selKL_blockStart k) = true
    · rw [ite_eq_left hk, ite_eq_left hk]
      rw [hk] at hQ
      by_cases hq : selKL_select_selP w
        (selKL_blockStart k + m)
      · rw [ite_eq_left hq]
        rcases hQ.mp hq with h | ⟨h1, h2, _⟩ | ⟨_, h2⟩
        · omega
        · omega
        · exact absurd h2 (by decide)
      · rw [ite_eq_right hq]
        have h1 : ¬ m = 0 := fun h => hq (hQ.mpr (Or.inl h))
        have h2 : ¬ (0 < m ∧ m ≤ selKL_blockLen k)
            :=
          fun h => hq (hQ.mpr (Or.inr (Or.inl ⟨h.1, h.2, rfl⟩)))
        omega
    · have hk' : w (selKL_blockStart k) = false :=
        by
        simpa using hk
      rw [ite_eq_right hk, ite_eq_right hk]
      rw [hk'] at hQ
      by_cases hq : selKL_select_selP w
        (selKL_blockStart k + m)
      · rw [ite_eq_left hq]
        rcases hQ.mp hq with h | ⟨_, _, h3⟩ | ⟨h1, _⟩
        · split_ifs <;> omega
        · exact absurd h3 (by decide)
        · split_ifs <;> omega
      · rw [ite_eq_right hq]
        have h1 : ¬ m = 0 := fun h => hq (hQ.mpr (Or.inl h))
        have h2 : ¬ selKL_blockLen k < m :=
          fun h => hq (hQ.mpr (Or.inr (Or.inr ⟨h, rfl⟩)))
        rw [ite_eq_right h1, ite_eq_right (Nat.succ_ne_zero m)]
        omega

/-- `chunkStart m (k + 1) = chunkStart m k + m k + 1`. -/
private lemma selKL_select_aux_chunkStart_succ
    (m : ℕ → ℕ) (k : ℕ) :
    selKL_chunkStart m (k + 1) =
      selKL_chunkStart m k + m k + 1 := by
  simp [selKL_chunkStart, List.range_succ,
    List.foldl_append]

open Classical in
/-- Before block `k` exactly `chunkStart blockLen k` positions are selected. -/
private lemma selKL_select_aux_count_blockStart
    (w : CantorSeq) (k : ℕ) :
    Nat.count (selKL_select_selP w)
      (selKL_blockStart k) =
    selKL_chunkStart
      selKL_blockLen k := by
  induction k with
  | zero => simp [selKL_blockStart,
      selKL_chunkStart]
  | succ k ih =>
    have h2 : selKL_blockStart (k + 1) =
      selKL_blockStart k +
        (2 * selKL_blockLen k + 1) := by
      change selKL_blockStart k +
        2 * selKL_blockLen k + 1 = _
      omega
    have hc := selKL_select_aux_countQ w k
      (2 * selKL_blockLen k + 1) le_rfl
    have e1 : Nat.count (selKL_select_selP
        w)
        (selKL_blockStart k +
          (2 * selKL_blockLen k + 1)) =
        Nat.count (selKL_select_selP w)
          (selKL_blockStart k) +
        Nat.count (fun o =>
          selKL_select_selP w
          (selKL_blockStart k + o))
          (2 * selKL_blockLen k + 1) :=
              Nat.count_add _ _ _
    rw [h2, e1, ih, hc,
        selKL_select_aux_chunkStart_succ]
    by_cases hk : w (selKL_blockStart k) = true
    · rw [ite_eq_left hk]
      omega
    · rw [ite_eq_right hk, ite_eq_right (by omega :
        2 * selKL_blockLen k + 1 ≠ 0)]
      omega

open Classical in
/-- The selected position at offset `o` of block `k`, preceded by `j` selected offsets of the block,
is the `(chunkStart blockLen k + j)`-th selected position. -/
private lemma selKL_select_aux_nth_of
    (w : CantorSeq) (k j o : ℕ)
    (hP : selKL_select_selP w
      (selKL_blockStart k + o))
    (hc : Nat.count
        (fun o' => selKL_select_selP w
        (selKL_blockStart k + o')) o = j) :
    Nat.nth (selKL_select_selP w)
      (selKL_chunkStart
        selKL_blockLen k + j) =
    selKL_blockStart k + o := by
  have e1 : Nat.count (selKL_select_selP w)
        (selKL_blockStart k + o) =
      Nat.count (selKL_select_selP w)
        (selKL_blockStart k) +
      Nat.count (fun o' => selKL_select_selP
                             w
        (selKL_blockStart k + o')) o :=
            Nat.count_add _ _ _
  rw [selKL_select_aux_count_blockStart w k,
      hc] at e1
  rw [← e1]
  exact Nat.nth_count hP

/-- Step 6 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
sequences in good set select an infinite key predictable sequence. -/
private lemma selKL_select (w : CantorSeq)
    (hw : w ∈ selKL_goodSet) :
    ∃ u, selectStream selKL_selR w = .infinite u ∧ selKL_KeyPredictable selKL_blockLen u := by
  have hinf : ∀ n, ∃ i ≥ n, cantorPrefix w i ∈
      selKL_selR := fun n =>
    ⟨selKL_blockStart n,
      selKL_conv_blockStart_ge n,
      (selKL_select_aux_selP_iff w n 0
          (Nat.zero_le _)).2 (Or.inl rfl)⟩
  refine ⟨fun j =>
    w (Nat.nth (selKL_select_selP w) j),
    selKL_select_aux_stream _ w hinf, ?_⟩
  intro k
  dsimp only
  have h0 : Nat.nth (selKL_select_selP w)
      (selKL_chunkStart
        selKL_blockLen k) =
      selKL_blockStart k := by
    have := selKL_select_aux_nth_of w k 0 0
      ((selKL_select_aux_selP_iff w k 0
          (Nat.zero_le _)).2 (Or.inl rfl)) (by simp)
    simpa using this
  have hwk := hw k
  dsimp only at hwk
  obtain ⟨hL, hR⟩ := hwk
  by_cases hk : w (selKL_blockStart k) = true
  · have hmap : (List.range (selKL_blockLen
      k)).map
        (fun t => w (Nat.nth
                    (selKL_select_selP w)
          (selKL_chunkStart
            selKL_blockLen k + 1 + t))) =
        (List.range (selKL_blockLen k)).map
          (fun t => w (selKL_blockStart k + 1 +
                      t)) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hc := selKL_select_aux_countQ w k
          (1 + j) (by omega)
      rw [ite_eq_left hk] at hc
      have := selKL_select_aux_nth_of w k
          (1 + j) (1 + j)
        ((selKL_select_aux_selP_iff w k
            (1 + j) (by omega)).2
          (Or.inr (Or.inl ⟨by omega, by omega, hk⟩))) (by omega)
      rw [show selKL_chunkStart
          selKL_blockLen k + 1 + j =
          selKL_chunkStart
          selKL_blockLen k + (1 + j) by
            omega, this]
      congr 1
      omega
    rw [h0, hmap, hk]
    exact (decide_eq_true hL).symm
  · have hk' : w (selKL_blockStart k) = false :=
      by
      simpa using hk
    have hmap : (List.range (selKL_blockLen
        k)).map
        (fun t => w (Nat.nth
                    (selKL_select_selP w)
          (selKL_chunkStart
            selKL_blockLen k + 1 + t))) =
        (List.range (selKL_blockLen k)).map
          (fun t => w (selKL_blockStart k + 1 +
            selKL_blockLen k + t)) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hc := selKL_select_aux_countQ w k
        (1 + selKL_blockLen k + j) (by omega)
      rw [ite_eq_right hk] at hc
      have := selKL_select_aux_nth_of w k
          (1 + j)
        (1 + selKL_blockLen k + j)
        ((selKL_select_aux_selP_iff w k
          (1 + selKL_blockLen k + j) (by omega)).2
          (Or.inr (Or.inr ⟨by omega, hk'⟩))) (by split_ifs at hc <;> omega)
      rw [show selKL_chunkStart
          selKL_blockLen k + 1 + j =
          selKL_chunkStart
          selKL_blockLen k + (1 + j) by
            omega, this]
      congr 1
      omega
    rw [h0, hmap, hk']
    exact (decide_eq_false (by omega)).symm

/-- Step 7 of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`: set
of positive measure contains a Martin-Löf random point. -/
private lemma selKL_ml_exists
    {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (hc : IsComputableProbSeq p)
    {G : Set CantorSeq} (hG : 0 < independentTrials p hp G) :
    ∃ w ∈ G, IsMartinLofRandom (independentTrials p hp) w := by
  by_contra h_not
  push Not at h_not
  have hμ := isComputableMeasure_independentTrials hp hc
  have h_null : IsEffectivelyNull (independentTrials p hp) G := by
    apply (isEffectivelyNull_iff_forall_not_random hμ G).mpr
    intro w hw
    exact h_not w hw
  have h_zero : independentTrials p hp G = 0 := by
    apply IsEffectivelyNull.measure_eq_zero
    exact h_null
  rw [h_zero] at hG
  revert hG
  norm_num

private def selKL_rule_kstep (m : ℕ → ℕ)
    (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if s.2.1 < m s.1 then (s.1, s.2.1 + 1, s.2.2) else (s.1 + 1, 0, s.2.2 + m s.1 + 1)

private def selKL_rule_kstate (m : ℕ → ℕ)
    (t : ℕ) : ℕ × ℕ × ℕ :=
  Nat.rec (0, 0, 0)
      (fun _ s => selKL_rule_kstep m s) t

private def selKL_rule_kpos (m : ℕ → ℕ)
    (t : ℕ) : ℕ :=
  if (selKL_rule_kstate m t).2.1 <
      m (selKL_rule_kstate m t).1 then
    (selKL_rule_kstate m t).2.2 +
        (selKL_rule_kstate m t).2.1 + 1
  else (selKL_rule_kstate m t).2.2

private def selKL_rule_ksel (m : ℕ → ℕ)
    (b : Bool) (x : BitString) : Bool :=
  decide ((selKL_rule_kstate m
      x.length).2.1 = m (selKL_rule_kstate
      m x.length).1) &&
    (decide (m (selKL_rule_kstate m
        x.length).1 < 2 *
        (x.drop (selKL_rule_kstate m
        x.length).2.2).count true) == b)

private lemma selKL_rule_kstate_zero
    (m : ℕ → ℕ) :
    selKL_rule_kstate m 0 = (0, 0, 0) :=
        rfl

private lemma selKL_rule_kstate_succ
    (m : ℕ → ℕ) (t : ℕ) :
    selKL_rule_kstate m (t + 1) =
      selKL_rule_kstep m (selKL_rule_kstate m t) := rfl

private lemma selKL_rule_chunkStart_zero
    (m : ℕ → ℕ) :
    selKL_chunkStart m 0 = 0 := by
  simp [selKL_chunkStart]

private lemma selKL_rule_chunkStart_succ
    (m : ℕ → ℕ) (k : ℕ) :
    selKL_chunkStart m (k + 1) =
      selKL_chunkStart m k + m k + 1 := by
  simp [selKL_chunkStart, List.range_succ,
      List.foldl_append]

private lemma selKL_rule_chunkStart_mono
    (m : ℕ → ℕ) :
    Monotone (selKL_chunkStart m) :=
  monotone_nat_of_le_succ fun k => by
    rw [selKL_rule_chunkStart_succ]; omega

private lemma selKL_rule_le_chunkStart
    (m : ℕ → ℕ) (k : ℕ) :
    k ≤ selKL_chunkStart m k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [selKL_rule_chunkStart_succ]; omega

private lemma selKL_rule_kstate_run
    (m : ℕ → ℕ) (t0 c k : ℕ)
    (h : selKL_rule_kstate m t0 =
        (k, 0, c)) :
    ∀ i, i ≤ m k → selKL_rule_kstate m
        (t0 + i) = (k, i, c) := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
    intro hi
    rw [← Nat.add_assoc,
        selKL_rule_kstate_succ, ih (by
          omega),
      selKL_rule_kstep, ite_eq_left (by
        simpa using hi)]

private lemma selKL_rule_kstate_chunkStart
    (m : ℕ → ℕ) (k : ℕ) :
    selKL_rule_kstate m (selKL_chunkStart m k) =
      (k, 0, selKL_chunkStart m k) := by
  induction k with
  | zero =>
    simp [selKL_rule_chunkStart_zero,
      selKL_rule_kstate_zero]
  | succ k ih =>
    have h := selKL_rule_kstate_run m _ _ _
        ih (m k) le_rfl
    rw [selKL_rule_chunkStart_succ,
      selKL_rule_kstate_succ, h,
      selKL_rule_kstep, ite_eq_right (lt_irrefl
          _)]

private lemma selKL_rule_kstate_chunkStart_add
    (m : ℕ → ℕ) (k i : ℕ) (hi : i ≤ m k) :
    selKL_rule_kstate m (selKL_chunkStart m k + i) =
      (k, i, selKL_chunkStart m k) :=
  selKL_rule_kstate_run m _ _ _
    (selKL_rule_kstate_chunkStart m k) i hi

private lemma selKL_rule_exists_chunk
    (m : ℕ → ℕ) (t : ℕ) :
    ∃ k j, j ≤ m k ∧ t = selKL_chunkStart m k +
        j := by
  induction t with
  | zero =>
    exact ⟨0, 0, by omega,
        by simp [selKL_rule_chunkStart_zero]⟩
  | succ t ih =>
    obtain ⟨k, j, hj, rfl⟩ := ih
    by_cases h : j < m k
    · exact ⟨k, j + 1, by omega, by omega⟩
    · refine ⟨k + 1, 0, by omega, ?_⟩
      rw [selKL_rule_chunkStart_succ]; omega

private lemma selKL_rule_kpos_chunkStart_add
    (m : ℕ → ℕ) (k i : ℕ) (hi : i ≤ m k) :
    selKL_rule_kpos m (selKL_chunkStart m k + i) =
      if i < m k then selKL_chunkStart m k + i + 1
      else selKL_chunkStart m k := by
  rw [selKL_rule_kpos,
    selKL_rule_kstate_chunkStart_add m k i
        hi]

private lemma selKL_rule_kpos_inj
    (m : ℕ → ℕ) {s t : ℕ}
    (h : selKL_rule_kpos m s =
        selKL_rule_kpos m t) :
    s = t := by
  obtain ⟨k, j, hj, rfl⟩ :=
      selKL_rule_exists_chunk m s
  obtain ⟨k', j', hj', rfl⟩ :=
      selKL_rule_exists_chunk m t
  rw [selKL_rule_kpos_chunkStart_add m k j
      hj,
    selKL_rule_kpos_chunkStart_add m k' j'
        hj'] at h
  have hk1 := selKL_rule_chunkStart_succ m
      k
  have hk1' := selKL_rule_chunkStart_succ m
      k'
  have hkk : k = k' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := selKL_rule_chunkStart_mono m
        (show k + 1 ≤ k' by omega)
      split_ifs at h <;> omega
    · have := selKL_rule_chunkStart_mono m
        (show k' + 1 ≤ k by omega)
      split_ifs at h <;> omega
  subst hkk
  split_ifs at h <;> omega

private def selKL_rule_kRule (m : ℕ → ℕ)
    (b : Bool) : KLRule where
  next x := Part.some (selKL_rule_kpos m
      x.length)
  sel x := Part.some (selKL_rule_ksel m b
      x)
  noRepeat := by
    intro x y hxy hne a ha a' ha' haa
    rw [Part.mem_some_iff] at ha ha'
    exact hne (hxy.eq_of_length
      (selKL_rule_kpos_inj m (ha.symm.trans
          (haa.trans ha'))))

open Classical in
private lemma selKL_rule_kRule_revealed
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq) (t : ℕ) :
    (selKL_rule_kRule m b).revealed u t =
      (List.range t).map (fun s =>
        u (selKL_rule_kpos m s)) := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    have hlen : ((selKL_rule_kRule m
        b).revealed u t).length = t := by
      rw [ih]; simp
    have hstep : ∀ x : BitString, (if h :
        ((selKL_rule_kRule m b).next x).Dom
        then
        x ++ [u (((selKL_rule_kRule m
            b).next x).get h)] else x) =
          x ++ [u (selKL_rule_kpos m
              x.length)] :=
      fun x => dite_eq_left trivial
    rw [KLRule.revealed]
    rw [hstep, hlen, ih, List.range_succ, List.map_append]
    rfl

private lemma selKL_rule_kRule_revealed_succ
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq) (t : ℕ) :
    (selKL_rule_kRule m b).revealed u
        (t + 1) =
      (selKL_rule_kRule m b).revealed u t
          ++
        [u (selKL_rule_kpos m t)] := by
  rw [selKL_rule_kRule_revealed,
    selKL_rule_kRule_revealed, List.range_succ, List.map_append]
  rfl

private lemma selKL_rule_mem_partialRuleSet_kRule
    (m : ℕ → ℕ) (b : Bool) (x : BitString) :
    x ∈ partialRuleSet (selKL_rule_kRule m
        b).sel ↔
      selKL_rule_ksel m b x = true := by
  constructor
  · rintro ⟨_, h⟩
    exact (Part.mem_some_iff.mp h).symm
  · intro h
    exact ⟨fun y _ => Part.some_dom _, Part.mem_some_iff.mpr h.symm⟩

private lemma selKL_rule_kRule_outputChain_succ
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq) (t : ℕ) :
    (selKL_rule_kRule m b).outputChain u
        (t + 1) =
      (selKL_rule_kRule m b).outputChain u
          t ++
        (if selKL_rule_ksel m b
            ((selKL_rule_kRule m b).revealed u t)
                = true
          then [u (selKL_rule_kpos m t)]
                 else []) := by
  unfold KLRule.outputChain
  rw [selKL_rule_kRule_revealed_succ, selectedBits_append_singleton]
  simp only [selKL_rule_mem_partialRuleSet_kRule]

private lemma selKL_rule_ksel_revealed_key
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq)
    (hKP : selKL_KeyPredictable m u) (k : ℕ) :
    selKL_rule_ksel m b
        ((selKL_rule_kRule m b).revealed u
          (selKL_chunkStart m k + m k)) =
      (u (selKL_chunkStart m k) == b) := by
  rw [selKL_rule_kRule_revealed]
  have hlen : ((List.range (selKL_chunkStart m k +
      m k)).map
      (fun s => u (selKL_rule_kpos m
                  s))).length =
      selKL_chunkStart m k + m k := by simp
  have hdrop : ((List.range (selKL_chunkStart m k
      + m k)).map
      (fun s => u (selKL_rule_kpos m
                  s))).drop
      (selKL_chunkStart m k) =
      (List.range (m k)).map
          (fun t => u (selKL_chunkStart m k + 1 +
                      t)) := by
    rw [List.range_add, List.map_append, List.drop_left' (by simp), List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : i < m k := List.mem_range.mp hi
    simp only [Function.comp,
      selKL_rule_kpos_chunkStart_add m k i
          hi'.le, ite_eq_left hi']
    congr 1
    omega
  unfold selKL_rule_ksel
  rw [hlen, selKL_rule_kstate_chunkStart_add m k
      (m k) le_rfl]
  dsimp only
  rw [hdrop, ← hKP k]
  simp

private lemma selKL_rule_ksel_revealed_nonkey
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq)
    (k j : ℕ) (hj : j < m k) :
    selKL_rule_ksel m b
        ((selKL_rule_kRule m b).revealed u
          (selKL_chunkStart m k + j)) = false :=
              by
  rw [selKL_rule_kRule_revealed]
  have hlen : ((List.range (selKL_chunkStart m k +
      j)).map
      (fun s => u (selKL_rule_kpos m
                  s))).length =
      selKL_chunkStart m k + j := by simp
  unfold selKL_rule_ksel
  rw [hlen, selKL_rule_kstate_chunkStart_add m k j
      hj.le]
  simp [hj.ne]

private lemma selKL_rule_ksel_eq_true_iff
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq)
    (hKP : selKL_KeyPredictable m u) (t : ℕ) :
    selKL_rule_ksel m b
        ((selKL_rule_kRule m b).revealed u
            t) = true ↔
      ∃ k, t = selKL_chunkStart m k + m k ∧
        u (selKL_chunkStart m k) = b := by
  constructor
  · intro h
    obtain ⟨k, j, hj, rfl⟩ :=
        selKL_rule_exists_chunk m t
    rcases hj.lt_or_eq with hlt | heq
    · rw [selKL_rule_ksel_revealed_nonkey m
        b u k j hlt] at h
      exact absurd h (by simp)
    · subst heq
      rw [selKL_rule_ksel_revealed_key m b
          u hKP] at h
      exact ⟨k, rfl, by simpa using h⟩
  · rintro ⟨k, rfl, hu⟩
    rw [selKL_rule_ksel_revealed_key m b u
        hKP, hu]
    simp

private lemma selKL_rule_kRule_outputChain_replicate (m : ℕ → ℕ) (b : Bool) (u : CantorSeq)
    (hKP : selKL_KeyPredictable m u) (t : ℕ) :
    ∃ n, (selKL_rule_kRule m b).outputChain
        u t = List.replicate n b := by
  induction t with
  | zero => exact ⟨0, by simp [KLRule.outputChain, KLRule.revealed, selectedBits, selectedAux]⟩
  | succ t ih =>
    obtain ⟨n, hn⟩ := ih
    rw [selKL_rule_kRule_outputChain_succ]
    by_cases hs : selKL_rule_ksel m b
        ((selKL_rule_kRule m b).revealed u
            t) = true
    · obtain ⟨k, rfl, hu⟩ :=
        (selKL_rule_ksel_eq_true_iff m b u
        hKP t).mp hs
      rw [selKL_rule_kpos_chunkStart_add m
          k (m k) le_rfl,
        ite_eq_right (lt_irrefl _), ite_eq_left hs, hu, hn]
      exact ⟨n + 1, by rw [List.replicate_succ']⟩
    · rw [ite_eq_right hs, hn]
      exact ⟨n, by simp⟩

private lemma selKL_rule_kRule_outputChain_length_unbounded (m : ℕ → ℕ) (b : Bool) (u : CantorSeq)
    (hKP : selKL_KeyPredictable m u)
    (hfreq : ∃ᶠ k in Filter.atTop,
        u (selKL_chunkStart m k) = b) (N : ℕ) :
    ∃ t, N ≤ ((selKL_rule_kRule m
        b).outputChain u t).length := by
  induction N with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨k, hkt, hk⟩ := Filter.frequently_atTop.mp hfreq t
    have hle : t ≤ selKL_chunkStart m k + m k :=
        by
      have := selKL_rule_le_chunkStart m k
      omega
    have hsel : selKL_rule_ksel m b
        ((selKL_rule_kRule m b).revealed u
          (selKL_chunkStart m k + m k)) = true :=
      (selKL_rule_ksel_eq_true_iff m b u
          hKP _).mpr ⟨k, rfl, hk⟩
    refine ⟨selKL_chunkStart m k + m k + 1, ?_⟩
    have hmono := (chain_prefix_of_le
      (KLRule.outputChain_prefix (selKL_rule_kRule m b) u) hle).length_le
    rw [selKL_rule_kRule_outputChain_succ, ite_eq_left hsel]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma selKL_rule_kRule_output
    (m : ℕ → ℕ) (b : Bool) (u : CantorSeq)
    (hKP : selKL_KeyPredictable m u)
    (hfreq : ∃ᶠ k in Filter.atTop,
        u (selKL_chunkStart m k) = b) :
    (selKL_rule_kRule m b).output u =
        .infinite (fun _ => b) := by
  have hunb : ¬ ∃ M, ∀ x ∈ chainPrefixSet
      ((selKL_rule_kRule m b).outputChain
          u), x.length ≤ M := by
    rintro ⟨M, hM⟩
    obtain ⟨t, ht⟩ := selKL_rule_kRule_outputChain_length_unbounded
      m b u hKP hfreq (M + 1)
    have := hM _ ⟨t, List.prefix_refl _⟩
    omega
  unfold KLRule.output streamOfChain BitStream.ofPrefixSet
  rw [dite_eq_right hunb]
  congr 1
  funext i
  obtain ⟨⟨t, hpre⟩, hi⟩ := Classical.choose_spec (exists_mem_length_gt hunb i)
  obtain ⟨n, hn⟩ :=
      selKL_rule_kRule_outputChain_replicate m b u
      hKP t
  rw [hn] at hpre
  exact List.eq_of_mem_replicate (hpre.sublist.subset (List.get_mem _ _))

private lemma selKL_rule_kstep_computable
    (m : ℕ → ℕ) (hm : Computable m) :
    Computable (selKL_rule_kstep m) := by
  have h1 : Computable (fun s : ℕ × ℕ × ℕ => s.1) := Computable.fst
  have h2 : Computable (fun s : ℕ × ℕ × ℕ => s.2.1) := Computable.fst.comp Computable.snd
  have h3 : Computable (fun s : ℕ × ℕ × ℕ => s.2.2) := Computable.snd.comp Computable.snd
  have hms : Computable (fun s : ℕ × ℕ × ℕ => m s.1) := hm.comp h1
  have hc : Computable (fun s : ℕ × ℕ × ℕ => decide (s.2.1 < m s.1)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp h2 hms
  have hf : Computable (fun s : ℕ × ℕ × ℕ => ((s.1, s.2.1 + 1, s.2.2) : ℕ × ℕ × ℕ)) :=
    h1.pair ((Computable.succ.comp h2).pair h3)
  have hg : Computable (fun s : ℕ × ℕ × ℕ => ((s.1 + 1, 0, s.2.2 + m s.1 + 1) : ℕ × ℕ × ℕ)) :=
    (Computable.succ.comp h1).pair ((Computable.const 0).pair
      (Computable.succ.comp (Primrec.nat_add.to_comp.comp h3 hms)))
  refine (Computable.cond hc hf hg).of_eq fun s => ?_
  by_cases h : s.2.1 < m s.1 <;>
      simp [selKL_rule_kstep, h]

private lemma selKL_rule_kstate_computable
    (m : ℕ → ℕ) (hm : Computable m) :
    Computable (selKL_rule_kstate m) :=
  Computable.nat_rec (f := id) (g := fun _ => ((0, 0, 0) : ℕ × ℕ × ℕ))
    (h := fun _ p => selKL_rule_kstep m
                       p.2) Computable.id (Computable.const _)
    ((selKL_rule_kstep_computable m hm).comp
      (Computable.snd.comp Computable.snd))

private lemma selKL_rule_kpos_computable
    (m : ℕ → ℕ) (hm : Computable m) :
    Computable (selKL_rule_kpos m) := by
  have hs := selKL_rule_kstate_computable m
      hm
  have h1 : Computable
      (fun t : ℕ => (selKL_rule_kstate m
                      t).1) :=
    Computable.fst.comp hs
  have h2 : Computable
      (fun t : ℕ => (selKL_rule_kstate m
                      t).2.1) :=
    Computable.fst.comp (Computable.snd.comp hs)
  have h3 : Computable
      (fun t : ℕ => (selKL_rule_kstate m
                      t).2.2) :=
    Computable.snd.comp (Computable.snd.comp hs)
  have hms : Computable
      (fun t : ℕ => m (selKL_rule_kstate m
                      t).1) :=
    hm.comp h1
  have hc : Computable (fun t : ℕ => decide ((selKL_rule_kstate m t).2.1 <
      m (selKL_rule_kstate m t).1)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp h2 hms
  have hf : Computable
      (fun t : ℕ => (selKL_rule_kstate m
                      t).2.2 +
      (selKL_rule_kstate m t).2.1 + 1) :=
    Computable.succ.comp (Primrec.nat_add.to_comp.comp h3 h2)
  refine (Computable.cond hc hf h3).of_eq fun t => ?_
  by_cases h : (selKL_rule_kstate m t).2.1
      <
      m (selKL_rule_kstate m t).1 <;>
    simp [selKL_rule_kpos, h]

private lemma selKL_rule_count_true_drop_primrec :
    Primrec (fun p : List Bool × ℕ => (p.1.drop p.2).count true) := by
  have hf : Primrec (fun p : List Bool × ℕ => p.1.drop p.2) :=
    Primrec.list_drop.comp Primrec.snd Primrec.fst
  have hh : Primrec₂ (fun (_ : List Bool × ℕ) (q : Bool × ℕ) => cond q.1 (q.2 + 1) q.2) :=
    Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  refine (Primrec.list_foldr hf (Primrec.const 0) hh).of_eq fun p => ?_
  have : ∀ l : List Bool, l.foldr (fun a n => cond a (n + 1) n) 0 = l.count true := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases a <;> simp_all
  exact this _

private lemma selKL_rule_ksel_computable
    (m : ℕ → ℕ) (hm : Computable m) (b : Bool) :
    Computable (selKL_rule_ksel m b) := by
  have hS : Computable (fun x : BitString =>
    selKL_rule_kstate m x.length) :=
    (selKL_rule_kstate_computable m hm).comp
        Computable.list_length
  have h1 : Computable (fun x : BitString =>
    (selKL_rule_kstate m x.length).1) :=
    Computable.fst.comp hS
  have h2 : Computable (fun x : BitString =>
    (selKL_rule_kstate m x.length).2.1) :=
    Computable.fst.comp (Computable.snd.comp hS)
  have h3 : Computable (fun x : BitString =>
    (selKL_rule_kstate m x.length).2.2) :=
    Computable.snd.comp (Computable.snd.comp hS)
  have hms : Computable (fun x : BitString =>
    m (selKL_rule_kstate m x.length).1) :=
    hm.comp h1
  have hA : Computable (fun x : BitString =>
      decide ((selKL_rule_kstate m
          x.length).2.1 =
        m (selKL_rule_kstate m
            x.length).1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp h2 hms
  have hcnt : Computable (fun x : BitString =>
      (x.drop (selKL_rule_kstate m
          x.length).2.2).count true) :=
    selKL_rule_count_true_drop_primrec.to_comp.comp (Computable.id.pair h3)
  have hB : Computable (fun x : BitString =>
      decide (m (selKL_rule_kstate m
          x.length).1 <
        2 * (x.drop (selKL_rule_kstate m
            x.length).2.2).count true)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hms (Primrec.nat_mul.to_comp.comp
        (Computable.const 2) hcnt)
  have hC := Primrec.beq.to_comp.comp hB (Computable.const b)
  exact Primrec.and.to_comp.comp hA hC

/-- Step 8a of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`:
there exists a rule producing the target bit. -/
private lemma selKL_rule (m : ℕ → ℕ)
    (hm : Computable m) (b : Bool) :
    ∃ ρ : KLRule, ρ.IsAdmissible ∧ ∀ u,
        selKL_KeyPredictable m u →
        (∃ᶠ k in Filter.atTop, u (selKL_chunkStart
        m k) = b) → ∃ v, ρ.output u = .infinite v ∧ ∀ n, v n = b :=
  ⟨selKL_rule_kRule m b,
    ⟨((selKL_rule_kpos_computable m hm).comp
        Computable.list_length).partrec,
      (selKL_rule_ksel_computable m hm
          b).partrec⟩,
    fun u hKP hf => ⟨fun _ => b,
      selKL_rule_kRule_output m b u hKP hf,
          fun _ => rfl⟩⟩

/-- Step 8b of the proof of `exists_isMisesKLRandom_selectStream_not_isMisesKLRandom`: key
predictable sequence is not MKL random. -/
private lemma selKL_not_mkl (m : ℕ → ℕ)
    (hm : Computable m) {u : CantorSeq}
    (hu : selKL_KeyPredictable m u) :
    ¬ IsMisesKLRandom u := by
  intro hrand
  have hb : ∃ b : Bool, ∃ᶠ k in Filter.atTop,
      u (selKL_chunkStart m k) = b := by
    by_cases h : ∃ᶠ k in Filter.atTop,
        u (selKL_chunkStart m k) = true
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      rw [Filter.not_frequently] at h
      apply Filter.Eventually.frequently
      filter_upwards [h] with k hk
      simpa using hk
  obtain ⟨b, hbf⟩ := hb
  obtain ⟨ρ, hρ, hρu⟩ := selKL_rule m hm b
  obtain ⟨v, hv, hvb⟩ := hρu u hu hbf
  have hfin := hrand ρ hρ
  rw [hv] at hfin
  have hlim : HasLimitFreq (1 / 2) v := hfin
  have hconst : ∀ n, 1 ≤ n → (freqOne v n : ℝ) = bitVal b := by
    intro n hn
    rw [freqOne_eq]
    have : ∀ i ∈ Finset.range n, bitVal (v i) = bitVal b := fun i _ => by rw [hvb i]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hlim2 : Filter.Tendsto (fun n => (freqOne v n : ℝ)) Filter.atTop (nhds (bitVal b)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hconst n hn).symm
  have heq : (1 / 2 : ℝ) = bitVal b := tendsto_nhds_unique hlim hlim2
  cases b <;> simp [bitVal] at heq

/-- **SUV Theorem 203(c), p. 307 (Merkle).**  There is a Mises-Kolmogorov-Loveland random sequence
with frequency `1/2` such that some Church-admissible rule, hence some Kolmogorov-Loveland
admissible rule, selects from it a sequence that is not Mises-Kolmogorov-Loveland random. -/
theorem exists_isMisesKLRandom_selectStream_not_isMisesKLRandom :
    ∃ w, IsMisesKLRandom w ∧ ∃ R : Set BitString, IsDecidableSet R ∧ ∃ u,
      selectStream R w = .infinite u ∧ ¬ IsMisesKLRandom u := by
  have step3_conv := selKL_conv
  have hconv : ConvergesComputably selKL_pSeq
      (1 / 2) := by exact_mod_cast step3_conv
  obtain ⟨w, hwG, hw⟩ := selKL_ml_exists selKL_pSeq_le_one hconv.computable selKL_measure_pos
  have hMKL : IsMisesKLRandom w := isMisesKLRandomAt_of_isMartinLofRandom
      selKL_pSeq_le_one (by norm_num)
      (by norm_num) hconv hw
  obtain ⟨u, hu, hKP⟩ := selKL_select w hwG
  exact ⟨w, hMKL, selKL_selR, selKL_selR_dec, u, hu,
    selKL_not_mkl selKL_blockLen selKL_blockLen_comp hKP⟩

private def permNotMC_blockLen (k : ℕ) :
    ℕ := 2^(k+5)*(k+3)^2

private def permNotMC_bigStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => permNotMC_bigStart k +
             (2 * permNotMC_blockLen k +
                 1)

private def permNotMC_bigIdx (i : ℕ) :
    ℕ :=
  Nat.findGreatest (fun k =>
    permNotMC_bigStart k ≤ i) i

private noncomputable def permNotMC_pSeq
    (i : ℕ) : NNReal :=
  let k := permNotMC_bigIdx i
  let offset := i - permNotMC_bigStart k
  if offset = 0 then (1 / 2 : NNReal)
  else if offset ≤ permNotMC_blockLen k
         then Real.toNNReal (1 / 2 + 1 / (k + 3 : ℝ))
  else Real.toNNReal (1 / 2 - 1 / (k + 3 : ℝ))

private def permNotMC_selR :
    Set BitString :=
  { x | let i := x.length
        let k := permNotMC_bigIdx i
        let offset :=
            i - permNotMC_bigStart k
        offset = 0 ∨
        (offset ≤ permNotMC_blockLen k ∧
            offset > 0 ∧
            x.getD (permNotMC_bigStart k)
            false = false) ∨
        (offset > permNotMC_blockLen k ∧
            x.getD (permNotMC_bigStart k)
            false = true) }

private def permNotMC_goodSet :
    Set CantorSeq :=
  { w | ∀ k, permNotMC_blockLen k < 2 * ((List.range (permNotMC_blockLen k)).map
        (fun j => w (permNotMC_bigStart k + 1 + j))).count true ∧
      2 * ((List.range (permNotMC_blockLen k)).map
        (fun j => w (permNotMC_bigStart k + 1 + permNotMC_blockLen k + j))).count true <
          permNotMC_blockLen k }

private def permNotMC_blockStart
    (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => permNotMC_blockStart N k +
               1 + N k

private def permNotMC_predictable
    (N : ℕ → ℕ) (w : CantorSeq) : Prop :=
  ∀ k, let s := permNotMC_blockStart N k;
       let ones := ((List.range (N k)).map (fun j => w (s + 1 + j))).count true;
       w s = false ↔ ones * 2 > N k

private lemma permNotMC_perm_aux_comp_blockStart
    {N : ℕ → ℕ} (hN : Computable N) :
    Computable (permNotMC_blockStart N) :=
        by
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (0 : ℕ))
    (h := fun (_ : ℕ) (yi : ℕ × ℕ) => yi.2 + 1 + N yi.1) Computable.id (Computable.const 0)
    ((Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp (Computable.snd.comp
        Computable.snd)
      (Computable.const 1)) (hN.comp (Computable.fst.comp Computable.snd))).to₂)
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih =>
    change _ + 1 + N k = _
    rw [ih]; rfl

private lemma permNotMC_perm_aux_comp_findGreatest
    {s : ℕ → ℕ} (hs : Computable s) :
    Computable (fun n : ℕ => Nat.findGreatest (fun k => s k ≤ n) n) := by
  have hle : Computable (fun p : ℕ × (ℕ × ℕ) => decide (s (p.2.1 + 1) ≤ p.1)) :=
    (Primrec.nat_le.decide.to_comp : Computable₂ (fun a b : ℕ => decide (a ≤ b))).comp
      (hs.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))) Computable.fst
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (0 : ℕ))
    (h := fun (n : ℕ) (yi : ℕ × ℕ) => if s (yi.1 + 1) ≤ n then yi.1 + 1 else yi.2) Computable.id
        (Computable.const 0)
    (((Computable.cond hle (Computable.succ.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).of_eq fun p => by
        by_cases hp : s (p.2.1 + 1) ≤ p.1 <;> simp [hp] :
      Computable (fun p : ℕ × (ℕ × ℕ) => if s (p.2.1 + 1) ≤ p.1 then p.2.1 + 1 else p.2.2)).to₂)
  refine h.of_eq fun n => ?_
  have : ∀ m, Nat.rec (motive := fun _ => ℕ) 0
      (fun y IH => if s (y + 1) ≤ n then y + 1 else IH) m = Nat.findGreatest (fun k => s k ≤ n) m :=
          by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.findGreatest_succ, ← ih]
  exact this n

/-- Step 1 of the proof of
`permNotMC_not_MC`:
for a computable block-length sequence `N` there is a computable bijection `σ` that rotates every
block `[s_k, s_k + N k]` (`s_k = blockStart N k`) one step to the left:
`σ (s_k + j) = s_k + j + 1` for `j < N k` and `σ (s_k + N k) = s_k`. -/
private lemma permNotMC_perm
    {N : ℕ → ℕ} (hN : Computable N) :
    ∃ σ : ℕ → ℕ, Computable σ ∧ Function.Bijective σ ∧
      ∀ k, (∀ j < N k,
          σ (permNotMC_blockStart N k + j)
          =
          permNotMC_blockStart N k + j +
              1) ∧
        σ (permNotMC_blockStart N k + N k)
            =
          permNotMC_blockStart N k := by
  set s := permNotMC_blockStart N with
      hsdef
  have hs : Computable s :=
    permNotMC_perm_aux_comp_blockStart hN
  have hsucc : ∀ k, s (k + 1) = s k + 1 + N k := fun k => rfl
  have hle : ∀ k, k ≤ s k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => rw [hsucc]; omega
  have hmono : Monotone s := monotone_nat_of_le_succ fun k => by rw [hsucc]; omega
  set b : ℕ → ℕ := fun n => Nat.findGreatest (fun k => s k ≤ n) n with hbdef
  have hb : Computable b :=
    permNotMC_perm_aux_comp_findGreatest hs
  have hbeq : ∀ k j, j ≤ N k → b (s k + j) = k := by
    intro k j hj
    rw [hbdef]
    change Nat.findGreatest (fun m => s m ≤ s k + j) (s k + j) = k
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by have := hle k; omega, fun _ => by omega, ?_⟩
    intro m hm hmn hP
    have h1 : s (k + 1) ≤ s m := hmono hm
    rw [hsucc] at h1
    omega
  have hblock : ∀ n, s (b n) ≤ n ∧ n < s (b n) + N (b n) + 1 := by
    intro n
    have hP : s (b n) ≤ n := Nat.findGreatest_spec (P := fun k => s k ≤ n) (Nat.zero_le n)
        (by simp [hsdef,
      permNotMC_blockStart])
    refine ⟨hP, ?_⟩
    by_contra hcon
    have h1 : s (b n + 1) ≤ n := by rw [hsucc]; omega
    have h2 : b n + 1 ≤ n := le_trans (hle _) h1
    exact Nat.findGreatest_is_greatest (P := fun k => s k ≤ n) (Nat.lt_succ_self _) h2 h1
  classical
  let σ : ℕ → ℕ := fun n => if n = s (b n) + N (b n) then s (b n) else n + 1
  let τ : ℕ → ℕ := fun n => if n = s (b n) then n + N (b n) else n - 1
  have hσ : ∀ k j, j ≤ N k → σ (s k + j) = if j = N k then s k else s k + j + 1 := by
    intro k j hj
    change (if s k + j = s (b (s k + j)) + N (b (s k + j)) then s (b (s k + j)) else s k + j + 1) =
        _
    rw [hbeq k j hj]
    by_cases h : j = N k
    · simp [h]
    · simp [h]
  have hτ : ∀ k j, j ≤ N k → τ (s k + j) = if j = 0 then s k + N k else s k + j - 1 := by
    intro k j hj
    change (if s k + j = s (b (s k + j)) then s k + j + N (b (s k + j)) else s k + j - 1) = _
    rw [hbeq k j hj]
    by_cases h : j = 0
    · simp [h]
    · have : s k + j ≠ s k := by omega
      simp [h]
  have hdecomp : ∀ n, ∃ k j, j ≤ N k ∧ n = s k + j := fun n =>
    ⟨b n, n - s (b n), by have := hblock n; omega, by have := hblock n; omega⟩
  have hbij : Function.Bijective σ := by
    refine Function.bijective_iff_has_inverse.2 ⟨τ, ?_, ?_⟩
    · intro n
      obtain ⟨k, j, hj, rfl⟩ := hdecomp n
      rw [hσ k j hj]
      by_cases h : j = N k
      · rw [ite_eq_left h, show s k = s k + 0 by rfl, hτ k 0 (Nat.zero_le _)]
        simp [h]
      · rw [ite_eq_right h, show s k + j + 1 = s k + (j + 1) by omega, hτ k (j + 1) (by omega)]
        simp
    · intro n
      obtain ⟨k, j, hj, rfl⟩ := hdecomp n
      rw [hτ k j hj]
      by_cases h : j = 0
      · rw [ite_eq_left h, show s k + N k = s k + N k from rfl, hσ k (N k) le_rfl]
        simp [h]
      · rw [ite_eq_right h, show s k + j - 1 = s k + (j - 1) by omega, hσ k (j - 1) (by omega),
          ite_eq_right (by omega)]
        omega
  refine ⟨σ, ?_, hbij, fun k => ⟨fun j hj => ?_, ?_⟩⟩
  · have hc : Computable (fun n : ℕ => decide (n = s (b n) + N (b n))) :=
      (Primrec.eq.decide.to_comp : Computable₂ (fun a c : ℕ => decide (a = c))).comp Computable.id
        (Primrec.nat_add.to_comp.comp (hs.comp hb) (hN.comp hb))
    exact (Computable.cond hc (hs.comp hb) Computable.succ).of_eq fun n => by
      by_cases hp : n = s (b n) + N (b n)
      · change _ = if n = s (b n) + N (b n) then s (b n) else n + 1
        rw [ite_eq_left hp, decide_eq_true hp]; rfl
      · change _ = if n = s (b n) + N (b n) then s (b n) else n + 1
        rw [ite_eq_right hp, decide_eq_false hp]; rfl
  · rw [hσ k j hj.le, ite_eq_right (by omega)]
  · have := hσ k (N k) le_rfl
    simpa using this

/-- The rule selecting the key of block `k` (read after the `N k` non-key terms of the block)
when the non-key terms hold a strict majority of ones. -/
private def permNotMC_not_MC_ruleA
    (N : ℕ → ℕ) : Set BitString :=
  {x | ∃ k, x.length =
      permNotMC_blockStart N k + N k ∧
    N k < 2 * ((x.drop
        (permNotMC_blockStart N k)).count
        true)}

/-- The rule selecting the key of block `k` (read after the `N k` non-key terms of the block)
when the non-key terms do not hold a strict majority of ones. -/
private def permNotMC_not_MC_ruleB
    (N : ℕ → ℕ) : Set BitString :=
  {x | ∃ k, x.length =
      permNotMC_blockStart N k + N k ∧
    2 * ((x.drop (permNotMC_blockStart N
        k)).count true) ≤ N k}

/-- Step 2 of the proof of
`permNotMC_not_MC`:
for computable `N` the two rules `ruleA`, `ruleB` are decidable sets of strings. -/
private lemma permNotMC_dec
    {N : ℕ → ℕ} (hN : Computable N) :
    IsDecidableSet (permNotMC_not_MC_ruleA N) ∧
    IsDecidableSet (permNotMC_not_MC_ruleB N) := by
  set s := permNotMC_blockStart N
  have hs : Computable s :=
    permNotMC_perm_aux_comp_blockStart hN
  have hle : ∀ k, k ≤ s k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => change k + 1 ≤ s k + 1 + N k; omega
  have hcnt : Computable₂ (fun (n : ℕ) (x : BitString) => (x.drop n).count true) := by
    have h := Kolmogorov.list_countP_primrec (f := fun p : ℕ × BitString => p.2.drop p.1)
      (p := fun _ c => c == true) (Primrec.list_drop.comp Primrec.fst Primrec.snd)
      (Primrec.beq.comp Primrec.snd (Primrec.const true))
    have h2 : Computable (fun p : ℕ × BitString => (p.2.drop p.1).count true) :=
      h.to_comp.of_eq fun p => rfl
    exact h2.to₂
  -- membership is a bounded search over `k ≤ |x|`, since `k ≤ s k ≤ s k + N k`
  have key : ∀ (P : ℕ → ℕ → Prop) [DecidableRel P], Computable₂ (fun a c => decide (P a c)) →
      IsDecidableSet {x : BitString | ∃ k, x.length = s k + N k ∧ P (N k) ((x.drop (s k)).count
          true)} := by
    intro P _ hP
    let p : BitString → ℕ → Bool := fun x k =>
      decide (x.length = s k + N k) && decide (P (N k) ((x.drop (s k)).count true))
    have hp : Computable₂ p := by
      refine (Primrec.and.to_comp.comp
        ((Primrec.eq.decide.to_comp : Computable₂ (fun a c : ℕ => decide (a = c))).comp
          (Computable.list_length.comp Computable.fst)
          (Primrec.nat_add.to_comp.comp (hs.comp Computable.snd) (hN.comp Computable.snd)))
        (hP.comp (hN.comp Computable.snd) (hcnt.comp (hs.comp Computable.snd) Computable.fst))).to₂
    have hany : Computable (fun x : BitString => (List.range (x.length + 1)).any (p x)) := by
      refine (Computable.list_foldr (l := fun x : BitString => List.range (x.length + 1))
        (g := fun _ => false) (h := fun x (q : ℕ × Bool) => p x q.1 || q.2)
        (Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.list_length))
        (Computable.const false)
        (Primrec.or.to_comp.comp (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
          (Computable.snd.comp Computable.snd)).to₂).of_eq fun x => ?_
      induction List.range (x.length + 1) with
      | nil => rfl
      | cons b t ih => simp [List.any_cons, ih]
    refine ⟨_, hany, fun x => ?_⟩
    simp only [List.any_eq_true, List.mem_range, p, Bool.and_eq_true, decide_eq_true_eq,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, -, h⟩
      exact ⟨k, h⟩
    · rintro ⟨k, h⟩
      exact ⟨k, by have := hle k; omega, h⟩
  exact ⟨key (fun a c => a < 2 * c) (Primrec.nat_lt.decide.to_comp.comp Computable.fst
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.snd)).to₂,
    key (fun a c => 2 * c ≤ a) (Primrec.nat_le.decide.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.snd) Computable.fst).to₂⟩

/-- Step 3 of the proof of
`permNotMC_not_MC`
(private copy of `exists_rule_not_finiteOrFreq_step2_not_freq` of `Selection.lean`): if a rule
selects
from the first `j` terms of `w` exactly `z j` copies of `b`, with `z` unbounded, then the selected
sequence is not finite-or-balanced. -/
private lemma permNotMC_not_freq
    (R : Set BitString)
    (w : CantorSeq) (b : Bool) (z : ℕ → ℕ)
    (hsel : ∀ j, selectedBits R (cantorPrefix w j) = List.replicate (z j) b)
    (hunb : ∀ i, ∃ j, i ≤ z j) : ¬ FiniteOrFreq (1 / 2) (selectStream R w) := by
  intro hfin
  have hmem : ∀ j, List.replicate (z j) b ∈ chainPrefixSet (selectChain R w) := fun j =>
    ⟨j, by rw [selectChain, hsel j]⟩
  have key : ∀ x, BitStream.finite x ≤ selectStream R w ↔ x ∈ chainPrefixSet (selectChain R w) :=
    fun x => BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x
  rcases hs : selectStream R w with u | u
  · obtain ⟨j, hj⟩ := hunb (u.length + 1)
    have h1 : BitStream.finite (List.replicate (z j) b) ≤ selectStream R w :=
      (key _).2 (hmem j)
    rw [hs] at h1
    have h2 : List.replicate (z j) b <+: u := h1
    have h3 := h2.length_le
    rw [List.length_replicate] at h3
    omega
  · have hu : ∀ k, u k = b := by
      intro k
      obtain ⟨j, hj⟩ := hunb (k + 1)
      have h1 : BitStream.finite (List.replicate (z j) b) ≤ selectStream R w :=
        (key _).2 (hmem j)
      rw [hs] at h1
      have h2 : IsCantorPrefix (List.replicate (z j) b) u := h1
      have h3 := h2 k (by rw [List.length_replicate]; omega)
      simpa using h3
    rw [hs] at hfin
    have hlim : HasLimitFreq (1 / 2) u := hfin
    have hconst : ∀ n, (freqOne u n : ℝ) = (∑ i ∈ Finset.range n, bitVal b) / n := by
      intro n
      rw [freqOne_eq]
      simp [hu]
    cases b
    · have hlim0 : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 0) := by
        have hfun : (fun n => (freqOne u n : ℝ)) = fun _ => 0 := by
          funext n
          rw [hconst]
          simp [bitVal]
        rw [hfun]
        exact tendsto_const_nhds
      have h12 := tendsto_nhds_unique hlim hlim0
      norm_num at h12
    · have hlim1 : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ne_atTop 0] with n hn
        rw [hconst]
        simp [bitVal, hn]
      have h12 := tendsto_nhds_unique hlim hlim1
      norm_num at h12

open Classical in
/-- Step 4a of the proof of
`permNotMC_not_MC`:
if every term selected by `R` from `v` equals `b`, the selected prefix is `b` repeated as often as
`R`
selects. -/
private lemma permNotMC_sel_const
    (R : Set BitString) (v : CantorSeq) (b : Bool) (h : ∀ n, cantorPrefix v n ∈ R → v n = b) (t : ℕ)
        :
    selectedBits R (cantorPrefix v t) =
      List.replicate (((Finset.range t).filter (fun n => cantorPrefix v n ∈ R)).card) b := by
  induction t with
  | zero =>
    have h0 : cantorPrefix v 0 = [] := rfl
    simp [h0, selectedBits, selectedAux]
  | succ t ih =>
    rw [cantorPrefix_succ, selectedBits_append_singleton, ih, Finset.range_add_one,
        Finset.filter_insert]
    by_cases hz : cantorPrefix v t ∈ R
    · rw [ite_eq_left hz, ite_eq_left hz, Finset.card_insert_of_notMem (by simp), h t hz]
      simp [List.replicate_succ']
    · rw [ite_eq_right hz, ite_eq_right hz]
      simp

open Classical in
/-- Step 4b of the proof of
`permNotMC_not_MC`:
if `R` selects a term of `v` infinitely often, the number of selecting positions is unbounded. -/
private lemma permNotMC_unbounded
    (R : Set BitString) (v : CantorSeq) (hinf : ∀ M, ∃ n, M ≤ n ∧ cantorPrefix v n ∈ R) (i : ℕ) :
    ∃ j, i ≤ ((Finset.range j).filter (fun n => cantorPrefix v n ∈ R)).card := by
  induction i with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ i ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨n, hn, hnR⟩ := hinf j
    refine ⟨n + 1, ?_⟩
    have hsub : ((Finset.range j).filter (fun n => cantorPrefix v n ∈ R)).card ≤
        ((Finset.range n).filter (fun n => cantorPrefix v n ∈ R)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hn))
    rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left hnR, Finset.card_insert_of_notMem
        (by simp)]
    omega

/-- Step 4c of the proof of
`permNotMC_not_MC`:
a rule selecting only copies of `b` from `v`, infinitely often, gives a non-balanced selected
stream. -/
private lemma permNotMC_not_MC_not_freq
    (R : Set BitString) (v : CantorSeq) (b : Bool) (h : ∀ n, cantorPrefix v n ∈ R → v n = b)
    (hinf : ∀ M, ∃ n, M ≤ n ∧ cantorPrefix v n ∈ R) : ¬ FiniteOrFreq (1 / 2) (selectStream R v) :=
  permNotMC_not_freq R v b _
    (permNotMC_sel_const R v b h)
    (permNotMC_unbounded R v hinf)

/-- Step 5 of the proof of
`permNotMC_not_MC`:
the block starts satisfy `k ≤ blockStart N k`. -/
private lemma permNotMC_le_blockStart
    (N : ℕ → ℕ) (k : ℕ) :
    k ≤ permNotMC_blockStart N k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    change k + 1 ≤ permNotMC_blockStart N
        k + 1 + N k
    omega

/-- Step 6 of the proof of
`permNotMC_not_MC`:
the part of the prefix of `v` read in block `k` before the key. -/
private lemma permNotMC_drop
    (v : CantorSeq) (s n : ℕ) :
    (cantorPrefix v (s + n)).drop s = (List.range n).map (fun j => v (s + j)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1 h2
    simp [cantorPrefix, List.getElem_drop]

/-- Step 7 of the proof of
`permNotMC_not_MC`:
assembly, given the rotation `σ` and the decidability of the two rules. -/
private lemma permNotMC_main
    {N : ℕ → ℕ} {w : CantorSeq}
    (h_pred : permNotMC_predictable N w)
    (σ : ℕ → ℕ)
    (hσ : ∀ k, (∀ j < N k,
        σ (permNotMC_blockStart N k + j) =
          permNotMC_blockStart N k + j +
              1) ∧
        σ (permNotMC_blockStart N k + N k)
            =
          permNotMC_blockStart N k)
    (hdA : IsDecidableSet
        (permNotMC_not_MC_ruleA N))
    (hdB : IsDecidableSet
        (permNotMC_not_MC_ruleB N)) :
    ¬ IsMisesChurchRandom (w ∘ σ) := by
  intro hMC
  set bs := permNotMC_blockStart N with
      hbs
  have hones : ∀ k, (List.range (N k)).map (fun j => (w ∘ σ) (bs k + j)) =
      (List.range (N k)).map (fun j => w (bs k + 1 + j)) := by
    intro k
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [Function.comp, (hσ k).1 j hj']
    congr 1; omega
  have hdrop : ∀ k, (cantorPrefix (w ∘ σ) (bs k + N k)).drop (bs k) =
      (List.range (N k)).map (fun j => w (bs k + 1 + j)) := fun k => by
    rw [permNotMC_drop, hones]
  have hkey : ∀ k, (w ∘ σ) (bs k + N k) = w (bs k) := fun k => by
    simp [Function.comp, (hσ k).2]
  have hA : ∀ n, cantorPrefix (w ∘ σ) n ∈
      permNotMC_not_MC_ruleA N →
      (w ∘ σ) n = false := by
    intro n ⟨k, hlen, hc⟩
    rw [cantorPrefix_length] at hlen
    subst hlen
    rw [hdrop] at hc
    rw [hkey]
    have := h_pred k
    simp only at this
    rw [← hbs] at this
    exact this.2 (by omega)
  have hB : ∀ n, cantorPrefix (w ∘ σ) n ∈
      permNotMC_not_MC_ruleB N →
      (w ∘ σ) n = true := by
    intro n ⟨k, hlen, hc⟩
    rw [cantorPrefix_length] at hlen
    subst hlen
    rw [hdrop] at hc
    rw [hkey]
    have := h_pred k
    simp only at this
    rw [← hbs] at this
    by_contra hne
    have hf : w (bs k) = false := by simpa using hne
    have := this.1 hf
    omega
  have hle : ∀ k, k ≤ bs k :=
    permNotMC_le_blockStart N
  by_cases hinfA : ∀ M, ∃ k, M ≤ k ∧ N k < 2 *
      (((List.range (N k)).map (fun j => w (bs k + 1 + j))).count true)
  · refine permNotMC_not_MC_not_freq _
      (w ∘ σ) false hA ?_ (hMC _ hdA)
    intro M
    obtain ⟨k, hk, hc⟩ := hinfA M
    refine ⟨bs k + N k, by have := hle k; omega, k, by rw [cantorPrefix_length], ?_⟩
    rw [hdrop]
    exact hc
  · push Not at hinfA
    obtain ⟨M, hM⟩ := hinfA
    refine permNotMC_not_MC_not_freq _
        (w ∘ σ) true hB ?_ (hMC _ hdB)
    intro M'
    refine ⟨bs (max M M') + N (max M M'), by have := hle (max M M'); omega, max M M',
        by rw [cantorPrefix_length], ?_⟩
    rw [hdrop]
    exact hM _ (le_max_left _ _)

/-- Step 1 of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
If a sequence `w` has the predictable-blocks property for a computable block-length sequence `N`,
then there is a computable permutation `σ` such that `w ∘ σ` is not Mises-Church random. -/
private lemma permNotMC_not_MC
    {N : ℕ → ℕ} (hN : Computable N) {w : CantorSeq}
    (h_pred : permNotMC_predictable N w) :
    ∃ σ : ℕ → ℕ, Computable σ ∧ Function.Bijective σ ∧ ¬ IsMisesChurchRandom (w ∘ σ) := by
  obtain ⟨σ, hσc, hσb, hσ⟩ :=
    permNotMC_perm hN
  obtain ⟨hdA, hdB⟩ :=
    permNotMC_dec hN
  exact ⟨σ, hσc, hσb,
    permNotMC_main h_pred σ hσ hdA hdB⟩

/-- Step 2a of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
The probability sequence `pSeq` values are bounded by 1. -/
private lemma permNotMC_pSeq_le_one
    :
    ∀ i, permNotMC_pSeq i ≤ 1 := by
  intro i
  unfold permNotMC_pSeq
  dsimp only
  generalize permNotMC_bigIdx i = k
  have hk : (0 : ℝ) < (k + 3 : ℝ) := by positivity
  have hk' : 1 / (k + 3 : ℝ) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hk0 : 0 ≤ 1 / (k + 3 : ℝ) := by positivity
  split_ifs
  · exact (by norm_num : (1 / 2 : NNReal) ≤ 1)
  · rw [Real.toNNReal_le_iff_le_coe]
    simp only [NNReal.coe_one]
    linarith
  · rw [Real.toNNReal_le_iff_le_coe]
    simp only [NNReal.coe_one]
    linarith

/-- Step 2a of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
The block length sequence `blockLen` is computable. -/
private lemma permNotMC_computable_blockLen :
    Computable permNotMC_blockLen := by
  unfold permNotMC_blockLen
  have hpow : Primrec₂ (fun (a b : ℕ) => a ^ b) := Primrec.nat_iff.mpr Nat.Primrec.pow
  have h : Primrec (fun k : ℕ => 2^(k+5)*(k+3)^2) := by
    refine Primrec.nat_mul.comp ?_ ?_
    · exact hpow.comp (Primrec.const 2) (Primrec.succ.comp
        (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp Primrec.succ))))
    · exact hpow.comp (Primrec.succ.comp (Primrec.succ.comp Primrec.succ)) (Primrec.const 2)
  exact h.to_comp

private def permNotMC_computable_pSeq_numer (i : ℕ) : ℕ :=
  if i - permNotMC_bigStart
      (permNotMC_bigIdx i) = 0 then
    permNotMC_bigIdx i + 3
  else if i - permNotMC_bigStart (permNotMC_bigIdx i) ≤ permNotMC_blockLen (permNotMC_bigIdx i) then
    permNotMC_bigIdx i + 5
  else permNotMC_bigIdx i + 1

private lemma permNotMC_computable_pSeq_primrec_blockLen :
    Primrec permNotMC_blockLen := by
  unfold permNotMC_blockLen
  exact Primrec.nat_mul.comp
    (nat_pow_primrec₂.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp
        (Primrec.succ.comp Primrec.id))))))
    (nat_pow_primrec₂.comp (Primrec.succ.comp (Primrec.succ.comp (Primrec.succ.comp Primrec.id)))
        (Primrec.const 2))

private lemma permNotMC_computable_pSeq_primrec_bigStart :
    Primrec permNotMC_bigStart := by
  have h := Primrec.nat_rec₁ (f := fun (k : ℕ) (acc : ℕ) =>
    acc + (2 * permNotMC_blockLen k + 1))
    0
    (Primrec.nat_add.comp Primrec.snd
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (permNotMC_computable_pSeq_primrec_blockLen.comp Primrec.fst))))
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [permNotMC_bigStart]
    rw [← ih]

private lemma permNotMC_computable_pSeq_primrec_bigIdx :
    Primrec permNotMC_bigIdx := by
  have hp : PrimrecRel (fun (i k : ℕ) =>
    permNotMC_bigStart k ≤ i) :=
    Primrec.nat_le.comp (permNotMC_computable_pSeq_primrec_bigStart.comp Primrec.snd) Primrec.fst
  exact Primrec.nat_findGreatest Primrec.id hp

private lemma permNotMC_computable_pSeq_primrec_numer :
    Primrec permNotMC_computable_pSeq_numer := by
  have hI := permNotMC_computable_pSeq_primrec_bigIdx
  have hoff : Primrec (fun i : ℕ => i - permNotMC_bigStart (permNotMC_bigIdx i)) :=
    Primrec.nat_sub.comp Primrec.id (permNotMC_computable_pSeq_primrec_bigStart.comp hI)
  have hL : Primrec (fun i : ℕ => permNotMC_blockLen (permNotMC_bigIdx i)) :=
    permNotMC_computable_pSeq_primrec_blockLen.comp hI
  unfold permNotMC_computable_pSeq_numer
  refine Primrec.ite (Primrec.eq.comp hoff (Primrec.const 0)) ?_
      (Primrec.ite (Primrec.nat_le.comp hoff hL) ?_ ?_)
  · exact Primrec.nat_add.comp hI (Primrec.const 3)
  · exact Primrec.nat_add.comp hI (Primrec.const 5)
  · exact Primrec.nat_add.comp hI (Primrec.const 1)

private lemma permNotMC_computable_pSeq_eq
    (i : ℕ) :
    ((permNotMC_pSeq i : NNReal) : ℝ) =
      ((permNotMC_computable_pSeq_numer i : ℕ) : ℝ) /
        (2 * ((permNotMC_bigIdx i : ℕ) +
            3 : ℝ)) := by
  have hk : (0 : ℝ) < (permNotMC_bigIdx i
      : ℝ) + 3 := by positivity
  unfold permNotMC_pSeq
    permNotMC_computable_pSeq_numer
  simp only
  split_ifs with h1 h2
  · push_cast
    field_simp
  · rw [Real.coe_toNNReal _ (by positivity)]
    push_cast
    field_simp
    ring
  · have : (1 : ℝ) / ((permNotMC_bigIdx i
      : ℝ) + 3) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hk (by norm_num)]
      have : (0 : ℝ) ≤ (permNotMC_bigIdx i
          : ℝ) := Nat.cast_nonneg _
      linarith
    rw [Real.coe_toNNReal _ (by linarith)]
    push_cast
    field_simp
    ring

/-- Step 2b of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
The probability sequence `pSeq` is a computable probability sequence. -/
private lemma permNotMC_computable_pSeq :
    IsComputableProbSeq permNotMC_pSeq :=
        by
  have hnumP := permNotMC_computable_pSeq_primrec_numer
  have hidxP := permNotMC_computable_pSeq_primrec_bigIdx
  refine ⟨fun a => (((permNotMC_computable_pSeq_numer a.1 : ℕ) : ℤ) : ℚ) /
      ((2 * (permNotMC_bigIdx a.1 + 3) :
          ℕ) : ℚ), ?_, ?_⟩
  · refine computable_of_num_den
      (N := fun a : ℕ × ℕ => ((permNotMC_computable_pSeq_numer a.1 : ℕ) : ℤ))
      (D := fun a : ℕ × ℕ => 2 * (permNotMC_bigIdx a.1 + 3)) ?_ ?_ ?_ (fun a => rfl)
    · exact Computable.comp (f := fun n : ℕ => (n : ℤ)) ComputableReals.primrec_natCastInt.to_comp
        (hnumP.to_comp.comp Computable.fst)
    · exact (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (hidxP.comp Primrec.fst) (Primrec.const 3))).to_comp
    · intro a; positivity
  · intro i s
    have h := permNotMC_computable_pSeq_eq
        i
    simp only
    rw [h]
    push_cast
    simp [pow_nonneg]

private lemma permNotMC_converges_bigStart_ge
    (k : ℕ) : k ≤ permNotMC_bigStart k :=
        by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    simp only [permNotMC_bigStart]
    omega

/-- `pSeq i` is `1/2` or `1/2 ± 1/(k+3)` for the index `k = bigIdx i` of the big block of `i`. -/
private lemma permNotMC_converges_abs_le
    (i : ℕ) :
    |((permNotMC_pSeq i : NNReal) : ℝ) -
        1 / 2| ≤
      1 / ((permNotMC_bigIdx i : ℕ) + 3 :
          ℝ) := by
  unfold permNotMC_pSeq
  dsimp only
  generalize permNotMC_bigIdx i = k
  have hk3 : 1 / (k + 3 : ℝ) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hk0 : 0 < 1 / (k + 3 : ℝ) := by positivity
  split_ifs
  · rw [show ((1 / 2 : NNReal) : ℝ) = 1 / 2 by norm_num, sub_self, abs_zero]
    exact hk0.le
  · rw [Real.coe_toNNReal _ (by linarith),
      show (1 / 2 + 1 / (k + 3 : ℝ) - 1 / 2) = 1 / (k + 3 : ℝ) by ring, abs_of_pos hk0]
  · rw [Real.coe_toNNReal _ (by linarith),
      show (1 / 2 - 1 / (k + 3 : ℝ) - 1 / 2) = -(1 / (k + 3 : ℝ)) by ring, abs_neg,
      abs_of_pos hk0]

/-- Step 2b of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
The probability sequence `pSeq` converges computably to `1/2`. -/
private lemma permNotMC_converges :
    ConvergesComputably permNotMC_pSeq (1
        / 2) := by
  refine ⟨permNotMC_computable_pSeq,
    fun ε => permNotMC_bigStart ε.den,
    permNotMC_computable_pSeq_primrec_bigStart.to_comp.comp
      computable_ratDen, ?_⟩
  intro ε hε i hi
  have hle : ε.den ≤ permNotMC_bigIdx i :=
      by
    unfold permNotMC_bigIdx
    exact Nat.le_findGreatest
      ((permNotMC_converges_bigStart_ge
        ε.den).trans hi) hi
  have hdpos : (0 : ℝ) < (ε.den : ℝ) := by exact_mod_cast ε.den_pos
  have hleR : (ε.den : ℝ) ≤
      (permNotMC_bigIdx i : ℝ) := by
    exact_mod_cast hle
  calc |((permNotMC_pSeq i : NNReal) : ℝ)
      - 1 / 2|
      ≤ 1 / ((permNotMC_bigIdx i : ℕ) +
          3 : ℝ) :=
        permNotMC_converges_abs_le i
    _ < 1 / (ε.den : ℝ) := one_div_lt_one_div_of_lt hdpos (by linarith)
    _ ≤ (ε : ℝ) := zsd_inv_den_le ε hε

private lemma permNotMC_pm_integral_bitVal {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (i : ℕ) :
    ∫ w, bitVal (w i) ∂(independentTrials p hp) = (p i : ℝ) := by
  have hmeas : MeasurableSet {w : CantorSeq | w i = true} := by
    have h0 : MeasurableSet ((fun f : CantorSeq => f i) ⁻¹' {true}) :=
      (measurable_pi_apply i) (measurableSet_singleton true)
    exact h0
  have h : (fun w : CantorSeq => bitVal (w i)) =
      Set.indicator {w : CantorSeq | w i = true} (fun _ => (1 : ℝ)) := by
    funext w
    by_cases hw : w i = true <;> simp [Set.indicator, bitVal, hw]
  rw [h, integral_indicator_const _ hmeas]
  simp only [smul_eq_mul, mul_one, measureReal_def]
  rw [isMisesKLRandomAt_of_isMartinLofRandom_aux_coord_mass hp i true]
  simp

private lemma permNotMC_pm_subG {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (i : ℕ) :
    ProbabilityTheory.HasSubgaussianMGF (fun w : CantorSeq => bitVal (w i) - (p i : ℝ))
      (1 / 4 : NNReal) (independentTrials p hp) := by
  have hm : AEMeasurable (fun w : CantorSeq => bitVal (w i)) (independentTrials p hp) :=
    (measurable_bitVal.comp (measurable_pi_apply i)).aemeasurable
  have hb : ∀ᵐ w ∂(independentTrials p hp), bitVal (w i) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with w
    cases w i <;> simp [bitVal]
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := independentTrials p hp)
    (X := fun w : CantorSeq => bitVal (w i)) hm hb
  rw [permNotMC_pm_integral_bitVal hp i] at h
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : NNReal) := by
    simp
    norm_num
  rwa [hc] at h

private lemma permNotMC_pm_block_upper {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (a n : ℕ) (q : ℝ)
    (hq : ∀ j < n, (p (a + j) : ℝ) = q) {ε : ℝ} (hε : 0 ≤ ε) :
    independentTrials p hp {w | ε ≤ ∑ j ∈ Finset.range n, (bitVal (w (a + j)) - q)} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * n * (1 / 4)))) := by
  have hind : ProbabilityTheory.iIndepFun
      (fun (j : ℕ) (w : CantorSeq) => bitVal (w (a + j)) - q) (independentTrials p hp) := by
    have h1 := (isMisesKLRandomAt_of_isMartinLofRandom_aux_iIndep hp).precomp
      (g := fun j : ℕ => a + j) (add_right_injective a)
    exact h1.comp (fun _ x => bitVal x - q) (fun _ => measurable_bitVal.sub_const q)
  have hsub : ∀ j < n, ProbabilityTheory.HasSubgaussianMGF
      (fun w : CantorSeq => bitVal (w (a + j)) - q) (1 / 4 : NNReal) (independentTrials p hp) := by
    intro j hj
    rw [← hq j hj]
    exact permNotMC_pm_subG hp (a + j)
  have h := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind hsub hε
  have hfin : independentTrials p hp {w | ε ≤ ∑ j ∈ Finset.range n, (bitVal (w (a + j)) - q)} ≠ ⊤ :=
    measure_ne_top _ _
  calc _ = ENNReal.ofReal ((independentTrials p hp).real
          {w | ε ≤ ∑ j ∈ Finset.range n, (bitVal (w (a + j)) - q)}) :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by push_cast at h; exact h)

private lemma permNotMC_pm_block_lower {p : ℕ → NNReal} (hp : ∀ i, p i ≤ 1) (a n : ℕ) (q : ℝ)
    (hq : ∀ j < n, (p (a + j) : ℝ) = q) {ε : ℝ} (hε : 0 ≤ ε) :
    independentTrials p hp {w | ε ≤ ∑ j ∈ Finset.range n, (q - bitVal (w (a + j)))} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (2 * n * (1 / 4)))) := by
  have hind : ProbabilityTheory.iIndepFun
      (fun (j : ℕ) (w : CantorSeq) => q - bitVal (w (a + j))) (independentTrials p hp) := by
    have h1 := (isMisesKLRandomAt_of_isMartinLofRandom_aux_iIndep hp).precomp
      (g := fun j : ℕ => a + j) (add_right_injective a)
    exact h1.comp (fun _ x => q - bitVal x) (fun _ => measurable_const.sub measurable_bitVal)
  have hsub : ∀ j < n, ProbabilityTheory.HasSubgaussianMGF
      (fun w : CantorSeq => q - bitVal (w (a + j))) (1 / 4 : NNReal) (independentTrials p hp) := by
    intro j hj
    have h := (permNotMC_pm_subG hp (a + j)).neg
    rw [hq j hj] at h
    have heq : (-(fun w : CantorSeq => bitVal (w (a + j)) - q)) =
        fun w : CantorSeq => q - bitVal (w (a + j)) := by
      funext w
      simp
    rwa [heq] at h
  have h := ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind hsub hε
  have hfin : independentTrials p hp {w | ε ≤ ∑ j ∈ Finset.range n, (q - bitVal (w (a + j)))} ≠ ⊤ :=
    measure_ne_top _ _
  calc _ = ENNReal.ofReal ((independentTrials p hp).real
          {w | ε ≤ ∑ j ∈ Finset.range n, (q - bitVal (w (a + j)))}) :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by push_cast at h; exact h)

private lemma permNotMC_pm_bigStart_mono : Monotone permNotMC_bigStart :=
  monotone_nat_of_le_succ (fun k => by simp only [permNotMC_bigStart]; omega)

private lemma permNotMC_pm_bigStart_ge (k : ℕ) : k ≤ permNotMC_bigStart k := by
  induction k with
  | zero => simp [permNotMC_bigStart]
  | succ k ih => simp only [permNotMC_bigStart]; omega

private lemma permNotMC_pm_bigIdx_eq {k i : ℕ} (h1 : permNotMC_bigStart k ≤ i)
    (h2 : i < permNotMC_bigStart (k + 1)) :
    permNotMC_bigIdx i = k := by
  unfold permNotMC_bigIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨le_trans (permNotMC_pm_bigStart_ge k) h1, fun _ => h1, ?_⟩
  intro m hm _ hP
  have := permNotMC_pm_bigStart_mono (show k + 1 ≤ m from hm)
  omega

private lemma permNotMC_pm_pSeq_left (k j : ℕ) (hj : j < permNotMC_blockLen k) :
    (permNotMC_pSeq (permNotMC_bigStart k + 1 + j) : ℝ) = 1 / 2 + 1 / ((k : ℝ) + 3) := by
  have hidx : permNotMC_bigIdx
      (permNotMC_bigStart k + 1 + j) =
      k := by
    apply permNotMC_pm_bigIdx_eq
    · omega
    · simp only [permNotMC_bigStart];
        omega
  have hoff : permNotMC_bigStart k + 1 +
      j - permNotMC_bigStart k = j + 1 :=
      by omega
  have hnn : (0 : ℝ) ≤ 1 / 2 + 1 / ((k : ℝ) + 3) := by positivity
  unfold permNotMC_pSeq
  simp only [hidx, hoff]
  rw [ite_eq_right (by omega), ite_eq_left (by omega), Real.coe_toNNReal _ hnn]

private lemma permNotMC_pm_pSeq_right (k j : ℕ) (hj : j < permNotMC_blockLen k) :
    (permNotMC_pSeq (permNotMC_bigStart k + 1 + permNotMC_blockLen k + j) : ℝ) =
      1 / 2 - 1 / ((k : ℝ) + 3) := by
  have hidx : permNotMC_bigIdx
      (permNotMC_bigStart k + 1 +
      permNotMC_blockLen k + j) = k := by
    apply permNotMC_pm_bigIdx_eq
    · omega
    · simp only [permNotMC_bigStart];
        omega
  have hoff : permNotMC_bigStart k + 1 +
      permNotMC_blockLen k + j -
      permNotMC_bigStart k =
      permNotMC_blockLen k + j + 1 := by
        omega
  have hk : (1 : ℝ) / ((k : ℝ) + 3) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hnn : (0 : ℝ) ≤ 1 / 2 - 1 / ((k : ℝ) + 3) := by linarith
  unfold permNotMC_pSeq
  simp only [hidx, hoff]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), Real.coe_toNNReal _ hnn]

private lemma permNotMC_pm_count_eq_sum (w : CantorSeq) (a n : ℕ) :
    (((List.range n).map (fun j => w (a + j))).count true : ℝ) =
      ∑ j ∈ Finset.range n, bitVal (w (a + j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.sum_range_succ, ← ih]
    rcases h : w (a + n) with _ | _ <;> simp [bitVal, h]

private lemma permNotMC_pm_exp_bound (k : ℕ) :
    Real.exp (-((permNotMC_blockLen k : ℝ)
        * (1 / ((k : ℝ) + 3))) ^ 2 / (2 *
        (permNotMC_blockLen k : ℝ) *
        (1 / 4)))
      ≤ (1 / 2 : ℝ) ^ (k + 6) := by
  have hk : ((k : ℝ) + 3) ≠ 0 := by positivity
  have e : -((permNotMC_blockLen k : ℝ) *
      (1 / ((k : ℝ) + 3))) ^ 2 /
      (2 * (permNotMC_blockLen k : ℝ) *
      (1 / 4))
      = -((2 : ℝ) ^ (k + 6)) := by
    unfold permNotMC_blockLen
    push_cast
    field_simp
    ring
  rw [e]
  have h1 : ((k + 6 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 6) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := k + 6)).le
  have h2 : Real.exp (-((2 : ℝ) ^ (k + 6))) ≤ Real.exp (-((k + 6 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by linarith)
  refine h2.trans ?_
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp 1])
  have h4 : Real.exp (-((k + 6 : ℕ) : ℝ)) = Real.exp (-1) ^ (k + 6) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h4]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) h3 _

private lemma permNotMC_pm_fail_left (k : ℕ) :
    independentTrials permNotMC_pSeq permNotMC_pSeq_le_one
      {w | ¬ (permNotMC_blockLen k < 2 * ((List.range (permNotMC_blockLen k)).map
          (fun j => w (permNotMC_bigStart
                      k + 1 + j))).count true)} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 6)) := by
  have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  have hε : (0 : ℝ) ≤ (permNotMC_blockLen
      k : ℝ) * (1 / ((k : ℝ) + 3)) := by positivity
  refine le_trans (measure_mono ?_)
    ((permNotMC_pm_block_lower permNotMC_pSeq_le_one (permNotMC_bigStart k + 1)
        (permNotMC_blockLen k) (1 / 2 + 1 / ((k : ℝ) + 3))
      (fun j hj => permNotMC_pm_pSeq_left k j hj) hε).trans
        (ENNReal.ofReal_le_ofReal (permNotMC_pm_exp_bound k)))
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  have hc := permNotMC_pm_count_eq_sum w (permNotMC_bigStart k + 1) (permNotMC_blockLen k)
  rw [Finset.sum_sub_distrib, ← hc]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (2 * (((List.range
      (permNotMC_blockLen k)).map (fun j
      => w (permNotMC_bigStart k + 1 +
           j))).count true) : ℕ) ≤
           permNotMC_blockLen k := by
    omega
  have h2 : (2 : ℝ) * (((List.range (permNotMC_blockLen k)).map
      (fun j => w (permNotMC_bigStart k + 1 + j))).count true : ℕ) ≤
        (permNotMC_blockLen k : ℝ) := by
    exact_mod_cast this
  nlinarith

private lemma permNotMC_pm_fail_right (k : ℕ) :
    independentTrials permNotMC_pSeq permNotMC_pSeq_le_one
      {w | ¬ (2 * ((List.range
          (permNotMC_blockLen k)).map
          (fun j => w (permNotMC_bigStart k + 1 + permNotMC_blockLen k + j))).count true <
            permNotMC_blockLen k)} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 6)) := by
  have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  have hε : (0 : ℝ) ≤ (permNotMC_blockLen
      k : ℝ) * (1 / ((k : ℝ) + 3)) := by positivity
  refine le_trans (measure_mono ?_)
    ((permNotMC_pm_block_upper permNotMC_pSeq_le_one
        (permNotMC_bigStart k + 1 + permNotMC_blockLen k) (permNotMC_blockLen k)
        (1 / 2 - 1 / ((k : ℝ) + 3))
      (fun j hj => permNotMC_pm_pSeq_right k j hj) hε).trans
        (ENNReal.ofReal_le_ofReal (permNotMC_pm_exp_bound k)))
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  have hc := permNotMC_pm_count_eq_sum w (permNotMC_bigStart k + 1 + permNotMC_blockLen k)
    (permNotMC_blockLen k)
  rw [Finset.sum_sub_distrib, ← hc]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : permNotMC_blockLen k ≤ 2 * (((List.range (permNotMC_blockLen k)).map
      (fun j => w (permNotMC_bigStart k + 1 + permNotMC_blockLen k + j))).count true) := by
    omega
  have h2 : (permNotMC_blockLen k : ℝ) ≤
      (2 : ℝ) * (((List.range
      (permNotMC_blockLen k)).map (fun j
      => w (permNotMC_bigStart k + 1 +
           permNotMC_blockLen k +
           j))).count true : ℕ) := by
    exact_mod_cast this
  nlinarith

/-- Step 2c of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
The set `goodSet` has strictly positive measure under the independent trials measure for `pSeq`. -/
private lemma permNotMC_pm_pos :
    0 < independentTrials permNotMC_pSeq permNotMC_pSeq_le_one permNotMC_goodSet := by
  have hsub : permNotMC_goodSetᶜ ⊆ ⋃ k :
      ℕ,
      ({w : CantorSeq | ¬ (permNotMC_blockLen k < 2 * ((List.range (permNotMC_blockLen k)).map
          (fun j => w (permNotMC_bigStart
                      k + 1 + j))).count true)} ∪
       {w : CantorSeq | ¬ (2 * ((List.range
           (permNotMC_blockLen k)).map
          (fun j => w (permNotMC_bigStart k + 1 + permNotMC_blockLen k + j))).count true <
            permNotMC_blockLen k)}) := by
    intro w hw
    simp only [permNotMC_goodSet,
        Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hw
    obtain ⟨k, hk⟩ := hw
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    rw [not_and_or] at hk
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr hk
  have hs : HasSum (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ (k + 6)) (1 / 16) := by
    have h := (hasSum_geometric_two).mul_left (2 * (1 / 2 : ℝ) ^ 6)
    convert h using 1
    · funext k
      ring
    · norm_num
  have hsum : independentTrials permNotMC_pSeq permNotMC_pSeq_le_one permNotMC_goodSetᶜ ≤
      ENNReal.ofReal (1 / 16) := by
    calc independentTrials permNotMC_pSeq permNotMC_pSeq_le_one permNotMC_goodSetᶜ
        ≤ independentTrials permNotMC_pSeq
            permNotMC_pSeq_le_one (⋃ k :
            ℕ, _) := measure_mono hsub
      _ ≤ ∑' k : ℕ, independentTrials permNotMC_pSeq permNotMC_pSeq_le_one _ := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (k + 6)) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          refine (measure_union_le _ _).trans ?_
          refine (add_le_add (permNotMC_pm_fail_left k)
            (permNotMC_pm_fail_right k)).trans (le_of_eq ?_)
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ = ENNReal.ofReal (1 / 16) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable, hs.tsum_eq]
  by_contra hcon
  have h0 : independentTrials permNotMC_pSeq permNotMC_pSeq_le_one permNotMC_goodSet = 0 := by
    simpa using hcon
  have h1 : (1 : ℝ≥0∞) ≤ independentTrials permNotMC_pSeq permNotMC_pSeq_le_one permNotMC_goodSet +
      independentTrials permNotMC_pSeq permNotMC_pSeq_le_one permNotMC_goodSetᶜ := by
    calc (1 : ℝ≥0∞)
        = independentTrials permNotMC_pSeq permNotMC_pSeq_le_one Set.univ := measure_univ.symm
      _ ≤ independentTrials permNotMC_pSeq permNotMC_pSeq_le_one
          (permNotMC_goodSet ∪ permNotMC_goodSetᶜ) := by rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  rw [h0, zero_add] at h1
  have h3 := h1.trans hsum
  have h2 : ENNReal.ofReal (1 / 16) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  exact absurd h3 (not_le.2 h2)

/-- Step 2e of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
The selection rule `selR` is a decidable set. -/
private lemma permNotMC_decidable_aux_blockLen :
    Primrec permNotMC_blockLen := by
  unfold permNotMC_blockLen
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have h1 : Primrec fun k : ℕ => 2 ^ (k + 5) :=
    hpow.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.id (Primrec.const 5))
  have h2 : Primrec fun k : ℕ => (k + 3) ^ 2 :=
    hpow.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 3)) (Primrec.const 2)
  exact Primrec.nat_mul.comp h1 h2

private lemma permNotMC_decidable_aux_bigStart :
    Primrec permNotMC_bigStart := by
  have hb := permNotMC_decidable_aux_blockLen
  have hf : Primrec₂ fun (n IH : ℕ) =>
      IH + (2 * permNotMC_blockLen n + 1)
          :=
    Primrec.nat_add.comp Primrec₂.right
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) (hb.comp Primrec₂.left))
        (Primrec.const 1))
  have h := Primrec.nat_rec₁ (0 : ℕ) hf
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih =>
    show _ = _
    simp only [permNotMC_bigStart]
    rw [← ih]

private lemma permNotMC_decidable_aux_bigIdx :
    Primrec permNotMC_bigIdx := by
  have hs := permNotMC_decidable_aux_bigStart
  unfold permNotMC_bigIdx
  exact Primrec.nat_findGreatest Primrec.id
    (Primrec.nat_le.comp (hs.comp Primrec.snd) Primrec.fst)

private lemma permNotMC_decidable :
    IsDecidableSet permNotMC_selR := by
  have hb := permNotMC_decidable_aux_blockLen
  have hs := permNotMC_decidable_aux_bigStart
  have hi := permNotMC_decidable_aux_bigIdx
  have hk : Primrec fun x : BitString =>
      permNotMC_bigIdx x.length :=
    hi.comp Primrec.list_length
  have hst : Primrec fun x : BitString =>
      permNotMC_bigStart
        (permNotMC_bigIdx x.length) :=
    hs.comp hk
  have hbl : Primrec fun x : BitString =>
      permNotMC_blockLen
        (permNotMC_bigIdx x.length) :=
    hb.comp hk
  have hoff : Primrec fun x : BitString =>
      x.length - permNotMC_bigStart
        (permNotMC_bigIdx x.length) :=
    Primrec.nat_sub.comp Primrec.list_length hst
  have hbit : Primrec fun x : BitString =>
      x.getD (permNotMC_bigStart
        (permNotMC_bigIdx x.length)) false
            :=
    (Primrec.list_getD false).comp Primrec.id hst
  have p0 : PrimrecPred fun x : BitString =>
      x.length - permNotMC_bigStart
        (permNotMC_bigIdx x.length) = 0 :=
    (Primrec.eq.comp hoff (Primrec.const 0))
  have p1 : PrimrecPred fun x : BitString =>
      x.length - permNotMC_bigStart
        (permNotMC_bigIdx x.length) ≤
      permNotMC_blockLen
        (permNotMC_bigIdx x.length) :=
    Primrec.nat_le.comp hoff hbl
  have p2 : PrimrecPred fun x : BitString =>
      0 < x.length - permNotMC_bigStart
        (permNotMC_bigIdx x.length) :=
    Primrec.nat_lt.comp (Primrec.const 0) hoff
  have p3 : PrimrecPred fun x : BitString =>
      x.getD (permNotMC_bigStart
        (permNotMC_bigIdx x.length)) false
            = false :=
    Primrec.eq.comp hbit (Primrec.const false)
  have p4 : PrimrecPred fun x : BitString =>
      permNotMC_blockLen
        (permNotMC_bigIdx x.length) <
      x.length - permNotMC_bigStart
        (permNotMC_bigIdx x.length) :=
    Primrec.nat_lt.comp hbl hoff
  have p5 : PrimrecPred fun x : BitString =>
      x.getD (permNotMC_bigStart
        (permNotMC_bigIdx x.length)) false
            = true :=
    Primrec.eq.comp hbit (Primrec.const true)
  have hP := p0.or (((p1.and p2).and p3).or (p4.and p5))
  refine ⟨_, hP.decide.to_comp, fun x => ?_⟩
  simp only [permNotMC_selR,
    Set.mem_ofPred_eq, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · rintro (h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, h3⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

open Classical in
private lemma permNotMC_predictable_aux_chain (R : Set BitString) (w : CantorSeq) (t : ℕ) :
    selectChain R w t =
      (List.range (Nat.count (fun i => cantorPrefix w i ∈ R) t)).map
        (fun j => w (Nat.nth (fun i => cantorPrefix w i ∈ R) j)) := by
  induction t with
  | zero =>
    have h0 : cantorPrefix w 0 = [] := by simp [cantorPrefix]
    simp [selectChain, selectedBits, h0, selectedAux]
  | succ t ih =>
    have h1 : selectChain R w (t + 1) = selectChain R w t ++ (if cantorPrefix w t ∈
        R then [w t] else []) := by
      unfold selectChain
      rw [cantorPrefix_succ, selectedBits_append_singleton]
    rw [h1, ih, Nat.count_succ]
    by_cases hP : cantorPrefix w t ∈ R
    · simp only [hP, ite_true, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [Nat.nth_count hP]
    · simp [hP]

open Classical in
private lemma permNotMC_predictable_aux_stream (R : Set BitString) (w : CantorSeq)
    (hinf : ∀ n, ∃ i ≥ n, cantorPrefix w i ∈ R) :
    selectStream R w = .infinite (fun j => w (Nat.nth (fun i => cantorPrefix w i ∈ R) j)) := by
  set P : ℕ → Prop := fun i => cantorPrefix w i ∈ R with hPdef
  have hInf : (Set.ofPred P).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨i, hi, hiP⟩ := hinf (n + 1)
    exact ⟨i, hiP, by omega⟩
  set u : CantorSeq := fun j => w (Nat.nth P j) with hu
  have hmem : ∀ y, BitStream.finite y ≤ selectStream R w ↔ ∃ t, y <+: selectChain R w t := fun y =>
    BitStream.finite_le_ofPrefixSet_iff (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w))
        y
  apply BitStream.eq_of_forall_finite_le_iff
  intro y
  rw [hmem]
  change _ ↔ IsCantorPrefix y u
  constructor
  · rintro ⟨t, ht⟩
    rw [permNotMC_predictable_aux_chain] at ht
    intro i hi
    have hlen : i < (List.map (fun j => w (Nat.nth P j)) (List.range (Nat.count P t))).length :=
      lt_of_lt_of_le hi ht.length_le
    have := ht.getElem hi
    rw [this, List.getElem_map, List.getElem_range]
  · intro h
    refine ⟨Nat.nth P y.length, ?_⟩
    rw [permNotMC_predictable_aux_chain, Nat.count_nth_of_infinite hInf]
    have hy : y = List.map (fun j => w (Nat.nth P j)) (List.range y.length) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        rw [List.getElem_map, List.getElem_range]
        exact (h i h1).symm
    exact ⟨[], by rw [List.append_nil]; exact hy⟩

private lemma permNotMC_predictable_aux_bigStart_ge (k : ℕ) :
    k ≤ permNotMC_bigStart k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    change k + 1 ≤ permNotMC_bigStart k +
        (2 * _ + 1)
    omega

private lemma permNotMC_predictable_aux_bigStart_mono :
    Monotone permNotMC_bigStart := by
  apply monotone_nat_of_le_succ
  intro k
  change _ ≤ permNotMC_bigStart k +
      (2 * _ + 1)
  omega

private lemma permNotMC_predictable_aux_bigIdx (k o : ℕ)
    (ho : o ≤ 2 * permNotMC_blockLen k) :
    permNotMC_bigIdx
      (permNotMC_bigStart k + o) = k := by
  have hge := permNotMC_predictable_aux_bigStart_ge k
  unfold permNotMC_bigIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => by omega, ?_⟩
  intro m hkm hm hP
  have hP' : permNotMC_bigStart m ≤
      permNotMC_bigStart k + o := hP
  have h1 := permNotMC_predictable_aux_bigStart_mono (show k + 1 ≤ m from hkm)
  have h2 : permNotMC_bigStart (k + 1) =
      permNotMC_bigStart k +
        (2 * permNotMC_blockLen k + 1) :=
            rfl
  omega

private def permNotMC_predictable_selP
    (w : CantorSeq) (i : ℕ) : Prop :=
  cantorPrefix w i ∈ permNotMC_selR

private lemma permNotMC_predictable_aux_selP_iff (w : CantorSeq) (k o : ℕ)
    (ho : o ≤ 2 * permNotMC_blockLen k) :
    permNotMC_predictable_selP w
        (permNotMC_bigStart k + o) ↔
      (o = 0 ∨ (o ≤ permNotMC_blockLen k ∧
          0 < o ∧
          w (permNotMC_bigStart k) =
              false) ∨
        (permNotMC_blockLen k < o ∧
          w (permNotMC_bigStart k) =
              true)) := by
  unfold permNotMC_predictable_selP
    permNotMC_selR
  simp only [Set.mem_ofPred_eq, cantorPrefix_length]
  rw [permNotMC_predictable_aux_bigIdx k o
      ho,
    Nat.add_sub_cancel_left]
  by_cases ho0 : o = 0
  · simp [ho0]
  · have hget :
      (cantorPrefix w (permNotMC_bigStart
      k + o)).getD
        (permNotMC_bigStart k) false =
        w (permNotMC_bigStart k) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
      simp
    rw [hget]

open Classical in
private lemma permNotMC_predictable_aux_countQ (w : CantorSeq) (k : ℕ) :
    ∀ m, m ≤ 2 * permNotMC_blockLen k +
        1 →
    Nat.count (fun o =>
      permNotMC_predictable_selP w
        (permNotMC_bigStart k + o)) m =
      if w (permNotMC_bigStart k) =
          false then
        min m (permNotMC_blockLen k + 1)
      else (if m = 0 then 0 else 1 + (m - (permNotMC_blockLen k + 1))) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Nat.count_succ, ih (by omega)]
    have hQ := permNotMC_predictable_aux_selP_iff w k m (by omega)
    by_cases hk : w (permNotMC_bigStart k)
        = false
    · simp only [hk, ite_true, Bool.false_eq_true, and_false, or_false, and_true] at hQ ⊢
      by_cases hq :
          permNotMC_predictable_selP w
        (permNotMC_bigStart k + m)
      · rw [ite_eq_left hq]
        have := hQ.mp hq
        omega
      · rw [ite_eq_right hq]
        have : ¬ (m = 0 ∨
            (m ≤ permNotMC_blockLen k ∧
            0 < m)) :=
          fun h => hq (hQ.mpr h)
        omega
    · have hk' : w (permNotMC_bigStart k)
        = true := by simpa using hk
      simp only [hk, Bool.true_eq_false, and_false, false_or, and_true] at hQ
      simp only [hk', Bool.true_eq_false, ite_false]
      by_cases hq :
          permNotMC_predictable_selP w
        (permNotMC_bigStart k + m)
      · rw [ite_eq_left hq]
        have := hQ.mp hq
        split_ifs <;> omega
      · rw [ite_eq_right hq]
        have : ¬ (m = 0 ∨
            permNotMC_blockLen k < m) :=
          fun h => hq (hQ.mpr h)
        split_ifs <;> first | omega | (exfalso; simp_all)

open Classical in
private lemma permNotMC_predictable_aux_count_bigStart (w : CantorSeq) (k : ℕ) :
    Nat.count (permNotMC_predictable_selP w)
      (permNotMC_bigStart k) =
    permNotMC_blockStart
      permNotMC_blockLen k := by
  induction k with
  | zero => simp [permNotMC_bigStart,
      permNotMC_blockStart]
  | succ k ih =>
    have h2 : permNotMC_bigStart (k + 1) =
      permNotMC_bigStart k +
        (2 * permNotMC_blockLen k + 1) :=
            rfl
    have h3 : permNotMC_blockStart
        permNotMC_blockLen (k + 1) =
      permNotMC_blockStart
        permNotMC_blockLen k + 1 +
        permNotMC_blockLen k := rfl
    have hc := permNotMC_predictable_aux_countQ w k
      (2 * permNotMC_blockLen k + 1)
          le_rfl
    have e1 : Nat.count
        (permNotMC_predictable_selP w)
        (permNotMC_bigStart k +
          (2 * permNotMC_blockLen k + 1))
              =
        Nat.count (permNotMC_predictable_selP w)
          (permNotMC_bigStart k) +
        Nat.count (fun o =>
          permNotMC_predictable_selP w
          (permNotMC_bigStart k + o))
          (2 * permNotMC_blockLen k + 1)
              := Nat.count_add _ _ _
    rw [h2, e1, ih, hc, h3]
    by_cases hk : w (permNotMC_bigStart k)
        = false
    · simp only [hk, ite_true]
      omega
    · have hk' : w (permNotMC_bigStart k)
        = true := by simpa using hk
      split_ifs <;> first | omega | (exfalso; simp_all)

open Classical in
private lemma permNotMC_predictable_aux_nth_of (w : CantorSeq) (k j o : ℕ)
    (hP : permNotMC_predictable_selP w
      (permNotMC_bigStart k + o))
    (hc : Nat.count (fun o' => permNotMC_predictable_selP w
        (permNotMC_bigStart k + o')) o =
            j) :
    Nat.nth (permNotMC_predictable_selP w)
      (permNotMC_blockStart
        permNotMC_blockLen k + j) =
    permNotMC_bigStart k + o := by
  have e1 : Nat.count
      (permNotMC_predictable_selP w)
        (permNotMC_bigStart k + o) =
      Nat.count (permNotMC_predictable_selP w)
        (permNotMC_bigStart k) +
      Nat.count (fun o' =>
        permNotMC_predictable_selP w
        (permNotMC_bigStart k + o')) o :=
            Nat.count_add _ _ _
  rw [permNotMC_predictable_aux_count_bigStart w k, hc] at e1
  rw [← e1]
  exact Nat.nth_count hP

/-- Step 2f of the proof of
exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom:
For any sequence `w` in `goodSet`, the stream selected by `selR` is infinite and satisfies the
`predictable` property: the selected stream is `w ∘ nth P`. -/
private lemma permNotMC_step2f_predictable {w : CantorSeq} (hw : w ∈ permNotMC_goodSet) :
    ∃ u, selectStream permNotMC_selR w = .infinite u ∧
      permNotMC_predictable permNotMC_blockLen u := by
  have hinf : ∀ n, ∃ i ≥ n, cantorPrefix w i ∈
      permNotMC_selR := fun n =>
    ⟨permNotMC_bigStart n,
      permNotMC_predictable_aux_bigStart_ge n,
      (permNotMC_predictable_aux_selP_iff w n 0 (Nat.zero_le _)).2 (Or.inl rfl)⟩
  refine ⟨fun j =>
    w (Nat.nth (permNotMC_predictable_selP
    w) j),
    permNotMC_predictable_aux_stream _ w
        hinf, ?_⟩
  intro k
  dsimp only
  have h0 : Nat.nth
      (permNotMC_predictable_selP w)
      (permNotMC_blockStart
        permNotMC_blockLen k) =
      permNotMC_bigStart k := by
    have := permNotMC_predictable_aux_nth_of w k 0 0
      ((permNotMC_predictable_aux_selP_iff w k 0 (Nat.zero_le _)).2 (Or.inl rfl)) (by simp)
    simpa using this
  obtain ⟨hL, hR⟩ := hw k
  by_cases hk : w (permNotMC_bigStart k) =
      false
  · have hmap : (List.range (permNotMC_blockLen k)).map
        (fun j => w (Nat.nth (permNotMC_predictable_selP w)
          (permNotMC_blockStart
            permNotMC_blockLen k + 1 +
                j))) =
        (List.range (permNotMC_blockLen k)).map
          (fun j => w (permNotMC_bigStart
                      k + 1 + j)) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hc := permNotMC_predictable_aux_countQ w k (1 + j) (by omega)
      rw [ite_eq_left hk] at hc
      have := permNotMC_predictable_aux_nth_of w k (1 + j) (1 + j)
        ((permNotMC_predictable_aux_selP_iff w k (1 + j) (by omega)).2
          (Or.inr (Or.inl ⟨by omega, by omega, hk⟩))) (by omega)
      rw [show permNotMC_blockStart
          permNotMC_blockLen k + 1 + j =
          permNotMC_blockStart
          permNotMC_blockLen k + (1 + j)
              by omega, this]
      congr 1
      omega
    rw [h0, hmap]
    constructor
    · intro _
      omega
    · intro _
      exact hk
  · have hk' : w (permNotMC_bigStart k) =
      true := by simpa using hk
    have hmap : (List.range
        (permNotMC_blockLen k)).map
        (fun j => w (Nat.nth (permNotMC_predictable_selP w)
          (permNotMC_blockStart
            permNotMC_blockLen k + 1 +
                j))) =
        (List.range (permNotMC_blockLen k)).map
          (fun j => w (permNotMC_bigStart
                      k + 1 +
            permNotMC_blockLen k + j)) :=
                by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hc := permNotMC_predictable_aux_countQ w k
        (1 + permNotMC_blockLen k + j)
            (by omega)
      rw [ite_eq_right hk] at hc
      have := permNotMC_predictable_aux_nth_of w k (1 + j)
        (1 + permNotMC_blockLen k + j)
        ((permNotMC_predictable_aux_selP_iff w k
          (1 + permNotMC_blockLen k + j)
              (by omega)).2
          (Or.inr (Or.inr ⟨by omega, hk'⟩))) (by split_ifs at hc <;> omega)
      rw [show permNotMC_blockStart
          permNotMC_blockLen k + 1 + j =
          permNotMC_blockStart
          permNotMC_blockLen k + (1 + j)
              by omega, this]
      congr 1
      omega
    rw [h0, hmap]
    constructor
    · intro h
      exact absurd h hk
    · intro _
      omega

/-- **SUV Theorem 203(d), p. 307.**  There is a Mises-Church-Daley random sequence with frequency
`1/2` that becomes not Mises-Church random after a computable permutation of its terms. -/
theorem exists_isMisesChurchDaleyRandom_permutation_not_isMisesChurchRandom :
    ∃ w, IsMisesChurchDaleyRandom w ∧ ∃ σ : ℕ → ℕ, Computable σ ∧ Function.Bijective σ ∧
      ¬ IsMisesChurchRandom (w ∘ σ) := by
  have hμ := isComputableMeasure_independentTrials
    permNotMC_pSeq_le_one
    permNotMC_computable_pSeq
  have h_not_null : ¬ IsEffectivelyNull
      (independentTrials permNotMC_pSeq permNotMC_pSeq_le_one) permNotMC_goodSet := by
    intro h
    have h_zero := h.measure_eq_zero
    have h_pos := permNotMC_pm_pos
    rw [h_zero] at h_pos
    exact lt_irrefl _ h_pos
  have h_exists_rand : ∃ w ∈ permNotMC_goodSet,
      IsMartinLofRandom (independentTrials permNotMC_pSeq permNotMC_pSeq_le_one) w := by
    by_contra h
    push Not at h
    have h_null := (isEffectivelyNull_iff_forall_not_random hμ _).mpr h
    exact h_not_null h_null
  rcases h_exists_rand with ⟨w, hw_good, hw_rand⟩
  have h_MCD_w := isMisesChurchDaleyRandomAt_of_isMartinLofRandom
      permNotMC_pSeq_le_one (by norm_num)
      (by norm_num) permNotMC_converges
      hw_rand
  rcases exists_partrec_partialRuleSet_eq permNotMC_decidable with ⟨r, hr_partrec, hr_eq⟩
  rcases permNotMC_step2f_predictable hw_good with ⟨u, hu_select, hu_pred⟩
  have hu_select_r : selectStream (partialRuleSet r) w = .infinite u := by
    rw [hr_eq]
    exact hu_select
  have h_MCD_u := isMisesChurchDaleyRandom_of_selectStream h_MCD_w hr_partrec hu_select_r
  rcases permNotMC_not_MC permNotMC_computable_blockLen hu_pred with ⟨σ, hσ_comp, hσ_bij, hσ_not_MC⟩
  exact ⟨u, h_MCD_u, σ, hσ_comp, hσ_bij, hσ_not_MC⟩

/-- Step 1 of the proof of `exists_isMisesKLRandom_not_isKurtzRandom`: the biased measure
`independentTrials my_p` (of Theorem 203(a)) gives positive mass to every cylinder, since every
`my_p i` lies strictly between `0` and `1` (it equals `1/2 - 1/√(i+5)`). -/
private lemma klNotKurtz_pos (x : BitString) :
    0 < cantorMass (independentTrials klNotML_my_p
      klNotML_my_p_le_one) x := by
  have hp : ∀ i : ℕ, 0 < ((klNotML_my_p i : NNReal) : ℝ) ∧
      ((klNotML_my_p i : NNReal) : ℝ) < 1 := by
    intro i
    have hS : (2 : ℝ) < Real.sqrt ((i : ℝ) + 5) := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    have h1 : 1 / Real.sqrt ((i : ℝ) + 5) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hS
    have h2 : (0 : ℝ) < 1 / Real.sqrt ((i : ℝ) + 5) := by positivity
    have hc : ((klNotML_my_p i : NNReal) : ℝ) =
        1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) := by
      unfold klNotML_my_p
      rw [Real.coe_toNNReal _ (by linarith)]
    rw [hc]
    constructor <;> linarith
  have hR : 0 < massR (independentTrials klNotML_my_p
      klNotML_my_p_le_one) x := by
    rw [massR_independentTrials]
    apply Finset.prod_pos
    intro i _
    split_ifs
    · exact (hp i).1
    · linarith [(hp i).2]
  have hfin : cantorMass (independentTrials klNotML_my_p
      klNotML_my_p_le_one) x ≠ 0 := by
    intro h0
    unfold massR at hR
    rw [h0] at hR
    simp at hR
  exact pos_iff_ne_zero.mpr hfin

/-- Step 2 of the proof of `exists_isMisesKLRandom_not_isKurtzRandom`: along a sequence
that
is Martin-Löf random for the biased measure `P = independentTrials my_p`, the `P`-martingale
`bookmakerCapital P uniformMeasure` is bounded on the prefixes (it is computable, hence lower
semicomputable, and Martin-Löf random sequences are computably random). -/
private lemma klNotKurtz_bounded {w : CantorSeq}
    (hw : IsMartinLofRandom (independentTrials klNotML_my_p
      klNotML_my_p_le_one) w) :
    ∃ C : ℝ, ∀ n, bookmakerCapital (independentTrials
        klNotML_my_p
      klNotML_my_p_le_one) uniformMeasure (cantorPrefix w n) ≤
          C := by
  set P := independentTrials klNotML_my_p
      klNotML_my_p_le_one with hP
  have hPc : IsComputableMeasure P :=
    isComputableMeasure_independentTrials
      klNotML_my_p_le_one
      klNotML_computable
  have hUc : IsComputableMeasure uniformMeasure := isComputableMeasure_uniform
  have hposU : ∀ x, 0 < cantorMass uniformMeasure x := by
    intro x
    rw [cantorMass_uniformMeasure]
    exact ENNReal.pow_pos (by norm_num) _
  have hposP := klNotKurtz_pos
  have hcr := isComputablyRandom_of_isMartinLofRandom hPc hw
  have hcomp := (summable_sq_condOne_sub_of_isComputablyRandom_comp hPc hUc hposP hposU).1
  have hmart := isMartingale_bookmakerCapital hposP hposU
  have hnw : ¬ Wins (bookmakerCapital P uniformMeasure) w :=
    hcr _ hmart.toIsFairCapital hcomp
  unfold Wins at hnw
  push Not at hnw
  obtain ⟨C, hC⟩ := hnw
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

private lemma klNotKurtz_product_aux_p (i : ℕ) :
    0 < (klNotML_my_p i : ℝ) ∧
      (klNotML_my_p i : ℝ) < 1 := by
  have h2 : (2 : ℝ) < Real.sqrt ((i : ℝ) + 5) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  have h3 : 1 / Real.sqrt ((i : ℝ) + 5) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) h2
  have h4 : (0 : ℝ) < 1 / Real.sqrt ((i : ℝ) + 5) := by positivity
  unfold klNotML_my_p
  rw [Real.coe_toNNReal _ (by linarith)]
  constructor <;> linarith

private lemma klNotKurtz_product_aux_one_add_sum_le
    {ι : Type*} (s : Finset ι) (a f : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hf : ∀ i, 1 + a i ≤ f i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i _ => ha i)
    have h1 : (1 + a j) * (1 + ∑ i ∈ s, a i) ≤ f j * ∏ i ∈ s, f i :=
      mul_le_mul (hf j) ih (by linarith) (by have := ha j; have := hf j; linarith)
    nlinarith [ha j]

private lemma klNotKurtz_product_aux_factor
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    1 + (1 / 2 : ℝ) * (q - 1 / 2) ^ 2 ≤ (1 / 2 + q) * ((q + 1 / 2) / (2 * q)) := by
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (q - 1 / 2), mul_nonneg (sq_nonneg (q - 1 / 2)) (sub_nonneg.2 hq1)]

private lemma klNotKurtz_product_aux_massR_pos (x : BitString) :
    0 < massR (independentTrials klNotML_my_p
      klNotML_my_p_le_one) x := by
  rw [massR_independentTrials]
  refine Finset.prod_pos (fun i _ => ?_)
  have := klNotKurtz_product_aux_p i
  split_ifs
  · exact this.1
  · linarith [this.2]

private lemma klNotKurtz_product_aux_cond (y : BitString)
    (b : Bool) :
    condProb (cantorMass (independentTrials klNotML_my_p
      klNotML_my_p_le_one)) y b =
      if b then (klNotML_my_p y.length : ℝ)
      else 1 - (klNotML_my_p y.length : ℝ) := by
  have hmass := klNotKurtz_product_aux_massR_pos y
  have hne : cantorMass (independentTrials klNotML_my_p
      klNotML_my_p_le_one) y ≠ 0 := by
    intro h
    simp [massR, h] at hmass
  have h1 := condOne_independentTrials klNotML_my_p
    klNotML_my_p_le_one hne
  have h2 := condProb_cantorMass_add_eq_one (independentTrials
    klNotML_my_p
    klNotML_my_p_le_one) hne
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    unfold condOne at h1
    linarith
  · simpa [condOne] using h1

private lemma klNotKurtz_product_aux_cond_unif (y : BitString)
    (b : Bool) : condProb (cantorMass uniformMeasure) y b = 1 / 2 := by
  have h := massR_uniformMeasure (y ++ [b])
  have h' := massR_uniformMeasure y
  unfold condProb
  change massR uniformMeasure (y ++ [b]) / massR uniformMeasure y = _
  rw [h, h']
  simp only [List.length_append, List.length_singleton, pow_succ]
  have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ y.length := by positivity
  field_simp

/-- Step 3 of the proof of `exists_isMisesKLRandom_not_isKurtzRandom`: for every string
`x` the product of the two bookmaker capitals (against the uniform and the biased measure) is at
least
`1 + (1/2) ∑_{i < |x|} (my_p i - 1/2)²`.  Each factor of the product is
`1 + (q - 1/2)²/(2q) ≥ 1 + (q - 1/2)²/2` with `q ∈ {my_p i, 1 - my_p i}`. -/
private lemma klNotKurtz_product (x : BitString) :
    1 + (1 / 2 : ℝ) * ∑ i ∈ Finset.range x.length,
        ((klNotML_my_p i : ℝ) - 1 / 2) ^ 2 ≤
      bookmakerCapital uniformMeasure (independentTrials
          klNotML_my_p
        klNotML_my_p_le_one) x *
      bookmakerCapital (independentTrials klNotML_my_p
        klNotML_my_p_le_one) uniformMeasure x := by
  unfold bookmakerCapital
  rw [← Finset.prod_mul_distrib]
  have hmain := klNotKurtz_product_aux_one_add_sum_le
    (Finset.univ : Finset (Fin x.length))
    (fun i => (1 / 2 : ℝ) *
      ((klNotML_my_p i : ℝ) - 1 / 2) ^ 2)
    (fun i => bookmakerFactor uniformMeasure (independentTrials
        klNotML_my_p
        klNotML_my_p_le_one) (x.take i) x[i] *
      bookmakerFactor (independentTrials klNotML_my_p
        klNotML_my_p_le_one) uniformMeasure (x.take i) x[i])
    (fun i => by positivity) (fun i => ?_)
  · rw [← Fin.sum_univ_eq_sum_range
      (fun i => ((klNotML_my_p i : ℝ) - 1 / 2) ^ 2) x.length,
      Finset.mul_sum]
    exact hmain
  · have hlen : (x.take i).length = i := by simp
    unfold bookmakerFactor
    rw [klNotKurtz_product_aux_cond_unif,
      klNotKurtz_product_aux_cond, hlen]
    obtain ⟨hp0, hp1⟩ := klNotKurtz_product_aux_p i
    cases hb : x[i]
    · simp only [Bool.false_eq_true, ite_false]
      have := klNotKurtz_product_aux_factor
        (q := 1 - (klNotML_my_p i : ℝ)) (by linarith)
        (by linarith)
      have e : (1 - (klNotML_my_p i : ℝ) - 1 / 2) ^ 2 =
          ((klNotML_my_p i : ℝ) - 1 / 2) ^ 2 := by ring
      rw [e] at this
      have e2 : (1 / 2 + (1 - (klNotML_my_p i : ℝ))) /
          (2 * (1 / 2)) = 1 / 2 + (1 - (klNotML_my_p i : ℝ)) :=
              by
        field_simp
      rw [e2]
      linarith
    · simp only [ite_true]
      have := klNotKurtz_product_aux_factor
        (q := (klNotML_my_p i : ℝ)) hp0 hp1.le
      have e2 : (1 / 2 + (klNotML_my_p i : ℝ)) /
          (2 * (1 / 2)) = 1 / 2 + (klNotML_my_p i : ℝ) := by
        field_simp
      rw [e2]
      linarith

private lemma klNotKurtz_growth_aux_sq (i : ℕ) :
    ((klNotML_my_p i : ℝ) - 1 / 2) ^ 2 = 1 / ((i : ℝ) + 5) :=
        by
  have hpos : (0 : ℝ) < (i : ℝ) + 5 := by positivity
  have hs2 : (2 : ℝ) ≤ Real.sqrt ((i : ℝ) + 5) := by
    apply Real.le_sqrt_of_sq_le
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith
  have hspos : (0 : ℝ) < Real.sqrt ((i : ℝ) + 5) := by linarith
  have hle : 1 / Real.sqrt ((i : ℝ) + 5) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hspos (by norm_num)]
    linarith
  have hc : (klNotML_my_p i : ℝ)
      = 1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) := by
    unfold klNotML_my_p
    rw [Real.coe_toNNReal _ (by linarith)]
  rw [hc]
  have : (1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) - 1 / 2) ^ 2
      = ((Real.sqrt ((i : ℝ) + 5)) ^ 2)⁻¹ := by
    rw [show (1 / 2 - 1 / Real.sqrt ((i : ℝ) + 5) - 1 / 2) = -(1 / Real.sqrt ((i : ℝ) + 5)) by ring]
    rw [neg_sq, div_pow, one_pow, one_div]
  rw [this, Real.sq_sqrt hpos.le, one_div]

private lemma klNotKurtz_growth_aux_harm (n : ℕ) :
    Real.log ((n : ℝ) + 5) - Real.log 5 ≤ ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 5) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h0 : (0 : ℝ) < (n : ℝ) + 5 := by positivity
    have h1 : Real.log (((n : ℝ) + 6) / ((n : ℝ) + 5)) ≤ ((n : ℝ) + 6) / ((n : ℝ) + 5) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) h0.ne'] at h1
    have h2 : ((n : ℝ) + 6) / ((n : ℝ) + 5) - 1 = 1 / ((n : ℝ) + 5) := by
      field_simp; ring
    have h3 : (((n + 1 : ℕ) : ℝ) + 5) = (n : ℝ) + 6 := by push_cast; ring
    rw [h3]
    linarith

private lemma klNotKurtz_growth_aux_log5 :
    Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

/-- Step 4 of the proof of `exists_isMisesKLRandom_not_isKurtzRandom`: the partial sums
`1 + (1/2) ∑_{i<n} (my_p i - 1/2)²` (here `(my_p i - 1/2)² = 1/(i+5)`, a harmonic sum) dominate,
after
division by any fixed `C > 0`, a computable non-decreasing unbounded integer function. -/
private lemma klNotKurtz_growth {C : ℝ} (hC : 0 < C) :
    ∃ g : ℕ → ℕ, IsComputableGrowth g ∧ ∀ n, (g n : ℝ) * C ≤
      1 + (1 / 2 : ℝ) * ∑ i ∈ Finset.range n,
        ((klNotML_my_p i : ℝ) - 1 / 2) ^ 2 := by
  set K : ℕ := ⌈4 * C⌉₊ + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos _
  have hKR : 4 * C < (K : ℝ) := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (4 * C)]
  refine ⟨fun n => Nat.log 2 (n + 5) / K, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (Primrec.nat_div.comp
      (primrec_natLogTwo.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 5)))
      (Primrec.const K)).to_comp
  · intro a b hab
    exact Nat.div_le_div_right (Nat.log_mono_right (by omega))
  · intro B
    refine ⟨2 ^ (K * B), ?_⟩
    have h1 : K * B ≤ Nat.log 2 (2 ^ (K * B) + 5) :=
      Nat.le_log_of_pow_le (by norm_num) (by omega)
    change B ≤ Nat.log 2 (2 ^ (K * B) + 5) / K
    rw [Nat.le_div_iff_mul_le hKpos]
    linarith
  · intro n
    simp only
    rw [Finset.sum_congr rfl (fun i _ =>
      klNotKurtz_growth_aux_sq i)]
    have hh := klNotKurtz_growth_aux_harm n
    have h5 := klNotKurtz_growth_aux_log5
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    set L : ℝ := Real.log ((n : ℝ) + 5) with hL
    have hn5 : (1 : ℝ) < (n : ℝ) + 5 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hL0 : 0 ≤ L := Real.log_nonneg hn5.le
    have hgl : ((Nat.log 2 (n + 5) / K : ℕ) : ℝ) ≤ (Nat.log 2 (n + 5) : ℝ) / K :=
      Nat.cast_div_le
    have hnl : (Nat.log 2 (n + 5) : ℝ) ≤ L / Real.log 2 := by
      have := Real.natLog_le_logb (n + 5) 2
      rw [Real.logb] at this
      push_cast at this
      exact this
    have hl2pos : 0 < Real.log 2 := by linarith
    have hKpos' : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hg : ((Nat.log 2 (n + 5) / K : ℕ) : ℝ) ≤ L / (Real.log 2 * K) := by
      calc _ ≤ (Nat.log 2 (n + 5) : ℝ) / K := hgl
        _ ≤ (L / Real.log 2) / K := by gcongr
        _ = L / (Real.log 2 * K) := by rw [div_div]
    have hg2 : ((Nat.log 2 (n + 5) / K : ℕ) : ℝ) * C ≤ L / 2 := by
      calc _ ≤ L / (Real.log 2 * K) * C := by gcongr
        _ ≤ L / (Real.log 2 * K) * (K / 4) := by gcongr; linarith
        _ = L / (4 * Real.log 2) := by field_simp
        _ ≤ L / 2 := by
          apply div_le_div_of_nonneg_left hL0 (by norm_num); linarith
    change ((Nat.log 2 (n + 5) / K : ℕ) : ℝ) * C ≤ _
    nlinarith

/-- **SUV Problem 280, p. 309.**  There is a Mises-Kolmogorov-Loveland random sequence with limit
frequency `1/2` that is not even Kurtz random. -/
theorem exists_isMisesKLRandom_not_isKurtzRandom :
    ∃ w, IsMisesKLRandom w ∧ ¬ IsKurtzRandom uniformMeasure w := by
  obtain ⟨w, hw⟩ := klNotML_random_witness
  refine ⟨w, ?_, ?_⟩
  · have hconv : ConvergesComputably klNotML_my_p (1 / 2) :=
      ⟨klNotML_computable,
        klNotML_converges⟩
    exact isMisesKLRandomAt_of_isMartinLofRandom
      klNotML_my_p_le_one (by norm_num) (by norm_num) hconv hw
  · set P := independentTrials klNotML_my_p
      klNotML_my_p_le_one with hP
    have hμ : IsComputableMeasure uniformMeasure := isComputableMeasure_uniform
    have hposU : ∀ x, 0 < cantorMass uniformMeasure x := by
      intro x
      rw [cantorMass_uniformMeasure]
      exact ENNReal.pow_pos (by norm_num) _
    have hposP := klNotKurtz_pos
    obtain ⟨C, hC⟩ := klNotKurtz_bounded hw
    have hC0 : 0 < C := by
      have h1 := hC 0
      have h2 : bookmakerCapital P uniformMeasure (cantorPrefix w 0) = 1 :=
        isMartingale_bookmakerCapital_nil _ _
      linarith
    obtain ⟨g, hg, hgle⟩ := klNotKurtz_growth hC0
    refine (not_isKurtzRandom_iff_exists_growth hμ hposU w).mpr ?_
    refine ⟨bookmakerCapital uniformMeasure P, g,
      (isMartingale_bookmakerCapital hposU hposP).toIsFairCapital,
      (summable_sq_condOne_sub_of_isComputablyRandom_comp hμ
        (isComputableMeasure_independentTrials
          klNotML_my_p_le_one
          klNotML_computable) hposU hposP).1, hg, ?_⟩
    intro n
    have h3 := klNotKurtz_product (cantorPrefix w n)
    rw [cantorPrefix_length] at h3
    have h4 := hgle n
    have hB2 := hC n
    have hB2nn : 0 ≤ bookmakerCapital P uniformMeasure (cantorPrefix w n) :=
      isMartingale_bookmakerCapital_nonneg _ _ _
    have hB1nn : 0 ≤ bookmakerCapital uniformMeasure P (cantorPrefix w n) :=
      isMartingale_bookmakerCapital_nonneg _ _ _
    by_contra hlt
    push Not at hlt
    have : bookmakerCapital uniformMeasure P (cantorPrefix w n) *
        bookmakerCapital P uniformMeasure (cantorPrefix w n) <
        (g n : ℝ) * C := by
      calc _ ≤ bookmakerCapital uniformMeasure P (cantorPrefix w n) * C :=
            mul_le_mul_of_nonneg_left hB2 hB1nn
        _ < (g n : ℝ) * C := mul_lt_mul_of_pos_right hlt hC0
    linarith

end Kolmogorov.FrequencyGames
