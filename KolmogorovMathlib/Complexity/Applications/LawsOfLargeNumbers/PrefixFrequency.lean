/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LibraryAPI
import KolmogorovMathlib.MonotoneComplexity.ArithmeticCoding
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import KolmogorovMathlib.Solomonoff.Domination
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations.DyadicEnumeration
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import KolmogorovMathlib.MonotoneComplexity.PlainMonotoneComparison
import KolmogorovMathlib.Entropy.Complexity.Frequencies
import KolmogorovMathlib.Entropy.Inequalities.Fano
import KolmogorovMathlib.Complexity.PairComplexity.LogarithmicTerms.ConditionalBounds
import KolmogorovMathlib.Solomonoff.KL

/-!
# Prefix Frequency

For a binary sequence `w`, `prefixFreq w n` is the frequency of ones in its `n`-bit prefix. The
module contains two results of the book by Shen, Uspensky and Vereshchagin on the law of large
numbers for sequences of high complexity.

* `tendsto_prefixFreq_of_plainK_isLittleO` (Theorem 155): if `C((ω)_n) = n + o(n)`, then the
  frequency of ones in the prefixes tends to `1/2`. The proof bounds the complexity of a prefix
  by the entropy of its letter frequencies, so that the binary entropy of the frequency tends to
  `1`, and uses the strict maximum of the binary entropy at `1/2`.
* `prefixFreq_sub_half_isBigO` (p. 240): for a Martin-Löf random sequence,
  `|p_n - 1/2| = O(√(log n / n))`. The proof uses the Taylor expansion of the binary entropy at
  `1/2`, `binaryEntropy_half_add_isLittleO`.
-/

namespace Kolmogorov.Applications

open Filter Topology Asymptotics

/-- The frequency of ones in the `n`-bit prefix, as a real. -/
noncomputable def prefixFreq (w : CantorSeq) (n : ℕ) : ℝ := (freqOne w n : ℝ)


private def tendsto_prefixFreq_of_plainK_isLittleO_entropy_keepEven (l : List Bool) :
    List Bool :=
  (List.range (l.length / 2)).map (fun i => List.getD l (2 * i) false)

private lemma tendsto_prefixFreq_of_plainK_isLittleO_keepEven_computable :
    Computable tendsto_prefixFreq_of_plainK_isLittleO_entropy_keepEven := by
  let f1 : List Bool → List ℕ := fun l => List.range (l.length / 2)
  have h1 : Computable f1 :=
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))).to_comp
  have h2 : Computable₂ (fun (l : List Bool) (i : ℕ) => List.getD l (2 * i) false) :=
    (Primrec.list_getD false |>.comp Primrec.fst (Primrec.nat_mul.comp (Primrec.const 2)
        Primrec.snd)).to₂.to_comp
  exact Computable.list_map h1 h2

private lemma tendsto_prefixFreq_of_plainK_isLittleO_keepEven_finWordBits_bool_alphabetCode
    (b : Bool) : alphabetCode Bool b = [b, false] := by
  cases b
  · rfl
  · rfl

private lemma prefixFreq_flatten_alphabetCode_length
    (w : List Bool) : ((w.map (alphabetCode Bool)).flatten).length = w.length * 2 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.map_cons, List.flatten_cons,
      tendsto_prefixFreq_of_plainK_isLittleO_keepEven_finWordBits_bool_alphabetCode,
      List.length_append, List.length_cons, List.length_nil, ih]
    omega

private lemma prefixFreq_flatten_alphabetCode_getD
    (w : List Bool) (i : ℕ) (hi : i < w.length) :
    ((w.map (alphabetCode Bool)).flatten).getD (2 * i) false = w[i] := by
  induction w generalizing i with
  | nil => contradiction
  | cons b w ih =>
    cases i with
    | zero =>
      simp [tendsto_prefixFreq_of_plainK_isLittleO_keepEven_finWordBits_bool_alphabetCode]
    | succ i =>
      have hi_w : i < w.length := by
        simp only [List.length_cons] at hi
        omega
      specialize ih i hi_w
      simp only [List.map_cons, List.flatten_cons,
        tendsto_prefixFreq_of_plainK_isLittleO_keepEven_finWordBits_bool_alphabetCode]
      have : 2 * (i + 1) = 2 * i + 2 := by omega
      rw [this]
      have h1 : ([b, false] ++ (List.map (alphabetCode Bool) w).flatten).getD (2 * i + 2) false =
        ((List.map (alphabetCode Bool) w).flatten).getD (2 * i) false := by
        rfl
      rw [h1, ih]
      rfl

/-- Step 1 of the proof of `tendsto_prefixFreq_of_plainK_isLittleO_entropy`:
the prefix is recovered from it by the computable map that keeps every other bit. -/
private lemma tendsto_prefixFreq_of_plainK_isLittleO_keepEven_finWordBits
    {n : ℕ} (v : Fin n → Bool) :
    tendsto_prefixFreq_of_plainK_isLittleO_entropy_keepEven (finWordBits Bool v) = List.ofFn
        v := by
  unfold finWordBits wordBits Code.encodeWord
      tendsto_prefixFreq_of_plainK_isLittleO_entropy_keepEven
  rw [prefixFreq_flatten_alphabetCode_length]
  have : (List.ofFn v).length * 2 / 2 = (List.ofFn v).length := by omega
  rw [this]
  exact List.ext_get (by simp) (by
    intro i h1 h2
    have h3 : (List.map (fun i => (List.map (alphabetCode Bool) (List.ofFn v)).flatten.getD (2 * i)
                                    false) (List.range (List.ofFn v).length)).get ⟨i, h1⟩ =
      ((List.map (alphabetCode Bool) (List.ofFn v)).flatten).getD (2 * i) false := by
      simp [List.getElem_map]
    rw [h3]
    exact prefixFreq_flatten_alphabetCode_getD (List.ofFn v) i h2
  )

private lemma tendsto_prefixFreq_of_plainK_isLittleO_plainK_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c1 : ℕ, ∀ n (v : Fin n → Bool), plainK V (List.ofFn v) ≤ plainK V (finWordBits Bool v) + c1 :=
        by
  obtain ⟨c, hc⟩ := plainK_map_le V hV tendsto_prefixFreq_of_plainK_isLittleO_entropy_keepEven
    tendsto_prefixFreq_of_plainK_isLittleO_keepEven_computable
  use c
  intro n v
  have h := hc (finWordBits Bool v)
  rw [tendsto_prefixFreq_of_plainK_isLittleO_keepEven_finWordBits v] at h
  exact h

/-- Step 2 of the proof of `tendsto_prefixFreq_of_plainK_isLittleO_entropy`:
$H$ is $h(p_n)$. -/
private lemma tendsto_prefixFreq_of_plainK_isLittleO_entropyDist_eq_count_ofFn_eq_freq {α : Type*}
    [DecidableEq α] :
    ∀ {N : ℕ} (w : Fin N → α) (a : α), (List.ofFn w).count a = freq w a := by
  intro N
  induction N with
  | zero => intro w a; simp [freq]
  | succ N ih =>
      intro w a
      rw [List.ofFn_succ]
      simp only [List.count_cons]
      rw [ih]
      unfold freq
      have h1 : (Finset.univ.filter fun i : Fin (N + 1) => w i = a).card = (∑ i : Fin (N + 1),
          if w i = a then 1 else 0) := by
        rw [Finset.sum_ite]
        simp
      have h2 : (Finset.univ.filter fun i : Fin N => w (Fin.succ i) = a).card =
          (∑ i : Fin N, if w (Fin.succ i) = a then 1 else 0) := by
        rw [Finset.sum_ite]
        simp
      rw [h1, h2, Fin.sum_univ_succ]
      by_cases h : w 0 = a
      · have : (w 0 == a) = true := by
          rw [beq_iff_eq]
          exact h
        rw [this]
        dsimp
        simp only [h, ↓reduceIte]
        exact add_comm _ _
      · have h_beq : (w 0 == a) = false := by
          cases h_beq_cases : (w 0 == a)
          · rfl
          · have : w 0 = a := by rwa [← beq_iff_eq]
            exact False.elim (h this)
        rw [h_beq]
        dsimp
        simp [h]

private lemma tendsto_prefixFreq_of_plainK_isLittleO_entropyDist_eq
    (w : CantorSeq) (n : ℕ) :
    entropyDist (fun a : Bool => (freq (fun i : Fin n => w i) a : ℝ) / n) = binaryEntropy
        (prefixFreq w n) := by
  have H : entropyDist (fun a : Bool => (freq (fun i : Fin n => w i) a : ℝ) / n) = 
      negMulLog2 ((freq (fun i : Fin n => w i) true : ℝ) / n) + 
      negMulLog2 ((freq (fun i : Fin n => w i) false : ℝ) / n) := by
    dsimp [entropyDist]
    have H_sum := Fintype.sum_bool (fun a : Bool => negMulLog2 ((freq (fun i : Fin n => w i) a : ℝ)
                                                      / n))
    change ∑ a : Bool, negMulLog2 ((freq (fun i : Fin n => w i) a : ℝ) / n) = negMulLog2
        ((freq (fun i : Fin n => w i) true : ℝ) / n) + negMulLog2
        ((freq (fun i : Fin n => w i) false : ℝ) / n)
    rw [H_sum]
  rw [H]
  dsimp [binaryEntropy, prefixFreq, freqOne]
  by_cases hn : n = 0
  · simp [hn, negMulLog2]
  · have h1 : (freq (fun i : Fin n => w i) true : ℝ) = ((cantorPrefix w n).count true : ℝ) := by
      have h : freq (fun i : Fin n => w i) true = (List.ofFn (fun i : Fin n => w i)).count true :=
          (tendsto_prefixFreq_of_plainK_isLittleO_entropyDist_eq_count_ofFn_eq_freq _ _).symm
      have hw : cantorPrefix w n = List.ofFn (fun (i : Fin n) => w i) := rfl
      rw [hw, ← h]
    have h2 : (freq (fun i : Fin n => w i) false : ℝ) = n - ((cantorPrefix w n).count true : ℝ) :=
        by
      have H_sum := sum_freq (fun i : Fin n => w i)
      have H_sum2 : ∑ a : Bool, freq (fun i : Fin n => w i) a = freq (fun i : Fin n => w i) true +
          freq (fun i : Fin n => w i) false := Fintype.sum_bool _
      rw [H_sum2] at H_sum
      have h_false : (freq (fun i : Fin n => w i) false : ℝ) = n - (freq (fun i : Fin n => w i) true
          : ℝ) := by 
        have h_sum' : (freq (fun (i : Fin n) => w ↑i) true : ℝ) + (freq (fun (i : Fin n) => w ↑i)
            false : ℝ) = (n : ℝ) := by exact_mod_cast H_sum
        linarith
      rw [h_false, h1]
    rw [h1, h2]
    have h3 : (n - ↑(List.count true (cantorPrefix w n))) / (n : ℝ) = 1 -
        ↑(List.count true (cantorPrefix w n)) / (n : ℝ) := by
      rw [sub_div]
      have : (n : ℝ) / n = 1 := div_self (by exact_mod_cast hn)
      rw [this]
    rw [h3]
    push_cast
    rfl

/-- Step 3 of the proof of `tendsto_prefixFreq_of_plainK_isLittleO_entropy`:
Altogether, squeeze theorem. -/
private lemma tendsto_prefixFreq_of_plainK_isLittleO_asymptotics
    {p : ℕ → ℝ} (C : ℕ → ℝ)
    (hC : (fun n => C n - n) =o[atTop] (fun n => (n : ℝ))) (c c1 : ℝ)
    (h_ineq : ∀ n ≥ 1, C n ≤ n * binaryEntropy (p n) + (2 + 1) * Real.logb 2 n + c + c1) :
    Tendsto (fun n => binaryEntropy (p n)) atTop (𝓝 1) := by
  have h_upper (x : ℝ) : binaryEntropy x ≤ 1 := by
    have h_eq : binaryEntropy x = Real.binEntropy x / Real.log 2 := by
      unfold binaryEntropy negMulLog2
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      ring
    rw [h_eq, div_le_one (Real.log_pos (by norm_num))]
    exact Real.binEntropy_le_log_two
  have h_log : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have h_logb : Tendsto (fun n : ℕ => Real.logb 2 n / n) atTop (𝓝 0) := by
    have h := h_log.tendsto_div_nhds_zero.div_const (Real.log 2)
    rw [zero_div] at h
    refine h.congr (fun n => ?_)
    unfold Real.logb
    ring
  have h_error : Tendsto
      (fun n : ℕ => ((2 + 1) * Real.logb 2 n + c + c1) / n) atTop (𝓝 0) := by
    have h := ((h_logb.const_mul (2 + 1)).add
      (tendsto_const_div_atTop_nhds_zero_nat c)).add
      (tendsto_const_div_atTop_nhds_zero_nat c1)
    simpa only [mul_zero, zero_add, ← mul_div_assoc, ← add_div] using h
  have h_lower : Tendsto
      (fun n : ℕ => 1 + (C n - n) / n -
        ((2 + 1) * Real.logb 2 n + c + c1) / n) atTop (𝓝 1) := by
    simpa only [add_zero, sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add hC.tendsto_div_nhds_zero).sub h_error
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower tendsto_const_nhds ?_
    (Eventually.of_forall fun n => h_upper (p n))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    1 + (C n - n) / n - ((2 + 1) * Real.logb 2 n + c + c1) / n =
        (C n - ((2 + 1) * Real.logb 2 n + c + c1)) / n := by
          field_simp
          ring
    _ ≤ binaryEntropy (p n) := (div_le_iff₀ hn_pos).mpr (by linarith [h_ineq n hn])

/-- Step 1 of the proof of `tendsto_prefixFreq_of_plainK_isLittleO`:
Obtain that `binaryEntropy(prefixFreq w n) -> 1` as `n -> ∞`. -/
private theorem tendsto_prefixFreq_of_plainK_isLittleO_entropy
    (V : Map) (hV : isOptimalConditional V) {w : CantorSeq}
    (hC : (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) - n) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    Tendsto (fun n : ℕ => binaryEntropy (prefixFreq w n)) atTop (𝓝 1) := by
  have h_bound := exists_plainK_word_le_entropy_freq_card_logb Bool V hV (ε := 1) (by norm_num)
  obtain ⟨c, hc⟩ := h_bound
  obtain ⟨c1, hc1⟩ := tendsto_prefixFreq_of_plainK_isLittleO_plainK_le V hV
  have h_ineq : ∀ n ≥ 1, ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤
      n * binaryEntropy (prefixFreq w n) + (2 + 1) * Real.logb 2 n + (c : ℝ) + (c1 : ℝ) := by
    intro n hn
    have h1 := hc1 n (fun i => w i)
    have h2 := hc n (fun i => w i)
    have h_cantor : cantorPrefix w n = List.ofFn (fun i : Fin n => w i) := rfl
    have hk_le : (plainK V (cantorPrefix w n) : ENat) ≤ plainK V
        (finWordBits Bool (fun i : Fin n => w i)) + (c1 : ENat) := by
      rw [h_cantor]
      exact h1
    have hk_le_real : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤
        ((plainK V (finWordBits Bool (fun i : Fin n => w i))).toNat : ℝ) + (c1 : ℝ) := by
      have hk_le' : plainK V (finWordBits Bool (fun i : Fin n => w i)) + (c1 : ENat) =
        (((plainK V (finWordBits Bool (fun i : Fin n => w i))).toNat + c1 : ℕ) : ENat) := by
          push_cast
          have htop : plainK V (finWordBits Bool (fun i : Fin n => w i)) ≠ ⊤ := by
            exact plainK_ne_top V hV _
          rw [ENat.natCast_toNat htop]
      rw [hk_le'] at hk_le
      have h3 := ENat.toNat_le_of_le_natCast
          (n := (plainK V (finWordBits Bool (fun i : Fin n => w i))).toNat + c1) hk_le
      exact_mod_cast h3
    have h2' : ((plainK V (finWordBits Bool (fun i : Fin n => w i))).toNat : ℝ) ≤
        (n : ℝ) * entropyDist (fun a : Bool => (freq (fun i : Fin n => w i) a : ℝ) / n) +
        ((Fintype.card Bool : ℝ) + 1) * Real.logb 2 n + (c : ℝ) := h2
    have H : entropyDist (fun a : Bool => (freq (fun i : Fin n => w i) a : ℝ) / n) = binaryEntropy
        (prefixFreq w n) :=
      tendsto_prefixFreq_of_plainK_isLittleO_entropyDist_eq w n
    rw [H] at h2'
    have card_bool : (Fintype.card Bool : ℝ) = 2 := rfl
    rw [card_bool] at h2'
    linarith
  exact tendsto_prefixFreq_of_plainK_isLittleO_asymptotics
    (fun n => ((plainK V (cantorPrefix w n)).toNat : ℝ)) hC c c1 h_ineq

/-- The binary entropy function equals the natural-logarithm entropy divided by `log 2`. -/
lemma tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity_h_eq (x : ℝ) :
    binaryEntropy x = Real.binEntropy x / Real.log 2 := by
  unfold binaryEntropy negMulLog2
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

private lemma tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity_continuous :
    Continuous binaryEntropy := by
  have : binaryEntropy = fun x => Real.binEntropy x / Real.log 2 := by
    ext
    rw [tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity_h_eq]
  rw [this]
  exact Real.binEntropy_continuous.div_const _

/-- Step 2 of the proof of `tendsto_prefixFreq_of_plainK_isLittleO`:
If `binaryEntropy(p n) -> 1` for `0 ≤ p n ≤ 1`, then `p n -> 1/2`. -/
theorem tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (h : Tendsto (fun n => binaryEntropy (p n)) atTop (𝓝 1)) :
    Tendsto p atTop (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let K := (Set.Icc (0:ℝ) 1) ∩ {x : ℝ | ε ≤ |x - 1/2|}
  have hK_compact : IsCompact K := by
    apply IsCompact.inter_right isCompact_Icc
    have h_closed : IsClosed {x : ℝ | ε ≤ |x - 1/2|} := by
      exact isClosed_le continuous_const (Continuous.norm (Continuous.sub continuous_id
          continuous_const))
    exact h_closed
  by_cases hK : K.Nonempty
  · obtain ⟨x0, hx0, h_max⟩ := hK_compact.exists_isMaxOn hK
      tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity_continuous.continuousOn
    have h_lt : binaryEntropy x0 < 1 := by
      rw [tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity_h_eq x0]
      rw [div_lt_one (Real.log_pos (by norm_num))]
      apply (Real.binEntropy_lt_log_two (p := x0)).mpr
      intro h_eq_half
      have : ε ≤ |x0 - 1/2| := hx0.2
      rw [h_eq_half] at this
      norm_num at this
      linarith
    rw [Metric.tendsto_atTop] at h
    let m := binaryEntropy x0
    have hm1 : m < 1 := h_lt
    have hd : 0 < 1 - m := sub_pos.mpr hm1
    obtain ⟨N, hN⟩ := h (1 - m) hd
    use N
    intro n hn
    specialize hN n hn
    have h_not_in_K : p n ∉ K := by
      intro h_in_K
      have : binaryEntropy (p n) ≤ m := h_max h_in_K
      have : |binaryEntropy (p n) - 1| < 1 - m := hN
      have : 1 - binaryEntropy (p n) < 1 - m := by
        calc 1 - binaryEntropy (p n) ≤ |1 - binaryEntropy (p n)| := le_abs_self _
             _ = |binaryEntropy (p n) - 1| := abs_sub_comm _ _
             _ < 1 - m := this
      linarith
    have hpn_Icc : p n ∈ Set.Icc (0:ℝ) 1 := hp n
    have : dist (p n) (1 / 2) = |p n - 1 / 2| := rfl
    rw [this]
    have : ε > |p n - 1 / 2| := by
      contrapose! h_not_in_K
      exact ⟨hpn_Icc, h_not_in_K⟩
    exact this
  · use 0
    intro n _
    have hpn_Icc : p n ∈ Set.Icc (0:ℝ) 1 := hp n
    have : dist (p n) (1 / 2) = |p n - 1 / 2| := rfl
    rw [this]
    have : ε > |p n - 1 / 2| := by
      contrapose! hK
      have hK_mem : p n ∈ K := ⟨hpn_Icc, hK⟩
      exact Set.nonempty_of_mem hK_mem
    exact this

/-- Step 3 of the proof of `tendsto_prefixFreq_of_plainK_isLittleO`:
The frequency of ones in any prefix of a Cantor sequence is always between 0 and 1. -/
private theorem tendsto_prefixFreq_of_plainK_isLittleO_bounds (w : CantorSeq) (n : ℕ) :
    0 ≤ prefixFreq w n ∧ prefixFreq w n ≤ 1 := by
  dsimp [prefixFreq, freqOne]
  push_cast
  constructor
  · positivity
  · by_cases hn : n = 0
    · simp [hn]
    · have h1 : ((cantorPrefix w n).count true : ℝ) ≤ n := by
        have H : (cantorPrefix w n).count true ≤ (cantorPrefix w n).length := List.count_le_length
        have H2 : (cantorPrefix w n).length = n := by
          dsimp [cantorPrefix]
          simp
        rw [H2] at H
        exact_mod_cast H
      have h2 : (0 : ℝ) < n := by positivity
      exact (div_le_one h2).mpr h1

/-- **SUV Theorem 155, p. 239.**  If `C((ω)_n) = n + o(n)`, the frequency of ones in `(ω)_n`
converges to `1/2`. -/
theorem tendsto_prefixFreq_of_plainK_isLittleO (V : Map) (hV : isOptimalConditional V)
    {w : CantorSeq}
    (hC : (fun n : ℕ => ((plainK V (cantorPrefix w n)).toNat : ℝ) - n) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    Tendsto (prefixFreq w) atTop (𝓝 (1 / 2)) := by
  exact tendsto_prefixFreq_of_plainK_isLittleO_entropy_rigidity (prefixFreq w)
    (tendsto_prefixFreq_of_plainK_isLittleO_bounds w)
    (tendsto_prefixFreq_of_plainK_isLittleO_entropy V hV hC)


/-- Step 1 of the proof of `binaryEntropy_half_add_isLittleO`: `binaryEntropy` is `C^2` on
`(0, 1)`. -/
private theorem binaryEntropy_half_add_isLittleO_smooth :
    ContDiffOn ℝ 2 binaryEntropy (Set.Ioo 0 1) := by
  unfold binaryEntropy negMulLog2
  have : (fun x => Real.negMulLog x / Real.log 2 + Real.negMulLog (1 - x) / Real.log 2) =
      (fun x => Real.negMulLog x * (Real.log 2)⁻¹ + Real.negMulLog (1 - x) * (Real.log 2)⁻¹) := by
    ext x
    ring
  rw [this]
  apply ContDiffOn.add
  · apply ContDiffOn.mul
    · have h_negmul : Real.negMulLog = (fun x => -x * Real.log x) := rfl
      rw [h_negmul]
      have : (fun x => -x * Real.log x) = (fun x => -(x * Real.log x)) := by ext x; ring
      rw [this]
      apply ContDiffOn.neg
      apply ContDiffOn.mul
      · exact contDiffOn_id
      · apply ContDiffOn.log contDiffOn_id
        intro x hx
        exact ne_of_gt hx.1
    · exact contDiffOn_const
  · apply ContDiffOn.mul
    · have h_negmul : (fun x => Real.negMulLog (1 - x)) = (fun x => -(1 - x) * Real.log (1 - x)) :=
        rfl
      rw [h_negmul]
      have : (fun x => -(1 - x) * Real.log (1 - x)) = (fun x => -((1 - x) * Real.log (1 - x))) := by
        ext x; ring
      rw [this]
      apply ContDiffOn.neg
      apply ContDiffOn.mul
      · exact (contDiffOn_const (c:=1)).sub contDiffOn_id
      · apply ContDiffOn.log ((contDiffOn_const (c:=1)).sub contDiffOn_id)
        intro x hx
        have : 1 - x > 0 := sub_pos.mpr hx.2
        exact ne_of_gt this
    · exact contDiffOn_const

/-- Step 2 of the proof of `binaryEntropy_half_add_isLittleO`: The remainder of the Taylor
expansion of `binaryEntropy` at `1/2` is `o(δ^2)`. -/
private theorem binaryEntropy_half_add_isLittleO_remainder :
    (fun δ : ℝ => binaryEntropy (1 / 2 + δ) -
      taylorWithinEval binaryEntropy 2 (Set.Ioo 0 1) (1 / 2) (1 / 2 + δ)) =o[𝓝 0]
        (fun δ : ℝ => δ ^ 2) := by
  have h2 := @taylor_isLittleO _ _ _ binaryEntropy (1/2) 2 (Set.Ioo 0 1) (convex_Ioo 0 1)
      (by norm_num) binaryEntropy_half_add_isLittleO_smooth
  have h2' : (fun x => binaryEntropy x - taylorWithinEval binaryEntropy 2 (Set.Ioo 0 1) (1 / 2) x)
      =o[𝓝 (1 / 2)] fun x => (x - 1 / 2) ^ 2 := by
    have h_nhds : 𝓝 (1 / 2) = 𝓝[Set.Ioo (0:ℝ) 1] (1 / 2) := by
      symm
      rw [nhdsWithin_eq_nhds]
      exact Ioo_mem_nhds (by norm_num) (by norm_num)
    rw [h_nhds]
    exact h2
  have h3 : (fun δ : ℝ => binaryEntropy (1/2 + δ) - taylorWithinEval binaryEntropy 2 (Set.Ioo 0 1)
                            (1/2) (1/2 + δ)) =
    (fun x : ℝ => binaryEntropy x - taylorWithinEval binaryEntropy 2 (Set.Ioo 0 1) (1/2) x) ∘
        (fun δ : ℝ => 1/2 + δ) := rfl
  rw [h3]
  have h4 : Tendsto (fun δ : ℝ => 1/2 + δ) (𝓝 0) (𝓝 (1/2)) := by
    have : (fun δ : ℝ => 1/2 + δ) = (fun δ : ℝ => 1/2) + (fun δ : ℝ => δ) := rfl
    rw [this]
    have h4_aux : 𝓝 (1/2 : ℝ) = 𝓝 (1/2 + 0) := by norm_num
    rw [h4_aux]
    exact Tendsto.add tendsto_const_nhds tendsto_id
  have h5 := h2'.comp_tendsto h4
  have h6 : (fun x => (x - 1 / 2) ^ 2) ∘ (fun δ : ℝ => 1 / 2 + δ) = (fun δ => δ ^ 2) := by
    ext x; change (1 / 2 + x - 1 / 2) ^ 2 = x ^ 2; ring
  rw [h6] at h5
  exact h5

/-- Step 4 of the proof of `binaryEntropy_half_add_isLittleO`: The value of
`binaryEntropy` at `1/2` is `1`. -/
theorem binaryEntropy_half_add_isLittleO_value :
    binaryEntropy (1 / 2) = 1 := by
  unfold binaryEntropy negMulLog2
  unfold Real.negMulLog
  have : 1 - (1/2 : ℝ) = 1/2 := by ring
  rw [this]
  have : Real.log (1/2) = -Real.log 2 := by simp
  rw [this]
  have h1 : Real.log 2 ≠ 0 := by positivity
  have h2 : Real.log 2 / Real.log 2 = 1 := div_self h1
  calc
    -(1 / 2) * -Real.log 2 / Real.log 2 + -(1 / 2) * -Real.log 2 / Real.log 2 =
      1 / 2 * (Real.log 2 / Real.log 2) + 1 / 2 * (Real.log 2 / Real.log 2) := by ring
    _ = 1 / 2 * 1 + 1 / 2 * 1 := by rw [h2]
    _ = 1 := by ring

/-- Step 5 of the proof of `binaryEntropy_half_add_isLittleO`: The first derivative of
`binaryEntropy` at `1/2` is `0`. -/
private theorem binaryEntropy_half_add_isLittleO_first_derivative :
    derivWithin binaryEntropy (Set.Ioo 0 1) (1 / 2) = 0 := by
  have h1 : derivWithin binaryEntropy (Set.Ioo 0 1) (1/2) = deriv binaryEntropy (1/2) := by
    apply derivWithin_of_isOpen
    · exact isOpen_Ioo
    · exact ⟨by norm_num, by norm_num⟩
  rw [h1]
  have h2 : HasDerivAt (fun x => Real.negMulLog x / Real.log 2) ((-Real.log (1/2) - 1) / Real.log 2)
      (1/2) := by
    have : (fun x => Real.negMulLog x / Real.log 2) = (fun x => Real.negMulLog x * (Real.log 2)⁻¹)
        := by ext x; ring
    rw [this]
    have : (-Real.log (1/2) - 1) / Real.log 2 = (-Real.log (1/2) - 1) * (Real.log 2)⁻¹ := by ring
    rw [this]
    apply HasDerivAt.mul_const
    apply Real.hasDerivAt_negMulLog
    norm_num
  have h3 : HasDerivAt (fun x => Real.negMulLog (1 - x) / Real.log 2) ((-(-Real.log (1 - 1/2) - 1))
      / Real.log 2) (1/2) := by
    have : (fun x => Real.negMulLog (1 - x) / Real.log 2) =
        (fun x => Real.negMulLog (1 - x) * (Real.log 2)⁻¹) := by ext x; ring
    rw [this]
    have : (-(-Real.log (1 - 1/2) - 1)) / Real.log 2 = (-(-Real.log (1 - 1/2) - 1)) *
        (Real.log 2)⁻¹ := by ring
    rw [this]
    apply HasDerivAt.mul_const
    have hc : HasDerivAt (fun x : ℝ => 1 - x) (-1) (1/2) := by
      have : (fun (x : ℝ) => 1 - x) = (fun x : ℝ => -x + 1) := by ext x; ring
      rw [this]
      exact hasDerivAt_neg (1/2 : ℝ) |>.add_const 1
    have hn : HasDerivAt Real.negMulLog (-Real.log (1 - 1/2) - 1) (1 - 1/2) := by
      apply Real.hasDerivAt_negMulLog
      norm_num
    have h_comp := HasDerivAt.comp (1/2 : ℝ) hn hc
    have : ((-Real.log (1 - 1 / 2) - 1) * -1) = -(-Real.log (1 - 1 / 2) - 1) := by ring
    rw [this] at h_comp
    exact h_comp
  have h4 := HasDerivAt.add h2 h3
  have h5 : deriv binaryEntropy (1/2) = (-Real.log (1/2) - 1) / Real.log 2 +
      (-(-Real.log (1 - 1/2) - 1)) / Real.log 2 := by
    have h_eq : binaryEntropy = (fun x => Real.negMulLog x / Real.log 2) +
        (fun x => Real.negMulLog (1 - x) / Real.log 2) := by
      ext x
      unfold binaryEntropy negMulLog2
      rfl
    have : (fun x => (Real.negMulLog x) / Real.log 2) +
        (fun x => Real.negMulLog (1 - x) / Real.log 2) =
      (fun x => Real.negMulLog x / Real.log 2 + Real.negMulLog (1 - x) / Real.log 2) := rfl
    rw [h_eq, this]
    exact h4.deriv
  rw [h5]
  have h_log : Real.log (1/2) = -Real.log 2 := by simp
  have h_log2 : Real.log (1 - 1/2) = -Real.log 2 := by
    have : (1:ℝ) - 1/2 = 1/2 := by norm_num
    rw [this, h_log]
  rw [h_log, h_log2]
  ring

/-- Step 6 of the proof of `binaryEntropy_half_add_isLittleO`: The second derivative of
`binaryEntropy` at `1/2` is `-4 / ln 2`. -/
private theorem binaryEntropy_half_add_isLittleO_second_derivative :
    iteratedDerivWithin 2 binaryEntropy (Set.Ioo 0 1) (1 / 2) = -4 / Real.log 2 := by
  have h1 : iteratedDerivWithin 2 binaryEntropy (Set.Ioo 0 1) (1/2) = iteratedDeriv 2 binaryEntropy
      (1/2) := by
    apply iteratedDerivWithin_of_isOpen
    · exact isOpen_Ioo
    · exact ⟨by norm_num, by norm_num⟩
  rw [h1]
  have h2 : iteratedDeriv 2 binaryEntropy = deriv (deriv binaryEntropy) := by
    have : 2 = 1 + 1 := rfl
    rw [this, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  have h3 : ∀ᶠ x in 𝓝 (1/2 : ℝ), deriv binaryEntropy x = (Real.log (1 - x) - Real.log x) / Real.log
      2 := by
    apply Filter.eventually_of_mem (Ioo_mem_nhds (by norm_num : (0:ℝ) < 1/2)
        (by norm_num : (1/2:ℝ) < 1))
    intro x hx
    have h2_x : HasDerivAt (fun x => Real.negMulLog x / Real.log 2) ((-Real.log x - 1) / Real.log 2)
        x := by
      have : (fun x => Real.negMulLog x / Real.log 2) = (fun x => Real.negMulLog x * (Real.log 2)⁻¹)
          := by ext y; ring
      rw [this]
      have : (-Real.log x - 1) / Real.log 2 = (-Real.log x - 1) * (Real.log 2)⁻¹ := by ring
      rw [this]
      apply HasDerivAt.mul_const
      apply Real.hasDerivAt_negMulLog
      exact ne_of_gt hx.1
    have h3_x : HasDerivAt (fun x => Real.negMulLog (1 - x) / Real.log 2)
        ((-(-Real.log (1 - x) - 1)) / Real.log 2) x := by
      have : (fun x => Real.negMulLog (1 - x) / Real.log 2) =
          (fun x => Real.negMulLog (1 - x) * (Real.log 2)⁻¹) := by ext y; ring
      rw [this]
      have : (-(-Real.log (1 - x) - 1)) / Real.log 2 = (-(-Real.log (1 - x) - 1)) *
          (Real.log 2)⁻¹ := by ring
      rw [this]
      apply HasDerivAt.mul_const
      have hc : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        have : (fun (y : ℝ) => 1 - y) = (fun y : ℝ => -y + 1) := by ext y; ring
        rw [this]
        exact hasDerivAt_neg x |>.add_const 1
      have hn : HasDerivAt Real.negMulLog (-Real.log (1 - x) - 1) (1 - x) := by
        apply Real.hasDerivAt_negMulLog
        have : 1 - x > 0 := sub_pos.mpr hx.2
        exact ne_of_gt this
      have h_comp := HasDerivAt.comp x hn hc
      have : ((-Real.log (1 - x) - 1) * -1) = -(-Real.log (1 - x) - 1) := by ring
      rw [this] at h_comp
      exact h_comp
    have h4_x := HasDerivAt.add h2_x h3_x
    have h_eq : binaryEntropy = (fun x => Real.negMulLog x / Real.log 2) +
        (fun x => Real.negMulLog (1 - x) / Real.log 2) := by
      ext y
      unfold binaryEntropy negMulLog2
      rfl
    have h_eq2 : (fun x => Real.negMulLog x / Real.log 2) +
        (fun x => Real.negMulLog (1 - x) / Real.log 2) =
      (fun x => Real.negMulLog x / Real.log 2 + Real.negMulLog (1 - x) / Real.log 2) := rfl
    rw [h_eq, h_eq2]
    have : (-Real.log x - 1) / Real.log 2 + -(-Real.log (1 - x) - 1) / Real.log 2 =
        (Real.log (1 - x) - Real.log x) / Real.log 2 := by ring
    rw [← this]
    exact h4_x.deriv
  have h4 : deriv (deriv binaryEntropy) (1/2) =
      deriv (fun x => (Real.log (1 - x) - Real.log x) / Real.log 2) (1/2) := by
    exact Filter.EventuallyEq.deriv_eq h3
  rw [h4]
  have hd_log1 : HasDerivAt Real.log (1/2 : ℝ)⁻¹ (1/2) := by
    apply Real.hasDerivAt_log
    norm_num
  have hc : HasDerivAt (fun y : ℝ => 1 - y) (-1) (1/2) := by
    have : (fun (y : ℝ) => 1 - y) = (fun y : ℝ => -y + 1) := by ext y; ring
    rw [this]
    exact hasDerivAt_neg (1/2 : ℝ) |>.add_const 1
  have hd_log2_inner : HasDerivAt Real.log (1 - 1/2 : ℝ)⁻¹ (1 - 1/2) := by
    apply Real.hasDerivAt_log
    norm_num
  have hd_log2 := HasDerivAt.comp (1/2 : ℝ) hd_log2_inner hc
  have hd_sub := HasDerivAt.sub hd_log2 hd_log1
  have hd_div := HasDerivAt.div_const hd_sub (Real.log 2)
  have hd_val : ((1 - 1 / 2 : ℝ)⁻¹ * -1 - (1 / 2 : ℝ)⁻¹) / Real.log 2 = -4 / Real.log 2 := by
    have : (1 - 1/2 : ℝ) = 1/2 := by norm_num
    rw [this]
    have : (1/2 : ℝ)⁻¹ = 2 := by norm_num
    rw [this]
    ring
  rw [hd_val] at hd_div
  exact hd_div.deriv

/-- **SUV p. 239.**  The Taylor expansion of the entropy function at `1/2`:
`h(1/2 + δ) = 1 - (2 / ln 2) δ² + o(δ²)` as `δ → 0`. -/
theorem binaryEntropy_half_add_isLittleO :
    (fun δ : ℝ => binaryEntropy (1 / 2 + δ) - (1 - 2 / Real.log 2 * δ ^ 2)) =o[𝓝 0]
      (fun δ : ℝ => δ ^ 2) := by
  have htaylor := binaryEntropy_half_add_isLittleO_remainder
  have htaylor_eval : ∀ δ : ℝ, taylorWithinEval binaryEntropy 2 (Set.Ioo 0 1) (1/2) (1/2 + δ) =
    binaryEntropy (1/2) + derivWithin binaryEntropy (Set.Ioo 0 1) (1/2) * δ +
      iteratedDerivWithin 2 binaryEntropy (Set.Ioo 0 1) (1/2) / 2 * δ^2 := by
    intro δ
    change taylorWithinEval binaryEntropy (1 + 1) (Set.Ioo 0 1) (1/2) (1/2 + δ) = _
    rw [taylorWithinEval_succ]
    change taylorWithinEval binaryEntropy (0 + 1) (Set.Ioo 0 1) (1/2) (1/2 + δ) + _ = _
    rw [taylorWithinEval_succ]
    rw [taylor_within_zero_eval]
    have : 1 / 2 + δ - 1 / 2 = δ := by ring
    rw [this]
    rw [iteratedDerivWithin_one]
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.factorial_one, pow_one,
      Nat.cast_zero, zero_add, smul_eq_mul]
    ring
  have : (fun δ : ℝ => binaryEntropy (1/2 + δ) - taylorWithinEval binaryEntropy 2 (Set.Ioo 0 1)
                         (1/2) (1/2 + δ)) =
    (fun δ : ℝ => binaryEntropy (1/2 + δ) - (1 - 2 / Real.log 2 * δ^2)) := by
    ext δ
    rw [htaylor_eval δ]
    rw [binaryEntropy_half_add_isLittleO_value]
    rw [binaryEntropy_half_add_isLittleO_first_derivative]
    rw [binaryEntropy_half_add_isLittleO_second_derivative]
    have : 1 + 0 * δ + (-4 / Real.log 2) / 2 * δ ^ 2 = 1 - 2 / Real.log 2 * δ ^ 2 := by ring
    rw [this]
  rw [this] at htaylor
  exact htaylor


private lemma prefixFreq_sub_half_isBigO_entropy_bound_plainK_ne_top (V : Map)
    (hV : isOptimalConditional V) (x : List Bool) :
  plainK V x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  have h := hc x
  intro h_top
  rw [h_top] at h
  have h_ne_top : (programLength x : ENat) + c ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨WithTop.natCast_ne_top _, WithTop.natCast_ne_top _⟩
  exact h_ne_top (top_le_iff.mp h)

private lemma prefixFreq_sub_half_isBigO_entropy_bound_count_ofFn_eq_freq {α : Type*}
    [DecidableEq α] :
    ∀ {N : ℕ} (w : Fin N → α) (a : α), (List.ofFn w).count a = freq w a := by
  intro N
  induction N with
  | zero => intro w a; simp [freq]
  | succ N ih =>
      intro w a
      rw [List.ofFn_succ]
      simp only [List.count_cons]
      rw [ih]
      unfold freq
      rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
      simp only [Finset.sum_filter, Fin.sum_univ_succ]
      split <;> simp_all [Nat.add_comm]

private lemma prefixFreq_sub_half_isBigO_entropy_bound_h_freq_true (n : ℕ) (w : CantorSeq) :
  (freq (fun (i : Fin n) => w i) true : ℝ) / (n : ℝ) = prefixFreq w n := by
  have h_cnt : (freq (fun (i : Fin n) => w i) true : ℝ) = ((cantorPrefix w n).count true : ℝ) := by
    have hw : cantorPrefix w n = List.ofFn (fun (i : Fin n) => w i) := rfl
    rw [hw, prefixFreq_sub_half_isBigO_entropy_bound_count_ofFn_eq_freq]
  rw [h_cnt]
  unfold prefixFreq freqOne
  push_cast
  rfl

private lemma prefixFreq_sub_half_isBigO_entropy_bound_h_freq_false (n : ℕ) (w : CantorSeq)
    (hn_pos : (n : ℝ) ≠ 0) :
  (freq (fun (i : Fin n) => w i) false : ℝ) / (n : ℝ) = 1 - prefixFreq w n := by
  have h_le : freq (fun (i : Fin n) => w i) true ≤ n := by
    have h_sum := Fintype.sum_bool (fun a : Bool => freq (fun (i : Fin n) => w i) a)
    have h_tot := sum_freq (fun (i : Fin n) => w i)
    omega
  have h_nat : freq (fun (i : Fin n) => w i) false = n - freq (fun (i : Fin n) => w i) true := by
    have h_sum := Fintype.sum_bool (fun a : Bool => freq (fun (i : Fin n) => w i) a)
    have h_tot := sum_freq (fun (i : Fin n) => w i)
    omega
  have h_real : (freq (fun (i : Fin n) => w i) false : ℝ) = (n : ℝ) - (freq (fun (i : Fin n) => w i)
      true : ℝ) := by
    rw [h_nat, Nat.cast_sub h_le]
  rw [h_real, sub_div, div_self hn_pos, ← prefixFreq_sub_half_isBigO_entropy_bound_h_freq_true
      n w]

private lemma prefixFreq_sub_half_isBigO_entropy_bound_h_sum (n : ℕ) (w : CantorSeq) :
  ∑ a : Bool, negMulLog2 ((freq (fun (i : Fin n) => w i) a : ℝ) / n) =
    negMulLog2 ((freq (fun (i : Fin n) => w i) true : ℝ) / n) +
    negMulLog2 ((freq (fun (i : Fin n) => w i) false : ℝ) / n) :=
        Fintype.sum_bool (fun a : Bool => negMulLog2 ((freq (fun (i : Fin n) => w i) a : ℝ) / n))

/-- Step 1 of the proof of `prefixFreq_sub_half_isBigO`: the actual-prefix entropy bound.
-/
private theorem prefixFreq_sub_half_isBigO_entropy_bound
    (V : Map) (hV : isOptimalConditional V) {w : CantorSeq} :
    ∃ c : ℕ, ∀ n : ℕ,
      ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤
        (n : ℝ) * binaryEntropy (prefixFreq w n) + logSlack c n := by
  obtain ⟨cG, hcG⟩ := tendsto_prefixFreq_of_plainK_isLittleO_plainK_le V hV
  obtain ⟨cW, hcW⟩ := exists_plainK_word_le_entropy_freq Bool V hV
  use cG + cW
  intro n
  have h_word := hcW n (fun (i : Fin n) => w i)
  have h_le_ENat := hcG n (fun (i : Fin n) => w i)
  have h_plainK_ne_top : plainK V (cantorPrefix w n) ≠ ⊤ :=
      prefixFreq_sub_half_isBigO_entropy_bound_plainK_ne_top V hV (cantorPrefix w n)
  have h_plainK_word_ne_top : plainK V (finWordBits Bool (fun (i : Fin n) => w i)) ≠ ⊤ :=
      prefixFreq_sub_half_isBigO_entropy_bound_plainK_ne_top V hV
      (finWordBits Bool (fun (i : Fin n) => w i))
  have h_le_nat : (plainK V (cantorPrefix w n)).toNat ≤
      (plainK V (finWordBits Bool (fun (i : Fin n) => w i))).toNat + cG := by
    change plainK V (cantorPrefix w n) ≤ plainK V (finWordBits Bool (fun (i : Fin n) => w i)) +
        cG at h_le_ENat
    generalize h1 : plainK V (cantorPrefix w n) = k1
    generalize h2 : plainK V (finWordBits Bool (fun (i : Fin n) => w i)) = k2
    rw [h1] at h_plainK_ne_top h_le_ENat
    rw [h2] at h_plainK_word_ne_top h_le_ENat
    lift k1 to ℕ using h_plainK_ne_top
    lift k2 to ℕ using h_plainK_word_ne_top
    exact_mod_cast h_le_ENat
  have h_le_real : ((plainK V (cantorPrefix w n)).toNat : ℝ) ≤
      ((plainK V (finWordBits Bool (fun (i : Fin n) => w i))).toNat : ℝ) + (cG : ℝ) := by
    exact_mod_cast h_le_nat
  have h_ent : (n : ℝ) * entropyDist (fun a : Bool => (freq (fun (i : Fin n) => w i) a : ℝ) / n) =
      (n : ℝ) * binaryEntropy (prefixFreq w n) := by
    by_cases hn : n = 0
    · rw [hn]; simp
    · unfold entropyDist binaryEntropy
      have hn_pos : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      rw [prefixFreq_sub_half_isBigO_entropy_bound_h_sum n w]
      try rw [prefixFreq_sub_half_isBigO_entropy_bound_h_freq_true n w]
      try rw [prefixFreq_sub_half_isBigO_entropy_bound_h_freq_false n w hn_pos]
  calc
    ((plainK V (cantorPrefix w n)).toNat : ℝ)
      ≤ ((plainK V (finWordBits Bool (fun (i : Fin n) => w i))).toNat : ℝ) + (cG : ℝ) := h_le_real
    _ ≤ ((n : ℝ) * entropyDist (fun a : Bool => (freq (fun (i : Fin n) => w i) a : ℝ) / n) +
        logSlack cW n) + (cG : ℝ) := by linarith
    _ = (n : ℝ) * binaryEntropy (prefixFreq w n) + logSlack cW n + cG := by rw [h_ent]
    _ ≤ (n : ℝ) * binaryEntropy (prefixFreq w n) + logSlack (cG + cW) n := by
      unfold logSlack
      have h_slack1 : (((cW * (Nat.bits n).length + cW : ℕ) : ℝ) + cG : ℝ) ≤
          ((cG + cW) * (Nat.bits n).length + (cG + cW) : ℕ) := by
        push_cast
        have h_pos : (0 : ℝ) ≤ cG * (Nat.bits n).length := mul_nonneg (by positivity)
            (by positivity)
        linarith
      linarith




private lemma nat_size_real_le (n : ℕ) (hn : 1 ≤ n) : (Nat.size n : ℝ) ≤ Real.logb 2 n + 1 := by
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
  have h_lower : 2 ^ (Nat.size n - 1) ≤ n := by
    by_cases hlt : n < 2 ^ (Nat.size n - 1)
    · have h_size_le : Nat.size n ≤ Nat.size n - 1 := Nat.size_le.mpr hlt
      have : 0 < Nat.size n := Nat.size_pos.mpr hn
      omega
    · exact not_lt.mp hlt
  have h_lower_R : (2 : ℝ) ^ (Nat.size n - 1) ≤ (n : ℝ) := by exact_mod_cast h_lower
  have h_lower_log : Real.logb 2 ((2 : ℝ) ^ (Nat.size n - 1)) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.logb_le_logb (by norm_num) (by positivity) (by positivity)]
    exact h_lower_R
  rw [Real.logb_pow] at h_lower_log
  have h_log2_2 : Real.logb 2 2 = 1 := by norm_num
  rw [h_log2_2, mul_one] at h_lower_log
  have h_cast : ((Nat.size n - 1 : ℕ) : ℝ) = (Nat.size n : ℝ) - 1 := by
    have h_size_pos : 0 < Nat.size n := Nat.size_pos.mpr hn
    exact_mod_cast Nat.cast_sub h_size_pos
  rw [h_cast] at h_lower_log
  linarith

/-- Step 2 of the proof of `prefixFreq_sub_half_isBigO`: the entropy deficit bound. -/
private theorem prefixFreq_sub_half_isBigO_entropy_deficit
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℝ, ∀ n : ℕ,
      (n : ℝ) * (1 - binaryEntropy (prefixFreq w n)) ≤
        c * (Real.log n + 1) := by
  have hw_LS := (isMartinLofRandom_uniform_iff_KA_KMOf_eq_length hD w).mp hw
  obtain ⟨c1, hc1⟩ := hw_LS
  obtain ⟨c2, hc2⟩ := exists_const_KMOf_le_plainK_add_log V U hV hU hD
  obtain ⟨c3, hc3⟩ := prefixFreq_sub_half_isBigO_entropy_bound V hV (w := w)
  let K : ℝ := |(c1 : ℝ)| + |(c2 : ℝ)| + 2 * (c3 : ℝ) + 4
  use K
  intro n
  by_cases hn : n = 0
  · have hK : (0 : ℝ) ≤ |(c1 : ℝ)| + |(c2 : ℝ)| + 2 * (c3 : ℝ) + 4 := by positivity
    subst hn
    simp only [Nat.cast_zero, zero_mul, Real.log_zero, zero_add, mul_one]
    exact hK
  · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn
    have hn_real_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have hn_real_pos2 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hn_real_ge_1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
    have hc1_le := hc1 n
    
    have h_km_lower : (n : ℝ) - c1 ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ) := by
      have hc1_le' := (abs_le.mp hc1_le.2).1
      linarith
    have h_km_upper := hc2 (cantorPrefix w n)
    rw [cantorPrefix_length] at h_km_upper
    have h_plainK_bound := hc3 n
    
    have h_logSlack_le : (logSlack c3 n : ℝ) ≤ c3 * (Real.logb 2 n + 1) + c3 := by
      unfold logSlack
      have h1 : ((c3 * Nat.size n + c3 : ℕ) : ℝ) = c3 * (Nat.size n : ℝ) + c3 := by
        push_cast
        rfl
      have h2 : (Nat.size n : ℝ) ≤ Real.logb 2 n + 1 := nat_size_real_le n hn_pos
      have H_cast2 : ((c3 * (Nat.bits n).length + c3 : ℕ) : ℝ) = (c3 * Nat.size n + c3 : ℕ) := by
        have H_size_eq : (Nat.bits n).length = Nat.size n := by
          have H := Nat.size_eq_bits_len n
          rw [H]
        rw [H_size_eq]
      rw [H_cast2]
      rw [h1]
      have h3 : 0 ≤ (c3 : ℝ) := Nat.cast_nonneg c3
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      linarith
      
    have h_log_bound1 : Real.logb 2 n = Real.log n / Real.log 2 := by
      rw [Real.logb]
    have h_log_bound2 : Real.logb 2 (n + 1) = Real.log (n + 1) / Real.log 2 := by
      rw [Real.logb]
    
    have H_log_two : 1 / 2 < Real.log 2 := by
      have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have H_log_two2 : Real.log 2 < 1 := by
      have h : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
      linarith
    
    have H_log1 : Real.log (n + 1) ≤ Real.log 2 + Real.log n := by
      have h3 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have h4 : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by positivity)
          h3
      have h5 : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num)
          (by positivity)
      rw [h5] at h4
      exact h4
      
    have h_combine : (n : ℝ) * (1 - binaryEntropy (prefixFreq w n)) ≤ 
      c1 + c2 + c3 * (Real.logb 2 n + 1) + c3 + 2 * Real.logb 2 (n + 1) := by
      calc (n : ℝ) * (1 - binaryEntropy (prefixFreq w n))
        _ = (n : ℝ) - (n : ℝ) * binaryEntropy (prefixFreq w n) := by ring
        _ ≤ ((KMOf D (cantorPrefix w n)).toNat : ℝ) + c1 - (n : ℝ) * binaryEntropy (prefixFreq w n)
            := by linarith
        _ ≤ ((plainK V (cantorPrefix w n)).toNat : ℝ) + 2 * Real.logb 2 (n + 1) + c2 + c1 - (n : ℝ)
            * binaryEntropy (prefixFreq w n) := by linarith
        _ ≤ (n : ℝ) * binaryEntropy (prefixFreq w n) + logSlack c3 n + 2 * Real.logb 2 (n + 1) +
            c2 + c1 - (n : ℝ) * binaryEntropy (prefixFreq w n) := by linarith
        _ = logSlack c3 n + 2 * Real.logb 2 (n + 1) + c2 + c1 := by ring
        _ ≤ c3 * (Real.logb 2 n + 1) + c3 + 2 * Real.logb 2 (n + 1) + c2 + c1 := by linarith
        _ = c1 + c2 + c3 * (Real.logb 2 n + 1) + c3 + 2 * Real.logb 2 (n + 1) := by ring
        
    have h_final : c1 + c2 + c3 * (Real.logb 2 n + 1) + c3 + 2 * Real.logb 2 (n + 1) ≤ K *
        (Real.log n + 1) := by
      have hc1_abs : c1 ≤ |(c1 : ℝ)| := le_abs_self _
      have hc2_abs : c2 ≤ |(c2 : ℝ)| := le_abs_self _
      have hc3_nonneg : 0 ≤ (c3 : ℝ) := Nat.cast_nonneg _
      have h_log_pos : 0 ≤ Real.log n := Real.log_nonneg hn_real_ge_1
      have H_logb_le_log : Real.logb 2 n ≤ 2 * Real.log n := by
        rw [h_log_bound1]
        have h_div_le : 1 / Real.log 2 ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        calc Real.log n / Real.log 2 = Real.log n * (1 / Real.log 2) := div_eq_mul_one_div _ _
          _ ≤ Real.log n * 2 := mul_le_mul_of_nonneg_left h_div_le h_log_pos
          _ = 2 * Real.log n := by ring
      have H_logb_le_log2 : Real.logb 2 (n + 1) ≤ 2 * Real.log (n + 1) := by
        rw [h_log_bound2]
        have h_div_le : 1 / Real.log 2 ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        have H_pos : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
        calc Real.log (n + 1) / Real.log 2 = Real.log (n + 1) * (1 / Real.log 2) :=
            div_eq_mul_one_div _ _
          _ ≤ Real.log (n + 1) * 2 := mul_le_mul_of_nonneg_left h_div_le H_pos
          _ = 2 * Real.log (n + 1) := by ring
      
      have h1 : c3 * (Real.logb 2 n + 1) ≤ c3 * (2 * Real.log n + 1) := by
        nlinarith
      have h2 : 2 * Real.logb 2 (n + 1) ≤ 2 * (2 * Real.log (n + 1)) := by
        nlinarith
      have h3 : 2 * (2 * Real.log (n + 1)) ≤ 2 * (2 * (Real.log 2 + Real.log n)) := by
        nlinarith
      have h4 : 2 * (2 * (Real.log 2 + Real.log n)) ≤ 2 * (2 * (1 + Real.log n)) := by
        nlinarith
      
      have h_bound : c1 + c2 + c3 * (Real.logb 2 n + 1) + c3 + 2 * Real.logb 2 (n + 1) ≤ 
                     |(c1 : ℝ)| + |(c2 : ℝ)| + c3 * (2 * Real.log n + 1) + c3 + 2 *
                         (2 * (1 + Real.log n)) := by
        nlinarith
        
      have h_bound2 : |(c1 : ℝ)| + |(c2 : ℝ)| + c3 * (2 * Real.log n + 1) + c3 + 2 *
          (2 * (1 + Real.log n)) ≤ 
                     (|(c1 : ℝ)| + |(c2 : ℝ)| + 2 * c3 + 4) * (Real.log n + 1) := by
        calc |(c1 : ℝ)| + |(c2 : ℝ)| + c3 * (2 * Real.log n + 1) + c3 + 2 * (2 * (1 + Real.log n))
          _ = |(c1 : ℝ)| + |(c2 : ℝ)| + 2 * c3 * Real.log n + 2 * c3 + 4 + 4 * Real.log n := by ring
          _ ≤ |(c1 : ℝ)| + |(c2 : ℝ)| + 2 * c3 * Real.log n + 2 * c3 + 4 + 4 * Real.log n +
              (|(c1 : ℝ)| + |(c2 : ℝ)|) * Real.log n := by
            have H_nonneg : 0 ≤ (|(c1 : ℝ)| + |(c2 : ℝ)|) * Real.log n := mul_nonneg (by positivity)
                h_log_pos
            linarith
          _ = (|(c1 : ℝ)| + |(c2 : ℝ)| + 2 * c3 + 4) * (Real.log n + 1) := by ring
      
      exact h_bound.trans h_bound2
      
    exact h_combine.trans h_final

/-- Step 3 of the proof of `prefixFreq_sub_half_isBigO`: quantitative entropy inequality.
-/
private theorem prefixFreq_sub_half_isBigO_entropy_quadratic
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x - 1 / 2) ^ 2 ≤ 1 - binaryEntropy x := by
  have H : 2 * (x - (1 / 2 : ℝ)) ^ 2 ≤ (1 - x) * Real.log ((1 - x) / (1 - 1 / 2)) + x * Real.log
      (x / (1 / 2)) := by
    apply Kolmogorov.two_mul_sq_sub_le_bernoulliKL hx0 hx1 (by norm_num) (by norm_num)
  have h_id : 1 - binaryEntropy x = ((1 - x) * Real.log ((1 - x) / (1 - 1 / 2)) + x * Real.log
      (x / (1 / 2))) / Real.log 2 := by
    rcases eq_or_lt_of_le hx0 with rfl | hx0_lt
    · have H1 : (1 - 0 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
      rw [H1]
      simp [binaryEntropy, negMulLog2, Real.negMulLog]
      field_simp
    rcases eq_or_lt_of_le hx1 with rfl | hx1_lt
    · have H1 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
      rw [H1]
      simp [binaryEntropy, negMulLog2, Real.negMulLog]
      field_simp
    have H1 : x / (1 / 2) = x * 2 := by ring
    have H2 : (1 - x) / (1 - 1 / 2) = (1 - x) * 2 := by ring
    rw [H1, H2]
    rw [Real.log_mul (ne_of_gt hx0_lt) (by norm_num), Real.log_mul (ne_of_gt (sub_pos.mpr hx1_lt))
        (by norm_num)]
    unfold binaryEntropy negMulLog2 Real.negMulLog
    field_simp
    ring
  rw [h_id]
  have H3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (x - 1 / 2) ^ 2 ≤ 2 * (x - 1 / 2) ^ 2 / Real.log 2 := by
      exact le_div_iff₀ H3 |>.mpr (by nlinarith [Real.log_two_lt_d9])
    _ ≤ ((1 - x) * Real.log ((1 - x) / (1 - 1 / 2)) + x * Real.log (x / (1 / 2))) / Real.log 2 := by
      exact div_le_div_of_nonneg_right H (le_of_lt H3)

/-- Step 4 of the proof of `prefixFreq_sub_half_isBigO`: converting deficit to squared
bound. -/
private theorem prefixFreq_sub_half_isBigO_entropy_to_square
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (h : ∃ c : ℝ, ∀ n : ℕ,
      (n : ℝ) * (1 - binaryEntropy (p n)) ≤ c * (Real.log n + 1)) :
    ∃ c : ℝ, ∀ n : ℕ,
      (n : ℝ) * (p n - 1 / 2) ^ 2 ≤ c * (Real.log n + 1) := by
  obtain ⟨c, hc⟩ := h
  use c
  intro n
  have h1 := prefixFreq_sub_half_isBigO_entropy_quadratic (p n) (hp n).1 (hp n).2
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
  exact le_trans h2 (hc n)

/-- Step 5 of the proof of `prefixFreq_sub_half_isBigO`: final square-root bound. -/
private theorem prefixFreq_sub_half_isBigO_sqrt_bound
    (p : ℕ → ℝ)
    (h : ∃ c : ℝ, ∀ n : ℕ,
      (n : ℝ) * (p n - 1 / 2) ^ 2 ≤ c * (Real.log n + 1)) :
    (fun n => p n - 1 / 2) =O[atTop]
      (fun n => Real.sqrt (Real.log n / n)) := by
  obtain ⟨c, hc⟩ := h
  have hc_nonneg : 0 ≤ c := by
    have h1 := hc 1
    simp at h1
    nlinarith [sq_nonneg (p 1 - 1 / 2)]
  apply IsBigO.of_bound (Real.sqrt (2 * c))
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog_ge : 1 ≤ Real.log n := by
    have hn_real : (3 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 :=
        Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      _ ≤ Real.log n := Real.log_le_log (by norm_num) hn_real
  have hlog_add : Real.log n + 1 ≤ 2 * Real.log n := by linarith
  have h_bound : (p n - 1 / 2) ^ 2 ≤ 2 * c * (Real.log n / n) := by
    rw [mul_div_assoc', le_div_iff₀ hn_pos]
    have hle := (hc n).trans (mul_le_mul_of_nonneg_left hlog_add hc_nonneg)
    nlinarith only [hle]
  have h_sqrt := Real.sqrt_le_sqrt h_bound
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (by positivity)] at h_sqrt
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h_sqrt

/-- **SUV p. 240.**  The first estimate of the proof of Theorem 156, the level of Hardy and
Littlewood: for a Martin-Löf random sequence `|p_n - 1/2| = O(√(log n / n))`. -/
theorem prefixFreq_sub_half_isBigO {w : CantorSeq} (hw : IsMartinLofRandom uniformMeasure w) :
    (fun n : ℕ => prefixFreq w n - 1 / 2) =O[atTop]
      (fun n : ℕ => Real.sqrt (Real.log n / n)) := by
  have hp : ∀ n, 0 ≤ prefixFreq w n ∧ prefixFreq w n ≤ 1 := by
    intro n
    unfold prefixFreq freqOne
    have h1 : (0 : ℝ) ≤ (((cantorPrefix w n).count true : ℚ) / n : ℚ) := by
      positivity
    have h2 : ((((cantorPrefix w n).count true : ℚ) / n : ℚ) : ℝ) ≤ 1 := by
      by_cases hn : n = 0
      · simp [hn]
      · have : (cantorPrefix w n).count true ≤ n := by
          have := @List.count_le_length _ _ true (cantorPrefix w n)
          rwa [cantorPrefix_length] at this
        norm_cast
        rw [div_le_one (by positivity)]
        exact_mod_cast this
    exact ⟨h1, h2⟩
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨D, hD⟩ := exists_optimalMonotoneDecompressor
  have h2 := prefixFreq_sub_half_isBigO_entropy_deficit V U hV hU hD hw
  have h4 := prefixFreq_sub_half_isBigO_entropy_to_square (prefixFreq w) hp h2
  exact prefixFreq_sub_half_isBigO_sqrt_bound (prefixFreq w) h4

end Kolmogorov.Applications
