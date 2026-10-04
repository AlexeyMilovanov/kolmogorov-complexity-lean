import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.PlainAndFibreDecoders
import KolmogorovMathlib.Complexity.CanonicalObjects.Counting
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Entropy.Conditional
import KolmogorovMathlib.Entropy.Inequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.EquivFin

/-!
# The Shannon coding theorem for arbitrary probabilities (Problem 240)

SUV Section 7.3.5, p. 232, Problem 240.

The book proves Theorem 151 from Theorem 149 and part (b) through the complexity of correctly
decoded words, which needs the `p_i` to be computable; Problem 240 asks to remove that
assumption.  This module proves Theorem 149 for arbitrary real `p_i`
(`exists_const_prob_plainK_near_mul_entropyDist_of_real`: with high probability the complexity of
an i.i.d. word is `N H(ξ) ± c√N`) and Theorem 151(b) for arbitrary real `p_i`
(`exists_const_prob_correct_le_of_real`).
-/

namespace Kolmogorov

open Finset

/-! ### Problem 240: arbitrary probabilities -/

/-- The expectation of a product of functions of distinct coordinates under `μ^N` is the
product of their expectations (independence of the coordinates). -/
private lemma power_sum_mul_prod {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω) (N : ℕ)
    (h : Fin N → Ω → ℝ) :
    ∑ w : Fin N → Ω, (μ.power N).prob w * ∏ k, h k (w k) = ∏ k, ∑ a, μ.prob a * h k a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [FiniteProbSpace.power, Finset.prod_mul_distrib]

/-- The second moment of a sum of `N` independent centred copies is `N` times the second moment
of one copy. -/
private lemma power_sum_sq_eq {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω) (g : Ω → ℝ)
    (hg : ∑ a, μ.prob a * g a = 0) (N : ℕ) :
    ∑ w : Fin N → Ω, (μ.power N).prob w * (∑ i, g (w i)) ^ 2 =
      N * ∑ a, μ.prob a * g a ^ 2 := by
  classical
  have hsq : ∀ w : Fin N → Ω, (∑ i, g (w i)) ^ 2 = ∑ i, ∑ j,
      ∏ k, (if k = i then g (w k) else 1) * (if k = j then g (w k) else 1) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  have h1 : ∀ i j : Fin N, (∏ k, ∑ a, μ.prob a *
      ((if k = i then g a else 1) * (if k = j then g a else 1))) =
      if i = j then ∑ a, μ.prob a * g a ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      rw [Finset.prod_eq_single i]
      · simp [sq]
      · intro k _ hk; simp [hk, μ.sum_prob]
      · exact fun h => absurd (Finset.mem_univ i) h
    · exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [hij] using hg)
  calc ∑ w : Fin N → Ω, (μ.power N).prob w * (∑ i, g (w i)) ^ 2
      = ∑ i, ∑ j, ∑ w : Fin N → Ω, (μ.power N).prob w *
          ∏ k, (if k = i then g (w k) else 1) * (if k = j then g (w k) else 1) := by
        simp_rw [hsq, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin N, ∑ j : Fin N, if i = j then ∑ a, μ.prob a * g a ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← h1, ← power_sum_mul_prod μ N
          (fun k a => (if k = i then g a else 1) * (if k = j then g a else 1))]
    _ = N * ∑ a, μ.prob a * g a ^ 2 := by simp


/-- **Type classes are small.**  The number of words with a given letter histogram, times the
probability of any one of them, is at most one: it is a term of the multinomial expansion of
`(∑ q)^n = 1`. -/
private lemma multinomial_count_mul_prod_le_one {k : ℕ} (q : Fin k → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∑ j, q j = 1) (v : List (Fin k)) :
    (Nat.multinomial univ (fun j => v.count j) : ℝ) * (v.map q).prod ≤ 1 := by
  classical
  have hprod : (v.map q).prod = ∏ j, q j ^ v.count j := by
    rw [Finset.prod_list_map_count]
    exact Finset.prod_subset (Finset.subset_univ _) fun j _ hj => by
      simp [List.count_eq_zero_of_not_mem (by simpa using hj)]
  have hmem : (fun j => v.count j) ∈ (univ : Finset (Fin k)).piAntidiag v.length := by
    simp only [mem_piAntidiag, ne_eq, mem_univ, implies_true, and_true]
    exact (length_eq_sum_count v).symm
  have hexp := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin k)) q v.length
  rw [hq1, one_pow] at hexp
  rw [hprod, hexp]
  exact Finset.single_le_sum (f := fun κ => (Nat.multinomial univ κ : ℝ) * ∏ i, q i ^ κ i)
    (fun κ _ => mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ =>
      pow_nonneg (hq0 i) _)) hmem


/-- A word of positive probability has probability `2^(−L)`, where `L = ∑ −log₂ p(wᵢ)` is its
self-information. -/
private lemma power_prob_eq_rpow_neg_selfInfo {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    {N : ℕ} (w : Fin N → Ω) (hP : 0 < (μ.power N).prob w) :
    (μ.power N).prob w = 2 ^ (-∑ i, -Real.logb 2 (μ.prob (w i))) := by
  have hP' : 0 < ∏ i, μ.prob (w i) := hP
  have hne : ∀ i ∈ (univ : Finset (Fin N)), μ.prob (w i) ≠ 0 :=
    Finset.prod_ne_zero_iff.1 hP'.ne'
  rw [Finset.sum_neg_distrib, neg_neg, ← Real.logb_prod _ _ hne,
    Real.rpow_logb (by norm_num) (by norm_num) hP']
  rfl

/-- **Upper bound through the type class.**  A word is described by its letter histogram and its
rank inside the histogram class, so its complexity is at most its self-information
`−log₂ Pr[w] = ∑ −log₂ p(wᵢ)` plus `O(log N)`; no computability of the `p_i` is needed. -/
private lemma exists_plainK_le_selfInfo_add_size (A : Type*) [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A) (D : Map) (hD : isOptimalConditional D) :
    ∃ C : ℕ, ∀ (N : ℕ) (w : Fin N → A), 0 < (μ.power N).prob w →
      ((plainK D (finWordBits A w)).toNat : ℝ) ≤
        ∑ i, -Real.logb 2 (μ.prob (w i)) + C * Nat.size N + C := by
  classical
  set k := Fintype.card A
  let idx : A → Fin k := fun a => ⟨alphabetIndex A a, alphabetIndex_lt_card a⟩
  have hbij : Function.Bijective idx := (Fintype.bijective_iff_injective_and_card idx).2
    ⟨fun a b h => alphabetIndex_injective (congrArg Fin.val h), by simp [k]⟩
  let e := Equiv.ofBijective idx hbij
  let table : List BitString := (List.range k).map (natBitsFixed (alphabetWidth A))
  let g : BitString → BitString := fun x =>
    ((Encodable.decode (bitsToNat x) : Option (List ℕ)).getD []).flatMap
      (fun n => table.getD n [])
  have hg : Computable g := (Primrec.list_flatMap
    (Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec) (Primrec.const []))
    ((Primrec.list_getD []).comp (Primrec.const table) Primrec.snd).to₂).to_comp
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD g hg
  obtain ⟨c2, hc2⟩ := plainK_fixedHistogramWord_le_size_multinomial_add_params D hD
  refine ⟨3 * k + 2 * Nat.size k + c1 + c2 + 1, fun N w hP => ?_⟩
  set v : List (Fin k) := List.ofFn fun i => idx (w i)
  have hgv : g (finiteWordCode v) = finWordBits A w := by
    have hmap : v.map FiniteLetterCode.encode = List.ofFn fun i => alphabetIndex A (w i) := by
      simp [v, List.map_ofFn]; rfl
    simp only [g, finiteWordCode, bitsToNat_bits, hmap, Encodable.encodek, Option.getD_some]
    simp only [finWordBits, wordBits, Code.encodeWord, List.flatMap, List.map_ofFn]
    congr 2
    funext i
    have hi : alphabetIndex A (w i) < k := alphabetIndex_lt_card (w i)
    simp [table, alphabetCode, List.getElem?_range hi]
  set f : Fin k → ℕ := fun j => v.count j
  set M := Nat.multinomial univ f
  set L := ∑ i, -Real.logb 2 (μ.prob (w i))
  have hK : plainK D (finWordBits A w) ≤
      ((M.size + 2 * k.size + 2 * ∑ j, (f j).size + k + c2 + c1 : ℕ) : ENat) := by
    rw [← hgv]
    refine (hc1 _).trans ?_
    refine (add_le_add_left (hc2 k f v fun j => rfl) _).trans (le_of_eq ?_)
    push_cast
    ring
  have hK' : ((plainK D (finWordBits A w)).toNat : ℝ) ≤
      ((M.size + 2 * k.size + 2 * ∑ j, (f j).size + k + c2 + c1 : ℕ) : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hK
  have hp1 : ∀ a, μ.prob a ≤ 1 := fun a => by
    simpa [μ.sum_prob] using
      Finset.single_le_sum (fun b _ => μ.prob_nonneg b) (Finset.mem_univ a)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ =>
    neg_nonneg.2 (Real.logb_nonpos one_lt_two (μ.prob_nonneg _) (hp1 _))
  have hMP : (M : ℝ) * (μ.power N).prob w ≤ 1 := by
    have h := multinomial_count_mul_prod_le_one (fun j => μ.prob (e.symm j))
      (fun j => μ.prob_nonneg _) (by rw [e.symm.sum_comp]; exact μ.sum_prob) v
    convert h using 2
    simp [v, List.map_ofFn, FiniteProbSpace.power, List.prod_ofFn, e]
  have hM : (M : ℝ) < 2 ^ (⌊L⌋₊ + 1) := by
    calc (M : ℝ) ≤ 1 / (μ.power N).prob w := (le_div_iff₀ hP).2 hMP
      _ = 2 ^ L := by
        rw [power_prob_eq_rpow_neg_selfInfo μ w hP, Real.rpow_neg (by norm_num), one_div,
          inv_inv]
      _ < 2 ^ ((⌊L⌋₊ + 1 : ℕ) : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
          (by push_cast; exact Nat.lt_floor_add_one L)
      _ = _ := Real.rpow_natCast _ _
  have hsM : M.size ≤ ⌊L⌋₊ + 1 := Nat.size_le.2 (by exact_mod_cast hM)
  have hsMr : (M.size : ℝ) ≤ L + 1 := by
    have h1 := Nat.floor_le hL0
    have h2 : (M.size : ℝ) ≤ ⌊L⌋₊ + 1 := by exact_mod_cast hsM
    linarith
  have hsum : ∑ j, (f j).size ≤ k * N.size := by
    calc ∑ j, (f j).size ≤ ∑ _j : Fin k, N.size := Finset.sum_le_sum fun j _ =>
          Nat.size_le_size (by simpa [f, v] using List.count_le_length (a := j) (l := v))
      _ = k * N.size := by simp
  have hsumr : ((∑ j, (f j).size : ℕ) : ℝ) ≤ k * N.size := by exact_mod_cast hsum
  push_cast at hK' hsumr ⊢
  have hNs : (0 : ℝ) ≤ N.size := Nat.cast_nonneg _
  have hks : (0 : ℝ) ≤ k.size := Nat.cast_nonneg _
  nlinarith

/-- **Counting bound for the lower tail.**  Fewer than `2^⌈m⌉` words have complexity below `m`,
and a word of self-information at least `m + t` has probability at most `2^(−m−t)`; so words
with both properties carry probability at most `2^(1−t)`. -/
private lemma prob_plainK_lt_selfInfo_ge_le (A : Type*) [Fintype A] [Encodable A]
    (μ : FiniteProbSpace A) (D : Map) (hD : isOptimalConditional D) (N : ℕ) (m t : ℝ) :
    (μ.power N).probOfPred (fun w => ((plainK D (finWordBits A w)).toNat : ℝ) < m ∧
      m + t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ≤ 2 ^ (1 - t) := by
  classical
  obtain ⟨c0, hc0⟩ := plainK_le_length D hD
  obtain ⟨_, hcnt⟩ := card_plainK_lt_mem_Icc D hD
  set n := ⌈m⌉₊
  set S := (univ : Finset (Fin N → A)).filter fun w =>
    ((plainK D (finWordBits A w)).toNat : ℝ) < m ∧ m + t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))
  have hprob : (μ.power N).probOfPred (fun w => ((plainK D (finWordBits A w)).toNat : ℝ) < m ∧
      m + t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) = ∑ w ∈ S, (μ.power N).prob w := by
    rw [Finset.sum_filter, FiniteProbSpace.probOfPred]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hpt : ∀ w ∈ S, (μ.power N).prob w ≤ 2 ^ (-(m + t)) := by
    intro w hw
    rcases ((μ.power N).prob_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    rw [power_prob_eq_rpow_neg_selfInfo μ w hpos]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(mem_filter.1 hw).2.2])
  have hcard : S.card ≤ 2 ^ n := by
    have hfin := (hcnt n).1
    refine (Finset.card_le_card_of_injOn (finWordBits A) (t := hfin.toFinset) ?_ ?_).trans ?_
    · intro w hw
      have hw' := (mem_filter.1 hw).2.1
      have hne : plainK D (finWordBits A w) ≠ ⊤ := ne_top_of_le_natCast_add (hc0 _)
      have hlt : (plainK D (finWordBits A w)).toNat < n := Nat.lt_ceil.2 hw'
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      rw [← ENat.natCast_toNat hne]
      exact_mod_cast hlt
    · intro w _ w' _ h
      exact List.ofFn_injective (wordBits_injective h)
    · rw [← Set.ncard_eq_toFinset_card _ hfin]
      exact (hcnt n).2.2
  rw [hprob]
  by_cases hm : 0 < m
  · calc ∑ w ∈ S, (μ.power N).prob w ≤ S.card * (2 : ℝ) ^ (-(m + t)) := by
          simpa using Finset.sum_le_sum hpt
      _ ≤ (2 : ℝ) ^ (m + 1) * 2 ^ (-(m + t)) := by
          gcongr
          calc (S.card : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hcard
            _ = (2 : ℝ) ^ (n : ℝ) := by push_cast; exact (Real.rpow_natCast 2 n).symm
            _ ≤ 2 ^ (m + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (Nat.ceil_lt_add_one hm.le).le
      _ = 2 ^ (1 - t) := by rw [← Real.rpow_add (by norm_num)]; ring_nf
  · have hS : S = ∅ := Finset.filter_eq_empty_iff.2 fun w _ h =>
      hm (lt_of_le_of_lt (Nat.cast_nonneg _) h.1)
    rw [hS, Finset.sum_empty]
    positivity

/-- **Chebyshev's inequality for i.i.d. sums.**  The sum of `N` independent copies of `f`
deviates from `N 𝔼f` by more than `c√N` with probability at most `δ`, for a suitable `c`. -/
private lemma exists_const_prob_abs_sum_sub_gt_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (f : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ N : ℕ, (μ.power N).probOfPred
      (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|) ≤ δ := by
  classical
  set g : Ω → ℝ := fun a => f a - μ.expect f
  set V := ∑ a, μ.prob a * g a ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg fun a _ => mul_nonneg (μ.prob_nonneg a) (sq_nonneg _)
  obtain ⟨c, hc⟩ := exists_nat_gt (V / δ)
  have hVc : V < δ * c := by rw [div_lt_iff₀ hδ] at hc; linarith
  have hc1 : (1 : ℝ) ≤ c := by
    have : (0 : ℝ) < c := lt_of_le_of_lt (div_nonneg hV hδ.le) hc
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at this)
  refine ⟨c, fun N => ?_⟩
  have hg : ∑ a, μ.prob a * g a = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, μ.sum_prob, one_mul]
    simp [FiniteProbSpace.expect]
  have hpt : ∀ w : Fin N → Ω, Set.indicator
      {w | c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|} (μ.power N).prob w *
        ((c : ℝ) ^ 2 * N) ≤ (μ.power N).prob w * (∑ i, g (w i)) ^ 2 := by
    intro w
    have hcent : ∑ i, g (w i) = ∑ i, f (w i) - N * μ.expect f := by simp [g]
    by_cases hw : w ∈ {w | c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|}
    · rw [Set.indicator_of_mem hw]
      refine mul_le_mul_of_nonneg_left ?_ ((μ.power N).prob_nonneg w)
      have hw' : c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f| := hw
      calc (c : ℝ) ^ 2 * N = (c * Real.sqrt N) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        _ ≤ |∑ i, f (w i) - N * μ.expect f| ^ 2 := pow_le_pow_left₀ (by positivity) hw'.le 2
        _ = (∑ i, g (w i)) ^ 2 := by rw [sq_abs, hcent]
    · rw [Set.indicator_of_notMem hw, zero_mul]
      exact mul_nonneg ((μ.power N).prob_nonneg w) (sq_nonneg _)
  have hmul : (μ.power N).probOfPred
      (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|) * ((c : ℝ) ^ 2 * N) ≤
        N * V := by
    rw [FiniteProbSpace.probOfPred, Finset.sum_mul, ← power_sum_sq_eq μ g hg N]
    exact Finset.sum_le_sum fun w _ => hpt w
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [FiniteProbSpace.probOfPred, hδ.le]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 := (μ.power N).probOfPred_nonneg
    (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|)
  have h2 : (μ.power N).probOfPred
      (fun w => c * Real.sqrt N < |∑ i, f (w i) - N * μ.expect f|) * (c : ℝ) ^ 2 ≤ V := by
    nlinarith
  nlinarith

/-- The bit length of `N` is at most `2√N`, so an `O(log N)` term is absorbed by `c√N`. -/
private lemma size_le_two_mul_sqrt (N : ℕ) : (Nat.size N : ℝ) ≤ 2 * Real.sqrt N := by
  have key : ∀ s : ℕ, s ^ 2 ≤ 2 ^ (s + 1) := by
    intro s
    induction s with
    | zero => norm_num
    | succ n ih =>
      rcases lt_or_ge n 3 with h | h
      · interval_cases n <;> norm_num
      · rw [pow_succ 2 (n + 1)]; nlinarith
  have hnat : Nat.size N ^ 2 ≤ 4 * N := by
    rcases N.eq_zero_or_pos with rfl | hN
    · simp
    have hs : 0 < Nat.size N := Nat.size_pos.2 hN
    have h2 : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.1 (by omega)
    calc Nat.size N ^ 2 ≤ 2 ^ (Nat.size N - 1 + 2) := by
          rw [show Nat.size N - 1 + 2 = Nat.size N + 1 by omega]; exact key _
      _ = 4 * 2 ^ (Nat.size N - 1) := by ring
      _ ≤ 4 * N := by omega
  have h : (Nat.size N : ℝ) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    exact_mod_cast (show Nat.size N ^ 2 ≤ 2 ^ 2 * N by simpa using hnat)
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).1 h

/-- The expected self-information `𝔼[−log₂ p(ξ)]` is the entropy `H(ξ)`. -/
private lemma expect_neg_logb_prob (A : Type*) [Fintype A] (μ : FiniteProbSpace A) :
    μ.expect (fun a => -Real.logb 2 (μ.prob a)) = entropyDist μ.prob := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [negMulLog2, Real.negMulLog, Real.logb]
  ring

/-- Union bound: a property that forces one of two others has probability at most the sum of
their probabilities. -/
private lemma probOfPred_le_add_of_imp {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (P Q R : Ω → Prop) (h : ∀ ω, P ω → Q ω ∨ R ω) :
    μ.probOfPred P ≤ μ.probOfPred Q + μ.probOfPred R := by
  classical
  unfold FiniteProbSpace.probOfPred
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h0 := μ.prob_nonneg ω
  have := h ω
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

/-- A property and its negation have total probability one. -/
private lemma probOfPred_add_probOfPred_not {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (P : Ω → Prop) : μ.probOfPred P + μ.probOfPred (fun ω => ¬ P ω) = 1 := by
  classical
  unfold FiniteProbSpace.probOfPred
  rw [← Finset.sum_add_distrib, ← μ.sum_prob]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

/-- The outcomes of probability zero form an event of probability zero. -/
private lemma probOfPred_prob_eq_zero {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω) :
    μ.probOfPred (fun ω => μ.prob ω = 0) = 0 := by
  classical
  refine Finset.sum_eq_zero fun ω _ => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

/-- **Theorem 149 for arbitrary real probabilities.**  Replacing the `p_i` by approximations of
precision `1/N²`, which cost `O(log N)` bits, removes the computability assumption of
Theorem 149: the complexity of `ξ^N` lies within `c√N` of `N H(ξ)` with probability at least
`1 − ε`, for every distribution on the alphabet.  The complexity is the plain complexity of the
block encoding `finWordBits`, and `ENat.toNat` is faithful because an optimal decompressor gives
every string a finite complexity.  As in Theorem 149, `N = 0` is excluded.
SUV Problem 240, p. 232. -/
theorem exists_const_prob_plainK_near_mul_entropyDist_of_real (A : Type*) [Fintype A]
    [Encodable A] (μ : FiniteProbSpace A) (D : Map)
    (hD : isOptimalConditional D) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N : ℕ, 0 < N →
      1 - ε ≤ (μ.power N).probOfPred fun w =>
        (N : ℝ) * entropyDist μ.prob - c * Real.sqrt N <
            ((plainK D (finWordBits A w)).toNat : ℝ) ∧
          ((plainK D (finWordBits A w)).toNat : ℝ) <
            (N : ℝ) * entropyDist μ.prob + c * Real.sqrt N := by
  classical
  obtain ⟨c0, hc0⟩ := exists_const_prob_abs_sum_sub_gt_le μ
    (fun a => -Real.logb 2 (μ.prob a)) (half_pos hε)
  obtain ⟨C, hC⟩ := exists_plainK_le_selfInfo_add_size A μ D hD
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨c0 + 3 * C + n + 2, fun N hN => ?_⟩
  rw [expect_neg_logb_prob] at hc0
  set H := entropyDist μ.prob
  set c : ℝ := ((c0 + 3 * C + n + 2 : ℕ) : ℝ) with hc
  have hc' : c = c0 + 3 * C + n + 2 := by rw [hc]; push_cast; ring
  have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  have hsize := size_le_two_mul_sqrt N
  set m : ℝ := N * H - c * Real.sqrt N + 1
  set t : ℝ := (c - c0) * Real.sqrt N - 1
  have himp : ∀ w : Fin N → A, ¬ ((N : ℝ) * H - c * Real.sqrt N <
      ((plainK D (finWordBits A w)).toNat : ℝ) ∧
      ((plainK D (finWordBits A w)).toNat : ℝ) < (N : ℝ) * H + c * Real.sqrt N) →
      (c0 * Real.sqrt N < |∑ i, -Real.logb 2 (μ.prob (w i)) - N * H|) ∨
        ((μ.power N).prob w = 0 ∨
          (((plainK D (finWordBits A w)).toNat : ℝ) < m ∧
            m + t ≤ ∑ i, -Real.logb 2 (μ.prob (w i)))) := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hab := abs_le.1 h1
    apply hw
    constructor
    · by_contra hlow
      push Not at hlow
      have := h3 (by linarith)
      nlinarith
    · have hup := hC N w (lt_of_le_of_ne ((μ.power N).prob_nonneg w) (Ne.symm h2))
      have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  have hlow := prob_plainK_lt_selfInfo_ge_le A μ D hD N m t
  have ht : (2 : ℝ) ^ (1 - t) < ε / 2 := by
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (2 : ℝ) ^ (1 - t) ≤ 2 ^ (-(n : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = (1 / 2) ^ n := by rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; simp
      _ < ε / 2 := hn
  have hbad := (probOfPred_le_add_of_imp _ _ _ _ himp).trans (add_le_add (hc0 N)
    (probOfPred_le_add_of_imp _ _ _ _ fun w h => h))
  rw [probOfPred_prob_eq_zero] at hbad
  have hsum := probOfPred_add_probOfPred_not (μ.power N) fun w =>
    (N : ℝ) * H - c * Real.sqrt N < ((plainK D (finWordBits A w)).toNat : ℝ) ∧
      ((plainK D (finWordBits A w)).toNat : ℝ) < (N : ℝ) * H + c * Real.sqrt N
  linarith

/-- **Theorem 151(b) for arbitrary real probabilities.**  The converse half of the coding theorem
holds without the computability assumption that its proof through complexity uses: any code for
`ξ^N` of length at most `N H(ξ) − c√N` decodes correctly with probability at most `ε`.  (Part (a)
needs no change beyond using the first declaration of this problem in place of Theorem 149.)
SUV Problem 240, p. 232. -/
private lemma Kolmogorov.probOfPred_le_of_subset_uncond {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω)
    (P Q : Ω → Prop) (h : ∀ ω, P ω → Q ω) :
    μ.probOfPred P ≤ μ.probOfPred Q := by
  unfold FiniteProbSpace.probOfPred
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω
  · have hQ : Q ω := h ω hP
    have eqP : {ω | P ω}.indicator μ.prob ω = μ.prob ω := Set.indicator_of_mem (f := μ.prob) hP
    have eqQ : {ω | Q ω}.indicator μ.prob ω = μ.prob ω := Set.indicator_of_mem (f := μ.prob) hQ
    rw [eqP, eqQ]
  · have eqP : {ω | P ω}.indicator μ.prob ω = 0 := Set.indicator_of_notMem (f := μ.prob) hP
    rw [eqP]
    exact Set.indicator_nonneg (fun _ _ => μ.prob_nonneg _) _

private lemma Kolmogorov.probOfPred_congr_uncond {Ω : Type*} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (P Q : Ω → Prop) (h : ∀ ω, P ω ↔ Q ω) :
    μ.probOfPred P = μ.probOfPred Q := by
  have hset : {ω | P ω} = {ω | Q ω} := Set.ext h
  unfold FiniteProbSpace.probOfPred
  rw [hset]

private lemma Kolmogorov.exists_nat_power_prob_sum_gt_uncond {Ω : Type*} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (f : Ω → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N : ℕ,
      (μ.power N).probOfPred
        (fun w => (N : ℝ) * μ.expect f - c * Real.sqrt N > ∑ i, f (w i)) ≤ ε := by
  obtain ⟨c, hc⟩ := Kolmogorov.exists_const_prob_abs_sum_sub_gt_le μ f hε
  refine ⟨c, fun N => ?_⟩
  have h_bound := hc N
  have h_subset : ∀ w : Fin N → Ω,
      (N : ℝ) * μ.expect f - c * Real.sqrt N > ∑ i, f (w i) →
      c * Real.sqrt N < |∑ i, f (w i) - (N : ℝ) * μ.expect f| := by
    intro w hw
    have h1 : (N : ℝ) * μ.expect f - ∑ i, f (w i) > c * Real.sqrt N := by linarith
    have h2 : (N : ℝ) * μ.expect f - ∑ i, f (w i) =
        - (∑ i, f (w i) - (N : ℝ) * μ.expect f) := by ring
    rw [h2] at h1
    calc c * Real.sqrt N < - (∑ i, f (w i) - (N : ℝ) * μ.expect f) := h1
      _ ≤ |∑ i, f (w i) - (N : ℝ) * μ.expect f| := neg_le_abs _
  have h_subset_app : ∀ w : Fin N → Ω,
      ((N : ℝ) * μ.expect f - c * Real.sqrt N > ∑ i, f (w i)) →
      (c * Real.sqrt N < |∑ i, f (w i) - (N : ℝ) * μ.expect f|) := h_subset
  exact (Kolmogorov.probOfPred_le_of_subset_uncond (μ.power N) _ _ h_subset_app).trans h_bound

private lemma Kolmogorov.prob_correct_ge_le_uncond {A : Type*} [Fintype A] (μ : FiniteProbSpace A)
    (N m : ℕ) (t : ℝ) (e : (Fin N → A) → Fin m → Bool) (d : (Fin m → Bool) → Fin N → A) :
    (μ.power N).probOfPred
      (fun w => d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ≤
      (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) := by
  classical
  have hpt : ∀ w : Fin N → A,
      Set.indicator {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))} (μ.power N).prob w ≤
        (2 : ℝ) ^ (-t) * (if d (e w) = w then (1 : ℝ) else 0) := by
    intro w
    by_cases hmem : w ∈ {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))}
    · rw [Set.indicator_of_mem hmem]
      obtain ⟨hcorr, _⟩ := hmem
      rw [ite_eq_left hcorr, mul_one]
      rcases eq_or_lt_of_le ((μ.power N).prob_nonneg w) with h0 | hpos
      · rw [← h0]; positivity
      · have hfac : (μ.power N).prob w = (2 : ℝ) ^ (-∑ i, -Real.logb 2 (μ.prob (w i))) := by
          have hP' : 0 < ∏ i, μ.prob (w i) := hpos
          have hne : ∀ i ∈ (Finset.univ : Finset (Fin N)), μ.prob (w i) ≠ 0 :=
            Finset.prod_ne_zero_iff.1 hP'.ne'
          have hq0 : ∀ i, 0 < μ.prob (w i) := fun i =>
            lt_of_le_of_ne (μ.prob_nonneg _) (hne i (Finset.mem_univ i)).symm
          calc (μ.power N).prob w = ∏ i, μ.prob (w i) := rfl
            _ = ∏ i, 2 ^ Real.logb 2 (μ.prob (w i)) :=
              Finset.prod_congr rfl fun i _ =>
                (Real.rpow_logb (by norm_num) (by norm_num) (hq0 i)).symm
            _ = 2 ^ ∑ i, Real.logb 2 (μ.prob (w i)) := by
              rw [← Real.rpow_sum_of_pos (by norm_num) _ _]
            _ = 2 ^ (-∑ i, -Real.logb 2 (μ.prob (w i))) := by
              rw [Finset.sum_neg_distrib, neg_neg]
        rw [hfac]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
    · rw [Set.indicator_of_notMem hmem]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by split_ifs <;> norm_num)
  have hsum_indicator : (μ.power N).probOfPred
        (fun w => d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) =
      ∑ w : Fin N → A,
        Set.indicator {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))} (μ.power N).prob w :=
    rfl
  have hsum_le : ∑ w : Fin N → A,
        Set.indicator {w | d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))} (μ.power N).prob w ≤
      ∑ w : Fin N → A, (2 : ℝ) ^ (-t) * (if d (e w) = w then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun i _ => hpt i
  rw [hsum_indicator]
  apply hsum_le.trans
  rw [← Finset.mul_sum]
  have hcard : ∑ w : Fin N → A, (if d (e w) = w then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (m : ℝ) := by
    let S : Finset (Fin N → A) := Finset.filter (fun w => d (e w) = w) Finset.univ
    have h1 : ∑ w : Fin N → A, (if d (e w) = w then (1 : ℝ) else 0) = S.card := by
      rw [Finset.sum_ite]; simp [S]
    rw [h1]
    have h_inj : ∀ w₁ w₂ : S, e w₁ = e w₂ → w₁ = w₂ := by
      intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h_eq
      apply Subtype.ext
      change w₁ = w₂
      have h_w1 : w₁ = d (e w₁) := (Finset.mem_filter.mp hw₁).2.symm
      have h_w2 : w₂ = d (e w₂) := (Finset.mem_filter.mp hw₂).2.symm
      rw [h_w1, h_w2, h_eq]
    have h_card_S_le_card_codomain : Fintype.card S ≤ Fintype.card (Fin m → Bool) :=
      Fintype.card_le_of_injective (fun w => e w) h_inj
    have h_card_codomain : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
    have h_S_card : (S.card : ℝ) = (Fintype.card S : ℝ) := by simp
    rw [h_S_card]
    have h_card_S_le_2_m : (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast (h_card_S_le_card_codomain.trans h_card_codomain.le)
    have h_2_m : (2 : ℝ) ^ m = (2 : ℝ) ^ (m : ℝ) := by
      exact Real.rpow_natCast 2 m |>.symm
    rw [← h_2_m]
    exact h_card_S_le_2_m
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-t) := Real.rpow_nonneg (by norm_num) _
  have h1 : (2 : ℝ) ^ (-t) * (∑ i : Fin N → A, if d (e i) = i then (1 : ℝ) else 0) =
      (∑ i : Fin N → A, if d (e i) = i then (1 : ℝ) else 0) * (2 : ℝ) ^ (-t) := mul_comm _ _
  rw [h1]
  exact mul_le_mul_of_nonneg_right hcard hpos

/-- **Theorem 151(b) for arbitrary real probabilities.**  The converse half of the coding theorem
holds without the computability assumption that its proof through complexity uses: any code for
`ξ^N` of length at most `N H(ξ) − c√N` decodes correctly with probability at most `ε`.  (Part (a)
needs no change beyond using the first declaration of this problem in place of Theorem 149.)
SUV Problem 240, p. 232. -/
theorem exists_const_prob_correct_le_of_real (A : Type*) [Fintype A]
    (μ : FiniteProbSpace A) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N m : ℕ, 0 < N → (m : ℝ) ≤ (N : ℝ) * entropyDist μ.prob - c * Real.sqrt N →
      ∀ (e : (Fin N → A) → Fin m → Bool) (d : (Fin m → Bool) → Fin N → A),
        (μ.power N).probOfPred (fun w => d (e w) = w) ≤ ε := by
  classical
  set H : ℝ := entropyDist μ.prob with hH
  have hH_eq : H = entropyDist μ.prob := rfl
  have h_half_eps_pos : 0 < ε / 2 := half_pos hε
  obtain ⟨c₁, hc₁⟩ := Kolmogorov.exists_nat_power_prob_sum_gt_uncond μ
      (fun a => -Real.logb 2 (μ.prob a)) h_half_eps_pos
  obtain ⟨c₂, hc₂pow⟩ := exists_nat_gt (2 / ε)
  refine ⟨c₁ + c₂, fun N m hN hm e d => ?_⟩
  push_cast at hm
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  set t : ℝ := (N : ℝ) * H - c₁ * Real.sqrt N with ht
  have hsplit : (μ.power N).probOfPred (fun w => d (e w) = w) ≤
      (μ.power N).probOfPred
        (fun w => d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) +
      (μ.power N).probOfPred (fun w => ∑ i, -Real.logb 2 (μ.prob (w i)) < t) := by
    apply Kolmogorov.probOfPred_le_add_of_imp
    intro w hcorr
    by_cases hgt : t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))
    · exact Or.inl ⟨hcorr, hgt⟩
    · exact Or.inr (lt_of_not_ge hgt)
  have hterm2 : (μ.power N).probOfPred (fun w => ∑ i, -Real.logb 2 (μ.prob (w i)) < t) ≤ ε / 2 := by
    have hkey := hc₁ N
    have hexp : μ.expect (fun a => -Real.logb 2 (μ.prob a)) = H := by
      rw [hH_eq]
      exact Kolmogorov.expect_neg_logb_prob A μ
    have hpredeq : ∀ w : Fin N → A,
        (∑ i, -Real.logb 2 (μ.prob (w i)) < t) ↔
        (N : ℝ) * μ.expect (fun a => -Real.logb 2 (μ.prob a)) - c₁ * Real.sqrt N >
          ∑ i, -Real.logb 2 (μ.prob (w i)) := by
      intro w
      rw [hexp]
    have heq : (μ.power N).probOfPred (fun w => ∑ i, -Real.logb 2 (μ.prob (w i)) < t) =
        (μ.power N).probOfPred
          (fun w => (N : ℝ) * μ.expect (fun a => -Real.logb 2 (μ.prob a)) - c₁ * Real.sqrt N >
            ∑ i, -Real.logb 2 (μ.prob (w i))) := by
      apply Kolmogorov.probOfPred_congr_uncond
      exact hpredeq
    rw [heq]
    exact hkey
  have hterm1 : (μ.power N).probOfPred
      (fun w => d (e w) = w ∧ t ≤ ∑ i, -Real.logb 2 (μ.prob (w i))) ≤ ε / 2 := by
    have hbound := Kolmogorov.prob_correct_ge_le_uncond μ N m t e d
    have hpow : (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) ≤ ε / 2 := by
      have h1 : (m : ℝ) - t ≤ - c₂ * Real.sqrt N := by
        calc (m : ℝ) - t = (m : ℝ) - ((N : ℝ) * H - c₁ * Real.sqrt N) := by rw [ht]
          _ ≤ ((N : ℝ) * H - (c₁ + c₂) * Real.sqrt N) - ((N : ℝ) * H - c₁ * Real.sqrt N) := by
            apply sub_le_sub_right
            have hc1c2 : (c₁ + c₂ : ℝ) = (c₁ : ℝ) + (c₂ : ℝ) := by rfl
            rw [hc1c2]
            linarith
          _ = - (c₂ : ℝ) * Real.sqrt N := by ring
      have h2 : (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (-t) = (2 : ℝ) ^ ((m : ℝ) - t) := by
        rw [← Real.rpow_add (by norm_num)]
        have h_sub : (m : ℝ) + -t = (m : ℝ) - t := rfl
        rw [h_sub]
      rw [h2]
      calc (2 : ℝ) ^ ((m : ℝ) - t) ≤ (2 : ℝ) ^ (- (c₂ : ℝ) * Real.sqrt N) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ ≤ (2 : ℝ) ^ (- (c₂ : ℝ) * 1) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have hc2nn : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg c₂
            nlinarith
        _ = (2 : ℝ) ^ (- (c₂ : ℝ)) := by ring_nf
        _ = ((2 : ℝ) ^ (c₂ : ℝ))⁻¹ := by
            rw [Real.rpow_neg (by norm_num)]
        _ ≤ ε / 2 := by
            have hc2pos : 2 / ε < c₂ := by exact_mod_cast hc₂pow
            have hc2_pow_gt : 2 / ε < (2 : ℝ) ^ (c₂ : ℝ) := by
              calc 2 / ε < c₂ := hc2pos
                _ ≤ (2 : ℝ) ^ (c₂ : ℝ) := by
                  have h_le : (c₂ : ℝ) ≤ (2 : ℝ) ^ (c₂ : ℝ) := by
                    have h_nat : (c₂ : ℝ) ≤ (2 : ℝ) ^ c₂ := by
                      exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 2) |>.le
                    have h_rpow : (2 : ℝ) ^ c₂ = (2 : ℝ) ^ (c₂ : ℝ) := by
                      rw [Real.rpow_natCast]
                    rw [← h_rpow]
                    exact h_nat
                  exact h_le
            have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (c₂ : ℝ) :=
              Real.rpow_pos_of_pos (by norm_num) _
            have h_inv : ((2 : ℝ) ^ (c₂ : ℝ))⁻¹ < (2 / ε)⁻¹ :=
              (inv_lt_inv₀ h_pow_pos (div_pos (by norm_num) hε)).mpr hc2_pow_gt
            have h_eps : (2 / ε)⁻¹ = ε / 2 := inv_div 2 ε
            rw [h_eps] at h_inv
            exact h_inv.le
    exact hbound.trans hpow
  linarith

end Kolmogorov
