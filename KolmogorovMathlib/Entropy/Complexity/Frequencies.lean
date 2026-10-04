/-
Copyright (c) 2024 The KolmogorovMathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Contributors
-/
import KolmogorovMathlib.Entropy.Complexity.Basic
import KolmogorovMathlib.Entropy.Subtuples
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.CommonInformation.TypeBounds
import KolmogorovMathlib.CommonInformation.FixedHistogram
import KolmogorovMathlib.CommonInformation.FixedHistogramRank.PlainAndFibreDecoders
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Complexity and the entropy of the letter frequencies

SUV Section 7.3.1, pp. 226–227.

For a word `x` of length `N` over a `k`-letter alphabet with letter frequencies `p₁, …, p_k`,
Theorem 146 bounds the plain complexity of `x` by `N h(p₁, …, p_k) + O(log N)`, where the constant
hidden in `O(log N)` depends on `k` but not on `N`, on `x` or on the frequencies.

The proof described in the book identifies `x` by its ordinal number in the set of words with the
same frequencies, whose size is the multinomial coefficient `N! / ((p₁N)! ⋯ (p_kN)!)`.  The
combinatorial half of that argument is the displayed inequality
`N! / ∏_i n_i! ≤ 2^{N h(n/N)}`, stated here as `card_typeClass_le_rpow_entropy`; it holds exactly,
with no Stirling approximation, for the set `typeClass N c` of words with prescribed letter
counts.

`freq w a` is the *number of occurrences* of the letter `a` in the word `w`, so the book's
frequency `p_a` of that letter is `freq w a / N`, and that quotient is what the statements below
feed to the entropy.

The complexity of a word over a `k`-letter alphabet is the complexity of its fixed block encoding
`finWordBits`, as fixed in `KolmogorovMathlib.Entropy.Complexity.Basic`.  The `ℕ∞`-valued
complexity is read through `ENat.toNat`, which is faithful here because an optimal decompressor
gives every string a finite complexity.  `logSlack c N` is the library's `O(log N)`.
-/

namespace Kolmogorov

open Finset

/-! ### The multinomial bound -/

private theorem count_ofFn_eq_freq {α : Type*} [DecidableEq α] :
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

private theorem card_typeClass_eq_multinomial {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (c : α → ℕ) (hc : ∑ a, c a = N) :
    (typeClass N c).card = Nat.multinomial Finset.univ c := by
  let m := Fintype.card α
  let e : α ≃ Fin m := Fintype.equivFin α
  let f : Fin m → ℕ := fun i => c (e.symm i)
  have hf : ∑ i, f i = N := by
    rw [show (∑ i, f i) = ∑ a, c a by simpa [f] using Equiv.sum_comp e.symm c, hc]
  have hmulti : Nat.multinomial Finset.univ f = Nat.multinomial Finset.univ c := by
    unfold Nat.multinomial
    have hsum : ∑ i, f i = ∑ a, c a := by
      simpa [f] using Equiv.sum_comp e.symm c
    have hprod : ∏ i, (f i).factorial = ∏ a, (c a).factorial := by
      simpa [f] using Equiv.prod_comp e.symm (fun a => (c a).factorial)
    rw [hsum, hprod]
  rw [← hmulti, ← length_fixedHistogramWords]
  rw [← List.toFinset_card_of_nodup (fixedHistogramWords_nodup f)]
  by_cases hm : m = 0
  · let : IsEmpty (Fin m) := ⟨fun i => by have := i.isLt; omega⟩
    have hf0 : ∀ i, f i = 0 := fun i => isEmptyElim i
    have hN : N = 0 := by
      rw [← hf]
      simp [hf0]
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by simpa [m] using hm)
    subst N
    simp [typeClass, fixedHistogramWords, allWords, hf0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  refine Finset.card_bij
    (fun w _ => List.ofFn fun i => e (w i)) ?_ ?_ ?_
  · intro w hw
    rw [List.mem_toFinset, mem_fixedHistogramWords]
    refine ⟨by simp [hf], fun i => ?_⟩
    have hwc := (mem_typeClass.mp hw) (e.symm i)
    change (List.ofFn (e ∘ w)).count i = f i
    rw [← List.map_ofFn]
    conv_lhs => rw [← e.apply_symm_apply i]
    rw [List.count_map_of_injective _ e e.injective (e.symm i),
      count_ofFn_eq_freq]
    simpa [f]
  · intro w hw v hv heq
    apply funext
    intro i
    have := congrArg (fun z => z[i.val]?) heq
    simpa using this
  · intro z hz
    have hz' := (mem_fixedHistogramWords f z).mp (List.mem_toFinset.mp hz)
    have hzlen : z.length = N := hz'.1.trans hf
    let w : Fin N → α := fun i => e.symm (z.get ⟨i, by rw [hzlen]; exact i.isLt⟩)
    have hof : (List.ofFn w).map e = z := by
      apply List.ext_getElem
      · simp [hzlen]
      · intro i hi₁ hi₂
        simp [w]
    refine ⟨w, ?_, ?_⟩
    · rw [mem_typeClass]
      intro a
      have hcount := hz'.2 (e a)
      rw [← count_ofFn_eq_freq w a,
        ← List.count_map_of_injective (List.ofFn w) e e.injective a, hof, hcount]
      simp [f]
    · change List.ofFn (e ∘ w) = z
      rw [← List.map_ofFn]
      exact hof

private theorem multinomial_cast_mul_prod_pow_le {α : Type*} [Fintype α]
    (N : ℕ) (c : α → ℕ) (hc : ∑ a, c a = N) :
    (Nat.multinomial Finset.univ c : ℝ) * ∏ a, (c a : ℝ) ^ c a ≤ (N : ℝ) ^ N := by
  classical
  have hmem : c ∈ Finset.piAntidiag (Finset.univ : Finset α) N := by
    simp [Finset.mem_piAntidiag, hc]
  exact_mod_cast multinomial_mul_typeProb_le_one Finset.univ c N hmem

private theorem coordinate_entropy_identity (N k : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ ((N : ℝ) * negMulLog2 ((k : ℝ) / N)) * (k : ℝ) ^ k =
      (N : ℝ) ^ k := by
  by_cases hk : k = 0
  · simp [hk]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [negMulLog2, Real.negMulLog_eq_neg]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hdiv : (k : ℝ) / N > 0 := div_pos hkr hNr
  rw [show Real.log 2 * ((N : ℝ) *
      (-((k : ℝ) / N * Real.log ((k : ℝ) / N)) / Real.log 2)) =
      -(k : ℝ) * Real.log ((k : ℝ) / N) by field_simp]
  rw [show -(k : ℝ) * Real.log ((k : ℝ) / N) =
      -(Real.log ((k : ℝ) / N) * (k : ℝ)) by ring]
  rw [Real.exp_neg, Real.exp_mul, Real.exp_log hdiv, Real.rpow_natCast]
  rw [div_pow]
  field_simp

private theorem rpow_entropy_mul_prod_pow {α : Type*} [Fintype α]
    (N : ℕ) (c : α → ℕ) (hc : ∑ a, c a = N) :
    (2 : ℝ) ^ ((N : ℝ) * entropyDist fun a => (c a : ℝ) / N) *
        ∏ a, (c a : ℝ) ^ c a = (N : ℝ) ^ N := by
  by_cases hN : N = 0
  · have hsum0 : ∑ a, c a = 0 := hc.trans hN
    subst N
    have hc0 : ∀ a, c a = 0 := by
      intro a
      exact Finset.sum_eq_zero_iff.mp hsum0 a (Finset.mem_univ a)
    simp [entropyDist, hc0]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [entropyDist, Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
  rw [← Finset.prod_mul_distrib]
  simp_rw [coordinate_entropy_identity N _ hNpos]
  rw [Finset.prod_pow_eq_pow_sum, hc]

/-- **The multinomial bound.**  The number of words of length `N` with prescribed letter counts
`c` is at most `2^{N h(c/N)}`, where `h` is the entropy of the frequency distribution.  This is
the displayed estimate of the proof of Theorem 146; it is exact and needs no Stirling
approximation.  SUV Section 7.3.1, p. 226. -/
theorem card_typeClass_le_rpow_entropy {α : Type*} [Fintype α] [DecidableEq α] (N : ℕ)
    (c : α → ℕ) (hc : ∑ a, c a = N) :
    ((typeClass N c).card : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * entropyDist fun a => (c a : ℝ) / N) := by
  rw [card_typeClass_eq_multinomial N c hc]
  have hbound := multinomial_cast_mul_prod_pow_le N c hc
  rw [← rpow_entropy_mul_prod_pow N c hc] at hbound
  refine le_of_mul_le_mul_right hbound (Finset.prod_pos fun a _ => ?_)
  by_cases hca : c a = 0
  · simp [hca]
  · positivity

/-! ### An efficient histogram code with leading coefficient `k`

The plain decoder `fixedHistogramPlainDecoder` spends `2·∑ᵢ |cᵢ|` bits on the histogram, giving a
`2k log N` term.  To reach the coefficient `k` promised by Problem 234 we transmit the histogram
differently: a single self-delimiting number `W` (the common bit width, of size `O(log log N)`),
then each of the `k` counts in exactly `W` bits, then the rank as the trailing bits.  The counts
now cost `k·W = k·|N|` bits, and `W` itself only `O(log log N)`. -/

/-- Read `k` blocks of `W` bits each off the front of a bit string, as numbers. -/
private def readCounts (W : ℕ) : ℕ → BitString → List ℕ
  | 0, _ => []
  | (n + 1), z => decodeFixedWidthNatCode (z.take W) :: readCounts W n (z.drop W)

/-- Write a list of numbers as consecutive `W`-bit blocks. -/
private def writeBlocks (W : ℕ) : List ℕ → BitString
  | [] => []
  | (x :: xs) => fixedWidthNatCode x W ++ writeBlocks W xs

private theorem writeBlocks_length (W : ℕ) (cs : List ℕ) (h : ∀ x ∈ cs, x < 2 ^ W) :
    (writeBlocks W cs).length = cs.length * W := by
  induction cs with
  | nil => simp [writeBlocks]
  | cons x xs ih =>
      have hx : x < 2 ^ W := h x (by simp)
      rw [writeBlocks, List.length_append, fixedWidthNatCode_length hx,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy)), List.length_cons]
      ring

private theorem readCounts_writeBlocks (W : ℕ) (cs : List ℕ) (tail : BitString)
    (h : ∀ x ∈ cs, x < 2 ^ W) :
    readCounts W cs.length (writeBlocks W cs ++ tail) = cs := by
  induction cs generalizing tail with
  | nil => simp [readCounts, writeBlocks]
  | cons x xs ih =>
      have hx : x < 2 ^ W := h x (by simp)
      have hlen : (fixedWidthNatCode x W).length = W := fixedWidthNatCode_length hx
      have e1 : (fixedWidthNatCode x W ++ (writeBlocks W xs ++ tail)).take W
          = fixedWidthNatCode x W := List.take_left' hlen
      have e2 : (fixedWidthNatCode x W ++ (writeBlocks W xs ++ tail)).drop W
          = writeBlocks W xs ++ tail := List.drop_left' hlen
      simp only [List.length_cons, writeBlocks, List.append_assoc, readCounts]
      rw [e1, e2, decodeFixedWidthNatCode_encode,
        ih tail (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem readCounts_primrec (k : ℕ) :
    Primrec (fun p : ℕ × BitString => readCounts p.1 k p.2) := by
  induction k with
  | zero => simpa [readCounts] using (Primrec.const ([] : List ℕ))
  | succ k ih =>
      have hdrop : Primrec (fun p : ℕ × BitString => (p.1, p.2.drop p.1)) :=
        Primrec.pair Primrec.fst (primrec_list_drop.comp Primrec.snd Primrec.fst)
      have hrest : Primrec (fun p : ℕ × BitString => readCounts p.1 k (p.2.drop p.1)) :=
        ih.comp hdrop
      have htake : Primrec (fun p : ℕ × BitString => decodeFixedWidthNatCode (p.2.take p.1)) :=
        decodeFixedWidthNatCode_primrec.comp (primrec_list_take.comp Primrec.snd Primrec.fst)
      exact (Primrec.list_cons.comp htake hrest).of_eq (fun _ => rfl)

/-- The efficient plain decoder for a fixed `k`-letter alphabet: it reads the common width `W`,
then `k` counts of `W` bits each, then the rank as the trailing bits. -/
private def freqPlainDecoder (k : ℕ) : Map := fun pr =>
  Part.some
    (((numericFixedHistogramWords
        ((List.range k).map (fun i =>
          (i, (readCounts (bitsToNat (decodeFirst pr.1)) k (decodeSecond pr.1)).getD i 0)))).map
      numericWordCode).getD
      (bitsToNat ((decodeSecond pr.1).drop (k * bitsToNat (decodeFirst pr.1)))) [])

private theorem freqPlainDecoder_isDecompressor (k : ℕ) :
    isDecompressor (freqPlainDecoder k) := by
  have hW : Primrec (fun pr : BitString × BitString => bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst)
  have hbody : Primrec (fun pr : BitString × BitString => decodeSecond pr.1) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hcounts : Primrec (fun pr : BitString × BitString =>
      readCounts (bitsToNat (decodeFirst pr.1)) k (decodeSecond pr.1)) :=
    (readCounts_primrec k).comp (Primrec.pair hW hbody)
  have htable : Primrec (fun pr : BitString × BitString =>
      (List.range k).map (fun i =>
        (i, (readCounts (bitsToNat (decodeFirst pr.1)) k (decodeSecond pr.1)).getD i 0))) :=
    Primrec.list_map (Primrec.const (List.range k))
      (Primrec.pair Primrec.snd
        ((Primrec.list_getD (0 : ℕ)).comp (hcounts.comp Primrec.fst) Primrec.snd)).to₂
  have hlist : Primrec (fun pr : BitString × BitString =>
      (numericFixedHistogramWords
        ((List.range k).map (fun i =>
          (i, (readCounts (bitsToNat (decodeFirst pr.1)) k (decodeSecond pr.1)).getD i 0)))).map
        numericWordCode) :=
    Primrec.list_map (numericFixedHistogramWords_primrec.comp htable)
      (numericWordCode_primrec.comp Primrec.snd).to₂
  have hrank : Primrec (fun pr : BitString × BitString =>
      bitsToNat ((decodeSecond pr.1).drop (k * bitsToNat (decodeFirst pr.1)))) :=
    bitsToNat_primrec.comp
      (primrec_list_drop.comp hbody (Primrec.nat_mul.comp (Primrec.const k) hW))
  exact (((Primrec.list_getD ([] : BitString)).comp hlist hrank).to_comp).partrec

private theorem freqPlainDecoder_recovers (k : ℕ) (v : List (Fin k)) (W : ℕ)
    (hW : ∀ i : Fin k, v.count i < 2 ^ W) :
    ∃ p, p.length ≤ 2 * Nat.size W + 1 + k * W +
        Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) ∧
      produces (freqPlainDecoder k) p [] (finiteWordCode v) := by
  classical
  set f : Fin k → ℕ := fun i => v.count i with hf
  set cs : List ℕ := List.ofFn f with hcs
  have hcslen : cs.length = k := by rw [hcs, List.length_ofFn]
  have hcsW : ∀ x ∈ cs, x < 2 ^ W := by
    intro x hx
    rw [hcs, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hW i
  set table : List (ℕ × ℕ) :=
    (List.finRange k).map (fun i : Fin k => (FiniteLetterCode.encode i, f i)) with htable
  set L : List BitString := (numericFixedHistogramWords table).map numericWordCode with hL
  have hnd : (List.finRange k).Nodup := List.nodup_finRange k
  have hcomp : ∀ i : Fin k, i ∈ List.finRange k := fun i => List.mem_finRange i
  have hmemtab : v.map Fin.val ∈ numericFixedHistogramWords table := by
    rw [htable]
    exact (mem_numericTable f (List.finRange k) hnd hcomp _).mpr ⟨v, fun _ => rfl, rfl⟩
  have hmem : finiteWordCode v ∈ L := by
    rw [hL, List.mem_map]
    exact ⟨v.map Fin.val, hmemtab, (finiteWordCode_eq_numericWordCode v).symm⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlenL : L.length = Nat.multinomial univ f := by
    rw [hL, List.length_map, htable, length_numericTableFin f (List.finRange k) hnd hcomp]
  have hi_lt : i < Nat.multinomial univ f := by rw [← hlenL]; exact hi
  set p : BitString := pairCode (Nat.bits W) (writeBlocks W cs ++ Nat.bits i) with hp
  have hwblen : (writeBlocks W cs).length = k * W := by
    rw [writeBlocks_length W cs hcsW, hcslen]
  have htab_eq : (List.range k).map (fun j => (j, cs.getD j 0)) = table := by
    rw [htable]
    apply List.ext_getElem
    · simp
    · intro j h1 _
      have hjk : j < k := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.cast_mk]
      rw [Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      rw [hcs, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hjk), List.getElem_ofFn]
  refine ⟨p, ?_, ?_⟩
  · rw [hp, length_pairCode, List.length_append, hwblen, Nat.size_eq_bits_len W,
      Nat.size_eq_bits_len i]
    have hrank_le : Nat.size i ≤ Nat.size (Nat.multinomial univ f) :=
      Nat.size_le_size (le_of_lt hi_lt)
    omega
  · change finiteWordCode v ∈ freqPlainDecoder k (p, [])
    unfold freqPlainDecoder
    rw [Part.mem_some_iff]
    have hW' : bitsToNat (decodeFirst p) = W := by
      rw [hp, decodeFirst_pairCode, bitsToNat_bits]
    have hbd : decodeSecond p = writeBlocks W cs ++ Nat.bits i := by
      rw [hp, decodeSecond_pairCode]
    rw [hW', hbd]
    have hrc : readCounts W k (writeBlocks W cs ++ Nat.bits i) = cs := by
      rw [← hcslen]; exact readCounts_writeBlocks W cs (Nat.bits i) hcsW
    have hdrop : (writeBlocks W cs ++ Nat.bits i).drop (k * W) = Nat.bits i := by
      rw [← hwblen]; exact List.drop_left
    rw [hrc, htab_eq, hdrop, bitsToNat_bits, ← hL,
      List.getD_eq_getElem _ _ (by rw [hlenL]; exact hi_lt), hget]

/-- Describing a `Fin k`-word from nothing costs the log of its type-class size plus `k·|W|` bits
for the counts and `O(|W|)` bits for the common width. -/
private theorem plainK_finiteWordCode_le (k : ℕ) (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (v : List (Fin k)) (W : ℕ), (∀ i : Fin k, v.count i < 2 ^ W) →
      plainK D (finiteWordCode v) ≤
        ((2 * Nat.size W + 1 + k * W +
          Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) : ℕ) : ENat) + c := by
  obtain ⟨c, hc⟩ := hD.2 (freqPlainDecoder k) (freqPlainDecoder_isDecompressor k)
  refine ⟨c, fun v W hW => ?_⟩
  obtain ⟨p, hplen, hprod⟩ := freqPlainDecoder_recovers k v W hW
  have hDp : plainK (freqPlainDecoder k) (finiteWordCode v) ≤ (p.length : ENat) :=
    sInf_le ⟨p, hprod, rfl⟩
  calc plainK D (finiteWordCode v)
      ≤ plainK (freqPlainDecoder k) (finiteWordCode v) + (c : ENat) := hc _ _
    _ ≤ (p.length : ENat) + c := by gcongr
    _ ≤ ((2 * Nat.size W + 1 + k * W +
          Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) : ℕ) : ENat) + c := by
        have hle : p.length + c ≤
            (2 * Nat.size W + 1 + k * W +
              Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i))) + c :=
          Nat.add_le_add_right hplen c
        exact_mod_cast hle

/-- The log of the multinomial coefficient is at most `N·H(c/N) + 1`, where `H` is the entropy of
the frequency distribution.  This is the combinatorial estimate `card_typeClass_le_rpow_entropy`
read through `Nat.size`. -/
private theorem size_multinomial_le (A : Type*) [Fintype A]
    (N : ℕ) (c : A → ℕ) (hc : ∑ a, c a = N) :
    (Nat.size (Nat.multinomial univ c) : ℝ) ≤
      (N : ℝ) * entropyDist (fun a => (c a : ℝ) / N) + 1 := by
  classical
  have hcard := card_typeClass_le_rpow_entropy N c hc
  rw [card_typeClass_eq_multinomial N c hc] at hcard
  set H := entropyDist (fun a => (c a : ℝ) / N) with hH
  have hH0 : 0 ≤ H := by
    rw [hH, entropyDist]
    refine Finset.sum_nonneg (fun a _ => ?_)
    refine negMulLog2_nonneg (by positivity) ?_
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · rw [div_le_one (by exact_mod_cast hN)]
      have : c a ≤ N := hc ▸ Finset.single_le_sum (fun b _ => Nat.zero_le (c b)) (Finset.mem_univ a)
      exact_mod_cast this
  have hNH0 : 0 ≤ (N : ℝ) * H := mul_nonneg (Nat.cast_nonneg _) hH0
  have hlt : (Nat.multinomial univ c : ℝ) < 2 ^ (⌊(N : ℝ) * H⌋₊ + 1) := by
    calc (Nat.multinomial univ c : ℝ) ≤ 2 ^ ((N : ℝ) * H) := hcard
      _ < 2 ^ ((⌊(N : ℝ) * H⌋₊ + 1 : ℕ) : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
            (by push_cast; exact Nat.lt_floor_add_one _)
      _ = 2 ^ (⌊(N : ℝ) * H⌋₊ + 1) := by rw [Real.rpow_natCast]
  have hsize : Nat.size (Nat.multinomial univ c) ≤ ⌊(N : ℝ) * H⌋₊ + 1 :=
    Nat.size_le.2 (by exact_mod_cast hlt)
  have hsr : (Nat.size (Nat.multinomial univ c) : ℝ) ≤ (⌊(N : ℝ) * H⌋₊ : ℝ) + 1 := by
    exact_mod_cast hsize
  have hfloor : (⌊(N : ℝ) * H⌋₊ : ℝ) ≤ (N : ℝ) * H := Nat.floor_le hNH0
  linarith

private theorem nat_size_real_le (n : ℕ) : (Nat.size n : ℝ) ≤ Real.logb 2 n + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpow_nat : 2 ^ (n.size - 1) ≤ n :=
    Nat.lt_size.mp (by have : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn); omega)
  have hpow_real : (2 : ℝ) ^ (n.size - 1) ≤ (n : ℝ) := by exact_mod_cast hpow_nat
  have hlog : Real.logb 2 ((2 : ℝ) ^ (n.size - 1)) ≤ Real.logb 2 n :=
    (Real.logb_le_logb (by norm_num) (by positivity)
      (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hpow_real
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one] at hlog
  have h1n : 1 ≤ n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  push_cast [Nat.cast_sub h1n] at hlog
  linarith

private theorem logb_add_one_le (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x : ℝ, 0 ≤ x → Real.logb 2 (x + 1) ≤ ε * x + c := by
  set δ : ℝ := ε * Real.log 2 with hδ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδpos : 0 < δ := mul_pos hε hlog2
  refine ⟨(δ - 1 - Real.log δ) / Real.log 2, fun x hx => ?_⟩
  have hxpos : 0 < x + 1 := by linarith
  have hkey : Real.log (x + 1) ≤ δ * x + (δ - 1 - Real.log δ) := by
    have h1 : Real.log (δ * (x + 1)) ≤ δ * (x + 1) - 1 :=
      Real.log_le_sub_one_of_pos (mul_pos hδpos hxpos)
    rw [Real.log_mul (ne_of_gt hδpos) (ne_of_gt hxpos)] at h1
    nlinarith [h1]
  rw [Real.logb, div_le_iff₀ hlog2]
  have hrw : (ε * x + (δ - 1 - Real.log δ) / Real.log 2) * Real.log 2
      = δ * x + (δ - 1 - Real.log δ) := by rw [hδ]; field_simp
  rw [hrw]; exact hkey

private theorem two_size_size_le (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ N : ℕ, (2 * Nat.size (Nat.size N) : ℝ) ≤ ε * Real.logb 2 N + c := by
  obtain ⟨cR, hcR⟩ := logb_add_one_le (ε / 2) (by positivity)
  refine ⟨⌈2 * cR + 2⌉₊, fun N => ?_⟩
  have hcast : (2 : ℝ) * cR + 2 ≤ (⌈2 * cR + 2⌉₊ : ℝ) := Nat.le_ceil _
  by_cases hN : N = 0
  · subst hN
    simp only [Nat.size_zero, Nat.cast_zero, mul_zero, Real.logb_zero, mul_zero, zero_add]
    positivity
  have hL0 : 0 ≤ Real.logb 2 N :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN)
  have h1 : (Nat.size (Nat.size N) : ℝ) ≤ Real.logb 2 (Nat.size N) + 1 := nat_size_real_le _
  have h2 : (Nat.size N : ℝ) ≤ Real.logb 2 N + 1 := nat_size_real_le N
  have h3 : Real.logb 2 (Nat.size N) ≤ Real.logb 2 (Real.logb 2 N + 1) := by
    rcases Nat.eq_zero_or_pos (Nat.size N) with hs | hs
    · rw [hs]; simp only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by norm_num) (by linarith)
    · exact (Real.logb_le_logb (by norm_num) (by exact_mod_cast hs) (by linarith)).mpr h2
  have h4 : Real.logb 2 (Real.logb 2 N + 1) ≤ (ε / 2) * Real.logb 2 N + cR := hcR _ hL0
  have : (Nat.size (Nat.size N) : ℝ) ≤ (ε / 2) * Real.logb 2 N + cR + 1 := by linarith
  nlinarith [hcast, hL0, this]

/-! ### Theorem 146 -/

/-- **The complexity of a word is at most `N` times the entropy of its letter frequencies, up to
`O(log N)`.**  The constant is quantified before the length and the word, so it depends only on
the alphabet and on the decompressor, exactly as the book requires ("the constant in `O(log N)`
does not depend on `N`, `x` and the frequencies; however, this constant may depend on `k`").
The complexity is the plain complexity `C` of the block encoding of the word.
SUV Theorem 146, p. 226. -/
theorem exists_plainK_word_le_entropy_freq (A : Type*) [Fintype A] [DecidableEq A] [Encodable A]
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ) (w : Fin N → A),
      ((plainK D (finWordBits A w)).toNat : ℝ) ≤
        (N : ℝ) * (entropyDist fun a => (freq w a : ℝ) / N) + logSlack c N := by
  classical
  set k := Fintype.card A with hk
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
  refine ⟨3 * k + 2 * Nat.size k + c1 + c2 + 1, fun N w => ?_⟩
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
  set L : ℝ := (N : ℝ) * entropyDist (fun a => (freq w a : ℝ) / N) with hL
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
  have hf_freq : ∀ j, f j = freq w (e.symm j) := by
    intro j
    change (List.ofFn fun i => idx (w i)).count j = freq w (e.symm j)
    rw [count_ofFn_eq_freq]
    unfold freq
    congr 1
    ext i
    simp only [mem_filter, Finset.mem_univ, true_and]
    exact (e.eq_symm_apply).symm
  have hMfreq : M = Nat.multinomial univ (freq w) := by
    change Nat.multinomial univ f = Nat.multinomial univ (freq w)
    unfold Nat.multinomial
    have hsum : ∑ j, f j = ∑ a, freq w a := by
      rw [funext hf_freq]; exact Equiv.sum_comp e.symm (freq w)
    have hprod : ∏ j, (f j).factorial = ∏ a, (freq w a).factorial := by
      rw [funext hf_freq]; exact Equiv.prod_comp e.symm (fun a => (freq w a).factorial)
    rw [hsum, hprod]
  have hL0 : 0 ≤ L := by
    rw [hL]
    refine mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun a _ => ?_)
    refine negMulLog2_nonneg (by positivity) ?_
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · rw [div_le_one (by exact_mod_cast hN)]
      have hfle : freq w a ≤ N := by
        have h := Finset.single_le_sum (f := freq w) (fun b _ => Nat.zero_le _)
          (Finset.mem_univ a)
        rwa [sum_freq w] at h
      exact_mod_cast hfle
  have hMbound : (M : ℝ) ≤ (2 : ℝ) ^ L := by
    rw [hMfreq, hL, ← card_typeClass_eq_multinomial N (freq w) (sum_freq w)]
    exact card_typeClass_le_rpow_entropy N (freq w) (sum_freq w)
  have hM : (M : ℝ) < 2 ^ (⌊L⌋₊ + 1) := by
    calc (M : ℝ) ≤ 2 ^ L := hMbound
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
  have hsumr : ∑ j, ((f j).size : ℝ) ≤ (k : ℝ) * Nat.size N := by
    rw [← Nat.cast_sum]; exact_mod_cast hsum
  have hbits : ((Nat.bits N).length : ℝ) = (Nat.size N : ℝ) := by rw [Nat.size_eq_bits_len]
  have hNs : (0 : ℝ) ≤ Nat.size N := Nat.cast_nonneg _
  have hks : (0 : ℝ) ≤ Nat.size k := Nat.cast_nonneg _
  have hkc : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  simp only [logSlack]
  push_cast at hK' ⊢
  rw [hbits]
  nlinarith [hK', hsMr, hsumr, hNs, hks, hkc, mul_nonneg hNs hkc, mul_nonneg hNs hks,
    mul_nonneg hNs (Nat.cast_nonneg c1 : (0 : ℝ) ≤ c1),
    mul_nonneg hNs (Nat.cast_nonneg c2 : (0 : ℝ) ≤ c2)]

/-- **The constant hidden in the `O(log N)` of Theorem 146 is `k(1 + o(1))`.**  For every `ε > 0`
the bound of Theorem 146 holds with the explicit coefficient `k + ε` in front of `log N`, where
`k` is the number of letters of the alphabet.  The book asks for the value of the constant as a
function of `k` and answers `k(1 + o(1)) log N` in the hint; this is that answer.  The complexity
is the plain complexity of the block encoding `finWordBits` of the word.
SUV Problem 234, p. 227. -/
theorem exists_plainK_word_le_entropy_freq_card_logb (A : Type*) [Fintype A] [DecidableEq A]
    [Encodable A] (D : Map) (hD : isOptimalConditional D) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (N : ℕ) (w : Fin N → A),
      ((plainK D (finWordBits A w)).toNat : ℝ) ≤
        (N : ℝ) * (entropyDist fun a => (freq w a : ℝ) / N)
          + ((Fintype.card A : ℝ) + ε) * Real.logb 2 N + c := by
  classical
  set k := Fintype.card A with hkdef
  let idx : A → Fin k := fun a => ⟨alphabetIndex A a, alphabetIndex_lt_card a⟩
  have hbij : Function.Bijective idx := (Fintype.bijective_iff_injective_and_card idx).2
    ⟨fun a b h => alphabetIndex_injective (congrArg Fin.val h), by rw [Fintype.card_fin, hkdef]⟩
  let e := Equiv.ofBijective idx hbij
  let letterTable : List BitString := (List.range k).map (natBitsFixed (alphabetWidth A))
  let g : BitString → BitString := fun x =>
    ((Encodable.decode (bitsToNat x) : Option (List ℕ)).getD []).flatMap
      (fun n => letterTable.getD n [])
  have hg : Computable g := (Primrec.list_flatMap
    (Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec) (Primrec.const []))
    ((Primrec.list_getD []).comp (Primrec.const letterTable) Primrec.snd).to₂).to_comp
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD g hg
  obtain ⟨c2, hc2⟩ := plainK_finiteWordCode_le k D hD
  obtain ⟨cLog, hcLog⟩ := two_size_size_le ε hε
  refine ⟨c2 + c1 + cLog + k + 2, fun N w => ?_⟩
  set v : List (Fin k) := List.ofFn fun i => idx (w i) with hv
  have hgv : g (finiteWordCode v) = finWordBits A w := by
    have hmap : v.map FiniteLetterCode.encode = List.ofFn fun i => alphabetIndex A (w i) := by
      simp [hv, List.map_ofFn]; rfl
    simp only [g, finiteWordCode, bitsToNat_bits, hmap, Encodable.encodek, Option.getD_some]
    simp only [finWordBits, wordBits, Code.encodeWord, List.flatMap, List.map_ofFn]
    congr 2
    funext i
    have hi : alphabetIndex A (w i) < k := alphabetIndex_lt_card (w i)
    simp [letterTable, alphabetCode, List.getElem?_range hi]
  set W := Nat.size N with hWdef
  have hvlen : v.length = N := by rw [hv, List.length_ofFn]
  have hWcond : ∀ i : Fin k, v.count i < 2 ^ W := by
    intro i
    have hcv : v.count i ≤ N := by rw [← hvlen]; exact List.count_le_length
    rw [hWdef]; exact lt_of_le_of_lt hcv (Nat.lt_size_self N)
  have hcount : ∀ i : Fin k, v.count i = freq w (e.symm i) := by
    intro i
    have h1 : v.count i = freq (fun j => idx (w j)) i := by rw [hv]; exact count_ofFn_eq_freq _ i
    rw [h1]
    unfold freq
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show idx (w j) = e (w j) from rfl, ← e.eq_symm_apply]
  have hmuleq : Nat.multinomial univ (fun i : Fin k => v.count i)
      = Nat.multinomial univ (freq w) := by
    have hsum : (∑ i, v.count i) = ∑ a, freq w a := by
      rw [← Equiv.sum_comp e.symm (freq w)]
      exact Finset.sum_congr rfl (fun i _ => hcount i)
    have hprod : (∏ i, (v.count i).factorial) = ∏ a, (freq w a).factorial := by
      rw [← Equiv.prod_comp e.symm (fun a => (freq w a).factorial)]
      exact Finset.prod_congr rfl (fun i _ => by rw [hcount i])
    unfold Nat.multinomial
    rw [hsum, hprod]
  have hK : plainK D (finWordBits A w) ≤
      ((2 * Nat.size W + 1 + k * W +
        Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) + c2 + c1 : ℕ) : ENat) := by
    calc plainK D (finWordBits A w)
        = plainK D (g (finiteWordCode v)) := by rw [hgv]
      _ ≤ plainK D (finiteWordCode v) + c1 := hc1 _
      _ ≤ (((2 * Nat.size W + 1 + k * W +
            Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) : ℕ) : ENat)
            + c2) + c1 := by
          gcongr
          exact hc2 v W hWcond
      _ = ((2 * Nat.size W + 1 + k * W +
            Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i))
              + c2 + c1 : ℕ) : ENat) := by
          push_cast; ring
  have hK' : ((plainK D (finWordBits A w)).toNat : ℝ) ≤
      ((2 * Nat.size W + 1 + k * W +
        Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) + c2 + c1 : ℕ) : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hK
  set H := entropyDist (fun a => (freq w a : ℝ) / N) with hHdef
  have hsizemul : (Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) : ℝ)
      ≤ (N : ℝ) * H + 1 := by
    rw [hmuleq]; exact size_multinomial_le A N (freq w) (sum_freq w)
  have hkW : (k : ℝ) * (W : ℝ) ≤ (k : ℝ) * Real.logb 2 N + k := by
    rw [hWdef]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [nat_size_real_le N, hk0]
  have hdbl : (2 * (Nat.size W : ℝ)) ≤ ε * Real.logb 2 N + cLog := by
    rw [hWdef]; exact hcLog N
  push_cast at hK' ⊢
  rw [add_mul]
  nlinarith [hK', hsizemul, hkW, hdbl]

/-! ### Problem 235: keeping the square roots of Stirling's formula -/

/-- The upper half of Stirling's estimate: `n! ≤ e √n (n/e)^n` for `n ≥ 1`, since the Stirling
sequence `n! / (√(2n) (n/e)^n)` decreases from its first value `e/√2`. -/
private theorem factorial_le_exp_mul_sqrt_stirling (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * √(n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
  have h1 : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    simpa [Nat.add_comm] using this
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq, div_le_iff₀ (by positivity)] at h1
  refine h1.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by norm_num)]
  have h2 : (0 : ℝ) < √2 := by positivity
  field_simp

/-- **The multinomial coefficient with the square roots of Stirling's formula.**  For letter
counts `c` summing to `N ≥ 1`, `N!/∏ c_a! · ∏ √(c_a) ≤ e √N 2^{N h(c/N)}`: the upper Stirling
bound for `N!` over the lower Stirling bound for each `c_a!`. -/
private theorem multinomial_mul_prod_sqrt_le {α : Type*} [Fintype α] (N : ℕ) (hN : 0 < N)
    (c : α → ℕ) (hc : ∑ a, c a = N) :
    (Nat.multinomial univ c : ℝ) * ∏ a, √(c a : ℝ) ≤
      Real.exp 1 * √(N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * entropyDist fun a => (c a : ℝ) / N) := by
  classical
  set P : ℝ := ∏ a, (c a : ℝ) ^ c a with hPdef
  have hP : 0 < P := Finset.prod_pos fun a _ => by
    rcases Nat.eq_zero_or_pos (c a) with h | h
    · simp [h]
    · positivity
  have hE := rpow_entropy_mul_prod_pow N c hc
  have hspec : (Nat.multinomial univ c : ℝ) * ∏ a, ((c a).factorial : ℝ) = (N.factorial : ℝ) := by
    have := Nat.multinomial_spec univ c
    rw [hc] at this
    rw [mul_comm]
    exact_mod_cast this
  have hlow : (∏ a, √(c a : ℝ)) * (P / Real.exp 1 ^ N) ≤ ∏ a, ((c a).factorial : ℝ) := by
    have heq : (∏ a, √(c a : ℝ)) * (P / Real.exp 1 ^ N) =
        ∏ a, (√(c a : ℝ) * ((c a : ℝ) / Real.exp 1) ^ c a) := by
      rw [Finset.prod_mul_distrib, hPdef, ← hc, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_div_distrib]
      simp [div_pow]
    rw [heq]
    refine Finset.prod_le_prod₀ (fun a _ => by positivity) (fun a _ => ?_)
    refine le_trans ?_ (Stirling.le_factorial_stirling (c a))
    gcongr
    have := Real.two_le_pi
    have : (0 : ℝ) ≤ c a := Nat.cast_nonneg _
    nlinarith
  have hup := factorial_le_exp_mul_sqrt_stirling N hN
  have hQ : 0 < P / Real.exp 1 ^ N := by positivity
  rw [← mul_le_mul_iff_of_pos_right hQ]
  calc (Nat.multinomial univ c : ℝ) * (∏ a, √(c a : ℝ)) * (P / Real.exp 1 ^ N)
      = (Nat.multinomial univ c : ℝ) * ((∏ a, √(c a : ℝ)) * (P / Real.exp 1 ^ N)) := by ring
    _ ≤ (Nat.multinomial univ c : ℝ) * ∏ a, ((c a).factorial : ℝ) := by gcongr
    _ = (N.factorial : ℝ) := hspec
    _ ≤ Real.exp 1 * √(N : ℝ) * ((N : ℝ) / Real.exp 1) ^ N := hup
    _ = _ := by
      rw [div_pow, ← hE, ← hPdef]
      field_simp

/-- **The log of the multinomial coefficient for frequencies bounded below by `δ`.**  When every
count is at least `δN`, the square roots `√(c_a) ≥ √(δN)` save `(k/2) log N` bits:
`|N!/∏ c_a!| ≤ N h(c/N) + (1/2 - k/2) log N + O_{k,δ}(1)`. -/
private theorem size_multinomial_le_of_freq_ge {α : Type*} [Fintype α] (N : ℕ) (c : α → ℕ)
    (hc : ∑ a, c a = N) (δ : ℝ) (hδ : 0 < δ) (hcδ : ∀ a, δ ≤ (c a : ℝ) / N) :
    (Nat.size (Nat.multinomial univ c) : ℝ) ≤
      (N : ℝ) * entropyDist (fun a => (c a : ℝ) / N)
        + (1 / 2 - (Fintype.card α : ℝ) / 2) * Real.logb 2 N
        + (Real.logb 2 (Real.exp 1) + 1 - (Fintype.card α : ℝ) / 2 * Real.logb 2 δ) := by
  classical
  have he0 : 0 ≤ Real.logb 2 (Real.exp 1) :=
    Real.logb_nonneg (by norm_num) (Real.one_le_exp (by norm_num))
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hc0 : ∀ a, c a = 0 := fun a => Finset.sum_eq_zero_iff.mp hc a (mem_univ a)
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
    · simp
      linarith
    · have := hcδ a
      simp at this
      linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcN : ∀ a, δ * N ≤ c a := fun a => (le_div_iff₀ hNr).mp (hcδ a)
  have hB := multinomial_mul_prod_sqrt_le N hNpos c hc
  have hprod : √(δ * N) ^ Fintype.card α ≤ ∏ a, √(c a : ℝ) := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun a _ => Real.sqrt_le_sqrt (hcN a))
  set M : ℝ := (Nat.multinomial univ c : ℝ) with hMdef
  set H := entropyDist (fun a => (c a : ℝ) / N) with hH
  have hMpos : 0 < M := by rw [hMdef]; exact_mod_cast Nat.multinomial_pos univ c
  have hkey : M * √(δ * N) ^ Fintype.card α ≤
      Real.exp 1 * √(N : ℝ) * (2 : ℝ) ^ ((N : ℝ) * H) :=
    le_trans (mul_le_mul_of_nonneg_left hprod hMpos.le) hB
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hkey
  have hsq : ∀ x : ℝ, 0 ≤ x → Real.logb 2 √x = Real.logb 2 x / 2 := by
    intro x hx
    have := Real.logb_pow 2 (√x) 2
    rw [Real.sq_sqrt hx] at this
    push_cast at this
    linarith
  rw [Real.logb_mul hMpos.ne' (by positivity), Real.logb_pow, hsq _ (by positivity),
    Real.logb_mul hδ.ne' hNr.ne', Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), hsq _ hNr.le,
    Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  have hsize := nat_size_real_le (Nat.multinomial univ c)
  rw [← hMdef] at hsize
  nlinarith

/-- **The coding step of Theorem 146, before any estimate of the multinomial coefficient.**  A
word over `A` is described by the common bit width `|N|` of its letter counts (`2·||N|| + O(1)`
bits), the `k` counts (`k·|N|` bits) and its rank in its type class (`|N!/∏ n_a!|` bits). -/
private theorem plainK_word_le_size_multinomial (A : Type*) [Fintype A] [DecidableEq A]
    [Encodable A] (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ) (w : Fin N → A),
      ((plainK D (finWordBits A w)).toNat : ℝ) ≤
        2 * (Nat.size (Nat.size N) : ℝ) + (Fintype.card A : ℝ) * Nat.size N
          + Nat.size (Nat.multinomial univ (freq w)) + c := by
  set k := Fintype.card A with hkdef
  let idx : A → Fin k := fun a => ⟨alphabetIndex A a, alphabetIndex_lt_card a⟩
  have hbij : Function.Bijective idx := (Fintype.bijective_iff_injective_and_card idx).2
    ⟨fun a b h => alphabetIndex_injective (congrArg Fin.val h), by rw [Fintype.card_fin, hkdef]⟩
  let e := Equiv.ofBijective idx hbij
  let letterTable : List BitString := (List.range k).map (natBitsFixed (alphabetWidth A))
  let g : BitString → BitString := fun x =>
    ((Encodable.decode (bitsToNat x) : Option (List ℕ)).getD []).flatMap
      (fun n => letterTable.getD n [])
  have hg : Computable g := (Primrec.list_flatMap
    (Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec) (Primrec.const []))
    ((Primrec.list_getD []).comp (Primrec.const letterTable) Primrec.snd).to₂).to_comp
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD g hg
  obtain ⟨c2, hc2⟩ := plainK_finiteWordCode_le k D hD
  refine ⟨c2 + c1 + 1, fun N w => ?_⟩
  set v : List (Fin k) := List.ofFn fun i => idx (w i) with hv
  have hgv : g (finiteWordCode v) = finWordBits A w := by
    have hmap : v.map FiniteLetterCode.encode = List.ofFn fun i => alphabetIndex A (w i) := by
      simp [hv, List.map_ofFn]; rfl
    simp only [g, finiteWordCode, bitsToNat_bits, hmap, Encodable.encodek, Option.getD_some]
    simp only [finWordBits, wordBits, Code.encodeWord, List.flatMap, List.map_ofFn]
    congr 2
    funext i
    have hi : alphabetIndex A (w i) < k := alphabetIndex_lt_card (w i)
    simp [letterTable, alphabetCode, List.getElem?_range hi]
  set W := Nat.size N with hWdef
  have hvlen : v.length = N := by rw [hv, List.length_ofFn]
  have hWcond : ∀ i : Fin k, v.count i < 2 ^ W := by
    intro i
    have hcv : v.count i ≤ N := by rw [← hvlen]; exact List.count_le_length
    rw [hWdef]; exact lt_of_le_of_lt hcv (Nat.lt_size_self N)
  have hcount : ∀ i : Fin k, v.count i = freq w (e.symm i) := by
    intro i
    have h1 : v.count i = freq (fun j => idx (w j)) i := by rw [hv]; exact count_ofFn_eq_freq _ i
    rw [h1]
    unfold freq
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show idx (w j) = e (w j) from rfl, ← e.eq_symm_apply]
  have hmuleq : Nat.multinomial univ (fun i : Fin k => v.count i)
      = Nat.multinomial univ (freq w) := by
    have hsum : (∑ i, v.count i) = ∑ a, freq w a := by
      rw [← Equiv.sum_comp e.symm (freq w)]
      exact Finset.sum_congr rfl (fun i _ => hcount i)
    have hprod : (∏ i, (v.count i).factorial) = ∏ a, (freq w a).factorial := by
      rw [← Equiv.prod_comp e.symm (fun a => (freq w a).factorial)]
      exact Finset.prod_congr rfl (fun i _ => by rw [hcount i])
    unfold Nat.multinomial
    rw [hsum, hprod]
  have hK : plainK D (finWordBits A w) ≤
      ((2 * Nat.size W + 1 + k * W +
        Nat.size (Nat.multinomial univ (freq w)) + c2 + c1 : ℕ) : ENat) := by
    calc plainK D (finWordBits A w)
        = plainK D (g (finiteWordCode v)) := by rw [hgv]
      _ ≤ plainK D (finiteWordCode v) + c1 := hc1 _
      _ ≤ (((2 * Nat.size W + 1 + k * W +
            Nat.size (Nat.multinomial univ (fun i : Fin k => v.count i)) : ℕ) : ENat)
            + c2) + c1 := by
          gcongr
          exact hc2 v W hWcond
      _ = ((2 * Nat.size W + 1 + k * W +
            Nat.size (Nat.multinomial univ (freq w)) + c2 + c1 : ℕ) : ENat) := by
          rw [hmuleq]; push_cast; ring
  have hK' : ((plainK D (finWordBits A w)).toNat : ℝ) ≤
      ((2 * Nat.size W + 1 + k * W +
        Nat.size (Nat.multinomial univ (freq w)) + c2 + c1 : ℕ) : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hK
  push_cast at hK' ⊢
  linarith

/-- **For frequencies bounded away from zero the coefficient improves to `k/2 + O(1)`.**  Here
`O(1)` is a constant `C₀` that does not depend on the alphabet — otherwise the claim would say
nothing beyond Theorem 146 — so it is quantified before the alphabet; the additive constant `c`
may depend on the alphabet and on `δ`.  The book's hypothesis that the frequencies are "not very
close to 0" is read as a fixed positive lower bound `δ` on all of them.  The complexity is the
plain complexity of the block encoding `finWordBits` of the word.
SUV Problem 235, p. 227. -/
theorem exists_plainK_word_le_entropy_freq_half_card_logb (D : Map)
    (hD : isOptimalConditional D) :
    ∃ C₀ : ℕ, ∀ (A : Type) [Fintype A] [DecidableEq A] [Encodable A] (δ : ℝ), 0 < δ →
      ∃ c : ℕ, ∀ (N : ℕ) (w : Fin N → A), (∀ a, δ ≤ (freq w a : ℝ) / N) →
        ((plainK D (finWordBits A w)).toNat : ℝ) ≤
          (N : ℝ) * (entropyDist fun a => (freq w a : ℝ) / N)
            + ((Fintype.card A : ℝ) / 2 + C₀) * Real.logb 2 N + c := by
  refine ⟨1, fun A _ _ _ δ hδ => ?_⟩
  obtain ⟨c1, hc1⟩ := plainK_word_le_size_multinomial A D hD
  obtain ⟨cL, hcL⟩ := two_size_size_le (1 / 2) (by norm_num)
  set k := Fintype.card A with hkdef
  refine ⟨c1 + cL + k + ⌈Real.logb 2 (Real.exp 1) + 1 - (k : ℝ) / 2 * Real.logb 2 δ⌉₊,
    fun N w hw => ?_⟩
  have h1 := hc1 N w
  have h2 := hcL N
  have h3 := size_multinomial_le_of_freq_ge N (freq w) (sum_freq w) δ hδ hw
  have h4 := nat_size_real_le N
  have h5 := Nat.le_ceil (Real.logb 2 (Real.exp 1) + 1 - (k : ℝ) / 2 * Real.logb 2 δ)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h6 : (k : ℝ) * Nat.size N ≤ k * Real.logb 2 N + k := by nlinarith
  push_cast
  nlinarith

end Kolmogorov
