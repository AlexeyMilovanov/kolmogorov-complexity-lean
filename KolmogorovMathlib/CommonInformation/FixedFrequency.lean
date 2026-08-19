import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Choose.Basic
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2

/-!
# Fixed-frequency strings and their incompressibility

Chapter 11 of SUV repeatedly uses *fixed-frequency* families of binary strings:
the strings of length `n` containing exactly `k` ones.  This module supplies the
exact finite combinatorics of those families together with *both* halves of the
fixed-frequency complexity bridge (the finite core of SUV Theorem 146 used by
Exercise 316):

* `fixedWeightList n k` explicitly enumerates the strings of length `n` with
  exactly `k` ones; it is duplicate free, its membership predicate is exact, and
  its length is `n.choose k`;
* `fixedWeightStrings n k` is the corresponding `Finset`, with
  `card_fixedWeightStrings`;
* **counting (lower) half.** `exists_fixedWeight_condK_gt` and
  `exists_fixedWeight_plainK_gt` produce a fixed-frequency string of high
  (conditional) plain complexity whenever the binomial coefficient is large
  enough;
* **enumeration (upper) half.** `condK_fixedWeight_le_size_choose` shows that,
  *given the frequency parameters `n` and `k`*, every length-`n` weight-`k`
  string is describable by its index among the `n.choose k` such strings, hence
  has conditional complexity at most `Nat.size (n.choose k) + O(1)`
  (`= log₂(n.choose k) + O(1)`); the plain decoder
  `plainK_fixedWeight_le_size_choose_add_params` includes self-delimiting binary
  encodings of `n` and `k`, and
  `plainK_fixedWeight_le_size_choose_add_length` folds their cost to `O(log n)`.

Together these pin the conditional complexity of a *maximally complex*
fixed-frequency string to `Nat.size (n.choose k) ± O(1)` and provide the
corresponding plain upper bound with logarithmic parameter overhead.  The
general finite-alphabet (multinomial) generalization needed to run Exercise 316
in full remains part of the Theorem-146 bridge.
-/

namespace Kolmogorov

/-! ### Enumeration of fixed-frequency strings -/

/-- `fixedWeightList n k` lists every bit string of length `n` containing
exactly `k` occurrences of `true`. -/
def fixedWeightList : ℕ → ℕ → List BitString
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 => (fixedWeightList n 0).map (false :: ·)
  | n + 1, k + 1 =>
      (fixedWeightList n (k + 1)).map (false :: ·) ++
        (fixedWeightList n k).map (true :: ·)

/-- `fixedWeightList n k` has exactly `n.choose k` entries. -/
@[simp]
lemma length_fixedWeightList (n k : ℕ) :
    (fixedWeightList n k).length = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp [fixedWeightList]
  | succ n ih =>
    cases k with
    | zero => simp [fixedWeightList, ih]
    | succ k =>
      simp [fixedWeightList, ih, Nat.choose_succ_succ, Nat.add_comm]

/-- Membership in `fixedWeightList n k` is exactly "length `n`, weight `k`". -/
@[simp]
lemma mem_fixedWeightList (n k : ℕ) (s : BitString) :
    s ∈ fixedWeightList n k ↔ s.length = n ∧ s.count true = k := by
  induction n generalizing k s with
  | zero =>
    cases k with
    | zero =>
      cases s with
      | nil => simp [fixedWeightList]
      | cons b bs => simp [fixedWeightList]
    | succ k =>
      cases s with
      | nil => simp [fixedWeightList]
      | cons b bs => simp [fixedWeightList]
  | succ n ih =>
    cases k with
    | zero =>
      cases s with
      | nil => simp [fixedWeightList]
      | cons b bs =>
        cases b with
        | false => simp [fixedWeightList, ih]
        | true => simp [fixedWeightList]
    | succ k =>
      cases s with
      | nil => simp [fixedWeightList]
      | cons b bs =>
        cases b with
        | false => simp [fixedWeightList, ih]
        | true =>
          simp [fixedWeightList, ih]

/-- `fixedWeightList n k` is duplicate free. -/
lemma fixedWeightList_nodup (n k : ℕ) : (fixedWeightList n k).Nodup := by
  induction n generalizing k with
  | zero => cases k <;> simp [fixedWeightList]
  | succ n ih =>
    cases k with
    | zero =>
      exact (ih 0).map (fun _ _ h => by injection h)
    | succ k =>
      refine List.nodup_append.mpr ⟨(ih (k + 1)).map (fun _ _ h => by injection h),
        (ih k).map (fun _ _ h => by injection h), ?_⟩
      intro x hx y hy hxy
      rw [List.mem_map] at hx hy
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, -, rfl⟩ := hy
      exact absurd hxy (by simp)

/-- The finite set of bit strings of length `n` with exactly `k` ones. -/
def fixedWeightStrings (n k : ℕ) : Finset BitString :=
  (fixedWeightList n k).toFinset

/-- Membership in `fixedWeightStrings n k` is exactly "length `n`, weight `k`". -/
@[simp]
lemma mem_fixedWeightStrings (n k : ℕ) (s : BitString) :
    s ∈ fixedWeightStrings n k ↔ s.length = n ∧ s.count true = k := by
  simp [fixedWeightStrings]

/-- There are exactly `n.choose k` bit strings of length `n` with `k` ones. -/
lemma card_fixedWeightStrings (n k : ℕ) :
    (fixedWeightStrings n k).card = n.choose k := by
  rw [fixedWeightStrings, List.toFinset_card_of_nodup (fixedWeightList_nodup n k),
    length_fixedWeightList]

/-! ### Fixed-frequency incompressibility -/

/-- Pigeonhole over an arbitrary finite family of strings: if a finite set of
strings has at least `2 ^ (m + 1)` elements, one of its members has conditional
complexity strictly above `m`. -/
theorem exists_mem_condK_gt_of_card_le
    (D : Map) (y : BitString) (m : ℕ) (S : Finset BitString)
    (hcard : 2 ^ (m + 1) ≤ S.card) :
    ∃ s ∈ S, (m : ENat) < condK D s y := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ compressibleWords D y m := by
    intro s hs
    exact (mem_compressibleWords_iff D y s m).mpr (hcon s hs)
  have hle := Finset.card_le_card hsub
  have hlt := cardCompressibleWordsLt D y m
  omega

/-- Fixed-frequency incompressibility (conditional form): whenever the binomial
coefficient `n.choose k` is at least `2 ^ (m + 1)`, there is a string of length
`n` with exactly `k` ones whose complexity conditional on `y` exceeds `m`. -/
theorem exists_fixedWeight_condK_gt
    (D : Map) (y : BitString) (n k m : ℕ) (hcard : 2 ^ (m + 1) ≤ n.choose k) :
    ∃ s : BitString, s.length = n ∧ s.count true = k ∧ (m : ENat) < condK D s y := by
  obtain ⟨s, hs, hK⟩ :=
    exists_mem_condK_gt_of_card_le D y m (fixedWeightStrings n k)
      (by rw [card_fixedWeightStrings]; exact hcard)
  rw [mem_fixedWeightStrings] at hs
  exact ⟨s, hs.1, hs.2, hK⟩

/-- Fixed-frequency incompressibility (unconditional form). -/
theorem exists_fixedWeight_plainK_gt
    (D : Map) (n k m : ℕ) (hcard : 2 ^ (m + 1) ≤ n.choose k) :
    ∃ s : BitString, s.length = n ∧ s.count true = k ∧ (m : ENat) < plainK D s :=
  exists_fixedWeight_condK_gt D [] n k m hcard

/-! ### Fixed-frequency incompressibility: the enumeration (upper) half

This is the effective side of the fixed-frequency bridge.  A length-`n`
weight-`k` string carries no more than `log₂(n.choose k)` bits of information
*once the frequency parameters `n, k` are known*: it is determined by its
position in the (computable, duplicate-free) list of all such strings, encoded
as a fixed-width index.  This complements `exists_fixedWeight_condK_gt`, which
shows the maximal such complexity is actually attained. -/

open Kolmogorov.CodedFiniteDistribution in
/-- The length-`n` weight-`k` strings, obtained by filtering `allStrings n`.
Unlike `fixedWeightList`, this presentation is manifestly a filter of the
computable enumeration `allStrings`, which makes the decoder below computable. -/
def fixedWeightFiltered (n k : ℕ) : List BitString :=
  (allStrings n).filter (fun s => s.count true == k)

theorem mem_fixedWeightFiltered (n k : ℕ) (s : BitString) :
    s ∈ fixedWeightFiltered n k ↔ s.length = n ∧ s.count true = k := by
  unfold fixedWeightFiltered
  rw [List.mem_filter, mem_allStrings]
  simp [beq_iff_eq]

theorem fixedWeightFiltered_nodup (n k : ℕ) : (fixedWeightFiltered n k).Nodup :=
  (allStrings_nodup n).filter _

/-- The filtered enumeration has exactly `n.choose k` entries. -/
theorem length_fixedWeightFiltered (n k : ℕ) :
    (fixedWeightFiltered n k).length = n.choose k := by
  have hnodup := fixedWeightFiltered_nodup n k
  have htoFinset : (fixedWeightFiltered n k).toFinset = fixedWeightStrings n k := by
    ext s
    rw [List.mem_toFinset, mem_fixedWeightFiltered, mem_fixedWeightStrings]
  rw [← List.toFinset_card_of_nodup hnodup, htoFinset, card_fixedWeightStrings]

open Kolmogorov.CodedFiniteDistribution in
/-- The decoder for the enumeration bound: from a context
`pairCode (natCode n) (natCode k)` and a program encoding a fixed-width index
`i`, return the `i`-th length-`n` weight-`k` string. -/
def fixedWeightDecoder : Map := fun pr =>
  Part.some
    ((fixedWeightFiltered (decodeNatCode (decodeFirst pr.2))
        (decodeNatCode (decodeSecond pr.2))).getD (decodeFixedWidthNatCode pr.1) [])

open Kolmogorov.CodedFiniteDistribution in
theorem fixedWeightDecoder_isDecompressor : isDecompressor fixedWeightDecoder := by
  have hn : Primrec (fun pr : BitString × BitString =>
      decodeNatCode (decodeFirst pr.2)) :=
    decodeNatCode_primrec.comp (decodeFirst_primrec.comp Primrec.snd)
  have hk : Primrec (fun pr : BitString × BitString =>
      decodeNatCode (decodeSecond pr.2)) :=
    decodeNatCode_primrec.comp (decodeSecond_primrec.comp Primrec.snd)
  have hlist : Primrec (fun pr : BitString × BitString =>
      allStrings (decodeNatCode (decodeFirst pr.2))) :=
    allStrings_primrec.comp hn
  have hpred : Primrec₂ (fun (pr : BitString × BitString) (s : BitString) =>
      s.count true == decodeNatCode (decodeSecond pr.2)) := by
    have hcount : Primrec (fun q : (BitString × BitString) × BitString =>
        q.2.count true) := by
      have := list_countP_primrec (β := Bool)
        (f := fun q : (BitString × BitString) × BitString => q.2)
        (p := fun _ b => b == true) Primrec.snd
        (Primrec.beq.comp Primrec.snd (Primrec.const true))
      simpa [List.count] using this
    exact (Primrec.beq.comp hcount (hk.comp Primrec.fst))
  have hfilter : Primrec (fun pr : BitString × BitString =>
      (allStrings (decodeNatCode (decodeFirst pr.2))).filter
        (fun s => s.count true == decodeNatCode (decodeSecond pr.2))) :=
    list_filter_primrec hlist hpred
  have hdecodeIdx : Primrec decodeFixedWidthNatCode := by
    unfold decodeFixedWidthNatCode
    exact bitsToNat_primrec.comp Primrec.list_reverse
  have hidx : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode pr.1) :=
    hdecodeIdx.comp Primrec.fst
  have hg : Computable (fun pr : BitString × BitString =>
      (fixedWeightFiltered (decodeNatCode (decodeFirst pr.2))
          (decodeNatCode (decodeSecond pr.2))).getD (decodeFixedWidthNatCode pr.1) []) :=
    ((Primrec.list_getD ([] : BitString)).comp hfilter hidx).to_comp
  exact hg.partrec

open Kolmogorov.CodedFiniteDistribution in
/-- **Fixed-frequency complexity upper bound (conditional form).**
Given the frequency parameters `n` and `k` as context, every length-`n`
string with exactly `k` ones is describable by its index among the
`n.choose k` such strings, so its conditional complexity is at most
`log₂(n.choose k) + O(1)` (here `Nat.size (n.choose k)`).  This is the
enumeration (upper) half of the fixed-frequency bridge, complementing the
counting lower bound `exists_fixedWeight_condK_gt`.  The constant is uniform in
`n, k` and `s`. -/
theorem condK_fixedWeight_le_size_choose
    (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n k : ℕ) (s : BitString),
      s.length = n → s.count true = k →
      condK U s (pairCode (natCode n) (natCode k)) ≤
        (Nat.size (n.choose k) : ENat) + c := by
  obtain ⟨c, hc⟩ := hU.2 fixedWeightDecoder fixedWeightDecoder_isDecompressor
  refine ⟨c, fun n k s hlen hcount => ?_⟩
  set y : BitString := pairCode (natCode n) (natCode k) with hy
  -- `s` lies in the filtered list at some index `i < n.choose k`.
  have hmem : s ∈ fixedWeightFiltered n k :=
    (mem_fixedWeightFiltered n k s).mpr ⟨hlen, hcount⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hi_choose : i < n.choose k := by
    rwa [length_fixedWeightFiltered] at hi
  set width : ℕ := Nat.size (n.choose k) with hwidth
  have hchoose_lt : n.choose k < 2 ^ width := Nat.lt_size_self (n.choose k)
  have hi_lt : i < 2 ^ width := lt_trans hi_choose hchoose_lt
  set p : BitString := fixedWidthNatCode i width with hp
  have hplen : p.length = width := fixedWidthNatCode_length hi_lt
  -- The decoder produces `s` from program `p` and context `y`.
  have hprod : produces fixedWeightDecoder p y s := by
    change s ∈ fixedWeightDecoder (p, y)
    unfold fixedWeightDecoder
    rw [Part.mem_some_iff]
    have hdf : decodeFirst y = natCode n := by rw [hy, decodeFirst_pairCode]
    have hds : decodeSecond y = natCode k := by rw [hy, decodeSecond_pairCode]
    simp only [hdf, hds, decodeNatCode_natCode]
    rw [hp, decodeFixedWidthNatCode_encode]
    rw [List.getD_eq_getElem _ _ hi, hget]
  -- Package the complexity bound through optimality.
  have hDbound : condK fixedWeightDecoder s y ≤ (width : ENat) := by
    have hcand : (p.length : ENat) ∈ candidateLengths fixedWeightDecoder s y :=
      ⟨p, hprod, rfl⟩
    calc condK fixedWeightDecoder s y ≤ (p.length : ENat) := sInf_le hcand
      _ = (width : ENat) := by rw [hplen]
  calc condK U s y ≤ condK fixedWeightDecoder s y + (c : ENat) := hc s y
    _ ≤ (width : ENat) + (c : ENat) := by gcongr
    _ = (Nat.size (n.choose k) : ENat) + (c : ENat) := by rw [hwidth]

open Kolmogorov.CodedFiniteDistribution in
/-- A plain decoder for fixed-frequency strings.  Its program contains binary,
self-delimiting encodings of `n` and `k`, followed by a fixed-width rank in the
length-`n`, weight-`k` family. -/
def fixedWeightPlainDecoder : Map := fun pr =>
  Part.some
    ((fixedWeightFiltered (bitsToNat (decodeFirst pr.1))
        (bitsToNat (decodeFirst (decodeSecond pr.1)))).getD
      (decodeFixedWidthNatCode (decodeSecond (decodeSecond pr.1))) [])

open Kolmogorov.CodedFiniteDistribution in
theorem fixedWeightPlainDecoder_isDecompressor : isDecompressor fixedWeightPlainDecoder := by
  have hn : Primrec (fun pr : BitString × BitString =>
      bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst)
  have hk : Primrec (fun pr : BitString × BitString =>
      bitsToNat (decodeFirst (decodeSecond pr.1))) :=
    bitsToNat_primrec.comp
      (decodeFirst_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
  have hlist : Primrec (fun pr : BitString × BitString =>
      allStrings (bitsToNat (decodeFirst pr.1))) :=
    allStrings_primrec.comp hn
  have hpred : Primrec₂ (fun (pr : BitString × BitString) (s : BitString) =>
      s.count true == bitsToNat (decodeFirst (decodeSecond pr.1))) := by
    have hcount : Primrec (fun q : (BitString × BitString) × BitString =>
        q.2.count true) := by
      have := list_countP_primrec (β := Bool)
        (f := fun q : (BitString × BitString) × BitString => q.2)
        (p := fun _ b => b == true) Primrec.snd
        (Primrec.beq.comp Primrec.snd (Primrec.const true))
      simpa [List.count] using this
    exact Primrec.beq.comp hcount (hk.comp Primrec.fst)
  have hfilter : Primrec (fun pr : BitString × BitString =>
      (allStrings (bitsToNat (decodeFirst pr.1))).filter
        (fun s => s.count true == bitsToNat (decodeFirst (decodeSecond pr.1)))) :=
    list_filter_primrec hlist hpred
  have hdecodeIdx : Primrec decodeFixedWidthNatCode := by
    unfold decodeFixedWidthNatCode
    exact bitsToNat_primrec.comp Primrec.list_reverse
  have hidx : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode (decodeSecond (decodeSecond pr.1))) :=
    hdecodeIdx.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
  have hg : Computable (fun pr : BitString × BitString =>
      (fixedWeightFiltered (bitsToNat (decodeFirst pr.1))
          (bitsToNat (decodeFirst (decodeSecond pr.1)))).getD
        (decodeFixedWidthNatCode (decodeSecond (decodeSecond pr.1))) []) :=
    ((Primrec.list_getD ([] : BitString)).comp hfilter hidx).to_comp
  exact hg.partrec

open Kolmogorov.CodedFiniteDistribution in
/-- **Fixed-frequency complexity upper bound (plain form).** Every length-`n`,
weight-`k` string is described by its rank in the family plus self-delimiting
binary encodings of the two frequency parameters.  Thus the parameter charge
is logarithmic rather than the unary length of `natCode n` and `natCode k`. -/
theorem plainK_fixedWeight_le_size_choose_add_params
    (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n k : ℕ) (s : BitString),
      s.length = n → s.count true = k →
      plainK U s ≤
        ((Nat.size (n.choose k) + 2 * Nat.size n + 2 * Nat.size k + c : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := hU.2 fixedWeightPlainDecoder fixedWeightPlainDecoder_isDecompressor
  refine ⟨c + 2, fun n k s hlen hcount => ?_⟩
  have hmem : s ∈ fixedWeightFiltered n k :=
    (mem_fixedWeightFiltered n k s).mpr ⟨hlen, hcount⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hi_choose : i < n.choose k := by
    rwa [length_fixedWeightFiltered] at hi
  set width : ℕ := Nat.size (n.choose k) with hwidth
  have hi_lt : i < 2 ^ width :=
    lt_trans hi_choose (Nat.lt_size_self (n.choose k))
  set p : BitString :=
    pairCode (Nat.bits n) (pairCode (Nat.bits k) (fixedWidthNatCode i width)) with hp
  have hplen :
      p.length = Nat.size (n.choose k) + 2 * Nat.size n + 2 * Nat.size k + 2 := by
    rw [hp, length_pairCode, length_pairCode, fixedWidthNatCode_length hi_lt,
      Nat.size_eq_bits_len, Nat.size_eq_bits_len, hwidth]
    omega
  have hprod : produces fixedWeightPlainDecoder p [] s := by
    change s ∈ fixedWeightPlainDecoder (p, [])
    unfold fixedWeightPlainDecoder
    rw [Part.mem_some_iff]
    simp only [hp, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits,
      decodeFixedWidthNatCode_encode]
    rw [List.getD_eq_getElem _ _ hi, hget]
  have hDbound : plainK fixedWeightPlainDecoder s ≤ (p.length : ENat) := by
    have hcand : (p.length : ENat) ∈ candidateLengths fixedWeightPlainDecoder s [] :=
      ⟨p, hprod, rfl⟩
    exact sInf_le hcand
  calc
    plainK U s ≤ plainK fixedWeightPlainDecoder s + (c : ENat) := hc s []
    _ ≤ (p.length : ENat) + (c : ENat) := by gcongr
    _ = ((Nat.size (n.choose k) + 2 * Nat.size n + 2 * Nat.size k + (c + 2) : ℕ) :
        ENat) := by
      rw [show (p.length : ENat) =
        ((Nat.size (n.choose k) + 2 * Nat.size n + 2 * Nat.size k + 2 : ℕ) : ENat) by
          exact_mod_cast hplen]
      norm_cast
      omega

/-- The same plain upper bound with all parameter overhead folded into
`O(log n)`: the frequency hypothesis forces `k ≤ n`, hence
`Nat.size k ≤ Nat.size n`. -/
theorem plainK_fixedWeight_le_size_choose_add_length
    (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n k : ℕ) (s : BitString),
      s.length = n → s.count true = k →
      plainK U s ≤ ((Nat.size (n.choose k) + 4 * Nat.size n + c : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := plainK_fixedWeight_le_size_choose_add_params U hU
  refine ⟨c, fun n k s hlen hcount => ?_⟩
  have hkn : k ≤ n := by
    rw [← hcount, ← hlen]
    exact List.count_le_length
  have hsize : Nat.size k ≤ Nat.size n := Nat.size_le_size hkn
  calc
    plainK U s ≤
        ((Nat.size (n.choose k) + 2 * Nat.size n + 2 * Nat.size k + c : ℕ) : ENat) :=
      hc n k s hlen hcount
    _ ≤ ((Nat.size (n.choose k) + 4 * Nat.size n + c : ℕ) : ENat) := by
      exact_mod_cast (by omega :
        Nat.size (n.choose k) + 2 * Nat.size n + 2 * Nat.size k + c ≤
          Nat.size (n.choose k) + 4 * Nat.size n + c)

end Kolmogorov
