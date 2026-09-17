import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.InfiniteSequences.MonotoneComparison

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution
variable (Q : ℕ × ℕ × BitString → Bool)

/-! ### Machinery for Exercise 53(c) and 53(d): split and substring decompressors -/
/-! ### Helper arithmetic -/

/-! ### The two split decompressors of Exercise 53(c) -/

private lemma four_mul_le_two_pow : ∀ m : ℕ, 4 ≤ m → 4 * m ≤ 2 ^ m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k
      · omega
      · omega
      · omega
      · norm_num
    · have h1 := ih hk
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

/-- If `d` is at most twice its bit length plus `K`, then `d` is bounded by `2K+8`. -/
private lemma le_of_le_two_mul_bits_len (K d : ℕ)
    (hd : d ≤ 2 * (Nat.bits d).length + K) : d ≤ 2 * K + 8 := by
  rw [Nat.size_eq_bits_len] at hd
  set s := Nat.size d with hs
  rcases Nat.lt_or_ge s 5 with hlt | hge
  · omega
  · have h1 : 2 ^ (s - 1) ≤ d := by
      by_contra h
      replace h := Nat.lt_of_not_le h
      have : Nat.size d ≤ s - 1 := Nat.size_le.mpr h
      omega
    have h2 : 4 * (s - 1) ≤ 2 ^ (s - 1) := four_mul_le_two_pow (s - 1) (by omega)
    omega

/-- The deficiency parameter read off the self-delimiting first component. -/
private def splitDefect (w : BitString) : ℕ := bitsToNat (decodeFirst w)

/-- The payload of a split program. -/
private def splitBody (w : BitString) : BitString := decodeSecond w

/-- The length of the embedded `U`-program: from `|body| = k + n` and `d = n - k`
one recovers `k = (|body| + d) / 2 - d`. -/
private def splitProgLen (w : BitString) : ℕ :=
  ((splitBody w).length + splitDefect w) / 2 - splitDefect w

private lemma splitDefect_primrec : Primrec splitDefect :=
  bitsToNat_primrec.comp decodeFirst_primrec

private lemma splitBody_primrec : Primrec splitBody := decodeSecond_primrec

private lemma splitProgLen_primrec : Primrec splitProgLen := by
  have h : Primrec (fun w : BitString => ((splitBody w).length + splitDefect w) / 2) :=
    Primrec.nat_div.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp splitBody_primrec) splitDefect_primrec)
      (Primrec.const 2)
  exact Primrec.nat_sub.comp h splitDefect_primrec

private lemma splitDefect_pairCode (d : ℕ) (r : BitString) :
    splitDefect (pairCode (Nat.bits d) r) = d := by
  simp [splitDefect, decodeFirst_pairCode, bitsToNat_bits]

private lemma splitBody_pairCode (d : ℕ) (r : BitString) :
    splitBody (pairCode (Nat.bits d) r) = r := by
  simp [splitBody, decodeSecond_pairCode]

/-- Decompressor recovering `x = u ++ v` from a program for the *second* half `v`
together with the first half `u` given in the clear. -/
noncomputable def suffixSplitDecoder (U : Map) : Map := fun pr =>
  (U ((splitBody pr.1).take (splitProgLen pr.1), [])).map
    (fun v => (splitBody pr.1).drop (splitProgLen pr.1) ++ v)

/-- Decompressor recovering `x = u ++ v` from a program for the *first* half `u`
together with the second half `v` given in the clear. -/
noncomputable def prefixSplitDecoder (U : Map) : Map := fun pr =>
  (U ((splitBody pr.1).take (splitProgLen pr.1), [])).map
    (fun u => u ++ (splitBody pr.1).drop (splitProgLen pr.1))

private lemma splitDecoder_arg_computable :
    Computable (fun pr : BitString × BitString =>
      ((splitBody pr.1).take (splitProgLen pr.1), ([] : BitString))) := by
  refine Computable.pair ?_ (Computable.const _)
  exact (Primrec.list_take.comp (splitProgLen_primrec.comp Primrec.fst)
      (splitBody_primrec.comp Primrec.fst)).to_comp

/-- The decompressor that recovers a string from a program for its prefix and the literal suffix
is a decompressor whenever `U` is. -/
lemma suffixSplitDecoder_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (suffixSplitDecoder U) := by
  have hg : Computable₂ (fun (pr : BitString × BitString) (v : BitString) =>
      (splitBody pr.1).drop (splitProgLen pr.1) ++ v) := by
    have h1 : Primrec (fun q : (BitString × BitString) × BitString =>
        (splitBody q.1.1).drop (splitProgLen q.1.1)) :=
      Primrec.list_drop.comp (splitProgLen_primrec.comp (Primrec.fst.comp Primrec.fst))
        (splitBody_primrec.comp (Primrec.fst.comp Primrec.fst))
    exact (Primrec.list_append.comp h1 Primrec.snd).to_comp
  exact Partrec.map (hU.comp splitDecoder_arg_computable) hg

/-- The decompressor that recovers a string from the literal prefix and a program for its suffix
is a decompressor whenever `U` is. -/
lemma prefixSplitDecoder_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (prefixSplitDecoder U) := by
  have hg : Computable₂ (fun (pr : BitString × BitString) (u : BitString) =>
      u ++ (splitBody pr.1).drop (splitProgLen pr.1)) := by
    have h1 : Primrec (fun q : (BitString × BitString) × BitString =>
        (splitBody q.1.1).drop (splitProgLen q.1.1)) :=
      Primrec.list_drop.comp (splitProgLen_primrec.comp (Primrec.fst.comp Primrec.fst))
        (splitBody_primrec.comp (Primrec.fst.comp Primrec.fst))
    exact (Primrec.list_append.comp Primrec.snd h1).to_comp
  exact Partrec.map (hU.comp splitDecoder_arg_computable) hg

private lemma suffixSplit_produces (U : Map) (n : ℕ) (p u v : BitString)
    (hu : u.length = n) (hk : p.length ≤ n) (hv : v ∈ U (p, [])) :
    produces (suffixSplitDecoder U) (pairCode (Nat.bits (n - p.length)) (p ++ u)) []
      (u ++ v) := by
  have hd := splitDefect_pairCode (n - p.length) (p ++ u)
  have hb := splitBody_pairCode (n - p.length) (p ++ u)
  have hlen : splitProgLen (pairCode (Nat.bits (n - p.length)) (p ++ u)) = p.length := by
    unfold splitProgLen
    rw [hd, hb, List.length_append, hu]
    omega
  change _ ∈ suffixSplitDecoder U _
  unfold suffixSplitDecoder
  simp only [hb, hlen]
  rw [List.take_left' rfl, List.drop_left' rfl]
  exact Part.mem_map _ hv

private lemma prefixSplit_produces (U : Map) (n : ℕ) (p u v : BitString)
    (hv : v.length = n) (hk : p.length ≤ n) (hu : u ∈ U (p, [])) :
    produces (prefixSplitDecoder U) (pairCode (Nat.bits (n - p.length)) (p ++ v)) []
      (u ++ v) := by
  have hd := splitDefect_pairCode (n - p.length) (p ++ v)
  have hb := splitBody_pairCode (n - p.length) (p ++ v)
  have hlen : splitProgLen (pairCode (Nat.bits (n - p.length)) (p ++ v)) = p.length := by
    unfold splitProgLen
    rw [hd, hb, List.length_append, hv]
    omega
  change _ ∈ prefixSplitDecoder U _
  unfold prefixSplitDecoder
  simp only [hb, hlen]
  rw [List.take_left' rfl, List.drop_left' rfl]
  exact Part.mem_map _ hu

private lemma split_length_bound (U D : Map) (C n : ℕ) (x p w : BitString)
    (hCD : ∀ y z : BitString, condK U y z ≤ condK D y z + (C : ℕ∞)) (hw : w.length = n)
    (hprod : produces D (pairCode (Nat.bits (n - p.length)) (p ++ w)) [] x)
    (hxK : ((2 * n : ℕ) : ℕ∞) ≤ plainK U x) (hpn : p.length ≤ n) :
    n ≤ p.length + (2 * C + 10) := by
  set d := n - p.length with hd_def
  set L := (Nat.bits d).length with hL_def
  have hq_len : (pairCode (Nat.bits d) (p ++ w)).length = L + 1 + L + (p.length + n) := by
    rw [length_pairCode, List.length_append, hw, ← hL_def]
  have h2 : condK D x [] ≤ ((L + 1 + L + (p.length + n) : ℕ) : ℕ∞) := by
    refine sInf_le ⟨pairCode (Nat.bits d) (p ++ w), hprod, ?_⟩
    rw [show programLength (pairCode (Nat.bits d) (p ++ w)) =
      (pairCode (Nat.bits d) (p ++ w)).length from rfl, hq_len]
  have h3 : ((2 * n : ℕ) : ℕ∞) ≤ ((L + 1 + L + (p.length + n) + C : ℕ) : ℕ∞) := by
    refine hxK.trans ((hCD x []).trans ?_)
    calc condK D x [] + (C : ℕ∞) ≤ ((L + 1 + L + (p.length + n) : ℕ) : ℕ∞) + (C : ℕ∞) := by
          gcongr
      _ = ((L + 1 + L + (p.length + n) + C : ℕ) : ℕ∞) := by push_cast; ring
  have h4 : 2 * n ≤ L + 1 + L + (p.length + n) + C := by exact_mod_cast h3
  have h5 : d ≤ 2 * (Nat.bits d).length + (1 + C) := by rw [← hL_def]; omega
  have h6 : d ≤ 2 * (1 + C) + 8 := le_of_le_two_mul_bits_len (1 + C) d h5
  omega

/-- **Exercise 53(c).** Both halves of an incompressible string of length `2 n`
have complexity `n - O(1)`. -/
theorem plainK_halves_of_incompressible (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : BitString), x.length = 2 * n → ((2 * n : ℕ) : ℕ∞) ≤ plainK U x →
      (n : ℕ∞) ≤ plainK U (x.take n) + (c : ℕ∞) ∧
        (n : ℕ∞) ≤ plainK U (x.drop n) + (c : ℕ∞) := by
  obtain ⟨C1, hC1⟩ := hU.2 (suffixSplitDecoder U) (suffixSplitDecoder_isDecompressor U hU.1)
  obtain ⟨C2, hC2⟩ := hU.2 (prefixSplitDecoder U) (prefixSplitDecoder_isDecompressor U hU.1)
  refine ⟨2 * (max C1 C2) + 10, fun n x hx hxK => ?_⟩
  set u := x.take n with hu_def
  set v := x.drop n with hv_def
  have hu_len : u.length = n := by rw [hu_def, List.length_take, hx]; omega
  have hv_len : v.length = n := by rw [hv_def, List.length_drop, hx]; omega
  have hx_eq : u ++ v = x := List.take_append_drop n x
  have step : ∀ (D : Map) (C : ℕ) (hlf oth : BitString),
      (∀ y z : BitString, condK U y z ≤ condK D y z + (C : ℕ∞)) →
      oth.length = n →
      (∀ p : BitString, p.length ≤ n → hlf ∈ U (p, []) →
        produces D (pairCode (Nat.bits (n - p.length)) (p ++ oth)) [] x) →
      (n : ℕ∞) ≤ plainK U hlf + ((2 * C + 10 : ℕ) : ℕ∞) := by
    intro D C hlf oth hCD hoth hprod
    by_cases htop : plainK U hlf = ⊤
    · rw [htop]; simp
    · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp htop
      have hle : plainK U hlf ≤ (j : ℕ∞) := le_of_eq hj.symm
      obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U hlf [] j).mp hle
      have hpl : programLength p = p.length := rfl
      by_cases hpn : p.length ≤ n
      · have hb := split_length_bound U D C n x p oth hCD hoth
          (hprod p hpn hp_prod) hxK hpn
        have hnj : n ≤ j + (2 * C + 10) := by omega
        calc (n : ℕ∞) ≤ ((j + (2 * C + 10) : ℕ) : ℕ∞) := by exact_mod_cast hnj
          _ = (j : ℕ∞) + ((2 * C + 10 : ℕ) : ℕ∞) := by push_cast; ring
          _ = plainK U hlf + ((2 * C + 10 : ℕ) : ℕ∞) := by rw [hj]
      · have hjn : n ≤ j := by omega
        calc (n : ℕ∞) ≤ (j : ℕ∞) := by exact_mod_cast hjn
          _ = plainK U hlf := hj
          _ ≤ plainK U hlf + ((2 * C + 10 : ℕ) : ℕ∞) := le_self_add
  constructor
  · refine (step (prefixSplitDecoder U) C2 u v hC2 hv_len ?_).trans ?_
    · intro p hpn hpu
      have h := prefixSplit_produces U n p u v hv_len hpn hpu
      rwa [hx_eq] at h
    · gcongr
      exact le_max_right C1 C2
  · refine (step (suffixSplitDecoder U) C1 v u hC1 hu_len ?_).trans ?_
    · intro p hpn hpv
      have h := suffixSplit_produces U n p u v hu_len hpn hpv
      rwa [hx_eq] at h
    · gcongr
      exact le_max_left C1 C2

private def subI (w : BitString) : ℕ := bitsToNat (decodeFirst w)
private def subK (w : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond w))
private def subN (w : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond (decodeSecond w)))
private def subB (w : BitString) : BitString := decodeSecond (decodeSecond (decodeSecond w))
private def subJ (w : BitString) : ℕ := (subB w).length + subK w - subN w
private def subProg (w : BitString) : BitString := (subB w).take (subJ w)
private def subRest (w : BitString) : BitString := (subB w).drop (subJ w)
private def subPre (w : BitString) : BitString := (subRest w).take (subI w)
private def subSuf (w : BitString) : BitString := (subRest w).drop (subI w)

private lemma subI_primrec : Primrec subI := bitsToNat_primrec.comp decodeFirst_primrec
private lemma subK_primrec : Primrec subK :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
private lemma subN_primrec : Primrec subN :=
  bitsToNat_primrec.comp
    (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))
private lemma subB_primrec : Primrec subB :=
  decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec)
private lemma subJ_primrec : Primrec subJ :=
  Primrec.nat_sub.comp
    (Primrec.nat_add.comp (Primrec.list_length.comp subB_primrec) subK_primrec) subN_primrec
private lemma subProg_primrec : Primrec subProg :=
  Primrec.list_take.comp subJ_primrec subB_primrec
private lemma subRest_primrec : Primrec subRest :=
  Primrec.list_drop.comp subJ_primrec subB_primrec
private lemma subPre_primrec : Primrec subPre :=
  Primrec.list_take.comp subI_primrec subRest_primrec
private lemma subSuf_primrec : Primrec subSuf :=
  Primrec.list_drop.comp subI_primrec subRest_primrec

/-- Decompressor for Exercise 53(d): the program carries the positions `i`, `k`, the
length `n`, a `U`-program for the substring, and the two remaining pieces of the
string in the clear. -/
noncomputable def substringDecoder (U : Map) : Map := fun pr =>
  (U (subProg pr.1, [])).map (fun s => subPre pr.1 ++ (s ++ subSuf pr.1))

/-- The decompressor that recovers a string from a program for a substring together with the
surrounding literal blocks is a decompressor whenever `U` is. -/
lemma substringDecoder_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (substringDecoder U) := by
  have harg : Computable (fun pr : BitString × BitString => (subProg pr.1, ([] : BitString))) :=
    Computable.pair (subProg_primrec.comp Primrec.fst).to_comp (Computable.const _)
  have hg : Computable₂ (fun (pr : BitString × BitString) (s : BitString) =>
      subPre pr.1 ++ (s ++ subSuf pr.1)) := by
    have h1 : Primrec (fun q : (BitString × BitString) × BitString => subPre q.1.1) :=
      subPre_primrec.comp (Primrec.fst.comp Primrec.fst)
    have h2 : Primrec (fun q : (BitString × BitString) × BitString => subSuf q.1.1) :=
      subSuf_primrec.comp (Primrec.fst.comp Primrec.fst)
    exact (Primrec.list_append.comp h1 (Primrec.list_append.comp Primrec.snd h2)).to_comp
  exact Partrec.map (hU.comp harg) hg

/-- The program of `substringDecoder`. -/
private def substringProgram (i k n : ℕ) (p rest : BitString) : BitString :=
  pairCode (Nat.bits i) (pairCode (Nat.bits k) (pairCode (Nat.bits n) (p ++ rest)))

private lemma substringProgram_length (i k n : ℕ) (p rest : BitString) :
    (substringProgram i k n p rest).length =
      2 * (Nat.bits i).length + 2 * (Nat.bits k).length + 2 * (Nat.bits n).length + 3
        + (p.length + rest.length) := by
  unfold substringProgram
  rw [length_pairCode, length_pairCode, length_pairCode, List.length_append]
  ring

private lemma substring_produces (U : Map) (i k n : ℕ) (x p : BitString)
    (hx : x.length = n) (hik : i + k ≤ n)
    (hp : (x.drop i).take k ∈ U (p, [])) :
    produces (substringDecoder U) (substringProgram i k n p (x.take i ++ x.drop (i + k))) [] x := by
  set rest := x.take i ++ x.drop (i + k) with hrest
  have hrest_len : rest.length = n - k := by
    rw [hrest, List.length_append, List.length_take, List.length_drop, hx]
    omega
  have hi : subI (substringProgram i k n p rest) = i := by
    simp [subI, substringProgram, decodeFirst_pairCode, bitsToNat_bits]
  have hk : subK (substringProgram i k n p rest) = k := by
    simp [subK, substringProgram, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  have hn : subN (substringProgram i k n p rest) = n := by
    simp [subN, substringProgram, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  have hb : subB (substringProgram i k n p rest) = p ++ rest := by
    simp [subB, substringProgram, decodeSecond_pairCode]
  have hj : subJ (substringProgram i k n p rest) = p.length := by
    unfold subJ
    rw [hb, hk, hn, List.length_append, hrest_len]
    omega
  have hprog : subProg (substringProgram i k n p rest) = p := by
    unfold subProg; rw [hb, hj]; exact List.take_left' rfl
  have hrst : subRest (substringProgram i k n p rest) = rest := by
    unfold subRest; rw [hb, hj]; exact List.drop_left' rfl
  have hpre : subPre (substringProgram i k n p rest) = x.take i := by
    unfold subPre
    rw [hrst, hi, hrest]
    refine List.take_left' ?_
    rw [List.length_take, hx]; omega
  have hsuf : subSuf (substringProgram i k n p rest) = x.drop (i + k) := by
    unfold subSuf
    rw [hrst, hi, hrest]
    refine List.drop_left' ?_
    rw [List.length_take, hx]; omega
  have hxsplit : x.take i ++ ((x.drop i).take k ++ x.drop (i + k)) = x := by
    have h1 : (x.drop i).drop k = x.drop (i + k) := by
      rw [List.drop_drop]
    rw [← h1, List.take_append_drop]
    exact List.take_append_drop i x
  change _ ∈ substringDecoder U _
  unfold substringDecoder
  simp only [hprog, hpre, hsuf]
  rw [Part.mem_map_iff]
  exact ⟨(x.drop i).take k, hp, hxsplit⟩

/-- **Exercise 53(d).** Every substring of length `k` of an incompressible string
of length `n` has complexity at least `k - O(log n)`. -/
theorem plainK_substring_of_incompressible (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n k i : ℕ) (x : BitString), x.length = n → (n : ℕ∞) ≤ plainK U x →
      i + k ≤ n → (k : ℕ∞) ≤ plainK U ((x.drop i).take k) + ((logSlack c n : ℕ) : ℕ∞) := by
  obtain ⟨C, hC⟩ := hU.2 (substringDecoder U) (substringDecoder_isDecompressor U hU.1)
  refine ⟨max 6 (3 + C), fun n k i x hx hxK hik => ?_⟩
  set s := (x.drop i).take k with hs
  by_cases htop : plainK U s = ⊤
  · rw [htop]; simp
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U s [] j).mp (le_of_eq hj.symm)
  have hpl : programLength p = p.length := rfl
  have hprod := substring_produces U i k n x p hx hik (hs ▸ hp_prod)
  set rest := x.take i ++ x.drop (i + k) with hrest
  have hrest_len : rest.length = n - k := by
    rw [hrest, List.length_append, List.length_take, List.length_drop, hx]
    omega
  set Ln := (Nat.bits n).length with hLn
  have hLi : (Nat.bits i).length ≤ Ln := length_natBits_mono (by omega)
  have hLk : (Nat.bits k).length ≤ Ln := length_natBits_mono (by omega)
  have hq_len : (substringProgram i k n p rest).length ≤
      6 * Ln + 3 + (p.length + (n - k)) := by
    rw [substringProgram_length, hrest_len]
    omega
  have h2 : condK (substringDecoder U) x [] ≤
      ((6 * Ln + 3 + (p.length + (n - k)) : ℕ) : ℕ∞) := by
    refine le_trans (sInf_le ⟨substringProgram i k n p rest, hprod, rfl⟩) ?_
    exact_mod_cast hq_len
  have h3 : (n : ℕ∞) ≤ ((6 * Ln + 3 + (p.length + (n - k)) + C : ℕ) : ℕ∞) := by
    refine hxK.trans ((hC x []).trans ?_)
    calc condK (substringDecoder U) x [] + (C : ℕ∞)
        ≤ ((6 * Ln + 3 + (p.length + (n - k)) : ℕ) : ℕ∞) + (C : ℕ∞) := by gcongr
      _ = ((6 * Ln + 3 + (p.length + (n - k)) + C : ℕ) : ℕ∞) := by push_cast; ring
  have h4 : n ≤ 6 * Ln + 3 + (p.length + (n - k)) + C := by exact_mod_cast h3
  have h5 : k ≤ j + (max 6 (3 + C) * Ln + max 6 (3 + C)) := by
    have h6 : 6 * Ln ≤ max 6 (3 + C) * Ln := Nat.mul_le_mul_right _ (le_max_left _ _)
    have h7 : 3 + C ≤ max 6 (3 + C) := le_max_right _ _
    omega
  calc (k : ℕ∞) ≤ ((j + logSlack (max 6 (3 + C)) n : ℕ) : ℕ∞) := by
        rw [show logSlack (max 6 (3 + C)) n = max 6 (3 + C) * Ln + max 6 (3 + C) from rfl]
        exact_mod_cast h5
    _ = (j : ℕ∞) + ((logSlack (max 6 (3 + C)) n : ℕ) : ℕ∞) := by push_cast; ring
    _ = plainK U s + ((logSlack (max 6 (3 + C)) n : ℕ) : ℕ∞) := by rw [hj]

/-! ### Detecting a run of zeros -/

/-- `hasZeroRun L x` tests whether `x` contains a block of `L` consecutive zeros. -/
def hasZeroRun (L : ℕ) (x : BitString) : Bool :=
  decide ((List.range (x.length + 1)).findIdx
    (fun i => decide ((x.drop i).take L = List.replicate L false)) < x.length + 1)

/-- The zero-run test succeeds exactly when `L` consecutive zeros occur as an infix. -/
lemma hasZeroRun_iff (L : ℕ) (x : BitString) :
    hasZeroRun L x = true ↔ List.replicate L false <:+: x := by
  unfold hasZeroRun
  rw [decide_eq_true_eq]
  have hrlen : (List.range (x.length + 1)).length = x.length + 1 := List.length_range
  have key := List.findIdx_lt_length
    (p := fun i => decide ((x.drop i).take L = List.replicate L false))
    (xs := List.range (x.length + 1))
  rw [hrlen] at key
  rw [key]
  constructor
  · rintro ⟨i, -, hi⟩
    rw [decide_eq_true_eq] at hi
    have h1 : (x.drop i).take L <:+: x :=
      ((x.drop i).take_prefix L).isInfix.trans (x.drop_suffix i).isInfix
    rwa [hi] at h1
  · rintro ⟨s, t, hst⟩
    have hi_mem : s.length ∈ List.range (x.length + 1) := by
      rw [List.mem_range]
      have : s.length ≤ x.length := by
        rw [← hst]
        simp
      omega
    have hi : (x.drop s.length).take L = List.replicate L false := by
      rw [← hst, List.append_assoc, List.drop_left' rfl]
      exact List.take_left' (by simp)
    exact ⟨s.length, hi_mem, by rw [decide_eq_true_eq]; exact hi⟩

/-! ### Counting the strings without a long run of zeros -/

/-- The list of strings of length `k` with no run of `L` zeros. -/
def noRunList (L k : ℕ) : List BitString :=
  (allStrings k).filter (fun x => ! hasZeroRun L x)

/-- The listed strings of length `k` are exactly those with no run of `L` zeros. -/
lemma mem_noRunList (L k : ℕ) (x : BitString) :
    x ∈ noRunList L k ↔ x.length = k ∧ ¬ (List.replicate L false <:+: x) := by
  unfold noRunList
  rw [List.mem_filter, mem_allStrings, ← hasZeroRun_iff]
  simp

/-- The list of strings without a long zero run has no repetitions. -/
lemma noRunList_nodup (L k : ℕ) : (noRunList L k).Nodup :=
  (allStrings_nodup k).filter _

/-- The strings of length `k` with no run of `L` zeros, as a finite set. -/
def noRunFinset (L k : ℕ) : Finset BitString := (noRunList L k).toFinset

/-- The finite set of run-free strings of length `k` consists of the strings of length `k` with
no run of `L` zeros. -/
lemma mem_noRunFinset (L k : ℕ) (x : BitString) :
    x ∈ noRunFinset L k ↔ x.length = k ∧ ¬ (List.replicate L false <:+: x) := by
  rw [noRunFinset, List.mem_toFinset, mem_noRunList]

/-- The finite set of run-free strings has as many elements as the list enumerating them. -/
lemma card_noRunFinset (L k : ℕ) : (noRunFinset L k).card = (noRunList L k).length :=
  List.toFinset_card_of_nodup (noRunList_nodup L k)

/-- Run-free strings of length `k` are strings of length `k`. -/
lemma noRunFinset_subset (L k : ℕ) : noRunFinset L k ⊆ stringsOfLength k := by
  intro x hx
  rw [mem_stringsOfLength]
  exact ((mem_noRunFinset L k x).mp hx).1

/-- Prefixing a run-free string by a block of `L` bits that is not all zero: the count grows by a
factor of at most `2 ^ L - 1` per block. -/
lemma card_noRunFinset_step (L j : ℕ) :
    (noRunFinset L (L + j)).card ≤ (2 ^ L - 1) * (noRunFinset L j).card := by
  classical
  set T : Finset BitString := (stringsOfLength L).erase (List.replicate L false) with hT
  have hTcard : T.card = 2 ^ L - 1 := by
    rw [hT, Finset.card_erase_of_mem, card_stringsOfLength]
    rw [mem_stringsOfLength, List.length_replicate]
  have hmaps : ∀ x ∈ noRunFinset L (L + j), (x.take L, x.drop L) ∈ T ×ˢ noRunFinset L j := by
    intro x hx
    rw [mem_noRunFinset] at hx
    obtain ⟨hlen, hno⟩ := hx
    rw [Finset.mem_product]
    constructor
    · rw [hT, Finset.mem_erase, mem_stringsOfLength, List.length_take, hlen]
      refine ⟨?_, by omega⟩
      intro heq
      exact hno (heq ▸ ((x.take_prefix L).isInfix))
    · rw [mem_noRunFinset, List.length_drop, hlen]
      refine ⟨by omega, ?_⟩
      intro hinf
      exact hno (hinf.trans (x.drop_suffix L).isInfix)
  have hinj : Set.InjOn (fun x : BitString => (x.take L, x.drop L)) ↑(noRunFinset L (L + j)) := by
    intro a _ b _ hab
    have h1 : a.take L = b.take L := congrArg Prod.fst hab
    have h2 : a.drop L = b.drop L := congrArg Prod.snd hab
    calc a = a.take L ++ a.drop L := (List.take_append_drop L a).symm
      _ = b.take L ++ b.drop L := by rw [h1, h2]
      _ = b := List.take_append_drop L b
  have := Finset.card_le_card_of_injOn (fun x : BitString => (x.take L, x.drop L))
    (fun x hx => hmaps x (by simpa using hx)) hinj
  rwa [Finset.card_product, hTcard] at this

/-- There are at most `(2 ^ L - 1) ^ m * 2 ^ r` run-free strings of length `m L + r`, so a
positive fraction of the bits is saved. -/
lemma card_noRunFinset_le (L : ℕ) :
    ∀ (m r : ℕ), (noRunFinset L (m * L + r)).card ≤ (2 ^ L - 1) ^ m * 2 ^ r := by
  intro m
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_mul, Nat.zero_add, pow_zero, Nat.one_mul]
    calc (noRunFinset L r).card ≤ (stringsOfLength r).card :=
          Finset.card_le_card (noRunFinset_subset L r)
      _ = 2 ^ r := card_stringsOfLength r
  | succ m ih =>
    intro r
    have harg : (m + 1) * L + r = L + (m * L + r) := by ring
    rw [harg]
    calc (noRunFinset L (L + (m * L + r))).card
        ≤ (2 ^ L - 1) * (noRunFinset L (m * L + r)).card := card_noRunFinset_step L _
      _ ≤ (2 ^ L - 1) * ((2 ^ L - 1) ^ m * 2 ^ r) := Nat.mul_le_mul_left _ (ih r)
      _ = (2 ^ L - 1) ^ (m + 1) * 2 ^ r := by ring

/-! ### Elementary growth estimates -/

/-! ### A multiplicative gain estimate -/

/-! ### The index decompressor for Exercise 53(e) -/

/-- The zero-run test is primitive recursive in the run length and the string. -/
lemma hasZeroRun_primrec : Primrec₂ hasZeroRun := by
  have hrange : Primrec (fun q : ℕ × BitString => List.range (q.2.length + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd))
  have hpred : Primrec₂ (fun (q : ℕ × BitString) (i : ℕ) =>
      decide ((q.2.drop i).take q.1 = List.replicate q.1 false)) := by
    have hL : Primrec (fun r : (ℕ × BitString) × ℕ => r.1.1) := Primrec.fst.comp Primrec.fst
    have hdrop : Primrec (fun r : (ℕ × BitString) × ℕ => (r.1.2.drop r.2).take r.1.1) :=
      Primrec.list_take.comp hL
        (Primrec.list_drop.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
    have hrep : Primrec (fun r : (ℕ × BitString) × ℕ => List.replicate r.1.1 false) :=
      KraftChaitin.replicate_false_primrec.comp hL
    have h0 := Primrec.eq.comp hdrop hrep
    unfold PrimrecPred at h0
    obtain ⟨inst, h⟩ := h0
    exact Primrec.of_eq h (fun _ => by rw [decide_eq_decide])
  have hfind : Primrec (fun q : ℕ × BitString =>
      (List.range (q.2.length + 1)).findIdx
        (fun i => decide ((q.2.drop i).take q.1 = List.replicate q.1 false))) :=
    Primrec.list_findIdx hrange hpred
  have h0 := Primrec.nat_lt.comp hfind
    (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd))
  unfold PrimrecPred at h0
  obtain ⟨inst, h⟩ := h0
  exact Primrec.of_eq h (fun _ => by unfold hasZeroRun; rw [decide_eq_decide])

/-- The list of run-free strings of a given length is primitive recursive in both parameters. -/
lemma noRunList_primrec : Primrec₂ noRunList := by
  have hall : Primrec (fun p : ℕ × ℕ => allStrings p.2) :=
    allStrings_primrec.comp Primrec.snd
  have hpred : Primrec₂ (fun (p : ℕ × ℕ) (x : BitString) => ! hasZeroRun p.1 x) :=
    Primrec.not.comp (hasZeroRun_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact list_filter_primrec hall hpred

/-- Decompressor for Exercise 53(e): the program `pairCode (bits n) (pairCode (bits L) w)`
returns the string listed at position `w` among the length-`n` strings without a run of
`L` zeros. -/
def runIndexDecoder : Map := fun pr =>
  Part.some ((noRunList (bitsToNat (decodeFirst (decodeSecond pr.1)))
      (bitsToNat (decodeFirst pr.1))).getD
    (decodeFixedWidthNatCode (decodeSecond (decodeSecond pr.1))) [])

/-- The decompressor indexing the run-free strings is a decompressor. -/
lemma runIndexDecoder_isDecompressor : isDecompressor runIndexDecoder := by
  have hn : Primrec (fun pr : BitString × BitString => bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp Primrec.fst)
  have hL : Primrec (fun pr : BitString × BitString =>
      bitsToNat (decodeFirst (decodeSecond pr.1))) :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
  have hi : Primrec (fun pr : BitString × BitString =>
      decodeFixedWidthNatCode (decodeSecond (decodeSecond pr.1))) :=
    (bitsToNat_primrec.comp Primrec.list_reverse).comp
      (decodeSecond_primrec.comp (decodeSecond_primrec.comp Primrec.fst))
  have hlist : Primrec (fun pr : BitString × BitString =>
      noRunList (bitsToNat (decodeFirst (decodeSecond pr.1))) (bitsToNat (decodeFirst pr.1))) :=
    noRunList_primrec.comp hL hn
  have h : Computable (fun pr : BitString × BitString =>
      (noRunList (bitsToNat (decodeFirst (decodeSecond pr.1)))
        (bitsToNat (decodeFirst pr.1))).getD
      (decodeFixedWidthNatCode (decodeSecond (decodeSecond pr.1))) []) := by
    have hget : Primrec (fun pr : BitString × BitString =>
        (noRunList (bitsToNat (decodeFirst (decodeSecond pr.1)))
          (bitsToNat (decodeFirst pr.1)))[decodeFixedWidthNatCode
            (decodeSecond (decodeSecond pr.1))]?) :=
      Primrec.list_getElem?.comp hlist hi
    exact (Primrec.option_getD.comp hget (Primrec.const [])).to_comp
  exact h.partrec

/-- On the program carrying `n`, `L` and an index `i`, the run-free indexing decompressor outputs
the `i`-th length-`n` string without a run of `L` zeros. -/
lemma runIndex_produces (n L i W : ℕ) (x : BitString)
    (hx : (noRunList L n).getD i [] = x) :
    produces runIndexDecoder
      (pairCode (Nat.bits n) (pairCode (Nat.bits L) (fixedWidthNatCode i W))) [] x := by
  change _ ∈ runIndexDecoder _
  unfold runIndexDecoder
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode,
    decodeSecond_pairCode, bitsToNat_bits, bitsToNat_bits, decodeFixedWidthNatCode_encode]
  rw [hx]
  exact Part.mem_some x

/-! ### Exercise 53(e) -/

private lemma sq_add_one_le_two_pow : ∀ t : ℕ, 5 ≤ t → t ^ 2 + 1 ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 5 with h5 | h5
    · interval_cases k
      · omega
      · omega
      · omega
      · omega
      · norm_num
    · have h1 := ih h5
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      nlinarith

/-- Any fixed power is eventually dominated by the exponential. -/
private lemma pow_succ_le_two_pow (k : ℕ) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → (s + 1) ^ k ≤ 2 ^ s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, fun s _ => by simpa using Nat.one_le_two_pow⟩
  refine ⟨k * (2 * k + 6), fun s hs => ?_⟩
  set t := s / k with ht
  have hkpos : 0 < k := hk
  have hdm : k * (s / k) + s % k = s := Nat.div_add_mod s k
  have hmod : s % k < k := Nat.mod_lt s hkpos
  have hts : k * t ≤ s := by rw [ht]; omega
  have hst : s < k * (t + 1) := by
    rw [ht, Nat.mul_add, Nat.mul_one]
    omega
  have ht_ge : 2 * k + 6 ≤ t := by
    by_contra hcon
    replace hcon := Nat.lt_of_not_le hcon
    have : s < k * (2 * k + 6) := by
      calc s < k * (t + 1) := hst
        _ ≤ k * (2 * k + 6) := Nat.mul_le_mul_left k (by omega)
    omega
  have h5 : 5 ≤ t := by omega
  have hpow := sq_add_one_le_two_pow t h5
  have hbig : s + 1 ≤ 2 ^ t := by
    have hk2 : 2 * k ≤ t := by omega
    have h1 : k * (t + 1) ≤ t ^ 2 := by nlinarith
    omega
  calc (s + 1) ^ k ≤ (2 ^ t) ^ k := Nat.pow_le_pow_left hbig k
    _ = 2 ^ (t * k) := by rw [← pow_mul]
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; exact hts)

/-- The `k`-th power of the binary logarithm is eventually dominated by the argument. -/
private lemma const_mul_log_pow_le (k C : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (Nat.log 2 n + 1) ^ k ≤ n := by
  obtain ⟨s₀, hs₀⟩ := pow_succ_le_two_pow (k + 1)
  refine ⟨2 ^ (s₀ + C), fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.two_pow_pos (s₀ + C)) hn
  set s := Nat.log 2 n with hs
  have hsge : s₀ + C ≤ s := by
    rw [hs]
    exact Nat.le_log_of_pow_le (by decide) hn
  have hpow_le : 2 ^ s ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
  have hC : C ≤ s + 1 := by omega
  calc C * (s + 1) ^ k ≤ (s + 1) * (s + 1) ^ k := Nat.mul_le_mul_right _ hC
    _ = (s + 1) ^ (k + 1) := by ring
    _ ≤ 2 ^ s := hs₀ s (by omega)
    _ ≤ n := hpow_le

/-- The block length `L = ⌈a log₂ n⌉` is subexponential: `2 ^ (L q) ≤ 2 ^ q * n ^ (q-1)`
whenever `a ≤ 1 - 1/q`. -/
private lemma two_pow_ceil_logb_pow_le (a : ℝ) (ha : 0 ≤ a) (q : ℕ) (hq : 1 ≤ q)
    (haq : a ≤ 1 - 1 / (q : ℝ)) (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ ⌈a * Real.logb 2 n⌉₊) ^ q ≤ 2 ^ q * n ^ (q - 1) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set Lg := Real.logb 2 n with hLg
  have hLg0 : 0 ≤ Lg := Real.logb_nonneg (by norm_num) hn1
  set L := ⌈a * Lg⌉₊ with hL
  have hceil : (L : ℝ) < a * Lg + 1 := Nat.ceil_lt_add_one (by positivity)
  have hqa : (q : ℝ) * a ≤ (q : ℝ) - 1 := by
    have := mul_le_mul_of_nonneg_left haq (le_of_lt hqR)
    calc (q : ℝ) * a ≤ (q : ℝ) * (1 - 1 / (q : ℝ)) := this
      _ = (q : ℝ) - 1 := by field_simp
  have hexp : ((L * q : ℕ) : ℝ) ≤ ((q : ℝ) - 1) * Lg + (q : ℝ) := by
    push_cast
    have h1 : (L : ℝ) * q ≤ (a * Lg + 1) * q := by
      apply mul_le_mul_of_nonneg_right (le_of_lt hceil) (le_of_lt hqR)
    have h2 : (a * Lg + 1) * q = ((q : ℝ) * a) * Lg + q := by ring
    have h3 : ((q : ℝ) * a) * Lg ≤ ((q : ℝ) - 1) * Lg :=
      mul_le_mul_of_nonneg_right hqa hLg0
    linarith
  have hreal : ((2 ^ (L * q) : ℕ) : ℝ) ≤ ((2 ^ q * n ^ (q - 1) : ℕ) : ℝ) := by
    push_cast
    have hstep : (2 : ℝ) ^ ((L * q : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((q : ℝ) - 1) * Lg + (q : ℝ)) :=
      Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hexp
    have hlhs : (2 : ℝ) ^ ((L * q : ℕ) : ℝ) = (2 : ℝ) ^ (L * q) :=
      Real.rpow_natCast 2 (L * q)
    have hrhs : (2 : ℝ) ^ (((q : ℝ) - 1) * Lg + (q : ℝ)) = (n : ℝ) ^ (q - 1) * 2 ^ q := by
      rw [Real.rpow_add (by norm_num)]
      have h1 : (2 : ℝ) ^ (((q : ℝ) - 1) * Lg) = ((2 : ℝ) ^ Lg) ^ ((q : ℝ) - 1) := by
        rw [mul_comm, Real.rpow_mul (by norm_num)]
      have h2 : (2 : ℝ) ^ Lg = (n : ℝ) := by
        rw [hLg]
        exact Real.rpow_logb (by norm_num) (by norm_num) hnR
      have h3 : ((q : ℝ) - 1) = ((q - 1 : ℕ) : ℝ) := by
        have : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          push_cast [Nat.cast_sub hq]
          ring
        rw [this]
      rw [h1, h2, h3, Real.rpow_natCast, Real.rpow_natCast]
    rw [hlhs] at hstep
    rw [hrhs] at hstep
    calc (2 : ℝ) ^ (L * q) ≤ (n : ℝ) ^ (q - 1) * 2 ^ q := hstep
      _ = 2 ^ q * (n : ℝ) ^ (q - 1) := by ring
  have hnat : 2 ^ (L * q) ≤ 2 ^ q * n ^ (q - 1) := by exact_mod_cast hreal
  calc (2 ^ L) ^ q = 2 ^ (L * q) := by rw [← pow_mul]
    _ ≤ 2 ^ q * n ^ (q - 1) := hnat

private lemma two_mul_sub_one_pow_le (A : ℕ) (hA : 2 ≤ A) : 2 * (A - 1) ^ A ≤ A ^ A := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hBpos : (0 : ℝ) < (A : ℝ) - 1 := by linarith
  have hbern : (1 : ℝ) + (A : ℝ) * (1 / ((A : ℝ) - 1)) ≤ (1 + 1 / ((A : ℝ) - 1)) ^ A := by
    refine one_add_mul_le_pow ?_ A
    have : (0 : ℝ) < 1 / ((A : ℝ) - 1) := by positivity
    linarith
  have hAB : (1 : ℝ) ≤ (A : ℝ) * (1 / ((A : ℝ) - 1)) := by
    rw [mul_one_div, le_div_iff₀ hBpos, one_mul]
    linarith
  have hge2 : (2 : ℝ) ≤ (1 + 1 / ((A : ℝ) - 1)) ^ A := by linarith
  have hfac : ((A : ℝ) - 1) ^ A * (1 + 1 / ((A : ℝ) - 1)) ^ A = (A : ℝ) ^ A := by
    rw [← mul_pow]
    have hmul : ((A : ℝ) - 1) * (1 + 1 / ((A : ℝ) - 1)) = (A : ℝ) := by
      field_simp
      ring
    rw [hmul]
  have hpos : (0 : ℝ) ≤ ((A : ℝ) - 1) ^ A := by positivity
  have hreal : (2 : ℝ) * ((A : ℝ) - 1) ^ A ≤ (A : ℝ) ^ A := by
    calc (2 : ℝ) * ((A : ℝ) - 1) ^ A = ((A : ℝ) - 1) ^ A * 2 := by ring
      _ ≤ ((A : ℝ) - 1) ^ A * (1 + 1 / ((A : ℝ) - 1)) ^ A :=
          mul_le_mul_of_nonneg_left hge2 hpos
      _ = (A : ℝ) ^ A := hfac
  have hcast : (((A - 1 : ℕ)) : ℝ) = (A : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ A := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hfinal : ((2 * (A - 1) ^ A : ℕ) : ℝ) ≤ ((A ^ A : ℕ) : ℝ) := by
    push_cast [hcast]
    exact hreal
  exact_mod_cast hfinal

private lemma sub_one_pow_mul_two_pow_le_aux (A : ℕ) (hA : 2 ≤ A) :
    ∀ v : ℕ, (A - 1) ^ (A * v) * 2 ^ v ≤ A ^ (A * v) := by
  intro v
  induction v with
  | zero => simp
  | succ v ih =>
    have hstep := two_mul_sub_one_pow_le A hA
    have hmul : (A - 1) ^ (A * (v + 1)) * 2 ^ (v + 1)
        = ((A - 1) ^ (A * v) * 2 ^ v) * ((A - 1) ^ A * 2) := by
      rw [Nat.mul_add, Nat.mul_one, pow_add, pow_succ]
      ring
    rw [hmul]
    calc ((A - 1) ^ (A * v) * 2 ^ v) * ((A - 1) ^ A * 2)
        ≤ A ^ (A * v) * ((A - 1) ^ A * 2) := Nat.mul_le_mul_right _ ih
      _ ≤ A ^ (A * v) * A ^ A := by
          refine Nat.mul_le_mul_left _ ?_
          calc (A - 1) ^ A * 2 = 2 * (A - 1) ^ A := by ring
            _ ≤ A ^ A := hstep
      _ = A ^ (A * (v + 1)) := by rw [← pow_add]; ring_nf

private lemma sub_one_pow_mul_two_pow_le (A m v : ℕ) (hA : 2 ≤ A) (hv : A * v ≤ m) :
    (A - 1) ^ m * 2 ^ v ≤ A ^ m := by
  have hsplit : (A - 1) ^ m = (A - 1) ^ (A * v) * (A - 1) ^ (m - A * v) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit' : A ^ m = A ^ (A * v) * A ^ (m - A * v) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, hsplit']
  calc (A - 1) ^ (A * v) * (A - 1) ^ (m - A * v) * 2 ^ v
      = ((A - 1) ^ (A * v) * 2 ^ v) * (A - 1) ^ (m - A * v) := by ring
    _ ≤ A ^ (A * v) * (A - 1) ^ (m - A * v) :=
        Nat.mul_le_mul_right _ (sub_one_pow_mul_two_pow_le_aux A hA v)
    _ ≤ A ^ (A * v) * A ^ (m - A * v) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private lemma logb_le_log_add_one (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 n ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    exact_mod_cast this.le
  have h1 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
    (Real.logb_le_logb (by norm_num) hpos (by positivity)).mpr hle
  simpa [Real.logb_pow, Real.logb_self_eq_one] using h1

/-- Upper bound on the size of `noRunList L n` when `2 ^ L * K * L ≤ n`. -/
private lemma noRunList_length_le (L n K : ℕ) (hL1 : 1 ≤ L) (hmain : 2 ^ L * K * L ≤ n) :
    (noRunList L n).length ≤ 2 ^ (n - K) := by
  set m := n / L with hm; set r := n % L with hr
  have hnmr : m * L + r = n := Nat.div_add_mod' n L
  have hLpos : 0 < L := by omega
  have hdiv : 2 ^ L * K ≤ m := by
    have h1 : 2 ^ L * K ≤ n / L := (Nat.le_div_iff_mul_le hLpos).mpr hmain
    rwa [← hm] at h1
  have hA : 2 ≤ 2 ^ L := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
  have hcount : (noRunList L n).length ≤ (2 ^ L - 1) ^ m * 2 ^ r := by
    have h1 := card_noRunFinset_le L m r
    rw [hnmr, card_noRunFinset] at h1
    exact h1
  have hkey : (2 ^ L - 1) ^ m * 2 ^ K ≤ (2 ^ L) ^ m :=
    sub_one_pow_mul_two_pow_le (2 ^ L) m K hA hdiv
  have hSK : (noRunList L n).length * 2 ^ K ≤ 2 ^ n := by
    have hpow_n : (2 ^ L) ^ m * 2 ^ r = 2 ^ n := by rw [← pow_mul, ← pow_add, mul_comm L m, hnmr]
    calc (noRunList L n).length * 2 ^ K ≤ ((2 ^ L - 1) ^ m * 2 ^ r) * 2 ^ K :=
          Nat.mul_le_mul_right _ hcount
      _ = ((2 ^ L - 1) ^ m * 2 ^ K) * 2 ^ r := by ring
      _ ≤ (2 ^ L) ^ m * 2 ^ r := Nat.mul_le_mul_right _ hkey
      _ = 2 ^ n := hpow_n
  have hKn : K ≤ n := by nlinarith [hA, hL1, hmain]
  have h2 : 2 ^ (n - K) * 2 ^ K = 2 ^ n := by rw [← pow_add]; congr 1; omega
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos K)
  rwa [h2]

/-- Product bound `2 ^ L * K * L ≤ n` from the `q`-th power bounds `(2 ^ L) ^ q ≤ 2 ^ q * n ^ (q-1)`
and `2 ^ q * (K * L) ^ q ≤ n`: the two factors together consume at most one factor `n` each time
they are raised to the power `q`, and a `q`-th power comparison of naturals is a comparison. -/
private lemma two_pow_mul_mul_le (q L K n : ℕ) (hq : 1 ≤ q)
    (hpowq : (2 ^ L) ^ q ≤ 2 ^ q * n ^ (q - 1))
    (hstep : 2 ^ q * (K * L) ^ q ≤ n) :
    2 ^ L * K * L ≤ n := by
  have hpow : (2 ^ L * K * L) ^ q ≤ n ^ q := by
    have h1 : (2 ^ L * K * L) ^ q = (2 ^ L) ^ q * (K * L) ^ q := by rw [mul_assoc, mul_pow]
    have h2 : n ^ q = n * n ^ (q - 1) := by rw [← pow_succ', show q - 1 + 1 = q by omega]
    rw [h1, h2]
    calc (2 ^ L) ^ q * (K * L) ^ q ≤ (2 ^ q * n ^ (q - 1)) * (K * L) ^ q :=
          Nat.mul_le_mul_right _ hpowq
      _ = (2 ^ q * (K * L) ^ q) * n ^ (q - 1) := by ring
      _ ≤ n * n ^ (q - 1) := Nat.mul_le_mul_right _ hstep
  exact (Nat.pow_le_pow_iff_left (by omega)).mp hpow

/-- **Exercise 53(e).** For every `c < 1`, all incompressible strings of
sufficiently large length contain a run of `⌈c log₂ n⌉` zeros. -/
theorem incompressible_contains_zero_run (U : Map) (hU : isOptimalConditional U)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : BitString), N ≤ n → x.length = n → (n : ℕ∞) ≤ plainK U x →
      List.replicate ⌈a * Real.logb 2 n⌉₊ false <:+: x := by
  obtain ⟨C0, hC0⟩ := hU.2 runIndexDecoder runIndexDecoder_isDecompressor
  obtain ⟨q0, hq0⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 1 - a by linarith)
  set q := q0 + 1 with hq_def
  have hq : 1 ≤ q := by omega
  have haq : a ≤ 1 - 1 / (q : ℝ) := by
    have hcast : ((q : ℕ) : ℝ) = (q0 : ℝ) + 1 := by rw [hq_def]; push_cast; ring
    rw [hcast]
    linarith
  obtain ⟨N1, hN1⟩ := const_mul_log_pow_le (2 * q) (2 ^ q * (C0 + 8) ^ q)
  obtain ⟨N2, hN2⟩ := const_mul_log_pow_le 1 (C0 + 8)
  refine ⟨max (max N1 N2) 2, fun n x hn hxlen hxK => ?_⟩
  by_contra hno
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left N1 N2) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right N1 N2) (le_max_left _ _)) hn
  set Lg := Nat.log 2 n with hLg
  set L := ⌈a * Real.logb 2 n⌉₊ with hLdef
  have hlogpos : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by exact_mod_cast hn2)
  have hL1 : 1 ≤ L := Nat.one_le_ceil_iff.mpr (by positivity)
  have hLle : L ≤ Lg + 1 := by
    rw [hLdef]
    refine Nat.ceil_le.mpr ?_
    have h1 : a * Real.logb 2 n ≤ Real.logb 2 n := by nlinarith
    exact h1.trans (logb_le_log_add_one n (by omega))
  -- the index of `x` among the strings without a run of `L` zeros
  have hxmem : x ∈ noRunList L n := (mem_noRunList L n x).mpr ⟨hxlen, hno⟩
  set i := List.idxOf x (noRunList L n) with hidef
  have hilt : i < (noRunList L n).length := List.idxOf_lt_length_of_mem hxmem
  have hgetD : (noRunList L n).getD i [] = x := by
    rw [List.getD_eq_getElem?_getD, hidef, List.getElem?_idxOf hxmem]
    rfl
  set W := Nat.size i with hW
  have hprod := runIndex_produces n L i W x hgetD
  set bn := (Nat.bits n).length with hbn
  set bL := (Nat.bits L).length with hbL
  have hproglen :
      (pairCode (Nat.bits n) (pairCode (Nat.bits L) (fixedWidthNatCode i W))).length
        = 2 * bn + 1 + (2 * bL + 1 + W) := by
    rw [length_pairCode, length_pairCode, fixedWidthNatCode_length (Nat.lt_size_self (n := i)),
      ← hbn, ← hbL]
    ring
  have hcomp : plainK U x ≤ ((2 * bn + 1 + (2 * bL + 1 + W) + C0 : ℕ) : ℕ∞) := by
    refine (hC0 x []).trans ?_
    have h2 : condK runIndexDecoder x [] ≤ ((2 * bn + 1 + (2 * bL + 1 + W) : ℕ) : ℕ∞) := by
      refine sInf_le ⟨_, hprod, ?_⟩
      rw [show programLength (pairCode (Nat.bits n)
          (pairCode (Nat.bits L) (fixedWidthNatCode i W)))
        = (pairCode (Nat.bits n) (pairCode (Nat.bits L) (fixedWidthNatCode i W))).length from rfl,
        hproglen]
    calc condK runIndexDecoder x [] + (C0 : ℕ∞)
        ≤ ((2 * bn + 1 + (2 * bL + 1 + W) : ℕ) : ℕ∞) + (C0 : ℕ∞) := by gcongr
      _ = ((2 * bn + 1 + (2 * bL + 1 + W) + C0 : ℕ) : ℕ∞) := by push_cast; ring
  have hnat : n ≤ 2 * bn + 2 * bL + 2 + W + C0 := by
    have : ((n : ℕ) : ℕ∞) ≤ ((2 * bn + 1 + (2 * bL + 1 + W) + C0 : ℕ) : ℕ∞) := hxK.trans hcomp
    have h2 : n ≤ 2 * bn + 1 + (2 * bL + 1 + W) + C0 := by exact_mod_cast this
    omega
  -- numeric bounds on the pieces of the program
  set K := 2 * bn + 2 * bL + 3 + C0 with hK
  have hbn_le : bn ≤ Lg + 1 := by
    rw [hbn, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hbL_le : bL ≤ Lg + 1 := by
    have h1 : bL ≤ L := by
      rw [hbL, Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hK_le : K ≤ (C0 + 7) * (Lg + 1) := by
    have h1 : 4 * (Lg + 1) ≤ (C0 + 4) * (Lg + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : C0 + 3 ≤ (C0 + 3) * (Lg + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : (C0 + 4) * (Lg + 1) + (C0 + 3) * (Lg + 1) = (2 * C0 + 7) * (Lg + 1) := by ring
    have h4 : (C0 + 7) * (Lg + 1) ≤ (2 * C0 + 7) * (Lg + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [hK]
    nlinarith [hbn_le, hbL_le, Nat.zero_le Lg]
  -- the key inequality `2 ^ L * K * L ≤ n`
  have hKL : K * L ≤ (C0 + 8) * (Lg + 1) ^ 2 := by
    have h1 : K * L ≤ ((C0 + 7) * (Lg + 1)) * (Lg + 1) :=
      Nat.mul_le_mul hK_le hLle
    have h2 : ((C0 + 7) * (Lg + 1)) * (Lg + 1) = (C0 + 7) * (Lg + 1) ^ 2 := by ring
    have h3 : (C0 + 7) * (Lg + 1) ^ 2 ≤ (C0 + 8) * (Lg + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hstep : 2 ^ q * (K * L) ^ q ≤ n := by
    have h1 : (K * L) ^ q ≤ ((C0 + 8) * (Lg + 1) ^ 2) ^ q := Nat.pow_le_pow_left hKL q
    have h2 : 2 ^ q * ((C0 + 8) * (Lg + 1) ^ 2) ^ q =
        (2 ^ q * (C0 + 8) ^ q) * (Lg + 1) ^ (2 * q) := by
      rw [mul_pow, ← pow_mul]; ring
    calc 2 ^ q * (K * L) ^ q ≤ 2 ^ q * ((C0 + 8) * (Lg + 1) ^ 2) ^ q :=
          Nat.mul_le_mul_left _ h1
      _ = (2 ^ q * (C0 + 8) ^ q) * (Lg + 1) ^ (2 * q) := h2
      _ ≤ n := hN1 n hnN1
  have hmain : 2 ^ L * K * L ≤ n :=
    two_pow_mul_mul_le q L K n hq
      (by rw [hLdef]; exact two_pow_ceil_logb_pow_le a ha.le q hq haq n (by omega))
      hstep
  have hlen_le : (noRunList L n).length ≤ 2 ^ (n - K) := noRunList_length_le L n K hL1 hmain
  have hi_lt : i < 2 ^ (n - K) := lt_of_lt_of_le hilt hlen_le
  have hWle : W ≤ n - K := by
    rw [hW]
    exact Nat.size_le.mpr hi_lt
  have hK_n : K ≤ n := by
    have h1 : (C0 + 8) * (Lg + 1) ≤ n := by
      have h2 := hN2 n hnN2
      simpa [pow_one] using h2
    have h2 : (C0 + 7) * (Lg + 1) ≤ (C0 + 8) * (Lg + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- A string of length `n` denotes a number below `2 ^ n`. -/
lemma bitsToNat_lt_two_pow (s : BitString) : bitsToNat s < 2 ^ s.length := by
  induction s with
  | nil => dsimp [bitsToNat]; decide
  | cons b t ih =>
    cases b
    · change 2 * bitsToNat t < 2 ^ (t.length + 1)
      have h_pow : 2 ^ (t.length + 1) = 2 * 2 ^ t.length := by ring
      rw [h_pow]
      omega
    · change 2 * bitsToNat t + 1 < 2 ^ (t.length + 1)
      have h_pow : 2 ^ (t.length + 1) = 2 * 2 ^ t.length := by ring
      rw [h_pow]
      omega

end Kolmogorov
