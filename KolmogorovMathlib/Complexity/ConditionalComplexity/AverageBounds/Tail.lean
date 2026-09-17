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
import KolmogorovMathlib.Complexity.RandomConditions.Bound

/-!
# Few conditions make a string much simpler

`fraction_condK_lt_condK_length_le` (SUV Exercise 42, tail bound): among the `n`-bit
conditions `y`, only a small fraction satisfy `C(x | y) < C(x | n) - s`.

A string that is simple given many conditions is *heavy*; the heavy strings can be enumerated
(`heavyEnum`, primitive recursive by `heavyEnum_primrec` through `isHeavyAt_primrec`), so a
heavy string is described by its index in that enumeration.  `heavyDecoder` is the
decompressor that reads such a description — its program carries the bound `s`, the index `i`
and, through its length, the complexity bound `t`, read back by `heavyS`, `heavyI` and
`heavyT` — and `heavyDecoder_isDecompressor` makes it a conditional decompressor.  The
counting of heavy strings then gives the tail bound.  `condK_ne_top_of_opt` and
`condK_eq_condCVal` are the finiteness facts used throughout.
-/



namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-- Heaviness at a stage is a primitive recursive predicate of all its parameters. -/
lemma isHeavyAt_primrec (c : Code) :
    Primrec (fun q : ((ℕ × ℕ) × ℕ × ℕ) × BitString =>
      isHeavyAt c q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2) := by
  unfold isHeavyAt
  have hpow : Primrec (fun q : ((ℕ × ℕ) × ℕ × ℕ) × BitString => 2 ^ q.1.1.1) :=
    primrec_two_pow_aux.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hpow2 : Primrec (fun q : ((ℕ × ℕ) × ℕ × ℕ) × BitString => 2 ^ q.1.2.1) :=
    primrec_two_pow_aux.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hcount : Primrec (fun q : ((ℕ × ℕ) × ℕ × ℕ) × BitString =>
      countY c q.1.1.1 q.1.1.2 q.1.2.2 q.2) :=
    (countY_primrec c).comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      Primrec.snd)
  exact primrec_decide_of_primrecPred
    (Primrec.nat_le.comp hpow (Primrec.nat_mul.comp hcount hpow2))

/-- The enumeration of heavy strings, written as a primitive recursion on the stage, the form in
which it is transported to a primitive recursive function. -/
lemma heavyEnum_eq_rec (c : Code) (n t s T : ℕ) :
    heavyStringsEnum c n t s T =
      Nat.rec (motive := fun _ => List BitString) []
        (fun T prev => prev ++ (candStage c n t (T + 1)).filter
          (fun x => isHeavyAt c n t s (T + 1) x && !(decide (x ∈ prev)))) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    conv_lhs => rw [heavyStringsEnum]
    rw [ih]

/-- The enumeration of heavy strings is primitive recursive in its parameters and the stage. -/
lemma heavyEnum_primrec (c : Code) :
    Primrec (fun q : (ℕ × ℕ × ℕ) × ℕ => heavyStringsEnum c q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hheavy : Primrec (fun z : ((ℕ × ℕ × ℕ) × ℕ × List BitString) × BitString =>
      isHeavyAt c z.1.1.1 z.1.1.2.1 z.1.1.2.2 (z.1.2.1 + 1) z.2) :=
    (isHeavyAt_primrec c).comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))))
      Primrec.snd)
  have hnotmem : Primrec (fun z : ((ℕ × ℕ × ℕ) × ℕ × List BitString) × BitString =>
      !(decide (z.2 ∈ z.1.2.2))) :=
    Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hpred : Primrec₂ (fun (a : (ℕ × ℕ × ℕ) × ℕ × List BitString) (x : BitString) =>
      isHeavyAt c a.1.1 a.1.2.1 a.1.2.2 (a.2.1 + 1) x && !(decide (x ∈ a.2.2))) :=
    Primrec.and.comp hheavy hnotmem
  have hcand : Primrec (fun a : (ℕ × ℕ × ℕ) × ℕ × List BitString =>
      candStage c a.1.1 a.1.2.1 (a.2.1 + 1)) :=
    (candStage_primrec c).comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  have hstep1 : Primrec₂ (fun (a : ℕ × ℕ × ℕ) (q : ℕ × List BitString) =>
      q.2 ++ (candStage c a.1 a.2.1 (q.1 + 1)).filter
        (fun x => isHeavyAt c a.1 a.2.1 a.2.2 (q.1 + 1) x && !(decide (x ∈ q.2)))) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (list_filter_primrec hcand hpred)
  have hstep : Primrec₂ (fun (a : ℕ × ℕ × ℕ) (q : ℕ × List BitString) =>
      q.2 ++ (candStage c a.1 a.2.1 (q.1 + 1)).filter
        (fun x => isHeavyAt c a.1 a.2.1 a.2.2 (q.1 + 1) x && !(decide (x ∈ q.2)))) :=
    Primrec₂.of_eq hstep1 (fun a q => rfl)
  have h1 := Primrec.nat_rec (f := fun _ : ℕ × ℕ × ℕ => ([] : List BitString))
    (Primrec.const []) hstep
  have h : Primrec₂ (fun (a : ℕ × ℕ × ℕ) (T : ℕ) => heavyStringsEnum c a.1 a.2.1 a.2.2 T) :=
    Primrec₂.of_eq h1 (fun a T => (heavyEnum_eq_rec c a.1 a.2.1 a.2.2 T).symm)
  exact h

/-! ### The decompressor that reads off the enumeration -/

/-- The bound `s` encoded in the first component of a program. -/
def heavyS (p : BitString) : ℕ := bitsToNat (decodeFirst p)

/-- The index `i` encoded in the second component of a program. -/
def heavyI (p : BitString) : ℕ := decodeFixedWidthNatCode (decodeSecond p)

/-- The complexity bound `t` recovered from the length of the second component. -/
def heavyT (p : BitString) : ℕ := (decodeSecond p).length - bitsToNat (decodeFirst p) - 1

/-- Decompressor for Exercise 42: from the condition `Nat.bits n` and the program
`pairCode (Nat.bits s) (fixedWidthNatCode i (t + s + 1))` it enumerates the strings that
have at least `2 ^ n / 2 ^ s` conditions of length `n` producing them by a program of
length at most `t`, and returns the `i`-th one. -/
def heavyDecoder (c : Code) : Map := fun pr =>
  (Nat.rfind (show ℕ →. Bool from fun T => Part.some (decide (heavyI pr.1 <
      (heavyStringsEnum c (bitsToNat pr.2) (heavyT pr.1) (heavyS pr.1) T).length)))).map
    (fun T =>
      (heavyStringsEnum c (bitsToNat pr.2) (heavyT pr.1) (heavyS pr.1) T).getD (heavyI pr.1) [])

/-- Reading the bound `s` off a program is primitive recursive. -/
lemma heavyS_primrec : Primrec heavyS :=
  bitsToNat_primrec.comp decodeFirst_primrec

/-- Reading the index `i` off a program is primitive recursive. -/
lemma heavyI_primrec : Primrec heavyI :=
  (bitsToNat_primrec.comp Primrec.list_reverse).comp decodeSecond_primrec

/-- Recovering the complexity bound `t` from a program is primitive recursive. -/
lemma heavyT_primrec : Primrec heavyT :=
  Primrec.nat_sub.comp
    (Primrec.nat_sub.comp (Primrec.list_length.comp decodeSecond_primrec)
      (bitsToNat_primrec.comp decodeFirst_primrec))
    (Primrec.const 1)

/-- The decompressor reading a heavy string off the enumeration is a conditional decompressor. -/
lemma heavyDecoder_isDecompressor (c : Code) : isDecompressor (heavyDecoder c) := by
  have hlist : Primrec (fun q : (BitString × BitString) × ℕ =>
      heavyStringsEnum c (bitsToNat q.1.2) (heavyT q.1.1) (heavyS q.1.1) q.2) :=
    (heavyEnum_primrec c).comp (Primrec.pair
      (Primrec.pair (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (heavyT_primrec.comp (Primrec.fst.comp Primrec.fst))
          (heavyS_primrec.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)
  have hidx : Primrec (fun q : (BitString × BitString) × ℕ => heavyI q.1.1) :=
    heavyI_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hcheck : Computable₂ (fun (pr : BitString × BitString) (T : ℕ) =>
      decide (heavyI pr.1 <
        (heavyStringsEnum c (bitsToNat pr.2) (heavyT pr.1) (heavyS pr.1) T).length)) :=
    (primrec_decide_of_primrecPred
      (Primrec.nat_lt.comp hidx (Primrec.list_length.comp hlist))).to_comp
  have hval : Computable₂ (fun (pr : BitString × BitString) (T : ℕ) =>
      (heavyStringsEnum c (bitsToNat pr.2) (heavyT pr.1) (heavyS pr.1) T).getD (heavyI pr.1) []) :=
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp hlist hidx)
      (Primrec.const [])).to_comp
  exact Partrec.map (Partrec.rfind hcheck.partrec₂) hval

/-- On the program `pairCode (bits s) (fixedWidthNatCode i (t + s + 1))` with condition `n`, the
decompressor outputs the `i`-th heavy string of the enumeration. -/
lemma heavyDecoder_produces (c : Code) (n t s i T0 : ℕ)
    (hi : i < 2 ^ (t + s + 1))
    (hlt : i < (heavyStringsEnum c n t s T0).length) :
    produces (heavyDecoder c) (pairCode (Nat.bits s) (fixedWidthNatCode i (t + s + 1)))
      (Nat.bits n) ((heavyStringsEnum c n t s T0).getD i []) := by
  have hS : heavyS (pairCode (Nat.bits s) (fixedWidthNatCode i (t + s + 1))) = s := by
    unfold heavyS
    rw [decodeFirst_pairCode, bitsToNat_bits]
  have hI : heavyI (pairCode (Nat.bits s) (fixedWidthNatCode i (t + s + 1))) = i := by
    unfold heavyI
    rw [decodeSecond_pairCode, decodeFixedWidthNatCode_encode]
  have hT : heavyT (pairCode (Nat.bits s) (fixedWidthNatCode i (t + s + 1))) = t := by
    unfold heavyT
    rw [decodeSecond_pairCode, decodeFirst_pairCode, bitsToNat_bits,
      fixedWidthNatCode_length hi]
    omega
  change _ ∈ heavyDecoder c _
  unfold heavyDecoder
  simp only [hS, hI, hT, bitsToNat_bits]
  have hdom : (Nat.rfind (show ℕ →. Bool from fun T =>
      Part.some (decide (i < (heavyStringsEnum c n t s T).length)))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨T0, Part.mem_some_iff.mpr (decide_eq_true hlt).symm, fun _ => Part.some_dom _⟩
  obtain ⟨T1, hT1⟩ := Part.dom_iff_mem.mp hdom
  have hT1eq : Nat.rfind (show ℕ →. Bool from fun T =>
        Part.some (decide (i < (heavyStringsEnum c n t s T).length))) = Part.some T1 :=
      Part.eq_some_iff.mpr hT1
  rw [hT1eq, Part.map_some, Part.mem_some_iff]
  have hT1lt : i < (heavyStringsEnum c n t s T1).length := by
    have := Nat.rfind_spec hT1
    simpa using this
  rcases le_total T1 T0 with hle | hle
  · exact getD_eq_of_prefix_of_lt_length (heavyEnum_prefix_of_le c n t s hle) i [] hT1lt
  · exact (getD_eq_of_prefix_of_lt_length (heavyEnum_prefix_of_le c n t s hle) i [] hlt).symm

/-! ### From complexity to the enumeration -/

open Classical in
/-- The number of length-`n` conditions from which `x` has a program of length at most
`t`. -/
noncomputable def lowCount (U : Map) (n t : ℕ) (x : BitString) : ℕ :=
  (allStrings n).countP (fun y => decide (condK U x y ≤ (t : ℕ∞)))

/-- For a finite list of conditions there is one stage at which every condition of complexity at
most `t` has already produced `x`. -/
lemma exists_stage_hit {U : Map} {c : Code} (hc : IsCodeFor c U) (t : ℕ) (x : BitString)
    (M : List BitString) :
    ∃ T, ∀ y ∈ M, condK U x y ≤ (t : ℕ∞) → hitAt c t T x y = true := by
  induction M with
  | nil => exact ⟨0, fun y hy => absurd hy (List.not_mem_nil)⟩
  | cons y M ih =>
    obtain ⟨T, hT⟩ := ih
    by_cases hy : condK U x y ≤ (t : ℕ∞)
    · obtain ⟨p, hplen, hprod⟩ := (condK_le_iff U x y t).mp hy
      obtain ⟨Ty, hTy⟩ := runOutC_complete hc hprod
      refine ⟨max T Ty, fun z hz hzc => ?_⟩
      rcases List.mem_cons.mp hz with heq | hzM
      · subst heq
        refine (hitAt_iff _ _ _ _ _).mpr ⟨p, ?_, ?_⟩
        · exact (mem_boundedPrograms_iff p t).mpr hplen
        · exact runOutC_mono c (le_max_right T Ty) hTy
      · exact hitAt_mono c t (le_max_left T Ty) x z (hT z hzM hzc)
    · refine ⟨T, fun z hz hzc => ?_⟩
      rcases List.mem_cons.mp hz with heq | hzM
      · subst heq
        exact absurd hzc hy
      · exact hT z hzM hzc

/-- A string with at least `2 ^ n / 2 ^ s` cheap conditions eventually appears in the
enumeration of heavy strings. -/
lemma exists_mem_heavyEnum {U : Map} {c : Code} (hc : IsCodeFor c U) (n t s : ℕ)
    (x : BitString) (hheavy : 2 ^ n ≤ lowCount U n t x * 2 ^ s) :
    ∃ T, x ∈ heavyStringsEnum c n t s T := by
  classical
  obtain ⟨T, hT⟩ := exists_stage_hit hc t x (allStrings n)
  have hmono : lowCount U n t x ≤ countY c n t T x := by
    refine List.countP_mono_left ?_
    intro y hy hyc
    exact hT y hy (of_decide_eq_true hyc)
  have hheavyT : isHeavyAt c n t s T x = true := by
    unfold isHeavyAt
    refine decide_eq_true ?_
    exact hheavy.trans (Nat.mul_le_mul_right _ hmono)
  have hpos : 0 < lowCount U n t x := by
    rcases Nat.eq_zero_or_pos (lowCount U n t x) with h0 | hpos
    · rw [h0, zero_mul] at hheavy
      exact absurd (Nat.le_zero.mp hheavy) (Nat.two_pow_pos n).ne'
    · exact hpos
  obtain ⟨y, hymem, hyc⟩ := List.countP_pos_iff.mp hpos
  obtain ⟨p, hp, hrun⟩ := (hitAt_iff c t T x y).mp (hT y hymem (of_decide_eq_true hyc))
  have hcand : x ∈ candStage c n t T :=
    (mem_candStage_iff c n t T x).mpr ⟨y, hymem, p, hp, hrun⟩
  exact ⟨T, mem_heavyEnum_of_cand c n t s T hcand hheavyT⟩

/-! ### The complexity bound for heavy strings -/

/-- A string with at least `2 ^ n / 2 ^ s` conditions of length `n` describing it in `t` bits
satisfies `C(x | n) ≤ t + s + 2 log s + O(1)`.  SUV Exercise 42. -/
lemma heavy_condK_bound {U : Map} (hU : isOptimalConditional U) :
    ∃ C0 : ℕ, ∀ (n t s : ℕ) (x : BitString),
      2 ^ n ≤ lowCount U n t x * 2 ^ s →
      condK U x (Nat.bits n) ≤ ((2 * (Nat.bits s).length + 1 + (t + s + 1) + C0 : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := Dovetailing.exists_isCodeFor hU
  obtain ⟨C0, hC0⟩ := hU.2 (heavyDecoder c) (heavyDecoder_isDecompressor c)
  refine ⟨C0, fun n t s x hheavy => ?_⟩
  obtain ⟨T, hT⟩ := exists_mem_heavyEnum hc n t s x hheavy
  set i := List.idxOf x (heavyStringsEnum c n t s T) with hi
  have hilt : i < (heavyStringsEnum c n t s T).length := List.idxOf_lt_length_of_mem hT
  have hgetD : (heavyStringsEnum c n t s T).getD i [] = x := by
    rw [List.getD_eq_getElem?_getD, hi, List.getElem?_idxOf hT]
    rfl
  have hiw : i < 2 ^ (t + s + 1) := lt_of_lt_of_le hilt (heavyEnum_length_le c n t s T)
  have hprod := heavyDecoder_produces c n t s i T hiw hilt
  rw [hgetD] at hprod
  have hlen : (pairCode (Nat.bits s) (fixedWidthNatCode i (t + s + 1))).length
      = 2 * (Nat.bits s).length + 1 + (t + s + 1) := by
    rw [length_pairCode, fixedWidthNatCode_length hiw]
    ring
  have hdec : condK (heavyDecoder c) x (Nat.bits n)
      ≤ ((2 * (Nat.bits s).length + 1 + (t + s + 1) : ℕ) : ℕ∞) := by
    have := condK_le_of_produces hprod
    rwa [hlen] at this
  calc condK U x (Nat.bits n) ≤ condK (heavyDecoder c) x (Nat.bits n) + (C0 : ℕ∞) :=
        hC0 x (Nat.bits n)
    _ ≤ ((2 * (Nat.bits s).length + 1 + (t + s + 1) : ℕ) : ℕ∞) + (C0 : ℕ∞) := by gcongr
    _ = ((2 * (Nat.bits s).length + 1 + (t + s + 1) + C0 : ℕ) : ℕ∞) := by push_cast; ring

/-! ### Finiteness of conditional complexity -/

/-- For an optimal conditional decompressor every conditional complexity is finite. -/
lemma condK_ne_top_of_opt {U : Map} (hU : isOptimalConditional U) (x y : BitString) :
    condK U x y ≠ ⊤ := by
  obtain ⟨cid, hcid⟩ := hU.2 (fun pr => Part.some pr.1) (Computable.fst.partrec)
  have hle : condK U x y ≤ ((x.length + cid : ℕ) : ℕ∞) := by
    have h1 : condK (fun pr : BitString × BitString => Part.some pr.1) x y
        ≤ ((x.length : ℕ) : ℕ∞) := condK_le_of_produces (Part.mem_some x)
    calc condK U x y ≤ condK (fun pr : BitString × BitString => Part.some pr.1) x y + (cid : ℕ∞) :=
          hcid x y
      _ ≤ ((x.length : ℕ) : ℕ∞) + (cid : ℕ∞) := by gcongr
      _ = ((x.length + cid : ℕ) : ℕ∞) := by push_cast; ring
  intro htop
  rw [htop] at hle
  exact absurd (top_le_iff.mp hle) (ENat.natCast_ne_top _)

/-- For an optimal conditional decompressor the `ℕ∞`-valued conditional complexity agrees with
its `ℕ`-valued shadow `condCVal`. -/
lemma condK_eq_condCVal {U : Map} (hU : isOptimalConditional U) (x y : BitString) :
    condK U x y = ((condCVal U x y : ℕ) : ℕ∞) := by
  unfold condCVal
  exact (ENat.natCast_toNat (condK_ne_top_of_opt hU x y)).symm

/-! ### The tail bound -/

/-- For `s ≥ 1` the least power of two above `s` is at most `2 s`. -/
lemma two_pow_size_le (s : ℕ) (hs : 1 ≤ s) : 2 ^ (Nat.size s) ≤ 2 * s := by
  have h1 : 0 < Nat.size s := by
    rcases Nat.eq_zero_or_pos (Nat.size s) with h | h
    · exfalso
      have := Nat.lt_size_self s
      rw [h] at this
      omega
    · exact h
  have h2 : 2 ^ (Nat.size s - 1) ≤ s := Nat.lt_size.mp (by omega)
  have h3 : 2 ^ (Nat.size s) = 2 * 2 ^ (Nat.size s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- **Exercise 42, tail bound.** The fraction of `n`-bit `y` with
`C(x | y) < C(x | n) - d` is at most `c d² / 2 ^ d`. -/
theorem fraction_condK_lt_condK_length_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n d : ℕ), d > 0 →
      ((((allStrings n).filter
          (fun y => decide (condCVal U x y + d < condCVal U x (Nat.bits n)))).length : ℝ))
        ≤ (c : ℝ) * (d : ℝ) ^ 2 / (2 : ℝ) ^ d * (2 : ℝ) ^ n := by
  classical
  obtain ⟨C0, hC0⟩ := heavy_condK_bound hU
  refine ⟨2 ^ (C0 + 5), fun x n d hd => ?_⟩
  set F := ((allStrings n).filter
    (fun y => decide (condCVal U x y + d < condCVal U x (Nat.bits n)))).length with hF
  have hFle : F ≤ 2 ^ n := by
    rw [hF]
    calc ((allStrings n).filter _).length ≤ (allStrings n).length := List.length_filter_le _ _
      _ = 2 ^ n := length_allStrings n
  have hnat : F * 2 ^ d ≤ 2 ^ (C0 + 5) * d ^ 2 * 2 ^ n := by
    rcases Nat.eq_zero_or_pos F with hF0 | hFpos
    · rw [hF0]
      simp
    -- there is a witness in the filter
    have hex : ∃ y ∈ allStrings n, condCVal U x y + d < condCVal U x (Nat.bits n) := by
      have : 0 < ((allStrings n).filter
          (fun y => decide (condCVal U x y + d < condCVal U x (Nat.bits n)))).length := by
        rw [← hF]; exact hFpos
      rw [← List.countP_eq_length_filter] at this
      obtain ⟨y, hy, hyc⟩ := List.countP_pos_iff.mp this
      exact ⟨y, hy, of_decide_eq_true hyc⟩
    obtain ⟨y0, -, hy0⟩ := hex
    set m := condCVal U x (Nat.bits n) with hm
    have hmd : d < m := by omega
    set t := m - d - 1 with ht
    -- the filtered strings all have a program of length at most `t`
    have hFlow : F ≤ lowCount U n t x := by
      rw [hF, ← List.countP_eq_length_filter]
      refine List.countP_mono_left ?_
      intro y _ hy
      have hy' : condCVal U x y + d < m := of_decide_eq_true hy
      refine decide_eq_true ?_
      rw [condK_eq_condCVal hU]
      exact_mod_cast (by omega : condCVal U x y ≤ t)
    -- the least `s` for which `x` is heavy
    have hexists : ∃ s : ℕ, 2 ^ n ≤ F * 2 ^ s := by
      refine ⟨n, ?_⟩
      calc 2 ^ n = 1 * 2 ^ n := (one_mul _).symm
        _ ≤ F * 2 ^ n := Nat.mul_le_mul_right _ hFpos
    set s := Nat.find hexists with hs
    have hsspec : 2 ^ n ≤ F * 2 ^ s := Nat.find_spec hexists
    have hheavy : 2 ^ n ≤ lowCount U n t x * 2 ^ s :=
      hsspec.trans (Nat.mul_le_mul_right _ hFlow)
    have hbound := hC0 n t s x hheavy
    rw [condK_eq_condCVal hU, ← hm] at hbound
    have hmle : m ≤ 2 * (Nat.bits s).length + 1 + (t + s + 1) + C0 := by exact_mod_cast hbound
    have hdle : d ≤ 2 * (Nat.bits s).length + s + 1 + C0 := by omega
    -- the two cases
    rcases lt_or_ge (F * 2 ^ d) (2 ^ n) with hcase | hcase
    · calc F * 2 ^ d ≤ 2 ^ n := hcase.le
        _ = 1 * 1 * 2 ^ n := by ring
        _ ≤ 2 ^ (C0 + 5) * d ^ 2 * 2 ^ n := by
            refine Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ ?_)
            · exact Nat.one_le_two_pow
            · nlinarith
    · have hsd : s ≤ d := Nat.find_le hcase
      rcases Nat.eq_zero_or_pos s with hs0 | hs1
      · -- `s = 0`: then `d ≤ C0 + 1`
        have hd1 : d ≤ 1 + C0 := by
          rw [hs0] at hdle
          simpa using hdle
        calc F * 2 ^ d ≤ 2 ^ n * 2 ^ (1 + C0) :=
              Nat.mul_le_mul hFle (Nat.pow_le_pow_right (by norm_num) hd1)
          _ ≤ 2 ^ (C0 + 5) * d ^ 2 * 2 ^ n := by
              have h1 : 2 ^ (1 + C0) ≤ 2 ^ (C0 + 5) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              have h2 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
              calc 2 ^ n * 2 ^ (1 + C0) ≤ 2 ^ n * 2 ^ (C0 + 5) := Nat.mul_le_mul_left _ h1
                _ = 2 ^ (C0 + 5) * 1 * 2 ^ n := by ring
                _ ≤ 2 ^ (C0 + 5) * d ^ 2 * 2 ^ n := by
                    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
      · -- `s ≥ 1`: minimality of `s` bounds `F * 2 ^ s`
        have hmin : ¬ (2 ^ n ≤ F * 2 ^ (s - 1)) := Nat.find_min hexists (by omega)
        have hlt : F * 2 ^ s < 2 ^ (n + 1) := by
          push Not at hmin
          have hstep : F * 2 ^ s = 2 * (F * 2 ^ (s - 1)) := by
            have : 2 ^ s = 2 * 2 ^ (s - 1) := by
              rw [← pow_succ']
              congr 1
              omega
            rw [this]
            ring
          rw [hstep, pow_succ]
          omega
        have hbs : 2 ^ ((Nat.bits s).length) ≤ 2 * s := by
          rw [Nat.size_eq_bits_len]
          exact two_pow_size_le s hs1
        have hpowd : 2 ^ d ≤ 2 ^ s * ((2 * s) * (2 * s)) * 2 ^ (1 + C0) := by
          have h1 : 2 ^ d ≤ 2 ^ (2 * (Nat.bits s).length + s + 1 + C0) :=
            Nat.pow_le_pow_right (by norm_num) hdle
          have h2 : 2 ^ (2 * (Nat.bits s).length + s + 1 + C0)
              = 2 ^ s * (2 ^ ((Nat.bits s).length) * 2 ^ ((Nat.bits s).length))
                * 2 ^ (1 + C0) := by
            rw [← pow_add, ← pow_add, ← pow_add]
            congr 1
            ring
          rw [h2] at h1
          refine h1.trans ?_
          exact Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul hbs hbs))
        calc F * 2 ^ d ≤ F * (2 ^ s * ((2 * s) * (2 * s)) * 2 ^ (1 + C0)) :=
              Nat.mul_le_mul_left _ hpowd
          _ = (F * 2 ^ s) * (((2 * s) * (2 * s)) * 2 ^ (1 + C0)) := by ring
          _ ≤ 2 ^ (n + 1) * (((2 * s) * (2 * s)) * 2 ^ (1 + C0)) :=
              Nat.mul_le_mul_right _ hlt.le
          _ = (2 ^ (C0 + 4) * (s * s)) * 2 ^ n := by
              rw [pow_succ, pow_add]
              ring
          _ ≤ (2 ^ (C0 + 5) * d ^ 2) * 2 ^ n := by
              refine Nat.mul_le_mul_right _ ?_
              have h1 : s * s ≤ d ^ 2 := by nlinarith
              have h2 : 2 ^ (C0 + 4) ≤ 2 ^ (C0 + 5) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
              exact Nat.mul_le_mul h2 h1
  have hreal : (F : ℝ) * (2 : ℝ) ^ d ≤ ((2 ^ (C0 + 5) : ℕ) : ℝ) * (d : ℝ) ^ 2 * (2 : ℝ) ^ n := by
    exact_mod_cast hnat
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact hreal

end Kolmogorov
