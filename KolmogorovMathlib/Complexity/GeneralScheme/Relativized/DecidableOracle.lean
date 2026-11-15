import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs
import KolmogorovMathlib.Complexity.GeneralScheme.Conditional
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Complexity.InfiniteSequences.PrefixComplexity
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold
import KolmogorovMathlib.Prefix.Kraft
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# Decidable Oracle

Plain complexity is computable in the halting problem `0'`
(`computableIn_haltingOracle_cVal`), and a decidable oracle does not change the complexities
of the general scheme: if the oracle `A` is decidable, relativizing to `A` leaves the plain,
monotone, decision and a priori complexities unchanged
(`isDecidableSet_of_plainK_eq_plainK_oracle`, `isDecidableSet_of_KMOf_eq_KMOf_oracle`,
`isDecidableSet_of_KROf_eq_KRInOf`, `isDecidableSet_of_KA_eq_KAOf`).

This formalizes the discussion of Section 6.4.1 of the book by Shen, Uspensky and
Vereshchagin ("Kolmogorov complexity and algorithmic randomness"), including Problem 205.
-/

open scoped ENNReal
namespace Kolmogorov
namespace GeneralScheme

open Encodable in
open Nat.Partrec (Code) in
/-- The decidable test of the `Σ⁰₁` predicate "some `p` of length at most `a.2` has
`U (p, []) = a.1`": the search index `k = ⟨s, ⌜p⌝⟩` codes a run time `s` and a program `p`, and
`c` is a code of `U`. -/
private def computableIn_haltingOracle_cVal_gTest (c : Code) (a : BitString × ℕ) (k : ℕ) :
    Bool :=
  Option.casesOn (decode (α := BitString) (Nat.unpair k).2) false fun p =>
    decide (p.length ≤ a.2) &&
      decide (Code.evaln (Nat.unpair k).1 c (encode (p, ([] : BitString))) =
        Option.some (encode a.1))

open Encodable in
open Nat.Partrec (Code) in
private theorem computableIn_haltingOracle_cVal_gTest_comp (c : Code) :
    Computable₂ (computableIn_haltingOracle_cVal_gTest c) := by
  have hm : Primrec fun q : (BitString × ℕ) × ℕ => decode (α := BitString) (Nat.unpair q.2).2 :=
    Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hl : Primrec fun q : ((BitString × ℕ) × ℕ) × BitString =>
      decide (q.2.length ≤ q.1.1.2) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have h1 : Primrec fun q : ((BitString × ℕ) × ℕ) × BitString => (Nat.unpair q.1.2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
  have h2 : Primrec fun q : ((BitString × ℕ) × ℕ) × BitString =>
      encode (q.2, ([] : BitString)) :=
    Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const []))
  have he : Primrec fun q : ((BitString × ℕ) × ℕ) × BitString =>
      Code.evaln (Nat.unpair q.1.2).1 c (encode (q.2, ([] : BitString))) :=
    Code.primrec_evaln.comp (Primrec.pair (Primrec.pair h1 (Primrec.const c)) h2)
  have hr : Primrec fun q : ((BitString × ℕ) × ℕ) × BitString =>
      decide (Code.evaln (Nat.unpair q.1.2).1 c (encode (q.2, ([] : BitString))) =
        Option.some (encode q.1.1.1)) :=
    PrimrecPred.decide (PrimrecRel.comp Primrec.eq he
      (Primrec.option_some.comp (Primrec.encode.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  have hb : Primrec₂ fun (q : (BitString × ℕ) × ℕ) (p : BitString) =>
      decide (p.length ≤ q.1.2) &&
      decide (Code.evaln (Nat.unpair q.2).1 c (encode (p, ([] : BitString))) =
        Option.some (encode q.1.1)) :=
    Primrec.and.comp hl hr
  refine Primrec.to_comp ?_
  exact Primrec.option_casesOn hm (Primrec.const false) hb

open Encodable in
open Nat.Partrec (Code) in
private theorem computableIn_haltingOracle_cVal_gTest_iff {U : Map} (c : Code)
    (hc : ∀ n, Code.eval c n = Part.bind (decode (α := BitString × BitString) n)
      fun a => (U a).map encode) (x : BitString) (n : ℕ) :
    (∃ k, computableIn_haltingOracle_cVal_gTest c (x, n) k = true) ↔
      ∃ p : BitString, p.length ≤ n ∧ x ∈ U (p, []) := by
  constructor
  · rintro ⟨k, hk⟩
    unfold computableIn_haltingOracle_cVal_gTest at hk
    cases hd : decode (α := BitString) (Nat.unpair k).2 with
    | none => simp [hd] at hk
    | some p =>
      simp only [hd, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨hlen, hev⟩ := hk
      refine ⟨p, hlen, ?_⟩
      have h1 := Code.evaln_sound (Option.mem_def.2 hev)
      rw [hc] at h1
      simp only [encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff] at h1
      obtain ⟨y, hy, hye⟩ := h1
      have : y = x := encode_injective hye
      simpa [this] using hy
  · rintro ⟨p, hlen, hp⟩
    have h1 : encode x ∈ Code.eval c (encode (p, ([] : BitString))) := by
      rw [hc]
      simp only [encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff]
      exact ⟨x, hp, rfl⟩
    obtain ⟨s, hs⟩ := Code.evaln_complete.1 h1
    refine ⟨Nat.pair s (encode p), ?_⟩
    have hd : decode (α := BitString) (Nat.unpair (Nat.pair s (encode p))).2 = some p := by
      simp [Nat.unpair_pair]
    simpa [computableIn_haltingOracle_cVal_gTest, hd, hlen] using Option.mem_def.1 hs

private theorem computableIn_haltingOracle_cVal_plainK_ne_top {U : Map}
    (hU : isOptimalConditional U) (x : BitString) : plainK U x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := hU.2 (fun q => Part.some q.1) (Computable.fst.partrec)
  have h1 : condK (fun q : BitString × BitString => Part.some q.1) x [] ≤ (x.length : ℕ∞) :=
    sInf_le ⟨x, by simp [produces], rfl⟩
  exact ne_top_of_le_natCast_add (n := x.length) (c := c)
    ((hc x []).trans (add_le_add_left h1 _))

private theorem computableIn_haltingOracle_cVal_exists_iff {U : Map}
    (hU : isOptimalConditional U) (x : BitString) (m : ℕ) :
    (∃ p : BitString, p.length ≤ m ∧ x ∈ U (p, [])) ↔ cVal U x ≤ m := by
  have hne := computableIn_haltingOracle_cVal_plainK_ne_top hU x
  constructor
  · rintro ⟨p, hlen, hp⟩
    have : plainK U x ≤ (m : ℕ∞) :=
      (sInf_le (show (p.length : ℕ∞) ∈ candidateLengths U x [] from ⟨p, hp, rfl⟩)).trans
        (by exact_mod_cast hlen)
    unfold cVal
    exact ENat.toNat_le_of_le_natCast this
  · intro h
    have hmem : plainK U x ∈ candidateLengths U x [] :=
      csInf_mem (s := candidateLengths U x []) (by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        exact hne (by simp [plainK, condK, hempty]))
    obtain ⟨p, hp, hlen⟩ := hmem
    refine ⟨p, ?_, hp⟩
    have : (p.length : ℕ∞) = ((plainK U x).toNat : ℕ∞) := by
      rw [hlen]; exact (ENat.natCast_toNat hne).symm
    have h2 : p.length = cVal U x := by exact_mod_cast this
    omega

open Encodable in
open Nat.Partrec (Code) in
/-- **SUV Section 6.4.1 (printed p. 203), unnumbered.** Plain complexity is `0'`-computable: with
the halting oracle one can find the shortest description of `x`. `cVal U x` is the
natural-number value of `C(x)`, which is finite for optimal `U`. -/
theorem computableIn_haltingOracle_cVal {U : Map} (hU : isOptimalConditional U) :
    ComputableIn {haltingOracle} (fun x : BitString => cVal U x) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hU.1
  have hc' : ∀ n, Code.eval c n = Part.bind (decode (α := BitString × BitString) n)
      fun a => (U a).map encode := fun n => by rw [hc]
  obtain ⟨h, hh, hspec⟩ := exists_computableInJump_semidecide
    (α := BitString × ℕ) (g := computableIn_haltingOracle_cVal_gTest c)
    (computableIn_haltingOracle_cVal_gTest_comp c)
  have hhalt : haltingChi = haltingOracle := by
    funext n
    simp only [haltingChi, haltingOracle, charOracle, haltingSet, Set.mem_ofPred_eq]
    congr
  have hh' : ComputableIn ({haltingOracle} : Set (ℕ →. ℕ)) h := by
    simpa [ComputableInJump, hhalt] using hh
  have h2 : PartrecIn₂ ({haltingOracle} : Set (ℕ →. ℕ))
      fun (x : BitString) (n : ℕ) => (Part.some (h (x, n)) : Part Bool) :=
    (ComputableIn₂.mk hh').partrecIn₂
  have h3 := PartrecIn.rfind h2
  refine PartrecIn.of_eq_tot h3 fun x => ?_
  refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
  · have : h (x, cVal U x) = true := by
      rw [hspec, computableIn_haltingOracle_cVal_gTest_iff c hc']
      exact (computableIn_haltingOracle_cVal_exists_iff hU x _).2 le_rfl
    simp [this]
  · have : h (x, m) = false := by
      by_contra hne
      have hne' : h (x, m) = true := by simpa using hne
      rw [hspec, computableIn_haltingOracle_cVal_gTest_iff c hc',
        computableIn_haltingOracle_cVal_exists_iff hU x] at hne'
      omega
    simp [this]

open Classical in
/-- The prefixes of the characteristic sequence of `A` are computable in the oracle `A`. -/
private theorem isDecidableSet_of_plainK_eq_plainK_oracle_aux_prefix (A : Set ℕ) :
    ComputableIn {charOracle A}
      (fun n : ℕ => seqPrefix (fun i => decide (i ∈ A)) n) := by
  classical
  have hchar : ComputableIn {charOracle A}
      (fun k : ℕ => if k ∈ A then 1 else 0) :=
    PartrecIn.oracle (charOracle A) (Set.mem_singleton _)
  have hbool : ComputableIn {charOracle A} (fun k : ℕ => decide (k ∈ A)) := by
    have h1 : Computable (fun m : ℕ => decide (m = 1)) :=
      (PrimrecPred.decide (Primrec.eq.comp Primrec.id (Primrec.const 1))).to_comp
    refine (h1.computableIn.comp hchar).of_eq fun k => ?_
    by_cases hk : k ∈ A <;> simp [hk]
  have happ : Computable (fun p : BitString × Bool => p.1 ++ [p.2]) :=
    Computable.list_append.comp Computable.fst
      (Computable.list_cons.comp Computable.snd (Computable.const []))
  have hpstep : ComputableIn₂ {charOracle A}
      (fun (_ : ℕ) (p : ℕ × BitString) => p.2 ++ [decide (p.1 ∈ A)]) :=
    (happ.computableIn.comp
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (hbool.comp (ComputableIn.fst.comp ComputableIn.snd)))).to₂
  refine (ComputableIn.nat_rec ComputableIn.id
    (ComputableIn.const ([] : BitString)) hpstep).of_eq ?_
  intro u
  change Nat.rec (motive := fun _ => BitString) []
    (fun k acc => acc ++ [decide (k ∈ A)]) u = _
  induction u with
  | zero => rfl
  | succ u ih =>
    simpa only [seqPrefix, List.range_succ, List.map_append, List.map_singleton] using
      congrArg (fun l : BitString => l ++ [decide (u ∈ A)]) ih

open Classical in
/-- The `A`-decompressor sending the binary numeral `Nat.bits n` to the length-`n` prefix of the
characteristic sequence of `A`. -/
private theorem isDecidableSet_of_plainK_eq_plainK_oracle_aux_decomp (A : Set ℕ) :
    IsDecompressorIn (charOracle A)
      (fun pr : BitString × BitString =>
        Part.some (seqPrefix (fun i => decide (i ∈ A)) (bitsToNat pr.1))) := by
  refine (PointToSet.isDecompressorIn_iff_partrecIn _ _).2 ?_
  have h1 : ComputableIn {charOracle A}
      (fun pr : BitString × BitString => bitsToNat pr.1) :=
    (bitsToNat_primrec.comp Primrec.fst).to_comp.computableIn
  exact (isDecidableSet_of_plainK_eq_plainK_oracle_aux_prefix A).comp h1

open Classical in
/-- `A`-plain complexity of the length-`n` prefix of `χ_A` is at most `log n + c`. -/
private theorem isDecidableSet_of_plainK_eq_plainK_oracle_aux_bound (A : Set ℕ) {V : Map}
    (hV : IsOptimalConditionalIn (charOracle A) V) :
    ∃ c : ℕ, ∀ n : ℕ,
      plainK V (seqPrefix (fun i => decide (i ∈ A)) n) ≤ ((Nat.log 2 n + c : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := hV.2 _ (isDecidableSet_of_plainK_eq_plainK_oracle_aux_decomp A)
  refine ⟨c + 1, fun n => ?_⟩
  have h1 : condK (fun pr : BitString × BitString =>
        Part.some (seqPrefix (fun i => decide (i ∈ A)) (bitsToNat pr.1)))
      (seqPrefix (fun i => decide (i ∈ A)) n) [] ≤ ((Nat.bits n).length : ℕ∞) :=
    sInf_le ⟨Nat.bits n, by simp [produces, bitsToNat_bits], rfl⟩
  have h2 : (Nat.bits n).length ≤ Nat.log 2 n + 1 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)
  calc plainK V (seqPrefix (fun i => decide (i ∈ A)) n)
      ≤ _ := hc _ []
    _ ≤ ((Nat.bits n).length : ℕ∞) + c := by gcongr
    _ ≤ ((Nat.log 2 n + 1 : ℕ) : ℕ∞) + c := by gcongr
    _ = ((Nat.log 2 n + (c + 1) : ℕ) : ℕ∞) := by push_cast; ring

/-- **SUV Problem 205 (Section 6.4.1, printed p. 203), plain complexity.** If the oracle `A` does
not change plain complexity, `C(x) = C^A(x) + O(1)`, then `A` is decidable.

Proof idea (book's hint): the characteristic sequence `χ` of `A` satisfies
`C^A(χ₀ … χₙ₋₁) ≤ C^A(n) + O(1) ≤ log n + O(1)`, so `C(χ₀ … χₙ₋₁) ≤ log n + O(1)`, and `χ` is
computable by Problem 49 (`computable_of_plainK_prefix_le_log`). -/
theorem isDecidableSet_of_plainK_eq_plainK_oracle (A : Set ℕ) {U : Map}
    (hU : isOptimalConditional U) {V : Map} (hV : IsOptimalConditionalIn (charOracle A) V)
    (h : ∃ c : ℕ, ∀ x, plainK U x ≤ plainK V x + c ∧ plainK V x ≤ plainK U x + c) :
    IsDecidableSet A := by
  classical
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := isDecidableSet_of_plainK_eq_plainK_oracle_aux_bound A hV
  have hcomp : Computable (fun i : ℕ => decide (i ∈ A)) := by
    refine computable_of_plainK_prefix_le_log U hU _ (c' + c) fun n => ?_
    calc plainK U (seqPrefix (fun i => decide (i ∈ A)) n)
        ≤ plainK V (seqPrefix (fun i => decide (i ∈ A)) n) + c := (hc _).1
      _ ≤ ((Nat.log 2 n + c' : ℕ) : ℕ∞) + c := by gcongr; exact hc' n
      _ = ((Nat.log 2 n + (c' + c) : ℕ) : ℕ∞) := by push_cast; ring
  exact ⟨fun i => decide (i ∈ A), hcomp, fun a => by simp⟩

open Classical in
private theorem isDecidableSet_of_KMOf_eq_KMOf_oracle_charSeq_computableIn (A : Set ℕ) :
    ComputableIn {charOracle A} (charSeq A) := by
  have h1 : ComputableIn {charOracle A} (fun n : ℕ => if n ∈ A then (1 : ℕ) else 0) :=
    PartrecIn.of_eq_tot (PartrecIn.oracle (charOracle A) (Set.mem_singleton _)) fun n => by
      simp [charOracle]
  have h2 : ComputableIn {charOracle A}
      (fun n : ℕ => decide ((if n ∈ A then (1 : ℕ) else 0) = 1)) :=
    (Primrec.eq.decide.to_comp.computableIn).comp (h1.pair (ComputableIn.const 1))
  refine h2.of_eq fun n => ?_
  by_cases hn : n ∈ A <;> simp [charSeq, hn]

private theorem isDecidableSet_of_KMOf_eq_KMOf_oracle_cantorPrefix_computableIn
    {O : Set (ℕ →. ℕ)} (w : CantorSeq) (hw : ComputableIn O w) :
    ComputableIn O (cantorPrefix w) := by
  have hstep : ComputableIn O (fun p : ℕ × (ℕ × BitString) => p.2.2 ++ [w p.2.1]) :=
    (Computable.list_concat.computableIn).comp
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (hw.comp (ComputableIn.fst.comp ComputableIn.snd)))
  have hrec := ComputableIn.nat_rec (O := O) (f := @id ℕ) (g := fun _ => ([] : BitString))
    (h := fun _ (k, ih) => ih ++ [w k]) ComputableIn.id (ComputableIn.const []) hstep.to₂
  refine hrec.of_eq fun n => ?_
  change Nat.rec ([] : BitString) (fun k ih => ih ++ [w k]) n = cantorPrefix w n
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.rec ([] : BitString) (fun k ih => ih ++ [w k]) n ++ [w n] =
        cantorPrefix w (n + 1)
      rw [ih, cantorPrefix_succ]

private theorem isDecidableSet_of_KMOf_eq_KMOf_oracle_constStreamMap (A : Set ℕ) :
    IsComputableStreamMapIn A (constStreamMap (charSeq A)) := by
  refine ⟨constStreamMap_isContinuous _, ?_⟩
  have hp := isDecidableSet_of_KMOf_eq_KMOf_oracle_cantorPrefix_computableIn (O := {charOracle A})
    _ (isDecidableSet_of_KMOf_eq_KMOf_oracle_charSeq_computableIn A)
  have H : ComputableIn {charOracle A} (fun p : BitString × BitString =>
      decide (cantorPrefix (charSeq A) p.2.length = p.2)) :=
    (Primrec.eq.decide.to_comp.computableIn).comp
      ((hp.comp (Primrec.list_length.comp Primrec.snd).to_comp.computableIn).pair
        ComputableIn.snd)
  have := PointToSet.isREIn_of_computableIn_decide A
    (fun p : BitString × BitString => cantorPrefix (charSeq A) p.2.length = p.2) H
  have hfun : (fun p : BitString × BitString =>
      streamLowerGraph (constStreamMap (charSeq A)) p.1 p.2) =
      fun p : BitString × BitString => cantorPrefix (charSeq A) p.2.length = p.2 := by
    funext p
    apply propext
    dsimp [streamLowerGraph, constStreamMap]
    have H_le : BitStream.finite p.2 ≤ BitStream.infinite (charSeq A) ↔
        IsCantorPrefix p.2 (charSeq A) := Iff.rfl
    rw [H_le, isCantorPrefix_iff_cantorPrefix_eq]
  rw [hfun]
  exact this

/-- **SUV Problem 205 (Section 6.4.1, printed p. 203), monotone complexity.** If
`KM(x) = KM^A(x) + O(1)`, then `A` is decidable.

Proof idea: `KM^A` is bounded on the prefixes of the `A`-computable characteristic sequence, so
`KM` is too, and Theorem 85 (`computable_iff_KMOf_prefixes_bounded`) applies. -/
theorem isDecidableSet_of_KMOf_eq_KMOf_oracle (A : Set ℕ) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {E : BitStream → BitStream}
    (hE : IsOptimalMonotoneDecompressorIn A E)
    (h : ∃ c : ℕ, ∀ x, KMOf D x ≤ KMOf E x + c ∧ KMOf E x ≤ KMOf D x + c) :
    IsDecidableSet A := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := hE.2 _ (isDecidableSet_of_KMOf_eq_KMOf_oracle_constStreamMap A)
  have hw : Computable (charSeq A) := by
    rw [computable_iff_KMOf_prefixes_bounded hD]
    refine ⟨c + c', fun n => ?_⟩
    have h1 := (hc (cantorPrefix (charSeq A) n)).1
    have h2 := hc' (cantorPrefix (charSeq A) n)
    rw [KMOf_constStreamMap_zero, zero_add] at h2
    calc KMOf D (cantorPrefix (charSeq A) n)
        ≤ KMOf E (cantorPrefix (charSeq A) n) + c := h1
      _ ≤ (c' : ℕ∞) + c := by gcongr
      _ = ((c + c' : ℕ) : ℕ∞) := by push_cast; ring
  refine ⟨charSeq A, hw, fun a => ?_⟩
  simp [charSeq]

/-- The `A`-decision decompressor that ignores its input and prints the characteristic sequence
of `A`. -/
private noncomputable def isDecidableSet_of_KROf_eq_KRInOf_charSeqMachine (A : Set ℕ) :
    DecisionDecompressorIn A where
  rel _ x := IsCantorPrefix x (charSeq A)
  re := by
    classical
    have hchar : ComputableIn {charOracle A} (fun k : ℕ => if k ∈ A then 1 else 0) :=
      PartrecIn.oracle (charOracle A) (Set.mem_singleton _)
    have hbit : ComputableIn {charOracle A} (fun k : ℕ => charSeq A k) := by
      have hb : Computable (fun m : ℕ => m == 1) :=
        (Primrec.beq.comp Primrec.id (Primrec.const 1)).to_comp
      refine (hb.computableIn.comp hchar).of_eq fun k => ?_
      by_cases hk : k ∈ A <;> simp [charSeq, hk]
    have happ : Computable (fun p : BitString × Bool => p.1 ++ [p.2]) :=
      Computable.list_append.comp Computable.fst
        (Computable.list_cons.comp Computable.snd (Computable.const []))
    have hpstep : ComputableIn₂ {charOracle A}
        (fun (_ : ℕ) (p : ℕ × BitString) => p.2 ++ [charSeq A p.1]) :=
      (happ.computableIn.comp
        ((ComputableIn.snd.comp ComputableIn.snd).pair
          (hbit.comp (ComputableIn.fst.comp ComputableIn.snd)))).to₂
    have hprefix : ComputableIn {charOracle A} (cantorPrefix (charSeq A)) := by
      refine (ComputableIn.nat_rec ComputableIn.id
        (ComputableIn.const ([] : BitString)) hpstep).of_eq ?_
      intro n
      change Nat.rec (motive := fun _ => BitString) []
        (fun k acc => acc ++ [charSeq A k]) n = _
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => BitString) []
          (fun k acc => acc ++ [charSeq A k]) n ++ [charSeq A n] = _
        rw [ih, cantorPrefix_succ]
    have hlen : Computable (fun p : BitString × BitString => p.2.length) :=
      Primrec.to_comp (Primrec.list_length.comp Primrec.snd)
    have H : ComputableIn {charOracle A}
        (fun p : BitString × BitString => cantorPrefix (charSeq A) p.2.length) :=
      hprefix.comp hlen.computableIn
    have H2 : ComputableIn {charOracle A}
        (fun p : BitString × BitString =>
          decide (cantorPrefix (charSeq A) p.2.length = p.2)) :=
      (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).computableIn.comp
        (H.pair Computable.snd.computableIn)
    have H3 : ComputableIn {charOracle A}
        (fun p : BitString × BitString => decide (IsCantorPrefix p.2 (charSeq A))) :=
      H2.of_eq fun p => by
        simp only [isCantorPrefix_iff_cantorPrefix_eq p.2 (charSeq A)]
    exact PointToSet.isREIn_of_computableIn_decide A
      (fun p : BitString × BitString => IsCantorPrefix p.2 (charSeq A)) H3
  nil_mem _ := fun i hi => by simp at hi
  prefix_closed := fun _ x x' hx hx' i hi => by
    rw [hx i (lt_of_lt_of_le hi hx'.length_le)]
    exact (hx'.getElem hi).symm
  regular := fun p₁ x₁ p₂ x₂ h₁ h₂ _ => by
    replace h₁ : IsCantorPrefix x₁ (charSeq A) := h₁
    replace h₂ : IsCantorPrefix x₂ (charSeq A) := h₂
    rw [isCantorPrefix_iff_cantorPrefix_eq] at h₁ h₂
    rw [← h₁, ← h₂]
    rcases le_total x₁.length x₂.length with h | h
    · exact Or.inl (cantorPrefix_mono _ h)
    · exact Or.inr (cantorPrefix_mono _ h)

/-- **SUV Problem 205 (Section 6.4.1, printed p. 203), decision complexity.** If
`KR(x) = KR^A(x) + O(1)`, then `A` is decidable.

Proof idea: as for `KM`, using Theorem 127 (b) (`computable_iff_KROf_prefixes_bounded`). -/
theorem isDecidableSet_of_KROf_eq_KRInOf (A : Set ℕ) {R : DecisionDecompressor}
    (hR : R.IsOptimal) {R' : DecisionDecompressorIn A} (hR' : R'.IsOptimal)
    (h : ∃ c : ℕ, ∀ x, KROf R x ≤ KRInOf R' x + c ∧ KRInOf R' x ≤ KROf R x + c) :
    IsDecidableSet A := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := hR' (isDecidableSet_of_KROf_eq_KRInOf_charSeqMachine A)
  have hb : ∃ d : ℕ, ∀ n, KROf R (cantorPrefix (charSeq A) n) ≤ d := by
    refine ⟨c' + c, fun n => ?_⟩
    have h0 : KRInOf (isDecidableSet_of_KROf_eq_KRInOf_charSeqMachine A)
        (cantorPrefix (charSeq A) n) ≤ 0 :=
      (modeComplexity_le_length (p := []) (fun i hi => by
        rw [cantorPrefix_getElem])).trans (by simp)
    calc KROf R (cantorPrefix (charSeq A) n)
        ≤ KRInOf R' (cantorPrefix (charSeq A) n) + c := (hc _).1
      _ ≤ (KRInOf (isDecidableSet_of_KROf_eq_KRInOf_charSeqMachine A)
            (cantorPrefix (charSeq A) n) + c') + c := by gcongr; exact hc' _
      _ ≤ (0 + c') + c := by gcongr
      _ = ((c' + c : ℕ) : ℕ∞) := by push_cast; simp
  have hcomp := (computable_iff_KROf_prefixes_bounded hR (charSeq A)).2 hb
  refine ⟨charSeq A, hcomp, fun a => ?_⟩
  classical
  simp [charSeq]

/-- The characteristic sequence of `A` is `A`-computable. -/
private theorem isDecidableSet_of_KA_eq_KAOf_aux_charSeq (A : Set ℕ) :
    ComputableIn {charOracle A} (charSeq A) := by
  classical
  have h1 : PartrecIn {charOracle A} (fun n : ℕ => charOracle A n) :=
    PartrecIn.oracle _ (Set.mem_singleton _)
  have hp : Computable (fun a : ℕ => decide (a = 1)) :=
    ((PrimrecRel.decide Primrec.eq).comp Primrec.id (Primrec.const 1)).to_comp
  have h3 := PartrecIn.map h1
    (show ComputableIn₂ {charOracle A} (fun (_ : ℕ) (a : ℕ) => decide (a = 1)) from
      (hp.comp Computable.snd).computableIn)
  refine PartrecIn.of_eq h3 fun n => ?_
  by_cases hn : n ∈ A <;> simp [charOracle, charSeq, hn]

/-- The prefixes of the characteristic sequence of `A` are `A`-computable. -/
private theorem isDecidableSet_of_KA_eq_KAOf_aux_prefix (A : Set ℕ) :
    ComputableIn {charOracle A} (cantorPrefix (charSeq A)) := by
  have hw := isDecidableSet_of_KA_eq_KAOf_aux_charSeq A
  have hstep : ComputableIn {charOracle A} (fun p : ℕ × (ℕ × BitString) =>
      p.2.2 ++ [charSeq A p.2.1]) :=
    Computable.list_concat.computableIn.comp
      (ComputableIn.pair (ComputableIn.snd.comp ComputableIn.snd)
        (hw.comp (ComputableIn.fst.comp ComputableIn.snd)))
  have hrec := ComputableIn.nat_rec (f := @id ℕ) (g := fun _ => ([] : BitString))
    (h := fun _ (k, ih) => ih ++ [charSeq A k]) ComputableIn.id
    (ComputableIn.const []) hstep.to₂
  refine hrec.of_eq fun n => ?_
  change Nat.rec ([] : BitString) (fun k ih => ih ++ [charSeq A k]) n = cantorPrefix (charSeq A) n
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.rec ([] : BitString) (fun k ih => ih ++ [charSeq A k]) n ++ [charSeq A n] =
        cantorPrefix (charSeq A) (n + 1)
      rw [ih, cantorPrefix_succ]

/-- The branch measure of the characteristic sequence of `A` is `A`-lower-semicomputable. -/
private theorem isDecidableSet_of_KA_eq_KAOf_aux_lsc (A : Set ℕ) :
    IsLSCContinuousSemimeasureIn A (branchMeasure (charSeq A)) := by
  classical
  refine ⟨branchMeasure_isContinuousTreeSemimeasure _, ?_⟩
  have hpre := isDecidableSet_of_KA_eq_KAOf_aux_prefix A
  have hlen : Computable (fun x : BitString => x.length) := Primrec.list_length.to_comp
  have hcmp : ComputableIn {charOracle A} (fun x : BitString =>
      decide (cantorPrefix (charSeq A) x.length = x)) :=
    ((PrimrecRel.decide Primrec.eq).to_comp.computableIn).comp
      (ComputableIn.pair (hpre.comp hlen.computableIn) ComputableIn.id)
  have hq : Computable (fun w : BitString × ℚ => decide (w.2 < 1)) :=
    (computable_ratLtConst 1).comp Computable.snd
  have hq0 : Computable (fun w : BitString × ℚ => decide (w.2 < 0)) :=
    (computable_ratLtConst 0).comp Computable.snd
  have hcmp2 : ComputableIn {charOracle A} (fun w : BitString × ℚ =>
      decide (cantorPrefix (charSeq A) w.1.length = w.1)) :=
    hcmp.comp ComputableIn.fst
  have hmain : ComputableIn {charOracle A} (fun w : BitString × ℚ =>
      (decide (cantorPrefix (charSeq A) w.1.length = w.1) && decide (w.2 < 1)) ||
        decide (w.2 < 0)) :=
    (Primrec.or.computableIn).comp
      (ComputableIn.pair ((Primrec.and.computableIn).comp
        (ComputableIn.pair hcmp2 hq.computableIn)) hq0.computableIn)
  refine PointToSet.isREIn_of_computableIn_decide A
    (fun w : BitString × ℚ => (w.2 : ℝ) < (branchMeasure (charSeq A) w.1).toReal) ?_
  refine hmain.of_eq fun w => ?_
  by_cases hp : cantorPrefix (charSeq A) w.1.length = w.1
  · have : ((w.2 : ℝ) < 1) ↔ w.2 < 1 := by exact_mod_cast Iff.rfl
    simp only [branchMeasure, hp, ite_true, ENNReal.toReal_one, this, decide_true, Bool.true_and]
    by_cases h1 : w.2 < 1
    · simp [h1]
    · have : ¬ w.2 < 0 := fun h => h1 (h.trans zero_lt_one)
      simp [h1, this]
  · have : ((w.2 : ℝ) < 0) ↔ w.2 < 0 := by exact_mod_cast Iff.rfl
    simp [branchMeasure, hp, this]

/-- **SUV Problem 205 (Section 6.4.1, printed p. 203), a priori complexity.** If
`KA(x) = KA^A(x) + O(1)`, then `A` is decidable. `KA^A` is `KAOf a` for a maximal
`A`-lower-semicomputable continuous semimeasure `a`.

Proof idea: as for `KM`, using `computable_iff_KA_prefixes_bounded` (Theorem 79). -/
theorem isDecidableSet_of_KA_eq_KAOf (A : Set ℕ) {a : BitString → ℝ≥0∞}
    (ha : IsMaximalContinuousSemimeasureIn A a) (h : ∃ c : ℝ, ∀ x, |KA x - KAOf a x| ≤ c) :
    IsDecidableSet A := by
  classical
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd_top, hd⟩ := ha.2 _ (isDecidableSet_of_KA_eq_KAOf_aux_lsc A)
  have hbound : ∃ B : ℝ, ∀ n, KA (cantorPrefix (charSeq A) n) ≤ B := by
    refine ⟨Real.logb 2 d.toReal + c, fun n => ?_⟩
    set x := cantorPrefix (charSeq A) n with hx
    have h1 : (1 : ℝ≥0∞) ≤ d * a x := by
      have := hd x
      have hb : branchMeasure (charSeq A) x = 1 := by simp [branchMeasure, hx]
      rwa [hb] at this
    have hax : a x ≠ ⊤ := ha.1.1.ne_top x
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h1
    have hdpos : 0 < d.toReal := ENNReal.toReal_pos hd0 hd_top
    have h2 : (1 : ℝ) ≤ d.toReal * (a x).toReal := by
      have := (ENNReal.toReal_mono (ENNReal.mul_ne_top hd_top hax) h1)
      simpa [ENNReal.toReal_mul] using this
    have hapos : 0 < (a x).toReal := by
      rcases (ENNReal.toReal_nonneg (a := a x)).lt_or_eq with h | h
      · exact h
      · rw [← h] at h2; norm_num at h2
    have h3 : 0 ≤ Real.logb 2 d.toReal + Real.logb 2 (a x).toReal := by
      rw [← Real.logb_mul hdpos.ne' hapos.ne']
      exact Real.logb_nonneg (by norm_num) h2
    have h4 := (abs_le.1 (hc x)).2
    have h5 : KAOf a x ≤ Real.logb 2 d.toReal := by unfold KAOf; linarith
    linarith
  have hcomp := (computable_iff_KA_prefixes_bounded (charSeq A)).2 hbound
  refine ⟨charSeq A, hcomp, fun n => ?_⟩
  simp [charSeq]

end GeneralScheme

end Kolmogorov
