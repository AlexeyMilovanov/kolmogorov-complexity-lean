import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ChargedHeavyNoiseCandidates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseEnumeration

/-!
# Append-only enumeration of the charged heavy candidate codes

This is the heavy-truncation counterpart of `AddNoiseEnumeration.lean`.  At
time `t` we scan the snapshot codes of programs of length `≤ i` that halt within
`t` steps, keep the canonical uniform codes whose support `B` has size `≤ 2 ^ j`,
contains a pair code `⟨x, y⟩` with `|y| = noiseLen`, and whose distinguished
fibre over `x` survives the heavy truncation at threshold `thr`; and we output
the canonical uniform code of the heavy truncation of `B`.  The stages are
accumulated with `eraseDups`, producing a duplicate-free list that only grows
with `t`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- Deduplication does not change the represented finite set. -/
theorem dedup_toFinset_bitString (L : List BitString) :
    L.dedup.toFinset = L.toFinset := by
  ext z
  simp [List.mem_dedup]

/-! ### Primitive recursiveness of the heavy output list -/

theorem heavyOutputList_primrec : Primrec₂ heavyOutputList := by
  have hcount : Primrec
      (fun q : (List BitString × Nat) × BitString => q.1.1.count q.2) := by
    have hp : Primrec₂ (fun a : (List BitString × Nat) × BitString =>
        fun z : BitString => decide (z = a.2)) := by
      exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.snd : Primrec (fun q :
          ((List BitString × Nat) × BitString) × BitString => q.2))
        (Primrec.snd.comp Primrec.fst : Primrec (fun q :
          ((List BitString × Nat) × BitString) × BitString => q.1.2)))).to₂
    convert (list_countP_primrec
      (α := (List BitString × Nat) × BitString) (β := BitString)
      (Primrec.fst.comp Primrec.fst) hp) using 1
    ext q
    simp only [List.count]
    congr 1
    funext z
    apply Bool.eq_iff_iff.mpr
    simp
  have hpow : Primrec
      (fun q : (List BitString × Nat) × BitString => 2 ^ (q.1.2 - 1)) :=
    CodedFiniteDistribution.twoPow_primrec.comp
      (Primrec.pred.comp (Primrec.snd.comp Primrec.fst))
  have hpred : Primrec₂
      (fun q : List BitString × Nat => fun y : BitString =>
        decide (2 ^ (q.2 - 1) ≤ q.1.count y)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp hpow hcount)).to₂
  exact list_filter_primrec (dedup_primrec.comp Primrec.fst) hpred

/-! ### The candidate code filter -/

/-- Boolean test selecting the codes whose support has size `≤ 2 ^ j`, contains
a pair code `⟨x, y⟩` with `|y| = noiseLen`, and has a heavy fibre over `x`. -/
def chargedHeavyCodeFilter (x : BitString) (noiseLen j thr : ℕ) (w : BitString) : Bool :=
  decide (0 < (codeSupportList w).countP
      (fun z => decide (z = pairCode x (decodeSecond z) ∧ (decodeSecond z).length = noiseLen)) ∧
    (codeSupportList w).dedup.length ≤ 2 ^ j ∧
    2 ^ (thr - 1) ≤ (codeSupportList w).dedup.countP (fun z => decide (decodeFirst z = x)))

theorem chargedHeavyCodeFilter_iff (x : BitString) (noiseLen j thr : ℕ) (w : BitString) :
    chargedHeavyCodeFilter x noiseLen j thr w = true ↔
      (∃ y : BitString, y.length = noiseLen ∧ pairCode x y ∈ codeSupportList w) ∧
        (codeSupportList w).toFinset.card ≤ 2 ^ j ∧
        2 ^ (thr - 1) ≤ (finiteSetFstFiber (codeSupportList w).toFinset x).card := by
  have hfib : (codeSupportList w).dedup.countP (fun z => decide (decodeFirst z = x)) =
      (finiteSetFstFiber (codeSupportList w).toFinset x).card := by
    rw [countP_decodeFirst_eq_fiber_card (List.nodup_dedup _) x, dedup_toFinset_bitString]
  rw [chargedHeavyCodeFilter, decide_eq_true_eq, List.card_toFinset, hfib]
  refine and_congr ?_ Iff.rfl
  rw [List.countP_pos_iff]
  constructor
  · rintro ⟨z, hz, hzp⟩
    rw [decide_eq_true_eq] at hzp
    exact ⟨decodeSecond z, hzp.2, hzp.1 ▸ hz⟩
  · rintro ⟨y, hy, hmem⟩
    refine ⟨pairCode x y, hmem, ?_⟩
    rw [decide_eq_true_eq, decodeSecond_pairCode]
    exact ⟨rfl, hy⟩

theorem chargedHeavyCodeFilter_primrec :
    Primrec (fun p : (BitString × ℕ × ℕ × ℕ) × BitString =>
      chargedHeavyCodeFilter p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have hL : Primrec (fun p : (BitString × ℕ × ℕ × ℕ) × BitString => codeSupportList p.2) :=
    codeSupportList_primrec.comp Primrec.snd
  have hpred : Primrec₂ (fun (p : (BitString × ℕ × ℕ × ℕ) × BitString) (z : BitString) =>
      decide (z = pairCode p.1.1 (decodeSecond z) ∧ (decodeSecond z).length = p.1.2.1)) := by
    have h1 : PrimrecPred (fun q : ((BitString × ℕ × ℕ × ℕ) × BitString) × BitString =>
        q.2 = pairCode q.1.1.1 (decodeSecond q.2)) :=
      Primrec.eq.comp Primrec.snd
        (pairCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (decodeSecond_primrec.comp Primrec.snd))
    have h2 : PrimrecPred (fun q : ((BitString × ℕ × ℕ × ℕ) × BitString) × BitString =>
        (decodeSecond q.2).length = q.1.1.2.1) :=
      Primrec.eq.comp (Primrec.list_length.comp (decodeSecond_primrec.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    exact (PrimrecPred.decide (PrimrecPred.and h1 h2)).to₂
  have hcount : Primrec (fun p : (BitString × ℕ × ℕ × ℕ) × BitString =>
      (codeSupportList p.2).countP
        (fun z => decide (z = pairCode p.1.1 (decodeSecond z) ∧
          (decodeSecond z).length = p.1.2.1))) :=
    list_countP_primrec hL hpred
  have hpos : PrimrecPred (fun p : (BitString × ℕ × ℕ × ℕ) × BitString =>
      0 < (codeSupportList p.2).countP
        (fun z => decide (z = pairCode p.1.1 (decodeSecond z) ∧
          (decodeSecond z).length = p.1.2.1))) :=
    Primrec.nat_lt.comp (Primrec.const 0) hcount
  have hcard : PrimrecPred (fun p : (BitString × ℕ × ℕ × ℕ) × BitString =>
      (codeSupportList p.2).dedup.length ≤ 2 ^ p.1.2.2.1) :=
    Primrec.nat_le.comp
      (Primrec.list_length.comp (dedup_primrec.comp hL))
      (twoPow_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hfibpred : Primrec₂ (fun (p : (BitString × ℕ × ℕ × ℕ) × BitString) (z : BitString) =>
      decide (decodeFirst z = p.1.1)) := by
    have : PrimrecPred (fun q : ((BitString × ℕ × ℕ × ℕ) × BitString) × BitString =>
        decodeFirst q.2 = q.1.1.1) :=
      Primrec.eq.comp (decodeFirst_primrec.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    exact (PrimrecPred.decide this).to₂
  have hfibcount : Primrec (fun p : (BitString × ℕ × ℕ × ℕ) × BitString =>
      (codeSupportList p.2).dedup.countP (fun z => decide (decodeFirst z = p.1.1))) :=
    list_countP_primrec (dedup_primrec.comp hL) hfibpred
  have hheavy : PrimrecPred (fun p : (BitString × ℕ × ℕ × ℕ) × BitString =>
      2 ^ (p.1.2.2.2 - 1) ≤
        (codeSupportList p.2).dedup.countP (fun z => decide (decodeFirst z = p.1.1))) :=
    Primrec.nat_le.comp
      (twoPow_primrec.comp (Primrec.pred.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
      hfibcount
  exact PrimrecPred.decide (PrimrecPred.and hpos (PrimrecPred.and hcard hheavy))

/-! ### The stages -/

/-- The snapshot codes at time `t` that pass the charged heavy filter. -/
def chargedHeavyFilteredCodes
    (c : Code) (x : BitString) (noiseLen i j thr t : ℕ) : List BitString :=
  ((snapshotCodes c i t).filter isCanonicalUniformCodeBool).filter
    (chargedHeavyCodeFilter x noiseLen j thr)

/-- The heavy truncation codes produced at time `t`. -/
noncomputable def chargedHeavyTruncationCodes
    (c : Code) (x : BitString) (noiseLen i j thr t : ℕ) : List BitString :=
  (chargedHeavyFilteredCodes c x noiseLen i j thr t).map
    (fun w => canonicalImageCodeOfList
      (heavyOutputList ((codeSupportList w).dedup.map decodeFirst) thr))

/-- Append-only enumeration of the charged heavy truncation codes. -/
noncomputable def chargedHeavyAppearanceCodes
    (c : Code) (x : BitString) (noiseLen i j thr : ℕ) : ℕ → List BitString
  | 0 => (chargedHeavyTruncationCodes c x noiseLen i j thr 0).eraseDups
  | t + 1 => (chargedHeavyAppearanceCodes c x noiseLen i j thr t ++
      chargedHeavyTruncationCodes c x noiseLen i j thr (t + 1)).eraseDups

theorem chargedHeavyFilteredCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      chargedHeavyFilteredCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2.1 p.1.1.2.2.2 p.2) := by
  have h1 : Primrec (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      snapshotCodes c p.1.2 p.2) :=
    (snapshotCodes_primrec c).comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have h2 : Primrec (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      (snapshotCodes c p.1.2 p.2).filter isCanonicalUniformCodeBool) :=
    list_filter_primrec h1 (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)
  refine list_filter_primrec h2 ?_
  exact (chargedHeavyCodeFilter_primrec.comp
    (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂

theorem chargedHeavyTruncationCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      chargedHeavyTruncationCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2.1 p.1.1.2.2.2 p.2) := by
  refine Primrec.list_map (chargedHeavyFilteredCodes_primrec c) ?_
  have hlist : Primrec (fun q : (((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ) × BitString =>
      (codeSupportList q.2).dedup.map decodeFirst) :=
    Primrec.list_map (dedup_primrec.comp (codeSupportList_primrec.comp Primrec.snd))
      ((decodeFirst_primrec.comp Primrec.snd).to₂)
  have hthr : Primrec (fun q : (((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ) × BitString =>
      q.1.1.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  exact (canonicalImageCodeOfList_primrec.comp
    (heavyOutputList_primrec.comp hlist hthr)).to₂

theorem chargedHeavyAppearanceCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      chargedHeavyAppearanceCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2.1 p.1.1.2.2.2 p.2) := by
  have hbase : Primrec (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      (chargedHeavyTruncationCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2.1
        p.1.1.2.2.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      ((chargedHeavyTruncationCodes_primrec c).comp
        (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ chargedHeavyTruncationCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2.1 p.1.1.2.2.2
        (z.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp (Primrec.list_append.comp
      (Primrec.snd.comp Primrec.snd)
      ((chargedHeavyTruncationCodes_primrec c).comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨⟨x, noiseLen, j, thr⟩, i⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih => simp only [chargedHeavyAppearanceCodes]; rw [← ih]

theorem chargedHeavyAppearanceCodes_computable (c : Code) :
    Computable (fun p : ((BitString × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      chargedHeavyAppearanceCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2.1 p.1.1.2.2.2 p.2) :=
  (chargedHeavyAppearanceCodes_primrec c).to_comp

/-! ### Structural properties of the enumeration -/

@[simp] theorem chargedHeavyAppearanceCodes_zero
    (c : Code) (x : BitString) (noiseLen i j thr : ℕ) :
    chargedHeavyAppearanceCodes c x noiseLen i j thr 0 =
      (chargedHeavyTruncationCodes c x noiseLen i j thr 0).eraseDups := rfl

theorem chargedHeavyAppearanceCodes_succ
    (c : Code) (x : BitString) (noiseLen i j thr t : ℕ) :
    chargedHeavyAppearanceCodes c x noiseLen i j thr (t + 1) =
      (chargedHeavyAppearanceCodes c x noiseLen i j thr t ++
        chargedHeavyTruncationCodes c x noiseLen i j thr (t + 1)).eraseDups := rfl

theorem chargedHeavyAppearanceCodes_nodup
    (c : Code) (x : BitString) (noiseLen i j thr t : ℕ) :
    (chargedHeavyAppearanceCodes c x noiseLen i j thr t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

theorem chargedHeavyAppearanceCodes_prefix
    (c : Code) (x : BitString) (noiseLen i j thr t : ℕ) :
    chargedHeavyAppearanceCodes c x noiseLen i j thr t <+:
      chargedHeavyAppearanceCodes c x noiseLen i j thr (t + 1) := by
  rw [chargedHeavyAppearanceCodes_succ]
  exact prefix_eraseDups_append_of_nodup _ _
    (chargedHeavyAppearanceCodes_nodup c x noiseLen i j thr t)

theorem mem_chargedHeavyAppearanceCodes_of_mem_stage
    {c : Code} {x : BitString} {noiseLen i j thr t : ℕ} {w : BitString}
    (hw : w ∈ chargedHeavyTruncationCodes c x noiseLen i j thr t) :
    w ∈ chargedHeavyAppearanceCodes c x noiseLen i j thr t := by
  cases t with
  | zero => exact mem_eraseDups_bitString.mpr hw
  | succ t =>
    rw [chargedHeavyAppearanceCodes_succ]
    exact mem_eraseDups_bitString.mpr (List.mem_append_right _ hw)

theorem exists_stage_of_mem_chargedHeavyAppearanceCodes
    {c : Code} {x : BitString} {noiseLen i j thr t : ℕ} {w : BitString}
    (hw : w ∈ chargedHeavyAppearanceCodes c x noiseLen i j thr t) :
    ∃ t', w ∈ chargedHeavyTruncationCodes c x noiseLen i j thr t' := by
  induction t with
  | zero => exact ⟨0, mem_eraseDups_bitString.mp hw⟩
  | succ t ih =>
    rw [chargedHeavyAppearanceCodes_succ] at hw
    rcases List.mem_append.mp (mem_eraseDups_bitString.mp hw) with h | h
    · exact ih h
    · exact ⟨t + 1, h⟩

/-! ### Soundness and completeness against `chargedHeavyNoiseCandidatesRaw` -/

/-- Each stage entry is the canonical uniform code of an actual charged heavy
candidate, and decoding it returns that candidate. -/
theorem mem_chargedHeavyTruncationCodes_sound
    {U : Map} {c : Code} (hc : IsCodeFor c U)
    {x : BitString} {noiseLen i j thr t : ℕ} {w : BitString}
    (hw : w ∈ chargedHeavyTruncationCodes c x noiseLen i j thr t) :
    ∃ (H : Finset BitString) (hH : H.Nonempty),
      H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr ∧
        w = (codedUniformOn H hH).code ∧
        (codeSupportList w).toFinset = H := by
  rw [chargedHeavyTruncationCodes, List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [chargedHeavyFilteredCodes, List.mem_filter, List.mem_filter] at hv
  obtain ⟨⟨hsnap, hcanon⟩, hfilter⟩ := hv
  obtain ⟨⟨y, hy, hpairlist⟩, hcard, hheavy⟩ :=
    (chargedHeavyCodeFilter_iff x noiseLen j thr v).mp hfilter
  have hpair : pairCode x y ∈ (codeSupportList v).toFinset := List.mem_toFinset.mpr hpairlist
  set B : Finset BitString := (codeSupportList v).toFinset with hB
  have hBmem : B ∈ snapshotDescriptionsAndSizeLe c i j t := by
    rw [snapshotDescriptionsAndSizeLe, Finset.mem_filter]
    refine ⟨?_, hcard⟩
    rw [snapshotDescriptions, Finset.mem_image]
    exact ⟨v, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hsnap, hcanon⟩), rfl⟩
  have hBdesc : B ∈ descriptionsWithComplexityLeAndSizeLe U i j :=
    snapshotDescriptionsAndSizeLe_subset_descriptions hc i j t hBmem
  have hxH : x ∈ finiteSetFstHeavyTruncation B thr := by
    rw [mem_finiteSetFstHeavyTruncation_iff]
    exact ⟨⟨pairCode x y, hpair, decodeFirst_pairCode x y⟩, hheavy⟩
  have hHmem : finiteSetFstHeavyTruncation B thr ∈
      chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr :=
    mem_chargedHeavyNoiseCandidatesRaw_iff.mpr
      ⟨B, hBdesc, ⟨y, by simp [stringsOfLength, hy], hpair⟩, hxH, rfl⟩
  have hHne : (finiteSetFstHeavyTruncation B thr).Nonempty := ⟨x, hxH⟩
  have hlist : (heavyOutputList ((codeSupportList v).dedup.map decodeFirst) thr).toFinset =
      finiteSetFstHeavyTruncation B thr := by
    rw [heavyOutputList_map_decodeFirst_toFinset (List.nodup_dedup _) thr,
      dedup_toFinset_bitString]
  have hcode : canonicalImageCodeOfList
      (heavyOutputList ((codeSupportList v).dedup.map decodeFirst) thr) =
      (codedUniformOn (finiteSetFstHeavyTruncation B thr) hHne).code := by
    rw [canonicalImageCodeOfList_eq_codedUniformOn _ (by rw [hlist]; exact hHne)]
    exact codedUniformOn_code_congr _ _ hlist
  refine ⟨finiteSetFstHeavyTruncation B thr, hHne, hHmem, hcode, ?_⟩
  rw [hcode, codeSupportList_codedUniformOn, canonicalFinsetList_toFinset]

/-- Every charged heavy candidate eventually appears in the enumeration. -/
theorem mem_chargedHeavyTruncationCodes_complete
    {U : Map} {c : Code} (hc : IsCodeFor c U)
    {x : BitString} {noiseLen i j thr : ℕ} {H : Finset BitString}
    (hH : H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr) :
    ∃ t, canonicalUniformCodeOfList (canonicalFinsetList H) ∈
      chargedHeavyTruncationCodes c x noiseLen i j thr t := by
  obtain ⟨B, hBdesc, ⟨y, hy, hpair⟩, hxH, rfl⟩ := mem_chargedHeavyNoiseCandidatesRaw_iff.mp hH
  have hylen : y.length = noiseLen := by
    simpa [stringsOfLength] using hy
  obtain ⟨t₀, hmax⟩ := exists_max_countHalts c i
  have hBsnap : B ∈ snapshotDescriptionsAndSizeLe c i j t₀ := by
    rw [snapshotDescriptionsAndSizeLe_eq_descriptionsWithComplexityLeAndSizeLe hc i j t₀ hmax]
    exact hBdesc
  rw [snapshotDescriptionsAndSizeLe, Finset.mem_filter, snapshotDescriptions,
    Finset.mem_image] at hBsnap
  obtain ⟨⟨v, hv, hvB⟩, hcard⟩ := hBsnap
  rw [List.mem_toFinset, List.mem_filter] at hv
  have hsupp : (codeSupportList v).toFinset = B := hvB
  have hheavy : 2 ^ (thr - 1) ≤ (finiteSetFstFiber B x).card :=
    ((mem_finiteSetFstHeavyTruncation_iff B thr x).mp hxH).2
  have hfilter : chargedHeavyCodeFilter x noiseLen j thr v = true := by
    rw [chargedHeavyCodeFilter_iff]
    refine ⟨⟨y, hylen, ?_⟩, by rw [hsupp]; exact hcard, by rw [hsupp]; exact hheavy⟩
    exact List.mem_toFinset.mp (by rw [hsupp]; exact hpair)
  have hvmem : v ∈ chargedHeavyFilteredCodes c x noiseLen i j thr t₀ := by
    rw [chargedHeavyFilteredCodes, List.mem_filter, List.mem_filter]
    exact ⟨⟨hv.1, hv.2⟩, hfilter⟩
  have hHne : (finiteSetFstHeavyTruncation B thr).Nonempty := ⟨x, hxH⟩
  have hlist : (heavyOutputList ((codeSupportList v).dedup.map decodeFirst) thr).toFinset =
      finiteSetFstHeavyTruncation B thr := by
    rw [heavyOutputList_map_decodeFirst_toFinset (List.nodup_dedup _) thr,
      dedup_toFinset_bitString, hsupp]
  refine ⟨t₀, ?_⟩
  rw [canonicalUniformCodeOfList_canonicalFinsetList _ hHne,
    chargedHeavyTruncationCodes, List.mem_map]
  refine ⟨v, hvmem, ?_⟩
  rw [canonicalImageCodeOfList_eq_codedUniformOn _ (by rw [hlist]; exact hHne)]
  exact codedUniformOn_code_congr _ _ hlist

theorem chargedHeavyAppearanceCodes_length_le
    {U : Map} {c : Code} (hc : IsCodeFor c U) (x : BitString) (noiseLen i j thr t : ℕ) :
    (chargedHeavyAppearanceCodes c x noiseLen i j thr t).length ≤
      (chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr).card := by
  set L := chargedHeavyAppearanceCodes c x noiseLen i j thr t with hL
  have hnodup : L.Nodup := chargedHeavyAppearanceCodes_nodup c x noiseLen i j thr t
  have hmaps : ∀ w ∈ L, (codeSupportList w).toFinset ∈
      chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr := by
    intro w hw
    obtain ⟨t', hw'⟩ := exists_stage_of_mem_chargedHeavyAppearanceCodes hw
    obtain ⟨H, _, hHmem, _, hdec⟩ := mem_chargedHeavyTruncationCodes_sound hc hw'
    rw [hdec]; exact hHmem
  have hinj : ∀ w₁ ∈ L, ∀ w₂ ∈ L,
      (codeSupportList w₁).toFinset = (codeSupportList w₂).toFinset → w₁ = w₂ := by
    intro w₁ hw₁ w₂ hw₂ heq
    obtain ⟨t₁, hs₁⟩ := exists_stage_of_mem_chargedHeavyAppearanceCodes hw₁
    obtain ⟨t₂, hs₂⟩ := exists_stage_of_mem_chargedHeavyAppearanceCodes hw₂
    obtain ⟨H₁, hH₁, _, hcode₁, hdec₁⟩ := mem_chargedHeavyTruncationCodes_sound hc hs₁
    obtain ⟨H₂, hH₂, _, hcode₂, hdec₂⟩ := mem_chargedHeavyTruncationCodes_sound hc hs₂
    rw [hcode₁, hcode₂]
    refine codedUniformOn_code_congr hH₁ hH₂ ?_
    rw [← hdec₁, ← hdec₂]
    exact heq
  have hnd : (L.map (fun w => (codeSupportList w).toFinset)).Nodup :=
    List.Nodup.map_on hinj hnodup
  have hsub : (L.map (fun w => (codeSupportList w).toFinset)).toFinset ⊆
      chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr := by
    intro S hS
    rw [List.mem_toFinset, List.mem_map] at hS
    obtain ⟨w, hwL, rfl⟩ := hS
    exact hmaps w hwL
  calc L.length = (L.map (fun w => (codeSupportList w).toFinset)).length := by simp
    _ = (L.map (fun w => (codeSupportList w).toFinset)).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Charged leaf packet 1.**  The append-only enumeration of charged heavy
truncation codes is duplicate free, grows only by appending, enumerates exactly
the canonical codes of `chargedHeavyNoiseCandidatesRaw`, and never exceeds the
number of candidates. -/
theorem chargedHeavyAppearanceCodes_spec
    {U : Map} {c : Code} (hc : IsCodeFor c U) :
    (∀ x noiseLen i j thr t,
      (chargedHeavyAppearanceCodes c x noiseLen i j thr t).Nodup) ∧
    (∀ x noiseLen i j thr t,
      chargedHeavyAppearanceCodes c x noiseLen i j thr t <+:
        chargedHeavyAppearanceCodes c x noiseLen i j thr (t + 1)) ∧
    (∀ x noiseLen i j thr H,
      H ∈ chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr ↔
        ∃ t, canonicalUniformCodeOfList (canonicalFinsetList H) ∈
          chargedHeavyAppearanceCodes c x noiseLen i j thr t) ∧
    (∀ x noiseLen i j thr t,
      (chargedHeavyAppearanceCodes c x noiseLen i j thr t).length ≤
        (chargedHeavyNoiseCandidatesRaw U x noiseLen i j thr).card) := by
  refine ⟨chargedHeavyAppearanceCodes_nodup c,
    chargedHeavyAppearanceCodes_prefix c, ?_,
    fun x noiseLen i j thr t =>
      chargedHeavyAppearanceCodes_length_le hc x noiseLen i j thr t⟩
  intro x noiseLen i j thr H
  constructor
  · intro hH
    obtain ⟨t, ht⟩ := mem_chargedHeavyTruncationCodes_complete hc hH
    exact ⟨t, mem_chargedHeavyAppearanceCodes_of_mem_stage ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := exists_stage_of_mem_chargedHeavyAppearanceCodes ht
    obtain ⟨H', hH', hmem, hcode, _⟩ := mem_chargedHeavyTruncationCodes_sound hc ht'
    have hlist : canonicalFinsetList H = canonicalFinsetList H' := by
      have : canonicalUniformCodeOfList (canonicalFinsetList H) =
          canonicalUniformCodeOfList (canonicalFinsetList H') := by
        rw [hcode, canonicalUniformCodeOfList_canonicalFinsetList H' hH']
      exact canonicalUniformCodeOfList_injective this
    have : H = H' := by
      have := congrArg List.toFinset hlist
      rwa [canonicalFinsetList_toFinset, canonicalFinsetList_toFinset] at this
    rw [this]
    exact hmem

end Kolmogorov
