import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseCandidates
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CanonicalImage
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting

/-!
# Append-only enumeration of the candidate truncation codes

The direct add-noise route needs the finite set `noiseCandidateTruncations`
to be *enumerable*: an online, append-only list of the canonical uniform codes
of the candidate truncations, computable in all parameters, never longer than
the abstract candidate set.

This file provides that enumeration.  At time `t` we scan the snapshot codes of
programs of length `≤ i` that halt within `t` steps, keep the canonical uniform
codes whose support `B` has size `≤ 2 ^ j` and contains a pair code `⟨x, y⟩`
with `|y| = l`, and output the canonical uniform code of the first-coordinate
truncation of `B`.  The stages are accumulated with `eraseDups`, producing a
duplicate-free list that only grows with `t`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- The decoded support list of a distribution code. -/
def codeSupportList (w : BitString) : List BitString :=
  (decodeDistributionData w).map CodedDistributionEntry.point

theorem codeSupportList_primrec : Primrec codeSupportList :=
  Primrec.list_map decodeDistributionData_primrec (entry_point_primrec.comp Primrec.snd)

@[simp] theorem codeSupportList_codedUniformOn (S : Finset BitString) (hS : S.Nonempty) :
    codeSupportList (codedUniformOn S hS).code = canonicalFinsetList S := by
  unfold codeSupportList
  exact dataPoints_codedUniformOn S hS

/-- Boolean test selecting the codes whose support has size `≤ 2 ^ j` and
contains a pair code `⟨x, y⟩` with `|y| = l`. -/
def noiseCandidateCodeFilter (x : BitString) (l j : ℕ) (w : BitString) : Bool :=
  decide (0 < (codeSupportList w).countP
      (fun z => decide (z = pairCode x (decodeSecond z) ∧ (decodeSecond z).length = l)) ∧
    (codeSupportList w).dedup.length ≤ 2 ^ j)

theorem noiseCandidateCodeFilter_iff (x : BitString) (l j : ℕ) (w : BitString) :
    noiseCandidateCodeFilter x l j w = true ↔
      (∃ y : BitString, y.length = l ∧ pairCode x y ∈ codeSupportList w) ∧
        (codeSupportList w).toFinset.card ≤ 2 ^ j := by
  rw [noiseCandidateCodeFilter, decide_eq_true_eq, List.card_toFinset]
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

theorem noiseCandidateCodeFilter_primrec :
    Primrec (fun p : (BitString × ℕ × ℕ) × BitString =>
      noiseCandidateCodeFilter p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hL : Primrec (fun p : (BitString × ℕ × ℕ) × BitString => codeSupportList p.2) :=
    codeSupportList_primrec.comp Primrec.snd
  have hpred : Primrec₂ (fun (p : (BitString × ℕ × ℕ) × BitString) (z : BitString) =>
      decide (z = pairCode p.1.1 (decodeSecond z) ∧ (decodeSecond z).length = p.1.2.1)) := by
    have h1 : PrimrecPred (fun q : ((BitString × ℕ × ℕ) × BitString) × BitString =>
        q.2 = pairCode q.1.1.1 (decodeSecond q.2)) :=
      Primrec.eq.comp Primrec.snd
        (pairCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (decodeSecond_primrec.comp Primrec.snd))
    have h2 : PrimrecPred (fun q : ((BitString × ℕ × ℕ) × BitString) × BitString =>
        (decodeSecond q.2).length = q.1.1.2.1) :=
      Primrec.eq.comp (Primrec.list_length.comp (decodeSecond_primrec.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    exact (PrimrecPred.decide (PrimrecPred.and h1 h2)).to₂
  have hcount : Primrec (fun p : (BitString × ℕ × ℕ) × BitString =>
      (codeSupportList p.2).countP
        (fun z => decide (z = pairCode p.1.1 (decodeSecond z) ∧
          (decodeSecond z).length = p.1.2.1))) :=
    list_countP_primrec hL hpred
  have hpos : PrimrecPred (fun p : (BitString × ℕ × ℕ) × BitString =>
      0 < (codeSupportList p.2).countP
        (fun z => decide (z = pairCode p.1.1 (decodeSecond z) ∧
          (decodeSecond z).length = p.1.2.1))) :=
    Primrec.nat_lt.comp (Primrec.const 0) hcount
  have hcard : PrimrecPred (fun p : (BitString × ℕ × ℕ) × BitString =>
      (codeSupportList p.2).dedup.length ≤ 2 ^ p.1.2.2) :=
    Primrec.nat_le.comp
      (Primrec.list_length.comp (dedup_primrec.comp hL))
      (twoPow_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  exact PrimrecPred.decide (PrimrecPred.and hpos hcard)

/-- The snapshot codes at time `t` that pass the candidate filter. -/
def noiseCandidateFilteredCodes (c : Code) (x : BitString) (l i j t : ℕ) : List BitString :=
  ((snapshotCodes c i t).filter isCanonicalUniformCodeBool).filter
    (noiseCandidateCodeFilter x l j)

/-- The truncation codes produced at time `t`. -/
noncomputable def noiseCandidateTruncationCodes
    (c : Code) (x : BitString) (l i j t : ℕ) : List BitString :=
  (noiseCandidateFilteredCodes c x l i j t).map
    (fun w => canonicalImageCodeOfList ((codeSupportList w).map decodeFirst))

/-- Append-only enumeration of the candidate truncation codes. -/
noncomputable def noiseCandidateTruncationAppearanceCodes
    (c : Code) (x : BitString) (l i j : ℕ) : ℕ → List BitString
  | 0 => (noiseCandidateTruncationCodes c x l i j 0).eraseDups
  | t + 1 => (noiseCandidateTruncationAppearanceCodes c x l i j t ++
      noiseCandidateTruncationCodes c x l i j (t + 1)).eraseDups

theorem noiseCandidateFilteredCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      noiseCandidateFilteredCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2 p.2) := by
  have h1 : Primrec (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      snapshotCodes c p.1.2 p.2) :=
    (snapshotCodes_primrec c).comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have h2 : Primrec (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      (snapshotCodes c p.1.2 p.2).filter isCanonicalUniformCodeBool) :=
    list_filter_primrec h1 (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)
  refine list_filter_primrec h2 ?_
  exact (noiseCandidateCodeFilter_primrec.comp
    (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂

theorem noiseCandidateTruncationCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      noiseCandidateTruncationCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2 p.2) := by
  refine Primrec.list_map (noiseCandidateFilteredCodes_primrec c) ?_
  exact (canonicalImageCodeOfList_primrec.comp
    (Primrec.list_map (codeSupportList_primrec.comp Primrec.snd)
      ((decodeFirst_primrec.comp Primrec.snd).to₂))).to₂

theorem noiseCandidateTruncationAppearanceCodes_primrec (c : Code) :
    Primrec (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      noiseCandidateTruncationAppearanceCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2 p.2) := by
  have hbase : Primrec (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      (noiseCandidateTruncationCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      ((noiseCandidateTruncationCodes_primrec c).comp
        (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : ((BitString × ℕ × ℕ) × ℕ) × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ noiseCandidateTruncationCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2
        (z.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp (Primrec.list_append.comp
      (Primrec.snd.comp Primrec.snd)
      ((noiseCandidateTruncationCodes_primrec c).comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨⟨x, l, j⟩, i⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih => simp only [noiseCandidateTruncationAppearanceCodes]; rw [← ih]

theorem noiseCandidateTruncationAppearanceCodes_computable (c : Code) :
    Computable (fun p : ((BitString × ℕ × ℕ) × ℕ) × ℕ =>
      noiseCandidateTruncationAppearanceCodes c p.1.1.1 p.1.1.2.1 p.1.2 p.1.1.2.2 p.2) :=
  (noiseCandidateTruncationAppearanceCodes_primrec c).to_comp

/-! ### Structural properties of the enumeration -/

@[simp] theorem noiseCandidateTruncationAppearanceCodes_zero
    (c : Code) (x : BitString) (l i j : ℕ) :
    noiseCandidateTruncationAppearanceCodes c x l i j 0 =
      (noiseCandidateTruncationCodes c x l i j 0).eraseDups := rfl

theorem noiseCandidateTruncationAppearanceCodes_succ
    (c : Code) (x : BitString) (l i j t : ℕ) :
    noiseCandidateTruncationAppearanceCodes c x l i j (t + 1) =
      (noiseCandidateTruncationAppearanceCodes c x l i j t ++
        noiseCandidateTruncationCodes c x l i j (t + 1)).eraseDups := rfl

theorem noiseCandidateTruncationAppearanceCodes_nodup
    (c : Code) (x : BitString) (l i j t : ℕ) :
    (noiseCandidateTruncationAppearanceCodes c x l i j t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

theorem noiseCandidateTruncationAppearanceCodes_prefix
    (c : Code) (x : BitString) (l i j t : ℕ) :
    noiseCandidateTruncationAppearanceCodes c x l i j t <+:
      noiseCandidateTruncationAppearanceCodes c x l i j (t + 1) := by
  rw [noiseCandidateTruncationAppearanceCodes_succ]
  exact prefix_eraseDups_append_of_nodup _ _
    (noiseCandidateTruncationAppearanceCodes_nodup c x l i j t)

theorem mem_noiseCandidateTruncationAppearanceCodes_of_mem_stage
    {c : Code} {x : BitString} {l i j t : ℕ} {w : BitString}
    (hw : w ∈ noiseCandidateTruncationCodes c x l i j t) :
    w ∈ noiseCandidateTruncationAppearanceCodes c x l i j t := by
  cases t with
  | zero => exact mem_eraseDups_bitString.mpr hw
  | succ t =>
    rw [noiseCandidateTruncationAppearanceCodes_succ]
    exact mem_eraseDups_bitString.mpr (List.mem_append_right _ hw)

theorem exists_stage_of_mem_noiseCandidateTruncationAppearanceCodes
    {c : Code} {x : BitString} {l i j t : ℕ} {w : BitString}
    (hw : w ∈ noiseCandidateTruncationAppearanceCodes c x l i j t) :
    ∃ t', w ∈ noiseCandidateTruncationCodes c x l i j t' := by
  induction t with
  | zero => exact ⟨0, mem_eraseDups_bitString.mp hw⟩
  | succ t ih =>
    rw [noiseCandidateTruncationAppearanceCodes_succ] at hw
    rcases List.mem_append.mp (mem_eraseDups_bitString.mp hw) with h | h
    · exact ih h
    · exact ⟨t + 1, h⟩

/-! ### Soundness and completeness against `noiseCandidateTruncations` -/

/-- The canonical uniform list encoder is injective. -/
theorem canonicalUniformCodeOfList_injective :
    Function.Injective canonicalUniformCodeOfList := by
  intro s t h
  have h1 := codedDistributionDataCode_injective h
  have h2 := congrArg (List.map CodedDistributionEntry.point) h1
  simpa [List.map_map, Function.comp_def] using h2

/-- Each stage entry is the canonical uniform code of an actual candidate
truncation, and decoding it returns that candidate. -/
theorem mem_noiseCandidateTruncationCodes_sound
    {U : Map} {c : Code} (hc : IsCodeFor c U)
    {x : BitString} {l i j t : ℕ} {w : BitString}
    (hw : w ∈ noiseCandidateTruncationCodes c x l i j t) :
    ∃ (A : Finset BitString) (hA : A.Nonempty),
      A ∈ noiseCandidateTruncations U x l i j ∧
        w = (codedUniformOn A hA).code ∧
        (codeSupportList w).toFinset = A := by
  rw [noiseCandidateTruncationCodes, List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [noiseCandidateFilteredCodes, List.mem_filter, List.mem_filter] at hv
  obtain ⟨⟨hsnap, hcanon⟩, hfilter⟩ := hv
  obtain ⟨⟨y, hy, hpairlist⟩, hcard⟩ := (noiseCandidateCodeFilter_iff x l j v).mp hfilter
  have hpair : pairCode x y ∈ (codeSupportList v).toFinset := List.mem_toFinset.mpr hpairlist
  set B : Finset BitString := (codeSupportList v).toFinset with hB
  have hBmem : B ∈ snapshotDescriptionsAndSizeLe c i j t := by
    rw [snapshotDescriptionsAndSizeLe, Finset.mem_filter]
    refine ⟨?_, hcard⟩
    rw [snapshotDescriptions, Finset.mem_image]
    exact ⟨v, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hsnap, hcanon⟩), rfl⟩
  have hBdesc : B ∈ descriptionsWithComplexityLeAndSizeLe U i j :=
    snapshotDescriptionsAndSizeLe_subset_descriptions hc i j t hBmem
  have hAmem : finiteSetFstTruncation B ∈ noiseCandidateTruncations U x l i j := by
    rw [noiseCandidateTruncations, Finset.mem_image]
    refine ⟨B, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨hBdesc, y, ?_, hpair⟩
    simp [stringsOfLength, hy]
  have hAne : (finiteSetFstTruncation B).Nonempty :=
    ⟨x, finiteSetFstTruncation_mem hpair⟩
  have hlist : ((codeSupportList v).map decodeFirst).toFinset = finiteSetFstTruncation B := by
    ext z
    simp [finiteSetFstTruncation, hB]
  have hcode : canonicalImageCodeOfList ((codeSupportList v).map decodeFirst) =
      (codedUniformOn (finiteSetFstTruncation B) hAne).code := by
    rw [canonicalImageCodeOfList_eq_codedUniformOn _ (by rw [hlist]; exact hAne)]
    exact codedUniformOn_code_congr _ _ hlist
  refine ⟨finiteSetFstTruncation B, hAne, hAmem, hcode, ?_⟩
  rw [hcode, codeSupportList_codedUniformOn, canonicalFinsetList_toFinset]

/-- Every candidate truncation eventually appears in the enumeration. -/
theorem mem_noiseCandidateTruncationCodes_complete
    {U : Map} {c : Code} (hc : IsCodeFor c U)
    {x : BitString} {l i j : ℕ} {A : Finset BitString}
    (hA : A ∈ noiseCandidateTruncations U x l i j) :
    ∃ t, canonicalUniformCodeOfList (canonicalFinsetList A) ∈
      noiseCandidateTruncationCodes c x l i j t := by
  rw [noiseCandidateTruncations, Finset.mem_image] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [Finset.mem_filter] at hB
  obtain ⟨hBdesc, y, hy, hpair⟩ := hB
  have hylen : y.length = l := by
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
  have hfilter : noiseCandidateCodeFilter x l j v = true := by
    rw [noiseCandidateCodeFilter_iff]
    refine ⟨⟨y, hylen, ?_⟩, by rw [hsupp]; exact hcard⟩
    exact List.mem_toFinset.mp (by rw [hsupp]; exact hpair)
  have hvmem : v ∈ noiseCandidateFilteredCodes c x l i j t₀ := by
    rw [noiseCandidateFilteredCodes, List.mem_filter, List.mem_filter]
    exact ⟨⟨hv.1, hv.2⟩, hfilter⟩
  have hAne : (finiteSetFstTruncation B).Nonempty :=
    ⟨x, finiteSetFstTruncation_mem hpair⟩
  have hlist : ((codeSupportList v).map decodeFirst).toFinset = finiteSetFstTruncation B := by
    ext z
    simp [finiteSetFstTruncation, ← hsupp]
  refine ⟨t₀, ?_⟩
  rw [canonicalUniformCodeOfList_canonicalFinsetList _ hAne,
    noiseCandidateTruncationCodes, List.mem_map]
  refine ⟨v, hvmem, ?_⟩
  rw [canonicalImageCodeOfList_eq_codedUniformOn _ (by rw [hlist]; exact hAne)]
  exact codedUniformOn_code_congr _ _ hlist

theorem noiseCandidateTruncationAppearanceCodes_length_le
    {U : Map} {c : Code} (hc : IsCodeFor c U) (x : BitString) (l i j t : ℕ) :
    (noiseCandidateTruncationAppearanceCodes c x l i j t).length ≤
      (noiseCandidateTruncations U x l i j).card := by
  set L := noiseCandidateTruncationAppearanceCodes c x l i j t with hL
  have hnodup : L.Nodup := noiseCandidateTruncationAppearanceCodes_nodup c x l i j t
  have hmaps : ∀ w ∈ L, (codeSupportList w).toFinset ∈ noiseCandidateTruncations U x l i j := by
    intro w hw
    obtain ⟨t', hw'⟩ := exists_stage_of_mem_noiseCandidateTruncationAppearanceCodes hw
    obtain ⟨A, _, hAmem, _, hdec⟩ := mem_noiseCandidateTruncationCodes_sound hc hw'
    rw [hdec]; exact hAmem
  have hinj : ∀ w₁ ∈ L, ∀ w₂ ∈ L,
      (codeSupportList w₁).toFinset = (codeSupportList w₂).toFinset → w₁ = w₂ := by
    intro w₁ hw₁ w₂ hw₂ heq
    obtain ⟨t₁, hs₁⟩ := exists_stage_of_mem_noiseCandidateTruncationAppearanceCodes hw₁
    obtain ⟨t₂, hs₂⟩ := exists_stage_of_mem_noiseCandidateTruncationAppearanceCodes hw₂
    obtain ⟨A₁, hA₁, _, hcode₁, hdec₁⟩ := mem_noiseCandidateTruncationCodes_sound hc hs₁
    obtain ⟨A₂, hA₂, _, hcode₂, hdec₂⟩ := mem_noiseCandidateTruncationCodes_sound hc hs₂
    rw [hcode₁, hcode₂]
    refine codedUniformOn_code_congr hA₁ hA₂ ?_
    rw [← hdec₁, ← hdec₂]
    exact heq
  have hnd : (L.map (fun w => (codeSupportList w).toFinset)).Nodup :=
    List.Nodup.map_on hinj hnodup
  have hsub : (L.map (fun w => (codeSupportList w).toFinset)).toFinset ⊆
      noiseCandidateTruncations U x l i j := by
    intro S hS
    rw [List.mem_toFinset, List.mem_map] at hS
    obtain ⟨w, hwL, rfl⟩ := hS
    exact hmaps w hwL
  calc L.length = (L.map (fun w => (codeSupportList w).toFinset)).length := by simp
    _ = (L.map (fun w => (codeSupportList w).toFinset)).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Leaf packet 1.**  The append-only enumeration of candidate truncation
codes is duplicate free, grows only by appending, enumerates exactly the
canonical codes of `noiseCandidateTruncations`, and never exceeds the number of
candidates. -/
theorem noiseCandidateTruncationAppearanceCodes_spec
    {U : Map} {c : Code} (hc : IsCodeFor c U) :
    (∀ x l i j t,
      (noiseCandidateTruncationAppearanceCodes c x l i j t).Nodup) ∧
    (∀ x l i j t,
      noiseCandidateTruncationAppearanceCodes c x l i j t <+:
        noiseCandidateTruncationAppearanceCodes c x l i j (t + 1)) ∧
    (∀ x l i j A,
      A ∈ noiseCandidateTruncations U x l i j ↔
        ∃ t, canonicalUniformCodeOfList (canonicalFinsetList A) ∈
          noiseCandidateTruncationAppearanceCodes c x l i j t) ∧
    (∀ x l i j t,
      (noiseCandidateTruncationAppearanceCodes c x l i j t).length ≤
        (noiseCandidateTruncations U x l i j).card) := by
  refine ⟨noiseCandidateTruncationAppearanceCodes_nodup c,
    noiseCandidateTruncationAppearanceCodes_prefix c, ?_,
    fun x l i j t => noiseCandidateTruncationAppearanceCodes_length_le hc x l i j t⟩
  intro x l i j A
  constructor
  · intro hA
    obtain ⟨t, ht⟩ := mem_noiseCandidateTruncationCodes_complete hc hA
    exact ⟨t, mem_noiseCandidateTruncationAppearanceCodes_of_mem_stage ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := exists_stage_of_mem_noiseCandidateTruncationAppearanceCodes ht
    obtain ⟨A', hA', hmem, hcode, _⟩ := mem_noiseCandidateTruncationCodes_sound hc ht'
    have hlist : canonicalFinsetList A = canonicalFinsetList A' := by
      have : canonicalUniformCodeOfList (canonicalFinsetList A) =
          canonicalUniformCodeOfList (canonicalFinsetList A') := by
        rw [hcode, canonicalUniformCodeOfList_canonicalFinsetList A' hA']
      exact canonicalUniformCodeOfList_injective this
    have : A = A' := by
      have := congrArg List.toFinset hlist
      rwa [canonicalFinsetList_toFinset, canonicalFinsetList_toFinset] at this
    rw [this]
    exact hmem

end Kolmogorov
