import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift

/-!
# The partition-intersection step in the hereditary construction

This file implements the `M → M₁` counting and total-selection step from the
proof of VS40 Theorem `thm:hereditary`.  The selector is deliberately total on
every context: its ordinary partition program is run at the fixed empty
context, and all subsequent decoding, filtering, and indexing is computable
post-processing of the varying finite-set context.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

private lemma finiteSetLogCard_inter_le
    (A M : Finset BitString) :
    finiteSetLogCard (A ∩ M) ≤ finiteSetLogCard A := by
  rw [finiteSetLogCard_le_iff]
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (finiteSetLogCard_spec A)

private lemma pow_pred_le_card_of_nonempty_logCard_le
    (S : Finset BitString) (hS : S.Nonempty) (r : Nat)
    (hr : r ≤ finiteSetLogCard S) :
    2 ^ (r - 1) ≤ S.card := by
  by_cases hr0 : r = 0
  · subst hr0
    simpa using hS.card_pos
  · have hcard : 1 < S.card := by
      by_contra h
      have hcardOne : S.card = 1 :=
        Nat.le_antisymm (Nat.le_of_not_gt h) hS.card_pos
      have hlogZero : finiteSetLogCard S = 0 := by
        unfold finiteSetLogCard
        rw [hcardOne]
        decide
      omega
    have hsub : r - 1 ≤ finiteSetLogCard S - 1 :=
      Nat.sub_le_sub_right hr 1
    exact ((Nat.pow_le_pow_right (by decide) hsub).trans_lt
      (finiteSetLogCard_pred_lt S hcard)).le

/-- The number of partition members having a nonempty intersection with `A`
whose ceiling log-cardinality is at least `r` is bounded by the disjointness
count. -/
theorem partitionLargeIntersections_card_le
    (A : Finset BitString) (P : Finset (Finset BitString))
    (hP : IsPartition P) (r : Nat) :
    (P.filter fun M => (A ∩ M).Nonempty ∧
      r ≤ finiteSetLogCard (A ∩ M)).card
      ≤ 2 ^ (finiteSetLogCard A - r + 1) := by
  let F := P.filter fun M => (A ∩ M).Nonempty ∧
    r ≤ finiteSetLogCard (A ∩ M)
  by_cases hr : r ≤ finiteSetLogCard A
  · have hdisj : (F : Set (Finset BitString)).PairwiseDisjoint
        (fun M => A ∩ M) := by
      intro M hMF N hNF hMN
      rw [Finset.mem_coe, Finset.mem_filter] at hMF hNF
      exact (hP M hMF.1 N hNF.1 hMN).mono
        Finset.inter_subset_right Finset.inter_subset_right
    have hsum : F.card * 2 ^ (r - 1) ≤
        ∑ M ∈ F, (A ∩ M).card := by
      simpa [nsmul_eq_mul] using
        Finset.card_nsmul_le_sum F (fun M => (A ∩ M).card)
          (2 ^ (r - 1)) (fun M hMF => by
            rw [Finset.mem_filter] at hMF
            exact pow_pred_le_card_of_nonempty_logCard_le
              (A ∩ M) hMF.2.1 r hMF.2.2)
    have hUnionSubset : F.biUnion (fun M => A ∩ M) ⊆ A := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      exact (Finset.mem_inter.mp hx.choose_spec.2).1
    have hsumA : (∑ M ∈ F, (A ∩ M).card) ≤ A.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card hUnionSubset
    have hmul : F.card * 2 ^ (r - 1) ≤ 2 ^ finiteSetLogCard A :=
      hsum.trans (hsumA.trans (finiteSetLogCard_spec A))
    by_cases hr0 : r = 0
    · subst hr0
      have hbase : F.card ≤ 2 ^ finiteSetLogCard A := by
        simpa using hmul
      simpa [F] using
        hbase.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    · have hexp : finiteSetLogCard A =
          (finiteSetLogCard A - r + 1) + (r - 1) := by omega
      rw [hexp, pow_add] at hmul
      simpa [F] using
        Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)
  · have hFempty : F = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨M, hMF⟩
      rw [Finset.mem_filter] at hMF
      exact hr (hMF.2.2.trans (finiteSetLogCard_inter_le A M))
    simp [F, hFempty]

/-! ### Executable filtered enumeration -/

/-- Intersection of the two decoded canonical point lists, kept as a list in
the order of the first code. -/
noncomputable def partitionIntersectionPointList
    (Acode Mcode : BitString) : List BitString :=
  (canonicalPointListOfCode Acode).filter
    (fun x => decide (x ∈ canonicalPointListOfCode Mcode))

theorem partitionIntersectionPointList_primrec :
    Primrec₂ partitionIntersectionPointList := by
  unfold partitionIntersectionPointList
  refine list_filter_primrec
    (canonicalPointListOfCode_primrec.comp Primrec.fst) ?_
  have hpred : Primrec₂
      (fun (input : BitString × BitString) (x : BitString) =>
        decide (x ∈ canonicalPointListOfCode input.2)) := by
    have hx : Primrec
        (fun q : (BitString × BitString) × BitString => q.2) :=
      Primrec.snd
    have hm : Primrec
        (fun q : (BitString × BitString) × BitString => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    exact (bitString_mem_primrec.comp hx
      (canonicalPointListOfCode_primrec.comp hm)).to₂
  exact hpred

/-- Boolean form of `0 < m ∧ r ≤ Nat.clog 2 m`, expressed without computing
`Nat.clog`. -/
def largeIntersectionBool (m r : Nat) : Bool :=
  decide (0 < m ∧ (r = 0 ∨ 2 ^ (r - 1) < m))

theorem largeIntersectionBool_iff (m r : Nat) :
    largeIntersectionBool m r = true ↔
      0 < m ∧ r ≤ Nat.clog 2 m := by
  unfold largeIntersectionBool
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hr0 | hpow⟩
    · subst hr0
      exact ⟨hm, Nat.zero_le _⟩
    · exact ⟨hm, by
        have := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hpow
        omega⟩
  · rintro ⟨hm, hr⟩
    by_cases hr0 : r = 0
    · exact ⟨hm, Or.inl hr0⟩
    · refine ⟨hm, Or.inr ?_⟩
      exact (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)

theorem largeIntersectionBool_primrec :
    Primrec₂ largeIntersectionBool := by
  have h : PrimrecPred (fun p : Nat × Nat =>
      0 < p.1 ∧ (p.2 = 0 ∨ 2 ^ (p.2 - 1) < p.1)) :=
    PrimrecPred.and
      (Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst)
      (PrimrecPred.or
        (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.nat_lt.comp
          (twoPow_primrec.comp
            (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
          Primrec.fst))
  exact h.decide

/-- Canonical member codes of the decoded partition whose decoded sets have a
large nonempty intersection with the decoded context set. -/
noncomputable def partitionIntersectionCandidates
    (input : (BitString × BitString) × Nat) : List BitString :=
  (canonicalPointListOfCode input.1.1).filter fun Mcode =>
    largeIntersectionBool
      (partitionIntersectionPointList input.1.2 Mcode).length input.2

theorem partitionIntersectionCandidates_primrec :
    Primrec partitionIntersectionCandidates := by
  unfold partitionIntersectionCandidates
  refine list_filter_primrec
    (canonicalPointListOfCode_primrec.comp
      (Primrec.fst.comp Primrec.fst)) ?_
  exact largeIntersectionBool_primrec.comp
    (Primrec.list_length.comp
      (partitionIntersectionPointList_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd))
    (Primrec.snd.comp Primrec.fst)

theorem partitionIntersectionPointList_toFinset
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty) :
    (partitionIntersectionPointList (codedUniformOn A hA).code
      (codedUniformOn M hM).code).toFinset = A ∩ M := by
  ext x
  simp [partitionIntersectionPointList,
    canonicalPointListOfCode_codedUniformOn, mem_canonicalFinsetList]

private theorem partitionIntersectionPointList_canonical_toFinset
    (A M : Finset BitString) (hA : A.Nonempty) :
    (partitionIntersectionPointList (codedUniformOn A hA).code
      (canonicalFiniteSetCode M)).toFinset = A ∩ M := by
  ext x
  simp [partitionIntersectionPointList,
    canonicalPointListOfCode_codedUniformOn,
    canonicalPointListOfCode_canonicalFiniteSetCode,
    mem_canonicalFinsetList]

private theorem partitionIntersectionPointList_nodup
    (Acode Mcode : BitString) :
    (partitionIntersectionPointList Acode Mcode).Nodup :=
  (canonicalPointListOfCode_nodup Acode).filter _

private theorem canonicalFiniteSetCode_injective :
    Function.Injective canonicalFiniteSetCode := by
  intro A B h
  have h' := congrArg canonicalPointListOfCode h
  rw [canonicalPointListOfCode_canonicalFiniteSetCode,
    canonicalPointListOfCode_canonicalFiniteSetCode] at h'
  rw [← canonicalFinsetList_toFinset A,
    ← canonicalFinsetList_toFinset B, h']

theorem mem_partitionIntersectionCandidates_iff
    (P : Finset (Finset BitString))
    (A M : Finset BitString) (hA : A.Nonempty)
    (r : Nat) :
    canonicalFiniteSetCode M ∈
        partitionIntersectionCandidates
          ((partitionCode P, (codedUniformOn A hA).code), r) ↔
      M ∈ P ∧ (A ∩ M).Nonempty ∧
        r ≤ finiteSetLogCard (A ∩ M) := by
  rw [partitionIntersectionCandidates, List.mem_filter]
  simp only
  have hPdecode : canonicalPointListOfCode (partitionCode P) =
      canonicalFinsetList (P.image canonicalFiniteSetCode) := by
    unfold partitionCode
    exact canonicalPointListOfCode_canonicalFiniteSetCode _
  rw [hPdecode, mem_canonicalFinsetList, largeIntersectionBool_iff]
  have hto := partitionIntersectionPointList_canonical_toFinset A M hA
  have hlen : (partitionIntersectionPointList (codedUniformOn A hA).code
      (canonicalFiniteSetCode M)).length = (A ∩ M).card := by
    rw [← hto, List.toFinset_card_of_nodup
      (partitionIntersectionPointList_nodup _ _)]
  rw [hlen]
  simp only [finiteSetLogCard]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨M', hM'P, hcode⟩, hpos, hlog⟩
    have hMM' : M = M' := by
      apply canonicalFiniteSetCode_injective
      exact hcode.symm
    subst M'
    exact ⟨hM'P, Finset.card_pos.mp hpos, hlog⟩
  · rintro ⟨hMP, hinter, hlog⟩
    exact ⟨⟨M, hMP, rfl⟩, hinter.card_pos, hlog⟩

theorem partitionIntersectionCandidates_length
    (P : Finset (Finset BitString)) (A : Finset BitString)
    (hA : A.Nonempty) (r : Nat) :
    (partitionIntersectionCandidates
      ((partitionCode P, (codedUniformOn A hA).code), r)).length =
      (P.filter fun M => (A ∩ M).Nonempty ∧
        r ≤ finiteSetLogCard (A ∩ M)).card := by
  let F := P.filter fun M => (A ∩ M).Nonempty ∧
    r ≤ finiteSetLogCard (A ∩ M)
  have himage : (partitionIntersectionCandidates
      ((partitionCode P, (codedUniformOn A hA).code), r)).toFinset =
      F.image canonicalFiniteSetCode := by
    ext w
    constructor
    · intro hw
      rw [List.mem_toFinset] at hw
      rw [partitionIntersectionCandidates, List.mem_filter] at hw
      simp only at hw
      have hPdecode : canonicalPointListOfCode (partitionCode P) =
          canonicalFinsetList (P.image canonicalFiniteSetCode) := by
        unfold partitionCode
        exact canonicalPointListOfCode_canonicalFiniteSetCode _
      rw [hPdecode, mem_canonicalFinsetList] at hw
      obtain ⟨M, hMP, hcode⟩ := Finset.mem_image.mp hw.1
      subst w
      rw [Finset.mem_image]
      refine ⟨M, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact (mem_partitionIntersectionCandidates_iff P A M hA r).mp
        (by simpa [partitionIntersectionCandidates, hPdecode] using hw)
    · intro hw
      obtain ⟨M, hMF, rfl⟩ := Finset.mem_image.mp hw
      rw [List.mem_toFinset]
      exact (mem_partitionIntersectionCandidates_iff P A M hA r).mpr
        (by simpa [F] using hMF)
  have hnodup : (partitionIntersectionCandidates
      ((partitionCode P, (codedUniformOn A hA).code), r)).Nodup :=
    (canonicalPointListOfCode_nodup (partitionCode P)).filter _
  rw [← List.toFinset_card_of_nodup hnodup, himage,
    Finset.card_image_of_injective _ canonicalFiniteSetCode_injective]

/-! ### Total selector -/

noncomputable def partitionIntersectionSelectorPostFn
    (input : BitString × BitString) (Pcode : BitString) : BitString :=
  let params := decodeTotalProgramPairSecond input.1
  let r := decodeBits (decodeTotalProgramPairFirst params)
  let idx := bitsToNat (decodeTotalProgramPairSecond params)
  (partitionIntersectionCandidates ((Pcode, input.2), r)).getD idx
    (canonicalFiniteSetCode ∅)

theorem partitionIntersectionSelectorPostFn_computable :
    Computable₂ partitionIntersectionSelectorPostFn := by
  unfold partitionIntersectionSelectorPostFn
  have hcand : Computable
      (fun q : (BitString × BitString) × BitString =>
        partitionIntersectionCandidates
          ((q.2, q.1.2), decodeBits
            (decodeTotalProgramPairFirst
              (decodeTotalProgramPairSecond q.1.1)))) :=
    partitionIntersectionCandidates_primrec.to_comp.comp
      ((Computable.snd.pair (Computable.snd.comp Computable.fst)).pair
        (decodeBitsComputable.comp
          (decodeTotalProgramPairFirst_computable.comp
            (decodeTotalProgramPairSecond_computable.comp
              (Computable.fst.comp Computable.fst)))))
  have hidx : Computable
      (fun q : (BitString × BitString) × BitString =>
        bitsToNat (decodeTotalProgramPairSecond
          (decodeTotalProgramPairSecond q.1.1))) :=
    bitsToNat_primrec.to_comp.comp
      (decodeTotalProgramPairSecond_computable.comp
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst)))
  exact (Primrec.list_getD (canonicalFiniteSetCode ∅)).to_comp.comp
    hcand hidx

/-- Run an ordinary description of a partition at empty context, then select a
large-intersection member by threshold and fixed-width ordinal. -/
noncomputable def partitionIntersectionSelector (V : Map) : Map := fun input =>
  (V (decodeTotalProgramPairFirst input.1, [])).map
    (partitionIntersectionSelectorPostFn input)

theorem partitionIntersectionSelector_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (partitionIntersectionSelector V) := by
  unfold partitionIntersectionSelector
  exact Partrec.map
    (Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        (Computable.const [])))
    partitionIntersectionSelectorPostFn_computable

theorem partitionIntersectionSelector_total
    {V : Map} {q Pcode params : BitString}
    (hq : produces V q [] Pcode) :
    IsTotalProgram (partitionIntersectionSelector V)
      (totalProgramPairCode q params) := by
  intro Acode
  unfold partitionIntersectionSelector
  rw [decodeTotalProgramPairFirst_pair, Part.dom_iff_mem]
  exact ⟨partitionIntersectionSelectorPostFn
      (totalProgramPairCode q params, Acode) Pcode,
    (Part.mem_map_iff _).2 ⟨Pcode, hq, rfl⟩⟩

theorem partitionIntersectionSelector_produces
    {V : Map} {q : BitString}
    (P : Finset (Finset BitString))
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty)
    (r : Nat) (hq : produces V q [] (partitionCode P))
    (hMP : M ∈ P) (hinter : (A ∩ M).Nonempty)
    (hr : r ≤ finiteSetLogCard (A ∩ M)) :
    let F := partitionIntersectionCandidates
      ((partitionCode P, (codedUniformOn A hA).code), r)
    let idx := F.findIdx (· == canonicalFiniteSetCode M)
    ∀ s, idx < 2 ^ s →
      produces (partitionIntersectionSelector V)
        (totalProgramPairCode q
          (totalProgramPairCode (Nat.bits r) (chunkAddress idx s)))
        (codedUniformOn A hA).code (codedUniformOn M hM).code := by
  intro F idx s hidx
  have hmem : canonicalFiniteSetCode M ∈ F :=
    (mem_partitionIntersectionCandidates_iff P A M hA r).mpr
      ⟨hMP, hinter, hr⟩
  have hidxLen : idx < F.length := by
    dsimp [idx]
    rw [List.findIdx_lt_length]
    exact ⟨canonicalFiniteSetCode M, hmem, by simp⟩
  have hget : F.getD idx (canonicalFiniteSetCode ∅) =
      canonicalFiniteSetCode M := by
    rw [List.getD_eq_getElem F _ hidxLen]
    exact eq_of_beq (List.findIdx_getElem
      (p := (· == canonicalFiniteSetCode M)) (w := hidxLen))
  unfold produces partitionIntersectionSelector
  rw [decodeTotalProgramPairFirst_pair]
  apply (Part.mem_map_iff _).2
  refine ⟨partitionCode P, hq, ?_⟩
  unfold partitionIntersectionSelectorPostFn
  simp only [decodeTotalProgramPairSecond_pair,
    decodeTotalProgramPairFirst_pair, decodeBits_natBits,
    bitsToNat_chunkAddress]
  rw [hget]
  exact canonicalUniformCodeOfList_canonicalFinsetList M hM

/-- A simple partition member is total-computable from any set having a large
intersection with it. -/
theorem partition_member_totalCondK_of_intersection (V T : Map)
    (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ P M (hM : M.Nonempty) A (hA : A.Nonempty) (p N : Nat),
      IsPartition P → M ∈ P → (A ∩ M).Nonempty →
      partitionComplexity V P ≤ (p : ENat) → finiteSetLogCard A ≤ N →
      totalCondK T (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤
        (c * p + (finiteSetLogCard A - finiteSetLogCard (A ∩ M)) +
          logSlack c N : ENat) := by
  obtain ⟨cSim, hSim⟩ := hT.2 (partitionIntersectionSelector V)
    (partitionIntersectionSelector_partrec V hV.1)
  let c := cSim + 10
  refine ⟨c, ?_⟩
  intro P M hM A hA p N hPart hMP hinter hPcomp hAN
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condKLeIff V (partitionCode P) [] p).mp hPcomp
  change q.length ≤ p at hqLen
  let r := finiteSetLogCard (A ∩ M)
  let F := partitionIntersectionCandidates
    ((partitionCode P, (codedUniformOn A hA).code), r)
  let idx := F.findIdx (· == canonicalFiniteSetCode M)
  let s := finiteSetLogCard A - r + 1
  have hidxLen : idx < F.length := by
    dsimp [idx, F]
    rw [List.findIdx_lt_length]
    exact ⟨canonicalFiniteSetCode M,
      (mem_partitionIntersectionCandidates_iff P A M hA r).mpr
        ⟨hMP, hinter, le_rfl⟩, by simp⟩
  have hFcard : F.length ≤ 2 ^ s := by
    dsimp [F, s]
    rw [partitionIntersectionCandidates_length P A hA r]
    exact partitionLargeIntersections_card_le A P hPart r
  have hidxPow : idx < 2 ^ s := hidxLen.trans_le hFcard
  let z := chunkAddress idx s
  let params := totalProgramPairCode (Nat.bits r) z
  let w := totalProgramPairCode q params
  have hzLen : z.length = s := chunkAddress_length idx s hidxPow
  have hwTotal : IsTotalProgram (partitionIntersectionSelector V) w :=
    partitionIntersectionSelector_total hqProd
  have hwProd : produces (partitionIntersectionSelector V) w
      (codedUniformOn A hA).code (codedUniformOn M hM).code := by
    exact partitionIntersectionSelector_produces P A M hA hM r hqProd
      hMP hinter le_rfl s hidxPow
  have hrN : r ≤ N :=
    (finiteSetLogCard_inter_le A M).trans hAN
  have hqBits : (Nat.bits q.length).length ≤ q.length :=
    length_natBits_le q.length
  have hrBits : (Nat.bits r).length ≤ (Nat.bits N).length :=
    length_natBits_mono hrN
  have hrBitsBits : (Nat.bits (Nat.bits r).length).length ≤
      (Nat.bits r).length := length_natBits_le _
  have hwLen : w.length = q.length +
      ((Nat.bits r).length + s +
        2 * (Nat.bits (Nat.bits r).length).length + 1) +
      2 * (Nat.bits q.length).length + 1 := by
    dsimp [w, params]
    rw [length_totalProgramPairCode, length_totalProgramPairCode, hzLen]
  have hframe : w.length + cSim ≤
      c * p + (finiteSetLogCard A - r) + logSlack c N := by
    rw [hwLen]
    dsimp [s, c]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits N).length)]
  calc
    totalCondK T (codedUniformOn M hM).code (codedUniformOn A hA).code
        ≤ totalCondK (partitionIntersectionSelector V)
            (codedUniformOn M hM).code (codedUniformOn A hA).code +
              (cSim : ENat) := hSim _ _
    _ ≤ (w.length : ENat) + (cSim : ENat) := by
      gcongr
      exact totalCondK_le_programLength hwTotal hwProd
    _ ≤ ((c * p + (finiteSetLogCard A - r) + logSlack c N : Nat) : ENat) := by
      exact_mod_cast hframe
    _ = (c * p + (finiteSetLogCard A - finiteSetLogCard (A ∩ M)) +
        logSlack c N : Nat) := rfl

/-! ### The filtered family used in the next hereditary step -/

/-- Canonical codes of the partition members whose intersections with `M` are
nonempty and have ceiling log-cardinality at least `r`. -/
noncomputable def hereditaryFamily
    (P : Finset (Finset BitString)) (M : Finset BitString) (r : Nat) :
    Finset BitString :=
  (P.filter fun A => (A ∩ M).Nonempty ∧
    r ≤ finiteSetLogCard (A ∩ M)).image canonicalFiniteSetCode

/-- The distinguished partition member belongs to the filtered family at its
own intersection threshold. -/
theorem hereditaryFamily_mem_code
    (P : Finset (Finset BitString)) (A M : Finset BitString)
    (hA : A.Nonempty) (hAP : A ∈ P) (hinter : (A ∩ M).Nonempty) :
    (codedUniformOn A hA).code ∈
      hereditaryFamily P M (finiteSetLogCard (A ∩ M)) := by
  have hcode : canonicalFiniteSetCode A = (codedUniformOn A hA).code :=
    canonicalUniformCodeOfList_canonicalFinsetList A hA
  rw [← hcode, hereditaryFamily, Finset.mem_image]
  exact ⟨A, by simp [hAP, hinter], rfl⟩

/-- The filtered-family count is the source's disjoint-intersection estimate,
stated in the logarithmic form needed by the `M₁ → F` construction. -/
theorem hereditaryFamily_card_add_intersection_le
    (P : Finset (Finset BitString)) (A M : Finset BitString)
    (hP : IsPartition P) :
    finiteSetLogCard
        (hereditaryFamily P M (finiteSetLogCard (A ∩ M))) +
      finiteSetLogCard (A ∩ M) ≤ finiteSetLogCard M + 2 := by
  let r := finiteSetLogCard (A ∩ M)
  have hrM : r ≤ finiteSetLogCard M := by
    dsimp [r]
    rw [finiteSetLogCard_le_iff]
    exact (Finset.card_le_card Finset.inter_subset_right).trans
      (finiteSetLogCard_spec M)
  have hcard : (hereditaryFamily P M r).card ≤
      2 ^ (finiteSetLogCard M - r + 1) := by
    unfold hereditaryFamily
    rw [Finset.card_image_of_injective _ canonicalFiniteSetCode_injective]
    simpa [Finset.inter_comm] using
      partitionLargeIntersections_card_le M P hP r
  have hlog : finiteSetLogCard (hereditaryFamily P M r) ≤
      finiteSetLogCard M - r + 1 :=
    (finiteSetLogCard_le_iff _ _).mpr hcard
  dsimp [r] at hlog ⊢
  omega

/-- The executable filtered enumeration represents `hereditaryFamily`
extensionally on canonical inputs. -/
theorem partitionIntersectionCandidates_toFinset_eq_hereditaryFamily
    (P : Finset (Finset BitString)) (M : Finset BitString)
    (hM : M.Nonempty) (r : Nat) :
    (partitionIntersectionCandidates
      ((partitionCode P, (codedUniformOn M hM).code), r)).toFinset =
      hereditaryFamily P M r := by
  ext w
  constructor
  · intro hw
    rw [List.mem_toFinset, partitionIntersectionCandidates,
      List.mem_filter] at hw
    simp only at hw
    have hPdecode : canonicalPointListOfCode (partitionCode P) =
        canonicalFinsetList (P.image canonicalFiniteSetCode) := by
      unfold partitionCode
      exact canonicalPointListOfCode_canonicalFiniteSetCode _
    rw [hPdecode, mem_canonicalFinsetList] at hw
    obtain ⟨A, hAP, rfl⟩ := Finset.mem_image.mp hw.1
    rw [hereditaryFamily, Finset.mem_image]
    refine ⟨A, ?_, rfl⟩
    rw [Finset.mem_filter]
    have hcand := (mem_partitionIntersectionCandidates_iff P M A hM r).mp
      (by simpa [partitionIntersectionCandidates, hPdecode] using hw)
    simpa [Finset.inter_comm] using hcand
  · intro hw
    obtain ⟨A, hAF, rfl⟩ := by
      simpa [hereditaryFamily] using hw
    rw [List.mem_toFinset]
    exact (mem_partitionIntersectionCandidates_iff P M A hM r).mpr
      (by simpa [Finset.inter_comm] using hAF)

/-- Canonical code of the executable filtered family. -/
noncomputable def hereditaryFamilyCode
    (input : (BitString × BitString) × Nat) : BitString :=
  canonicalImageCodeOfList (partitionIntersectionCandidates input)

theorem hereditaryFamilyCode_computable :
    Computable hereditaryFamilyCode :=
  (canonicalImageCodeOfList_primrec.comp
    partitionIntersectionCandidates_primrec).to_comp

/-- On canonical inputs, the executable family code is exactly the canonical
uniform-set code of `hereditaryFamily`. -/
theorem hereditaryFamilyCode_eq
    (P : Finset (Finset BitString)) (M : Finset BitString)
    (hM : M.Nonempty) (r : Nat) (hF : (hereditaryFamily P M r).Nonempty) :
    hereditaryFamilyCode
        ((partitionCode P, (codedUniformOn M hM).code), r) =
      (codedUniformOn (hereditaryFamily P M r) hF).code := by
  let L := partitionIntersectionCandidates
    ((partitionCode P, (codedUniformOn M hM).code), r)
  have hLF : L.toFinset = hereditaryFamily P M r :=
    partitionIntersectionCandidates_toFinset_eq_hereditaryFamily
      P M hM r
  have hL : L.toFinset.Nonempty := hLF.symm ▸ hF
  unfold hereditaryFamilyCode
  change canonicalImageCodeOfList L = _
  rw [canonicalImageCodeOfList_eq_codedUniformOn L hL]
  exact codedUniformOn_code_congr hL hF hLF

/-! ### Coefficient-one plain-complexity bound -/

/-- The partition program and threshold are framed in a prefix, while the
shortest program for `M` is left as the suffix. -/
noncomputable def hereditaryFamilyPlainDecompressor (V : Map) : Map :=
  fun input =>
    let params := decodeTotalProgramPairSecond input.1
    (V (decodeSecond params, [])).bind fun Mcode =>
      (V (decodeTotalProgramPairFirst input.1, [])).map fun Pcode =>
        hereditaryFamilyCode
          ((Pcode, Mcode), bitsToNat (decodeFirst params))

theorem hereditaryFamilyPlainDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (hereditaryFamilyPlainDecompressor V) := by
  have hrunM : Partrec (fun input : BitString × BitString =>
      V (decodeSecond (decodeTotalProgramPairSecond input.1), [])) :=
    Partrec.comp hV
      (Computable.pair
        (decodeSecond_computable.comp
          (decodeTotalProgramPairSecond_computable.comp Computable.fst))
        (Computable.const []))
  have hrunP : Partrec (fun q : (BitString × BitString) × BitString =>
      V (decodeTotalProgramPairFirst q.1.1, [])) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp
          (Computable.fst.comp Computable.fst))
        (Computable.const []))
  have hpost : Computable
      (fun q : ((BitString × BitString) × BitString) × BitString =>
        hereditaryFamilyCode
          ((q.2, q.1.2), bitsToNat
            (decodeFirst (decodeTotalProgramPairSecond q.1.1.1)))) :=
    hereditaryFamilyCode_computable.comp
      ((Computable.snd.pair (Computable.snd.comp Computable.fst)).pair
        (bitsToNat_computable.comp
          (decodeFirst_computable.comp
            (decodeTotalProgramPairSecond_computable.comp
              (Computable.fst.comp
                (Computable.fst.comp Computable.fst))))))
  unfold hereditaryFamilyPlainDecompressor
  exact Partrec.bind hrunM (Partrec.map hrunP hpost)

theorem hereditaryFamilyPlainDecompressor_produces
    {V : Map} {q m Pcode Mcode : BitString} {r : Nat}
    (hP : produces V q [] Pcode) (hM : produces V m [] Mcode) :
    produces (hereditaryFamilyPlainDecompressor V)
      (totalProgramPairCode q (pairCode (Nat.bits r) m)) []
      (hereditaryFamilyCode ((Pcode, Mcode), r)) := by
  unfold produces hereditaryFamilyPlainDecompressor
  simp only [decodeTotalProgramPairSecond_pair, decodeSecond_pairCode,
    decodeTotalProgramPairFirst_pair, decodeFirst_pairCode, bitsToNat_bits]
  rw [Part.mem_bind_iff]
  refine ⟨Mcode, hM, ?_⟩
  exact (Part.mem_map_iff _).2 ⟨Pcode, hP, rfl⟩

/-- Generic coefficient-one code bound.  No self-delimiting framing is charged
to the shortest `M` program. -/
theorem plainK_hereditaryFamilyCode_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ q Pcode Mcode r,
      produces V q [] Pcode →
      plainK V (hereditaryFamilyCode ((Pcode, Mcode), r)) ≤
        plainK V Mcode +
          (c * q.length + logSlack c r : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (hereditaryFamilyPlainDecompressor V)
    (hereditaryFamilyPlainDecompressor_partrec V hV.1)
  let c := cSim + 6
  refine ⟨c, ?_⟩
  intro q Pcode Mcode r hP
  let overhead := q.length + 2 * (Nat.bits q.length).length +
    2 * (Nat.bits r).length + 2
  have hbound : condK (hereditaryFamilyPlainDecompressor V)
      (hereditaryFamilyCode ((Pcode, Mcode), r)) [] ≤
      condK V Mcode [] + (overhead : ENat) := by
    apply sInfLeSInfAdd
    rintro len ⟨m, hm, rfl⟩
    let w := totalProgramPairCode q (pairCode (Nat.bits r) m)
    refine ⟨(w.length : ENat),
      ⟨w, hereditaryFamilyPlainDecompressor_produces hP hm, rfl⟩, ?_⟩
    have hw : w.length = m.length + overhead := by
      dsimp [w, overhead]
      rw [length_totalProgramPairCode, length_pairCode]
      omega
    exact_mod_cast le_of_eq hw
  have hqBits : (Nat.bits q.length).length ≤ q.length :=
    length_natBits_le _
  have hoverhead : overhead + cSim ≤
      c * q.length + logSlack c r := by
    dsimp [overhead, c]
    unfold logSlack
    nlinarith [Nat.zero_le (cSim * q.length),
      Nat.zero_le (cSim * (Nat.bits r).length)]
  calc
    plainK V (hereditaryFamilyCode ((Pcode, Mcode), r)) ≤
        condK (hereditaryFamilyPlainDecompressor V)
          (hereditaryFamilyCode ((Pcode, Mcode), r)) [] +
          (cSim : ENat) := hSim _ _
    _ ≤ (condK V Mcode [] + (overhead : ENat)) +
        (cSim : ENat) := by gcongr
    _ = plainK V Mcode + ((overhead + cSim : Nat) : ENat) := by
      rw [add_assoc]
      norm_cast
    _ ≤ plainK V Mcode +
        ((c * q.length + logSlack c r : Nat) : ENat) := by
      have hcast : ((overhead + cSim : Nat) : ENat) ≤
          ((c * q.length + logSlack c r : Nat) : ENat) := by
        exact_mod_cast hoverhead
      exact add_le_add_right hcast _
    _ = plainK V Mcode +
        (c * q.length + logSlack c r : ENat) := by norm_cast

/-- Plain-complexity half of the `M₁ → F` construction.  The coefficient of
`plainSetComplexity V M hM` is one; the partition program and the threshold
framing are charged separately. -/
theorem plainSetComplexity_hereditaryFamily_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ P M (hM : M.Nonempty) r
        (hF : (hereditaryFamily P M r).Nonempty) (p N : Nat),
      partitionComplexity V P ≤ (p : ENat) →
      r ≤ N →
      plainSetComplexity V (hereditaryFamily P M r) hF ≤
        plainSetComplexity V M hM +
          (c * p + logSlack c N : ENat) := by
  obtain ⟨c, hc⟩ := plainK_hereditaryFamilyCode_le V hV
  refine ⟨c, ?_⟩
  intro P M hM r hF p N hPcomp hrN
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condKLeIff V (partitionCode P) [] p).mp hPcomp
  change q.length ≤ p at hqLen
  unfold plainSetComplexity
  rw [← hereditaryFamilyCode_eq P M hM r hF]
  refine (hc q (partitionCode P) (codedUniformOn M hM).code r hqProd).trans ?_
  gcongr
  exact_mod_cast logSlack_mono_right c hrN

/-! ### Total strongness transport -/

/-- Executable ceiling-log search.  The range `0, ..., m` contains
`Nat.clog 2 m`, and `clogEqBool` recognizes it uniquely. -/
def clogSearch (m : Nat) : Nat :=
  (List.range (m + 1)).findIdx (fun r => clogEqBool m r)

theorem clogSearch_primrec : Primrec clogSearch := by
  have hrange : Primrec (fun m : Nat => List.range (m + 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  exact Primrec.list_findIdx hrange clogEqBool_primrec

theorem clogSearch_eq (m : Nat) : clogSearch m = Nat.clog 2 m := by
  have hk : Nat.clog 2 m ≤ m :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hfind : clogSearch m < (List.range (m + 1)).length := by
    unfold clogSearch
    rw [List.findIdx_lt_length]
    exact ⟨Nat.clog 2 m, by simp [hk],
      (clogEqBool_iff m (Nat.clog 2 m)).2 rfl⟩
  have hget := List.findIdx_getElem
    (p := fun r => clogEqBool m r)
    (xs := List.range (m + 1)) (w := hfind)
  have hp : clogEqBool m (clogSearch m) = true := by
    simpa [clogSearch] using hget
  exact ((clogEqBool_iff m (clogSearch m)).1 hp).symm

/-- Ceiling log-cardinality of the intersection decoded from two canonical
finite-set codes. -/
noncomputable def intersectionLogFromCodes
    (Acode Mcode : BitString) : Nat :=
  clogSearch (partitionIntersectionPointList Acode Mcode).length

theorem intersectionLogFromCodes_primrec :
    Primrec₂ intersectionLogFromCodes :=
  clogSearch_primrec.comp
    (Primrec.list_length.comp partitionIntersectionPointList_primrec)

theorem intersectionLogFromCodes_eq
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty) :
    intersectionLogFromCodes (codedUniformOn A hA).code
      (codedUniformOn M hM).code = finiteSetLogCard (A ∩ M) := by
  unfold intersectionLogFromCodes finiteSetLogCard
  rw [clogSearch_eq, ← partitionIntersectionPointList_toFinset A M hA hM,
    List.toFinset_card_of_nodup
      (partitionIntersectionPointList_nodup _ _)]

/-- Run a total program for `M` on the varying context and an ordinary
partition program at empty context, then compute the filtered family. -/
noncomputable def hereditaryFamilyTotalDecompressor
    (V T : Map) : Map := fun input =>
  (T (decodeTotalProgramPairSecond input.1, input.2)).bind fun Mcode =>
    (V (decodeTotalProgramPairFirst input.1, [])).map fun Pcode =>
      hereditaryFamilyCode
        ((Pcode, Mcode), intersectionLogFromCodes input.2 Mcode)

theorem hereditaryFamilyTotalDecompressor_partrec
    (V T : Map) (hV : isDecompressor V) (hT : isDecompressor T) :
    isDecompressor (hereditaryFamilyTotalDecompressor V T) := by
  have hrunM : Partrec (fun input : BitString × BitString =>
      T (decodeTotalProgramPairSecond input.1, input.2)) :=
    Partrec.comp hT
      (Computable.pair
        (decodeTotalProgramPairSecond_computable.comp Computable.fst)
        Computable.snd)
  have hrunP : Partrec (fun q : (BitString × BitString) × BitString =>
      V (decodeTotalProgramPairFirst q.1.1, [])) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp
          (Computable.fst.comp Computable.fst))
        (Computable.const []))
  have hpost : Computable
      (fun q : ((BitString × BitString) × BitString) × BitString =>
        hereditaryFamilyCode
          ((q.2, q.1.2), intersectionLogFromCodes q.1.1.2 q.1.2)) :=
    hereditaryFamilyCode_computable.comp
      ((Computable.snd.pair (Computable.snd.comp Computable.fst)).pair
        (intersectionLogFromCodes_primrec.to_comp.comp
          (Computable.snd.comp
            (Computable.fst.comp Computable.fst))
          (Computable.snd.comp Computable.fst)))
  unfold hereditaryFamilyTotalDecompressor
  exact Partrec.bind hrunM (Partrec.map hrunP hpost)

theorem hereditaryFamilyTotalDecompressor_total
    {V T : Map} {q t Pcode : BitString}
    (hP : produces V q [] Pcode) (ht : IsTotalProgram T t) :
    IsTotalProgram (hereditaryFamilyTotalDecompressor V T)
      (totalProgramPairCode q t) := by
  intro Acode
  rw [Part.dom_iff_mem]
  obtain ⟨Mcode, hM⟩ := Part.dom_iff_mem.mp (ht Acode)
  refine ⟨hereditaryFamilyCode
      ((Pcode, Mcode), intersectionLogFromCodes Acode Mcode), ?_⟩
  unfold hereditaryFamilyTotalDecompressor
  simp only [decodeTotalProgramPairSecond_pair,
    decodeTotalProgramPairFirst_pair]
  rw [Part.mem_bind_iff]
  exact ⟨Mcode, hM, (Part.mem_map_iff _).2 ⟨Pcode, hP, rfl⟩⟩

theorem hereditaryFamilyTotalDecompressor_produces
    {V T : Map} {q t Pcode : BitString}
    (P : Finset (Finset BitString))
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty)
    (hPcode : Pcode = partitionCode P)
    (hq : produces V q [] Pcode)
    (ht : produces T t (codedUniformOn A hA).code
      (codedUniformOn M hM).code) :
    produces (hereditaryFamilyTotalDecompressor V T)
      (totalProgramPairCode q t) (codedUniformOn A hA).code
      (hereditaryFamilyCode
        ((partitionCode P, (codedUniformOn M hM).code),
          finiteSetLogCard (A ∩ M))) := by
  unfold produces hereditaryFamilyTotalDecompressor
  simp only [decodeTotalProgramPairSecond_pair,
    decodeTotalProgramPairFirst_pair]
  rw [Part.mem_bind_iff]
  refine ⟨(codedUniformOn M hM).code, ht, ?_⟩
  apply (Part.mem_map_iff _).2
  refine ⟨Pcode, hq, ?_⟩
  rw [hPcode, intersectionLogFromCodes_eq A M hA hM]

/-- Total-complexity half of the `M₁ → F` construction.  A total program for
`M` from the canonical code of `A` is post-processed, on every context, into
the same filtered family construction. -/
theorem hereditaryFamily_isStrong
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ P A (hA : A.Nonempty) M (hM : M.Nonempty)
        (p s N : Nat)
        (hF : (hereditaryFamily P M
          (finiteSetLogCard (A ∩ M))).Nonempty),
      partitionComplexity V P ≤ (p : ENat) →
      totalCondK T (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤ (s : ENat) →
      IsStrongSetModel T (codedUniformOn A hA).code
        (hereditaryFamily P M (finiteSetLogCard (A ∩ M))) hF
        (c * (p + s) + logSlack c N) := by
  obtain ⟨cSim, hSim⟩ := hT.2
    (hereditaryFamilyTotalDecompressor V T)
    (hereditaryFamilyTotalDecompressor_partrec V T hV.1 hT.1)
  let c := cSim + 4
  refine ⟨c, ?_⟩
  intro P A hA M hM p s N hF hPcomp hMA
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condKLeIff V (partitionCode P) [] p).mp hPcomp
  change q.length ≤ p at hqLen
  obtain ⟨t, htTotal, htLen, htProd⟩ :=
    (totalCondK_le_iff T (codedUniformOn M hM).code
      (codedUniformOn A hA).code s).mp hMA
  let w := totalProgramPairCode q t
  have hwTotal : IsTotalProgram
      (hereditaryFamilyTotalDecompressor V T) w :=
    hereditaryFamilyTotalDecompressor_total hqProd htTotal
  have hwProd : produces (hereditaryFamilyTotalDecompressor V T) w
      (codedUniformOn A hA).code
      (hereditaryFamilyCode
        ((partitionCode P, (codedUniformOn M hM).code),
          finiteSetLogCard (A ∩ M))) := by
    exact hereditaryFamilyTotalDecompressor_produces P A M hA hM rfl
      hqProd htProd
  have hqBits : (Nat.bits q.length).length ≤ q.length :=
    length_natBits_le _
  have hwLen : w.length =
      q.length + t.length + 2 * (Nat.bits q.length).length + 1 :=
    length_totalProgramPairCode q t
  have hframe : w.length + cSim ≤
      c * (p + s) + logSlack c N := by
    rw [hwLen]
    dsimp [c]
    unfold logSlack
    nlinarith [Nat.zero_le (cSim * (p + s)),
      Nat.zero_le ((cSim + 4) * (Nat.bits N).length)]
  unfold IsStrongSetModel
  rw [← hereditaryFamilyCode_eq P M hM
    (finiteSetLogCard (A ∩ M)) hF]
  calc
    totalCondK T
        (hereditaryFamilyCode
          ((partitionCode P, (codedUniformOn M hM).code),
            finiteSetLogCard (A ∩ M)))
        (codedUniformOn A hA).code ≤
      totalCondK (hereditaryFamilyTotalDecompressor V T)
          (hereditaryFamilyCode
            ((partitionCode P, (codedUniformOn M hM).code),
              finiteSetLogCard (A ∩ M)))
          (codedUniformOn A hA).code + (cSim : ENat) := hSim _ _
    _ ≤ (w.length : ENat) + (cSim : ENat) := by
      gcongr
      exact totalCondK_le_programLength hwTotal hwProd
    _ ≤ ((c * (p + s) + logSlack c N : Nat) : ENat) := by
      exact_mod_cast hframe

/-- Exact public target for the `M₁ → F` part of the proof of VS40 Theorem
`thm:hereditary`.  Unlike the preceding selector theorem, this additionally
constructs the family itself from `M` and proves that it is a strong model of
the canonical code of `A`. -/
theorem hereditary_family_model
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ P A (hA : A.Nonempty) M (hM : M.Nonempty)
        (p s N : Nat),
      IsPartition P →
      A ∈ P →
      (A ∩ M).Nonempty →
      partitionComplexity V P ≤ (p : ENat) →
      plainSetComplexity V M hM ≤ (N : ENat) →
      p + s + finiteSetLogCard A + finiteSetLogCard M ≤ N →
      totalCondK T (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤ (s : ENat) →
      ∃ F, ∃ hF : F.Nonempty,
        (codedUniformOn A hA).code ∈ F ∧
        IsStrongSetModel T (codedUniformOn A hA).code F hF
          (c * (p + s) + logSlack c N) ∧
        plainSetComplexity V F hF ≤
          plainSetComplexity V M hM +
            (c * p + logSlack c N : ENat) ∧
        finiteSetLogCard F + finiteSetLogCard (A ∩ M) ≤
          finiteSetLogCard M + 2 := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_hereditaryFamily_le V hV
  obtain ⟨cStrong, hStrong⟩ := hereditaryFamily_isStrong V T hV hT
  let c := cPlain + cStrong
  refine ⟨c, ?_⟩
  intro P A hA M hM p s N hPart hAP hinter hPcomp _hMcomp hbudget hMA
  let r := finiteSetLogCard (A ∩ M)
  let F := hereditaryFamily P M r
  have hmem : (codedUniformOn A hA).code ∈ F := by
    dsimp [F, r]
    exact hereditaryFamily_mem_code P A M hA hAP hinter
  have hF : F.Nonempty := ⟨(codedUniformOn A hA).code, hmem⟩
  refine ⟨F, hF, hmem, ?_, ?_, ?_⟩
  · have hs := hStrong P A hA M hM p s N hF hPcomp hMA
    exact hs.mono (by
      unfold c logSlack
      nlinarith [Nat.zero_le ((Nat.bits N).length)])
  · have hrN : r ≤ N := by
      have hrM : r ≤ finiteSetLogCard M := by
        dsimp [r]
        rw [finiteSetLogCard_le_iff]
        exact (Finset.card_le_card Finset.inter_subset_right).trans
          (finiteSetLogCard_spec M)
      omega
    refine (hPlain P M hM r hF p N hPcomp hrN).trans ?_
    gcongr
    · dsimp [c]
      omega
    · exact_mod_cast logSlack_mono_left (show cPlain ≤ c by
        dsimp [c]
        omega) N
  · dsimp [F, r]
    exact hereditaryFamily_card_add_intersection_le P A M hPart

/-- Sharp worker form of `hereditary_family_model`.  The total decoder's
framing depends only on the partition and total-reduction programs, so its
strength does not need a visible bound for `C(M)` or `log #M`.  The ordinary
decoder only encodes the intersection threshold, which is bounded by
`log #A`.  Keeping these two budgets separate is essential in the hereditary
assembly, where `M` may have a loose cardinality coordinate. -/
theorem hereditary_family_model_sharp
    (V T : Map)
    (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ P A (hA : A.Nonempty) M (hM : M.Nonempty) (p s : Nat),
      IsPartition P →
      A ∈ P →
      (A ∩ M).Nonempty →
      partitionComplexity V P ≤ (p : ENat) →
      totalCondK T (codedUniformOn M hM).code
          (codedUniformOn A hA).code ≤ (s : ENat) →
      ∃ F, ∃ hF : F.Nonempty,
        (codedUniformOn A hA).code ∈ F ∧
        IsStrongSetModel T (codedUniformOn A hA).code F hF
          (c * (p + s) + c) ∧
        plainSetComplexity V F hF ≤
          plainSetComplexity V M hM +
            (c * p + logSlack c (finiteSetLogCard A) : ENat) ∧
        finiteSetLogCard F + finiteSetLogCard (A ∩ M) ≤
          finiteSetLogCard M + 2 := by
  obtain ⟨cPlain, hPlain⟩ :=
    plainSetComplexity_hereditaryFamily_le V hV
  obtain ⟨cStrong, hStrong⟩ := hereditaryFamily_isStrong V T hV hT
  let c := cPlain + cStrong
  refine ⟨c, ?_⟩
  intro P A hA M hM p s hPart hAP hinter hPcomp hMA
  let r := finiteSetLogCard (A ∩ M)
  let F := hereditaryFamily P M r
  have hmem : (codedUniformOn A hA).code ∈ F := by
    dsimp [F, r]
    exact hereditaryFamily_mem_code P A M hA hAP hinter
  have hF : F.Nonempty := ⟨(codedUniformOn A hA).code, hmem⟩
  refine ⟨F, hF, hmem, ?_, ?_, ?_⟩
  · have hs := hStrong P A hA M hM p s 0 hF hPcomp hMA
    refine hs.mono ?_
    rw [show logSlack cStrong 0 = cStrong by simp [logSlack]]
    dsimp [c]
    nlinarith [Nat.zero_le (cPlain * (p + s))]
  · have hrA : r ≤ finiteSetLogCard A := by
      dsimp [r]
      rw [finiteSetLogCard_le_iff]
      exact (Finset.card_le_card Finset.inter_subset_left).trans
        (finiteSetLogCard_spec A)
    refine (hPlain P M hM r hF p (finiteSetLogCard A) hPcomp hrA).trans ?_
    gcongr
    · dsimp [c]
      omega
    · exact_mod_cast logSlack_mono_left (show cPlain ≤ c by
        dsimp [c]
        omega) (finiteSetLogCard A)
  · dsimp [F, r]
    exact hereditaryFamily_card_add_intersection_le P A M hPart

end Kolmogorov
