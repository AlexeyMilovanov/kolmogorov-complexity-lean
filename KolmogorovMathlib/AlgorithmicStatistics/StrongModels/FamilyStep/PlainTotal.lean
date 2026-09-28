import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.HereditaryLift
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.FamilyStep.Filtered

/-!
# From a strong model to a family: the total-complexity half

`hereditary_family_model` is the `M₁ → F` step in the proof of VS40 Theorem `thm:hereditary`:
from a strong model one builds a hereditary family whose members are total-computable at the
required budget.  `hereditaryFamily_isStrong` is its total-complexity half.

The construction intersects the model with the members of a partition.
`partitionLargeIntersections_card_le` counts the members whose intersection is large,
`partitionIntersectionCandidates` (with `mem_partitionIntersectionCandidates_iff` and
`partitionIntersectionCandidates_length`) enumerates their codes,
`partitionIntersectionSelector_produces` and `partition_member_totalCondK_of_intersection`
recover a partition member from any set with a large intersection, and
`hereditaryFamily_card_add_intersection_le` is the source's disjoint-intersection estimate.
`hereditaryFamilyTotalDecompressor`, with its `_partrec`, `_total` and `_produces` lemmas, is
the machine that makes the estimate a complexity bound.
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

/-- A canonical set code occurs among the candidates exactly when it codes a
partition member whose intersection with `A` is nonempty and of log-cardinality
at least `r`. -/
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

/-- The number of candidates equals the number of partition members meeting the two
conditions. -/
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

/-- Given a program for the partition code, the selector produces the code of any
prescribed partition member with a large enough intersection, from its index in
the candidate list. -/
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
    (condK_le_iff V (partitionCode P) [] p).mp hPcomp
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

/-- On canonical codes the executable log-cardinality is `finiteSetLogCard (A ∩ M)`. -/
theorem intersectionLogFromCodes_eq
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty) :
    intersectionLogFromCodes (codedUniformOn A hA).code
      (codedUniformOn M hM).code = finiteSetLogCard (A ∩ M) := by
  unfold intersectionLogFromCodes finiteSetLogCard
  rw [clogSearch_eq, ← partitionIntersectionPointList_toFinset A M hA hM,
    List.toFinset_card_of_nodup
      (partitionIntersectionPointList_nodup _ _)]

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
    (condK_le_iff V (partitionCode P) [] p).mp hPcomp
  change q.length ≤ p at hqLen
  unfold plainSetComplexity
  rw [← hereditaryFamilyCode_eq P M hM r hF]
  refine (hc q (partitionCode P) (codedUniformOn M hM).code r hqProd).trans ?_
  gcongr
  exact_mod_cast logSlack_mono_right c hrN

/-- Run a total program for `M` on the varying context and an ordinary
partition program at empty context, then compute the filtered family. -/
noncomputable def hereditaryFamilyTotalDecompressor
    (V T : Map) : Map := fun input =>
  (T (decodeTotalProgramPairSecond input.1, input.2)).bind fun Mcode =>
    (V (decodeTotalProgramPairFirst input.1, [])).map fun Pcode =>
      hereditaryFamilyCode
        ((Pcode, Mcode), intersectionLogFromCodes input.2 Mcode)

/-- The total-complexity decompressor for the filtered family is a decompressor. -/
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

/-- A program pairing a partition program with a total program is total in the
filtered-family decompressor. -/
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

/-- From a program for the partition code and a total program producing the code of
`M` on the condition `A`, the decompressor produces the code of the filtered
family at the threshold `finiteSetLogCard (A ∩ M)`. -/
theorem hereditaryFamilyTotalDecompressor_produces
    {V T : Map} {q t : BitString}
    (P : Finset (Finset BitString))
    (A M : Finset BitString) (hA : A.Nonempty) (hM : M.Nonempty)
    (hq : produces V q [] (partitionCode P))
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
  refine ⟨partitionCode P, hq, ?_⟩
  rw [intersectionLogFromCodes_eq A M hA hM]

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
    (condK_le_iff V (partitionCode P) [] p).mp hPcomp
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
    exact hereditaryFamilyTotalDecompressor_produces P A M hA hM
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

end Kolmogorov
