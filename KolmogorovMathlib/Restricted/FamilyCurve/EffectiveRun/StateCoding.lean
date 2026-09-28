import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRebuild
import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream
import KolmogorovMathlib.Foundation.UnboundedSearch
import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding

/-!
# Encodings for the effective restricted-family run

The sampled run is executed on bitstring codes. This module defines the code of a run state and
the primitive-recursive operations used by one transition: deleting a model, folding the live
codes, decoding cover cardinalities, testing density and finding the first failed scale.

It then packages the initial state, step input, step postprocessing, transition and iterated
process as partial recursive maps. The `*_primrec` and `*_partrec` theorems form the
computability interface used by `EffectiveRun.Computability`.

`restrictedSampledNewBadBatch` isolates the newly visible segment of the monotone bad stream.
-/



namespace Kolmogorov

open Nat.Partrec (Code)

/-- Code a root live pool together with the current sampled model codes. -/
def restrictedEffectiveSampledStateCode
    (rootLiveCode : BitString) (modelCodes : List BitString) : BitString :=
  listCode [rootLiveCode, listCode modelCodes]

/-- Coding a root live pool together with the sampled model codes is primitive recursive. -/
theorem restrictedEffectiveSampledStateCode_primrec :
    Primrec (fun p : BitString × List BitString =>
      restrictedEffectiveSampledStateCode p.1 p.2) := by
  unfold restrictedEffectiveSampledStateCode
  exact listCode_primrec.comp
    (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp (listCode_primrec.comp Primrec.snd)
        (Primrec.const [])))

/-- The zeroth field of a coded sampled state is the root live-pool code. -/
@[simp] lemma restrictedSelectorField_sampledState_zero
    (rootLiveCode : BitString) (modelCodes : List BitString) :
    restrictedSelectorField
      (restrictedEffectiveSampledStateCode rootLiveCode modelCodes) 0 =
        rootLiveCode := by
  unfold restrictedEffectiveSampledStateCode restrictedSelectorField
  rw [decodeListCode_listCode]
  rfl

/-- The first field of a coded sampled state decodes to the list of model codes. -/
@[simp] lemma restrictedSelectorField_sampledState_one
    (rootLiveCode : BitString) (modelCodes : List BitString) :
    decodeListCode (restrictedSelectorField
      (restrictedEffectiveSampledStateCode rootLiveCode modelCodes) 1) =
        modelCodes := by
  unfold restrictedEffectiveSampledStateCode restrictedSelectorField
  rw [decodeListCode_listCode]
  simp only [List.getD_cons_succ, List.getD_cons_zero,
    decodeListCode_listCode]

/-- Delete the points represented by `badCode` from the live pool represented
by `liveCode`, preserving the live list's canonical order. -/
noncomputable def restrictedEffectiveDeleteCode
    (liveCode badCode : BitString) : BitString :=
  canonicalUniformCodeOfList
    ((decodeCoverCodeList liveCode).filter
      (fun x => decide (x ∉ decodeCoverCodeList badCode))).dedup

/-- Deleting one code from a coded live pool is primitive recursive in both arguments. -/
theorem restrictedEffectiveDeleteCode_primrec :
    Primrec (fun p : BitString × BitString =>
      restrictedEffectiveDeleteCode p.1 p.2) := by
  unfold restrictedEffectiveDeleteCode
  apply canonicalUniformCodeOfList_primrec.comp
  apply dedup_primrec.comp
  apply list_filter_primrec
  · exact decodeCoverCodeList_primrec.comp Primrec.fst
  · have hmem : Primrec (fun q : (BitString × BitString) × BitString =>
        decide (q.2 ∈ decodeCoverCodeList q.1.2)) :=
      bitString_mem_primrec.comp Primrec.snd
        (decodeCoverCodeList_primrec.comp (Primrec.snd.comp Primrec.fst))
    have hnot : Primrec (fun q : (BitString × BitString) × BitString =>
        decide (q.2 ∉ decodeCoverCodeList q.1.2)) := by
      apply (Primrec.not.comp hmem).of_eq
      intro q
      simp
    exact hnot.to₂

/-- Tail-recursive accumulator used to expose the computability of the live
intersection trace.  Its reversed accumulator avoids appending at each step. -/
private noncomputable def restrictedEffectiveRebuildLiveFold
    (p : BitString × List BitString) : BitString × List BitString :=
  p.2.foldl (fun state Bcode =>
    (restrictedLiveIntersectionCode state.1 Bcode, state.1 :: state.2))
    (p.1, [])

private lemma restrictedEffectiveRebuildLiveFold_aux
    (Ccode : BitString) (codes acc : List BitString) :
    let final := codes.foldl (fun state Bcode =>
      (restrictedLiveIntersectionCode state.1 Bcode, state.1 :: state.2))
      (Ccode, acc)
    (final.1 :: final.2).reverse =
      acc.reverse ++ restrictedEffectiveRebuildLiveCodesFrom Ccode codes := by
  induction codes generalizing Ccode acc with
  | nil => simp [restrictedEffectiveRebuildLiveCodesFrom]
  | cons Bcode codes ih =>
      simp only [List.foldl_cons, restrictedEffectiveRebuildLiveCodesFrom]
      rw [ih (restrictedLiveIntersectionCode Ccode Bcode) (Ccode :: acc)]
      simp

private lemma restrictedEffectiveRebuildLiveFold_eq
    (Ccode : BitString) (codes : List BitString) :
    let final := restrictedEffectiveRebuildLiveFold (Ccode, codes)
    (final.1 :: final.2).reverse =
      restrictedEffectiveRebuildLiveCodesFrom Ccode codes := by
  simpa [restrictedEffectiveRebuildLiveFold] using
    restrictedEffectiveRebuildLiveFold_aux Ccode codes []

private theorem restrictedEffectiveRebuildLiveFold_primrec :
    Primrec restrictedEffectiveRebuildLiveFold := by
  unfold restrictedEffectiveRebuildLiveFold
  exact Primrec.list_foldl Primrec.snd
    (Primrec.pair Primrec.fst (Primrec.const []))
    (Primrec.pair
      (restrictedLiveIntersectionCode_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_cons.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).to₂

/-- The live-pool codes obtained by intersecting successively with the model codes are primitive
recursive in the starting pool and the models. -/
theorem restrictedEffectiveRebuildLiveCodesFrom_primrec :
    Primrec (fun p : BitString × List BitString =>
      restrictedEffectiveRebuildLiveCodesFrom p.1 p.2) := by
  have hout : Primrec (fun state : BitString × List BitString =>
      (state.1 :: state.2).reverse) :=
    Primrec.list_reverse.comp
      (Primrec.list_cons.comp Primrec.fst Primrec.snd)
  exact (hout.comp restrictedEffectiveRebuildLiveFold_primrec).of_eq (fun p =>
    restrictedEffectiveRebuildLiveFold_eq p.1 p.2)

/-- The rebuilt live-pool codes are primitive recursive in the starting pool and the codes. -/
theorem restrictedEffectiveRebuildLiveCodes_primrec :
    Primrec (fun p : BitString × List BitString =>
      restrictedEffectiveRebuildLiveCodes p.1 p.2) := by
  have hcons : Primrec₂ (fun (p : BitString × List BitString)
      (q : BitString × List BitString) =>
      restrictedEffectiveRebuildLiveCodesFrom p.1 q.2) :=
    (restrictedEffectiveRebuildLiveCodesFrom_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))).to₂
  refine (Primrec.list_casesOn Primrec.snd (Primrec.const []) hcons).of_eq ?_
  intro p
  cases p.2 <;> rfl

/-- Each rebuilt live pool is the intersection of the previous one with the next model. -/
lemma restrictedEffectiveRebuildLiveCodesFrom_succ_getD
    (Ccode : BitString) (models : List BitString)
    (i : ℕ) (hi : i < models.length) :
    (restrictedEffectiveRebuildLiveCodesFrom Ccode models).getD (i + 1) [] =
      restrictedLiveIntersectionCode
        ((restrictedEffectiveRebuildLiveCodesFrom Ccode models).getD i [])
        (models.getD i []) := by
  induction i generalizing Ccode models with
  | zero =>
      cases models with
      | nil => simp at hi
      | cons Bcode models =>
          cases models <;> simp [restrictedEffectiveRebuildLiveCodesFrom]
  | succ i ih =>
      cases models with
      | nil => simp at hi
      | cons Bcode models =>
          simpa [restrictedEffectiveRebuildLiveCodesFrom] using
            ih (restrictedLiveIntersectionCode Ccode Bcode) models
              (by simp at hi; omega)

/-- Each rebuilt live pool is the intersection of the previous one with the model of that index. -/
lemma restrictedEffectiveRebuildLiveCodes_succ_getD
    (Ccode : BitString) (codes : List BitString)
    (i : ℕ) (hi : i + 1 < codes.length) :
    (restrictedEffectiveRebuildLiveCodes Ccode codes).getD (i + 1) [] =
      restrictedLiveIntersectionCode
        ((restrictedEffectiveRebuildLiveCodes Ccode codes).getD i [])
        (codes.getD (i + 1) []) := by
  cases codes with
  | nil => simp at hi
  | cons Acode models =>
      simpa [restrictedEffectiveRebuildLiveCodes] using
        restrictedEffectiveRebuildLiveCodesFrom_succ_getD Ccode models i
          (by simp at hi; omega)

/-- A nonempty aligned live trace starts with its supplied root code. -/
lemma restrictedEffectiveRebuildLiveCodes_getD_zero
    (rootCode : BitString) (modelCodes : List BitString)
    (hne : modelCodes ≠ []) :
    (restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD 0 [] =
      rootCode := by
  cases modelCodes with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
      cases tail <;> rfl

/-- Requested live cardinalities at all `gridSteps + 1` sampled scales. -/
def restrictedEffectiveSampledSizes
    (gridCode : BitString) (gridSteps Δ : ℕ) : List ℕ :=
  (List.range (gridSteps + 1)).map (fun s =>
    2 ^ ((decodeRestrictedCurveGridCodeSample gridCode s).2 - (Δ + 1)))

/-- The sampled scales run over `gridSteps + 1` values. -/
@[simp] lemma restrictedEffectiveSampledSizes_length
    (gridCode : BitString) (gridSteps Δ : ℕ) :
    (restrictedEffectiveSampledSizes gridCode gridSteps Δ).length =
      gridSteps + 1 := by
  simp [restrictedEffectiveSampledSizes]

/-- The requested cardinality at scale `s` is `2 ^ (j_s - (Δ + 1))`, read off the coded grid. -/
lemma restrictedEffectiveSampledSizes_getD
    (gridCode : BitString) (gridSteps Δ s : ℕ) (hs : s ≤ gridSteps) :
    (restrictedEffectiveSampledSizes gridCode gridSteps Δ).getD s 0 =
      2 ^ ((decodeRestrictedCurveGridCodeSample gridCode s).2 - (Δ + 1)) := by
  unfold restrictedEffectiveSampledSizes
  rw [List.getD_eq_getElem]
  · rw [List.getElem_map]
    simp
  · simp
    omega

/-- For a grid given as a structure, the requested cardinality at scale `s` is
`2 ^ (grid.j s - (Δ + 1))`. -/
lemma restrictedEffectiveSampledSizes_grid_getD
    {n k gridSteps : ℕ} {t : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k gridSteps t) (Δ s : ℕ)
    (hs : s ≤ gridSteps) :
    (restrictedEffectiveSampledSizes (restrictedCurveGridCode grid)
        gridSteps Δ).getD s 0 =
      2 ^ (grid.j s - (Δ + 1)) := by
  rw [restrictedEffectiveSampledSizes_getD _ _ _ _ hs,
    decode_restrictedCurveGridCode_sample_eq grid hs]

/-- The reconstructed live trace after deleting one coded bad set. -/
noncomputable def restrictedEffectiveLiveCodesAfterDelete
    (stateCode badCode : BitString) : List BitString :=
  restrictedEffectiveRebuildLiveCodes
    (restrictedEffectiveDeleteCode
      (restrictedSelectorField stateCode 0) badCode)
    (decodeListCode (restrictedSelectorField stateCode 1))

/-- The live-pool codes obtained after deleting a code are primitive recursive in the arguments. -/
theorem restrictedEffectiveLiveCodesAfterDelete_primrec :
    Primrec (fun p : BitString × BitString =>
      restrictedEffectiveLiveCodesAfterDelete p.1 p.2) := by
  have hroot : Primrec (fun p : BitString × BitString =>
      restrictedSelectorField p.1 0) :=
    (restrictedSelectorField_primrec.comp Primrec.fst
      ((Primrec.const 0) : Primrec (fun p : BitString × BitString => 0))).of_eq fun _ => rfl
  have hmodels : Primrec (fun p : BitString × BitString =>
      decodeListCode (restrictedSelectorField p.1 1)) :=
    (decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp Primrec.fst
        ((Primrec.const 1) : Primrec (fun p : BitString × BitString => 1)))).of_eq fun _ => rfl
  have hdeleted : Primrec (fun p : BitString × BitString =>
      restrictedEffectiveDeleteCode
        (restrictedSelectorField p.1 0) p.2) :=
    (restrictedEffectiveDeleteCode_primrec.comp
      (Primrec.pair hroot Primrec.snd)).of_eq fun _ => rfl
  exact (restrictedEffectiveRebuildLiveCodes_primrec.comp
    (Primrec.pair hdeleted hmodels)).of_eq fun _ => rfl

/-- Cardinality of the finite set decoded from one cover code. -/
def restrictedDecodedCoverCard (code : BitString) : ℕ :=
  (decodeCoverCodeList code).dedup.length

/-- The cardinality of the finite set decoded from a cover code is primitive recursive. -/
theorem restrictedDecodedCoverCard_primrec :
    Primrec restrictedDecodedCoverCard :=
  Primrec.list_length.comp (dedup_primrec.comp decodeCoverCodeList_primrec)

/-- Boolean density failure test at one sampled edge. -/
noncomputable def restrictedEffectiveDensityFailsBool (q0 : ℕ)
    (p : (List ℕ × BitString × BitString) × ℕ) : Bool :=
  let liveCodes := restrictedEffectiveLiveCodesAfterDelete p.1.2.1 p.1.2.2
  decide ((2 * q0 * p.1.1.getD p.2 0) *
      restrictedDecodedCoverCard (liveCodes.getD (p.2 + 1) []) <
    p.1.1.getD (p.2 + 1) 0 *
      restrictedDecodedCoverCard (liveCodes.getD p.2 []))

/-- The test for failure of the density condition at a scale is primitive recursive. -/
theorem restrictedEffectiveDensityFailsBool_primrec (q0 : ℕ) :
    Primrec (restrictedEffectiveDensityFailsBool q0) := by
  have hlive : Primrec (fun p :
      (List ℕ × BitString × BitString) × ℕ =>
      restrictedEffectiveLiveCodesAfterDelete p.1.2.1 p.1.2.2) :=
    restrictedEffectiveLiveCodesAfterDelete_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hsize : Primrec (fun p :
      (List ℕ × BitString × BitString) × ℕ =>
      p.1.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hsizeSucc : Primrec (fun p :
      (List ℕ × BitString × BitString) × ℕ =>
      p.1.1.getD (p.2 + 1) 0) :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.succ.comp Primrec.snd)
  have hliveCode : Primrec (fun p :
      (List ℕ × BitString × BitString) × ℕ =>
      (restrictedEffectiveLiveCodesAfterDelete p.1.2.1 p.1.2.2).getD p.2 []) :=
    (Primrec.list_getD []).comp hlive Primrec.snd
  have hliveCodeSucc : Primrec (fun p :
      (List ℕ × BitString × BitString) × ℕ =>
      (restrictedEffectiveLiveCodesAfterDelete p.1.2.1 p.1.2.2).getD
        (p.2 + 1) []) :=
    (Primrec.list_getD []).comp hlive (Primrec.succ.comp Primrec.snd)
  have hleft := Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.const (2 * q0)) hsize)
    (restrictedDecodedCoverCard_primrec.comp hliveCodeSucc)
  have hright := Primrec.nat_mul.comp hsizeSucc
    (restrictedDecodedCoverCard_primrec.comp hliveCode)
  exact (PrimrecPred.decide (Primrec.nat_lt.comp hleft hright)).of_eq
    (fun _ => rfl)

/-- The least density edge that fails after deleting `badCode`.  If no edge
fails, `List.findIdx` returns the number of edges, so the whole model prefix is
retained. -/
noncomputable def restrictedEffectiveFirstFailedScale
    (q0 : ℕ) (sizes : List ℕ) (stateCode badCode : BitString) : ℕ :=
  (List.range (sizes.length - 1)).findIdx (fun s =>
    restrictedEffectiveDensityFailsBool q0 ((sizes, stateCode, badCode), s))

/-- The first scale at which the density condition fails is primitive recursive in the requested
sizes and the two codes. -/
theorem restrictedEffectiveFirstFailedScale_primrec (q0 : ℕ) :
    Primrec (fun p : List ℕ × BitString × BitString =>
      restrictedEffectiveFirstFailedScale q0 p.1 p.2.1 p.2.2) := by
  have hrange : Primrec (fun p : List ℕ × BitString × BitString =>
      List.range (p.1.length - 1)) :=
    Primrec.list_range.comp
      (Primrec.nat_sub.comp
        (Primrec.list_length.comp Primrec.fst) (Primrec.const 1))
  exact (Primrec.list_findIdx hrange
    (restrictedEffectiveDensityFailsBool_primrec q0).to₂).of_eq (fun _ => rfl)

/-- Initial state search.  Starting from the full ambient cube, select all
`sizes.length` sampled models.  The suffix iterator returns the predecessor
cube first; it is dropped from the stored model list. -/
noncomputable def restrictedEffectiveSampledInitialState
    (𝒜 : DescriptionFamily) (ambientLength : ℕ)
    (sizes : List ℕ) : Part BitString :=
  let q0 := 𝒜.overhead ambientLength
  let Acode := (codedUniformOn (stringsOfLength ambientLength)
    (codedStringsOfLength_nonempty ambientLength)).code
  (restrictedEffectiveRebuildSuffix 𝒜
    (restrictedEffectiveRebuildSuffixInput Acode Acode sizes q0)).map
      (fun output =>
        let modelCodes := (decodeListCode output).tail
        let rootLiveCode := restrictedLiveIntersectionCode Acode
          (modelCodes.headD [])
        restrictedEffectiveSampledStateCode rootLiveCode modelCodes)

/-- Encoded input for the strict-suffix rebuild performed by one bad event. -/
noncomputable def restrictedEffectiveSampledRunStepInput (q0 : ℕ)
    (p : List ℕ × BitString × BitString) : BitString :=
  let q := restrictedEffectiveFirstFailedScale q0 p.1 p.2.1 p.2.2
  let modelCodes := decodeListCode (restrictedSelectorField p.2.1 1)
  let liveCodes := restrictedEffectiveLiveCodesAfterDelete p.2.1 p.2.2
  restrictedEffectiveRebuildSuffixInput (modelCodes.getD q [])
    (liveCodes.getD q []) (p.1.drop (q + 1)) q0

/-- Assembling the input of one sampled run step is primitive recursive. -/
theorem restrictedEffectiveSampledRunStepInput_primrec (q0 : ℕ) :
    Primrec (restrictedEffectiveSampledRunStepInput q0) := by
  have hq := restrictedEffectiveFirstFailedScale_primrec q0
  have hmodels : Primrec (fun p : List ℕ × BitString × BitString =>
      decodeListCode (restrictedSelectorField p.2.1 1)) :=
    decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
  have hlive : Primrec (fun p : List ℕ × BitString × BitString =>
      restrictedEffectiveLiveCodesAfterDelete p.2.1 p.2.2) :=
    restrictedEffectiveLiveCodesAfterDelete_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
  have hpredecessor := (Primrec.list_getD []).comp hmodels hq
  have hliveAtQ := (Primrec.list_getD []).comp hlive hq
  have hsuffix := Primrec.list_drop.comp Primrec.fst
    (Primrec.succ.comp hq)
  have hsuffixBits := Primrec.list_map hsuffix
    (primrec_natBits.comp Primrec.snd).to₂
  unfold restrictedEffectiveSampledRunStepInput
  unfold restrictedEffectiveRebuildSuffixInput
  exact listCode_primrec.comp
    (Primrec.list_cons.comp hpredecessor
      (Primrec.list_cons.comp hliveAtQ
        (Primrec.list_cons.comp (listCode_primrec.comp hsuffixBits)
          (Primrec.list_cons.comp (primrec_natBits.comp (Primrec.const q0))
            (Primrec.const [])))))

/-- Reassemble the retained prefix and decoded rebuilt suffix into a state. -/
noncomputable def restrictedEffectiveSampledRunStepPost (q0 : ℕ)
    (p : (List ℕ × BitString × BitString) × BitString) : BitString :=
  let q := restrictedEffectiveFirstFailedScale q0 p.1.1 p.1.2.1 p.1.2.2
  let modelCodes := decodeListCode (restrictedSelectorField p.1.2.1 1)
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField p.1.2.1 0) p.1.2.2
  restrictedEffectiveSampledStateCode deletedRootCode
    (modelCodes.take q ++ decodeListCode p.2)

/-- Reading the new state off the output of one sampled run step is primitive recursive. -/
theorem restrictedEffectiveSampledRunStepPost_primrec (q0 : ℕ) :
    Primrec (restrictedEffectiveSampledRunStepPost q0) := by
  have h_eq : restrictedEffectiveSampledRunStepPost q0 =
      fun p : (List ℕ × BitString × BitString) × BitString =>
    restrictedEffectiveSampledStateCode
      (restrictedEffectiveDeleteCode (restrictedSelectorField p.1.2.1 0) p.1.2.2)
      ((decodeListCode (restrictedSelectorField p.1.2.1 1)).take
          (restrictedEffectiveFirstFailedScale q0 p.1.1 p.1.2.1 p.1.2.2) ++
            decodeListCode p.2) := rfl
  rw [h_eq]
  have hq : Primrec (fun p : (List ℕ × BitString × BitString) × BitString =>
      restrictedEffectiveFirstFailedScale q0 p.1.1 p.1.2.1 p.1.2.2) :=
    ((restrictedEffectiveFirstFailedScale_primrec q0).comp
      (@Primrec.fst (List ℕ × BitString × BitString) BitString inferInstance inferInstance)).of_eq
      fun _ => rfl
  have hmodels : Primrec (fun p :
      (List ℕ × BitString × BitString) × BitString =>
      decodeListCode (restrictedSelectorField p.1.2.1 1)) :=
    (decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        ((Primrec.const 1) :
          Primrec (fun p : (List ℕ × BitString × BitString) × BitString => 1)))).of_eq
      fun _ => rfl
  have hdeleted : Primrec (fun p :
      (List ℕ × BitString × BitString) × BitString =>
      restrictedEffectiveDeleteCode
        (restrictedSelectorField p.1.2.1 0) p.1.2.2) :=
    (restrictedEffectiveDeleteCode_primrec.comp
      (Primrec.pair
        (restrictedSelectorField_primrec.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          ((Primrec.const 0) : Primrec (fun p : (List ℕ × BitString × BitString) × BitString => 0)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).of_eq fun _ => rfl
  have hcodes : Primrec (fun p : (List ℕ × BitString × BitString) × BitString =>
      (decodeListCode (restrictedSelectorField p.1.2.1 1)).take
          (restrictedEffectiveFirstFailedScale q0 p.1.1 p.1.2.1 p.1.2.2) ++ decodeListCode p.2) :=
    (Primrec.list_append.comp
      (Primrec.list_take.comp hmodels hq)
      (decodeListCode_primrec.comp Primrec.snd)).of_eq fun _ => rfl
  exact (restrictedEffectiveSampledStateCode_primrec.comp
    (Primrec.pair hdeleted hcodes)).of_eq fun _ => rfl

/-- Process one bad event.  Prefix models strictly before `q` are copied,
model `q` is retained as the predecessor emitted by the suffix iterator, and
only models after `q` are selected again. -/
noncomputable def restrictedEffectiveSampledRunStep
    (𝒜 : DescriptionFamily) (q0 : ℕ) (sizes : List ℕ)
    (stateCode badCode : BitString) : Part BitString :=
  (restrictedEffectiveRebuildSuffix 𝒜
    (restrictedEffectiveSampledRunStepInput q0
      (sizes, stateCode, badCode))).map (fun suffixOutput =>
        restrictedEffectiveSampledRunStepPost q0
          ((sizes, stateCode, badCode), suffixOutput))

/-- One step of the sampled run is partial computable in the requested sizes and the state. -/
theorem restrictedEffectiveSampledRunStep_partrec
    (𝒜 : DescriptionFamily) (q0 : ℕ) :
    Partrec (fun p : List ℕ × BitString × BitString =>
      restrictedEffectiveSampledRunStep 𝒜 q0 p.1 p.2.1 p.2.2) := by
  exact Partrec.map
    ((restrictedEffectiveRebuildSuffix_partrec 𝒜).comp
      (restrictedEffectiveSampledRunStepInput_primrec q0).to_comp)
    (restrictedEffectiveSampledRunStepPost_primrec q0).to_comp.to₂

/-- Execute a finite chronological batch by partial recursion. -/
noncomputable def restrictedEffectiveSampledRunProcess
    (𝒜 : DescriptionFamily) (q0 : ℕ) (sizes : List ℕ)
    (stateCode : BitString) (badCodes : List BitString) : Part BitString :=
  Nat.rec (motive := fun _ => Part BitString)
    (Part.some stateCode)
    (fun idx current => current.bind (fun state =>
      restrictedEffectiveSampledRunStep 𝒜 q0 sizes state
        (badCodes.getD idx [])))
    badCodes.length

/-- The whole sampled run is partial computable in the requested sizes and the initial state. -/
theorem restrictedEffectiveSampledRunProcess_partrec
    (𝒜 : DescriptionFamily) (q0 : ℕ) :
    Partrec (fun p : List ℕ × BitString × List BitString =>
      restrictedEffectiveSampledRunProcess 𝒜 q0 p.1 p.2.1 p.2.2) := by
  have hcount : Computable (fun p : List ℕ × BitString × List BitString =>
      p.2.2.length) :=
    Computable.list_length.comp (Computable.snd.comp Computable.snd)
  have hinitial : Partrec (fun p : List ℕ × BitString × List BitString =>
      Part.some p.2.1) :=
    (Computable.fst.comp Computable.snd).partrec
  have hinput : Computable (fun q :
      (List ℕ × BitString × List BitString) × (ℕ × BitString) =>
      (q.1.1, q.2.2, q.1.2.2.getD q.2.1 [])) := by
    apply Primrec.to_comp
    exact Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.snd)
        ((Primrec.list_getD []).comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)))
  have hnext : Partrec₂ (fun p : List ℕ × BitString × List BitString =>
      fun indexed : ℕ × BitString =>
        restrictedEffectiveSampledRunStep 𝒜 q0 p.1 indexed.2
          (p.2.2.getD indexed.1 [])) :=
    ((restrictedEffectiveSampledRunStep_partrec 𝒜 q0).comp hinput).to₂
  refine (Partrec.nat_rec hcount hinitial hnext).of_eq ?_
  intro p
  rfl

/-- The genuinely new suffix at stage `time + 1`. -/
def restrictedSampledNewBadBatch (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ time : ℕ) : List BitString :=
  (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ (time + 1)).drop
    (restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time).length

end Kolmogorov
