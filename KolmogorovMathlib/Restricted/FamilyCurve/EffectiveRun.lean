import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRebuild
import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream

/-!
# Partial-recursive chronological sampled run

The family cover selector is a partial-recursive search.  Consequently the
honest executable interface is a `Part BitString`: validity hypotheses prove
termination, rather than a noncomputable default being substituted when a
search diverges.

A coded state contains the current root live pool and the `N + 1` current
model codes.  All deeper live pools are reconstructed by successive
intersection.  On a bad event the executor finds the least failed density
edge, retains the prefix through that edge, and invokes the effective suffix
rebuild only on the strict suffix.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- Code a root live pool together with the current sampled model codes. -/
def restrictedEffectiveSampledStateCode
    (rootLiveCode : BitString) (modelCodes : List BitString) : BitString :=
  listCode [rootLiveCode, listCode modelCodes]

theorem restrictedEffectiveSampledStateCode_primrec :
    Primrec (fun p : BitString × List BitString =>
      restrictedEffectiveSampledStateCode p.1 p.2) := by
  unfold restrictedEffectiveSampledStateCode
  exact listCode_primrec.comp
    (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp (listCode_primrec.comp Primrec.snd)
        (Primrec.const [])))

@[simp] lemma restrictedSelectorField_sampledState_zero
    (rootLiveCode : BitString) (modelCodes : List BitString) :
    restrictedSelectorField
      (restrictedEffectiveSampledStateCode rootLiveCode modelCodes) 0 =
        rootLiveCode := by
  unfold restrictedEffectiveSampledStateCode restrictedSelectorField
  rw [decodeListCode_listCode]
  rfl

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

theorem restrictedEffectiveRebuildLiveCodesFrom_primrec :
    Primrec (fun p : BitString × List BitString =>
      restrictedEffectiveRebuildLiveCodesFrom p.1 p.2) := by
  have hout : Primrec (fun state : BitString × List BitString =>
      (state.1 :: state.2).reverse) :=
    Primrec.list_reverse.comp
      (Primrec.list_cons.comp Primrec.fst Primrec.snd)
  exact (hout.comp restrictedEffectiveRebuildLiveFold_primrec).of_eq (fun p =>
    restrictedEffectiveRebuildLiveFold_eq p.1 p.2)

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
    2 ^ ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)))

@[simp] lemma restrictedEffectiveSampledSizes_length
    (gridCode : BitString) (gridSteps Δ : ℕ) :
    (restrictedEffectiveSampledSizes gridCode gridSteps Δ).length =
      gridSteps + 1 := by
  simp [restrictedEffectiveSampledSizes]

lemma restrictedEffectiveSampledSizes_getD
    (gridCode : BitString) (gridSteps Δ s : ℕ) (hs : s ≤ gridSteps) :
    (restrictedEffectiveSampledSizes gridCode gridSteps Δ).getD s 0 =
      2 ^ ((decode_restrictedCurveGridCode_sample gridCode s).2 - (Δ + 1)) := by
  unfold restrictedEffectiveSampledSizes
  rw [List.getD_eq_getElem]
  · rw [List.getElem_map]
    simp
  · simp
    omega

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

set_option maxHeartbeats 4000000 in
-- Raised heartbeat limit: `Primrec` composition over decoded selector fields.
theorem restrictedEffectiveLiveCodesAfterDelete_primrec :
    Primrec (fun p : BitString × BitString =>
      restrictedEffectiveLiveCodesAfterDelete p.1 p.2) := by
  have hroot : Primrec (fun p : BitString × BitString =>
      restrictedSelectorField p.1 0) :=
    restrictedSelectorField_primrec.comp Primrec.fst (Primrec.const 0)
  have hmodels : Primrec (fun p : BitString × BitString =>
      decodeListCode (restrictedSelectorField p.1 1)) :=
    decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp Primrec.fst (Primrec.const 1))
  have hdeleted : Primrec (fun p : BitString × BitString =>
      restrictedEffectiveDeleteCode
        (restrictedSelectorField p.1 0) p.2) :=
    restrictedEffectiveDeleteCode_primrec.comp
      (Primrec.pair hroot Primrec.snd)
  exact restrictedEffectiveRebuildLiveCodes_primrec.comp
    (Primrec.pair hdeleted hmodels)

/-- Cardinality of the finite set decoded from one cover code. -/
def restrictedDecodedCoverCard (code : BitString) : ℕ :=
  (decodeCoverCodeList code).dedup.length

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
    (primrecNatBits.comp Primrec.snd).to₂
  unfold restrictedEffectiveSampledRunStepInput
  unfold restrictedEffectiveRebuildSuffixInput
  exact listCode_primrec.comp
    (Primrec.list_cons.comp hpredecessor
      (Primrec.list_cons.comp hliveAtQ
        (Primrec.list_cons.comp (listCode_primrec.comp hsuffixBits)
          (Primrec.list_cons.comp (primrecNatBits.comp (Primrec.const q0))
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

set_option maxHeartbeats 12000000 in
-- Raised heartbeat limit: the effective-runner computability layer composes
-- `Primrec` towers over large product types.
theorem restrictedEffectiveSampledRunStepPost_primrec (q0 : ℕ) :
    Primrec (restrictedEffectiveSampledRunStepPost q0) := by
  have h_eq : restrictedEffectiveSampledRunStepPost q0 = fun p : (List ℕ × BitString × BitString) × BitString =>
    restrictedEffectiveSampledStateCode
      (restrictedEffectiveDeleteCode (restrictedSelectorField p.1.2.1 0) p.1.2.2)
      ((decodeListCode (restrictedSelectorField p.1.2.1 1)).take (restrictedEffectiveFirstFailedScale q0 p.1.1 p.1.2.1 p.1.2.2) ++ decodeListCode p.2) := rfl
  rw [h_eq]
  have hq := (restrictedEffectiveFirstFailedScale_primrec q0).comp
    (@Primrec.fst (List ℕ × BitString × BitString) BitString inferInstance inferInstance)
  have hmodels : Primrec (fun p :
      (List ℕ × BitString × BitString) × BitString =>
      decodeListCode (restrictedSelectorField p.1.2.1 1)) :=
    decodeListCode_primrec.comp
      (restrictedSelectorField_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const 1))
  have hdeleted : Primrec (fun p :
      (List ℕ × BitString × BitString) × BitString =>
      restrictedEffectiveDeleteCode
        (restrictedSelectorField p.1.2.1 0) p.1.2.2) :=
    restrictedEffectiveDeleteCode_primrec.comp
      (Primrec.pair
        (restrictedSelectorField_primrec.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.const 0))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hcodes := Primrec.list_append.comp
    (Primrec.list_take.comp hmodels hq)
    (decodeListCode_primrec.comp Primrec.snd)
  exact restrictedEffectiveSampledStateCode_primrec.comp
    (Primrec.pair hdeleted hcodes)

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

set_option maxHeartbeats 4000000 in
-- Raised heartbeat limit: the effective-runner computability layer composes
-- `Primrec` towers over large product types.
-- The finite `Partrec.nat_rec` carries the coded state through a dependent pair.
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

/-- Prefix monotonicity identifies the next stream as the old stream followed
by exactly `restrictedSampledNewBadBatch`. -/
lemma restrictedSampledNewBadBatch_append (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ time : ℕ) :
    restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time ++
        restrictedSampledNewBadBatch c gridCode 𝒜 gridSteps Δ time =
      restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ (time + 1) := by
  obtain ⟨suffix, hsuffix⟩ :=
    restrictedSampledBadCodeStream_mono c gridCode 𝒜 gridSteps Δ time
  unfold restrictedSampledNewBadBatch
  rw [← hsuffix]
  simp

/-- Every code in the appended batch is genuinely fresh. -/
lemma restrictedSampledNewBadBatch_fresh (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ time : ℕ) {w : BitString}
    (hw : w ∈ restrictedSampledNewBadBatch c gridCode 𝒜 gridSteps Δ time) :
    w ∉ restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ time := by
  have hnodup := restrictedSampledBadCodeStream_nodup c gridCode 𝒜
    gridSteps Δ (time + 1)
  rw [← restrictedSampledNewBadBatch_append c gridCode 𝒜 gridSteps Δ time]
    at hnodup
  intro hold
  exact (List.nodup_append.mp hnodup).2.2 w hold w hw rfl

/-- The first batch is the stage-zero stream; subsequent batches are the new
suffix supplied by `restrictedSampledNewBadBatch`.  Thus every stream event is
processed, including events already visible at stage zero. -/
def restrictedSampledBadBatchAt (c : Code) (gridCode : BitString)
    (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) : ℕ → List BitString
  | 0 => restrictedSampledBadCodeStream c gridCode 𝒜 gridSteps Δ 0
  | time + 1 =>
      restrictedSampledNewBadBatch c gridCode 𝒜 gridSteps Δ time

/-- Chronological partial-recursive run.  Time zero is the initial state; the
transition to time `time + 1` processes `restrictedSampledBadBatchAt time`. -/
noncomputable def restrictedEffectiveSampledRun
    (𝒜 : DescriptionFamily) (c : Code) (gridCode : BitString)
    (ambientLength gridSteps Δ time : ℕ) : Part BitString :=
  let q0 := 𝒜.overhead ambientLength
  let sizes := restrictedEffectiveSampledSizes gridCode gridSteps Δ
  Nat.rec (motive := fun _ => Part BitString)
    (restrictedEffectiveSampledInitialState 𝒜 ambientLength sizes)
    (fun stage current => current.bind (fun state =>
      restrictedEffectiveSampledRunProcess 𝒜 q0 sizes state
        (restrictedSampledBadBatchAt c gridCode 𝒜.toPre gridSteps Δ stage)))
    time

lemma restrictedEffectiveSampledSizes_computable_uniform
    (gridSteps Δ : ℕ) :
    Computable (fun gridCode : BitString =>
      restrictedEffectiveSampledSizes gridCode gridSteps Δ) := by
  unfold restrictedEffectiveSampledSizes;
  -- The function that takes a grid code and returns the list of sizes is computable because it's a composition of computable functions.
  have h_computable : Computable (fun (p : BitString × ℕ) => 2 ^ ((decode_restrictedCurveGridCode_sample p.1 p.2).2 - (Δ + 1))) := by
    have h_computable : Computable (fun (p : BitString × ℕ) => (decode_restrictedCurveGridCode_sample p.1 p.2).2 - (Δ + 1)) := by
      have h_computable : Computable (fun (p : BitString × ℕ) => (decode_restrictedCurveGridCode_sample p.1 p.2).2) := by
        exact Computable.snd.comp ( decode_restrictedCurveGridCode_sample_computable );
      have h_computable : Computable (fun (p : ℕ × ℕ) => p.1 - p.2) := by
        convert Primrec.nat_sub.to_comp using 1;
      convert h_computable.comp ( Computable.pair ‹Computable fun p : BitString × ℕ => ( decode_restrictedCurveGridCode_sample p.1 p.2 ).2› ( Computable.const ( Δ + 1 ) ) ) using 1;
    grind +suggestions;
  generalize gridSteps + 1 = k
  induction k with
  | zero =>
      simp_all +decide
      exact Computable.const []
  | succ gridSteps ih =>
      simp_all +decide [ List.range_succ ]
      have h_append : Computable (fun (p : List ℕ × ℕ) => p.1 ++ [p.2]) := by
        convert Computable.list_append.comp ( Computable.fst )
          ( Computable.list_cons.comp ( Computable.snd )
            ( Computable.const [] ) ) using 1
      convert h_append.comp ( Computable.pair ih ( h_computable.comp
        ( Computable.pair ( Computable.id )
          ( Computable.const gridSteps ) ) ) ) using 1

lemma restrictedEffectiveSampledInitialState_input_computable
    (𝒜 : DescriptionFamily) (ambientLength gridSteps Δ : ℕ) :
    Computable (fun gridCode : BitString =>
      let Acode := (codedUniformOn (stringsOfLength ambientLength)
        (codedStringsOfLength_nonempty ambientLength)).code
      restrictedEffectiveRebuildSuffixInput Acode Acode
        (restrictedEffectiveSampledSizes gridCode gridSteps Δ)
        (𝒜.overhead ambientLength)) := by
  have h_listCode_primrec : Computable (fun (l : List BitString) => listCode l) := by
    exact Computable.of_eq ( listCode_primrec.to_comp ) fun _ => rfl;
  convert Computable.comp h_listCode_primrec _ using 1;
  convert Computable.list_cons.comp _ _ using 1;
  · exact Computable.const _;
  · convert Computable.list_cons.comp _ _ using 1;
    · exact Computable.const _;
    · convert Computable.list_cons.comp _ _ using 1;
      · convert Computable.comp h_listCode_primrec _ using 1;
        have h_map_primrec : Computable (fun (l : List ℕ) => List.map Nat.bits l) := by
          have h_bits_primrec : Primrec Nat.bits := by
            exact primrecNatBits
          have h_map_primrec : Primrec (fun (l : List ℕ) => List.map Nat.bits l) := by
            convert Primrec.list_map _ _ using 1;
            exact Primcodable.ofDenumerable ℕ
            · exact Primrec.id;
            · exact h_bits_primrec.comp ( Primrec.snd );
          exact Primrec.to_comp h_map_primrec
        convert h_map_primrec.comp ( restrictedEffectiveSampledSizes_computable_uniform gridSteps Δ ) using 1;
      · exact Computable.const _

lemma restrictedEffectiveSampledInitialState_post_computable
    (ambientLength : ℕ) :
    Computable (fun output : BitString =>
      let Acode := (codedUniformOn (stringsOfLength ambientLength)
        (codedStringsOfLength_nonempty ambientLength)).code
      let modelCodes := (decodeListCode output).tail
      let rootLiveCode := restrictedLiveIntersectionCode Acode
        (modelCodes.headD [])
      restrictedEffectiveSampledStateCode rootLiveCode modelCodes) := by
  apply Computable.comp
  · exact listCode_computable
  · have h_restrictedLiveIntersectionCode : Primrec (fun (p : BitString × BitString) => restrictedLiveIntersectionCode p.1 p.2) := by
      exact restrictedLiveIntersectionCode_primrec
    have h_decodeListCode : Primrec (fun (a : BitString) => decodeListCode a) := by
      exact decodeListCode_primrec
    have h_listCode : Primrec (fun (l : List BitString) => listCode l) := by
      exact listCode_primrec
    have h_listCode : Primrec (fun (l : List BitString) => [restrictedLiveIntersectionCode (codedUniformOn (stringsOfLength ambientLength) (codedStringsOfLength_nonempty ambientLength)).code (l.headD []), listCode l]) := by
      have h_listCode : Primrec (fun (l : List BitString) => restrictedLiveIntersectionCode (codedUniformOn (stringsOfLength ambientLength) (codedStringsOfLength_nonempty ambientLength)).code (l.headD [])) := by
        have h_listCode : Primrec (fun (l : List BitString) => l.headD []) := by
          convert Primrec.list_headI using 1;
          exact funext fun l => by cases l <;> rfl;
        convert h_restrictedLiveIntersectionCode.comp ( Primrec.const _ |> Primrec.pair <| h_listCode ) using 1;
      exact Primrec.list_cons.comp h_listCode ( Primrec.list_cons.comp ‹_› ( Primrec.const [] ) );
    convert h_listCode.comp ( Primrec.list_tail.comp h_decodeListCode ) |> Primrec.to_comp using 1

lemma restrictedEffectiveSampledInitialState_partrec_uniform
    (𝒜 : DescriptionFamily) (ambientLength gridSteps Δ : ℕ) :
    Partrec (fun gridCode : BitString =>
      restrictedEffectiveSampledInitialState 𝒜 ambientLength
        (restrictedEffectiveSampledSizes gridCode gridSteps Δ)) := by
  refine Partrec.map ?_ ?_
  · have := @restrictedEffectiveSampledInitialState_input_computable;
    exact Partrec.comp ( restrictedEffectiveRebuildSuffix_partrec 𝒜 ) ( this 𝒜 ambientLength gridSteps Δ );
  · convert Computable.comp ( restrictedEffectiveSampledInitialState_post_computable ambientLength ) ( Computable.snd ) using 1

lemma restrictedSampledBadBatchAt_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) (gridSteps Δ : ℕ) :
    Computable (fun p : BitString × ℕ =>
      restrictedSampledBadBatchAt c p.1 𝒜 gridSteps Δ p.2) := by
  -- We'll use the fact that if the `restrictedSampledBadCodeStream` is computable, then the `restrictedSampledBadBatchAt` is also computable.
  have h_computable : Computable (fun p : BitString × ℕ => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2) := by
    convert restrictedSampledBadCodeStream_computable_uniform c 𝒜 gridSteps Δ using 1;
  have h_computable : Computable (fun p : BitString × ℕ => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ (p.2 + 1)) := by
    convert h_computable.comp ( Computable.pair ( Computable.fst ) ( Computable.succ.comp ( Computable.snd ) ) ) using 1;
  have h_computable : Computable (fun p : BitString × ℕ => (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ (p.2 + 1)).drop (restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2).length) := by
    have h_computable : Computable (fun p : List BitString × List BitString => p.1.drop p.2.length) := by
      have h_computable : Computable (fun p : List BitString × ℕ => p.1.drop p.2) := by
        have h_computable : Primrec (fun p : List BitString × ℕ => p.1.drop p.2) := by
          convert Primrec.list_drop using 1
        exact Primrec.to_comp h_computable
      convert h_computable.comp ( Computable.fst.pair ( Computable.list_length.comp Computable.snd ) ) using 1;
    convert h_computable.comp ( Computable.pair ‹Computable fun p : BitString × ℕ => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ ( p.2 + 1 ) › ‹Computable fun p : BitString × ℕ => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2 › ) using 1;
  convert Computable.nat_casesOn _ _ _ using 1;
  rotate_left;
  exact fun p => p.2;
  exact fun p => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ 0;
  exact fun p n => List.drop ( restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ n ).length ( restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ ( n + 1 ) );
  · exact Computable.snd;
  · convert Computable.comp ‹Computable fun p : BitString × ℕ => restrictedSampledBadCodeStream c p.1 𝒜 gridSteps Δ p.2› (Computable.pair (Computable.fst) (Computable.const 0)) using 1;
  · convert h_computable.comp ( Computable.fst.comp ( Computable.fst ) |> Computable.pair <| Computable.snd ) using 1;
  · ext ⟨gridCode, time⟩; cases time <;> rfl;

set_option maxHeartbeats 40000000 in
-- Raised heartbeat limit: the effective-runner computability layer composes
-- `Primrec` towers over large product types.
-- The outer recursion composes the grid decoder, bad-event batches, and coded runner.
/-- The executor is one uniform partial-recursive procedure in the encoded
grid and time.  Termination is deliberately separated into the validity
specifications below. -/
lemma restrictedEffectiveSampledRun_partrec_uniform
    (𝒜 : DescriptionFamily) (c : Code)
    (ambientLength gridSteps Δ : ℕ) :
    Partrec (fun p : BitString × ℕ =>
      restrictedEffectiveSampledRun 𝒜 c p.1 ambientLength gridSteps Δ p.2) := by
  let q0 := 𝒜.overhead ambientLength
  have hcount : Computable (fun p : BitString × ℕ => p.2) :=
    Computable.snd
  have hinitial : Partrec (fun p : BitString × ℕ =>
      restrictedEffectiveSampledInitialState 𝒜 ambientLength
        (restrictedEffectiveSampledSizes p.1 gridSteps Δ)) :=
    (restrictedEffectiveSampledInitialState_partrec_uniform
      𝒜 ambientLength gridSteps Δ).comp Computable.fst
  have hsizes : Computable (fun q :
      (BitString × ℕ) × (ℕ × BitString) =>
      restrictedEffectiveSampledSizes q.1.1 gridSteps Δ) :=
    (restrictedEffectiveSampledSizes_computable_uniform gridSteps Δ).comp
      (Computable.fst.comp Computable.fst)
  have hbatch : Computable (fun q :
      (BitString × ℕ) × (ℕ × BitString) =>
      restrictedSampledBadBatchAt c q.1.1 𝒜.toPre gridSteps Δ q.2.1) :=
    (restrictedSampledBadBatchAt_computable_uniform c 𝒜.toPre gridSteps Δ).comp
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
  have hinput : Computable (fun q :
      (BitString × ℕ) × (ℕ × BitString) =>
      (restrictedEffectiveSampledSizes q.1.1 gridSteps Δ,
        q.2.2,
        restrictedSampledBadBatchAt c q.1.1 𝒜.toPre gridSteps Δ q.2.1)) :=
    Computable.pair hsizes
      (Computable.pair (Computable.snd.comp Computable.snd) hbatch)
  have hnext : Partrec₂ (fun p : BitString × ℕ =>
      fun indexed : ℕ × BitString =>
        restrictedEffectiveSampledRunProcess 𝒜 q0
          (restrictedEffectiveSampledSizes p.1 gridSteps Δ)
          indexed.2
          (restrictedSampledBadBatchAt c p.1 𝒜.toPre gridSteps Δ indexed.1)) :=
    ((restrictedEffectiveSampledRunProcess_partrec 𝒜 q0).comp hinput).to₂
  refine (Partrec.nat_rec hcount hinitial hnext).of_eq ?_
  intro p
  rfl

/-- A code represents a sampled mathematical state when it contains all model
codes and the live codes reconstructed from its root agree at every scale. -/
def DecodesToRestrictedSampledRunState
    {𝒜 : DescriptionFamily} {N ambientLength overheadBound : ℕ}
    {t : ℕ → ℕ} (stateCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength overheadBound t) : Prop :=
  let rootLiveCode := restrictedSelectorField stateCode 0
  let modelCodes := decodeListCode (restrictedSelectorField stateCode 1)
  let liveCodes := restrictedEffectiveRebuildLiveCodes rootLiveCode modelCodes
  modelCodes.length = N + 1 ∧
    ∀ s ≤ N,
      decodeCoverCodeList (modelCodes.getD s []) =
          canonicalFinsetList (state.B s) ∧
      decodeCoverCodeList (liveCodes.getD s []) =
          canonicalFinsetList (state.live s)

set_option maxHeartbeats 12000000 in
-- Raised heartbeat limit: the effective-runner computability layer composes
-- `Primrec` towers over large product types.
-- Decoding the effective trace elaborates all six sampled-state invariants together.
/-- A decreasing positive size schedule makes the initial full-cube search
terminate and decode to a genuine sampled state. -/
lemma restrictedEffectiveSampledInitialState_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (htop : t 0 ≤ ambientLength)
    (hmono : ∀ s < N, t (s + 1) ≤ t s) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        restrictedEffectiveSampledInitialState 𝒜 ambientLength sizes =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state := by
  let A := stringsOfLength ambientLength
  let hA : A.Nonempty := codedStringsOfLength_nonempty ambientLength
  let Acode := (codedUniformOn A hA).code
  have hAcode : decodeCoverCodeList Acode = canonicalFinsetList A := by
    exact decodeCoverCodeList_code A hA
  have hAmem : 𝒜.mem A := 𝒜.fullCube ambientLength
  have hAsub : A ⊆ A := Finset.Subset.rfl
  have hAlength : ∀ x ∈ A, x.length = ambientLength := by
    intro x hx
    exact (memStringsOfLength ambientLength x).mp hx
  have hAcard : A.card ≤ 2 ^ ambientLength := by
    rw [show A = stringsOfLength ambientLength from rfl, cardStringsOfLength]
  have hsizes_pos : ∀ i < sizes.length, 0 < sizes.getD i 0 := by
    intro i hi
    have hiN : i ≤ N := by omega
    rw [hpowers i hiN]
    positivity
  have hsizes_head : sizes.getD 0 0 ≤ 2 ^ ambientLength := by
    rw [hpowers 0 (Nat.zero_le N)]
    exact Nat.pow_le_pow_right (by decide) htop
  have hsizes_mono : ∀ i, i + 1 < sizes.length →
      sizes.getD (i + 1) 0 ≤ sizes.getD i 0 := by
    intro i hi
    have hiN : i < N := by omega
    rw [hpowers (i + 1) (by omega), hpowers i (by omega)]
    exact Nat.pow_le_pow_right (by decide) (hmono i hiN)
  obtain ⟨rawOutput, Afinal, Cfinal, codes, hrun, hrawOutput,
      htrace, hcodesLength, hsteps⟩ :=
    restrictedEffectiveRebuildSuffix_decodes_density 𝒜 Acode Acode sizes
      (𝒜.overhead ambientLength) ambientLength (2 ^ ambientLength)
      A A hAcode hAcode rfl hAmem hAsub hAlength hAcard
      hsizes_pos hsizes_head hsizes_mono
  rw [hlen] at hcodesLength
  have hcodes_ne : codes ≠ [] := by
    intro hnil
    rw [hnil] at hcodesLength
    simp at hcodesLength
  obtain ⟨predecessorCode, tail, hcodes⟩ :=
    List.exists_cons_of_ne_nil hcodes_ne
  subst codes
  have htail_ne : tail ≠ [] := by
    intro hnil
    rw [hnil] at hcodesLength
    simp at hcodesLength
  obtain ⟨firstModelCode, remainingModelCodes, htail⟩ :=
    List.exists_cons_of_ne_nil htail_ne
  subst tail
  have hremainingLength : remainingModelCodes.length = N := by
    simp only [List.length_cons] at hcodesLength
    omega
  let modelCodes := firstModelCode :: remainingModelCodes
  let rootLiveCode := restrictedLiveIntersectionCode Acode firstModelCode
  let liveCodes := restrictedEffectiveRebuildLiveCodes rootLiveCode modelCodes
  let stateCode := restrictedEffectiveSampledStateCode rootLiveCode modelCodes
  have hmodelLength : modelCodes.length = N + 1 := by
    simp [modelCodes, hremainingLength]
  have hmodelAlign : ∀ s,
      modelCodes.getD s [] =
        (predecessorCode :: firstModelCode :: remainingModelCodes).getD
          (s + 1) [] := by
    intro s
    cases s <;> simp [modelCodes]
  have hliveAlign : ∀ s,
      liveCodes.getD s [] =
        (restrictedEffectiveRebuildLiveCodes Acode
          (predecessorCode :: firstModelCode :: remainingModelCodes)).getD
            (s + 1) [] := by
    intro s
    rfl
  have hstepData : ∀ s ≤ N, ∃ Cprev Bnext : Finset BitString,
      decodeCoverCodeList (modelCodes.getD s []) = canonicalFinsetList Bnext ∧
      decodeCoverCodeList (liveCodes.getD s []) =
        canonicalFinsetList (Cprev ∩ Bnext) ∧
      𝒜.mem Bnext ∧ Bnext.card ≤ sizes.getD s 0 ∧
      (∀ x ∈ Cprev, x.length = ambientLength) := by
    intro s hs
    obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
        hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
        hBnextMem, hBnextCard, hdensity⟩ := hsteps s (by
          rw [hlen]
          exact Nat.lt_succ_of_le hs)
    refine ⟨Cprev, Bnext, ?_, ?_, hBnextMem, hBnextCard, hCprevLength⟩
    · rw [hmodelAlign]
      exact hBnextCode
    · rw [hliveAlign, restrictedEffectiveRebuildLiveCodes_succ_getD Acode
          (predecessorCode :: firstModelCode :: remainingModelCodes) s (by
            simp [hremainingLength]
            omega)]
      exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
        hCprevCode hBnextCode
  let decodedModels : ℕ → Finset BitString := fun s =>
    (decodeCoverCodeList (modelCodes.getD s [])).toFinset
  let decodedLive : ℕ → Finset BitString := fun s =>
    (decodeCoverCodeList (liveCodes.getD s [])).toFinset
  have hdecoded : ∀ s ≤ N,
      decodeCoverCodeList (modelCodes.getD s []) =
          canonicalFinsetList (decodedModels s) ∧
      decodeCoverCodeList (liveCodes.getD s []) =
          canonicalFinsetList (decodedLive s) := by
    intro s hs
    obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard,
      hCprevLength⟩ := hstepData s hs
    constructor
    · dsimp [decodedModels]
      rw [hBcode, canonicalFinsetList_toFinset]
    · dsimp [decodedLive]
      rw [hliveCode, canonicalFinsetList_toFinset]
  let state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t :=
    { B := decodedModels
      live := decodedLive
      mem_family := by
        intro s hs
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard,
          hCprevLength⟩ := hstepData s hs
        dsimp [decodedModels]
        rw [hBcode, canonicalFinsetList_toFinset]
        exact hBmem
      size_bound := by
        intro s hs
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard,
          hCprevLength⟩ := hstepData s hs
        dsimp [decodedModels]
        rw [hBcode, canonicalFinsetList_toFinset]
        rw [hpowers s hs] at hBcard
        exact hBcard
      live_subset := by
        intro s hs
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard,
          hCprevLength⟩ := hstepData s hs
        dsimp [decodedLive, decodedModels]
        rw [hliveCode, hBcode, canonicalFinsetList_toFinset,
          canonicalFinsetList_toFinset]
        exact Finset.inter_subset_right
      live_ambient := by
        intro s hs x hx
        obtain ⟨Cprev, Bnext, hBcode, hliveCode, hBmem, hBcard,
          hCprevLength⟩ := hstepData s hs
        dsimp [decodedLive] at hx
        rw [hliveCode, canonicalFinsetList_toFinset] at hx
        exact hCprevLength x (Finset.inter_subset_left hx)
      live_monotonic := by
        intro s hsN
        obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
          hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
          hBnextMem, hBnextCard, hdensity⟩ := hsteps (s + 1) (by
            rw [hlen]
            exact Nat.succ_lt_succ hsN)
        have hcurrent : decodeCoverCodeList (liveCodes.getD s []) =
            canonicalFinsetList Cprev := by
          rw [hliveAlign]
          exact hCprevCode
        have hnext : decodeCoverCodeList (liveCodes.getD (s + 1) []) =
            canonicalFinsetList (Cprev ∩ Bnext) := by
          rw [hliveAlign, restrictedEffectiveRebuildLiveCodes_succ_getD Acode
            (predecessorCode :: firstModelCode :: remainingModelCodes)
            (s + 1) (by simp [hremainingLength]; omega)]
          exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
            hCprevCode hBnextCode
        dsimp [decodedLive]
        rw [hnext, hcurrent, canonicalFinsetList_toFinset,
          canonicalFinsetList_toFinset]
        exact Finset.inter_subset_left
      density := by
        intro s hsN
        obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
          hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
          hBnextMem, hBnextCard, hdensity⟩ := hsteps (s + 1) (by
            rw [hlen]
            exact Nat.succ_lt_succ hsN)
        have hcurrent : decodeCoverCodeList (liveCodes.getD s []) =
            canonicalFinsetList Cprev := by
          rw [hliveAlign]
          exact hCprevCode
        have hnext : decodeCoverCodeList (liveCodes.getD (s + 1) []) =
            canonicalFinsetList (Cprev ∩ Bnext) := by
          rw [hliveAlign, restrictedEffectiveRebuildLiveCodes_succ_getD Acode
            (predecessorCode :: firstModelCode :: remainingModelCodes)
            (s + 1) (by simp [hremainingLength]; omega)]
          exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
            hCprevCode hBnextCode
        dsimp [decodedLive]
        rw [hcurrent, hnext, canonicalFinsetList_toFinset,
          canonicalFinsetList_toFinset, ← hpowers s (by omega),
          ← hpowers (s + 1) (by omega)]
        have hdensity' :
            sizes.getD (s + 1) 0 * Cprev.card ≤
              (𝒜.overhead ambientLength * sizes.getD s 0) *
                (Cprev ∩ Bnext).card := by
          simpa [Finset.inter_comm] using hdensity
        exact hdensity'.trans (by
          gcongr
          omega) }
  have hstateB : ∀ s, state.B s = decodedModels s := fun _ => rfl
  have hstateLive : ∀ s, state.live s = decodedLive s := fun _ => rfl
  refine ⟨stateCode, state, ?_, ?_⟩
  · unfold restrictedEffectiveSampledInitialState
    change Part.map _
      (restrictedEffectiveRebuildSuffix 𝒜
        (restrictedEffectiveRebuildSuffixInput Acode Acode sizes
          (𝒜.overhead ambientLength))) = Part.some stateCode
    rw [hrun, Part.map_some, hrawOutput]
    congr 1
    simp only [decodeListCode_listCode, List.tail_cons, List.headD_cons]
    rfl
  · unfold DecodesToRestrictedSampledRunState
    simp only [stateCode, restrictedSelectorField_sampledState_zero,
      restrictedSelectorField_sampledState_one]
    refine ⟨hmodelLength, ?_⟩
    intro s hs
    rw [hstateB, hstateLive]
    exact hdecoded s hs

lemma decode_restrictedEffectiveDeleteCode
    {liveCode badCode : BitString} {live bad : Finset BitString}
    (hlive : decodeCoverCodeList liveCode = canonicalFinsetList live)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad) :
    decodeCoverCodeList (restrictedEffectiveDeleteCode liveCode badCode) =
      canonicalFinsetList (live \ bad) := by
  convert decodeCoverCodeList_canonicalUniformCodeOfList _ using 2;
  simp_all +decide [ canonicalFinsetList ];
  have h_dedup : List.Perm (List.filter (fun x => !decide (x ∈ bad)) (live.sort bitStringLE)) ((live \ bad).sort bitStringLE) := by
    rw [ List.perm_iff_count ];
    intro a; by_cases ha : a ∈ live <;> by_cases hb : a ∈ bad <;> simp_all +decide [ List.count_eq_zero_of_not_mem ] ;
  rw [ List.dedup_eq_self.mpr ];
  · apply_rules [ List.Perm.eq_of_pairwise ];
    any_goals exact bitStringLE;
    · intros a b ha hb hab hba;
      exact Encodable.encode_injective ( le_antisymm hab hba );
    · exact Finset.pairwise_sort _ _;
    · exact List.Pairwise.filter _ ( Finset.pairwise_sort _ _ );
  · exact List.Nodup.filter _ ( Finset.sort_nodup _ _ )

lemma restrictedDecodedCoverCard_eq
    {code : BitString} {S : Finset BitString}
    (hcode : decodeCoverCodeList code = canonicalFinsetList S) :
    restrictedDecodedCoverCard code = S.card := by
  unfold restrictedDecodedCoverCard;
  convert length_canonicalFinsetList S using 1;
  rw [ hcode, List.dedup_eq_self.mpr ( canonicalFinsetList_nodup S ) ]

set_option maxHeartbeats 4000000 in
-- Raised heartbeat limit: decoded-state induction with `Finset` rewriting.
/-- Deleting a coded bad set from the root and replaying the unchanged model
codes reconstructs exactly the pointwise set differences of the old live
trace.  This is the decoding bridge needed to compare the executable density
test with `restrictedSampledDensityFails`. -/
lemma restrictedEffectiveLiveCodesAfterDelete_decode
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    {stateCode badCode : BitString}
    {state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t}
    {bad : Finset BitString}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad) :
    ∀ s ≤ N,
      decodeCoverCodeList
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD s []) =
        canonicalFinsetList (state.live s \ bad) := by
  let rootLiveCode := restrictedSelectorField stateCode 0
  let modelCodes := decodeListCode (restrictedSelectorField stateCode 1)
  let oldLiveCodes := restrictedEffectiveRebuildLiveCodes rootLiveCode modelCodes
  let deletedRootCode := restrictedEffectiveDeleteCode rootLiveCode badCode
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode modelCodes
  have hmodelLength : modelCodes.length = N + 1 := hstate.1
  have hmodel_ne : modelCodes ≠ [] := by
    intro hnil
    rw [hnil] at hmodelLength
    simp at hmodelLength
  have hold : ∀ s ≤ N,
      decodeCoverCodeList (oldLiveCodes.getD s []) =
        canonicalFinsetList (state.live s) := fun s hs => (hstate.2 s hs).2
  have hmodel : ∀ s ≤ N,
      decodeCoverCodeList (modelCodes.getD s []) =
        canonicalFinsetList (state.B s) := fun s hs => (hstate.2 s hs).1
  change ∀ s ≤ N,
    decodeCoverCodeList (newLiveCodes.getD s []) =
      canonicalFinsetList (state.live s \ bad)
  intro s hs
  induction s with
  | zero =>
      have hroot : decodeCoverCodeList rootLiveCode =
          canonicalFinsetList (state.live 0) := by
        have h := hold 0 (Nat.zero_le N)
        rw [restrictedEffectiveRebuildLiveCodes_getD_zero
          rootLiveCode modelCodes hmodel_ne] at h
        exact h
      rw [restrictedEffectiveRebuildLiveCodes_getD_zero
        deletedRootCode modelCodes hmodel_ne]
      exact decode_restrictedEffectiveDeleteCode hroot hbad
  | succ s ih =>
      have hslt : s + 1 < modelCodes.length := by omega
      have hsN : s ≤ N := by omega
      have hnext_old : state.live (s + 1) =
          state.live s ∩ state.B (s + 1) := by
        have hdecode := decode_restrictedLiveIntersectionCode
          (oldLiveCodes.getD s []) (modelCodes.getD (s + 1) [])
          (state.live s) (state.B (s + 1))
          (hold s hsN) (hmodel (s + 1) hs)
        rw [← restrictedEffectiveRebuildLiveCodes_succ_getD
          rootLiveCode modelCodes s hslt] at hdecode
        have heq : canonicalFinsetList (state.live (s + 1)) =
            canonicalFinsetList (state.live s ∩ state.B (s + 1)) := by
          rw [← hold (s + 1) hs]
          exact hdecode
        have hfin := congrArg List.toFinset heq
        simpa only [canonicalFinsetList_toFinset] using hfin
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD
        deletedRootCode modelCodes s hslt]
      have hdecode := decode_restrictedLiveIntersectionCode
        (newLiveCodes.getD s []) (modelCodes.getD (s + 1) [])
        (state.live s \ bad) (state.B (s + 1))
        (ih hsN) (hmodel (s + 1) hs)
      rw [hdecode, hnext_old]
      congr 1
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto

/-- On a decoded state, the executable Boolean density test is equivalent to
the mathematical failed-edge predicate. -/
lemma restrictedEffectiveDensityFailsBool_iff
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    {stateCode badCode : BitString}
    {state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t}
    {bad : Finset BitString}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
    (s : ℕ) (hs : s < N) :
    restrictedEffectiveDensityFailsBool (𝒜.overhead ambientLength)
        ((sizes, stateCode, badCode), s) = true ↔
      restrictedSampledDensityFails state bad s := by
  have hdecode_s := restrictedEffectiveLiveCodesAfterDelete_decode
    𝒜 N ambientLength t hstate hbad s (Nat.le_of_lt hs)
  have hdecode_succ := restrictedEffectiveLiveCodesAfterDelete_decode
    𝒜 N ambientLength t hstate hbad (s + 1) (Nat.succ_le_of_lt hs)
  have hcard_s := restrictedDecodedCoverCard_eq hdecode_s
  have hcard_succ := restrictedDecodedCoverCard_eq hdecode_succ
  unfold restrictedEffectiveDensityFailsBool restrictedSampledDensityFails
  simp only [decide_eq_true_eq]
  rw [hcard_s, hcard_succ, hpowers s (Nat.le_of_lt hs),
    hpowers (s + 1) (Nat.succ_le_of_lt hs)]

private lemma findIdx_range_spec (p : ℕ → Bool) (N : ℕ) :
    let q := (List.range N).findIdx p
    q ≤ N ∧
      ((q = N ∧ ∀ s < N, p s = false) ∨
        (q < N ∧ p q = true ∧ ∀ s < q, p s = false)) := by
  let q := (List.range N).findIdx p
  have hq : q ≤ N := by
    simpa [q] using (List.findIdx_le_length (p := p) (xs := List.range N))
  refine ⟨hq, ?_⟩
  by_cases hqN : q = N
  · refine Or.inl ⟨hqN, ?_⟩
    have hall : ∀ x ∈ List.range N, p x = false := by
      rw [← List.findIdx_eq_length]
      simpa [q] using hqN
    intro s hs
    exact hall s (by simp [hs])
  · have hqlt : q < N := by omega
    refine Or.inr ⟨hqlt, ?_, ?_⟩
    · have hget := List.findIdx_getElem
          (p := p) (xs := List.range N)
          (w := by simpa [q] using hqlt)
      simpa [q] using hget
    · intro s hs
      by_cases hp : p s = false
      · exact hp
      · have hptrue : p s = true := by
          cases h : p s <;> simp_all
        have hfindlt : List.findIdx p ((List.range N).take q) <
            ((List.range N).take q).length := by
          rw [List.findIdx_lt_length]
          have hsN : s < N := hs.trans hqlt
          exact ⟨s, by
            rw [List.mem_take_iff_getElem]
            refine ⟨s, ?_, ?_⟩
            · rw [List.length_range]
              exact Nat.lt_min.mpr ⟨hs, hsN⟩
            · simp, hptrue⟩
        rw [List.findIdx_take] at hfindlt
        simp [q] at hfindlt

/-- The executable first-failure search returns either `N` when every density
edge is safe, or the least failed edge below `N`. -/
lemma restrictedEffectiveFirstFailedScale_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    {stateCode badCode : BitString}
    {state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t}
    {bad : Finset BitString}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad) :
    let q := restrictedEffectiveFirstFailedScale
      (𝒜.overhead ambientLength) sizes stateCode badCode
    q ≤ N ∧
      ((q = N ∧ ∀ s < N, ¬ restrictedSampledDensityFails state bad s) ∨
        (q < N ∧ restrictedSampledDensityFails state bad q ∧
          ∀ s < q, ¬ restrictedSampledDensityFails state bad s)) := by
  let p : ℕ → Bool := fun s =>
    restrictedEffectiveDensityFailsBool (𝒜.overhead ambientLength)
      ((sizes, stateCode, badCode), s)
  have hlength : sizes.length - 1 = N := by omega
  obtain ⟨hq, hcases⟩ := findIdx_range_spec p N
  have hqdef : restrictedEffectiveFirstFailedScale
      (𝒜.overhead ambientLength) sizes stateCode badCode =
        (List.range N).findIdx p := by
    simp [restrictedEffectiveFirstFailedScale, p, hlength]
  rw [hqdef]
  refine ⟨hq, ?_⟩
  rcases hcases with hnone | hfailed
  · refine Or.inl ⟨hnone.1, ?_⟩
    intro s hs hfail
    have hptrue : p s = true :=
      (restrictedEffectiveDensityFailsBool_iff 𝒜 N ambientLength t sizes
        hpowers hstate hbad s hs).2 hfail
    have hfalse := hnone.2 s hs
    exact Bool.noConfusion (hptrue.symm.trans hfalse)
  · refine Or.inr ⟨hfailed.1, ?_, ?_⟩
    · exact (restrictedEffectiveDensityFailsBool_iff 𝒜 N ambientLength t sizes
        hpowers hstate hbad _ hfailed.1).1 hfailed.2.1
    · intro s hs hfail
      have hsN : s < N := hs.trans hfailed.1
      have hptrue : p s = true :=
        (restrictedEffectiveDensityFailsBool_iff 𝒜 N ambientLength t sizes
          hpowers hstate hbad s hsN).2 hfail
      have hpfalse := hfailed.2.2 s hs
      exact Bool.noConfusion (hptrue.symm.trans hpfalse)

/-- Under the decoded-state and decreasing-size hypotheses, the effective
one-event suffix search terminates.  Correctness of the decoded output is kept
separate in `restrictedEffectiveSampledRun_step_spec`. -/
lemma restrictedEffectiveSampledRunStep_terminates
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hmono : ∀ s < N, t (s + 1) ≤ t s)
    {stateCode badCode : BitString}
    {state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t}
    {bad : Finset BitString}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad) :
    ∃ output : BitString,
      restrictedEffectiveSampledRunStep 𝒜 (𝒜.overhead ambientLength)
        sizes stateCode badCode = Part.some output := by
  let q := restrictedEffectiveFirstFailedScale
    (𝒜.overhead ambientLength) sizes stateCode badCode
  let modelCodes := decodeListCode (restrictedSelectorField stateCode 1)
  let liveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let suffixSizes := sizes.drop (q + 1)
  have hqspec := restrictedEffectiveFirstFailedScale_spec
    𝒜 N ambientLength t sizes hlen hpowers hstate hbad
  have hq : q ≤ N := hqspec.1
  have hmodelLength : modelCodes.length = N + 1 := hstate.1
  have hAcode : decodeCoverCodeList (modelCodes.getD q []) =
      canonicalFinsetList (state.B q) := (hstate.2 q hq).1
  have hCcode : decodeCoverCodeList (liveCodes.getD q []) =
      canonicalFinsetList (state.live q \ bad) :=
    restrictedEffectiveLiveCodesAfterDelete_decode
      𝒜 N ambientLength t hstate hbad q hq
  have hdrop_getD : ∀ i < suffixSizes.length,
      suffixSizes.getD i 0 = sizes.getD (q + 1 + i) 0 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    have hindex : q + 1 + i < sizes.length := by
      have := hi
      simp only [suffixSizes, List.length_drop] at this
      omega
    rw [List.getD_eq_getElem _ _ hindex, List.getElem_drop]
  have hsuffix_pos : ∀ i < suffixSizes.length,
      0 < suffixSizes.getD i 0 := by
    intro i hi
    rw [hdrop_getD i hi]
    have hiN : q + 1 + i ≤ N := by
      have := hi
      simp [suffixSizes, List.length_drop, hlen] at this
      omega
    rw [hpowers (q + 1 + i) hiN]
    positivity
  have hsuffix_head : suffixSizes.getD 0 0 ≤ sizes.getD q 0 := by
    by_cases hqN : q < N
    · have hnonempty : 0 < suffixSizes.length := by
        simp [suffixSizes, List.length_drop, hlen]
        omega
      rw [hdrop_getD 0 hnonempty, hpowers (q + 1) (by omega),
        hpowers q hq]
      exact Nat.pow_le_pow_right (by decide) (hmono q hqN)
    · have hqeq : q = N := by omega
      have hsuffix_nil : suffixSizes = [] := by
        apply List.drop_eq_nil_iff.mpr
        simp [hlen, hqeq]
      rw [hsuffix_nil]
      exact Nat.zero_le _
  have hsuffix_mono : ∀ i, i + 1 < suffixSizes.length →
      suffixSizes.getD (i + 1) 0 ≤ suffixSizes.getD i 0 := by
    intro i hi
    have hi0 : i < suffixSizes.length := by omega
    rw [hdrop_getD (i + 1) hi, hdrop_getD i hi0]
    have hindex : q + 1 + i < N := by
      have := hi
      simp [suffixSizes, List.length_drop, hlen] at this
      omega
    rw [hpowers (q + 1 + (i + 1)) (by omega),
      hpowers (q + 1 + i) (by omega)]
    exact Nat.pow_le_pow_right (by decide) (hmono (q + 1 + i) hindex)
  have hCsub : state.live q \ bad ⊆ state.B q :=
    Finset.sdiff_subset.trans (state.live_subset q hq)
  have hCn : ∀ x ∈ state.live q \ bad, x.length = ambientLength := by
    intro x hx
    exact state.live_ambient q hq x (Finset.mem_sdiff.mp hx).1
  have hAcard : (state.B q).card ≤ sizes.getD q 0 := by
    rw [hpowers q hq]
    exact state.size_bound q hq
  obtain ⟨rawOutput, Afinal, Cfinal, codes, hrun, hrawOutput,
      htrace, hcodesLength, hsteps⟩ :=
    restrictedEffectiveRebuildSuffix_decodes_density 𝒜
      (modelCodes.getD q []) (liveCodes.getD q []) suffixSizes
      (𝒜.overhead ambientLength) ambientLength (sizes.getD q 0)
      (state.B q) (state.live q \ bad) hAcode hCcode rfl
      (state.mem_family q hq) hCsub hCn hAcard hsuffix_pos
      hsuffix_head hsuffix_mono
  refine ⟨restrictedEffectiveSampledRunStepPost
      (𝒜.overhead ambientLength)
      ((sizes, stateCode, badCode), rawOutput), ?_⟩
  unfold restrictedEffectiveSampledRunStep
  rw [show restrictedEffectiveSampledRunStepInput
      (𝒜.overhead ambientLength) (sizes, stateCode, badCode) =
        restrictedEffectiveRebuildSuffixInput (modelCodes.getD q [])
          (liveCodes.getD q []) suffixSizes
          (𝒜.overhead ambientLength) by
      simp [restrictedEffectiveSampledRunStepInput, q, modelCodes,
        liveCodes, suffixSizes]]
  rw [hrun]
  rfl

/-- Splicing the retained model prefix with the rebuilt suffix preserves the
required sampled-state code length. -/
lemma restrictedEffectiveSampledRun_splice_length
    {α : Type} (N q : ℕ) (modelCodes codes : List α)
    (hmodelLength : modelCodes.length = N + 1) (hq : q ≤ N)
    (hcodesLength : codes.length = N - q + 1) :
    (modelCodes.take q ++ codes).length = N + 1 := by
  grind

/-- Before the rebuild point, lookup in the spliced model trace is lookup in
the retained old prefix. -/
lemma restrictedEffectiveSampledRun_splice_getD_prefix
    {α : Type} (modelCodes codes : List α) (fallback : α) {q s : ℕ}
    (hq : q ≤ modelCodes.length) (hs : s < q) :
    (modelCodes.take q ++ codes).getD s fallback =
      modelCodes.getD s fallback := by
  grind +suggestions

/-- At and after the rebuild point, lookup in the spliced model trace is
lookup in the newly emitted suffix. -/
lemma restrictedEffectiveSampledRun_splice_getD_suffix
    {α : Type} (modelCodes codes : List α) (fallback : α) {q i : ℕ}
    (hq : q ≤ modelCodes.length) :
    (modelCodes.take q ++ codes).getD (q + i) fallback =
      codes.getD i fallback := by
  grind +qlia

/-- A suffix trace always keeps its initial predecessor code at index zero. -/
lemma restrictedEffectiveRebuildCodeTrace_getD_zero
    {𝒜 : DescriptionFamily} {q0 : ℕ} {sizes : List ℕ}
    {Acode Ccode : BitString} {count : ℕ} {Afinal Cfinal : BitString}
    {codes : List BitString}
    (htrace : RestrictedEffectiveRebuildCodeTrace 𝒜 q0 sizes Acode Ccode
      count Afinal Cfinal codes) :
    codes.getD 0 [] = Acode := by
  induction htrace with
  | nil => rfl
  | @cons idx AcurCode CcurCode Bcode previous hprev hstep ih =>
      have hne : previous ≠ [] := by
        cases hprev <;> simp
      rw [List.getD_append previous [Bcode] [] 0
        (List.length_pos_of_ne_nil hne)]
      exact ih

/-- Replaying a spliced model list agrees with replaying the old list strictly
below the splice point. -/
lemma restrictedEffectiveRebuildLiveCodes_splice_getD_prefix
    (rootCode : BitString) (modelCodes codes : List BitString)
    {q s : ℕ} (hq : q ≤ modelCodes.length) (hs : s < q) :
    (restrictedEffectiveRebuildLiveCodes rootCode
        (modelCodes.take q ++ codes)).getD s [] =
      (restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD s [] := by
  have hqpos : 0 < q := by omega
  have htakeLength : (modelCodes.take q).length = q := by
    simp [List.length_take, Nat.min_eq_left hq]
  have htakeNe : modelCodes.take q ≠ [] := by
    exact List.ne_nil_of_length_pos (by omega)
  have hnewPrefix := restrictedEffectiveRebuildLiveCodes_prefix_append
    rootCode (modelCodes.take q) codes htakeNe
  have holdPrefix0 := restrictedEffectiveRebuildLiveCodes_prefix_append
    rootCode (modelCodes.take q) (modelCodes.drop q) htakeNe
  have holdPrefix :
      restrictedEffectiveRebuildLiveCodes rootCode (modelCodes.take q) <+:
        restrictedEffectiveRebuildLiveCodes rootCode modelCodes := by
    simpa only [List.take_append_drop] using holdPrefix0
  have hliveLength :
      (restrictedEffectiveRebuildLiveCodes rootCode
        (modelCodes.take q)).length = q := by
    rw [restrictedEffectiveRebuildLiveCodes_length, htakeLength]
  obtain ⟨newExtra, hnewEq⟩ := hnewPrefix
  obtain ⟨oldExtra, holdEq⟩ := holdPrefix
  rw [← hnewEq, ← holdEq,
    List.getD_append _ newExtra [] s (by omega),
    List.getD_append _ oldExtra [] s (by omega)]

/-- At and after a splice, replaying the full model list agrees with replaying
the emitted suffix from the old live code at the splice point. -/
lemma restrictedEffectiveRebuildLiveCodes_splice_getD_suffix
    (rootCode : BitString) (modelCodes codes : List BitString)
    {q i : ℕ} (hq : q < modelCodes.length)
    (hcode0 : codes.getD 0 [] = modelCodes.getD q [])
    (hi : i < codes.length) :
    (restrictedEffectiveRebuildLiveCodes rootCode
        (modelCodes.take q ++ codes)).getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD q [])
        codes).getD i [] := by
  have hqle : q ≤ modelCodes.length := Nat.le_of_lt hq
  have htakeLength : (modelCodes.take q).length = q := by
    simp [List.length_take, Nat.min_eq_left hqle]
  have hnewLength : (modelCodes.take q ++ codes).length = q + codes.length := by
    simp [htakeLength]
  induction i with
  | zero =>
      have hcodesNe : codes ≠ [] := by
        intro hnil
        simp [hnil] at hi
      have hsuffixZero :
          (restrictedEffectiveRebuildLiveCodes
            ((restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD q [])
            codes).getD 0 [] =
            (restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD q [] := by
        exact restrictedEffectiveRebuildLiveCodes_getD_zero _ _ hcodesNe
      rw [Nat.add_zero, hsuffixZero]
      cases q with
      | zero =>
          have hmodelsNe : modelCodes ≠ [] := by
            intro hnil
            simp [hnil] at hq
          simpa using
            (restrictedEffectiveRebuildLiveCodes_getD_zero rootCode
              (modelCodes.take 0 ++ codes) (by simpa using hcodesNe)).trans
            (restrictedEffectiveRebuildLiveCodes_getD_zero rootCode
              modelCodes hmodelsNe).symm
      | succ q =>
          have hnewSucc : q + 1 < (modelCodes.take (q + 1) ++ codes).length := by
            simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hq)]
            omega
          rw [restrictedEffectiveRebuildLiveCodes_succ_getD rootCode
            (modelCodes.take (q + 1) ++ codes) q hnewSucc]
          rw [restrictedEffectiveRebuildLiveCodes_succ_getD rootCode
            modelCodes q hq]
          rw [restrictedEffectiveRebuildLiveCodes_splice_getD_prefix
            rootCode modelCodes codes (q := q + 1) (s := q)
            (Nat.le_of_lt hq) (by omega)]
          rw [restrictedEffectiveSampledRun_splice_getD_suffix
            modelCodes codes [] (q := q + 1) (i := 0)
            (Nat.le_of_lt hq)]
          exact congrArg (restrictedLiveIntersectionCode
            ((restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD q []))
            hcode0
  | succ i ih =>
      have hi' : i < codes.length := by omega
      have hnewSucc : q + i + 1 < (modelCodes.take q ++ codes).length := by
        rw [hnewLength]
        omega
      rw [show q + (i + 1) = (q + i) + 1 by omega]
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD rootCode
        (modelCodes.take q ++ codes) (q + i) hnewSucc]
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD
        ((restrictedEffectiveRebuildLiveCodes rootCode modelCodes).getD q [])
        codes i hi]
      rw [ih hi']
      have hmodelAt :
          (modelCodes.take q ++ codes).getD (q + i + 1) [] =
            codes.getD (i + 1) [] := by
        simpa [Nat.add_assoc] using
          (restrictedEffectiveSampledRun_splice_getD_suffix
            modelCodes codes [] (q := q) (i := i + 1) hqle)
      rw [hmodelAt]

/-- One effective event has the same least-failed-edge contract as the
extensional transition, without claiming equality to its arbitrary
`Classical.choose` witness. -/
lemma restrictedEffectiveSampledRun_step_decodes_splice
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString)
    (q : ℕ)
    (modelCodes codes : List BitString)
    (hlen : sizes.length = N + 1)
    (hmodelCodes : modelCodes =
      decodeListCode (restrictedSelectorField stateCode 1))
    (hmodelLength : modelCodes.length = N + 1)
    (hq_le : q ≤ N)
    (hcodesLength : codes.length = N - q + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hprefix : ∀ s < q, ¬ restrictedSampledDensityFails state bad s)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
    (Afinal Cfinal : BitString)
    (htrace : RestrictedEffectiveRebuildCodeTrace 𝒜 (𝒜.overhead ambientLength)
      (sizes.drop (q + 1)) (modelCodes.getD q [])
      ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
      (sizes.drop (q + 1)).length Afinal Cfinal codes)
    (hsteps : ∀ i < (sizes.drop (q + 1)).length, ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q []) codes).getD i []) =
          canonicalFinsetList Cprev ∧
        decodeCoverCodeList (codes.getD (i + 1) []) =
          canonicalFinsetList Bnext ∧
        𝒜.mem Bprev ∧
        Bprev.card ≤ (if i = 0 then sizes.getD q 0 else sizes.getD (q + 1 + (i - 1)) 0) ∧
        Cprev ⊆ Bprev ∧
        (∀ x ∈ Cprev, x.length = ambientLength) ∧
        𝒜.mem Bnext ∧
        Bnext.card ≤ sizes.getD (q + 1 + i) 0 ∧
        sizes.getD (q + 1 + i) 0 * Cprev.card ≤
          (𝒜.overhead ambientLength *
            (if i = 0 then sizes.getD q 0 else sizes.getD (q + 1 + (i - 1)) 0)) *
            (Bnext ∩ Cprev).card) :
    ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        DecodesToRestrictedSampledRunState
          (restrictedEffectiveSampledStateCode
            (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
            (modelCodes.take q ++ codes)) next := by
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let oldDeletedLiveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  let suffixRootCode := oldDeletedLiveCodes.getD q []
  let suffixLiveCodes := restrictedEffectiveRebuildLiveCodes suffixRootCode codes
  have hqModel : q < modelCodes.length := by omega
  have hnewModelLength : newModelCodes.length = N + 1 := by
    exact restrictedEffectiveSampledRun_splice_length N q modelCodes codes
      hmodelLength hq_le hcodesLength
  have htrace0 : codes.getD 0 [] = modelCodes.getD q [] :=
    restrictedEffectiveRebuildCodeTrace_getD_zero htrace
  have hsuffixRoot : suffixRootCode =
      (restrictedEffectiveRebuildLiveCodes deletedRootCode modelCodes).getD q [] := by
    simp [suffixRootCode, oldDeletedLiveCodes,
      restrictedEffectiveLiveCodesAfterDelete, deletedRootCode, ← hmodelCodes]
  have halignSuffix : ∀ i < codes.length,
      newLiveCodes.getD (q + i) [] = suffixLiveCodes.getD i [] := by
    intro i hi
    dsimp [newLiveCodes, newModelCodes, suffixLiveCodes]
    rw [hsuffixRoot]
    exact restrictedEffectiveRebuildLiveCodes_splice_getD_suffix
      deletedRootCode modelCodes codes hqModel htrace0 hi
  have hmodelRetained : ∀ s ≤ q,
      decodeCoverCodeList (newModelCodes.getD s []) =
        canonicalFinsetList (state.B s) := by
    intro s hs
    by_cases hsq : s < q
    · rw [show newModelCodes.getD s [] = modelCodes.getD s [] by
        exact restrictedEffectiveSampledRun_splice_getD_prefix
          modelCodes codes [] (Nat.le_of_lt hqModel) hsq]
      simpa [hmodelCodes] using (hstate.2 s (hs.trans hq_le)).1
    · have hsqeq : s = q := by omega
      subst s
      rw [show newModelCodes.getD q [] = codes.getD 0 [] by
        exact restrictedEffectiveSampledRun_splice_getD_suffix
          modelCodes codes [] (q := q) (i := 0) (Nat.le_of_lt hqModel)]
      rw [htrace0]
      simpa [hmodelCodes] using (hstate.2 q hq_le).1
  have hliveRetained : ∀ s ≤ q,
      decodeCoverCodeList (newLiveCodes.getD s []) =
        canonicalFinsetList (state.live s \ bad) := by
    intro s hs
    by_cases hsq : s < q
    · have halign : newLiveCodes.getD s [] = oldDeletedLiveCodes.getD s [] := by
        dsimp [newLiveCodes, newModelCodes, oldDeletedLiveCodes,
          restrictedEffectiveLiveCodesAfterDelete]
        rw [← hmodelCodes]
        exact restrictedEffectiveRebuildLiveCodes_splice_getD_prefix
          deletedRootCode modelCodes codes (Nat.le_of_lt hqModel) hsq
      rw [halign]
      exact restrictedEffectiveLiveCodesAfterDelete_decode
        𝒜 N ambientLength t hstate hbad s (hs.trans hq_le)
    · have hsqeq : s = q := by omega
      subst s
      have hcodesPos : 0 < codes.length := by omega
      have halign0 : newLiveCodes.getD q [] = suffixLiveCodes.getD 0 [] := by
        simpa using halignSuffix 0 hcodesPos
      rw [halign0]
      have hsuffixZero : suffixLiveCodes.getD 0 [] = suffixRootCode := by
        have hcodesNe : codes ≠ [] := List.ne_nil_of_length_pos hcodesPos
        simpa [suffixLiveCodes] using
          (restrictedEffectiveRebuildLiveCodes_getD_zero
            suffixRootCode codes hcodesNe)
      rw [hsuffixZero]
      exact restrictedEffectiveLiveCodesAfterDelete_decode
        𝒜 N ambientLength t hstate hbad q hq_le
  have hstepData : ∀ s ≤ N, ∃ Bcur Ccur : Finset BitString,
      decodeCoverCodeList (newModelCodes.getD s []) = canonicalFinsetList Bcur ∧
      decodeCoverCodeList (newLiveCodes.getD s []) = canonicalFinsetList Ccur ∧
      𝒜.mem Bcur ∧
      Bcur.card ≤ 2 ^ t s ∧
      Ccur ⊆ Bcur ∧
      (∀ x ∈ Ccur, x.length = ambientLength) := by
    intro s hsN
    by_cases hsq : s ≤ q
    · refine ⟨state.B s, state.live s \ bad,
        hmodelRetained s hsq, hliveRetained s hsq,
        state.mem_family s hsN, state.size_bound s hsN, ?_, ?_⟩
      · exact Finset.sdiff_subset.trans (state.live_subset s hsN)
      · intro x hx
        exact state.live_ambient s hsN x (Finset.mem_sdiff.mp hx).1
    · let i := s - (q + 1)
      have hi : i < (sizes.drop (q + 1)).length := by
        simp [i, List.length_drop, hlen]
        omega
      have hsi : s = q + 1 + i := by
        dsimp [i]
        omega
      obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
        hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
        hBnextMem, hBnextCard, hdensity⟩ := hsteps i hi
      have hiCode : i + 1 < codes.length := by
        rw [hcodesLength]
        omega
      have hmodelCode : decodeCoverCodeList (newModelCodes.getD s []) =
          canonicalFinsetList Bnext := by
        rw [hsi, show q + 1 + i = q + (i + 1) by omega]
        rw [restrictedEffectiveSampledRun_splice_getD_suffix
          modelCodes codes [] (q := q) (i := i + 1)
          (Nat.le_of_lt hqModel)]
        exact hBnextCode
      have hliveCode : decodeCoverCodeList (newLiveCodes.getD s []) =
          canonicalFinsetList (Cprev ∩ Bnext) := by
        rw [hsi, show q + 1 + i = q + (i + 1) by omega,
          halignSuffix (i + 1) hiCode]
        rw [restrictedEffectiveRebuildLiveCodes_succ_getD
          suffixRootCode codes i hiCode]
        exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
          hCprevCode hBnextCode
      refine ⟨Bnext, Cprev ∩ Bnext, hmodelCode, hliveCode,
        hBnextMem, ?_, Finset.inter_subset_right, ?_⟩
      · rw [← hpowers s hsN, hsi]
        simpa [Nat.add_assoc] using hBnextCard
      · intro x hx
        exact hCprevLength x (Finset.inter_subset_left hx)
  let next : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t :=
    { B := fun s => (decodeCoverCodeList (newModelCodes.getD s [])).toFinset
      live := fun s => (decodeCoverCodeList (newLiveCodes.getD s [])).toFinset
      mem_family := by
        intro s hs
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard,
          hCsub, hClength⟩ := hstepData s hs
        rw [hBcode, canonicalFinsetList_toFinset]
        exact hBmem
      size_bound := by
        intro s hs
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard,
          hCsub, hClength⟩ := hstepData s hs
        rw [hBcode, canonicalFinsetList_toFinset]
        exact hBcard
      live_subset := by
        intro s hs
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard,
          hCsub, hClength⟩ := hstepData s hs
        rw [hCcode, hBcode, canonicalFinsetList_toFinset,
          canonicalFinsetList_toFinset]
        exact hCsub
      live_ambient := by
        intro s hs x hx
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard,
          hCsub, hClength⟩ := hstepData s hs
        rw [hCcode, canonicalFinsetList_toFinset] at hx
        exact hClength x hx
      live_monotonic := by
        intro s hsN
        by_cases hsq : s < q
        · have hsle : s ≤ q := by omega
          have hsuccle : s + 1 ≤ q := by omega
          rw [hliveRetained s hsle, hliveRetained (s + 1) hsuccle,
            canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
          intro x hx
          exact Finset.mem_sdiff.mpr
            ⟨state.live_monotonic s hsN (Finset.mem_sdiff.mp hx).1,
              (Finset.mem_sdiff.mp hx).2⟩
        · let i := s - q
          have hsi : s = q + i := by dsimp [i]; omega
          have hi : i < (sizes.drop (q + 1)).length := by
            simp [i, List.length_drop, hlen]
            omega
          obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
            hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
            hBnextMem, hBnextCard, hdensity⟩ := hsteps i hi
          have hiCode : i + 1 < codes.length := by
            rw [hcodesLength]
            omega
          have hcurrent : decodeCoverCodeList (newLiveCodes.getD s []) =
              canonicalFinsetList Cprev := by
            rw [hsi, halignSuffix i
              (Nat.lt_trans (Nat.lt_succ_self i) hiCode)]
            exact hCprevCode
          have hnextCode : decodeCoverCodeList (newLiveCodes.getD (s + 1) []) =
              canonicalFinsetList (Cprev ∩ Bnext) := by
            rw [hsi, show q + i + 1 = q + (i + 1) by omega,
              halignSuffix (i + 1) hiCode]
            rw [restrictedEffectiveRebuildLiveCodes_succ_getD
              suffixRootCode codes i hiCode]
            exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
              hCprevCode hBnextCode
          rw [hcurrent, hnextCode, canonicalFinsetList_toFinset,
            canonicalFinsetList_toFinset]
          exact Finset.inter_subset_left
      density := by
        intro s hsN
        by_cases hsq : s < q
        · have hsle : s ≤ q := by omega
          have hsuccle : s + 1 ≤ q := by omega
          rw [hliveRetained s hsle, hliveRetained (s + 1) hsuccle,
            canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
          exact Nat.le_of_not_gt (hprefix s hsq)
        · let i := s - q
          have hsi : s = q + i := by dsimp [i]; omega
          have hi : i < (sizes.drop (q + 1)).length := by
            simp [i, List.length_drop, hlen]
            omega
          obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
            hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
            hBnextMem, hBnextCard, hdensity⟩ := hsteps i hi
          have hiCode : i + 1 < codes.length := by
            rw [hcodesLength]
            omega
          have hcurrent : decodeCoverCodeList (newLiveCodes.getD s []) =
              canonicalFinsetList Cprev := by
            rw [hsi, halignSuffix i
              (Nat.lt_trans (Nat.lt_succ_self i) hiCode)]
            exact hCprevCode
          have hnextCode : decodeCoverCodeList (newLiveCodes.getD (s + 1) []) =
              canonicalFinsetList (Cprev ∩ Bnext) := by
            rw [hsi, show q + i + 1 = q + (i + 1) by omega,
              halignSuffix (i + 1) hiCode]
            rw [restrictedEffectiveRebuildLiveCodes_succ_getD
              suffixRootCode codes i hiCode]
            exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
              hCprevCode hBnextCode
          rw [hcurrent, hnextCode, canonicalFinsetList_toFinset,
            canonicalFinsetList_toFinset]
          have hprevSize :
              (if i = 0 then sizes.getD q 0
                else sizes.getD (q + 1 + (i - 1)) 0) =
                sizes.getD (q + i) 0 := by
            by_cases hi0 : i = 0
            · simp [hi0]
            · rw [if_neg hi0]
              congr 1
              omega
          have hsSucc : s + 1 = q + 1 + i := by omega
          have hdensity' :
              (2 ^ t (s + 1)) * Cprev.card ≤
                (𝒜.overhead ambientLength * 2 ^ t s) *
                  (Cprev ∩ Bnext).card := by
            rw [← hpowers (s + 1) (by omega), ← hpowers s (by omega),
              hsSucc, hsi, Finset.inter_comm, ← hprevSize]
            simpa [Nat.add_assoc, Nat.add_comm i 1] using hdensity
          exact hdensity'.trans (by
            gcongr
            omega) }
  refine ⟨next, ?_⟩
  dsimp [DecodesToRestrictedSampledRunState]
  simp only [restrictedSelectorField_sampledState_zero,
    restrictedSelectorField_sampledState_one]
  refine ⟨hnewModelLength, ?_⟩
  intro s hs
  obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard,
    hCsub, hClength⟩ := hstepData s hs
  constructor
  · dsimp [next]
    rw [hBcode, canonicalFinsetList_toFinset]
  · dsimp [next]
    rw [hCcode, canonicalFinsetList_toFinset]

lemma restrictedEffectiveSampledRun_step_contract
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString)
    (q : ℕ)
    (modelCodes codes : List BitString)
    (hmodelCodes : modelCodes =
      decodeListCode (restrictedSelectorField stateCode 1))
    (hmodelLength : modelCodes.length = N + 1)
    (hq_le : q ≤ N)
    (hq_cases : (q = N ∧ ∀ s < N, ¬ restrictedSampledDensityFails state bad s) ∨
      (q < N ∧ restrictedSampledDensityFails state bad q ∧
        ∀ s < q, ¬ restrictedSampledDensityFails state bad s))
    (hcodesLength : codes.length = N - q + 1)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
    (next : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (hnext : DecodesToRestrictedSampledRunState
      (restrictedEffectiveSampledStateCode
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)) next)
    (Afinal Cfinal : BitString)
    (htrace : RestrictedEffectiveRebuildCodeTrace 𝒜 (𝒜.overhead ambientLength)
      (sizes.drop (q + 1)) (modelCodes.getD q [])
      ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
      (sizes.drop (q + 1)).length Afinal Cfinal codes)
    (hsteps : ∀ i < (sizes.drop (q + 1)).length, ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q []) codes).getD i []) =
          canonicalFinsetList Cprev ∧
        decodeCoverCodeList (codes.getD (i + 1) []) =
          canonicalFinsetList Bnext ∧
        𝒜.mem Bprev ∧
        Bprev.card ≤ (if i = 0 then sizes.getD q 0 else sizes.getD (q + 1 + (i - 1)) 0) ∧
        Cprev ⊆ Bprev ∧
        (∀ x ∈ Cprev, x.length = ambientLength) ∧
        𝒜.mem Bnext ∧
        Bnext.card ≤ sizes.getD (q + 1 + i) 0 ∧
        sizes.getD (q + 1 + i) 0 * Cprev.card ≤
          (𝒜.overhead ambientLength *
            (if i = 0 then sizes.getD q 0 else sizes.getD (q + 1 + (i - 1)) 0)) *
            (Bnext ∩ Cprev).card) :
    RestrictedSampledRunStepSpec state next bad q := by
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let oldDeletedLiveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  let suffixRootCode := oldDeletedLiveCodes.getD q []
  let suffixLiveCodes := restrictedEffectiveRebuildLiveCodes suffixRootCode codes
  have hqModel : q < modelCodes.length := by omega
  have htrace0 : codes.getD 0 [] = modelCodes.getD q [] :=
    restrictedEffectiveRebuildCodeTrace_getD_zero htrace
  have hsuffixRoot : suffixRootCode =
      (restrictedEffectiveRebuildLiveCodes deletedRootCode modelCodes).getD q [] := by
    simp [suffixRootCode, oldDeletedLiveCodes,
      restrictedEffectiveLiveCodesAfterDelete, deletedRootCode, ← hmodelCodes]
  have halignSuffix : ∀ i < codes.length,
      newLiveCodes.getD (q + i) [] = suffixLiveCodes.getD i [] := by
    intro i hi
    dsimp [newLiveCodes, newModelCodes, suffixLiveCodes]
    rw [hsuffixRoot]
    exact restrictedEffectiveRebuildLiveCodes_splice_getD_suffix
      deletedRootCode modelCodes codes hqModel htrace0 hi
  have hnext' := hnext
  dsimp [DecodesToRestrictedSampledRunState] at hnext'
  simp only [restrictedSelectorField_sampledState_zero,
    restrictedSelectorField_sampledState_one] at hnext'
  have hretained : ∀ s ≤ q,
      next.B s = state.B s ∧ next.live s = state.live s \ bad := by
    intro s hs
    have hsN : s ≤ N := hs.trans hq_le
    have hnewModelCode : newModelCodes.getD s [] = modelCodes.getD s [] := by
      by_cases hsq : s < q
      · exact restrictedEffectiveSampledRun_splice_getD_prefix
          modelCodes codes [] (Nat.le_of_lt hqModel) hsq
      · have hsqeq : s = q := by omega
        subst s
        calc
          newModelCodes.getD q [] = codes.getD 0 [] :=
            restrictedEffectiveSampledRun_splice_getD_suffix
              modelCodes codes [] (q := q) (i := 0)
                (Nat.le_of_lt hqModel)
          _ = modelCodes.getD q [] := htrace0
    have hBcanonical : canonicalFinsetList (state.B s) =
        canonicalFinsetList (next.B s) := by
      have holdModel := (hstate.2 s hsN).1
      rw [← hmodelCodes] at holdModel
      rw [← holdModel, ← (hnext'.2 s hsN).1, hnewModelCode]
    have hBeq : next.B s = state.B s := by
      have hfin := congrArg List.toFinset hBcanonical
      simpa only [canonicalFinsetList_toFinset] using hfin.symm
    have hnewLiveCode : newLiveCodes.getD s [] = oldDeletedLiveCodes.getD s [] := by
      by_cases hsq : s < q
      · dsimp [newLiveCodes, newModelCodes, oldDeletedLiveCodes,
          restrictedEffectiveLiveCodesAfterDelete]
        rw [← hmodelCodes]
        exact restrictedEffectiveRebuildLiveCodes_splice_getD_prefix
          deletedRootCode modelCodes codes (Nat.le_of_lt hqModel) hsq
      · have hsqeq : s = q := by omega
        subst s
        have hcodesPos : 0 < codes.length := by omega
        have halign0 : newLiveCodes.getD q [] = suffixLiveCodes.getD 0 [] := by
          simpa using halignSuffix 0 hcodesPos
        rw [halign0]
        have hcodesNe : codes ≠ [] := List.ne_nil_of_length_pos hcodesPos
        simpa [suffixLiveCodes] using
          (restrictedEffectiveRebuildLiveCodes_getD_zero
            suffixRootCode codes hcodesNe)
    have holdDecode := restrictedEffectiveLiveCodesAfterDelete_decode
      𝒜 N ambientLength t hstate hbad s hsN
    have hCcanonical : canonicalFinsetList (state.live s \ bad) =
        canonicalFinsetList (next.live s) := by
      rw [← holdDecode, ← (hnext'.2 s hsN).2, hnewLiveCode]
    have hCeq : next.live s = state.live s \ bad := by
      have hfin := congrArg List.toFinset hCcanonical
      simpa only [canonicalFinsetList_toFinset] using hfin.symm
    exact ⟨hBeq, hCeq⟩
  have hliveSubQ : ∀ s, q ≤ s → s ≤ N → next.live s ⊆ next.live q := by
    intro s hqs
    induction hqs with
    | refl =>
        intro _
        exact Finset.Subset.rfl
    | @step s hqs ih =>
        intro hsN
        exact (next.live_monotonic s (by omega)).trans (ih (by omega))
  refine ⟨hq_le, hq_cases, hretained, ?_, ?_⟩
  · intro s hqs hsN
    have hsub := hliveSubQ s hqs hsN
    simpa [(hretained q le_rfl).2] using hsub
  · intro s hqs hsN
    let i := s - q
    have hsi : s = q + i := by dsimp [i]; omega
    have hi : i < (sizes.drop (q + 1)).length := by
      simp [i, List.length_drop, hlen]
      omega
    obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
      hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
      hBnextMem, hBnextCard, hdensity⟩ := hsteps i hi
    have hiCode : i + 1 < codes.length := by
      rw [hcodesLength]
      omega
    have hcurrentCode : decodeCoverCodeList (newLiveCodes.getD s []) =
        canonicalFinsetList Cprev := by
      rw [hsi, halignSuffix i
        (Nat.lt_trans (Nat.lt_succ_self i) hiCode)]
      exact hCprevCode
    have hnextCode : decodeCoverCodeList (newLiveCodes.getD (s + 1) []) =
        canonicalFinsetList (Cprev ∩ Bnext) := by
      rw [hsi, show q + i + 1 = q + (i + 1) by omega,
        halignSuffix (i + 1) hiCode]
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD
        suffixRootCode codes i hiCode]
      exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext
        hCprevCode hBnextCode
    have hcurrentEq : next.live s = Cprev := by
      have hcanonical : canonicalFinsetList Cprev =
          canonicalFinsetList (next.live s) := by
        rw [← hcurrentCode]
        exact (hnext'.2 s (by omega)).2
      have hfin := congrArg List.toFinset hcanonical
      simpa only [canonicalFinsetList_toFinset] using hfin.symm
    have hnextEq : next.live (s + 1) = Cprev ∩ Bnext := by
      have hcanonical : canonicalFinsetList (Cprev ∩ Bnext) =
          canonicalFinsetList (next.live (s + 1)) := by
        rw [← hnextCode]
        exact (hnext'.2 (s + 1) (by omega)).2
      have hfin := congrArg List.toFinset hcanonical
      simpa only [canonicalFinsetList_toFinset] using hfin.symm
    rw [hcurrentEq, hnextEq]
    have hprevSize :
        (if i = 0 then sizes.getD q 0
          else sizes.getD (q + 1 + (i - 1)) 0) =
          sizes.getD (q + i) 0 := by
      by_cases hi0 : i = 0
      · simp [hi0]
      · rw [if_neg hi0]
        congr 1
        omega
    have hsSucc : s + 1 = q + 1 + i := by omega
    have hdensity' :
        (2 ^ t (s + 1)) * Cprev.card ≤
          (𝒜.overhead ambientLength * 2 ^ t s) *
            (Cprev ∩ Bnext).card := by
      rw [← hpowers (s + 1) (by omega), ← hpowers s (by omega),
        hsSucc, hsi, Finset.inter_comm, ← hprevSize]
      simpa [Nat.add_assoc, Nat.add_comm i 1] using hdensity
    calc
      2 * ((2 ^ t (s + 1)) * Cprev.card) ≤
          2 * ((𝒜.overhead ambientLength * 2 ^ t s) *
            (Cprev ∩ Bnext).card) := Nat.mul_le_mul_left 2 hdensity'
      _ = ((2 * 𝒜.overhead ambientLength) * 2 ^ t s) *
            (Cprev ∩ Bnext).card := by ring

lemma restrictedEffectiveSampledRun_step_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hmono : ∀ s < N, t (s + 1) ≤ t s)
    {stateCode badCode : BitString}
    {state : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t}
    {bad : Finset BitString}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad) :
    ∃ output : BitString,
      ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        ∃ q : ℕ,
          restrictedEffectiveSampledRunStep 𝒜 (𝒜.overhead ambientLength)
              sizes stateCode badCode = Part.some output ∧
          DecodesToRestrictedSampledRunState output next ∧
          RestrictedSampledRunStepSpec state next bad q := by
  let q := restrictedEffectiveFirstFailedScale
    (𝒜.overhead ambientLength) sizes stateCode badCode
  let modelCodes := decodeListCode (restrictedSelectorField stateCode 1)
  let liveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let suffixSizes := sizes.drop (q + 1)
  have hqspec := restrictedEffectiveFirstFailedScale_spec
    𝒜 N ambientLength t sizes hlen hpowers hstate hbad
  have hq : q ≤ N := hqspec.1
  have hq_cases : (q = N ∧ ∀ (s : ℕ), s < N → ¬restrictedSampledDensityFails state bad s) ∨
    q < N ∧ restrictedSampledDensityFails state bad q ∧ ∀ (s : ℕ), s < q → ¬restrictedSampledDensityFails state bad s := hqspec.2
  have hmodelLength : modelCodes.length = N + 1 := hstate.1
  have hAcode : decodeCoverCodeList (modelCodes.getD q []) =
      canonicalFinsetList (state.B q) := (hstate.2 q hq).1
  have hCcode : decodeCoverCodeList (liveCodes.getD q []) =
      canonicalFinsetList (state.live q \ bad) :=
    restrictedEffectiveLiveCodesAfterDelete_decode
      𝒜 N ambientLength t hstate hbad q hq
  have hdrop_getD : ∀ i < suffixSizes.length,
      suffixSizes.getD i 0 = sizes.getD (q + 1 + i) 0 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    have hindex : q + 1 + i < sizes.length := by
      have := hi
      simp [suffixSizes, List.length_drop] at this
      omega
    rw [List.getD_eq_getElem _ _ hindex, List.getElem_drop]
  have hsuffix_pos : ∀ i < suffixSizes.length,
      0 < suffixSizes.getD i 0 := by
    intro i hi
    rw [hdrop_getD i hi]
    have hiN : q + 1 + i ≤ N := by
      have := hi
      simp [suffixSizes, List.length_drop, hlen] at this
      omega
    rw [hpowers (q + 1 + i) hiN]
    positivity
  have hsuffix_head : suffixSizes.getD 0 0 ≤ sizes.getD q 0 := by
    by_cases hqN : q < N
    · have hnonempty : 0 < suffixSizes.length := by
        simp [suffixSizes, List.length_drop, hlen]
        omega
      rw [hdrop_getD 0 hnonempty, hpowers (q + 1) (by omega),
        hpowers q hq]
      exact Nat.pow_le_pow_right (by decide) (hmono q hqN)
    · have hqeq : q = N := by omega
      subst q
      have hdrop : suffixSizes = [] := by
        apply List.drop_eq_nil_iff.mpr
        simp [hlen, hqeq]
      rw [hdrop]
      exact Nat.zero_le _
  have hsuffix_mono : ∀ i, i + 1 < suffixSizes.length →
      suffixSizes.getD (i + 1) 0 ≤ suffixSizes.getD i 0 := by
    intro i hi
    have hi0 : i < suffixSizes.length := by omega
    rw [hdrop_getD (i + 1) hi, hdrop_getD i hi0]
    have hindex : q + 1 + i < N := by
      have := hi
      simp [suffixSizes, List.length_drop, hlen] at this
      omega
    rw [hpowers (q + 1 + (i + 1)) (by omega),
      hpowers (q + 1 + i) (by omega)]
    exact Nat.pow_le_pow_right (by decide) (hmono (q + 1 + i) hindex)
  have hCsub : state.live q \ bad ⊆ state.B q :=
    Finset.sdiff_subset.trans (state.live_subset q hq)
  have hCn : ∀ x ∈ state.live q \ bad, x.length = ambientLength := by
    intro x hx
    exact state.live_ambient q hq x (Finset.mem_sdiff.mp hx).1
  have hAcard : (state.B q).card ≤ sizes.getD q 0 := by
    rw [hpowers q hq]
    exact state.size_bound q hq
  obtain ⟨rawOutput, Afinal, Cfinal, codes, hrun, hrawOutput,
      htrace, hcodesLength, hsteps⟩ :=
    restrictedEffectiveRebuildSuffix_decodes_density 𝒜
      (modelCodes.getD q []) (liveCodes.getD q []) suffixSizes
      (𝒜.overhead ambientLength) ambientLength (sizes.getD q 0)
      (state.B q) (state.live q \ bad) hAcode hCcode rfl
      (state.mem_family q hq) hCsub hCn hAcard hsuffix_pos
      hsuffix_head hsuffix_mono
  have hcodesLength2 : codes.length = N - q + 1 := by
    rw [hcodesLength]
    simp [suffixSizes]
    omega
  have hsteps2 : ∀ i < (sizes.drop (q + 1)).length,
      ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
          codes).getD i []) = canonicalFinsetList Cprev ∧
        decodeCoverCodeList (codes.getD (i + 1) []) =
          canonicalFinsetList Bnext ∧
        𝒜.mem Bprev ∧
        Bprev.card ≤
          (if i = 0 then sizes.getD q 0
            else sizes.getD (q + 1 + (i - 1)) 0) ∧
        Cprev ⊆ Bprev ∧
        (∀ x ∈ Cprev, x.length = ambientLength) ∧
        𝒜.mem Bnext ∧
        Bnext.card ≤ sizes.getD (q + 1 + i) 0 ∧
        sizes.getD (q + 1 + i) 0 * Cprev.card ≤
          (𝒜.overhead ambientLength *
            (if i = 0 then sizes.getD q 0
              else sizes.getD (q + 1 + (i - 1)) 0)) *
            (Bnext ∩ Cprev).card := by
    intro i hi
    have hiSuffix : i < suffixSizes.length := by
      simpa [suffixSizes] using hi
    obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
      hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
      hBnextMem, hBnextCard, hdensity⟩ := hsteps i hiSuffix
    have hprevSize :
        (if i = 0 then sizes.getD q 0
          else suffixSizes.getD (i - 1) 0) =
        (if i = 0 then sizes.getD q 0
          else sizes.getD (q + 1 + (i - 1)) 0) := by
      by_cases hi0 : i = 0
      · simp [hi0]
      · rw [if_neg hi0, if_neg hi0]
        exact hdrop_getD (i - 1) (by omega)
    refine ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
      hBnextCode, hBprevMem, ?_, hCprevSub, hCprevLength,
      hBnextMem, ?_, ?_⟩
    · rw [hprevSize] at hBprevCard
      exact hBprevCard
    · rw [hdrop_getD i hiSuffix] at hBnextCard
      exact hBnextCard
    · rw [hdrop_getD i hiSuffix, hprevSize] at hdensity
      exact hdensity
  have h_decodes : ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        DecodesToRestrictedSampledRunState
          (restrictedEffectiveSampledStateCode
            (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
            (modelCodes.take q ++ codes)) next := by
    have hprefix : ∀ s < q,
        ¬ restrictedSampledDensityFails state bad s := by
      rcases hq_cases with hnone | hfailed
      · intro s hs
        exact hnone.2 s (by simpa [hnone.1] using hs)
      · exact hfailed.2.2
    exact restrictedEffectiveSampledRun_step_decodes_splice
      𝒜 N ambientLength t sizes stateCode badCode state bad q modelCodes codes
      hlen rfl hmodelLength hq hcodesLength2 hpowers hprefix hstate hbad
      Afinal Cfinal htrace hsteps2
  obtain ⟨next, hnext⟩ := h_decodes
  have h_contract : RestrictedSampledRunStepSpec state next bad q := by
    exact restrictedEffectiveSampledRun_step_contract 𝒜 N ambientLength t
      sizes hlen hpowers stateCode badCode state bad q modelCodes codes
      rfl hmodelLength hq hq_cases hcodesLength2 hstate hbad next hnext
      Afinal Cfinal htrace hsteps2
  refine ⟨restrictedEffectiveSampledRunStepPost
      (𝒜.overhead ambientLength)
      ((sizes, stateCode, badCode), rawOutput), ⟨next, ⟨q, ?_⟩⟩⟩
  refine ⟨?_, ?_, h_contract⟩
  · rw [restrictedEffectiveSampledRunStep]
    have hinput : restrictedEffectiveSampledRunStepInput (𝒜.overhead ambientLength) (sizes, stateCode, badCode) =
      restrictedEffectiveRebuildSuffixInput (modelCodes.getD q []) (liveCodes.getD q []) suffixSizes (𝒜.overhead ambientLength) := by
      simp [restrictedEffectiveSampledRunStepInput, q, modelCodes, liveCodes, suffixSizes]
    rw [hinput, hrun, Part.map_some]
  · unfold restrictedEffectiveSampledRunStepPost
    rw [hrawOutput]
    simpa only [decodeListCode_listCode] using hnext

end Kolmogorov
