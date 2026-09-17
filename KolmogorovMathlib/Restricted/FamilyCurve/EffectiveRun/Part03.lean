import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRebuild
import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.Part02

/-!
# Preservation contract for the effective sampled run

This module proves that one encoded transition preserves the mathematical sampled-run
invariants. Private contract lemmas separately handle retained prefixes, density of rebuilt
suffixes, size schedules and adaptation of the abstract run steps.

`restrictedEffectiveSampledRun_step_contract` combines those components, and
`restrictedEffectiveSampledRun_step_spec` exposes the public transition specification used by
`EffectiveRunSemantics`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- Retained state for scale `s ≤ q` in contract step. -/
private lemma restrictedEffectiveSampledRun_step_contract_retained
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString)
    (q : ℕ) (codes : List BitString)
    (hq_le : q ≤ N)
    (hcodesLength : codes.length = N - q + 1)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
    (next : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (hnext : DecodesToRestrictedSampledRunState
      (restrictedEffectiveSampledStateCode
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        ((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
          codes)) next)
    (htrace0 : codes.getD 0 [] =
      (decodeListCode (restrictedSelectorField stateCode 1)).getD q [])
    (halignSuffix : ∀ i < codes.length,
      (restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        ((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
          codes)).getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i []) :
    ∀ s ≤ q, next.B s = state.B s ∧ next.live s = state.live s \ bad := by
  set modelCodes := decodeListCode (restrictedSelectorField stateCode 1) with hmodelCodes
  have hmodelLength : modelCodes.length = N + 1 := hstate.1
  have hqModel : q < modelCodes.length := by omega
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let oldDeletedLiveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  let suffixRootCode := oldDeletedLiveCodes.getD q []
  let suffixLiveCodes := restrictedEffectiveRebuildLiveCodes suffixRootCode codes
  have hnext' := hnext
  dsimp [DecodesToRestrictedSampledRunState] at hnext'
  simp only [restrictedSelectorField_sampledState_zero,
    restrictedSelectorField_sampledState_one] at hnext'
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
      have hcodesPos : 0 < codes.length := by
        rw [hcodesLength]
        omega
      have halign0 : newLiveCodes.getD q [] = suffixLiveCodes.getD 0 [] := by
        exact halignSuffix 0 hcodesPos
      rw [halign0]
      have hcodesNe : codes ≠ [] := List.ne_nil_of_length_pos hcodesPos
      exact restrictedEffectiveRebuildLiveCodes_getD_zero
          suffixRootCode codes hcodesNe
  have holdDecode := restrictedEffectiveLiveCodesAfterDelete_decode
    𝒜 N ambientLength t hstate hbad s hsN
  have hCcanonical : canonicalFinsetList (state.live s \ bad) =
      canonicalFinsetList (next.live s) := by
    rw [← holdDecode, ← (hnext'.2 s hsN).2, hnewLiveCode]
  have hCeq : next.live s = state.live s \ bad := by
    have hfin := congrArg List.toFinset hCcanonical
    simpa only [canonicalFinsetList_toFinset] using hfin.symm
  exact ⟨hBeq, hCeq⟩

/-- Step density inequality for scale `s ≥ q` in contract step. -/
private lemma restrictedEffectiveSampledRun_step_contract_density
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (stateCode badCode : BitString)
    (q : ℕ) (modelCodes codes : List BitString)
    (hcodesLength : codes.length = N - q + 1)
    (next : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (hnext : DecodesToRestrictedSampledRunState
      (restrictedEffectiveSampledStateCode
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)) next)
    (halignSuffix : ∀ i < codes.length,
      (restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)).getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i [])
    (hsteps : ∀ i < (sizes.drop (q + 1)).length, ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
            codes).getD i []) =
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
    ∀ s, q ≤ s → s < N →
      2 * (2 ^ t (s + 1) * (next.live s).card) ≤
        (2 * 𝒜.overhead ambientLength * 2 ^ t s) * (next.live (s + 1)).card := by
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  let suffixRootCode := (restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q []
  let suffixLiveCodes := restrictedEffectiveRebuildLiveCodes suffixRootCode codes
  have hnext' := hnext
  dsimp [DecodesToRestrictedSampledRunState] at hnext'
  simp only [restrictedSelectorField_sampledState_zero,
    restrictedSelectorField_sampledState_one] at hnext'
  intro s hqs hsN
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

/-- The state produced by one effective run step decodes to a state satisfying the abstract step
specification with the given failure scale `q`. -/
lemma restrictedEffectiveSampledRun_step_contract
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString)
    (q : ℕ)
    (codes : List BitString)
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
        ((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
          codes)) next)
    (Afinal Cfinal : BitString)
    (htrace : RestrictedEffectiveRebuildCodeTrace 𝒜 (𝒜.overhead ambientLength)
      (sizes.drop (q + 1))
      ((decodeListCode (restrictedSelectorField stateCode 1)).getD q [])
      ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
      (sizes.drop (q + 1)).length Afinal Cfinal codes)
    (hsteps : ∀ i < (sizes.drop (q + 1)).length, ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
            codes).getD i []) =
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
  set modelCodes := decodeListCode (restrictedSelectorField stateCode 1) with hmodelCodes
  have hmodelLength : modelCodes.length = N + 1 := hstate.1
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
  have hretained : ∀ s ≤ q,
      next.B s = state.B s ∧ next.live s = state.live s \ bad :=
    restrictedEffectiveSampledRun_step_contract_retained 𝒜 N ambientLength t stateCode badCode
      state bad q codes hq_le hcodesLength hstate hbad
      next hnext htrace0 halignSuffix
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
  · exact restrictedEffectiveSampledRun_step_contract_density 𝒜 N ambientLength t sizes
      hlen hpowers stateCode badCode q modelCodes codes hcodesLength next hnext halignSuffix hsteps

/-- Helper properties for suffix sizes list used in step spec. -/
private lemma restrictedEffectiveSampledRun_suffix_sizes_props
    (N : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hmono : ∀ s < N, t (s + 1) ≤ t s)
    (q : ℕ) (hq : q ≤ N) :
    let suffixSizes := sizes.drop (q + 1)
    (∀ i < suffixSizes.length, 0 < suffixSizes.getD i 0) ∧
    (suffixSizes.getD 0 0 ≤ sizes.getD q 0) ∧
    (∀ i, i + 1 < suffixSizes.length →
      suffixSizes.getD (i + 1) 0 ≤ suffixSizes.getD i 0) := by
  intro suffixSizes
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
        simp [hlen]
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
  exact ⟨hsuffix_pos, hsuffix_head, hsuffix_mono⟩

/-- Adapts rebuilding step bounds to the index arithmetic in full sampled run state. -/
private lemma restrictedEffectiveSampledRun_adapt_steps
    (𝒜 : DescriptionFamily) (ambientLength : ℕ) (q : ℕ) (sizes : List ℕ)
    (stateCode badCode : BitString) (codes : List BitString)
    (hsteps : ∀ i < (sizes.drop (q + 1)).length,
      ∃ Bprev Cprev Bnext : Finset BitString,
        decodeCoverCodeList (codes.getD i []) = canonicalFinsetList Bprev ∧
        decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
          ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
          codes).getD i []) = canonicalFinsetList Cprev ∧
        decodeCoverCodeList (codes.getD (i + 1) []) = canonicalFinsetList Bnext ∧
        𝒜.mem Bprev ∧
        Bprev.card ≤ (if i = 0 then sizes.getD q 0 else (sizes.drop (q + 1)).getD (i - 1) 0) ∧
        Cprev ⊆ Bprev ∧
        (∀ x ∈ Cprev, x.length = ambientLength) ∧
        𝒜.mem Bnext ∧
        Bnext.card ≤ (sizes.drop (q + 1)).getD i 0 ∧
        (sizes.drop (q + 1)).getD i 0 * Cprev.card ≤
          (𝒜.overhead ambientLength *
            (if i = 0 then sizes.getD q 0 else (sizes.drop (q + 1)).getD (i - 1) 0)) *
            (Bnext ∩ Cprev).card) :
    ∀ i < (sizes.drop (q + 1)).length,
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
  let suffixSizes := sizes.drop (q + 1)
  intro i hi
  have hdrop_getD : ∀ j < suffixSizes.length,
      suffixSizes.getD j 0 = sizes.getD (q + 1 + j) 0 := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    have hindex : q + 1 + j < sizes.length := by
      have := hj
      simp [suffixSizes, List.length_drop] at this
      omega
    rw [List.getD_eq_getElem _ _ hindex, List.getElem_drop]
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

/-- One effective run step halts and its output decodes to a state satisfying the abstract step
specification. -/
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
    q < N ∧ restrictedSampledDensityFails state bad q ∧
      ∀ (s : ℕ), s < q → ¬restrictedSampledDensityFails state bad s := hqspec.2
  have hAcode : decodeCoverCodeList (modelCodes.getD q []) =
      canonicalFinsetList (state.B q) := (hstate.2 q hq).1
  have hCcode : decodeCoverCodeList (liveCodes.getD q []) =
      canonicalFinsetList (state.live q \ bad) :=
    restrictedEffectiveLiveCodesAfterDelete_decode
      𝒜 N ambientLength t hstate hbad q hq
  have ⟨hsuffix_pos, hsuffix_head, hsuffix_mono⟩ :=
    restrictedEffectiveSampledRun_suffix_sizes_props N t sizes hlen hpowers hmono q hq
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
  have hsteps2 := restrictedEffectiveSampledRun_adapt_steps 𝒜 ambientLength q sizes stateCode
    badCode codes hsteps
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
      𝒜 N ambientLength t sizes stateCode badCode state bad q codes
      hlen hq hcodesLength2 hpowers hprefix hstate hbad
      Afinal Cfinal htrace hsteps2
  obtain ⟨next, hnext⟩ := h_decodes
  have h_contract : RestrictedSampledRunStepSpec state next bad q := by
    exact restrictedEffectiveSampledRun_step_contract 𝒜 N ambientLength t
      sizes hlen hpowers stateCode badCode state bad q codes
      hq hq_cases hcodesLength2 hstate hbad next hnext
      Afinal Cfinal htrace hsteps2
  refine ⟨restrictedEffectiveSampledRunStepPost
      (𝒜.overhead ambientLength)
      ((sizes, stateCode, badCode), rawOutput), ⟨next, ⟨q, ?_⟩⟩⟩
  refine ⟨?_, ?_, h_contract⟩
  · rw [restrictedEffectiveSampledRunStep]
    have hinput :
        restrictedEffectiveSampledRunStepInput (𝒜.overhead ambientLength)
            (sizes, stateCode, badCode) =
          restrictedEffectiveRebuildSuffixInput (modelCodes.getD q []) (liveCodes.getD q [])
            suffixSizes (𝒜.overhead ambientLength) := by
      simp [restrictedEffectiveSampledRunStepInput, q, modelCodes, liveCodes, suffixSizes]
    rw [hinput, hrun, Part.map_some]
  · unfold restrictedEffectiveSampledRunStepPost
    rw [hrawOutput]
    simpa only [decodeListCode_listCode] using hnext

end Kolmogorov
