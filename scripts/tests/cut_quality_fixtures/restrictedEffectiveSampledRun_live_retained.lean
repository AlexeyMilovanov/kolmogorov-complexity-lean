-- Calibration fixture for scripts/cut_quality.py: restrictedEffectiveSampledRun_live_retained.
-- Lines 523-577, 851-900, 901-904, 909-922, 928-932 of KolmogorovMathlib/Restricted/FamilyCurve/EffectiveRun/Part02.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Retained live codes decode to the original live sets minus `bad` for prefix indices `s ≤ q`. -/
private lemma restrictedEffectiveSampledRun_live_retained
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString) (q : ℕ) (modelCodes codes : List BitString)
    (hmodelCodes : modelCodes = decodeListCode (restrictedSelectorField stateCode 1))
    (hmodelLength : modelCodes.length = N + 1)
    (hq_le : q ≤ N) (hcodesLength : codes.length = N - q + 1)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
    (halignSuffix : ∀ i < codes.length,
      (restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)).getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i [])
    (s : ℕ) (hs : s ≤ q) :
    decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
      (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
      (modelCodes.take q ++ codes)).getD s []) =
        canonicalFinsetList (state.live s \ bad) := by
  have hqModel : q < modelCodes.length := by omega
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let oldDeletedLiveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  let suffixRootCode := oldDeletedLiveCodes.getD q []
  let suffixLiveCodes := restrictedEffectiveRebuildLiveCodes suffixRootCode codes
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

-- ------------------------------------------------------------

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
    ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        DecodesToRestrictedSampledRunState
          (restrictedEffectiveSampledStateCode
            (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
            (modelCodes.take q ++ codes)) next := by

-- ------------------------------------------------------------

  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes

-- ------------------------------------------------------------

  have htrace0 : codes.getD 0 [] = modelCodes.getD q [] :=
    restrictedEffectiveRebuildCodeTrace_getD_zero htrace
  have halignSuffix : ∀ i < codes.length,
      newLiveCodes.getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i [] := by
    intro i hi
    have hsuffixRoot : (restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [] =
        (restrictedEffectiveRebuildLiveCodes deletedRootCode modelCodes).getD q [] := by
      simp [restrictedEffectiveLiveCodesAfterDelete, deletedRootCode, ← hmodelCodes]
    rw [hsuffixRoot]
    exact restrictedEffectiveRebuildLiveCodes_splice_getD_suffix
      deletedRootCode modelCodes codes hqModel htrace0 hi

-- ------------------------------------------------------------

  have hliveRetained : ∀ s ≤ q,
      decodeCoverCodeList (newLiveCodes.getD s []) = canonicalFinsetList (state.live s \ bad) :=
    restrictedEffectiveSampledRun_live_retained
      𝒜 N ambientLength t stateCode badCode state bad q modelCodes codes
      hmodelCodes hmodelLength hq_le hcodesLength hstate hbad halignSuffix

end Kolmogorov
