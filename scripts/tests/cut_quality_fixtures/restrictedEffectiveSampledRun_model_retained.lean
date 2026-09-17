-- Calibration fixture for scripts/cut_quality.py: restrictedEffectiveSampledRun_model_retained.
-- Lines 496-521, 851-900, 901-904, 909-910, 923-927 of KolmogorovMathlib/Restricted/FamilyCurve/EffectiveRun/Part02.lean, verbatim at c989552;
-- everything between them is elided.  The fixture is not meant to
-- compile: it is the text the gate reads.

namespace Kolmogorov

/-- Retained model codes decode to the original model sets for prefix indices `s ≤ q`. -/
private lemma restrictedEffectiveSampledRun_model_retained
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (stateCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (q : ℕ) (modelCodes codes : List BitString)
    (hmodelCodes : modelCodes = decodeListCode (restrictedSelectorField stateCode 1))
    (hmodelLength : modelCodes.length = N + 1)
    (hq_le : q ≤ N)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (htrace0 : codes.getD 0 [] = modelCodes.getD q []) (s : ℕ) (hs : s ≤ q) :
    decodeCoverCodeList ((modelCodes.take q ++ codes).getD s []) =
      canonicalFinsetList (state.B s) := by
  have hqModel : q < modelCodes.length := by omega
  by_cases hsq : s < q
  · rw [show (modelCodes.take q ++ codes).getD s [] = modelCodes.getD s [] by
      exact restrictedEffectiveSampledRun_splice_getD_prefix
        modelCodes codes [] (Nat.le_of_lt hqModel) hsq]
    simpa [hmodelCodes] using (hstate.2 s (hs.trans hq_le)).1
  · have hsqeq : s = q := by omega
    subst s
    rw [show (modelCodes.take q ++ codes).getD q [] = codes.getD 0 [] by
      exact restrictedEffectiveSampledRun_splice_getD_suffix
        modelCodes codes [] (q := q) (i := 0) (Nat.le_of_lt hqModel)]
    rw [htrace0]
    simpa [hmodelCodes] using (hstate.2 q hq_le).1

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

-- ------------------------------------------------------------

  have hmodelRetained : ∀ s ≤ q,
      decodeCoverCodeList (newModelCodes.getD s []) = canonicalFinsetList (state.B s) :=
    restrictedEffectiveSampledRun_model_retained
      𝒜 N ambientLength t stateCode state q modelCodes codes
      hmodelCodes hmodelLength hq_le hstate htrace0

end Kolmogorov
