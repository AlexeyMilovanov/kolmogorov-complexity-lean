import KolmogorovMathlib.Restricted.FamilyCurve.RunCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRebuild
import KolmogorovMathlib.Restricted.FamilyCurve.CoupledRun
import KolmogorovMathlib.Restricted.FamilyCurve.BadStream
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.StateCoding
import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRun.Computability

/-!
# Decoding and splice invariants for an effective sampled step

One effective run step deletes newly bad models and, when a density test fails, rebuilds a suffix
of the live model sequence. This module proves the low-level facts that make that transition
faithful to the mathematical run.

It relates encoded deletions and cover cardinalities to their decoded values, characterises the
first failed scale, proves termination of the step search, and establishes the length and
`getD` equations for splicing the old prefix with the rebuilt suffix. The final lemma
`restrictedEffectiveSampledRun_step_decodes_splice` packages these facts into the decoded
splice statement consumed by the step contract and completed in `EffectiveRun.Part03`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- The delete code of the codes of `live` and `bad` decodes to the canonical list of
`live \ bad`. -/
lemma decode_restrictedEffectiveDeleteCode
    {liveCode badCode : BitString} {live bad : Finset BitString}
    (hlive : decodeCoverCodeList liveCode = canonicalFinsetList live)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad) :
    decodeCoverCodeList (restrictedEffectiveDeleteCode liveCode badCode) =
      canonicalFinsetList (live \ bad) := by
  rw [restrictedEffectiveDeleteCode,
    decodeCoverCodeList_canonicalUniformCodeOfList, hlive, hbad]
  let L := (canonicalFinsetList live).filter
    (fun x => decide (x ∉ canonicalFinsetList bad))
  have hnd : L.Nodup := (canonicalFinsetList_nodup live).filter _
  have hpair : L.Pairwise bitStringLE :=
    List.Pairwise.filter _ (Finset.pairwise_sort live bitStringLE)
  have hfin : L.toFinset = live \ bad := by
    ext x
    simp [L, mem_canonicalFinsetList]
  have hcanon : canonicalFinsetList L.toFinset = L :=
    canonicalFinsetList_of_sorted L hnd hpair
  rw [List.dedup_eq_self.mpr hnd, ← hfin, hcanon]

/-- The decoded cardinality of a cover code is the cardinality of the set it codes. -/
lemma restrictedDecodedCoverCard_eq
    {code : BitString} {S : Finset BitString}
    (hcode : decodeCoverCodeList code = canonicalFinsetList S) :
    restrictedDecodedCoverCard code = S.card := by
  rw [restrictedDecodedCoverCard, hcode,
    List.dedup_eq_self.mpr (canonicalFinsetList_nodup S),
    length_canonicalFinsetList]

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
      exact congrArg canonicalFinsetList
        (Finset.sdiff_inter_right_comm (state.live s) bad (state.B (s + 1)))

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
  rw [List.length_append, List.length_take, hmodelLength, hcodesLength]
  have hq_le : q ≤ N + 1 := by omega
  rw [Nat.min_eq_left hq_le]
  omega

/-- Before the rebuild point, lookup in the spliced model trace is lookup in
the retained old prefix. -/
lemma restrictedEffectiveSampledRun_splice_getD_prefix
    {α : Type} (modelCodes codes : List α) (fallback : α) {q s : ℕ}
    (hq : q ≤ modelCodes.length) (hs : s < q) :
    (modelCodes.take q ++ codes).getD s fallback =
      modelCodes.getD s fallback := by
  have hlen : s < (modelCodes.take q).length := by rw [List.length_take]; omega
  rw [List.getD_append _ _ _ _ hlen, List.getD_eq_getElem _ _ hlen, List.getElem_take]
  have hs_len : s < modelCodes.length := by omega
  rw [List.getD_eq_getElem _ _ hs_len]

/-- At and after the rebuild point, lookup in the spliced model trace is
lookup in the newly emitted suffix. -/
lemma restrictedEffectiveSampledRun_splice_getD_suffix
    {α : Type} (modelCodes codes : List α) (fallback : α) {q i : ℕ}
    (hq : q ≤ modelCodes.length) :
    (modelCodes.take q ++ codes).getD (q + i) fallback =
      codes.getD i fallback := by
  rw [List.getD_append_right] <;> simp [List.length_take, Nat.min_eq_left hq]

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

/-- Splicing `codes` onto the first `q` model codes of `stateCode` retains the old data below
`q` and continues with the rebuild trace above it: the rebuilt live codes at index `q + i` are
the rebuild of the deleted suffix root at `i`, the spliced model codes at every `s ≤ q` decode
to `state.B s`, and the rebuilt live codes at every `s ≤ q` decode to `state.live s \ bad`. -/
private lemma restrictedEffectiveSampledRun_splice_retained
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString) (q : ℕ) (codes : List BitString)
    (hq_le : q ≤ N) (hcodesLength : codes.length = N - q + 1)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
    (htrace0 : codes.getD 0 [] =
      (decodeListCode (restrictedSelectorField stateCode 1)).getD q []) :
    (∀ i < codes.length,
      (restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        ((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
          codes)).getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i []) ∧
    (∀ s ≤ q, decodeCoverCodeList
      (((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
        codes).getD s []) =
      canonicalFinsetList (state.B s)) ∧
    (∀ s ≤ q, decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
      (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
      ((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
        codes)).getD s []) =
        canonicalFinsetList (state.live s \ bad)) := by
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
  have halignSuffix : ∀ i < codes.length,
      newLiveCodes.getD (q + i) [] = suffixLiveCodes.getD i [] := by
    intro i hi
    have hsuffixRoot : suffixRootCode =
        (restrictedEffectiveRebuildLiveCodes deletedRootCode modelCodes).getD q [] := by
      simp [suffixRootCode, oldDeletedLiveCodes, restrictedEffectiveLiveCodesAfterDelete,
        deletedRootCode, ← hmodelCodes]
    dsimp only [suffixLiveCodes]
    rw [hsuffixRoot]
    exact restrictedEffectiveRebuildLiveCodes_splice_getD_suffix
      deletedRootCode modelCodes codes hqModel htrace0 hi
  refine ⟨halignSuffix, ?_, ?_⟩
  · intro s hs
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
  · intro s hs
    by_cases hsq : s < q
    · have halign : newLiveCodes.getD s [] = oldDeletedLiveCodes.getD s [] := by
        dsimp [newLiveCodes, newModelCodes, oldDeletedLiveCodes,
          restrictedEffectiveLiveCodesAfterDelete]
        rw [← hmodelCodes]
        exact restrictedEffectiveRebuildLiveCodes_splice_getD_prefix
          deletedRootCode modelCodes codes (Nat.le_of_lt hqModel) hsq
      rw [show (restrictedEffectiveRebuildLiveCodes
          (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
          (modelCodes.take q ++ codes)).getD s [] = oldDeletedLiveCodes.getD s [] from halign]
      exact restrictedEffectiveLiveCodesAfterDelete_decode
        𝒜 N ambientLength t hstate hbad s (hs.trans hq_le)
    · have hsqeq : s = q := by omega
      subst s
      have hcodesPos : 0 < codes.length := by omega
      have halign0 : newLiveCodes.getD q [] = suffixLiveCodes.getD 0 [] := by
        simpa using halignSuffix 0 hcodesPos
      have hsuffixZero : suffixLiveCodes.getD 0 [] = suffixRootCode := by
        have hcodesNe : codes ≠ [] := List.ne_nil_of_length_pos hcodesPos
        simpa [suffixLiveCodes] using
          (restrictedEffectiveRebuildLiveCodes_getD_zero
            suffixRootCode codes hcodesNe)
      rw [show (restrictedEffectiveRebuildLiveCodes
          (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
          (modelCodes.take q ++ codes)).getD q [] = suffixRootCode from
        halign0.trans hsuffixZero]
      exact restrictedEffectiveLiveCodesAfterDelete_decode
        𝒜 N ambientLength t hstate hbad q hq_le
/-- Step data properties for spliced model and live codes at index `s ≤ N`. -/
private lemma restrictedEffectiveSampledRun_step_data
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString) (q : ℕ) (modelCodes codes : List BitString)
    (hlen : sizes.length = N + 1)
    (hmodelLength : modelCodes.length = N + 1)
    (hq_le : q ≤ N) (hcodesLength : codes.length = N - q + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
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
            (Bnext ∩ Cprev).card)
    (hmodelRetained : ∀ s ≤ q,
      decodeCoverCodeList ((modelCodes.take q ++ codes).getD s []) =
        canonicalFinsetList (state.B s))
    (hliveRetained : ∀ s ≤ q,
      decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)).getD s []) =
        canonicalFinsetList (state.live s \ bad))
    (halignSuffix : ∀ i < codes.length,
      (restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)).getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i [])
    (s : ℕ) (hsN : s ≤ N) :
    ∃ Bcur Ccur : Finset BitString,
      decodeCoverCodeList ((modelCodes.take q ++ codes).getD s []) = canonicalFinsetList Bcur ∧
      decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes
        (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
        (modelCodes.take q ++ codes)).getD s []) = canonicalFinsetList Ccur ∧
      𝒜.mem Bcur ∧
      Bcur.card ≤ 2 ^ t s ∧
      Ccur ⊆ Bcur ∧
      (∀ x ∈ Ccur, x.length = ambientLength) := by
  have hqModel : q < modelCodes.length := by omega
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let oldDeletedLiveCodes := restrictedEffectiveLiveCodesAfterDelete stateCode badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  let suffixRootCode := oldDeletedLiveCodes.getD q []
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

/-- Density inequality bound for suffix step transition. -/
private lemma restrictedEffectiveSampledRun_step_density_suffix
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (q s i : ℕ) (Cprev Bnext : Finset BitString)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hsi : s = q + i) (hsN : s + 1 ≤ N)
    (hdensity : sizes.getD (q + 1 + i) 0 * Cprev.card ≤
      (𝒜.overhead ambientLength *
        (if i = 0 then sizes.getD q 0 else sizes.getD (q + 1 + (i - 1)) 0)) *
        (Bnext ∩ Cprev).card) :
    (2 ^ t (s + 1)) * Cprev.card ≤
      (2 * 𝒜.overhead ambientLength * 2 ^ t s) * (Cprev ∩ Bnext).card := by
  have hprevSize :
      (if i = 0 then sizes.getD q 0
        else sizes.getD (q + 1 + (i - 1)) 0) =
        sizes.getD (q + i) 0 := by
    by_cases hi0 : i = 0
    · simp [hi0]
    · rw [ite_eq_right hi0]
      congr 1
      omega
  have hsSucc : s + 1 = q + 1 + i := by omega
  have hdensity' :
      (2 ^ t (s + 1)) * Cprev.card ≤
        (𝒜.overhead ambientLength * 2 ^ t s) *
          (Cprev ∩ Bnext).card := by
    rw [← hpowers (s + 1) hsN, ← hpowers s (by omega),
      hsSucc, hsi, Finset.inter_comm, ← hprevSize]
    simpa [Nat.add_assoc, Nat.add_comm i 1] using hdensity
  exact hdensity'.trans (by gcongr; omega)

/-- Monotonicity of live sets for spliced run state. -/
private lemma restrictedEffectiveSampledRun_step_live_monotonic
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString) (q : ℕ) (codes newLiveCodes : List BitString)
    (hlen : sizes.length = N + 1) (hcodesLength : codes.length = N - q + 1)
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
            (Bnext ∩ Cprev).card)
    (hliveRetained : ∀ s ≤ q,
      decodeCoverCodeList (newLiveCodes.getD s []) =
        canonicalFinsetList (state.live s \ bad))
    (halignSuffix : ∀ i < codes.length,
      newLiveCodes.getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i [])
    (s : ℕ) (hsN : s < N) :
    (decodeCoverCodeList (newLiveCodes.getD (s + 1) [])).toFinset ⊆
    (decodeCoverCodeList (newLiveCodes.getD s [])).toFinset := by
  let suffixRootCode := (restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q []
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
      rw [hsi, halignSuffix i (Nat.lt_trans (Nat.lt_succ_self i) hiCode)]
      exact hCprevCode
    have hnextCode : decodeCoverCodeList (newLiveCodes.getD (s + 1) []) =
        canonicalFinsetList (Cprev ∩ Bnext) := by
      rw [hsi, show q + i + 1 = q + (i + 1) by omega, halignSuffix (i + 1) hiCode]
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD suffixRootCode codes i hiCode]
      exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext hCprevCode hBnextCode
    rw [hcurrent, hnextCode, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
    exact Finset.inter_subset_left

/-- Density property for spliced run state. -/
private lemma restrictedEffectiveSampledRun_step_density
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ) (sizes : List ℕ)
    (stateCode badCode : BitString)
    (state : RestrictedSampledRunState 𝒜 N ambientLength (2 * 𝒜.overhead ambientLength) t)
    (bad : Finset BitString) (q : ℕ) (codes newLiveCodes : List BitString)
    (hlen : sizes.length = N + 1) (hcodesLength : codes.length = N - q + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hprefix : ∀ s < q, ¬ restrictedSampledDensityFails state bad s)
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
            (Bnext ∩ Cprev).card)
    (hliveRetained : ∀ s ≤ q,
      decodeCoverCodeList (newLiveCodes.getD s []) =
        canonicalFinsetList (state.live s \ bad))
    (halignSuffix : ∀ i < codes.length,
      newLiveCodes.getD (q + i) [] =
      (restrictedEffectiveRebuildLiveCodes
        ((restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q [])
        codes).getD i [])
    (s : ℕ) (hsN : s < N) :
    (2 ^ t (s + 1)) * (decodeCoverCodeList (newLiveCodes.getD s [])).toFinset.card ≤
    (2 * 𝒜.overhead ambientLength * 2 ^ t s) *
      (decodeCoverCodeList (newLiveCodes.getD (s + 1) [])).toFinset.card := by
  let suffixRootCode := (restrictedEffectiveLiveCodesAfterDelete stateCode badCode).getD q []
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
      rw [hsi, halignSuffix i (Nat.lt_trans (Nat.lt_succ_self i) hiCode)]
      exact hCprevCode
    have hnextCode : decodeCoverCodeList (newLiveCodes.getD (s + 1) []) =
        canonicalFinsetList (Cprev ∩ Bnext) := by
      rw [hsi, show q + i + 1 = q + (i + 1) by omega, halignSuffix (i + 1) hiCode]
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD suffixRootCode codes i hiCode]
      exact decode_restrictedLiveIntersectionCode _ _ Cprev Bnext hCprevCode hBnextCode
    rw [hcurrent, hnextCode, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
    exact restrictedEffectiveSampledRun_step_density_suffix
      𝒜 N ambientLength t sizes q s i Cprev Bnext hpowers hsi hsN hdensity

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
    (codes : List BitString)
    (hlen : sizes.length = N + 1)
    (hq_le : q ≤ N)
    (hcodesLength : codes.length = N - q + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s)
    (hprefix : ∀ s < q, ¬ restrictedSampledDensityFails state bad s)
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (hbad : decodeCoverCodeList badCode = canonicalFinsetList bad)
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
    ∃ next : RestrictedSampledRunState 𝒜 N ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        DecodesToRestrictedSampledRunState
          (restrictedEffectiveSampledStateCode
            (restrictedEffectiveDeleteCode (restrictedSelectorField stateCode 0) badCode)
            ((decodeListCode (restrictedSelectorField stateCode 1)).take q ++
              codes)) next := by
  set modelCodes := decodeListCode (restrictedSelectorField stateCode 1) with hmodelCodes
  have hmodelLength : modelCodes.length = N + 1 := hstate.1
  let deletedRootCode := restrictedEffectiveDeleteCode
    (restrictedSelectorField stateCode 0) badCode
  let newModelCodes := modelCodes.take q ++ codes
  let newLiveCodes := restrictedEffectiveRebuildLiveCodes deletedRootCode newModelCodes
  have hqModel : q < modelCodes.length := by omega
  have hnewModelLength : newModelCodes.length = N + 1 :=
    restrictedEffectiveSampledRun_splice_length N q modelCodes codes
      hmodelLength hq_le hcodesLength
  have htrace0 : codes.getD 0 [] = modelCodes.getD q [] :=
    restrictedEffectiveRebuildCodeTrace_getD_zero htrace
  obtain ⟨halignSuffix, hmodelRetained, hliveRetained⟩ :=
    restrictedEffectiveSampledRun_splice_retained
      𝒜 N ambientLength t stateCode badCode state bad q codes
      hq_le hcodesLength hstate hbad htrace0
  have hstepData : ∀ s ≤ N, ∃ Bcur Ccur : Finset BitString,
      decodeCoverCodeList (newModelCodes.getD s []) = canonicalFinsetList Bcur ∧
      decodeCoverCodeList (newLiveCodes.getD s []) = canonicalFinsetList Ccur ∧
      𝒜.mem Bcur ∧
      Bcur.card ≤ 2 ^ t s ∧
      Ccur ⊆ Bcur ∧
      (∀ x ∈ Ccur, x.length = ambientLength) :=
    restrictedEffectiveSampledRun_step_data
      𝒜 N ambientLength t sizes stateCode badCode state bad q modelCodes codes
      hlen hmodelLength hq_le hcodesLength hpowers hsteps
      hmodelRetained hliveRetained halignSuffix
  let next : RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength) t :=
    { B := fun s => (decodeCoverCodeList (newModelCodes.getD s [])).toFinset
      live := fun s => (decodeCoverCodeList (newLiveCodes.getD s [])).toFinset
      mem_family := by
        intro s hs
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard, hCsub, hClength⟩ := hstepData s hs
        rw [hBcode, canonicalFinsetList_toFinset]
        exact hBmem
      size_bound := by
        intro s hs
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard, hCsub, hClength⟩ := hstepData s hs
        rw [hBcode, canonicalFinsetList_toFinset]
        exact hBcard
      live_subset := by
        intro s hs
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard, hCsub, hClength⟩ := hstepData s hs
        rw [hCcode, hBcode, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
        exact hCsub
      live_ambient := by
        intro s hs x hx
        obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard, hCsub, hClength⟩ := hstepData s hs
        rw [hCcode, canonicalFinsetList_toFinset] at hx
        exact hClength x hx
      live_monotonic :=
        restrictedEffectiveSampledRun_step_live_monotonic
          𝒜 N ambientLength t sizes stateCode badCode state bad q codes newLiveCodes
          hlen hcodesLength hsteps hliveRetained halignSuffix
      density :=
        restrictedEffectiveSampledRun_step_density
          𝒜 N ambientLength t sizes stateCode badCode state bad q codes newLiveCodes
          hlen hcodesLength hpowers hprefix hsteps hliveRetained halignSuffix }
  refine ⟨next, ?_⟩
  dsimp [DecodesToRestrictedSampledRunState]
  simp only [restrictedSelectorField_sampledState_zero, restrictedSelectorField_sampledState_one]
  refine ⟨hnewModelLength, ?_⟩
  intro s hs
  obtain ⟨Bcur, Ccur, hBcode, hCcode, hBmem, hBcard, hCsub, hClength⟩ := hstepData s hs
  constructor
  · change decodeCoverCodeList (newModelCodes.getD s []) = canonicalFinsetList (next.B s)
    dsimp [next]
    rw [hBcode, canonicalFinsetList_toFinset]
  · change decodeCoverCodeList (newLiveCodes.getD s []) = canonicalFinsetList (next.live s)
    dsimp [next]
    rw [hCcode, canonicalFinsetList_toFinset]

end Kolmogorov
