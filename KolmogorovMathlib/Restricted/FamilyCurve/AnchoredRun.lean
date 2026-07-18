import KolmogorovMathlib.Restricted.FamilyCurve.EffectiveRunSemantics

/-!
# M7: anchored effective sampled run — DRAFT statements

The unanchored executor stores only the sampled family models.  Consequently
its level zero is retained forever, whereas the paper's first sampled model
must be rebuildable.  This module inserts the missing fixed ambient cube at
level zero and shifts sampled scale `s` to run level `s + 1`.

The bad stream remains indexed by the original `N` sampled intervals.  No
paper-facing interface is changed here.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- The anchored target exponent: the ambient cube at level zero, followed by
the sampled grid heights. -/
def restrictedAnchoredTarget
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    ℕ → ℕ
  | 0 => ambientLength
  | s + 1 => grid.j s - (Δ + 1)

@[simp] lemma restrictedAnchoredTarget_zero
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    restrictedAnchoredTarget ambientLength Δ grid 0 = ambientLength := rfl

@[simp] lemma restrictedAnchoredTarget_succ
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (s : ℕ) :
    restrictedAnchoredTarget ambientLength Δ grid (s + 1) =
      grid.j s - (Δ + 1) := rfl

/-- The executable anchored size schedule.  Its head is exactly the ambient
cube size; its tail is the existing sampled schedule. -/
def restrictedEffectiveAnchoredSizes
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    List ℕ :=
  2 ^ ambientLength :: restrictedEffectiveSampledSizes
    (restrictedCurveGridCode grid) N Δ

@[simp] lemma restrictedEffectiveAnchoredSizes_length
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    (restrictedEffectiveAnchoredSizes ambientLength Δ grid).length = N + 2 := by
  simp [restrictedEffectiveAnchoredSizes]

@[simp] lemma restrictedEffectiveAnchoredSizes_getD_zero
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    (restrictedEffectiveAnchoredSizes ambientLength Δ grid).getD 0 0 =
      2 ^ ambientLength := by
  simp [restrictedEffectiveAnchoredSizes]

/-- Anchored size at a successor level reads the sampled grid size. -/
lemma restrictedEffectiveAnchoredSizes_getD_succ
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (s : ℕ) (hs : s ≤ N) :
    (restrictedEffectiveAnchoredSizes ambientLength Δ grid).getD (s + 1) 0 =
      2 ^ (grid.j s - (Δ + 1)) := by
  simpa [restrictedEffectiveAnchoredSizes] using
    restrictedEffectiveSampledSizes_grid_getD grid Δ s hs

/-- Anchored size at level zero is the full ambient cube. -/
lemma restrictedEffectiveAnchoredSizes_getD
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (s : ℕ) (hs : s ≤ N + 1) :
    (restrictedEffectiveAnchoredSizes ambientLength Δ grid).getD s 0 =
      2 ^ restrictedAnchoredTarget ambientLength Δ grid s := by
  cases s with
  | zero =>
      exact restrictedEffectiveAnchoredSizes_getD_zero
        ambientLength Δ grid
  | succ s =>
      exact restrictedEffectiveAnchoredSizes_getD_succ
        ambientLength Δ grid s (by omega)

/-- The shifted target is nonincreasing.  The only new edge is from the cube
height `ambientLength` to sampled height `grid.j 0 - (Δ+1)`. -/
lemma restrictedAnchoredTarget_mono
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength) :
    ∀ s < N + 1,
      restrictedAnchoredTarget ambientLength Δ grid (s + 1) ≤
        restrictedAnchoredTarget ambientLength Δ grid s := by
  intro s hs
  cases s with
  | zero =>
      simp only [restrictedAnchoredTarget_zero, restrictedAnchoredTarget_succ,
        grid.j_start]
      omega
  | succ s =>
      simp only [restrictedAnchoredTarget_succ]
      exact Nat.sub_le_sub_right (grid.j_mono s (by omega)) (Δ + 1)

/-- Initial anchored state search.  The effective suffix builder emits the
ambient predecessor first; unlike the unanchored initializer, this wrapper
keeps that code as run level zero. -/
noncomputable def restrictedEffectiveAnchoredInitialState
    (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    Part BitString :=
  let q0 := 𝒜.overhead ambientLength
  let Acode := (codedUniformOn (stringsOfLength ambientLength)
    (codedStringsOfLength_nonempty ambientLength)).code
  let sampledSizes := restrictedEffectiveSampledSizes
    (restrictedCurveGridCode grid) N Δ
  (restrictedEffectiveRebuildSuffix 𝒜
    (restrictedEffectiveRebuildSuffixInput Acode Acode sampledSizes q0)).map
      (fun output =>
        restrictedEffectiveSampledStateCode Acode (decodeListCode output))

/-- Anchored chronological executor.  Its mathematical state has `N + 2`
levels indexed by `0, ..., N + 1`, while bad batches still use the original
`N` sampled intervals. -/
noncomputable def restrictedEffectiveAnchoredSampledRun
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) : Part BitString :=
  let q0 := 𝒜.overhead ambientLength
  let sizes := restrictedEffectiveAnchoredSizes ambientLength Δ grid
  Nat.rec (motive := fun _ => Part BitString)
    (restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ grid)
    (fun stage current => current.bind (fun state =>
      restrictedEffectiveSampledRunProcess 𝒜 q0 sizes state
        (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
          𝒜.toPre N Δ stage)))
    time

/-- Codes of all bad events processed before run time `time`. -/
def restrictedAnchoredProcessedBadCodes
    (c : Code) (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) : List BitString :=
  (List.range time).flatMap (fun stage =>
    restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
      𝒜.toPre N Δ stage)

/-- Union of the canonical bad sets decoded from one executable code batch. -/
def restrictedDecodedBadCodesUnion (codes : List BitString) : Finset BitString :=
  restrictedBadPrefixUnion
    (codes.map (fun w => (decodeCoverCodeList w).toFinset)) codes.length

/-- Union of the decoded bad events processed before time `time`.  Stream
soundness ensures each decoded list is canonical; `toFinset` merely forgets
that representation. -/
def restrictedAnchoredProcessedBadUnion
    (c : Code) (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) : Finset BitString :=
  Nat.rec (motive := fun _ => Finset BitString)
    ∅
    (fun stage previous => previous ∪ restrictedDecodedBadCodesUnion
      (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
        𝒜.toPre N Δ stage))
    time

set_option linter.style.show false in
-- `show` unfolds local `let`-abbreviations to expose the rewrite target.
/-- Generic decoding theorem for an anchored rebuild trace.  Unlike the
unanchored initializer, the predecessor emitted at the head of the trace is
retained as level zero. -/
lemma restrictedEffectiveAnchoredInitialState_generic_spec
    (𝒜 : DescriptionFamily) (N ambientLength : ℕ) (t : ℕ → ℕ)
    (sizes : List ℕ)
    (hlen : sizes.length = N + 1)
    (hpowers : ∀ s ≤ N, sizes.getD s 0 = 2 ^ t (s + 1))
    (htop : t 0 = ambientLength)
    (hmono : ∀ s < N + 1, t (s + 1) ≤ t s) :
    let Acode := (codedUniformOn (stringsOfLength ambientLength)
      (codedStringsOfLength_nonempty ambientLength)).code
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
          (2 * 𝒜.overhead ambientLength) t,
        (restrictedEffectiveRebuildSuffix 𝒜
          (restrictedEffectiveRebuildSuffixInput Acode Acode sizes
            (𝒜.overhead ambientLength))).map
              (fun raw => restrictedEffectiveSampledStateCode Acode
                (decodeListCode raw)) = Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        state.B 0 = stringsOfLength ambientLength ∧
        state.live 0 = stringsOfLength ambientLength := by
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
  have hsizes_head : sizes.getD 0 0 ≤ 2 ^ ambientLength := by
    have h0le : (0 : ℕ) ≤ N := Nat.zero_le N
    rw [hpowers 0 h0le]
    refine Nat.pow_le_pow_right (by decide) ?_
    exact htop ▸ hmono 0 (by omega)
  have hsizes_pos : ∀ i < sizes.length, 0 < sizes.getD i 0 := by
    intro i hi
    have hiN : i ≤ N := by omega
    rw [hpowers i hiN]
    positivity
  have hsizes_mono : ∀ i, i + 1 < sizes.length →
      sizes.getD (i + 1) 0 ≤ sizes.getD i 0 := by
    intro i hi
    have hiN : i < N := by omega
    rw [hpowers (i + 1) (by omega), hpowers i (by omega)]
    exact Nat.pow_le_pow_right (by decide) (hmono (i + 1) (by omega))
  -- Call rebuild suffix decodes density
  obtain ⟨output, Afinal, Cfinal, codes, hrun, houtput, htrace,
      hcodesLength, hsteps⟩ :=
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
  have codes_ne_nil : ∀ {idx Acode_s Ccode_s codes}
      (ht : RestrictedEffectiveRebuildCodeTrace 𝒜 (𝒜.overhead ambientLength) sizes Acode Acode idx Acode_s Ccode_s codes),
      codes ≠ [] := by
    intro idx Acode_s Ccode_s codes ht
    induction ht with
    | nil => simp
    | cons hprev _ => simp
  have codes_head_eq : ∀ {idx Acode_s Ccode_s codes}
      (ht : RestrictedEffectiveRebuildCodeTrace 𝒜 (𝒜.overhead ambientLength) sizes Acode Acode idx Acode_s Ccode_s codes),
      codes.headI = Acode := by
    intro idx Acode_s Ccode_s codes ht
    induction ht with
    | nil => rfl
    | cons hprev ih =>
        rename_i idx Acode_s Ccode_s codes ih'
        rcases codes with - | ⟨x, xs⟩
        · exact (codes_ne_nil hprev rfl).elim
        · simp_all
  have hpredecessor_eq_A : predecessorCode = Acode := by
    have := codes_head_eq htrace
    rw [hcodes] at this
    simp_all
  -- htrace already has Acode, nothing to simp
  have htail_ne : tail ≠ [] := by
    intro hnil
    rw [hcodes, hnil] at hcodesLength
    simp at hcodesLength
  obtain ⟨firstModelCode, remainingModelCodes, htail⟩ :=
    List.exists_cons_of_ne_nil htail_ne
  subst tail
  have hremainingLength : remainingModelCodes.length = N := by
    rw [hcodes] at hcodesLength
    simp only [List.length_cons] at hcodesLength
    omega
  let extendedModelCodes := predecessorCode :: firstModelCode :: remainingModelCodes
  have hextendedLength : extendedModelCodes.length = N + 2 := by
    simp [extendedModelCodes, hremainingLength]
  let modelCodes := firstModelCode :: remainingModelCodes
  let stateModelCodes := extendedModelCodes
  have hcodes_eq : codes = stateModelCodes := by rw [hcodes]
  let stateLiveCodes := restrictedEffectiveRebuildLiveCodes Acode stateModelCodes
  let stateCode := restrictedEffectiveSampledStateCode Acode stateModelCodes
  have hstateModelLength : stateModelCodes.length = N + 2 := by
    simp [stateModelCodes, extendedModelCodes, hremainingLength]
  have hstateModel0 : stateModelCodes.getD 0 [] = Acode := by
    simp [stateModelCodes, extendedModelCodes, hpredecessor_eq_A]
  have hstateLive0 : stateLiveCodes.getD 0 [] = Acode := by
    show (restrictedEffectiveRebuildLiveCodes Acode stateModelCodes).getD 0 [] = Acode
    simp only [restrictedEffectiveRebuildLiveCodes, stateModelCodes, extendedModelCodes]
    rfl
  -- Get step data with proper indexing for s ≤ N (indices 0 to N of stateModelCodes)
  have hstepData : ∀ s ≤ N, ∃ Bprev Cprev Bnext : Finset BitString,
      decodeCoverCodeList (stateModelCodes.getD (s + 1) []) = canonicalFinsetList Bnext ∧
      decodeCoverCodeList (stateLiveCodes.getD (s + 1) []) =
        canonicalFinsetList (Cprev ∩ Bnext) ∧
      decodeCoverCodeList (stateLiveCodes.getD s []) = canonicalFinsetList Cprev ∧
      𝒜.mem Bnext ∧ Bnext.card ≤ sizes.getD s 0 ∧
      (∀ x ∈ Cprev, x.length = ambientLength) ∧
      sizes.getD s 0 * Cprev.card ≤
        (𝒜.overhead ambientLength * if s = 0 then 2 ^ ambientLength else sizes.getD (s - 1) 0) *
          (Bnext ∩ Cprev).card := by
    intro s hs
    obtain ⟨Bprev, Cprev, Bnext, hBprevCode, hCprevCode,
        hBnextCode, hBprevMem, hBprevCard, hCprevSub, hCprevLength,
        hBnextMem, hBnextCard, hdensity⟩ := hsteps s (by
          rw [hlen]
          exact Nat.lt_succ_of_le hs)
    refine ⟨Bprev, Cprev, Bnext, ?_, ?_, ?_, hBnextMem, hBnextCard, hCprevLength, hdensity⟩
    · simpa [hcodes_eq] using hBnextCode
    · rw [hcodes_eq] at hCprevCode
      simp only [stateLiveCodes]
      show decodeCoverCodeList ((restrictedEffectiveRebuildLiveCodes Acode stateModelCodes).getD (s + 1) []) = _
      rw [restrictedEffectiveRebuildLiveCodes_succ_getD Acode
          stateModelCodes s (by omega)]
      simpa [hcodes_eq] using decode_restrictedLiveIntersectionCode _ _ Cprev Bnext hCprevCode hBnextCode
    · rw [hcodes_eq] at hCprevCode
      simp only [stateLiveCodes]
      rw [hcodes_eq] at hBprevCode
      exact hCprevCode
  let decodedModels : ℕ → Finset BitString := fun s =>
    (decodeCoverCodeList (stateModelCodes.getD s [])).toFinset
  let decodedLive : ℕ → Finset BitString := fun s =>
    (decodeCoverCodeList (stateLiveCodes.getD s [])).toFinset
  have hdecoded : ∀ s ≤ N + 1,
      decodeCoverCodeList (stateModelCodes.getD s []) =
          canonicalFinsetList (decodedModels s) ∧
      decodeCoverCodeList (stateLiveCodes.getD s []) =
          canonicalFinsetList (decodedLive s) := by
    intro s hs
    simp only [decodedModels, decodedLive]
    cases s with
    | zero =>
      constructor
      · -- stateModelCodes[0] = predecessorCode, and predecessorCode = Acode
        have h0 : stateModelCodes.getD 0 [] = Acode := by
          simp [stateModelCodes, extendedModelCodes, hpredecessor_eq_A]
        rw [h0, hAcode]
        simp [canonicalFinsetList_toFinset]
      · -- stateLiveCodes[0] = Acode
        have h0 : stateLiveCodes.getD 0 [] = Acode := by
          show (restrictedEffectiveRebuildLiveCodes Acode stateModelCodes).getD 0 [] = Acode
          simp only [restrictedEffectiveRebuildLiveCodes, stateModelCodes, extendedModelCodes]
          rfl
        rw [h0, hAcode]
        simp [canonicalFinsetList_toFinset]
    | succ s =>
      have hs' : s ≤ N := by omega
      obtain ⟨Bprev, Cprev, Bnext, hBnextCode, hliveCode, hBnextMem, hBnextCard, hCprevLength⟩ := hstepData s hs'
      constructor
      · rw [hBnextCode, canonicalFinsetList_toFinset]
      · rw [hliveCode, canonicalFinsetList_toFinset]
  let state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
      (2 * 𝒜.overhead ambientLength) t :=
    { B := decodedModels
      live := decodedLive
      mem_family := by
        intro s hs
        cases s with
        | zero =>
          dsimp [decodedModels]
          rw [hstateModel0, hAcode]
          simp [hAmem]
        | succ s =>
          have hs' : s ≤ N := by omega
          obtain ⟨Bprev, Cprev, Bnext, hBnextCode, _, _, hBnextMem, _, _⟩ := hstepData s hs'
          dsimp [decodedModels]
          rw [hBnextCode, canonicalFinsetList_toFinset]
          exact hBnextMem
      size_bound := by
        intro s hs
        cases s with
        | zero =>
          dsimp [decodedModels]
          rw [hstateModel0, hAcode, canonicalFinsetList_toFinset, htop]
          exact hAcard
        | succ s =>
          have hs' : s ≤ N := by omega
          obtain ⟨Bprev, Cprev, Bnext, hBnextCode, _, _, _, hBnextCard, _⟩ := hstepData s hs'
          dsimp [decodedModels]
          rw [hBnextCode, canonicalFinsetList_toFinset]
          rw [hpowers s hs'] at hBnextCard
          exact hBnextCard
      live_subset := by
        intro s hs
        cases s with
        | zero =>
          dsimp [decodedLive, decodedModels]
          rw [hstateLive0, hstateModel0, hAcode]
        | succ s =>
          have hs' : s ≤ N := by omega
          obtain ⟨Bprev, Cprev, Bnext, hBnextCode, hliveCode, _, _, _, _⟩ := hstepData s hs'
          dsimp [decodedLive, decodedModels]
          rw [hliveCode, hBnextCode, canonicalFinsetList_toFinset,
            canonicalFinsetList_toFinset]
          exact Finset.inter_subset_right
      live_ambient := by
        intro s hs x hx
        cases s with
        | zero =>
          dsimp [decodedLive] at hx
          rw [hstateLive0, hAcode] at hx
          rw [canonicalFinsetList_toFinset] at hx
          exact hAlength x hx
        | succ s =>
          have hs' : s ≤ N := by omega
          obtain ⟨Bprev, Cprev, Bnext, hBnextCode, hliveCode, hCprevCode,
              hBnextMem, hBnextCard, hCprevLength, _⟩ := hstepData s hs'
          dsimp [decodedLive] at hx
          rw [hliveCode, canonicalFinsetList_toFinset] at hx
          exact hCprevLength x (Finset.inter_subset_left hx)
      live_monotonic := by
        intro s hsN
        have hsLE : s ≤ N := by omega
        obtain ⟨Bprev, Cprev, Bnext, hBnextCode, hliveCode, hliveCode_s, hBnextMem, hBnextCard, hCprevLength, _⟩ := hstepData s hsLE
        have hdecodedLive_s : decodeCoverCodeList (stateLiveCodes.getD s []) = canonicalFinsetList Cprev := hliveCode_s
        dsimp [decodedLive]
        rw [hliveCode, hdecodedLive_s, canonicalFinsetList_toFinset, canonicalFinsetList_toFinset]
        exact Finset.inter_subset_left
      density := by
        intro s hsN
        have hsLE : s ≤ N := by omega
        -- Use hstepData which has the right form for stateModelCodes
        obtain ⟨Bprev, Cprev, Bnext, hBnextCode, hliveCode, hCprevCode,
            hBnextMem, hBnextCard, hCprevLength, hdensity⟩ := hstepData s hsLE
        -- decodedLive s = Cprev
        have hdecodedLive_s : decodedLive s = Cprev := by
          simp only [decodedLive]
          rw [hCprevCode]
          exact canonicalFinsetList_toFinset Cprev
        -- decodedLive (s + 1) = Cprev ∩ Bnext
        have hdecodedLive_sp : decodedLive (s + 1) = Cprev ∩ Bnext := by
          simp only [decodedLive]
          rw [hliveCode]
          exact canonicalFinsetList_toFinset (Cprev ∩ Bnext)
        -- Now apply density property
        simp only [hdecodedLive_s, hdecodedLive_sp]
        -- hdensity: sizes.getD s 0 * Cprev.card ≤ (𝒜.overhead * (if s = 0 then 2^ambientLength else sizes.getD (s-1) 0)) * (Bnext ∩ Cprev).card
        -- Need: (2 ^ t (s + 1)) * Cprev.card ≤ (2 * overhead * 2 ^ t s) * (Cprev ∩ Bnext).card
        have hsizes_eq : sizes.getD s 0 = 2 ^ t (s + 1) := hpowers s (by omega)
        rw [← hsizes_eq, Finset.inter_comm]
        -- Now need to show the bound follows from hdensity
        rcases s.eq_zero_or_pos with rfl | hs_pos
        · -- Case s = 0
          have h2 : 2 ^ t 0 = 2 ^ ambientLength := by rw [htop]
          have h3 : 𝒜.overhead ambientLength ≤ 2 * 𝒜.overhead ambientLength := by omega
          calc sizes.getD 0 0 * Cprev.card
              ≤ 𝒜.overhead ambientLength * 2 ^ ambientLength * (Bnext ∩ Cprev).card := hdensity
            _ ≤ 2 * 𝒜.overhead ambientLength * 2 ^ ambientLength * (Bnext ∩ Cprev).card := by
                gcongr
            _ = 2 * 𝒜.overhead ambientLength * 2 ^ t 0 * (Bnext ∩ Cprev).card := by rw [h2]
        · -- Case s > 0
          have hsizes_pred : sizes.getD (s - 1) 0 = 2 ^ t s := by
            have h1 : s - 1 + 1 = s := Nat.sub_add_cancel hs_pos
            rw [← h1]
            exact hpowers (s - 1) (by omega)
          calc sizes.getD s 0 * Cprev.card
              ≤ 𝒜.overhead ambientLength * sizes.getD (s - 1) 0 * (Bnext ∩ Cprev).card := by
                rw [if_neg (ne_of_gt hs_pos)] at hdensity; exact hdensity
            _ = 𝒜.overhead ambientLength * 2 ^ t s * (Bnext ∩ Cprev).card := by rw [hsizes_pred]
            _ ≤ 2 * 𝒜.overhead ambientLength * 2 ^ t s * (Bnext ∩ Cprev).card := by
                gcongr; omega }
  have hstateB : ∀ s, state.B s = decodedModels s := fun _ => rfl
  have hstateLive : ∀ s, state.live s = decodedLive s := fun _ => rfl
  refine ⟨stateCode, state, ?_, ?_, ?_⟩
  · rw [hrun]
    simp [Part.map_some, houtput, hcodes_eq]
    rfl
  · unfold DecodesToRestrictedSampledRunState
    -- Need to show modelCodes.length = (N + 1) + 1 and decoding properties
    simp only [stateCode, restrictedSelectorField_sampledState_zero,
      restrictedSelectorField_sampledState_one]
    refine ⟨?_, ?_⟩
    · omega
    · intro s hs
      exact hdecoded s hs
  · simp only [hstateB, hstateLive]
    simp only [decodedModels, decodedLive, hstateModel0, hstateLive0, hAcode,
      canonicalFinsetList_toFinset, A]
    trivial

/-- DRAFT leaf: the anchored initializer terminates, decodes to the shifted
state, and keeps both the level-zero model and live pool equal to the ambient
cube. -/
lemma restrictedEffectiveAnchoredInitialState_spec
    (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
          (2 * 𝒜.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength Δ grid),
        restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ grid =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        state.B 0 = stringsOfLength ambientLength ∧
        state.live 0 = stringsOfLength ambientLength := by
  apply restrictedEffectiveAnchoredInitialState_generic_spec
  · norm_num [restrictedEffectiveSampledSizes]
  · intro s hs
    exact restrictedEffectiveSampledSizes_grid_getD grid Δ s hs
  · rfl
  · exact fun s hs ↦
      restrictedAnchoredTarget_mono ambientLength Δ grid hnambient s hs

/-- Finite-time correctness of the anchored run.  Besides decoded
validity and processed-event disjointness, it states the exact paper invariant:
the root model is the fixed cube and the root live pool is that cube minus all
events processed so far. -/
lemma restrictedEffectiveAnchoredSampledRun_spec
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ time : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
          (2 * 𝒜.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength Δ grid),
        restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ grid time =
            Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        state.B 0 = stringsOfLength ambientLength ∧
        state.live 0 = stringsOfLength ambientLength \
          restrictedAnchoredProcessedBadUnion c 𝒜 Δ grid time ∧
        ∀ eventTime < time,
          ∀ w ∈ restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
            𝒜.toPre N Δ eventTime,
          ∀ bad : Finset BitString,
            decodeCoverCodeList w = canonicalFinsetList bad →
            ∀ s ≤ N + 1, Disjoint (state.live s) bad := by
  let anchoredTarget := restrictedAnchoredTarget ambientLength Δ grid
  let sizes := restrictedEffectiveAnchoredSizes ambientLength Δ grid
  have hlen : sizes.length = (N + 1) + 1 := by
    simp [sizes]
  have hpowers : ∀ s ≤ N + 1,
      sizes.getD s 0 = 2 ^ anchoredTarget s := by
    intro s hs
    exact restrictedEffectiveAnchoredSizes_getD
      ambientLength Δ grid s hs
  have hmono : ∀ s < N + 1,
      anchoredTarget (s + 1) ≤ anchoredTarget s := by
    exact restrictedAnchoredTarget_mono ambientLength Δ grid hnambient
  induction time with
  | zero =>
      obtain ⟨output, state, hrun, hstate, hBzero, hliveZero⟩ :=
        restrictedEffectiveAnchoredInitialState_spec 𝒜 ambientLength Δ grid
          hnambient
      refine ⟨output, state, hrun, hstate, hBzero, ?_, ?_⟩
      · simpa [restrictedAnchoredProcessedBadUnion] using hliveZero
      · intro eventTime heventTime
        omega
  | succ time ih =>
      obtain ⟨previousCode, previous, hrun, hprevious, hpreviousB,
          hpreviousLive, hprocessed⟩ := ih
      let badCodes := restrictedSampledBadBatchAt c
        (restrictedCurveGridCode grid) 𝒜.toPre N Δ time
      let bads : List (Finset BitString) :=
        badCodes.map (fun w => (decodeCoverCodeList w).toFinset)
      have hlen_bads : badCodes.length = bads.length := by
        simp [bads]
      have hbad : ∀ i < badCodes.length,
          decodeCoverCodeList (badCodes.getD i []) =
            canonicalFinsetList (bads.getD i ∅) := by
        intro i hi
        have hwmem : badCodes[i] ∈ restrictedSampledBadBatchAt c
            (restrictedCurveGridCode grid) 𝒜.toPre N Δ time := by
          exact List.getElem_mem hi
        obtain ⟨bad, hdecode⟩ :=
          restrictedSampledBadBatchAt_decode_sound c
            (restrictedCurveGridCode grid) 𝒜 N Δ time badCodes[i] hwmem
        rw [List.getD_eq_getElem _ _ hi]
        have hibads : i < bads.length := by omega
        rw [List.getD_eq_getElem _ _ hibads]
        simp only [bads, List.getElem_map]
        rw [hdecode, canonicalFinsetList_toFinset]
      obtain ⟨output, state, hbatch, hstate, hBzero, hliveZero,
          hroot, hbatchDisjoint⟩ :=
        restrictedEffectiveSampledRunProcess_spec 𝒜 (N + 1) ambientLength
          anchoredTarget sizes hlen hpowers hmono previousCode previous
          badCodes bads hprevious hlen_bads hbad
      refine ⟨output, state, ?_, hstate, ?_, ?_, ?_⟩
      · change
          (restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ grid
            time).bind (fun current =>
              restrictedEffectiveSampledRunProcess 𝒜
                (𝒜.overhead ambientLength) sizes current badCodes) =
            Part.some output
        rw [hrun, Part.bind_some, hbatch]
      · exact hBzero.trans hpreviousB
      · rw [hliveZero, hpreviousLive]
        ext x
        simp [restrictedAnchoredProcessedBadUnion,
          restrictedDecodedBadCodesUnion, bads, badCodes, and_assoc]
      · intro eventTime heventTime w hw bad hdecode s hs
        by_cases hcurrent : eventTime = time
        · subst eventTime
          obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
          have hiBadCodes : i < badCodes.length := by
            simpa [badCodes] using hi
          have hibads : i < bads.length := by omega
          have hbadEq : bads.getD i ∅ = bad := by
            rw [List.getD_eq_getElem _ _ hibads]
            simp only [bads, List.getElem_map]
            rw [hwi, hdecode, canonicalFinsetList_toFinset]
          have hdisjoint := hbatchDisjoint i hibads s hs
          rw [hbadEq] at hdisjoint
          exact hdisjoint
        · have heventPrevious : eventTime < time := by omega
          have hprevDisjoint := hprocessed eventTime heventPrevious w hw bad
            hdecode 0 (Nat.zero_le (N + 1))
          apply Finset.disjoint_left.mpr
          intro x hx hxbad
          exact (Finset.disjoint_left.mp hprevDisjoint) (hroot s hs hx) hxbad

/-- Code-level lookup for sampled model `s`, now stored at anchored level
`s + 1`. -/
lemma restrictedAnchoredRun_sample_getD
    {𝒜 : DescriptionFamily} {n k N ambientLength Δ : ℕ}
    {target : ℕ → ℕ} {grid : RestrictedCurveGrid n k N target}
    {stateCode : BitString}
    {state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
      (2 * 𝒜.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength Δ grid)}
    (hstate : DecodesToRestrictedSampledRunState stateCode state)
    (s : ℕ) (hs : s ≤ N) :
    decodeCoverCodeList
        ((decodeListCode (restrictedSelectorField stateCode 1)).getD (s + 1) []) =
      canonicalFinsetList (state.B (s + 1)) := by
  exact (hstate.2 (s + 1) (by omega)).1

/-- Forget the fixed anchor and shift the sampled levels back down by one. -/
def RestrictedSampledRunState.dropAnchor
    {𝒜 : DescriptionFamily} {n k N ambientLength Δ : ℕ}
    {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (state : RestrictedSampledRunState 𝒜 (N + 1) ambientLength
      (2 * 𝒜.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength Δ grid)) :
    RestrictedSampledRunState 𝒜 N ambientLength
      (2 * 𝒜.overhead ambientLength)
      (fun s => grid.j s - (Δ + 1)) where
  B := fun s => state.B (s + 1)
  live := fun s => state.live (s + 1)
  mem_family := by
    intro s hs
    exact state.mem_family (s + 1) (by omega)
  size_bound := by
    intro s hs
    simpa using state.size_bound (s + 1) (by omega)
  live_subset := by
    intro s hs
    exact state.live_subset (s + 1) (by omega)
  live_ambient := by
    intro s hs
    exact state.live_ambient (s + 1) (by omega)
  live_monotonic := by
    intro s hs
    exact state.live_monotonic (s + 1) (by omega)
  density := by
    intro s hs
    simpa using state.density (s + 1) (by omega)

end Kolmogorov
