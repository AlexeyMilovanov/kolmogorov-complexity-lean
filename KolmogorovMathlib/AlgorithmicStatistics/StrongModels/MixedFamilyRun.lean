import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain
import KolmogorovMathlib.Restricted.Examples.Cylinders

/-!
# Mixed-family anchored runs

The family-curve construction uses one description family for rebuilding its
live models.  Strong-profile realization needs a different family for the
forbidden-description stream: cylinders supply the good models, while the full
family supplies the lower-profile exclusions.  This module separates those two
roles without changing the existing one-family executor.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- Anchored chronological executor with good/rebuilding family `𝒢` and
bad-enumeration family `ℬ`.  States and rebuilds use only `𝒢`; chronological
bad batches are decoded from `ℬ.toPre`. -/
noncomputable def restrictedEffectiveAnchoredSampledRunAgainst
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) : Part BitString :=
  let q0 := 𝒢.overhead ambientLength
  let sizes := restrictedEffectiveAnchoredSizes ambientLength Δ grid
  Nat.rec (motive := fun _ => Part BitString)
    (restrictedEffectiveAnchoredInitialState 𝒢 ambientLength Δ grid)
    (fun stage current => current.bind (fun state =>
      restrictedEffectiveSampledRunProcess 𝒢 q0 sizes state
        (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
          ℬ.toPre N Δ stage)))
    time

@[simp] lemma restrictedEffectiveAnchoredSampledRunAgainst_zero
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target) :
    restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
        ambientLength Δ grid 0 =
      restrictedEffectiveAnchoredInitialState 𝒢 ambientLength Δ grid := rfl

@[simp] lemma restrictedEffectiveAnchoredSampledRunAgainst_succ
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ time : ℕ)
    (grid : RestrictedCurveGrid n k N target) :
    restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
        ambientLength Δ grid (time + 1) =
      (restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
        ambientLength Δ grid time).bind (fun state =>
          restrictedEffectiveSampledRunProcess 𝒢
            (𝒢.overhead ambientLength)
            (restrictedEffectiveAnchoredSizes ambientLength Δ grid)
            state
            (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
              ℬ.toPre N Δ time)) := rfl

/-- The mixed executor recovers the existing one-family executor on the
diagonal. -/
theorem restrictedEffectiveAnchoredSampledRunAgainst_self
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (time : ℕ) :
    restrictedEffectiveAnchoredSampledRunAgainst 𝒜 𝒜 c
        ambientLength Δ grid time =
      restrictedEffectiveAnchoredSampledRun 𝒜 c
        ambientLength Δ grid time := by
  rfl

/-- Replay correctness for the mixed run: at time `τ + 1` the mixed anchored
executor equals the event-prefix executor that rebuilds with `𝒢` but reads the
first `(ℬ-stream τ).length` events of any later `ℬ`-stream stage `T`.  The
event-prefix primitives take the event list as a plain parameter, so this is the
one-family boundary argument with the rebuild family `𝒢` and the
bad-enumeration family `ℬ` kept separate. -/
lemma restrictedEffectiveAnchoredSampledRunAgainst_eq_eventPrefix
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    {T τ : ℕ} (hτ : τ ≤ T) :
    restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c ambientLength Δ grid
        (τ + 1) =
      (restrictedEffectiveAnchoredInitialState 𝒢 ambientLength Δ grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒢 (𝒢.overhead ambientLength)
          (restrictedEffectiveAnchoredSizes ambientLength Δ grid) st0
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            ℬ.toPre N Δ T)
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            ℬ.toPre N Δ τ).length) := by
  induction τ with
  | zero =>
      rw [restrictedEffectiveAnchoredSampledRunAgainst_succ,
        restrictedEffectiveAnchoredSampledRunAgainst_zero]
      apply congrArg
      funext st0
      rw [show restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
          ℬ.toPre N Δ 0 = restrictedSampledBadCodeStream c
            (restrictedCurveGridCode grid) ℬ.toPre N Δ 0 from rfl,
        restrictedEffectiveSampledRunProcess_eq_prefixRun]
      exact restrictedEventPrefixRun_congr 𝒢 _ _ _ _
        (fun i hi => (prefix_getD_eq
          (restrictedSampledBadCodeStream_prefix_of_le c
            (restrictedCurveGridCode grid) ℬ.toPre N Δ
            (Nat.zero_le T)) hi).symm)
  | succ τ ih =>
      have hτT : τ ≤ T := by omega
      rw [restrictedEffectiveAnchoredSampledRunAgainst_succ, ih hτT,
        Part.bind_assoc]
      apply congrArg
      funext st0
      set q0 := 𝒢.overhead ambientLength with hq0
      set sizes := restrictedEffectiveAnchoredSizes ambientLength Δ grid
        with hsizes
      set gridCode := restrictedCurveGridCode grid with hgridCode
      set streamτ := restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ τ
        with hstreamτ
      set streamT := restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ T
        with hstreamT
      set batch := restrictedSampledBadBatchAt c gridCode ℬ.toPre N Δ (τ + 1)
        with hbatchdef
      have hbatch_new : batch = restrictedSampledNewBadBatch c gridCode
          ℬ.toPre N Δ τ := rfl
      have happend : streamτ ++ restrictedSampledNewBadBatch c gridCode
          ℬ.toPre N Δ τ = restrictedSampledBadCodeStream c gridCode ℬ.toPre
            N Δ (τ + 1) :=
        restrictedSampledNewBadBatch_append c gridCode ℬ.toPre N Δ τ
      have hprefix1 : restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ
          (τ + 1) <+: streamT :=
        restrictedSampledBadCodeStream_prefix_of_le c gridCode ℬ.toPre N Δ
          (by omega)
      have hlen1 : (restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ
          (τ + 1)).length = streamτ.length + batch.length := by
        rw [← happend, hbatch_new]
        simp
      have hproc : ∀ state : BitString,
          restrictedEffectiveSampledRunProcess 𝒢 q0 sizes state batch =
            restrictedEventPrefixRun 𝒢 q0 sizes state
              (streamT.drop streamτ.length) batch.length := by
        intro state
        rw [restrictedEffectiveSampledRunProcess_eq_prefixRun]
        apply restrictedEventPrefixRun_congr
        intro i hi
        have hidx : streamτ.length + i <
            (restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ
              (τ + 1)).length := by
          rw [hlen1]
          omega
        calc batch.getD i []
            = (streamτ ++ restrictedSampledNewBadBatch c gridCode ℬ.toPre
                N Δ τ).getD (streamτ.length + i) [] := by
              have hsub : streamτ.length + i - streamτ.length = i := by
                omega
              rw [hbatch_new, List.getD, List.getD,
                List.getElem?_append_right (by omega), hsub]
          _ = (restrictedSampledBadCodeStream c gridCode ℬ.toPre N Δ
                (τ + 1)).getD (streamτ.length + i) [] := by rw [happend]
          _ = streamT.getD (streamτ.length + i) [] :=
              (prefix_getD_eq hprefix1 hidx).symm
          _ = (streamT.drop streamτ.length).getD i [] := by
              rw [List.getD, List.getD, List.getElem?_drop]
      simp only [hproc]
      rw [← restrictedEventPrefixRun_add, hlen1]

/-- Family monotonicity of the restricted profile: enlarging the description
family enlarges `P_x^𝒜`.  This is the transport used in final profile assembly
to turn a `𝒢`-model into a `ℬ`-model whenever `𝒢 ⊆ ℬ`. -/
lemma inDescriptionProfileIn_mono_family
    {𝒢 ℬ : DescriptionFamily} (hsub : ∀ S, 𝒢.mem S → ℬ.mem S)
    {U : Map} {x : BitString} {i j : ℕ}
    (h : InDescriptionProfileIn 𝒢 U x i j) :
    InDescriptionProfileIn ℬ U x i j := by
  obtain ⟨S, hS, hmem, hdesc⟩ := h
  exact ⟨S, hS, hsub S hmem, hdesc⟩

/-- Every nonempty cylinder is, in particular, a member of the unrestricted
family. -/
lemma cylinderFamily_le_fullFamily :
    ∀ S, cylinderFamily.mem S → fullFamily.mem S := by
  intro S hS
  change S.Nonempty
  exact cylinderFamily.nonempty_of_mem hS

/-- Finite-time semantics of the mixed run.  The decoded state is a `𝒢` state,
while its root deletion invariant and all processed-event disjointness facts
refer to batches enumerated from `ℬ`. -/
lemma restrictedEffectiveAnchoredSampledRunAgainst_spec
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ time : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒢 (N + 1) ambientLength
          (2 * 𝒢.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength Δ grid),
        restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
            ambientLength Δ grid time = Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        state.B 0 = stringsOfLength ambientLength ∧
        state.live 0 = stringsOfLength ambientLength \
          restrictedAnchoredProcessedBadUnion c ℬ Δ grid time ∧
        ∀ eventTime < time,
          ∀ w ∈ restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
            ℬ.toPre N Δ eventTime,
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
      anchoredTarget (s + 1) ≤ anchoredTarget s :=
    restrictedAnchoredTarget_mono ambientLength Δ grid hnambient
  induction time with
  | zero =>
      obtain ⟨output, state, hrun, hstate, hBzero, hliveZero⟩ :=
        restrictedEffectiveAnchoredInitialState_spec 𝒢 ambientLength Δ grid
          hnambient
      refine ⟨output, state, hrun, hstate, hBzero, ?_, ?_⟩
      · simpa [restrictedAnchoredProcessedBadUnion] using hliveZero
      · intro eventTime heventTime
        omega
  | succ time ih =>
      obtain ⟨previousCode, previous, hrun, hprevious, hpreviousB,
          hpreviousLive, hprocessed⟩ := ih
      let badCodes := restrictedSampledBadBatchAt c
        (restrictedCurveGridCode grid) ℬ.toPre N Δ time
      let bads : List (Finset BitString) :=
        badCodes.map (fun w => (decodeCoverCodeList w).toFinset)
      have hlen_bads : badCodes.length = bads.length := by
        simp [bads]
      have hbad : ∀ i < badCodes.length,
          decodeCoverCodeList (badCodes.getD i []) =
            canonicalFinsetList (bads.getD i ∅) := by
        intro i hi
        have hwmem : badCodes[i] ∈ restrictedSampledBadBatchAt c
            (restrictedCurveGridCode grid) ℬ.toPre N Δ time :=
          List.getElem_mem hi
        obtain ⟨bad, hdecode⟩ :=
          restrictedSampledBadBatchAt_decode_sound c
            (restrictedCurveGridCode grid) ℬ N Δ time badCodes[i] hwmem
        rw [List.getD_eq_getElem _ _ hi]
        have hibads : i < bads.length := by omega
        rw [List.getD_eq_getElem _ _ hibads]
        simp only [bads, List.getElem_map]
        rw [hdecode, canonicalFinsetList_toFinset]
      obtain ⟨output, state, hbatch, hstate, hBzero, hliveZero,
          hroot, hbatchDisjoint⟩ :=
        restrictedEffectiveSampledRunProcess_spec 𝒢 (N + 1) ambientLength
          anchoredTarget sizes hlen hpowers hmono previousCode previous
          badCodes bads hprevious hlen_bads hbad
      refine ⟨output, state, ?_, hstate, ?_, ?_, ?_⟩
      · rw [restrictedEffectiveAnchoredSampledRunAgainst_succ,
          hrun, Part.bind_some, hbatch]
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
          exact (Finset.disjoint_left.mp hprevDisjoint)
            (hroot s hs hx) hxbad

/-- The mixed terminal root remains nonempty whenever the `ℬ` processed union
is smaller than the ambient cube. -/
lemma restrictedAnchoredRun_terminal_nonempty_against
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ time : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength)
    (hcard : (restrictedAnchoredProcessedBadUnion c ℬ Δ grid time).card <
      2 ^ ambientLength) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒢 (N + 1) ambientLength
          (2 * 𝒢.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength Δ grid),
        restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
            ambientLength Δ grid time = Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        (state.live (N + 1)).Nonempty := by
  obtain ⟨output, state, hrun, hstate, _hBzero, hroot, _hprocessed⟩ :=
    restrictedEffectiveAnchoredSampledRunAgainst_spec 𝒢 ℬ c
      ambientLength Δ time grid hnambient
  have hroot_nonempty : (state.live 0).Nonempty := by
    rw [hroot, Finset.sdiff_nonempty]
    intro hsubset
    have hcard_le := Finset.card_le_card hsubset
    rw [cardStringsOfLength] at hcard_le
    omega
  have hterminal : (state.live (N + 1)).Nonempty :=
    restricted_rebuild_suffix_preserves_terminal_nonempty
      0 (N + 1) (2 * 𝒢.overhead ambientLength)
      (restrictedAnchoredTarget ambientLength Δ grid) state.live
      (Nat.zero_le (N + 1)) hroot_nonempty
      (fun i _hi hiN => state.density i hiN)
  exact ⟨output, state, hrun, hstate, hterminal⟩

/-- Stabilization of the `ℬ` stream forces every terminal live
candidate of the `𝒢` run to avoid the `ℬ` forbidden profile. -/
lemma restrictedAnchoredFinalState_avoids_profileBadSet_against
    (U : Map)
    (𝒢 ℬ : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength streamSlack profileSlack T : ℕ)
    (grid : RestrictedCurveGrid n k N target)
    (hc : IsCodeFor c U)
    (hnambient : n ≤ ambientLength)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    (hslack : streamSlack ≤ profileSlack)
    (hstable : ∀ time ≥ T,
      restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          ℬ.toPre N streamSlack time =
        restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          ℬ.toPre N streamSlack T) :
    ∃ output : BitString,
      ∃ state : RestrictedSampledRunState 𝒢 (N + 1) ambientLength
          (2 * 𝒢.overhead ambientLength)
          (restrictedAnchoredTarget ambientLength streamSlack grid),
        restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
            ambientLength streamSlack grid (T + 1) = Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∀ x ∈ state.live (N + 1),
          x ∉ restrictedProfileBadSet ℬ U (state.live (N + 1)) k
            profileSlack target := by
  obtain ⟨output, state, hrun, hstate, _hBzero, _hroot, hprocessed⟩ :=
    restrictedEffectiveAnchoredSampledRunAgainst_spec 𝒢 ℬ c
      ambientLength streamSlack (T + 1) grid hnambient
  refine ⟨output, state, hrun, hstate, ?_⟩
  intro x hx hbad
  obtain ⟨_hbad_subset, hbad_spec⟩ :=
    restrictedProfileBadSet_spec ℬ U (state.live (N + 1)) k
      profileSlack target
  obtain ⟨i, hi, _htarget, hprof⟩ := (hbad_spec x hx).mp hbad
  have hprof' :
      InDescriptionProfileIn ℬ U x i
        (target i - (streamSlack + 1)) :=
    hprof.mono_j
      (Nat.sub_le_sub_left (Nat.succ_le_succ hslack) (target i))
  obtain ⟨w, appearanceTime, _s, _hs, hwstream, hdescription⟩ :=
    restrictedSampledBadCodeStream_catches_violation grid U c hc
      streamSlack hstrict x i hi ℬ hprof'
  have hwT : w ∈ restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) ℬ.toPre N streamSlack T := by
    by_cases htime : appearanceTime ≤ T
    · have hprefix := restrictedSampledBadCodeStream_prefix_of_le c
        (restrictedCurveGridCode grid) ℬ.toPre N streamSlack htime
      exact hprefix.subset hwstream
    · have hTle : T ≤ appearanceTime :=
        Nat.le_of_lt (Nat.lt_of_not_ge htime)
      rw [← hstable appearanceTime hTle]
      exact hwstream
  obtain ⟨eventTime, heventTime, hbatch⟩ :=
    restrictedSampledBadCodeStream_mem_batchAt c
      (restrictedCurveGridCode grid) ℬ.toPre N streamSlack T hwT
  obtain ⟨bad, hdecode⟩ :=
    restrictedSampledBadBatchAt_decode_sound c
      (restrictedCurveGridCode grid) ℬ N streamSlack eventTime w hbatch
  obtain ⟨S, hS, _hSmem, hwcode, _hScard, hxS⟩ := hdescription
  have hbad_eq : bad = S := by
    have hdecodeS :
        decodeCoverCodeList w = canonicalFinsetList S := by
      rw [hwcode]
      exact decodeCoverCodeList_code S hS
    rw [hdecodeS] at hdecode
    have hfinsets := congrArg List.toFinset hdecode.symm
    simpa using hfinsets
  have hdisjoint := hprocessed eventTime (by omega) w hbatch bad hdecode
    (N + 1) le_rfl
  rw [hbad_eq] at hdisjoint
  exact (Finset.disjoint_left.mp hdisjoint) hx hxS

/-- Mixed structural endpoint for a fixed code: good models are in `𝒢`, while
the common survivor avoids the full `ℬ` forbidden profile. -/
lemma exists_restricted_anchored_structural_output_for_code_against
    (U : Map) (𝒢 ℬ : DescriptionFamily) (c : Code) (hc : IsCodeFor c U)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    ∃ T output,
      ∃ state : RestrictedSampledRunState 𝒢 (N + 1)
          (n + logSlack 8 n) (2 * 𝒢.overhead (n + logSlack 8 n))
          (restrictedAnchoredTarget (n + logSlack 8 n)
            (sqrtSlack 8 n) grid),
        restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
            (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
              Part.some output ∧
        DecodesToRestrictedSampledRunState output state ∧
        ∃ x : BitString, x ∈ state.live (N + 1) ∧
          x ∉ restrictedProfileBadSet ℬ U (state.live (N + 1)) k
            (sqrtSlack 8 n) target := by
  obtain ⟨T, hstable⟩ := restrictedSampledBadCodeStream_stabilizes c
    (restrictedCurveGridCode grid) ℬ.toPre N (sqrtSlack 8 n)
  have hcard :
      (restrictedAnchoredProcessedBadUnion c ℬ (sqrtSlack 8 n) grid
        (T + 1)).card < 2 ^ (n + logSlack 8 n) :=
    (restrictedAnchoredProcessedBadUnion_card_le c ℬ
      (sqrtSlack 8 n) grid T).trans_lt
        (restrictedCurveGrid_bad_volume_padding grid hN hkn htarget hstrict)
  obtain ⟨output, state, hrun, hstate, hnonempty⟩ :=
    restrictedAnchoredRun_terminal_nonempty_against 𝒢 ℬ c
      (n + logSlack 8 n) (sqrtSlack 8 n) (T + 1) grid (by omega) hcard
  obtain ⟨output', state', hrun', hstate', havoids⟩ :=
    restrictedAnchoredFinalState_avoids_profileBadSet_against U 𝒢 ℬ c
      (n + logSlack 8 n) (sqrtSlack 8 n) (sqrtSlack 8 n) T grid hc
      (by omega) hstrict le_rfl hstable
  have houtput : output' = output := by
    rw [hrun] at hrun'
    exact Part.some_injective hrun'.symm
  subst output'
  have hlive_eq : state'.live (N + 1) = state.live (N + 1) := by
    have hcodes : canonicalFinsetList (state'.live (N + 1)) =
        canonicalFinsetList (state.live (N + 1)) :=
      (hstate'.2 (N + 1) le_rfl).2.symm.trans
        (hstate.2 (N + 1) le_rfl).2
    have hfinsets := congrArg List.toFinset hcodes
    simpa using hfinsets
  have hnonempty' : (state'.live (N + 1)).Nonempty := by
    rw [hlive_eq]
    exact hnonempty
  obtain ⟨x, hx⟩ := hnonempty'
  exact ⟨T, output, state', hrun', hstate', x, hx, havoids x hx⟩

/-- Mixed structural endpoint with the decompressor code chosen internally. -/
lemma exists_restricted_anchored_structural_output_against
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒢 ℬ : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    ∃ c : Code, IsCodeFor c U ∧
      ∃ T output,
        ∃ state : RestrictedSampledRunState 𝒢 (N + 1)
            (n + logSlack 8 n) (2 * 𝒢.overhead (n + logSlack 8 n))
            (restrictedAnchoredTarget (n + logSlack 8 n)
              (sqrtSlack 8 n) grid),
          restrictedEffectiveAnchoredSampledRunAgainst 𝒢 ℬ c
              (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
                Part.some output ∧
          DecodesToRestrictedSampledRunState output state ∧
          ∃ x : BitString, x ∈ state.live (N + 1) ∧
            x ∉ restrictedProfileBadSet ℬ U (state.live (N + 1)) k
              (sqrtSlack 8 n) target := by
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨T, output, state, hrun, hstate, hsurvivor⟩ :=
    exists_restricted_anchored_structural_output_for_code_against
      U 𝒢 ℬ c hc grid hN hkn htarget hstrict
  exact ⟨c, hc, T, output, state, hrun, hstate, hsurvivor⟩

end Kolmogorov
