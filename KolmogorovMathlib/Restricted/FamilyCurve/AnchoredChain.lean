/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Restricted.FamilyCurve.RunChain
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun
import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds

/-!
# M7: the anchored run as an event-indexed chain

The anchored effective run processes its bad stream batch by batch; each batch
is a contiguous block of stream events.  This module re-indexes the run by
single events (`restrictedEventPrefixRun`), identifies the batch boundaries
with the chronological run, and packages the decoded per-event states as a
`RestrictedRunChain`, so that the version-count bound of `RunChain` applies to
the actual anchored construction.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- Binding a part into `Part.some` is the identity. -/
private lemma part_bind_some {α : Type} (p : Part α) :
    p.bind Part.some = p := by
  ext a
  simp

/-- Event-indexed prefix executor: process the first `m` events. -/
noncomputable def restrictedEventPrefixRun (𝒜 : DescriptionFamily) (q0 : ℕ)
    (sizes : List ℕ) (stateCode : BitString) (events : List BitString)
    (m : ℕ) : Part BitString :=
  Nat.rec (motive := fun _ => Part BitString)
    (Part.some stateCode)
    (fun idx current => current.bind (fun state =>
      restrictedEffectiveSampledRunStep 𝒜 q0 sizes state
        (events.getD idx [])))
    m

@[simp] lemma restrictedEventPrefixRun_zero (𝒜 : DescriptionFamily) (q0 : ℕ)
    (sizes : List ℕ) (stateCode : BitString) (events : List BitString) :
    restrictedEventPrefixRun 𝒜 q0 sizes stateCode events 0 =
      Part.some stateCode := rfl

/-- The `m + 1`-prefix executor runs one more event after the `m`-prefix. -/
lemma restrictedEventPrefixRun_succ (𝒜 : DescriptionFamily) (q0 : ℕ)
    (sizes : List ℕ) (stateCode : BitString) (events : List BitString)
    (m : ℕ) :
    restrictedEventPrefixRun 𝒜 q0 sizes stateCode events (m + 1) =
      (restrictedEventPrefixRun 𝒜 q0 sizes stateCode events m).bind
        (fun state => restrictedEffectiveSampledRunStep 𝒜 q0 sizes state
          (events.getD m [])) := rfl

/-- The batch processor is the event-prefix executor run to the end. -/
lemma restrictedEffectiveSampledRunProcess_eq_prefixRun
    (𝒜 : DescriptionFamily) (q0 : ℕ) (sizes : List ℕ)
    (stateCode : BitString) (badCodes : List BitString) :
    restrictedEffectiveSampledRunProcess 𝒜 q0 sizes stateCode badCodes =
      restrictedEventPrefixRun 𝒜 q0 sizes stateCode badCodes
        badCodes.length := rfl

/-- The prefix executor only reads the events below the prefix bound. -/
lemma restrictedEventPrefixRun_congr (𝒜 : DescriptionFamily) (q0 : ℕ)
    (sizes : List ℕ) (stateCode : BitString)
    {events events' : List BitString} (m : ℕ)
    (h : ∀ i < m, events.getD i [] = events'.getD i []) :
    restrictedEventPrefixRun 𝒜 q0 sizes stateCode events m =
      restrictedEventPrefixRun 𝒜 q0 sizes stateCode events' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [restrictedEventPrefixRun_succ, restrictedEventPrefixRun_succ,
        ih (fun i hi => h i (by omega)), h m (by omega)]

/-- Prefix executors compose across an additive split of the event count. -/
lemma restrictedEventPrefixRun_add (𝒜 : DescriptionFamily) (q0 : ℕ)
    (sizes : List ℕ) (stateCode : BitString) (events : List BitString)
    (m₁ m₂ : ℕ) :
    restrictedEventPrefixRun 𝒜 q0 sizes stateCode events (m₁ + m₂) =
      (restrictedEventPrefixRun 𝒜 q0 sizes stateCode events m₁).bind
        (fun mid => restrictedEventPrefixRun 𝒜 q0 sizes mid
          (events.drop m₁) m₂) := by
  induction m₂ with
  | zero =>
      simp [restrictedEventPrefixRun_zero]
  | succ m₂ ih =>
      rw [show m₁ + (m₂ + 1) = (m₁ + m₂) + 1 by omega,
        restrictedEventPrefixRun_succ, ih, Part.bind_assoc]
      apply congrArg
      funext mid
      rw [restrictedEventPrefixRun_succ]
      have hgetD : events.getD (m₁ + m₂) [] =
          (events.drop m₁).getD m₂ [] := by
        rw [List.getD, List.getD, List.getElem?_drop]
      rw [hgetD]

/-- Prefixes of the underlying list agree on `getD` below their length. -/
lemma prefix_getD_eq {l₁ l₂ : List BitString} (h : l₁ <+: l₂)
    {i : ℕ} (hi : i < l₁.length) :
    l₂.getD i [] = l₁.getD i [] := by
  obtain ⟨tail, rfl⟩ := h
  rw [List.getD, List.getD, List.getElem?_append_left hi]

section EventBoundary

variable (𝒜 : DescriptionFamily) (c : Code)
  {n k N : ℕ} {target : ℕ → ℕ}
  (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)

/-- The anchored run at time `τ + 1` is the event-prefix executor applied to
the first `(stream τ).length` events of any later stream stage. -/
lemma restrictedEffectiveAnchoredSampledRun_eq_eventPrefix
    {T τ : ℕ} (hτ : τ ≤ T) :
    restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ grid (τ + 1) =
      (restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒜 (𝒜.overhead ambientLength)
          (restrictedEffectiveAnchoredSizes ambientLength Δ grid) st0
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N Δ T)
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N Δ τ).length) := by
  induction τ with
  | zero =>
      have hstep : restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ
          grid 1 =
          (restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ
            grid).bind (fun state =>
              restrictedEffectiveSampledRunProcess 𝒜
                (𝒜.overhead ambientLength)
                (restrictedEffectiveAnchoredSizes ambientLength Δ grid) state
                (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
                  𝒜.toPre N Δ 0)) := rfl
      rw [hstep]
      apply congrArg
      funext st0
      rw [show restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
          𝒜.toPre N Δ 0 = restrictedSampledBadCodeStream c
            (restrictedCurveGridCode grid) 𝒜.toPre N Δ 0 from rfl,
        restrictedEffectiveSampledRunProcess_eq_prefixRun]
      exact restrictedEventPrefixRun_congr 𝒜 _ _ _ _
        (fun i hi => (prefix_getD_eq
          (restrictedSampledBadCodeStream_prefix_of_le c
            (restrictedCurveGridCode grid) 𝒜.toPre N Δ
            (Nat.zero_le T)) hi).symm)
  | succ τ ih =>
      have hτT : τ ≤ T := by omega
      have hstep : restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ
          grid (τ + 1 + 1) =
          (restrictedEffectiveAnchoredSampledRun 𝒜 c ambientLength Δ grid
            (τ + 1)).bind (fun state =>
              restrictedEffectiveSampledRunProcess 𝒜
                (𝒜.overhead ambientLength)
                (restrictedEffectiveAnchoredSizes ambientLength Δ grid) state
                (restrictedSampledBadBatchAt c (restrictedCurveGridCode grid)
                  𝒜.toPre N Δ (τ + 1))) := rfl
      rw [hstep, ih hτT, Part.bind_assoc]
      apply congrArg
      funext st0
      set q0 := 𝒜.overhead ambientLength with hq0
      set sizes := restrictedEffectiveAnchoredSizes ambientLength Δ grid
        with hsizes
      set gridCode := restrictedCurveGridCode grid with hgridCode
      set streamτ := restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ τ
        with hstreamτ
      set streamT := restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ T
        with hstreamT
      set batch := restrictedSampledBadBatchAt c gridCode 𝒜.toPre N Δ (τ + 1)
        with hbatchdef
      have hbatch_new : batch = restrictedSampledNewBadBatch c gridCode
          𝒜.toPre N Δ τ := rfl
      have happend : streamτ ++ restrictedSampledNewBadBatch c gridCode
          𝒜.toPre N Δ τ = restrictedSampledBadCodeStream c gridCode 𝒜.toPre
            N Δ (τ + 1) :=
        restrictedSampledNewBadBatch_append c gridCode 𝒜.toPre N Δ τ
      have hprefix1 : restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ
          (τ + 1) <+: streamT :=
        restrictedSampledBadCodeStream_prefix_of_le c gridCode 𝒜.toPre N Δ
          (by omega)
      have hlen1 : (restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ
          (τ + 1)).length = streamτ.length + batch.length := by
        rw [← happend, hbatch_new]
        simp
      have hproc : ∀ state : BitString,
          restrictedEffectiveSampledRunProcess 𝒜 q0 sizes state batch =
            restrictedEventPrefixRun 𝒜 q0 sizes state
              (streamT.drop streamτ.length) batch.length := by
        intro state
        rw [restrictedEffectiveSampledRunProcess_eq_prefixRun]
        apply restrictedEventPrefixRun_congr
        intro i hi
        have hidx : streamτ.length + i <
            (restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ
              (τ + 1)).length := by
          rw [hlen1]
          omega
        calc batch.getD i []
            = (streamτ ++ restrictedSampledNewBadBatch c gridCode 𝒜.toPre
                N Δ τ).getD (streamτ.length + i) [] := by
              have hsub : streamτ.length + i - streamτ.length = i := by
                omega
              rw [hbatch_new, List.getD, List.getD,
                List.getElem?_append_right (by omega), hsub]
          _ = (restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ
                (τ + 1)).getD (streamτ.length + i) [] := by rw [happend]
          _ = streamT.getD (streamτ.length + i) [] :=
              (prefix_getD_eq hprefix1 hidx).symm
          _ = (streamT.drop streamτ.length).getD i [] := by
              rw [List.getD, List.getD, List.getElem?_drop]
      simp only [hproc]
      rw [← restrictedEventPrefixRun_add, hlen1]

end EventBoundary

section ChainConstruction

/-- Decoding determines the model and live sets of a decoded state. -/
lemma decodesTo_eq_B_live {𝒜 : DescriptionFamily}
    {NN aL oB : ℕ} {tt : ℕ → ℕ} {code : BitString}
    {st st' : RestrictedSampledRunState 𝒜 NN aL oB tt}
    (h : DecodesToRestrictedSampledRunState code st)
    (h' : DecodesToRestrictedSampledRunState code st')
    {s : ℕ} (hs : s ≤ NN) :
    st.B s = st'.B s ∧ st.live s = st'.live s := by
  obtain ⟨_hlen, hfields⟩ := h
  obtain ⟨_hlen', hfields'⟩ := h'
  obtain ⟨hB, hlive⟩ := hfields s hs
  obtain ⟨hB', hlive'⟩ := hfields' s hs
  constructor
  · have hEq := hB.symm.trans hB'
    have h2 := congrArg List.toFinset hEq
    rwa [canonicalFinsetList_toFinset, canonicalFinsetList_toFinset] at h2
  · have hEq := hlive.symm.trans hlive'
    have h2 := congrArg List.toFinset hEq
    rwa [canonicalFinsetList_toFinset, canonicalFinsetList_toFinset] at h2

/-- The one-step contract only reads the model/live sets, so it transfers
along set-equal replacements of both endpoint states. -/
lemma stepSpec_transfer {𝒜 : DescriptionFamily}
    {NN aL oB : ℕ} {tt : ℕ → ℕ}
    {st st' nx nx' : RestrictedSampledRunState 𝒜 NN aL oB tt}
    {bad : Finset BitString} {q : ℕ}
    (hstB : ∀ s ≤ NN, st.B s = st'.B s ∧ st.live s = st'.live s)
    (hnxB : ∀ s ≤ NN, nx.B s = nx'.B s ∧ nx.live s = nx'.live s)
    (hspec : RestrictedSampledRunStepSpec st nx bad q) :
    RestrictedSampledRunStepSpec st' nx' bad q := by
  obtain ⟨hqN, hcases, hretain, hsubset, hdouble⟩ := hspec
  have hfails_iff : ∀ r, r < NN →
      (restrictedSampledDensityFails st' bad r ↔
        restrictedSampledDensityFails st bad r) := by
    intro r hr
    unfold restrictedSampledDensityFails
    rw [(hstB r (by omega)).2, (hstB (r + 1) (by omega)).2]
  refine ⟨hqN, ?_, ?_, ?_, ?_⟩
  · rcases hcases with ⟨hqEq, hnone⟩ | ⟨hqlt, hfail, hmin⟩
    · exact Or.inl ⟨hqEq, fun s hs h' =>
        hnone s hs ((hfails_iff s hs).mp h')⟩
    · exact Or.inr ⟨hqlt, (hfails_iff q hqlt).mpr hfail,
        fun s hs h' => hmin s hs ((hfails_iff s (by omega)).mp h')⟩
  · intro s hs
    have hsNN : s ≤ NN := by omega
    rw [← (hstB s hsNN).1, ← (hstB s hsNN).2, ← (hnxB s hsNN).1,
      ← (hnxB s hsNN).2]
    exact hretain s hs
  · intro s hqs hsNN
    rw [← (hnxB s hsNN).2, ← (hstB q (by omega)).2]
    exact hsubset s hqs hsNN
  · intro s hqs hsNN
    rw [← (hnxB s (by omega)).2, ← (hnxB (s + 1) (by omega)).2]
    exact hdouble s hqs hsNN

@[simp] lemma decodeCoverCodeList_nil :
    decodeCoverCodeList ([] : BitString) = [] := rfl

/-- Every stream slot decodes to a canonical finite-set list (junk slots past
the end decode to the empty set). -/
lemma restrictedSampledBadCodeStream_getD_canonical
    (𝒜 : DescriptionFamily) (c : Code)
    (gridCode : BitString) (gridSteps Δ T m : ℕ) :
    decodeCoverCodeList ((restrictedSampledBadCodeStream c gridCode
        𝒜.toPre gridSteps Δ T).getD m []) =
      canonicalFinsetList ((decodeCoverCodeList
        ((restrictedSampledBadCodeStream c gridCode 𝒜.toPre gridSteps Δ
          T).getD m [])).toFinset) := by
  classical
  set events := restrictedSampledBadCodeStream c gridCode 𝒜.toPre gridSteps
    Δ T with hevents
  by_cases hm : m < events.length
  · have hmem : events.getD m [] ∈ events := by
      rw [List.getD_eq_getElem _ _ hm]
      exact List.getElem_mem hm
    obtain ⟨s, hs, hmodel⟩ :=
      restrictedSampledBadCodeStream_sound c gridCode 𝒜.toPre gridSteps Δ
        T hmem
    obtain ⟨S, hS, _hmemS, hwEq, _hcard⟩ := hmodel
    rw [hwEq, decodeCoverCodeList_code, canonicalFinsetList_toFinset]
  · rw [List.getD_eq_default _ _ (by omega)]
    have hempty : (([] : List BitString)).toFinset = (∅ : Finset BitString) :=
      rfl
    rw [decodeCoverCodeList_nil, hempty]
    have : canonicalFinsetList (∅ : Finset BitString) = [] := by
      simp [canonicalFinsetList]
    rw [this]

/-- The anchored run, event by event: the decoded per-event states form a run
chain over the stage-`T` stream, starting from the full ambient cube. -/
lemma exists_restrictedAnchoredEventChain
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (ambientLength Δ : ℕ) (grid : RestrictedCurveGrid n k N target)
    (hnambient : n ≤ ambientLength) (T : ℕ) :
    ∃ (chain : RestrictedRunChain 𝒜 (N + 1) ambientLength
        (2 * 𝒜.overhead ambientLength)
        (restrictedAnchoredTarget ambientLength Δ grid)
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N Δ T).length)
      (codes : ℕ → BitString),
      (∀ m,
        (restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ
            grid).bind
          (fun st0 => restrictedEventPrefixRun 𝒜 (𝒜.overhead ambientLength)
            (restrictedEffectiveAnchoredSizes ambientLength Δ grid) st0
            (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
              𝒜.toPre N Δ T) m) = Part.some (codes m) ∧
        DecodesToRestrictedSampledRunState (codes m) (chain.states m)) ∧
      (∀ m, chain.bads m = (decodeCoverCodeList
        ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N Δ T).getD m [])).toFinset) ∧
      (chain.states 0).B 0 = stringsOfLength ambientLength ∧
      (chain.states 0).live 0 = stringsOfLength ambientLength := by
  classical
  set gridCode := restrictedCurveGridCode grid with hgridCode
  set events := restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ T
    with hevents
  set q0 := 𝒜.overhead ambientLength with hq0
  set sizes := restrictedEffectiveAnchoredSizes ambientLength Δ grid
    with hsizesdef
  set tt := restrictedAnchoredTarget ambientLength Δ grid with htt
  have hlen : sizes.length = (N + 1) + 1 := by simp [hsizesdef]
  have hpowers : ∀ s ≤ N + 1, sizes.getD s 0 = 2 ^ tt s := fun s hs =>
    restrictedEffectiveAnchoredSizes_getD ambientLength Δ grid s hs
  have hmono : ∀ s < N + 1, tt (s + 1) ≤ tt s :=
    restrictedAnchoredTarget_mono ambientLength Δ grid hnambient
  have hbadDecode : ∀ m, decodeCoverCodeList (events.getD m []) =
      canonicalFinsetList
        ((decodeCoverCodeList (events.getD m [])).toFinset) := fun m =>
    restrictedSampledBadCodeStream_getD_canonical 𝒜 c gridCode N Δ T m
  have hdata : ∀ m : ℕ, ∃ p : BitString ×
      RestrictedSampledRunState 𝒜 (N + 1) ambientLength
        (2 * 𝒜.overhead ambientLength) tt,
      (restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒜 q0 sizes st0 events m) =
          Part.some p.1 ∧
      DecodesToRestrictedSampledRunState p.1 p.2 ∧
      (m = 0 → p.2.B 0 = stringsOfLength ambientLength ∧
        p.2.live 0 = stringsOfLength ambientLength) := by
    intro m
    induction m with
    | zero =>
        obtain ⟨code0, st0, hrun0, hdec0, hB0, hlive0⟩ :=
          restrictedEffectiveAnchoredInitialState_spec 𝒜 ambientLength Δ
            grid hnambient
        refine ⟨(code0, st0), ?_, hdec0, fun _ => ⟨hB0, hlive0⟩⟩
        simpa [restrictedEventPrefixRun_zero, part_bind_some] using hrun0
    | succ m ih =>
        obtain ⟨⟨cd, st⟩, hfold, hdec, _⟩ := ih
        obtain ⟨output, next, q, hstepEq, hnextDec, _hspec⟩ :=
          restrictedEffectiveSampledRun_step_spec 𝒜 (N + 1) ambientLength
            tt sizes hlen hpowers hmono hdec (hbadDecode m)
        refine ⟨(output, next), ?_, hnextDec,
          fun h => absurd h (Nat.succ_ne_zero m)⟩
        have hsplit : (restrictedEffectiveAnchoredInitialState 𝒜
            ambientLength Δ grid).bind (fun st0 =>
              restrictedEventPrefixRun 𝒜 q0 sizes st0 events (m + 1)) =
            ((restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ
              grid).bind (fun st0 =>
                restrictedEventPrefixRun 𝒜 q0 sizes st0 events m)).bind
              (fun state => restrictedEffectiveSampledRunStep 𝒜 q0 sizes
                state (events.getD m [])) := by
          rw [Part.bind_assoc]
          rfl
        rw [hsplit, hfold, Part.bind_some, hstepEq]
  choose data hd1 hd2 hd3 using hdata
  have hedge : ∀ m : ℕ, ∃ q,
      RestrictedSampledRunStepSpec ((data m).2) ((data (m + 1)).2)
        ((decodeCoverCodeList (events.getD m [])).toFinset) q := by
    intro m
    obtain ⟨output, next, q, hstepEq, hnextDec, hspec⟩ :=
      restrictedEffectiveSampledRun_step_spec 𝒜 (N + 1) ambientLength tt
        sizes hlen hpowers hmono (hd2 m) (hbadDecode m)
    have hsplit : (restrictedEffectiveAnchoredInitialState 𝒜
        ambientLength Δ grid).bind (fun st0 =>
          restrictedEventPrefixRun 𝒜 q0 sizes st0 events (m + 1)) =
        ((restrictedEffectiveAnchoredInitialState 𝒜 ambientLength Δ
          grid).bind (fun st0 =>
            restrictedEventPrefixRun 𝒜 q0 sizes st0 events m)).bind
          (fun state => restrictedEffectiveSampledRunStep 𝒜 q0 sizes
            state (events.getD m [])) := by
      rw [Part.bind_assoc]
      rfl
    have hout : output = (data (m + 1)).1 := by
      have hfold1 := hd1 (m + 1)
      rw [hsplit, hd1 m, Part.bind_some, hstepEq] at hfold1
      exact Part.some_injective hfold1
    refine ⟨q, stepSpec_transfer (fun s hs => ⟨rfl, rfl⟩) ?_ hspec⟩
    intro s hs
    exact decodesTo_eq_B_live (hout ▸ hnextDec) (hd2 (m + 1)) hs
  choose edges hedges using hedge
  exact ⟨⟨fun m => (data m).2,
      fun m => (decodeCoverCodeList (events.getD m [])).toFinset,
      edges, fun m _ => hedges m⟩,
    fun m => (data m).1,
    fun m => ⟨hd1 m, hd2 m⟩, fun m => rfl,
    (hd3 0 rfl).1, (hd3 0 rfl).2⟩

end ChainConstruction

section CountInstantiation

/-- Grid indices are monotone across arbitrary gaps. -/
lemma restrictedCurveGrid_i_mono_le
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    {b a : ℕ} (hba : b ≤ a) (haN : a ≤ N) : grid.i b ≤ grid.i a := by
  induction hba with
  | refl => exact le_rfl
  | @step a' hba ih =>
      exact le_trans (ih (by omega)) (grid.i_mono a' (by omega))

/-- Grid heights are antitone across arbitrary gaps. -/
lemma restrictedCurveGrid_j_anti_le
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    {b a : ℕ} (hba : b ≤ a) (haN : a ≤ N) : grid.j a ≤ grid.j b := by
  induction hba with
  | refl => exact le_rfl
  | @step a' hba ih =>
      exact le_trans (grid.j_mono a' (by omega)) (ih (by omega))

/-- The boundary slope at grid points: the index-plus-height product does not
increase (up to one unit) along the grid. -/
lemma restrictedCurveGrid_slope
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    {b a : ℕ} (hba : b ≤ a) (haN : a ≤ N) :
    grid.i a + grid.j a ≤ grid.i b + grid.j b + 1 := by
  have hbN : b ≤ N := by omega
  have himono := restrictedCurveGrid_i_mono_le grid hba haN
  rcases Nat.eq_or_lt_of_le himono with hEq | hlt
  · have hj := restrictedCurveGrid_j_anti_le grid hba haN
    omega
  · have hpos : 0 < grid.i a := by omega
    have habove := grid.cross_above a haN hpos
    have hbelow := grid.cross_below b hbN
    have hik : grid.i a - 1 ≤ k := by
      have := grid.i_le_k a haN
      omega
    have hdrop := restricted_curve_drop_bound hstrict
      (show grid.i b ≤ grid.i a - 1 by omega) hik
    omega

/-- Exponent comparison for a small-event stage `l` against the target
scale `s`. -/
lemma restrictedCurveGrid_sStage_exponent_le
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hstrict : ∀ i < k, target (i + 1) < target i)
    {s l Δ : ℕ} (hsN : s ≤ N) (hlN : l < N)
    (hgt : grid.i s < grid.i (l + 1)) :
    grid.i (l + 1) + 1 + (grid.j l - (Δ + 1)) ≤
      grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4 := by
  have hsl : s ≤ l := by
    by_contra hcon
    have : l + 1 ≤ s := by omega
    have := restrictedCurveGrid_i_mono_le grid this hsN
    omega
  have hslope1 := restrictedCurveGrid_slope grid hstrict
    (show s + 1 ≤ l + 1 by omega) (show l + 1 ≤ N by omega)
  have hslope2 := restrictedCurveGrid_slope grid hstrict
    (show s ≤ s + 1 by omega) (show s + 1 ≤ N by omega)
  have hstep := grid.j_step_le l hlN
  have hjmono := grid.j_mono l hlN
  have hjls := restrictedCurveGrid_j_anti_le grid hsl (by omega : l ≤ N)
  omega

/-- Half-strength padding: twice the total decoded bad volume still fits
strictly inside the ambient cube. -/
lemma restrictedCurveGrid_bad_volume_padding_half
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    2 * ((List.range N).map fun s =>
        2 ^ (grid.i (s + 1) + 1) *
          2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum <
      2 ^ (n + logSlack 8 n) := by
  have hterm : ∀ s ∈ List.range N,
      2 ^ (grid.i (s + 1) + 1) *
          2 ^ (grid.j s - (sqrtSlack 8 n + 1)) ≤
        2 ^ (n + 1) := by
    intro s hs
    have hslt : s < N := List.mem_range.mp hs
    have hnext := restrictedCurveGrid_next_index_add_height_le grid
      htarget hstrict s hslt
    have hjmono := grid.j_mono s hslt
    have hjstep := grid.j_step_le s hslt
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by omega)
    by_cases hj : grid.j s ≤ sqrtSlack 8 n + 1
    · have hiN : grid.i (s + 1) ≤ n := (grid.i_le_k (s + 1) hslt).trans hkn
      omega
    · have hmesh : n / N + 1 ≤ sqrtSlack 8 n := by
        rw [hN]
        exact restrictedCurveGrid_mesh_le_sqrtSlack n
      omega
  have hsum : ((List.range N).map fun s =>
      2 ^ (grid.i (s + 1) + 1) *
        2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum ≤ N * 2 ^ (n + 1) := by
    calc ((List.range N).map fun s =>
          2 ^ (grid.i (s + 1) + 1) *
            2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum
        ≤ ((List.range N).map fun _s => 2 ^ (n + 1)).sum :=
          List.sum_le_sum hterm
      _ = N * 2 ^ (n + 1) := by simp
  have hNle : N ≤ n + 1 := by
    rw [hN]
    exact Nat.add_le_add_right
      ((Nat.sqrt_le_self (n / (Nat.log2 n + 1))).trans
        (Nat.div_le_self n (Nat.log2 n + 1))) 1
  have hnBits : n + 1 ≤ 2 ^ (Nat.bits n).length := by
    simpa [Nat.size_eq_bits_len] using
      (Nat.succ_le_iff.mpr (Nat.lt_size_self n))
  have hcount : N * 4 < 2 ^ logSlack 8 n := by
    have hcountLe : N * 4 ≤ 2 ^ ((Nat.bits n).length + 2) := by
      calc N * 4 ≤ (n + 1) * 4 := Nat.mul_le_mul_right 4 hNle
        _ ≤ 2 ^ (Nat.bits n).length * 4 := Nat.mul_le_mul_right 4 hnBits
        _ = 2 ^ ((Nat.bits n).length + 2) := by ring
    refine hcountLe.trans_lt (Nat.pow_lt_pow_right (by omega) ?_)
    unfold logSlack
    omega
  calc 2 * ((List.range N).map fun s =>
        2 ^ (grid.i (s + 1) + 1) *
          2 ^ (grid.j s - (sqrtSlack 8 n + 1))).sum
      ≤ 2 * (N * 2 ^ (n + 1)) := Nat.mul_le_mul_left 2 hsum
    _ = (N * 4) * 2 ^ n := by ring
    _ < 2 ^ logSlack 8 n * 2 ^ n :=
        Nat.mul_lt_mul_of_pos_right hcount (pow_pos (by omega) n)
    _ = 2 ^ (n + logSlack 8 n) := by rw [← pow_add]; ring_nf

/-- A deduplicated finite sum is at most the raw list sum. -/
private lemma sum_toFinset_le_list_sum' {α : Type*} [DecidableEq α]
    (values : α → ℕ) : ∀ items : List α,
    ∑ item ∈ items.toFinset, values item ≤ (items.map values).sum := by
  intro items
  induction items with
  | nil => simp
  | cons item items ih =>
      by_cases hitem : item ∈ items
      · have hle : (items.map values).sum ≤
            values item + (items.map values).sum := by omega
        simpa [hitem] using ih.trans hle
      · simpa [hitem] using Nat.add_le_add_left ih (values item)

/-- Two power bounds multiply into a power of the summed exponents. -/
private lemma mul_pow_le_pow_add {a b e f : ℕ} (ha : a ≤ 2 ^ e)
    (hb : b ≤ 2 ^ f) : a * b ≤ 2 ^ (e + f) := by
  calc a * b ≤ 2 ^ e * 2 ^ f := Nat.mul_le_mul ha hb
    _ = 2 ^ (e + f) := (pow_add 2 e f).symm

/-- The arithmetic core of the version-count bound. -/
private lemma version_count_arith {I Δm mesh LN Lob NN OB s : ℕ}
    (hNN : NN + 1 ≤ 2 ^ LN) (hOB : OB ≤ 2 ^ Lob) (hs : s ≤ NN) :
    (s + 1) * (NN * 2 ^ (I + 1) + 1 +
        2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4))) ≤
      2 ^ (I + ((NN + 1) * Lob + 2 * LN + Δm + mesh + 9)) := by
  set E : ℕ := I + (NN + 1) * Lob + LN + Δm + mesh + 5 with hE
  have hNN' : NN ≤ 2 ^ LN := by omega
  have hOBpow : OB ^ (s + 1) ≤ 2 ^ ((NN + 1) * Lob) := by
    calc OB ^ (s + 1) ≤ (2 ^ Lob) ^ (s + 1) := Nat.pow_le_pow_left hOB _
      _ = 2 ^ (Lob * (s + 1)) := by rw [← pow_mul]
      _ ≤ 2 ^ ((NN + 1) * Lob) := by
          apply Nat.pow_le_pow_right (by omega)
          calc Lob * (s + 1) ≤ Lob * (NN + 1) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = (NN + 1) * Lob := Nat.mul_comm _ _
  have h1 : NN * 2 ^ (I + 1) ≤ 2 ^ E := by
    refine le_trans (mul_pow_le_pow_add hNN' le_rfl) ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (1 : ℕ) ≤ 2 ^ E := Nat.one_le_two_pow
  have h3 : 2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4)) ≤ 2 ^ E := by
    have ha : 2 * OB ^ (s + 1) ≤ 2 ^ (1 + (NN + 1) * Lob) :=
      mul_pow_le_pow_add (by omega) hOBpow
    have hb : NN * 2 ^ (I + Δm + mesh + 4) ≤
        2 ^ (LN + (I + Δm + mesh + 4)) :=
      mul_pow_le_pow_add hNN' le_rfl
    refine le_trans (mul_pow_le_pow_add ha hb) ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hbr : NN * 2 ^ (I + 1) + 1 +
      2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4)) ≤ 2 ^ (E + 2) := by
    have h4 : (2:ℕ) ^ (E + 2) = 4 * 2 ^ E := by
      rw [pow_add]
      ring
    omega
  calc (s + 1) * (NN * 2 ^ (I + 1) + 1 +
        2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4)))
      ≤ 2 ^ LN * 2 ^ (E + 2) :=
        Nat.mul_le_mul (by omega) hbr
    _ = 2 ^ (LN + (E + 2)) := (pow_add 2 LN (E + 2)).symm
    _ ≤ 2 ^ (I + ((NN + 1) * Lob + 2 * LN + Δm + mesh + 9)) :=
        Nat.pow_le_pow_right (by omega) (by omega)

/-- A sum over a finite union is at most the corresponding double sum. -/
private lemma sum_biUnion_le' {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℕ) :
    ∑ w ∈ s.biUnion t, f w ≤ ∑ a ∈ s, ∑ w ∈ t a, f w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc ∑ w ∈ t a ∪ s.biUnion t, f w
          ≤ ∑ w ∈ t a, f w + ∑ w ∈ s.biUnion t, f w := by
            have hsub : t a ∪ s.biUnion t ⊆ t a ∪ (s.biUnion t \ t a) := by
              intro x hx
              rcases Finset.mem_union.mp hx with h | h
              · exact Finset.mem_union_left _ h
              · by_cases hxa : x ∈ t a
                · exact Finset.mem_union_left _ hxa
                · exact Finset.mem_union_right _
                    (Finset.mem_sdiff.mpr ⟨h, hxa⟩)
            calc ∑ w ∈ t a ∪ s.biUnion t, f w
                ≤ ∑ w ∈ t a ∪ (s.biUnion t \ t a), f w :=
                  Finset.sum_le_sum_of_subset hsub
              _ = ∑ w ∈ t a, f w + ∑ w ∈ s.biUnion t \ t a, f w :=
                  Finset.sum_union Finset.disjoint_sdiff
              _ ≤ ∑ w ∈ t a, f w + ∑ w ∈ s.biUnion t, f w :=
                  Nat.add_le_add_left
                    (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _
        _ ≤ ∑ w ∈ t a, f w + ∑ a' ∈ s, ∑ w ∈ t a', f w :=
            Nat.add_le_add_left ih _

/-- The version-count exponent: everything the rebuild bound costs beyond the
grid's `i`-coordinate. -/
def anchoredVersionExp (𝒜 : DescriptionFamily) (n N : ℕ) : ℕ :=
  (N + 2) * (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length +
    2 * (Nat.bits (N + 1)).length + sqrtSlack 8 n + (n / N + 1) + 9

/-- The anchored event chain of the specialized run (ambient
`n + logSlack 8 n`, stream slack `sqrtSlack 8 n`) rebuilds each level `s + 1`
at most `2 ^ (grid.i s + anchoredVersionExp 𝒜 n N)` times. -/
theorem exists_restrictedAnchoredEventChain_with_count
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n) (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) (T : ℕ) :
    ∃ (chain : RestrictedRunChain 𝒜 (N + 1) (n + logSlack 8 n)
        (2 * 𝒜.overhead (n + logSlack 8 n))
        (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid)
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length)
      (codes : ℕ → BitString),
      (∀ m,
        (restrictedEffectiveAnchoredInitialState 𝒜 (n + logSlack 8 n)
            (sqrtSlack 8 n) grid).bind
          (fun st0 => restrictedEventPrefixRun 𝒜
            (𝒜.overhead (n + logSlack 8 n))
            (restrictedEffectiveAnchoredSizes (n + logSlack 8 n)
              (sqrtSlack 8 n) grid) st0
            (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
              𝒜.toPre N (sqrtSlack 8 n) T) m) = Part.some (codes m) ∧
        DecodesToRestrictedSampledRunState (codes m) (chain.states m)) ∧
      (∀ m, chain.bads m = (decodeCoverCodeList
        ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).getD m [])).toFinset) ∧
      (chain.states 0).B 0 = stringsOfLength (n + logSlack 8 n) ∧
      (chain.states 0).live 0 = stringsOfLength (n + logSlack 8 n) ∧
      ∀ s ≤ N, (chain.rebuildSteps s).card ≤
        2 ^ (grid.i s + anchoredVersionExp 𝒜 n N) := by
  classical
  set Δ := sqrtSlack 8 n with hΔdef
  set gridCode := restrictedCurveGridCode grid with hgridCodeDef
  set events := restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ T
    with heventsDef
  set M := events.length with hMdef
  set OB := 2 * 𝒜.overhead (n + logSlack 8 n) with hOBdef
  have hnamb : n ≤ n + logSlack 8 n := Nat.le_add_right _ _
  obtain ⟨chain, codes, hfold, hbads, hB0, hlive0⟩ :=
    exists_restrictedAnchoredEventChain 𝒜 c (n + logSlack 8 n) Δ grid
      hnamb T
  refine ⟨chain, codes, hfold, hbads, hB0, hlive0, ?_⟩
  intro s hsN
  -- root floor from the half padding
  have hbadsub : ∀ m : ℕ, m < M → chain.bads m ⊆
      restrictedAnchoredProcessedBadUnion c 𝒜 Δ grid (T + 1) := by
    intro m hm x hx
    rw [hbads m, List.mem_toFinset] at hx
    rw [restrictedAnchoredProcessedBadUnion_eq_codes,
      restrictedAnchoredProcessedBadCodes_succ]
    refine (mem_restrictedDecodedBadCodesUnion_iff _ x).mpr
      ⟨events.getD m [], ?_, List.mem_toFinset.mpr hx⟩
    rw [List.getD_eq_getElem _ _ hm]
    exact List.getElem_mem hm
  have hUcard : 2 * (restrictedAnchoredProcessedBadUnion c 𝒜 Δ grid
      (T + 1)).card < 2 ^ (n + logSlack 8 n) := by
    calc 2 * (restrictedAnchoredProcessedBadUnion c 𝒜 Δ grid (T + 1)).card
        ≤ 2 * ((List.range N).map fun s' =>
            2 ^ (grid.i (s' + 1) + 1) *
              2 ^ (grid.j s' - (Δ + 1))).sum :=
          Nat.mul_le_mul_left 2
            (restrictedAnchoredProcessedBadUnion_card_le c 𝒜 Δ grid T)
      _ < 2 ^ (n + logSlack 8 n) :=
          restrictedCurveGrid_bad_volume_padding_half grid hN hkn htarget
            hstrict
  have hroot : ∀ m ≤ M, 2 ^ (restrictedAnchoredTarget (n + logSlack 8 n) Δ
      grid) 0 ≤ 2 * ((chain.states m).live 0).card := by
    intro m hm
    have hwin := chain.window_live_eq (Nat.zero_le m) hm
      (fun m' _ _ => Nat.zero_le _)
    rw [hwin, hlive0]
    have hsub : (Finset.Ico 0 m).biUnion chain.bads ⊆
        restrictedAnchoredProcessedBadUnion c 𝒜 Δ grid (T + 1) := by
      intro x hx
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
      rw [Finset.mem_Ico] at ha
      exact hbadsub a (by omega) hxa
    have hcardsub := Finset.card_le_card hsub
    have hcube : (stringsOfLength (n + logSlack 8 n)).card =
        2 ^ (n + logSlack 8 n) := cardStringsOfLength _
    have hsdiff := Finset.card_le_card_sdiff_add_card
      (s := stringsOfLength (n + logSlack 8 n))
      (t := (Finset.Ico 0 m).biUnion chain.bads)
    rw [restrictedAnchoredTarget_zero]
    omega
  have hmono : ∀ r < N + 1,
      restrictedAnchoredTarget (n + logSlack 8 n) Δ grid (r + 1) ≤
        restrictedAnchoredTarget (n + logSlack 8 n) Δ grid r :=
    restrictedAnchoredTarget_mono _ _ grid hnamb
  have hOB1 : 1 ≤ OB := by
    have := 𝒜.overhead_pos (n + logSlack 8 n)
    omega
  -- injectivity of the event lookup
  have hnodup : events.Nodup :=
    restrictedSampledBadCodeStream_nodup c gridCode 𝒜.toPre N Δ T
  have hgetD_inj : ∀ {a a' : ℕ}, a < M → a' < M →
      events.getD a [] = events.getD a' [] → a = a' := by
    intro a a' ha ha' hEq
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha'] at hEq
    have hinj := List.nodup_iff_injective_get.mp hnodup
    have h2 := hinj (show events.get ⟨a, ha⟩ = events.get ⟨a', ha'⟩ by
      simpa using hEq)
    simpa using h2
  set isL : ℕ → Bool := fun m => decide (∃ l, l < N ∧
    grid.i (l + 1) ≤ grid.i s ∧ events.getD m [] ∈
      familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
        (grid.j l - (Δ + 1)) T) with hisL
  -- L-events are few
  have hLcard : ((Finset.range M).filter fun a => isL a = true).card ≤
      N * 2 ^ (grid.i s + 1) := by
    have hmapsTo : ∀ a ∈ (Finset.range M).filter (fun a => isL a = true),
        events.getD a [] ∈ (((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
            (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset)) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      have hprop : ∃ l, l < N ∧ grid.i (l + 1) ≤ grid.i s ∧
          events.getD a [] ∈ familyStageModelCodesList c (grid.i (l + 1))
            𝒜.toPre (grid.j l - (Δ + 1)) T := of_decide_eq_true ha.2
      obtain ⟨l, hlN, hle, hmem⟩ := hprop
      refine Finset.mem_biUnion.mpr ⟨l, ?_, List.mem_toFinset.mpr hmem⟩
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨List.mem_range.mpr hlN, by simpa using hle⟩
    have hinj : Set.InjOn (fun a => events.getD a [])
        ↑((Finset.range M).filter fun a => isL a = true) := by
      intro a ha a' ha' hEq
      have ha1 : a ∈ (Finset.range M).filter fun a => isL a = true := ha
      have ha2 : a' ∈ (Finset.range M).filter fun a => isL a = true := ha'
      rw [Finset.mem_filter, Finset.mem_range] at ha1 ha2
      exact hgetD_inj ha1.1 ha2.1 hEq
    calc ((Finset.range M).filter fun a => isL a = true).card
        ≤ (((List.range N).filter (fun l =>
            grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
              (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                (grid.j l - (Δ + 1)) T).toFinset)).card :=
          Finset.card_le_card_of_injOn _ hmapsTo hinj
      _ ≤ ∑ l ∈ ((List.range N).filter (fun l =>
            grid.i (l + 1) ≤ grid.i s)).toFinset,
            (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _l ∈ ((List.range N).filter (fun l =>
            grid.i (l + 1) ≤ grid.i s)).toFinset, 2 ^ (grid.i s + 1) := by
          apply Finset.sum_le_sum
          intro l hl
          rw [List.mem_toFinset, List.mem_filter] at hl
          have hle : grid.i (l + 1) ≤ grid.i s := by
            have := hl.2
            simpa using this
          calc (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                (grid.j l - (Δ + 1)) T).toFinset.card
              ≤ (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                  (grid.j l - (Δ + 1)) T).length := List.toFinset_card_le _
            _ ≤ 2 ^ (grid.i (l + 1) + 1) :=
                familyStageModelCodesList_length_le c _ 𝒜.toPre _ T
            _ ≤ 2 ^ (grid.i s + 1) :=
                Nat.pow_le_pow_right (by omega) (by omega)
      _ = (((List.range N).filter (fun l =>
            grid.i (l + 1) ≤ grid.i s)).toFinset).card *
            2 ^ (grid.i s + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ N * 2 ^ (grid.i s + 1) := by
          apply Nat.mul_le_mul_right
          calc (((List.range N).filter (fun l =>
                grid.i (l + 1) ≤ grid.i s)).toFinset).card
              ≤ ((List.range N).filter (fun l =>
                  grid.i (l + 1) ≤ grid.i s)).length :=
                List.toFinset_card_le _
            _ ≤ (List.range N).length := List.length_filter_le _ _
            _ = N := List.length_range
  -- S-events have controlled volume
  have hSsum : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
      (chain.bads a).card ≤
      N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
    have hinj2 : Set.InjOn (fun a => events.getD a [])
        ↑((Finset.range M).filter (fun a => isL a = false)) := by
      intro a ha a' ha' hEq
      have ha1 : a ∈ (Finset.range M).filter (fun a => isL a = false) := ha
      have ha2 : a' ∈ (Finset.range M).filter (fun a => isL a = false) :=
        ha'
      rw [Finset.mem_filter, Finset.mem_range] at ha1 ha2
      exact hgetD_inj ha1.1 ha2.1 hEq
    have hstep1 : ∑ a ∈ (Finset.range M).filter (fun a => isL a = false),
        (chain.bads a).card =
        ∑ w ∈ ((Finset.range M).filter (fun a => isL a = false)).image
          (fun a => events.getD a []),
          (decodeCoverCodeList w).toFinset.card := by
      rw [Finset.sum_image hinj2]
      exact Finset.sum_congr rfl (fun a _ => by rw [hbads a])
    rw [hstep1]
    have himg : ((Finset.range M).filter (fun a => isL a = false)).image
        (fun a => events.getD a []) ⊆
        (((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
            (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset)) := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [Finset.mem_filter, Finset.mem_range] at ha
      obtain ⟨haM, hnotL⟩ := ha
      have hmem : events.getD a [] ∈ events := by
        rw [List.getD_eq_getElem _ _ haM]
        exact List.getElem_mem haM
      have hraw := restrictedSampledBadCodeStream_mem_raw c gridCode
        𝒜.toPre N Δ T hmem
      rw [restrictedSampledBadCodesRaw, List.mem_flatMap] at hraw
      obtain ⟨l, hlrange, hlmem⟩ := hraw
      have hlN : l < N := List.mem_range.mp hlrange
      rw [decode_restrictedCurveGridCode_sample_eq grid
          (show l + 1 ≤ N by omega),
        decode_restrictedCurveGridCode_sample_eq grid
          (show l ≤ N by omega)] at hlmem
      have hgt : ¬ grid.i (l + 1) ≤ grid.i s := by
        intro hle
        have htrue : isL a = true :=
          decide_eq_true ⟨l, hlN, hle, hlmem⟩
        rw [hnotL] at htrue
        exact absurd htrue (by decide)
      refine Finset.mem_biUnion.mpr ⟨l, ?_, List.mem_toFinset.mpr hlmem⟩
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨List.mem_range.mpr hlN, by simpa using hgt⟩
    calc ∑ w ∈ ((Finset.range M).filter
          (fun a => isL a = false)).image (fun a => events.getD a []),
          (decodeCoverCodeList w).toFinset.card
        ≤ ∑ w ∈ (((List.range N).filter (fun l =>
            ¬ grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
              (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                (grid.j l - (Δ + 1)) T).toFinset)),
            (decodeCoverCodeList w).toFinset.card :=
          Finset.sum_le_sum_of_subset himg
      _ ≤ ∑ l ∈ ((List.range N).filter (fun l =>
            ¬ grid.i (l + 1) ≤ grid.i s)).toFinset,
            ∑ w ∈ (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset,
              (decodeCoverCodeList w).toFinset.card :=
          sum_biUnion_le' _ _ _
      _ ≤ ∑ _l ∈ ((List.range N).filter (fun l =>
            ¬ grid.i (l + 1) ≤ grid.i s)).toFinset,
            2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
          apply Finset.sum_le_sum
          intro l hl
          rw [List.mem_toFinset, List.mem_filter] at hl
          have hlN : l < N := List.mem_range.mp hl.1
          have hgt : grid.i s < grid.i (l + 1) := by
            have := hl.2
            simp at this
            omega
          calc ∑ w ∈ (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                (grid.j l - (Δ + 1)) T).toFinset,
                (decodeCoverCodeList w).toFinset.card
              ≤ ((familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                  (grid.j l - (Δ + 1)) T).map fun w =>
                    (decodeCoverCodeList w).toFinset.card).sum :=
                sum_toFinset_le_list_sum' _ _
            _ ≤ 2 ^ (grid.i (l + 1) + 1) * 2 ^ (grid.j l - (Δ + 1)) :=
                familyStageModelCodesList_decoded_volume_le c _ 𝒜.toPre _ T
            _ = 2 ^ (grid.i (l + 1) + 1 + (grid.j l - (Δ + 1))) :=
                (pow_add 2 _ _).symm
            _ ≤ 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
                  (n / N + 1) + 4) :=
                Nat.pow_le_pow_right (by omega)
                  (restrictedCurveGrid_sStage_exponent_le grid hstrict hsN
                    hlN hgt)
      _ = (((List.range N).filter (fun l =>
            ¬ grid.i (l + 1) ≤ grid.i s)).toFinset).card *
            2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
            (n / N + 1) + 4) := by
          apply Nat.mul_le_mul_right
          calc (((List.range N).filter (fun l =>
                ¬ grid.i (l + 1) ≤ grid.i s)).toFinset).card
              ≤ ((List.range N).filter (fun l =>
                  ¬ grid.i (l + 1) ≤ grid.i s)).length :=
                List.toFinset_card_le _
            _ ≤ (List.range N).length := List.length_filter_le _ _
            _ = N := List.length_range
  -- abstract bound and arithmetic collapse
  have hmain := chain.rebuildSteps_card_mul_le hroot hmono hOB1
    (show s < N + 1 by omega) isL hLcard hSsum
  rw [restrictedAnchoredTarget_succ] at hmain
  have hVSsplit : N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
      (n / N + 1) + 4) =
      N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4) *
        2 ^ (grid.j s - (Δ + 1)) := by
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hVSsplit] at hmain
  have hfact : (s + 1) * ((N * 2 ^ (grid.i s + 1) + 1) *
      2 ^ (grid.j s - (Δ + 1)) +
      2 * OB ^ (s + 1) *
        (N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4) *
          2 ^ (grid.j s - (Δ + 1)))) =
      ((s + 1) * (N * 2 ^ (grid.i s + 1) + 1 +
        2 * OB ^ (s + 1) *
          (N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4)))) *
        2 ^ (grid.j s - (Δ + 1)) := by
    ring
  rw [hfact] at hmain
  have hcount := Nat.le_of_mul_le_mul_right hmain (pow_pos (by omega) _)
  have hNN : N + 1 ≤ 2 ^ (Nat.bits (N + 1)).length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self (N + 1)).le
  have hOBsize : OB ≤ 2 ^ (Nat.bits OB).length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self OB).le
  have harith := version_count_arith (I := grid.i s) (Δm := Δ)
    (mesh := n / N + 1) (LN := (Nat.bits (N + 1)).length)
    (Lob := (Nat.bits OB).length) (NN := N) (OB := OB) (s := s)
    hNN hOBsize hsN
  refine hcount.trans (harith.trans (Nat.pow_le_pow_right (by omega) ?_))
  have hexp : anchoredVersionExp 𝒜 n N =
      (N + 2) * (Nat.bits OB).length +
        2 * (Nat.bits (N + 1)).length + Δ + (n / N + 1) + 9 := rfl
  rw [hexp]
  have hmul : (N + 1) * (Nat.bits OB).length ≤
      (N + 2) * (Nat.bits OB).length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- For a polynomial-overhead family the version-count exponent is a genuine
square-root slack. -/
lemma anchoredVersionExp_le_sqrtSlack
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_P : ℕ, ∀ n N : ℕ, N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      anchoredVersionExp 𝒜 n N ≤ sqrtSlack c_P n := by
  obtain ⟨c_over, hover⟩ := 𝒜.overhead_bits_le_logSlack hPoly
  refine ⟨5 * (5 * c_over + 2) + 40, ?_⟩
  intro n N hN
  set L := (Nat.bits n).length with hL
  set S := Nat.sqrt (n * L) with hS
  set q := Nat.sqrt (n / (Nat.log2 n + 1)) with hq
  set C₁ := 5 * c_over + 2 with hC₁
  -- the ambient length has at most `L + 4` bits
  have hLsize : L = Nat.size n := Nat.size_eq_bits_len n
  have hn2 : n < 2 ^ L := by
    rw [hLsize]
    exact Nat.lt_size_self n
  have hLpow : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  have hambBits : (Nat.bits (n + logSlack 8 n)).length ≤ L + 4 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hlog : logSlack 8 n = 8 * L + 8 := by
      unfold logSlack
      rfl
    have hpow4 : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by
      rw [pow_add]
      ring
    omega
  -- the overhead bound in bits
  have hOBbits : (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
      C₁ * (L + 1) := by
    have hovpos := 𝒜.overhead_pos (n + logSlack 8 n)
    have hsz : (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
        (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length + 1 := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      apply Nat.size_le.mpr
      have := Nat.lt_size_self (𝒜.overhead (n + logSlack 8 n))
      calc 2 * 𝒜.overhead (n + logSlack 8 n)
          < 2 * 2 ^ Nat.size (𝒜.overhead (n + logSlack 8 n)) := by omega
        _ = 2 ^ (Nat.size (𝒜.overhead (n + logSlack 8 n)) + 1) := by
            rw [pow_succ]
            ring
    have hlogS : logSlack c_over (n + logSlack 8 n) ≤
        c_over * (L + 4) + c_over := by
      unfold logSlack
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left c_over hambBits) c_over
    have hov := hover (n + logSlack 8 n)
    have hexpand : c_over * (L + 4) + c_over + 1 ≤ C₁ * (L + 1) := by
      rw [hC₁]
      nlinarith
    calc (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length
        ≤ (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length + 1 := hsz
      _ ≤ logSlack c_over (n + logSlack 8 n) + 1 :=
          Nat.add_le_add_right hov 1
      _ ≤ c_over * (L + 4) + c_over + 1 := Nat.add_le_add_right hlogS 1
      _ ≤ C₁ * (L + 1) := hexpand
  -- N + 1 has at most L + 2 bits
  have hNle : N ≤ n + 1 := by
    rw [hN]
    exact Nat.add_le_add_right
      ((Nat.sqrt_le_self (n / (Nat.log2 n + 1))).trans
        (Nat.div_le_self n (Nat.log2 n + 1))) 1
  have hN1bits : (Nat.bits (N + 1)).length ≤ L + 2 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hpow2 : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by
      rw [pow_add]
      ring
    omega
  -- square-root balances
  have hqL : q * L ≤ S := by
    apply Nat.le_sqrt.mpr
    have hq2 : q * q ≤ n / (Nat.log2 n + 1) := by
      simpa [pow_two] using Nat.sqrt_le' (n / (Nat.log2 n + 1))
    have hLb : L ≤ Nat.log2 n + 1 := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp [hL]
      · have : (Nat.bits n).length = Nat.log2 n + 1 := by
          rw [Nat.size_eq_bits_len, Nat.le_antisymm_iff]
          constructor
          · rw [Nat.size_le]
            exact Nat.lt_log2_self
          · rw [Nat.add_one_le_iff, Nat.log2_lt (by omega)]
            exact Nat.lt_size_self n
        omega
    have hdivL : n / (Nat.log2 n + 1) * L ≤ n := by
      calc n / (Nat.log2 n + 1) * L
          ≤ n / (Nat.log2 n + 1) * (Nat.log2 n + 1) :=
            Nat.mul_le_mul_left _ hLb
        _ ≤ n := Nat.div_mul_le_self n _
    calc q * L * (q * L) = q * q * (L * L) := by ring
      _ ≤ n / (Nat.log2 n + 1) * (L * L) := Nat.mul_le_mul_right _ hq2
      _ = n / (Nat.log2 n + 1) * L * L := by ring
      _ ≤ n * L := Nat.mul_le_mul_right _ hdivL
  have hnL : n ≤ n * L := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · simp [hn0]
    · have hLpos : 0 < L := by
        rw [hLsize]
        exact Nat.size_pos.mpr hnpos
      exact Nat.le_mul_of_pos_right n hLpos
  have hq_le : q ≤ S := by
    apply Nat.le_sqrt.mpr
    have hq2 : q * q ≤ n / (Nat.log2 n + 1) := by
      simpa [pow_two] using Nat.sqrt_le' (n / (Nat.log2 n + 1))
    calc q * q ≤ n / (Nat.log2 n + 1) := hq2
      _ ≤ n := Nat.div_le_self _ _
      _ ≤ n * L := hnL
  have hL_le : L ≤ S := by
    apply Nat.le_sqrt.mpr
    have hLn : L ≤ n := by
      rw [hLsize]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    exact Nat.mul_le_mul_right _ hLn
  -- mesh
  have hmesh : n / N + 1 ≤ sqrtSlack 8 n := by
    rw [hN]
    exact restrictedCurveGrid_mesh_le_sqrtSlack n
  -- assemble
  have hNq : N + 2 = q + 3 := by
    rw [hN]
  have hOBterm : (N + 2) *
      (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
      C₁ * (5 * S + 3) := by
    calc (N + 2) * (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length
        ≤ (N + 2) * (C₁ * (L + 1)) := Nat.mul_le_mul_left _ hOBbits
      _ = C₁ * ((q + 3) * (L + 1)) := by
          rw [hNq]
          ring
      _ = C₁ * (q * L + q + 3 * L + 3) := by ring
      _ ≤ C₁ * (S + S + 3 * S + 3) := by
          apply Nat.mul_le_mul_left
          have h3L : 3 * L ≤ 3 * S := Nat.mul_le_mul_left 3 hL_le
          omega
      _ = C₁ * (5 * S + 3) := by ring
  have hsq8 : sqrtSlack 8 n = 8 * S + 8 := by
    unfold sqrtSlack
    rw [hS]
  unfold anchoredVersionExp
  set X := C₁ * (S + 1) with hX
  have hOBterm' : (N + 2) *
      (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤ 5 * X := by
    refine hOBterm.trans ?_
    rw [hX]
    calc C₁ * (5 * S + 3) ≤ C₁ * (5 * S + 5) := by
          apply Nat.mul_le_mul_left
          omega
      _ = 5 * (C₁ * (S + 1)) := by ring
  have htarget : sqrtSlack (5 * C₁ + 40) n = (5 * C₁ + 40) * S +
      (5 * C₁ + 40) := by
    unfold sqrtSlack
    rw [hS]
  rw [htarget]
  have hexp : (5 * C₁ + 40) * S + (5 * C₁ + 40) = 5 * X + 40 * S + 40 := by
    rw [hX]
    ring
  rw [hexp]
  have hN1 : 2 * (Nat.bits (N + 1)).length ≤ 2 * S + 4 := by
    have := hN1bits
    have h2 : 2 * (Nat.bits (N + 1)).length ≤ 2 * (L + 2) :=
      Nat.mul_le_mul_left 2 hN1bits
    have h3 : 2 * L ≤ 2 * S := Nat.mul_le_mul_left 2 hL_le
    omega
  omega

end CountInstantiation

end Kolmogorov
