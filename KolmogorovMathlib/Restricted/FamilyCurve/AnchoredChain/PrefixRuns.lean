import KolmogorovMathlib.Restricted.FamilyCurve.RunChain
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun
import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds

/-!
# Running an anchored chain event by event

`restrictedEventPrefixRun` processes the first `m` events of a sampled run, so that the batch
processor is its limit (`restrictedEffectiveSampledRunProcess_eq_prefixRun`); it satisfies the
expected recursion (`restrictedEventPrefixRun_zero`, `restrictedEventPrefixRun_succ`) and only
reads events below the prefix bound (`restrictedEventPrefixRun_congr`), which is what lets the
chain be analysed one event at a time. The remaining material prepares the version count: the
stage exponent comparison `restrictedCurveGrid_sStage_exponent_le`, the padding estimate
`restrictedCurveGrid_bad_volume_padding_half`, and the definition `anchoredVersionExp` of the
exponent that the rebuild bound costs beyond the grid coordinate.
-/



namespace Kolmogorov

open Nat.Partrec (Code)

/-- Binding a part into `Part.some` is the identity. -/
lemma part_bind_some {α : Type} (p : Part α) :
    p.bind Part.some = p := by
  exact Part.bind_some_right p

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

/-- A prefix run of length zero returns the state it started from. -/
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

/-- The empty string decodes to the empty list of points. -/
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

/-- The version-count exponent: everything the rebuild bound costs beyond the
grid's `i`-coordinate. -/
def anchoredVersionExp (𝒜 : DescriptionFamily) (n N : ℕ) : ℕ :=
  (N + 2) * (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length +
    2 * (Nat.bits (N + 1)).length + sqrtSlack 8 n + (n / N + 1) + 9

end CountInstantiation
end Kolmogorov
