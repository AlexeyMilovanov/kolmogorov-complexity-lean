import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1EffectiveRunCharging
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1VersionDecoder
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1RunBounds

namespace Kolmogorov

def T1RunVersionsModelInvariant
    (n k epsilon : Nat) (s : T1RunState) : Prop :=
  ∀ L ∈ s.versions,
    L.Nodup ∧
    L.length = 2 ^ (k - epsilon) ∧
    L.toFinset ⊆ stringsOfLength n

theorem t1InitialRunState_versions_model
    {n k epsilon : Nat}
    (hepsilon : epsilon ≤ k) (hkn : k ≤ n) :
    T1RunVersionsModelInvariant n k epsilon
      (t1InitialRunState n k epsilon) := by
  intro L hL
  simp only [t1InitialRunState, List.mem_singleton] at hL
  subst L
  exact ⟨t1InitialCurrent_nodup n k epsilon,
    t1InitialCurrent_length hepsilon hkn,
    t1InitialCurrent_subset_stringsOfLength n k epsilon⟩

theorem t1RunStep_preserves_versions_model
    {cSparse n k epsilon quota : Nat} {s : T1RunState} {event : T1MarkEvent}
    (hversions : T1RunVersionsModelInvariant n k epsilon s)
    (hcurrent :
      let s' := t1RunStep cSparse n k epsilon quota s event
      s'.current.Nodup ∧
      s'.current.length = 2 ^ (k - epsilon) ∧
      s'.current.toFinset ⊆ stringsOfLength n) :
    T1RunVersionsModelInvariant n k epsilon
      (t1RunStep cSparse n k epsilon quota s event) := by
  let s' := t1RunStep cSparse n k epsilon quota s event
  have hcurrent' :
      s'.current.Nodup ∧
      s'.current.length = 2 ^ (k - epsilon) ∧
      s'.current.toFinset ⊆ stringsOfLength n := by
    simpa [s'] using hcurrent
  rcases t1RunStep_versions cSparse n k epsilon quota s event with
    hsame | hrebuild
  · change ∀ L, L ∈ s'.versions →
      L.Nodup ∧ L.length = 2 ^ (k - epsilon) ∧
        L.toFinset ⊆ stringsOfLength n
    rw [show s'.versions = s.versions by simpa [s'] using hsame.2]
    exact hversions
  · change ∀ L, L ∈ s'.versions →
      L.Nodup ∧ L.length = 2 ^ (k - epsilon) ∧
        L.toFinset ⊆ stringsOfLength n
    rw [show s'.versions = s.versions ++ [s'.current] by
      simpa [s'] using hrebuild.2]
    intro L hL
    rcases List.mem_append.mp hL with hold | hnew
    · exact hversions L hold
    · have hLcurrent : L = s'.current := by
        simpa only [List.mem_singleton] using hnew
      subst L
      exact hcurrent'

theorem t1RunFromEvents_versions_model_of_prefix_model
    {cSparse n k epsilon quota : Nat} {events : List T1MarkEvent}
    (hprefixModel :
      ∀ pref, pref <+: events →
        T1RunModelInvariant cSparse n k epsilon quota
          (t1RunFromEvents cSparse n k epsilon quota
            (t1InitialRunState n k epsilon) pref)) :
    T1RunVersionsModelInvariant n k epsilon
      (t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon) events) := by
  induction events using List.reverseRecOn with
  | nil =>
      have hmodel := hprefixModel [] (List.prefix_refl [])
      intro L hL
      change L ∈ [t1InitialCurrent n k epsilon] at hL
      simp only [List.mem_singleton] at hL
      subst L
      exact ⟨hmodel.1, hmodel.2.1, hmodel.2.2.1⟩
  | append_singleton events event ih =>
      have hprefixOld :
          ∀ pref, pref <+: events →
            T1RunModelInvariant cSparse n k epsilon quota
              (t1RunFromEvents cSparse n k epsilon quota
                (t1InitialRunState n k epsilon) pref) := by
        intro pref hpref
        exact hprefixModel pref
          (hpref.trans (List.prefix_append events [event]))
      have hversions := ih hprefixOld
      rw [t1RunFromEvents_append]
      apply t1RunStep_preserves_versions_model hversions
      have hmodel :=
        hprefixModel (events ++ [event]) (List.prefix_refl _)
      rw [t1RunFromEvents_append] at hmodel
      exact ⟨hmodel.1, hmodel.2.1, hmodel.2.2.1⟩

theorem t1RunFromEvents_versions_model_spec
    (V : Map) (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon quota t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      quota = 2 ^ (k - epsilon) →
      let events := t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t
      T1RunCoreInvariant cSparse n k epsilon quota events
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events) ∧
      T1RunVersionsModelInvariant n k epsilon
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t1RunFromEvents_core_spec V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon quota t hc0 hepsilon hkn hquota
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  have hfull :=
    hcore n k epsilon quota t events hc0 hepsilon hkn hquota
      (List.prefix_refl events)
  refine ⟨hfull, ?_⟩
  apply t1RunFromEvents_versions_model_of_prefix_model
  intro pref hpref
  exact (hcore n k epsilon quota t pref hc0 hepsilon hkn hquota
    (hpref.trans (List.prefix_refl events))).1

theorem t1RunAt_totalC_le_of_model_spec
    {cSparse n k epsilon quota : Nat} {events : List T1MarkEvent}
    (hprefixModel : ∀ pref, pref <+: events →
      T1RunModelInvariant cSparse n k epsilon quota
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) pref)) :
    (t1RunFromEvents cSparse n k epsilon quota
      (t1InitialRunState n k epsilon) events).totalC ≤
        (events.filter t1RunCPrimeEvent).length *
          (cSparse * n + cSparse) := by
  induction events using List.reverseRecOn with
  | nil =>
      simp [t1RunFromEvents, t1InitialRunState]
  | append_singleton events event ih =>
      have hprefixOld :
          ∀ pref, pref <+: events →
            T1RunModelInvariant cSparse n k epsilon quota
              (t1RunFromEvents cSparse n k epsilon quota
                (t1InitialRunState n k epsilon) pref) := by
        intro pref hpref
        exact hprefixModel pref
          (hpref.trans (List.prefix_append events [event]))
      have hstate :=
        hprefixModel events (List.prefix_append events [event])
      have hstep :=
        t1RunStep_totalC_le cSparse n k epsilon quota
          (t1RunFromEvents cSparse n k epsilon quota
            (t1InitialRunState n k epsilon) events)
          event hstate
      have ih' := ih hprefixOld
      rw [t1RunFromEvents_append]
      cases event with
      | bSet w =>
          simpa [t1RunCPrimeEvent] using hstep.trans ih'
      | cDoublePrimeBatch batch =>
          simpa [t1RunCPrimeEvent] using hstep.trans ih'
      | cPrimeModel w =>
          simp only [List.filter_append, List.filter_singleton,
            t1RunCPrimeEvent, List.length_append]
          calc
            (t1RunStep cSparse n k epsilon quota
                (t1RunFromEvents cSparse n k epsilon quota
                  (t1InitialRunState n k epsilon) events)
                (.cPrimeModel w)).totalC
                ≤ (t1RunFromEvents cSparse n k epsilon quota
                    (t1InitialRunState n k epsilon) events).totalC +
                      (cSparse * n + cSparse) := hstep
            _ ≤ (events.filter t1RunCPrimeEvent).length *
                  (cSparse * n + cSparse) +
                    (cSparse * n + cSparse) :=
              Nat.add_le_add_right ih' _
            _ = ((events.filter t1RunCPrimeEvent).length + 1) *
                  (cSparse * n + cSparse) := by ring
      | dString x =>
          simpa [t1RunCPrimeEvent] using hstep.trans ih'

/-- The fixed-width version ordinal bound derived from explicit charging and
rebuild-count arithmetic for one already-chosen selector. -/
theorem t1RunAt_version_lt_width_of_model_spec
    (c : Nat.Partrec.Code) (cDesc cSparse : Nat) :
    ∃ cWidth, ∀ n k epsilon t version,
      (∀ events,
        events <+: t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t →
        T1RunModelInvariant cSparse n k epsilon
          (2 ^ (k - epsilon))
          (t1RunFromEvents cSparse n k epsilon
            (2 ^ (k - epsilon))
            (t1InitialRunState n k epsilon) events)) →
      epsilon ≤ k →
      k + 4 ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.length →
      version < 2 ^ (epsilon + logSlack cWidth n) := by
  obtain ⟨cWidth, hcount⟩ :=
    t1_change_count_arith cDesc cSparse
  refine ⟨cWidth, ?_⟩
  intro n k epsilon t version hmodel hepsilon hkn hversion
  let quota := 2 ^ (k - epsilon)
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  have hCraw :
      (t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon) events).totalC ≤
          (events.filter t1RunCPrimeEvent).length *
            (cSparse * n + cSparse) := by
    apply t1RunAt_totalC_le_of_model_spec
    intro pref hpref
    exact hmodel pref (by simpa [events, quota] using hpref)
  have hcountC :
      (events.filter t1RunCPrimeEvent).length ≤ 2 ^ (k + 1) := by
    exact (t1MarkingEventStage_cPrime_count_le c n k epsilon
      (epsilon + logSlack cDesc n) t).trans
        (t1CPrimeStage_length_lt c k t).le
  have hC :
      s.totalC ≤ 2 ^ (k + 1) * (cSparse * n + cSparse) := by
    have hraw := hCraw.trans
      (Nat.mul_le_mul_right (cSparse * n + cSparse) hcountC)
    simpa [s, t1RunAt, events, quota] using hraw
  have hrebuild :
      s.external + s.saturation <
        2 ^ (epsilon + logSlack cWidth n) := by
    apply hcount n k epsilon s.external s.saturation
      s.totalC s.totalD hepsilon hkn
    · exact t1RunAt_external_rebuilds_le
        c cDesc cSparse n k epsilon t
    · exact hC
    · exact t1RunAt_totalD_le
        c cDesc cSparse n k epsilon t
    · exact t1RunAt_saturation_charge
        c cDesc cSparse n k epsilon t
  have hlength :
      s.versions.length = s.external + s.saturation + 1 := by
    simpa [s, quota] using
      t1RunAt_versions_length c cDesc cSparse n k epsilon quota t
  have hversion' : version < s.versions.length := by
    simpa [s, quota] using hversion
  omega

theorem t1RunVersion_nonempty
    {L : List BitString} {k epsilon : Nat}
    (hlength : L.length = 2 ^ (k - epsilon)) :
    L.toFinset.Nonempty := by
  have hL : L ≠ [] := by
    intro h
    subst L
    have hpos : 0 < 2 ^ (k - epsilon) := pow_pos (by decide) _
    simp only [List.length_nil] at hlength
    omega
  simpa using hL

/-- Decoder evaluation bounds the ordinary plain complexity of the decoded
canonical finite-set code. -/
theorem plainSetComplexity_of_t1VersionDecoder_eval
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code) (cDesc cSparse : Nat) :
    ∃ cDecoder : Nat, ∀ p L (hL : L.toFinset.Nonempty),
      canonicalImageCodeOfList L ∈
        t1VersionDecoder c cDesc cSparse p →
      plainSetComplexity V L.toFinset hL ≤
        (p.length + cDecoder : ENat) := by
  obtain ⟨cMap, hMap⟩ :=
    plainK_partrec_map_le V hV
      (t1VersionDecoder c cDesc cSparse)
      (t1VersionDecoder_partrec c cDesc cSparse)
  obtain ⟨cLiteral, hLiteral⟩ := plainKLeLength V hV
  refine ⟨cLiteral + cMap, ?_⟩
  intro p L hL hEval
  unfold plainSetComplexity
  rw [← canonicalImageCodeOfList_eq_codedUniformOn L hL]
  calc
    plainK V (canonicalImageCodeOfList L)
        ≤ plainK V p + (cMap : ENat) :=
      hMap p (canonicalImageCodeOfList L) hEval
    _ ≤ ((p.length : ENat) + (cLiteral : ENat)) +
          (cMap : ENat) := by
      gcongr
      exact hLiteral p
    _ = (p.length + (cLiteral + cMap) : Nat) := by
      push_cast
      ac_rfl

theorem plainSetComplexity_t1RunVersion_le
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code) (cDesc cSparse cWidth : Nat) :
    ∃ cComplexity, ∀ n k epsilon t version,
      epsilon ≤ k →
      k + 4 ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.length →
      version < 2 ^ (epsilon + logSlack cWidth n) →
      let L :=
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.getD version []
      ∀ (hL : L.toFinset.Nonempty),
        plainSetComplexity V L.toFinset hL ≤
          (epsilon + logSlack cComplexity n : ENat) := by
  obtain ⟨cDecoder, hDecoder⟩ :=
    plainSetComplexity_of_t1VersionDecoder_eval
      V hV c cDesc cSparse
  refine ⟨cWidth + 20 + cDecoder, ?_⟩
  intro n k epsilon t version hepsilon hkn hseen hwidth
  dsimp only
  intro hL
  have hEval :=
    t1VersionDecoder_eval c cDesc cSparse cWidth
      n k epsilon t version hseen hwidth
  have hPlain :=
    hDecoder
      (t1VersionProgram cWidth n k epsilon version)
      ((t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon)) t).versions.getD version [])
      hL hEval
  have hProgram :=
    t1VersionProgram_length_le cWidth n k epsilon version
      (by omega) (by omega) hwidth
  calc
    plainSetComplexity V
        ((t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.getD version []).toFinset hL
        ≤ (((t1VersionProgram cWidth n k epsilon version).length +
            cDecoder : Nat) : ENat) := by
      simpa only [Nat.cast_add] using hPlain
    _ ≤ ((epsilon + logSlack (cWidth + 20) n + cDecoder :
          Nat) : ENat) := by
      exact_mod_cast Nat.add_le_add_right hProgram cDecoder
    _ ≤ ((epsilon + logSlack (cWidth + 20 + cDecoder) n :
          Nat) : ENat) := by
      exact_mod_cast (show
        epsilon + logSlack (cWidth + 20) n + cDecoder ≤
          epsilon + logSlack (cWidth + 20 + cDecoder) n by
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits n).length)])

theorem t1RunAt_reachable_version_spec
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse cWidth cComplexity,
      ∀ n k epsilon t,
        c0 ≤ epsilon →
        epsilon ≤ k →
        k + 4 ≤ n →
        let quota := 2 ^ (k - epsilon)
        let events := t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t
        let s := t1RunAt c cDesc cSparse n k epsilon quota t
        T1RunCoreInvariant cSparse n k epsilon quota events s ∧
        ∀ version, version < s.versions.length →
          version < 2 ^ (epsilon + logSlack cWidth n) ∧
          let L := s.versions.getD version []
          L.Nodup ∧
          L.length = 2 ^ (k - epsilon) ∧
          L.toFinset ⊆ stringsOfLength n ∧
          ∃ hL : L.toFinset.Nonempty,
            plainSetComplexity V L.toFinset hL ≤
              (epsilon + logSlack cComplexity n : ENat) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t1RunFromEvents_core_spec V c hc cDesc
  obtain ⟨cWidth, hwidth⟩ :=
    t1RunAt_version_lt_width_of_model_spec c cDesc cSparse
  obtain ⟨cComplexity, hcomplexity⟩ :=
    plainSetComplexity_t1RunVersion_le
      V hV c cDesc cSparse cWidth
  refine ⟨c0, cSparse, cWidth, cComplexity, ?_⟩
  intro n k epsilon t hc0 hepsilon hkn
  let quota := 2 ^ (k - epsilon)
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  have hprefixCore :
      ∀ pref, pref <+: events →
        T1RunCoreInvariant cSparse n k epsilon quota pref
          (t1RunFromEvents cSparse n k epsilon quota
            (t1InitialRunState n k epsilon) pref) := by
    intro pref hpref
    exact hcore n k epsilon quota t pref hc0 hepsilon hkn rfl
      (by simpa [events] using hpref)
  have hfull :
      T1RunCoreInvariant cSparse n k epsilon quota events s := by
    simpa [s, t1RunAt, events] using
      hprefixCore events (List.prefix_refl events)
  have hversions :
      T1RunVersionsModelInvariant n k epsilon s := by
    change T1RunVersionsModelInvariant n k epsilon
      (t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon) events)
    apply t1RunFromEvents_versions_model_of_prefix_model
    intro pref hpref
    exact (hprefixCore pref hpref).1
  refine ⟨hfull, ?_⟩
  intro version hversion
  have hversionRaw :
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon)) t).versions.length := by
    simpa [s, quota] using hversion
  have hwidthVersion :
      version < 2 ^ (epsilon + logSlack cWidth n) :=
    hwidth n k epsilon t version
      (by
        intro pref hpref
        exact (hprefixCore pref
          (by simpa [events] using hpref)).1)
      hepsilon hkn hversionRaw
  refine ⟨hwidthVersion, ?_⟩
  let L := s.versions.getD version []
  have hLmem : L ∈ s.versions := by
    dsimp [L]
    rw [List.getD_eq_getElem s.versions [] hversion]
    exact List.getElem_mem hversion
  obtain ⟨hLnodup, hLlength, hLsubset⟩ :=
    hversions L hLmem
  have hL : L.toFinset.Nonempty :=
    t1RunVersion_nonempty hLlength
  have hcomplexityVersion :
      plainSetComplexity V L.toFinset hL ≤
        (epsilon + logSlack cComplexity n : ENat) := by
    exact hcomplexity n k epsilon t version
      hepsilon hkn hversionRaw hwidthVersion hL
  exact ⟨hLnodup, hLlength, hLsubset, hL,
    hcomplexityVersion⟩

end Kolmogorov
