import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3

/-!
# Complexity of reachable T3 run versions

This module converts the quota-aware replay theorem from `T3.lean` into the
ordinary plain-complexity bound needed by the many-strange-strings
construction.  The decoder remains partial: only version ordinals already
present at a reachable stage are used.
-/

namespace Kolmogorov

/-- The four-field T3 header and fixed-width version address fit in the
advertised `epsilon + delta + O(log n)` budget. -/
theorem t3VersionProgram_length_le
    (cWidth n k epsilon delta version : Nat)
    (hk : k ≤ n) (hepsilon : epsilon ≤ n) (hdelta : delta ≤ n)
    (hv : version <
      2 ^ (epsilon + delta + logSlack cWidth n)) :
    (t3VersionProgram cWidth n k epsilon delta version).length ≤
      epsilon + delta + logSlack (cWidth + 24) n := by
  unfold t3VersionProgram
  rw [length_pairCode]
  rw [chunkAddress_length version
    (epsilon + delta + logSlack cWidth n) hv]
  have hlistCode :
      (listCode [Nat.bits n, Nat.bits k, Nat.bits epsilon,
        Nat.bits delta]).length =
        2 * (Nat.bits n).length +
        2 * (Nat.bits k).length +
        2 * (Nat.bits epsilon).length +
        2 * (Nat.bits delta).length + 4 := by
    simp [listCode_cons, length_pairCode]
    ring
  rw [hlistCode]
  have hbitsK :
      (Nat.bits k).length ≤ (Nat.bits n).length :=
    length_natBits_mono hk
  have hbitsE :
      (Nat.bits epsilon).length ≤ (Nat.bits n).length :=
    length_natBits_mono hepsilon
  have hbitsD :
      (Nat.bits delta).length ≤ (Nat.bits n).length :=
    length_natBits_mono hdelta
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits n).length),
    Nat.zero_le ((Nat.bits k).length),
    Nat.zero_le ((Nat.bits epsilon).length),
    Nat.zero_le ((Nat.bits delta).length)]

/-- Evaluation of the quota-aware partial decoder bounds the ordinary plain
complexity of the decoded canonical finite-set code. -/
theorem plainSetComplexity_of_t3VersionDecoder_eval
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code) (cDesc cSparse : Nat) :
    ∃ cDecoder : Nat, ∀ p L (hL : L.toFinset.Nonempty),
      canonicalImageCodeOfList L ∈
        t3VersionDecoder c cDesc cSparse p →
      plainSetComplexity V L.toFinset hL ≤
        (p.length + cDecoder : ENat) := by
  obtain ⟨cMap, hMap⟩ :=
    plainK_partrec_map_le V hV
      (t3VersionDecoder c cDesc cSparse)
      (t3VersionDecoder_partrec c cDesc cSparse)
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

/-- Every reachable version of the exact smaller-quota run has ordinary
canonical set complexity at most `epsilon + delta + O(log n)`. -/
theorem plainSetComplexity_t3RunVersion_le_of_k_le_n
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code)
    (cDesc cSparse cWidth : Nat) :
    ∃ cComplexity, ∀ n k epsilon delta t version,
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.length →
      version <
        2 ^ (epsilon + delta + logSlack cWidth n) →
      let L :=
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.getD version []
      ∀ hL : L.toFinset.Nonempty,
        plainSetComplexity V L.toFinset hL ≤
          (epsilon + delta + logSlack cComplexity n : ENat) := by
  obtain ⟨cDecoder, hDecoder⟩ :=
    plainSetComplexity_of_t3VersionDecoder_eval
      V hV c cDesc cSparse
  refine ⟨cWidth + 24 + cDecoder, ?_⟩
  intro n k epsilon delta t version hepsilon hdelta hkn
    hseen hwidth
  dsimp only
  intro hL
  have hEval :=
    t3VersionDecoder_eval c cDesc cSparse cWidth
      n k epsilon delta t version hseen hwidth
  have hPlain :=
    hDecoder
      (t3VersionProgram cWidth n k epsilon delta version)
      ((t1RunAt c cDesc cSparse n k epsilon
        (2 ^ (k - epsilon - delta)) t).versions.getD version [])
      hL hEval
  have hProgram :=
    t3VersionProgram_length_le cWidth n k epsilon delta version
      (by omega) (by omega) (by omega) hwidth
  calc
    plainSetComplexity V
        ((t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.getD
            version []).toFinset hL
        ≤ (((t3VersionProgram cWidth n k epsilon delta version).length +
            cDecoder : Nat) : ENat) := by
      simpa only [Nat.cast_add] using hPlain
    _ ≤ ((epsilon + delta + logSlack (cWidth + 24) n +
          cDecoder : Nat) : ENat) := by
      exact_mod_cast Nat.add_le_add_right hProgram cDecoder
    _ ≤ ((epsilon + delta +
          logSlack (cWidth + 24 + cDecoder) n : Nat) : ENat) := by
      exact_mod_cast (show
        epsilon + delta + logSlack (cWidth + 24) n + cDecoder ≤
          epsilon + delta +
            logSlack (cWidth + 24 + cDecoder) n by
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits n).length)])

/-- Compatibility form of the reachable-version bound in the interior range. -/
theorem plainSetComplexity_t3RunVersion_le
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code)
    (cDesc cSparse cWidth : Nat) :
    ∃ cComplexity, ∀ n k epsilon delta t version,
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.length →
      version < 2 ^ (epsilon + delta + logSlack cWidth n) →
      let L :=
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.getD version []
      ∀ hL : L.toFinset.Nonempty,
        plainSetComplexity V L.toFinset hL ≤
          (epsilon + delta + logSlack cComplexity n : ENat) := by
  obtain ⟨cComplexity, hComplexity⟩ :=
    plainSetComplexity_t3RunVersion_le_of_k_le_n
      V hV c cDesc cSparse cWidth
  exact ⟨cComplexity, fun n k epsilon delta t version hepsilon hdelta hkn =>
    hComplexity n k epsilon delta t version hepsilon hdelta (by omega)⟩

/-- The canonical initial current model has ordinary complexity at most
`epsilon + delta + O(log n)`, uniformly through the boundary range `k ≤ n`. -/
theorem plainSetComplexity_t3InitialCurrent_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ (n k epsilon delta : Nat),
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k ≤ n →
      let A := (t1InitialCurrent n k epsilon).toFinset
      ∀ hA : A.Nonempty,
        plainSetComplexity V A hA ≤
          (epsilon + delta + logSlack c n : ENat) := by
  let code : Nat.Partrec.Code := Nat.Partrec.Code.zero
  obtain ⟨cComplexity, hComplexity⟩ :=
    plainSetComplexity_t3RunVersion_le_of_k_le_n
      V hV code 0 0 0
  refine ⟨cComplexity, ?_⟩
  intro n k epsilon delta hepsilon hdelta hkn
  dsimp only
  intro hA
  let s := t1RunAt code 0 0 n k epsilon
    (2 ^ (k - epsilon - delta)) 0
  have hprefix : [t1InitialCurrent n k epsilon] <+: s.versions := by
    simpa [s, t1InitialRunState] using
      (t1RunFromEvents_versions_prefix 0 n k epsilon
        (2 ^ (k - epsilon - delta))
        (t1InitialRunState n k epsilon)
        (t1MarkingEventStage code n k epsilon
          (epsilon + logSlack 0 n) 0))
  obtain ⟨tail, htail⟩ := hprefix
  have hseen : 0 < s.versions.length := by
    rw [← htail]
    simp
  have hzero : s.versions.getD 0 [] = t1InitialCurrent n k epsilon := by
    rw [← htail]
    simp
  have hbound : 0 < 2 ^ (epsilon + delta + logSlack 0 n) :=
    Nat.two_pow_pos _
  have h := hComplexity n k epsilon delta 0 0 hepsilon hdelta hkn
    (by simpa [s] using hseen) hbound
  change s.versions.getD 0 [] = t1InitialCurrent n k epsilon at hzero
  rw [hzero] at h
  exact h hA

/-- The fixed-width T3 version bound derived from an explicit prefix model
invariant for one already-chosen selector.  This selector-fixed form is what
later packages may safely combine with the structural run theorem. -/
theorem t3RunAt_version_lt_width_of_model_spec
    (c : Nat.Partrec.Code) (cDesc cSparse : Nat) :
    ∃ cWidth, ∀ n k epsilon delta t version,
      (∀ events,
        events <+: t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t →
        T1RunModelInvariant cSparse n k epsilon
          (2 ^ (k - epsilon - delta))
          (t1RunFromEvents cSparse n k epsilon
            (2 ^ (k - epsilon - delta))
            (t1InitialRunState n k epsilon) events)) →
      epsilon ≤ k →
      delta ≤ k - epsilon →
      k + 4 ≤ n →
      version <
        (t1RunAt c cDesc cSparse n k epsilon
          (2 ^ (k - epsilon - delta)) t).versions.length →
      version <
        2 ^ (epsilon + delta + logSlack cWidth n) := by
  obtain ⟨cWidth, hcount⟩ :=
    t3_change_count_arith cDesc cSparse
  refine ⟨cWidth, ?_⟩
  intro n k epsilon delta t version hmodel hepsilon hdelta hkn
    hversion
  let quota := 2 ^ (k - epsilon - delta)
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
        2 ^ (epsilon + delta + logSlack cWidth n) := by
    apply hcount n k epsilon delta s.external s.saturation
      s.totalC s.totalD hepsilon hdelta hkn
    · exact t1RunAt_external_rebuilds_le_of_quota
        c cDesc cSparse n k epsilon quota t
    · exact hC
    · exact t1RunAt_totalD_le_of_quota
        c cDesc cSparse n k epsilon quota t
    · simpa [s, quota] using
        (t3RunAt_saturation_charge
          c cDesc cSparse n k epsilon delta t)
  have hlength :
      s.versions.length = s.external + s.saturation + 1 := by
    simpa [s, quota] using
      t1RunAt_versions_length c cDesc cSparse n k epsilon quota t
  have hversion' : version < s.versions.length := by
    simpa [s, quota] using hversion
  omega

/-- One shared sparse selector supplies the structural, fixed-width, and
ordinary plain-complexity facts for every reachable T3 version. -/
theorem t3RunAt_reachable_version_spec
    (V : Map) (hV : isOptimalConditional V)
    (c : Nat.Partrec.Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse cWidth cComplexity,
      ∀ n k epsilon delta t,
        c0 ≤ epsilon →
        epsilon ≤ k →
        delta ≤ k - epsilon →
        k + 4 ≤ n →
        let quota := 2 ^ (k - epsilon - delta)
        let events := t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t
        let s := t1RunAt c cDesc cSparse n k epsilon quota t
        T1RunCoreInvariant cSparse n k epsilon quota events s ∧
        ∀ version, version < s.versions.length →
          version <
              2 ^ (epsilon + delta + logSlack cWidth n) ∧
          let L := s.versions.getD version []
          L.Nodup ∧
          L.length = 2 ^ (k - epsilon) ∧
          L.toFinset ⊆ stringsOfLength n ∧
          ∃ hL : L.toFinset.Nonempty,
            plainSetComplexity V L.toFinset hL ≤
              (epsilon + delta +
                logSlack cComplexity n : ENat) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t3RunFromEvents_core_spec V c hc cDesc
  obtain ⟨cWidth, hwidth⟩ :=
    t3RunAt_version_lt_width_of_model_spec c cDesc cSparse
  obtain ⟨cComplexity, hcomplexity⟩ :=
    plainSetComplexity_t3RunVersion_le_of_k_le_n
      V hV c cDesc cSparse cWidth
  refine ⟨c0, cSparse, cWidth, cComplexity, ?_⟩
  intro n k epsilon delta t hc0 hepsilon hdelta hkn
  let quota := 2 ^ (k - epsilon - delta)
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  have hprefixCore :
      ∀ pref, pref <+: events →
        T1RunCoreInvariant cSparse n k epsilon quota pref
          (t1RunFromEvents cSparse n k epsilon quota
            (t1InitialRunState n k epsilon) pref) := by
    intro pref hpref
    exact hcore n k epsilon delta t pref hc0 hepsilon hdelta hkn
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
          (2 ^ (k - epsilon - delta)) t).versions.length := by
    simpa [s, quota] using hversion
  have hwidthVersion :
      version <
        2 ^ (epsilon + delta + logSlack cWidth n) :=
    hwidth n k epsilon delta t version
      (by
        intro pref hpref
        exact (hprefixCore pref
          (by simpa [events] using hpref)).1)
      hepsilon hdelta hkn hversionRaw
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
        (epsilon + delta +
          logSlack cComplexity n : ENat) := by
    exact hcomplexity n k epsilon delta t version
      hepsilon hdelta (by omega) hversionRaw hwidthVersion hL
  exact ⟨hLnodup, hLlength, hLsubset, hL,
    hcomplexityVersion⟩

theorem t3_current_exceptional_of_core
    {cSparse n k epsilon delta : Nat} {events : List T1MarkEvent}
    {s : T1RunState}
    (hcore : T1RunCoreInvariant cSparse n k epsilon
      (2 ^ (k - epsilon - delta)) events s) :
    ∃ bad,
      bad ⊆ s.current.toFinset ∧
      bad.card ≤ 2 ^ (k - epsilon - delta) ∧
      ∀ x ∈ s.current.toFinset \ bad,
        x ∉ s.cMarked.toFinset ∪ s.dMarked.toFinset := by
  let bad := s.current.toFinset ∩ (s.cMarked.toFinset ∪ s.dMarked.toFinset)
  refine ⟨bad, Finset.inter_subset_left, ?_, ?_⟩
  · exact hcore.1.2.2.2.2.1.le
  · intro x hx
    simp only [Finset.mem_sdiff, bad, Finset.mem_inter, not_and] at hx
    exact hx.2 hx.1

theorem t3_terminal_avoidance_of_core
    (V : Map) (_hV : isOptimalConditional V)
    (c : Nat.Partrec.Code) (hc : IsCodeFor c V)
    (cDesc _c0 cSparse cWidth cComplexity : Nat)
    (n k epsilon delta t : Nat)
    (_hc0 : _c0 ≤ epsilon)
    (_hepsilon : epsilon ≤ k)
    (_hdelta : delta ≤ k - epsilon)
    (_hkn : k + 4 ≤ n)
    (hstable : ∀ m ≥ t,
      t1MarkingEventStage c n k epsilon (epsilon + logSlack cDesc n) m =
        t1MarkingEventStage c n k epsilon (epsilon + logSlack cDesc n) t)
    (hreachable :
        let quota := 2 ^ (k - epsilon - delta)
        let events := t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t
        let s := t1RunAt c cDesc cSparse n k epsilon quota t
        T1RunCoreInvariant cSparse n k epsilon quota events s ∧
        ∀ version, version < s.versions.length →
          version < 2 ^ (epsilon + delta + logSlack cWidth n) ∧
          let L := s.versions.getD version []
          L.Nodup ∧
          L.length = 2 ^ (k - epsilon) ∧
          L.toFinset ⊆ stringsOfLength n ∧
          ∃ hL : L.toFinset.Nonempty,
            plainSetComplexity V L.toFinset hL ≤
              (epsilon + delta + logSlack cComplexity n : ENat)) :
    ∃ (A : Finset BitString) (hA : A.Nonempty) (bad : Finset BitString),
      A ⊆ stringsOfLength n ∧
      A.card = 2 ^ (k - epsilon) ∧
      bad ⊆ A ∧
      bad.card ≤ 2 ^ (k - epsilon - delta) ∧
      plainSetComplexity V A hA ≤
        (epsilon + delta + logSlack cComplexity n : ENat) ∧
      ∀ x ∈ A \ bad,
        x.length = n ∧
        ¬ T1BMarked V n epsilon x ∧
        ¬ T1CMarked V n k (epsilon + logSlack cDesc n) x ∧
        ¬ T1DMarked V n k x := by
  let quota := 2 ^ (k - epsilon - delta)
  let events := t1MarkingEventStage c n k epsilon
    (epsilon + logSlack cDesc n) t
  let s := t1RunAt c cDesc cSparse n k epsilon quota t
  obtain ⟨hcore, hversions⟩ := hreachable
  obtain ⟨bad, hbad_sub, hbad_card, hbad_avoid⟩ :=
    t3_current_exceptional_of_core hcore
  obtain ⟨version, hversion, hcurrent⟩ :=
    hcore.exists_current_version
  have hversionSpec := hversions version hversion
  dsimp only at hversionSpec
  obtain ⟨_hwidth, _hnodup, _hlength, _hsubset,
      _hversionNonempty, hversionComplexity⟩ :=
    hversionSpec
  have hA : s.current.toFinset.Nonempty :=
    hcore.1.current_nonempty
  have hcomplexity :
      plainSetComplexity V s.current.toFinset hA ≤
        (epsilon + delta + logSlack cComplexity n : ENat) := by
    simpa only [hcurrent] using hversionComplexity
  refine ⟨s.current.toFinset, hA, bad,
    hcore.1.2.2.1, ?_, hbad_sub, hbad_card, hcomplexity, ?_⟩
  · exact (List.toFinset_card_of_nodup hcore.1.1).trans hcore.1.2.1
  · intro x hx
    have hx_A : x ∈ s.current.toFinset := (Finset.mem_sdiff.mp hx).1
    have hxlen : x.length = n :=
      (memStringsOfLength n x).mp (hcore.1.2.2.1 hx_A)
    have hhistory := hcore.2.1
    have hBEvent : ∀ code,
        T1MarkEvent.bSet code ∈ events →
          x ∉ t1CodeToSet code := by
      intro code hevent hxcode
      have hxb : x ∉ s.bMarked.toFinset :=
        Finset.disjoint_left.mp hcore.1.2.2.2.1 hx_A
      apply hxb
      exact (hhistory.1 x).2
        ⟨hxlen, code, hevent, hxcode⟩
    have hx_not_CD : x ∉ s.cMarked.toFinset ∪ s.dMarked.toFinset :=
      hbad_avoid x hx
    have hxc : x ∉ s.cMarked.toFinset := fun h => hx_not_CD (Finset.mem_union_left _ h)
    have hxd : x ∉ s.dMarked.toFinset := fun h => hx_not_CD (Finset.mem_union_right _ h)
    have hCEvent : ∀ code batch,
        T1MarkEvent.cPrimeModel code ∈ events →
        T1MarkEvent.cDoublePrimeBatch batch ∈ events →
        code ∈ batch →
          x ∉ t1CodeToSet code := by
      intro code batch hprime hdouble hcode hxcode
      apply hxc
      exact (hhistory.2.1 x).2
        ⟨hxlen, code, batch, hprime, hdouble, hcode,
          hxcode⟩
    have hDEvent :
        T1MarkEvent.dString x ∉ events := by
      intro hevent
      apply hxd
      exact (hhistory.2.2.1 x).2 ⟨hxlen, hevent⟩
    have havoid :
        ¬ T1BMarked V n epsilon x ∧
        ¬ T1CMarked V n k (epsilon + logSlack cDesc n) x ∧
        ¬ T1DMarked V n k x :=
      t1FinalEventAvoidance hc hstable hBEvent hCEvent hDEvent
    exact ⟨hxlen, havoid.1, havoid.2.1, havoid.2.2⟩

/-- The stabilized smaller-quota run supplies one simple model together with
an exceptional subset of the source's advertised size.  Every other member
avoids the three marking families used by the Figure 6 profile argument.

Unlike `t3_terminal_avoidance_of_core`, this theorem chooses the machine code,
the shared sparse selector, the replay constants, and the stabilization stage;
its only inputs are the visible parameters of the construction. -/
theorem exists_t3_avoiding_set_core
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cDesc : Nat, ∃ c0 cCore : Nat,
      ∀ n k epsilon delta : Nat,
        c0 ≤ epsilon →
        epsilon ≤ k →
        delta ≤ k - epsilon →
        k + 4 ≤ n →
        ∃ (A : Finset BitString) (hA : A.Nonempty)
            (bad : Finset BitString),
          A ⊆ stringsOfLength n ∧
          A.card = 2 ^ (k - epsilon) ∧
          bad ⊆ A ∧
          bad.card ≤ 2 ^ (k - epsilon - delta) ∧
          plainSetComplexity V A hA ≤
            (epsilon + delta + logSlack cCore n : ENat) ∧
          ∀ x ∈ A \ bad,
            x.length = n ∧
            ¬ T1BMarked V n epsilon x ∧
            ¬ T1CMarked V n k
              (epsilon + logSlack cDesc n) x ∧
            ¬ T1DMarked V n k x := by
  obtain ⟨c, hc⟩ :
      ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  intro cDesc
  obtain ⟨c0, cSparse, cWidth, cCore, hreachable⟩ :=
    t3RunAt_reachable_version_spec V hV c hc cDesc
  refine ⟨c0, cCore, ?_⟩
  intro n k epsilon delta hc0 hepsilon hdelta hkn
  obtain ⟨T, hstable⟩ :=
    t1MarkingEventStage_stabilizes c n k epsilon
      (epsilon + logSlack cDesc n)
  have hreachableT :
      let quota := 2 ^ (k - epsilon - delta)
      let events := t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) T
      let s := t1RunAt c cDesc cSparse n k epsilon quota T
      T1RunCoreInvariant cSparse n k epsilon quota events s ∧
      ∀ version, version < s.versions.length →
        version <
            2 ^ (epsilon + delta + logSlack cWidth n) ∧
        let L := s.versions.getD version []
        L.Nodup ∧
        L.length = 2 ^ (k - epsilon) ∧
        L.toFinset ⊆ stringsOfLength n ∧
        ∃ hL : L.toFinset.Nonempty,
          plainSetComplexity V L.toFinset hL ≤
            (epsilon + delta + logSlack cCore n : ENat) := by
    exact hreachable n k epsilon delta T
      hc0 hepsilon hdelta hkn
  exact t3_terminal_avoidance_of_core
    V hV c hc cDesc c0 cSparse cWidth cCore
    n k epsilon delta T hc0 hepsilon hdelta hkn
    hstable hreachableT

end Kolmogorov
