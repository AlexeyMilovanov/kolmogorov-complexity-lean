import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1RunComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation

namespace Kolmogorov

theorem T1RunModelInvariant.current_nonempty
    {cSparse n k epsilon quota : Nat} {s : T1RunState}
    (h : T1RunModelInvariant cSparse n k epsilon quota s) :
    s.current.toFinset.Nonempty :=
  t1RunVersion_nonempty h.2.1

theorem T1RunModelInvariant.current_not_subset_cd
    {cSparse n k epsilon quota : Nat} {s : T1RunState}
    (h : T1RunModelInvariant cSparse n k epsilon quota s)
    (hquota : quota = 2 ^ (k - epsilon)) :
    ¬ s.current.toFinset ⊆
      s.cMarked.toFinset ∪ s.dMarked.toFinset := by
  intro hsubset
  have hinter :
      s.current.toFinset ∩
          (s.cMarked.toFinset ∪ s.dMarked.toFinset) =
        s.current.toFinset :=
    Finset.inter_eq_left.mpr hsubset
  have hcard : s.current.toFinset.card = s.current.length :=
    List.toFinset_card_of_nodup h.1
  have hlt := h.2.2.2.2.1
  rw [hinter, hcard, h.2.1, hquota] at hlt
  exact (Nat.lt_irrefl _ hlt)

theorem T1RunCoreInvariant.exists_current_version
    {cSparse n k epsilon quota : Nat} {events : List T1MarkEvent} {s : T1RunState}
    (h : T1RunCoreInvariant cSparse n k epsilon quota events s) :
    ∃ version, version < s.versions.length ∧
      s.versions.getD version [] = s.current := by
  refine ⟨s.versions.length - 1, ?_, h.2.2.2⟩
  rw [h.2.2.1]
  omega

/-- Avoiding the source's `D` marks gives the lower plain-complexity endpoint
used in the Figure 6 profile argument. -/
theorem t1_not_dMarked_plainK_lower
    {V : Map} {n k : Nat} {x : BitString}
    (hxlen : x.length = n)
    (hnot : ¬ T1DMarked V n k x) :
    (k : ENat) ≤ plainK V x := by
  unfold T1DMarked at hnot
  push_neg at hnot
  exact hnot hxlen

theorem exists_t1_avoiding_set_core
    (V : Map) (hV : isOptimalConditional V) :
    ∀ cDesc : Nat, ∃ c0 cCore : Nat, ∀ n k epsilon : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      ∃ (A : Finset BitString) (hA : A.Nonempty)
          (x : BitString),
        A ⊆ stringsOfLength n ∧
        A.card = 2 ^ (k - epsilon) ∧
        x ∈ A ∧
        x.length = n ∧
        plainSetComplexity V A hA ≤
          (epsilon + logSlack cCore n : ENat) ∧
        ¬ T1BMarked V n epsilon x ∧
        ¬ T1CMarked V n k
          (epsilon + logSlack cDesc n) x ∧
        ¬ T1DMarked V n k x := by
  obtain ⟨c, hc⟩ :
      ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  intro cDesc
  obtain ⟨c0, cSparse, cWidth, cCore, hreachable⟩ :=
    t1RunAt_reachable_version_spec V hV c hc cDesc
  refine ⟨c0, cCore, ?_⟩
  intro n k epsilon hc0 hepsilon hkn
  let d := epsilon + logSlack cDesc n
  obtain ⟨T, hstable⟩ :=
    t1MarkingEventStage_stabilizes c n k epsilon d
  let quota := 2 ^ (k - epsilon)
  let events :=
    t1MarkingEventStage c n k epsilon d T
  let s :=
    t1RunAt c cDesc cSparse n k epsilon quota T
  have hreachableT :
      T1RunCoreInvariant cSparse n k epsilon quota events s ∧
      ∀ version, version < s.versions.length →
        version < 2 ^ (epsilon + logSlack cWidth n) ∧
        let L := s.versions.getD version []
        L.Nodup ∧
        L.length = 2 ^ (k - epsilon) ∧
        L.toFinset ⊆ stringsOfLength n ∧
        ∃ hL : L.toFinset.Nonempty,
          plainSetComplexity V L.toFinset hL ≤
            (epsilon + logSlack cCore n : ENat) := by
    simpa [quota, events, s, d] using
      hreachable n k epsilon T hc0 hepsilon hkn
  obtain ⟨hcore, hversions⟩ := hreachableT
  obtain ⟨version, hversion, hcurrent⟩ :=
    hcore.exists_current_version
  have hversionSpec := hversions version hversion
  dsimp only at hversionSpec
  obtain ⟨_hwidth, _hnodup, _hlength, _hsubset,
      hversionNonempty, hversionComplexity⟩ :=
    hversionSpec
  have hA : s.current.toFinset.Nonempty :=
    hcore.1.current_nonempty
  have hcomplexity :
      plainSetComplexity V s.current.toFinset hA ≤
        (epsilon + logSlack cCore n : ENat) := by
    simpa only [hcurrent] using hversionComplexity
  have hnotSubset :
      ¬ s.current.toFinset ⊆
        s.cMarked.toFinset ∪ s.dMarked.toFinset :=
    hcore.1.current_not_subset_cd rfl
  obtain ⟨x, hx, hxb, hxc, hxd⟩ :=
    t1_exists_current_survivor hcore.1.2.2.2.1
      hnotSubset
  have hxlen : x.length = n :=
    (memStringsOfLength n x).mp
      (hcore.1.2.2.1 hx)
  have hhistory := hcore.2.1
  have hBEvent : ∀ code,
      T1MarkEvent.bSet code ∈ events →
        x ∉ t1CodeToSet code := by
    intro code hevent hxcode
    apply hxb
    exact (hhistory.1 x).2
      ⟨hxlen, code, hevent, hxcode⟩
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
      ¬ T1CMarked V n k d x ∧
      ¬ T1DMarked V n k x :=
    t1FinalEventAvoidance hc hstable
      hBEvent hCEvent hDEvent
  refine ⟨s.current.toFinset, hA, x,
    hcore.1.2.2.1, ?_, hx, hxlen, hcomplexity,
    havoid.1, ?_, havoid.2.2⟩
  · exact
      (List.toFinset_card_of_nodup hcore.1.1).trans
        hcore.1.2.1
  · simpa [d] using havoid.2.1

theorem t1_profile_bounds_of_optimal
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c0 cProfile : Nat, ∀ n k epsilon : Nat,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      ∃ x : BitString,
        x.length = n ∧
        (k : ENat) ≤ plainK V x ∧
        plainK V x ≤ (k + logSlack cProfile n : ENat) ∧
        ProfileSetsWithinNeighborhood
          (plainDescriptionProfileSet V x)
          (t1PlainPolygon n k epsilon)
          (logSlack cProfile n) ∧
        (∀ q ∈ strongDescriptionProfileSet V T x epsilon,
          ∃ q' ∈ t1StrongPolygon n k,
            natPairLInfDistance q q' ≤ logSlack cProfile n) ∧
        (logSlack cProfile n, n) ∈
          strongDescriptionProfileSet V T x epsilon ∧
        (k + logSlack cProfile n, 0) ∈
          strongDescriptionProfileSet V T x epsilon := by
  obtain ⟨cDesc, cEndpoint, hprofile⟩ :=
    t1_avoiding_set_profile_bounds V T hV hT
  obtain ⟨cCore, cA, hcore⟩ :=
    exists_t1_avoiding_set_core V hV cDesc
  obtain ⟨cProfile, hbounds⟩ := hprofile cA
  refine ⟨max cCore cEndpoint, cProfile, ?_⟩
  intro n k epsilon hc0 hepsilon hkn
  obtain ⟨A, hA, x, hAcube, hAcard, hxA, hxlen,
      hAcomplexity, hnotB, hnotC, hnotD⟩ :=
    hcore n k epsilon (le_trans (Nat.le_max_left _ _) hc0)
      hepsilon hkn
  obtain ⟨hKlower, hKupper, hplain, hstrong,
      hfull, hsingleton⟩ :=
    hbounds n k epsilon A hA x
      (le_trans (Nat.le_max_right _ _) hc0)
      hepsilon hkn hAcube hAcard hxA hxlen
      hAcomplexity hnotB hnotC hnotD
  exact ⟨x, hxlen, hKlower, hKupper, hplain,
    hstrong, hfull, hsingleton⟩

end Kolmogorov
