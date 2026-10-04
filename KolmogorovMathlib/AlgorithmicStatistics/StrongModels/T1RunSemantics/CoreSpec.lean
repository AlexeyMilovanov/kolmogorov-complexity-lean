import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part03
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1RunSemantics.History

/-!
# The core invariant of the marking run

`t1RunAt_core_spec`: for suitable constants and quota `2 ^ (k - epsilon)`, the T1 run at any
stage satisfies the core invariant — its current block is a genuine model, every version is
recorded, and the charging accounts are in order.  This is the statement `T1Core` and
`T1RunComplexity` consume.

It is built up one step at a time: `t1RunRebuild_preserves_model` for a rebuild,
`t1RunPrepared_preserves_model` for a transition that keeps the current model,
`t1RunRebuild_model_of_history` for a rebuild justified by the histories of a stage, and
`t1RunStep_preserves_model` for one reachable chronological event.
`t1RunFromEvents_model_spec_of_quota_pos` and `t1RunFromEvents_core_spec_of_quota_pos` extend
these along a whole event prefix, with the whole-model-quota specialisations
`t1RunFromEvents_model_spec` and `t1RunFromEvents_core_spec` retained for the original API.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The selector output is a valid model immediately after a rebuild.  This is
the local bridge from `t1RunRebuild_model_spec` to the state invariant. -/
private theorem t1RunRebuild_preserves_model
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (hquota : 0 < quota)
    (hspec :
      let s' := t1RunRebuild cSparse n k epsilon s
      s'.current.Nodup ∧
        s'.current.toFinset ⊆ (t1RunUnmarked n s).toFinset ∧
        s'.current.length = 2 ^ (k - epsilon) ∧
        ∀ code ∈ s.seenCDouble,
          (s'.current.toFinset ∩
            (canonicalPointListOfCode code).toFinset).card ≤
              cSparse * n + cSparse) :
    T1RunModelInvariant cSparse n k epsilon quota
      (t1RunRebuild cSparse n k epsilon s) := by
  let s' := t1RunRebuild cSparse n k epsilon s
  change
    s'.current.Nodup ∧
    s'.current.length = 2 ^ (k - epsilon) ∧
    s'.current.toFinset ⊆ stringsOfLength n ∧
    Disjoint s'.current.toFinset s'.bMarked.toFinset ∧
    (s'.current.toFinset ∩
      (s'.cMarked.toFinset ∪ s'.dMarked.toFinset)).card < quota ∧
    (∀ code ∈ s'.seenCDouble,
      (s'.current.toFinset ∩ t1CodeToSet code).card ≤
        cSparse * n + cSparse)
  dsimp only at hspec
  rcases hspec with ⟨hnodup, hsub, hlength, hsparse⟩
  have hdata :
      T1RunMarkingDataEq s s' := by
    exact t1RunRebuild_markingDataEq cSparse n k epsilon s
  rcases hdata with ⟨hb, hc, hd, _hcp, hcd⟩
  rw [t1RunUnmarked_toFinset] at hsub
  have hcube : s'.current.toFinset ⊆ stringsOfLength n := by
    intro x hx
    exact (Finset.mem_sdiff.mp (hsub hx)).1
  have havoids :
      ∀ x ∈ s'.current.toFinset,
        x ∉ (t1RunMarked s).toFinset := by
    intro x hx
    exact (Finset.mem_sdiff.mp (hsub hx)).2
  have hbdisjoint :
      Disjoint s'.current.toFinset s.bMarked.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxcurrent hxb
    exact havoids x hxcurrent (by
      rw [t1RunMarked_toFinset]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hxb))
  have hcdempty :
      s'.current.toFinset ∩
        (s.cMarked.toFinset ∪ s.dMarked.toFinset) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hxcurrent, hxcd⟩ := hx
    exact havoids x hxcurrent (by
      rw [t1RunMarked_toFinset]
      rcases Finset.mem_union.mp hxcd with hxc | hxd
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ hxc)
      · exact Finset.mem_union_right _ hxd)
  refine ⟨hnodup, hlength, hcube, ?_, ?_, ?_⟩
  · simpa [← hb] using hbdisjoint
  · simpa [← hc, ← hd, hcdempty] using hquota
  · intro code hcode
    have hcode' : code ∈ s.seenCDouble := by
      simpa [hcd] using hcode
    simpa [canonicalPointListOfCode, t1CodeToSet] using
      hsparse code hcode'

/-- A transition that keeps the current model needs only the explicit
post-transition nonsaturation test; all other model clauses are inherited. -/
private theorem t1RunPrepared_preserves_model
    (cSparse n k epsilon quota : Nat) (s prepared : T1RunState)
    (hmodel : T1RunModelInvariant cSparse n k epsilon quota s)
    (hcurrent : prepared.current = s.current)
    (hb : prepared.bMarked = s.bMarked)
    (hseen : prepared.seenCDouble = s.seenCDouble)
    (hnotSaturated : t1RunSaturated prepared quota ≠ true) :
    T1RunModelInvariant cSparse n k epsilon quota prepared := by
  rcases hmodel with
    ⟨hnodup, hlength, hcube, hbdisjoint, _holdHits, hsparse⟩
  have hpreparedNodup : prepared.current.Nodup := by
    simpa [hcurrent] using hnodup
  refine ⟨hpreparedNodup, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcurrent] using hlength
  · simpa [hcurrent] using hcube
  · simpa [hcurrent, hb] using hbdisjoint
  · apply Nat.lt_of_not_ge
    intro hge
    exact hnotSaturated
      ((t1RunSaturated_iff prepared quota hpreparedNodup).2 hge)
  · intro code hcode
    have hcode' : code ∈ s.seenCDouble := by
      simpa [hseen] using hcode
    simpa [hcurrent] using hsparse code hcode'

/-- A rebuild state whose exact histories come from a prefix of the fixed
chronological stage satisfies the complete model invariant. -/
private theorem t1RunRebuild_model_of_history
    (V : Map) (c : Code) (hc : IsCodeFor c V)
    (cDesc cSparse n k epsilon quota t : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (hquota : 0 < quota)
    (hprefix : events <+:
      t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t)
    (hhistory : T1RunHistoryInvariant n events s)
    (hrebuild :
      ∀ state : T1RunState,
        (∀ x ∈ (t1RunMarked state).toFinset,
          T1BMarked V n epsilon x ∨
            (∃ d, T1CMarked V n k d x) ∨
            T1DMarked V n k x) →
        state.seenCDouble.toFinset ⊆
          (t1CDoublePrimeBatches c n k
            (epsilon + logSlack cDesc n) t).flatten.toFinset →
        let state' := t1RunRebuild cSparse n k epsilon state
        state'.current.Nodup ∧
          state'.current.toFinset ⊆
            (t1RunUnmarked n state).toFinset ∧
          state'.current.length = 2 ^ (k - epsilon) ∧
          ∀ code ∈ state.seenCDouble,
            (state'.current.toFinset ∩
              (canonicalPointListOfCode code).toFinset).card ≤
                cSparse * n + cSparse) :
    T1RunModelInvariant cSparse n k epsilon quota
      (t1RunRebuild cSparse n k epsilon s) := by
  apply t1RunRebuild_preserves_model cSparse n k epsilon quota s hquota
  apply hrebuild s
  · exact t1RunHistory_marked_sound_of_prefix
      V c hc n k epsilon (epsilon + logSlack cDesc n) t
      events s hprefix hhistory
  · exact t1RunHistory_seenCDouble_subset_of_prefix
      c n k epsilon (epsilon + logSlack cDesc n) t
      events s hprefix hhistory

/-- Model semantics are preserved by one reachable chronological event. -/
private theorem t1RunStep_preserves_model
    (V : Map) (c : Code) (hc : IsCodeFor c V)
    (cDesc cSparse n k epsilon quota t : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (event : T1MarkEvent)
    (hquota : 0 < quota)
    (hprefix : events ++ [event] <+:
      t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t)
    (hrebuild :
      ∀ state : T1RunState,
        (∀ x ∈ (t1RunMarked state).toFinset,
          T1BMarked V n epsilon x ∨
            (∃ d, T1CMarked V n k d x) ∨
            T1DMarked V n k x) →
        state.seenCDouble.toFinset ⊆
          (t1CDoublePrimeBatches c n k
            (epsilon + logSlack cDesc n) t).flatten.toFinset →
        let state' := t1RunRebuild cSparse n k epsilon state
        state'.current.Nodup ∧
          state'.current.toFinset ⊆
            (t1RunUnmarked n state).toFinset ∧
          state'.current.length = 2 ^ (k - epsilon) ∧
          ∀ code ∈ state.seenCDouble,
            (state'.current.toFinset ∩
              (canonicalPointListOfCode code).toFinset).card ≤
                cSparse * n + cSparse)
    (hmodel : T1RunModelInvariant cSparse n k epsilon quota s)
    (hhistory : T1RunHistoryInvariant n (events ++ [event])
      (t1RunStep cSparse n k epsilon quota s event)) :
    T1RunModelInvariant cSparse n k epsilon quota
      (t1RunStep cSparse n k epsilon quota s event) := by
  cases event with
  | bSet w =>
      let prepared := t1RunBSetPrepared n s w
      have hdata :
          T1RunMarkingDataEq prepared
            (t1RunStep cSparse n k epsilon quota s (.bSet w)) :=
        t1RunStep_bSet_markingDataEq
          cSparse n k epsilon quota s w
      have hpreparedHistory :
          T1RunHistoryInvariant n (events ++ [.bSet w]) prepared :=
        (t1RunHistoryInvariant_congr hdata).mpr hhistory
      have hrebuildModel :
          T1RunModelInvariant cSparse n k epsilon quota
            (t1RunRebuild cSparse n k epsilon prepared) :=
        t1RunRebuild_model_of_history V c hc cDesc cSparse n k
          epsilon quota t (events ++ [.bSet w]) prepared hquota
          hprefix hpreparedHistory hrebuild
      rw [t1RunStep_bSet_eq]
      simpa [T1RunModelInvariant] using hrebuildModel
  | cDoublePrimeBatch batch =>
      let prepared := t1RunCDoublePrepared n s batch
      have hdata :
          T1RunMarkingDataEq prepared
            (t1RunStep cSparse n k epsilon quota s
              (.cDoublePrimeBatch batch)) :=
        t1RunStep_cDouble_markingDataEq
          cSparse n k epsilon quota s batch
      have hpreparedHistory :
          T1RunHistoryInvariant n
            (events ++ [.cDoublePrimeBatch batch]) prepared :=
        (t1RunHistoryInvariant_congr hdata).mpr hhistory
      have hrebuildModel :
          T1RunModelInvariant cSparse n k epsilon quota
            (t1RunRebuild cSparse n k epsilon prepared) :=
        t1RunRebuild_model_of_history V c hc cDesc cSparse n k
          epsilon quota t
          (events ++ [.cDoublePrimeBatch batch]) prepared hquota
          hprefix hpreparedHistory hrebuild
      rw [t1RunStep_cDouble_eq]
      simpa [T1RunModelInvariant] using hrebuildModel
  | cPrimeModel w =>
      by_cases hactive : w ∈ s.seenCDouble
      · let prepared := t1RunCPrimePrepared n s w
        have hdata :
            T1RunMarkingDataEq prepared
              (t1RunStep cSparse n k epsilon quota s
                (.cPrimeModel w)) :=
          t1RunStep_cPrime_active_markingDataEq
            cSparse n k epsilon quota s w hactive
        have hpreparedHistory :
            T1RunHistoryInvariant n
              (events ++ [.cPrimeModel w]) prepared :=
          (t1RunHistoryInvariant_congr hdata).mpr hhistory
        rw [t1RunStep_cPrime_eq]
        simp only [hactive, ite_true]
        by_cases hsat :
            t1RunSaturated (t1RunCPrimePrepared n s w) quota = true
        · simp only [hsat, ite_true]
          have hrebuildModel :
              T1RunModelInvariant cSparse n k epsilon quota
                (t1RunRebuild cSparse n k epsilon prepared) :=
            t1RunRebuild_model_of_history V c hc cDesc cSparse n k
              epsilon quota t (events ++ [.cPrimeModel w]) prepared
              hquota hprefix hpreparedHistory hrebuild
          simpa [T1RunModelInvariant] using hrebuildModel
        · simp only [Bool.not_eq_true] at hsat
          simp only [hsat, Bool.false_eq_true, ite_false]
          exact t1RunPrepared_preserves_model
            cSparse n k epsilon quota s prepared hmodel
              rfl rfl rfl (by
                intro htrue
                have hcontra :
                    t1RunSaturated
                      (t1RunCPrimePrepared n s w) quota = true := by
                  simpa [prepared] using htrue
                rw [hsat] at hcontra
                cases hcontra)
      · rw [t1RunStep_cPrime_eq]
        simp only [hactive, ite_false]
        simpa [T1RunModelInvariant, t1RunCPrimeSeenPrepared] using hmodel
  | dString x =>
      let prepared := t1RunDPrepared n s x
      have hdata :
          T1RunMarkingDataEq prepared
            (t1RunStep cSparse n k epsilon quota s (.dString x)) :=
        t1RunStep_dString_markingDataEq
          cSparse n k epsilon quota s x
      have hpreparedHistory :
          T1RunHistoryInvariant n (events ++ [.dString x]) prepared :=
        (t1RunHistoryInvariant_congr hdata).mpr hhistory
      rw [t1RunStep_dString_eq]
      by_cases hsat :
          t1RunSaturated (t1RunDPrepared n s x) quota = true
      · simp only [hsat, ite_true]
        have hrebuildModel :
            T1RunModelInvariant cSparse n k epsilon quota
              (t1RunRebuild cSparse n k epsilon prepared) :=
          t1RunRebuild_model_of_history V c hc cDesc cSparse n k
            epsilon quota t (events ++ [.dString x]) prepared hquota
            hprefix hpreparedHistory hrebuild
        simpa [T1RunModelInvariant] using hrebuildModel
      · simp only [Bool.not_eq_true] at hsat
        simp only [hsat, Bool.false_eq_true, ite_false]
        exact t1RunPrepared_preserves_model
          cSparse n k epsilon quota s prepared hmodel
            rfl rfl rfl (by
              intro htrue
              have hcontra :
                  t1RunSaturated (t1RunDPrepared n s x) quota = true := by
                simpa [prepared] using htrue
              rw [hsat] at hcontra
              cases hcontra)

/-- Reachable model semantics for every prefix of one fixed chronological
stage and every positive saturation quota.  The selector constants are
existential and depend on the fixed machine code and description slack,
exactly as in `t1RunRebuild_model_spec`; taking an arbitrary `cSparse` here
would be false. -/
theorem t1RunFromEvents_model_spec_of_quota_pos
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon quota t
      (events : List T1MarkEvent),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      0 < quota →
      events <+: t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t →
      T1RunModelInvariant cSparse n k epsilon quota
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events) := by
  intro cDesc
  obtain ⟨c0, cSparse, hrebuild⟩ :=
    t1RunRebuild_model_spec V c cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon quota t events hc0 hepsilon hkn hquota hprefix
  have hrebuildAt :
      ∀ state : T1RunState,
        (∀ x ∈ (t1RunMarked state).toFinset,
          T1BMarked V n epsilon x ∨
            (∃ d, T1CMarked V n k d x) ∨
            T1DMarked V n k x) →
        state.seenCDouble.toFinset ⊆
          (t1CDoublePrimeBatches c n k
            (epsilon + logSlack cDesc n) t).flatten.toFinset →
        let state' := t1RunRebuild cSparse n k epsilon state
        state'.current.Nodup ∧
          state'.current.toFinset ⊆
            (t1RunUnmarked n state).toFinset ∧
          state'.current.length = 2 ^ (k - epsilon) ∧
          ∀ code ∈ state.seenCDouble,
            (state'.current.toFinset ∩
              (canonicalPointListOfCode code).toFinset).card ≤
                cSparse * n + cSparse := by
    intro state hmarked hseen
    exact hrebuild n k epsilon t state hc0 hepsilon hkn
      hmarked hseen
  revert hprefix
  induction events using List.reverseRecOn with
  | nil =>
      intro _hprefix
      simpa [t1RunFromEvents] using
        t1InitialRunState_model_of_quota_pos cSparse n k epsilon quota
          hepsilon (by omega) hquota
  | append_singleton events event ih =>
      intro hprefix
      have hprefixOld :
          events <+: t1MarkingEventStage c n k epsilon
            (epsilon + logSlack cDesc n) t :=
        (List.prefix_append events [event]).trans hprefix
      have hmodel :
          T1RunModelInvariant cSparse n k epsilon quota
            (t1RunFromEvents cSparse n k epsilon quota
              (t1InitialRunState n k epsilon) events) :=
        ih hprefixOld
      have hhistory :
          T1RunHistoryInvariant n (events ++ [event])
            (t1RunStep cSparse n k epsilon quota
              (t1RunFromEvents cSparse n k epsilon quota
                (t1InitialRunState n k epsilon) events) event) :=
        t1RunStep_preserves_history cSparse n k epsilon quota
          events _ event
          (t1RunFromEvents_history cSparse n k epsilon quota events)
      rw [t1RunFromEvents_append]
      exact t1RunStep_preserves_model V c hc cDesc cSparse n k
        epsilon quota t events _ event hquota hprefix
        hrebuildAt hmodel hhistory

/-- Whole-model-quota specialization retained for the original T1 charging
and version-coding API. -/
theorem t1RunFromEvents_model_spec
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon quota t
      (events : List T1MarkEvent),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      quota = 2 ^ (k - epsilon) →
      events <+: t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t →
      T1RunModelInvariant cSparse n k epsilon quota
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events) := by
  intro cDesc
  obtain ⟨c0, cSparse, hmodel⟩ :=
    t1RunFromEvents_model_spec_of_quota_pos V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon quota t events hc0 hepsilon hkn hquota hprefix
  apply hmodel n k epsilon quota t events hc0 hepsilon hkn
  · rw [hquota]
    exact Nat.two_pow_pos _
  · exact hprefix

/-- For suitable constants and a positive quota, the run on any prefix of the marking events
satisfies the core invariant. -/
theorem t1RunFromEvents_core_spec_of_quota_pos
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon quota t
      (events : List T1MarkEvent),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      0 < quota →
      events <+: t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t →
      T1RunCoreInvariant cSparse n k epsilon quota events
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events) := by
  intro cDesc
  obtain ⟨c0, cSparse, hmodel⟩ :=
    t1RunFromEvents_model_spec_of_quota_pos V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon quota t events hc0 hepsilon hkn hquota hprefix
  refine ⟨hmodel n k epsilon quota t events hc0 hepsilon hkn
    hquota hprefix, t1RunFromEvents_history
      cSparse n k epsilon quota events, ?_⟩
  constructor
  · apply t1RunFromEvents_preserves_versions_length
    simp [t1InitialRunState]
  · apply t1RunFromEvents_preserves_versions_last
    simp [t1InitialRunState]

/-- Whole-model-quota specialization of
`t1RunFromEvents_core_spec_of_quota_pos`. -/
theorem t1RunFromEvents_core_spec
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon quota t
      (events : List T1MarkEvent),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      quota = 2 ^ (k - epsilon) →
      events <+: t1MarkingEventStage c n k epsilon
        (epsilon + logSlack cDesc n) t →
      T1RunCoreInvariant cSparse n k epsilon quota events
        (t1RunFromEvents cSparse n k epsilon quota
          (t1InitialRunState n k epsilon) events) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t1RunFromEvents_core_spec_of_quota_pos V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon quota t events hc0 hepsilon hkn hquota hprefix
  apply hcore n k epsilon quota t events hc0 hepsilon hkn
  · rw [hquota]
    exact Nat.two_pow_pos _
  · exact hprefix

/-- For suitable constants, the run at stage `t` with quota `2 ^ (k - epsilon)` satisfies the core
invariant for the events of that stage. -/
theorem t1RunAt_core_spec
    (V : Map) (c : Code) (hc : IsCodeFor c V) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon quota t,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      quota = 2 ^ (k - epsilon) →
      T1RunCoreInvariant cSparse n k epsilon quota
        (t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t)
        (t1RunAt c cDesc cSparse n k epsilon quota t) := by
  intro cDesc
  obtain ⟨c0, cSparse, hcore⟩ :=
    t1RunFromEvents_core_spec V c hc cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon quota t hc0 hepsilon hkn hquota
  exact hcore n k epsilon quota t _ hc0 hepsilon hkn hquota
    (List.prefix_refl _)

end Kolmogorov
