import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.StatePrimrec
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Transitions
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Computable
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Histories

/-!
# Semantics of the run: what each event does

The exact transition equations of the T1 marking run.  For each kind of event there is a
`_markingDataEq` lemma — `t1RunStep_bSet_markingDataEq`,
`t1RunStep_cDouble_markingDataEq`, the two `C'` cases and
`t1RunStep_dString_markingDataEq` — saying that the step changes the marking data exactly as
the prepared state describes, and `t1RunStep_cPrime_seen` and `t1RunStep_cDouble_seen` record
what is appended to the seen lists.

`t1RunFromEvents_append` replays an event list one step at a time, and the three prefix lemmas
`t1RunStep_versions_prefix`, `t1RunFromEvents_versions_prefix` and `t1RunAt_versions_prefix`
say the version list only ever grows.  `t1RunRebuild_current_spec` describes the candidate
list after a rebuild: duplicate-free, unmarked, of the required length.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Replaying a list of events with one more event at the end is one further step
from the replayed state. -/
theorem t1RunFromEvents_append
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) (event : T1MarkEvent) :
    t1RunFromEvents cSparse n k epsilon quota s (events ++ [event]) =
      t1RunStep cSparse n k epsilon quota
        (t1RunFromEvents cSparse n k epsilon quota s events) event := by
  simp [t1RunFromEvents, List.foldl_append]

/-- One step only appends to the list of candidate-list versions. -/
theorem t1RunStep_versions_prefix
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (event : T1MarkEvent) :
    s.versions <+:
      (t1RunStep cSparse n k epsilon quota s event).versions := by
  rcases t1RunStep_versions cSparse n k epsilon quota s event with h | h
  · rw [h.2]
  · rw [h.2]
    exact List.prefix_append _ _

/-- Replaying events only appends to the list of candidate-list versions. -/
theorem t1RunFromEvents_versions_prefix
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) :
    s.versions <+:
      (t1RunFromEvents cSparse n k epsilon quota s events).versions := by
  induction events generalizing s with
  | nil =>
      exact List.prefix_refl _
  | cons event events ih =>
      exact (t1RunStep_versions_prefix cSparse n k epsilon quota s event).trans
        (ih (t1RunStep cSparse n k epsilon quota s event))

/-- The version list of the run at an earlier time is a prefix of the one at a later
time. -/
theorem t1RunAt_versions_prefix (c : Nat.Partrec.Code) (cDesc cSparse n k epsilon quota : Nat)
    {t t' : Nat} (htt' : t ≤ t') :
    (t1RunAt c cDesc cSparse n k epsilon quota t).versions <+:
      (t1RunAt c cDesc cSparse n k epsilon quota t').versions := by
  have hEvents :=
    t1MarkingEventStage_mono c n k epsilon
      (epsilon + logSlack cDesc n) htt'
  obtain ⟨tail, htail⟩ := hEvents
  unfold t1RunAt
  rw [← htail]
  simpa only [t1RunFromEvents, List.foldl_append] using
    (t1RunFromEvents_versions_prefix cSparse n k epsilon quota
      (t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon)
        (t1MarkingEventStage c n k epsilon
          (epsilon + logSlack cDesc n) t))
      tail)

/-- A `B`-set event changes the marking data exactly as the prepared state
describes. -/
theorem t1RunStep_bSet_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    T1RunMarkingDataEq (t1RunBSetPrepared n s w)
      (t1RunStep cSparse n k epsilon quota s (.bSet w)) := by
  rw [t1RunStep_bSet_eq]
  simpa [T1RunMarkingDataEq] using
    t1RunRebuild_markingDataEq cSparse n k epsilon
      (t1RunBSetPrepared n s w)

/-- A `C''`-portion event changes the marking data exactly as the prepared state
describes. -/
theorem t1RunStep_cDouble_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    T1RunMarkingDataEq (t1RunCDoublePrepared n s batch)
      (t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch)) := by
  rw [t1RunStep_cDouble_eq]
  simpa [T1RunMarkingDataEq] using
    t1RunRebuild_markingDataEq cSparse n k epsilon
      (t1RunCDoublePrepared n s batch)

/-- A `C'` event on a model not yet seen in `C''` changes the marking data as the
corresponding prepared state describes. -/
theorem t1RunStep_cPrime_seen_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString)
    (hactive : w ∉ s.seenCDouble) :
    T1RunMarkingDataEq (t1RunCPrimeSeenPrepared s w)
      (t1RunStep cSparse n k epsilon quota s
        (.cPrimeModel w)) := by
  rw [t1RunStep_cPrime_eq]
  simp [hactive, T1RunMarkingDataEq]

/-- A `C'` event on a model already seen in `C''` changes the marking data as the
corresponding prepared state describes. -/
theorem t1RunStep_cPrime_active_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString)
    (hactive : w ∈ s.seenCDouble) :
    T1RunMarkingDataEq (t1RunCPrimePrepared n s w)
      (t1RunStep cSparse n k epsilon quota s
        (.cPrimeModel w)) := by
  rw [t1RunStep_cPrime_eq]
  simp only [hactive, ite_true]
  split
  · simpa [T1RunMarkingDataEq] using
      t1RunRebuild_markingDataEq cSparse n k epsilon
        (t1RunCPrimePrepared n s w)
  · exact T1RunMarkingDataEq.refl _

/-- A `D`-string event changes the marking data exactly as the prepared state
describes. -/
theorem t1RunStep_dString_markingDataEq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (x : BitString) :
    T1RunMarkingDataEq (t1RunDPrepared n s x)
      (t1RunStep cSparse n k epsilon quota s
        (.dString x)) := by
  rw [t1RunStep_dString_eq]
  by_cases hsat :
      t1RunSaturated (t1RunDPrepared n s x) quota = true
  · simp only [hsat, ite_true]
    simpa [T1RunMarkingDataEq] using
      t1RunRebuild_markingDataEq cSparse n k epsilon
        (t1RunDPrepared n s x)
  · simp only [Bool.not_eq_true] at hsat
    simp [hsat, T1RunMarkingDataEq]

/-- After a rebuild the candidate list has no repetitions and consists of unmarked
strings of length `n`. -/
theorem t1RunRebuild_current_spec
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    (t1RunRebuild cSparse n k epsilon s).current.Nodup ∧
      (t1RunRebuild cSparse n k epsilon s).current.toFinset ⊆
        stringsOfLength n \ (t1RunMarked s).toFinset := by
  have hsub :
      List.Sublist
        (t1RunRebuild cSparse n k epsilon s).current
        (t1RunUnmarked n s) := by
    exact t1SparseSubsetSelectorList_sublist
      (t1RunUnmarked n s)
      (s.seenCDouble.map canonicalPointListOfCode)
      (2 ^ (k - epsilon)) (cSparse * n + cSparse)
  constructor
  · exact hsub.nodup (t1RunUnmarked_nodup n s)
  · have hfinset :
        (t1RunRebuild cSparse n k epsilon s).current.toFinset ⊆
          (t1RunUnmarked n s).toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      exact hsub.subset hx
    rwa [t1RunUnmarked_toFinset] at hfinset

/-- A `C'` event appends its model to the list of models seen in `C'`. -/
theorem t1RunStep_cPrime_seen
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    (t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)).seenCPrime = s.seenCPrime ++ [w] := by
  exact (t1RunStep_cPrime_history
    cSparse n k epsilon quota s w).1

/-- A `C''` event appends its whole portion to the list of models seen in `C''`. -/
theorem t1RunStep_cDouble_seen
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    (t1RunStep cSparse n k epsilon quota s
      (.cDoublePrimeBatch batch)).seenCDouble =
        s.seenCDouble ++ batch := by
  exact (t1RunStep_cDouble_history
    cSparse n k epsilon quota s batch).2.1

/-- One step preserves the invariant that the number of versions is one more than
the number of external and saturation rebuilds. -/
theorem t1RunStep_preserves_versions_length
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hversions :
      s.versions.length = s.external + s.saturation + 1) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    s'.versions.length = s'.external + s'.saturation + 1 := by
  dsimp only
  rcases t1RunStep_versions cSparse n k epsilon quota s event with
    hsame | hrebuild
  · rw [hsame.2, hsame.1, hversions]
  · rw [hrebuild.2, List.length_append, hrebuild.1, hversions]
    simp

private theorem t1GetD_append_singleton_last
    (versions : List (List BitString)) (current : List BitString) :
    (versions ++ [current]).getD
        ((versions ++ [current]).length - 1) [] =
      current := by
  rw [List.getD_append_right]
  · simp
  · simp

/-- One step preserves the invariant that the last version is the current candidate
list. -/
theorem t1RunStep_preserves_versions_last
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hlast :
      s.versions.getD (s.versions.length - 1) [] =
        s.current) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    s'.versions.getD (s'.versions.length - 1) [] =
      s'.current := by
  dsimp only
  rcases t1RunStep_versions cSparse n k epsilon quota s event with
    hsame | hrebuild
  · have hcurrent :=
      t1RunStep_current_eq_of_versions_eq
        cSparse n k epsilon quota s event hsame.2
    rw [hsame.2, hcurrent]
    exact hlast
  · rw [hrebuild.2]
    exact t1GetD_append_singleton_last _ _

/-- Replaying events preserves the version-count invariant. -/
theorem t1RunFromEvents_preserves_versions_length
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent)
    (hversions :
      s.versions.length = s.external + s.saturation + 1) :
    let s' :=
      t1RunFromEvents cSparse n k epsilon quota s events
    s'.versions.length = s'.external + s'.saturation + 1 := by
  induction events generalizing s with
  | nil =>
      simpa [t1RunFromEvents] using hversions
  | cons event events ih =>
      exact ih
        (t1RunStep cSparse n k epsilon quota s event)
        (t1RunStep_preserves_versions_length
          cSparse n k epsilon quota s event hversions)

/-- Replaying events preserves the invariant that the last version is the current
candidate list. -/
theorem t1RunFromEvents_preserves_versions_last
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent)
    (hlast :
      s.versions.getD (s.versions.length - 1) [] =
        s.current) :
    let s' :=
      t1RunFromEvents cSparse n k epsilon quota s events
    s'.versions.getD (s'.versions.length - 1) [] =
      s'.current := by
  induction events generalizing s with
  | nil =>
      simpa [t1RunFromEvents] using hlast
  | cons event events ih =>
      exact ih
        (t1RunStep cSparse n k epsilon quota s event)
        (t1RunStep_preserves_versions_last
          cSparse n k epsilon quota s event hlast)

/-- In the run at time `t` the number of versions is one more than the number of
rebuilds. -/
theorem t1RunAt_versions_length
    (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon quota t : Nat) :
    let s :=
      t1RunAt c cDesc cSparse n k epsilon quota t
    s.versions.length = s.external + s.saturation + 1 := by
  apply t1RunFromEvents_preserves_versions_length
  simp [t1InitialRunState]

/-- In the run at time `t` the last version is the current candidate list. -/
theorem t1RunAt_versions_spec
    (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon quota t : Nat) :
    let s :=
      t1RunAt c cDesc cSparse n k epsilon quota t
    s.versions.length = s.external + s.saturation + 1 ∧
      s.versions.getD (s.versions.length - 1) [] =
        s.current := by
  constructor
  · exact t1RunAt_versions_length
      c cDesc cSparse n k epsilon quota t
  · apply t1RunFromEvents_preserves_versions_last
    simp [t1InitialRunState]

end Kolmogorov
