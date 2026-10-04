import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part03
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run

/-!
# Structural semantics of the executable `t1` run

The state stores only length-`n` marks.  Consequently the exact event-history
statements below explicitly include `x.length = n`; omitting this guard would
make the statements false for models that also contain strings of other
lengths.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Exact histories of the four marking streams.  The two `C` histories are
kept separately in the state, while `cMarked` records precisely the points
whose code has appeared in both histories, independently of arrival order. -/
def T1RunHistoryInvariant (n : Nat)
    (events : List T1MarkEvent) (s : T1RunState) : Prop :=
  (∀ x, x ∈ s.bMarked.toFinset ↔
    x.length = n ∧
      ∃ w, .bSet w ∈ events ∧ x ∈ t1CodeToSet w) ∧
  (∀ x, x ∈ s.cMarked.toFinset ↔
    x.length = n ∧
      ∃ w batch, .cPrimeModel w ∈ events ∧
        .cDoublePrimeBatch batch ∈ events ∧
        w ∈ batch ∧ x ∈ t1CodeToSet w) ∧
  (∀ x, x ∈ s.dMarked.toFinset ↔
    x.length = n ∧ .dString x ∈ events) ∧
  (∀ w, w ∈ s.seenCPrime ↔ .cPrimeModel w ∈ events) ∧
  (∀ w, w ∈ s.seenCDouble ↔
    ∃ batch, .cDoublePrimeBatch batch ∈ events ∧ w ∈ batch)

/-- The model-theoretic part of the reachable-run invariant. -/
def T1RunModelInvariant (cSparse n k epsilon quota : Nat)
    (s : T1RunState) : Prop :=
  s.current.Nodup ∧
  s.current.length = 2 ^ (k - epsilon) ∧
  s.current.toFinset ⊆ stringsOfLength n ∧
  Disjoint s.current.toFinset s.bMarked.toFinset ∧
  (s.current.toFinset ∩
    (s.cMarked.toFinset ∪ s.dMarked.toFinset)).card < quota ∧
  (∀ code ∈ s.seenCDouble,
    (s.current.toFinset ∩ t1CodeToSet code).card ≤
      cSparse * n + cSparse)

/-- The complete structural invariant, including exact histories and the
version-counter contract. -/
def T1RunCoreInvariant (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) (s : T1RunState) : Prop :=
  T1RunModelInvariant cSparse n k epsilon quota s ∧
  T1RunHistoryInvariant n events s ∧
  s.versions.length = s.external + s.saturation + 1 ∧
  s.versions.getD (s.versions.length - 1) [] = s.current

/-- Exact histories depend only on the five marking-data fields of the run
state. -/
theorem t1RunHistoryInvariant_congr
    {n : Nat} {events : List T1MarkEvent} {s s' : T1RunState}
    (hdata : T1RunMarkingDataEq s s') :
    T1RunHistoryInvariant n events s ↔
      T1RunHistoryInvariant n events s' := by
  rcases hdata with ⟨hb, hc, hd, hcp, hcd⟩
  unfold T1RunHistoryInvariant
  rw [hb, hc, hd, hcp, hcd]

/-- If a `C'` code arrives after it was already visible in `C''`, exactly its
length-`n` points are activated. -/
theorem t1_cMarked_history_cDouble_first
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w x : BitString) :
    x ∈ (t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)).cMarked.toFinset ↔
      x ∈ s.cMarked.toFinset ∨
        (w ∈ s.seenCDouble ∧ x.length = n ∧
          x ∈ t1CodeToSet w) := by
  by_cases hw : w ∈ s.seenCDouble
  · rw [(t1RunStep_cPrime_history
      cSparse n k epsilon quota s w).2.1 hw |>.1]
    simp [hw, canonicalPointListOfCode, t1CodeToSet]
    tauto
  · rw [(t1RunStep_cPrime_history
      cSparse n k epsilon quota s w).2.2 hw |>.1]
    simp [hw]

/-- If a `C''` batch arrives after matching `C'` codes were already visible,
exactly the length-`n` points of those matching codes are activated. -/
theorem t1_cMarked_history_cPrime_first
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) (x : BitString) :
    x ∈ (t1RunStep cSparse n k epsilon quota s
      (.cDoublePrimeBatch batch)).cMarked.toFinset ↔
      x ∈ s.cMarked.toFinset ∨
        (x.length = n ∧
          ∃ w, w ∈ batch ∧ w ∈ s.seenCPrime ∧
            x ∈ t1CodeToSet w) := by
  rw [(t1RunStep_cDouble_history
    cSparse n k epsilon quota s batch).1]
  simp only [List.toFinset_append, Finset.mem_union,
    List.mem_toFinset, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq]
  simp [canonicalPointListOfCode, t1CodeToSet]
  aesop

@[simp] private theorem t1_cPrime_ne_bSet (a b : BitString) :
    T1MarkEvent.cPrimeModel a ≠ .bSet b := by
  intro h
  cases h

@[simp] private theorem t1_cDouble_ne_bSet
    (a : List BitString) (b : BitString) :
    T1MarkEvent.cDoublePrimeBatch a ≠ .bSet b := by
  intro h
  cases h

@[simp] private theorem t1_dString_ne_bSet (a b : BitString) :
    T1MarkEvent.dString a ≠ .bSet b := by
  intro h
  cases h

@[simp] private theorem t1_bSet_ne_cDouble
    (a : BitString) (b : List BitString) :
    T1MarkEvent.bSet a ≠ .cDoublePrimeBatch b := by
  intro h
  cases h

@[simp] private theorem t1_cPrime_ne_cDouble
    (a : BitString) (b : List BitString) :
    T1MarkEvent.cPrimeModel a ≠ .cDoublePrimeBatch b := by
  intro h
  cases h

@[simp] private theorem t1_dString_ne_cDouble
    (a : BitString) (b : List BitString) :
    T1MarkEvent.dString a ≠ .cDoublePrimeBatch b := by
  intro h
  cases h

@[simp] private theorem t1_bSet_ne_cPrime (a b : BitString) :
    T1MarkEvent.bSet a ≠ .cPrimeModel b := by
  intro h
  cases h

@[simp] private theorem t1_cDouble_ne_cPrime
    (a : List BitString) (b : BitString) :
    T1MarkEvent.cDoublePrimeBatch a ≠ .cPrimeModel b := by
  intro h
  cases h

@[simp] private theorem t1_dString_ne_cPrime (a b : BitString) :
    T1MarkEvent.dString a ≠ .cPrimeModel b := by
  intro h
  cases h

@[simp] private theorem t1_bSet_ne_dString (a b : BitString) :
    T1MarkEvent.bSet a ≠ .dString b := by
  intro h
  cases h

@[simp] private theorem t1_cPrime_ne_dString (a b : BitString) :
    T1MarkEvent.cPrimeModel a ≠ .dString b := by
  intro h
  cases h

@[simp] private theorem t1_cDouble_ne_dString
    (a : List BitString) (b : BitString) :
    T1MarkEvent.cDoublePrimeBatch a ≠ .dString b := by
  intro h
  cases h

private theorem t1RunStep_bSet_preserves_history
    (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (w : BitString)
    (h : T1RunHistoryInvariant n events s) :
    T1RunHistoryInvariant n (events ++ [.bSet w])
      (t1RunStep cSparse n k epsilon quota s (.bSet w)) := by
  rcases h with ⟨hb, hc, hd, hcp, hcd⟩
  have hcMarked :
      (t1RunStep cSparse n k epsilon quota s
        (.bSet w)).cMarked = s.cMarked := by rfl
  have hdMarked :
      (t1RunStep cSparse n k epsilon quota s
        (.bSet w)).dMarked = s.dMarked := by rfl
  have hseenCPrime :
      (t1RunStep cSparse n k epsilon quota s
        (.bSet w)).seenCPrime = s.seenCPrime := by rfl
  have hseenCDouble :
      (t1RunStep cSparse n k epsilon quota s
        (.bSet w)).seenCDouble = s.seenCDouble := by rfl
  have hpoint (code x : BitString) :
      x ∈ canonicalPointListOfCode code ↔
        x ∈ t1CodeToSet code := by
    unfold canonicalPointListOfCode t1CodeToSet
    exact mem_canonicalFinsetList
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [(t1RunStep_bSet_history
      cSparse n k epsilon quota s w).1,
      List.toFinset_append, Finset.mem_union, hb x]
    simp only [List.mem_append, List.mem_singleton]
    simp only [List.toFinset_filter, decide_eq_true_eq,
      Finset.mem_filter, List.mem_toFinset,
      T1MarkEvent.bSet.injEq, hpoint]
    constructor
    · rintro (⟨hlen, u, hu, hxu⟩ | ⟨hxw, hlen⟩)
      · exact ⟨hlen, u, Or.inl hu, hxu⟩
      · exact ⟨hlen, w, Or.inr rfl, hxw⟩
    · rintro ⟨hlen, u, hu | rfl, hxu⟩
      · exact Or.inl ⟨hlen, u, hu, hxu⟩
      · exact Or.inr ⟨hxu, hlen⟩
  · intro x
    rw [hcMarked, hc x]
    simp
  · intro x
    rw [hdMarked, hd x]
    simp
  · intro code
    rw [hseenCPrime, hcp code]
    simp
  · intro code
    rw [hseenCDouble, hcd code]
    simp

private theorem t1RunStep_cDouble_preserves_history
    (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (batch : List BitString)
    (h : T1RunHistoryInvariant n events s) :
    T1RunHistoryInvariant n
      (events ++ [.cDoublePrimeBatch batch])
      (t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch)) := by
  rcases h with ⟨hb, hc, hd, hcp, hcd⟩
  have hbMarked :
      (t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch)).bMarked = s.bMarked := by rfl
  have hdMarked :
      (t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch)).dMarked = s.dMarked := by rfl
  have hseenCPrime :
      (t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch)).seenCPrime =
          s.seenCPrime := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hbMarked, hb x]
    simp
  · intro x
    rw [t1_cMarked_history_cPrime_first
      cSparse n k epsilon quota s batch x, hc x]
    simp only [List.mem_append, List.mem_singleton]
    simp [hcp]
    aesop
  · intro x
    rw [hdMarked, hd x]
    simp
  · intro code
    rw [hseenCPrime, hcp code]
    simp
  · intro code
    rw [t1RunStep_cDouble_seen
      cSparse n k epsilon quota s batch,
      List.mem_append, hcd code]
    constructor
    · rintro (⟨oldBatch, hold, hmem⟩ | hmem)
      · exact ⟨oldBatch, List.mem_append.mpr (Or.inl hold), hmem⟩
      · exact ⟨batch, List.mem_append.mpr (Or.inr (by simp)), hmem⟩
    · rintro ⟨oldBatch, hold, hmem⟩
      rcases List.mem_append.mp hold with hold | hold
      · exact Or.inl ⟨oldBatch, hold, hmem⟩
      · have heq : oldBatch = batch := by simpa using hold
        subst oldBatch
        exact Or.inr hmem

private theorem t1RunStep_cPrime_preserves_history
    (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (w : BitString)
    (h : T1RunHistoryInvariant n events s) :
    T1RunHistoryInvariant n (events ++ [.cPrimeModel w])
      (t1RunStep cSparse n k epsilon quota s
        (.cPrimeModel w)) := by
  rcases h with ⟨hb, hc, hd, hcp, hcd⟩
  obtain ⟨hbMarked, hdMarked, hseenCDouble⟩ :=
    t1RunStep_cPrime_unchanged_histories
      cSparse n k epsilon quota s w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hbMarked, hb x]
    simp
  · intro x
    rw [t1_cMarked_history_cDouble_first
      cSparse n k epsilon quota s w x, hc x]
    simp only [List.mem_append, List.mem_singleton]
    simp [hcd]
    aesop
  · intro x
    rw [hdMarked, hd x]
    simp
  · intro code
    rw [t1RunStep_cPrime_seen
      cSparse n k epsilon quota s w,
      List.mem_append, hcp code]
    simp
  · intro code
    rw [hseenCDouble, hcd code]
    simp

private theorem t1RunStep_dString_preserves_history
    (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (w : BitString)
    (h : T1RunHistoryInvariant n events s) :
    T1RunHistoryInvariant n (events ++ [.dString w])
      (t1RunStep cSparse n k epsilon quota s
        (.dString w)) := by
  rcases h with ⟨hb, hc, hd, hcp, hcd⟩
  obtain ⟨hbMarked, hcMarked, hseenCPrime, hseenCDouble⟩ :=
    t1RunStep_dString_unchanged_histories
      cSparse n k epsilon quota s w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hbMarked, hb x]
    simp
  · intro x
    rw [hcMarked, hc x]
    simp
  · intro x
    rw [(t1RunStep_dString_history
      cSparse n k epsilon quota s w).1,
      List.toFinset_append, Finset.mem_union, hd x]
    simp only [List.mem_append, List.mem_singleton]
    by_cases hw : w.length = n
    · simp only [List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false,
        T1MarkEvent.dString.injEq, hw, ite_true]
      constructor
      · rintro (⟨hxn, hold⟩ | hxw)
        · exact ⟨hxn, Or.inl hold⟩
        · subst x
          exact ⟨hw, Or.inr rfl⟩
      · rintro ⟨hxn, hold | hxw⟩
        · exact Or.inl ⟨hxn, hold⟩
        · exact Or.inr hxw
    · simp only [List.mem_toFinset, List.not_mem_nil, or_false,
        T1MarkEvent.dString.injEq, hw, ite_false]
      constructor
      · rintro ⟨hxn, hold⟩
        exact ⟨hxn, Or.inl hold⟩
      · rintro ⟨hxn, hold | hxw⟩
        · exact ⟨hxn, hold⟩
        · subst x
          exact (hw hxn).elim
  · intro code
    rw [hseenCPrime, hcp code]
    simp
  · intro code
    rw [hseenCDouble, hcd code]
    simp

/-- Exact event histories are preserved by one transition. -/
theorem t1RunStep_preserves_history
    (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) (s : T1RunState)
    (event : T1MarkEvent)
    (h : T1RunHistoryInvariant n events s) :
    T1RunHistoryInvariant n (events ++ [event])
      (t1RunStep cSparse n k epsilon quota s event) := by
  cases event with
  | bSet w =>
      exact t1RunStep_bSet_preserves_history
        cSparse n k epsilon quota events s w h
  | cDoublePrimeBatch batch =>
      exact t1RunStep_cDouble_preserves_history
        cSparse n k epsilon quota events s batch h
  | cPrimeModel w =>
      exact t1RunStep_cPrime_preserves_history
        cSparse n k epsilon quota events s w h
  | dString w =>
      exact t1RunStep_dString_preserves_history
        cSparse n k epsilon quota events s w h

/-- The initial T1 run state satisfies the history invariant for the empty event list. -/
theorem t1InitialRunState_history
    (n k epsilon : Nat) :
    T1RunHistoryInvariant n [] (t1InitialRunState n k epsilon) := by
  simp [T1RunHistoryInvariant, t1InitialRunState]

/-- The state reached from the initial state by a list of events satisfies the history invariant for
that list. -/
theorem t1RunFromEvents_history
    (cSparse n k epsilon quota : Nat)
    (events : List T1MarkEvent) :
    T1RunHistoryInvariant n events
      (t1RunFromEvents cSparse n k epsilon quota
        (t1InitialRunState n k epsilon) events) := by
  induction events using List.reverseRecOn with
  | nil =>
      simpa [t1RunFromEvents] using
        t1InitialRunState_history n k epsilon
  | append_singleton events event ih =>
      rw [t1RunFromEvents_append]
      exact t1RunStep_preserves_history
        cSparse n k epsilon quota events _ event ih

/-- The model invariant holds in the initial state for every positive
saturation quota.  The current marked intersection is initially empty, so the
quota need not equal the model size. -/
theorem t1InitialRunState_model_of_quota_pos
    (cSparse n k epsilon quota : Nat)
    (hepsilon : epsilon ≤ k) (hkn : k ≤ n)
    (hquota : 0 < quota) :
    T1RunModelInvariant cSparse n k epsilon quota
      (t1InitialRunState n k epsilon) := by
  unfold T1RunModelInvariant
  refine ⟨t1InitialCurrent_nodup n k epsilon,
    t1InitialCurrent_length hepsilon hkn,
    t1InitialCurrent_subset_stringsOfLength n k epsilon,
    ?_, ?_, ?_⟩
  · simp [t1InitialRunState]
  · simpa [t1InitialRunState] using hquota
  · simp [t1InitialRunState]

/-- Original whole-model-quota specialization of
`t1InitialRunState_model_of_quota_pos`. -/
theorem t1InitialRunState_model
    (cSparse n k epsilon quota : Nat)
    (hepsilon : epsilon ≤ k) (hkn : k ≤ n)
    (hquota : quota = 2 ^ (k - epsilon)) :
    T1RunModelInvariant cSparse n k epsilon quota
      (t1InitialRunState n k epsilon) := by
  apply t1InitialRunState_model_of_quota_pos cSparse n k epsilon quota
    hepsilon hkn
  rw [hquota]
  exact Nat.two_pow_pos _

/-- Every event of a marking stage already occurs among the events produced up to some earlier time.
Every event of a marking stage already occurs among the events produced up to some earlier time. -/
theorem t1MarkingEventStage_mem_origin
    (c : Code) (n k epsilon d t : Nat) (event : T1MarkEvent)
    (h : event ∈ t1MarkingEventStage c n k epsilon d t) :
    ∃ u ≤ t, event ∈ t1MarkingEventsUpToTime c n k epsilon d u := by
  induction t with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      exact (t1_mem_eraseDups_event (event := event)).mp h
  | succ t ih =>
      have hmem :
          event ∈ t1MarkingEventStage c n k epsilon d t ∨
            event ∈ t1MarkingEventsUpToTime c n k epsilon d (t + 1) := by
        exact List.mem_append.mp
          ((t1_mem_eraseDups_event (event := event)).mp h)
      rcases hmem with hold | hnew
      · obtain ⟨u, hu, hevent⟩ := ih hold
        exact ⟨u, hu.trans (Nat.le_succ t), hevent⟩
      · exact ⟨t + 1, le_rfl, hnew⟩

/-- Every string marked along a prefix of the marking events is genuinely B-, C- or D-marked. -/
theorem t1RunHistory_marked_sound_of_prefix
    (V : Map) (c : Code) (hc : IsCodeFor c V)
    (n k epsilon d t : Nat) (events : List T1MarkEvent) (s : T1RunState)
    (hp : events <+: t1MarkingEventStage c n k epsilon d t)
    (hh : T1RunHistoryInvariant n events s) :
    ∀ x ∈ (t1RunMarked s).toFinset,
      T1BMarked V n epsilon x ∨
      (∃ d', T1CMarked V n k d' x) ∨
      T1DMarked V n k x := by
  intro x hx
  rw [t1RunMarked_toFinset] at hx
  simp only [Finset.mem_union] at hx
  rcases hh with ⟨hb, hcMarked, hd, _hcp, _hcd⟩
  rcases hx with (hxb | hxc) | hxd
  · obtain ⟨hlen, w, hwevent, hxw⟩ := (hb x).mp hxb
    have hstage :
        T1MarkEvent.bSet w ∈
          t1MarkingEventStage c n k epsilon d t :=
      hp.subset hwevent
    obtain ⟨u, _hu, horigin⟩ :=
      t1MarkingEventStage_mem_origin
        c n k epsilon d t (.bSet w) hstage
    have hw : w ∈ t1BStage c n epsilon u := by
      simpa [t1MarkingEventsUpToTime] using horigin
    exact Or.inl (t1BStage_member_marked hc hw hxw hlen)
  · obtain ⟨hlen, w, batch, hprime, hdouble, hwbatch, hxw⟩ :=
      (hcMarked x).mp hxc
    have hprimeStage :
        T1MarkEvent.cPrimeModel w ∈
          t1MarkingEventStage c n k epsilon d t :=
      hp.subset hprime
    have hdoubleStage :
        T1MarkEvent.cDoublePrimeBatch batch ∈
          t1MarkingEventStage c n k epsilon d t :=
      hp.subset hdouble
    obtain ⟨uPrime, _huPrime, hprimeOrigin⟩ :=
      t1MarkingEventStage_mem_origin
        c n k epsilon d t (.cPrimeModel w) hprimeStage
    obtain ⟨uDouble, _huDouble, hdoubleOrigin⟩ :=
      t1MarkingEventStage_mem_origin
        c n k epsilon d t (.cDoublePrimeBatch batch) hdoubleStage
    have hwPrime : w ∈ t1CPrimeStage c k uPrime := by
      simpa [t1MarkingEventsUpToTime] using hprimeOrigin
    have hbatch :
        batch ∈ t1CDoublePrimeBatches c n k d uDouble := by
      simpa [t1MarkingEventsUpToTime] using hdoubleOrigin
    exact Or.inr (Or.inl ⟨d,
      t1CStreams_member_marked hc hwPrime hbatch hwbatch hxw hlen⟩)
  · obtain ⟨_hlen, hdevent⟩ := (hd x).mp hxd
    have hstage :
        T1MarkEvent.dString x ∈
          t1MarkingEventStage c n k epsilon d t :=
      hp.subset hdevent
    obtain ⟨u, _hu, horigin⟩ :=
      t1MarkingEventStage_mem_origin
        c n k epsilon d t (.dString x) hstage
    have hxStage : x ∈ t1DStage c n k u := by
      simpa [t1MarkingEventsUpToTime] using horigin
    exact Or.inr (Or.inr (t1DStage_member_marked hc hxStage))

/-- The C''-codes recorded along a prefix of the marking events all come from the enumerated
C''-batches. -/
theorem t1RunHistory_seenCDouble_subset_of_prefix
    (c : Code) (n k epsilon d t : Nat) (events : List T1MarkEvent) (s : T1RunState)
    (hp : events <+: t1MarkingEventStage c n k epsilon d t)
    (hh : T1RunHistoryInvariant n events s) :
    s.seenCDouble.toFinset ⊆
      (t1CDoublePrimeBatches c n k d t).flatten.toFinset := by
  intro w hw
  have hwSeen : w ∈ s.seenCDouble := List.mem_toFinset.mp hw
  obtain ⟨batch, hbatchEvent, hwbatch⟩ := (hh.2.2.2.2 w).mp hwSeen
  have hstage :
      T1MarkEvent.cDoublePrimeBatch batch ∈
        t1MarkingEventStage c n k epsilon d t :=
    hp.subset hbatchEvent
  obtain ⟨u, hu, horigin⟩ :=
    t1MarkingEventStage_mem_origin
      c n k epsilon d t (.cDoublePrimeBatch batch) hstage
  have hbatchU :
      batch ∈ t1CDoublePrimeBatches c n k d u := by
    simpa [t1MarkingEventsUpToTime] using horigin
  have hprefix :
      t1CDoublePrimeBatches c n k d u <+:
        t1CDoublePrimeBatches c n k d t :=
    t1CDoublePrimeBatches_mono c n k d hu
  rw [List.mem_toFinset, List.mem_flatten]
  exact ⟨batch, hprefix.subset hbatchU, hwbatch⟩

end Kolmogorov
