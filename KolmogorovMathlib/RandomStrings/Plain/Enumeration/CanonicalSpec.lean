/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Enumeration.Schedule

/-!
# Correctness of the canonical enumeration schedule

`KolmogorovMathlib.RandomStrings.Plain.Enumeration.Schedule` defines the common logical clock
`masterState` on which the plain decompressor `V` and the conditional prefix decompressor `D`
are enumerated, together with the objects read off it: the events `eventAt`, the finite output
sets `stageOutputs`, the candidate test `validCandidate`, the search `findEmission` and the
finite prefix minimum `stagePrefixComplexity`. This module proves that these finite objects
describe the semantics of `V` and `D` exactly (blueprint node `lem:stage-api`).

* `canonical_enumeration_spec_sound`, `canonical_enumeration_spec_complete`,
  `canonical_enumeration_spec_queue`, `canonical_enumeration_spec_unique` and
  `canonical_enumeration_spec_position` say that the emitted events are exactly the halting
  `V` computations, that every queued event is emitted at a later tick, that a program is
  emitted at most once, and where an event sits in the history.
* `canonical_enumeration_spec_union` identifies the bounded-output predicate `Simple B.V x k`
  with membership in some finite set `E_{k,t}`.
* `canonical_enumeration_spec_search` and `canonical_enumeration_spec_search_eq` show that the
  emission tick of a halting program is found by a partial computable search, and
  `canonical_enumeration_spec_candidate` characterises the candidate records accepted by
  `validCandidate`.
* `canonical_enumeration_spec_prefix`, `canonical_enumeration_spec_prefix_min` and
  `canonical_enumeration_spec_prefix_bound` do the same for `D`: the observation table is
  sound and complete, and `stagePrefixComplexity` is a computable upper bound on `KP B.D`.

These facts are the interface used by the stability, accounting and marker modules, which
replay the schedule instead of reasoning about `V` and `D` directly.
-/

namespace Kolmogorov.Milovanov

private lemma isCodeFor_vCode (B : Base) : IsCodeFor B.vCode B.V := by
  unfold IsCodeFor
  rw [B.vCode_eq]
  rfl

private lemma isCodeFor_dCode (B : Base) : IsCodeFor B.dCode B.D := by
  unfold IsCodeFor
  rw [B.dCode_eq]
  rfl

/-- The V programs of the batch of tick `t + 1` that are neither queued nor emitted at tick
`t`. -/
private def freshEvents (B : Base) (t : ℕ) : List ProgramEvent :=
  (plainBatch B (t + 1)).filter (fun e => decide (e.1 ∉ (masterState B t).1.map Prod.fst ++
    (eventHistory B t).map (fun e => e.2.2.1)))

/-- The V events waiting at tick `t + 1`, before the head of the queue is emitted. -/
private def pendingEvents (B : Base) (t : ℕ) : List ProgramEvent :=
  (masterState B t).1 ++ freshEvents B t

/-- One master tick either leaves the queue and the history empty-handed, or emits the head of
the pending events at tick `t + 1` and keeps the rest as the new queue. -/
private lemma masterState_succ_cases (B : Base) (t : ℕ) :
    (pendingEvents B t = [] ∧ (masterState B (t + 1)).1 = [] ∧
      eventHistory B (t + 1) = eventHistory B t) ∨
    ∃ hd rest, pendingEvents B t = hd :: rest ∧ (masterState B (t + 1)).1 = rest ∧
      eventHistory B (t + 1) = eventHistory B t ++ [(t + 1, (eventHistory B t).length, hd)] := by
  unfold pendingEvents freshEvents eventHistory
  dsimp only [masterState, masterStep]
  split
  · rename_i h
    exact Or.inl ⟨h, rfl, rfl⟩
  · rename_i hd rest h
    exact Or.inr ⟨hd, rest, h, rfl, rfl⟩

/-- An event is present at a tick exactly when it is the last event of the history and was
emitted at that tick. -/
private lemma eventAt_eq_some_iff {B : Base} {t : ℕ} {e : TimedEvent} :
    eventAt B t = some e ↔ (eventHistory B t).getLast? = some e ∧ e.1 = t := by
  unfold eventAt
  cases (eventHistory B t).getLast? with
  | none => simp [Option.filter]
  | some v =>
    simp only [Option.filter, decide_eq_true_eq, Option.some.injEq]
    split_ifs with hv
    · exact ⟨fun h => ⟨Option.some.inj h, Option.some.inj h ▸ hv⟩, fun h => congrArg some h.1⟩
    · simp only [false_iff, not_and]
      rintro rfl
      exact hv

private lemma mem_eventHistory_of_eventAt {B : Base} {t : ℕ} {e : TimedEvent}
    (h : eventAt B t = some e) : e ∈ eventHistory B t :=
  List.mem_of_getLast? (eventAt_eq_some_iff.mp h).1

private lemma eventAt_eq_some_of_eventHistory_eq_append {B : Base} {t : ℕ} {l : List TimedEvent}
    {e : TimedEvent} (hl : eventHistory B t = l ++ [e]) (he : e.1 = t) : eventAt B t = some e :=
  eventAt_eq_some_iff.mpr ⟨by rw [hl, List.getLast?_concat], he⟩

private lemma time_le_of_mem_eventHistory {B : Base} {t : ℕ} {e : TimedEvent}
    (h : e ∈ eventHistory B t) : e.1 ≤ t := by
  induction t with
  | zero => simp [eventHistory, masterState] at h
  | succ t ih =>
    rcases masterState_succ_cases B t with ⟨-, -, h2⟩ | ⟨hd, rest, -, -, h2⟩
    · rw [h2] at h
      exact (ih h).trans t.le_succ
    · rw [h2, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact (ih h).trans t.le_succ
      · exact le_rfl

private lemma eventAt_eq_some_of_mem_eventHistory {B : Base} {t : ℕ} {e : TimedEvent}
    (h : e ∈ eventHistory B t) : eventAt B e.1 = some e := by
  induction t with
  | zero => simp [eventHistory, masterState] at h
  | succ t ih =>
    rcases masterState_succ_cases B t with ⟨-, -, h2⟩ | ⟨hd, rest, -, -, h2⟩
    · rw [h2] at h
      exact ih h
    · rw [h2, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact ih h
      · exact eventAt_eq_some_of_eventHistory_eq_append h2 rfl

private lemma produces_of_mem_plainBatch {B : Base} {t : ℕ} {e : ProgramEvent}
    (h : e ∈ plainBatch B t) : produces B.V e.1 [] e.2 := by
  unfold plainBatch at h
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact runOut_sound (isCodeFor_vCode B) hx

/-- Everything queued or emitted by the schedule is an actual `V` computation. -/
private lemma produces_of_mem_masterState (B : Base) (t : ℕ) :
    (∀ e ∈ (masterState B t).1, produces B.V e.1 [] e.2) ∧
      ∀ e ∈ eventHistory B t, produces B.V e.2.2.1 [] e.2.2.2 := by
  induction t with
  | zero => simp [masterState, eventHistory]
  | succ t ih =>
    have hpend : ∀ e ∈ pendingEvents B t, produces B.V e.1 [] e.2 := by
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact ih.1 e h
      · exact produces_of_mem_plainBatch (List.mem_filter.mp h).1
    rcases masterState_succ_cases B t with ⟨-, h1, h2⟩ | ⟨hd, rest, hp, h1, h2⟩
    · rw [h1, h2]
      exact ⟨by simp, ih.2⟩
    · rw [h1, h2]
      refine ⟨fun e he => hpend e (by rw [hp]; exact List.mem_cons_of_mem _ he), fun e he => ?_⟩
      rcases List.mem_append.mp he with h | h
      · exact ih.2 e h
      · rw [List.mem_singleton.mp h]
        exact hpend hd (by rw [hp]; exact List.mem_cons_self)

/-- Every event is an actual V computation, and its recorded timestamp is its emission tick.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_sound (B : Base) {t : ℕ} {e : TimedEvent}
    (h : eventAt B t = some e) : e.1 = t ∧ produces B.V e.2.2.1 [] e.2.2.2 :=
  ⟨(eventAt_eq_some_iff.mp h).2, (produces_of_mem_masterState B t).2 e
    (mem_eventHistory_of_eventAt h)⟩

/-- A program halts with output `x` exactly when `(p, x)` occurs in some batch of halting
programs. -/
private lemma produces_iff_exists_mem_plainBatch (B : Base) (p x : BitString) :
    produces B.V p [] x ↔ ∃ s, (p, x) ∈ plainBatch B s := by
  refine ⟨fun hp => ?_, fun ⟨_, hs⟩ => produces_of_mem_plainBatch hs⟩
  obtain ⟨n, hn⟩ := runOut_complete (isCodeFor_vCode B) hp
  refine ⟨max n (Encodable.encode p + 1), ?_⟩
  unfold plainBatch
  refine List.mem_filterMap.mpr ⟨p, ?_, by simp [runOut_mono (le_max_left _ _) hn]⟩
  refine List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨Encodable.encode p, ?_,
    Encodable.encodek p⟩)
  exact List.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))

/-- Two V events with the same program coincide, since a program has at most one output. -/
private lemma programEvent_eq_of_produces {B : Base} {e e' : ProgramEvent}
    (h : produces B.V e.1 [] e.2) (h' : produces B.V e'.1 [] e'.2) (h1 : e.1 = e'.1) :
    e = e' :=
  Prod.ext h1 (Part.mem_unique h (by rw [h1]; exact h'))

/-- Queued events cannot starve: every pending event eventually receives an emission tick.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_queue (B : Base) {s : ℕ} {e : ProgramEvent}
    (h : e ∈ (masterState B s).1) : ∃ t > s, ∃ i, eventAt B t = some (t, i, e) := by
  obtain ⟨pre, post, hq⟩ := List.mem_iff_append.mp h
  clear h
  induction pre generalizing s post with
  | nil =>
    rcases masterState_succ_cases B s with ⟨hp, -⟩ | ⟨hd, rest, hp, -, h2⟩
    · simp [pendingEvents, hq] at hp
    · simp only [pendingEvents, hq, List.nil_append, List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      exact ⟨s + 1, s.lt_succ_self, _, eventAt_eq_some_of_eventHistory_eq_append h2 rfl⟩
  | cons head tail ih =>
    rcases masterState_succ_cases B s with ⟨hp, -⟩ | ⟨hd, rest, hp, h1, -⟩
    · simp [pendingEvents, hq] at hp
    · simp only [pendingEvents, hq, List.cons_append, List.cons.injEq, List.append_assoc] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨t, ht, hi⟩ := ih (post ++ freshEvents B s) h1
      exact ⟨t, s.lt_succ_self.trans ht, hi⟩

/-- Every program of a batch is eventually emitted. -/
private lemma exists_eventAt_of_mem_plainBatch (B : Base) {s : ℕ} {e : ProgramEvent}
    (h : e ∈ plainBatch B s) : ∃ t i, eventAt B t = some (t, i, e) := by
  cases s with
  | zero => simp [plainBatch] at h
  | succ s =>
    obtain ⟨hq, hh⟩ := produces_of_mem_masterState B s
    have hsound := produces_of_mem_plainBatch h
    by_cases hhist : ∃ e' ∈ eventHistory B s, e'.2.2 = e
    · obtain ⟨e', he', rfl⟩ := hhist
      exact ⟨e'.1, e'.2.1, eventAt_eq_some_of_mem_eventHistory he'⟩
    have hpend : e ∈ pendingEvents B s := by
      by_cases hqueue : e.1 ∈ (masterState B s).1.map Prod.fst
      · obtain ⟨e', he', he'1⟩ := List.mem_map.mp hqueue
        rw [← programEvent_eq_of_produces (hq e' he') hsound he'1]
        exact List.mem_append_left _ he'
      · refine List.mem_append_right _ (List.mem_filter.mpr ⟨h, ?_⟩)
        simp only [decide_eq_true_eq, List.mem_append, not_or]
        refine ⟨hqueue, fun hmem => hhist ?_⟩
        obtain ⟨e', he', he'1⟩ := List.mem_map.mp hmem
        exact ⟨e', he', programEvent_eq_of_produces (hh e' he') hsound he'1⟩
    rcases masterState_succ_cases B s with ⟨hp, -⟩ | ⟨hd, rest, hp, h1, h2⟩
    · simp [hp] at hpend
    · rw [hp] at hpend
      rcases List.mem_cons.mp hpend with rfl | hrest
      · exact ⟨s + 1, _, eventAt_eq_some_of_eventHistory_eq_append h2 rfl⟩
      · obtain ⟨t, -, i, hi⟩ := canonical_enumeration_spec_queue B (h1 ▸ hrest)
        exact ⟨t, i, hi⟩

/-- Every halting V program is eventually emitted with its output.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_complete (B : Base) (p x : BitString) :
    produces B.V p [] x ↔ ∃ t i, eventAt B t = some (t, i, p, x) := by
  refine ⟨fun h => ?_, fun ⟨t, i, ht⟩ => (canonical_enumeration_spec_sound B ht).2⟩
  obtain ⟨s, hs⟩ := (produces_iff_exists_mem_plainBatch B p x).mp h
  exact exists_eventAt_of_mem_plainBatch B hs

/-- The programs of a batch have pairwise distinct programs. -/
private lemma nodup_map_fst_plainBatch (B : Base) (t : ℕ) :
    ((plainBatch B t).map Prod.fst).Nodup := by
  unfold plainBatch
  rw [List.map_filterMap]
  refine List.Nodup.filterMap ?_ (nodup_eraseDups_list _)
  intro a a' b hb hb'
  simp only [Option.mem_def, Option.map_eq_some_iff] at hb hb'
  cases h1 : runOut B.vCode t a <;> cases h2 : runOut B.vCode t a' <;> simp_all

/-- No program is queued or emitted twice. -/
private lemma nodup_queued_and_emitted (B : Base) (t : ℕ) :
    ((masterState B t).1.map Prod.fst ++
      (eventHistory B t).map (fun e => e.2.2.1)).Nodup := by
  induction t with
  | zero => simp [masterState, eventHistory]
  | succ t ih =>
    obtain ⟨hq, hh, hqh⟩ := List.nodup_append'.mp ih
    have hf : ((freshEvents B t).map Prod.fst).Nodup :=
      (nodup_map_fst_plainBatch B (t + 1)).sublist (List.filter_sublist.map Prod.fst)
    have hn : ∀ p ∈ (freshEvents B t).map Prod.fst, p ∉ (masterState B t).1.map Prod.fst ++
        (eventHistory B t).map (fun e => e.2.2.1) := by
      intro p hp
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    have hfh : List.Disjoint ((freshEvents B t).map Prod.fst)
        ((eventHistory B t).map (fun e => e.2.2.1)) :=
      List.disjoint_left.mpr fun p hpf hph => hn p hpf (List.mem_append_right _ hph)
    have hqfh : List.Disjoint ((masterState B t).1.map Prod.fst)
        ((freshEvents B t).map Prod.fst ++ (eventHistory B t).map (fun e => e.2.2.1)) := by
      refine List.disjoint_left.mpr fun p hpq hpfh => ?_
      rcases List.mem_append.mp hpfh with hpf | hph
      · exact hn p hpf (List.mem_append_left _ hpq)
      · exact List.disjoint_left.mp hqh hpq hph
    have hpend : ((pendingEvents B t).map Prod.fst ++
        (eventHistory B t).map (fun e => e.2.2.1)).Nodup := by
      simpa only [pendingEvents, List.map_append, List.append_assoc] using
        hq.append (hf.append hh hfh) hqfh
    rcases masterState_succ_cases B t with ⟨hp, h1, h2⟩ | ⟨hd, rest, hp, h1, h2⟩
    · rw [h1, h2]
      simpa using hh
    · rw [hp] at hpend
      rw [h1, h2, List.map_append]
      simp only [List.map_cons, List.cons_append] at hpend
      rw [← List.append_assoc]
      exact (List.perm_append_singleton _ _).nodup_iff.mpr hpend

/-- Two events with the same program emitted by ticks `s ≤ t` are equal. -/
private lemma eq_of_eventAt_of_le {B : Base} {s t : ℕ} {e e' : TimedEvent} (hle : s ≤ t)
    (hs : eventAt B s = some e) (ht : eventAt B t = some e') (hp : e.2.2.1 = e'.2.2.1) :
    e = e' := by
  have hnodup : ((eventHistory B t).map (fun e => e.2.2.1)).Nodup :=
    (nodup_queued_and_emitted B t).sublist (List.sublist_append_right _ _)
  exact List.inj_on_of_nodup_map hnodup
    ((eventHistory_prefix_of_le B hle).subset (mem_eventHistory_of_eventAt hs))
    (mem_eventHistory_of_eventAt ht) hp

/-- A V program is emitted at only one tick, irrespective of repeated output values.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_unique (B : Base) {s t i j : ℕ} {p x y : BitString}
    (hs : eventAt B s = some (s, i, p, x)) (ht : eventAt B t = some (t, j, p, y)) :
    s = t ∧ i = j ∧ x = y := by
  rcases le_total s t with h | h
  · have := eq_of_eventAt_of_le h hs ht rfl
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1, this.2.1, this.2.2.2⟩
  · have := eq_of_eventAt_of_le h ht hs rfl
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1.symm, this.2.1.symm, this.2.2.2.symm⟩

/-- Event position indexes the history at its emission tick and is distinct from that tick.
Blueprint node `lem:stage-api`. Positions start at zero, while emission ticks are positive. -/
theorem canonical_enumeration_spec_position (B : Base) {t i : ℕ} {p x : BitString}
    (h : eventAt B t = some (t, i, p, x)) :
    0 < t ∧ (eventHistory B t).length = i + 1 ∧
      (eventHistory B t)[i]? = some (t, i, p, x) := by
  obtain ⟨hlast, -⟩ := eventAt_eq_some_iff.mp h
  have hmem := List.mem_of_getLast? hlast
  cases t with
  | zero => simp [eventHistory, masterState] at hmem
  | succ t =>
    refine ⟨t.succ_pos, ?_⟩
    rcases masterState_succ_cases B t with ⟨-, -, h2⟩ | ⟨hd, rest, -, -, h2⟩
    · rw [h2] at hmem
      exact absurd (time_le_of_mem_eventHistory hmem) t.not_succ_le_self
    · rw [h2, List.getLast?_concat, Option.some.injEq] at hlast
      rw [h2]
      simp only [Prod.mk.injEq, true_and] at hlast
      obtain ⟨rfl, rfl⟩ := hlast
      simp

/-- The union of finite emitted-output sets is exactly the bounded-output predicate.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_union (B : Base) (k : ℕ) (x : BitString) :
    Simple B.V x k ↔ ∃ t, x ∈ stageOutputs B k t := by
  rw [simple_iff_exists_program]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨t, i, he⟩ := (canonical_enumeration_spec_complete B p x).mp hx
    have hmem : (t, i, p, x) ∈ eventHistory B t :=
      List.mem_of_getElem? (canonical_enumeration_spec_position B he).2.2
    refine ⟨t, ?_⟩
    simp only [stageOutputs, stageOutputList, List.mem_toFinset, List.mem_eraseDups,
      List.mem_filterMap]
    exact ⟨(t, i, p, x), hmem, by simp only [hp, ↓reduceIte]⟩
  · rintro ⟨t, ht⟩
    simp only [stageOutputs, stageOutputList, List.mem_toFinset, List.mem_eraseDups,
      List.mem_filterMap] at ht
    obtain ⟨e, he, hex⟩ := ht
    by_cases hl : e.2.2.1.length ≤ k
    · simp only [hl, ↓reduceIte, Option.some.injEq] at hex
      exact ⟨e.2.2.1, hl, hex ▸ (produces_of_mem_masterState B t).2 e he⟩
    · simp only [hl, ↓reduceIte, reduceCtorEq] at hex

/-- Every conditional D computation of a batch is an actual D computation. -/
private lemma produces_of_mem_prefixBatch {B : Base} {t : ℕ} {e : PrefixObservation}
    (h : e ∈ prefixBatch B t) : produces B.D e.1.1 e.1.2 e.2 := by
  unfold prefixBatch at h
  obtain ⟨q, -, hq⟩ := List.mem_filterMap.mp h
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hq
  exact conditionalRunOut_sound (isCodeFor_dCode B) ha

/-- The D observations at tick `t + 1` are those at tick `t` followed by the batch inputs not
observed before. -/
private lemma prefixHistory_succ (B : Base) (t : ℕ) :
    prefixHistory B (t + 1) = prefixHistory B t ++
      (prefixBatch B (t + 1)).filter
        (fun e => decide (e.1 ∉ (prefixHistory B t).map Prod.fst)) := by
  unfold prefixHistory
  dsimp only [masterState, masterStep]
  split <;> rfl

/-- Every observed D computation is an actual D computation. -/
private lemma produces_of_mem_prefixHistory {B : Base} {t : ℕ} {e : PrefixObservation}
    (h : e ∈ prefixHistory B t) : produces B.D e.1.1 e.1.2 e.2 := by
  induction t with
  | zero => simp [prefixHistory, masterState] at h
  | succ t ih =>
    rw [prefixHistory_succ, List.mem_append] at h
    rcases h with h | h
    · exact ih h
    · exact produces_of_mem_prefixBatch (List.mem_filter.mp h).1

/-- Every halting conditional D computation is observed at some tick. -/
private lemma exists_mem_prefixHistory_of_produces {B : Base} {p b a : BitString}
    (hprod : produces B.D p b a) : ∃ t, ((p, b), a) ∈ prefixHistory B t := by
  obtain ⟨s, hs⟩ := conditionalRunOut_complete (isCodeFor_dCode B) hprod
  set T := max s (Encodable.encode (p, b)) with hT
  have hs' : conditionalRunOut B.dCode (T + 1) p b = some a :=
    conditionalRunOut_mono B.dCode (le_trans (le_max_left _ _) (Nat.le_succ _)) hs
  have hmem : ((p, b), a) ∈ prefixBatch B (T + 1) := by
    unfold prefixBatch
    refine List.mem_filterMap.mpr ⟨(p, b), ?_, by simp [hs']⟩
    refine List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨Encodable.encode (p, b), ?_,
      Encodable.encodek _⟩)
    exact List.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _))
  by_cases hseen : (p, b) ∈ (prefixHistory B T).map Prod.fst
  · obtain ⟨⟨pb', a'⟩, hx, rfl⟩ := List.mem_map.mp hseen
    obtain rfl := Part.mem_unique (produces_of_mem_prefixHistory hx) hprod
    exact ⟨T, hx⟩
  · refine ⟨T + 1, ?_⟩
    rw [prefixHistory_succ, List.mem_append]
    exact Or.inr (List.mem_filter.mpr ⟨hmem, by simpa using hseen⟩)

/-- A D observation is sound, and every halting conditional D computation is observed.
Blueprint node `lem:stage-api`. Its tick is on the same clock as V's emissions. -/
theorem canonical_enumeration_spec_prefix (B : Base) (p b a : BitString) :
    produces B.D p b a ↔ ∃ t, ((p, b), a) ∈ prefixHistory B t :=
  ⟨exists_mem_prefixHistory_of_produces, fun ⟨_, ht⟩ => produces_of_mem_prefixHistory ht⟩

/-- Whether the event at a tick belongs to a given program is a computable test. -/
private lemma computable_hasProgramAt (B : Base) :
    Computable₂ (fun (p : BitString) (t : ℕ) =>
      (eventAt B t).any (fun e => decide (e.2.2.1 = p))) := by
  have hmatch : Primrec₂ (fun (q : BitString × ℕ) (e : TimedEvent) => decide (e.2.2.1 = q.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp Primrec.fst)).decide
  have h : Computable (fun q : BitString × ℕ =>
      ((eventAt B q.2).map (fun e => decide (e.2.2.1 = q.1))).getD false) :=
    Computable.option_getD
      (Computable.option_map ((canonical_enumeration_spec_tables B).2.2.comp Computable.snd)
        hmatch.to_comp)
      (Computable.const false)
  exact h.of_eq (fun q => by dsimp only; cases eventAt B q.2 <;> rfl)

/-- Searching for an emission is partial computable in the program.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_search (B : Base) : Partrec (findEmission B) :=
  Partrec.rfind (Computable.partrec (computable_hasProgramAt B))

/-- The event of a tick belongs to program `p` exactly when `p` is emitted at that tick. -/
private lemma any_eventAt_eq_true_iff (B : Base) (p : BitString) (t : ℕ) :
    (eventAt B t).any (fun e => decide (e.2.2.1 = p)) = true ↔
      ∃ i x, eventAt B t = some (t, i, p, x) := by
  constructor
  · intro h
    cases he : eventAt B t with
    | none => simp [he] at h
    | some e =>
      obtain ⟨t', i, p', x⟩ := e
      simp only [he, Option.any_some, decide_eq_true_eq] at h
      obtain rfl := (canonical_enumeration_spec_sound B he).1
      obtain rfl : p' = p := h
      exact ⟨i, x, rfl⟩
  · rintro ⟨i, x, h⟩
    simp [h]

/-- A halting witness guarantees the timestamp search returns the unique program event.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_search_eq (B : Base) (p : BitString) (t : ℕ) :
    t ∈ findEmission B p ↔ ∃ i x, eventAt B t = some (t, i, p, x) := by
  refine Nat.mem_rfind.trans ?_
  simp only [Part.mem_some_iff]
  constructor
  · rintro ⟨h, -⟩
    exact (any_eventAt_eq_true_iff B p t).mp h.symm
  · intro h
    refine ⟨((any_eventAt_eq_true_iff B p t).mpr h).symm, fun {m} hm => ?_⟩
    obtain ⟨i, x, h⟩ := h
    symm
    rw [← Bool.not_eq_true]
    intro hm'
    obtain ⟨i', x', h'⟩ := (any_eventAt_eq_true_iff B p m).mp hm'
    exact hm.ne' (canonical_enumeration_spec_unique B h h').1

/-- A valid candidate ends its snapshot with precisely its own event.
Blueprint node `lem:stage-api`. This is the witnessed replay contract for later algorithms. -/
theorem canonical_enumeration_spec_candidate (B : Base) (n : ℕ) (candidate : Candidate) :
    validCandidate B n candidate = true ↔ candidate.1.length ≤ n ∧
      ∃ i x, eventAt B candidate.2 = some (candidate.2, i, candidate.1, x) := by
  unfold validCandidate
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr_right fun _ => any_eventAt_eq_true_iff B candidate.1 candidate.2

/-- A left fold of `min` is at most `k` iff its start or one of the folded values is. -/
private lemma foldl_min_le_iff {α : Type*} (l : List α) (f : α → ℕ) (start k : ℕ) :
    l.foldl (fun acc e => min acc (f e)) start ≤ k ↔ start ≤ k ∨ ∃ x ∈ l, f x ≤ k := by
  induction l generalizing start with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, ih, min_le_iff, List.mem_cons, exists_eq_or_imp]
    tauto

/-- Stage complexity is the finite minimum of the literal default and observed program lengths.
Blueprint node `lem:stage-api`. The literal default need not have been observed. -/
theorem canonical_enumeration_spec_prefix_min (B : Base) (t k : ℕ) (a b : BitString) :
    stagePrefixComplexity B t a b ≤ k ↔ literalBound B a ≤ k ∨
      ∃ p, ((p, b), a) ∈ prefixHistory B t ∧ p.length ≤ literalBound B a ∧ p.length ≤ k := by
  unfold stagePrefixComplexity
  rw [foldl_min_le_iff]
  refine or_congr Iff.rfl ⟨fun ⟨x, hx, hxk⟩ => ?_, fun ⟨p, hp1, hp2, hp3⟩ => ?_⟩
  · obtain ⟨hxh, hxcond⟩ := List.mem_filter.mp hx
    obtain ⟨⟨p, b'⟩, a'⟩ := x
    obtain ⟨rfl, rfl, h3⟩ := of_decide_eq_true hxcond
    exact ⟨p, hxh, h3, hxk⟩
  · exact ⟨((p, b), a), List.mem_filter.mpr ⟨hp1, by simpa using hp2⟩, hp3⟩

/-- Every finite prefix approximation is an upper bound on actual prefix complexity.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_prefix_bound (B : Base) (t : ℕ) (a b : BitString) :
    KP B.D a b ≤ (stagePrefixComplexity B t a b : ENat) ∧
      stagePrefixComplexity B t a b ≤ literalBound B a := by
  have hle : stagePrefixComplexity B t a b ≤ literalBound B a :=
    (canonical_enumeration_spec_prefix_min B t _ a b).mpr (Or.inl le_rfl)
  refine ⟨?_, hle⟩
  rcases (canonical_enumeration_spec_prefix_min B t _ a b).mp le_rfl with hlit | ⟨p, hp, -, hpk⟩
  · rw [le_antisymm hle hlit]
    exact B.literal_bound a b
  · have hprod : produces B.D p b a := (canonical_enumeration_spec_prefix B p b a).mpr ⟨t, hp⟩
    exact (KP_le_programLength_of_produces hprod).trans (by exact_mod_cast hpk)

end Kolmogorov.Milovanov
