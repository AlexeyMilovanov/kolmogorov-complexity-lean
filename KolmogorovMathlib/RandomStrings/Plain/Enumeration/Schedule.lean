/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.RandomStrings.Plain.Encoding
import KolmogorovMathlib.RandomStrings.Plain.ListLemmas
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Part02

/-!
# The canonical schedule of V events and D observations

This module defines the common logical clock on which the enumeration of the plain decompressor
`V` and of the conditional prefix decompressor `D` is replayed. A `ScheduleState` consists of the
FIFO queue of pending `V` events, the history of emitted `V` events and the table of observed `D`
computations. `masterStep` advances this state by one numeric tick, and `masterState` replays
the clock from the empty state.

From the history we read off the finite sets `E_{k,t}` of outputs of programs of length at most
`k` emitted by tick `t` (`stageOutputs`, `stageCount`), the event emitted at a given tick
(`eventAt`), the validity test for candidate emission records (`validCandidate`) and the finite
prefix-complexity minimum over the `D` table (`stagePrefixComplexity`,
`candidatePrefixComplexity`).

The main results are blueprint node `lem:stage-api`: every one of these objects is computable
(`canonical_enumeration_spec` and its variants), histories and the sets `E_{k,t}` are monotone in
the tick (`canonical_enumeration_spec_history`, `canonical_enumeration_spec_prefix_mono`,
`canonical_enumeration_spec_mono`), and finite membership tests need no halting oracle. The
candidate interface is what the marker argument of `lem:short-prefix-exact` uses, and
`KolmogorovMathlib.RandomStrings.Plain.Enumeration.CanonicalSpec` builds on the whole API.
-/

namespace Kolmogorov.Milovanov

/-- A V program event records the program and its output, without deduplicating outputs.
Blueprint node `lem:stage-api`. -/
abbrev ProgramEvent := BitString × BitString

/-- A timestamped event records numeric tick, zero-based event position, program, and output.
Blueprint node `lem:stage-api`. -/
abbrev TimedEvent := ℕ × ℕ × ProgramEvent

/-- An observed conditional prefix computation records `(program, condition)` and output.
Blueprint node `lem:stage-api`. -/
abbrev PrefixObservation := (BitString × BitString) × BitString

/-- Encodable schedule state: pending V events, emitted V history, and observed D graph.
Blueprint node `lem:stage-api`. The first list is a FIFO queue. -/
abbrev ScheduleState := List ProgramEvent × List TimedEvent × List PrefixObservation

/-- The V programs whose bounded simulations halt in the current canonical input sweep.
Blueprint node `lem:stage-api`. Input-code order is used only for internal scheduling. -/
def plainBatch (B : Base) (t : ℕ) : List ProgramEvent :=
  ((List.range t).filterMap (Encodable.decode (α := BitString))).eraseDups.filterMap
    (fun p => (runOut B.vCode t p).map (fun x => (p, x)))

/-- The D computations whose bounded simulations halt in the current canonical input sweep.
Blueprint node `lem:stage-api`. The fuel is the same numeric tick as for V. -/
def prefixBatch (B : Base) (t : ℕ) : List PrefixObservation :=
  ((List.range t).filterMap (Encodable.decode (α := BitString × BitString))).eraseDups.filterMap
    (fun p => (conditionalRunOut B.dCode t p.1 p.2).map (fun x => (p, x)))

/-- One master tick queues fresh V programs, emits one head, and records fresh D inputs.
Blueprint node `lem:stage-api`. Previously queued or emitted programs are never queued again. -/
def masterStep (B : Base) (t : ℕ) (state : ScheduleState) : ScheduleState :=
  let seen := state.1.map Prod.fst ++ state.2.1.map (fun e => e.2.2.1)
  let fresh := (plainBatch B t).filter (fun e => decide (e.1 ∉ seen))
  let pending := state.1 ++ fresh
  let prefixSeen := state.2.2.map Prod.fst
  let prefixFresh := (prefixBatch B t).filter (fun e => decide (e.1 ∉ prefixSeen))
  let prefixNext := state.2.2 ++ prefixFresh
  match pending with
  | [] => ([], state.2.1, prefixNext)
  | e :: rest => (rest, state.2.1 ++ [(t, state.2.1.length, e)], prefixNext)

/-- Replay the common logical clock by structural recursion from the empty state.
Blueprint node `lem:stage-api`. Construction actions between ticks are not clock inputs. -/
def masterState (B : Base) : ℕ → ScheduleState
  | 0 => ([], [], [])
  | t + 1 => masterStep B (t + 1) (masterState B t)

/-- All V events emitted through the given numeric tick, in event order.
Blueprint node `lem:stage-api`. -/
def eventHistory (B : Base) (t : ℕ) : List TimedEvent := (masterState B t).2.1

/-- All conditional D computations observed through the same numeric tick.
Blueprint node `lem:stage-api`. -/
def prefixHistory (B : Base) (t : ℕ) : List PrefixObservation := (masterState B t).2.2

/-- The sole V event at a tick, or `none` if that tick emits no event.
Blueprint node `lem:stage-api`. Its timestamp is the emission tick, not the discovery tick. -/
def eventAt (B : Base) (t : ℕ) : Option TimedEvent :=
  (eventHistory B t).getLast?.filter (fun e => decide (e.1 = t))

/-- Distinct outputs of short programs in emitted-event order through a numeric tick.
Blueprint node `lem:stage-api`. This list counts outputs once, even if programs repeat them. -/
def stageOutputList (B : Base) (k t : ℕ) : List BitString :=
  ((eventHistory B t).filterMap
    (fun e => if e.2.2.1.length ≤ k then some e.2.2.2 else none)).eraseDups

/-- The finite set `E_{k,t}` of outputs of short programs emitted through tick `t`.
Blueprint node `lem:stage-api`. -/
def stageOutputs (B : Base) (k t : ℕ) : Finset BitString :=
  (stageOutputList B k t).toFinset

/-- The number of distinct short-program outputs emitted through a numeric tick.
Blueprint node `lem:stage-api`. -/
def stageCount (B : Base) (k t : ℕ) : ℕ := (stageOutputs B k t).card

/-- A candidate record supplies a program and its claimed emission timestamp.
Blueprint node `lem:stage-api`. Records need not be valid; validity is a finite test. -/
abbrev Candidate := BitString × ℕ

/-- Check a candidate's length and exact emission timestamp against the finite event table.
Blueprint node `lem:stage-api`. No test of being the last short program is performed. -/
def validCandidate (B : Base) (n : ℕ) (candidate : Candidate) : Bool :=
  decide (candidate.1.length ≤ n) &&
    (eventAt B candidate.2).any (fun e => decide (e.2.2.1 = candidate.1))

/-- Search effectively for a program's emission timestamp; diverge for nonhalting programs.
Blueprint node `lem:stage-api`. A halting witness guarantees termination. -/
def findEmission (B : Base) (p : BitString) : Part ℕ :=
  Nat.rfind (fun t => Part.some
    ((eventAt B t).any (fun e => decide (e.2.2.1 = p))))

/-- The finite prefix minimum at a numeric tick, with the fixed literal bound as a default.
Blueprint node `lem:stage-api`. Only D observations on the master clock enter this minimum. -/
def stagePrefixComplexity (B : Base) (t : ℕ) (a b : BitString) : ℕ :=
  ((prefixHistory B t).filter (fun e =>
    decide (e.1.2 = b ∧ e.2 = a ∧ e.1.1.length ≤ literalBound B a))).foldl
      (fun k e => min k e.1.1.length) (literalBound B a)

/-- The total candidate interface for bounded prefix complexity, defaulting on bad records.
Blueprint node `lem:short-prefix-exact`. A valid record uses its numeric timestamp. -/
def candidatePrefixComplexity (B : Base) (n : ℕ) (candidate : Candidate)
    (a b : BitString) : ℕ :=
  if validCandidate B n candidate then stagePrefixComplexity B candidate.2 a b
  else literalBound B a

/-- Bounded simulation of a code on a bit-string input is primitive recursive in fuel and input. -/
private lemma runOut_primrec (c : Nat.Partrec.Code) :
    Primrec₂ (fun (t : ℕ) (p : BitString) => runOut c t p) := by
  have h : Primrec (fun q : ℕ × BitString => runOut c q.1 q.2) := by
    refine Primrec.option_bind ?_ ?_
    · exact (evaln_primrec c).comp Primrec.fst
        (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const ([] : BitString))))
    · exact Primrec.decode.comp Primrec.snd
  exact h.to₂

/-- Bounded simulation of a code on a pair of bit strings is primitive recursive in the fuel and
the two inputs. -/
private lemma conditionalRunOut_primrec (c : Nat.Partrec.Code) :
    Primrec (fun q : ℕ × BitString × BitString => conditionalRunOut c q.1 q.2.1 q.2.2) := by
  unfold conditionalRunOut
  apply Primrec.option_bind
  · exact (evaln_primrec c).comp Primrec.fst
      (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))
  · exact Primrec.decode.comp Primrec.snd

/-- The batch of halting `V` programs at a tick is primitive recursive in the tick. -/
private lemma plainBatch_primrec (B : Base) :
    Primrec (plainBatch B) := by
  unfold plainBatch
  have hrun := runOut_primrec B.vCode
  have hcand : Primrec (fun t : ℕ =>
      ((List.range t).filterMap (Encodable.decode (α := BitString))).eraseDups) := by
    refine CodedFiniteDistribution.eraseDups_bitstring_primrec.comp ?_
    exact Primrec.listFilterMap Primrec.list_range
      (Primrec.decode.comp Primrec.snd).to₂
  refine Primrec.listFilterMap hcand ?_
  exact Primrec.option_map (hrun.comp Primrec.fst Primrec.snd)
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

/-- The batch of halting `D` computations at a tick is primitive recursive in the tick. -/
private lemma prefixBatch_primrec (B : Base) :
    Primrec (prefixBatch B) := by
  unfold prefixBatch
  have hrun := conditionalRunOut_primrec B.dCode
  have hcand : Primrec (fun t : ℕ =>
      ((List.range t).filterMap (Encodable.decode (α := BitString × BitString))).eraseDups) := by
    refine (primrec_eraseDups (α := BitString × BitString)).comp ?_
    exact Primrec.listFilterMap Primrec.list_range
      (Primrec.decode.comp Primrec.snd).to₂
  refine Primrec.listFilterMap hcand ?_
  exact Primrec.option_map
    (hrun.comp (Primrec.pair Primrec.fst Primrec.snd))
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

/-- The one-tick transition `masterStep` is primitive recursive in the tick and the state. -/
private lemma masterStep_primrec (B : Base) :
    Primrec (fun q : ℕ × ScheduleState => masterStep B q.1 q.2) := by
  -- projections of the input (tick, (queue, history, observations))
  have hqueue : Primrec (fun q : ℕ × ScheduleState => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hhist : Primrec (fun q : ℕ × ScheduleState => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hobs : Primrec (fun q : ℕ × ScheduleState => q.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  -- V programs already seen
  have hseen : Primrec (fun q : ℕ × ScheduleState =>
      q.2.1.map Prod.fst ++ q.2.2.1.map (fun e => e.2.2.1)) :=
    Primrec.list_append.comp
      (Primrec.list_map hqueue (Primrec.fst.comp Primrec.snd).to₂)
      (Primrec.list_map hhist
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)
  have hfresh : Primrec (fun q : ℕ × ScheduleState =>
      (plainBatch B q.1).filter (fun e => decide (e.1 ∉
        (q.2.1.map Prod.fst ++ q.2.2.1.map (fun e => e.2.2.1))))) := by
    refine Primrec.list_filter ((plainBatch_primrec B).comp Primrec.fst) ?_
    have hm : Primrec (fun p : (ℕ × ScheduleState) × ProgramEvent =>
        decide (p.2.1 ∈ (p.1.2.1.map Prod.fst ++ p.1.2.2.1.map (fun e => e.2.2.1)))) :=
      (Primrec₂.of_eq (α := BitString) list_mem_decide_primrec
        (fun a l => decide_eq_decide.mpr Iff.rfl)).comp (Primrec.fst.comp Primrec.snd)
        (hseen.comp Primrec.fst)
    exact (Primrec.not.comp hm).of_eq (fun p => by simp)
  have hpending : Primrec (fun q : ℕ × ScheduleState =>
      q.2.1 ++ (plainBatch B q.1).filter (fun e => decide (e.1 ∉
        (q.2.1.map Prod.fst ++ q.2.2.1.map (fun e => e.2.2.1))))) :=
    Primrec.list_append.comp hqueue hfresh
  -- D observations already seen
  have hprefixSeen : Primrec (fun q : ℕ × ScheduleState => q.2.2.2.map Prod.fst) :=
    Primrec.list_map hobs (Primrec.fst.comp Primrec.snd).to₂
  have hprefixFresh : Primrec (fun q : ℕ × ScheduleState =>
      (prefixBatch B q.1).filter (fun e => decide (e.1 ∉ q.2.2.2.map Prod.fst))) := by
    refine Primrec.list_filter ((prefixBatch_primrec B).comp Primrec.fst) ?_
    have hm : Primrec (fun p : (ℕ × ScheduleState) × PrefixObservation =>
        decide (p.2.1 ∈ p.1.2.2.2.map Prod.fst)) :=
      (Primrec₂.of_eq list_mem_decide_primrec
        (fun a l => decide_eq_decide.mpr Iff.rfl)).comp (Primrec.fst.comp Primrec.snd)
        (hprefixSeen.comp Primrec.fst)
    exact (Primrec.not.comp hm).of_eq (fun p => by simp)
  have hprefixNext : Primrec (fun q : ℕ × ScheduleState =>
      q.2.2.2 ++ (prefixBatch B q.1).filter (fun e => decide (e.1 ∉ q.2.2.2.map Prod.fst))) :=
    Primrec.list_append.comp hobs hprefixFresh
  -- the two cases of the final match
  have hnil : Primrec (fun q : ℕ × ScheduleState =>
      (([] : List ProgramEvent), q.2.2.1,
        q.2.2.2 ++ (prefixBatch B q.1).filter (fun e => decide (e.1 ∉ q.2.2.2.map Prod.fst)))) :=
    Primrec.pair (Primrec.const []) (Primrec.pair hhist hprefixNext)
  have hcons : Primrec₂ (fun (q : ℕ × ScheduleState) (er : ProgramEvent × List ProgramEvent) =>
      (er.2, q.2.2.1 ++ [(q.1, q.2.2.1.length, er.1)],
        q.2.2.2 ++ (prefixBatch B q.1).filter (fun e => decide (e.1 ∉ q.2.2.2.map Prod.fst)))) := by
    have hh : Primrec (fun p : (ℕ × ScheduleState) × (ProgramEvent × List ProgramEvent) =>
        p.1.2.2.1) := hhist.comp Primrec.fst
    have hevent : Primrec (fun p : (ℕ × ScheduleState) × (ProgramEvent × List ProgramEvent) =>
        (p.1.1, p.1.2.2.1.length, p.2.1)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.list_length.comp hh) (Primrec.fst.comp Primrec.snd))
    exact Primrec.pair (Primrec.snd.comp Primrec.snd)
      (Primrec.pair
        (Primrec.list_append.comp hh (Primrec.list_cons.comp hevent (Primrec.const [])))
        (hprefixNext.comp Primrec.fst))
  refine (Primrec.list_casesOn hpending hnil hcons).of_eq (fun q => ?_)
  symm
  unfold masterStep
  dsimp only
  generalize q.2.1 ++ _ = pending
  cases pending <;> rfl

/-- The one-tick transition on `ScheduleState`, indexed by the previous tick, is computable. -/
private lemma masterStep_computable (B : Base) :
    Computable₂ (fun (_t : ℕ) (p : ℕ × ScheduleState) =>
      masterStep B (p.1 + 1) p.2) := by
  have h : Primrec (fun r : ℕ × ℕ × ScheduleState => masterStep B (r.2.1 + 1) r.2.2) :=
    (masterStep_primrec B).comp
      (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact h.to_comp

/-- The entire finite state is computable from the tick and the supplied interpreter codes.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec (B : Base) : Computable (masterState B) := by
  have H : masterState B = fun t =>
      Nat.rec (([], [], []) : ScheduleState) (fun t' state => masterStep B (t' + 1) state) t := by
    funext t
    induction t with
    | zero => rfl
    | succ t ih =>
      change masterStep B (t + 1) (masterState B t) = masterStep B (t + 1) _
      rw [ih]
  rw [H]
  exact Computable.nat_rec Computable.id (Computable.const _) (masterStep_computable B)

/-- Event histories and prefix observation tables are computable finite data.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_tables (B : Base) :
    Computable (eventHistory B) ∧ Computable (prefixHistory B) ∧ Computable (eventAt B) := by
  have h := canonical_enumeration_spec B
  have hev : Computable (eventHistory B) :=
    Computable.fst.comp (Computable.snd.comp h)
  have hph : Computable (prefixHistory B) :=
    Computable.snd.comp (Computable.snd.comp h)
  have hlast : Computable (fun t : ℕ => (eventHistory B t).getLast?) :=
    (Primrec.list_head?.to_comp.comp (Computable.list_reverse.comp hev)).of_eq
      (fun t => (List.getLast?_eq_head?_reverse (xs := eventHistory B t)).symm)
  -- keep an event only if it was emitted at the given tick
  have hkeep : Computable₂ (fun (t : ℕ) (e : TimedEvent) =>
      if decide (e.1 = t) then some e else none) := by
    have heq : Primrec (fun p : ℕ × TimedEvent => decide (p.2.1 = p.1)) :=
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).decide
    refine (Primrec.cond heq (Primrec.option_some.comp Primrec.snd)
      (Primrec.const (none : Option TimedEvent))).to_comp.of_eq (fun p => ?_)
    dsimp only
    cases decide (p.2.1 = p.1) <;> rfl
  refine ⟨hev, hph, ?_⟩
  exact (Computable.option_casesOn hlast (Computable.const (none : Option TimedEvent))
    hkeep).of_eq (fun t => by
      dsimp [eventAt]
      cases (eventHistory B t).getLast? <;> rfl)

/-- The list of distinct outputs of the events of length at most `p.1` in a list of timed events
is primitive recursive in the bound and the events. -/
private lemma stageOutputList_primrec :
    Primrec (fun p : ℕ × List TimedEvent =>
      (p.2.filterMap
        (fun e => if e.2.2.1.length ≤ p.1 then some e.2.2.2 else none)).eraseDups) := by
  refine CodedFiniteDistribution.eraseDups_bitstring_primrec.comp
    (Primrec.listFilterMap Primrec.snd ?_)
  have hprog : Primrec (fun q : (ℕ × List TimedEvent) × TimedEvent => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have houtput : Primrec (fun q : (ℕ × List TimedEvent) × TimedEvent => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite (Primrec.nat_le.comp (Primrec.list_length.comp hprog)
    (Primrec.fst.comp Primrec.fst)) (Primrec.option_some.comp houtput)
    (Primrec.const (none : Option BitString))

/-- The distinct-output list and its count are computable uniformly in budget and tick.
Blueprint node `lem:stage-api`. Membership in the associated finset is also computable. -/
theorem canonical_enumeration_spec_outputs (B : Base) :
    Computable₂ (stageOutputList B) ∧ Computable₂ (stageCount B) ∧
      Computable (fun p : ℕ × ℕ × BitString => decide (p.2.2 ∈ stageOutputs B p.1 p.2.1)) := by
  have hlist : Computable₂ (stageOutputList B) :=
    (stageOutputList_primrec.to_comp.comp
      (Computable.fst.pair (((canonical_enumeration_spec_tables B).1).comp Computable.snd))).of_eq
      (fun _ => rfl)
  have hcount : Computable₂ (stageCount B) :=
    (Computable.list_length.comp hlist).of_eq (fun _ => by
      dsimp [stageCount, stageOutputs, stageOutputList]
      rw [List.toFinset_card_of_nodup (nodup_eraseDups_list _)])
  have hdecide : Primrec₂ (fun (a : BitString) (l : List BitString) => decide (a ∈ l)) :=
    Primrec₂.of_eq list_mem_decide_primrec (fun a l => decide_eq_decide.mpr Iff.rfl)
  refine ⟨hlist, hcount, ?_⟩
  exact (hdecide.to_comp.comp (Computable.snd.comp Computable.snd)
    (hlist.comp Computable.fst (Computable.fst.comp Computable.snd))).of_eq (fun p => by
      dsimp [stageOutputs]
      exact decide_eq_decide.mpr List.mem_toFinset.symm)

/-- The finite candidate-validity test is computable. -/
private theorem validCandidate_computable (B : Base) : Computable₂ (validCandidate B) := by
  have hat : Computable (fun x : ℕ × Candidate => eventAt B x.2.2) :=
    (canonical_enumeration_spec_tables B).2.2.comp (Computable.snd.comp Computable.snd)
  have hprog : Computable₂ (fun (x : ℕ × Candidate) (e : TimedEvent) =>
      decide (e.2.2.1 = x.2.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).decide.to_comp
  have hany : Computable (fun x : ℕ × Candidate =>
      (eventAt B x.2.2).any (fun e => decide (e.2.2.1 = x.2.1))) :=
    (Computable.option_casesOn hat (Computable.const false) hprog).of_eq
      (fun x => by cases eventAt B x.2.2 <;> rfl)
  have hlen : Computable (fun x : ℕ × Candidate => decide (x.2.1.length ≤ x.1)) :=
    (Primrec.nat_le.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      Primrec.fst).decide.to_comp
  exact (Primrec.and.to_comp.comp hlen hany).of_eq (fun _ => rfl)

/-- One step of the fold defining `stagePrefixComplexity`: the query `(t, a, b)` together with the
running minimum and the current table entry. -/
private abbrev PrefixFoldStep := (ℕ × BitString × BitString) × ℕ × PrefixObservation

/-- The finite prefix minimum `stagePrefixComplexity` is computable in the tick and the pair. -/
private theorem stagePrefixComplexity_computable (B : Base) :
    Computable (fun p : ℕ × BitString × BitString =>
      stagePrefixComplexity B p.1 p.2.1 p.2.2) := by
  have hbound : Computable (literalBound B) := literalBound_computable B
  have decEq : Computable₂ (fun (a b : BitString) => decide (a = b)) :=
    (PrimrecRel.decide Primrec.eq).to_comp
  have decLe : Computable₂ (fun (a b : ℕ) => decide (a ≤ b)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp
  -- the three conjuncts of the filter condition
  have hcond : Computable (fun x : PrefixFoldStep => x.2.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hquery : Computable (fun x : PrefixFoldStep => x.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have houtput : Computable (fun x : PrefixFoldStep => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have htarget : Computable (fun x : PrefixFoldStep => x.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hlen : Computable (fun x : PrefixFoldStep => x.2.2.1.1.length) :=
    Computable.list_length.comp
      (Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hfilter : Computable (fun x : PrefixFoldStep =>
      decide (x.2.2.1.2 = x.1.2.2 ∧ x.2.2.2 = x.1.2.1 ∧
        x.2.2.1.1.length ≤ literalBound B x.1.2.1)) :=
    (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp (decEq.comp hcond hquery)
      (decEq.comp houtput htarget)) (decLe.comp hlen (hbound.comp htarget))).of_eq
      (fun x => by simp only [Bool.decide_and, Bool.and_assoc])
  have hmin : Computable (fun x : PrefixFoldStep => min x.2.1 x.2.2.1.1.length) :=
    Primrec.nat_min.to_comp.comp (Computable.fst.comp Computable.snd) hlen
  have hstep : Computable₂ (fun (p : ℕ × BitString × BitString) (u : ℕ × PrefixObservation) =>
      bif decide (u.2.1.2 = p.2.2 ∧ u.2.2 = p.2.1 ∧ u.2.1.1.length ≤ literalBound B p.2.1)
      then min u.1 u.2.1.1.length else u.1) :=
    Computable.cond hfilter hmin (Computable.fst.comp Computable.snd)
  have hfold := Computable.list_foldl
    ((canonical_enumeration_spec_tables B).2.1.comp Computable.fst)
    (hbound.comp (Computable.fst.comp Computable.snd)) hstep
  refine hfold.of_eq (fun p => ?_)
  unfold stagePrefixComplexity
  rw [List.foldl_filter]
  congr 1
  funext s e
  cases decide (e.1.2 = p.2.2 ∧ e.2 = p.2.1 ∧ e.1.1.length ≤ literalBound B p.2.1) <;> rfl

/-- Finite candidate validation and the finite prefix minimum are computable functions.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_prefix_computable (B : Base) :
    Computable₂ (validCandidate B) ∧
      Computable (fun p : ℕ × BitString × BitString =>
        stagePrefixComplexity B p.1 p.2.1 p.2.2) ∧
      Computable (fun p : ℕ × Candidate × BitString × BitString =>
        candidatePrefixComplexity B p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  refine ⟨validCandidate_computable B, stagePrefixComplexity_computable B, ?_⟩
  have hcandidate : Computable (fun p : ℕ × Candidate × BitString × BitString => p.2.1) :=
    Computable.fst.comp Computable.snd
  have ha : Computable (fun p : ℕ × Candidate × BitString × BitString => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hb : Computable (fun p : ℕ × Candidate × BitString × BitString => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hvalid : Computable (fun p : ℕ × Candidate × BitString × BitString =>
      validCandidate B p.1 p.2.1) :=
    Computable₂.comp (validCandidate_computable B) Computable.fst hcandidate
  have hstamp : Computable (fun p : ℕ × Candidate × BitString × BitString => p.2.1.2) :=
    Computable.snd.comp hcandidate
  have hpair : Computable (fun p : ℕ × Candidate × BitString × BitString =>
      (p.2.2.1, p.2.2.2)) :=
    Computable.pair (f := fun p : ℕ × Candidate × BitString × BitString => p.2.2.1)
      (g := fun p => p.2.2.2) ha hb
  have hquery : Computable (fun p : ℕ × Candidate × BitString × BitString =>
      (p.2.1.2, (p.2.2.1, p.2.2.2))) :=
    Computable.pair (f := fun p : ℕ × Candidate × BitString × BitString => p.2.1.2)
      (g := fun p => (p.2.2.1, p.2.2.2)) hstamp hpair
  have hstage : Computable (fun p : ℕ × Candidate × BitString × BitString =>
      stagePrefixComplexity B p.2.1.2 p.2.2.1 p.2.2.2) :=
    Computable.comp
      (f := fun p : ℕ × BitString × BitString => stagePrefixComplexity B p.1 p.2.1 p.2.2)
      (g := fun p : ℕ × Candidate × BitString × BitString => (p.2.1.2, (p.2.2.1, p.2.2.2)))
      (stagePrefixComplexity_computable B) hquery
  have hdefault : Computable (fun p : ℕ × Candidate × BitString × BitString =>
      literalBound B p.2.2.1) :=
    (literalBound_computable B).comp ha
  refine (Computable.cond hvalid hstage hdefault).of_eq (fun p => ?_)
  dsimp only [candidatePrefixComplexity]
  cases h : validCandidate B p.1 p.2.1 <;> rfl

/-- V event histories grow by appending at most one event per tick.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_history (B : Base) (t : ℕ) :
    eventHistory B t <+: eventHistory B (t + 1) ∧
      (eventHistory B (t + 1)).length ≤ (eventHistory B t).length + 1 := by
  dsimp [eventHistory, masterState, masterStep]
  generalize (masterState B t).fst ++ _ = pending
  cases pending <;> simp

/-- Prefix observations persist when the common numeric clock advances.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_prefix_mono (B : Base) {s t : ℕ} (h : s ≤ t) :
    prefixHistory B s <+: prefixHistory B t := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t' _ ih =>
    apply List.IsPrefix.trans ih
    dsimp [prefixHistory, masterState]
    generalize masterState B t' = state
    dsimp [masterStep]
    split <;> apply List.prefix_append

/-- The V event history at an earlier tick is a prefix of the history at a later tick. -/
lemma eventHistory_prefix_of_le (B : Base) {s t : ℕ} (h : s ≤ t) :
    eventHistory B s <+: eventHistory B t := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @step m ht ih => exact ih.trans (canonical_enumeration_spec_history B m).1

/-- The list of short-program outputs only grows (as a set) with the tick. -/
private lemma stageOutputList_subset_of_le (B : Base) (k : ℕ) {s t : ℕ} (h : s ≤ t) :
    stageOutputList B k s ⊆ stageOutputList B k t := by
  unfold stageOutputList
  obtain ⟨l, hl⟩ := eventHistory_prefix_of_le B h
  rw [← hl, List.filterMap_append]
  intro x hx
  rw [List.mem_eraseDups] at hx ⊢
  exact List.mem_append.mpr (Or.inl hx)

/-- The sets `E_{k,t}` only grow with the tick. -/
private lemma stageOutputs_subset_of_le (B : Base) (k : ℕ) {s t : ℕ} (h : s ≤ t) :
    stageOutputs B k s ⊆ stageOutputs B k t := by
  intro x hx
  unfold stageOutputs at hx ⊢
  rw [List.mem_toFinset] at hx ⊢
  exact stageOutputList_subset_of_le B k h hx

/-- Distinct-output sets and counts increase with the numeric tick.
Blueprint node `lem:stage-api`. -/
theorem canonical_enumeration_spec_mono (B : Base) (k : ℕ) {s t : ℕ} (h : s ≤ t) :
    stageOutputs B k s ⊆ stageOutputs B k t ∧ stageCount B k s ≤ stageCount B k t :=
  ⟨stageOutputs_subset_of_le B k h, Finset.card_le_card (stageOutputs_subset_of_le B k h)⟩

end Kolmogorov.Milovanov
