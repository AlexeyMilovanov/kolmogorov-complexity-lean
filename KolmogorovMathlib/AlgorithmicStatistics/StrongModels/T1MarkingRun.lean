import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingCount
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- One chronological event in the `t1` marking construction. -/
inductive T1MarkEvent
  | bSet (code : BitString)
  | cDoublePrimeBatch (batch : List BitString)
  | cPrimeModel (code : BitString)
  | dString (w : BitString)
  deriving Repr, DecidableEq, Inhabited

def t1MarkEventEquiv :
    T1MarkEvent ≃
      Sum BitString (Sum (List BitString) (Sum BitString BitString)) where
  toFun
    | .bSet code => .inl code
    | .cDoublePrimeBatch batch => .inr (.inl batch)
    | .cPrimeModel code => .inr (.inr (.inl code))
    | .dString w => .inr (.inr (.inr w))
  invFun
    | .inl code => .bSet code
    | .inr (.inl batch) => .cDoublePrimeBatch batch
    | .inr (.inr (.inl code)) => .cPrimeModel code
    | .inr (.inr (.inr w)) => .dString w
  left_inv event := by cases event <;> rfl
  right_inv code := by
    rcases code with code | batchOrCode
    · rfl
    · rcases batchOrCode with batch | codeOrString
      · rfl
      · rcases codeOrString with code | w <;> rfl

instance : Primcodable T1MarkEvent :=
  Primcodable.ofEquiv _ t1MarkEventEquiv

/-! The bounded-output API exposes fixed-machine primitive-recursion lemmas.
The chronological stream is uniform in the machine code, so we locally lift
the same constructions through the code evaluator. -/

private theorem t1SnapshotCodes_primrec_uniform :
    Primrec (fun p : (Code × Nat) × Nat =>
      snapshotCodes p.1.1 p.1.2 p.2) := by
  apply Primrec.listFilterMap
    (primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst))
  apply Primrec.option_bind
  · exact Code.primrec_evaln.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.encode.comp
          (Primrec.pair Primrec.snd (Primrec.const []))))
  · exact Primrec.decode.comp Primrec.snd

private theorem t1BoundedOutputStage_primrec_uniform :
    Primrec (fun p : (Code × Nat) × Nat =>
      boundedOutputStage p.1.1 p.1.2 p.2) := by
  have hbase : Primrec (fun p : (Code × Nat) × Nat =>
      (snapshotCodes p.1.1 p.1.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (t1SnapshotCodes_primrec_uniform.comp
        (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂
      (fun (p : (Code × Nat) × Nat)
        (z : Nat × List BitString) =>
          (z.2 ++ snapshotCodes p.1.1 p.1.2 (z.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp
        (Primrec.snd.comp Primrec.snd)
        (t1SnapshotCodes_primrec_uniform.comp
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨c, m⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [boundedOutputStage]
      rw [← ih]

private theorem t1BStage_primrec_uniform :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      t1BStage p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hstage : Primrec (fun p : Code × Nat × Nat × Nat =>
      boundedOutputStage p.1 p.2.2.1 p.2.2.2) :=
    t1BoundedOutputStage_primrec_uniform.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hbound : Primrec
      (fun q : (Code × Nat × Nat × Nat) × BitString =>
        2 ^ (q.1.2.1 - q.1.2.2.1 - 4)) :=
    twoPow_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.const 4))
  have hvalid : Primrec₂
      (fun (p : Code × Nat × Nat × Nat) (w : BitString) =>
        t1ModelCodeValid (2 ^ (p.2.1 - p.2.2.1 - 4)) w) :=
    (t1ModelCodeValid_primrec.comp
      (Primrec.pair hbound Primrec.snd)).to₂
  exact list_filter_primrec hstage hvalid

private theorem t1CPrimeStage_primrec_uniform :
    Primrec (fun p : Code × Nat × Nat =>
      t1CPrimeStage p.1 p.2.1 p.2.2) := by
  have hstage : Primrec (fun p : Code × Nat × Nat =>
      boundedOutputStage p.1 p.2.1 p.2.2) :=
    t1BoundedOutputStage_primrec_uniform.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact list_filter_primrec hstage
    (isCanonicalUniformCodeBool_primrec.comp Primrec.snd)

private theorem t1DescriptionStage_primrec_uniform :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      t1DescriptionStage p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hstage : Primrec (fun p : Code × Nat × Nat × Nat =>
      boundedOutputStage p.1 p.2.2.1 p.2.2.2) :=
    t1BoundedOutputStage_primrec_uniform.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hbound : Primrec
      (fun q : (Code × Nat × Nat × Nat) × BitString =>
        2 ^ q.1.2.1) :=
    twoPow_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hvalid : Primrec₂
      (fun (p : Code × Nat × Nat × Nat) (w : BitString) =>
        t1ModelCodeValid (2 ^ p.2.1) w) :=
    (t1ModelCodeValid_primrec.comp
      (Primrec.pair hbound Primrec.snd)).to₂
  exact list_filter_primrec hstage hvalid

private theorem t1CDoublePrimeBatches_primrec_uniform :
    Primrec (fun p : Code × Nat × Nat × Nat × Nat =>
      t1CDoublePrimeBatches p.1 p.2.1 p.2.2.1
        p.2.2.2.1 p.2.2.2.2) := by
  have hdescs : Primrec (fun p : Code × Nat × Nat × Nat × Nat =>
      t1DescriptionStage p.1 p.2.1 p.2.2.2.1 p.2.2.2.2) :=
    t1DescriptionStage_primrec_uniform.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.snd))))
            (Primrec.snd.comp
              (Primrec.snd.comp
                (Primrec.snd.comp Primrec.snd))))))
  have hbatch : Primrec₂
      (fun (p : Code × Nat × Nat × Nat × Nat)
        (w : BitString) =>
          t1CDoublePrimeBatch p.2.1 p.2.2.1 w) :=
    (t1CDoublePrimeBatch_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp
            (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))
        Primrec.snd)).to₂
  exact Primrec.list_map hdescs hbatch

private theorem t1DStage_primrec_uniform :
    Primrec (fun p : Code × Nat × Nat × Nat =>
      t1DStage p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hbase : Primrec (fun _ : Code × Nat × Nat × Nat =>
      ([] : List BitString)) := Primrec.const []
  have hstage : Primrec (fun p : Code × Nat × Nat × Nat =>
      boundedOutputStage p.1 p.2.2.1.pred p.2.2.2) :=
    t1BoundedOutputStage_primrec_uniform.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.pred.comp
            (Primrec.fst.comp
              (Primrec.snd.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hlen : Primrec₂
      (fun (p : Code × Nat × Nat × Nat) (w : BitString) =>
        decide (w.length = p.2.1)) := by
    have heq : Primrec
        (fun q : (Code × Nat × Nat × Nat) × BitString =>
          decide (q.2.length = q.1.2.1)) :=
      PrimrecPred.decide
        (Primrec.eq.comp
          (Primrec.list_length.comp Primrec.snd)
          (Primrec.fst.comp
            (Primrec.snd.comp Primrec.fst)))
    exact heq.to₂
  have hfiltered : Primrec (fun p : Code × Nat × Nat × Nat =>
      (boundedOutputStage p.1 p.2.2.1.pred p.2.2.2).filter
        (fun w => decide (w.length = p.2.1))) :=
    list_filter_primrec hstage hlen
  have hzero : Primrec (fun p : Code × Nat × Nat × Nat =>
      decide (p.2.2.1 = 0)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const 0))
  refine (Primrec.cond hzero hbase hfiltered).of_eq ?_
  intro p
  unfold t1DStage
  cases p.2.2.1 <;> rfl

private theorem t1MarkEvent_bSet_primrec :
    Primrec T1MarkEvent.bSet :=
  (Primrec.of_equiv_iff t1MarkEventEquiv).mp
    Primrec.sumInl

private theorem t1MarkEvent_cDoublePrimeBatch_primrec :
    Primrec T1MarkEvent.cDoublePrimeBatch :=
  (Primrec.of_equiv_iff t1MarkEventEquiv).mp
    (Primrec.sumInr.comp Primrec.sumInl)

private theorem t1MarkEvent_cPrimeModel_primrec :
    Primrec T1MarkEvent.cPrimeModel :=
  (Primrec.of_equiv_iff t1MarkEventEquiv).mp
    (Primrec.sumInr.comp
      (Primrec.sumInr.comp Primrec.sumInl))

private theorem t1MarkEvent_dString_primrec :
    Primrec T1MarkEvent.dString :=
  (Primrec.of_equiv_iff t1MarkEventEquiv).mp
    (Primrec.sumInr.comp
      (Primrec.sumInr.comp Primrec.sumInr))

private theorem t1MarkEvent_mapB_primrec :
    Primrec (fun l : List BitString =>
      l.map T1MarkEvent.bSet) :=
  Primrec.list_map Primrec.id
    ((t1MarkEvent_bSet_primrec.comp Primrec.snd).to₂)

private theorem t1MarkEvent_mapCDoublePrime_primrec :
    Primrec (fun l : List (List BitString) =>
      l.map T1MarkEvent.cDoublePrimeBatch) :=
  Primrec.list_map Primrec.id
    ((t1MarkEvent_cDoublePrimeBatch_primrec.comp Primrec.snd).to₂)

private theorem t1MarkEvent_mapCPrime_primrec :
    Primrec (fun l : List BitString =>
      l.map T1MarkEvent.cPrimeModel) :=
  Primrec.list_map Primrec.id
    ((t1MarkEvent_cPrimeModel_primrec.comp Primrec.snd).to₂)

private theorem t1MarkEvent_mapD_primrec :
    Primrec (fun l : List BitString =>
      l.map T1MarkEvent.dString) :=
  Primrec.list_map Primrec.id
    ((t1MarkEvent_dString_primrec.comp Primrec.snd).to₂)

private theorem t1EraseDupsEvent_eq_foldl
    (l : List T1MarkEvent) :
    l.eraseDups =
      l.foldl
        (fun acc event =>
          if event ∈ acc then acc else acc ++ [event]) [] := by
  have mem_foldl : ∀ (xs acc : List T1MarkEvent)
      (event : T1MarkEvent),
      event ∈ xs.foldl
          (fun acc next =>
            if next ∈ acc then acc else acc ++ [next]) acc ↔
        event ∈ acc ∨ event ∈ xs := by
    intro xs
    induction xs with
    | nil => simp
    | cons next xs ih =>
        intro acc event
        rw [List.foldl_cons, ih]
        by_cases hnext : next ∈ acc
        · simp only [hnext, ↓reduceIte, List.mem_cons]
          constructor
          · rintro (hacc | hxs)
            · exact Or.inl hacc
            · exact Or.inr (Or.inr hxs)
          · rintro (hacc | heq | hxs)
            · exact Or.inl hacc
            · subst event
              exact Or.inl hnext
            · exact Or.inr hxs
        · simp only [hnext, ↓reduceIte, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          tauto
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l event ih =>
      simp only [List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rw [List.eraseDups_append, ih]
      have hmem : event ∈ List.foldl
          (fun acc next =>
            if next ∈ acc then acc else acc ++ [next]) [] l ↔
          event ∈ l := by
        simpa using mem_foldl l [] event
      by_cases hevent : event ∈ l
      · have hfold := hmem.mpr hevent
        simp [hfold, List.removeAll, hevent]
      · have hfold : event ∉ List.foldl
            (fun acc next =>
              if next ∈ acc then acc else acc ++ [next]) [] l :=
          fun h => hevent (hmem.mp h)
        simp [hfold, List.removeAll, hevent,
          List.eraseDups_cons]

private theorem t1EraseDupsEvent_primrec :
    Primrec (fun l : List T1MarkEvent => l.eraseDups) := by
  rw [show (fun l : List T1MarkEvent => l.eraseDups) =
      fun l => l.foldl
        (fun acc event =>
          if event ∈ acc then acc else acc ++ [event]) []
    from funext t1EraseDupsEvent_eq_foldl]
  have hmem : Primrec
      (fun p : List T1MarkEvent ×
          (List T1MarkEvent × T1MarkEvent) =>
        decide (p.2.2 ∈ p.2.1)) :=
    decide_mem_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂
      (fun (_ : List T1MarkEvent)
        (p : List T1MarkEvent × T1MarkEvent) =>
          if p.2 ∈ p.1 then p.1 else p.1 ++ [p.2]) := by
    have h := Primrec.cond hmem
      (Primrec.fst.comp Primrec.snd)
      (Primrec.list_append.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.snd.comp Primrec.snd)
          (Primrec.const [])))
    exact h.of_eq fun p => by
      cases hp : decide (p.2.2 ∈ p.2.1) <;> simp_all
  exact Primrec.list_foldl Primrec.id
    (Primrec.const []) hstep

/-- Deduplication of a chronological event list preserves membership. -/
theorem t1_mem_eraseDups_event {event : T1MarkEvent} :
    ∀ {events : List T1MarkEvent},
      event ∈ events.eraseDups ↔ event ∈ events := by
  intro events
  induction events using List.reverseRecOn with
  | nil => simp
  | append_singleton events last ih =>
      rw [List.eraseDups_append, List.mem_append, ih]
      by_cases hlast : last ∈ events
      · have hremove :
            ([last] : List T1MarkEvent).removeAll events = [] := by
          simp [List.removeAll, hlast]
        rw [hremove, List.eraseDups_nil]
        simp only [List.not_mem_nil, or_false, List.mem_append,
          List.mem_singleton]
        exact ⟨Or.inl, fun h =>
          h.elim id (fun heq => heq ▸ hlast)⟩
      · have hremove :
            ([last] : List T1MarkEvent).removeAll events = [last] := by
          simp [List.removeAll, hlast]
        rw [hremove,
          show ([last] : List T1MarkEvent).eraseDups = [last] from rfl]
        simp

private theorem nodup_eraseDups_t1MarkEvent :
    ∀ events : List T1MarkEvent, events.eraseDups.Nodup
  | [] => by simp
  | event :: events => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr
        ⟨?_, nodup_eraseDups_t1MarkEvent _⟩
      intro hmem
      rw [t1_mem_eraseDups_event, List.mem_filter] at hmem
      simp at hmem
  termination_by events => events.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- All marking objects visible at one dovetailing stage, in the source's
within-stage order: `B`, then the `C''` portions, then `C'`, then `D`. -/
noncomputable def t1MarkingEventsUpToTime
    (c : Code) (n k epsilon d t : Nat) : List T1MarkEvent :=
  (t1BStage c n epsilon t).map T1MarkEvent.bSet ++
  (t1CDoublePrimeBatches c n k d t).map
    T1MarkEvent.cDoublePrimeBatch ++
  (t1CPrimeStage c k t).map T1MarkEvent.cPrimeModel ++
  (t1DStage c n k t).map T1MarkEvent.dString

private abbrev T1MarkingEventInput :=
  Code × Nat × Nat × Nat × Nat × Nat

private theorem t1EventInput_c_primrec :
    Primrec (fun p : T1MarkingEventInput => p.1) :=
  Primrec.fst

private theorem t1EventInput_n_primrec :
    Primrec (fun p : T1MarkingEventInput => p.2.1) :=
  Primrec.fst.comp Primrec.snd

private theorem t1EventInput_k_primrec :
    Primrec (fun p : T1MarkingEventInput => p.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem t1EventInput_epsilon_primrec :
    Primrec (fun p : T1MarkingEventInput => p.2.2.2.1) :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem t1EventInput_d_primrec :
    Primrec (fun p : T1MarkingEventInput => p.2.2.2.2.1) :=
  Primrec.fst.comp
    (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem t1EventInput_t_primrec :
    Primrec (fun p : T1MarkingEventInput => p.2.2.2.2.2) :=
  Primrec.snd.comp
    (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem t1MarkingEventsUpToTime_primrec :
    Primrec (fun p : T1MarkingEventInput =>
      t1MarkingEventsUpToTime p.1 p.2.1 p.2.2.1
        p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have hB := t1BStage_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_n_primrec
        (Primrec.pair t1EventInput_epsilon_primrec
          t1EventInput_t_primrec)))
  have hC2 := t1CDoublePrimeBatches_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_n_primrec
        (Primrec.pair t1EventInput_k_primrec
          (Primrec.pair t1EventInput_d_primrec
            t1EventInput_t_primrec))))
  have hC1 := t1CPrimeStage_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_k_primrec
        t1EventInput_t_primrec))
  have hD := t1DStage_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_n_primrec
        (Primrec.pair t1EventInput_k_primrec
          t1EventInput_t_primrec)))
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (t1MarkEvent_mapB_primrec.comp hB)
        (t1MarkEvent_mapCDoublePrime_primrec.comp hC2))
      (t1MarkEvent_mapCPrime_primrec.comp hC1))
    (t1MarkEvent_mapD_primrec.comp hD)

/-- The chronological marking-event stream. Re-emitting the full visible list
at every dovetailing stage and deduplicating retains the old stream as a prefix
while appending genuinely new events in the prescribed within-stage order. -/
noncomputable def t1MarkingEventStage
    (c : Code) (n k epsilon d : Nat) : Nat → List T1MarkEvent
  | 0 => (t1MarkingEventsUpToTime c n k epsilon d 0).eraseDups
  | t + 1 =>
      (t1MarkingEventStage c n k epsilon d t ++
        t1MarkingEventsUpToTime c n k epsilon d
          (t + 1)).eraseDups

private theorem t1MarkingEventsAtZero_primrec :
    Primrec (fun p : T1MarkingEventInput =>
      t1MarkingEventsUpToTime p.1 p.2.1 p.2.2.1
        p.2.2.2.1 p.2.2.2.2.1 0) := by
  have hB := t1BStage_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_n_primrec
        (Primrec.pair t1EventInput_epsilon_primrec
          (Primrec.const 0))))
  have hC2 := t1CDoublePrimeBatches_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_n_primrec
        (Primrec.pair t1EventInput_k_primrec
          (Primrec.pair t1EventInput_d_primrec
            (Primrec.const 0)))))
  have hC1 := t1CPrimeStage_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_k_primrec
        (Primrec.const 0)))
  have hD := t1DStage_primrec_uniform.comp
    (Primrec.pair t1EventInput_c_primrec
      (Primrec.pair t1EventInput_n_primrec
        (Primrec.pair t1EventInput_k_primrec
          (Primrec.const 0))))
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (t1MarkEvent_mapB_primrec.comp hB)
        (t1MarkEvent_mapCDoublePrime_primrec.comp hC2))
      (t1MarkEvent_mapCPrime_primrec.comp hC1))
    (t1MarkEvent_mapD_primrec.comp hD)

private theorem t1MarkingEventsAtNext_primrec :
    Primrec (fun q : T1MarkingEventInput ×
        (Nat × List T1MarkEvent) =>
      t1MarkingEventsUpToTime q.1.1 q.1.2.1 q.1.2.2.1
        q.1.2.2.2.1 q.1.2.2.2.2.1 (q.2.1 + 1)) := by
  have hinput : Primrec
      (fun q : T1MarkingEventInput ×
          (Nat × List T1MarkEvent) => q.1) :=
    Primrec.fst
  have hnext : Primrec
      (fun q : T1MarkingEventInput ×
          (Nat × List T1MarkEvent) => q.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have hc := t1EventInput_c_primrec.comp hinput
  have hn := t1EventInput_n_primrec.comp hinput
  have hk := t1EventInput_k_primrec.comp hinput
  have hepsilon := t1EventInput_epsilon_primrec.comp hinput
  have hd := t1EventInput_d_primrec.comp hinput
  have hB := t1BStage_primrec_uniform.comp
    (Primrec.pair hc
      (Primrec.pair hn (Primrec.pair hepsilon hnext)))
  have hC2 := t1CDoublePrimeBatches_primrec_uniform.comp
    (Primrec.pair hc
      (Primrec.pair hn
        (Primrec.pair hk (Primrec.pair hd hnext))))
  have hC1 := t1CPrimeStage_primrec_uniform.comp
    (Primrec.pair hc (Primrec.pair hk hnext))
  have hD := t1DStage_primrec_uniform.comp
    (Primrec.pair hc
      (Primrec.pair hn (Primrec.pair hk hnext)))
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (t1MarkEvent_mapB_primrec.comp hB)
        (t1MarkEvent_mapCDoublePrime_primrec.comp hC2))
      (t1MarkEvent_mapCPrime_primrec.comp hC1))
    (t1MarkEvent_mapD_primrec.comp hD)

/-- The merged chronological stream is primitive recursive uniformly in the
plain machine code and all numerical parameters. -/
theorem t1MarkingEventStage_primrec :
    Primrec
      (fun p : Code × Nat × Nat × Nat × Nat × Nat =>
        t1MarkingEventStage p.1 p.2.1 p.2.2.1
          p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have hbase : Primrec (fun p : T1MarkingEventInput =>
      (t1MarkingEventsUpToTime p.1 p.2.1 p.2.2.1
        p.2.2.2.1 p.2.2.2.2.1 0).eraseDups) := by
    exact t1EraseDupsEvent_primrec.comp
      t1MarkingEventsAtZero_primrec
  have hstep : Primrec₂
      (fun (p : T1MarkingEventInput)
        (z : Nat × List T1MarkEvent) =>
          (z.2 ++ t1MarkingEventsUpToTime p.1 p.2.1
            p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
              (z.1 + 1)).eraseDups) := by
    exact (t1EraseDupsEvent_primrec.comp
      (Primrec.list_append.comp
        (Primrec.snd.comp Primrec.snd)
        t1MarkingEventsAtNext_primrec)).to₂
  refine (Primrec.nat_rec' t1EventInput_t_primrec
    hbase hstep).of_eq ?_
  intro p
  induction p.2.2.2.2.2 with
  | zero => rfl
  | succ t ih =>
      simp only [t1MarkingEventStage]
      rw [← ih]

/-- The merged chronological stream is computable uniformly in the plain
machine code and all numerical parameters. -/
theorem t1MarkingEventStage_computable :
    Computable
      (fun p : Code × Nat × Nat × Nat × Nat × Nat =>
        t1MarkingEventStage p.1 p.2.1 p.2.2.1
          p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  t1MarkingEventStage_primrec.to_comp

theorem t1MarkingEventStage_nodup
    (c : Code) (n k epsilon d t : Nat) :
    (t1MarkingEventStage c n k epsilon d t).Nodup := by
  cases t <;> exact nodup_eraseDups_t1MarkEvent _

theorem t1MarkingEventStage_prefix
    (c : Code) (n k epsilon d t : Nat) :
    t1MarkingEventStage c n k epsilon d t <+:
      t1MarkingEventStage c n k epsilon d (t + 1) := by
  change t1MarkingEventStage c n k epsilon d t <+:
    (t1MarkingEventStage c n k epsilon d t ++
      t1MarkingEventsUpToTime c n k epsilon d
        (t + 1)).eraseDups
  exact prefix_eraseDups_append_of_nodup _ _
    (t1MarkingEventStage_nodup c n k epsilon d t)

/-- The chronological event stream is prefix-monotone at arbitrary times. -/
theorem t1MarkingEventStage_mono
    (c : Code) (n k epsilon d : Nat) {t u : Nat}
    (htu : t ≤ u) :
    t1MarkingEventStage c n k epsilon d t <+:
      t1MarkingEventStage c n k epsilon d u := by
  induction u, htu using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ u htu ih =>
      exact ih.trans
        (t1MarkingEventStage_prefix c n k epsilon d u)

private theorem t1MarkingEventsUpToTime_mem_eventStage
    (c : Code) (n k epsilon d t : Nat) :
    ∀ event ∈ t1MarkingEventsUpToTime c n k epsilon d t,
      event ∈ t1MarkingEventStage c n k epsilon d t := by
  intro event hevent
  cases t with
  | zero =>
      exact t1_mem_eraseDups_event.mpr hevent
  | succ t =>
      exact t1_mem_eraseDups_event.mpr
        (List.mem_append_right _ hevent)

private theorem t1EventStage_absorbs_visible
    (c : Code) (n k epsilon d t : Nat) :
    (t1MarkingEventStage c n k epsilon d t ++
      t1MarkingEventsUpToTime c n k epsilon d t).eraseDups =
        t1MarkingEventStage c n k epsilon d t := by
  rw [List.eraseDups_append,
    eraseDups_eq_self_of_nodup
      (t1MarkingEventStage_nodup c n k epsilon d t)]
  have hremove :
      (t1MarkingEventsUpToTime c n k epsilon d t).removeAll
        (t1MarkingEventStage c n k epsilon d t) = [] := by
    have haux : ∀ events : List T1MarkEvent,
        (∀ event ∈ events,
          event ∈ t1MarkingEventStage c n k epsilon d t) →
        events.removeAll
          (t1MarkingEventStage c n k epsilon d t) = [] := by
      intro events hevents
      induction events with
      | nil => rfl
      | cons event events ih =>
          have hevent :
              event ∈ t1MarkingEventStage c n k epsilon d t :=
            hevents event (by simp)
          have htail : ∀ other ∈ events,
              other ∈
                t1MarkingEventStage c n k epsilon d t := by
            intro other hother
            exact hevents other (by simp [hother])
          simpa [List.removeAll, hevent] using ih htail
    apply haux
    exact t1MarkingEventsUpToTime_mem_eventStage
      c n k epsilon d t
  rw [hremove]
  simp

/-- Every fixed marking-event stream stabilizes because all four component
streams stabilize. -/
theorem t1MarkingEventStage_stabilizes
    (c : Code) (n k epsilon d : Nat) :
    ∃ T, ∀ t, T ≤ t →
      t1MarkingEventStage c n k epsilon d t =
        t1MarkingEventStage c n k epsilon d T := by
  obtain ⟨TB, hB⟩ := t1BStage_stabilizes c n epsilon
  obtain ⟨TCD, hCD⟩ :=
    t1CDoublePrimeBatches_stabilizes c n k d
  obtain ⟨TCP, hCP⟩ := t1CPrimeStage_stabilizes c k
  obtain ⟨TD, hD⟩ := t1DStage_stabilizes c n k
  let T := max (max TB TCD) (max TCP TD)
  have hvisible : ∀ t, T ≤ t →
      t1MarkingEventsUpToTime c n k epsilon d t =
        t1MarkingEventsUpToTime c n k epsilon d T := by
    intro t ht
    unfold t1MarkingEventsUpToTime
    rw [hB t (by omega), hB T (by simp [T]),
      hCD t (by omega), hCD T (by simp [T]),
      hCP t (by omega), hCP T (by simp [T]),
      hD t (by omega), hD T (by simp [T])]
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
      rw [show t1MarkingEventStage c n k epsilon d (t + 1) =
          (t1MarkingEventStage c n k epsilon d t ++
            t1MarkingEventsUpToTime c n k epsilon d
              (t + 1)).eraseDups
        from rfl,
        ih, hvisible (t + 1) (by omega),
        t1EventStage_absorbs_visible]

/-- Any event that occurs somewhere in a stabilized chronological stream is
already present at the chosen stabilization stage. -/
theorem t1MarkingEventStage_mem_at_stabilization
    (c : Code) (n k epsilon d T : Nat)
    (hstable : ∀ t, T ≤ t →
      t1MarkingEventStage c n k epsilon d t =
        t1MarkingEventStage c n k epsilon d T)
    {event : T1MarkEvent}
    (hevent : ∃ t,
      event ∈ t1MarkingEventStage c n k epsilon d t) :
    event ∈ t1MarkingEventStage c n k epsilon d T := by
  obtain ⟨t, ht⟩ := hevent
  rcases le_total t T with hle | hge
  · exact
      (t1MarkingEventStage_mono c n k epsilon d hle).sublist.subset ht
  · rw [hstable t hge] at ht
    exact ht

/-- A member of a model emitted by the `B` stream has the extensional
`B`-mark. This is the soundness bridge used by a later reachable-state
invariant. -/
theorem t1BStage_member_marked
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n epsilon t : Nat} {w x : BitString}
    (hw : w ∈ t1BStage c n epsilon t)
    (hx : x ∈ t1CodeToSet w) (hlen : x.length = n) :
    T1BMarked V n epsilon x := by
  obtain ⟨S, hS, hcode, hcomp, hcard⟩ :=
    t1BStage_sound hc hw
  have hxS : x ∈ S := by
    rw [hcode, t1CodeToSet_codedUniformOn] at hx
    exact hx
  exact ⟨hlen, S, hS, hxS, hcomp, hcard⟩

/-- Every extensional `B`-model eventually produces its chronological event. -/
theorem t1BEvent_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k epsilon d : Nat}
    (S : Finset BitString) (hS : S.Nonempty)
    (hcomp : plainSetComplexity V S hS ≤ (epsilon : ENat))
    (hcard : S.card ≤ 2 ^ (n - epsilon - 4)) :
    ∃ t, T1MarkEvent.bSet (codedUniformOn S hS).code ∈
      t1MarkingEventStage c n k epsilon d t := by
  obtain ⟨t, ht⟩ :=
    t1BStage_complete hc S hS hcomp hcard
  refine ⟨t, t1MarkingEventsUpToTime_mem_eventStage
    c n k epsilon d t _ ?_⟩
  simp [t1MarkingEventsUpToTime, ht]

/-- When the same canonical model code has appeared in `C'` and in a `C''`
batch, every length-`n` member of that model has the extensional `C`-mark. -/
theorem t1CStreams_member_marked
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k d t₁ t₂ : Nat} {batch : List BitString}
    {w x : BitString}
    (hp : w ∈ t1CPrimeStage c k t₁)
    (hbatch :
      batch ∈ t1CDoublePrimeBatches c n k d t₂)
    (hw : w ∈ batch) (hx : x ∈ t1CodeToSet w)
    (hlen : x.length = n) :
    T1CMarked V n k d x := by
  obtain ⟨M, hM, hMcode, hMcomp⟩ :=
    t1CPrimeStage_sound hc hp
  obtain ⟨D, hD, hDcomp, hDcard, hsound⟩ :=
    t1CDoublePrimeBatches_sound hc hbatch
  obtain ⟨hwD, N, hN, hNcode, hNcard⟩ :=
    hsound w hw
  have hdecodeM : t1CodeToSet w = M := by
    rw [hMcode, t1CodeToSet_codedUniformOn]
  have hdecodeN : t1CodeToSet w = N := by
    rw [hNcode, t1CodeToSet_codedUniformOn]
  have hxM : x ∈ M := by
    rw [← hdecodeM]
    exact hx
  have hMcard : M.card ≤ 2 ^ (n - k - 4) := by
    calc
      M.card = (t1CodeToSet w).card :=
        congrArg Finset.card hdecodeM |>.symm
      _ = N.card := congrArg Finset.card hdecodeN
      _ ≤ 2 ^ (n - k - 4) := hNcard
  have hprofile :
      InPlainDescriptionProfile V
        (codedUniformOn M hM).code d n := by
    rw [← hMcode]
    exact ⟨D, hD, hwD, hDcomp, hDcard⟩
  exact ⟨hlen, M, hM, hxM, hMcomp, hMcard, hprofile⟩

/-- Every extensional `C`-mark eventually has a common canonical model code
visible on the `C'` side and inside one visible `C''` batch. -/
theorem t1CEvents_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k d epsilon : Nat} {x : BitString}
    (hx : T1CMarked V n k d x) :
    ∃ w batch tPrime tDouble,
      x ∈ t1CodeToSet w ∧
      T1MarkEvent.cPrimeModel w ∈
        t1MarkingEventStage c n k epsilon d tPrime ∧
      T1MarkEvent.cDoublePrimeBatch batch ∈
        t1MarkingEventStage c n k epsilon d tDouble ∧
      w ∈ batch := by
  obtain ⟨_hlen, M, hM, hxM, hcomp, hcard, hprofile⟩ := hx
  let w := (codedUniformOn M hM).code
  obtain ⟨tPrime, hPrime⟩ :=
    t1CPrimeStage_complete hc M hM hcomp
  obtain ⟨tDouble, batch, hbatch, hw⟩ :=
    t1CDoublePrimeBatches_complete hc M hM hcard hprofile
  refine ⟨w, batch, tPrime, tDouble, ?_, ?_, ?_, hw⟩
  · dsimp [w]
    rw [t1CodeToSet_codedUniformOn]
    exact hxM
  · apply t1MarkingEventsUpToTime_mem_eventStage
      c n k epsilon d tPrime
    simp [t1MarkingEventsUpToTime, w, hPrime]
  · apply t1MarkingEventsUpToTime_mem_eventStage
      c n k epsilon d tDouble
    simp [t1MarkingEventsUpToTime, hbatch]

/-- Every string emitted by the `D` stream has the extensional `D`-mark. -/
theorem t1DStage_member_marked
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k t : Nat} {w : BitString}
    (hw : w ∈ t1DStage c n k t) :
    T1DMarked V n k w :=
  t1DStage_sound hc hw

/-- Every extensional `D`-marked string eventually produces its event. -/
theorem t1DEvent_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k epsilon d : Nat} {w : BitString}
    (hlen : w.length = n) (hcomp : plainK V w < (k : ENat)) :
    ∃ t, T1MarkEvent.dString w ∈
      t1MarkingEventStage c n k epsilon d t := by
  obtain ⟨t, ht⟩ := t1DStage_complete hc hlen hcomp
  refine ⟨t, t1MarkingEventsUpToTime_mem_eventStage
    c n k epsilon d t _ ?_⟩
  simp [t1MarkingEventsUpToTime, ht]

/-- Event-level final-survivor extraction.  Once the event stream has
stabilized, avoiding every visible `B` model, every visible `C' ∩ C''`
intersection, and the visible `D` string event implies avoidance of the three
extensional marking predicates.  The reachable-state construction only needs
to establish the three event-level avoidance hypotheses below. -/
theorem t1FinalEventAvoidance
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {n k epsilon d T : Nat} {x : BitString}
    (hstable : ∀ t, T ≤ t →
      t1MarkingEventStage c n k epsilon d t =
        t1MarkingEventStage c n k epsilon d T)
    (hB : ∀ code,
      T1MarkEvent.bSet code ∈
          t1MarkingEventStage c n k epsilon d T →
        x ∉ t1CodeToSet code)
    (hC : ∀ code batch,
      T1MarkEvent.cPrimeModel code ∈
          t1MarkingEventStage c n k epsilon d T →
      T1MarkEvent.cDoublePrimeBatch batch ∈
          t1MarkingEventStage c n k epsilon d T →
      code ∈ batch →
        x ∉ t1CodeToSet code)
    (hD : T1MarkEvent.dString x ∉
      t1MarkingEventStage c n k epsilon d T) :
    ¬ T1BMarked V n epsilon x ∧
      ¬ T1CMarked V n k d x ∧
      ¬ T1DMarked V n k x := by
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    obtain ⟨_hlen, S, hS, hxS, hcomp, hcard⟩ := hx
    have hevent := t1BEvent_complete
      (c := c) (k := k) (d := d) hc S hS hcomp hcard
    have hfinal := t1MarkingEventStage_mem_at_stabilization
      c n k epsilon d T hstable hevent
    have hnot := hB (codedUniformOn S hS).code hfinal
    rw [t1CodeToSet_codedUniformOn] at hnot
    exact hnot hxS
  · intro hx
    obtain ⟨code, batch, tPrime, tDouble, hxcode,
      hPrime, hDouble, hcode⟩ :=
      t1CEvents_complete (c := c) (epsilon := epsilon) hc hx
    have hPrimeFinal := t1MarkingEventStage_mem_at_stabilization
      c n k epsilon d T hstable ⟨tPrime, hPrime⟩
    have hDoubleFinal := t1MarkingEventStage_mem_at_stabilization
      c n k epsilon d T hstable ⟨tDouble, hDouble⟩
    exact hC code batch hPrimeFinal hDoubleFinal hcode hxcode
  · intro hx
    have hevent := t1DEvent_complete
      (c := c) (epsilon := epsilon) (d := d) hc hx.1 hx.2
    exact hD (t1MarkingEventStage_mem_at_stabilization
      c n k epsilon d T hstable hevent)

/-- Finite-set survivor extraction used by the eventual run invariant: a
current model disjoint from the `B` marks and not saturated by the `C ∪ D`
marks contains a string outside all three classes. -/
theorem t1_exists_current_survivor
    {current bMarked cMarked dMarked : Finset BitString}
    (hB : Disjoint current bMarked)
    (hCD : ¬ current ⊆ cMarked ∪ dMarked) :
    ∃ x ∈ current,
      x ∉ bMarked ∧ x ∉ cMarked ∧ x ∉ dMarked := by
  rw [Finset.subset_iff] at hCD
  push Not at hCD
  obtain ⟨x, hx, hxcd⟩ := hCD
  have hxb : x ∉ bMarked := by
    intro hmem
    exact Finset.disjoint_left.mp hB hx hmem
  simp only [Finset.mem_union, not_or] at hxcd
  exact ⟨x, hx, hxb, hxcd.1, hxcd.2⟩

/-- Assemble one total sparse-selector rebuild from the current marked set and
the visible `C″` codes.  The conclusion is exactly the cardinality, cube
containment, and sparse-intersection package needed by a reachable run step. -/
theorem t1_rebuild_selector_spec (V : Map) (c : Code) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon t
      (Marked : Finset BitString) (seen : List BitString),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      (∀ x ∈ Marked,
        T1BMarked V n epsilon x ∨
          (∃ d, T1CMarked V n k d x) ∨
          T1DMarked V n k x) →
      seen.toFinset ⊆
        (t1CDoublePrimeBatches c n k
          (epsilon + logSlack cDesc n) t).flatten.toFinset →
      let U := canonicalFinsetList (stringsOfLength n \ Marked)
      let Cs := seen.map canonicalPointListOfCode
      let A := t1SparseSubsetSelectorList U Cs
        (2 ^ (k - epsilon)) (cSparse * n + cSparse)
      A.Nodup ∧
        A.toFinset ⊆ U.toFinset ∧
        A.length = 2 ^ (k - epsilon) ∧
        ∀ C ∈ Cs,
          (A.toFinset ∩ C.toFinset).card ≤
            cSparse * n + cSparse := by
  intro cDesc
  obtain ⟨c0, cSparse, hSelector⟩ :=
    t1_sparse_selector_available cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon t Marked seen hc0 hEpsilon hLength
    hMarked hSeen
  let U := canonicalFinsetList (stringsOfLength n \ Marked)
  let Cs := seen.map canonicalPointListOfCode
  have hEpsilonLength : epsilon + 4 ≤ n := by omega
  have hUnmarked :
      2 ^ (n - 1) ≤ (stringsOfLength n \ Marked).card :=
    t1_unmarked_card_ge_half V n k epsilon hEpsilonLength
      hLength Marked hMarked
  have hUSpec := t1_unmarked_list_spec n Marked
  have hULength : 2 ^ (n - 1) ≤ U.length := by
    rw [show U.length = (stringsOfLength n \ Marked).card
      from hUSpec.2.2]
    exact hUnmarked
  have hFamily :
      (Cs.map List.toFinset).toFinset.card ≤
        2 ^ (n + (epsilon + logSlack cDesc n) + 1) := by
    have h_eq : Cs.map List.toFinset =
        seen.map (fun w => (canonicalPointListOfCode w).toFinset) := by
      dsimp [Cs]
      rw [List.map_map]
      rfl
    rw [h_eq]
    exact t1_seen_cdouble_family_card_le c n k (epsilon + logSlack cDesc n) t seen hSeen
  have hSmall : ∀ C ∈ Cs,
      C.toFinset.card ≤ 2 ^ (n - k - 4) := by
    intro C hC
    change C ∈ seen.map canonicalPointListOfCode at hC
    rw [List.mem_map] at hC
    obtain ⟨w, hw, rfl⟩ := hC
    exact t1_seen_cdouble_model_card_le c n k
      (epsilon + logSlack cDesc n) t seen hSeen hw
  exact hSelector n k epsilon U Cs hc0 hEpsilon hLength
    hUSpec.1 hULength hFamily hSmall

/-- Structural endpoint of the chronological marking construction: existence of
a `2^(k-ε)`-element cube of length-`n` strings together with a surviving element
avoiding all three extensional marking families.

This is the *counting* half of the source proof of Theorem `t1` (items (a)–(d)
minus the complexity clause `K(A) ≤ ε + O(log n)` of (a)).  The source is
explicit that this half is easy — "we cannot let `A` be *any* `2^{k-ε}`-element
non-covered set, as in that case `K(A)` could be large" — the entire difficulty
of `t1` lives in the *complexity* of `A`, which is the separate obligation
`exists_t1_avoiding_set_core` for a future reachable-run worker.  Hence the
structural existence follows
directly from the already-proved static union bound `t1_unmarked_card_ge_half`:
the unmarked length-`n` set has at least `2^(n-1) ≥ 2^(k-ε)` elements, every one
of which avoids the three families; extract a `2^(k-ε)`-subset and take any
element.  (Avoiding `∃ d, T1CMarked` in particular avoids the fixed-budget
`T1CMarked V n k (ε + logSlack cDesc n)`.) -/
theorem exists_t1_avoiding_set_structural
    (V : Map) (_hV : isOptimalConditional V) :
    ∀ cDesc, ∃ c0 _cSparse : Nat, ∀ n k epsilon,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      ∃ A x,
        A ⊆ stringsOfLength n ∧
        A.card = 2 ^ (k - epsilon) ∧
        x ∈ A ∧
        ¬ T1BMarked V n epsilon x ∧
        ¬ T1CMarked V n k
          (epsilon + logSlack cDesc n) x ∧
        ¬ T1DMarked V n k x := by
  classical
  intro cDesc
  refine ⟨0, 0, ?_⟩
  intro n k epsilon _hc0 hεk hkn
  have hεn : epsilon + 4 ≤ n := by omega
  set Marked : Finset BitString :=
    (stringsOfLength n).filter
      (fun x => T1BMarked V n epsilon x ∨
        (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x)
    with hMarkedDef
  have hMarkedSpec : ∀ x ∈ Marked,
      T1BMarked V n epsilon x ∨
        (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x := by
    intro x hx
    rw [hMarkedDef] at hx
    exact (Finset.mem_filter.mp hx).2
  have hge : 2 ^ (n - 1) ≤ (stringsOfLength n \ Marked).card :=
    t1_unmarked_card_ge_half V n k epsilon hεn hkn Marked hMarkedSpec
  have hcard_le : 2 ^ (k - epsilon) ≤ (stringsOfLength n \ Marked).card :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hge
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard_le
  have hAstr : A ⊆ stringsOfLength n := hAsub.trans Finset.sdiff_subset
  have hApos : 0 < A.card := by rw [hAcard]; positivity
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hApos
  have hxdiff := hAsub hx
  rw [Finset.mem_sdiff] at hxdiff
  obtain ⟨hxstr, hxnm⟩ := hxdiff
  have hxnotP : ¬ (T1BMarked V n epsilon x ∨
      (∃ d, T1CMarked V n k d x) ∨ T1DMarked V n k x) := by
    intro hPx
    apply hxnm
    rw [hMarkedDef]
    exact Finset.mem_filter.mpr ⟨hxstr, hPx⟩
  push Not at hxnotP
  obtain ⟨hxB, hxC, hxD⟩ := hxnotP
  exact ⟨A, x, hAstr, hAcard, hx, hxB,
    hxC (epsilon + logSlack cDesc n), hxD⟩

end Kolmogorov
