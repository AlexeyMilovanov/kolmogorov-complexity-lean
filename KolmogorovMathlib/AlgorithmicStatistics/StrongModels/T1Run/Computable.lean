import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Transitions

/-!
# The run step of Theorem T1 is computable

One step of the marking run — receive an event, mark the points it names, charge it, and
rebuild the current model when the sparse selector says so — has to be primitive recursive for
the run to be describable by a short program.  This module discharges that, by presenting the
step input as the flat datum `T1RunStepInputData` (`T1RunStepInput.toData`, `.ofData`,
`t1RunStepInputDataEquiv`) and proving each branch computable
(`t1RunStepDRebuilt_computable`, `t1RunStepDSaturated_computable`,
`t1RunStepDStringFn_computable`, and their neighbours for the other event kinds).

`t1RunRebuild_model_spec` says a rebuild produces a duplicate-free block of exactly
`2 ^ (k - epsilon)` unmarked strings, and the `_history` lemmas
(`t1RunStep_bSet_history`, `t1RunStep_cPrime_history`, `t1RunStep_cDouble_history`) record
what each kind of event does to the marked lists and charges.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

private theorem t1RunStepDRebuilt_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepDRebuilt p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun p : Q => p.1) := Primrec.fst
  have hinput : Computable (fun p : Q =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepDCharged p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepDCharged_primrec.to_comp)))
  exact t1RunRebuildTuple_computable.comp hinput

private theorem t1RunStepDSaturated_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepDSaturated p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturationRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      t1RunStepDRebuilt_computable)).of_eq
        (fun p => by rfl)

private theorem t1RunStepDSaturatedGuard_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDSaturatedGuard p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturated_primrec.comp
    (t1RunStepDCharged_primrec.pair
      (t1RunStepParams_quota_primrec.comp hparams))).of_eq
        (fun p => by rfl)

private theorem t1RunStepDStringFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepDStringFn p) := by
  exact (Computable.cond
    t1RunStepDSaturatedGuard_primrec.to_comp
    t1RunStepDSaturated_computable
    t1RunStepDCharged_primrec.to_comp).of_eq
      (fun p => by
        simp only [t1RunStepDStringFn]
        cases t1RunStepDSaturatedGuard p <;> rfl)

private abbrev T1RunStepInputData :=
  T1RunStepParams × T1MarkEvent

private def T1RunStepInput.toData
    (input : T1RunStepInput) : T1RunStepInputData :=
  ((((input.cSparse, input.n), (input.k, input.epsilon)),
    (input.quota, input.s)), input.event)

private def T1RunStepInput.ofData
    (p : T1RunStepInputData) : T1RunStepInput :=
  { cSparse := t1RunStepParamsCSparse p.1
  , n := t1RunStepParamsN p.1
  , k := t1RunStepParamsK p.1
  , epsilon := t1RunStepParamsEpsilon p.1
  , quota := t1RunStepParamsQuota p.1
  , s := t1RunStepParamsState p.1
  , event := p.2 }

private def t1RunStepInputDataEquiv :
    T1RunStepInput ≃ T1RunStepInputData where
  toFun := T1RunStepInput.toData
  invFun := T1RunStepInput.ofData
  left_inv input := by cases input; rfl
  right_inv p := by
    rcases p with
      ⟨⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, s⟩⟩, event⟩
    rfl

instance : Primcodable T1RunStepInput :=
  Primcodable.ofEquiv _ t1RunStepInputDataEquiv

private theorem t1RunStepInput_toData_primrec :
    Primrec T1RunStepInput.toData :=
  Primrec.of_equiv

private noncomputable def t1RunStepTailRep
    (p : T1RunStepParams × (BitString ⊕ BitString)) :
    T1RunState :=
  match p.2 with
  | .inl w => t1RunStepCPrimeFn (p.1, w)
  | .inr x => t1RunStepDStringFn (p.1, x)

private theorem t1RunStepTailRep_computable :
    Computable t1RunStepTailRep := by
  have hc : Computable₂ (fun
      (p : T1RunStepParams × (BitString ⊕ BitString))
      (w : BitString) => t1RunStepCPrimeFn (p.1, w)) :=
    t1RunStepCPrimeFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have hd : Computable₂ (fun
      (p : T1RunStepParams × (BitString ⊕ BitString))
      (x : BitString) => t1RunStepDStringFn (p.1, x)) :=
    t1RunStepDStringFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact (Computable.sumCasesOn Computable.snd hc hd).of_eq
    (fun p => by
      rcases p with ⟨params, event⟩
      cases event <;> rfl)

private noncomputable def t1RunStepRestRep
    (p : T1RunStepParams ×
      (List BitString ⊕ (BitString ⊕ BitString))) :
    T1RunState :=
  match p.2 with
  | .inl batch => t1RunStepCDoubleFn (p.1, batch)
  | .inr tail => t1RunStepTailRep (p.1, tail)

private theorem t1RunStepRestRep_computable :
    Computable t1RunStepRestRep := by
  have hcd : Computable₂ (fun
      (p : T1RunStepParams ×
        (List BitString ⊕ (BitString ⊕ BitString)))
      (batch : List BitString) =>
        t1RunStepCDoubleFn (p.1, batch)) :=
    t1RunStepCDoubleFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have htail : Computable₂ (fun
      (p : T1RunStepParams ×
        (List BitString ⊕ (BitString ⊕ BitString)))
      (tail : BitString ⊕ BitString) =>
        t1RunStepTailRep (p.1, tail)) :=
    t1RunStepTailRep_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact (Computable.sumCasesOn Computable.snd hcd htail).of_eq
    (fun p => by
      rcases p with ⟨params, event⟩
      cases event <;> rfl)

private noncomputable def t1RunStepRep
    (p : T1RunStepParams ×
      (BitString ⊕ List BitString ⊕ BitString ⊕ BitString)) :
    T1RunState :=
  match p.2 with
  | .inl w => t1RunStepBSetFn (p.1, w)
  | .inr rest => t1RunStepRestRep (p.1, rest)

private theorem t1RunStepRep_computable :
    Computable t1RunStepRep := by
  have hb : Computable₂ (fun
      (p : T1RunStepParams ×
        (BitString ⊕ List BitString ⊕ BitString ⊕ BitString))
      (w : BitString) => t1RunStepBSetFn (p.1, w)) :=
    t1RunStepBSetFn_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  have hrest : Computable₂ (fun
      (p : T1RunStepParams ×
        (BitString ⊕ List BitString ⊕ BitString ⊕ BitString))
      (rest : List BitString ⊕ BitString ⊕ BitString) =>
        t1RunStepRestRep (p.1, rest)) :=
    t1RunStepRestRep_computable.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact (Computable.sumCasesOn Computable.snd hb hrest).of_eq
    (fun p => by
      rcases p with ⟨params, event⟩
      cases event <;> rfl)

/-- One step of the T1 run is computable jointly in the parameters, the state and the event. -/
theorem t1RunStep_computable_uniform :
    Computable T1RunStepInput.run := by
  have hevent : Primrec (fun p : T1RunStepInputData =>
      t1MarkEventEquiv p.2) :=
    Primrec.of_equiv.comp Primrec.snd
  have hrep : Computable (fun input : T1RunStepInput =>
      ((T1RunStepInput.toData input).1,
        t1MarkEventEquiv (T1RunStepInput.toData input).2)) :=
    ((Primrec.fst.comp t1RunStepInput_toData_primrec).to_comp.pair
      (hevent.comp t1RunStepInput_toData_primrec).to_comp)
  exact (t1RunStepRep_computable.comp hrep).of_eq
    (fun input => by
      cases input
      rename_i cSparse n k epsilon quota s event
      cases event <;> rfl)

private noncomputable def t1RunFromEventsNat
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) (i : Nat) : T1RunState :=
  Nat.rec s
    (fun j current =>
      t1RunStep cSparse n k epsilon quota current
        (events.getD j default))
    i

private abbrev T1RunFoldInput :=
  T1RunStepParams × (List T1MarkEvent × Nat)

private noncomputable def t1RunFromEventsNatInput
    (p : T1RunFoldInput) : T1RunState :=
  t1RunFromEventsNat
    (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
    (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
    (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
    p.2.1 p.2.2

private theorem t1RunFromEventsNatInput_computable :
    Computable t1RunFromEventsNatInput := by
  have hparams : Primrec (fun p : T1RunFoldInput => p.1) :=
    Primrec.fst
  have hevents : Primrec (fun p : T1RunFoldInput => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : T1RunFoldInput => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hinitial : Primrec (fun p : T1RunFoldInput =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hstep : Computable₂ (fun (p : T1RunFoldInput)
      (rec : Nat × T1RunState) =>
      t1RunStep
        (t1RunStepParamsCSparse p.1)
        (t1RunStepParamsN p.1)
        (t1RunStepParamsK p.1)
        (t1RunStepParamsEpsilon p.1)
        (t1RunStepParamsQuota p.1)
        rec.2 (p.2.1[rec.1]?.getD default)) := by
    let Q := T1RunFoldInput × (Nat × T1RunState)
    have hp : Primrec (fun q : Q => q.1) := Primrec.fst
    have hfixed : Primrec (fun q : Q => q.1.1) :=
      Primrec.fst.comp hp
    have hrec : Primrec (fun q : Q => q.2) := Primrec.snd
    have hevent : Primrec (fun q : Q =>
        q.1.2.1[q.2.1]?.getD default) :=
      (Primrec.list_getD default).comp
        ((Primrec.fst.comp (Primrec.snd.comp hp)))
        (Primrec.fst.comp hrec)
    have hnewParams : Primrec (fun q : Q =>
        ((((t1RunStepParamsCSparse q.1.1,
          t1RunStepParamsN q.1.1),
          (t1RunStepParamsK q.1.1,
            t1RunStepParamsEpsilon q.1.1)),
          (t1RunStepParamsQuota q.1.1, q.2.2)) :
          T1RunStepParams)) :=
      ((t1RunStepParams_cSparse_primrec.comp hfixed).pair
        (t1RunStepParams_n_primrec.comp hfixed)).pair
        ((t1RunStepParams_k_primrec.comp hfixed).pair
          (t1RunStepParams_epsilon_primrec.comp hfixed)) |>.pair
        ((t1RunStepParams_quota_primrec.comp hfixed).pair
          (Primrec.snd.comp hrec))
    have heventRep : Primrec (fun q : Q =>
        t1MarkEventEquiv (q.1.2.1[q.2.1]?.getD default)) :=
      Primrec.of_equiv.comp hevent
    exact (t1RunStepRep_computable.comp
      (hnewParams.to_comp.pair heventRep.to_comp)).of_eq
        (fun q => by
          rcases q with ⟨p, ⟨j, current⟩⟩
          rcases p with ⟨params, ⟨events, i⟩⟩
          generalize heventVal :
            events[j]?.getD default = event
          cases event <;>
            simp [t1RunStep, t1RunStepRep,
              t1RunStepRestRep, t1RunStepTailRep,
              t1MarkEventEquiv,
              t1RunStepParamsCSparse, t1RunStepParamsN,
              t1RunStepParamsK, t1RunStepParamsEpsilon,
              t1RunStepParamsQuota, heventVal])
  exact (Computable.nat_rec hi.to_comp hinitial.to_comp hstep).of_eq
    (fun p => by rfl)

private theorem t1RunFromEventsNat_eq_take
    (cSparse n k epsilon quota : Nat) (s : T1RunState)
    (events : List T1MarkEvent) (i : Nat)
    (hi : i ≤ events.length) :
    t1RunFromEventsNat cSparse n k epsilon quota s events i =
      t1RunFromEvents cSparse n k epsilon quota s
        (events.take i) := by
  induction i with
  | zero =>
      simp [t1RunFromEventsNat, t1RunFromEvents]
  | succ i ih =>
      have hilt : i < events.length := hi
      have htake :
          events.take (i + 1) =
            events.take i ++ [events.getD i default] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hilt,
          List.getD_eq_getElem events default hilt]
        rfl
      change t1RunStep cSparse n k epsilon quota
          (t1RunFromEventsNat cSparse n k epsilon quota s events i)
          (events.getD i default) =
        t1RunFromEvents cSparse n k epsilon quota s
          (events.take (i + 1))
      rw [ih (Nat.le_of_succ_le hi), htake]
      simp [t1RunFromEvents, List.foldl_append]

private theorem t1RunFromEvents_computable :
    Computable (fun p : T1RunStepParams × List T1MarkEvent =>
      t1RunFromEvents
        (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
        (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
        (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
        p.2) := by
  have hinput : Primrec (fun p :
      T1RunStepParams × List T1MarkEvent =>
      ((p.1, p.2, p.2.length) : T1RunFoldInput)) :=
    Primrec.fst.pair
      (Primrec.snd.pair
        (Primrec.list_length.comp Primrec.snd))
  exact (t1RunFromEventsNatInput_computable.comp
    hinput.to_comp).of_eq (fun p => by
      change
        t1RunFromEventsNat
          (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
          (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
          (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
          p.2 p.2.length =
        t1RunFromEvents
          (t1RunStepParamsCSparse p.1) (t1RunStepParamsN p.1)
          (t1RunStepParamsK p.1) (t1RunStepParamsEpsilon p.1)
          (t1RunStepParamsQuota p.1) (t1RunStepParamsState p.1)
          p.2
      rw [t1RunFromEventsNat_eq_take]
      · simp
      · exact le_rfl)

private abbrev T1RunInputData :=
  ((Nat.Partrec.Code × Nat) × (Nat × Nat)) ×
    ((Nat × Nat) × (Nat × Nat))

private def T1RunInput.toData (input : T1RunInput) :
    T1RunInputData :=
  (((input.c, input.cDesc), (input.cSparse, input.n)),
    ((input.k, input.epsilon), (input.quota, input.t)))

private def T1RunInput.ofData (p : T1RunInputData) :
    T1RunInput :=
  { c := p.1.1.1
  , cDesc := p.1.1.2
  , cSparse := p.1.2.1
  , n := p.1.2.2
  , k := p.2.1.1
  , epsilon := p.2.1.2
  , quota := p.2.2.1
  , t := p.2.2.2 }

private def t1RunInputDataEquiv :
    T1RunInput ≃ T1RunInputData where
  toFun := T1RunInput.toData
  invFun := T1RunInput.ofData
  left_inv input := by cases input; rfl
  right_inv p := by
    rcases p with
      ⟨⟨⟨c, cDesc⟩, ⟨cSparse, n⟩⟩,
        ⟨⟨k, epsilon⟩, ⟨quota, t⟩⟩⟩
    rfl

instance : Primcodable T1RunInput :=
  Primcodable.ofEquiv _ t1RunInputDataEquiv

private theorem t1RunInput_toData_primrec :
    Primrec T1RunInput.toData := by
  have h : Primrec (fun input : T1RunInput =>
      t1RunInputDataEquiv input) :=
    Primrec.of_equiv
  exact h.of_eq (fun input => by rfl)

/-- The state of the T1 run at a given stage is computable jointly in the parameters and the stage.
The state of the T1 run at a given stage is computable jointly in the parameters and the stage. -/
theorem t1RunAt_computable_uniform :
    Computable T1RunInput.run := by
  have hdata : Primrec (fun input : T1RunInput =>
      T1RunInput.toData input) :=
    t1RunInput_toData_primrec
  have hc : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).comp hdata
  have hcDesc : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.1.2) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).comp hdata
  have hcSparse : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).comp hdata
  have hn : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).1.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).comp hdata
  have hk : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).comp hdata
  have hepsilon : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.1.2) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).comp hdata
  have hquota : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.2.1) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hdata
  have ht : Primrec (fun input : T1RunInput =>
      (T1RunInput.toData input).2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp hdata
  have hinitial : Primrec (fun input : T1RunInput =>
      t1InitialRunState input.n input.k input.epsilon) :=
    (t1InitialRunState_primrec.comp (hn.pair (hk.pair hepsilon))).of_eq
      (fun input => by rfl)
  have hparams : Primrec (fun input : T1RunInput =>
      ((((input.cSparse, input.n), (input.k, input.epsilon)),
        (input.quota, t1InitialRunState input.n input.k input.epsilon)) :
        T1RunStepParams)) :=
    ((hcSparse.pair hn).pair (hk.pair hepsilon)).pair
      (hquota.pair hinitial)
  have hd : Primrec (fun input : T1RunInput =>
      input.epsilon + logSlack input.cDesc input.n) :=
    (Primrec.nat_add.comp hepsilon
      (Primrec₂.comp t1LogSlack_primrec hcDesc hn)).of_eq
        (fun input => by rfl)
  have heventInput : Primrec (fun input : T1RunInput =>
      ((input.c, input.n, input.k, input.epsilon,
        input.epsilon + logSlack input.cDesc input.n, input.t) :
        Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat)) :=
    hc.pair (hn.pair (hk.pair
      (hepsilon.pair (hd.pair ht))))
  have hevents : Primrec (fun input : T1RunInput =>
      t1MarkingEventStage input.c input.n input.k input.epsilon
        (input.epsilon + logSlack input.cDesc input.n) input.t) :=
    (t1MarkingEventStage_primrec.comp heventInput).of_eq
      (fun input => by rfl)
  exact (t1RunFromEvents_computable.comp
    (hparams.to_comp.pair hevents.to_comp)).of_eq
      (fun input => by
        cases input
        rfl)

/-- Each step either leaves the external and saturation counters and the version list untouched, or
increases their sum by one and appends exactly one new version. -/
theorem t1RunStep_versions (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent) :
    let s' := t1RunStep cSparse n k epsilon quota s event
    (s'.external + s'.saturation = s.external + s.saturation ∧
      s'.versions = s.versions) ∨
    (s'.external + s'.saturation = s.external + s.saturation + 1 ∧
      s'.versions = s.versions ++ [s'.current]) := by
  cases event with
  | bSet w =>
      simp [t1RunStep, t1RunStepBSetFn,
        t1RunExternalRebuildFinal, t1RunStepBSetRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepBSetPre, t1RunAppendB,
        t1RunStepParamsState]
      omega
  | cDoublePrimeBatch batch =>
      simp [t1RunStep, t1RunStepCDoubleFn,
        t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCDoublePre, t1RunAppendCSeenDouble,
        t1RunStepParamsState]
      omega
  | cPrimeModel w =>
      simp only [t1RunStep, t1RunStepCPrimeFn,
        t1RunStepCPrimeActiveFn]
      split
      · split <;>
          simp_all [t1RunStepCPrimeSaturated,
            t1RunSaturationRebuildFinal, t1RunStepCPrimeRebuilt,
            t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
            t1RunStepCPrimeCharged, t1RunChargeC, t1RunAppendC,
            t1RunStepCPrimeSeen, t1RunAppendSeenCPrime,
            t1RunStepParamsState]
        all_goals omega
      · simp [t1RunStepCPrimeSeen, t1RunAppendSeenCPrime,
          t1RunStepParamsState]
  | dString x =>
      simp only [t1RunStep, t1RunStepDStringFn]
      split <;>
        simp_all [t1RunStepDSaturated,
          t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
          t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
          t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
          t1RunStepParamsState]
      all_goals omega

/-- Rebuilding leaves the marking-history fields of the run state unchanged. -/
theorem t1RunRebuild_markingDataEq
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    T1RunMarkingDataEq s
      (t1RunRebuild cSparse n k epsilon s) := by
  simp [T1RunMarkingDataEq, t1RunRebuild,
    t1RunReplaceCurrent]

/-- A rebuild changes neither rebuild counters nor realized charge counters;
the caller increments exactly one rebuild counter when appropriate. -/
theorem t1RunRebuild_counters
    (cSparse n k epsilon : Nat) (s : T1RunState) :
    (t1RunRebuild cSparse n k epsilon s).external = s.external ∧
      (t1RunRebuild cSparse n k epsilon s).saturation = s.saturation ∧
      (t1RunRebuild cSparse n k epsilon s).totalC = s.totalC ∧
      (t1RunRebuild cSparse n k epsilon s).totalD = s.totalD := by
  simp [t1RunRebuild, t1RunReplaceCurrent]

/-- On a B-set event the run rebuilds from the prepared state and increments the external counter.
On a B-set event the run rebuilds from the prepared state and increments the external counter. -/
theorem t1RunStep_bSet_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    t1RunStep cSparse n k epsilon quota s (.bSet w) =
      { t1RunRebuild cSparse n k epsilon
          (t1RunBSetPrepared n s w) with
        external := s.external + 1 } := by
  simp only [t1RunStep, t1RunStepBSetFn,
    t1RunExternalRebuildFinal, t1RunStepBSetRebuilt,
    t1RunRebuildTuple, t1RunBSetPrepared,
    t1RunStepBSetPre, t1RunAppendB, t1RunValidPoints,
    t1RunStepParamsState, t1RunStepParamsN,
    t1RunStepParamsCSparse, t1RunStepParamsK,
    t1RunStepParamsEpsilon]
  rfl

/-- On a C''-batch event the run rebuilds from the prepared state and increments the external
counter. -/
theorem t1RunStep_cDouble_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    t1RunStep cSparse n k epsilon quota s
        (.cDoublePrimeBatch batch) =
      { t1RunRebuild cSparse n k epsilon
          (t1RunCDoublePrepared n s batch) with
        external := s.external + 1 } := by
  simp only [t1RunStep, t1RunStepCDoubleFn,
    t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
    t1RunRebuildTuple, t1RunCDoublePrepared,
    t1RunStepCDoublePre, t1RunAppendCSeenDouble,
    t1RunBatchValidPoints, t1RunStepParamsState,
    t1RunStepParamsN, t1RunStepParamsCSparse,
    t1RunStepParamsK, t1RunStepParamsEpsilon]
  rfl

/-- On a C'-model event the run only acts when the model was already seen as a C'' code, in which
case it rebuilds and charges the saturation counter if the prepared state is saturated. -/
theorem t1RunStep_cPrime_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    t1RunStep cSparse n k epsilon quota s (.cPrimeModel w) =
      if w ∈ s.seenCDouble then
        let prepared := t1RunCPrimePrepared n s w
        if t1RunSaturated prepared quota then
          { t1RunRebuild cSparse n k epsilon prepared with
            saturation := s.saturation + 1 }
        else prepared
      else t1RunCPrimeSeenPrepared s w := by
  by_cases hactive : w ∈ s.seenCDouble <;>
    simp [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, t1RunStepCPrimeActiveFn,
      t1RunStepCPrimeSaturatedGuard,
      t1RunStepCPrimeSaturated, t1RunSaturationRebuildFinal,
      t1RunStepCPrimeRebuilt, t1RunRebuildTuple,
      t1RunCPrimePrepared, t1RunStepCPrimeCharged,
      t1RunChargeC, t1RunAppendC, t1RunStepCPrimeSeen,
      t1RunAppendSeenCPrime, t1RunCPrimeSeenPrepared,
      t1RunStepCPrimePoints, t1RunValidPoints,
      t1RunHitCount, t1RunStepParamsState,
      t1RunStepParamsN, t1RunStepParamsCSparse,
      t1RunStepParamsK, t1RunStepParamsEpsilon,
      t1RunStepParamsQuota, hactive, List.mem_filter,
      Bool.decide_and, decide_eq_true_eq]
  congr

/-- On a D-string event the run passes to the prepared state, rebuilding and charging the saturation
counter when the prepared state is saturated. -/
theorem t1RunStep_dString_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (x : BitString) :
    t1RunStep cSparse n k epsilon quota s (.dString x) =
      let prepared := t1RunDPrepared n s x
      if t1RunSaturated prepared quota then
        { t1RunRebuild cSparse n k epsilon prepared with
          saturation := s.saturation + 1 }
      else prepared := by
  simp [t1RunStep, t1RunStepDStringFn,
    t1RunStepDSaturatedGuard, t1RunStepDSaturated,
    t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
    t1RunRebuildTuple, t1RunDPrepared,
    t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
    t1RunStepDValidPoints, t1RunStepDHitCount,
    t1RunStepParamsState, t1RunStepParamsN,
    t1RunStepParamsCSparse, t1RunStepParamsK,
    t1RunStepParamsEpsilon, t1RunStepParamsQuota]
  rfl

/-- A rebuild produces a duplicate-free block of exactly `2 ^ (k - epsilon)` unmarked strings of
length `n` meeting every model seen so far in at most `cSparse * n + cSparse` points. -/
theorem t1RunRebuild_model_spec (V : Map) (c : Nat.Partrec.Code) :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon t
      (s : T1RunState),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      (∀ x ∈ (t1RunMarked s).toFinset,
        T1BMarked V n epsilon x ∨
          (∃ d, T1CMarked V n k d x) ∨
          T1DMarked V n k x) →
      s.seenCDouble.toFinset ⊆
        (t1CDoublePrimeBatches c n k
          (epsilon + logSlack cDesc n) t).flatten.toFinset →
      let s' := t1RunRebuild cSparse n k epsilon s
      s'.current.Nodup ∧
        s'.current.toFinset ⊆ (t1RunUnmarked n s).toFinset ∧
        s'.current.length = 2 ^ (k - epsilon) ∧
        ∀ code ∈ s.seenCDouble,
          (s'.current.toFinset ∩
            (canonicalPointListOfCode code).toFinset).card ≤
              cSparse * n + cSparse := by
  intro cDesc
  obtain ⟨c0, cSparse, hselector⟩ :=
    t1_rebuild_selector_spec V c cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon t s hc0 hεk hkn hmarked hseen
  have hspec :=
    hselector n k epsilon t (t1RunMarked s).toFinset
      s.seenCDouble hc0 hεk hkn hmarked hseen
  rw [← t1RunUnmarked_eq_canonicalFinsetList] at hspec
  obtain ⟨h1, h2, h3, h4⟩ := hspec
  simp only [t1RunRebuild, t1RunReplaceCurrent, t1RunNextCurrent]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert h1 using 2
  · convert h2 using 3
  · convert h3 using 3
  · intro code hcode
    convert h4 (canonicalPointListOfCode code)
      (List.mem_map_of_mem hcode) using 3
    congr 1

/-- A B-set event appends the length-`n` points of the received code to the B-marked list and
increments the external counter. -/
theorem t1RunStep_bSet_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s (.bSet w)
    s'.bMarked =
        s.bMarked ++
          (canonicalPointListOfCode w).filter
            (fun x => x.length = n) ∧
      s'.external = s.external + 1 := by
  simp [t1RunStep, t1RunStepBSetFn, t1RunExternalRebuildFinal,
    t1RunStepBSetRebuilt, t1RunRebuildTuple, t1RunRebuild,
    t1RunReplaceCurrent, t1RunStepBSetPre, t1RunAppendB,
    t1RunValidPoints, t1RunStepParamsState, t1RunStepParamsN]
  rfl

/-- A C''-batch event appends the codes of the batch to the seen list, marks the points of those
already seen as C' models, increments the external counter and leaves the C-charge unchanged. -/
theorem t1RunStep_cDouble_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (batch : List BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.cDoublePrimeBatch batch)
    let activated :=
      ((batch.filter fun w => w ∈ s.seenCPrime).flatMap
        canonicalPointListOfCode).filter (fun x => x.length = n)
    s'.cMarked = s.cMarked ++ activated ∧
      s'.seenCDouble = s.seenCDouble ++ batch ∧
      s'.external = s.external + 1 ∧
      s'.totalC = s.totalC := by
  simp [t1RunStep, t1RunStepCDoubleFn,
    t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
    t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
    t1RunStepCDoublePre, t1RunAppendCSeenDouble,
    t1RunBatchValidPoints, t1RunStepParamsState,
    t1RunStepParamsN]
  rfl

/-- A C'-model event records the model; it marks the model's length-`n` points and charges the
current block's hits when the model was already seen as a C'' code, and changes nothing else
otherwise. -/
theorem t1RunStep_cPrime_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)
    let points :=
      (canonicalPointListOfCode w).filter (fun x => x.length = n)
    s'.seenCPrime = s.seenCPrime ++ [w] ∧
      (w ∈ s.seenCDouble →
        s'.cMarked = s.cMarked ++ points ∧
        s'.totalC =
          s.totalC + (s.current.filter fun x => x ∈ points).length) ∧
      (w ∉ s.seenCDouble →
        s'.cMarked = s.cMarked ∧ s'.totalC = s.totalC) := by
  by_cases hactive : w ∈ s.seenCDouble
  · simp only [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, t1RunStepParamsState, hactive,
      decide_true, ite_true, t1RunStepCPrimeActiveFn]
    split <;>
      simp only [t1RunStepCPrimeSaturated,
        t1RunSaturationRebuildFinal, t1RunStepCPrimeRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCPrimeCharged, t1RunChargeC, t1RunHitCount,
        t1RunAppendC, t1RunStepCPrimeSeen,
        t1RunAppendSeenCPrime, t1RunStepCPrimePoints,
        t1RunValidPoints, t1RunStepParamsState,
        t1RunStepParamsN, List.mem_filter, decide_eq_true_eq,
        Bool.decide_and, forall_const, not_true_eq_false,
        IsEmpty.forall_iff, and_true]
    all_goals and_intros
    all_goals first | rfl | trivial |
      (congr!
       all_goals first | rfl | trivial | (exact Subsingleton.elim _ _) |
         exact decide_eq_true_iff)
  · simp [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, hactive, t1RunStepCPrimeSeen,
      t1RunAppendSeenCPrime, t1RunStepParamsState]


/-- A `C'` event changes only the `C` marks, `C'` history, charge, and
possibly the current model/version counters. -/
theorem t1RunStep_cPrime_unchanged_histories
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.cPrimeModel w)
    s'.bMarked = s.bMarked ∧
      s'.dMarked = s.dMarked ∧
      s'.seenCDouble = s.seenCDouble := by
  by_cases hactive : w ∈ s.seenCDouble
  · simp only [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, t1RunStepParamsState, hactive,
      decide_true, ite_true, t1RunStepCPrimeActiveFn]
    split <;>
      simp_all [t1RunStepCPrimeSaturated,
        t1RunSaturationRebuildFinal, t1RunStepCPrimeRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCPrimeCharged, t1RunChargeC, t1RunAppendC,
        t1RunStepCPrimeSeen, t1RunAppendSeenCPrime,
        t1RunStepParamsState]
  · simp [t1RunStep, t1RunStepCPrimeFn,
      t1RunStepCPrimeActive, hactive, t1RunStepCPrimeSeen,
      t1RunAppendSeenCPrime, t1RunStepParamsState]

end Kolmogorov
