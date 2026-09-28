import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.StatePrimrec

/-!
# The transitions of the marking run

One marking step, defined branch by branch.  For the `C'` stream: `t1RunStepCPrimeActive`
decides whether the incoming code has already been seen twice,
`t1RunStepCPrimeSaturatedGuard` whether the charged state has reached the quota,
`t1RunStepCPrimeActiveFn` rebuilds or keeps the charged state accordingly, and
`t1RunStepCPrimeFn` is the whole step.  For the `D` stream: `t1RunAppendD`, `t1RunChargeD`,
`t1RunStepDValidPoints`, `t1RunStepDHitCount`, `t1RunStepDCharged`, `t1RunStepDRebuilt`,
`t1RunStepDSaturated` and `t1RunStepDSaturatedGuard` do the same, and the `B` and `C''`
branches follow the same pattern.

Each branch is written as a composition of small named pieces so that `T1Run/StatePrimrec` and
`T1Run/Computable` can prove it effective and `T1Run/Part03` can state its semantics.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- Whether the incoming code has already been seen twice, so that the C′-step is active. -/
def t1RunStepCPrimeActive
    (p : T1RunStepParams × BitString) : Bool :=
  decide (p.2 ∈ (t1RunStepParamsState p.1).seenCDouble)

/-- Whether the charged C′-state has reached the quota, so that the run must rebuild. -/
noncomputable def t1RunStepCPrimeSaturatedGuard
    (p : T1RunStepParams × BitString) : Bool :=
  t1RunSaturated (t1RunStepCPrimeCharged p)
    (t1RunStepParamsQuota p.1)

/-- The active C′-step: rebuild when the quota is reached, otherwise keep the charged state. -/
noncomputable def t1RunStepCPrimeActiveFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  if t1RunStepCPrimeSaturatedGuard p then
    t1RunStepCPrimeSaturated p
  else t1RunStepCPrimeCharged p

/-- One C′-step of the effective run: an active step when the code was seen twice, and a bare
recording otherwise. -/
noncomputable def t1RunStepCPrimeFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  if t1RunStepCPrimeActive p then
    t1RunStepCPrimeActiveFn p
  else
    t1RunStepCPrimeSeen p

/-- Mark a batch of points as D-marked. -/
def t1RunAppendD
    (p : T1RunState × List BitString) : T1RunState :=
  { p.1 with dMarked := p.1.dMarked ++ p.2 }

/-- Add a number of hits to the accumulated D-charge. -/
def t1RunChargeD
    (p : T1RunState × Nat) : T1RunState :=
  { p.1 with totalD := p.1.totalD + p.2 }

/-- The point list of a D-step: the incoming string itself if it has the right length, and
nothing otherwise. -/
noncomputable def t1RunStepDValidPoints
    (p : T1RunStepParams × BitString) : List BitString :=
  if p.2.length = t1RunStepParamsN p.1 then [p.2] else []

/-- One if the incoming string lies in the current subset, zero otherwise. -/
noncomputable def t1RunStepDHitCount
    (p : T1RunStepParams × BitString) : Nat :=
  if p.2 ∈ (t1RunStepParamsState p.1).current then 1 else 0

/-- The D-step state: the incoming point is D-marked and a hit against the current subset is
charged. -/
noncomputable def t1RunStepDCharged
    (p : T1RunStepParams × BitString) : T1RunState :=
  let marked := t1RunAppendD
    (t1RunStepParamsState p.1, t1RunStepDValidPoints p)
  t1RunChargeD (marked, t1RunStepDHitCount p)

/-- The charged D-state after the current subset has been rebuilt. -/
noncomputable def t1RunStepDRebuilt
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunRebuildTuple
    (t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
      t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
      t1RunStepDCharged p)

/-- The rebuilt D-state, with one saturation rebuild counted. -/
noncomputable def t1RunStepDSaturated
    (p : T1RunStepParams × BitString) : T1RunState :=
  t1RunSaturationRebuildFinal
    (t1RunStepParamsState p.1, t1RunStepDRebuilt p)

/-- Whether the charged D-state has reached the quota, so that the run must rebuild. -/
noncomputable def t1RunStepDSaturatedGuard
    (p : T1RunStepParams × BitString) : Bool :=
  t1RunSaturated (t1RunStepDCharged p)
    (t1RunStepParamsQuota p.1)

/-- One D-step of the effective run: rebuild when the quota is reached, otherwise keep the
charged state. -/
noncomputable def t1RunStepDStringFn
    (p : T1RunStepParams × BitString) : T1RunState :=
  if t1RunStepDSaturatedGuard p then
    t1RunStepDSaturated p
  else t1RunStepDCharged p

private theorem t1RunValidPoints_primrec :
    Primrec t1RunValidPoints := by
  have hpoints : Primrec (fun p : Nat × BitString =>
      canonicalPointListOfCode p.2) :=
    canonicalPointListOfCode_primrec.comp Primrec.snd
  have hlength : Primrec (fun q : (Nat × BitString) × BitString =>
      decide (q.2.length = q.1.1)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst))
  exact list_filter_primrec hpoints hlength.to₂

private theorem t1RunBatchValidPoints_primrec :
    Primrec t1RunBatchValidPoints := by
  have hbatch : Primrec (fun p :
      Nat × List BitString × List BitString => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hmem : Primrec (fun q :
      (Nat × List BitString × List BitString) × BitString =>
        decide (q.2 ∈ q.1.2.1)) :=
    by
      exact PrimrecPred.decide
        (mem_bitstring_primrec.comp
          (Primrec.snd.pair
            (Primrec.fst.comp
              (Primrec.snd.comp Primrec.fst))))
  have htoActivate : Primrec (fun p :
      Nat × List BitString × List BitString =>
        p.2.2.filter (fun w => w ∈ p.2.1)) :=
    list_filter_primrec hbatch hmem.to₂
  have hpoints : Primrec (fun p :
      Nat × List BitString × List BitString =>
        (p.2.2.filter (fun w => w ∈ p.2.1)).flatMap
          canonicalPointListOfCode) :=
    Primrec.list_flatMap htoActivate
      ((canonicalPointListOfCode_primrec.comp Primrec.snd).to₂)
  have hlength : Primrec (fun q :
      (Nat × List BitString × List BitString) × BitString =>
        decide (q.2.length = q.1.1)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst))
  exact list_filter_primrec hpoints hlength.to₂

private theorem t1RunHitCount_primrec :
    Primrec t1RunHitCount := by
  have hmem : Primrec (fun q :
      (List BitString × List BitString) × BitString =>
        decide (q.2 ∈ q.1.2)) :=
    by
      exact PrimrecPred.decide
        (mem_bitstring_primrec.comp
          (Primrec.snd.pair
            (Primrec.snd.comp Primrec.fst)))
  exact Primrec.list_length.comp
    (list_filter_primrec Primrec.fst hmem.to₂)

private theorem t1RunAppendB_primrec :
    Primrec t1RunAppendB := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_bMarked_primrec.comp hs) Primrec.snd)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private theorem t1RunExternalRebuildFinal_primrec :
    Primrec t1RunExternalRebuildFinal := by
  have hold : Primrec (fun p : T1RunState × T1RunState => p.1) :=
    Primrec.fst
  have hnew : Primrec (fun p : T1RunState × T1RunState => p.2) :=
    Primrec.snd
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hnew)
    (t1RunState_bMarked_primrec.comp hnew)
    (t1RunState_cMarked_primrec.comp hnew)
    (t1RunState_dMarked_primrec.comp hnew)
    (t1RunState_seenCPrime_primrec.comp hnew)
    (t1RunState_seenCDouble_primrec.comp hnew)
    (t1RunState_versions_primrec.comp hnew)
    (Primrec.nat_add.comp
      (t1RunState_external_primrec.comp hold) (Primrec.const 1))
    (t1RunState_saturation_primrec.comp hnew)
    (t1RunState_totalC_primrec.comp hnew)
    (t1RunState_totalD_primrec.comp hnew)

private theorem t1RunAppendCSeenDouble_primrec :
    Primrec t1RunAppendCSeenDouble := by
  have hs : Primrec (fun p :
      T1RunState × (List BitString × List BitString) => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_cMarked_primrec.comp hs)
      (Primrec.fst.comp Primrec.snd))
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_seenCDouble_primrec.comp hs)
      (Primrec.snd.comp Primrec.snd))
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private theorem t1RunAppendSeenCPrime_primrec :
    Primrec t1RunAppendSeenCPrime := by
  have hs : Primrec (fun p : T1RunState × BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_seenCPrime_primrec.comp hs)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private theorem t1RunAppendC_primrec :
    Primrec t1RunAppendC := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_cMarked_primrec.comp hs) Primrec.snd)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private theorem t1RunChargeC_primrec :
    Primrec t1RunChargeC := by
  have hs : Primrec (fun p : T1RunState × Nat => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (Primrec.nat_add.comp
      (t1RunState_totalC_primrec.comp hs) Primrec.snd)
    (t1RunState_totalD_primrec.comp hs)

private theorem t1RunStepBSetPre_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepBSetPre p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunAppendB_primrec.comp
    ((t1RunStepParams_state_primrec.comp hparams).pair
      (t1RunValidPoints_primrec.comp
        ((t1RunStepParams_n_primrec.comp hparams).pair
          Primrec.snd)))).of_eq (fun p => by rfl)

private theorem t1RunStepBSetRebuilt_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepBSetRebuilt p) := by
  have hparams : Primrec (fun q :
      T1RunStepParams × BitString => q.1) := Primrec.fst
  have hinput : Computable (fun p :
      T1RunStepParams × BitString =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepBSetPre p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepBSetPre_primrec.to_comp)))
  exact t1RunRebuildTuple_computable.comp hinput

/-- The B-step function is computable. -/
theorem t1RunStepBSetFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepBSetFn p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  have hrebuild : Computable (fun q : Q =>
      t1RunStepBSetRebuilt q) :=
    t1RunStepBSetRebuilt_computable
  exact (t1RunExternalRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      hrebuild)).of_eq (fun q => by rfl)

private theorem t1RunStepCDoublePre_computable :
    Computable (fun p : T1RunStepParams × List BitString =>
      t1RunStepCDoublePre p) := by
  let Q := T1RunStepParams × List BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  have hs : Primrec (fun q : Q =>
      t1RunStepParamsState q.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hpoints : Primrec (fun q : Q =>
      t1RunBatchValidPoints
        (t1RunStepParamsN q.1,
          (t1RunStepParamsState q.1).seenCPrime, q.2)) :=
    t1RunBatchValidPoints_primrec.comp
      ((t1RunStepParams_n_primrec.comp hparams).pair
        ((t1RunState_seenCPrime_primrec.comp hs).pair
          Primrec.snd))
  exact (t1RunAppendCSeenDouble_primrec.comp
    (hs.pair (hpoints.pair Primrec.snd))).to_comp.of_eq
      (fun q => by rfl)

private theorem t1RunStepCDoubleRebuilt_computable :
    Computable (fun p : T1RunStepParams × List BitString =>
      t1RunStepCDoubleRebuilt p) := by
  let Q := T1RunStepParams × List BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  have hinput : Computable (fun p : Q =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepCDoublePre p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepCDoublePre_computable)))
  exact t1RunRebuildTuple_computable.comp hinput

/-- The C″-step function is computable. -/
theorem t1RunStepCDoubleFn_computable :
    Computable (fun p : T1RunStepParams × List BitString =>
      t1RunStepCDoubleFn p) := by
  let Q := T1RunStepParams × List BitString
  have hparams : Primrec (fun q : Q => q.1) := Primrec.fst
  exact (t1RunExternalRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      t1RunStepCDoubleRebuilt_computable)).of_eq
        (fun q => by rfl)

private theorem t1RunStepCPrimeSeen_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeSeen p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunAppendSeenCPrime_primrec.comp
    ((t1RunStepParams_state_primrec.comp hparams).pair
      Primrec.snd)).of_eq (fun p => by rfl)

private theorem t1RunStepCPrimePoints_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimePoints p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunValidPoints_primrec.comp
    ((t1RunStepParams_n_primrec.comp hparams).pair
      Primrec.snd)).of_eq (fun p => by rfl)

private theorem t1RunStepCPrimeCharged_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeCharged p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun p : Q => p.1) := Primrec.fst
  have hs : Primrec (fun p : Q =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hmarked : Primrec (fun p : Q =>
      t1RunAppendC
        (t1RunStepCPrimeSeen p, t1RunStepCPrimePoints p)) :=
    t1RunAppendC_primrec.comp
      (t1RunStepCPrimeSeen_primrec.pair
        t1RunStepCPrimePoints_primrec)
  have hhits : Primrec (fun p : Q =>
      t1RunHitCount
        ((t1RunStepParamsState p.1).current,
          t1RunStepCPrimePoints p)) :=
    t1RunHitCount_primrec.comp
      ((t1RunState_current_primrec.comp hs).pair
        t1RunStepCPrimePoints_primrec)
  exact (t1RunChargeC_primrec.comp
    (hmarked.pair hhits)).of_eq (fun p => by rfl)

private theorem t1RunStepCPrimeRebuilt_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeRebuilt p) := by
  let Q := T1RunStepParams × BitString
  have hparams : Primrec (fun p : Q => p.1) := Primrec.fst
  have hinput : Computable (fun p : Q =>
      ((t1RunStepParamsCSparse p.1, t1RunStepParamsN p.1,
        t1RunStepParamsK p.1, t1RunStepParamsEpsilon p.1,
        t1RunStepCPrimeCharged p) :
        Nat × Nat × Nat × Nat × T1RunState)) :=
    (t1RunStepParams_cSparse_primrec.comp hparams).to_comp.pair
      ((t1RunStepParams_n_primrec.comp hparams).to_comp.pair
        ((t1RunStepParams_k_primrec.comp hparams).to_comp.pair
          ((t1RunStepParams_epsilon_primrec.comp hparams).to_comp.pair
            t1RunStepCPrimeCharged_primrec.to_comp)))
  exact t1RunRebuildTuple_computable.comp hinput

private theorem t1RunStepCPrimeSaturated_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeSaturated p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturationRebuildFinal_primrec.to_comp.comp
    ((t1RunStepParams_state_primrec.comp hparams).to_comp.pair
      t1RunStepCPrimeRebuilt_computable)).of_eq
        (fun p => by rfl)

private theorem t1RunStepCPrimeActive_primrec :
    Primrec t1RunStepCPrimeActive := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hs : Primrec (fun p :
      T1RunStepParams × BitString =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  exact PrimrecPred.decide
    (mem_bitstring_primrec.comp
      (Primrec.snd.pair
        (t1RunState_seenCDouble_primrec.comp hs)))

private theorem t1RunStepCPrimeSaturatedGuard_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeSaturatedGuard p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  exact (t1RunSaturated_primrec.comp
    (t1RunStepCPrimeCharged_primrec.pair
      (t1RunStepParams_quota_primrec.comp hparams))).of_eq
        (fun p => by rfl)

private theorem t1RunStepCPrimeActiveFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeActiveFn p) := by
  exact (Computable.cond
    t1RunStepCPrimeSaturatedGuard_primrec.to_comp
    t1RunStepCPrimeSaturated_computable
    t1RunStepCPrimeCharged_primrec.to_comp).of_eq
      (fun p => by
        simp only [t1RunStepCPrimeActiveFn]
        cases t1RunStepCPrimeSaturatedGuard p <;> rfl)

/-- The C′-step function is computable. -/
theorem t1RunStepCPrimeFn_computable :
    Computable (fun p : T1RunStepParams × BitString =>
      t1RunStepCPrimeFn p) := by
  exact (Computable.cond t1RunStepCPrimeActive_primrec.to_comp
    t1RunStepCPrimeActiveFn_computable
    t1RunStepCPrimeSeen_primrec.to_comp).of_eq
      (fun p => by
        simp only [t1RunStepCPrimeFn]
        cases t1RunStepCPrimeActive p <;> rfl)

/-- The D-step hit count is primitive recursive. -/
theorem t1RunStepDHitCount_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDHitCount p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hs : Primrec (fun p :
      T1RunStepParams × BitString =>
      t1RunStepParamsState p.1) :=
    t1RunStepParams_state_primrec.comp hparams
  have hguard : Primrec (fun p :
      T1RunStepParams × BitString =>
      decide (p.2 ∈ (t1RunStepParamsState p.1).current)) :=
    PrimrecPred.decide
      (mem_bitstring_primrec.comp
        (Primrec.snd.pair
          (t1RunState_current_primrec.comp hs)))
  exact (Primrec.cond hguard (Primrec.const 1)
    (Primrec.const 0)).of_eq (fun p => by
      simp only [t1RunStepDHitCount]
      split <;> simp_all)

private theorem t1RunAppendD_primrec :
    Primrec t1RunAppendD := by
  have hs : Primrec (fun p : T1RunState × List BitString => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (Primrec.list_append.comp
      (t1RunState_dMarked_primrec.comp hs) Primrec.snd)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (t1RunState_totalD_primrec.comp hs)

private theorem t1RunChargeD_primrec :
    Primrec t1RunChargeD := by
  have hs : Primrec (fun p : T1RunState × Nat => p.1) :=
    Primrec.fst
  exact t1RunState_mk_primrec
    (t1RunState_current_primrec.comp hs)
    (t1RunState_bMarked_primrec.comp hs)
    (t1RunState_cMarked_primrec.comp hs)
    (t1RunState_dMarked_primrec.comp hs)
    (t1RunState_seenCPrime_primrec.comp hs)
    (t1RunState_seenCDouble_primrec.comp hs)
    (t1RunState_versions_primrec.comp hs)
    (t1RunState_external_primrec.comp hs)
    (t1RunState_saturation_primrec.comp hs)
    (t1RunState_totalC_primrec.comp hs)
    (Primrec.nat_add.comp
      (t1RunState_totalD_primrec.comp hs) Primrec.snd)

private theorem t1RunStepDValidPoints_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDValidPoints p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hguard : Primrec (fun p :
      T1RunStepParams × BitString =>
      decide (p.2.length = t1RunStepParamsN p.1)) :=
    PrimrecPred.decide
      (Primrec.eq.comp
        (Primrec.list_length.comp Primrec.snd)
        (t1RunStepParams_n_primrec.comp hparams))
  exact (Primrec.cond hguard
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    (Primrec.const [])).of_eq (fun p => by
      simp only [t1RunStepDValidPoints]
      split <;> simp_all)

/-- The charged D-state is primitive recursive. -/
theorem t1RunStepDCharged_primrec :
    Primrec (fun p : T1RunStepParams × BitString =>
      t1RunStepDCharged p) := by
  have hparams : Primrec (fun p :
      T1RunStepParams × BitString => p.1) := Primrec.fst
  have hmarked : Primrec (fun p :
      T1RunStepParams × BitString =>
      t1RunAppendD
        (t1RunStepParamsState p.1, t1RunStepDValidPoints p)) :=
    t1RunAppendD_primrec.comp
      ((t1RunStepParams_state_primrec.comp hparams).pair
        t1RunStepDValidPoints_primrec)
  exact (t1RunChargeD_primrec.comp
    (hmarked.pair t1RunStepDHitCount_primrec)).of_eq
      (fun p => by rfl)

/-- One step of the T1 marking run: the state is updated according to the kind of the marking
event (a `B` set, a batch of `C''` models, a `C'` model, or a `D` string). -/
noncomputable def t1RunStep (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent) : T1RunState :=
  let params : T1RunStepParams :=
    (((cSparse, n), (k, epsilon)), (quota, s))
  match event with
  | .bSet w => t1RunStepBSetFn (params, w)
  | .cDoublePrimeBatch batch => t1RunStepCDoubleFn (params, batch)
  | .cPrimeModel w => t1RunStepCPrimeFn (params, w)
  | .dString x => t1RunStepDStringFn (params, x)

/-- The state reached by running the T1 marking steps over a list of events. -/
noncomputable def t1RunFromEvents (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (events : List T1MarkEvent) : T1RunState :=
  events.foldl (t1RunStep cSparse n k epsilon quota) s

/-- The T1 run state at time `t`: the run from the initial state over the events enumerated by
the marking stage of the machine code `c` up to `t`. -/
noncomputable def t1RunAt (c : Nat.Partrec.Code)
    (cDesc cSparse n k epsilon quota t : Nat) : T1RunState :=
  t1RunFromEvents cSparse n k epsilon quota
    (t1InitialRunState n k epsilon)
    (t1MarkingEventStage c n k epsilon
      (epsilon + logSlack cDesc n) t)

/-- The single run step packaged as a function of a bundled input, for the computability proofs. -/
noncomputable def T1RunStepInput.run (input : T1RunStepInput) : T1RunState :=
  t1RunStep input.cSparse input.n input.k input.epsilon input.quota input.s input.event

/-- The run at a time packaged as a function of a bundled input, for the computability proofs. -/
noncomputable def T1RunInput.run (input : T1RunInput) : T1RunState :=
  t1RunAt input.c input.cDesc input.cSparse input.n input.k
    input.epsilon input.quota input.t

end Kolmogorov
