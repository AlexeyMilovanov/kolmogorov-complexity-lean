import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1SparseSelector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingRun
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1MarkingStreams
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T1Run.Computable

/-!
# What a `D` event changes

The frame lemmas for the `D` branch of the T1 run step: `t1RunStep_dString_history` records
what a `D` event does — appends the string to the `D` marks and increases the `D` charge — and
`t1RunStep_dString_unchanged_histories` says it touches nothing else.
`t1RunStep_current_eq_of_versions_eq` is the general frame fact behind them: a step that
leaves the version list unchanged leaves the current model unchanged.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-- A `D` event appends `x` to the `D` marks when `x` has length `n`, and increases the `D`
charge exactly when `x` lies in the current model. -/
theorem t1RunStep_dString_history
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (x : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.dString x)
    s'.dMarked =
        s.dMarked ++ (if x.length = n then [x] else []) ∧
      s'.totalD =
        s.totalD + (if x ∈ s.current then 1 else 0) := by
  simp only [t1RunStep, t1RunStepDStringFn]
  split <;>
    simp_all [t1RunStepDSaturated,
      t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
      t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
      t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
      t1RunStepDValidPoints, t1RunStepDHitCount,
      t1RunStepParamsState, t1RunStepParamsN]

/-- A `D` event changes only the `D` marks, `D` charge, and possibly the
current model/version counters. -/
theorem t1RunStep_dString_unchanged_histories
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (w : BitString) :
    let s' := t1RunStep cSparse n k epsilon quota s
      (.dString w)
    s'.bMarked = s.bMarked ∧
      s'.cMarked = s.cMarked ∧
      s'.seenCPrime = s.seenCPrime ∧
      s'.seenCDouble = s.seenCDouble := by
  simp only [t1RunStep, t1RunStepDStringFn]
  split <;>
    simp_all [t1RunStepDSaturated,
      t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
      t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
      t1RunStepDCharged, t1RunChargeD, t1RunAppendD,
      t1RunStepParamsState]

/-- A run step that leaves the version list unchanged leaves the current model unchanged. -/
theorem t1RunStep_current_eq_of_versions_eq
    (cSparse n k epsilon quota : Nat)
    (s : T1RunState) (event : T1MarkEvent)
    (hversions :
      (t1RunStep cSparse n k epsilon quota s event).versions =
        s.versions) :
    (t1RunStep cSparse n k epsilon quota s event).current =
      s.current := by
  cases event with
  | bSet w =>
      exfalso
      have hlength := congrArg List.length hversions
      simp [t1RunStep, t1RunStepBSetFn,
        t1RunExternalRebuildFinal, t1RunStepBSetRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepBSetPre, t1RunAppendB,
        t1RunStepParamsState] at hlength
  | cDoublePrimeBatch batch =>
      exfalso
      have hlength := congrArg List.length hversions
      simp [t1RunStep, t1RunStepCDoubleFn,
        t1RunExternalRebuildFinal, t1RunStepCDoubleRebuilt,
        t1RunRebuildTuple, t1RunRebuild, t1RunReplaceCurrent,
        t1RunStepCDoublePre, t1RunAppendCSeenDouble,
        t1RunStepParamsState] at hlength
  | cPrimeModel w =>
      simp only [t1RunStep, t1RunStepCPrimeFn,
        t1RunStepCPrimeActiveFn] at hversions ⊢
      split
      · split
        · exfalso
          have hlength := congrArg List.length hversions
          simp_all [t1RunStepCPrimeSaturated,
            t1RunSaturationRebuildFinal,
            t1RunStepCPrimeRebuilt, t1RunRebuildTuple,
            t1RunRebuild, t1RunReplaceCurrent,
            t1RunStepCPrimeCharged, t1RunChargeC,
            t1RunAppendC, t1RunStepCPrimeSeen,
            t1RunAppendSeenCPrime, t1RunStepParamsState]
        · simp [t1RunStepCPrimeCharged, t1RunChargeC,
            t1RunAppendC, t1RunStepCPrimeSeen,
            t1RunAppendSeenCPrime, t1RunStepParamsState]
      · simp [t1RunStepCPrimeSeen,
          t1RunAppendSeenCPrime, t1RunStepParamsState]
  | dString x =>
      simp only [t1RunStep, t1RunStepDStringFn] at hversions ⊢
      split
      · exfalso
        have hlength := congrArg List.length hversions
        simp_all [t1RunStepDSaturated,
          t1RunSaturationRebuildFinal, t1RunStepDRebuilt,
          t1RunRebuildTuple, t1RunRebuild,
          t1RunReplaceCurrent, t1RunStepDCharged,
          t1RunChargeD, t1RunAppendD,
          t1RunStepParamsState]
      · simp [t1RunStepDCharged, t1RunChargeD,
          t1RunAppendD, t1RunStepParamsState]

end Kolmogorov
