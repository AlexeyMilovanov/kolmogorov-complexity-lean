import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedWitness
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustRung

/-!
# The charged base rung

Stage two supplies the first rung carrying Gacs's designated-gray upper bound.
The certificate is selected from the globally incomparable witness cylinders,
so the proof works for every `eta ≥ 1`; the repaired ladder fixes `eta = 4`.
-/

namespace Kolmogorov

/-- The stage-two family strategy, shifted by three levels, is a charged rung with parameters
`q = 2` and `L = 3`, for any branching `B ≥ 2` and any amplification `eta ≥ 1`. -/
theorem chargedGrayRung_two
    (eta : Rat) (heta : 1 ≤ eta) (B : Nat) (hB : 2 ≤ B) :
    ChargedGrayRung eta 2 3 B
      (fun a e => stageTwoFamilyStrategy a (e + 3)) := by
  intro a e _ha hae n A hn
  let : NeZero n := ⟨by omega⟩
  have hbranch : 2 ≤ ladderBranching B a e :=
    two_le_ladderBranching hB a e
  have hForcing :
      FamilyWitnessForcing 2 4 (ladderBranching B a e)
        a (e + 3) n A (stageTwoFamilyStrategy a (e + 3)) := by
    (convert (familyWitnessForcing_two a e hae n A).mono_branching hbranch using 1;
      norm_num [halfAmplification])
  have hweak :
      GrayFamilyGameSpec 2 (dyadicScale a)
        ((3 / 4 : Rat) * dyadicScale a)
        e (e + 3) 4 (ladderBranching B a e) n A
        (stageTwoFamilyStrategy a (e + 3)) := by
    (convert grayFamilyGameSpec_mono_branching hbranch
      (grayFamilyGameSpec_stageTwo a e hae n hn A) using 1;
        norm_num [halfAmplification])
  have H : ChargedGrayFamilyGameSpec eta 2 (dyadicScale a)
      ((3 / 4 : Rat) * dyadicScale a) e (e + 3) 4
      (ladderBranching B a e) n A (stageTwoFamilyStrategy a (e + 3)) := by
    apply chargedGrayFamilyGameSpec_two_of_witnessForcing
      eta 4 (ladderBranching B a e) a e (e + 3) n A
      (stageTwoFamilyStrategy a (e + 3)) heta hForcing hweak
    · intro sm hsm t i hi
      simp only [getFamilyReq]
      rw [stageTwo_move_eq a (e + 3) A n sm t hi]
      simp [stageTwoTreeMove, dyadicScale]
    · omega
    · omega
  (convert H using 1;
    norm_num [halfAmplification])

/-- The base rung used by the repaired Gacs induction. -/
theorem chargedGrayRung_two_four (B : Nat) (hB : 2 ≤ B) :
    ChargedGrayRung 4 2 3 B
      (fun a e => stageTwoFamilyStrategy a (e + 3)) :=
  chargedGrayRung_two 4 (by norm_num) B hB

/-- Forgetting the internal designated charge recovers the existing public
stage-two rung without changing its statement. -/
theorem chargedGrayRung_two_four_toGrayRung (B : Nat) (hB : 2 ≤ B) :
    GrayRung 2 3 B
      (fun a e => stageTwoFamilyStrategy a (e + 3)) :=
  (chargedGrayRung_two_four B hB).toGrayRung

end Kolmogorov
