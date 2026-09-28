import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustWitness
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRungs

/-!
# The hereditary rung used internally by Day's recursion

The public ladder only promises the aggregate gray alternative. The recursive
half-step starts at stage two and needs the stronger subfamily estimate from
Definition 4.3.2(c). We keep that strengthening internal and expose the old
`GrayRung` by forgetting the extra certificate.
-/

namespace Kolmogorov

/-- A rung whose winning alternative contains Day's estimate for every
subfamily, not just for the whole family. -/
def RobustGrayRung (k L B : Nat) (sigma : FamilyStrategyScheme) : Prop :=
  forall a e, 1 <= a -> a <= e -> forall n A, 1 <= n ->
    RobustGrayFamilyGameSpec (halfAmplification k) (dyadicScale a)
      ((3 / 4 : Rat) * dyadicScale a) e (e + L) (2 * k)
      (ladderBranching B a e) n A (sigma a e)

/-- Forgetting the hereditary certificate recovers the public rung. -/
theorem RobustGrayRung.toGrayRung {k L B : Nat} {sigma : FamilyStrategyScheme}
    (H : RobustGrayRung k L B sigma) : GrayRung k L B sigma := by
  intro a e ha hae n A hn
  exact (H a e ha hae n A hn).weak

/-- The hereditary game specification is monotone in the branching factor.
The certificate itself is unchanged; only a positive unserved request has to
be reinterpreted on the wider tree. -/
theorem RobustGrayFamilyGameSpec.mono_branching
    {kappa alpha beta : Rat} {epsDepth deltaDepth h b b' n : Nat}
    {A : Allocation} {sigma : ClientFamilyStrategy}
    (hbb : b <= b')
    (H : RobustGrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth
      h b n A sigma) :
    RobustGrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth
      h b' n A sigma := by
  refine ⟨grayFamilyGameSpec_mono_branching hbb H.weak, ?_⟩
  intro sm hsm
  rcases H.wins_robust sm
      (familyServerPlayLegal_mono_branching hbb hsm) with hwin | hgray
  · exact Or.inl (familyClientWinsUnservedPositive_mono_branching hbb hwin)
  · exact Or.inr hgray

/-- Stage two is the first hereditary rung. Its three witnesses are anchored
in their own component and are globally prefix-incomparable, so every
subfamily inherits the same certificate. -/
theorem robustGrayRung_two (B : Nat) (hB : 2 <= B) :
    RobustGrayRung 2 3 B
      (fun a e => stageTwoFamilyStrategy a (e + 3)) := by
  intro a e _ha hae n A hn
  let H := grayFamilyGameSpec_stageTwo a e hae n hn A
  letI : NeZero n := ⟨by omega⟩
  apply robustGrayFamilyGameSpec_of_witnessForcing
    (halfAmplification 2) 4 (ladderBranching B a e) a e (e + 3) n A
      (stageTwoFamilyStrategy a (e + 3))
  · exact (familyWitnessForcing_two a e hae n A).mono_branching
      (two_le_ladderBranching hB a e)
  · exact grayFamilyGameSpec_mono_branching
      (two_le_ladderBranching hB a e) H
  · norm_num [halfAmplification]
  · intro sm hsm t i hi
    simp only [getFamilyReq]
    rw [stageTwo_move_eq a (e + 3) A n sm t hi]
    simp [stageTwoTreeMove, dyadicScale]
  · omega

end Kolmogorov
