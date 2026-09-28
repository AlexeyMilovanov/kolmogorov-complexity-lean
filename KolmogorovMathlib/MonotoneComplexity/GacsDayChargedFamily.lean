import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayCharge
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRungs

/-!
# The charged family-game specification

This is the internal strengthening used by the repaired Gacs-Day induction.
The public game remains `GrayFamilyGameSpec`; the extra finite charge witness is
forgotten at the boundary of the canonical ladder.
-/

namespace Kolmogorov

/-- A charged gray goal is in particular a plain gray goal for the same parameters, once the
epsilon depth is below the delta depth. -/
lemma familyChargedGrayGoal.to_familyGrayGoal
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n : Nat}
    (hed : epsDepth ≤ deltaDepth) {A : Allocation}
    {cm : Nat → FamilyClientMove} {sm : Nat → FamilyServerMove}
    (h : familyChargedGrayGoal eta kappa alpha beta epsDepth deltaDepth n A cm sm) :
    familyGrayGoal kappa beta epsDepth deltaDepth n A cm sm := by
  obtain ⟨T, hT⟩ := h
  apply (familyGrayGoal_iff_exists_familyGrayGoalAtB hed n A cm sm).2
  refine ⟨T, ?_⟩
  simpa using familyChargedGrayGoalAtB.to_familyGrayGoalAtB hT

/-- A family game whose gray outcome includes Gacs's designated charge. -/
structure ChargedGrayFamilyGameSpec (eta kappa alpha beta : Rat)
    (epsDepth deltaDepth h b n : Nat) (A : Allocation)
    (sigma : ClientFamilyStrategy) : Prop where
  weak : GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A sigma
  wins_charged : ∀ sm, familyServerPlayLegal n b A sm →
    familyClientWinsUnservedPositive n h b
        (playClientFamily A n sigma sm) sm ∨
      familyChargedGrayGoal eta kappa alpha beta epsDepth deltaDepth n A
        (playClientFamily A n sigma sm) sm

/-- Forget the designated charge and retain the public family-game result. -/
theorem ChargedGrayFamilyGameSpec.toGrayFamilyGameSpec
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth h b n : Nat}
    {A : Allocation} {sigma : ClientFamilyStrategy}
    (H : ChargedGrayFamilyGameSpec eta kappa alpha beta epsDepth deltaDepth
      h b n A sigma) :
    GrayFamilyGameSpec kappa alpha beta epsDepth deltaDepth h b n A sigma :=
  H.weak

/-- Widening the game tree does not change the charge certificate. -/
theorem ChargedGrayFamilyGameSpec.mono_branching
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth h b b' n : Nat}
    {A : Allocation} {sigma : ClientFamilyStrategy}
    (hbb : b ≤ b')
    (H : ChargedGrayFamilyGameSpec eta kappa alpha beta epsDepth deltaDepth
      h b n A sigma) :
    ChargedGrayFamilyGameSpec eta kappa alpha beta epsDepth deltaDepth
      h b' n A sigma := by
  refine ⟨grayFamilyGameSpec_mono_branching hbb H.weak, ?_⟩
  intro sm hsm
  rcases H.wins_charged sm
      (familyServerPlayLegal_mono_branching hbb hsm) with hwin | hgray
  · exact Or.inl (familyClientWinsUnservedPositive_mono_branching hbb hwin)
  · exact Or.inr hgray

/-- The internal rung carrying the designated charge invariant. -/
def ChargedGrayRung (eta : Rat) (k L B : Nat)
    (sigma : FamilyStrategyScheme) : Prop :=
  ∀ a e, 1 ≤ a → a ≤ e → ∀ n A, 1 ≤ n →
    ChargedGrayFamilyGameSpec eta (halfAmplification k) (dyadicScale a)
      ((3 / 4 : Rat) * dyadicScale a) e (e + L) (2 * k)
      (ladderBranching B a e) n A (sigma a e)

/-- A charged rung of the ladder is in particular a rung of the plain gray ladder. -/
theorem ChargedGrayRung.toGrayRung
    {eta : Rat} {k L B : Nat} {sigma : FamilyStrategyScheme}
    (H : ChargedGrayRung eta k L B sigma) : GrayRung k L B sigma := by
  intro a e ha hae n A hn
  exact (H a e ha hae n A hn).weak

end Kolmogorov
