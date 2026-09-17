import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Schedule
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2GoalCoarsen

/-!
# V2 spec: the pinned rung, the universal wrapper, and the adapter

Blueprint v11, Stage A4 (verbatim-frozen signatures; proof doc v14
§9.0.1).  The pinned rung is the Day-literal interface: the stage `j` is
the only parameter, the gap `e − a = 8·fp(j−1) + 3` and the export depth
`a + fp j` are derived, and the domain `3 ≤ j` is carried as an explicit
hypothesis by every producer and consumer.

The certificate is anchored at the call's outer scale `a` (proof doc v15.1,
A2: `epsDepth = a`, v14 §9.3 taken literally) — validity of the charged
cells is tested at `a`, not at the bin scale `e = a + 8·fp(j−1) + 3`.  The
consumers (the block goals of the parent's rounds, the endgame at
`eps := a`) read the certificate at exactly this anchor, and the parent's
own certificate at its anchor follows by downward coarsening only.

The adapter runs universal → pinned only: specialize the universal spec at
the pinned gap, rewrite the export depth through the bridge identity, and
coarsen the anchor from `e` to `a`.  The reverse direction does not exist
(a pinned theorem cannot serve arbitrary `a ≤ e` without padding).
-/

namespace Kolmogorov

/-- **The charged game specification survives coarsening of the anchor
depth**: the weak goal and the charged goal are antitone in `epsDepth`
(`familyGrayGoalAtB_coarsen`, `familyChargedGrayGoalAtB_coarsen`); no other
field mentions it. -/
theorem ChargedGrayFamilyGameSpec.coarsen_epsDepth
    {eta kappa alpha beta : Rat} {e0 e1 deltaDepth h b n : Nat}
    {A : Allocation} {sigma : ClientFamilyStrategy} (h01 : e0 ≤ e1)
    (H : ChargedGrayFamilyGameSpec eta kappa alpha beta e1 deltaDepth h b n A
      sigma) :
    ChargedGrayFamilyGameSpec eta kappa alpha beta e0 deltaDepth h b n A
      sigma := by
  have hscales : e1 ≤ deltaDepth := H.weak.scales
  have h0d : e0 ≤ deltaDepth := le_trans h01 hscales
  have hgoal : ∀ (sm : Nat → FamilyServerMove) (cm : Nat → FamilyClientMove),
      familyGrayGoal kappa beta e1 deltaDepth n A cm sm →
        familyGrayGoal kappa beta e0 deltaDepth n A cm sm := by
    intro sm cm hg
    obtain ⟨T, hT⟩ := hg
    refine ⟨T, ?_⟩
    have h1 := (familyGrayGoalAtB_eq_true_iff hscales n T A cm sm).mpr hT
    exact (familyGrayGoalAtB_eq_true_iff h0d n T A cm sm).mp
      (familyGrayGoalAtB_coarsen h01 h1)
  refine ⟨?_, ?_⟩
  · refine { H.weak with scales := h0d, wins := ?_, wins_positively := ?_ }
    · intro sm hsm
      rcases H.weak.wins sm hsm with hw | hg
      · exact Or.inl hw
      · exact Or.inr (hgoal sm _ hg)
    · intro sm hsm
      rcases H.weak.wins_positively sm hsm with hw | hg
      · exact Or.inl hw
      · exact Or.inr (hgoal sm _ hg)
  · intro sm hsm
    rcases H.wins_charged sm hsm with hw | hg
    · exact Or.inl hw
    · obtain ⟨T, hT⟩ := hg
      exact Or.inr ⟨T, familyChargedGrayGoalAtB_coarsen h01 hT⟩

/-- For every anchor `a ≥ 1` and every family size `n ≥ 1`, the scheme instantiated at `a` and `a +
8 * grayFootprint (j - 1) + 3` satisfies `ChargedGrayFamilyGameSpec` at amplification
`halfAmplification j` with request scale `dyadicScale a`, target `3 / 4 * dyadicScale a`, window
`a` to `a + grayFootprint j`, height `2 * j` and the ladder branching of stage `j - 1`. -/
def PinnedChargedRung (eta : Rat) (j : Nat)
    (sigma : FamilyStrategyScheme) : Prop :=
  ∀ a, 1 ≤ a → ∀ n A, 1 ≤ n →
    ChargedGrayFamilyGameSpec eta (halfAmplification j) (dyadicScale a)
      ((3 / 4 : Rat) * dyadicScale a)
      a
      (a + grayFootprint j)
      (2 * j)
      (ladderBranching (grayTailBaseBranch (j - 1) (grayFootprint (j - 1)))
        a (a + 8 * grayFootprint (j - 1) + 3))
      n A (sigma a (a + 8 * grayFootprint (j - 1) + 3))

/-- The rung `ChargedGrayRung eta j (grayTailNewLoss (j - 1) L) (grayTailBaseBranch (j - 1) L)
sigma`: a charged rung whose depth loss and branching are those produced by a tail step run at
input budget `L`. -/
def UniversalChargedRung (eta : Rat) (j L : Nat)
    (sigma : FamilyStrategyScheme) : Prop :=
  ChargedGrayRung eta j (grayTailNewLoss (j - 1) L)
    (grayTailBaseBranch (j - 1) L) sigma

/-- **The adapter, universal → pinned**: specialize the universal rung at
the pinned gap `e = a + 8L + 3`, rewrite the export depth by the bridge
identity `e + grayTailNewLoss (j−1) L = a + fp j` (which needs the premise
`L = fp (j−1)`), and coarsen the anchor from `e` to `a`. -/
theorem pinnedChargedRung_of_universal {eta : Rat} {j L : Nat}
    {sigma : FamilyStrategyScheme}
    (hj : 3 ≤ j)
    (h : UniversalChargedRung eta j L sigma)
    (hL : L = grayFootprint (j - 1)) :
    PinnedChargedRung eta j sigma := by
  intro a ha n A hn
  subst hL
  have hspec := h a (a + 8 * grayFootprint (j - 1) + 3) ha (by omega) n A hn
  have hdepth :
      (a + 8 * grayFootprint (j - 1) + 3) +
          grayTailNewLoss (j - 1) (grayFootprint (j - 1)) =
        a + grayFootprint j := grayFootprint_bridge hj
  rw [hdepth] at hspec
  exact hspec.coarsen_epsDepth (by omega)

end Kolmogorov
