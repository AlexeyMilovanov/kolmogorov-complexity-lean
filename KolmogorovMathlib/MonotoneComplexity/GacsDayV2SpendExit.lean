import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Finalization

/-!
# O2 reduced: spend progress from the eventual block spend goal

`GrayChargedSpendProgressV2` (every spend pass is eventually left, unless the
client wins) follows from the rung-dependent **eventual acceptance** of the
block spend goal `GrayChargedSpendGoalEventuallyV2`: from any spend time, the
client wins, or at some later time of the same pass the slots are exhausted or
the block spend goal is accepted — and the V2 step then leaves the pass.
-/

namespace Kolmogorov

/-- A V2 spend step with exhausted slots or an accepted block spend goal
leaves the pass. -/
lemma grayChargedStepV2_leaves_spend_of_goal
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayChargedStateV2 n b} {pass : Nat}
    {sm : FamilyServerMove}
    (hst : st.phase = .spend pass)
    (hacc : st.core.slots.isEmpty = true ∨
      grayChargedBlockSpendGoalAtB q L a e pass st.core.slots.length
        st.core.unavailable (grayBlockSpendMoveV2 q L a e pass sigma st.core)
        (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
          st.core.slots sm) = true) :
    (grayChargedStepV2 q L a e sigma A st sm).phase ≠ .spend pass := by
  simp only [grayChargedStepV2, hst]
  split
  · simp
  · rename_i hne
    split
    · split
      · split
        · simp
        · simp
      · simp
    · rename_i hgoal
      rcases hacc with hempty | hg
      · exact absurd hempty hne
      · exact absurd hg hgoal

/-- At every time `t` at which the run is in the spend pass `pass`, either it makes a positive
request forever (`GrayChargedPositiveV2`), or there is a time `u ≥ t` still in that pass at
which the slot list is empty or the spend acceptance goal `grayChargedBlockSpendGoalAtB` holds
of the pass move against the localised server move. -/
def GrayChargedSpendGoalEventuallyV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  forall t pass,
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass ->
      GrayChargedPositiveV2 q L a e n sigma A sm ∨
        exists u, t <= u ∧
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).phase = .spend pass ∧
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm u).core.slots.isEmpty = true ∨
            grayChargedBlockSpendGoalAtB q L a e pass
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm u).core.slots.length
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm u).core.unavailable
              (grayBlockSpendMoveV2 q L a e pass sigma
                (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm u).core)
              (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm u).core.slots (sm u)) = true)

/-- **O2 from the eventual spend goal.** -/
theorem grayChargedV2_spendProgress_of_goal
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hgoal : GrayChargedSpendGoalEventuallyV2 q L a e n sigma A sm) :
    GrayChargedSpendProgressV2 q L a e n sigma A sm := by
  intro t pass hst
  rcases hgoal t pass hst with hpos | ⟨u, htu, hphu, hacc⟩
  · exact Or.inl hpos
  · refine Or.inr ⟨u, htu, ?_⟩
    rw [grayChargedRunStateV2_succ]
    exact grayChargedStepV2_leaves_spend_of_goal hphu hacc

end Kolmogorov
