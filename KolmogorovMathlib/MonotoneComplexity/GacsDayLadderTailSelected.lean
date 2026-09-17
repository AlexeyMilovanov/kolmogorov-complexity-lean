import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Invariants
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.StateAt
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFresh

/-!
# Selected components of a frozen tail round

The hereditary certificate of a recursive call is indexed by sublists of the
local family. This module packages the routine conversion from a predicate on
outer grandson slots to such a sublist and exposes the corresponding numerical
gray inequality.
-/

namespace Kolmogorov

/-- The indices of the slots of a round that the predicate `keep` selects. -/
def grayTailSelectedIndices {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b) : List Nat :=
  (List.range p.slots.length).filter fun j =>
    if hj : j < p.slots.length then keep (p.slots.get ⟨j, hj⟩) else false

/-- The selected indices form a sublist of all slot indices of the round. -/
lemma grayTailSelectedIndices_sublist {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b) :
    (grayTailSelectedIndices keep p).Sublist
      (List.range p.slots.length) := by
  exact List.filter_sublist

/-- The selected indices occur among the sublists of the slot indices. -/
lemma grayTailSelectedIndices_mem_sublists {n b : Nat}
    (keep : GrayTailSlot n b -> Bool) (p : GrayTailRound n b) :
    grayTailSelectedIndices keep p ∈
      (List.range p.slots.length).sublists := by
  exact List.mem_sublists.mpr (grayTailSelectedIndices_sublist keep p)

/-- A round meeting the robust gray goal meets the subfamily goal on every subfamily of clients. -/
lemma familyRobustGrayGoalAtB.subfamily
    {kappa beta : Rat} {epsDepth deltaDepth n : Nat}
    {A : Allocation} {client : FamilyClientMove}
    {server : FamilyServerMove}
    (hgoal : familyRobustGrayGoalAtB kappa beta epsDepth deltaDepth n
      A client server = true)
    {indices : List Nat}
    (hindices : indices ∈ (List.range n).sublists) :
    familySubfamilyGrayAtB kappa epsDepth deltaDepth n
      A client server indices = true := by
  unfold familyRobustGrayGoalAtB at hgoal
  simp only [Bool.and_eq_true] at hgoal
  rw [List.all_eq_true] at hgoal
  exact hgoal.2.1 indices hindices

/-- Every frozen round of a certified tail state meets the subfamily gray goal on any selection
of its slots. -/
theorem grayTailRound_selected_subfamily
    {n b q L e t : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (hcert : GrayTailCertified q L e A sm t st)
    {p : GrayTailRound n b} (hp : p ∈ st.frozen)
    (keep : GrayTailSlot n b -> Bool) :
    familySubfamilyGrayAtB (halfAmplification q)
      p.epsDepth (p.epsDepth + L) p.slots.length p.unavailable
      p.move
      (grayTailLocalServerMove (p.epsDepth + L) p.slots
        (sm p.serverTime))
      (grayTailSelectedIndices keep p) = true := by
  have hgoal := (hcert.round_valid p hp).2.2.2.2.1
  exact familyRobustGrayGoalAtB.subfamily hgoal
    (grayTailSelectedIndices_mem_sublists keep p)

/-- For any selection of slots of a frozen round, twice the selected root request minus the total
request is bounded, after amplification, by the gray mass the selection harvests. -/
theorem grayTailRound_selected_inequality
    {n b q L e t : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {st : GrayTailState n b}
    (hcert : GrayTailCertified q L e A sm t st)
    {p : GrayTailRound n b} (hp : p ∈ st.frozen)
    (keep : GrayTailSlot n b -> Bool) :
    halfAmplification q *
        (2 * totalRootRequestOnList
            (grayTailSelectedIndices keep p) p.move -
          totalRootRequest p.slots.length p.move) <=
      grayMassOfCount (p.epsDepth + L)
        (newGrayCount p.epsDepth (p.epsDepth + L)
          (familyAllocatedOnList (grayTailSelectedIndices keep p)
            (grayTailLocalServerMove (p.epsDepth + L) p.slots
              (sm p.serverTime)))
          p.unavailable) := by
  have h := grayTailRound_selected_subfamily hcert hp keep
  unfold familySubfamilyGrayAtB at h
  exact of_decide_eq_true h

end Kolmogorov
