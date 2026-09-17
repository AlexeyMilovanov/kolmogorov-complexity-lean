import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Progress

/-!
# The strict V2 block controller is done or has slots

The V2 analogue of `GrayTailDoneOrNonempty` (`GacsDayChargedTerminationSupport`):
along the strict advantage trajectory a state is either `done` or carries a
nonempty slot list.  The initial wide block is nonempty (`n ≥ 1`, the source
count and the round-`0` grandson block are positive); a freeze with an empty
wide next-block has an empty narrow next-block (the wide count factors through
the nonempty grandson block), so the global quarter fires and the state is
`done`.  Consequently a terminal state (`done || slots.isEmpty`) is `done`.
-/

namespace Kolmogorov

/-- A V2 block state is `done` or has a nonempty slot list. -/
def GrayTailDoneOrNonemptyV2 {n b : Nat} (st : GrayTailStateV2 n b) : Prop :=
  st.done = true ∨ st.slots ≠ []

/-- The freeze data of a V2 round: the new `done` flag or the new wide slot
list is nonempty. -/
lemma grayBlockFreeze_done_or_nonempty {n q L a e round : Nat}
    (source : Nat) (threshold : Rat) (A : Allocation)
    (frozenV1 : GrayTailFrozen n (grayTailBranch q L a e))
    (sm : FamilyServerMove) :
    (grayTailGlobalQuarterB source
        (grayTailNextSlots e source round threshold A frozenV1 sm) ||
      decide (grayChargedAdvantageRoundCount q <= round)) = true ∨
    grayBlockNextSlots q L e source round threshold A frozenV1 sm ≠ [] := by
  by_cases hcount : grayChargedAdvantageRoundCount q <= round
  · left
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hcount
  · have hlt : round < grayChargedAdvantageRoundCount q := by omega
    by_cases htail : grayTailNextSlots e source round threshold A frozenV1 sm = []
    · left
      simp [grayTailGlobalQuarterB, htail]
    · right
      intro hnil
      have hr : round < grayTailBranch q L a e :=
        round_lt_branch_of_lt_advCount hlt
      have hlen := grayBlockNextSlots_length q L e source round threshold A
        frozenV1 sm hr
      rw [hnil] at hlen
      simp only [List.length_nil] at hlen
      have hG := grayAdvBlockGrandsons_length_used (L := L) (a := a) (e := e) hlt
      rw [hG] at hlen
      have hpos := grayAdvBlockMult_pos q L round
      have htl : 0 <
          (grayTailNextSlots e source round threshold A frozenV1 sm).length :=
        List.length_pos_of_ne_nil htail
      have hprod := Nat.mul_pos htl hpos
      omega

/-- The initial V2 block tail state of a nonempty family has an open slot. -/
lemma grayChargedBlockDoneOrNonemptyV2_initial
    {n q L a e : Nat} (hn : 1 <= n) (A : Allocation) :
    GrayTailDoneOrNonemptyV2
      (grayChargedBlockTailInitialStateV2 n (grayTailBranch q L a e) a e q L A) := by
  right
  intro hnil
  have hb : 0 < grayTailBranch q L a e :=
    lt_of_lt_of_le (by omega) (two_le_ladderBranching (le_max_left 2 _) a e)
  let i : Fin n := ⟨0, by omega⟩
  let c : Fin (grayTailBranch q L a e) := ⟨0, hb⟩
  have hG : grayAdvBlockGrandsons (grayTailBranch q L a e) q L 0 ≠ [] :=
    grayAdvBlockGrandsons_ne_nil_of_le (a := a) (e := e) (Nat.zero_le _)
  have hson := grayAdvBlockSlots_hasSon (n := n)
    (used := grayChargedSourceCount a e) i c
    (by
      change 0 < grayChargedSourceCount a e
      simp [grayChargedSourceCount]) hG
  obtain ⟨s, hs, _⟩ := hson
  have hnil' :
      grayAdvBlockSlots n (grayTailBranch q L a e)
        (grayChargedSourceCount a e) q L 0 = [] := hnil
  rw [hnil'] at hs
  simp at hs

/-- A V2 block tail step keeps the state either finished or holding an open slot. -/
lemma grayChargedBlockDoneOrNonemptyV2_step
    {n q L a e : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {st : GrayTailStateV2 n (grayTailBranch q L a e)} (sm : FamilyServerMove)
    (hst : GrayTailDoneOrNonemptyV2 st) :
    GrayTailDoneOrNonemptyV2 (grayChargedBlockTailStepV2 q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · simp [grayChargedBlockTailStepV2, hd, GrayTailDoneOrNonemptyV2]
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · simpa [grayChargedBlockTailStepV2, hd', hs, GrayTailDoneOrNonemptyV2] using hst
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length st.slots.length
          st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots sm) = true
      · simp only [grayChargedBlockTailStepV2, hd', hs', hg, Bool.false_eq_true,
          ↓reduceIte]
        unfold GrayTailDoneOrNonemptyV2
        dsimp only
        exact grayBlockFreeze_done_or_nonempty _ _ _ _ _
      · simpa [grayChargedBlockTailStepV2, hd', hs', hg,
          GrayTailDoneOrNonemptyV2] using hst

/-- Every state of a V2 block tail run over a nonempty family is either finished or holds an open
slot. -/
theorem grayChargedBlockDoneOrNonemptyV2_stateAt
    {n q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n) (t : Nat) :
    GrayTailDoneOrNonemptyV2
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayChargedBlockDoneOrNonemptyV2_initial hn A
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayChargedBlockDoneOrNonemptyV2_step (sm t) ih

/-- A terminal strict V2 state (`done || slots.isEmpty`) is `done`. -/
theorem grayChargedBlockV2_done_of_terminal
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hn : 1 <= n)
    (hterminal : ((grayChargedBlockTailStateAtV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t).done ||
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done = true := by
  rcases grayChargedBlockDoneOrNonemptyV2_stateAt
      (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) hn t with hdone | hnonempty
  · exact hdone
  · by_contra h
    have hdoneFalse : (grayChargedBlockTailStateAtV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t).done = false :=
      Bool.eq_false_of_not_eq_true h
    have hempty : (grayChargedBlockTailStateAtV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t).slots.isEmpty = true := by
      simpa [hdoneFalse] using hterminal
    exact hnonempty (List.isEmpty_iff.mp hempty)

end Kolmogorov
