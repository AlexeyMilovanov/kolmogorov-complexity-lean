import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Legality

/-!
# Legality of the V2 spend passes' recursive plays

Spend-phase companion of `GacsDayV2Legality`: the sub-game server seen by
spend pass `pass` of the V2 controller lives at the pass's fine depth
`grayChargedSpendDelta a L e pass`, and its play avoids the snapshot-harvested
unavailable list of the spend certificate (field `unavailable_snap`).  The
argument is the same two-case length-cap argument as for the advantage
rounds — every shown cell lives in its own slot's grandchild subtree at
length `≤ δ`, while every unavailable entry is either ambient (`A`) or a
`δ`-truncated foreign allocation of the pass's snapshot, killed by
`grayHarvest_untouchable`.  All underlying lemmas are slot-list-generic and
depth-generic, so only the certificate (and hence the source of
`st.slots.Nodup`, here `core.all_slots_nodup`) differs.
-/

namespace Kolmogorov

/-- The sub-game server seen by spend pass `pass` of the V2 controller
(same shape as `grayBlockFutureServerV2`, at the pass's fine depth). -/
def grayChargedSpendFutureServerV2 {n b : Nat}
    (a L e pass : Nat) (st : GrayTailStateV2 n b)
    (sm : Nat → FamilyServerMove) : Nat → FamilyServerMove :=
  fun t =>
    grayTailLocalServerMove
      (grayChargedSpendDelta a L e pass) st.slots
      (sm (st.roundStart + t))

/-- Ambient legality of the V2 spend future server (avoids `A`). -/
lemma grayChargedSpendFutureServerV2_legal_A {n b : Nat}
    (a L e pass : Nat) {A : Allocation}
    {st : GrayTailStateV2 n b} (hnodup : st.slots.Nodup)
    {sm : Nat → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b A
      (grayChargedSpendFutureServerV2 a L e pass st sm) := by
  have hshift :
      familyServerPlayLegal n b A
        (fun t => sm (st.roundStart + t)) := by
    simpa [Nat.add_comm] using
      familyServerPlayLegal_shift hsm st.roundStart
  unfold grayChargedSpendFutureServerV2 grayTailLocalServerMove
  exact familyServerPlayLegal_truncFamily
    (familyServerPlayLegal_inTreeFamily
      (serverPlayLegal_extractGrandchild st.slots hnodup hshift))

/-- **Legality of the V2 spend pass's recursive play**: the pass's future play
avoids the snapshot-harvested unavailable list. -/
theorem grayChargedSpendFutureServerV2_legal {n b q L a e t pass : Nat}
    {A : Allocation} {st : GrayTailStateV2 n b}
    {sm : Nat → FamilyServerMove}
    (hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass st)
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b st.unavailable
      (grayChargedSpendFutureServerV2 a L e pass st sm) := by
  have hnodup : st.slots.Nodup :=
    (List.nodup_append.mp hspend.core.all_slots_nodup).2.1
  have hA := grayChargedSpendFutureServerV2_legal_A a L e pass hnodup hsm
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro u i hi x
  obtain ⟨s, -, -, hsnap⟩ := hspend.unavailable_snap
  rw [hsnap]
  intro c hc y hy
  rcases List.mem_append.mp hy with hyA | hyH
  · exact hA.2.2 u i hi x c hc y hyA
  · let newSlot : GrayTailSlot n b := st.slots.get ⟨i, hi⟩
    have hcLocal :
        c ∈ getFamilyAlloc
          (grayTailLocalServerMove
            (grayChargedSpendDelta a L e pass) st.slots
            (sm (st.roundStart + u))) i x := by
      simpa [grayChargedSpendFutureServerV2] using hc
    have hx : ∀ d, d ∈ x → d < b := by
      by_contra hbad
      have hz := getFamilyAlloc_grayTailLocalServerMove_of_not_mem
        (eps := grayChargedSpendDelta a L e pass)
        st.slots (sm (st.roundStart + u)) i hi x hbad
      rw [hz] at hcLocal
      simp at hcLocal
    have hcFull : c ∈ getFamilyAlloc (sm (st.roundStart + u)) newSlot.1.val
        (grayTailSlotNode newSlot ++ x) := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      have hextract := (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).1
      exact hextract
    have hcLength :
        c.length ≤ grayChargedSpendDelta a L e pass := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      exact (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).2
    have hnewMem : newSlot ∈ st.slots := List.get_mem st.slots ⟨i, hi⟩
    have hx' : ∀ d, d ∈ grayTailSlotNode newSlot ++ x → d < b := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_cons.mp hd with hd | hd
        · exact hd ▸ newSlot.2.1.isLt
        · have hde : d = newSlot.2.2.val := by simpa using hd
          exact hde ▸ newSlot.2.2.isLt
      · exact hx d hd
    exact grayHarvest_untouchable hsm hnewMem hx' hcFull hcLength hyH

end Kolmogorov
