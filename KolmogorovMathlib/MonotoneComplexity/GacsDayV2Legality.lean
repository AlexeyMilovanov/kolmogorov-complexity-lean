import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReplayStrict
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailLegality

/-!
# Legality of the strict V2 block controller's recursive plays

Stage C4 (legality), per blueprint: anchor-generic port of
`grayChargedTailFutureServer_legal`.  With the per-round snapshot harvest as
the unavailable list (V2 cert field `unavailable_snap`), acceptance legality
is the same two-case length-cap argument — every shown cell lives in its own
slot's grandchild subtree at length `≤ δ`, while every unavailable entry is
either ambient (`A`) or a `δ`-truncated foreign allocation of the round's
snapshot, killed by `grayHarvest_untouchable`.  All underlying lemmas are
slot-list-generic, so only the V2 state record differs.
-/

namespace Kolmogorov

/-- The sub-game server seen by round `st.frozen.length` of the V2 controller
(identical shape to the V1 `grayTailFutureServer`, on the V2 state). -/
def grayBlockFutureServerV2 {n b : Nat}
    (q L e : Nat) (st : GrayTailStateV2 n b)
    (sm : Nat → FamilyServerMove) : Nat → FamilyServerMove :=
  fun t =>
    grayTailLocalServerMove
      (grayTailRoundDelta q L e st.frozen.length) st.slots
      (sm (st.roundStart + t))

/-- Ambient legality of the V2 future server (avoids `A`). -/
lemma grayBlockFutureServerV2_legal_A {n b : Nat}
    (q L e : Nat) {A : Allocation}
    {st : GrayTailStateV2 n b} (hnodup : st.slots.Nodup)
    {sm : Nat → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b A
      (grayBlockFutureServerV2 q L e st sm) := by
  have hshift :
      familyServerPlayLegal n b A
        (fun t => sm (st.roundStart + t)) := by
    simpa [Nat.add_comm] using
      familyServerPlayLegal_shift hsm st.roundStart
  unfold grayBlockFutureServerV2 grayTailLocalServerMove
  exact familyServerPlayLegal_truncFamily
    (familyServerPlayLegal_inTreeFamily
      (serverPlayLegal_extractGrandchild st.slots hnodup hshift))

/-- **Legality of the V2 block controller's recursive play.**  The active
round's future play avoids both the (snapshot-harvested) unavailable list and
every root allocation frozen by an earlier round. -/
theorem grayChargedBlockTailFutureServerV2_legal {n b q L e t : Nat}
    {A : Allocation} {st : GrayTailStateV2 n b}
    {sm : Nat → FamilyServerMove}
    (hcert : GrayChargedBlockTailCertifiedV2 q L e A sm t st)
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b st.unavailable
      (grayBlockFutureServerV2 q L e st sm) := by
  have hA := grayBlockFutureServerV2_legal_A q L e hcert.shape.slots_nodup hsm
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro u i hi x
  rw [hcert.unavailable_snap]
  intro c hc a ha
  rcases List.mem_append.mp ha with haA | haH
  · exact hA.2.2 u i hi x c hc a haA
  · let newSlot : GrayTailSlot n b := st.slots.get ⟨i, hi⟩
    have hcLocal :
        c ∈ getFamilyAlloc
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots
            (sm (st.roundStart + u))) i x := by
      simpa [grayBlockFutureServerV2] using hc
    have hx : ∀ d, d ∈ x → d < b := by
      by_contra hbad
      have hz := getFamilyAlloc_grayTailLocalServerMove_of_not_mem
        (eps := grayTailRoundDelta q L e st.frozen.length)
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
        c.length ≤ grayTailRoundDelta q L e st.frozen.length := by
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
    cases hlast : st.frozen.getLast? with
    | none =>
        rw [hlast] at haH
        simp [grayHarvestSnapshot, grayHarvest_nil] at haH
    | some pLast =>
        rw [hlast] at haH
        simp only [Option.map_some, grayHarvestSnapshot] at haH
        exact grayHarvest_untouchable hsm hnewMem hx' hcFull hcLength haH

/-- Legality of the V2 recursive play at every point of the trajectory
(the certificate holds at every `stateAt`). -/
theorem grayChargedBlockTailFutureServerV2_legal_stateAt {n b q L a e t : Nat}
    (sigma : FamilyStrategyScheme) {A : Allocation}
    {sm : Nat → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal
      (grayChargedBlockTailStateAtV2 (n := n) (b := b)
        q L a e sigma A sm t).slots.length b
      (grayChargedBlockTailStateAtV2 (n := n) (b := b)
        q L a e sigma A sm t).unavailable
      (grayBlockFutureServerV2 q L e
        (grayChargedBlockTailStateAtV2 (n := n) (b := b)
          q L a e sigma A sm t) sm) :=
  grayChargedBlockTailFutureServerV2_legal
    (grayChargedBlockTailCertifiedV2_stateAt q L a e sigma A sm t) hsm

end Kolmogorov
