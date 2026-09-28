import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailRound
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLegality
import KolmogorovMathlib.MonotoneComplexity.GacsDayHarvest

/-!
# Legality of charged recursive plays

Proof doc v14 §9.6: with the per-round snapshot harvest as the unavailable
list, acceptance legality is the two-case length-cap argument — every cell
the sub-game is shown lives inside its own slot's grandchild subtree at
length at most `δ` (the round's fine end), while every unavailable entry is
either ambient (`A`, avoided by outer legality) or a `δ`-truncated foreign
allocation of the round's snapshot, killed by `grayHarvest_untouchable`.
No schedule telescope and no pass ordering are consumed.
-/

namespace Kolmogorov

/-- For a certified tail state, the server play seen by the recursive call is legal for the slots
of the state against its unavailable set. -/
theorem grayChargedTailFutureServer_legal {n b q L e t : Nat}
    {A : Allocation} {st : GrayTailState n b}
    {sm : Nat -> FamilyServerMove}
    (hcert : GrayChargedTailCertified q L e A sm t st)
    (_hround : st.frozen.length < grayTailRoundCount q)
    (hsm : familyServerPlayLegal n b A sm) :
    familyServerPlayLegal st.slots.length b st.unavailable
      (grayTailFutureServer q L e st sm) := by
  have hA := grayTailFutureServer_legal_A q L e hcert.shape hsm
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro u i hi x
  rw [hcert.unavailable_snap]
  intro c hc a ha
  rcases List.mem_append.mp ha with haA | haH
  · exact hA.2.2 u i hi x c hc a haA
  · -- the harvest case (v14 §9.6): lift the shown cell to the full server
    -- at its own slot's grandchild node and apply the untouchable lemma.
    let newSlot : GrayTailSlot n b := st.slots.get ⟨i, hi⟩
    have hcLocal :
        c ∈ getFamilyAlloc
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots
            (sm (st.roundStart + u))) i x := by
      simpa [grayTailFutureServer] using hc
    have hx : forall d, d ∈ x -> d < b := by
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
      simpa [grayTailSlotNode, getFamilyAlloc] using hextract
    have hcLength :
        c.length <= grayTailRoundDelta q L e st.frozen.length := by
      rw [getFamilyAlloc_grayTailLocalServerMove
        st.slots (sm (st.roundStart + u)) i hi x hx] at hcLocal
      exact (mem_truncAlloc.mp (by simpa [newSlot] using hcLocal)).2
    have hnewMem : newSlot ∈ st.slots := List.get_mem st.slots ⟨i, hi⟩
    have hx' : forall d, d ∈ grayTailSlotNode newSlot ++ x -> d < b := by
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

end Kolmogorov
