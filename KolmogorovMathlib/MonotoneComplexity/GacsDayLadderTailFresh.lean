import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailResolutionExact

/-!
# Freshness of the reserve after the last call

The exact exit invariant records a checkpoint before a son's last recursive
call at which no family reserve exists. This file turns that Boolean search
fact into the geometric statement used in Day's accounting: the later reserve
is incomparable with every allocation retained from an earlier call.
-/

namespace Kolmogorov

/-- If the exhaustive family-reserve search is empty at time t, a cylinder
which is a family reserve at a later time cannot already be a tail reserve at
time t. The missing cross-tree clauses are inherited backwards from the later
family reserve, while its hypothetical anchor at t supplies the remaining
clause. -/
lemma IsTailFamilyReserve.not_tail_of_search_none
    {e b n i t T : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {x : GacsDayNode} {R : BitString}
    (hleg : familyServerPlayLegal n b A sm) (htT : t <= T)
    (hR : IsTailFamilyReserve e b A n i (sm T) x R)
    (hnone : (getTailFamilyReserve e b A n i (sm t) x).isNone) :
    ¬ IsTailReserve e b A (familyServerMoveAt (sm t) i) x R := by
  intro hRt
  have hfamily : IsTailFamilyReserve e b A n i (sm t) x R := by
    refine ⟨hRt, ?_⟩
    intro j hj hji c hc hcomp
    have hmono := allocationSubset_mono_time
      (hleg.1 j hj) htT ([] : GacsDayNode)
    obtain ⟨d, hd, hdc⟩ := hmono c hc
    apply hR.2 j hj hji d hd
    exact prefixComparable_of_common_extension hcomp hdc
  have hsome :
      (getTailFamilyReserve e b A n i (sm t) x).isSome :=
    (getTailFamilyReserve_isSome_iff e b A n i (sm t) x).2
      ⟨R, hfamily⟩
  cases hopt : getTailFamilyReserve e b A n i (sm t) x <;>
    simp_all

/-- The last-reserve witness can be exposed together with the geometric
freshness statement for every earlier round in its prefix. -/
theorem GrayTailReserveExit.prefix_allocations_fresh
    {n b e L : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm)
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    (h : GrayTailReserveExit e A sm frozen i c) :
    exists pre p post R,
      frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      IsTailFamilyReserve e b A n i.val (sm p.serverTime) [c.val] R ∧
      grayTailFrozenSonBase frozen i c =
        grayTailFrozenSonBase pre i c +
          grayTailSonBase (grayTailSlotEntries p.slots p.move) i c ∧
      forall q, q ∈ pre ->
        forall j : Fin q.slots.length,
          (q.slots.get j).1 = i ->
          (q.slots.get j).2.1 = c ->
          forall d, d ∈ getFamilyAlloc
            (grayTailLocalServerMove (q.epsDepth + L)
              q.slots (sm q.serverTime)) j.val [] ->
            ¬ (R <+: d ∨ d <+: R) := by
  obtain ⟨pre, p, post, R, hsplit, hp, hR, hfresh, hpost⟩ := h
  refine ⟨pre, p, post, R, hsplit, hp, hR, ?_, ?_⟩
  · rw [hsplit, show p :: post = [p] ++ post by rfl,
      grayTailFrozenSonBase_append_list,
      grayTailFrozenSonBase_append_list,
      grayTailFrozenSonBase_eq_zero_of_no_round i c hpost]
    have hone : grayTailFrozenSonBase ([p] : GrayTailFrozen n b) i c =
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by
      simp [grayTailFrozenSonBase, grayTailFrozenEntries, grayTailSonBase]
    rw [hone]
    ring
  · intro q hq j hji hjc d hd
    rcases hfresh with hempty | ⟨checkpoint, hmax, hcheckpoint, hnone⟩
    · subst pre
      simp at hq
    · have hqCheckpoint : q.serverTime <= checkpoint := hmax q hq
      have hmono := allocationSubset_mono_time
        (hleg.1 i.val i.isLt) hqCheckpoint
        [c.val, (q.slots.get j).2.2.val]
      have hdRaw : d ∈ getFamilyAlloc (sm q.serverTime) i.val
          [c.val, (q.slots.get j).2.2.val] := by
        rw [getFamilyAlloc_grayTailLocalServerMove
          q.slots (sm q.serverTime) j.val j.isLt [] (by simp)] at hd
        have hd' := (mem_truncAlloc.mp hd).1
        have hd'' : d ∈ getFamilyAlloc (sm q.serverTime)
            (q.slots.get j).1.val
            [(q.slots.get j).2.1.val, (q.slots.get j).2.2.val] := by
          simpa [getFamilyAlloc, getAlloc_extractSubtreeServerMove] using hd'
        simpa only [hji, hjc] using hd''
      obtain ⟨d', hd', hd'd⟩ := hmono d hdRaw
      have hnot := IsTailFamilyReserve.not_tail_of_search_none
        hleg hcheckpoint hR hnone
      have hfreshR := IsTailReserve.fresh_of_not_before
        (hleg.1 i.val i.isLt) hcheckpoint
        (x := [c.val]) (by simp)
        hR.1 hnot
        (y := [c.val, (q.slots.get j).2.2.val]) (by simp)
        (by
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact c.isLt
          · exact (q.slots.get j).2.2.isLt)
        hd'
      intro hcomp
      exact hfreshR (prefixComparable_of_common_extension hcomp hd'd)

/-- A reserve created after a threshold exit is incomparable with every
allocation from the calls strictly before the exit's last call. -/
theorem GrayTailThresholdExit.prefix_allocations_fresh
    {n b e L : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n b A sm)
    {frozen : GrayTailFrozen n b} {i : Fin n} {c : Fin b}
    (h : GrayTailThresholdExit e A sm frozen i c)
    {T : Nat} {R : BitString}
    (hR : IsTailFamilyReserve e b A n i.val (sm T) [c.val] R)
    (hafter : forall p, p ∈ frozen -> GrayTailRoundHasSon p i c ->
      p.serverTime <= T) :
    exists pre p post,
      frozen = pre ++ p :: post ∧
      GrayTailRoundHasSon p i c ∧
      grayTailFrozenSonBase frozen i c =
        grayTailFrozenSonBase pre i c +
          grayTailSonBase (grayTailSlotEntries p.slots p.move) i c ∧
      forall q, q ∈ pre ->
        forall j : Fin q.slots.length,
          (q.slots.get j).1 = i ->
          (q.slots.get j).2.1 = c ->
          forall d, d ∈ getFamilyAlloc
            (grayTailLocalServerMove (q.epsDepth + L)
              q.slots (sm q.serverTime)) j.val [] ->
            ¬ (R <+: d ∨ d <+: R) := by
  obtain ⟨pre, p, post, hsplit, hp, hfresh, hpost⟩ := h
  refine ⟨pre, p, post, hsplit, hp, ?_, ?_⟩
  · rw [hsplit, show p :: post = [p] ++ post by rfl,
      grayTailFrozenSonBase_append_list,
      grayTailFrozenSonBase_append_list,
      grayTailFrozenSonBase_eq_zero_of_no_round i c hpost]
    have hone : grayTailFrozenSonBase ([p] : GrayTailFrozen n b) i c =
        grayTailSonBase (grayTailSlotEntries p.slots p.move) i c := by
      simp [grayTailFrozenSonBase, grayTailFrozenEntries,
        grayTailSonBase]
    rw [hone]
    ring
  · intro q hq j hji hjc d hd
    rcases hfresh with hempty | ⟨checkpoint, hmax, hcheckpoint, hnone⟩
    · subst pre
      simp at hq
    · have hqCheckpoint : q.serverTime <= checkpoint := hmax q hq
      have hpT : p.serverTime <= T := hafter p (by simp [hsplit]) hp
      have hcheckpointT : checkpoint <= T :=
        le_trans hcheckpoint hpT
      have hmono := allocationSubset_mono_time
        (hleg.1 i.val i.isLt) hqCheckpoint
        [c.val, (q.slots.get j).2.2.val]
      have hdRaw : d ∈ getFamilyAlloc (sm q.serverTime) i.val
          [c.val, (q.slots.get j).2.2.val] := by
        rw [getFamilyAlloc_grayTailLocalServerMove
          q.slots (sm q.serverTime) j.val j.isLt [] (by simp)] at hd
        have hd' := (mem_truncAlloc.mp hd).1
        have hd'' : d ∈ getFamilyAlloc (sm q.serverTime)
            (q.slots.get j).1.val
            [(q.slots.get j).2.1.val, (q.slots.get j).2.2.val] := by
          simpa [getFamilyAlloc, getAlloc_extractSubtreeServerMove] using hd'
        simpa only [hji, hjc] using hd''
      obtain ⟨d', hd', hd'd⟩ := hmono d hdRaw
      have hnot := IsTailFamilyReserve.not_tail_of_search_none
        hleg hcheckpointT hR hnone
      have hfreshR := IsTailReserve.fresh_of_not_before
        (hleg.1 i.val i.isLt) hcheckpointT
        (x := [c.val]) (by simp)
        hR.1 hnot
        (y := [c.val, (q.slots.get j).2.2.val]) (by simp)
        (by
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact c.isLt
          · exact (q.slots.get j).2.2.isLt)
        hd'
      intro hcomp
      exact hfreshR (prefixComparable_of_common_extension hcomp hd'd)

end Kolmogorov
