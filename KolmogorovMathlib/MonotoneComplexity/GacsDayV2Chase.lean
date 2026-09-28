import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureLedger
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvSource
import KolmogorovMathlib.MonotoneComplexity.GacsDayBlockGeometry
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Round
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReplayStrict

/-!
# The V2 block controller's §9.2 disjointness chase

Stage D3, advantage side.  Port of `grayCharged_chase_core` to the V2 block
controller (`GrayTailRoundV2`, fields `blockAnchor`/`fineEnd`).  The proof is
~95% verbatim — the schedule telescope, the witness lift, the harvest
membership and the freshness kill are all string/slot-level and generic.  The
ONE substantive change is the foreignness core (Block F): the flattened
invariant "grandson = roundIndex" is replaced by the block invariant
"grandson ∈ grayInAdvBlock roundIndex", and the contradiction is closed by
`grayInAdvBlock_ne_of_round_ne` instead of `omega`.
-/

namespace Kolmogorov

/-- **The V2 cross-component chase** (proof doc v14 §9.2, block form): a
designated local gray cell of an earlier accepted block round is
prefix-incomparable with one of a later block round. -/
private lemma grayChargedBlock_chase_core
    {q L a e n t0 : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hidx : p.roundIndex < r.roundIndex)
    (hbound : r.roundIndex < grayChargedAdvantageRoundCount q)
    (hts : p.serverTime <= t0)
    (hpEps : p.blockAnchor = grayTailRoundEps q L e p.roundIndex)
    (hrEps : r.blockAnchor = grayTailRoundEps q L e r.roundIndex)
    (hpBlock : forall s, s ∈ p.slots -> grayInAdvBlock q L p.roundIndex s.2.2.val)
    (hrBlock : forall s, s ∈ r.slots -> grayInAdvBlock q L r.roundIndex s.2.2.val)
    (hrUnavail : r.unavailable =
      A ++ grayHarvest (r.blockAnchor + L) r.slots n (sm t0))
    {j j' : Nat} (hj : j < p.slots.length)
    {cu cv : BitString}
    (hcu : cu ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) j []) p.unavailable)
    (hcv : cv ∈ newGrayCellsList r.blockAnchor (r.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (r.blockAnchor + L) r.slots
        (sm r.serverTime)) j' []) r.unavailable) :
    ¬ (cu <+: cv ∨ cv <+: cu) := by
  intro hcmp
  have hRC : grayChargedAdvantageRoundCount q =
      grayTailRoundCount q - 8 := rfl
  have hdelta_le : r.blockAnchor + L <= p.blockAnchor := by
    rw [hpEps, hrEps]
    unfold grayTailRoundEps
    have hco : (grayTailRoundCount q - 1 - r.roundIndex) + 1 <=
        grayTailRoundCount q - 1 - p.roundIndex := by omega
    calc grayCallDepth q e +
          (grayTailRoundCount q - 1 - r.roundIndex) * L + L
        = grayCallDepth q e +
          ((grayTailRoundCount q - 1 - r.roundIndex) + 1) * L := by ring
      _ <= grayCallDepth q e +
          (grayTailRoundCount q - 1 - p.roundIndex) * L :=
        Nat.add_le_add_left (Nat.mul_le_mul_right L hco) _
  obtain ⟨hulen, ⟨c, hcS, hcomp_uc⟩, -⟩ := mem_newGrayCellsList.mp hcu
  obtain ⟨hvlen, -, hfreshv⟩ := mem_newGrayCellsList.mp hcv
  have hvu : cv <+: cu := by
    rcases hcmp with h | h
    · have hle := h.length_le
      have heq : cu = cv := h.eq_of_length (by omega)
      rw [heq]
    · exact h
  have hcvlen : cv.length <= p.blockAnchor := by omega
  have hvu_take : cv <+: cu.take p.blockAnchor := by
    obtain ⟨w, hw⟩ := hvu
    have h1 : cu.take cv.length = cv := by
      rw [← hw]
      exact List.take_left
    have h2 : (cu.take p.blockAnchor).take cv.length = cu.take cv.length := by
      rw [List.take_take, min_eq_left hcvlen]
    calc cv = (cu.take p.blockAnchor).take cv.length := by rw [h2, h1]
      _ <+: cu.take p.blockAnchor := List.take_prefix _ _
  have hvc : cv <+: c ∨ c <+: cv := by
    rcases hcomp_uc with h | h
    · exact Or.inl (hvu_take.trans h)
    · exact List.prefix_or_prefix_of_prefix hvu_take h
  have hcFam := grayCharged_mem_localAlloc_imp_mem_family p.toV1 ⟨j, hj⟩ hcS
  have hplay := hsm.1 (p.slots.get ⟨j, hj⟩).1.val (p.slots.get ⟨j, hj⟩).1.isLt
  have hsub := allocationSubset_mono_time hplay hts
    [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val]
  obtain ⟨c0, hc0, hc0c⟩ := hsub c hcFam
  have hforeign : grayNodeForeignB r.slots (p.slots.get ⟨j, hj⟩).1.val
      [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val] = true := by
    rw [grayNodeForeignB, List.all_eq_true]
    intro s hs
    rw [Bool.or_eq_true]
    by_cases htree : (p.slots.get ⟨j, hj⟩).1.val = s.1.val
    · right
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro hcmp2
      have heq2 : ([(p.slots.get ⟨j, hj⟩).2.1.val,
          (p.slots.get ⟨j, hj⟩).2.2.val] : GacsDayNode) =
          grayTailSlotNode s := by
        rcases hcmp2 with h | h
        · exact h.eq_of_length (by simp [grayTailSlotNode])
        · exact (h.eq_of_length (by simp [grayTailSlotNode])).symm
      have hg : (p.slots.get ⟨j, hj⟩).2.2.val = s.2.2.val := by
        simp only [grayTailSlotNode, List.cons.injEq, and_true] at heq2
        exact heq2.2
      have hpg := hpBlock _ (List.get_mem p.slots ⟨j, hj⟩)
      have hrg := hrBlock s hs
      exact absurd hg (grayInAdvBlock_ne_of_round_ne hpg hrg (Nat.ne_of_lt hidx))
    · left
      exact decide_eq_true htree
  have hvalidNode : grayNodeValidB (grayTailBranch q L a e)
      [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val] = true := by
    simp only [grayNodeValidB, List.all_eq_true]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · rcases List.mem_cons.mp hd with rfl | hd
      · simp
      · simp at hd
  have hH : c0.take (r.blockAnchor + L) ∈
      grayHarvest (r.blockAnchor + L) r.slots n (sm t0) :=
    mem_grayHarvest_of_getAlloc (p.slots.get ⟨j, hj⟩).1.isLt
      hvalidNode hforeign hc0
  have hHc : c0.take (r.blockAnchor + L) <+: c :=
    (List.take_prefix _ _).trans hc0c
  have hHv : cv <+: c0.take (r.blockAnchor + L) ∨
      c0.take (r.blockAnchor + L) <+: cv := by
    rcases hvc with h | h
    · exact List.prefix_or_prefix_of_prefix h hHc
    · exact Or.inr (hHc.trans h)
  exact hfreshv ⟨c0.take (r.blockAnchor + L),
    by rw [hrUnavail]; exact List.mem_append_right _ hH, hHv⟩

/-- The stored acceptance goal of a frozen V2 round, at its stored scales. -/
lemma grayChargedBlockV2_frozen_goal
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen) :
    grayChargedBlockGoalAtB q L e p.roundIndex
      p.slots.length p.unavailable p.move
      (grayTailLocalServerMove p.fineEnd p.slots (sm p.serverTime)) = true :=
  ((grayChargedBlockTailCertifiedV2_stateAt (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t).round_valid
      p hp).2.2.2.2.2.2.1

/-- **V2 positional chase** (Stage D3): designated local cells of two frozen
V2 block rounds at distinct positions are prefix-incomparable.  Simpler than
the V1 original — every V2 frozen round satisfies the block goal, so the
fine-vs-spend discrimination is gone. -/
theorem grayChargedBlockCells_incomparable
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {i j : Nat}
    (hi : i < (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen.length)
    (hj : j < (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen.length)
    (hij : i < j)
    {u v : Nat × BitString}
    (hu : u ∈ grayChargedLocalChargeOfBlockGoal
      (grayChargedBlockV2_frozen_goal (List.getElem_mem hi)))
    (hv : v ∈ grayChargedLocalChargeOfBlockGoal
      (grayChargedBlockV2_frozen_goal (List.getElem_mem hj))) :
    ¬ (u.2 <+: v.2 ∨ v.2 <+: u.2) := by
  set st := grayChargedBlockTailStateAtV2 (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t with hst
  have hcert := grayChargedBlockTailCertifiedV2_stateAt (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hpmem : st.frozen[i]'hi ∈ st.frozen := List.getElem_mem hi
  have hrmem : st.frozen[j]'hj ∈ st.frozen := List.getElem_mem hj
  have hpv := hcert.round_valid _ hpmem
  have hrv := hcert.round_valid _ hrmem
  -- cells of the extracted charges, at the rounds' stored scales
  have hcellu := grayChargedLocalChargeOfBlockGoal_cells
    (grayChargedBlockV2_frozen_goal hpmem) u hu
  have hcellv := grayChargedLocalChargeOfBlockGoal_cells
    (grayChargedBlockV2_frozen_goal hrmem) v hv
  -- positional facts
  have hpIdx := hcert.frozen_index i hi
  have hrIdx := hcert.frozen_index j hj
  have hijIdx : (st.frozen[i]'hi).roundIndex <
      (st.frozen[j]'hj).roundIndex := by
    rw [hpIdx, hrIdx]; exact hij
  have hrBound : (st.frozen[j]'hj).roundIndex <
      grayChargedAdvantageRoundCount q := by
    rw [hrIdx]
    exact lt_of_lt_of_le hj hcert.frozen_bound.1
  -- the snapshot of round j is a server time after every earlier round
  obtain ⟨s, hsOK, hchainj⟩ := hcert.frozen_chain j hj
  have hsne : s ≠ none := by
    intro hnone
    have htake := hsOK.1 hnone
    have hlen : (st.frozen.take j).length = j := List.length_take_of_le (le_of_lt hj)
    rw [htake] at hlen
    simp at hlen
    omega
  obtain ⟨tsnap, htsnap⟩ := Option.ne_none_iff_exists'.mp hsne
  have hts : (st.frozen[i]'hi).serverTime <= tsnap := by
    have hlen : i < (st.frozen.take j).length := by
      rw [List.length_take_of_le (le_of_lt hj)]
      exact hij
    have hmem : st.frozen[i]'hi ∈ st.frozen.take j := by
      have := List.getElem_mem hlen
      rwa [List.getElem_take] at this
    exact (hsOK.2 tsnap htsnap).2 _ hmem
  rw [htsnap] at hchainj
  simp only [grayHarvestSnapshot] at hchainj
  -- rewrite the chain's fineEnd to blockAnchor + L
  have hrFine : (st.frozen[j]'hj).fineEnd =
      (st.frozen[j]'hj).blockAnchor + L := by
    rw [hrv.2.2.2.1, hrv.2.1, grayTailRoundDelta]
  have hpFine : (st.frozen[i]'hi).fineEnd =
      (st.frozen[i]'hi).blockAnchor + L := by
    rw [hpv.2.2.2.1, hpv.2.1, grayTailRoundDelta]
  rw [hrFine] at hchainj
  -- rewrite the cells to the stored anchors
  have hcu : u.2 ∈ newGrayCellsList (st.frozen[i]'hi).blockAnchor
      ((st.frozen[i]'hi).blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove
        ((st.frozen[i]'hi).blockAnchor + L) (st.frozen[i]'hi).slots
        (sm (st.frozen[i]'hi).serverTime)) u.1 [])
      (st.frozen[i]'hi).unavailable := by
    have := hcellu.2
    rw [← hpv.2.1, ← hpv.2.2.2.1, hpFine] at this
    exact this
  have hcv : v.2 ∈ newGrayCellsList (st.frozen[j]'hj).blockAnchor
      ((st.frozen[j]'hj).blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove
        ((st.frozen[j]'hj).blockAnchor + L) (st.frozen[j]'hj).slots
        (sm (st.frozen[j]'hj).serverTime)) v.1 [])
      (st.frozen[j]'hj).unavailable := by
    have := hcellv.2
    rw [← hrv.2.1, ← hrv.2.2.2.1, hrFine] at this
    exact this
  exact grayChargedBlock_chase_core hsm hijIdx hrBound hts
    hpv.2.1 hrv.2.1
    (fun s hs => hpv.2.2.2.2.2.2.2.2 s hs)
    (fun s hs => hrv.2.2.2.2.2.2.2.2 s hs)
    hchainj hcellu.1 hcu hcv

/-- **Transported disjointness of two frozen V2 rounds** (Stage D3 lift):
the physical cylinder blocks transported from the designated charges of two
distinct frozen block rounds are disjoint, at any common final depth. -/
theorem grayChargedBlockTransport_disjoint
    {q L a e n t D : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {i j : Nat}
    (hi : i < (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen.length)
    (hj : j < (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen.length)
    (hij : i < j)
    {slots slots2 : List (GrayTailSlot n (grayTailBranch q L a e))} :
    List.Disjoint
      ((grayChargedTransportRound D slots
        (grayChargedLocalChargeOfBlockGoal
          (grayChargedBlockV2_frozen_goal (List.getElem_mem hi)))).map Prod.snd)
      ((grayChargedTransportRound D slots2
        (grayChargedLocalChargeOfBlockGoal
          (grayChargedBlockV2_frozen_goal (List.getElem_mem hj)))).map Prod.snd) :=
  grayChargedTransportRound_disjoint_of_incomparable_bases
    (fun _u hu _v hv => grayChargedBlockCells_incomparable hsm hi hj hij hu hv)

/-- **The generalized V2 chase core** (mixed phases): the schedule input
`r.fineEnd ≤ p.blockAnchor` and the slot-pair disjointness are abstract
hypotheses, so one proof serves advantage–advantage, advantage–spend and
spend–spend round pairs. -/
lemma grayChargedMixed_chase_core
    {q L a e n t0 : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p r : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hts : p.serverTime <= t0)
    (hdelta_le : r.fineEnd <= p.blockAnchor)
    (hpairs : forall sl, sl ∈ p.slots -> forall sl2, sl2 ∈ r.slots ->
      (sl.2.1, sl.2.2) ≠ (sl2.2.1, sl2.2.2))
    (hrFine : r.fineEnd = r.blockAnchor + L)
    (hrUnavail : r.unavailable =
      A ++ grayHarvest r.fineEnd r.slots n (sm t0))
    {j j' : Nat} (hj : j < p.slots.length)
    {cu cv : BitString}
    (hcu : cu ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) j []) p.unavailable)
    (hcv : cv ∈ newGrayCellsList r.blockAnchor r.fineEnd
      (getFamilyAlloc (grayTailLocalServerMove r.fineEnd r.slots
        (sm r.serverTime)) j' []) r.unavailable) :
    ¬ (cu <+: cv ∨ cv <+: cu) := by
  intro hcmp
  obtain ⟨hulen, ⟨c, hcS, hcomp_uc⟩, -⟩ := mem_newGrayCellsList.mp hcu
  obtain ⟨hvlen, -, hfreshv⟩ := mem_newGrayCellsList.mp hcv
  rw [hrFine] at hvlen
  have hvu : cv <+: cu := by
    rcases hcmp with h | h
    · have hle := h.length_le
      have heq : cu = cv := h.eq_of_length (by omega)
      rw [heq]
    · exact h
  have hcvlen : cv.length <= p.blockAnchor := by
    rw [hrFine] at hdelta_le
    omega
  have hvu_take : cv <+: cu.take p.blockAnchor := by
    obtain ⟨w, hw⟩ := hvu
    have h1 : cu.take cv.length = cv := by
      rw [← hw]
      exact List.take_left
    have h2 : (cu.take p.blockAnchor).take cv.length = cu.take cv.length := by
      rw [List.take_take, min_eq_left hcvlen]
    calc cv = (cu.take p.blockAnchor).take cv.length := by rw [h2, h1]
      _ <+: cu.take p.blockAnchor := List.take_prefix _ _
  have hvc : cv <+: c ∨ c <+: cv := by
    rcases hcomp_uc with h | h
    · exact Or.inl (hvu_take.trans h)
    · exact List.prefix_or_prefix_of_prefix hvu_take h
  have hcFam := grayCharged_mem_localAlloc_imp_mem_family p.toV1 ⟨j, hj⟩ hcS
  have hplay := hsm.1 (p.slots.get ⟨j, hj⟩).1.val (p.slots.get ⟨j, hj⟩).1.isLt
  have hsub := allocationSubset_mono_time hplay hts
    [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val]
  obtain ⟨c0, hc0, hc0c⟩ := hsub c hcFam
  have hforeign : grayNodeForeignB r.slots (p.slots.get ⟨j, hj⟩).1.val
      [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val] = true := by
    rw [grayNodeForeignB, List.all_eq_true]
    intro s hs
    rw [Bool.or_eq_true]
    by_cases htree : (p.slots.get ⟨j, hj⟩).1.val = s.1.val
    · right
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro hcmp2
      have heq2 : ([(p.slots.get ⟨j, hj⟩).2.1.val,
          (p.slots.get ⟨j, hj⟩).2.2.val] : GacsDayNode) =
          grayTailSlotNode s := by
        rcases hcmp2 with h | h
        · exact h.eq_of_length (by simp [grayTailSlotNode])
        · exact (h.eq_of_length (by simp [grayTailSlotNode])).symm
      simp only [grayTailSlotNode, List.cons.injEq, and_true] at heq2
      have hpair := hpairs _ (List.get_mem p.slots ⟨j, hj⟩) s hs
      apply hpair
      have h1 : (p.slots.get ⟨j, hj⟩).2.1.val = s.2.1.val := heq2.1
      have h2 : (p.slots.get ⟨j, hj⟩).2.2.val = s.2.2.val := heq2.2
      have h1' : (p.slots.get ⟨j, hj⟩).2.1 = s.2.1 := Fin.ext h1
      have h2' : (p.slots.get ⟨j, hj⟩).2.2 = s.2.2 := Fin.ext h2
      rw [h1', h2']
    · left
      exact decide_eq_true htree
  have hvalidNode : grayNodeValidB (grayTailBranch q L a e)
      [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val] = true := by
    simp only [grayNodeValidB, List.all_eq_true]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · rcases List.mem_cons.mp hd with rfl | hd
      · simp
      · simp at hd
  have hH : c0.take r.fineEnd ∈
      grayHarvest r.fineEnd r.slots n (sm t0) :=
    mem_grayHarvest_of_getAlloc (p.slots.get ⟨j, hj⟩).1.isLt
      hvalidNode hforeign hc0
  have hHc : c0.take r.fineEnd <+: c :=
    (List.take_prefix _ _).trans hc0c
  have hHv : cv <+: c0.take r.fineEnd ∨
      c0.take r.fineEnd <+: cv := by
    rcases hvc with h | h
    · exact List.prefix_or_prefix_of_prefix h hHc
    · exact Or.inr (hHc.trans h)
  exact hfreshv ⟨c0.take r.fineEnd,
    by rw [hrUnavail]; exact List.mem_append_right _ hH, hHv⟩

end Kolmogorov
