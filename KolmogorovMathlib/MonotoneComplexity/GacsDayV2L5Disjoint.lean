import KolmogorovMathlib.MonotoneComplexity.GacsDayV2OwnerComplement
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2L5Leaves

/-!
# The advantage-side source/reserve disjointness (Phase 2B/2C bridge)

The datum of Phase 2A excludes every non-owner slot allocation; through the
trace bridge this excludes every non-owner designated cell of every
advantage round from the reserve's comparability cone.  Owner-fibre cells
are exactly the owner window that the complement `K(z)` removes.
-/

namespace Kolmogorov

/-- The round charge does not depend on the observation time. -/
lemma grayChargedRoundLocalChargeV2_time_irrel
    {q L a e n t t' : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hp' : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm t').core.frozen) :
    grayChargedRoundLocalChargeV2 hae p hp =
      grayChargedRoundLocalChargeV2 hae p hp' := rfl

/-- Every advantage-terminal round is anchored at or above the call depth. -/
lemma grayChargedReplayV2_terminal_round_adv
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ replay.advantageTerminal.frozen) :
    grayCallDepth q e <= p.blockAnchor := by
  have hterm := grayChargedReplayV2_advantageTerminal_eq_stateAt replay
  have hmem : p ∈ (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (replay.advantageExitTime + 1)).frozen := by
    rw [← hterm]
    exact hp
  have hvalid := (grayChargedBlockTailCertifiedV2_stateAt (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm (replay.advantageExitTime + 1)).round_valid p hmem
  rw [hvalid.2.1, grayTailRoundEps]
  exact Nat.le_add_right _ _

/-- **Non-owner advantage cells are incomparable with the datum reserve**:
a designated cell of an advantage-terminal round, sitting at a non-owner
position or a non-fibre slot, cannot share a dyadic cone with the reserve. -/
theorem grayChargedV2_datum_advCell_incomparable
    {q L a e n T t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {tR : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z tR R k)
    (kk : Fin replay.advantageTerminal.frozen.length)
    (hp : replay.advantageTerminal.frozen[kk.val] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen)
    {u : Nat × BitString}
    (hu : u ∈ grayChargedRoundLocalChargeV2 hae
      (replay.advantageTerminal.frozen[kk.val]) hp)
    (hcond : kk.val ≠ k ∨
      forall hlt : u.1 <
          (replay.advantageTerminal.frozen[kk.val]).slots.length,
        ¬ (((replay.advantageTerminal.frozen[kk.val]).slots.get
              ⟨u.1, hlt⟩).1 = z.1 ∧
          ((replay.advantageTerminal.frozen[kk.val]).slots.get
              ⟨u.1, hlt⟩).2.1 = z.2)) :
    ¬ (u.2 <+: R ∨ R <+: u.2) := by
  have hlt : u.1 <
      (replay.advantageTerminal.frozen[kk.val]).slots.length :=
    (grayChargedRoundLocalChargeV2_cells hae _ hp u hu).1
  have hadv : grayCallDepth q e <=
      (replay.advantageTerminal.frozen[kk.val]).blockAnchor :=
    grayChargedReplayV2_terminal_round_adv replay
      (List.getElem_mem kk.isLt)
  have hcondD : kk.val ≠ k ∨
      ((replay.advantageTerminal.frozen[kk.val]).slots.get
        ⟨u.1, hlt⟩).1 ≠ z.1 ∨
      ((replay.advantageTerminal.frozen[kk.val]).slots.get
        ⟨u.1, hlt⟩).2.1 ≠ z.2 := by
    rcases hcond with h | h
    · exact Or.inl h
    · rcases not_and_or.mp (h hlt) with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  have hfreshS := hdata.2.2.2 kk ⟨u.1, hlt⟩ hcondD
  have hRe : R.length = e := hdata.1.1.1
  exact grayChargedV2_cell_reserve_incomparable_of_slot_fresh hae
    (replay.advantageTerminal.frozen[kk.val]) hp hu hRe hadv hfreshS

/-- A common final-depth string cannot extend both a fine cell and a
reserve the fine cell is incomparable with. -/
lemma grayChargedV2_extension_ne_of_incomparable
    {x R w y : BitString}
    (hxw : x <+: w) (hRy : R <+: y)
    (hincomp : ¬ (x <+: R ∨ R <+: x)) :
    w ≠ y := by
  intro heq
  subst heq
  exact hincomp (List.prefix_or_prefix_of_prefix hxw hRy)

/-- Complement cells extend the reserve. -/
lemma grayChargedReserveComplementV2_prefix
    {i D : Nat} {R : BitString} {owner : FamilyGrayCharge}
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 i D R owner) :
    R <+: y.2 := by
  have hmem := (grayChargedReserveComplementV2_sublist i D R owner).mem hy
  rw [grayChargedReserveCylinder, List.mem_map] at hmem
  obtain ⟨s, -, rfl⟩ := hmem
  exact ⟨s, rfl⟩

/-- Transported cells extend their fine source cell. -/
lemma grayChargedTransportRoot_extends
    {delta owner root : Nat} {G : FamilyGrayCharge}
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot delta owner root G) :
    exists u, u ∈ G ∧ u ∈ grayChargeAtRoot root G ∧ u.2 <+: w.2 := by
  obtain ⟨u, hu, hmap⟩ := mem_grayChargedTransportRoot.mp hw
  rw [List.mem_map] at hmap
  obtain ⟨s, -, rfl⟩ := hmap
  exact ⟨u, (mem_grayChargeAtRoot.mp hu).1, hu, ⟨s, rfl⟩⟩

/-- A fibre-slot transported cell reappears, tagged by the source tree, in
the owner fibre component. -/
lemma grayChargedOwnerFibreV2_mem_of_transport
    {q L a e n t t' : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hp' : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm t').core.frozen)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (j : Fin p.slots.length)
    (hfib : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2)
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      ((p.slots.get j).1.val) j.val
      (grayChargedRoundLocalChargeV2 hae p hp)) :
    (z.1.val, w.2) ∈ grayChargedOwnerFibreV2 hae p hp' z := by
  rw [grayChargedOwnerFibreV2, List.mem_flatMap]
  refine ⟨j, List.mem_finRange _, ?_⟩
  rw [if_pos hfib]
  obtain ⟨u, hu, hmap⟩ := mem_grayChargedTransportRoot.mp hw
  rw [List.mem_map] at hmap
  obtain ⟨s, hs, rfl⟩ := hmap
  rw [grayChargedRoundLocalChargeV2_time_irrel hae p hp' hp]
  exact mem_grayChargedTransportRoot.mpr
    ⟨u, hu, List.mem_map.mpr ⟨s, hs, rfl⟩⟩

/-- **The owner-window kill**: a transported cell of the owner fibre slot
never equals a complement cell — the complement removed exactly that
window. -/
theorem grayChargedV2_transported_ownerCell_ne_complement
    {q L a e n t t' : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hp' : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm t').core.frozen)
    (z : Fin n × Fin (grayTailBranch q L a e))
    {R : BitString}
    (j : Fin p.slots.length)
    (hfib : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2)
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      ((p.slots.get j).1.val) j.val
      (grayChargedRoundLocalChargeV2 hae p hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 z.1.val
      (e + grayTailNewLoss q L) R
      (grayChargedOwnerFibreV2 hae p hp' z)) :
    w.2 ≠ y.2 := by
  intro heq
  have hwmem := grayChargedOwnerFibreV2_mem_of_transport hae p hp hp' z j
    hfib hw
  have havoid := grayChargedReserveComplementV2_avoids hy hwmem
  exact havoid (heq ▸ List.prefix_refl _)

/-- **The non-owner kill**: a transported cell whose fine source is
incomparable with the reserve never equals a complement cell. -/
theorem grayChargedV2_transported_cell_ne_complement_of_incomparable
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    {tagOwner root : Nat} {R : BitString}
    {owner : FamilyGrayCharge} {i : Nat}
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      tagOwner root (grayChargedRoundLocalChargeV2 hae p hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 i
      (e + grayTailNewLoss q L) R owner)
    (hincomp : forall u, u ∈ grayChargeAtRoot root
        (grayChargedRoundLocalChargeV2 hae p hp) ->
      ¬ (u.2 <+: R ∨ R <+: u.2)) :
    w.2 ≠ y.2 := by
  obtain ⟨u, -, huR, huw⟩ := grayChargedTransportRoot_extends hw
  exact grayChargedV2_extension_ne_of_incomparable huw
    (grayChargedReserveComplementV2_prefix hy) (hincomp u huR)

/-- **§4.3(res), time-generalized**: a designated cell of a spend round is
prefix-incomparable with every reserve created at or before the round's
snapshot — the reserve's allocated witness persists into the snapshot and
its truncation is harvested into the round's unavailable list. -/
theorem grayChargedV2_spendCell_early_reserve_incomparable
    {q L a e n t t0 tau : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hchain : p.unavailable =
      A ++ grayHarvest p.fineEnd p.slots n (sm t0))
    (hspare : forall s, s ∈ p.slots ->
      grayChargedSourceCount a e <= s.2.1.val)
    (hfineE : p.fineEnd <= e)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)}
    (hcsrc : c.val < grayChargedSourceCount a e)
    {R : BitString} (htau : tau <= t0)
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val
      (sm tau) [c.val] R)
    (hRlen : R.length = e)
    {z : Nat × BitString}
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  intro hcmp
  have hcells := grayChargedRoundLocalChargeV2_cells hae p hp z hz
  obtain ⟨hzlen, -, hfresh⟩ := mem_newGrayCellsList.mp hcells.2
  have hfineEq : p.fineEnd = p.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
  -- the reserve's allocated witness, persisted into the snapshot
  obtain ⟨v0, hv0, hRv0⟩ := hR.1.2.1
  obtain ⟨v, hv, hvv0⟩ := allocationSubset_mono_time
    (hleg.1 i.val i.isLt) htau [c.val] v0 hv0
  -- the round's fine cells never extend the coarser reserve properly:
  -- lengths force `z.2 ≺ R`
  have hzR2 : z.2 <+: R := by
    rcases hcmp with h | h
    · exact h
    · have hle := h.length_le
      have heq : R = z.2 := h.eq_of_length (by omega)
      rw [heq]
  have hzv0 : z.2 <+: v0 ∨ v0 <+: z.2 := by
    rcases hRv0 with h2 | h2
    · exact Or.inl (hzR2.trans h2)
    · rcases List.prefix_or_prefix_of_prefix h2 hzR2 with h3 | h3
      · exact Or.inr h3
      · exact Or.inl h3
  have hzv : z.2 <+: v ∨ v <+: z.2 :=
    prefixComparable_of_common_extension hzv0 hvv0
  -- the harvested truncation of the persisted witness
  have hu : v.take p.fineEnd ∈ grayHarvest p.fineEnd p.slots n (sm t0) := by
    have hvalidNode : grayNodeValidB (grayTailBranch q L a e)
        [c.val] = true := by
      simp only [grayNodeValidB, List.all_eq_true]
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · simp [c.isLt]
      · simp at hd
    have hforeign : grayNodeForeignB p.slots i.val [c.val] = true := by
      rw [grayNodeForeignB, List.all_eq_true]
      intro s hs
      rw [Bool.or_eq_true]
      by_cases htree : i.val = s.1.val
      · right
        rw [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hcmp2
        have hlen1 : ([c.val] : GacsDayNode).length = 1 := rfl
        have hlen2 : (grayTailSlotNode s).length = 2 := by
          simp [grayTailSlotNode]
        rcases hcmp2 with h | h
        · -- [c] a prefix of [c', d'] forces c = c'
          obtain ⟨tl, htl⟩ := h
          have hc2 : c.val = s.2.1.val := by
            have hhead := congrArg (fun l => l.head?) htl
            simpa [grayTailSlotNode] using hhead
          have := hspare s hs
          omega
        · have := h.length_le
          simp [grayTailSlotNode] at this
      · left
        exact decide_eq_true htree
    exact mem_grayHarvest_of_getAlloc i.isLt hvalidNode hforeign hv
  -- freshness of z.2 against the harvested cell
  apply hfresh
  refine ⟨v.take p.fineEnd, ?_, ?_⟩
  · rw [hchain]
    exact List.mem_append_right _ hu
  · -- z.2 (length fineEnd) is comparable with the truncation
    have hzlen' : z.2.length = p.fineEnd := by
      rw [hzlen, hfineEq]
    rcases hzv with h | h
    · -- z.2 ≺ v: the truncation extends or equals z.2
      by_cases hlv : v.length <= p.fineEnd
      · have : v.take p.fineEnd = v := List.take_of_length_le hlv
        rw [this]
        exact Or.inl h
      · have hzt : z.2 <+: v.take p.fineEnd := by
          have h1 : (v.take p.fineEnd).take z.2.length =
              v.take z.2.length := by
            rw [List.take_take, min_eq_left (by omega)]
          have h2 : v.take z.2.length = z.2 := by
            obtain ⟨tl, htl⟩ := h
            rw [← htl, List.take_left]
          rw [← h2, ← h1]
          exact List.take_prefix _ _
        exact Or.inl hzt
    · -- v ≺ z.2: the truncation is a prefix of z.2
      have hvlen : v.length <= p.fineEnd := by
        have := h.length_le
        omega
      have : v.take p.fineEnd = v := List.take_of_length_le hvlen
      rw [this]
      exact Or.inr h

/-- **§4.3(res), anchored form** (amendment G1.4): with an ANCHORED early
reserve the persistence is direct — the anchor's persisted form is
harvested, and every cell comparable with the reserve is comparable with
it. -/
theorem grayChargedV2_spendCell_early_anchored_incomparable
    {q L a e n t t0 tau : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hchain : p.unavailable =
      A ++ grayHarvest p.fineEnd p.slots n (sm t0))
    (hspare : forall s, s ∈ p.slots ->
      grayChargedSourceCount a e <= s.2.1.val)
    (hfineE : p.fineEnd <= e)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)}
    (hcsrc : c.val < grayChargedSourceCount a e)
    {R : BitString} (htau : tau <= t0)
    (hR : IsAnchoredTailFamilyReserve e (grayTailBranch q L a e) A n i.val
      (sm tau) [c.val] R)
    (hRlen : R.length = e)
    {z : Nat × BitString}
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  intro hcmp
  have hcells := grayChargedRoundLocalChargeV2_cells hae p hp z hz
  obtain ⟨hzlen, -, hfresh⟩ := mem_newGrayCellsList.mp hcells.2
  have hfineEq : p.fineEnd = p.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
  -- the anchor, persisted into the snapshot
  obtain ⟨v0, hv0, hv0R⟩ := hR.2
  obtain ⟨v, hv, hvv0⟩ := allocationSubset_mono_time
    (hleg.1 i.val i.isLt) htau [c.val] v0 hv0
  have hvR : v <+: R := hvv0.trans hv0R
  -- the fine cell is a prefix of the reserve (lengths), hence comparable
  -- with the persisted anchor
  have hzR2 : z.2 <+: R := by
    rcases hcmp with h | h
    · exact h
    · have hle := h.length_le
      have heq : R = z.2 := h.eq_of_length (by omega)
      rw [heq]
  have hzv : z.2 <+: v ∨ v <+: z.2 := by
    rcases List.prefix_or_prefix_of_prefix hvR hzR2 with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- the harvested truncation of the persisted anchor
  have hu : v.take p.fineEnd ∈ grayHarvest p.fineEnd p.slots n (sm t0) := by
    have hvalidNode : grayNodeValidB (grayTailBranch q L a e)
        [c.val] = true := by
      simp only [grayNodeValidB, List.all_eq_true]
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · simp [c.isLt]
      · simp at hd
    have hforeign : grayNodeForeignB p.slots i.val [c.val] = true := by
      rw [grayNodeForeignB, List.all_eq_true]
      intro s hs
      rw [Bool.or_eq_true]
      by_cases htree : i.val = s.1.val
      · right
        rw [Bool.not_eq_true', decide_eq_false_iff_not]
        intro hcmp2
        have hlen1 : ([c.val] : GacsDayNode).length = 1 := rfl
        have hlen2 : (grayTailSlotNode s).length = 2 := by
          simp [grayTailSlotNode]
        rcases hcmp2 with h | h
        · obtain ⟨tl, htl⟩ := h
          have hc2 : c.val = s.2.1.val := by
            have hhead := congrArg (fun l => l.head?) htl
            simpa [grayTailSlotNode] using hhead
          have := hspare s hs
          omega
        · have := h.length_le
          simp [grayTailSlotNode] at this
      · left
        exact decide_eq_true htree
    exact mem_grayHarvest_of_getAlloc i.isLt hvalidNode hforeign hv
  apply hfresh
  refine ⟨v.take p.fineEnd, ?_, ?_⟩
  · rw [hchain]
    exact List.mem_append_right _ hu
  · have hzlen' : z.2.length = p.fineEnd := by
      rw [hzlen, hfineEq]
    rcases hzv with h | h
    · by_cases hlv : v.length <= p.fineEnd
      · have : v.take p.fineEnd = v := List.take_of_length_le hlv
        rw [this]
        exact Or.inl h
      · have hzt : z.2 <+: v.take p.fineEnd := by
          have h1 : (v.take p.fineEnd).take z.2.length =
              v.take z.2.length := by
            rw [List.take_take, min_eq_left (by omega)]
          have h2 : v.take z.2.length = z.2 := by
            obtain ⟨tl, htl⟩ := h
            rw [← htl, List.take_left]
          rw [← h2, ← h1]
          exact List.take_prefix _ _
        exact Or.inl hzt
    · have hvlen : v.length <= p.fineEnd := by
        have := h.length_le
        omega
      have : v.take p.fineEnd = v := List.take_of_length_le hvlen
      rw [this]
      exact Or.inr h

/-- **Spend rounds with an early reserve never meet the complement.** -/
theorem grayChargedV2_spendRound_transported_ne_complement
    {q L a e n t t0 tau : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hleg : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hchain : p.unavailable =
      A ++ grayHarvest p.fineEnd p.slots n (sm t0))
    (hspare : forall s, s ∈ p.slots ->
      grayChargedSourceCount a e <= s.2.1.val)
    (hfineE : p.fineEnd <= e)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)}
    (hcsrc : c.val < grayChargedSourceCount a e)
    {R : BitString} (htau : tau <= t0)
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val
      (sm tau) [c.val] R)
    (hRlen : R.length = e)
    {tagOwner root iC : Nat} {owner : FamilyGrayCharge}
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      tagOwner root (grayChargedRoundLocalChargeV2 hae p hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 iC
      (e + grayTailNewLoss q L) R owner) :
    w.2 ≠ y.2 := by
  refine grayChargedV2_transported_cell_ne_complement_of_incomparable hae
    p hp hw hy ?_
  intro u huR
  exact grayChargedV2_spendCell_early_reserve_incomparable hleg hae hp
    hchain hspare hfineE hcsrc htau hR hRlen
    (mem_grayChargeAtRoot.mp huR).1

/-- **Non-owner rounds are wholly excluded**: any transported cell of an
advantage-terminal round other than the owner never equals any complement
cell of the datum's reserve. -/
theorem grayChargedV2_nonOwnerRound_transported_ne_complement
    {q L a e n T t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {tR : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z tR R k)
    (kk : Fin replay.advantageTerminal.frozen.length) (hkk : kk.val ≠ k)
    (hp : replay.advantageTerminal.frozen[kk.val] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen)
    {tagOwner root : Nat} {owner : FamilyGrayCharge} {i : Nat}
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      tagOwner root (grayChargedRoundLocalChargeV2 hae
        (replay.advantageTerminal.frozen[kk.val]) hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 i
      (e + grayTailNewLoss q L) R owner) :
    w.2 ≠ y.2 := by
  refine grayChargedV2_transported_cell_ne_complement_of_incomparable hae
    _ hp hw hy ?_
  intro u huR
  exact grayChargedV2_datum_advCell_incomparable hae replay hdata kk hp
    (mem_grayChargeAtRoot.mp huR).1 (Or.inl hkk)

/-- **The owner round is excluded slot by slot**: fibre slots die on the
complement filter, foreign slots on the datum freshness. -/
theorem grayChargedV2_ownerRound_transported_ne_complement
    {q L a e n T t t' : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {tR : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z tR R k)
    (hk : k < replay.advantageTerminal.frozen.length)
    (hp : replay.advantageTerminal.frozen[k] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen)
    (hp' : replay.advantageTerminal.frozen[k] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t').core.frozen)
    (j : Fin (replay.advantageTerminal.frozen[k]).slots.length)
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      (((replay.advantageTerminal.frozen[k]).slots.get j).1.val) j.val
      (grayChargedRoundLocalChargeV2 hae
        (replay.advantageTerminal.frozen[k]) hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 z.1.val
      (e + grayTailNewLoss q L) R
      (grayChargedOwnerFibreV2 hae
        (replay.advantageTerminal.frozen[k]) hp' z)) :
    w.2 ≠ y.2 := by
  by_cases hfib :
      ((replay.advantageTerminal.frozen[k]).slots.get j).1 = z.1 ∧
        ((replay.advantageTerminal.frozen[k]).slots.get j).2.1 = z.2
  · exact grayChargedV2_transported_ownerCell_ne_complement hae _ hp hp'
      z j hfib hw hy
  · refine grayChargedV2_transported_cell_ne_complement_of_incomparable
      hae _ hp hw hy ?_
    intro u huR
    have hu1 : u.1 = j.val := (mem_grayChargeAtRoot.mp huR).2
    refine grayChargedV2_datum_advCell_incomparable hae replay hdata
      ⟨k, hk⟩ hp (mem_grayChargeAtRoot.mp huR).1 (Or.inr ?_)
    intro hlt
    rw [show (⟨u.1, hlt⟩ : Fin _) = j from Fin.ext hu1]
    exact hfib

end Kolmogorov
