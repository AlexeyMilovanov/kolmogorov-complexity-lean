import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Provenance

/-!
# The two L5 leaves (Stage D, remaining geometry)

The precise named statements the conditional assembly consumes, and the
first fully-proved component of leaf 1: a spend round's designated cells
avoid the cylinder of every reserve already present at the round's snapshot
— the snapshot harvest carries the reserve's witness into the round's
unavailable list, and the round's gray freshness excludes it (§4.3(res)).
-/

namespace Kolmogorov

/-- The physical cells of the transported source charge of `replay` and those of the reserve charge
of `reserves` are disjoint lists. -/
def GrayChargedL5DisjointV2
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) : Prop :=
  List.Disjoint
    ((grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
      hU hae)).map Prod.snd)
    ((grayChargedReserveChargeV2 reserves).map Prod.snd)

/-- For every sublist `I` of `List.range n`, the amplified defect of the client move on `I`,
`halfAmplification (q + 1) * (2 * totalRootRequestOnList I move - totalRootRequest n move)`
(truncated subtraction), is at most the charge mass
`grayChargeMass (e + grayTailNewLoss q L) (F.filter fun z => decide (z.1 ∈ I))` of the part of
`F` supported on `I`. -/
def GrayChargedL5SubfamilyV2 (q L e n : Nat)
    (move : FamilyClientMove) (F : FamilyGrayCharge) : Prop :=
  forall I, I ∈ (List.range n).sublists ->
    halfAmplification (q + 1) *
        (2 * totalRootRequestOnList I move - totalRootRequest n move) <=
      grayChargeMass (e + grayTailNewLoss q L) (F.filter fun z =>
        decide (z.1 ∈ I))

/-- **The proved component of leaf 1** (§4.3(res)): a designated cell of a
spend round is prefix-incomparable with every reserve that already exists at
the round's snapshot move, because the snapshot harvest carries the
reserve's allocated witness into the round's unavailable list. -/
theorem grayChargedV2_spendCell_snapshot_reserve_incomparable
    {q L a e n t t0 : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
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
    {R : BitString}
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val
      (sm t0) [c.val] R)
    (hRlen : R.length = e)
    {z : Nat × BitString}
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  intro hcmp
  have hcells := grayChargedRoundLocalChargeV2_cells hae p hp z hz
  obtain ⟨hzlen, -, hfresh⟩ := mem_newGrayCellsList.mp hcells.2
  have hfineEq : p.fineEnd = p.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
  -- the reserve's allocated witness at the son node
  obtain ⟨v, hv, hRv⟩ := hR.1.2.1
  -- the round's fine cells never extend the coarser reserve properly:
  -- lengths force `z.2 ≺ R`
  have hzR2 : z.2 <+: R := by
    rcases hcmp with h | h
    · exact h
    · have hle := h.length_le
      have heq : R = z.2 := h.eq_of_length (by omega)
      rw [heq]
  have hzv : z.2 <+: v ∨ v <+: z.2 := by
    rcases hRv with h2 | h2
    · exact Or.inl (hzR2.trans h2)
    · rcases List.prefix_or_prefix_of_prefix h2 hzR2 with h3 | h3
      · exact Or.inr h3
      · exact Or.inl h3
  -- the harvested truncation of the witness
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

end Kolmogorov
