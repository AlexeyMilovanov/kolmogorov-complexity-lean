import KolmogorovMathlib.MonotoneComplexity.GacsDayV2HarvestKill
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Export
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Sources
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendPhase

/-!
# v15 support: spend-round cells avoid snapshot-present source reserves

The anchoring-free form of leaf 1's spend-vs-frozen-reserve device (blueprint
"v15 implementation spec", step 3): every designated cell of a frozen SPEND
round of the V2 run is prefix-incomparable with any `e`-cylinder comparable
with an allocation at a SOURCE son's node present in the round's snapshot
server move — because the source son is foreign to the pass's spare slots, so
the allocation's `δ`-truncation is harvested into the round's unavailable
list, while the cell (of length `δ ≤ e`) is certified fresh.  The snapshot
identity of the frozen round (`hsnap`) is the invariant the wait phase will
record; here it is a hypothesis.
-/

namespace Kolmogorov

/-- At room `a + 3 + L ≤ e` every spend fine depth is at most `e`. -/
lemma grayChargedSpendDelta_le_e {a L e pass : Nat} (hroom : a + 3 + L <= e) :
    grayChargedSpendDelta a L e pass <= e := by
  have hL : L <= (pass + 1) * L := Nat.le_mul_of_pos_left L (Nat.succ_pos pass)
  unfold grayChargedSpendDelta grayChargedSpendEps grayChargedSpendAlphaDepth
  omega

/-- A source son's node is foreign to every spend slot list. -/
lemma grayNodeForeignB_source_of_spendSlots {n b source L pass i c : Nat}
    {slots : List (GrayTailSlot n b)}
    (hslots : ∀ s ∈ slots, GrayChargedBlockSpendSlotV2 n b source L pass s)
    (hsrc : c < source) :
    grayNodeForeignB slots i [c] = true := by
  unfold grayNodeForeignB
  rw [List.all_eq_true]
  intro s hs
  have hge : source <= s.2.1.val := grayBlockSpendPairs_first_ge (hslots s hs)
  have hne : c ≠ s.2.1.val := by omega
  have hnot : ¬ ([c] <+: grayTailSlotNode s ∨ grayTailSlotNode s <+: [c]) := by
    rintro (h | h)
    · obtain ⟨t, ht⟩ := h
      simp only [grayTailSlotNode, List.singleton_append, List.cons.injEq] at ht
      exact hne ht.1
    · obtain ⟨t, ht⟩ := h
      simp [grayTailSlotNode] at ht
  simp [hnot]

/-- **Spend-round cells avoid snapshot-present source reserves.** -/
theorem grayChargedSpendRoundV2_cell_incomparable_of_snapshot
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (hroom : a + 3 + L <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor)
    {smSnap : FamilyServerMove}
    (hsnap : p.unavailable = A ++ grayHarvest p.fineEnd p.slots n smSnap)
    {i c : Nat} (hi : i < n) (hc : c < grayTailBranch q L a e)
    (hsrc : c < grayChargedSourceCount a e)
    {R d : BitString} (hRlen : R.length = e)
    (hd : d ∈ getFamilyAlloc smSnap i [c]) (hRd : R <+: d ∨ d <+: R)
    (z : Nat × BitString)
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  -- the frozen round is a spend round: its slots are spare pairs
  have hshape := (grayChargedRunStateV2_coreCertified (n := n) q L a e sigma A sm t).round_valid
    p hp
  have hspendSlots : ∃ pass, ∀ s ∈ p.slots,
      GrayChargedBlockSpendSlotV2 n (grayTailBranch q L a e)
        (grayChargedSourceCount a e) L pass s := by
    rcases hshape.2.2.2.2.2 with hadv | ⟨pass, -, -, -, -, hslots, -⟩
    · exfalso
      apply hcoarse
      rw [hadv.1]
      exact grayTailRoundEps_lower q L e p.roundIndex
    · exact ⟨pass, hslots⟩
  obtain ⟨pass0, hslots0⟩ := hspendSlots
  -- the designated cell is a certified new-gray cell of the spend goal
  unfold grayChargedRoundLocalChargeV2 at hz
  rw [dite_eq_right hcoarse] at hz
  have hSp := grayChargedRunStateV2_frozen_spend_goal q L a e sigma A sm t hp hcoarse
  have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid hSp.choose_spec.2.2.2
  have hcell := (familyGrayChargeAtB.cell hvalid hz).2
  have hfineEq : p.fineEnd = grayChargedSpendDelta a L e hSp.choose :=
    hSp.choose_spec.2.2.1
  have hsub : ∀ u ∈ grayHarvest (n := n) (b := grayTailBranch q L a e)
      (grayChargedSpendDelta a L e hSp.choose) p.slots n smSnap, u ∈ p.unavailable := by
    intro u hu
    rw [hsnap, hfineEq]
    exact List.mem_append_right _ hu
  have hR : grayChargedSpendDelta a L e hSp.choose <= R.length := by
    rw [hRlen]
    exact grayChargedSpendDelta_le_e hroom
  have hx : grayNodeValidB (grayTailBranch q L a e) [c] = true := by
    simp [grayNodeValidB, hc]
  have hforeign : grayNodeForeignB p.slots i [c] = true :=
    grayNodeForeignB_source_of_spendSlots hslots0 hsrc
  have hxmem : [c] ∈ (familyServerMoveAt smSnap i).map Prod.fst :=
    grayLookup_mem_fst hd
  exact newGrayCell_incomparable_of_harvest hsub hcell hR hi hx hforeign hxmem hd hRd

end Kolmogorov
