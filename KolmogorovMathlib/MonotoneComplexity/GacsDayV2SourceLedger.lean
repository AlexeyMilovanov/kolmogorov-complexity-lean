import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Chase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ProgressBase
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport

/-!
# The V2 source ledger (Stage D1): transport validity at the block anchors

The block architecture dissolves the R2 re-anchoring cascade: every V2
advantage round's anchor satisfies `e ≤ blockAnchor` (`blockAnchor = ε_r ≥
grayCallDepth q e = e + …`), so the committed fine transport-validity theorem
`grayCharged_frozen_cell_transport_valid` applies VERBATIM through the
`toV1` projection — no shallow-cell case, no re-anchored `cells_valid`.

This module supplies:
* the harvest-chain bridge `grayChargedBlockV2_frozen_chainV1` (the V2
  snapshot chain, projected by `toV1`, is a V1 `GrayTailHarvestChain`);
* the anchor bound `grayChargedBlockV2_frozen_anchor_ge`;
* the **V2 transport validity** `grayChargedBlockCell_transport_valid`.
-/

namespace Kolmogorov

/-- `e` is below the call depth (schedule arithmetic). -/
lemma grayCallDepth_ge (q e : Nat) : e <= grayCallDepth q e := by
  unfold grayCallDepth
  omega

/-- Every frozen V2 round's block anchor is at least `e`. -/
lemma grayChargedBlockV2_frozen_anchor_ge
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen) :
    e <= p.blockAnchor := by
  have hrv := (grayChargedBlockTailCertifiedV2_stateAt (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t).round_valid p hp
  rw [hrv.2.1]
  unfold grayTailRoundEps
  have := grayCallDepth_ge q e
  omega

/-- Every frozen round of the strict block tail keeps the ambient list `A`
in its `unavailable` list (the harvest chain with admissible snapshots,
v15.1 A7). -/
lemma grayChargedBlockV2_frozen_mem_unavailable_of_A
    {n q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen) :
    forall z, z ∈ A -> z ∈ p.unavailable := by
  intro z hz
  obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨s, -, hsnap⟩ := (grayChargedBlockTailCertifiedV2_stateAt (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen_chain k hk
  rw [← hpk, hsnap]
  exact List.mem_append_left _ hz

/-- **Stage D1 / R2 dissolved: V2 transport validity at the block anchor.**
A designated local gray cell of a frozen V2 block round extends to a new gray
cell of the round's outer owner at the common final depth, anchored at `e` —
via the committed fine theorem, verbatim, because `e ≤ blockAnchor`. -/
theorem grayChargedBlockCell_transport_valid
    {n q L a e t U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).frozen)
    (hTU : p.serverTime <= U)
    (j : Fin p.slots.length) {cell w : BitString}
    (hcell : cell ∈ newGrayCellsList p.blockAnchor (p.blockAnchor + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.blockAnchor + L) p.slots
        (sm p.serverTime)) j.val []) p.unavailable)
    (hw : cell.length + w.length = e + grayTailNewLoss q L) :
    (cell ++ w) ∈ newGrayCellsList e (e + grayTailNewLoss q L)
      (getFamilyAlloc (sm U) (p.slots.get j).1.val []) A := by
  have hmemV1 : p.toV1 ∈ frozenV1OfV2 (grayChargedBlockTailStateAtV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t) := by
    rw [frozenV1OfV2]
    exact List.mem_map_of_mem hp
  have hlow : e <= p.toV1.epsDepth :=
    grayChargedBlockV2_frozen_anchor_ge hp
  have hA : forall z, z ∈ A -> z ∈ p.toV1.unavailable := fun z hz =>
    grayChargedBlockV2_frozen_mem_unavailable_of_A hp z hz
  exact grayCharged_frozen_cell_transport_valid_of_A hsm hA hlow hTU j hcell hw

end Kolmogorov
