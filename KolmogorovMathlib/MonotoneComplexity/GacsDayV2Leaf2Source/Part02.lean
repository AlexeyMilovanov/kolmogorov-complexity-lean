import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Corner
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Hereditary
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Source.Part01

/-!
# The hereditary subfamily bound for the composed charge

`grayChargedV2_l5subfamily_of_family` upgrades the pointwise bound of the previous part to the
hereditary subfamily bound for the composed charge: given the family hypotheses, the inequality
holds for every subfamily of roots at once. This is the last obligation of the composed-charge
argument.
-/

namespace Kolmogorov

/-- **Leaf 2 (D4), the hereditary subfamily bound for the composed charge**,
given the source subfamily bound `hS` (with source ledger requests `PI`, `P`)
and the raised-remainder cap `hEbound`.  Assembles per `I` via the pointwise
`(S)+(R_I) ⟹ H4` route.  This is `GrayChargedL5SubfamilyV2` for
`F = source ++ reserve`. -/
theorem grayChargedV2_l5subfamily_of_family
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hU : T + 1 <= U)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hcoverBack : ∀ r, r ∈ reserves -> r.coordinate ∈
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay)
    (hcover : ∀ z, z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      ∃ r, r ∈ reserves ∧ r.coordinate = z)
    (hcoordNodup : (reserves.map (fun r => r.coordinate)).Nodup)
    (hunit : ∀ r, r ∈ reserves ->
      5 * dyadicScale e / 6 <=
        grayChargeMass (e + grayTailNewLoss q L) r.cells)
    (hmove : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T)
    (PI : List Nat -> Rat) (P : Rat)
    (hS : ∀ I, I ∈ (List.range n).sublists ->
      halfAmplification q *
          (2 * PI I - P) <=
        grayChargeMass (e + grayTailNewLoss q L)
          ((grayChargedSourceChargeV2
            (grayChargedFrozenSourcesV2 hsm replay hU hae)).filter
            fun z => decide (z.1 ∈ I)))
    (hEbound : ∀ I, I ∈ (List.range n).sublists ->
      2 * (totalRootRequestOnList I
            (grayChargedRunMoveV2 q L a e n sigma A sm U) - PI I) -
          (totalRootRequest n
            (grayChargedRunMoveV2 q L a e n sigma A sm U) - P) <=
        ((reserves.countP
          (fun r => decide (r.coordinate.1.val ∈ I)) : Nat) : Rat) *
          (dyadicScale e / (6 * halfAmplification q))) :
    GrayChargedL5SubfamilyV2 q L e n
      (grayChargedRunMoveV2 q L a e n sigma A sm U)
      (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay hU hae) ++
        grayChargedReserveChargeV2 reserves) := by
  intro I hI
  have hIsub : I.Sublist (List.range n) := List.mem_sublists.mp hI
  have hInodup : I.Nodup := List.nodup_range.sublist hIsub
  have hIlt : ∀ x, x ∈ I -> x < n :=
    fun x hx => List.mem_range.mp (hIsub.subset hx)
  have hR := grayChargedV2_leaf2_reserve_deficit hpin hae replay reserves
    hcoverBack hcover hcoordNodup hunit hmove I hInodup hIlt (PI I) P
    (hEbound I hI)
  exact grayChargedV2_l5subfamily_pointwise
    (grayChargedRunMoveV2 q L a e n sigma A sm U)
    (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay hU hae))
    (grayChargedReserveChargeV2 reserves) I (by ring) (by ring)
    (hS I hI) hR

end Kolmogorov
