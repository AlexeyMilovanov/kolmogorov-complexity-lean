import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AdvantageCore
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendCore

/-!
# The pinned V2 device from the pinned rung

`grayChargedV2_remaining_devices_pinned` with the two finalization
facts discharged from the pinned child rung (O3 by
`grayChargedV2_advantageLeaves_of_rung`, O2 by
`grayChargedV2_spendProgress_of_rung`).  No named obligation remains: the
anchored exit datum `hSRanch` of v14 is retired (proof document v15.1).
-/

namespace Kolmogorov

/-- **The pinned V2 device**: at the pinned gap `e = a + 8 * fp q + 3` with
`L = fp q` (both written out in the statement), for every legal server the V2
client wins the positive game or the charged gray goal at the call's anchor
`a` holds at some late time. -/
theorem grayChargedV2_remaining_devices_of_rung
    {q a n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 <= a) (hn : 1 <= n)
    (hRung : PinnedChargedRung 4 q sigma)
    (sm : Nat -> FamilyServerMove)
    (hsm : familyServerPlayLegal n
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) A sm) :
    GrayChargedPositiveV2 q (grayFootprint q) a (a + 8 * grayFootprint q + 3)
        n sigma A sm ∨
      exists U, familyChargedGrayGoalAtB 4 (halfAmplification (q + 1))
        (dyadicScale a) ((3 / 4 : Rat) * dyadicScale a) a
        (a + 8 * grayFootprint q + 3 + grayTailNewLoss q (grayFootprint q)) n A
        (grayChargedRunMoveV2 q (grayFootprint q) a (a + 8 * grayFootprint q + 3)
          n sigma A sm U) (sm U) = true := by
  have hae : a <= a + 8 * grayFootprint q + 3 := by omega
  exact grayChargedV2_remaining_devices_pinned rfl hae sm hsm
    (grayChargedV2_advantageLeaves_of_rung ha hae hn rfl hRung hsm)
    (grayChargedV2_spendProgress_of_rung rfl hRung hsm)

end Kolmogorov
