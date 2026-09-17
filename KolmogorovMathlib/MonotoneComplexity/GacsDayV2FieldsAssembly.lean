import KolmogorovMathlib.MonotoneComplexity.GacsDayV2PinnedTailStep
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Minimum

/-!
# The V2 outer fields, assembled modulo `legal`

Three of the four outer fields of `GrayFamilyGameSpec` are theorems for the V2
charged strategy (`range_supported`, `tree_supported` in
`GacsDayV2OuterSupport`, `minimum_request` in `GacsDayV2OuterMinimum`); the
fourth, `legal` (`requestCoherentCap` + time-monotone requests), is the named
obligation `GrayChargedLegalV2`, discharged in `GacsDayV2OuterMonotonicity`.
The pinned tail step then depends on `GrayChargedLegalV2` alone.
-/

namespace Kolmogorov

/-- Against every legal server play on the branch `grayTailBranch q L a e`, the play of the V2
charged strategy is a legal client play at the outer scale `dyadicScale a`. -/
def GrayChargedLegalV2 (q L a e n : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) : Prop :=
  forall sm, familyServerPlayLegal n (grayTailBranch q L a e) A sm ->
    familyClientPlayLegal n (grayTailBranch q L a e) (dyadicScale a)
      (playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm)

/-- The outer fields from the three proved ones and the legality obligation. -/
theorem grayChargedOuterFieldsV2_of_legal
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 <= a) (hae : a <= e) (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hlegal : GrayChargedLegalV2 q L a e n sigma A) :
    GrayChargedOuterFieldsV2 q L a e n sigma A where
  legal := hlegal
  minimum_request := fun sm hsm t =>
    grayChargedStrategyV2_avoidsSmall ha hae hL hRung sm hsm t
  range_supported := grayChargedStrategyV2_rangeSupported hL hRung
  tree_supported := grayChargedStrategyV2_treeSupported hL hRung

/-- **The pinned tail step modulo `legal`.** -/
theorem pinnedChargedRung_tail_step_of_legal
    {q : Nat} {sigma : FamilyStrategyScheme} (hq : 3 <= q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hlegal : forall a n A, 1 <= a -> 1 <= n ->
      GrayChargedLegalV2 q (grayFootprint q) a (a + 8 * grayFootprint q + 3) n sigma A) :
    PinnedChargedRung 4 (q + 1)
      (fun a e => grayChargedStrategyV2 q (grayFootprint q) a e sigma) :=
  pinnedChargedRung_tail_step_of_devices hq hRung
    (fun a n A ha hn =>
      grayChargedOuterFieldsV2_of_legal ha (by omega) rfl hRung (hlegal a n A ha hn))

end Kolmogorov
