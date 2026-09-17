import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendKill
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveBackward

/-!
# v15 support: spend-round cells avoid reserves witnessed before the snapshot

Time transport of the snapshot kill: a family tail reserve `R` at a source
son observed at an EARLIER time (the advantage exit, or the service time of a
raised son that precedes the pass's snapshot) is comparable with an allocation
present at the snapshot time (`allocationSubset_mono_time`), so the
snapshot kill applies — the spend round's designated cells avoid `cyl(R)`.
-/

namespace Kolmogorov

/-- A cylinder comparable with an allocation at time `t₀` is comparable with
an allocation at any later time `t₁` (the earlier cylinder lies in a later
one). -/
lemma comparable_alloc_mono_time {n b t₀ t₁ i : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {x : GacsDayNode} {R d : BitString}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n) (ht : t₀ <= t₁)
    (hd : d ∈ getFamilyAlloc (sm t₀) i x) (hRd : R <+: d ∨ d <+: R) :
    ∃ d' ∈ getFamilyAlloc (sm t₁) i x, R <+: d' ∨ d' <+: R := by
  obtain ⟨d', hd', hdd⟩ :=
    allocationSubset_mono_time (hsm.1 i hi) ht x d hd
  exact ⟨d', hd', prefixComparable_of_common_extension hRd hdd⟩

/-- **Spend-round cells avoid reserves witnessed before the snapshot.** -/
theorem grayChargedSpendRoundV2_cell_incomparable_of_earlier_reserve
    {q L a e n t t₀ t₁ : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hroom : a + 3 + L <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor)
    (hsnap : p.unavailable = A ++ grayHarvest p.fineEnd p.slots n (sm t₁))
    (ht : t₀ <= t₁)
    {i c : Nat} (hi : i < n) (hc : c < grayTailBranch q L a e)
    (hsrc : c < grayChargedSourceCount a e)
    {R : BitString}
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n i (sm t₀) [c] R)
    (z : Nat × BitString)
    (hz : z ∈ grayChargedRoundLocalChargeV2 hae p hp) :
    ¬ (z.2 <+: R ∨ R <+: z.2) := by
  obtain ⟨hRlen, ⟨d, hd, hRd⟩, -, -⟩ := hR.1
  obtain ⟨d', hd', hRd'⟩ := comparable_alloc_mono_time hsm hi ht hd hRd
  exact grayChargedSpendRoundV2_cell_incomparable_of_snapshot hae hroom p hp hcoarse
    hsnap hi hc hsrc hRlen hd' hRd' z hz

end Kolmogorov
