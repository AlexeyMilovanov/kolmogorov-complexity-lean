import KolmogorovMathlib.MonotoneComplexity.GacsDayV2CanonicalScheme
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRung

/-!
# The base of the pinned ladder

The pinned tail step `pinnedChargedRung_tail_step` needs a first rung.  The
V1 stage-two rung `chargedGrayRung_two_four` (witness forcing, universal in
the anchor) supplies it.  Read on the diagonal (anchor = scale `a`, export `a + 3 = a +
grayFootprint 2`), it is a pinned rung at stage two; the tail step's proof
uses `3 ≤ q` only through `grayFootprint_bridge (j := q + 1)`, which needs
`2 ≤ q`, so one application of the (relaxed) tail step at `q = 2` produces
the pinned stage-three rung `pinnedChargedRung_three`.  The nesting identity
`graySpendSpan_add_childLoss` (which fails at `j = 3`) is not consumed by the
tail step: the device layer only needs `grayFootprint (q - 1) ≤ L` and the
child export `ε + L`.

With the base, the canonical V2 ladder `canonicalGraySchemeV2` is a pinned
rung at every stage `q ≥ 3` (`pinnedChargedRung_canonicalPinned`) and jointly
computable (`canonicalPinnedScheme_computable`), both axiom-clean.
-/

namespace Kolmogorov

/-- The stage-two scheme re-based to the diagonal: it ignores the pinned
bin-scale argument and plays at its own anchor `a`, exporting `a + 3`. -/
def stageTwoDiagScheme : FamilyStrategyScheme :=
  fun a _e => stageTwoFamilyStrategy a (a + 3)

/-- **The pinned rung at stage two**, from the universal stage-two
rung read at the anchor `a`. -/
theorem pinnedChargedRung_two : PinnedChargedRung 4 2 stageTwoDiagScheme := by
  intro a ha n A hn
  have hB : 2 ≤ grayTailBaseBranch 1 (grayFootprint 1) := le_max_left _ _
  have h := chargedGrayRung_two_four (grayTailBaseBranch 1 (grayFootprint 1)) hB
    a a ha le_rfl n A hn
  have hbb : ladderBranching (grayTailBaseBranch 1 (grayFootprint 1)) a a ≤
      ladderBranching (grayTailBaseBranch 1 (grayFootprint 1)) a
        (a + 8 * grayFootprint 1 + 3) := by
    simp only [ladderBranching]
    refine max_le_max ?_ le_rfl
    have hexp : a - a ≤ a + 8 * grayFootprint 1 + 3 - a := by omega
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hexp)
  exact h.mono_branching hbb

/-- `pinnedChargedRung_tail_step_of_devices` with `hq` relaxed to `2 ≤ q`
(the proof only uses `grayFootprint_bridge (j := q + 1)`). -/
theorem pinnedChargedRung_tail_step_of_devices_two
    {q : Nat} {sigma : FamilyStrategyScheme} (hq : 2 ≤ q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hfields : ∀ a n A, 1 ≤ a → 1 ≤ n →
      GrayChargedOuterFieldsV2 q (grayFootprint q) a
        (a + 8 * grayFootprint q + 3) n sigma A) :
    PinnedChargedRung 4 (q + 1)
      (fun a e => grayChargedStrategyV2 q (grayFootprint q) a e sigma) := by
  intro a ha n A hn
  have hspec := grayChargedStrategyV2_chargedGameSpec
    ha hn hRung (hfields a n A ha hn)
  have hbridge :
      (a + 8 * grayFootprint q + 3) + grayTailNewLoss q (grayFootprint q) =
        a + grayFootprint (q + 1) := by
    have hb := grayFootprint_bridge (j := q + 1) (a := a) (by omega)
    simpa using hb
  simp only [Nat.add_sub_cancel]
  rw [← hbridge]
  exact hspec

/-- The stage-three scheme `grayChargedStrategyV2 2 (grayFootprint 2) a e stageTwoDiagScheme`: the
V2 block controller at stage `2` run over the diagonal stage-two scheme. -/
def stageThreeSchemeV2 : FamilyStrategyScheme :=
  fun a e => grayChargedStrategyV2 2 (grayFootprint 2) a e stageTwoDiagScheme

/-- **E1: the pinned base rung at stage three** (axiom-clean). -/
theorem pinnedChargedRung_three : PinnedChargedRung 4 3 stageThreeSchemeV2 :=
  pinnedChargedRung_tail_step_of_devices_two (q := 2) (by omega) pinnedChargedRung_two
    (fun a n A ha hn =>
      grayChargedOuterFieldsV2_of_legal ha (by omega) rfl pinnedChargedRung_two
        (grayChargedLegalV2_of_rung ha pinnedChargedRung_two))

/-- The diagonal stage-two scheme is computable. -/
theorem computable_stageTwoDiagScheme :
    FamilyStrategySchemeComputable stageTwoDiagScheme := by
  have hre : Computable
      (fun p : (Nat × Nat) × (Allocation × (Nat × FamilyGameHistory)) =>
        (((p.1.1, p.1.1) : Nat × Nat), p.2)) :=
    ((Computable.fst.comp Computable.fst).pair
      (Computable.fst.comp Computable.fst)).pair Computable.snd
  exact (computable_stageTwoFamilyScheme.comp hre).of_eq (fun p => rfl)

/-- **E1, computability half**: the stage-three scheme has a code. -/
theorem exists_code_stageThreeV2 :
    ∃ code3 : Nat.Partrec.Code, CodeComputesScheme code3 stageThreeSchemeV2 := by
  obtain ⟨c2, hc2⟩ :=
    exists_code_of_familyStrategySchemeComputable computable_stageTwoDiagScheme
  obtain ⟨G, _hGcomp, hG⟩ := grayChargedV2_exists_code_step
  exact ⟨G 2 (grayFootprint 2) c2, hG 2 (grayFootprint 2) c2 _ hc2⟩

/-- The uniform family strategy scheme `canonicalGraySchemeV2 stageThreeSchemeV2`: the canonical
gray ladder of `canonicalGraySchemeV2` taken over the stage-three scheme as its base. -/
def canonicalPinnedScheme : UniformFamilyStrategyScheme :=
  canonicalGraySchemeV2 stageThreeSchemeV2

/-- Every stage `q ≥ 3` of the canonical pinned ladder is a pinned rung
(axiom-clean, no named obligation). -/
theorem pinnedChargedRung_canonicalPinned :
    ∀ q, 3 ≤ q → PinnedChargedRung 4 q (canonicalPinnedScheme q) :=
  pinnedChargedRung_canonicalV2 stageThreeSchemeV2 pinnedChargedRung_three

/-- The canonical pinned ladder is jointly computable. -/
theorem canonicalPinnedScheme_computable :
    UniformFamilyStrategySchemeComputable canonicalPinnedScheme := by
  obtain ⟨code3, hcode3⟩ := exists_code_stageThreeV2
  exact canonicalGraySchemeV2_computable stageThreeSchemeV2 code3 hcode3

end Kolmogorov
