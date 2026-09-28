import KolmogorovMathlib.MonotoneComplexity.GacsDayV2PinnedDevice

/-!
# The pinned tail step of the V2 block controller, modulo the outer fields

Blueprint A4: `3 ≤ j → PinnedChargedRung 4 j sigma → PinnedChargedRung 4 (j+1)
(fun a e => grayChargedStrategyV2 j (fp j) a e sigma)`.  The `wins_charged`
conjunct is the pinned device `grayChargedV2_remaining_devices_of_rung`, whose
charged goal is certified at the call's anchor `a` (proof document v15.1,
A2′); the export depth is rewritten by the bridge identity
`grayFootprint_bridge`; the outer fields of `GrayFamilyGameSpec` (`legal`,
`minimum_request`, `range_supported`, `tree_supported`) are carried as the
named obligation `GrayChargedOuterFieldsV2`.
-/

namespace Kolmogorov

/-- The outer fields of the V2 charged strategy: against every legal server play its play is legal
at scale `dyadicScale a` and avoids requests below `2 ^ -(e + grayTailNewLoss q L)`, and the
strategy is range supported on the branch and tree supported at height `2 * (q + 1)`. -/
structure GrayChargedOuterFieldsV2 (q L a e n : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) : Prop where
  legal : forall sm, familyServerPlayLegal n (grayTailBranch q L a e) A sm ->
    familyClientPlayLegal n (grayTailBranch q L a e) (dyadicScale a)
      (playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm)
  minimum_request : forall sm,
    familyServerPlayLegal n (grayTailBranch q L a e) A sm -> forall t,
      familyRequestAvoidsSmall n ((1 / 2 : Rat) ^ (e + grayTailNewLoss q L))
        (playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t)
  range_supported : FamilyRangeSupported n (grayTailBranch q L a e) A
    (grayChargedStrategyV2 q L a e sigma)
  tree_supported : FamilyTreeSupported n (2 * (q + 1)) A
    (grayChargedStrategyV2 q L a e sigma)

/-- **The V2 charged game specification at the pinned gap**, from the pinned
child rung and the outer fields.  The certificate is anchored at the outer
scale `a` (v15.1 A2′): the pinned device produces the charged goal at `a`
directly from validity at `a`. -/
theorem grayChargedStrategyV2_chargedGameSpec
    {q a n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (ha : 1 <= a) (hn : 1 <= n)
    (hRung : PinnedChargedRung 4 q sigma)
    (hfields : GrayChargedOuterFieldsV2 q (grayFootprint q) a
      (a + 8 * grayFootprint q + 3) n sigma A) :
    ChargedGrayFamilyGameSpec 4 (halfAmplification (q + 1))
      (dyadicScale a) ((3 / 4 : Rat) * dyadicScale a)
      a (a + 8 * grayFootprint q + 3 + grayTailNewLoss q (grayFootprint q))
      (2 * (q + 1))
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) n A
      (grayChargedStrategyV2 q (grayFootprint q) a
        (a + 8 * grayFootprint q + 3) sigma) := by
  set L := grayFootprint q with hL
  set e := a + 8 * L + 3 with hpin
  have hae : a <= e := by rw [hpin]; omega
  have hcharged : forall sm,
      familyServerPlayLegal n (grayTailBranch q L a e) A sm ->
      GrayChargedPositiveV2 q L a e n sigma A sm ∨
        familyChargedGrayGoal 4 (halfAmplification (q + 1))
          (dyadicScale a) ((3 / 4 : Rat) * dyadicScale a)
          a (e + grayTailNewLoss q L) n A
          (playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm) sm := by
    intro sm hsm
    rcases grayChargedV2_remaining_devices_of_rung ha hn hRung sm hsm
        with hpos | ⟨U, hU⟩
    · exact Or.inl hpos
    · exact Or.inr ⟨U, hU⟩
  have hscales : a <= e + grayTailNewLoss q L :=
    le_trans hae (Nat.le_add_right e (grayTailNewLoss q L))
  refine { weak := ?_, wins_charged := hcharged }
  refine {
    nonempty := hn
    kappa_ge_one := ?_
    alpha_pos := dyadicScale_pos a
    beta_nonneg := mul_nonneg (by norm_num) (dyadicScale_pos a).le
    scales := hscales
    legal := hfields.legal
    minimum_request := hfields.minimum_request
    wins := ?_
    wins_positively := ?_
    range_supported := hfields.range_supported
    tree_supported := hfields.tree_supported }
  · unfold halfAmplification
    have hq : (0 : Rat) <= ((q + 1 : Nat) : Rat) / 2 := by positivity
    linarith
  · intro sm hsm
    rcases hcharged sm hsm with hwin | hgray
    · exact Or.inl (familyClientWinsUnserved_of_positive _ _ _ _ _ hwin)
    · exact Or.inr (familyChargedGrayGoal.to_familyGrayGoal hscales hgray)
  · intro sm hsm
    rcases hcharged sm hsm with hwin | hgray
    · exact Or.inl hwin
    · exact Or.inr (familyChargedGrayGoal.to_familyGrayGoal hscales hgray)

/-- **The pinned tail step** (blueprint A4), modulo the outer fields at the
pinned gap. -/
theorem pinnedChargedRung_tail_step_of_devices
    {q : Nat} {sigma : FamilyStrategyScheme} (hq : 3 <= q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hfields : forall a n A, 1 <= a -> 1 <= n ->
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

end Kolmogorov
