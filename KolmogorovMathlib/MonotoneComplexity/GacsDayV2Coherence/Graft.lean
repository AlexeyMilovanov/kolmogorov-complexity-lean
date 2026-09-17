import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Minimum
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Coherence.Part01

namespace Kolmogorov

/-! ### The graft -/

/-- **Coherence of the two-level graft** from the coherence of its entries,
the source son-base cap and the root cap. -/
lemma grayChargedTailFamilyMove_coherentCap {n b : ℕ} {source : ℕ}
    {threshold eps alpha : ℚ}
    {frozen : GrayTailFrozen n b} {slots : List (GrayTailSlot n b)}
    {current : FamilyClientMove}
    (heps : 0 ≤ eps)
    (hnonneg : ∀ pr ∈ grayTailEntries frozen slots current, ∀ x, 0 ≤ getReq pr.2 x)
    (hchild : ∀ pr ∈ grayTailEntries frozen slots current, ∀ x,
      getReq pr.2 x ≥ ∑ c : Fin b, getReq pr.2 (x ++ [c.val]))
    {i : ℕ} (hi : i < n)
    (hsourceCap : ∀ c : Fin b, c.val < source →
      grayTailSonBase (grayTailEntries frozen slots current) ⟨i, hi⟩ c ≤ eps)
    (hrootcap : grayChargedRootRequest source threshold eps
      (grayTailEntries frozen slots current) ⟨i, hi⟩ ≤ alpha) :
    requestCoherentCap b alpha
      (familyClientMoveAt
        (grayChargedTailFamilyMove source threshold eps frozen slots current) i) := by
  let entries := grayTailEntries frozen slots current
  have hson_nonneg (c : Fin b) :
      0 ≤ grayChargedSonRequest source threshold eps entries ⟨i, hi⟩ c := by
    unfold grayChargedSonRequest
    by_cases hc : c.val < source
    · rw [if_pos hc]
      unfold grayTailSonRequest
      by_cases hlarge : threshold < grayTailSonBase entries ⟨i, hi⟩ c
      · rw [if_pos hlarge]
        exact heps
      · rw [if_neg hlarge]
        exact grayTailSonBase_nonneg_global (fun pr hpr => hnonneg pr hpr [])
    · rw [if_neg hc]
      exact grayTailSonBase_nonneg_global (fun pr hpr => hnonneg pr hpr [])
  have hbase_le_son (c : Fin b) :
      grayTailSonBase entries ⟨i, hi⟩ c ≤
        grayChargedSonRequest source threshold eps entries ⟨i, hi⟩ c := by
    by_cases hc : c.val < source
    · rw [grayChargedSonRequest_source _ _ hc]
      unfold grayTailSonRequest
      by_cases hlarge : threshold < grayTailSonBase entries ⟨i, hi⟩ c
      · rw [if_pos hlarge]
        exact hsourceCap c hc
      · rw [if_neg hlarge]
    · rw [grayChargedSonRequest_spare _ _ (Nat.le_of_not_gt hc)]
  unfold grayChargedTailFamilyMove familyClientMoveAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos hi]
  refine requestCoherentCap_graftTwoLevel ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold grayChargedRootRequest
    exact Finset.sum_nonneg fun c _ => hson_nonneg c
  · exact hrootcap
  · intro c hc
    rw [dif_pos hc]
    exact hson_nonneg ⟨c, hc⟩
  · have hsum_eq :
        (∑ c : Fin b, if hc : c.val < b then
          grayChargedSonRequest source threshold eps entries ⟨i, hi⟩ ⟨c.val, hc⟩ else 0) =
        ∑ c : Fin b, grayChargedSonRequest source threshold eps entries ⟨i, hi⟩ c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dif_pos c.isLt]
    rw [hsum_eq]
    exact le_rfl
  · intro c hc
    rw [dif_pos hc]
    have hsum := (sum_grayChargedEntryMove_root_le_sonBase entries hnonneg ⟨i, hi⟩
      ⟨c, hc⟩).trans (hbase_le_son ⟨c, hc⟩)
    refine le_trans (le_of_eq ?_) hsum
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [dif_pos hc, dif_pos c'.isLt]
  · intro c hc c' hc' x
    rw [dif_pos hc, dif_pos hc']
    exact grayChargedEntryMove_nonneg entries hnonneg (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) x
  · intro c hc c' hc' x
    rw [dif_pos hc, dif_pos hc']
    exact grayChargedEntryMove_child_le entries hchild (⟨i, hi⟩, ⟨c, hc⟩, ⟨c', hc'⟩) x

/-! ### The coherence field -/

/-- **Coherence of the V2 charged outer strategy at the pinned gap, given the
root cap**: at `L = grayFootprint q`, `e = a + 8 * L + 3` (both written out in
the statement) every displayed root is `requestCoherentCap`-capped at
`dyadicScale a` as soon as its charged root request is (the non-negativity and
the child-sum coherence are unconditional).  The displayed slots are the
active slots, none on a done core. -/
theorem grayChargedV2_output_coherentCap_of_rootCap
    {q a n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) A sm)
    (i : ℕ) (hi : i < n)
    (hroot : grayChargedRootRequest
      (grayChargedSourceCount a (a + 8 * grayFootprint q + 3))
      (grayChargedThreshold q (a + 8 * grayFootprint q + 3))
      (dyadicScale (a + 8 * grayFootprint q + 3))
      (grayTailEntries
        ((grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t).core.frozen.map
            GrayTailRoundV2.toV1)
        (if (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t).core.done then []
        else (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
          q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t).core.slots)
        (grayChargedCurrentMoveV2 q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma
          (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
            q (grayFootprint q) a (a + 8 * grayFootprint q + 3) sigma A sm t)))
        ⟨i, hi⟩ ≤ dyadicScale a) :
    requestCoherentCap
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
      (dyadicScale a)
      (familyClientMoveAt
        (playClientFamily A n (grayChargedStrategyV2 q (grayFootprint q) a
          (a + 8 * grayFootprint q + 3) sigma) sm t) i) := by
  obtain ⟨L, hL⟩ : ∃ L, L = grayFootprint q := ⟨grayFootprint q, rfl⟩
  rw [← hL] at hsm hroot ⊢
  set e := a + 8 * L + 3 with hpin
  have hae : a ≤ e := by rw [hpin]; omega
  rw [playClientFamily_grayChargedStrategyV2, grayChargedDisplayedMoveV2_eq_current]
  have hcoh := grayChargedRunStateV2_entries_coherent (t := t) ha hae hL hRung hsm
  have hsourceCap := fun (c : Fin (grayTailBranch q L a e))
      (hc : c.val < grayChargedSourceCount a e) =>
    grayChargedRunStateV2_display_sonBase_le (t := t) ha hae hL hRung hsm ⟨i, hi⟩ c hc
  generalize grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcoh hsourceCap hroot ⊢
  exact grayChargedTailFamilyMove_coherentCap (dyadicScale_pos e).le
    (fun pr hpr x => (hcoh pr hpr).1 x) (fun pr hpr x => (hcoh pr hpr).2.2 x) hi
    hsourceCap hroot

/-- **The coherence field of the V2 charged outer strategy** at the pinned gap
`L = grayFootprint q`, `e = a + 8 * L + 3` (both written out in the statement):
at every time, every root of the displayed outer move is
`requestCoherentCap`-capped at the outer scale `dyadicScale a`. -/
theorem grayChargedV2_output_coherentCap
    {q a n t : ℕ} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3)) A sm)
    (i : ℕ) (hi : i < n) :
    requestCoherentCap
      (grayTailBranch q (grayFootprint q) a (a + 8 * grayFootprint q + 3))
      (dyadicScale a)
      (familyClientMoveAt
        (playClientFamily A n (grayChargedStrategyV2 q (grayFootprint q) a
          (a + 8 * grayFootprint q + 3) sigma) sm t) i) :=
  grayChargedV2_output_coherentCap_of_rootCap ha hRung hsm i hi
    (grayChargedRunStateV2_display_root_cap (t := t) ha hRung hsm ⟨i, hi⟩)

end Kolmogorov


