import KolmogorovMathlib.MonotoneComplexity.GacsDayV2AllReduced
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Corner
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2PerRoot
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2DisjointAssembly

/-!
# The reduced corner (Phase 2C wiring)

H3 re-derived for complement reserves: the all-reduced scalar replaces the
full-cylinder mass equation, so `5ε/6` per resolved coordinate suffices —
one source may pay both the owner overlap and the raise remainder.
-/

namespace Kolmogorov

/-! ### Abbreviations for the frozen ledger of the charged run -/

/-- The frozen rounds of the V2 charged run at time `t`, on the tail branch
`grayTailBranch q L a e`. -/
abbrev grayChargedRunFrozenV2 (n q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    List (GrayTailRoundV2 n (grayTailBranch q L a e)) :=
  (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t).core.frozen

/-- The frozen entry table, in V1 form, of the V2 charged run at time `t`. -/
abbrev grayChargedRunFrozenEntriesV2 (n q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) :
    List (GrayTailSlot n (grayTailBranch q L a e) × ClientMove) :=
  grayTailFrozenEntries
    ((grayChargedRunFrozenV2 n q L a e sigma A sm t).map GrayTailRoundV2.toV1)

/-- The total root request displayed by the frozen rounds of the charged run at time `t`:
one `totalRootRequest` per frozen round, over the roots that round holds. -/
abbrev grayChargedRoundsRequestV2 (n q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) : Rat :=
  ∑ k : Fin (grayChargedRunFrozenV2 n q L a e sigma A sm t).length,
    totalRootRequest
      (((grayChargedRunFrozenV2 n q L a e sigma A sm t)[k.val]).slots.length)
      (((grayChargedRunFrozenV2 n q L a e sigma A sm t)[k.val]).move)

/-- The part of `grayChargedRoundsRequestV2` carried by the roots listed in `I`: each frozen
round contributes only the slots whose owner is in `I`. -/
abbrev grayChargedRoundsRequestOnListV2 (n q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) (I : List Nat) : Rat :=
  ∑ k : Fin (grayChargedRunFrozenV2 n q L a e sigma A sm t).length,
    totalRootRequestOnList
      (((List.finRange
        (((grayChargedRunFrozenV2 n q L a e sigma A sm t)[k.val]).slots.length)).filter
        (fun j => decide
          ((((grayChargedRunFrozenV2 n q L a e sigma A sm t)[k.val]).slots.get
            j).1.val ∈ I))).map Fin.val)
      (((grayChargedRunFrozenV2 n q L a e sigma A sm t)[k.val]).move)

/-- The total *raised remainder* over the roots of `S`: for every source son whose frozen base
already exceeds the charged threshold, the gap `dyadicScale e` minus that base. -/
abbrev grayChargedRaisedRemainderOnV2 (n q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat) (S : Finset (Fin n)) : Rat :=
  ∑ i ∈ S, ∑ c : Fin (grayTailBranch q L a e),
    if c.val < grayChargedSourceCount a e ∧
        grayChargedThreshold q e <
          grayTailSonBase (grayChargedRunFrozenEntriesV2 n q L a e sigma A sm t) i c
    then dyadicScale e -
      grayTailSonBase (grayChargedRunFrozenEntriesV2 n q L a e sigma A sm t) i c
    else 0

/-- The coarse budget identity `m · ε = n · α`. -/
private lemma grayChargedV2_budget_eq
    (n a e : Nat) (hae : a <= e) :
    ((n * grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e =
      (n : Rat) * dyadicScale a := by
  have h1 := grayCharged_dyadic_pow_convert a e hae
  rw [grayChargedSourceCount, Nat.cast_mul, mul_assoc, h1]

/-- The total root request at the done time is upper bounded by `n · α`. -/
private lemma grayChargedV2_done_display_upper
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) <=
      (n : Rat) * dyadicScale a := by
  classical
  have hdone1 := grayChargedFinalAtV2_successor_done replay.final
  have hinv := grayChargedRequestInvariantV2_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) hpin hae (T + 1)
  have hwindow : GrayChargedDoneWindow q a e
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.map
        GrayTailRoundV2.toV1) := by
    unfold GrayChargedRequestInvariantV2 at hinv
    rw [hdone1] at hinv
    exact hinv
  rw [totalRootRequest]
  calc (∑ i : Fin n, getFamilyReq
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) i.val []) <=
      ∑ _i : Fin n, dyadicScale a := by
        apply Finset.sum_le_sum
        intro i _
        rw [grayChargedRunMoveV2_root_eq_of_done hdone1 i]
        exact (hwindow i).2
    _ = (n : Rat) * dyadicScale a := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]

/-- The total requests over frozen rounds scaled by `halfAmplification q`
is bounded by the mass of frozen source charges. -/
private lemma grayChargedV2_rounds_request_le_frozen_mass
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) :
    halfAmplification q *
        grayChargedRoundsRequestV2 n q L a e sigma A sm (T + 1) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)) := by
  have hmassEq := grayChargedFrozenSourcesV2_mass hsm replay hU hae
  rw [hmassEq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact grayChargedV2_rounds_request_le_mass hae k

/-- **H3 at reduced reserves** (Phase 2C): the amplified final display is
dominated by the ledger plus any reserve charge carrying `5ε/6` per
resolved coordinate. -/
theorem grayChargedV2_aggregate_request_reduced
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)}
    (hRmassGe : ((grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
        (dyadicScale e - dyadicScale e / 6) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves))
    (hraisedEq : grayChargedRaisedSources (grayChargedSourceCount a e)
        (grayChargedThreshold q e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.map
          GrayTailRoundV2.toV1) =
      grayChargedReplayV2RaisedSources replay)
    (hQcalls0 : 0 <=
      (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)))
    (hR0 : (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) <=
      totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)))
    (hQlower : ((n * grayChargedSourceCount a e : Nat) : Rat) *
        dyadicScale e / 2 <=
      totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1))) :
    ((n * grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) ∧
    halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) := by
  classical
  have hdone1 := grayChargedFinalAtV2_successor_done replay.final
  have hmoveU : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm (T + 1) :=
    (replay.move_stable U hU).trans
      (grayChargedFinalAtV2_successor_move_eq replay.final).symm
  have hsplit1 := grayChargedV2_final_display_request_split
    (q := q) (L := L) (a := a) (e := e) (n := n)
    (sigma := sigma) (A := A) (sm := sm) hdone1
  rw [hraisedEq] at hsplit1
  have hQupper := grayChargedV2_done_display_upper hae hpin replay
  have hbudget := grayChargedV2_budget_eq n a e hae
  have hcallsLe := grayChargedV2_rounds_request_le_frozen_mass hsm hae replay hU
  have hthree := grayChargedReplayV2_resolved_three_quarters replay
  have hrc : (grayChargedReplayV2RaisedSources replay).card <=
      (grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card :=
    Finset.card_le_card Finset.subset_union_left
  have hFmass : grayChargeMass (e + grayTailNewLoss q L)
      (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
        hU hae) ++ grayChargedReserveChargeV2 reserves) =
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)) +
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves) :=
    grayChargeMass_append _ _ _
  have hkappa : (1 : Rat) <= halfAmplification q := by
    unfold halfAmplification
    have hq : (0 : Rat) <= (q : Rat) / 2 := by positivity
    linarith
  have heps : (0 : Rat) < dyadicScale e := dyadicScale_pos e
  have harith := grayChargedV2_allReduced_aggregate
    (m := n * grayChargedSourceCount a e)
    (c := (grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay).card)
    (r := (grayChargedReplayV2RaisedSources replay).card)
    (kappa := halfAmplification q) (eps := dyadicScale e)
    (Q := totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)))
    (Qcalls := ∑ k : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length,
      totalRootRequest
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[k.val]).move))
    (R := totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) -
      ∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move))
    (MS := grayChargeMass (e + grayTailNewLoss q L)
      (grayChargedSourceChargeV2
        (grayChargedFrozenSourcesV2 hsm replay hU hae)))
    (MR := grayChargeMass (e + grayTailNewLoss q L)
      (grayChargedReserveChargeV2 reserves))
    (MF := grayChargeMass (e + grayTailNewLoss q L)
      (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
        hU hae) ++ grayChargedReserveChargeV2 reserves))
    hkappa heps
    (by exact_mod_cast hthree)
    (by exact_mod_cast hrc)
    (by ring)
    (by linarith)
    hQcalls0
    hsplit1
    (by
      rw [← hbudget] at hQupper
      exact hQupper)
    hQlower
    hcallsLe
    (by
      have h56 : ((grayChargedReplayV2RaisedSources replay ∪
          grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
          (5 * dyadicScale e / 6) =
          ((grayChargedReplayV2RaisedSources replay ∪
            grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
          (dyadicScale e - dyadicScale e / 6) := by
        congr 1
        ring
      rw [h56]
      exact hRmassGe)
    hFmass
  constructor
  · exact harith.1
  · conv_lhs => rw [hmoveU]
    rw [halfAmplification_succ]
    exact harith.2

/-- The accepted round totals are nonnegative (discharges `hQcalls0`). -/
lemma grayChargedV2_rounds_total_nonneg
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} :
    0 <= (∑ k : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.length,
      totalRootRequest
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen[k.val]).slots.length)
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen[k.val]).move)) := by
  apply Finset.sum_nonneg
  intro k _
  rw [totalRootRequest]
  apply Finset.sum_nonneg
  intro j _
  have hmem : (((grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen[k.val]).toV1.slots.get
          ⟨j.val, j.isLt⟩,
      familyClientMoveAt (((grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen[k.val]).toV1.move) j.val) ∈
      grayTailFrozenEntries
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1) := by
    rw [grayTailFrozenEntries, List.mem_flatMap]
    refine ⟨_, List.mem_map_of_mem (List.getElem_mem k.isLt), ?_⟩
    rw [grayTailSlotEntries]
    exact List.mem_ofFn.mpr ⟨⟨j.val, j.isLt⟩, rfl⟩
  have hnn := grayChargedRunStateV2_frozenEntries_req_nonneg _ hmem
  simpa [getFamilyReq, GrayTailRoundV2.toV1] using hnn

/-- The final display carries at least half the coarse budget
(discharges `hQlower`). -/
lemma grayChargedV2_final_display_lower
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    ((n * grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e / 2 <=
      totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) := by
  classical
  have hdone1 := grayChargedFinalAtV2_successor_done replay.final
  have hinv := grayChargedRequestInvariantV2_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) hpin hae (T + 1)
  have hwindow : GrayChargedDoneWindow q a e
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.map
        GrayTailRoundV2.toV1) := by
    unfold GrayChargedRequestInvariantV2 at hinv
    rw [hdone1] at hinv
    exact hinv
  have hbudget := grayChargedV2_budget_eq n a e hae
  rw [show ((n * grayChargedSourceCount a e : Nat) : Rat) *
      dyadicScale e / 2 =
      ((n * grayChargedSourceCount a e : Nat) : Rat) *
        dyadicScale e * (1 / 2) by ring,
    hbudget]
  rw [totalRootRequest]
  calc (n : Rat) * dyadicScale a * (1 / 2) =
      ∑ _i : Fin n, dyadicScale a / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin]
        ring
    _ <= ∑ i : Fin n, getFamilyReq
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) i.val [] := by
        apply Finset.sum_le_sum
        intro i _
        rw [grayChargedRunMoveV2_root_eq_of_done hdone1 i]
        exact (hwindow i).1

/-- The accepted round totals never exceed the final display: the raise
terms are nonnegative because source son bases stay below one coarse unit
(discharges `hR0`). -/
lemma grayChargedV2_calls_le_display
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e) (_hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    (∑ k : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length,
      totalRootRequest
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) <=
      totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) := by
  classical
  have hdone1 := grayChargedFinalAtV2_successor_done replay.final
  set frozenV1 := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
    with hfv
  have hdisplay : totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) =
      ∑ i : Fin n, grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries frozenV1) i := by
    rw [totalRootRequest]
    exact Finset.sum_congr rfl fun i _ =>
      grayChargedRunMoveV2_root_eq_of_done hdone1 i
  have hsplit := grayCharged_rootRequest_sum_split
    (n := n) (b := grayTailBranch q L a e) (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (dyadicScale e)
    (grayTailFrozenEntries frozenV1)
  have htot := grayTailFrozenEntries_total_sum frozenV1
  have hround : (∑ k : Fin frozenV1.length,
      totalRootRequest (frozenV1[k.val]).slots.length
        (frozenV1[k.val]).move) =
      ∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm
              (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move) := by
    have hlen : frozenV1.length = (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length := by
      rw [hfv, List.length_map]
    refine Finset.sum_nbij' (fun k => ⟨k.val, by omega⟩)
      (fun k => ⟨k.val, by omega⟩) ?_ ?_ ?_ ?_ ?_ <;>
      intro k <;> simp [hfv, GrayTailRoundV2.toV1]
  -- the raise terms are nonnegative
  have hifnn : 0 <= ∑ z : Fin n × Fin (grayTailBranch q L a e),
      (if z.2.val < grayChargedSourceCount a e ∧
          grayChargedThreshold q e <
            grayTailSonBase (grayTailFrozenEntries frozenV1) z.1 z.2 then
        dyadicScale e -
          grayTailSonBase (grayTailFrozenEntries frozenV1) z.1 z.2
      else 0) := by
    apply Finset.sum_nonneg
    intro z _
    by_cases hz : z.2.val < grayChargedSourceCount a e ∧
        grayChargedThreshold q e <
          grayTailSonBase (grayTailFrozenEntries frozenV1) z.1 z.2
    · rw [ite_eq_left hz]
      have hle := grayChargedRunStateV2_source_sonBase_le hae replay
        le_rfl z.1 z.2 hz.1
      have hle2 : grayTailSonBase
          (grayTailFrozenEntries frozenV1) z.1 z.2 <= dyadicScale e := by
        rw [hfv]
        exact hle
      linarith
    · rw [ite_eq_right hz]
  rw [hdisplay, hsplit, htot, hround]
  linarith

/-- Source son bases are stable from the advantage terminal to every late
time: post-exit rounds occupy spare sons only. -/
lemma grayChargedRunStateV2_source_sonBase_stable
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hc : c.val < grayChargedSourceCount a e) :
    grayTailFrozenSonBase
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1)
        i c =
      grayTailFrozenSonBase (frozenV1OfV2 replay.advantageTerminal) i c := by
  classical
  have hexitU : replay.advantageExitTime + 1 <= U := by
    have := replay.advantageExit_le
    omega
  have hpre : replay.advantageTerminal.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen := by
    rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
    exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm hexitU
  obtain ⟨rest, hrest⟩ := hpre
  have hmap : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1 =
      replay.advantageTerminal.frozen.map GrayTailRoundV2.toV1 ++
      rest.map GrayTailRoundV2.toV1 := by
    rw [← List.map_append, hrest]
  have hzero : grayTailFrozenSonBase
      (rest.map GrayTailRoundV2.toV1) i c = 0 := by
    apply grayTailSonBase_eq_zero_of_no_match
    intro z hz
    right
    intro hzc
    rw [grayTailFrozenEntries, List.mem_flatMap] at hz
    obtain ⟨pV1, hpV1, hzp⟩ := hz
    rw [List.mem_map] at hpV1
    obtain ⟨p, hp, rfl⟩ := hpV1
    have hpmem : p ∈ (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen := by
      rw [← hrest]
      exact List.mem_append_right _ hp
    have hclass := grayChargedRunStateV2_frozen_post_exit_spend hae replay
      hexitU p hpmem
    have hnotpre : p ∉ replay.advantageTerminal.frozen := by
      intro hmem
      have hnodup : ((grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.map
            GrayTailRoundV2.roundIndex).Nodup := by
        have hidx := (grayChargedRunStateV2_coreCertified (n := n)
          q L a e sigma A sm U).frozen_index
        rw [List.nodup_iff_injective_getElem]
        intro k1 k2 heq
        have h1 := hidx k1.val (by
          simpa using k1.isLt)
        have h2 := hidx k2.val (by
          simpa using k2.isLt)
        simp only [List.getElem_map] at heq
        apply Fin.ext
        omega
      rw [← hrest, List.map_append] at hnodup
      have hdisj := (List.nodup_append.mp hnodup).2.2
      exact hdisj _ (List.mem_map_of_mem hmem)
        _ (List.mem_map_of_mem hp) rfl
    have hcoarse : ¬ grayCallDepth q e <= p.blockAnchor := by
      rcases hclass with hmem | hcoarse
      · exact (hnotpre hmem).elim
      · exact hcoarse
    have hslots := ((grayChargedRunStateV2_coreCertified (n := n)
      q L a e sigma A sm U).round_valid p hpmem).2.2.2.2.2
    rcases hslots with ⟨hpA, -, -, -, -, -⟩ |
      ⟨pass, hpass, hpA, hpF, hgoal, hpSlots, -⟩
    · exact hcoarse (by
        rw [hpA]
        unfold grayTailRoundEps
        exact Nat.le_add_right _ _)
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hzp
      have hmemj : (GrayTailRoundV2.toV1 p).slots.get j ∈ p.slots := by
        exact List.get_mem _ _
      have hpair := hpSlots ((GrayTailRoundV2.toV1 p).slots.get j) hmemj
      have hge : grayChargedSourceCount a e <=
          ((GrayTailRoundV2.toV1 p).slots.get j).2.1.val := by
        exact grayBlockSpendPairs_first_ge hpair
      have heq2 : ((GrayTailRoundV2.toV1 p).slots.get j).2.1.val = c.val :=
        congrArg Fin.val hzc
      omega
  rw [hmap, grayTailFrozenSonBase_append_list, hzero, add_zero,
    frozenV1OfV2]

/-- The raised set at any late time is the replay's raised set
(discharges `hraisedEq`). -/
lemma grayChargedReplayV2_raisedSources_late_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) :
    grayChargedRaisedSources (grayChargedSourceCount a e)
        (grayChargedThreshold q e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1) =
      grayChargedReplayV2RaisedSources replay := by
  classical
  ext z
  rw [grayChargedReplayV2RaisedSources]
  simp only [grayChargedRaisedSources, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← grayChargedRunStateV2_source_sonBase_stable hae replay hU
      z.1 z.2 h1]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [grayChargedRunStateV2_source_sonBase_stable hae replay hU
      z.1 z.2 h1]
    exact h2

/-- **H3 at reduced reserves, every premise discharged**: the amplified
final display is dominated by the ledger plus any reserve charge carrying
`5ε/6` per resolved coordinate. -/
theorem grayChargedV2_aggregate_request_reduced_final
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)}
    (hRmassGe : ((grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
        (dyadicScale e - dyadicScale e / 6) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves)) :
    ((n * grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) ∧
    halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) :=
  grayChargedV2_aggregate_request_reduced hsm hae hpin replay hU hRmassGe
    (grayChargedReplayV2_raisedSources_late_eq hae replay le_rfl)
    grayChargedV2_rounds_total_nonneg
    (grayChargedV2_calls_le_display hae hpin replay)
    (grayChargedV2_final_display_lower hae hpin replay)

end Kolmogorov
