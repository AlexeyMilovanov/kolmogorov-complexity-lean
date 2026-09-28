import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureLedgerCap

/-!
# The V2 aggregate-request corner (Stage D4/H3)

The final display splits into the accepted rounds' totals plus a raised-son
remainder; each round's total is dominated by its local charge mass at the
recursive amplification; the reserves carry one coarse unit per resolved
source, three quarters of the population.  The audited corner arithmetic
turns this into the amplified aggregate `H3` of the composed charge.
-/

namespace Kolmogorov

/-- **The V2 final display split** at a done horizon: total display = frozen
round totals + a raised-audited remainder. -/
theorem grayChargedV2_final_display_request_split
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).phase = .done) :
    totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) -
        (∑ k : Fin (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen.length,
          totalRootRequest
            (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm U).core.frozen[k.val]).slots.length)
            (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm U).core.frozen[k.val]).move)) <=
      ((grayChargedRaisedSources (grayChargedSourceCount a e)
          (grayChargedThreshold q e)
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen.map
            GrayTailRoundV2.toV1)).card : Rat) *
        (dyadicScale e / (6 * halfAmplification q)) := by
  classical
  set frozenV1 := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1 with hfv
  have hsplit := grayCharged_rootRequest_sum_split
    (n := n) (b := grayTailBranch q L a e) (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (dyadicScale e)
    (grayTailFrozenEntries frozenV1)
  have hdisplay : totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm U) =
      ∑ i : Fin n, grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries frozenV1) i := by
    rw [totalRootRequest]
    exact Finset.sum_congr rfl fun i _ =>
      grayChargedRunMoveV2_root_eq_of_done hdone i
  have htot := grayTailFrozenEntries_total_sum frozenV1
  have hround : (∑ k : Fin frozenV1.length,
      totalRootRequest (frozenV1[k.val]).slots.length
        (frozenV1[k.val]).move) =
      ∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen[k.val]).move) := by
    have hlen : frozenV1.length = (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen.length := by
      rw [hfv, List.length_map]
    refine Finset.sum_nbij' (fun k => ⟨k.val, by omega⟩)
      (fun k => ⟨k.val, by omega⟩) ?_ ?_ ?_ ?_ ?_ <;>
      intro k <;> simp [hfv, GrayTailRoundV2.toV1]
  have hrem := grayCharged_raise_remainder_le
    (n := n) (b := grayTailBranch q L a e) (grayChargedSourceCount a e)
    (dyadicScale e) (dyadicScale e / (6 * halfAmplification q))
    (grayTailFrozenEntries frozenV1)
  have hcard : (Finset.univ.filter
      fun z : Fin n × Fin (grayTailBranch q L a e) =>
      z.2.val < grayChargedSourceCount a e ∧
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailSonBase (grayTailFrozenEntries frozenV1) z.1 z.2) =
      grayChargedRaisedSources (grayChargedSourceCount a e)
        (grayChargedThreshold q e) frozenV1 := rfl
  rw [hcard] at hrem
  rw [← grayChargedThreshold_eq] at hrem
  have hchain : totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm U) =
      (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen[k.val]).move)) +
      ∑ z : Fin n × Fin (grayTailBranch q L a e),
        (if z.2.val < grayChargedSourceCount a e ∧
            grayChargedThreshold q e <
              grayTailSonBase (grayTailFrozenEntries frozenV1) z.1 z.2 then
          dyadicScale e -
            grayTailSonBase (grayTailFrozenEntries frozenV1) z.1 z.2
        else 0) := by
    rw [hdisplay, hsplit, htot, hround]
  linarith [hrem, hchain]

/-- Per-round amplified totals are dominated by the local charge masses. -/
lemma grayChargedV2_rounds_request_le_mass
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (k : Fin (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.length) :
    halfAmplification q *
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm U).core.frozen[k.val]).move) <=
      grayChargeMass
        (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen[k.val]).blockAnchor + L)
        (grayChargedRoundLocalChargeV2 hae _ (List.getElem_mem k.isLt)) := by
  set p := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm U).core.frozen[k.val] with hpdef
  have hp : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen := List.getElem_mem k.isLt
  unfold grayChargedRoundLocalChargeV2
  split
  next hfine =>
    have hsplit := grayChargedRunStateV2_frozen_phase_split
      q L a e sigma A sm U hp hae hfine
    have hvalid := grayChargedLocalChargeOfBlockGoal_valid
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm U hp
        hae hfine)
    have hagg := (familyGrayChargeAtB.aggregate hvalid).2
    have hEq : grayTailRoundDelta q L e p.roundIndex =
        p.blockAnchor + L := by
      rw [hsplit.1, grayTailRoundDelta]
    rw [← hEq]
    exact hagg
  next hfine =>
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm U hp hfine
    have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
      hSp.choose_spec.2.2.2
    have hagg := (familyGrayChargeAtB.aggregate hvalid).2
    have hanchor := hSp.choose_spec.2.1
    have hfineEq2 := hSp.choose_spec.2.2.1
    have hd : grayChargedSpendDelta a L e hSp.choose =
        grayChargedSpendEps a L e hSp.choose + L := rfl
    have hfineEq3 : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm U hp
    have hEq : grayChargedSpendDelta a L e hSp.choose =
        p.blockAnchor + L := by omega
    rw [← hEq]
    exact hagg

/-- **The V2 aggregate request H3**: at the reserve horizon, the amplified
final display is dominated by the composed charge (sources + reserves). -/
theorem grayChargedV2_aggregate_request
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)}
    (hRmass : grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves) =
      ((grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
        dyadicScale e) :
    halfAmplification (q + 1) *
        totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) := by
  classical
  -- everything happens at T + 1 (the ledger's home); the display at U is the
  -- display at T + 1
  have hdone1 := grayChargedFinalAtV2_successor_done replay.final
  have hmoveU : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm (T + 1) :=
    (replay.move_stable U hU).trans
      (grayChargedFinalAtV2_successor_move_eq replay.final).symm
  conv_lhs => rw [hmoveU]
  -- the display split at T + 1
  have hsplit1 := grayChargedV2_final_display_request_split
    (q := q) (L := L) (a := a) (e := e) (n := n)
    (sigma := sigma) (A := A) (sm := sm) hdone1
  -- Q ≤ n·α from the done window at T + 1
  have hQupper : totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) <=
      (n : Rat) * dyadicScale a := by
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
  -- κ·round totals ≤ ledger mass
  have hmassEq := grayChargedFrozenSourcesV2_mass hsm replay hU hae
  have hcallsLe : halfAmplification q *
      (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)) := by
    rw [hmassEq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    exact grayChargedV2_rounds_request_le_mass hae k
  -- the raised card is at most the source population
  have hm1 : (grayChargedRaisedSources (grayChargedSourceCount a e)
      (grayChargedThreshold q e)
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.map
        GrayTailRoundV2.toV1)).card <=
      n * grayChargedSourceCount a e := by
    have hsub : grayChargedRaisedSources (grayChargedSourceCount a e)
        (grayChargedThreshold q e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.map
          GrayTailRoundV2.toV1) ⊆
        Finset.univ.filter
          (fun z : Fin n × Fin (grayTailBranch q L a e) =>
            z.2.val < grayChargedSourceCount a e) := by
      intro z hz
      have := (Finset.mem_filter.mp hz).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
    have hprod : Finset.univ.filter
        (fun z : Fin n × Fin (grayTailBranch q L a e) =>
          z.2.val < grayChargedSourceCount a e) =
        (Finset.univ : Finset (Fin n)) ×ˢ
          (Finset.univ.filter
            (fun c : Fin (grayTailBranch q L a e) =>
              c.val < grayChargedSourceCount a e)) := by
      ext z
      simp [Finset.mem_product]
    calc (grayChargedRaisedSources _ _ _).card <=
        (Finset.univ.filter
          (fun z : Fin n × Fin (grayTailBranch q L a e) =>
            z.2.val < grayChargedSourceCount a e)).card :=
          Finset.card_le_card hsub
      _ <= n * grayChargedSourceCount a e := by
          rw [hprod, Finset.card_product, Finset.card_univ,
            Fintype.card_fin]
          exact Nat.mul_le_mul_left n
            (grayTail_source_fin_card_le (grayTailBranch q L a e)
              (grayChargedSourceCount a e))
  -- three quarters resolved
  have hthree := grayChargedReplayV2_resolved_three_quarters replay
  -- mass splits over the append
  have hFmass : grayChargeMass (e + grayTailNewLoss q L)
      (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
        hU hae) ++ grayChargedReserveChargeV2 reserves) =
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)) +
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves) :=
    grayChargeMass_append _ _ _
  -- assemble via the audited corner arithmetic
  exact grayCharged_aggregate_request_arith hae
    (by ring : totalRootRequest n
      (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) =
      (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) +
      (totalRootRequest n
        (grayChargedRunMoveV2 q L a e n sigma A sm (T + 1)) -
        ∑ k : Fin (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.length,
          totalRootRequest
            (((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
            (((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)))
    hsplit1 hm1 hQupper hthree hcallsLe hRmass hFmass

end Kolmogorov
