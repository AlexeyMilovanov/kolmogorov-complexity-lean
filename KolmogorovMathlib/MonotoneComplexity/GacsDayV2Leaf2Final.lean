import KolmogorovMathlib.MonotoneComplexity.GacsDayV2CornerReduced
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2PerRoot
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Source.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Source

/-!
# Leaf 2 (D4) — the raised-remainder cap `hEbound`, and the unconditional H4

The last open hypothesis of `grayChargedV2_l5subfamily_of_family` is the
owner-restricted raised-remainder cap
`2·(D_I − P_I) − (D − P) ≤ c_I · ε/(6κ)`.  With `D_I − P_I` the raised remainder
at `I` (per-son split `grayChargedSonRequest_eq_base_add_raise`, and
`P_I` = the owner-restricted base sum), every raised son's remainder is below
the strict owner cap `ε/(6κ)` (`threshold = ε − ε/(6κ)`), and the raised sons
at `I` inject into the resolved sons at `I` (`c_I`).  This module discharges it
and states the unconditional `GrayChargedL5SubfamilyV2` for the geometry's
final charge.
-/

namespace Kolmogorov

/-- The displayed root request at time `U` matches the charged root request computed
from frozen entries at `T + 1`. -/
private theorem grayChargedV2_leaf2_req_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (i : Fin n) :
    getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U) i.val [] =
      grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.map
            GrayTailRoundV2.toV1)) i := by
  have hdoneU := (replay.done_stable U hU).1
  have hfrozU := (replay.done_stable U hU).2
  rw [grayChargedRunMoveV2_root_eq_of_done hdoneU i, hfrozU]

/-- The total source-ledger base request across all roots equals the sum of frozen son bases. -/
private theorem grayChargedV2_leaf2_totalBaseSum_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} :
    (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        totalRootRequest
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
          (((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).move)) =
      ∑ i : Fin n, ∑ c : Fin (grayTailBranch q L a e),
        grayTailSonBase (grayTailFrozenEntries
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1)) i c := by
  have hPall := grayChargedV2_leaf2_PI_eq_base (q := q) (L := L) (a := a)
    (e := e) (n := n) (sigma := sigma) (A := A) (sm := sm) (t := T + 1)
    (List.range n)
  have hfiltAll : Finset.univ.filter (fun i : Fin n => i.val ∈ List.range n) =
      Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact List.mem_range.mpr i.isLt
  rw [hfiltAll] at hPall
  rw [← hPall]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [grayChargedV2_totalReqOnList_ownerFilter]
  unfold totalRootRequest
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [if_pos (List.mem_range.mpr (Fin.isLt _))]

/-- The sum of raised indicators over roots in `I` equals the cardinality of raised
sources restricted to `I`. -/
private theorem grayChargedV2_leaf2_raised_indicator_sum_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (I : List Nat) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
        ∑ c : Fin (grayTailBranch q L a e),
          (if c.val < grayChargedSourceCount a e ∧
              grayChargedThreshold q e <
                grayTailSonBase (grayTailFrozenEntries
                  ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1)) i c
            then (1 : Rat) else 0)) =
      (((grayChargedRaisedSources (grayChargedSourceCount a e) (grayChargedThreshold q e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1)).filter
        (fun z => z.1.val ∈ I)).card : Rat) := by
  classical
  set frozenV1 := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
  set entries := grayTailFrozenEntries frozenV1
  set src := grayChargedSourceCount a e
  rw [Finset.card_filter]
  unfold grayChargedRaisedSources
  simp only [Finset.sum_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs with hi
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    congr
  · simp

/-- Every raised remainder is bounded by the strict owner cap times the raised indicator. -/
private theorem grayChargedV2_leaf2_raise_le_cap
    (q e : Nat) {b src n : Nat} (entries : List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) :
    (if c.val < src ∧ grayChargedThreshold q e < grayTailSonBase entries i c
      then dyadicScale e - grayTailSonBase entries i c else 0) <=
      (dyadicScale e / (6 * halfAmplification q)) *
        (if c.val < src ∧ grayChargedThreshold q e < grayTailSonBase entries i c
          then (1 : Rat) else 0) := by
  split_ifs with h
  · have hthr := h.2
    unfold grayChargedThreshold at hthr
    rw [mul_one]
    linarith
  · simp

/-- The difference between displayed request on `I` and owner-restricted base sum on `I`
equals the sum of raised remainders over roots in `I`. -/
private theorem grayChargedV2_leaf2_remI_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (I : List Nat) (hInodup : I.Nodup) (hIlt : ∀ x, x ∈ I -> x < n) :
    totalRootRequestOnList I (grayChargedRunMoveV2 q L a e n sigma A sm U) -
      grayChargedRoundsRequestOnListV2 n q L a e sigma A sm (T + 1) I =
      grayChargedRaisedRemainderOnV2 n q L a e sigma A sm (T + 1)
        (Finset.univ.filter (fun i : Fin n => i.val ∈ I)) := by
  unfold grayChargedRoundsRequestOnListV2 grayChargedRaisedRemainderOnV2
    grayChargedRunFrozenEntriesV2 grayChargedRunFrozenV2
  set frozenV1 := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
  set entries := grayTailFrozenEntries frozenV1
  set src := grayChargedSourceCount a e
  set eps := dyadicScale e
  have hreq := grayChargedV2_leaf2_req_eq replay hU
  have hPI := grayChargedV2_leaf2_PI_eq_base (q := q) (L := L) (a := a)
    (e := e) (n := n) (sigma := sigma) (A := A) (sm := sm) (t := T + 1) I
  have hsplit : ∀ i : Fin n,
      grayChargedRootRequest src (grayChargedThreshold q e) eps entries i =
        (∑ c, grayTailSonBase entries i c) + ∑ c,
          if c.val < src ∧ grayChargedThreshold q e < grayTailSonBase entries i c
          then eps - grayTailSonBase entries i c else 0 := by
    intro i
    unfold grayChargedRootRequest
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ =>
      grayChargedSonRequest_eq_base_add_raise src (grayChargedThreshold q e)
        eps entries i c)
  have hDI : totalRootRequestOnList I
      (grayChargedRunMoveV2 q L a e n sigma A sm U) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
        grayChargedRootRequest src (grayChargedThreshold q e) eps entries i := by
    rw [totalRootRequestOnList_eq_map_sum,
      ← grayCharged_list_filter_univ_sum I hInodup hIlt
        (fun i => getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
          i [])]
    exact Finset.sum_congr rfl (fun i _ => hreq i)
  rw [hDI, hPI]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  ring

/-- The difference between total displayed request and total base sum
equals the sum of raised remainders over all roots. -/
private theorem grayChargedV2_leaf2_remAll_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) :
    totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) -
      grayChargedRoundsRequestV2 n q L a e sigma A sm (T + 1) =
      grayChargedRaisedRemainderOnV2 n q L a e sigma A sm (T + 1) Finset.univ := by
  unfold grayChargedRoundsRequestV2 grayChargedRaisedRemainderOnV2
    grayChargedRunFrozenEntriesV2 grayChargedRunFrozenV2
  set frozenV1 := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
  set entries := grayTailFrozenEntries frozenV1
  set src := grayChargedSourceCount a e
  set eps := dyadicScale e
  have hreq := grayChargedV2_leaf2_req_eq replay hU
  have hsplit : ∀ i : Fin n,
      grayChargedRootRequest src (grayChargedThreshold q e) eps entries i =
        (∑ c, grayTailSonBase entries i c) + ∑ c,
          if c.val < src ∧ grayChargedThreshold q e < grayTailSonBase entries i c
          then eps - grayTailSonBase entries i c else 0 := by
    intro i
    unfold grayChargedRootRequest
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ =>
      grayChargedSonRequest_eq_base_add_raise src (grayChargedThreshold q e)
        eps entries i c)
  have hD : totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) =
      ∑ i : Fin n,
        grayChargedRootRequest src (grayChargedThreshold q e) eps entries i := by
    unfold totalRootRequest
    exact Finset.sum_congr rfl (fun i _ => hreq i)
  have hP := grayChargedV2_leaf2_totalBaseSum_eq (q := q) (L := L) (a := a)
    (e := e) (n := n) (sigma := sigma) (A := A) (sm := sm) (T := T)
  rw [hD, hP]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  ring

/-- **The raised-remainder cap at a subfamily** (`hEbound`). -/
theorem grayChargedV2_leaf2_hEbound
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hcoverBack : ∀ r, r ∈ reserves -> r.coordinate ∈
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay)
    (hcover : ∀ z, z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      ∃ r, r ∈ reserves ∧ r.coordinate = z)
    (hcoordNodup : (reserves.map (fun r => r.coordinate)).Nodup)
    (I : List Nat) (hI : I ∈ (List.range n).sublists) :
    2 * (totalRootRequestOnList I
          (grayChargedRunMoveV2 q L a e n sigma A sm U) -
        (∑ k : Fin (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen.length,
            totalRootRequestOnList
              (((List.finRange
                (((grayChargedRunStateV2 (n := n)
                  (b := grayTailBranch q L a e)
                  q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)).filter
                (fun j => decide
                  ((((grayChargedRunStateV2 (n := n)
                    (b := grayTailBranch q L a e)
                    q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
                    j).1.val ∈ I))).map Fin.val)
              (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).move))) -
        (totalRootRequest n (grayChargedRunMoveV2 q L a e n sigma A sm U) -
          (∑ k : Fin (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen.length,
            totalRootRequest
              (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length)
              (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).move))) <=
      ((reserves.countP
        (fun r => decide (r.coordinate.1.val ∈ I)) : Nat) : Rat) *
        (dyadicScale e / (6 * halfAmplification q)) := by
  classical
  have hIsub : I.Sublist (List.range n) := List.mem_sublists.mp hI
  have hInodup : I.Nodup := List.nodup_range.sublist hIsub
  have hIlt : ∀ x, x ∈ I -> x < n :=
    fun x hx => List.mem_range.mp (hIsub.subset hx)
  have hsb : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      c.val < grayChargedSourceCount a e ->
      grayTailSonBase (grayTailFrozenEntries
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.map
            GrayTailRoundV2.toV1)) i c <= dyadicScale e := by
    intro i c hc
    have := grayChargedRunStateV2_source_sonBase_le hae replay (le_refl (T + 1))
      i c hc
    unfold grayTailFrozenSonBase at this
    exact this
  have hraisedEq := grayChargedReplayV2_raisedSources_late_eq hae replay
    (le_refl (T + 1))
  have hcI := grayChargedV2_reserve_countP_eq_resolved_card replay reserves
    hcoverBack hcover hcoordNodup I
  set frozenV1 := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
  set entries := grayTailFrozenEntries frozenV1
  set src := grayChargedSourceCount a e
  set eps := dyadicScale e
  set raise : Fin n -> Fin (grayTailBranch q L a e) -> Rat :=
    fun i c =>
      if c.val < src ∧ grayChargedThreshold q e < grayTailSonBase entries i c
      then eps - grayTailSonBase entries i c else 0 with hraise
  set resolved := grayChargedReplayV2RaisedSources replay ∪
    grayChargedReplayV2ServerResolvedSources replay
  have hRI := grayChargedV2_leaf2_remI_eq replay hU I hInodup hIlt
  have hR := grayChargedV2_leaf2_remAll_eq replay hU
  rw [hRI, hR]
  have hraise_nonneg : ∀ (i : Fin n) (c : Fin (grayTailBranch q L a e)),
      0 <= raise i c := by
    intro i c
    simp only [hraise]
    split_ifs with h
    · have := hsb i c h.1
      linarith
    · exact le_rfl
  have hRIleR : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
        ∑ c, raise i c) <= ∑ i : Fin n, ∑ c, raise i c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Finset.sum_nonneg (fun c _ => hraise_nonneg i c))
  have hcap0 : (0 : Rat) <= eps / (6 * halfAmplification q) := by
    have := dyadicScale_pos e
    have := halfAmplification_pos q
    positivity
  have hRIcap : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
        ∑ c, raise i c) <=
      (eps / (6 * halfAmplification q)) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ∈ I),
          ∑ c, (if c.val < src ∧
              grayChargedThreshold q e < grayTailSonBase entries i c
            then (1 : Rat) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun c _ => grayChargedV2_leaf2_raise_le_cap q e entries i c)
  have hcount := grayChargedV2_leaf2_raised_indicator_sum_eq (q := q) (L := L)
    (a := a) (e := e) (n := n) (sigma := sigma) (A := A) (sm := sm) (T := T) I
  have hle : ((grayChargedRaisedSources src (grayChargedThreshold q e)
        frozenV1).filter (fun z => z.1.val ∈ I)).card <=
      (resolved.filter (fun z => z.1.val ∈ I)).card := by
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    rw [hraisedEq]
    exact Finset.subset_union_left
  have hle' : (((grayChargedRaisedSources src (grayChargedThreshold q e)
        frozenV1).filter (fun z => z.1.val ∈ I)).card : Rat) <=
      ((resolved.filter (fun z => z.1.val ∈ I)).card : Rat) := by
    exact_mod_cast hle
  have hcI' : ((reserves.countP
      (fun r => decide (r.coordinate.1.val ∈ I)) : Nat) : Rat) =
      ((resolved.filter (fun z => z.1.val ∈ I)).card : Rat) := by
    exact_mod_cast hcI
  rw [hcI']
  have hfinal : (eps / (6 * halfAmplification q)) *
      (((grayChargedRaisedSources src (grayChargedThreshold q e)
        frozenV1).filter (fun z => z.1.val ∈ I)).card : Rat) <=
      ((resolved.filter (fun z => z.1.val ∈ I)).card : Rat) *
        (eps / (6 * halfAmplification q)) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hle' hcap0
  rw [hcount] at hRIcap
  linarith [hRIleR, hRIcap, hfinal]

/-- **Leaf 2 closed: the unconditional hereditary subfamily bound (H4)** for
the geometry's final charge `source ++ reserve`, from the source subfamily
bound `(S)`, the reserve deficit `(R_I)`, and the raised-remainder cap. -/
theorem grayChargedV2_l5subfamily_final
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
      grayChargedRunMoveV2 q L a e n sigma A sm T) :
    GrayChargedL5SubfamilyV2 q L e n
      (grayChargedRunMoveV2 q L a e n sigma A sm U)
      (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay hU hae) ++
        grayChargedReserveChargeV2 reserves) :=
  grayChargedV2_l5subfamily_of_family hpin hae replay hsm hU reserves
    hcoverBack hcover hcoordNodup hunit hmove _ _
    (fun I hI => grayChargedV2_leaf2_source_subfamily hsm replay hU hae I
      (List.nodup_range.sublist (List.mem_sublists.mp hI)))
    (fun I hI => grayChargedV2_leaf2_hEbound hae replay hU reserves
      hcoverBack hcover hcoordNodup I hI)

end Kolmogorov
