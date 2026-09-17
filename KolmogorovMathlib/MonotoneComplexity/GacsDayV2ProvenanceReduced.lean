import KolmogorovMathlib.MonotoneComplexity.GacsDayV2CornerReduced
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Provenance
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2DisjointAssembly
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Leaf2Final
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2L5Disjoint
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RaisedKill

/-!
# The reduced capstone (Phase 2D): geometry from the mixed family

The Stage-D assembly re-based on owner-aligned complements (proof document
v15.1): the plain mixed family supplies `5ε/6` certificates and the exit-time
data, the reduced corner supplies H2/H3, and the per-root cap survives
unchanged.  The source/reserve disjointness goes through
`grayChargedV2_family_reserve_disjoint_of_straddle`, whose raised-class
straddle is killed at the wait exit: a raised son's reserve is served at or
before `advantageExitTime`, every spend snapshot is taken at or after it
(A7′, `grayChargedReplayV2_spend_round_snapshot_exit`), so the reserve is
harvested and the spend round's cells avoid it.  No anchor is involved.
-/

namespace Kolmogorov

/-- The mixed family covers exactly the resolved coordinates. -/
lemma grayChargedV2_family_length_eq_card
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T}
    {reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)}
    (hcover : forall z, z ∈ grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay ->
      exists r, r ∈ reserves ∧ r.coordinate = z)
    (hcoverBack : forall r, r ∈ reserves -> r.coordinate ∈
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay)
    (hnodup : (reserves.map fun r => r.coordinate).Nodup) :
    reserves.length =
      (grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card := by
  classical
  have hset : (reserves.map fun r => r.coordinate).toFinset =
      grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay := by
    ext z
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hcoverBack r hr
    · intro hz
      obtain ⟨r, hr, hrz⟩ := hcover z hz
      exact ⟨r, hr, hrz⟩
  calc reserves.length = (reserves.map fun r => r.coordinate).length := by
        rw [List.length_map]
    _ = (reserves.map fun r => r.coordinate).toFinset.card :=
        (List.toFinset_card_of_nodup hnodup).symm
    _ = _ := by rw [hset]

/-- Source charge and reserve charge are disjoint for reduced reserves. -/
private lemma grayChargedV2_source_reserve_disjoint_reduced
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hres : GrayChargedReducedReserves hae replay reserves) :
    List.Disjoint
      ((grayChargedSourceChargeV2
        (grayChargedFrozenSourcesV2 hsm replay hU hae)).map Prod.snd)
      ((grayChargedReserveChargeV2 reserves).map Prod.snd) := by
  obtain ⟨hcoverBack, hdatumAll, hsrflag, hservLe⟩ := hres
  refine grayChargedV2_family_reserve_disjoint_of_straddle hsm hae hpin
    replay hU reserves hdatumAll hsrflag ?_
  intro r hr hrsr _k _hk _hp' hdata i hlate w hw y hy
  have hz2 : r.coordinate ∈ grayChargedRaisedSources
      (n := n) (b := grayTailBranch q L a e)
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (frozenV1OfV2 replay.advantageTerminal) :=
    (Finset.mem_union.mp (hcoverBack r hr)).resolve_right hrsr
  have hzsrc : r.coordinate.2.val < grayChargedSourceCount a e :=
    (Finset.mem_filter.mp hz2).2.1
  obtain ⟨hspare, hfineE, hcoarse⟩ :=
    grayChargedV2_late_position_spend_facts hae hpin replay i hlate
  obtain ⟨t₁, ht, hchain⟩ :=
    grayChargedReplayV2_spend_round_snapshot_exit replay
      (List.getElem_mem i.isLt) hcoarse
  rw [grayChargedTransportRound, List.mem_flatMap] at hw
  obtain ⟨l, hl, hw⟩ := hw
  rw [List.mem_ofFn] at hl
  obtain ⟨jj, rfl⟩ := hl
  exact grayChargedV2_spendRound_transported_ne_complement hsm hae
    (List.getElem_mem i.isLt) hchain hspare hfineE hzsrc
    (le_trans (hservLe r hr) ht) hdata.1 hdata.1.1.1 hw hy

/-- Coarse budget identity converting source count times dyadic scale at `e` to scale at `a`. -/
private lemma grayCharged_source_count_dyadic_scale_mul
    (n a e : Nat) (hae : a <= e) :
    ((n * grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e =
      (n : Rat) * dyadicScale a := by
  have h1 := grayCharged_dyadic_pow_convert a e hae
  rw [grayChargedSourceCount, Nat.cast_mul, mul_assoc, h1]

/-- Each reserve record's cells have gray charge mass bounded by dyadic scale at `e`. -/
private lemma grayChargedV2_reserve_cells_mass_le
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    {replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hdatumAll : GrayChargedReserveDataAll hae replay reserves) :
    forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e := by
  intro r hr
  obtain ⟨k, _hk, _hp', hdata, hcells⟩ := hdatumAll r hr
  have hRlen : r.reserve.length = e := hdata.1.1.1
  have hRD : r.reserve.length <= e + grayTailNewLoss q L := by
    rw [hRlen]
    exact Nat.le_add_right _ _
  rw [hcells]
  refine le_trans (grayChargeMass_le_of_sublist _
    (grayChargedReserveComplementV2_sublist _ _ _ _)) ?_
  rw [grayChargedReserveCylinder_mass hRD, hRlen]

/-- **The reduced Stage-D capstone** (Phase 2D, plain): from the mixed
complement family, the full geometry — validity at the call's anchor `a`, H2,
H3, H5, H4 — holds for a final charge of a finished non-positive run. -/
theorem grayChargedV2_geometry_of_l5_reduced
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    exists (U : Nat) (hU : T + 1 <= U)
      (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)),
      grayChargedRunMoveV2 q L a e n sigma A sm U =
        grayChargedRunMoveV2 q L a e n sigma A sm T ∧
      (forall r, r ∈ reserves ->
        exists (k : Nat)
          (hk : k < replay.advantageTerminal.frozen.length)
          (hp' : replay.advantageTerminal.frozen[k] ∈
            (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen),
          GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
            r.reserve k ∧
          r.cells = grayChargedReserveComplementV2 r.coordinate.1.val
            (e + grayTailNewLoss q L) r.reserve
            (grayChargedOwnerFibreV2 hae
              (replay.advantageTerminal.frozen[k]) hp' r.coordinate)) ∧
      (forall r, r ∈ reserves ->
        r.coordinate ∈ grayChargedReplayV2ServerResolvedSources replay ->
        r.serviceTime = replay.advantageDoneTime) ∧
      (exists F : FamilyGrayCharge,
          F.Perm (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2
              hsm replay hU hae) ++
            grayChargedReserveChargeV2 reserves) ∧
          F ∈ (familyGrayChargeUniverse n
            (e + grayTailNewLoss q L)).sublists ∧
          (F.map Prod.snd).Nodup ∧
          (forall z, z ∈ F -> z.1 < n ∧
            z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
              (getFamilyAlloc (sm U) z.1 []) A) ∧
          (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
            grayChargeMass (e + grayTailNewLoss q L) F ∧
          halfAmplification (q + 1) *
              totalRootRequest n
                (grayChargedRunMoveV2 q L a e n sigma A sm U) <=
            grayChargeMass (e + grayTailNewLoss q L) F ∧
          (forall i : Fin n,
            grayChargeMass (e + grayTailNewLoss q L)
                (grayChargeAtRoot i.val F) <=
              4 * halfAmplification (q + 1) *
                getFamilyReq
                  (grayChargedRunMoveV2 q L a e n sigma A sm U)
                  i.val []) ∧
          GrayChargedL5SubfamilyV2 q L e n
            (grayChargedRunMoveV2 q L a e n sigma A sm U) F)
      := by
  classical
  obtain ⟨U, reserves, hU, hmove, hcover, hcoverBack, hcoordNodup,
    hrnodup, hmass56, hdatumAll, hsrflag, hservLe⟩ :=
    grayChargedV2_complement_reserve_family_plain hsm hae hnotpos replay
  refine ⟨U, hU, reserves, hmove, hdatumAll, hsrflag, ?_⟩
  have Hdisj := grayChargedV2_source_reserve_disjoint_reduced hsm hae hpin
    replay hU reserves ⟨hcoverBack, hdatumAll, hsrflag, hservLe⟩
  have hlen := grayChargedV2_family_length_eq_card hcover hcoverBack
    hcoordNodup
  have hRmassGe : ((grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
      (dyadicScale e - dyadicScale e / 6) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves) := by
    have hagg := grayChargedV2_complement_family_aggregate_mass reserves
      (fun r hr => (hmass56 r hr).2)
    rw [hlen] at hagg
    exact hagg
  have hH23 := grayChargedV2_aggregate_request_reduced_final hsm hae hpin
    replay hU hRmassGe
  have hbudget := grayCharged_source_count_dyadic_scale_mul n a e hae
  have hunit := grayChargedV2_reserve_cells_mass_le hae reserves hdatumAll
  have hsnodup := grayChargedFrozenSourcesV2_cells_nodup hsm replay
    hU hae hpin
  obtain ⟨F, hFperm, hFmem, hFnodup, hFvalid, hFmass, hFroot⟩ :=
    grayChargedV2_exists_finalCharge
      (grayChargedFrozenSourcesV2 hsm replay hU hae) reserves
      hsnodup hrnodup Hdisj
  refine ⟨F, hFperm, hFmem, hFnodup, hFvalid, ?_, ?_, ?_, ?_⟩
  · have h2 := hH23.1
    rw [hFmass]
    rw [grayChargeMass_append] at h2
    have h34 : (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
        ((n * grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e := by
      rw [hbudget]
      have hpos : (0 : Rat) <= (n : Rat) * dyadicScale a :=
        mul_nonneg (Nat.cast_nonneg n) (dyadicScale_pos a).le
      linarith
    linarith
  · have h3 := hH23.2
    rw [hFmass]
    rw [grayChargeMass_append] at h3
    exact h3
  · intro i
    have hcap := grayChargedV2_perRoot_cap hsm hpin hae replay hU
      hunit hcoordNodup i
    rw [hFroot i.val]
    have hsplit : grayChargeAtRoot i.val
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) =
        grayChargeAtRoot i.val (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)) ++
        grayChargeAtRoot i.val (grayChargedReserveChargeV2 reserves) := by
      rw [grayChargeAtRoot, List.filter_append]
      rfl
    rw [hsplit, grayChargeMass_append] at hcap
    exact hcap
  · intro I hI
    have h4 := grayChargedV2_l5subfamily_final hpin hae replay hsm hU
      reserves hcoverBack hcover hcoordNodup
      (fun r hr => by have hm := (hmass56 r hr).2; linarith) hmove I hI
    rw [grayChargeMass_eq_length] at h4 ⊢
    rw [(hFperm.filter (fun z => decide (z.1 ∈ I))).length_eq]
    exact h4

end Kolmogorov
