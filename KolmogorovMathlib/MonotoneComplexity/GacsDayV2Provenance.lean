import KolmogorovMathlib.MonotoneComplexity.GacsDayV2PerRoot

/-!
# The V2 charge provenance (Stage D5): record and conditional assembly

The complete anchored ledger record of the finished V2 run, and its
constructor from the machine-checked suppliers.  The two L5 geometric
inputs — source/reserve cell disjointness and the hereditary subfamily
bound — are taken as explicit hypotheses: everything else is discharged by
the proved Stage C/D lemmas, so the roomy closure is reduced to exactly
those two named statements.
-/

namespace Kolmogorov

/-- Reorder the two V2 ledgers into one admissible final charge. -/
theorem grayChargedV2_exists_finalCharge
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {c : FamilyClientMove}
    (sources : List (GrayChargedChargeSourceV2 q L a e n A c (sm U)))
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hsnodup : ((grayChargedSourceChargeV2 sources).map Prod.snd).Nodup)
    (hrnodup : ((grayChargedReserveChargeV2 reserves).map Prod.snd).Nodup)
    (hdisj : List.Disjoint
      ((grayChargedSourceChargeV2 sources).map Prod.snd)
      ((grayChargedReserveChargeV2 reserves).map Prod.snd)) :
    exists F : FamilyGrayCharge,
      F.Perm (grayChargedSourceChargeV2 sources ++
          grayChargedReserveChargeV2 reserves) ∧
        F ∈ (familyGrayChargeUniverse n (e + grayTailNewLoss q L)).sublists ∧
        (F.map Prod.snd).Nodup ∧
        (forall z, z ∈ F -> z.1 < n ∧
          z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
            (getFamilyAlloc (sm U) z.1 []) A) ∧
        grayChargeMass (e + grayTailNewLoss q L) F =
          grayChargeMass (e + grayTailNewLoss q L)
              (grayChargedSourceChargeV2 sources) +
            grayChargeMass (e + grayTailNewLoss q L)
              (grayChargedReserveChargeV2 reserves) ∧
        forall i, grayChargeMass (e + grayTailNewLoss q L)
            (grayChargeAtRoot i F) =
          grayChargeMass (e + grayTailNewLoss q L)
              (grayChargeAtRoot i (grayChargedSourceChargeV2 sources)) +
            grayChargeMass (e + grayTailNewLoss q L)
              (grayChargeAtRoot i (grayChargedReserveChargeV2 reserves)) := by
  have hvalid : forall z, z ∈ grayChargedSourceChargeV2 sources ++
      grayChargedReserveChargeV2 reserves ->
      z.1 < n ∧ z.2 ∈ newGrayCellsList a (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨r, -, hzr⟩ := List.mem_flatMap.mp hz
      exact r.transported_valid z hzr
    · obtain ⟨r, -, hzr⟩ := List.mem_flatMap.mp hz
      exact r.cells_valid z hzr
  have hnodup : (((grayChargedSourceChargeV2 sources ++
      grayChargedReserveChargeV2 reserves).map Prod.snd)).Nodup := by
    rw [List.map_append]
    exact List.Nodup.append hsnodup hrnodup hdisj
  obtain ⟨F, hFmem, hFperm⟩ :=
    exists_mem_sublists_familyGrayChargeUniverse_perm hnodup
      (fun z hz => ⟨(hvalid z hz).1,
        (mem_newGrayCellsList.mp (hvalid z hz).2).1⟩)
  refine ⟨F, hFperm, hFmem, ?_, ?_, ?_, ?_⟩
  · exact ((hFperm.map Prod.snd).nodup_iff).mpr hnodup
  · intro z hz
    exact hvalid z (hFperm.subset hz)
  · rw [grayChargeMass_congr_perm hFperm, grayChargeMass_append]
  · intro i
    rw [grayChargeMass_grayChargeAtRoot_congr_perm hFperm,
      grayChargeAtRoot, List.filter_append,
      ← grayChargeAtRoot, ← grayChargeAtRoot, grayChargeMass_append]

/-- **The V2 anchored charge geometry of the finished run** (the conditional
assembly): given the L5 disjointness input for the constructed ledgers, the
composed final charge satisfies the anchored aggregate/per-root
specification of the next rung.  Everything except the disjointness (and
the hereditary subfamily clause, not stated here) is machine-checked. -/
theorem grayChargedV2_geometry_of_l5
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
      (forall _ : List.Disjoint
          ((grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
            hU hae)).map Prod.snd)
          ((grayChargedReserveChargeV2 reserves).map Prod.snd),
        exists F : FamilyGrayCharge,
          F.Perm (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm
              replay hU hae) ++
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
                  i.val [])) := by
  classical
  obtain ⟨U, reserves, hU, hmove, hcover, hcoverBack, hrnodup, hRmass,
    hcoordNodup, hunitEq, hcyl⟩ :=
    grayChargedV2_late_reserve_family hsm hae hnotpos replay
  refine ⟨U, hU, reserves, hmove, ?_⟩
  intro Hdisj
  have hsnodup := grayChargedFrozenSourcesV2_cells_nodup hsm replay
    hU hae hpin
  obtain ⟨F, hFperm, hFmem, hFnodup, hFvalid, hFmass, hFroot⟩ :=
    grayChargedV2_exists_finalCharge
      (grayChargedFrozenSourcesV2 hsm replay hU hae) reserves
      hsnodup hrnodup Hdisj
  refine ⟨F, hFperm, hFmem, hFnodup, hFvalid, ?_, ?_, ?_⟩
  · -- H2
    have hb := grayChargedV2_aggregate_beta hsm hae replay hU hRmass
    rw [hFmass]
    rw [grayChargeMass_append] at hb
    exact hb
  · -- H3
    have hr := grayChargedV2_aggregate_request hsm hae hpin replay hU hRmass
    rw [hFmass]
    rw [grayChargeMass_append] at hr
    exact hr
  · -- H5
    intro i
    have hcap := grayChargedV2_perRoot_cap hsm hpin hae replay hU
      (fun r hr => le_of_eq (hunitEq r hr)) hcoordNodup i
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

end Kolmogorov
