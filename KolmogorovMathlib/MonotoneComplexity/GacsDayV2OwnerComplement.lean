import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveDatum
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveComplement
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Progress
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Ledger

/-!
# Owner-aligned complements (Phase 2B): the owner window and its `ε/6` cap

The owner component of a resolved source is the transported designated
charge of the owner round restricted to the source's fibre slots.  The wide
block schedule telescopes: the fibre carries at most `mult(r)` slots, each
requesting at most `α_r = 2^{−ε_r}`, and `mult(r)·α_r` is exactly one
call-scale unit, so Day's per-element bound `mass ≤ 4κ·req` caps the whole
owner window at `4κ·2^{−callDepth} ≤ ε/6`.
-/

namespace Kolmogorov

/-- The owner fibre component: the owner round's transported charge over
the slots carrying the source fibre. -/
noncomputable def grayChargedOwnerFibreV2
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (z : Fin n × Fin (grayTailBranch q L a e)) : FamilyGrayCharge :=
  (List.finRange p.slots.length).flatMap fun j =>
    if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
      grayChargedTransportRoot (e + grayTailNewLoss q L) z.1.val j.val
        (grayChargedRoundLocalChargeV2 hae p hp)
    else []

/-- **The owner window cap** (committed local H5 at the call scale): the
owner fibre component of an advantage round carries at most `ε/6`. -/
theorem grayChargedOwnerFibreV2_mass_le
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hadv : grayCallDepth q e <= p.blockAnchor)
    (z : Fin n × Fin (grayTailBranch q L a e)) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedOwnerFibreV2 hae p hp z) <=
      dyadicScale e / 6 := by
  classical
  have hsplit := grayChargedRunStateV2_frozen_phase_split q L a e sigma A
    sm t hp hae hadv
  have hgoal := hsplit.2.2.1
  have hvalid := grayChargedLocalChargeOfBlockGoal_valid
    (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp hae hadv)
  have hnodup : p.slots.Nodup :=
    ((grayChargedRunStateV2_coreCertified q L a e sigma A sm
      t).round_valid p hp).2.2.2.2.1
  have hcount := grayInAdvBlock_fibre_count_le hnodup hsplit.2.2.2.1
  have hbase := grayChargedBlockRoundSonBase_le_callScale hgoal hcount
    z.1 z.2
  have hfineEq : p.fineEnd = p.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
  have hdeltaLe : grayTailRoundDelta q L e p.roundIndex <=
      e + grayTailNewLoss q L := by
    have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
    have h2 := hsplit.2.1
    omega
  have hcharge : grayChargedRoundLocalChargeV2 hae p hp =
      grayChargedLocalChargeOfBlockGoal
        (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp
          hae hadv) := by
    rw [grayChargedRoundLocalChargeV2, dif_pos hadv]
  -- pointwise: each guarded slot contributes at most `4κ·req_j`
  rw [grayChargedOwnerFibreV2, grayChargeMass_flatMap]
  have hstep : ((List.finRange p.slots.length).map fun j =>
      grayChargeMass (e + grayTailNewLoss q L)
        (if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
          grayChargedTransportRoot (e + grayTailNewLoss q L) z.1.val j.val
            (grayChargedRoundLocalChargeV2 hae p hp)
        else [])).sum <=
      ((List.finRange p.slots.length).map fun j =>
        if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
          4 * halfAmplification q * getFamilyReq p.move j.val [] else
          0).sum := by
    apply List.sum_le_sum
    intro j _
    by_cases hm : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2
    · rw [if_pos hm, if_pos hm, hcharge,
        grayChargedTransportRoot_mass_of_charge hdeltaLe hvalid]
      exact (familyGrayChargeAtB.root hvalid j.isLt).2.2
    · rw [if_neg hm, if_neg hm]
      simp [grayChargeMass, grayMassOfCount]
  refine le_trans hstep ?_
  -- the guarded request sum is `4κ`·(the fibre son base)
  have hbridge : ((List.finRange p.slots.length).map fun j =>
      if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
        4 * halfAmplification q * getFamilyReq p.move j.val [] else
        0).sum =
      4 * halfAmplification q *
        grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 := by
    rw [grayTailSonBase_eq_sum_map, grayTailSlotEntries, List.map_ofFn,
      List.ofFn_eq_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    by_cases hm : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2
    · rw [if_pos hm]
      rw [if_pos hm]
      rfl
    · rw [if_neg hm]
      rw [if_neg hm, mul_zero]
  rw [hbridge]
  have hcall := (grayCallDepth_scale_bounds q e).2
  have hkpos : (0 : Rat) < halfAmplification q := halfAmplification_pos q
  calc 4 * halfAmplification q *
      grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 <=
      4 * halfAmplification q * dyadicScale (grayCallDepth q e) := by
        apply mul_le_mul_of_nonneg_left hbase
        positivity
    _ <= 4 * halfAmplification q *
        (dyadicScale e / (24 * halfAmplification q)) := by
        apply mul_le_mul_of_nonneg_left hcall
        positivity
    _ = dyadicScale e / 6 := by
        field_simp
        ring

/-- Owner fibre cells sit at the common final depth. -/
lemma grayChargedOwnerFibreV2_cell_length
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (z : Fin n × Fin (grayTailBranch q L a e))
    {u : Nat × BitString}
    (hu : u ∈ grayChargedOwnerFibreV2 hae p hp z) :
    u.2.length = e + grayTailNewLoss q L := by
  rw [grayChargedOwnerFibreV2, List.mem_flatMap] at hu
  obtain ⟨j, -, hu⟩ := hu
  by_cases hm : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2
  · rw [if_pos hm, mem_grayChargedTransportRoot] at hu
    obtain ⟨source, hsource, hu⟩ := hu
    rw [List.mem_map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    have hwlen : w.length =
        (e + grayTailNewLoss q L) - source.2.length :=
      (mem_allStrings _ _).mp hw
    have hslen : source.2.length = p.blockAnchor + L :=
      grayChargedRoundLocalChargeV2_cell_length hae p hp source
        (mem_grayChargeAtRoot.mp hsource).1
    have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
    simp only [List.length_append, hwlen, hslen]
    omega
  · rw [if_neg hm] at hu
    simp at hu

/-- Constant-depth lists convert their dyadic sum to the charge mass. -/
lemma grayCharged_constant_length_mass (D : Nat) (F : FamilyGrayCharge)
    (h : forall u, u ∈ F -> u.2.length = D) :
    (F.map fun u => dyadicScale u.2.length).sum = grayChargeMass D F := by
  have hsum : (F.map fun u => dyadicScale u.2.length).sum =
      (F.length : Rat) * dyadicScale D := by
    induction F with
    | nil => simp
    | cons u rest ih =>
        rw [List.map_cons, List.sum_cons,
          ih (fun w hw => h w (List.mem_cons_of_mem _ hw)),
          h u List.mem_cons_self, List.length_cons]
        push_cast
        ring
  rw [hsum, grayChargeMass, grayMassOfCount, dyadicScale]

/-- Charge mass is monotone along sublists. -/
lemma grayChargeMass_le_of_sublist (D : Nat) {F G : FamilyGrayCharge}
    (h : F.Sublist G) :
    grayChargeMass D F <= grayChargeMass D G := by
  have hF : grayChargeMass D F = (F.length : Rat) * dyadicScale D := by
    rw [grayChargeMass, grayMassOfCount, dyadicScale]
  have hG : grayChargeMass D G = (G.length : Rat) * dyadicScale D := by
    rw [grayChargeMass, grayMassOfCount, dyadicScale]
  rw [hF, hG]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.length_le)
    (dyadicScale_pos D).le

/-- The owner-aligned complement reserve source: the record whose cells are the reserve cylinder
with the owner window removed, carrying the `5 * eps / 6` mass certificate. -/
noncomputable def grayChargedComplementReserveSourceOfV2
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R)
    (owner : FamilyGrayCharge)
    (howner_len : forall u, u ∈ owner ->
      u.2.length = e + grayTailNewLoss q L)
    (howner_mass : grayChargeMass (e + grayTailNewLoss q L) owner <=
      dyadicScale e / 6) :
    GrayChargedReserveSourceV2 q L a e n U A sm where
  kind := kind
  coordinate := z
  source_lt := hsrc
  serviceTime := tau
  service_le := htau
  reserve := R
  reserve_witness := hres
  cells := grayChargedReserveComplementV2 z.1.val
    (e + grayTailNewLoss q L) R owner
  cells_owner := fun _ hz => grayChargedReserveComplementV2_owner hz
  cells_valid := by
    intro w hw
    have hw' := (grayChargedReserveComplementV2_sublist z.1.val
      (e + grayTailNewLoss q L) R owner).mem hw
    have hbase := (grayChargedLateReserveSourceOf hsm hae kind z hsrc
      tau htau R hres).cells_valid w hw'
    exact ⟨hbase.1, grayChargedV2_newGrayCell_coarsen hae hbase.2⟩
  cells_nodup := grayChargedReserveComplementV2_nodup _ _ _ _
  massContribution := dyadicScale e - dyadicScale e / 6
  mass_lower := by
    have hRlen : R.length = e := hres.1.1
    have hRD : R.length <= e + grayTailNewLoss q L := by
      rw [hRlen]
      exact Nat.le_add_right _ _
    have hmass := grayChargedReserveComplementV2_mass_ge z.1.val
      (e + grayTailNewLoss q L) R owner hRD
      (fun u hu => le_of_eq (howner_len u hu))
    rw [hRlen] at hmass
    rw [grayCharged_constant_length_mass (e + grayTailNewLoss q L) owner
      howner_len] at hmass
    linarith
  root_upper := by
    have hRlen : R.length = e := hres.1.1
    have hRD : R.length <= e + grayTailNewLoss q L := by
      rw [hRlen]
      exact Nat.le_add_right _ _
    refine le_trans (grayChargeMass_le_of_sublist _
      (grayChargedReserveComplementV2_sublist z.1.val
        (e + grayTailNewLoss q L) R owner)) ?_
    rw [grayChargedReserveCylinder_mass hRD, hRlen]
    exact dyadicScale_antitone hae

/-- The complement reserve source extracted at coordinate `z` is recorded at that coordinate. -/
@[simp] lemma grayChargedComplementReserveSourceOfV2_coordinate
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R)
    (owner : FamilyGrayCharge)
    (howner_len : forall u, u ∈ owner ->
      u.2.length = e + grayTailNewLoss q L)
    (howner_mass : grayChargeMass (e + grayTailNewLoss q L) owner <=
      dyadicScale e / 6) :
    (grayChargedComplementReserveSourceOfV2 hsm hae kind z hsrc tau htau R
      hres owner howner_len howner_mass).coordinate = z := rfl

/-- The cells of the complement reserve source at coordinate `z` are the reserve cylinder above
`R` with the owner charge removed. -/
@[simp] lemma grayChargedComplementReserveSourceOfV2_cells
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (kind : GrayChargedReserveKind)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hsrc : z.2.val < grayChargedSourceCount a e)
    (tau : Nat) (htau : tau <= U) (R : BitString)
    (hres : IsTailFamilyReserve e (grayTailBranch q L a e) A n z.1.val
      (sm tau) [z.2.val] R)
    (owner : FamilyGrayCharge)
    (howner_len : forall u, u ∈ owner ->
      u.2.length = e + grayTailNewLoss q L)
    (howner_mass : grayChargeMass (e + grayTailNewLoss q L) owner <=
      dyadicScale e / 6) :
    (grayChargedComplementReserveSourceOfV2 hsm hae kind z hsrc tau htau R
      hres owner howner_len howner_mass).cells =
      grayChargedReserveComplementV2 z.1.val (e + grayTailNewLoss q L) R
        owner := rfl

end Kolmogorov
