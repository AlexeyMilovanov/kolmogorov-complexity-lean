import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureLedgerBeta
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLeafBGeom
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureLedgerRequest
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRequestWindow

/-!
# Narrowing the three residuals of the charged closure leaf L5

This file collects the exact statements that remain between the verified
ledger modules and the public leaf `grayCharged_final_charge_transport`.
Everything below is proved outright; nothing is postulated.

* **Aggregate request split.**  `grayCharged_final_display_request_split`
  formalises the decomposition `Q = Q_calls + R` used by
  `grayCharged_aggregate_bounds`: the displayed aggregate of a finished
  charged controller is exactly the total of the accepted recursive-call root
  requests plus the raised-son remainder, and the remainder is bounded by
  `m₁ * eps / (6 * halfAmplification q)` where `m₁` counts the raised sources
  of the final frozen ledger.  This is the real controller decomposition; no
  whole-call cap is counted once per root and no per-root H3 is introduced.

* **Reserve half of the per-root cap.**  `grayCharged_perRoot_cap_of_halves`
  shows that `4 * halfAmplification q * req` for the recursive half and
  `2 * req` for the reserve half combine to exactly
  `4 * halfAmplification (q + 1) * req`, with no constant weakened; and
  `grayChargedReserveCharge_perRoot_cap_of_contrib` supplies the reserve half
  from the controller fact that each raised or resolved source son of a root
  contributes at least `dyadicScale e - dyadicScale e / (6 * halfAmplification q)`
  to that root's final displayed request.

* **Physical source/reserve collision control.**  Because a reserve is a
  depth-`e` cylinder while a local designated cell of an accepted round is
  strictly deeper, prefix comparability of the two collapses to the single
  equation `cell.take e = R`.  `grayChargedTransportRound_disjoint_reserveCylinder_of_take_ne`
  turns the whole `source_reserve_disjoint` field into that one equation, and
  `grayChargedStateAt_frozen_eps_lt` supplies the strict depth gap.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ## 1. The aggregate request split -/

/-- Summing the owner-indicator of one entry over all outer roots recovers the
entry's own displayed request. -/
lemma grayCharged_sum_owner_indicator {n b : Nat}
    (l : List (GrayTailSlot n b × ClientMove)) :
    ∑ i : Fin n, (l.map fun p => if p.1.1 = i then getReq p.2 [] else 0).sum =
      (l.map fun p => getReq p.2 []).sum := by
  classical
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      congr 1
      simp

/-- Summing all son bases of all roots recovers the total displayed request of
the ledger. -/
lemma grayTailSonBase_total_sum {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove)) :
    ∑ i : Fin n, ∑ c : Fin b, grayTailSonBase entries i c =
      (entries.map fun p => getReq p.2 []).sum := by
  rw [← grayCharged_sum_owner_indicator entries]
  exact Finset.sum_congr rfl fun i _ => grayTailSonBase_sum_over_sons entries i

/-- The total displayed request of the frozen ledger is the sum of the root
requests of the accepted recursive calls. -/
lemma grayTailFrozenEntries_total_sum {n b : Nat} (frozen : GrayTailFrozen n b) :
    ((grayTailFrozenEntries frozen).map fun p => getReq p.2 []).sum =
      ∑ k : Fin frozen.length,
        totalRootRequest (frozen[k.val]).slots.length (frozen[k.val]).move := by
  rw [grayTailFrozenEntries, sum_map_flatMap_rat, sum_map_eq_sum_finRange_rat]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [grayTailSlotEntries, sum_map_ofFn_rat, totalRootRequest]
  rfl

/-- The charged son request is the son base plus the raise increment. -/
lemma grayChargedSonRequest_eq_base_add_raise {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) (c : Fin b) :
    grayChargedSonRequest source threshold eps entries i c =
      grayTailSonBase entries i c +
        (if c.val < source ∧ threshold < grayTailSonBase entries i c then
          eps - grayTailSonBase entries i c else 0) := by
  unfold grayChargedSonRequest grayTailSonRequest
  by_cases hc : c.val < source
  · rw [ite_eq_left hc]
    by_cases hr : threshold < grayTailSonBase entries i c
    · simp only [hr, hc, and_self, ite_true]
      ring
    · simp [hr]
  · rw [ite_eq_right hc]
    simp [hc]

/-- **The exact aggregate request split.**  The displayed aggregate of a
charged ledger is the total request of its accepted recursive calls plus the
raised-son remainder. -/
theorem grayCharged_rootRequest_sum_split {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (entries : List (GrayTailSlot n b × ClientMove)) :
    ∑ i : Fin n, grayChargedRootRequest source threshold eps entries i =
      (entries.map fun p => getReq p.2 []).sum +
        ∑ z : Fin n × Fin b,
          (if z.2.val < source ∧ threshold < grayTailSonBase entries z.1 z.2 then
            eps - grayTailSonBase entries z.1 z.2 else 0) := by
  classical
  have hstep : ∑ i : Fin n, grayChargedRootRequest source threshold eps entries i =
      (∑ i : Fin n, ∑ c : Fin b, grayTailSonBase entries i c) +
        ∑ i : Fin n, ∑ c : Fin b,
          (if c.val < source ∧ threshold < grayTailSonBase entries i c then
            eps - grayTailSonBase entries i c else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [grayChargedRootRequest, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ =>
      grayChargedSonRequest_eq_base_add_raise source threshold eps entries i c
  rw [hstep, grayTailSonBase_total_sum]
  congr 1
  rw [Fintype.sum_prod_type]

/-- The raised-son remainder is bounded by one fine unit per raised source. -/
theorem grayCharged_raise_remainder_le {n b : Nat}
    (source : Nat) (eps r : Rat)
    (entries : List (GrayTailSlot n b × ClientMove)) :
    ∑ z : Fin n × Fin b,
        (if z.2.val < source ∧ eps - r < grayTailSonBase entries z.1 z.2 then
          eps - grayTailSonBase entries z.1 z.2 else 0) <=
      (((Finset.univ.filter fun z : Fin n × Fin b =>
          z.2.val < source ∧
            eps - r < grayTailSonBase entries z.1 z.2).card : Nat) : Rat) * r := by
  classical
  rw [← Finset.sum_filter]
  calc ∑ z ∈ Finset.univ.filter (fun z : Fin n × Fin b =>
        z.2.val < source ∧ eps - r < grayTailSonBase entries z.1 z.2),
          (eps - grayTailSonBase entries z.1 z.2)
      <= ∑ _z ∈ Finset.univ.filter (fun z : Fin n × Fin b =>
        z.2.val < source ∧ eps - r < grayTailSonBase entries z.1 z.2), r := by
        refine Finset.sum_le_sum ?_
        intro z hz
        have := (Finset.mem_filter.mp hz).2.2
        linarith
    _ = (((Finset.univ.filter fun z : Fin n × Fin b =>
          z.2.val < source ∧
            eps - r < grayTailSonBase entries z.1 z.2).card : Nat) : Rat) * r := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The charged threshold is exactly one fine unit below the coarse scale. -/
lemma grayChargedThreshold_eq (q e : Nat) :
    grayChargedThreshold q e =
      dyadicScale e - dyadicScale e / (6 * halfAmplification q) := rfl

/-- **Aggregate request split for the finished charged controller.**  The
displayed aggregate at a late horizon is exactly the total root request of the
accepted recursive calls plus a remainder audited by the raised sources. -/
theorem grayCharged_final_display_request_split
    {q L a e n U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hdone : (grayChargedRunState q L a e n sigma A sm U).phase = .done) :
    totalRootRequest n (grayChargedRunMove q L a e n sigma A sm U) =
        (∑ k : Fin (grayChargedRunState q L a e n sigma A sm U).core.frozen.length,
          totalRootRequest
            ((grayChargedRunState q L a e n sigma A sm U).core.frozen[k.val]).slots.length
            ((grayChargedRunState q L a e n sigma A sm U).core.frozen[k.val]).move) +
          (totalRootRequest n (grayChargedRunMove q L a e n sigma A sm U) -
            ∑ k : Fin (grayChargedRunState q L a e n sigma A sm U).core.frozen.length,
              totalRootRequest
                ((grayChargedRunState q L a e n sigma A sm U).core.frozen[k.val]).slots.length
                ((grayChargedRunState q L a e n sigma A sm U).core.frozen[k.val]).move) ∧
      totalRootRequest n (grayChargedRunMove q L a e n sigma A sm U) -
          (∑ k : Fin (grayChargedRunState q L a e n sigma A sm U).core.frozen.length,
            totalRootRequest
              ((grayChargedRunState q L a e n sigma A sm U).core.frozen[k.val]).slots.length
              ((grayChargedRunState q L a e n sigma A sm U).core.frozen[k.val]).move) <=
        ((grayChargedRaisedSources (grayChargedSourceCount a e)
            (grayChargedThreshold q e)
            (grayChargedRunState q L a e n sigma A sm U).core.frozen).card : Rat) *
          (dyadicScale e / (6 * halfAmplification q)) := by
  classical
  refine ⟨by ring, ?_⟩
  have hsplit := grayCharged_rootRequest_sum_split
    (n := n) (b := grayTailBranch q L a e) (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (dyadicScale e)
    (grayTailFrozenEntries (grayChargedRunState q L a e n sigma A sm U).core.frozen)
  have hdisplay : totalRootRequest n (grayChargedRunMove q L a e n sigma A sm U) =
      ∑ i : Fin n, grayChargedRootRequest (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (grayTailFrozenEntries
          (grayChargedRunState q L a e n sigma A sm U).core.frozen) i := by
    rw [totalRootRequest]
    exact Finset.sum_congr rfl fun i _ =>
      grayChargedRunMove_root_eq_of_done hdone i
  rw [hdisplay, hsplit, grayTailFrozenEntries_total_sum]
  have hrem := grayCharged_raise_remainder_le
    (n := n) (b := grayTailBranch q L a e) (grayChargedSourceCount a e)
    (dyadicScale e) (dyadicScale e / (6 * halfAmplification q))
    (grayTailFrozenEntries (grayChargedRunState q L a e n sigma A sm U).core.frozen)
  have hcard : (Finset.univ.filter fun z : Fin n × Fin (grayTailBranch q L a e) =>
      z.2.val < grayChargedSourceCount a e ∧
        dyadicScale e - dyadicScale e / (6 * halfAmplification q) <
          grayTailSonBase (grayTailFrozenEntries
            (grayChargedRunState q L a e n sigma A sm U).core.frozen) z.1 z.2) =
      grayChargedRaisedSources (grayChargedSourceCount a e)
        (grayChargedThreshold q e)
        (grayChargedRunState q L a e n sigma A sm U).core.frozen := by
    rfl
  rw [hcard] at hrem
  have hrem2 : ∑ z : Fin n × Fin (grayTailBranch q L a e),
      (if z.2.val < grayChargedSourceCount a e ∧
          grayChargedThreshold q e <
            grayTailSonBase (grayTailFrozenEntries
              (grayChargedRunState q L a e n sigma A sm U).core.frozen) z.1 z.2 then
        dyadicScale e -
          grayTailSonBase (grayTailFrozenEntries
            (grayChargedRunState q L a e n sigma A sm U).core.frozen) z.1 z.2
        else 0) <=
      ((grayChargedRaisedSources (grayChargedSourceCount a e)
          (grayChargedThreshold q e)
          (grayChargedRunState q L a e n sigma A sm U).core.frozen).card : Rat) *
        (dyadicScale e / (6 * halfAmplification q)) := hrem
  linarith

/-! ## 2. The reserve half of the per-root cap -/

/-- The two halves of the per-root cap combine to exactly the amplified
constant of the next rung; no constant is weakened. -/
theorem grayCharged_perRoot_cap_of_halves {q : Nat} {req Ms Mr Mf : Rat}
    (hf : Mf = Ms + Mr)
    (hs : Ms <= 4 * halfAmplification q * req)
    (hr : Mr <= 2 * req) :
    Mf <= 4 * halfAmplification (q + 1) * req := by
  have hexp : 4 * halfAmplification (q + 1) * req =
      4 * halfAmplification q * req + 2 * req := by
    unfold halfAmplification
    push_cast
    ring
  rw [hf, hexp]
  linarith

/-- If `m` sources of a root each display at least the controller threshold,
the coarse mass they carry is at most twice the root's displayed request. -/
theorem grayCharged_reserve_count_mass_le {q m : Nat} {eps req : Rat}
    (heps : 0 < eps)
    (hcontrib : (m : Rat) * (eps - eps / (6 * halfAmplification q)) <= req) :
    (m : Rat) * eps <= 2 * req := by
  have hk : (1 : Rat) <= halfAmplification q := by
    unfold halfAmplification
    have : (0 : Rat) <= (q : Rat) / 2 := by positivity
    linarith
  have hkpos : (0 : Rat) < halfAmplification q := lt_of_lt_of_le one_pos hk
  have hm : (0 : Rat) <= (m : Rat) := Nat.cast_nonneg m
  have hdiv : eps / (6 * halfAmplification q) <= eps / 2 := by
    apply div_le_div_of_nonneg_left heps.le (by norm_num)
    linarith
  nlinarith

/-- **Reserve half of the H5 per-root cap.**  Assuming every reserve of a root
carries at most one coarse unit and that the reserves of that root each force
at least the controller threshold into its displayed request, the reserve mass
at that root is at most twice the displayed request. -/
theorem grayChargedReserveCharge_perRoot_cap_of_contrib
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) (i : Nat)
    {req : Rat}
    (hmass : forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e)
    (hcontrib :
      (((reserves.countP fun r => decide (r.coordinate.1.val = i)) : Nat) : Rat) *
          (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) <= req) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveCharge reserves)) <= 2 * req := by
  have hcount : grayChargeMass (e + grayTailNewLoss q L)
      (grayChargeAtRoot i (grayChargedReserveCharge reserves)) <=
      (((reserves.countP fun r => decide (r.coordinate.1.val = i)) : Nat) : Rat) *
        dyadicScale e := by
    rw [grayChargeMass_grayChargeAtRoot_reserveCharge,
      ← sum_map_ite_const_rat reserves (fun r => decide (r.coordinate.1.val = i))
        (dyadicScale e)]
    refine List.sum_le_sum ?_
    intro r hr
    by_cases h : r.coordinate.1.val = i
    · simp only [h, decide_true, ite_true]
      exact hmass r hr
    · simp [h]
  exact le_trans hcount
    (grayCharged_reserve_count_mass_le (q := q) (dyadicScale_pos e) hcontrib)

/-! ## 3. Physical source/reserve collision control -/

/-- A strictly deeper cell can meet a reserve cylinder only through its coarse
trace. -/
lemma grayCharged_incomparable_of_take_ne {u R : BitString} {d : Nat}
    (hR : R.length = d) (hlt : d <= u.length) (hne : u.take d ≠ R) :
    ¬ (u <+: R ∨ R <+: u) := by
  rintro (h | h)
  · exact hne (by
      have hlen : u.length <= d := by
        rw [← hR]
        exact h.length_le
      have : u.length = d := le_antisymm hlen hlt
      have hu : u.take d = u := by
        rw [List.take_of_length_le (le_of_eq this)]
      rw [hu]
      exact h.eq_of_length (by omega))
  · obtain ⟨t, rfl⟩ := h
    exact hne (by rw [List.take_left' hR])

/-- One owner fibre never meets a reserve cylinder over an incomparable
base. -/
lemma grayChargedTransportRoot_disjoint_reserveCylinder
    {delta owner root i : Nat} {G : FamilyGrayCharge} {R : BitString}
    (hinc : forall u, u ∈ grayChargeAtRoot root G ->
      ¬ (u.2 <+: R ∨ R <+: u.2)) :
    List.Disjoint ((grayChargedTransportRoot delta owner root G).map Prod.snd)
      ((grayChargedReserveCylinder i delta R).map Prod.snd) := by
  intro x hx hx'
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  obtain ⟨source, hsource, hzc⟩ := mem_grayChargedTransportRoot.mp hz
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hzc
  rw [grayChargedReserveCylinder_snd] at hx'
  obtain ⟨s, -, hs⟩ := List.mem_map.mp hx'
  exact hinc source hsource
    (List.prefix_or_prefix_of_prefix (List.prefix_append source.2 w)
      ⟨s, hs⟩)

/-- **The residual of `source_reserve_disjoint`, reduced to one equation.**
Since a reserve is a depth-`d` cylinder while every local designated cell of an
accepted round is at least that deep, the whole disjointness of a transported
round against a reserve cylinder follows from the single statement that no
local cell has the reserve as its depth-`d` trace. -/
theorem grayChargedTransportRound_disjoint_reserveCylinder_of_take_ne
    {n b D i d : Nat} {slots : List (GrayTailSlot n b)}
    {G : FamilyGrayCharge} {R : BitString}
    (hR : R.length = d)
    (hlen : forall u, u ∈ G -> d <= u.2.length)
    (hne : forall u, u ∈ G -> u.2.take d ≠ R) :
    List.Disjoint ((grayChargedTransportRound D slots G).map Prod.snd)
      ((grayChargedReserveCylinder i D R).map Prod.snd) :=
  grayChargedTransportRound_disjoint_reserveCylinder
    (fun u hu => grayCharged_incomparable_of_take_ne hR (hlen u hu) (hne u hu))

/-- Every accepted round of the charged controller lives strictly below the
coarse scale `e`, so its local cells are strictly longer than a reserve. -/
lemma grayChargedStateAt_frozen_eps_lt
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {p : GrayTailRound n b}
    (_hp : p ∈ (grayChargedStateAt (n := n) (b := b)
      q L a e sigma A sm t).core.frozen)
    (hfine : grayCallDepth q e <= p.epsDepth) :
    e < p.epsDepth := by
  have h5 := grayCallDepth_ge_add_five q e
  omega
/-- If the charged strategy does not win with positive unserved mass, then after a final replay
there is a later time `U`, displaying the same move as `T`, at which every raised or
server-resolved source of the replay owns a reserve: the reserves have pairwise distinct
coordinates and distinct cells, each carries mass exactly `dyadicScale e` on the cylinder of
its coordinate, and their total mass is the number of those sources times `dyadicScale e`. -/
theorem grayCharged_late_reserve_family_unit
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositive q L a e n sigma A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T) :
    exists (U : Nat) (reserves : List (GrayChargedReserveSource q L a e n U A sm)),
      T + 1 <= U ∧
      grayChargedRunMove q L a e n sigma A sm U =
        grayChargedRunMove q L a e n sigma A sm T ∧
      (forall z, z ∈ grayChargedReplayRaisedSources replay ∪
          grayChargedReplayServerResolvedSources replay ->
        exists r, r ∈ reserves ∧ r.coordinate = z) ∧
      ((grayChargedReserveCharge reserves).map Prod.snd).Nodup ∧
      grayChargeMass (e + grayTailNewLoss q L) (grayChargedReserveCharge reserves) =
        ((grayChargedReplayRaisedSources replay ∪
          grayChargedReplayServerResolvedSources replay).card : Rat) *
          dyadicScale e ∧
      (reserves.map fun r => r.coordinate).Nodup ∧
      (forall r, r ∈ reserves ->
        grayChargeMass (e + grayTailNewLoss q L) r.cells = dyadicScale e) ∧
      (forall r, r ∈ reserves -> r.cells =
        grayChargedReserveCylinder r.coordinate.1.val (e + grayTailNewLoss q L)
          r.reserve) := by
  classical
  obtain ⟨U, tau, res, hU, hmove, hall⟩ :=
    grayChargedReplay_resolved_late_reserves hsm hnotpos replay
  set S := grayChargedReplayRaisedSources replay ∪
    grayChargedReplayServerResolvedSources replay with hSdef
  refine ⟨U, S.toList.attach.map fun zz =>
    grayChargedLateReserveSourceOf hsm hae
      (if zz.1 ∈ grayChargedReplayRaisedSources replay then
        GrayChargedReserveKind.thresholdRaised
      else GrayChargedReserveKind.serverResolved)
      zz.1 (hall zz.1 (Finset.mem_toList.mp zz.2)).2.1
      (tau zz.1) (hall zz.1 (Finset.mem_toList.mp zz.2)).1
      (res zz.1) (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2,
    hU, hmove, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨_, List.mem_map.mpr
      ⟨⟨z, Finset.mem_toList.mpr hz⟩, List.mem_attach _ _, rfl⟩, rfl⟩
  · rw [grayChargedReserveCharge, List.map_flatMap, List.flatMap_map]
    refine List.nodup_flatMap.2 ⟨?_, ?_⟩
    · intro zz _
      exact grayChargedReserveCylinder_nodup _ _ _
    · refine List.Pairwise.imp ?_ (List.nodup_attach.mpr (Finset.nodup_toList S))
      intro zz zz' hne
      have hcoord : zz.1 ≠ zz'.1 := fun h => hne (Subtype.ext h)
      have hpair : ¬ (zz.1.1.val = zz'.1.1.val ∧ zz.1.2.val = zz'.1.2.val) := by
        rintro ⟨h1, h2⟩
        exact hcoord (Prod.ext (Fin.ext h1) (Fin.ext h2))
      have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
      have hR' := (hall zz'.1 (Finset.mem_toList.mp zz'.2)).2.2
      have hne' : res zz.1 ≠ res zz'.1 :=
        isTailFamilyReserve_ne_of_ne_coordinate hsm zz.1.1.isLt zz'.1.1.isLt
          zz.1.2.isLt zz'.1.2.isLt hR hR' hpair
      exact grayChargedReserveCylinder_disjoint hR.1.1 hR'.1.1 hne'
  · rw [grayChargedReserveCharge, grayChargeMass_flatMap]
    refine (List.sum_eq_length_nsmul _ (dyadicScale e) ?_).trans ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
      have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
      simp only [grayChargedLateReserveSourceOf_cells]
      rw [grayChargedReserveCylinder_mass
        (by rw [hR.1.1]; exact Nat.le_add_right _ _), hR.1.1]
    · simp [nsmul_eq_mul]
  · rw [List.map_map]
    refine List.Nodup.map ?_ (List.nodup_attach.mpr (Finset.nodup_toList S))
    intro zz zz' h
    exact Subtype.ext h
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    have hR := (hall zz.1 (Finset.mem_toList.mp zz.2)).2.2
    simp only [grayChargedLateReserveSourceOf_cells]
    rw [grayChargedReserveCylinder_mass
      (by rw [hR.1.1]; exact Nat.le_add_right _ _), hR.1.1]
  · intro r hr
    obtain ⟨zz, -, rfl⟩ := List.mem_map.mp hr
    rfl

/-! ## 5. The reserve half of the per-root cap -/

/-- The reserve mass at one root, when each block is a single coarse
cylinder. -/
lemma grayChargedReserveCharge_perRoot_mass_le_of_unit
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) (i : Nat)
    (hunit : forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveCharge reserves)) <=
      ((reserves.countP fun r => decide (r.coordinate.1.val = i) : Nat) : Rat) *
        dyadicScale e := by
  classical
  rw [grayChargeMass_grayChargeAtRoot_reserveCharge,
    ← sum_map_ite_const_rat reserves (fun r => decide (r.coordinate.1.val = i))
      (dyadicScale e)]
  refine List.sum_le_sum ?_
  intro r hr
  by_cases h : r.coordinate.1.val = i
  · simp only [h, decide_true, ite_true]
    exact hunit r hr
  · simp [h]

/-- At most one reserve per source son of a given root, hence at most
`grayChargedSourceCount a e` reserves at that root. -/
lemma grayChargedReserve_countP_le_sourceCount
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) (i : Nat)
    (hnodup : (reserves.map fun r => r.coordinate).Nodup) :
    (reserves.countP fun r => decide (r.coordinate.1.val = i)) <=
      grayChargedSourceCount a e := by
  classical
  set l := reserves.filter (fun r => decide (r.coordinate.1.val = i)) with hl
  have hcount : (reserves.countP fun r => decide (r.coordinate.1.val = i)) =
      l.length := by
    rw [hl, List.countP_eq_length_filter]
  have hlsub : l.Sublist reserves := by
    rw [hl]; exact List.filter_sublist
  have hlnodup : (l.map fun r => r.coordinate).Nodup :=
    hnodup.sublist (hlsub.map _)
  have hmapnodup : (l.map fun r => r.coordinate.2.val).Nodup := by
    have hinj : ∀ r ∈ l, ∀ r' ∈ l,
        r.coordinate.2.val = r'.coordinate.2.val ->
        r.coordinate = r'.coordinate := by
      intro r hr r' hr' h
      have h1 : r.coordinate.1.val = i := by
        have := List.of_mem_filter hr
        simpa using this
      have h1' : r'.coordinate.1.val = i := by
        have := List.of_mem_filter hr'
        simpa using this
      exact Prod.ext (Fin.ext (by rw [h1, h1'])) (Fin.ext h)
    rw [show (l.map fun r => r.coordinate.2.val) =
        (l.map fun r => r.coordinate).map (fun z => z.2.val) by
      rw [List.map_map]; rfl]
    refine List.Nodup.map_on ?_ hlnodup
    intro z hz z' hz' h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hz'
    exact hinj r hr r' hr' h
  have hsub : (l.map fun r => r.coordinate.2.val).toFinset ⊆
      Finset.range (grayChargedSourceCount a e) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact Finset.mem_range.mpr r.source_lt
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hmapnodup, List.length_map,
    Finset.card_range] at hcard
  omega

/-- **Reserve half of the per-root cap.**  With one coarse cylinder per
distinct source son of a root, the reserve mass displayed at that root is at
most one root scale, hence at most twice the root's displayed request. -/
theorem grayChargedReserveCharge_perRoot_cap_of_window
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm)) (i : Nat)
    (hae : a <= e)
    (hunit : forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e)
    (hnodup : (reserves.map fun r => r.coordinate).Nodup)
    {req : Rat} (hreq : dyadicScale a / 2 <= req) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveCharge reserves)) <=
      2 * req := by
  have hpos : (0 : Rat) < dyadicScale e := by unfold dyadicScale; positivity
  have hstep := grayChargedReserveCharge_perRoot_mass_le_of_unit reserves i hunit
  have hcount := grayChargedReserve_countP_le_sourceCount reserves i hnodup
  have hcast : ((reserves.countP fun r =>
      decide (r.coordinate.1.val = i) : Nat) : Rat) <=
      ((grayChargedSourceCount a e : Nat) : Rat) := by exact_mod_cast hcount
  have hmul : ((reserves.countP fun r =>
      decide (r.coordinate.1.val = i) : Nat) : Rat) * dyadicScale e <=
      ((grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e :=
    mul_le_mul_of_nonneg_right hcast hpos.le
  have hscale : ((grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e =
      dyadicScale a := by
    rw [dyadicScale_eq_pow_sub_mul (a := a) (e := e) hae]
    rfl
  rw [hscale] at hmul
  linarith

/-! ## 6. The aggregate request bound

The exact arithmetic that turns the two ledger bounds into the
`aggregate_request` field.  Nothing is weakened: the recursive half supplies
`halfAmplification q` times the accepted call requests, the reserve half
supplies one coarse unit per resolved source, and the raised-son remainder is
audited by the raised-source count. -/

/-- **The aggregate request field, in arithmetic form.**  If the displayed
aggregate splits as `Q = Q_calls + R` with an audited remainder, the recursive
ledger carries `halfAmplification q * Q_calls`, the reserve ledger carries one
coarse unit per resolved source, and three quarters of the sources are
resolved, then the total mass meets the amplified aggregate request target of
the next rung. -/
theorem grayCharged_aggregate_request_arith
    {q a e n m1 card : Nat} {Q Qcalls Rem massS massR massF : Rat}
    (hae : a <= e)
    (hQ : Q = Qcalls + Rem)
    (hRem : Rem <= (m1 : Rat) * (dyadicScale e / (6 * halfAmplification q)))
    (hm1 : m1 <= n * grayChargedSourceCount a e)
    (hQupper : Q <= (n : Rat) * dyadicScale a)
    (hthree : 3 * (n * grayChargedSourceCount a e) <= 4 * card)
    (hS : halfAmplification q * Qcalls <= massS)
    (hR : massR = (card : Rat) * dyadicScale e)
    (hF : massF = massS + massR) :
    halfAmplification (q + 1) * Q <= massF := by
  have hpos : (0 : Rat) < dyadicScale e := by unfold dyadicScale; positivity
  have hkpos : (1 : Rat) <= halfAmplification q := by
    have hq : (0 : Rat) <= (q : Rat) / 2 := by positivity
    unfold halfAmplification; linarith
  have hk' : halfAmplification (q + 1) = halfAmplification q + 1 / 2 := by
    unfold halfAmplification; push_cast; ring
  -- the audited remainder, multiplied by the recursive amplification
  have hremk : halfAmplification q * Rem <= (m1 : Rat) * dyadicScale e / 6 := by
    have hmul := mul_le_mul_of_nonneg_left hRem (by linarith : (0:Rat) <= halfAmplification q)
    refine le_trans hmul (le_of_eq ?_)
    field_simp
  have hm1card : (m1 : Rat) <=
      (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat) := by
    exact_mod_cast hm1
  -- the coarse count of all sources
  have hscale : ((grayChargedSourceCount a e : Nat) : Rat) * dyadicScale e =
      dyadicScale a := by
    rw [dyadicScale_eq_pow_sub_mul (a := a) (e := e) hae]
    rfl
  have hthreeQ : 3 * ((n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat)) <=
      4 * (card : Rat) := by exact_mod_cast hthree
  have hQN : Q <= (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat) *
      dyadicScale e := by
    rw [mul_assoc, hscale]; exact hQupper
  set N : Rat := (n : Rat) * ((grayChargedSourceCount a e : Nat) : Rat) with hN
  have hNnonneg : (0 : Rat) <= N := by
    rw [hN]; positivity
  -- assemble
  have hremN : halfAmplification q * Rem <= N * dyadicScale e / 6 := by
    have hstep : (m1 : Rat) * dyadicScale e <= N * dyadicScale e :=
      mul_le_mul_of_nonneg_right (by rw [hN]; exact hm1card) hpos.le
    linarith
  have hkey : (1 / 2 : Rat) * Q + halfAmplification q * Rem <=
      (card : Rat) * dyadicScale e := by
    have h1 : (1 / 2 : Rat) * Q <= (1 / 2 : Rat) * (N * dyadicScale e) := by
      nlinarith [hQN]
    have h2 : (3 : Rat) * N <= 4 * (card : Rat) := hthreeQ
    nlinarith [hpos, hremN, h1, h2]
  rw [hF, hR, hk', hQ]
  nlinarith [hS, hkey, hQ]

/-! ## 9. The fine half of the source ledger

Per plan §XII.5 the final charge consists of the advantage-round sources and
the reserve charges only; the spend rounds enter the ledger through their
displayed requests and the resolution counting, never through their own gray.
The aggregation below runs the (threaded) round-source machinery over the
fine rounds of the final replay — those at or above the call depth. -/

/-- The fine (advantage) rounds of the final replay, as a filtered index
list over the frozen rounds. -/
noncomputable def grayChargedFineIndices
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (T : Nat) :
    List (Fin (grayChargedRunState q L a e n sigma A sm
      (T + 1)).core.frozen.length) :=
  (List.finRange _).filter fun i =>
    decide (grayCallDepth q e <=
      ((grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen[i.val]).epsDepth)

/-- A fine index points at a frozen round whose epsilon depth is at least the call depth
`grayCallDepth q e`. -/
lemma grayChargedFineIndices_fine
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {i : Fin (grayChargedRunState q L a e n sigma A sm
      (T + 1)).core.frozen.length}
    (hi : i ∈ grayChargedFineIndices q L a e n sigma A sm T) :
    grayCallDepth q e <=
      ((grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen[i.val]).epsDepth := by
  have h := (List.mem_filter.mp hi).2
  exact of_decide_eq_true h

/-- The fine half of the recursive source ledger. -/
noncomputable def grayChargedFineSources
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (phase : Nat -> GrayChargedSourcePhase) :
    List (GrayChargedChargeSource q L a e n A
      (grayChargedRunMove q L a e n sigma A sm U) (sm U)) :=
  (grayChargedFineIndices q L a e n sigma A sm T).attach.flatMap
    fun i => grayChargedRoundSources hsm replay hU
      (List.getElem_mem i.val.isLt) hae
      (grayChargedFineIndices_fine i.property) (phase i.val.val)

/-- The charge carried by the fine sources is the transported round charge of every fine frozen
round, summed over the fine indices. -/
lemma grayChargedFineSources_charge_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (phase : Nat -> GrayChargedSourcePhase) :
    grayChargedSourceCharge (grayChargedFineSources hsm replay hU hae phase) =
      (grayChargedFineIndices q L a e n sigma A sm T).attach.flatMap
        fun i => grayChargedTransportRound (e + grayTailNewLoss q L)
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val.val]).slots
          (grayChargedLocalChargeOfGoal
            (grayChargedStateAt_frozen_goal (List.getElem_mem i.val.isLt)
              hae (grayChargedFineIndices_fine i.property))) := by
  rw [grayChargedFineSources, grayChargedSourceCharge_flatMap]
  refine List.flatMap_congr ?_
  intro i _
  exact grayChargedSourceCharge_roundSources hsm replay hU
    (List.getElem_mem i.val.isLt) hae
    (grayChargedFineIndices_fine i.property) (phase i.val.val)

/-- The cells charged by the fine sources are pairwise distinct. -/
lemma grayChargedFineSources_cells_nodup
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (phase : Nat -> GrayChargedSourcePhase) :
    ((grayChargedSourceCharge
      (grayChargedFineSources hsm replay hU hae phase)).map Prod.snd).Nodup := by
  rw [grayChargedFineSources_charge_eq, List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro i _
    exact grayChargedTransportRound_nodup_of_charge
      (grayChargedLocalChargeOfGoal_valid
        (grayChargedStateAt_frozen_goal (List.getElem_mem i.val.isLt) hae
          (grayChargedFineIndices_fine i.property)))
  · have hpw0 : (grayChargedFineIndices q L a e n sigma A sm T).Pairwise
        (· < ·) :=
      List.Pairwise.filter _ (List.pairwise_lt_finRange _)
    have hpw : (grayChargedFineIndices q L a e n sigma A sm T).attach.Pairwise
        (fun x y => x.val < y.val) := by
      have hmapval :
          ((grayChargedFineIndices q L a e n sigma A sm T).attach.map
            Subtype.val) =
            grayChargedFineIndices q L a e n sigma A sm T :=
        List.attach_map_subtype_val _
      have hiff := List.pairwise_map
        (l := (grayChargedFineIndices q L a e n sigma A sm T).attach)
        (f := Subtype.val) (R := (· < ·))
      rw [hmapval] at hiff
      exact hiff.mp hpw0
    refine List.Pairwise.imp ?_ hpw
    intro i j hij
    by_cases hslots :
        (grayChargedRunState q L a e n sigma A sm
          (T + 1)).core.frozen[i.val.val].slots = []
    · simp [Function.onFun, grayChargedTransportRound, hslots]
    · refine grayChargedTransportRound_disjoint_of_incomparable_bases ?_
      intro u hu v hv
      exact grayCharged_frozen_local_cells_incomparable hsm
        i.val.isLt j.val.isLt hij hae
        (grayChargedFineIndices_fine i.property)
        (grayChargedFineIndices_fine j.property) hu hv

/-- The mass of the fine-source charge is at least `halfAmplification q` times the total root
request of the fine frozen rounds. -/
lemma grayChargedFineSources_request_lower
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (phase : Nat -> GrayChargedSourcePhase) :
    halfAmplification q *
        ((grayChargedFineIndices q L a e n sigma A sm T).map
          fun i => totalRootRequest
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[i.val]).slots.length
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[i.val]).move).sum <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge
          (grayChargedFineSources hsm replay hU hae phase)) := by
  rw [grayChargedFineSources, grayChargedSourceCharge_flatMap,
    grayChargeMass_flatMap]
  have hconv :
      ((grayChargedFineIndices q L a e n sigma A sm T).map
        fun i => totalRootRequest
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val]).slots.length
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val]).move) =
      ((grayChargedFineIndices q L a e n sigma A sm T).attach.map
        fun i => totalRootRequest
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val.val]).slots.length
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val.val]).move) := by
    conv_lhs => rw [← List.attach_map_subtype_val
      (grayChargedFineIndices q L a e n sigma A sm T)]
    rw [List.map_map]
    rfl
  rw [hconv]
  have hdistrib :
      halfAmplification q *
        ((grayChargedFineIndices q L a e n sigma A sm T).attach.map
          fun i => totalRootRequest
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[i.val.val]).slots.length
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[i.val.val]).move).sum =
      ((grayChargedFineIndices q L a e n sigma A sm T).attach.map
        fun i => halfAmplification q * totalRootRequest
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val.val]).slots.length
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val.val]).move).sum := by
    induction (grayChargedFineIndices q L a e n sigma A sm T).attach with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, mul_add, ih]
  rw [hdistrib]
  refine List.sum_le_sum ?_
  intro i _
  exact grayChargedRoundSources_request_lower hsm replay hU
    (List.getElem_mem i.val.isLt) hae
    (grayChargedFineIndices_fine i.property) (phase i.val.val)

/-! ## 7. Residual 1, reduced to one elementary geometric statement

The `source_reserve_disjoint` field of `GrayChargedChargeProvenance` is an
assertion about physical cells of the *whole* flattened ledgers.  The lemmas
above collapse it, without any loss, to the statement that no local designated
gray cell of an accepted round has a selected reserve as its depth-`e` trace.
This is the exact verbatim residual of the charged closure leaf L5. -/

/-- A local designated gray cell of an accepted round is strictly finer than a
reserve, hence at least as long. -/
lemma grayCharged_localCharge_length_ge
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : List.Mem p (grayChargedRunState q L a e n sigma A sm t).core.frozen)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    {u : Nat × BitString}
    (hu : u ∈ grayChargedLocalChargeOfGoal
      (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)) :
    e <= u.2.length := by
  have hcell := familyGrayChargeAtB.cell
    (grayChargedLocalChargeOfGoal_valid
      (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)) hu
  have hlen : u.2.length = p.epsDepth + L := (mem_newGrayCellsList.mp hcell.2).1
  have heps : e < p.epsDepth :=
    grayChargedStateAt_frozen_eps_lt (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) (t := t) hp hfine
  omega

/-- **Foreign-slot freshness of the charged local charge.**  A designated local
gray cell of an accepted round is never traced, at depth `e`, onto a reserve of
a *different* source son, provided the reserve is observed no earlier than the
round.  This is the charged form of `grayTail_reserve_fresh_of_slot_ne_before`,
and it removes every cross-slot collision from residual 1. -/
theorem grayCharged_localCharge_fresh_of_slot_ne
    {q L a e n t tau : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : List.Mem p (grayChargedRunState q L a e n sigma A sm t).core.frozen)
    {i : Fin n} {c : Fin (grayTailBranch q L a e)} {R : BitString}
    (hR : IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val
      (sm tau) [c.val] R)
    (hpt : p.serverTime <= tau)
    (hae : a <= e)
    (hfine : grayCallDepth q e <= p.epsDepth)
    {u : Nat × BitString}
    (hu : u ∈ grayChargedLocalChargeOfGoal
      (grayChargedStateAt_frozen_goal (L := L) hp hae hfine))
    (hjne : forall hlt : u.1 < p.slots.length,
      (p.slots.get ⟨u.1, hlt⟩).1 ≠ i ∨ (p.slots.get ⟨u.1, hlt⟩).2.1 ≠ c) :
    u.2.take e ≠ R := by
  intro heq
  have hvalid := grayChargedLocalChargeOfGoal_valid
    (grayChargedStateAt_frozen_goal (L := L) hp hae hfine)
  obtain ⟨hlt, hmem⟩ := familyGrayChargeAtB.cell hvalid hu
  obtain ⟨-, ⟨d, hd, hcomp⟩, -⟩ := mem_newGrayCellsList.mp hmem
  have heps : e < p.epsDepth :=
    grayChargedStateAt_frozen_eps_lt (q := q) (L := L) (a := a) (e := e)
      (sigma := sigma) (A := A) (sm := sm) (t := t) hp hfine
  have hRP : R <+: u.2.take p.epsDepth := by
    have hcut : (u.2.take p.epsDepth).take e = u.2.take e := by
      rw [List.take_take]
      congr 1
      omega
    rw [← heq, ← hcut]
    exact List.take_prefix _ _
  exact grayTail_reserve_fresh_of_slot_ne_before (L := L) hsm hR p
      ⟨u.1, hlt⟩ hpt (hjne hlt) hd
    (prefixComparable_of_prefix_of_prefixComparable hRP hcomp)

/-- **Residual 1, in its exact reduced form.**  If no local designated gray
cell of an accepted round of the final replay has a selected reserve as its
depth-`e` trace, then the flattened recursive ledger and the flattened reserve
ledger are physically disjoint. -/
theorem grayCharged_source_reserve_disjoint_of_take_ne
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase)
    (reserves : List (GrayChargedReserveSource q L a e n U A sm))
    (hcells : forall r, r ∈ reserves -> r.cells =
      grayChargedReserveCylinder r.coordinate.1.val (e + grayTailNewLoss q L)
        r.reserve)
    (hne : forall k : Fin (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen.length,
      forall u, u ∈ grayChargedLocalChargeOfGoal
          (grayChargedStateAt_frozen_goal (L := L) (List.getElem_mem k.isLt)
            hae (hfineAll _ (List.getElem_mem k.isLt))) ->
        forall r, r ∈ reserves -> u.2.take e ≠ r.reserve) :
    List.Disjoint
      ((grayChargedSourceCharge
        (grayChargedFrozenSources hsm replay hU hae hfineAll phase)).map Prod.snd)
      ((grayChargedReserveCharge reserves).map Prod.snd) := by
  rw [grayChargedFrozenSources_charge_eq]
  intro x hx hx'
  rw [List.map_flatMap, List.mem_flatMap] at hx
  obtain ⟨k, -, hxk⟩ := hx
  rw [grayChargedReserveCharge, List.map_flatMap, List.mem_flatMap] at hx'
  obtain ⟨r, hr, hxr⟩ := hx'
  rw [hcells r hr] at hxr
  exact grayChargedTransportRound_disjoint_reserveCylinder_of_take_ne
    (d := e) r.reserve_witness.1.1
    (fun u hu => grayCharged_localCharge_length_ge
      (List.getElem_mem k.isLt) hae
      (hfineAll _ (List.getElem_mem k.isLt)) hu)
    (fun u hu => hne k u hu r hr) hxk hxr

/-! ## 8. The conditional assembly of the charged late charge witness

Residuals 2 and 3 are closed above.  Residual 1 survives only in the
own-source-son configuration, isolated as the single predicate
`GrayChargedReserveFreshness`; every cross-slot configuration is discharged by
`grayCharged_localCharge_fresh_of_slot_ne`.  The theorem below assembles the
complete `GrayChargedLateChargeWitness` from that one predicate, using the real
controller definitions throughout.  Nothing else is missing from the charged
closure leaf L5. -/

/-- The only configuration in which a designated local gray cell of an accepted
round can still meet a reserve of the son `(i, c)`: either the cell sits at the
reserve's *own* source son, or the reserve was observed strictly before the
round was frozen.  Every other configuration is excluded outright by
`grayCharged_localCharge_fresh_of_slot_ne`. -/
def GrayChargedOwnSonCollision {n b : Nat} (p : GrayTailRound n b)
    (u : Nat × BitString) (i : Fin n) (c : Fin b) (tau : Nat) : Prop :=
  (forall hlt : u.1 < p.slots.length,
    (p.slots.get ⟨u.1, hlt⟩).1 = i ∧ (p.slots.get ⟨u.1, hlt⟩).2.1 = c) ∨
      tau < p.serverTime

/-- **The exact remaining hypothesis of the charged closure leaf L5.**  For the
own-son configurations only, no designated local gray cell of an accepted round
of the final replay traces, at depth `e`, onto a family reserve of that son. -/
def GrayChargedReserveFreshness (q L a e n T : Nat)
    (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth) : Prop :=
  forall k : Fin (grayChargedRunState q L a e n sigma A sm
      (T + 1)).core.frozen.length,
    forall u, u ∈ grayChargedLocalChargeOfGoal
        (grayChargedStateAt_frozen_goal (L := L) (List.getElem_mem k.isLt)
          hae (hfineAll _ (List.getElem_mem k.isLt))) ->
      forall (i : Fin n) (c : Fin (grayTailBranch q L a e)) (tau : Nat)
          (R : BitString),
        IsTailFamilyReserve e (grayTailBranch q L a e) A n i.val
            (sm tau) [c.val] R ->
        GrayChargedOwnSonCollision
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[k.val]) u i c tau ->
          u.2.take e ≠ R

/-- The raised sources of any frozen ledger form a subset of the source
slab, hence never outnumber the whole source population. -/
lemma grayChargedRaisedSources_card_le {q L a e n : Nat}
    (frozen : GrayTailFrozen n (grayTailBranch q L a e)) (threshold : Rat) :
    (grayChargedRaisedSources (grayChargedSourceCount a e)
        threshold frozen).card <=
      n * grayChargedSourceCount a e := by
  classical
  have hsub : grayChargedRaisedSources (grayChargedSourceCount a e)
      threshold frozen ⊆
      Finset.univ.filter fun z : Fin n × Fin (grayTailBranch q L a e) =>
        z.2.val < grayChargedSourceCount a e := fun z hz =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ z,
      grayChargedRaisedSources_source_lt hz⟩
  have hcard := Finset.card_le_card hsub
  rwa [grayCharged_card_source_slab n (grayTailBranch q L a e)
    (grayChargedSourceCount a e)
    (grayChargedSourceCount_le_grayTailBranch q L a e)] at hcard

/-- The total accepted recursive call request only depends on the frozen
ledger. -/
lemma grayTailFrozen_callRequest_sum_congr {n b : Nat}
    {f g : GrayTailFrozen n b} (h : f = g) :
    ∑ k : Fin f.length,
        totalRootRequest (f[k.val]).slots.length (f[k.val]).move =
      ∑ k : Fin g.length,
        totalRootRequest (g[k.val]).slots.length (g[k.val]).move := by
  subst h; rfl

end Kolmogorov
