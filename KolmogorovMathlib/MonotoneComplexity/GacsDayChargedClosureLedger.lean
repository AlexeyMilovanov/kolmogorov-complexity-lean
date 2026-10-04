import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSources

/-!
# The global recursive source ledger of the charged Gacs-Day closure

`GacsDayChargedClosureSources` transports one accepted recursive round to the
common final depth.  This file assembles the *global* ledger: the flat map of
`grayChargedRoundSources` over all frozen rounds of the final replay, together
with the physical-cell facts that make the resulting charge admissible, namely

* cylinder disjointness from base incomparability;
* within-round global nodup (distinct owner components never collide);
* cross-round physical incomparability, obtained from the frozen chain
  (`grayTailFrozenChain_roundUnavailable_ordered`) and the freshness half of
  `newGrayCellsList`;
* the resulting global nodup, validity, mass identity and aggregate lower
  bounds of the flattened recursive source charge.

Nothing here assumes reserve persistence, and no per-root H3 is introduced:
the aggregate request bound is summed over accepted recursive calls exactly as
in `grayChargedRoundSources_request_lower`.
-/

namespace Kolmogorov

open scoped BigOperators

/-! ## Physical disjointness of cylinders over incomparable bases -/

/-- Two dyadic blocks over prefix-incomparable bases share no cell.  This
strengthens `grayChargedReserveCylinder_disjoint`, which needs the two bases to
have the same length. -/
lemma grayChargedReserveCylinder_disjoint_of_incomparable
    {i j delta : Nat} {R S : BitString}
    (hne : ¬ (R <+: S ∨ S <+: R)) :
    List.Disjoint ((grayChargedReserveCylinder i delta R).map Prod.snd)
      ((grayChargedReserveCylinder j delta S).map Prod.snd) := by
  rw [grayChargedReserveCylinder_snd, grayChargedReserveCylinder_snd]
  intro p hp hq
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨t, _, ht⟩ := List.mem_map.mp hq
  exact hne
    (List.prefix_or_prefix_of_prefix (List.prefix_append R s)
      (ht ▸ List.prefix_append S t))

/-! ## Owner components of one round never collide -/

/-- A cell of `grayChargedTransportRoot` remembers the local cell it refines. -/
lemma grayChargedTransportRoot_base
    {delta owner root : Nat} {G : FamilyGrayCharge}
    {x : BitString}
    (hx : x ∈ (grayChargedTransportRoot delta owner root G).map Prod.snd) :
    exists source, source ∈ grayChargeAtRoot root G ∧ source.2 <+: x := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  obtain ⟨source, hsource, hzc⟩ := mem_grayChargedTransportRoot.mp hz
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hzc
  exact ⟨source, hsource, List.prefix_append _ _⟩

/-- Two distinct owner components of one accepted round transport to disjoint
blocks of physical cells. -/
lemma grayChargedTransportRoot_disjoint_of_ne_root
    {delta owner owner' root root' d : Nat} {G : FamilyGrayCharge}
    (hnodup : (G.map Prod.snd).Nodup)
    (hlen : forall z, z ∈ G -> z.2.length = d)
    (hne : root ≠ root') :
    List.Disjoint ((grayChargedTransportRoot delta owner root G).map Prod.snd)
      ((grayChargedTransportRoot delta owner' root' G).map Prod.snd) := by
  intro x hx hx'
  obtain ⟨u, hu, hux⟩ := grayChargedTransportRoot_base hx
  obtain ⟨v, hv, hvx⟩ := grayChargedTransportRoot_base hx'
  have huG := (mem_grayChargeAtRoot.mp hu).1
  have hvG := (mem_grayChargeAtRoot.mp hv).1
  have hlenuv : u.2.length = v.2.length := by rw [hlen u huG, hlen v hvG]
  have huv : u.2 = v.2 :=
    (List.prefix_of_prefix_length_le hux hvx (le_of_eq hlenuv)).eq_of_length
      hlenuv
  have := List.inj_on_of_nodup_map hnodup huG hvG huv
  exact hne (by
    rw [← (mem_grayChargeAtRoot.mp hu).2, ← (mem_grayChargeAtRoot.mp hv).2,
      this])

/-- Global cell uniqueness inside one accepted recursive round. -/
lemma grayChargedTransportRound_nodup
    {n b : Nat} {D d : Nat} {slots : List (GrayTailSlot n b)}
    {G : FamilyGrayCharge}
    (hnodup : (G.map Prod.snd).Nodup)
    (hlen : forall z, z ∈ G -> z.2.length = d) :
    ((grayChargedTransportRound D slots G).map Prod.snd).Nodup := by
  rw [grayChargedTransportRound, List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact grayChargedTransportRoot_nodup
      (List.Nodup.sublist (List.filter_sublist.map Prod.snd) hnodup)
      (fun z hz => hlen z (mem_grayChargeAtRoot.mp hz).1)
  · rw [List.pairwise_ofFn]
    intro j j' hjj'
    exact grayChargedTransportRoot_disjoint_of_ne_root hnodup hlen
      (by exact fun h => absurd h (Nat.ne_of_lt hjj'))

/-- Round-level cell uniqueness for a genuine local charge. -/
lemma grayChargedTransportRound_nodup_of_charge
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n b D : Nat}
    {slots : List (GrayTailSlot n b)}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (hvalid : familyGrayChargeAtB eta kappa alpha beta
      epsDepth deltaDepth slots.length A c s G = true) :
    ((grayChargedTransportRound D slots G).map Prod.snd).Nodup :=
  grayChargedTransportRound_nodup (d := deltaDepth)
    (familyGrayChargeAtB.cells_nodup hvalid)
    (fun _ hz => (mem_newGrayCellsList.mp
      (familyGrayChargeAtB.cell hvalid hz).2).1)

/-! ## Cross-round physical incomparability

The frozen chain records, for every accepted round, the whole coarse gray
neighbourhood of the cells it allocated.  A later round's local gray cells are
fresh against that neighbourhood, which makes the local cells of two distinct
accepted rounds prefix-incomparable and therefore their cylinders disjoint. -/

/-- The coarse trace of a local gray cell of an accepted round belongs to the
round's recorded gray neighbourhood. -/
lemma grayCharged_local_cell_take_mem_roundUnavailable
    {n b L k : Nat} {sm : Nat -> FamilyServerMove}
    {p : GrayTailRound n b}
    (halloc : p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots (sm p.serverTime)))
    (hk : k < p.slots.length) {cell : BitString}
    (hcell : cell ∈ newGrayCellsList p.epsDepth (p.epsDepth + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.epsDepth + L) p.slots
        (sm p.serverTime)) k []) p.unavailable) :
    cell.take p.epsDepth ∈ grayTailRoundUnavailable p := by
  obtain ⟨hlen, ⟨c, hc, hcomp⟩, _⟩ := mem_newGrayCellsList.mp hcell
  rw [grayTailRoundUnavailable, mem_neighborhoodCellsList]
  refine ⟨by rw [List.length_take, hlen]; omega, c, ?_, hcomp⟩
  rw [halloc, grayTailLocalAllocatedList, List.mem_flatMap]
  exact ⟨k, List.mem_range.mpr
    (by rw [length_grayTailLocalServerMove]; exact hk), hc⟩

/-- Coarsening the validity anchor (v14 §9.3): the neighbourhood clause at a
finer anchor implies it at any coarser one. -/
lemma newGrayCell_anchor_coarsen {eps eps' delta : Nat} {S U : List BitString}
    {p : BitString} (hle : eps' <= eps)
    (hp : p ∈ newGrayCellsList eps delta S U) :
    ∃ c ∈ S, p.take eps' <+: c ∨ c <+: p.take eps' := by
  obtain ⟨-, ⟨c, hc, hcomp⟩, -⟩ := mem_newGrayCellsList.mp hp
  refine ⟨c, hc, ?_⟩
  have htake : p.take eps' <+: p.take eps := by
    have h1 : (p.take eps).take eps' = p.take eps' := by
      rw [List.take_take, min_eq_left hle]
    rw [← h1]
    exact List.take_prefix _ _
  rcases hcomp with h | h
  · exact Or.inl (htake.trans h)
  · exact List.prefix_or_prefix_of_prefix htake h

/-- **The cross-component chase** (proof doc v14 §9.2): a designated local
gray cell of an earlier fine round is prefix-incomparable with one of a later
fine round.  The later round's snapshot harvest contains a truncation of a
transported witness of the earlier cell, and the later cell's freshness
clause forbids comparability with it. -/
private lemma grayCharged_chase_core
    {q L a e n t0 : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {p r : GrayTailRound n (grayTailBranch q L a e)}
    (hidx : p.roundIndex < r.roundIndex)
    (hbound : r.roundIndex < grayChargedAdvantageRoundCount q)
    (hts : p.serverTime <= t0)
    (hpEps : p.epsDepth = grayTailRoundEps q L e p.roundIndex)
    (hrEps : r.epsDepth = grayTailRoundEps q L e r.roundIndex)
    (hpSlotsRound : forall s, s ∈ p.slots -> s.2.2.val = p.roundIndex)
    (hrSlotsRound : forall s, s ∈ r.slots -> s.2.2.val = r.roundIndex)
    (hrUnavail : r.unavailable =
      A ++ grayHarvest (r.epsDepth + L) r.slots n (sm t0))
    {j j' : Nat} (hj : j < p.slots.length)
    {cu cv : BitString}
    (hcu : cu ∈ newGrayCellsList p.epsDepth (p.epsDepth + L)
      (getFamilyAlloc (grayTailLocalServerMove (p.epsDepth + L) p.slots
        (sm p.serverTime)) j []) p.unavailable)
    (hcv : cv ∈ newGrayCellsList r.epsDepth (r.epsDepth + L)
      (getFamilyAlloc (grayTailLocalServerMove (r.epsDepth + L) r.slots
        (sm r.serverTime)) j' []) r.unavailable) :
    ¬ (cu <+: cv ∨ cv <+: cu) := by
  intro hcmp
  have hRC : grayChargedAdvantageRoundCount q =
      grayTailRoundCount q - 8 := rfl
  -- the schedule ordering: the later fine end is at most the earlier anchor
  have hdelta_le : r.epsDepth + L <= p.epsDepth := by
    rw [hpEps, hrEps]
    unfold grayTailRoundEps
    have hco : (grayTailRoundCount q - 1 - r.roundIndex) + 1 <=
        grayTailRoundCount q - 1 - p.roundIndex := by omega
    calc grayCallDepth q e +
          (grayTailRoundCount q - 1 - r.roundIndex) * L + L
        = grayCallDepth q e +
          ((grayTailRoundCount q - 1 - r.roundIndex) + 1) * L := by ring
      _ <= grayCallDepth q e +
          (grayTailRoundCount q - 1 - p.roundIndex) * L :=
        Nat.add_le_add_left (Nat.mul_le_mul_right L hco) _
  obtain ⟨hulen, ⟨c, hcS, hcomp_uc⟩, -⟩ := mem_newGrayCellsList.mp hcu
  obtain ⟨hvlen, -, hfreshv⟩ := mem_newGrayCellsList.mp hcv
  -- the later cell is a prefix of the earlier one
  have hvu : cv <+: cu := by
    rcases hcmp with h | h
    · have hle := h.length_le
      have heq : cu = cv := h.eq_of_length (by omega)
      rw [heq]
    · exact h
  have hcvlen : cv.length <= p.epsDepth := by omega
  have hvu_take : cv <+: cu.take p.epsDepth := by
    obtain ⟨w, hw⟩ := hvu
    have h1 : cu.take cv.length = cv := by
      rw [← hw]
      exact List.take_left
    have h2 : (cu.take p.epsDepth).take cv.length = cu.take cv.length := by
      rw [List.take_take, min_eq_left hcvlen]
    calc cv = (cu.take p.epsDepth).take cv.length := by rw [h2, h1]
      _ <+: cu.take p.epsDepth := List.take_prefix _ _
  -- hence comparable with the earlier round's own witness
  have hvc : cv <+: c ∨ c <+: cv := by
    rcases hcomp_uc with h | h
    · exact Or.inl (hvu_take.trans h)
    · exact List.prefix_or_prefix_of_prefix hvu_take h
  -- lift the witness to the full server at the earlier slot's node
  have hcFam := grayCharged_mem_localAlloc_imp_mem_family p ⟨j, hj⟩ hcS
  -- transport it to the later round's snapshot time
  have hplay := hsm.1 (p.slots.get ⟨j, hj⟩).1.val (p.slots.get ⟨j, hj⟩).1.isLt
  have hsub := allocationSubset_mono_time hplay hts
    [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val]
  obtain ⟨c0, hc0, hc0c⟩ := hsub c hcFam
  -- the earlier node is foreign to the later component
  have hforeign : grayNodeForeignB r.slots (p.slots.get ⟨j, hj⟩).1.val
      [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val] = true := by
    rw [grayNodeForeignB, List.all_eq_true]
    intro s hs
    rw [Bool.or_eq_true]
    by_cases htree : (p.slots.get ⟨j, hj⟩).1.val = s.1.val
    · right
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro hcmp2
      have heq2 : ([(p.slots.get ⟨j, hj⟩).2.1.val,
          (p.slots.get ⟨j, hj⟩).2.2.val] : GacsDayNode) =
          grayTailSlotNode s := by
        rcases hcmp2 with h | h
        · exact h.eq_of_length (by simp [grayTailSlotNode])
        · exact (h.eq_of_length (by simp [grayTailSlotNode])).symm
      have hg : (p.slots.get ⟨j, hj⟩).2.2.val = s.2.2.val := by
        simp only [grayTailSlotNode, List.cons.injEq, and_true] at heq2
        exact heq2.2
      have hpg := hpSlotsRound _ (List.get_mem p.slots ⟨j, hj⟩)
      have hrg := hrSlotsRound s hs
      omega
    · left
      exact decide_eq_true htree
  have hvalidNode : grayNodeValidB (grayTailBranch q L a e)
      [(p.slots.get ⟨j, hj⟩).2.1.val, (p.slots.get ⟨j, hj⟩).2.2.val] = true := by
    simp only [grayNodeValidB, List.all_eq_true]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · simp
    · rcases List.mem_cons.mp hd with rfl | hd
      · simp
      · simp at hd
  -- the transported truncation is a harvest entry of the later round
  have hH : c0.take (r.epsDepth + L) ∈
      grayHarvest (r.epsDepth + L) r.slots n (sm t0) :=
    mem_grayHarvest_of_getAlloc (p.slots.get ⟨j, hj⟩).1.isLt
      hvalidNode hforeign hc0
  have hHc : c0.take (r.epsDepth + L) <+: c :=
    (List.take_prefix _ _).trans hc0c
  have hHv : cv <+: c0.take (r.epsDepth + L) ∨
      c0.take (r.epsDepth + L) <+: cv := by
    rcases hvc with h | h
    · exact List.prefix_or_prefix_of_prefix h hHc
    · exact Or.inr (hHc.trans h)
  exact hfreshv ⟨c0.take (r.epsDepth + L),
    by rw [hrUnavail]; exact List.mem_append_right _ hH, hHv⟩

/-! ## Disjointness of two accepted rounds after transport -/

/-- A transported cell of a round refines a local cell of that round. -/
lemma grayChargedTransportRound_base
    {n b D : Nat} {slots : List (GrayTailSlot n b)} {G : FamilyGrayCharge}
    {x : BitString}
    (hx : x ∈ (grayChargedTransportRound D slots G).map Prod.snd) :
    exists u, u ∈ G ∧ u.2 <+: x := by
  rw [grayChargedTransportRound, List.map_flatMap, List.mem_flatMap] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨u, hu, hux⟩ := grayChargedTransportRoot_base hxl
  exact ⟨u, (mem_grayChargeAtRoot.mp hu).1, hux⟩

/-- Rounds whose local cells are pairwise incomparable transport to disjoint
blocks of physical cells. -/
lemma grayChargedTransportRound_disjoint_of_incomparable_bases
    {n b D : Nat} {slots slots' : List (GrayTailSlot n b)}
    {G H : FamilyGrayCharge}
    (hinc : forall u, u ∈ G -> forall v, v ∈ H ->
      ¬ (u.2 <+: v.2 ∨ v.2 <+: u.2)) :
    List.Disjoint ((grayChargedTransportRound D slots G).map Prod.snd)
      ((grayChargedTransportRound D slots' H).map Prod.snd) := by
  intro x hx hx'
  obtain ⟨u, hu, hux⟩ := grayChargedTransportRound_base hx
  obtain ⟨v, hv, hvx⟩ := grayChargedTransportRound_base hx'
  exact hinc u hu v hv (List.prefix_or_prefix_of_prefix hux hvx)

/-! ## The frozen rounds of the charged controller -/

/-- The recorded allocation of an accepted charged round is exactly the local
allocation produced by its own server move. -/
lemma grayChargedStateAt_frozen_allocated
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {p : GrayTailRound n (grayTailBranch q L a e)}
    (hp : List.Mem p
      (grayChargedRunState q L a e n sigma A sm t).core.frozen) :
    p.allocated =
      grayTailLocalAllocatedList
        (grayTailLocalServerMove (p.epsDepth + L) p.slots
          (sm p.serverTime)) := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  change List.Mem p
    (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen at hp
  generalize hst :
    grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t = st at hcert hp
  cases hcert with
  | advantage core hcore hsource hactive =>
      exact ((hcore.toCore (a := a) hsource).round_valid p hp).2.2.1
  | spend pass core hspend => exact (hspend.core.round_valid p hp).2.2.1
  | done core hdone => exact (hdone.core.round_valid p hp).2.2.1

/-- Local designated-gray cells of two distinct accepted fine rounds are
prefix-incomparable (v14 §9.2, the cross-component chase).  Positional form:
the round at the earlier position is the earlier component. -/
lemma grayCharged_frozen_local_cells_incomparable
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    {i j : Nat}
    (hi : i < (grayChargedRunState q L a e n sigma A sm t).core.frozen.length)
    (hj : j < (grayChargedRunState q L a e n sigma A sm t).core.frozen.length)
    (hij : i < j)
    (hae : a <= e)
    (hfinep : grayCallDepth q e <=
      ((grayChargedRunState q L a e n sigma A sm t).core.frozen[i]'hi).epsDepth)
    (hfiner : grayCallDepth q e <=
      ((grayChargedRunState q L a e n sigma A sm t).core.frozen[j]'hj).epsDepth)
    {u v : Nat × BitString}
    (hu : u ∈ grayChargedLocalChargeOfGoal
      (grayChargedStateAt_frozen_goal (List.getElem_mem hi) hae hfinep))
    (hv : v ∈ grayChargedLocalChargeOfGoal
      (grayChargedStateAt_frozen_goal (List.getElem_mem hj) hae hfiner)) :
    ¬ (u.2 <+: v.2 ∨ v.2 <+: u.2) := by
  have hcellu := familyGrayChargeAtB.cell
    (grayChargedLocalChargeOfGoal_valid
      (grayChargedStateAt_frozen_goal (List.getElem_mem hi) hae hfinep)) hu
  have hcellv := familyGrayChargeAtB.cell
    (grayChargedLocalChargeOfGoal_valid
      (grayChargedStateAt_frozen_goal (List.getElem_mem hj) hae hfiner)) hv
  have hcore := grayChargedCoreCertified_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t
  have hpmem : (grayChargedRunState q L a e n sigma A sm t).core.frozen[i]'hi
      ∈ (grayChargedRunState q L a e n sigma A sm t).core.frozen :=
    List.getElem_mem hi
  have hrmem : (grayChargedRunState q L a e n sigma A sm t).core.frozen[j]'hj
      ∈ (grayChargedRunState q L a e n sigma A sm t).core.frozen :=
    List.getElem_mem hj
  have hdiscr : forall m, m ∈ (grayChargedRunState q L a e n sigma A
      sm t).core.frozen ->
      grayCallDepth q e <= m.epsDepth ->
      m.epsDepth = grayTailRoundEps q L e m.roundIndex ∧
      (forall s, s ∈ m.slots -> s.2.2.val = m.roundIndex) ∧
      m.roundIndex < grayChargedAdvantageRoundCount q := by
    intro m hm hfine
    rcases (hcore.round_valid m hm).2.2.2.2 with ⟨h1, -, h3, h4, -⟩ |
      ⟨pass, -, hdepth, -, -, -⟩
    · exact ⟨h1, h3, h4⟩
    · exfalso
      have hcall5 : e + 5 <= grayCallDepth q e := by
        have h4sz : 2 ^ 2 <= 3 * q + 5 := by omega
        have := Nat.lt_size.mpr h4sz
        unfold grayCallDepth
        omega
      have hsp : grayChargedSpendEps a L e pass <= e + 3 := by
        unfold grayChargedSpendEps grayChargedSpendAlphaDepth
        exact max_le (by omega) (by omega)
      rw [hdepth] at hfine
      omega
  obtain ⟨hpEps, hpSlotsRound, -⟩ := hdiscr _ hpmem hfinep
  obtain ⟨hrEps, hrSlotsRound, hrBound⟩ := hdiscr _ hrmem hfiner
  have hpIdx := hcore.frozen_index i hi
  have hrIdx := hcore.frozen_index j hj
  have ht0 : j - 1 <
      (grayChargedRunState q L a e n sigma A sm t).core.frozen.length := by
    omega
  have hts : ((grayChargedRunState q L a e n sigma A
        sm t).core.frozen[i]'hi).serverTime <=
      ((grayChargedRunState q L a e n sigma A
        sm t).core.frozen[j - 1]'ht0).serverTime := by
    rcases Nat.lt_or_ge i (j - 1) with hlt | hge
    · exact le_of_lt (hcore.frozen_chrono i (j - 1) hi ht0 hlt)
    · have hie : i = j - 1 := by omega
      subst hie
      exact le_refl _
  have hchainj := hcore.frozen_chain j hj
  rw [dite_eq_right (show ¬ j = 0 by omega)] at hchainj
  simp only [grayHarvestSnapshot] at hchainj
  have hijIdx : ((grayChargedRunState q L a e n sigma A
        sm t).core.frozen[i]'hi).roundIndex <
      ((grayChargedRunState q L a e n sigma A
        sm t).core.frozen[j]'hj).roundIndex := by
    rw [hpIdx, hrIdx]
    exact hij
  exact grayCharged_chase_core hsm hijIdx hrBound hts hpEps hrEps
    hpSlotsRound hrSlotsRound hchainj hcellu.1 hcellu.2 hcellv.2

/-- The frozen slot layout of a certified charged state is duplicate free. -/
lemma grayChargedStateAt_frozenSlots_nodup
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} :
    (grayTailFrozenSlots
      (grayChargedRunState q L a e n sigma A sm t).core.frozen).Nodup := by
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  change (grayTailFrozenSlots
    (grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen).Nodup
  generalize hst :
    grayChargedStateAt (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t = st at hcert
  cases hcert with
  | advantage core hcore hsource hactive =>
      exact ((hcore.toCore (a := a) hsource).all_slots_nodup).of_append_left
  | spend pass core hspend => exact hspend.core.all_slots_nodup.of_append_left
  | done core hdone => exact hdone.core.all_slots_nodup.of_append_left

/-- Two accepted rounds at distinct positions of the frozen ledger use
disjoint slot sets. -/
lemma grayCharged_frozen_slots_disjoint_of_lt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {i j : Nat}
    (hi : i < (grayChargedRunState q L a e n sigma A sm t).core.frozen.length)
    (hj : j < (grayChargedRunState q L a e n sigma A sm t).core.frozen.length)
    (hij : i < j) :
    List.Disjoint
      ((grayChargedRunState q L a e n sigma A sm t).core.frozen[i].slots)
      ((grayChargedRunState q L a e n sigma A sm t).core.frozen[j].slots) := by
  have hnodup := grayChargedStateAt_frozenSlots_nodup
    (q := q) (L := L) (a := a) (e := e) (n := n) (t := t)
    (sigma := sigma) (A := A) (sm := sm)
  rw [grayTailFrozenSlots] at hnodup
  exact List.pairwise_iff_getElem.mp (List.nodup_flatMap.mp hnodup).2 i j hi hj hij

/-- Distinct positions of the frozen ledger carry distinct rounds as soon as
the earlier one actually fired a recursive call. -/
lemma grayCharged_frozen_ne_of_lt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {i j : Nat}
    (hi : i < (grayChargedRunState q L a e n sigma A sm t).core.frozen.length)
    (hj : j < (grayChargedRunState q L a e n sigma A sm t).core.frozen.length)
    (hij : i < j)
    (hne : (grayChargedRunState q L a e n sigma A sm t).core.frozen[i].slots ≠ []) :
    (grayChargedRunState q L a e n sigma A sm t).core.frozen[i] ≠
      (grayChargedRunState q L a e n sigma A sm t).core.frozen[j] := by
  intro heq
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
  exact grayCharged_frozen_slots_disjoint_of_lt hi hj hij hs (heq ▸ hs)

/-! ## The global recursive source ledger -/

/-- Flattening a family of owner-source lists commutes with the flattening of
their transported charges. -/
lemma grayChargedSourceCharge_flatMap {alpha : Type _}
    {q L a e n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (l : List alpha)
    (f : alpha -> List (GrayChargedChargeSource q L a e n A c s)) :
    grayChargedSourceCharge (l.flatMap f) =
      l.flatMap fun x => grayChargedSourceCharge (f x) := by
  simp [grayChargedSourceCharge, List.flatMap_assoc]

/-- **Step 1 of the charged final transport.**  The global recursive source
ledger: every owner component of every accepted frozen round of the final
replay, transported to the common final depth at the late horizon `U`. -/
noncomputable def grayChargedFrozenSources
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    List (GrayChargedChargeSource q L a e n A
      (grayChargedRunMove q L a e n sigma A sm U) (sm U)) :=
  (List.finRange
      (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen.length).flatMap
    fun i => grayChargedRoundSources hsm replay hU
      (List.getElem_mem i.isLt) hae
      (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)

/-- The flattened global recursive charge is the concatenation of the
round-wise cylinder transports. -/
lemma grayChargedFrozenSources_charge_eq
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    grayChargedSourceCharge (grayChargedFrozenSources hsm replay hU hae hfineAll phase) =
      (List.finRange
        (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen.length).flatMap
        fun i => grayChargedTransportRound (e + grayTailNewLoss q L)
          ((grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen[i.val]).slots
          (grayChargedLocalChargeOfGoal
            (grayChargedStateAt_frozen_goal (List.getElem_mem i.isLt) hae
              (hfineAll _ (List.getElem_mem i.isLt)))) := by
  rw [grayChargedFrozenSources, grayChargedSourceCharge_flatMap]
  refine List.flatMap_congr ?_
  intro i _
  exact grayChargedSourceCharge_roundSources hsm replay hU
    (List.getElem_mem i.isLt) hae
    (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)

/-- Every cell of a flattened recursive source charge is a genuinely new gray
cell of its owner at the common late server move. -/
lemma grayChargedSourceCharge_valid
    {q L a e n : Nat} {A : Allocation}
    {c : FamilyClientMove} {s : FamilyServerMove}
    (sources : List (GrayChargedChargeSource q L a e n A c s))
    {z : Nat × BitString} (hz : z ∈ grayChargedSourceCharge sources) :
    z.1 < n ∧
      z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
        (getFamilyAlloc s z.1 []) A := by
  obtain ⟨w, -, hzw⟩ := List.mem_flatMap.mp hz
  exact w.transported_valid z hzw

/-- **Step 3 of the charged final transport (source-source half).**  Global
physical cell uniqueness of the recursive source ledger, across owners inside
one accepted round and across distinct accepted rounds. -/
lemma grayChargedFrozenSources_cells_nodup
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    ((grayChargedSourceCharge
      (grayChargedFrozenSources hsm replay hU hae hfineAll phase)).map Prod.snd).Nodup := by
  rw [grayChargedFrozenSources_charge_eq, List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨?_, ?_⟩
  · intro i _
    exact grayChargedTransportRound_nodup_of_charge
      (grayChargedLocalChargeOfGoal_valid
        (grayChargedStateAt_frozen_goal (List.getElem_mem i.isLt) hae
              (hfineAll _ (List.getElem_mem i.isLt))))
  · refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange _)
    intro i j hij
    simp only [Function.onFun]
    by_cases hslots :
        (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen[i.val].slots
          = []
    · simp [grayChargedTransportRound, hslots]
    · refine grayChargedTransportRound_disjoint_of_incomparable_bases ?_
      intro u hu v hv
      exact grayCharged_frozen_local_cells_incomparable hsm
        i.isLt j.isLt hij hae
        (hfineAll _ (List.getElem_mem i.isLt))
        (hfineAll _ (List.getElem_mem j.isLt)) hu hv

/-- The mass of the global recursive charge is the exact sum of the accepted
rounds' local charge masses: transport is lossless and no round is counted
twice. -/
lemma grayChargedFrozenSources_mass
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge
          (grayChargedFrozenSources hsm replay hU hae hfineAll phase)) =
      ∑ i : Fin (grayChargedRunState q L a e n sigma A sm (T + 1)).core.frozen.length,
        grayChargeMass
          ((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val].epsDepth + L)
          (grayChargedLocalChargeOfGoal
            (grayChargedStateAt_frozen_goal (List.getElem_mem i.isLt) hae
              (hfineAll _ (List.getElem_mem i.isLt)))) := by
  rw [grayChargedFrozenSources, grayChargedSourceCharge_flatMap,
    grayChargeMass_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact grayChargedRoundSources_mass hsm replay hU
    (List.getElem_mem i.isLt) hae
    (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)

/-- Aggregate H3 for the whole recursive ledger: the amplified request of all
accepted recursive calls is dominated by the transported charge.  The bound is
summed once per accepted call, never once per owner root. -/
lemma grayChargedFrozenSources_request_lower
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    halfAmplification q *
        ∑ i : Fin (grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen.length,
          totalRootRequest
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[i.val]).slots.length
            ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[i.val]).move <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge
          (grayChargedFrozenSources hsm replay hU hae hfineAll phase)) := by
  rw [grayChargedFrozenSources_mass hsm replay hU hae hfineAll phase, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  have h := grayChargedRoundSources_request_lower hsm replay hU
    (List.getElem_mem i.isLt) hae
    (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)
  rwa [grayChargedRoundSources_mass hsm replay hU
    (List.getElem_mem i.isLt) hae
    (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)] at h

/-- Aggregate H2 for the whole recursive ledger. -/
lemma grayChargedFrozenSources_beta_lower
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    ∑ i : Fin (grayChargedRunState q L a e n sigma A sm
          (T + 1)).core.frozen.length,
        (((grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen[i.val]).slots.length : Rat) *
          ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e)) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceCharge
          (grayChargedFrozenSources hsm replay hU hae hfineAll phase)) := by
  rw [grayChargedFrozenSources_mass hsm replay hU hae hfineAll phase]
  refine Finset.sum_le_sum ?_
  intro i _
  have h := grayChargedRoundSources_beta_lower hsm replay hU
    (List.getElem_mem i.isLt) hae
    (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)
  rwa [grayChargedRoundSources_mass hsm replay hU
    (List.getElem_mem i.isLt) hae
    (hfineAll _ (List.getElem_mem i.isLt)) (phase i.val)] at h

/-! ## Step 6: the per-root fibres of the recursive ledger -/

/-- Selecting the charges at a fixed root commutes with flattening a family of charge lists. -/
lemma grayChargeAtRoot_flatMap {alpha : Type _} (i : Nat) (l : List alpha)
    (f : alpha -> FamilyGrayCharge) :
    grayChargeAtRoot i (l.flatMap f) =
      l.flatMap fun x => grayChargeAtRoot i (f x) := by
  induction l with
  | nil => simp [grayChargeAtRoot]
  | cons x xs ih =>
      simp only [List.flatMap_cons, grayChargeAtRoot, List.filter_append] at *
      rw [ih]

/-- A block owned by a single root is its own fibre at that root and is empty
at every other root. -/
lemma grayChargeAtRoot_of_single_owner {i owner : Nat} {G : FamilyGrayCharge}
    (h : forall z, z ∈ G -> z.1 = owner) :
    grayChargeAtRoot i G = if owner = i then G else [] := by
  by_cases hio : owner = i
  · subst hio
    rw [ite_eq_left rfl, grayChargeAtRoot, List.filter_eq_self]
    intro z hz
    simp [h z hz]
  · rw [ite_eq_right hio, grayChargeAtRoot, List.filter_eq_nil_iff]
    intro z hz
    simp [h z hz, hio]

/-- The empty charge list has mass `0`. -/
lemma grayChargeMass_nil (d : Nat) : grayChargeMass d [] = 0 := by
  simp [grayChargeMass, grayMassOfCount]

/-- Per-root mass of one transported accepted round: only the owner slots of
that root contribute, each with the mass of its own local fibre. -/
lemma grayChargeMass_grayChargeAtRoot_transportRound
    {eta kappa alpha beta : Rat} {epsDepth deltaDepth n b D i : Nat}
    {slots : List (GrayTailSlot n b)}
    {A : Allocation} {c : FamilyClientMove} {s : FamilyServerMove}
    {G : FamilyGrayCharge}
    (hdepth : deltaDepth <= D)
    (hvalid : familyGrayChargeAtB eta kappa alpha beta
      epsDepth deltaDepth slots.length A c s G = true) :
    grayChargeMass D (grayChargeAtRoot i (grayChargedTransportRound D slots G)) =
      ∑ j : Fin slots.length,
        (if (slots.get j).1.val = i then
          grayChargeMass deltaDepth (grayChargeAtRoot j.val G) else 0) := by
  rw [grayChargedTransportRound, grayChargeAtRoot_flatMap, grayChargeMass_flatMap,
    List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Function.comp_apply, id_eq,
    grayChargeAtRoot_of_single_owner
      (fun _ hz => grayChargedTransportRoot_owner hz)]
  by_cases hj : (slots.get j).1.val = i
  · rw [ite_eq_left hj, ite_eq_left hj]
    exact grayChargedTransportRoot_mass_of_charge hdepth hvalid
  · rw [ite_eq_right hj, ite_eq_right hj, grayChargeMass_nil]

/-- **Step 6 (per-root half).**  The recursive part of the final charge splits
over roots exactly into the local owner fibres of the accepted rounds, and is
bounded root-wise by the recursive per-root caps of those rounds.  What remains
for H5 is the purely arithmetic frozen-ledger inequality bounding the displayed
slot requests of one outer root by that root's final displayed request. -/
theorem grayChargedFrozenSources_perRoot_mass_le
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (hae : a <= e)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) (i : Nat) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedSourceCharge
          (grayChargedFrozenSources hsm replay hU hae hfineAll phase))) <=
      4 * halfAmplification q *
        ∑ k : Fin (grayChargedRunState q L a e n sigma A sm
            (T + 1)).core.frozen.length,
          ∑ j : Fin ((grayChargedRunState q L a e n sigma A sm
              (T + 1)).core.frozen[k.val]).slots.length,
            (if (((grayChargedRunState q L a e n sigma A sm
                (T + 1)).core.frozen[k.val]).slots.get j).1.val = i then
              getFamilyReq ((grayChargedRunState q L a e n sigma A sm
                (T + 1)).core.frozen[k.val]).move j.val []
            else 0) := by
  rw [grayChargedFrozenSources_charge_eq, grayChargeAtRoot_flatMap,
    grayChargeMass_flatMap, ← List.ofFn_eq_map, List.sum_ofFn, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro k _
  rw [grayChargeMass_grayChargeAtRoot_transportRound
    (grayChargedStateAt_frozen_depth_bounds (List.getElem_mem k.isLt) hae
      (hfineAll _ (List.getElem_mem k.isLt))).2
    (grayChargedLocalChargeOfGoal_valid
      (grayChargedStateAt_frozen_goal (List.getElem_mem k.isLt) hae
              (hfineAll _ (List.getElem_mem k.isLt)))),
    Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _
  by_cases hj : (((grayChargedRunState q L a e n sigma A sm
      (T + 1)).core.frozen[k.val]).slots.get j).1.val = i
  · rw [ite_eq_left hj, ite_eq_left hj]
    exact (familyGrayChargeAtB.root
      (grayChargedLocalChargeOfGoal_valid
        (grayChargedStateAt_frozen_goal (List.getElem_mem k.isLt) hae
              (hfineAll _ (List.getElem_mem k.isLt)))) j.isLt).2.2
  · rw [ite_eq_right hj, ite_eq_right hj, mul_zero]

/-! ## Step 5: reducing source-reserve collision control to base geometry -/

/-- A transported recursive block and a reserve block are disjoint as soon as
their bases are prefix-incomparable. -/
lemma grayChargedTransportRound_disjoint_reserveCylinder
    {n b D i : Nat} {slots : List (GrayTailSlot n b)}
    {G : FamilyGrayCharge} {R : BitString}
    (hinc : forall u, u ∈ G -> ¬ (u.2 <+: R ∨ R <+: u.2)) :
    List.Disjoint ((grayChargedTransportRound D slots G).map Prod.snd)
      ((grayChargedReserveCylinder i D R).map Prod.snd) := by
  intro x hx hx'
  obtain ⟨u, hu, hux⟩ := grayChargedTransportRound_base hx
  rw [grayChargedReserveCylinder_snd] at hx'
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx'
  exact hinc u hu (List.prefix_or_prefix_of_prefix hux (List.prefix_append R s))

/-- Source-reserve disjointness of the two flattened charges reduces to
block-wise disjointness of one transported owner component against one
reserve contribution. -/
lemma grayChargedSourceCharge_disjoint_reserveCharge
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {c : FamilyClientMove}
    (sources : List (GrayChargedChargeSource q L a e n A c (sm U)))
    (reserves : List (GrayChargedReserveSource q L a e n U A sm))
    (h : forall w, w ∈ sources -> forall r, r ∈ reserves ->
      List.Disjoint (w.transported.map Prod.snd) (r.cells.map Prod.snd)) :
    List.Disjoint ((grayChargedSourceCharge sources).map Prod.snd)
      ((grayChargedReserveCharge reserves).map Prod.snd) := by
  intro x hx hx'
  rw [grayChargedSourceCharge, List.map_flatMap, List.mem_flatMap] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  rw [grayChargedReserveCharge, List.map_flatMap, List.mem_flatMap] at hx'
  obtain ⟨r, hr, hxr⟩ := hx'
  exact h w hw r hr hxw hxr

/-! ## Step 4: one common late horizon carrying both ledgers -/

/-- On the non-positive branch there is a
single late server time `U` at which the terminal client display is unchanged,
every resolved source of the final replay carries a genuine reserve
contribution, and the complete recursive source ledger is available with global
cell uniqueness, exact reserve mass, and the aggregate recursive bounds.  Only
the source-reserve collision control and the final assembly are missing from
this package. -/
theorem grayCharged_late_source_and_reserve_ledger
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (hnotpos : ¬ GrayChargedPositive q L a e n sigma A sm)
    (replay : GrayChargedFinalReplay q L a e n sigma A sm T)
    (hfineAll : forall p, p ∈ (grayChargedRunState q L a e n sigma A sm
        (T + 1)).core.frozen ->
      grayCallDepth q e <= p.epsDepth)
    (phase : Nat -> GrayChargedSourcePhase) :
    exists (U : Nat) (hU : T + 1 <= U)
      (reserves : List (GrayChargedReserveSource q L a e n U A sm)),
      grayChargedRunMove q L a e n sigma A sm U =
          grayChargedRunMove q L a e n sigma A sm T ∧
        (forall z, z ∈ grayChargedReplayRaisedSources replay ∪
            grayChargedReplayServerResolvedSources replay ->
          exists r, r ∈ reserves ∧ r.coordinate = z) ∧
        ((grayChargedReserveCharge reserves).map Prod.snd).Nodup ∧
        grayChargeMass (e + grayTailNewLoss q L)
            (grayChargedReserveCharge reserves) =
          ((grayChargedReplayRaisedSources replay ∪
            grayChargedReplayServerResolvedSources replay).card : Rat) *
            dyadicScale e ∧
        ((grayChargedSourceCharge
          (grayChargedFrozenSources hsm replay hU hae hfineAll phase)).map Prod.snd).Nodup ∧
        halfAmplification q *
            ∑ i : Fin (grayChargedRunState q L a e n sigma A sm
                (T + 1)).core.frozen.length,
              totalRootRequest
                ((grayChargedRunState q L a e n sigma A sm
                  (T + 1)).core.frozen[i.val]).slots.length
                ((grayChargedRunState q L a e n sigma A sm
                  (T + 1)).core.frozen[i.val]).move <=
          grayChargeMass (e + grayTailNewLoss q L)
            (grayChargedSourceCharge
              (grayChargedFrozenSources hsm replay hU hae hfineAll phase)) := by
  obtain ⟨U, reserves, hU, hmove, hcomplete, -, hresNodup, hresMass⟩ :=
    grayCharged_late_reserve_family hsm hae hnotpos replay
  exact ⟨U, hU, reserves, hmove, hcomplete, hresNodup, hresMass,
    grayChargedFrozenSources_cells_nodup hsm replay hU hae hfineAll phase,
    grayChargedFrozenSources_request_lower hsm replay hU hae hfineAll phase⟩

/-! ## Step 6: selecting the final charge from the two ledgers -/

/-- Every cell of a flattened reserve charge is a genuinely new gray cell of
its owner at the common late server move. -/
lemma grayChargedReserveCharge_valid
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSource q L a e n U A sm))
    {z : Nat × BitString} (hz : z ∈ grayChargedReserveCharge reserves) :
    z.1 < n ∧
      z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A := by
  obtain ⟨r, -, hzr⟩ := List.mem_flatMap.mp hz
  exact r.cells_valid z hzr

/-- **Step 6 (selection half).**  Two ledgers whose cells are individually
unique, mutually disjoint and valid at the common late server move can be
reordered into one admissible `finalCharge`: an ordered subsequence of the
charge universe, permutation equivalent to their concatenation, hence with the
same total mass and the same mass at every root. -/
theorem grayCharged_exists_finalCharge
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    {c : FamilyClientMove}
    (sources : List (GrayChargedChargeSource q L a e n A c (sm U)))
    (reserves : List (GrayChargedReserveSource q L a e n U A sm))
    (hsnodup : ((grayChargedSourceCharge sources).map Prod.snd).Nodup)
    (hrnodup : ((grayChargedReserveCharge reserves).map Prod.snd).Nodup)
    (hdisj : List.Disjoint
      ((grayChargedSourceCharge sources).map Prod.snd)
      ((grayChargedReserveCharge reserves).map Prod.snd)) :
    exists F : FamilyGrayCharge,
      F.Perm (grayChargedSourceCharge sources ++
          grayChargedReserveCharge reserves) ∧
        F ∈ (familyGrayChargeUniverse n (e + grayTailNewLoss q L)).sublists ∧
        (F.map Prod.snd).Nodup ∧
        (forall z, z ∈ F -> z.1 < n ∧
          z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
            (getFamilyAlloc (sm U) z.1 []) A) ∧
        grayChargeMass (e + grayTailNewLoss q L) F =
          grayChargeMass (e + grayTailNewLoss q L)
              (grayChargedSourceCharge sources) +
            grayChargeMass (e + grayTailNewLoss q L)
              (grayChargedReserveCharge reserves) ∧
        forall i, grayChargeMass (e + grayTailNewLoss q L)
            (grayChargeAtRoot i F) =
          grayChargeMass (e + grayTailNewLoss q L)
              (grayChargeAtRoot i (grayChargedSourceCharge sources)) +
            grayChargeMass (e + grayTailNewLoss q L)
              (grayChargeAtRoot i (grayChargedReserveCharge reserves)) := by
  have hvalid : forall z, z ∈ grayChargedSourceCharge sources ++
      grayChargedReserveCharge reserves ->
      z.1 < n ∧ z.2 ∈ newGrayCellsList e (e + grayTailNewLoss q L)
        (getFamilyAlloc (sm U) z.1 []) A := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact grayChargedSourceCharge_valid sources hz
    · exact grayChargedReserveCharge_valid reserves hz
  have hnodup : (((grayChargedSourceCharge sources ++
      grayChargedReserveCharge reserves).map Prod.snd)).Nodup := by
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

end Kolmogorov
