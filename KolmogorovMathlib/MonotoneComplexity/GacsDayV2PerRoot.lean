import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Corner

/-!
# The V2 per-root cap and aggregate beta (Stage D4: H5 and H2)

The recursive half of the per-root cap sums the rounds' local owner fibres;
the displayed slot requests of one root are dominated by that root's final
display; the reserve half carries at most one coarse unit per source son.
Together with the audited halves arithmetic this closes H5.  H2 is the
three-quarters reserve mass against the beta target.
-/

namespace Kolmogorov

/-- **H2 for the composed V2 charge.** -/
theorem grayChargedV2_aggregate_beta
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)}
    (hRmass : grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves) =
      ((grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card : Rat) *
        dyadicScale e) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedSourceChargeV2 (grayChargedFrozenSourcesV2 hsm replay
          hU hae) ++ grayChargedReserveChargeV2 reserves) :=
  grayCharged_aggregate_beta_of_reserve_mass hae hRmass
    (grayChargedReplayV2_resolved_three_quarters replay)
    (grayChargeMass_append _ _ _)

/-- Per-fibre sum of son bases at one root equals the root-filtered entry
request sum. -/
lemma grayTail_sum_sonBase_eq_filter_sum {n b : Nat}
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n) :
    (∑ c : Fin b, grayTailSonBase entries i c) =
      ((entries.filter fun z => decide (z.1.1 = i)).map
        fun z => getReq z.2 []).sum := by
  induction entries with
  | nil => simp [grayTailSonBase]
  | cons x xs ih =>
      by_cases hx : x.1.1 = i
      · have hone : (∑ c : Fin b, if x.1.1 = i ∧ x.1.2.1 = c then
            getReq x.2 [] else 0) = getReq x.2 [] := by
          rw [Finset.sum_eq_single x.1.2.1]
          · simp [hx]
          · intro c _ hc
            rw [ite_eq_right]
            rintro ⟨-, h2⟩
            exact hc h2.symm
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        calc (∑ c : Fin b, grayTailSonBase (x :: xs) i c) =
            ∑ c : Fin b, ((if x.1.1 = i ∧ x.1.2.1 = c then
              getReq x.2 [] else 0) + grayTailSonBase xs i c) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              unfold grayTailSonBase
              simp only [List.foldr_cons]
              split_ifs with h
              · rfl
              · ring
          _ = (∑ c : Fin b, if x.1.1 = i ∧ x.1.2.1 = c then
                getReq x.2 [] else 0) +
              ∑ c : Fin b, grayTailSonBase xs i c := by
              rw [Finset.sum_add_distrib]
          _ = getReq x.2 [] +
              ((xs.filter fun z => decide (z.1.1 = i)).map
                fun z => getReq z.2 []).sum := by rw [hone, ih]
          _ = (((x :: xs).filter fun z => decide (z.1.1 = i)).map
                fun z => getReq z.2 []).sum := by
              rw [List.filter_cons, ite_eq_left (by simp [hx])]
              simp
      · have hzero : (∑ c : Fin b, if x.1.1 = i ∧ x.1.2.1 = c then
            getReq x.2 [] else 0) = 0 := by
          refine Finset.sum_eq_zero fun c _ => ?_
          simp [hx]
        calc (∑ c : Fin b, grayTailSonBase (x :: xs) i c) =
            (∑ c : Fin b, if x.1.1 = i ∧ x.1.2.1 = c then
              getReq x.2 [] else 0) +
              ∑ c : Fin b, grayTailSonBase xs i c := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun c _ => ?_
              unfold grayTailSonBase
              simp only [List.foldr_cons]
              split_ifs with h
              · rfl
              · ring
          _ = ((xs.filter fun z => decide (z.1.1 = i)).map
                fun z => getReq z.2 []).sum := by rw [hzero, ih]; ring
          _ = (((x :: xs).filter fun z => decide (z.1.1 = i)).map
                fun z => getReq z.2 []).sum := by
              rw [List.filter_cons, ite_eq_right (by simp [hx])]

/-- **The per-root source mass** is dominated by the local root caps summed
over the owner fibres of the accepted rounds. -/
theorem grayChargedFrozenSourcesV2_perRoot_mass_le
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e) (i : Nat) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae))) <=
      4 * halfAmplification q *
        ∑ k : Fin (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.length,
          ∑ j : Fin ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length,
            (if (((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
                j).1.val = i then
              getFamilyReq ((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[k.val]).move
                j.val []
            else 0) := by
  rw [grayChargedFrozenSourcesV2_charge_eq hsm replay hU hae,
    grayChargeAtRoot_flatMap, grayChargeMass_flatMap,
    ← List.ofFn_eq_map, List.sum_ofFn, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro k _
  have hub := grayChargedRunStateV2_frozen_depth_ub
    (t := T + 1) (List.getElem_mem k.isLt) hae
  set p := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen[k.val] with hpdef
  have hp : p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen := List.getElem_mem k.isLt
  unfold grayChargedRoundLocalChargeV2
  split
  next hfine =>
    have hsplit := grayChargedRunStateV2_frozen_phase_split
      q L a e sigma A sm (T + 1) hp hae hfine
    have hvalid := grayChargedLocalChargeOfBlockGoal_valid
      (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm (T + 1) hp
        hae hfine)
    have hdeltaLe : grayTailRoundDelta q L e p.roundIndex <=
        e + grayTailNewLoss q L := by
      have hfineEq : p.fineEnd = p.blockAnchor + L := by
        rw [hsplit.2.1, hsplit.1, grayTailRoundDelta]
      rw [← hsplit.2.1, hfineEq]
      exact hub
    rw [grayChargeMass_grayChargeAtRoot_transportRound hdeltaLe hvalid,
      Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro j _
    by_cases hj : (p.slots.get j).1.val = i
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact (familyGrayChargeAtB.root hvalid j.isLt).2.2
    · rw [ite_eq_right hj, ite_eq_right hj, mul_zero]
  next hfine =>
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm (T + 1) hp hfine
    have hvalid := grayChargedLocalChargeOfBlockSpendGoal_valid
      hSp.choose_spec.2.2.2
    have hanchor := hSp.choose_spec.2.1
    have hfineEq2 := hSp.choose_spec.2.2.1
    have hd : grayChargedSpendDelta a L e hSp.choose =
        grayChargedSpendEps a L e hSp.choose + L := rfl
    have hfineEq3 : p.fineEnd = p.blockAnchor + L :=
      grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm (T + 1) hp
    have hdeltaLe : grayChargedSpendDelta a L e hSp.choose <=
        e + grayTailNewLoss q L := by omega
    rw [grayChargeMass_grayChargeAtRoot_transportRound hdeltaLe hvalid,
      Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro j _
    by_cases hj : (p.slots.get j).1.val = i
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact (familyGrayChargeAtB.root hvalid j.isLt).2.2
    · rw [ite_eq_right hj, ite_eq_right hj, mul_zero]

/-- After the advantage exit, every newly frozen round is a spend round:
each frozen round either already sits in the terminal prefix or has a
coarse (spend) anchor. -/
lemma grayChargedRunStateV2_frozen_post_exit_spend
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {U : Nat} (hU : replay.advantageExitTime + 1 <= U) :
    forall p, p ∈ (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen ->
      p ∈ replay.advantageTerminal.frozen ∨
        ¬ grayCallDepth q e <= p.blockAnchor := by
  induction U, hU using Nat.le_induction with
  | base =>
      intro p hp
      left
      rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
      exact hp
  | succ m hm ih =>
      intro p hp
      -- classify the phase at time m
      have hcert := grayChargedCertifiedV2_stateAt (n := n)
        q L a e sigma A sm m
      rw [grayChargedRunStateV2_succ] at hp
      generalize hstate : grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm m = st at hcert hp ih
      -- the advantage phase cannot recur after the exit
      have hafter := replay.advantage_after
      have hmono : forall d,
          (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e) q L a e sigma A sm
            (replay.advantageExitTime + 1 + d)).phase ≠ .advantage := by
        intro d
        induction d with
        | zero =>
            simpa using hafter
        | succ d ihd =>
            intro hadv
            apply ihd
            have hcert2 := grayChargedCertifiedV2_stateAt (n := n)
              q L a e sigma A sm (replay.advantageExitTime + 1 + d)
            generalize hstate2 : grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e) q L a e sigma A sm
              (replay.advantageExitTime + 1 + d) = st2 at hcert2 hadv ⊢
            rw [show replay.advantageExitTime + 1 + (d + 1) =
                replay.advantageExitTime + 1 + d + 1 by omega,
              grayChargedRunStateV2_succ, hstate2] at hadv
            cases hcert2 with
            | advantage core2 hcore2 hsource2 hactive2 => rfl
            | wait core2 hcore2 hsource2 hdone2 => rfl
            | spend pass2 core2 hspend2 =>
                exfalso
                by_cases hslots2 : core2.slots.isEmpty = true
                · simp [grayChargedStepV2, hslots2] at hadv
                · by_cases hgoal2 : grayChargedBlockSpendGoalAtB q L a e
                      pass2 core2.slots.length core2.unavailable
                      (grayBlockSpendMoveV2 q L a e pass2 sigma core2)
                      (grayTailLocalServerMove
                        (grayChargedSpendDelta a L e pass2)
                        core2.slots (sm (replay.advantageExitTime + 1
                          + d))) = true
                  · simp only [grayChargedStepV2, hslots2,
                      Bool.false_eq_true, ↓reduceIte, hgoal2] at hadv
                    split at hadv
                    · split at hadv <;> simp_all
                    · simp_all
                  · simp [grayChargedStepV2, hslots2, hgoal2] at hadv
            | done core2 hdone2 =>
                exfalso
                simp [grayChargedStepV2] at hadv
      have hnoadv : st.phase ≠ .advantage := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm
        have := hmono d
        rw [← hd, hstate] at this
        exact this
      cases hcert with
      | advantage core hcore hsource hactive => exact absurd rfl hnoadv
      | wait core hcore hsource hdone => exact absurd rfl hnoadv
      | done core hdone =>
          have hstep := grayChargedStepV2_done_frozen q L a e sigma A
            { phase := .done, core := core } (sm m) rfl
          rw [hstep.2] at hp
          exact ih p hp
      | spend pass core hspend =>
          by_cases hslots : core.slots.isEmpty = true
          · have : (grayChargedStepV2 q L a e sigma A
                { phase := .spend pass, core := core } (sm m)).core.frozen =
                core.frozen := by
              simp [grayChargedStepV2, hslots]
            rw [this] at hp
            exact ih p hp
          · by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
                core.slots.length core.unavailable
                (grayBlockSpendMoveV2 q L a e pass sigma core)
                (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                  core.slots (sm m)) = true
            · have hfz : (grayChargedStepV2 q L a e sigma A
                  { phase := .spend pass, core := core } (sm m)).core.frozen =
                  core.frozen ++
                    [{ serverTime := core.time
                       roundIndex := core.frozen.length
                       blockAnchor := grayChargedSpendEps a L e pass
                       childEps := grayChargedSpendEps a L e pass +
                         graySpendSpan q
                       fineEnd := grayChargedSpendDelta a L e pass
                       slots := core.slots
                       move := grayBlockSpendMoveV2 q L a e pass sigma core
                       allocated := grayTailLocalAllocatedList
                         (grayTailLocalServerMove
                           (grayChargedSpendDelta a L e pass)
                           core.slots (sm m))
                       unavailable := core.unavailable }] := by
                simp only [grayChargedStepV2, hslots, Bool.false_eq_true,
                  ↓reduceIte, hgoal]
                split
                · split <;> rfl
                · rfl
              rw [hfz] at hp
              rcases List.mem_append.mp hp with hp | hp
              · exact ih p hp
              · right
                have hpe : p.blockAnchor = grayChargedSpendEps a L e pass := by
                  simp only [List.mem_singleton] at hp
                  rw [hp]
                rw [hpe]
                exact not_le.mpr (grayChargedSpendEps_lt_callDepth hae)
            · have : (grayChargedStepV2 q L a e sigma A
                  { phase := .spend pass, core := core } (sm m)).core.frozen =
                  core.frozen := by
                simp [grayChargedStepV2, hslots, hgoal]
              rw [this] at hp
              exact ih p hp

/-- Source son bases of the whole run stay below one coarse unit: the
advantage prefix is capped and the spend rounds only occupy spare sons. -/
lemma grayChargedRunStateV2_source_sonBase_le
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {U : Nat} (hU : T + 1 <= U)
    (i : Fin n) (c : Fin (grayTailBranch q L a e))
    (hc : c.val < grayChargedSourceCount a e) :
    grayTailFrozenSonBase
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen.map GrayTailRoundV2.toV1)
        i c <= dyadicScale e := by
  have hexitU : replay.advantageExitTime + 1 <= U := by
    have := replay.advantageExit_le
    omega
  have hterm := grayChargedReplayV2_advantageTerminal_frozen_eq replay
  have hpre : replay.advantageTerminal.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen := by
    rw [← hterm]
    exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm hexitU
  obtain ⟨rest, hrest⟩ := hpre
  have htermEq : replay.advantageTerminal =
      grayChargedBlockTailStateAtV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (replay.advantageExitTime + 1) := by
    rw [replay.advantageTerminal_eq,
      grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm
        replay.advantageExitTime replay.advantage_before,
      ← grayChargedBlockTailStateAtV2_succ]
  have hadv : grayTailFrozenSonBase
      (replay.advantageTerminal.frozen.map GrayTailRoundV2.toV1) i c <=
      dyadicScale e := by
    rw [htermEq]
    have := grayChargedBlockV2_all_frozen_base_le_stateAt
      q L a e sigma A sm (replay.advantageExitTime + 1) i c
    simpa [frozenV1OfV2] using this
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
    -- p is post-exit: not in the terminal (positions), so spend-anchored
    have hclass := grayChargedRunStateV2_frozen_post_exit_spend hae replay
      hexitU p hpmem
    have hnotpre : p ∉ replay.advantageTerminal.frozen := by
      intro hmem
      -- the same round cannot sit both in the prefix and the rest: the
      -- certificate's chronology forbids duplicates
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
    -- spend rounds occupy spare sons only
    have hSp := grayChargedRunStateV2_frozen_spend_goal
      q L a e sigma A sm U hpmem hcoarse
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
  rw [hmap, grayTailFrozenSonBase_append_list, hzero, add_zero]
  exact hadv

/-- Son bases distribute over a flatMap of entry blocks. -/
lemma grayTailSonBase_flatMap {n b : Nat} {alpha : Type _}
    (l : List alpha)
    (f : alpha -> List (GrayTailSlot n b × ClientMove))
    (i : Fin n) (c : Fin b) :
    grayTailSonBase (l.flatMap f) i c =
      (l.map fun x => grayTailSonBase (f x) i c).sum := by
  induction l with
  | nil => simp [grayTailSonBase]
  | cons x xs ih =>
      rw [List.flatMap_cons, grayTailSonBase_append_globalEntries, ih, List.map_cons,
        List.sum_cons]

/-- Root increments distribute over the frozen ledger (list form). -/
lemma grayChargedRootIncrement_frozenEntries {n b : Nat}
    (frozen : GrayTailFrozen n b) (i : Fin n) :
    grayChargedRootIncrement (grayTailFrozenEntries frozen) i =
      (frozen.map fun p => grayChargedRootIncrement
        (grayTailSlotEntries p.slots p.move) i).sum := by
  unfold grayChargedRootIncrement
  rw [grayTailFrozenEntries]
  simp_rw [grayTailSonBase_flatMap]
  induction frozen with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- The ledger increment at one root is dominated by that root's charged
request once every source son base is capped by one coarse unit. -/
lemma grayChargedRootIncrement_le_rootRequest {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (entries : List (GrayTailSlot n b × ClientMove)) (i : Fin n)
    (_hnonneg : forall z, z ∈ entries -> 0 <= getReq z.2 [])
    (hcap : forall c : Fin b, c.val < source ->
      grayTailSonBase entries i c <= eps) :
    grayChargedRootIncrement entries i <=
      grayChargedRootRequest source threshold eps entries i := by
  unfold grayChargedRootIncrement grayChargedRootRequest
  apply Finset.sum_le_sum
  intro c _
  unfold grayChargedSonRequest grayTailSonRequest
  by_cases hc : c.val < source
  · simp only [ite_eq_left hc]
    by_cases hr : threshold < grayTailSonBase entries i c
    · rw [ite_eq_left hr]
      exact hcap c hc
    · rw [ite_eq_right hr]
  · simp only [ite_eq_right hc]
    exact le_rfl

/-- List sums as Fin-indexed sums. -/
lemma grayCharged_list_sum_map_getElem {alpha : Type _} {beta : Type _}
    [AddCommMonoid beta] (l : List alpha) (g : alpha -> beta) :
    (l.map g).sum = ∑ k : Fin l.length, g (l[k.val]) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih]
      rw [show (∑ k : Fin (x :: xs).length, g ((x :: xs)[k.val])) =
        g x + ∑ k : Fin xs.length, g (xs[k.val]) from by
          simp only [List.length_cons]
          rw [Fin.sum_univ_succ]
          simp]

/-- **The per-root source cap against the final display** (H5, source
half). -/
theorem grayChargedFrozenSourcesV2_perRoot_cap
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) (hae : a <= e)
    (i : Fin n) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae))) <=
      4 * halfAmplification q *
        getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
          i.val [] := by
  have hdone1 := grayChargedFinalAtV2_successor_done replay.final
  set frozenV1 := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm (T + 1)).core.frozen.map GrayTailRoundV2.toV1
    with hfv
  -- step 1: the ledger cap against the owner-fibre double sum
  have hcap := grayChargedFrozenSourcesV2_perRoot_mass_le hsm replay hU hae
    i.val
  -- step 2: the double sum is the ledger increment
  have hlen : frozenV1.length = (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen.length := by
    rw [hfv, List.length_map]
  have hdouble :
      (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        ∑ j : Fin ((grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length,
          (if (((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
              j).1.val = i.val then
            getFamilyReq ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).move
              j.val []
          else 0)) =
      grayChargedRootIncrement (grayTailFrozenEntries frozenV1) i := by
    have h1 : (∑ k : Fin (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.length,
        ∑ j : Fin ((grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.length,
          (if (((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).slots.get
              j).1.val = i.val then
            getFamilyReq ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val]).move
              j.val []
          else 0)) =
        ∑ k : Fin (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.length,
          grayChargedRootIncrement (grayTailSlotEntries
            (GrayTailRoundV2.toV1 ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val])).slots
            (GrayTailRoundV2.toV1 ((grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen[k.val])).move) i := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [grayChargedRootIncrement_slotEntries_eq_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      refine if_congr ?_ rfl rfl
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    rw [h1, ← grayCharged_list_sum_map_getElem
      ((grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen)
      (fun p => grayChargedRootIncrement (grayTailSlotEntries
        (GrayTailRoundV2.toV1 p).slots (GrayTailRoundV2.toV1 p).move) i)]
    rw [show ((grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.map
        (fun p => grayChargedRootIncrement (grayTailSlotEntries
          (GrayTailRoundV2.toV1 p).slots
          (GrayTailRoundV2.toV1 p).move) i)) =
      frozenV1.map (fun p => grayChargedRootIncrement
        (grayTailSlotEntries p.slots p.move) i) from by
        rw [hfv, List.map_map]
        rfl]
    rw [← grayChargedRootIncrement_frozenEntries]
  -- step 3: the increment is dominated by the charged root request
  have hnonneg : forall z, z ∈ grayTailFrozenEntries frozenV1 ->
      0 <= getReq z.2 [] := by
    intro z hz
    exact grayChargedRunStateV2_frozenEntries_req_nonneg
      (q := q) (L := L) (a := a) (e := e) (t := T + 1)
      (sigma := sigma) (A := A) (sm := sm) z hz
  have hbasecap : forall c : Fin (grayTailBranch q L a e),
      c.val < grayChargedSourceCount a e ->
      grayTailSonBase (grayTailFrozenEntries frozenV1) i c <=
        dyadicScale e := by
    intro c hc
    have := grayChargedRunStateV2_source_sonBase_le hae replay
      (U := T + 1) (Nat.le_refl _) i c hc
    simpa [grayTailFrozenSonBase, hfv] using this
  have hdom := grayChargedRootIncrement_le_rootRequest
    (grayChargedSourceCount a e) (grayChargedThreshold q e) (dyadicScale e)
    (grayTailFrozenEntries frozenV1) i hnonneg hbasecap
  -- step 4: the charged root request is the displayed request
  have hdisplay : grayChargedRootRequest (grayChargedSourceCount a e)
      (grayChargedThreshold q e) (dyadicScale e)
      (grayTailFrozenEntries frozenV1) i =
      getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
        i.val [] := by
    have h1 := grayChargedRunMoveV2_root_eq_of_done hdone1 i
    have hmoveU : grayChargedRunMoveV2 q L a e n sigma A sm U =
        grayChargedRunMoveV2 q L a e n sigma A sm (T + 1) :=
      (replay.move_stable U hU).trans
        (grayChargedFinalAtV2_successor_move_eq replay.final).symm
    rw [hmoveU, h1]
  -- assemble
  rw [hdouble] at hcap
  refine le_trans hcap ?_
  rw [← hdisplay]
  apply mul_le_mul_of_nonneg_left hdom
  have := halfAmplification_pos q
  positivity

/-- Reserve mass at one root, one unit per block (V2 records). -/
lemma grayChargedReserveChargeV2_perRoot_mass_le_of_unit
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) (i : Nat)
    (hunit : forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveChargeV2 reserves)) <=
      ((reserves.countP fun r => decide (r.coordinate.1.val = i) : Nat) :
        Rat) * dyadicScale e := by
  classical
  rw [grayChargedReserveChargeV2, grayChargeAtRoot_flatMap,
    grayChargeMass_flatMap]
  rw [← sum_map_ite_const_rat reserves
    (fun r => decide (r.coordinate.1.val = i)) (dyadicScale e)]
  refine List.sum_le_sum ?_
  intro r hr
  by_cases h : r.coordinate.1.val = i
  · simp only [h, decide_true, ite_true]
    rw [grayChargeAtRoot_of_single_owner
      (fun z hz => r.cells_owner z hz)]
    rw [ite_eq_left h]
    exact hunit r hr
  · simp only [h, decide_false]
    rw [grayChargeAtRoot_of_single_owner
      (fun z hz => r.cells_owner z hz)]
    rw [ite_eq_right h, grayChargeMass_nil]
    simp

/-- At most one reserve per source son of a root (V2 records). -/
lemma grayChargedReserveV2_countP_le_sourceCount
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) (i : Nat)
    (hnodup : (reserves.map fun r => r.coordinate).Nodup) :
    (reserves.countP fun r => decide (r.coordinate.1.val = i)) <=
      grayChargedSourceCount a e := by
  classical
  set l := reserves.filter (fun r => decide (r.coordinate.1.val = i)) with hl
  have hcount : (reserves.countP fun r => decide (r.coordinate.1.val = i)) =
      l.length := by
    rw [hl, List.countP_eq_length_filter]
  have hlsub : l.Sublist reserves := by
    rw [hl]
    exact List.filter_sublist
  have hlnodup : (l.map fun r => r.coordinate).Nodup :=
    hnodup.sublist (hlsub.map _)
  have hmapnodup : (l.map fun r => r.coordinate.2.val).Nodup := by
    have hinj : ∀ r ∈ l, ∀ r2 ∈ l,
        r.coordinate.2.val = r2.coordinate.2.val ->
        r.coordinate = r2.coordinate := by
      intro r hr r2 hr2 h
      have h1 : r.coordinate.1.val = i := by
        have := List.of_mem_filter hr
        simpa using this
      have h12 : r2.coordinate.1.val = i := by
        have := List.of_mem_filter hr2
        simpa using this
      exact Prod.ext (Fin.ext (by rw [h1, h12])) (Fin.ext h)
    rw [show (l.map fun r => r.coordinate.2.val) =
        (l.map fun r => r.coordinate).map (fun z => z.2.val) by
      rw [List.map_map]
      rfl]
    refine List.Nodup.map_on ?_ hlnodup
    intro z hz z2 hz2 h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hz2
    exact hinj r hr r2 hr2 h
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

/-- Reserve half of the V2 per-root cap. -/
theorem grayChargedReserveChargeV2_perRoot_cap_of_window
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) (i : Nat)
    (hae : a <= e)
    (hunit : forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e)
    (hnodup : (reserves.map fun r => r.coordinate).Nodup)
    {req : Rat} (hreq : dyadicScale a / 2 <= req) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveChargeV2 reserves)) <=
      2 * req := by
  have hpos : (0 : Rat) < dyadicScale e := by
    unfold dyadicScale
    positivity
  have hstep := grayChargedReserveChargeV2_perRoot_mass_le_of_unit
    reserves i hunit
  have hcount := grayChargedReserveV2_countP_le_sourceCount reserves i hnodup
  have hcast : ((reserves.countP fun r =>
      decide (r.coordinate.1.val = i) : Nat) : Rat) <=
      ((grayChargedSourceCount a e : Nat) : Rat) := by
    exact_mod_cast hcount
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

/-- **The full V2 per-root cap (H5)**: the composed charge at one root is at
most `4·κ_{q+1}` times that root's final display. -/
theorem grayChargedV2_perRoot_cap
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)}
    (hunit : forall r, r ∈ reserves ->
      grayChargeMass (e + grayTailNewLoss q L) r.cells <= dyadicScale e)
    (hnodup : (reserves.map fun r => r.coordinate).Nodup)
    (i : Fin n) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i.val (grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae) ++
          grayChargedReserveChargeV2 reserves)) <=
      4 * halfAmplification (q + 1) *
        getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
          i.val [] := by
  -- the final displayed root is at least α/2 (H1)
  have hwindow := grayChargedV2_final_request_window hpin hae replay.final i
  have hmoveU : grayChargedRunMoveV2 q L a e n sigma A sm U =
      grayChargedRunMoveV2 q L a e n sigma A sm T :=
    replay.move_stable U hU
  have hreq : dyadicScale a / 2 <=
      getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm U)
        i.val [] := by
    rw [hmoveU]
    exact hwindow.1
  -- split the composed charge at the root
  have hsplit : grayChargeAtRoot i.val (grayChargedSourceChargeV2
      (grayChargedFrozenSourcesV2 hsm replay hU hae) ++
      grayChargedReserveChargeV2 reserves) =
      grayChargeAtRoot i.val (grayChargedSourceChargeV2
        (grayChargedFrozenSourcesV2 hsm replay hU hae)) ++
      grayChargeAtRoot i.val (grayChargedReserveChargeV2 reserves) := by
    rw [grayChargeAtRoot, List.filter_append]
    rfl
  rw [hsplit, grayChargeMass_append]
  exact grayCharged_perRoot_cap_of_halves rfl
    (grayChargedFrozenSourcesV2_perRoot_cap hsm replay hU hae i)
    (grayChargedReserveChargeV2_perRoot_cap_of_window reserves i.val hae
      hunit hnodup hreq)

end Kolmogorov
