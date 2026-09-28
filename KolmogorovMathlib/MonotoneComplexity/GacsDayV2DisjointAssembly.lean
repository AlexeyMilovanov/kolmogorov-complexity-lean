import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ComplementFamily

/-!
# The ledger/complement disjointness assembly (advantage side closed)

The flattened recursive ledger meets one owner-aligned complement only
through a spend-phase round: advantage-prefix rounds are dispatched to the
per-round kills (owner round by fibre, all others wholesale), leaving the
spend positions as one named hypothesis — the exact residual of the
straddled-serve corner.
-/

namespace Kolmogorov

/-- Advantage-prefix positions of the late frozen list carry the terminal
rounds. -/
lemma grayChargedReplayV2_terminal_getElem_late
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : replay.advantageExitTime + 1 <= U)
    {i : Nat} (hi : i < replay.advantageTerminal.frozen.length)
    (hi' : i < (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen.length) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen[i] =
      replay.advantageTerminal.frozen[i] := by
  have hpre : replay.advantageTerminal.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).core.frozen := by
    rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
    exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm hU
  obtain ⟨rest, hrest⟩ := hpre
  exact (List.getElem_of_eq hrest.symm hi').trans
    (List.getElem_append_left hi)

/-- Position-parametric non-owner kill. -/
theorem grayChargedV2_nonOwnerRound_transported_ne_complement_at
    {q L a e n T t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {tR : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z tR R k)
    (kk : Nat) (hkk : kk < replay.advantageTerminal.frozen.length)
    (hkkne : kk ≠ k)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hpos : p = replay.advantageTerminal.frozen[kk])
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    {tagOwner root : Nat} {owner : FamilyGrayCharge} {iC : Nat}
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      tagOwner root (grayChargedRoundLocalChargeV2 hae p hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 iC
      (e + grayTailNewLoss q L) R owner) :
    w.2 ≠ y.2 := by
  subst hpos
  exact grayChargedV2_nonOwnerRound_transported_ne_complement hae replay
    hdata ⟨kk, hkk⟩ hkkne hp hw hy

/-- Owner kill for the frozen round read off the advantage terminal at the
owner position `k`. -/
theorem grayChargedV2_ownerRound_transported_ne_complement_at
    {q L a e n T t t' : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {tR : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z tR R k)
    (hk : k < replay.advantageTerminal.frozen.length)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hpos : p = replay.advantageTerminal.frozen[k])
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hp' : replay.advantageTerminal.frozen[k] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t').core.frozen)
    (j : Fin p.slots.length)
    {w : Nat × BitString}
    (hw : w ∈ grayChargedTransportRoot (e + grayTailNewLoss q L)
      ((p.slots.get j).1.val) j.val
      (grayChargedRoundLocalChargeV2 hae p hp))
    {y : Nat × BitString}
    (hy : y ∈ grayChargedReserveComplementV2 z.1.val
      (e + grayTailNewLoss q L) R
      (grayChargedOwnerFibreV2 hae
        (replay.advantageTerminal.frozen[k]) hp' z)) :
    w.2 ≠ y.2 := by
  subst hpos
  exact grayChargedV2_ownerRound_transported_ne_complement hae replay
    hdata hk hp hp' j hw hy

/-- **The ledger/complement disjointness, advantage side closed**: the
flattened recursive ledger avoids one owner-aligned complement, given the
spend positions (the named straddled-serve residual). -/
theorem grayChargedV2_source_complement_disjoint
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    {z : Fin n × Fin (grayTailBranch q L a e)} {tR : Nat} {R : BitString}
    {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z tR R k)
    (hk : k < replay.advantageTerminal.frozen.length)
    (hp' : replay.advantageTerminal.frozen[k] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen)
    (hspend : forall i : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length,
      replay.advantageTerminal.frozen.length <= i.val ->
      forall w, w ∈ grayChargedTransportRound (e + grayTailNewLoss q L)
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots
          (grayChargedRoundLocalChargeV2 hae _ (List.getElem_mem i.isLt)) ->
      forall y, y ∈ grayChargedReserveComplementV2 z.1.val
          (e + grayTailNewLoss q L) R
          (grayChargedOwnerFibreV2 hae
            (replay.advantageTerminal.frozen[k]) hp' z) ->
        w.2 ≠ y.2) :
    List.Disjoint
      ((grayChargedSourceChargeV2
        (grayChargedFrozenSourcesV2 hsm replay hU hae)).map Prod.snd)
      ((grayChargedReserveComplementV2 z.1.val
        (e + grayTailNewLoss q L) R
        (grayChargedOwnerFibreV2 hae
          (replay.advantageTerminal.frozen[k]) hp' z)).map Prod.snd) := by
  classical
  intro s hs hs'
  rw [grayChargedFrozenSourcesV2_charge_eq hsm replay hU hae,
    List.map_flatMap, List.mem_flatMap] at hs
  obtain ⟨i, -, hs⟩ := hs
  rw [List.mem_map] at hs
  obtain ⟨w, hw, rfl⟩ := hs
  rw [List.mem_map] at hs'
  obtain ⟨y, hy, hys⟩ := hs'
  have hexitT : replay.advantageExitTime + 1 <= T + 1 := by
    have h1 := replay.advantageDone_le
    have h2 := replay.advantageExit_le
    omega
  by_cases hadvPos : i.val < replay.advantageTerminal.frozen.length
  · -- advantage prefix: dispatch owner / non-owner
    have hpos := grayChargedReplayV2_terminal_getElem_late replay hexitT
      hadvPos i.isLt
    rw [grayChargedTransportRound, List.mem_flatMap] at hw
    obtain ⟨l, hl, hw⟩ := hw
    rw [List.mem_ofFn] at hl
    obtain ⟨j, rfl⟩ := hl
    by_cases hik : i.val = k
    · subst hik
      exact grayChargedV2_ownerRound_transported_ne_complement_at hae
        replay hdata hk hpos
        (List.getElem_mem i.isLt) hp' j hw hy hys.symm
    · exact grayChargedV2_nonOwnerRound_transported_ne_complement_at
        hae replay hdata i.val hadvPos hik hpos
        (List.getElem_mem i.isLt) hw hy hys.symm
  · exact hspend i (Nat.le_of_not_lt hadvPos) w hw y hy hys.symm

/-- The advantage terminal is the exit core plus one freeze, stamped at the
exit time. -/
lemma grayChargedReplayV2_terminal_frozen_eq_concat
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    exists r : GrayTailRoundV2 n (grayTailBranch q L a e),
      replay.advantageTerminal.frozen =
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm replay.advantageDoneTime).core.frozen ++
          [r] ∧
      r.serverTime = replay.advantageDoneTime := by
  classical
  have hdone : (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm replay.advantageDoneTime).core
      (sm replay.advantageDoneTime)).done = true :=
    replay.advantageDone_step
  have hactive : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm replay.advantageDoneTime).core.done = false :=
    replay.advantageDone_active
  set core := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm replay.advantageDoneTime).core with hcoreDef
  have hs : core.slots.isEmpty = false := by
    by_contra hbad
    have hemp : core.slots.isEmpty = true := by
      cases h : core.slots.isEmpty <;> simp_all
    have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core
        (sm replay.advantageDoneTime)).done = false := by
      simp [grayChargedBlockTailStepV2, hactive, hemp]
    rw [hnd] at hdone
    exact Bool.noConfusion hdone
  have hg : grayChargedBlockGoalAtB q L e core.frozen.length
      core.slots.length core.unavailable
      (grayBlockCurrentMoveV2 q L e sigma core)
      (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
        core.slots (sm replay.advantageDoneTime)) = true := by
    by_contra hbad
    have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core
        (sm replay.advantageDoneTime)).done = false := by
      simp [grayChargedBlockTailStepV2, hactive, hs, hbad]
    rw [hnd] at hdone
    exact Bool.noConfusion hdone
  have hfroz := grayChargedBlockTailStepV2_accept_frozen_eq
    q L a e sigma A core (sm replay.advantageDoneTime) hactive hs hg
  have htime : core.time = replay.advantageDoneTime :=
    (grayChargedRunStateV2_coreCertified q L a e sigma A sm
      replay.advantageDoneTime).time_eq
  let r0 : GrayTailRoundV2 n (grayTailBranch q L a e) :=
    { serverTime := core.time
      roundIndex := core.frozen.length
      blockAnchor := grayTailRoundEps q L e core.frozen.length
      childEps := grayTailRoundEps q L e core.frozen.length +
        graySpendSpan q
      fineEnd := grayTailRoundDelta q L e core.frozen.length
      slots := core.slots
      move := grayBlockCurrentMoveV2 q L e sigma core
      allocated := grayTailLocalAllocatedList
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e core.frozen.length) core.slots
          (sm replay.advantageDoneTime))
      unavailable := core.unavailable }
  refine ⟨r0, ?_, htime⟩
  rw [replay.advantageTerminal_frozen_eq]
  exact hfroz

/-- Every position from the last advantage round on carries a server time
at or past the exit. -/
lemma grayChargedReplayV2_late_snapshot_ge
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {jj : Nat}
    (hjj : replay.advantageTerminal.frozen.length - 1 <= jj)
    (hjj' : jj < (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen.length) :
    replay.advantageDoneTime <=
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen[jj]'hjj').serverTime := by
  obtain ⟨r, hconcat, hrtime⟩ :=
    grayChargedReplayV2_terminal_frozen_eq_concat replay
  have hexitT : replay.advantageExitTime + 1 <= T + 1 := by
    have h1 := replay.advantageDone_le
    have h2 := replay.advantageExit_le
    omega
  have hlen : replay.advantageTerminal.frozen.length =
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm
          replay.advantageDoneTime).core.frozen.length + 1 := by
    rw [hconcat]
    simp
  have hpre : replay.advantageTerminal.frozen <+:
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen := by
    rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
    exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A sm hexitT
  have hprelen := hpre.length_le
  have hm : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm replay.advantageDoneTime).core.frozen.length <
      replay.advantageTerminal.frozen.length := by
    omega
  have hlast : replay.advantageTerminal.frozen[
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm
          replay.advantageDoneTime).core.frozen.length]'hm = r := by
    rw [List.getElem_of_eq hconcat hm]
    simp
  have hlateLast : ((grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen[
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm
            replay.advantageDoneTime).core.frozen.length]'(by omega)) =
      r := by
    rw [grayChargedReplayV2_terminal_getElem_late replay hexitT hm
      (by omega)]
    exact hlast
  rcases Nat.lt_or_ge ((grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm
        replay.advantageDoneTime).core.frozen.length) jj with hlt | hge
  · have hchrono := (grayChargedRunStateV2_coreCertified q L a e sigma A
      sm (T + 1)).frozen_chrono _ jj (by omega) hjj' hlt
    rw [hlateLast, hrtime] at hchrono
    omega
  · have heq : (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm
          replay.advantageDoneTime).core.frozen.length = jj := by
      omega
    subst heq
    rw [hlateLast, hrtime]

/-- Late positions are spend rounds: spare slots, coarse fine depth, and
outside the call-depth regime. -/
lemma grayChargedV2_late_position_spend_facts
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (i : Fin (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen.length)
    (hlate : replay.advantageTerminal.frozen.length <= i.val) :
    (forall s, s ∈ ((grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots ->
      grayChargedSourceCount a e <= s.2.1.val) ∧
    ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen[i.val]).fineEnd <= e ∧
    ¬ grayCallDepth q e <= ((grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor := by
  have hexitT : replay.advantageExitTime + 1 <= T + 1 := by
    have h1 := replay.advantageDone_le
    have h2 := replay.advantageExit_le
    omega
  have hcert := grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm (T + 1)
  have hvalid := hcert.round_valid _ (List.getElem_mem i.isLt)
  -- the round cannot sit in the advantage prefix: its recorded index is late
  have hindex := hcert.frozen_index i.val i.isLt
  have hnadv : ¬ grayCallDepth q e <=
      ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen[i.val]).blockAnchor := by
    rcases grayChargedRunStateV2_frozen_post_exit_spend hae replay hexitT
        _ (List.getElem_mem i.isLt) with hterm | hnadv
    · exfalso
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hterm
      have hjlate := grayChargedReplayV2_terminal_getElem_late replay
        hexitT hj (by
          have hpre : replay.advantageTerminal.frozen <+:
              (grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen := by
            rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
            exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A
              sm hexitT
          have := hpre.length_le
          omega)
      have hjindex := hcert.frozen_index j (by
        have hpre : replay.advantageTerminal.frozen <+:
            (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e)
              q L a e sigma A sm (T + 1)).core.frozen := by
          rw [← grayChargedReplayV2_advantageTerminal_frozen_eq replay]
          exact grayChargedRunStateV2_frozen_prefix_le q L a e sigma A
            sm hexitT
        have := hpre.length_le
        omega)
      rw [hjlate, hjeq] at hjindex
      omega
    · exact hnadv
  rcases hvalid.2.2.2.2.2 with ⟨h1, -, -, -, -, -⟩ |
    ⟨pass, -, hanchor, hfineEnd, -, hslots, -⟩
  · exfalso
    apply hnadv
    rw [h1, grayTailRoundEps]
    exact Nat.le_add_right _ _
  · refine ⟨?_, ?_, hnadv⟩
    · intro s hs
      exact grayBlockSpendPairs_first_ge (hslots s hs)
    · rw [hfineEnd, grayChargedSpendDelta, grayChargedSpendEps,
        grayChargedSpendAlphaDepth]
      have hLr : L <= (pass + 1) * L :=
        Nat.le_mul_of_pos_left L (by omega)
      rcases max_choice (a + 3) (e - (pass + 1) * L) with hm | hm <;>
        rw [hm] <;> omega

/-- **The spend side, discharged for exit-time reserves**: with the datum's
reserve taken at the advantage exit, every spend-position transported cell
avoids the complement — the exit time precedes every spend snapshot, so
the persisted trigger is harvested. -/
theorem grayChargedV2_exitReserve_spend_side
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {z : Fin n × Fin (grayTailBranch q L a e)} {R : BitString} {k : Nat}
    (hdata : GrayChargedSonReserveDataV2 replay z
      replay.advantageDoneTime R k)
    (hRlen : R.length = e)
    (hzsrc : z.2.val < grayChargedSourceCount a e)
    (hk : k < replay.advantageTerminal.frozen.length)
    (hp' : replay.advantageTerminal.frozen[k] ∈
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen) :
    forall i : Fin (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.length,
      replay.advantageTerminal.frozen.length <= i.val ->
      forall w, w ∈ grayChargedTransportRound (e + grayTailNewLoss q L)
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots
          (grayChargedRoundLocalChargeV2 hae _
            (List.getElem_mem i.isLt)) ->
      forall y, y ∈ grayChargedReserveComplementV2 z.1.val
          (e + grayTailNewLoss q L) R
          (grayChargedOwnerFibreV2 hae
            (replay.advantageTerminal.frozen[k]) hp' z) ->
        w.2 ≠ y.2 := by
  intro i hlate w hw y hy
  obtain ⟨hspare, hfineE, -⟩ :=
    grayChargedV2_late_position_spend_facts hae hpin replay i hlate
  have hiLt := i.isLt
  obtain ⟨s0, hsOK, hchain0⟩ := (grayChargedRunStateV2_coreCertified (n := n)
    q L a e sigma A sm (T + 1)).frozen_chain i.val i.isLt
  have hsne : s0 ≠ none := by
    intro hnone
    have htake := hsOK.1 hnone
    have hlen : ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.take i.val).length = i.val :=
      List.length_take_of_le (le_of_lt i.isLt)
    rw [htake] at hlen
    simp at hlen
    omega
  obtain ⟨tsnap, htsnap⟩ := Option.ne_none_iff_exists'.mp hsne
  have hsnap : replay.advantageDoneTime <= tsnap := by
    have hge := grayChargedReplayV2_late_snapshot_ge replay
      (jj := i.val - 1) (by omega) (by omega)
    have hlen : i.val - 1 < ((grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen.take i.val).length := by
      rw [List.length_take_of_le (le_of_lt i.isLt)]
      omega
    have hmem : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (T + 1)).core.frozen[i.val - 1]'(by omega) ∈
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen.take i.val := by
      have := List.getElem_mem hlen
      rwa [List.getElem_take] at this
    exact le_trans hge ((hsOK.2 tsnap htsnap).2 _ hmem)
  rw [htsnap] at hchain0
  simp only [grayHarvestSnapshot] at hchain0
  rw [grayChargedTransportRound, List.mem_flatMap] at hw
  obtain ⟨l, hl, hw⟩ := hw
  rw [List.mem_ofFn] at hl
  obtain ⟨j, rfl⟩ := hl
  refine grayChargedV2_spendRound_transported_ne_complement hsm hae
    (List.getElem_mem i.isLt) hchain0 hspare hfineE hzsrc hsnap hdata.1 hRlen
    hw hy

/-- **Full unconditional disjointness for the server-resolved class**: at
the pinned gap, every server-resolved son carries an exit-time reserve
whose owner-aligned complement avoids the ENTIRE recursive ledger —
advantage rounds by the datum, spend rounds by the harvested trigger. -/
theorem grayChargedV2_serverResolved_full_disjoint
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (z : Fin n × Fin (grayTailBranch q L a e))
    (hz : z ∈ grayChargedReplayV2ServerResolvedSources replay) :
    exists (R : BitString) (k : Nat)
      (hk : k < replay.advantageTerminal.frozen.length)
      (hp' : replay.advantageTerminal.frozen[k] ∈
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen),
      GrayChargedSonReserveDataV2 replay z
        replay.advantageDoneTime R k ∧
      List.Disjoint
        ((grayChargedSourceChargeV2
          (grayChargedFrozenSourcesV2 hsm replay hU hae)).map Prod.snd)
        ((grayChargedReserveComplementV2 z.1.val
          (e + grayTailNewLoss q L) R
          (grayChargedOwnerFibreV2 hae
            (replay.advantageTerminal.frozen[k]) hp' z)).map
              Prod.snd) := by
  classical
  obtain ⟨R, k, hdata⟩ :=
    grayChargedReplayV2_serverResolved_exit_datum hsm replay z hz
  have hk := grayChargedSonReserveDataV2_owner_lt hdata
  have hexitT : replay.advantageDoneTime + 1 <= T + 1 := by
    have h1 := replay.advantageDone_le
    have h2 := replay.advantageExit_le
    omega
  have hp' := grayChargedReplayV2_terminal_round_mem_late replay hexitT
    (List.getElem_mem hk)
  have hRlen : R.length = e := hdata.1.1.1
  have hz2 : z ∈ grayChargedServerResolvedSources e
      (grayChargedSourceCount a e) (grayChargedThreshold q e) A
      (frozenV1OfV2 replay.advantageTerminal)
      (sm replay.advantageDoneTime) := hz
  have hzsrc : z.2.val < grayChargedSourceCount a e :=
    (Finset.mem_filter.mp hz2).2.1
  refine ⟨R, k, hk, hp', hdata, ?_⟩
  exact grayChargedV2_source_complement_disjoint hsm hae replay hU hdata
    hk hp'
    (grayChargedV2_exitReserve_spend_side hsm hae hpin replay hdata hRlen
      hzsrc hk hp')

/-- Per-record disjointness flattens to the family charge. -/
lemma grayChargedV2_ledger_disjoint_reserveCharge_of_forall
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (SRC : List BitString)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hall : forall r, r ∈ reserves ->
      List.Disjoint SRC ((r.cells).map Prod.snd)) :
    List.Disjoint SRC
      ((grayChargedReserveChargeV2 reserves).map Prod.snd) := by
  intro s hs hs'
  rw [grayChargedReserveChargeV2, List.map_flatMap, List.mem_flatMap] at hs'
  obtain ⟨r, hr, hs'⟩ := hs'
  exact hall r hr hs hs'

/-- Every record of `reserves` carries its *reserve datum*: an index `k` of a frozen advantage
round of `replay` that is still a round of the charged run at time `T + 1`, the son-reserve
data of the record at that round, and the identification of the record's cells with the
complement of the owner fibre of the round. -/
def GrayChargedReserveDataAll {q L a e n T U : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) : Prop :=
  forall r, r ∈ reserves ->
    exists (k : Nat)
      (hk : k < replay.advantageTerminal.frozen.length)
      (hp' : replay.advantageTerminal.frozen[k] ∈
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (T + 1)).core.frozen),
      GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
        r.reserve k ∧
      r.cells = grayChargedReserveComplementV2 r.coordinate.1.val
        (e + grayTailNewLoss q L) r.reserve
        (grayChargedOwnerFibreV2 hae
          (replay.advantageTerminal.frozen[k]) hp' r.coordinate)

/-- A *reduced reserve family* for `replay`: every record is covered by a raised or
server-resolved source, carries its reserve datum, is timed at the advantage-done time when
its coordinate is server-resolved, and is served no later than the advantage exit.  These are
the four conditions the reduced-reserve bookkeeping always establishes together. -/
structure GrayChargedReducedReserves {q L a e n T U : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) : Prop where
  /-- Every coordinate is raised or server-resolved. -/
  cover_back : forall r, r ∈ reserves -> r.coordinate ∈
    grayChargedReplayV2RaisedSources replay ∪
      grayChargedReplayV2ServerResolvedSources replay
  /-- Every record carries its reserve datum. -/
  datum : GrayChargedReserveDataAll hae replay reserves
  /-- A server-resolved coordinate is served exactly at the advantage-done time. -/
  server_resolved_time : forall r, r ∈ reserves ->
    r.coordinate ∈ grayChargedReplayV2ServerResolvedSources replay ->
    r.serviceTime = replay.advantageDoneTime
  /-- No record is served after the advantage exit. -/
  service_le_exit : forall r, r ∈ reserves -> r.serviceTime <= replay.advantageExitTime

/-- **L5 leaf 1 for the mixed complement family, reduced to the raised
straddle**: the recursive ledger is physically disjoint from the family's
reserve charge, given only the spend-side hypothesis for the
raised-and-not-server-resolved records — the exact residue of Gács's
unproved sentence. -/
theorem grayChargedV2_family_reserve_disjoint_of_straddle
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hpin : e = a + 8 * L + 3)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U)
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hdatumAll : forall r, r ∈ reserves ->
      exists (k : Nat)
        (hk : k < replay.advantageTerminal.frozen.length)
        (hp' : replay.advantageTerminal.frozen[k] ∈
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen),
        GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
          r.reserve k ∧
        r.cells = grayChargedReserveComplementV2 r.coordinate.1.val
          (e + grayTailNewLoss q L) r.reserve
          (grayChargedOwnerFibreV2 hae
            (replay.advantageTerminal.frozen[k]) hp' r.coordinate))
    (hsrflag : forall r, r ∈ reserves ->
      r.coordinate ∈ grayChargedReplayV2ServerResolvedSources replay ->
      r.serviceTime = replay.advantageDoneTime)
    (hstraddle : forall r, r ∈ reserves ->
      r.coordinate ∉ grayChargedReplayV2ServerResolvedSources replay ->
      forall (k : Nat)
        (hk : k < replay.advantageTerminal.frozen.length)
        (hp' : replay.advantageTerminal.frozen[k] ∈
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen),
        GrayChargedSonReserveDataV2 replay r.coordinate r.serviceTime
          r.reserve k ->
        forall i : Fin (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen.length,
          replay.advantageTerminal.frozen.length <= i.val ->
          forall w, w ∈ grayChargedTransportRound
              (e + grayTailNewLoss q L)
              ((grayChargedRunStateV2 (n := n)
                (b := grayTailBranch q L a e)
                q L a e sigma A sm (T + 1)).core.frozen[i.val]).slots
              (grayChargedRoundLocalChargeV2 hae _
                (List.getElem_mem i.isLt)) ->
          forall y, y ∈ grayChargedReserveComplementV2 r.coordinate.1.val
              (e + grayTailNewLoss q L) r.reserve
              (grayChargedOwnerFibreV2 hae
                (replay.advantageTerminal.frozen[k]) hp'
                r.coordinate) ->
            w.2 ≠ y.2) :
    List.Disjoint
      ((grayChargedSourceChargeV2
        (grayChargedFrozenSourcesV2 hsm replay hU hae)).map Prod.snd)
      ((grayChargedReserveChargeV2 reserves).map Prod.snd) := by
  classical
  apply grayChargedV2_ledger_disjoint_reserveCharge_of_forall
  intro r hr
  obtain ⟨k, hk, hp', hdata, hcells⟩ := hdatumAll r hr
  rw [hcells]
  by_cases hsr : r.coordinate ∈
      grayChargedReplayV2ServerResolvedSources replay
  · have htime := hsrflag r hr hsr
    rw [htime] at hdata
    have hRlen : r.reserve.length = e := hdata.1.1.1
    have hz2 : r.coordinate ∈ grayChargedServerResolvedSources e
        (grayChargedSourceCount a e) (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime) := hsr
    have hzsrc : r.coordinate.2.val < grayChargedSourceCount a e :=
      (Finset.mem_filter.mp hz2).2.1
    exact grayChargedV2_source_complement_disjoint hsm hae replay hU
      hdata hk hp'
      (grayChargedV2_exitReserve_spend_side hsm hae hpin replay hdata
        hRlen hzsrc hk hp')
  · exact grayChargedV2_source_complement_disjoint hsm hae replay hU
      hdata hk hp' (hstraddle r hr hsr k hk hp' hdata)

end Kolmogorov
