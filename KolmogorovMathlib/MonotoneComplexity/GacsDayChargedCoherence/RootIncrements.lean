import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedOuterSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRequestWindow
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTerminationSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedCoherence.LegalOuterMoves

/-!
# How much a charged round adds at the root of a client

The budget side of coherence. `GrayChargedSpendPassMove` and
`GrayChargedAdvantageFrozenCaps` package the data of a state caught mid-pass and the two caps its
frozen table carries. In the spend phase `grayChargedRootIncrement_spend_upper` bounds the
increment of one pass by the dyadic scale and `grayCharged_spend_root_cap` bounds the accumulated
root request; in the advantage phase the same is done through
`grayCharged_advantage_son_base_le` and `grayCharged_advantage_root_cap`. The conclusion
`grayCharged_display_root_cap` bounds by `dyadicScale a` the amount the displayed move puts at
the root of any client.
-/

namespace Kolmogorov

/-- The data of a state `core` caught in the middle of the spend pass `pass`, together with the
client move `move` it is about to display: the exponent window `a ≤ e`, the pass index
`pass < 8`, the fact that the active slots of `core` are exactly the slots of the pass, the
spend window invariant of its frozen table, and the coherence of `move` on every slot of the
pass.  The five facts always travel together in the spend branch of the outer-coherence
induction. -/
structure GrayChargedSpendPassMove {n : Nat} (q L a e pass : Nat)
    (core : GrayTailState n (grayTailBranch q L a e)) (move : FamilyClientMove) : Prop where
  /-- The tail exponent does not exceed the call exponent. -/
  alpha_le : a <= e
  /-- There are eight spend passes. -/
  pass_lt : pass < 8
  /-- The active slots of `core` are the slots of the pass. -/
  slots_eq : core.slots = grayChargedSlotsForPass q a e pass core.frozen
  /-- The frozen table of `core` satisfies the spend window invariant. -/
  window : GrayChargedSpendWindow q a e pass core.frozen
  /-- The displayed move is coherent, with the spend cap, on every slot of the pass. -/
  move_coherent : ∀ j < (grayChargedSlotsForPass q a e pass core.frozen).length,
    requestCoherentCap (grayTailBranch q L a e)
      (dyadicScale (grayChargedSpendAlphaDepth a)) (familyClientMoveAt move j)

/-- The two caps carried by the frozen table of `core` in the advantage phase: every source son
of every client is at most `dyadicScale e`, and every son held by an active slot is at most the
charged threshold. -/
structure GrayChargedAdvantageFrozenCaps {n : Nat} (q L a e : Nat)
    (core : GrayTailState n (grayTailBranch q L a e)) : Prop where
  /-- Source sons of the frozen table are at most `dyadicScale e`. -/
  source_cap : ∀ i : Fin n, ∀ c : Fin (grayTailBranch q L a e),
    c.val < grayChargedSourceCount a e ->
      grayTailFrozenSonBase core.frozen i c <= dyadicScale e
  /-- Sons held by an active slot are at most the charged threshold. -/
  active_cap : ∀ s ∈ core.slots,
    grayTailFrozenSonBase core.frozen s.1 s.2.1 <= grayChargedThreshold q e

/-- A coherent spend pass increases the root request of a client by at most `dyadicScale a / 8`,
so that the eight passes together stay inside `dyadicScale a`. -/
lemma grayChargedRootIncrement_spend_upper
    {q L a e n pass : Nat}
    (hae : a <= e) (hpass : pass < 8)
    (frozen : GrayTailFrozen n (grayTailBranch q L a e))
    (move : FamilyClientMove)
    (hcoh : ∀ j <
      (grayChargedSlotsForPass q a e pass frozen).length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayChargedSpendAlphaDepth a))
        (familyClientMoveAt move j))
    (i : Fin n) :
    grayChargedRootIncrement
        (grayTailSlotEntries
          (grayChargedSlotsForPass q a e pass frozen) move) i <=
      dyadicScale a / 8 := by
  let slots := grayChargedSlotsForPass q a e pass frozen
  change grayChargedRootIncrement
      (grayTailSlotEntries slots move) i <= dyadicScale a / 8
  by_cases hi : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) frozen
  · let rootslots := Finset.univ.filter
      fun j : Fin slots.length => (slots.get j).1 = i
    have hcard : rootslots.card = grayChargedSpendCount q a e := by
      calc
        rootslots.card =
            (slots.filter fun s => decide (s.1 = i)).length := by
              simpa [rootslots, List.get_eq_getElem] using
                grayCharged_filter_index_card slots i
        _ = grayChargedSpendCount q a e := by
          dsimp [slots, grayChargedSlotsForPass]
          rw [grayChargedSpendSlots_filter_root_length, ite_eq_left hi,
            grayChargedSpendPairs_length (q := q) (L := L) hae hpass]
    have hsum :
        grayChargedRootIncrement (grayTailSlotEntries slots move) i =
          ∑ j ∈ rootslots, getFamilyReq move j.val [] := by
      rw [grayChargedRootIncrement_slotEntries_eq_sum]
      dsimp [rootslots]
      rw [Finset.sum_filter]
    rw [hsum]
    calc
      (∑ j ∈ rootslots, getFamilyReq move j.val []) <=
          ∑ _j ∈ rootslots,
            dyadicScale (grayChargedSpendAlphaDepth a) := by
            apply Finset.sum_le_sum
            intro j hj
            exact (hcoh j.val j.isLt).2.1
      _ = (rootslots.card : Rat) *
            dyadicScale (grayChargedSpendAlphaDepth a) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = (grayChargedSpendCount q a e : Rat) *
            dyadicScale (grayChargedSpendAlphaDepth a) := by rw [hcard]
      _ = dyadicScale a / 8 := grayChargedSpendCount_mass hae
  · rw [grayChargedRootIncrement_spend_eq_zero
      (q := q) (L := L) (a := a) (e := e)
      (pass := pass) frozen move i hi]
    exact div_nonneg (dyadicScale_pos a).le (by norm_num)

/-- In the `spend` phase, under the spend window invariant and a coherent spend move,
the root request of each client stays at most `dyadicScale a`. -/
private lemma grayCharged_spend_root_cap
    {q L a e n pass : Nat}
    {core : GrayTailState n (grayTailBranch q L a e)}
    {move : FamilyClientMove}
    (hspend : GrayChargedSpendPassMove q L a e pass core move)
    (i : Fin n) :
    grayChargedRootRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e)
        (grayTailEntries core.frozen core.slots move) i <=
      dyadicScale a := by
  obtain ⟨hae, hpass, hslots_eq, hwindow, hcoh⟩ := hspend
  have hspare :
      ∀ z ∈ grayTailSlotEntries core.slots move,
        grayChargedSourceCount a e <= z.1.2.1.val := by
    intro z hz
    have hzCore : z.1 ∈ core.slots := by
      rw [grayTailSlotEntries, List.mem_ofFn] at hz
      obtain ⟨j, rfl⟩ := hz
      exact List.get_mem _ _
    have hzSpend : z.1 ∈
        grayChargedSlotsForPass q a e pass core.frozen := by
      rw [← hslots_eq]
      exact hzCore
    exact grayChargedSpendSlots_son_ge
      (by simpa [grayChargedSlotsForPass] using hzSpend)
  have hsplit := grayChargedRootIncrement_append_spare
    (source := grayChargedSourceCount a e) (grayChargedThreshold q e)
    (dyadicScale e) (grayTailFrozenEntries core.frozen)
    (grayTailSlotEntries core.slots move) hspare i
  have hinc : grayChargedRootIncrement
      (grayTailSlotEntries core.slots move) i <=
    dyadicScale a / 8 := by
    have hupper := grayChargedRootIncrement_spend_upper
      (q := q) (L := L) (a := a) (e := e)
      hae hpass core.frozen move hcoh i
    simpa [hslots_eq] using hupper
  rw [grayTailEntries, hsplit]
  by_cases hi : i ∈ grayChargedDeficientRoots
      (grayChargedSourceCount a e) (grayChargedThreshold q e)
      (dyadicScale e) (dyadicScale a) core.frozen
  · have hfrozen :
        grayChargedFrozenRootRequest q a e core.frozen i <
          dyadicScale a / 2 :=
      (mem_grayChargedDeficientRoots_iff
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e) (dyadicScale a) core.frozen i).1 hi
    change grayChargedFrozenRootRequest q a e core.frozen i +
        grayChargedRootIncrement
          (grayTailSlotEntries core.slots move) i <= dyadicScale a
    linarith [dyadicScale_pos a]
  · have hzero := grayChargedRootIncrement_spend_eq_zero
      (q := q) (L := L) (a := a) (e := e)
      (pass := pass) core.frozen move i hi
    have hzero' :
        grayChargedRootIncrement
          (grayTailSlotEntries core.slots move) i = 0 := by
      simpa [hslots_eq] using hzero
    change grayChargedFrozenRootRequest q a e core.frozen i +
        grayChargedRootIncrement
          (grayTailSlotEntries core.slots move) i <= dyadicScale a
    rw [hzero', add_zero]
    exact (hwindow i).2.1

/-- In the `advantage` phase, the base request at any source son `c` of client `i`
is bounded by `dyadicScale e`. -/
private lemma grayCharged_advantage_son_base_le
    {q L a e n : Nat}
    {core : GrayTailState n (grayTailBranch q L a e)}
    {current : FamilyClientMove}
    (hcaps : GrayChargedAdvantageFrozenCaps q L a e core)
    (i : Fin n)
    (hslotBase : ∀ c : Fin (grayTailBranch q L a e),
      grayTailSonBase
          (grayTailSlotEntries core.slots current) i c <=
        dyadicScale (grayCallDepth q e))
    (c : Fin (grayTailBranch q L a e))
    (hc : c.val < grayChargedSourceCount a e) :
    grayTailSonBase
        (grayTailEntries core.frozen core.slots current) i c <=
      dyadicScale e := by
  obtain ⟨hsourceCap, hactive⟩ := hcaps
  rw [grayTailEntries, grayTailSonBase_append_globalEntries]
  by_cases hhas : GrayTailHasKey core.slots i c
  · obtain ⟨s, hs, hi, hc'⟩ := hhas
    have hfrozen : grayTailFrozenSonBase core.frozen i c <=
        grayChargedThreshold q e := by
      simpa [hi, hc'] using hactive s hs
    have hadd := grayTail_callScale_add_threshold_le q e
    change grayTailFrozenSonBase core.frozen i c +
        grayTailSonBase
          (grayTailSlotEntries core.slots current) i c <= dyadicScale e
    exact le_trans (add_le_add hfrozen (hslotBase c)) (by
      simpa [grayChargedThreshold] using hadd)
  · have hzero :
        grayTailSonBase
          (grayTailSlotEntries core.slots current) i c = 0 :=
      grayTailSonBase_eq_zero_of_not_hasKey i c hhas
    change grayTailFrozenSonBase core.frozen i c +
        grayTailSonBase
          (grayTailSlotEntries core.slots current) i c <= dyadicScale e
    rw [hzero, add_zero]
    exact hsourceCap i c hc

/-- In the `advantage` phase, under the source and shape invariants and a coherent current move,
the root request of each client stays at most `dyadicScale a`. -/
lemma grayCharged_advantage_root_cap
    {q L a e n : Nat}
    {core : GrayTailState n (grayTailBranch q L a e)}
    {current : FamilyClientMove}
    (hae : a <= e)
    (hsource : GrayTailSourceInvariant
      (grayChargedSourceCount a e) core)
    (hshape : GrayTailShape core)
    (hsourceCap : ∀ i : Fin n,
      ∀ c : Fin (grayTailBranch q L a e),
        c.val < grayChargedSourceCount a e ->
          grayTailFrozenSonBase core.frozen i c <= dyadicScale e)
    (hactive : ∀ s ∈ core.slots,
      grayTailFrozenSonBase core.frozen s.1 s.2.1 <=
        grayChargedThreshold q e)
    (hcurrent : ∀ j < core.slots.length,
      requestCoherentCap (grayTailBranch q L a e)
        (dyadicScale (grayCallDepth q e))
        (familyClientMoveAt current j))
    (i : Fin n) :
    grayChargedRootRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e)
        (grayTailEntries core.frozen core.slots current) i <=
      dyadicScale a := by
  let entries := grayTailEntries core.frozen core.slots current
  have hslotBase (c : Fin (grayTailBranch q L a e)) :
      grayTailSonBase
          (grayTailSlotEntries core.slots current) i c <=
        dyadicScale (grayCallDepth q e) := by
    apply grayTailSonBase_le_of_slot_request_bounds
      (dyadicScale_pos _).le hshape.slots_nodup hshape.slots_round
    · intro j
      exact (hcurrent j.val j.isLt).1 []
    · intro j
      exact (hcurrent j.val j.isLt).2.1
  have hbase (c : Fin (grayTailBranch q L a e))
      (hc : c.val < grayChargedSourceCount a e) :
      grayTailSonBase entries i c <= dyadicScale e :=
    grayCharged_advantage_son_base_le ⟨hsourceCap, hactive⟩ i hslotBase c hc
  have hson : ∀ c : Fin (grayTailBranch q L a e),
      grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c <=
        if c.val < grayChargedSourceCount a e then dyadicScale e else 0 := by
    intro c
    by_cases hc : c.val < grayChargedSourceCount a e
    · unfold grayChargedSonRequest grayTailSonRequest
      simp only [ite_eq_left hc]
      by_cases hlarge :
          grayChargedThreshold q e < grayTailSonBase entries i c
      · rw [ite_eq_left hlarge]
      · rw [ite_eq_right hlarge]
        exact hbase c hc
    · have hzero : grayTailSonBase entries i c = 0 := by
        exact grayTailSonBase_eq_zero_of_sourceInvariant
          hsource current i c (Nat.le_of_not_gt hc)
      have hc' : Not (c.val < 2 ^ (e - a)) := by
        simpa [grayChargedSourceCount] using hc
      unfold grayChargedSonRequest
      simp [hc', hzero]
  unfold grayChargedRootRequest
  calc
    (∑ c : Fin (grayTailBranch q L a e),
        grayChargedSonRequest
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) entries i c) <=
        ∑ c : Fin (grayTailBranch q L a e),
          if c.val < grayChargedSourceCount a e then
            dyadicScale e else 0 := by
              apply Finset.sum_le_sum
              intro c hc
              exact hson c
    _ = ∑ c ∈ Finset.univ.filter
          (fun c : Fin (grayTailBranch q L a e) =>
            c.val < grayChargedSourceCount a e), dyadicScale e := by
              rw [Finset.sum_filter]
    _ = ((Finset.univ.filter
          (fun c : Fin (grayTailBranch q L a e) =>
            c.val < grayChargedSourceCount a e)).card : Rat) *
          dyadicScale e := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (grayChargedSourceCount a e : Rat) * dyadicScale e := by
      apply mul_le_mul_of_nonneg_right _ (dyadicScale_pos e).le
      exact_mod_cast grayTail_source_fin_card_le
        (grayTailBranch q L a e) (grayChargedSourceCount a e)
    _ = dyadicScale a := grayChargedSource_mass hae

/-- Against a legal server play, the move displayed by the charged run puts at most
`dyadicScale a` at the root of each client, in every phase. -/
theorem grayCharged_display_root_cap
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (ha : 1 <= a) (hae : a <= e)
    (hroom : a + 8 * L + 3 <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (i : Fin n) :
    let st := grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t
    let current : FamilyClientMove := match st.phase with
      | .done => []
      | .advantage => if st.core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma st.core
      | .spend pass => if st.core.slots.isEmpty then []
        else grayChargedSpendMove q L a e pass sigma st.core
    grayChargedRootRequest
        (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (dyadicScale e)
        (grayTailEntries st.core.frozen st.core.slots current) i <=
      dyadicScale a := by
  dsimp only
  have hinvariant := grayChargedRequestInvariant_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) hae t
  have hsourceCap := grayChargedSourceBaseCap_stateAt
    (q := q) (L := L) (a := a) (e := e)
    (n := n) (sigma := sigma) (A := A) (sm := sm) (t := t)
  have hcurrent := grayChargedCurrentMove_stateAt_coherent
    (t := t) ha hae hB hRung hsm
  have hcurrentSpend := grayChargedSpendMove_stateAt_coherent
    (t := t) hroom hB hRung hsm
  have hcert := grayChargedCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  generalize hst :
    grayChargedStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t = st at hinvariant hsourceCap hcurrent hcurrentSpend hcert ⊢
  cases hcert with
  | advantage core hcore hsource hactive =>
      have hcoreTail' : core = grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t := by
        have hcoreTail := grayChargedStateAt_core_eq_tailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t (by rw [hst])
        simpa [hst] using hcoreTail
      have hactiveBase : ∀ s ∈ core.slots,
          grayTailFrozenSonBase core.frozen s.1 s.2.1 <=
            grayChargedThreshold q e := by
        have h := grayChargedTail_active_base_le_stateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t
        rwa [← hcoreTail'] at h
      let current : FamilyClientMove :=
        if core.slots.isEmpty then []
        else grayTailCurrentMove q L e sigma core
      have hcur : ∀ j < core.slots.length,
          requestCoherentCap (grayTailBranch q L a e)
            (dyadicScale (grayCallDepth q e))
            (familyClientMoveAt current j) := by
        by_cases hempty : core.slots.isEmpty
        · intro j hj
          have hlen : core.slots.length = 0 :=
            List.isEmpty_iff_length_eq_zero.mp hempty
          omega
        · have hne : 1 <= core.slots.length := by
            cases hs : core.slots with
            | nil => simp [hs] at hempty
            | cons x xs => exact Nat.succ_pos _
          intro j hj
          dsimp [current]
          rw [ite_eq_right hempty]
          exact hcurrent rfl hne j hj
      exact grayCharged_advantage_root_cap
        hae hsource hcore.shape
        (by simpa [GrayChargedSourceBaseCap] using hsourceCap)
        hactiveBase hcur i
  | spend pass core hspend =>
      have hempty : core.slots.isEmpty = false := hspend.slots_nonempty
      have hne : 1 <= core.slots.length := by
        cases hs : core.slots with
        | nil => simp [hs] at hempty
        | cons x xs => exact Nat.succ_pos _
      have hcur : ∀ j < (grayChargedSlotsForPass q a e pass core.frozen).length,
          requestCoherentCap (grayTailBranch q L a e)
            (dyadicScale (grayChargedSpendAlphaDepth a))
            (familyClientMoveAt
              (grayChargedSpendMove q L a e pass sigma core) j) := by
        intro j hj
        have hj' : j < core.slots.length := by
          simpa [hspend.slots_eq] using hj
        exact hcurrentSpend pass rfl hne j hj'
      have hwindow : GrayChargedSpendWindow q a e pass core.frozen := by
        simpa [GrayChargedRequestInvariant] using hinvariant
      have hgoal := grayCharged_spend_root_cap
        ⟨hae, hspend.pass_lt, hspend.slots_eq, hwindow, hcur⟩ i
      simpa [hempty] using hgoal
  | done core hdone =>
      have hwindow : GrayChargedDoneWindow q a e core.frozen := by
        simpa [GrayChargedRequestInvariant] using hinvariant
      simpa [grayTailEntries, hdone.slots_empty,
        grayTailSlotEntries, grayChargedFrozenRootRequest] using
        (hwindow i).2

end Kolmogorov
