import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RoundReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailDisplay

/-!
# An unserved positive sub-game request is an outer positive win (V2)

The V2 analogue of `grayChargedTail_round_positive_of_not_gray`: when the
recursive round's client wins its sub-game by an unserved positive request and
the round's block goal is never accepted, the V2 charged run stays in the
round, displays the transported request two levels down at the owning outer
root, and the outer server never serves it — the outer client wins
`GrayChargedPositiveV2`.
-/

namespace Kolmogorov

/-- The local allocation seen by slot `j` of the V2 future server is the
truncated outer allocation two levels down. -/
lemma getFamilyAlloc_grayBlockFutureServerV2
    {n b q L e : Nat} {st : GrayTailStateV2 n b}
    {sm : Nat -> FamilyServerMove}
    (j : Fin st.slots.length) (u : Nat) (x : GacsDayNode)
    (hx : ∀ c ∈ x, c < b) :
    let s := st.slots.get j
    getFamilyAlloc (grayBlockFutureServerV2 q L e st sm u) j.val x =
      truncAlloc (grayTailRoundDelta q L e st.frozen.length)
        (getFamilyAlloc (sm (st.roundStart + u)) s.1.val
          (s.2.1.val :: s.2.2.val :: x)) := by
  dsimp only
  unfold grayBlockFutureServerV2
  rw [getFamilyAlloc_grayTailLocalServerMove st.slots _ j.val j.isLt x hx]
  simp [getFamilyAlloc, getAlloc_extractSubtreeServerMove]

/-- The frozen slots of the V1 projection are the V2 frozen slots. -/
lemma grayTailFrozenSlots_map_toV1 {n b : Nat}
    (frozen : List (GrayTailRoundV2 n b)) :
    grayTailFrozenSlots (frozen.map GrayTailRoundV2.toV1) =
      grayTailFrozenSlotsV2 frozen := by
  simp [grayTailFrozenSlots, grayTailFrozenSlotsV2, List.flatMap_map,
    GrayTailRoundV2.toV1]

/-- The V2 family-move transfer of an unserved positive local request
(mirror of `grayChargedTailFamilyMove_transfers_positive` on the V2 future
server). -/
theorem grayChargedBlockV2_familyMove_transfers_positive
    {n b q L e h T source : Nat} {threshold eps : Rat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {cm : Nat -> FamilyClientMove}
    {st : GrayTailStateV2 n b}
    (hsm : familyServerPlayLegal n b A sm)
    (hkeys : (grayTailFrozenSlots (st.frozen.map GrayTailRoundV2.toV1) ++
      st.slots).Nodup)
    (hdisplay : cm T =
      grayChargedTailFamilyMove source threshold eps
        (st.frozen.map GrayTailRoundV2.toV1) st.slots
        (grayBlockCurrentMoveV2 q L e sigma st))
    (j : Fin st.slots.length) (x : GacsDayNode)
    (hlen : x.length ≤ h) (hin : ∀ d ∈ x, d < b)
    (hmin : (1 / 2 : Rat) ^ (grayTailRoundDelta q L e st.frozen.length) ≤
      getFamilyReq (grayBlockCurrentMoveV2 q L e sigma st) j.val x)
    (hfail : ∀ u,
      ¬ Serves (getFamilyAlloc (grayBlockFutureServerV2 q L e st sm u) j.val x)
        (getFamilyReq (grayBlockCurrentMoveV2 q L e sigma st) j.val x))
    (hpos : 0 < getFamilyReq (grayBlockCurrentMoveV2 q L e sigma st) j.val x) :
    familyClientWinsUnservedPositive n (h + 2) b cm sm := by
  let s := st.slots.get j
  let y : GacsDayNode := s.2.1.val :: s.2.2.val :: x
  have hreq :
      getFamilyReq (cm T) s.1.val y =
        getFamilyReq (grayBlockCurrentMoveV2 q L e sigma st) j.val x := by
    rw [hdisplay]
    exact grayChargedTailFamilyMove_current_req hkeys j x
  refine ⟨s.1.val, s.1.isLt, T, y, ?_, ?_, ?_, ?_⟩
  · simp [y]
    omega
  · intro d hd
    simp only [y, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact s.2.1.isLt
    · exact s.2.2.isLt
    · exact hin d hd
  · intro u hserves
    apply hfail (max u st.roundStart - st.roundStart)
    have hmono := serves_mono_time
      (hsm.1 s.1.val s.1.isLt) (le_max_left u st.roundStart) hserves
    change Serves
      (getFamilyAlloc (sm (max u st.roundStart)) s.1.val y)
      (getFamilyReq (cm T) s.1.val y) at hmono
    rw [hreq] at hmono
    rw [getFamilyAlloc_grayBlockFutureServerV2 j
      (max u st.roundStart - st.roundStart) x hin]
    rw [Nat.add_sub_of_le (le_max_right u st.roundStart)]
    exact (serves_truncAlloc_iff hmin).mpr hmono
  · change 0 < getFamilyReq (cm T) s.1.val y
    rw [hreq]
    exact hpos

/-- The V2 charged run's displayed move in an active advantage round is the
family move of the current block move. -/
lemma grayChargedRunMoveV2_eq_of_advantage
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hactive : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = false)
    (hslots : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots.isEmpty = false) :
    playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots
        (grayBlockCurrentMoveV2 q L e sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core) := by
  rw [playClientFamily_grayChargedStrategyV2]
  simp [grayChargedDisplayedMoveV2, hphase, hactive, hslots]

/-- The advantage phase persists across a step whose strict tail successor
is not done. -/
lemma grayChargedRunStateV2_phase_advantage_succ
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hnext : (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).done = false) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).phase = .advantage := by
  rw [grayChargedRunStateV2_succ]
  have hcore := grayChargedRunStateV2_core_eq_tailStateAt
    q L a e sigma A sm t hphase
  simp only [grayChargedStepV2, hphase]
  rw [hcore, ← grayChargedBlockTailStateAtV2_succ]
  simp [hnext]

/-- The advantage phase persists while the strict tail trajectory is not
done. -/
lemma grayChargedRunStateV2_phase_advantage_add
    {q L a e n t T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hnotdone : ∀ d, d ≤ T ->
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).done = false) :
    ∀ d, d ≤ T ->
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).phase = .advantage := by
  intro d
  induction d with
  | zero =>
      intro _
      simpa using hphase
  | succ d ih =>
      intro hd
      have hsucc : t + (d + 1) = (t + d) + 1 := by omega
      rw [hsucc]
      apply grayChargedRunStateV2_phase_advantage_succ (ih (by omega))
      rw [← hsucc]
      exact hnotdone (d + 1) hd

/-- The advantage phase persists up to any later time at which the strict
tail trajectory has not been done. -/
lemma grayChargedRunStateV2_phase_advantage_of_le
    {q L a e n t u : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (htu : t ≤ u)
    (hnotdone : ∀ v, t ≤ v -> v ≤ u ->
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm v).done = false) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm u).phase = .advantage := by
  obtain ⟨d, rfl⟩ : ∃ d, u = t + d := ⟨u - t, by omega⟩
  exact grayChargedRunStateV2_phase_advantage_add hphase
    (fun d' hd' => hnotdone (t + d') (by omega) (by omega)) d le_rfl

/-- **Positive win from an unserved positive sub-game request** (V2): if the
round's client wins its sub-game by an unserved positive request while the
block goal is never accepted, the outer V2 client wins the positive game. -/
theorem grayChargedBlockV2_round_positive_of_not_gray
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailStateV2 n (grayTailBranch q L a e)}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayChargedBlockTailStateAtV2
      (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hminimum : forall T,
      familyRequestAvoidsSmall base.slots.length
        ((1 / 2 : Rat) ^ (grayTailRoundDelta q L e base.frozen.length))
        (playClientFamily base.unavailable base.slots.length
          (grayBlockRoundStrategyV2 q L e sigma base)
          (grayBlockFutureServerV2 q L e base sm) T))
    (hwin : familyClientWinsUnservedPositive base.slots.length (2 * q)
      (grayTailBranch q L a e)
      (playClientFamily base.unavailable base.slots.length
        (grayBlockRoundStrategyV2 q L e sigma base)
        (grayBlockFutureServerV2 q L e base sm))
      (grayBlockFutureServerV2 q L e base sm))
    (hnogray : ¬ ∃ T, grayChargedBlockRoundGoalBV2 q L e sigma base sm T = true) :
    GrayChargedPositiveV2 q L a e n sigma A sm := by
  let localServer := grayBlockFutureServerV2 q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayBlockRoundStrategyV2 q L e sigma base) localServer
  obtain ⟨j, hj, T, x, hlen, hin, hfail, hpos⟩ := hwin
  have hmin :
      (1 / 2 : Rat) ^ (grayTailRoundDelta q L e base.frozen.length) <=
        getFamilyReq (localClient T) j x :=
    (hminimum T j hj x).resolve_left (ne_of_gt hpos)
  have hfalse : forall u,
      grayChargedBlockRoundGoalBV2 q L e sigma base sm u = false := by
    intro u
    cases hu : grayChargedBlockRoundGoalBV2 q L e sigma base sm u with
    | false => rfl
    | true => exact (hnogray ⟨u, hu⟩).elim
  have hstayAll := grayChargedBlockSameRoundV2_stateAt_add
    (q := q) (L := L) (a := a) (e := e)
    base hbase hstart hactive (T := T) (fun u _ => hfalse u)
  have hstay := hstayAll T le_rfl
  let stT := grayChargedBlockTailStateAtV2
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + T)
  have hsame : GrayBlockSameRoundV2 base stT := hstay.1
  have hhistlen : stT.history.2.length = T := hstay.2
  have hhist := grayChargedBlockHistoryOKV2_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + T)
  have htrace := grayChargedBlockTailTraceV2_stateAt
    (n := n) (b := grayTailBranch q L a e) q L a e sigma A sm (t + T)
  have hfuture : grayBlockFutureServerV2 q L e stT sm = localServer := by
    funext u
    simp [grayBlockFutureServerV2, localServer, hsame.frozen,
      hsame.slots, hsame.roundStart]
  have hcurrent : grayBlockCurrentMoveV2 q L e sigma stT = localClient T := by
    rw [grayBlockCurrentMoveV2_eq_futurePlay q L e sigma hhist htrace]
    rw [hfuture, hhistlen]
    change playClientFamily stT.unavailable stT.slots.length
      (sigma (grayTailRoundEps q L e stT.frozen.length)
        (grayTailRoundEps q L e stT.frozen.length + graySpendSpan q))
      localServer T = localClient T
    rw [hsame.unavailable, hsame.slots, hsame.frozen]
    rfl
  let jT : Fin stT.slots.length :=
    ⟨j, by simpa [hsame.slots] using hj⟩
  have hfailT : forall u,
      ¬ Serves
        (getFamilyAlloc (grayBlockFutureServerV2 q L e stT sm u) jT.val x)
        (getFamilyReq (grayBlockCurrentMoveV2 q L e sigma stT) jT.val x) := by
    intro u
    have h_eq :
        Serves
          (getFamilyAlloc (grayBlockFutureServerV2 q L e stT sm u) jT.val x)
          (getFamilyReq (grayBlockCurrentMoveV2 q L e sigma stT) jT.val x) =
        Serves
          (getAlloc (familyServerMoveAt (grayBlockFutureServerV2 q L e base sm u) j) x)
          (getReq (familyClientMoveAt
            (playClientFamily base.unavailable base.slots.length
              (grayBlockRoundStrategyV2 q L e sigma base)
              (grayBlockFutureServerV2 q L e base sm) T) j) x) := by
      have hjT : jT.val = j := rfl
      rw [hfuture, hcurrent, hjT]
      rfl
    exact h_eq ▸ hfail u
  have hposT :
      0 < getFamilyReq (grayBlockCurrentMoveV2 q L e sigma stT) jT.val x := by
    have h_eq :
        getFamilyReq (grayBlockCurrentMoveV2 q L e sigma stT) jT.val x =
        getReq (familyClientMoveAt
          (playClientFamily base.unavailable base.slots.length
            (grayBlockRoundStrategyV2 q L e sigma base) localServer T) j) x := by
      have hjT : jT.val = j := rfl
      rw [hcurrent, hjT]
      rfl
    exact h_eq ▸ hpos
  have hnotdone : ∀ d, d ≤ T ->
      (grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).done = false :=
    fun d hd => (hstayAll d hd).1.done
  have hphaseT := grayChargedRunStateV2_phase_advantage_add hphase hnotdone T le_rfl
  have hcoreT : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + T)).core = stT :=
    grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm (t + T) hphaseT
  have hslotsT : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + T)).core.slots.isEmpty = false := by
    rw [hcoreT, hsame.slots]
    cases hs : base.slots.isEmpty with
    | false => exact rfl
    | true =>
        exfalso
        apply hactive
        simp [hs]
  have hdisplay :
      playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm (t + T) =
        grayChargedTailFamilyMove (grayChargedSourceCount a e)
          (grayChargedThreshold q e) (dyadicScale e)
          (stT.frozen.map GrayTailRoundV2.toV1) stT.slots
          (grayBlockCurrentMoveV2 q L e sigma stT) := by
    have hactiveT : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + T)).core.done = false := by
      rw [hcoreT]
      exact hnotdone T le_rfl
    have hmove := grayChargedRunMoveV2_eq_of_advantage hphaseT hactiveT hslotsT
    rw [hcoreT] at hmove
    exact hmove
  have hkeys :
      (grayTailFrozenSlots (stT.frozen.map GrayTailRoundV2.toV1) ++
        stT.slots).Nodup := by
    rw [grayTailFrozenSlots_map_toV1]
    have hnodup := (grayChargedRunStateV2_coreCertified
      (n := n) q L a e sigma A sm (t + T)).all_slots_nodup
    rw [hcoreT] at hnodup
    exact hnodup
  have hminT :
      (1 / 2 : Rat) ^ (grayTailRoundDelta q L e stT.frozen.length) <=
        getFamilyReq (grayBlockCurrentMoveV2 q L e sigma stT) jT.val x := by
    rw [hcurrent, hsame.frozen]
    simpa [jT] using hmin
  have hout := grayChargedBlockV2_familyMove_transfers_positive
    (h := 2 * q) hsm hkeys hdisplay jT x hlen hin hminT hfailT hposT
  unfold GrayChargedPositiveV2
  rw [show 2 * (q + 1) = 2 * q + 2 by ring]
  exact hout

end Kolmogorov
