import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Legality
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2History
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Trace

/-!
# One advantage round of the strict V2 block controller, replayed

Stage C4 (replay equalities), the V2 analogue of `GacsDayChargedTailRound`:
the part of the block state frozen throughout one advantage round, the
Boolean block-goal test of that round indexed by the exchange number, the
identification of the controller's live test with the replayed test (history
+ trace consistency), the same-round persistence while the test fails, and
the freeze at the first accepted exchange.  Faithful mirror of the V1
development on the V2 records.
-/

namespace Kolmogorov

/-- The part of a V2 block state which is frozen throughout one advantage
round. -/
structure GrayBlockSameRoundV2 {n b : Nat}
    (base st : GrayTailStateV2 n b) : Prop where
  done : st.done = false
  frozen : st.frozen = base.frozen
  unavailable : st.unavailable = base.unavailable
  slots : st.slots = base.slots
  roundStart : st.roundStart = base.roundStart

/-- An active tail state (not done and with a nonempty slot list) is in the same round as itself. -/
lemma grayBlockSameRoundV2_refl {n b : Nat} {st : GrayTailStateV2 n b}
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    GrayBlockSameRoundV2 st st := by
  have hdone : st.done = false := by
    cases hd : st.done <;> simp_all
  exact ⟨hdone, rfl, rfl, rfl, rfl⟩

/-- The Boolean block-goal test of one fixed advantage round, indexed by the
exchange number. -/
def grayChargedBlockRoundGoalBV2 {n b : Nat}
    (q L e : Nat) (sigma : FamilyStrategyScheme)
    (base : GrayTailStateV2 n b) (sm : Nat -> FamilyServerMove)
    (T : Nat) : Bool :=
  let localServer := grayBlockFutureServerV2 q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayBlockRoundStrategyV2 q L e sigma base) localServer
  grayChargedBlockGoalAtB q L e base.frozen.length
    base.slots.length base.unavailable (localClient T) (localServer T)

/-- The recorded server list agrees with the V2 future server before the
current exchange. -/
lemma grayTailTraceV2_server_before {n b : Nat}
    (q L e : Nat) {sm : Nat -> FamilyServerMove} {t : Nat}
    {st : GrayTailStateV2 n b}
    (hst : GrayTailTraceV2 q L e sm t st)
    {j : Nat} (hj : j < st.history.2.length) :
    grayTailServerOfList st.history.2 j =
      grayBlockFutureServerV2 q L e st sm j := by
  have hget := congrArg
    (fun l : List FamilyServerMove => l.getD j [])
    hst.servers_eq
  unfold grayTailServerOfList grayBlockFutureServerV2
  have h1 : st.history.2.getD j (st.history.2.getLastD []) =
      st.history.2.getD j [] := by
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj]
  rw [h1]
  simpa [List.getD_eq_getElem?_getD, hj, List.getElem_ofFn] using hget

/-- The current V2 block move is the canonical play of the round strategy
against the V2 future server. -/
lemma grayBlockCurrentMoveV2_eq_futurePlay {n b : Nat}
    (q L e : Nat) (sigma : FamilyStrategyScheme)
    {sm : Nat -> FamilyServerMove} {t : Nat}
    {st : GrayTailStateV2 n b}
    (hhist : GrayBlockHistoryOKV2 q L e sigma st)
    (htrace : GrayTailTraceV2 q L e sm t st) :
    grayBlockCurrentMoveV2 q L e sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayBlockRoundStrategyV2 q L e sigma st)
        (grayBlockFutureServerV2 q L e st sm)
        st.history.2.length := by
  rw [grayBlockCurrentMoveV2_eq_play q L e sigma st hhist]
  apply playClientFamily_congr_before
  intro j hj
  exact grayTailTraceV2_server_before q L e htrace hj

/-- The controller's local server move at an active time is the V2 future
server at the current exchange. -/
lemma grayBlockLocalServerMoveV2_eq_future
    {n b q L e t : Nat} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b}
    (htrace : GrayTailTraceV2 q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t) =
      grayBlockFutureServerV2 q L e st sm st.history.2.length := by
  unfold grayBlockFutureServerV2
  rw [htrace.active_time hactive]

/-- The live block-goal test of the controller is the replayed test of the
round at the current exchange number. -/
lemma grayChargedBlockCurrent_goal_eq_roundGoalV2
    {n b q L e t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {base st : GrayTailStateV2 n b}
    (hsame : GrayBlockSameRoundV2 base st)
    (hhist : GrayBlockHistoryOKV2 q L e sigma st)
    (htrace : GrayTailTraceV2 q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    grayChargedBlockGoalAtB q L e st.frozen.length
        st.slots.length st.unavailable
        (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)) =
      grayChargedBlockRoundGoalBV2 q L e sigma base sm
        st.history.2.length := by
  rw [grayBlockCurrentMoveV2_eq_futurePlay q L e sigma hhist htrace]
  rw [grayBlockLocalServerMoveV2_eq_future htrace hactive]
  have hfuture :
      grayBlockFutureServerV2 q L e st sm =
        grayBlockFutureServerV2 q L e base sm := by
    funext u
    simp [grayBlockFutureServerV2, hsame.frozen, hsame.slots,
      hsame.roundStart]
  simp only [grayChargedBlockRoundGoalBV2]
  rw [hfuture]
  simp [grayBlockRoundStrategyV2, hsame.frozen, hsame.slots,
    hsame.unavailable]

/-- A rejected exchange keeps the round data. -/
lemma grayChargedBlockSameRoundV2_step_false
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {base st : GrayTailStateV2 n b}
    {m : FamilyServerMove}
    (hsame : GrayBlockSameRoundV2 base st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true)
    (hgoal : grayChargedBlockGoalAtB q L e st.frozen.length
      st.slots.length st.unavailable
      (grayBlockCurrentMoveV2 q L e sigma st)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots m) = false) :
    GrayBlockSameRoundV2 base
      (grayChargedBlockTailStepV2 q L a e sigma A st m) := by
  have hslots : st.slots.isEmpty = false := by
    cases hs : st.slots.isEmpty
    · rfl
    · exfalso
      apply hactive
      simp [hs]
  simp only [grayChargedBlockTailStepV2, Bool.false_eq_true, if_false,
    hsame.done, hslots, hgoal]
  exact ⟨by simp,
    by simpa using hsame.frozen,
    by simpa using hsame.unavailable,
    by simpa using hsame.slots,
    by simpa using hsame.roundStart⟩

/-- While the replayed test fails, the trajectory stays in the round and the
exchange counter is the elapsed time. -/
lemma grayChargedBlockSameRoundV2_stateAt_add
    {n b q L a e t T : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (base : GrayTailStateV2 n b)
    (hbase : base = grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hfalse : forall j, j < T ->
      grayChargedBlockRoundGoalBV2 q L e sigma base sm j = false) :
    forall j, j <= T ->
      let st := grayChargedBlockTailStateAtV2 (n := n) (b := b)
        q L a e sigma A sm (t + j)
      GrayBlockSameRoundV2 base st ∧ st.history.2.length = j := by
  intro j hj
  induction j with
  | zero =>
      have hstate : grayChargedBlockTailStateAtV2 (n := n) (b := b)
          q L a e sigma A sm (t + 0) = base := by simp [hbase]
      rw [hstate]
      refine ⟨grayBlockSameRoundV2_refl hactive, ?_⟩
      have htrace := grayChargedBlockTailTraceV2_stateAt
        (n := n) (b := b) q L a e sigma A sm t
      rw [← hbase] at htrace
      have hlen := htrace.active_time hactive
      rw [hstart] at hlen
      omega
  | succ j ih =>
      have hjT : j <= T := by omega
      obtain ⟨hsame, hlen⟩ := ih hjT
      let st := grayChargedBlockTailStateAtV2 (n := n) (b := b)
        q L a e sigma A sm (t + j)
      have hactiveSt : (st.done || st.slots.isEmpty) ≠ true := by
        have hdone : st.done = false := hsame.done
        have hslots : st.slots.isEmpty = false := by
          rw [hsame.slots]
          cases hs : base.slots.isEmpty with
          | false => exact rfl
          | true =>
              exfalso
              apply hactive
              simp [hs]
        simp [hdone, hslots]
      have hhist := grayChargedBlockHistoryOKV2_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + j)
      have htrace := grayChargedBlockTailTraceV2_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + j)
      have hjlt : j < T := by omega
      have hgoal : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable
          (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm (t + j))) = false := by
        rw [grayChargedBlockCurrent_goal_eq_roundGoalV2
          hsame hhist htrace hactiveSt]
        rw [hlen]
        exact hfalse j hjlt
      have hsucc : t + (j + 1) = (t + j) + 1 := by omega
      have hnext : GrayBlockSameRoundV2 base
          (grayChargedBlockTailStateAtV2 (n := n) (b := b)
            q L a e sigma A sm (t + (j + 1))) := by
        rw [hsucc, grayChargedBlockTailStateAtV2_succ]
        exact grayChargedBlockSameRoundV2_step_false hsame hactiveSt hgoal
      refine ⟨hnext, ?_⟩
      have htrace' := grayChargedBlockTailTraceV2_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + (j + 1))
      have hactive' :
          ((grayChargedBlockTailStateAtV2 (n := n) (b := b)
              q L a e sigma A sm (t + (j + 1))).done ||
            (grayChargedBlockTailStateAtV2 (n := n) (b := b)
              q L a e sigma A sm (t + (j + 1))).slots.isEmpty) ≠ true := by
        have hslots : (grayChargedBlockTailStateAtV2 (n := n) (b := b)
            q L a e sigma A sm (t + (j + 1))).slots.isEmpty = false := by
          rw [hnext.slots]
          cases hs : base.slots.isEmpty with
          | false => exact rfl
          | true =>
              exfalso
              apply hactive
              simp [hs]
        simp [hnext.done, hslots]
      have hlen' := htrace'.active_time hactive'
      rw [hnext.roundStart, hstart] at hlen'
      omega

/-- **Freeze at the first accepted exchange**: if the replayed block goal of
the round is eventually accepted, the controller freezes the round — one more
frozen round, a fresh round start, an empty history. -/
theorem grayChargedBlockV2_freezes_of_round_gray
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (base : GrayTailStateV2 n b)
    (hbase : base = grayChargedBlockTailStateAtV2 (n := n) (b := b)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hgray : ∃ T, grayChargedBlockRoundGoalBV2 q L e sigma base sm T = true) :
    ∃ u, t < u ∧
      (∀ v, t <= v -> v < u ->
        (grayChargedBlockTailStateAtV2 (n := n) (b := b)
          q L a e sigma A sm v).done = false) ∧
      (grayChargedBlockTailStateAtV2 (n := n) (b := b)
          q L a e sigma A sm u).frozen.length = base.frozen.length + 1 ∧
        (grayChargedBlockTailStateAtV2 (n := n) (b := b)
          q L a e sigma A sm u).roundStart = u ∧
        (grayChargedBlockTailStateAtV2 (n := n) (b := b)
          q L a e sigma A sm u).history = ([], []) := by
  classical
  let T := Nat.find hgray
  have hT : grayChargedBlockRoundGoalBV2 q L e sigma base sm T = true :=
    Nat.find_spec hgray
  have hfalse : forall j, j < T ->
      grayChargedBlockRoundGoalBV2 q L e sigma base sm j = false := by
    intro j hj
    cases hBj : grayChargedBlockRoundGoalBV2 q L e sigma base sm j with
    | false => rfl
    | true => exact (Nat.find_min hgray hj hBj).elim
  have hstayAll := grayChargedBlockSameRoundV2_stateAt_add
    (q := q) (L := L) (a := a) (e := e)
    base hbase hstart hactive hfalse
  have hstay := hstayAll T le_rfl
  let stT := grayChargedBlockTailStateAtV2 (n := n) (b := b)
    q L a e sigma A sm (t + T)
  have hsame : GrayBlockSameRoundV2 base stT := hstay.1
  have hlen : stT.history.2.length = T := hstay.2
  have hactiveT : (stT.done || stT.slots.isEmpty) ≠ true := by
    have hslots : stT.slots.isEmpty = false := by
      rw [hsame.slots]
      cases hs : base.slots.isEmpty with
      | false => exact rfl
      | true =>
          exfalso
          apply hactive
          simp [hs]
    simp [hsame.done, hslots]
  have hhist := grayChargedBlockHistoryOKV2_stateAt
    (n := n) (b := b) q L a e sigma A sm (t + T)
  have htrace := grayChargedBlockTailTraceV2_stateAt
    (n := n) (b := b) q L a e sigma A sm (t + T)
  have htime : stT.time = t + T := htrace.time_eq
  have htest : grayChargedBlockGoalAtB q L e stT.frozen.length
      stT.slots.length stT.unavailable
      (grayBlockCurrentMoveV2 q L e sigma stT)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e stT.frozen.length)
        stT.slots (sm (t + T))) = true := by
    rw [grayChargedBlockCurrent_goal_eq_roundGoalV2
      hsame hhist htrace hactiveT]
    rw [hlen]
    exact hT
  refine ⟨t + T + 1, by omega, ?_, ?_⟩
  · intro v hv1 hv2
    obtain ⟨j, rfl⟩ : ∃ j, v = t + j := ⟨v - t, by omega⟩
    exact (hstayAll j (by omega)).1.done
  have hnext : grayChargedBlockTailStateAtV2 (n := n) (b := b)
        q L a e sigma A sm (t + T + 1) =
      grayChargedBlockTailStepV2 q L a e sigma A stT (sm (t + T)) :=
    grayChargedBlockTailStateAtV2_succ q L a e sigma A sm (t + T)
  have hdoneT : stT.done = false := hsame.done
  have hslotsT : stT.slots.isEmpty = false := by
    cases hs : stT.slots.isEmpty
    · rfl
    · exfalso
      apply hactiveT
      simp [hs]
  rw [hnext]
  simp only [grayChargedBlockTailStepV2, Bool.false_eq_true, if_false,
    hdoneT, hslotsT, htest, if_true]
  simp [hsame.frozen, htime]

end Kolmogorov
