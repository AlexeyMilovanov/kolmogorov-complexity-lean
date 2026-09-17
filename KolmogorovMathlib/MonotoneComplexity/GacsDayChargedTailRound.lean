import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRound
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRung

/-!
# One designated-gray recursive round

This file connects the executable charged acceptance test to the strengthened
induction hypothesis.  It deliberately reuses the old relocation and grafting
geometry, which is independent of the discarded subfamily certificate.
-/

namespace Kolmogorov

/-- The strategy the tail plays inside an active round meets the charged game specification for
the round's parameters. -/
theorem grayChargedTailRound_gameSpec
    {q L B a e n b t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (_hcert : GrayChargedTailCertified q L e A sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true)
    (hb : grayTailBaseBranch q L <= b) :
    ChargedGrayFamilyGameSpec 4 (halfAmplification q)
      (dyadicScale (grayCallDepth q e))
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      (2 * q) b st.slots.length st.unavailable
      (grayTailRoundStrategy q L e sigma st) := by
  have he1 : 1 <= e := le_trans ha hae
  have hcall1 : 1 <= grayCallDepth q e :=
    le_trans he1 (le_grayCallDepth q e)
  have hcallEps :
      grayCallDepth q e <= grayTailRoundEps q L e st.frozen.length :=
    grayTailRoundEps_lower q L e st.frozen.length
  have hslots : 1 <= st.slots.length := by
    cases hs : st.slots with
    | nil => simp [hs] at hactive
    | cons _ _ => simp
  have hbase := hRung (grayCallDepth q e)
    (grayTailRoundEps q L e st.frozen.length)
    hcall1 hcallEps st.slots.length st.unavailable hslots
  have hbranch :
      ladderBranching B (grayCallDepth q e)
          (grayTailRoundEps q L e st.frozen.length) <= b :=
    le_trans (grayTailRecursiveBranch_le hB) hb
  simpa [grayTailRoundDelta, grayTailRoundStrategy] using
    hbase.mono_branching hbranch

/-- The fixed charged Boolean test of one recursive round. -/
def grayChargedTailRoundGoalB {n b : Nat}
    (q L e : Nat) (sigma : FamilyStrategyScheme)
    (base : GrayTailState n b) (sm : Nat -> FamilyServerMove)
    (T : Nat) : Bool :=
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  grayChargedTailGoalAtB q e
    (grayTailRoundEps q L e base.frozen.length)
    (grayTailRoundDelta q L e base.frozen.length)
    base.slots.length base.unavailable (localClient T) (localServer T)

/-- Inside one round, the goal test on the current move is the round goal of the base state at
the current history length. -/
lemma grayChargedTailCurrent_goal_eq_roundGoal
    {n b q L e t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {base st : GrayTailState n b}
    (hsame : GrayTailSameRound base st)
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    grayChargedTailGoalAtB q e
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)) =
      grayChargedTailRoundGoalB q L e sigma base sm st.history.2.length := by
  rw [grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace]
  rw [grayTailLocalServerMove_eq_future htrace hactive]
  have hfuture :
      grayTailFutureServer q L e st sm =
        grayTailFutureServer q L e base sm := by
    funext u
    simp [grayTailFutureServer, hsame.frozen, hsame.slots,
      hsame.roundStart]
  simp only [grayChargedTailRoundGoalB]
  rw [hfuture]
  simp [grayTailRoundStrategy, hsame.frozen, hsame.slots,
    hsame.unavailable]

/-- A step whose goal test fails stays inside the same round. -/
lemma grayChargedTailSameRound_step_false
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {base st : GrayTailState n b}
    {m : FamilyServerMove}
    (hsame : GrayTailSameRound base st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true)
    (hgoal : grayChargedTailGoalAtB q e
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      st.slots.length st.unavailable
      (grayTailCurrentMove q L e sigma st)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots m) = false) :
    GrayTailSameRound base
      (grayChargedTailStep q L a e sigma A st m) := by
  have hslots : st.slots.isEmpty = false := by
    cases hs : st.slots.isEmpty
    · rfl
    · exfalso
      apply hactive
      simp [hs]
  simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
    if_false, hsame.done, hslots, hgoal]
  exact ⟨by simp,
    by simpa using hsame.frozen,
    by simpa using hsame.unavailable,
    by simpa using hsame.slots,
    by simpa using hsame.roundStart⟩

/-- As long as the round goal keeps failing, the run stays in the round it started, and its
history grows by one entry per step. -/
lemma grayChargedTailSameRound_stateAt_add
    {n b q L a e t T : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (base : GrayTailState n b)
    (hbase : base = grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hfalse : forall j, j < T ->
      grayChargedTailRoundGoalB q L e sigma base sm j = false) :
    forall j, j <= T ->
      let st := grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm (t + j)
      GrayTailSameRound base st ∧ st.history.2.length = j := by
  intro j hj
  induction j with
  | zero =>
      have hstate : grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm (t + 0) = base := by simp [hbase]
      rw [hstate]
      refine ⟨grayTailSameRound_refl hactive, ?_⟩
      have htrace := grayChargedTailTrace_stateAt
        (n := n) (b := b) q L a e sigma A sm t
      rw [← hbase] at htrace
      have hlen := htrace.active_time hactive
      rw [hstart] at hlen
      omega
  | succ j ih =>
      have hjT : j <= T := by omega
      obtain ⟨hsame, hlen⟩ := ih hjT
      let st := grayChargedTailStateAt (n := n) (b := b)
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
      have hhist := grayChargedTailHistoryOK_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + j)
      have htrace := grayChargedTailTrace_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + j)
      have hjlt : j < T := by omega
      have hgoal : grayChargedTailGoalAtB q e
          (grayTailRoundEps q L e st.frozen.length)
          (grayTailRoundDelta q L e st.frozen.length)
          st.slots.length st.unavailable
          (grayTailCurrentMove q L e sigma st)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm (t + j))) = false := by
        rw [grayChargedTailCurrent_goal_eq_roundGoal
          hsame hhist htrace hactiveSt]
        rw [hlen]
        exact hfalse j hjlt
      have hnext : GrayTailSameRound base
          (grayChargedTailStep q L a e sigma A st (sm (t + j))) :=
        grayChargedTailSameRound_step_false hsame hactiveSt hgoal
      have hstate : grayChargedTailStateAt (n := n) (b := b)
            q L a e sigma A sm (t + (j + 1)) =
          grayChargedTailStep q L a e sigma A st (sm (t + j)) := by
        rw [show t + (j + 1) = (t + j) + 1 by omega,
          grayChargedTailStateAt_succ]
      rw [hstate]
      refine ⟨hnext, ?_⟩
      have hactiveNext :
          (((grayChargedTailStep q L a e sigma A st (sm (t + j))).done) ||
            ((grayChargedTailStep q L a e sigma A st
              (sm (t + j))).slots.isEmpty)) ≠ true := by
        have hdone := hnext.done
        have hslots : (grayChargedTailStep q L a e sigma A st
            (sm (t + j))).slots.isEmpty = false := by
          rw [hnext.slots]
          cases hs : base.slots.isEmpty with
          | false => exact rfl
          | true =>
              exfalso
              apply hactive
              simp [hs]
        simp [hdone, hslots]
      have htraceNext := grayChargedTailTrace_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + (j + 1))
      rw [hstate] at htraceNext
      have htime := htraceNext.active_time hactiveNext
      rw [hnext.roundStart, hstart] at htime
      omega

/-- The advantage strategy plays, at each time, the output of the charged tail state at that
time. -/
lemma playClientFamily_grayChargedAdvantageStrategy
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    let b := ladderBranching (grayTailBaseBranch q L) a e
    playClientFamily A n (grayChargedAdvantageStrategy q L a e sigma) sm t =
      grayChargedTailOutput q L a e sigma
        (grayChargedTailStateAt (n := n) (b := b)
          q L a e sigma A sm t) := by
  dsimp only
  cases t with
  | zero => rw [playClientFamily]; rfl
  | succ t => rw [playClientFamily]; rfl

end Kolmogorov
