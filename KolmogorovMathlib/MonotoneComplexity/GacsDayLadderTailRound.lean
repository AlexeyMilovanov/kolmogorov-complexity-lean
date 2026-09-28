import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailLegality
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustRung

/-!
# One certified recursive round of Day's ladder tail

This file connects the executable tail controller with the induction
hypothesis. At every active controller state, the current family of fresh
grandson slots is a genuine instance of the preceding `GrayRung`. The local
server play is legal by `grayTailFutureServer_legal`, while the deliberately
large outer branching factor absorbs both the scale ratio and the recursive
deep branching.
-/

namespace Kolmogorov

/-- The uniform outer branching `ladderBranching (grayTailBaseBranch q L) a e` used by the
executable tail controller. -/
abbrev grayTailBranch (q L a e : ℕ) : ℕ :=
  ladderBranching (grayTailBaseBranch q L) a e

/-- The preceding rung supplies the game specification used by every active
round of the tail controller. -/
theorem grayTailRound_gameSpec
    {q L B a e n b t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    {st : GrayTailState n b}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (_hcert : GrayTailCertified q L e A sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true)
    (hb : grayTailBaseBranch q L ≤ b) :
    RobustGrayFamilyGameSpec (halfAmplification q)
      (dyadicScale (grayCallDepth q e))
      ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e st.frozen.length)
      (grayTailRoundDelta q L e st.frozen.length)
      (2 * q) b st.slots.length st.unavailable
      (grayTailRoundStrategy q L e sigma st) := by
  have he1 : 1 ≤ e := le_trans ha hae
  have hcall1 : 1 ≤ grayCallDepth q e :=
    le_trans he1 (le_grayCallDepth q e)
  have hcallEps :
      grayCallDepth q e ≤ grayTailRoundEps q L e st.frozen.length :=
    grayTailRoundEps_lower q L e st.frozen.length
  have hslots : 1 ≤ st.slots.length := by
    cases hs : st.slots with
    | nil => simp [hs] at hactive
    | cons _ _ => simp
  have hbase := hRung (grayCallDepth q e)
    (grayTailRoundEps q L e st.frozen.length)
    hcall1 hcallEps st.slots.length st.unavailable hslots
  have hbranch :
      ladderBranching B (grayCallDepth q e)
          (grayTailRoundEps q L e st.frozen.length) ≤ b := by
    exact le_trans (grayTailRecursiveBranch_le hB) hb
  have hwiden := hbase.mono_branching hbranch
  simpa [grayTailRoundDelta, grayTailRoundStrategy] using hwiden

/-- Restricting a family server move to the tree keeps its number of clients. -/
@[simp] lemma length_inTreeFamilyServerMove (b : ℕ)
    (m : FamilyServerMove) :
    (inTreeFamilyServerMove b m).length = m.length := by
  simp [inTreeFamilyServerMove]

/-- The localised server move has one row per slot. -/
@[simp] lemma length_grayTailLocalServerMove
    {n b eps : ℕ} (slots : List (GrayTailSlot n b))
    (m : FamilyServerMove) :
  (grayTailLocalServerMove eps slots m).length = slots.length := by
  simp [grayTailLocalServerMove, truncFamilyServerMove,
    extractGrandchildFamilyMove]

/-- At an active certified state, the allocation list tested by the controller
is exactly the allocation list of the current recursive family play. -/
lemma grayTailLocalAllocatedList_eq_future
    {n b q L e t : ℕ} {sm : ℕ → FamilyServerMove}
    {st : GrayTailState n b}
    (htrace : GrayTailTrace q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    grayTailLocalAllocatedList
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)) =
      familyAllocatedList st.slots.length st.history.2.length
        (grayTailFutureServer q L e st sm) := by
  have htime := htrace.active_time hactive
  unfold grayTailLocalAllocatedList familyAllocatedList
  rw [length_grayTailLocalServerMove]
  congr 1
  funext i
  unfold grayTailFutureServer
  rw [htime]

/-- The local server move tested at the current outer time is exactly the
current move of the fixed future-server play for this recursive round. -/
lemma grayTailLocalServerMove_eq_future
    {n b q L e t : Nat} {sm : Nat -> FamilyServerMove}
    {st : GrayTailState n b}
    (htrace : GrayTailTrace q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    grayTailLocalServerMove
        (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t) =
      grayTailFutureServer q L e st sm st.history.2.length := by
  unfold grayTailFutureServer
  rw [htrace.active_time hactive]

/-- The Boolean branch taken by the controller is propositionally the gray
outcome of the current recursive game. -/
lemma grayTailCurrent_goal_iff
    {n b q L e t : ℕ} {sigma : FamilyStrategyScheme}
    {sm : ℕ → FamilyServerMove} {st : GrayTailState n b}
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    familyGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalAllocatedList
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t))) = true ↔
      let localServer := grayTailFutureServer q L e st sm
      let localClient := playClientFamily st.unavailable st.slots.length
        (grayTailRoundStrategy q L e sigma st) localServer
      let T := st.history.2.length
      ((st.slots.length : ℚ) *
            ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e)) ≤
          familyGrayMass
            (grayTailRoundEps q L e st.frozen.length)
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots.length T st.unavailable localServer ∧
        halfAmplification q * totalRootRequest st.slots.length (localClient T) ≤
          familyGrayMass
            (grayTailRoundEps q L e st.frozen.length)
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots.length T st.unavailable localServer ∧
        (st.slots.length : ℚ) *
            ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e)) ≤
          halfAmplification q * totalRootRequest st.slots.length (localClient T)) := by
  rw [grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace]
  rw [grayTailLocalAllocatedList_eq_future htrace hactive]
  exact familyGrayGoalAtB_eq_true_iff
    (grayTailRoundEps_le_delta q L e st.frozen.length)
    st.slots.length st.history.2.length st.unavailable _ _

/-- On an active round, the request displayed below one selected grandson is
exactly the corresponding request of the recursive family play. -/
lemma grayTailOutput_current_req
    {n b q L a e : ℕ} {sigma : FamilyStrategyScheme}
    {st : GrayTailState n b}
    (hshape : GrayTailShape st) (hdone : st.done = false)
    (j : Fin st.slots.length) (x : GacsDayNode) :
    let s := st.slots.get j
    getFamilyReq (grayTailOutput q L a e sigma st) s.1.val
        (s.2.1.val :: s.2.2.val :: x) =
      getFamilyReq (grayTailCurrentMove q L e sigma st) j.val x := by
  dsimp only
  let current := grayTailCurrentMove q L e sigma st
  let entries := grayTailEntries st.frozen st.slots current
  let s := st.slots.get j
  have hfamily :
      familyClientMoveAt (grayTailOutput q L a e sigma st) s.1.val =
        graftTwoLevel
          (grayTailRootRequest st.done (grayTailTargetFloor q a)
            (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
            (dyadicScale e) entries s.1)
          b
          (fun c =>
            if hc : c < b then
              grayTailSonRequest
                (dyadicScale e - dyadicScale e / (6 * halfAmplification q))
                (dyadicScale e) entries s.1 ⟨c, hc⟩
            else 0)
          (fun c c' =>
            if hc : c < b then
              if hc' : c' < b then
                grayTailEntryMove entries (s.1, ⟨c, hc⟩, ⟨c', hc'⟩)
              else []
            else []) := by
    unfold grayTailOutput
    simp only [hdone, Bool.false_eq_true, ↓reduceIte]
    unfold grayTailFamilyMove
    unfold familyClientMoveAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [s.1.isLt, current, entries]
  rw [getFamilyReq, hfamily]
  rw [getReq_graftTwoLevel_grandson s.2.1.isLt s.2.2.isLt]
  rw [dif_pos s.2.1.isLt, dif_pos s.2.2.isLt]
  unfold getFamilyReq
  exact congrArg (fun m => getReq m x)
    (grayTailEntryMove_current hshape current j)

/-- The local allocation below a selected grandson is literally the outer
allocation at the corresponding grafted node. -/
lemma getFamilyAlloc_grayTailFutureServer
    {n b q L e : ℕ} {st : GrayTailState n b}
    {sm : ℕ → FamilyServerMove}
    (j : Fin st.slots.length) (u : ℕ) (x : GacsDayNode)
    (hx : ∀ c ∈ x, c < b) :
    let s := st.slots.get j
    getFamilyAlloc (grayTailFutureServer q L e st sm u) j.val x =
      truncAlloc (grayTailRoundDelta q L e st.frozen.length)
        (getFamilyAlloc (sm (st.roundStart + u)) s.1.val
          (s.2.1.val :: s.2.2.val :: x)) := by
  dsimp only
  unfold grayTailFutureServer
  rw [getFamilyAlloc_grayTailLocalServerMove st.slots _ j.val j.isLt x hx]
  simp [getFamilyAlloc, getAlloc_extractSubtreeServerMove]

/-- An unserved positive request of the active recursive call is an unserved
positive request of the outer family, two levels lower in the same tree. -/
theorem grayTailOutput_transfers_positive
    {n b q L a e h T : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    {cm : ℕ → FamilyClientMove} {st : GrayTailState n b}
    (hsm : familyServerPlayLegal n b A sm)
    (hshape : GrayTailShape st) (hdone : st.done = false)
    (hdisplay : cm T = grayTailOutput q L a e sigma st)
    (j : Fin st.slots.length) (x : GacsDayNode)
    (hlen : x.length ≤ h) (hin : ∀ d ∈ x, d < b)
    (hmin : (1 / 2 : ℚ) ^
      (grayTailRoundDelta q L e st.frozen.length) ≤
        getFamilyReq (grayTailCurrentMove q L e sigma st) j.val x)
    (hfail : ∀ u,
      ¬ Serves (getFamilyAlloc (grayTailFutureServer q L e st sm u) j.val x)
        (getFamilyReq (grayTailCurrentMove q L e sigma st) j.val x))
    (hpos : 0 < getFamilyReq (grayTailCurrentMove q L e sigma st) j.val x) :
    familyClientWinsUnservedPositive n (h + 2) b cm sm := by
  let s := st.slots.get j
  let y : GacsDayNode := s.2.1.val :: s.2.2.val :: x
  have hreq :
      getFamilyReq (cm T) s.1.val y =
        getFamilyReq (grayTailCurrentMove q L e sigma st) j.val x := by
    rw [hdisplay]
    exact grayTailOutput_current_req hshape hdone j x
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
    rw [getFamilyAlloc_grayTailFutureServer j
      (max u st.roundStart - st.roundStart) x hin]
    rw [Nat.add_sub_of_le (le_max_right u st.roundStart)]
    exact (serves_truncAlloc_iff hmin).mpr hmono
  · change 0 < getFamilyReq (cm T) s.1.val y
    rw [hreq]
    exact hpos

/-- The state `st` is in the same recursive round as `base`: it is not done, and its frozen rounds,
unavailable set, open slots and round start all agree with those of `base`. -/
structure GrayTailSameRound {n b : ℕ}
    (base st : GrayTailState n b) : Prop where
  done : st.done = false
  frozen : st.frozen = base.frozen
  unavailable : st.unavailable = base.unavailable
  slots : st.slots = base.slots
  roundStart : st.roundStart = base.roundStart

/-- An active state is in the same round as itself. -/
lemma grayTailSameRound_refl {n b : ℕ} {st : GrayTailState n b}
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    GrayTailSameRound st st := by
  have hdone : st.done = false := by
    cases hd : st.done <;> simp_all
  exact ⟨hdone, rfl, rfl, rfl, rfl⟩

/-- The Boolean gray test of the round started in `base`, evaluated after `T` local moves:
`familyRobustGrayGoalAtB` at amplification `halfAmplification q` and target `3 / 4 * dyadicScale
(grayCallDepth q e)`, between the round precision and delta depths, applied to the replay of the
round strategy against the localised future server play. -/
def grayTailRoundGoalB {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (base : GrayTailState n b) (sm : ℕ → FamilyServerMove)
    (T : ℕ) : Bool :=
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  familyRobustGrayGoalAtB (halfAmplification q)
    ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
    (grayTailRoundEps q L e base.frozen.length)
    (grayTailRoundDelta q L e base.frozen.length)
    base.slots.length base.unavailable (localClient T) (localServer T)

/-- While a round is unchanged, the controller's current test is the fixed
round test at the length of the accumulated local history. -/
lemma grayTailCurrent_goal_eq_roundGoal
    {n b q L e t : ℕ} {sigma : FamilyStrategyScheme}
    {sm : ℕ → FamilyServerMove} {base st : GrayTailState n b}
    (hsame : GrayTailSameRound base st)
    (hhist : GrayTailHistoryOK q L e sigma st)
    (htrace : GrayTailTrace q L e sm t st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true) :
    familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots (sm t)) =
      grayTailRoundGoalB q L e sigma base sm st.history.2.length := by
  rw [grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace]
  rw [grayTailLocalServerMove_eq_future htrace hactive]
  have hfuture :
      grayTailFutureServer q L e st sm =
        grayTailFutureServer q L e base sm := by
    funext u
    simp [grayTailFutureServer, hsame.frozen, hsame.slots,
      hsame.roundStart]
  simp only [grayTailRoundGoalB]
  rw [hfuture]
  simp [grayTailRoundStrategy, hsame.frozen, hsame.slots,
    hsame.unavailable]

/-- A non-firing controller transition stays in the same recursive round. -/
lemma grayTailSameRound_step_false
    {n b q L a e : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {base st : GrayTailState n b}
    {m : FamilyServerMove}
    (hsame : GrayTailSameRound base st)
    (hactive : (st.done || st.slots.isEmpty) ≠ true)
    (hgoal :
      familyRobustGrayGoalAtB (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e st.frozen.length)
        (grayTailRoundDelta q L e st.frozen.length)
        st.slots.length st.unavailable
        (grayTailCurrentMove q L e sigma st)
        (grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots m) = false) :
    GrayTailSameRound base
      (grayTailStep q L a e sigma A st m) := by
  have hslots : st.slots.isEmpty = false := by
    cases hs : st.slots.isEmpty
    · rfl
    · exfalso
      apply hactive
      simp [hs]
  simp only [grayTailStep, grayTailWaitingB, Bool.false_eq_true,
    if_false, hsame.done, hslots, hgoal]
  exact ⟨by simp,
    by simpa using hsame.frozen,
    by simpa using hsame.unavailable,
    by simpa using hsame.slots,
    by simpa using hsame.roundStart⟩

/-- Before the first firing time of a round's Boolean gray test, the global
controller remains in that round and its local history has exactly the elapsed
length. -/
lemma grayTailSameRound_stateAt_add
    {n b q L a e t T : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (base : GrayTailState n b)
    (hbase :
      base = grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hfalse : ∀ j < T, grayTailRoundGoalB q L e sigma base sm j = false) :
    ∀ j ≤ T,
      let st := grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm (t + j)
      GrayTailSameRound base st ∧ st.history.2.length = j := by
  intro j hj
  induction j with
  | zero =>
      have hstate :
          grayTailStateAt (n := n) (b := b)
              q L a e sigma A sm (t + 0) = base := by
        simp [hbase]
      rw [hstate]
      refine ⟨grayTailSameRound_refl hactive, ?_⟩
      have htrace := grayTailTrace_stateAt
        (n := n) (b := b) q L a e sigma A sm t
      rw [← hbase] at htrace
      have hlen := htrace.active_time hactive
      rw [hstart] at hlen
      omega
  | succ j ih =>
      have hjT : j ≤ T := by omega
      obtain ⟨hsame, hlen⟩ := ih hjT
      let st := grayTailStateAt (n := n) (b := b)
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
      have hhist := grayTailHistoryOK_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + j)
      have htrace := grayTailTrace_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + j)
      have hjlt : j < T := by omega
      have hgoal :
          familyRobustGrayGoalAtB (halfAmplification q)
              ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
              (grayTailRoundEps q L e st.frozen.length)
              (grayTailRoundDelta q L e st.frozen.length)
              st.slots.length st.unavailable
              (grayTailCurrentMove q L e sigma st)
              (grayTailLocalServerMove
                (grayTailRoundDelta q L e st.frozen.length)
                st.slots (sm (t + j))) = false := by
        rw [grayTailCurrent_goal_eq_roundGoal hsame hhist htrace hactiveSt]
        rw [hlen]
        exact hfalse j hjlt
      have hnext :
          GrayTailSameRound base
            (grayTailStep q L a e sigma A st (sm (t + j))) :=
        grayTailSameRound_step_false hsame hactiveSt hgoal
      have hstate :
          grayTailStateAt (n := n) (b := b)
              q L a e sigma A sm (t + (j + 1)) =
            grayTailStep q L a e sigma A st (sm (t + j)) := by
        rw [show t + (j + 1) = (t + j) + 1 by omega,
          grayTailStateAt_succ]
      rw [hstate]
      refine ⟨hnext, ?_⟩
      have hactiveNext :
          (((grayTailStep q L a e sigma A st (sm (t + j))).done) ||
            ((grayTailStep q L a e sigma A st (sm (t + j))).slots.isEmpty)) ≠ true := by
        have hdone := hnext.done
        have hslots : (grayTailStep q L a e sigma A st
            (sm (t + j))).slots.isEmpty = false := by
          rw [hnext.slots]
          cases hs : base.slots.isEmpty with
          | false => exact rfl
          | true =>
              exfalso
              apply hactive
              simp [hs]
        simp [hdone, hslots]
      have htraceNext := grayTailTrace_stateAt
        (n := n) (b := b) q L a e sigma A sm (t + (j + 1))
      rw [hstate] at htraceNext
      have htime := htraceNext.active_time hactiveNext
      rw [hnext.roundStart, hstart] at htime
      omega

/-- If an active recursive round has a positive unserved outcome and never
reaches its gray alternative, that outcome transfers to the whole tail play. -/
theorem grayTail_round_positive_of_not_gray
    {q L a e n t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    {base : GrayTailState n (grayTailBranch q L a e)}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hminimum : ∀ T,
      familyRequestAvoidsSmall base.slots.length
        ((1 / 2 : ℚ) ^
          (grayTailRoundDelta q L e base.frozen.length))
        (playClientFamily base.unavailable base.slots.length
          (grayTailRoundStrategy q L e sigma base)
          (grayTailFutureServer q L e base sm) T))
    (hwin : familyClientWinsUnservedPositive base.slots.length (2 * q)
      (grayTailBranch q L a e)
      (playClientFamily base.unavailable base.slots.length
        (grayTailRoundStrategy q L e sigma base)
        (grayTailFutureServer q L e base sm))
      (grayTailFutureServer q L e base sm))
    (hnogray : ¬ familyRobustGrayGoal (halfAmplification q)
      ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e base.frozen.length)
      (grayTailRoundDelta q L e base.frozen.length)
      base.slots.length base.unavailable
      (playClientFamily base.unavailable base.slots.length
        (grayTailRoundStrategy q L e sigma base)
        (grayTailFutureServer q L e base sm))
      (grayTailFutureServer q L e base sm)) :
    familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm := by
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  obtain ⟨j, hj, T, x, hlen, hin, hfail, hpos⟩ := hwin
  have hmin :
      (1 / 2 : ℚ) ^
          (grayTailRoundDelta q L e base.frozen.length) ≤
        getFamilyReq (localClient T) j x :=
    (hminimum T j hj x).resolve_left (ne_of_gt hpos)
  have hfalse : ∀ u,
      grayTailRoundGoalB q L e sigma base sm u = false := by
    intro u
    cases hu : grayTailRoundGoalB q L e sigma base sm u with
    | false => rfl
    | true =>
        exfalso
        apply hnogray
        exact ⟨u, by
          simpa [grayTailRoundGoalB, localClient, localServer] using hu⟩
  have hstay := grayTailSameRound_stateAt_add
    (q := q) (L := L) (a := a) (e := e)
    base hbase hstart hactive (T := T) (fun u _ => hfalse u) T le_rfl
  let stT := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + T)
  have hsame : GrayTailSameRound base stT := hstay.1
  have hhistlen : stT.history.2.length = T := hstay.2
  have hhist := grayTailHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + T)
  have htrace := grayTailTrace_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + T)
  have hfuture : grayTailFutureServer q L e stT sm = localServer := by
    funext u
    simp [grayTailFutureServer, localServer, hsame.frozen,
      hsame.slots, hsame.roundStart]
  have hcurrent : grayTailCurrentMove q L e sigma stT = localClient T := by
    rw [grayTailCurrentMove_eq_futurePlay q L e sigma hhist htrace]
    rw [hfuture, hhistlen]
    change playClientFamily stT.unavailable stT.slots.length
      (sigma (grayCallDepth q e)
        (grayTailRoundEps q L e stT.frozen.length)) localServer T =
      localClient T
    rw [hsame.unavailable, hsame.slots, hsame.frozen]
    rfl
  let jT : Fin stT.slots.length :=
    ⟨j, by simpa [hsame.slots] using hj⟩
  have hfailT : ∀ u,
      ¬ Serves (getFamilyAlloc (grayTailFutureServer q L e stT sm u) jT.val x)
        (getFamilyReq (grayTailCurrentMove q L e sigma stT) jT.val x) := by
    intro u
    simpa [hfuture, hcurrent, localClient, localServer, jT] using hfail u
  have hposT :
      0 < getFamilyReq (grayTailCurrentMove q L e sigma stT) jT.val x := by
    simpa [hcurrent, localClient, jT] using hpos
  have hdisplay :
      playClientFamily A n (grayTailStrategy q L a e sigma) sm (t + T) =
        grayTailOutput q L a e sigma stT := by
    simpa [grayTailBranch, stT] using
      (playClientFamily_grayTailStrategy q L a e n sigma A sm (t + T))
  have hout := grayTailOutput_transfers_positive hsm
    (grayTailShape_stateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + T))
    hsame.done hdisplay jT x hlen hin (by
      rw [hcurrent, hsame.frozen]
      simpa [jT] using hmin)
    hfailT hposT
  convert hout using 1

/-- If the recursive game reaches its gray alternative, the outer controller
detects its first such time and freezes the round on the following step. -/
theorem grayTail_freezes_of_round_gray
    {n b q L a e t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (base : GrayTailState n b)
    (hbase :
      base = grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hgray :
      familyRobustGrayGoal (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e base.frozen.length)
        (grayTailRoundDelta q L e base.frozen.length)
        base.slots.length base.unavailable
        (playClientFamily base.unavailable base.slots.length
          (grayTailRoundStrategy q L e sigma base)
          (grayTailFutureServer q L e base sm))
        (grayTailFutureServer q L e base sm)) :
    ∃ u, t < u ∧
      let st := grayTailStateAt (n := n) (b := b)
        q L a e sigma A sm u
      st.frozen.length = base.frozen.length + 1 ∧
        st.roundStart = u ∧ st.history = ([], []) := by
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  have hex : ∃ T, grayTailRoundGoalB q L e sigma base sm T = true := by
    simpa [familyRobustGrayGoal, grayTailRoundGoalB,
      localClient, localServer] using hgray
  let T := Nat.find hex
  have hT : grayTailRoundGoalB q L e sigma base sm T = true :=
    Nat.find_spec hex
  have hfalse : ∀ j < T,
      grayTailRoundGoalB q L e sigma base sm j = false := by
    intro j hj
    cases hBj : grayTailRoundGoalB q L e sigma base sm j with
    | false => rfl
    | true => exact (Nat.find_min hex hj hBj).elim
  have hstay := grayTailSameRound_stateAt_add
    (q := q) (L := L) (a := a) (e := e)
    base hbase hstart hactive hfalse T le_rfl
  let stT := grayTailStateAt (n := n) (b := b)
    q L a e sigma A sm (t + T)
  have hsame : GrayTailSameRound base stT := hstay.1
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
  have hhist := grayTailHistoryOK_stateAt
    (n := n) (b := b) q L a e sigma A sm (t + T)
  have htrace := grayTailTrace_stateAt
    (n := n) (b := b) q L a e sigma A sm (t + T)
  have htime : stT.time = t + T := htrace.time_eq
  have htest :
      familyRobustGrayGoalAtB (halfAmplification q)
          ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
          (grayTailRoundEps q L e stT.frozen.length)
          (grayTailRoundDelta q L e stT.frozen.length)
          stT.slots.length stT.unavailable
          (grayTailCurrentMove q L e sigma stT)
          (grayTailLocalServerMove
            (grayTailRoundDelta q L e stT.frozen.length)
            stT.slots (sm (t + T))) = true := by
    rw [grayTailCurrent_goal_eq_roundGoal hsame hhist htrace hactiveT]
    rw [hlen]
    exact hT
  refine ⟨t + T + 1, by omega, ?_⟩
  have hnext :
      grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm (t + T + 1) =
        grayTailStep q L a e sigma A stT (sm (t + T)) := by
    exact grayTailStateAt_succ q L a e sigma A sm (t + T)
  have hdoneT : stT.done = false := by
    cases hd : stT.done
    · rfl
    · exfalso
      apply hactiveT
      simp [hd]
  have hslotsT : stT.slots.isEmpty = false := by
    cases hs : stT.slots.isEmpty
    · rfl
    · exfalso
      apply hactiveT
      simp [hs]
  rw [hnext]
  simp only [grayTailStep, grayTailWaitingB, Bool.false_eq_true,
    if_false, hdoneT, hslotsT, htest, if_true]
  by_cases hu :
      grayTailHasUnanchoredReserveB e A stT.slots (sm (t + T)) = true <;>
    simp [hsame.frozen, htime]

/-- Every active controller round either exposes a positive unserved outer
request or completes by freezing one certified gray recursive call. -/
theorem grayTail_active_round_dichotomy
    {q L B a e n t : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hstart : (grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).roundStart = t)
    (hactive : ((grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).done ||
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).slots.isEmpty) ≠ true) :
    familyClientWinsUnservedPositive n (2 * (q + 1))
        (grayTailBranch q L a e)
        (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm ∨
      ∃ u, t < u ∧
        let st := grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u
        st.frozen.length = (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length + 1 ∧
          st.roundStart = u ∧ st.history = ([], []) := by
  set base := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t with hbase
  have hcert := grayTailCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  rw [← hbase] at hcert
  have hb : grayTailBaseBranch q L ≤ grayTailBranch q L a e := by
    exact le_max_right _ _
  have hspec := grayTailRound_gameSpec ha hae hB hRung
    hcert hactive hb
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  have hlocal : familyServerPlayLegal base.slots.length
      (grayTailBranch q L a e) base.unavailable localServer := by
    have hround : base.frozen.length < grayTailRoundCount q := by
      by_contra h
      push_neg at h
      have hcount : grayTailRoundCount q ≤
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length := by
        rw [← hbase]
        exact h
      have hdone := grayTail_done_of_roundCount_stateAt_core
        (q := q) (L := L) (a := a) (e := e)
        (sigma := sigma) (A := A) (sm := sm) (t := t) hcount
      rw [← hbase] at hdone
      apply hactive
      simp [hdone]
    exact grayTailFutureServer_legal hcert hround hsm
  rcases hspec.wins_robust localServer hlocal with hwin | hgray
  · by_cases hg : familyRobustGrayGoal (halfAmplification q)
        ((3 / 4 : ℚ) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e base.frozen.length)
        (grayTailRoundDelta q L e base.frozen.length)
        base.slots.length base.unavailable localClient localServer
    · exact Or.inr (grayTail_freezes_of_round_gray
        base hbase hstart hactive hg)
    · exact Or.inl (grayTail_round_positive_of_not_gray
        hsm hbase hstart hactive
        (hspec.weak.minimum_request localServer hlocal) hwin hg)
  · exact Or.inr (grayTail_freezes_of_round_gray
      base hbase hstart hactive hgray)

/-- Iterating the one-round dichotomy through the finite source round budget
either exposes a positive unserved outer request or reaches a terminal
controller state.  Time is deliberately not used as the induction measure: a
single recursive round may take arbitrarily long, but every gray alternative
strictly increases the finite list of frozen rounds. -/
theorem grayTail_eventually_terminal_or_positive
    {q L B a e n t fuel : ℕ} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : ℕ → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e)
    (hB : B ≤ max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : RobustGrayRung q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hstart : (grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).roundStart = t)
    (hbudget : grayTailRoundCount q ≤
      (grayTailStateAt
        (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).frozen.length + fuel) :
    familyClientWinsUnservedPositive n (2 * (q + 1))
        (grayTailBranch q L a e)
        (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm ∨
      ∃ u, t ≤ u ∧
        let st := grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u
        (st.done || st.slots.isEmpty) = true := by
  induction fuel generalizing t with
  | zero =>
      have hcount' : grayTailRoundCount q ≤
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length := by
        omega
      have hdone := grayTail_done_of_roundCount_stateAt_core hcount'
      exact Or.inr ⟨t, le_rfl, by simp [hdone]⟩
  | succ fuel ih =>
      by_cases hterminal : ((grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).done ||
          (grayTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).slots.isEmpty) = true
      · exact Or.inr ⟨t, le_rfl, by simpa using hterminal⟩
      · rcases grayTail_active_round_dichotomy ha hae hB hRung hsm
            hstart hterminal with hwin | hfreeze
        · exact Or.inl hwin
        · rcases hfreeze with ⟨u, htu, hlen, hstart', _hhistory⟩
          have hbudget' : grayTailRoundCount q ≤
              (grayTailStateAt
                (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm u).frozen.length + fuel := by
            rw [hlen]
            omega
          have hrec := ih (t := u) hstart' hbudget'
          rcases hrec with hwin | ⟨v, huv, hv⟩
          · exact Or.inl hwin
          · exact Or.inr ⟨v, le_trans (Nat.le_of_lt htu) huv, hv⟩

end Kolmogorov
