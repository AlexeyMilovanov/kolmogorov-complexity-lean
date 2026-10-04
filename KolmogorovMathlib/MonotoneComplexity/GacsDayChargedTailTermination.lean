import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedTailLegality

/-!
# Termination of the charged advantage phase
-/

namespace Kolmogorov

/-- Once the advantage round budget is spent, the charged tail run is finished. -/
theorem grayChargedTail_done_of_roundCount_stateAt
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hcount : grayChargedAdvantageRoundCount q <=
      (grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t).frozen.length) :
    (grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t).done = true := by
  induction t with
  | zero =>
      simp only [grayChargedAdvantageRoundCount_eq, grayChargedTailStateAt, grayChargedTailFold,
        grayChargedTailInitialState, grayChargedSourceCount_eq_used, grayTailServerPrefix,
        List.ofFn_zero, List.foldl_nil, List.length_nil, nonpos_iff_eq_zero] at hcount
      have hq1 : 1 ≤ q + 1 := by omega
      have hsq : 1 ≤ (q + 1) ^ 2 := by
        simp [pow_two]
      have hlarge : 256 ≤ 256 * (q + 1) ^ 2 := by
        simpa using Nat.mul_le_mul_left 256 hsq
      omega
  | succ t ih =>
      rw [grayChargedTailStateAt_succ] at hcount ⊢
      let st := grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm t
      have ihst : grayChargedAdvantageRoundCount q <= st.frozen.length ->
          st.done = true := by simpa [st] using ih
      change grayChargedAdvantageRoundCount q <=
        (grayChargedTailStep q L a e sigma A st (sm t)).frozen.length at hcount
      change (grayChargedTailStep q L a e sigma A st (sm t)).done = true
      by_cases hd : st.done = true
      · simp [grayChargedTailStep, grayTailWaitingB, hd]
      · by_cases hs : st.slots.isEmpty = true
        · have hprev : grayChargedAdvantageRoundCount q <= st.frozen.length := by
            simpa [grayChargedTailStep, grayTailWaitingB, hd, hs] using hcount
          exact (hd (ihst hprev)).elim
        · by_cases hg : grayChargedTailGoalAtB q e
            (grayTailRoundEps q L e st.frozen.length)
            (grayTailRoundDelta q L e st.frozen.length)
            st.slots.length st.unavailable
            (grayTailCurrentMove q L e sigma st)
            (grayTailLocalServerMove
              (grayTailRoundDelta q L e st.frozen.length)
              st.slots (sm t)) = true
          · have hnext : grayChargedAdvantageRoundCount q <=
                st.frozen.length + 1 := by
              simpa [grayChargedTailStep, grayTailWaitingB,
                hd, hs, hg] using hcount
            have hnext' : 256 * (q + 1) ^ 2 ≤ st.frozen.length + 1 + 8 := by
              unfold grayChargedAdvantageRoundCount grayTailRoundCount at hnext
              have hq1 : 1 ≤ q + 1 := by omega
              have hsq : 1 ≤ (q + 1) ^ 2 := by
                simp [pow_two]
              have hlarge : 256 ≤ 256 * (q + 1) ^ 2 := by
                simpa using Nat.mul_le_mul_left 256 hsq
              omega
            simp [grayChargedTailStep, grayTailWaitingB, hd, hs, hg, hnext']
          · have hprev : grayChargedAdvantageRoundCount q <= st.frozen.length := by
              simpa [grayChargedTailStep, grayTailWaitingB,
                hd, hs, hg] using hcount
            exact (hd (ihst hprev)).elim

/-- If a round of the tail does not meet the charged gray goal, then the recursive play wins with
positive unserved mass while avoiding small requests. -/
theorem grayChargedTail_round_positive_of_not_gray
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailState n (grayTailBranch q L a e)}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hminimum : forall T,
      familyRequestAvoidsSmall base.slots.length
        ((1 / 2 : Rat) ^
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
    (hnogray : ¬ familyChargedGrayGoal 4 (halfAmplification q)
      (dyadicScale (grayCallDepth q e))
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e base.frozen.length)
      (grayTailRoundDelta q L e base.frozen.length)
      base.slots.length base.unavailable
      (playClientFamily base.unavailable base.slots.length
        (grayTailRoundStrategy q L e sigma base)
        (grayTailFutureServer q L e base sm))
      (grayTailFutureServer q L e base sm)) :
    familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n
        (grayChargedAdvantageStrategy q L a e sigma) sm) sm := by
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  obtain ⟨j, hj, T, x, hlen, hin, hfail, hpos⟩ := hwin
  have hmin :
      (1 / 2 : Rat) ^
          (grayTailRoundDelta q L e base.frozen.length) <=
        getFamilyReq (localClient T) j x :=
    (hminimum T j hj x).resolve_left (ne_of_gt hpos)
  have hfalse : forall u,
      grayChargedTailRoundGoalB q L e sigma base sm u = false := by
    intro u
    cases hu : grayChargedTailRoundGoalB q L e sigma base sm u with
    | false => rfl
    | true =>
        exfalso
        apply hnogray
        exact ⟨u, by
        have h_eq : grayChargedTailRoundGoalB q L e sigma base sm u =
          familyChargedGrayGoalAtB 4 (halfAmplification q) (dyadicScale (grayCallDepth q e))
            (3 / 4 * dyadicScale (grayCallDepth q e))
            (grayTailRoundEps q L e (List.length base.frozen))
            (grayTailRoundDelta q L e (List.length base.frozen))
            base.slots.length base.unavailable (localClient u) (localServer u) := rfl
        rw [← h_eq]
        exact hu⟩
  have hstay := grayChargedTailSameRound_stateAt_add
    (q := q) (L := L) (a := a) (e := e)
    base hbase hstart hactive (T := T) (fun u _ => hfalse u) T le_rfl
  let stT := grayChargedTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + T)
  have hsame : GrayTailSameRound base stT := hstay.1
  have hhistlen : stT.history.2.length = T := hstay.2
  have hhist := grayChargedTailHistoryOK_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + T)
  have htrace := grayChargedTailTrace_stateAt
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
  have hfailT : forall u,
      ¬ Serves
        (getFamilyAlloc (grayTailFutureServer q L e stT sm u) jT.val x)
        (getFamilyReq (grayTailCurrentMove q L e sigma stT) jT.val x) := by
    intro u
    have hjT : jT.val = j := rfl
    rw [hfuture, hcurrent, hjT]
    exact hfail u
  have hposT :
      0 < getFamilyReq (grayTailCurrentMove q L e sigma stT) jT.val x := by
    have hjT : jT.val = j := rfl
    rw [hcurrent, hjT]
    exact hpos
  have hdisplay :
      playClientFamily A n
          (grayChargedAdvantageStrategy q L a e sigma) sm (t + T) =
        grayChargedTailOutput q L a e sigma stT := by
    simpa [grayTailBranch, stT] using
      (playClientFamily_grayChargedAdvantageStrategy
        q L a e n sigma A sm (t + T))
  have hout := grayTailOutput_transfers_positive hsm
    (grayChargedTailShape_stateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + T))
    hsame.done hdisplay jT x hlen hin (by
      rw [hcurrent, hsame.frozen]
      simpa [jT] using hmin)
    hfailT hposT
  convert hout using 1

/-- If the round meets the charged gray goal, the tail freezes it at some later time, starting a
fresh round with empty history. -/
theorem grayChargedTail_freezes_of_round_gray
    {n b q L a e t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (base : GrayTailState n b)
    (hbase : base = grayChargedTailStateAt (n := n) (b := b)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true)
    (hgray : familyChargedGrayGoal 4 (halfAmplification q)
      (dyadicScale (grayCallDepth q e))
      ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
      (grayTailRoundEps q L e base.frozen.length)
      (grayTailRoundDelta q L e base.frozen.length)
      base.slots.length base.unavailable
      (playClientFamily base.unavailable base.slots.length
        (grayTailRoundStrategy q L e sigma base)
        (grayTailFutureServer q L e base sm))
      (grayTailFutureServer q L e base sm)) :
    ∃ u, t < u ∧
      let st := grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm u
      st.frozen.length = base.frozen.length + 1 ∧
        st.roundStart = u ∧ st.history = ([], []) := by
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  have hex : ∃ T,
      grayChargedTailRoundGoalB q L e sigma base sm T = true := by
    unfold familyChargedGrayGoal at hgray
    rcases hgray with ⟨T, hT⟩
    use T
    have h_eq : grayChargedTailRoundGoalB q L e sigma base sm T =
        familyChargedGrayGoalAtB 4 (halfAmplification q) (dyadicScale (grayCallDepth q e))
        (3 / 4 * dyadicScale (grayCallDepth q e)) (grayTailRoundEps q L e (List.length base.frozen))
        (grayTailRoundDelta q L e (List.length base.frozen)) base.slots.length base.unavailable
        (localClient T) (localServer T) := rfl
    rw [h_eq]
    exact hT
  let T := Nat.find hex
  have hT : grayChargedTailRoundGoalB q L e sigma base sm T = true :=
    Nat.find_spec hex
  have hfalse : forall j, j < T ->
      grayChargedTailRoundGoalB q L e sigma base sm j = false := by
    intro j hj
    cases hBj : grayChargedTailRoundGoalB q L e sigma base sm j with
    | false => rfl
    | true => exact (Nat.find_min hex hj hBj).elim
  have hstay := grayChargedTailSameRound_stateAt_add
    (q := q) (L := L) (a := a) (e := e)
    base hbase hstart hactive hfalse T le_rfl
  let stT := grayChargedTailStateAt (n := n) (b := b)
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
  have hhist := grayChargedTailHistoryOK_stateAt
    (n := n) (b := b) q L a e sigma A sm (t + T)
  have htrace := grayChargedTailTrace_stateAt
    (n := n) (b := b) q L a e sigma A sm (t + T)
  have htime : stT.time = t + T := htrace.time_eq
  have htest : grayChargedTailGoalAtB q e
      (grayTailRoundEps q L e stT.frozen.length)
      (grayTailRoundDelta q L e stT.frozen.length)
      stT.slots.length stT.unavailable
      (grayTailCurrentMove q L e sigma stT)
      (grayTailLocalServerMove
        (grayTailRoundDelta q L e stT.frozen.length)
        stT.slots (sm (t + T))) = true := by
    rw [grayChargedTailCurrent_goal_eq_roundGoal
      hsame hhist htrace hactiveT]
    rw [hlen]
    exact hT
  refine ⟨t + T + 1, by omega, ?_⟩
  have hnext : grayChargedTailStateAt (n := n) (b := b)
        q L a e sigma A sm (t + T + 1) =
      grayChargedTailStep q L a e sigma A stT (sm (t + T)) :=
    grayChargedTailStateAt_succ q L a e sigma A sm (t + T)
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
  simp only [grayChargedTailStep, grayTailWaitingB, Bool.false_eq_true,
    ite_false, hdoneT, hslotsT, htest, ite_true]
  simp [hsame.frozen, htime]

/-- From an active round, either the advantage strategy already wins with positive unserved mass,
or the round gets frozen at some later time. -/
theorem grayChargedTail_active_round_dichotomy
    {q L B a e n t : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailState n (grayTailBranch q L a e)}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hactive : (base.done || base.slots.isEmpty) ≠ true) :
    familyClientWinsUnservedPositive n (2 * (q + 1))
        (grayTailBranch q L a e)
        (playClientFamily A n
          (grayChargedAdvantageStrategy q L a e sigma) sm) sm ∨
      ∃ u, t < u ∧
        let st := grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u
        st.frozen.length = base.frozen.length + 1 ∧
          st.roundStart = u ∧ st.history = ([], []) := by
  have hcert := grayChargedTailCertified_stateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  rw [← hbase] at hcert
  have hb : grayTailBaseBranch q L <= grayTailBranch q L a e :=
    le_max_right _ _
  have hspec := grayChargedTailRound_gameSpec ha hae hB hRung
    hcert hactive hb
  let localServer := grayTailFutureServer q L e base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayTailRoundStrategy q L e sigma base) localServer
  have hlocal : familyServerPlayLegal base.slots.length
      (grayTailBranch q L a e) base.unavailable localServer := by
    have hround : base.frozen.length < grayTailRoundCount q := by
      by_contra h
      simp only [not_lt] at h
      have hcount : grayTailRoundCount q <=
          (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length := by
        rw [← hbase]
        exact h
      have hadv : grayChargedAdvantageRoundCount q <=
          (grayChargedTailStateAt q L a e sigma A sm t).frozen.length :=
        le_trans (by simp [grayChargedAdvantageRoundCount]) hcount
      have hdone := grayChargedTail_done_of_roundCount_stateAt hadv
      rw [← hbase] at hdone
      apply hactive
      simp [hdone]
    exact grayChargedTailFutureServer_legal hcert hround hsm
  rcases hspec.wins_charged localServer hlocal with hwin | hgray
  · by_cases hg : familyChargedGrayGoal 4 (halfAmplification q)
        (dyadicScale (grayCallDepth q e))
        ((3 / 4 : Rat) * dyadicScale (grayCallDepth q e))
        (grayTailRoundEps q L e base.frozen.length)
        (grayTailRoundDelta q L e base.frozen.length)
        base.slots.length base.unavailable localClient localServer
    · exact Or.inr (grayChargedTail_freezes_of_round_gray
        base hbase hstart hactive hg)
    · exact Or.inl (grayChargedTail_round_positive_of_not_gray
        hsm hbase hstart hactive
        (hspec.weak.minimum_request localServer hlocal) hwin hg)
  · exact Or.inr (grayChargedTail_freezes_of_round_gray
      base hbase hstart hactive hgray)

/-- With enough fuel to exhaust the round budget, either the advantage strategy wins with
positive unserved mass, or the tail reaches a terminal state. -/
theorem grayChargedTail_eventually_terminal_or_positive
    {q L B a e n t fuel : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailState n (grayTailBranch q L a e)}
    (ha : 1 <= a) (hae : a <= e)
    (hB : B <= max 2 (256 * (q + 1) * 2 ^ L))
    (hRung : ChargedGrayRung 4 q L B sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = grayChargedTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t)
    (hstart : base.roundStart = t)
    (hbudget : grayChargedAdvantageRoundCount q <= base.frozen.length + fuel) :
    familyClientWinsUnservedPositive n (2 * (q + 1))
        (grayTailBranch q L a e)
        (playClientFamily A n
          (grayChargedAdvantageStrategy q L a e sigma) sm) sm ∨
      ∃ u, t <= u ∧
        let st := grayChargedTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u
        (st.done || st.slots.isEmpty) = true := by
  induction fuel generalizing t base with
  | zero =>
      have hcount : grayChargedAdvantageRoundCount q <= base.frozen.length := by omega
      have hcount' : grayChargedAdvantageRoundCount q <=
          (grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).frozen.length := by
        simpa only [← hbase] using hcount
      have hdone' := grayChargedTail_done_of_roundCount_stateAt hcount'
      have hdone : base.done = true := by
        simpa only [hbase] using hdone'
      exact Or.inr ⟨t, le_rfl, by rw [← hbase]; simp [hdone]⟩
  | succ fuel ih =>
      by_cases hterminal : (base.done || base.slots.isEmpty) = true
      · exact Or.inr ⟨t, le_rfl, by simpa [hbase] using hterminal⟩
      · rcases grayChargedTail_active_round_dichotomy ha hae hB hRung hsm
            hbase hstart hterminal with hwin | hfreeze
        · exact Or.inl hwin
        · rcases hfreeze with ⟨u, htu, hlen, hstart', _hhistory⟩
          let next := grayChargedTailStateAt
            (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u
          have hbudget' : grayChargedAdvantageRoundCount q <=
              next.frozen.length + fuel := by
            dsimp [next]
            rw [hlen]
            omega
          have hrec := ih (t := u) (base := next) rfl hstart' hbudget'
          rcases hrec with hwin | ⟨v, huv, hv⟩
          · exact Or.inl hwin
          · exact Or.inr ⟨v, le_trans (Nat.le_of_lt htu) huv, hv⟩

end Kolmogorov
