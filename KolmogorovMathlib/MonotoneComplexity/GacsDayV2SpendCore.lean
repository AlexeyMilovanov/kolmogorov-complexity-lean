import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendLegality
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2RoundPositive
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2GoalCoarsen
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChildBranching
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendExit

/-!
# O2 closed: every V2 spend pass is eventually left, from the pinned rung

The spend-side analogue of `GacsDayV2AdvantageCore`: every V2 spend pass is a
legal play of the child rung's game at the pass anchor `spendEps`
(gap `graySpendSpan q`, export `spendEps + fp q = spendDelta` at `L = fp q`);
the rung's charged goal coarsens to the pass's block spend goal, which is
then accepted at the first accepted exchange while the run stays in the pass
(`GrayChargedSpendGoalEventuallyV2`'s witness); otherwise the sub-game's
unserved positive request transfers to the outer V2 client.  The
per-time statement follows by the V1 induction trick (`grayCharged_spend_progress`):
a pass is either continued from the previous time or freshly entered at a round
start.
-/

namespace Kolmogorov

/-- The Boolean block-spend-goal test of one fixed pass, indexed by the
exchange number. -/
def grayChargedSpendRoundGoalBV2 {n b : Nat}
    (q L a e pass : Nat) (sigma : FamilyStrategyScheme)
    (base : GrayTailStateV2 n b) (sm : Nat -> FamilyServerMove)
    (T : Nat) : Bool :=
  let localServer := grayChargedSpendFutureServerV2 a L e pass base sm
  let localClient := playClientFamily base.unavailable base.slots.length
    (grayChargedSpendRoundStrategyV2 q L a e pass sigma) localServer
  grayChargedBlockSpendGoalAtB q L a e pass base.slots.length base.unavailable
    (localClient T) (localServer T)

/-- The recorded server list agrees with the spend future server before the
current exchange. -/
lemma grayChargedSpendReplayOKV2_server_before {n b : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {st : GrayTailStateV2 n b}
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st)
    {j : Nat} (hj : j < st.history.2.length) :
    grayTailServerOfList st.history.2 j =
      grayChargedSpendFutureServerV2 a L e pass st sm j := by
  have hget := congrArg
    (fun l : List FamilyServerMove => l.getD j [])
    hst.servers_eq
  unfold grayTailServerOfList grayChargedSpendFutureServerV2
  have h1 : st.history.2.getD j (st.history.2.getLastD []) =
      st.history.2.getD j [] := by
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj]
  rw [h1]
  simpa [List.getD_eq_getElem?_getD, hj, List.getElem_ofFn] using hget

/-- The current spend move is the canonical play of the pass strategy against
the spend future server. -/
lemma grayBlockSpendMoveV2_eq_futurePlay {n b : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {st : GrayTailStateV2 n b}
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st) :
    grayBlockSpendMoveV2 q L a e pass sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
        (grayChargedSpendFutureServerV2 a L e pass st sm)
        st.history.2.length := by
  rw [grayBlockSpendMoveV2_eq_play q L a e pass sigma st hst.history_ok]
  apply playClientFamily_congr_before
  intro j hj
  exact grayChargedSpendReplayOKV2_server_before hst hj

/-- The controller's local server move at a spend time is the spend future
server at the current exchange. -/
lemma grayChargedSpendLocalServerMoveV2_eq_future {n b : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {st : GrayTailStateV2 n b}
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st) :
    grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots (sm t) =
      grayChargedSpendFutureServerV2 a L e pass st sm st.history.2.length := by
  unfold grayChargedSpendFutureServerV2
  rw [hst.active_time]

/-- The live block-spend-goal test is the replayed test of the pass at the
current exchange number. -/
lemma grayChargedSpendCurrent_goal_eq_roundGoalV2 {n b : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {base st : GrayTailStateV2 n b}
    (hsame : GrayBlockSameRoundV2 base st)
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st) :
    grayChargedBlockSpendGoalAtB q L a e pass st.slots.length st.unavailable
        (grayBlockSpendMoveV2 q L a e pass sigma st)
        (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots
          (sm t)) =
      grayChargedSpendRoundGoalBV2 q L a e pass sigma base sm
        st.history.2.length := by
  rw [grayBlockSpendMoveV2_eq_futurePlay hst,
    grayChargedSpendLocalServerMoveV2_eq_future hst]
  have hfuture :
      grayChargedSpendFutureServerV2 a L e pass st sm =
        grayChargedSpendFutureServerV2 a L e pass base sm := by
    funext u
    simp [grayChargedSpendFutureServerV2, hsame.slots, hsame.roundStart]
  simp only [grayChargedSpendRoundGoalBV2]
  rw [hfuture]
  simp [hsame.slots, hsame.unavailable]

/-- A spend time whose live test fails: the pass continues with the same
round data. -/
lemma grayChargedRunStateV2_spend_step_false {n : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass)
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots.length
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.unavailable
      (grayBlockSpendMoveV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core)
      (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots (sm t)) = false) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).phase = .spend pass ∧
      GrayBlockSameRoundV2
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + 1)).core ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).core.history.2.length =
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.history.2.length + 1 := by
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  rw [grayChargedRunStateV2_succ]
  generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcert hphase hgoal ⊢
  cases hcert with
  | advantage core hcore hsource hdone => simp at hphase
  | wait core hcore hsource hdone => simp at hphase
  | spend pass' core hspend =>
      have hpass : pass' = pass := GrayChargedPhase.spend.inj hphase
      subst hpass
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      simp only at hgoal
      simp only [grayChargedStepV2, hslots, hgoal, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp, ⟨hspend.done_false, rfl, rfl, rfl, rfl⟩, by simp⟩
  | done core hdone2 => simp at hphase

/-- The spend certificate of a spend time. -/
lemma grayChargedRunStateV2_spendCertified_of_phase {n : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass) :
    GrayChargedSpendCertifiedV2 q L a e A sm t pass
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core := by
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcert hphase ⊢
  cases hcert with
  | advantage core hcore hsource hd => simp at hphase
  | wait core hcore hsource hd => simp at hphase
  | spend pass' core hspend =>
      have hpass : pass' = pass := GrayChargedPhase.spend.inj hphase
      subst hpass
      exact hspend
  | done core hdone2 => simp at hphase

/-- While the replayed spend test fails, the run stays in the pass with the
same round data and the exchange counter is the elapsed time. -/
lemma grayChargedSpendV2_sameRound_stateAt_add {n : Nat}
    {q L a e pass t T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass)
    (hstart : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.roundStart = t)
    (hfalse : forall j, j < T ->
      grayChargedSpendRoundGoalBV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core sm j = false) :
    forall j, j <= T ->
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + j)).phase = .spend pass ∧
        GrayBlockSameRoundV2
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + j)).core ∧
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + j)).core.history.2.length = j := by
  intro j hj
  induction j with
  | zero =>
      have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm t pass hphase
      have hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done = false := by
        have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
        generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t = st at hcert hphase ⊢
        cases hcert with
        | advantage core hcore hsource hd => simp at hphase
        | wait core hcore hsource hd => simp at hphase
        | spend pass' core hspend => exact hspend.done_false
        | done core hdone2 => simp at hphase
      refine ⟨by simpa using hphase, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa using hdone
      · simp
      · simp
      · simp
      · simp
      · have htime := hok.active_time
        rw [hstart] at htime
        simp only [Nat.add_zero]
        omega
  | succ j ih =>
      have hjT : j <= T := by omega
      obtain ⟨hphaseJ, hsame, hlen⟩ := ih hjT
      have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm (t + j) pass hphaseJ
      have hjlt : j < T := by omega
      have hgoal : grayChargedBlockSpendGoalAtB q L a e pass
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + j)).core.slots.length
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + j)).core.unavailable
          (grayBlockSpendMoveV2 q L a e pass sigma
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm (t + j)).core)
          (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm (t + j)).core.slots (sm (t + j))) = false := by
        rw [grayChargedSpendCurrent_goal_eq_roundGoalV2 hsame hok, hlen]
        exact hfalse j hjlt
      obtain ⟨hphase', hsame', hlen'⟩ :=
        grayChargedRunStateV2_spend_step_false hphaseJ hgoal
      have hsucc : t + (j + 1) = (t + j) + 1 := by omega
      rw [hsucc]
      refine ⟨hphase', ?_, ?_⟩
      · exact ⟨hsame'.done, hsame'.frozen.trans hsame.frozen,
          hsame'.unavailable.trans hsame.unavailable,
          hsame'.slots.trans hsame.slots,
          hsame'.roundStart.trans hsame.roundStart⟩
      · rw [hlen', hlen]

/-- **The first accepted exchange**: if the replayed spend test of a pass is
eventually accepted, the run reaches a time in the pass at which the live
test is accepted. -/
theorem grayChargedSpendV2_accepted_of_gray {n : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass)
    (hstart : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.roundStart = t)
    (hgray : ∃ T, grayChargedSpendRoundGoalBV2 q L a e pass sigma
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core sm T = true) :
    ∃ u, t <= u ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm u).phase = .spend pass ∧
      grayChargedBlockSpendGoalAtB q L a e pass
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u).core.slots.length
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u).core.unavailable
        (grayBlockSpendMoveV2 q L a e pass sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).core)
        (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).core.slots (sm u)) = true := by
  classical
  let T := Nat.find hgray
  have hT := Nat.find_spec hgray
  have hfalse : forall j, j < T ->
      grayChargedSpendRoundGoalBV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core sm j = false := by
    intro j hj
    cases hBj : grayChargedSpendRoundGoalBV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core sm j with
    | false => rfl
    | true => exact (Nat.find_min hgray hj hBj).elim
  obtain ⟨hphaseT, hsame, hlen⟩ :=
    grayChargedSpendV2_sameRound_stateAt_add hphase hstart hfalse T le_rfl
  have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm (t + T) pass hphaseT
  refine ⟨t + T, by omega, hphaseT, ?_⟩
  rw [grayChargedSpendCurrent_goal_eq_roundGoalV2 hsame hok, hlen]
  exact hT

/-- The V2 family-move transfer of an unserved positive local request, for an
arbitrary local move and truncation depth. -/
theorem grayChargedV2_familyMove_transfers_positive_at
    {n b h T source delta : Nat} {threshold eps : Rat}
    {A : Allocation} {sm : Nat -> FamilyServerMove} {cm : Nat -> FamilyClientMove}
    {st : GrayTailStateV2 n b} {current : FamilyClientMove}
    (hsm : familyServerPlayLegal n b A sm)
    (hkeys : (grayTailFrozenSlots (st.frozen.map GrayTailRoundV2.toV1) ++
      st.slots).Nodup)
    (hdisplay : cm T =
      grayChargedTailFamilyMove source threshold eps
        (st.frozen.map GrayTailRoundV2.toV1) st.slots current)
    (j : Fin st.slots.length) (x : GacsDayNode)
    (hlen : x.length ≤ h) (hin : ∀ d ∈ x, d < b)
    (hmin : (1 / 2 : Rat) ^ delta ≤ getFamilyReq current j.val x)
    (hfail : ∀ u,
      ¬ Serves (getFamilyAlloc (grayTailLocalServerMove delta st.slots
          (sm (st.roundStart + u))) j.val x)
        (getFamilyReq current j.val x))
    (hpos : 0 < getFamilyReq current j.val x) :
    familyClientWinsUnservedPositive n (h + 2) b cm sm := by
  let s := st.slots.get j
  let y : GacsDayNode := s.2.1.val :: s.2.2.val :: x
  have hreq : getFamilyReq (cm T) s.1.val y = getFamilyReq current j.val x := by
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
    rw [getFamilyAlloc_grayTailLocalServerMove st.slots _ j.val j.isLt x hin]
    simp only [getAlloc_extractSubtreeServerMove]
    rw [Nat.add_sub_of_le (le_max_right u st.roundStart)]
    exact (serves_truncAlloc_iff hmin).mpr hmono
  · change 0 < getFamilyReq (cm T) s.1.val y
    rw [hreq]
    exact hpos

/-- The V2 charged run's displayed move in a spend pass is the family move of
the current spend move. -/
lemma grayChargedRunMoveV2_eq_of_spend
    {q L a e n t pass : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass)
    (hslots : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots.isEmpty = false) :
    playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.slots
        (grayBlockSpendMoveV2 q L a e pass sigma
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core) := by
  have hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = false :=
    (grayChargedRunStateV2_spendCertified_of_phase hphase).done_false
  rw [playClientFamily_grayChargedStrategyV2]
  simp [grayChargedDisplayedMoveV2, hphase, hdone, hslots]

/-- **Positive win from an unserved positive spend sub-game request** (V2). -/
theorem grayChargedSpendV2_round_positive_of_not_gray
    {q L a e n t pass : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {base : GrayTailStateV2 n (grayTailBranch q L a e)}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hbase : base = (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass)
    (hstart : base.roundStart = t)
    (hminimum : forall T,
      familyRequestAvoidsSmall base.slots.length
        ((1 / 2 : Rat) ^ (grayChargedSpendDelta a L e pass))
        (playClientFamily base.unavailable base.slots.length
          (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
          (grayChargedSpendFutureServerV2 a L e pass base sm) T))
    (hwin : familyClientWinsUnservedPositive base.slots.length (2 * q)
      (grayTailBranch q L a e)
      (playClientFamily base.unavailable base.slots.length
        (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
        (grayChargedSpendFutureServerV2 a L e pass base sm))
      (grayChargedSpendFutureServerV2 a L e pass base sm))
    (hnogray : ¬ ∃ T, grayChargedSpendRoundGoalBV2 q L a e pass sigma base sm T = true) :
    GrayChargedPositiveV2 q L a e n sigma A sm := by
  subst hbase
  let localServer := grayChargedSpendFutureServerV2 a L e pass
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core sm
  let localClient := playClientFamily
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.unavailable
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots.length
    (grayChargedSpendRoundStrategyV2 q L a e pass sigma) localServer
  obtain ⟨j, hj, T, x, hlen, hin, hfail, hpos⟩ := hwin
  have hmin :
      (1 / 2 : Rat) ^ (grayChargedSpendDelta a L e pass) <=
        getFamilyReq (localClient T) j x :=
    (hminimum T j hj x).resolve_left (ne_of_gt hpos)
  have hfalse : forall u,
      grayChargedSpendRoundGoalBV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core sm u = false := by
    intro u
    cases hu : grayChargedSpendRoundGoalBV2 q L a e pass sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core sm u with
    | false => rfl
    | true => exact (hnogray ⟨u, hu⟩).elim
  obtain ⟨hphaseT, hsame, hhistlen⟩ :=
    grayChargedSpendV2_sameRound_stateAt_add (T := T) hphase hstart
      (fun u _ => hfalse u) T le_rfl
  let stT := (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm (t + T)).core
  have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm (t + T) pass hphaseT
  have hfuture : grayChargedSpendFutureServerV2 a L e pass stT sm = localServer := by
    funext u
    simp [grayChargedSpendFutureServerV2, localServer, stT, hsame.slots,
      hsame.roundStart]
  have hcurrent : grayBlockSpendMoveV2 q L a e pass sigma stT = localClient T := by
    rw [grayBlockSpendMoveV2_eq_futurePlay hok, hfuture, hhistlen]
    change playClientFamily stT.unavailable stT.slots.length
      (grayChargedSpendRoundStrategyV2 q L a e pass sigma) localServer T = localClient T
    rw [hsame.unavailable, hsame.slots]
  let jT : Fin stT.slots.length := ⟨j, by simpa [stT, hsame.slots] using hj⟩
  have hfailT : forall u,
      ¬ Serves
        (getFamilyAlloc (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
          stT.slots (sm (stT.roundStart + u))) jT.val x)
        (getFamilyReq (grayBlockSpendMoveV2 q L a e pass sigma stT) jT.val x) := by
    intro u
    have hf := hfail u
    have hserver : grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
        stT.slots (sm (stT.roundStart + u)) = localServer u := by
      rw [← hfuture]
      rfl
    rw [hserver, hcurrent]
    exact hf
  have hposT : 0 < getFamilyReq (grayBlockSpendMoveV2 q L a e pass sigma stT) jT.val x := by
    rw [hcurrent]
    exact hpos
  have hminT : (1 / 2 : Rat) ^ (grayChargedSpendDelta a L e pass) <=
      getFamilyReq (grayBlockSpendMoveV2 q L a e pass sigma stT) jT.val x := by
    rw [hcurrent]
    exact hmin
  have hslotsT : stT.slots.isEmpty = false := by
    change (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + T)).core.slots.isEmpty = false
    rw [hsame.slots]
    exact (grayChargedRunStateV2_spendCertified_of_phase hphase).slots_nonempty
  have hdisplay :
      playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm (t + T) =
        grayChargedTailFamilyMove (grayChargedSourceCount a e)
          (grayChargedThreshold q e) (dyadicScale e)
          (stT.frozen.map GrayTailRoundV2.toV1) stT.slots
          (grayBlockSpendMoveV2 q L a e pass sigma stT) :=
    grayChargedRunMoveV2_eq_of_spend hphaseT hslotsT
  have hkeys :
      (grayTailFrozenSlots (stT.frozen.map GrayTailRoundV2.toV1) ++
        stT.slots).Nodup := by
    rw [grayTailFrozenSlots_map_toV1]
    exact (grayChargedRunStateV2_coreCertified (n := n) q L a e sigma A sm
      (t + T)).all_slots_nodup
  have hout := grayChargedV2_familyMove_transfers_positive_at
    (h := 2 * q) (delta := grayChargedSpendDelta a L e pass) hsm hkeys hdisplay
    jT x hlen hin hminT hfailT hposT
  unfold GrayChargedPositiveV2
  rw [show 2 * (q + 1) = 2 * q + 2 by ring]
  exact hout

/-- **The pinned rung supplies the game specification of every V2 spend
pass**, on the outer tree. -/
theorem grayChargedSpendRound_gameSpecV2
    {q L a e n pass : Nat} {sigma : FamilyStrategyScheme}
    {st : GrayTailStateV2 n (grayTailBranch q L a e)}
    (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hslots : st.slots.isEmpty = false) :
    ChargedGrayFamilyGameSpec 4 (halfAmplification q)
      (dyadicScale (grayChargedSpendEps a L e pass))
      ((3 / 4 : Rat) * dyadicScale (grayChargedSpendEps a L e pass))
      (grayChargedSpendEps a L e pass)
      (grayChargedSpendDelta a L e pass)
      (2 * q) (grayTailBranch q L a e) st.slots.length st.unavailable
      (grayChargedSpendRoundStrategyV2 q L a e pass sigma) := by
  have hEps1 : 1 <= grayChargedSpendEps a L e pass := by
    unfold grayChargedSpendEps grayChargedSpendAlphaDepth
    omega
  have hslotlen : 1 <= st.slots.length := by
    cases hs : st.slots with
    | nil => simp [hs] at hslots
    | cons _ _ => simp
  have hbase := hRung (grayChargedSpendEps a L e pass) hEps1
    st.slots.length st.unavailable hslotlen
  have hspan : forall x : Nat,
      x + 8 * grayFootprint (q - 1) + 3 = x + graySpendSpan q := by
    intro x
    unfold graySpendSpan
    omega
  have hbranch :
      ladderBranching (grayTailBaseBranch (q - 1) (grayFootprint (q - 1)))
          (grayChargedSpendEps a L e pass)
          (grayChargedSpendEps a L e pass + 8 * grayFootprint (q - 1) + 3) <=
        grayTailBranch q L a e := by
    rw [hspan]
    have h1 := grayChildBranching_le_baseBranch (q := q) (L := L)
      (a' := grayChargedSpendEps a L e pass)
      (by rw [hL]; exact grayFootprint_pred_le q)
    have h2 : grayTailBaseBranch q L <= grayTailBranch q L a e :=
      le_max_right _ _
    exact le_trans h1 h2
  have hspec := hbase.mono_branching hbranch
  rw [hspan] at hspec
  subst hL
  unfold grayChargedSpendDelta grayChargedSpendRoundStrategyV2
  exact hspec

/-- **The spend goal is eventually accepted from a pass's round start** (or
the outer client wins the positive game). -/
theorem grayChargedSpendV2_goal_eventually_from_start
    {q L a e n t pass : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass)
    (hstart : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.roundStart = t) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      ∃ u, t <= u ∧
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u).phase = .spend pass ∧
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm u).core.slots.isEmpty = true ∨
          grayChargedBlockSpendGoalAtB q L a e pass
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm u).core.slots.length
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm u).core.unavailable
            (grayBlockSpendMoveV2 q L a e pass sigma
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm u).core)
            (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm u).core.slots (sm u)) = true) := by
  obtain ⟨base, hbase⟩ : ∃ base : GrayTailStateV2 n (grayTailBranch q L a e),
      base = (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core := ⟨_, rfl⟩
  have hspend : GrayChargedSpendCertifiedV2 q L a e A sm t pass base := by
    rw [hbase]
    exact grayChargedRunStateV2_spendCertified_of_phase hphase
  have hstartB : base.roundStart = t := by
    rw [hbase]
    exact hstart
  have hspec := grayChargedSpendRound_gameSpecV2 (st := base) (pass := pass)
    hL hRung hspend.slots_nonempty
  let localServer := grayChargedSpendFutureServerV2 a L e pass base sm
  have hlocal : familyServerPlayLegal base.slots.length
      (grayTailBranch q L a e) base.unavailable localServer :=
    grayChargedSpendFutureServerV2_legal hspend hsm
  rcases hspec.wins_charged localServer hlocal with hwin | hgray
  · by_cases hg : ∃ T, grayChargedSpendRoundGoalBV2 q L a e pass sigma base sm T = true
    · rw [hbase] at hg
      obtain ⟨u, htu, hphu, hacc⟩ := grayChargedSpendV2_accepted_of_gray hphase hstart hg
      exact Or.inr ⟨u, htu, hphu, Or.inr hacc⟩
    · exact Or.inl (grayChargedSpendV2_round_positive_of_not_gray hsm hbase hphase hstartB
        (hspec.weak.minimum_request localServer hlocal) hwin hg)
  · have hgray' : ∃ T, familyChargedGrayGoalAtB 4 (halfAmplification q)
        (dyadicScale (grayChargedSpendEps a L e pass))
        ((3 / 4 : Rat) * dyadicScale (grayChargedSpendEps a L e pass))
        (grayChargedSpendEps a L e pass)
        (grayChargedSpendDelta a L e pass)
        base.slots.length base.unavailable
        (playClientFamily base.unavailable base.slots.length
          (grayChargedSpendRoundStrategyV2 q L a e pass sigma) localServer T)
        (localServer T) = true := hgray
    obtain ⟨T, hT⟩ := hgray'
    have hT' : grayChargedSpendRoundGoalBV2 q L a e pass sigma base sm T = true := by
      unfold grayChargedSpendRoundGoalBV2 grayChargedBlockSpendGoalAtB
      exact hT
    rw [hbase] at hT'
    obtain ⟨u, htu, hphu, hacc⟩ :=
      grayChargedSpendV2_accepted_of_gray hphase hstart ⟨T, hT'⟩
    exact Or.inr ⟨u, htu, hphu, Or.inr hacc⟩

/-- **O2's core from the pinned rung**: the eventual spend goal at every
spend time (V1's `grayCharged_spend_progress` induction: a pass is continued
from the previous time or freshly entered at a round start). -/
theorem grayChargedV2_spendGoalEventually_of_rung
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    GrayChargedSpendGoalEventuallyV2 q L a e n sigma A sm := by
  intro t
  induction t with
  | zero =>
      intro pass hphase
      simp [grayChargedRunStateV2, grayChargedFoldV2, grayChargedInitialStateV2,
        grayTailServerPrefix] at hphase
  | succ t ih =>
      intro pass hphase
      by_cases hprev : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).phase = .spend pass
      · rcases ih pass hprev with hpos | ⟨u, htu, hphu, hacc⟩
        · exact Or.inl hpos
        · have htu' : t + 1 <= u := by
            by_contra hnot
            have hut : u = t := by omega
            subst hut
            have hleave := grayChargedStepV2_leaves_spend_of_goal
              (q := q) (L := L) (a := a) (e := e) (sigma := sigma) (A := A)
              (sm := sm u) hphu hacc
            rw [← grayChargedRunStateV2_succ] at hleave
            exact hleave hphase
          exact Or.inr ⟨u, htu', hphu, hacc⟩
      · have hstart := grayChargedRunStateV2_spend_roundStart_of_new
          q L a e sigma A sm t pass hphase hprev
        exact grayChargedSpendV2_goal_eventually_from_start hL hRung hsm hphase hstart

/-- **O2 closed from the pinned rung**: every V2 spend pass is eventually
left, or the outer client wins the positive game. -/
theorem grayChargedV2_spendProgress_of_rung
    {q L a e n : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    (hL : L = grayFootprint q)
    (hRung : PinnedChargedRung 4 q sigma)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm) :
    GrayChargedSpendProgressV2 q L a e n sigma A sm :=
  grayChargedV2_spendProgress_of_goal
    (grayChargedV2_spendGoalEventually_of_rung hL hRung hsm)

end Kolmogorov
