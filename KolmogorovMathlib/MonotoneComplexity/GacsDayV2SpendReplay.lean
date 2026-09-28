import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure

/-!
# Run-level replay consistency of the V2 spend passes

The V2 analogue, for the charged run's spend phase, of the block-level
`GrayBlockHistoryOKV2` / `GrayTailTraceV2`: while the run is in `.spend pass`,
the recorded client history is the canonical play of the pass strategy
`sigma spendEps (spendEps + graySpendSpan q)` against the recorded server list,
the recorded server list is the local-server play from the pass's round start,
and `roundStart + |history| = t`.  A pass is entered fresh (empty history,
round start = entry time) both from the advantage exit and from the previous
pass's freeze.
-/

namespace Kolmogorov

/-- The V2 spend round strategy of pass `pass` (independent of the state). -/
def grayChargedSpendRoundStrategyV2 (q L a e pass : Nat)
    (sigma : FamilyStrategyScheme) : ClientFamilyStrategy :=
  sigma (grayChargedSpendEps a L e pass)
    (grayChargedSpendEps a L e pass + graySpendSpan q)

/-- Replay consistency of a V2 spend pass: the client half of the stored history is the replay of
the pass strategy against the stored server moves, the round start plus the stored history
length is `t`, and the stored server moves are the outer moves from the round start on,
localised to the pass's slots at its fine depth. -/
structure GrayChargedSpendReplayOKV2 {n b : Nat}
    (q L a e pass : Nat) (sigma : FamilyStrategyScheme)
    (sm : Nat -> FamilyServerMove) (t : Nat) (st : GrayTailStateV2 n b) : Prop where
  history_ok : st.history.1 =
    List.ofFn fun j : Fin st.history.2.length =>
      playClientFamily st.unavailable st.slots.length
        (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
        (grayTailServerOfList st.history.2) j.val
  active_time : st.roundStart + st.history.2.length = t
  servers_eq : st.history.2 =
    List.ofFn fun j : Fin st.history.2.length =>
      grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots
        (sm (st.roundStart + j.val))

/-- A freshly entered pass (empty history, round start = entry time) is
replay-consistent. -/
lemma grayChargedSpendReplayOKV2_fresh {n b : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {st : GrayTailStateV2 n b}
    (hhist : st.history = ([], [])) (hstart : st.roundStart = t) :
    GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hhist, hstart]

/-- The current V2 spend move is the canonical play of the pass strategy
against the recorded server list. -/
lemma grayBlockSpendMoveV2_eq_play {n b : Nat}
    (q L a e pass : Nat) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b)
    (hst : st.history.1 =
      List.ofFn fun j : Fin st.history.2.length =>
        playClientFamily st.unavailable st.slots.length
          (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
          (grayTailServerOfList st.history.2) j.val) :
    grayBlockSpendMoveV2 q L a e pass sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
        (grayTailServerOfList st.history.2) st.history.2.length := by
  rw [playClientFamily_eq_canonicalHistory]
  unfold grayBlockSpendMoveV2 grayChargedSpendRoundStrategyV2
  apply congrArg
  exact Prod.ext hst (grayTailServerOfList_ofFn st.history.2).symm

/-- A rejected spend exchange (the local server move appended) keeps
replay consistency. -/
lemma grayChargedSpendReplayOKV2_append {n b : Nat}
    {q L a e pass t : Nat} {sigma : FamilyStrategyScheme}
    {sm : Nat -> FamilyServerMove} {st : GrayTailStateV2 n b}
    (hst : GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st)
    {m : FamilyServerMove}
    (hm : m = grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
      st.slots (sm t)) :
    GrayChargedSpendReplayOKV2 q L a e pass sigma sm (t + 1)
      { st with
        time := st.time + 1
        history :=
          (st.history.1 ++ [grayBlockSpendMoveV2 q L a e pass sigma st],
            st.history.2 ++ [m]) } := by
  have hcurrent := grayBlockSpendMoveV2_eq_play q L a e pass sigma st
    hst.history_ok
  refine ⟨?_, ?_, ?_⟩
  · have hfirst :
        (List.ofFn fun i : Fin st.history.2.length =>
          playClientFamily st.unavailable st.slots.length
            (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
            (grayTailServerOfList (st.history.2 ++ [m])) i.val) =
          List.ofFn fun i : Fin st.history.2.length =>
            playClientFamily st.unavailable st.slots.length
              (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
              (grayTailServerOfList st.history.2) i.val := by
      apply congrArg List.ofFn
      funext i
      apply playClientFamily_congr_before
      intro j hj
      apply grayTailServerOfList_append_before
      omega
    have hlast :
        playClientFamily st.unavailable st.slots.length
            (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
            (grayTailServerOfList (st.history.2 ++ [m]))
            st.history.2.length =
          grayBlockSpendMoveV2 q L a e pass sigma st := by
      rw [hcurrent]
      apply playClientFamily_congr_before
      intro j hj
      apply grayTailServerOfList_append_before
      exact hj
    change st.history.1 ++ [grayBlockSpendMoveV2 q L a e pass sigma st] =
      List.ofFn (fun j : Fin (st.history.2 ++ [m]).length =>
        playClientFamily st.unavailable st.slots.length
          (grayChargedSpendRoundStrategyV2 q L a e pass sigma)
          (grayTailServerOfList (st.history.2 ++ [m])) j.val)
    rw [show (st.history.2 ++ [m]).length = st.history.2.length + 1 by simp]
    rw [grayTail_ofFn_succ_last_nat, hfirst, ← hst.history_ok, hlast]
  · have htime := hst.active_time
    simp only [List.length_append, List.length_singleton]
    omega
  · simp only [List.length_append, List.length_singleton]
    change st.history.2 ++ [m] =
      List.ofFn (fun j : Fin (st.history.2.length + 1) =>
        grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots
          (sm (st.roundStart + j.val)))
    have hdecomp :
        List.ofFn (fun j : Fin (st.history.2.length + 1) =>
          grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots
            (sm (st.roundStart + j.val))) =
          (List.ofFn (fun j : Fin st.history.2.length =>
            grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots
              (sm (st.roundStart + j.val)))) ++
            [grayTailLocalServerMove (grayChargedSpendDelta a L e pass) st.slots
              (sm (st.roundStart + st.history.2.length))] := by
      simpa only using
        (grayTail_ofFn_succ_last_nat st.history.2.length
          (fun u => grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
            st.slots (sm (st.roundStart + u))))
    rw [hdecomp, ← hst.servers_eq]
    congr 2
    rw [hm, hst.active_time]

/-- Every branch of the strict block step advances the clock. -/
lemma grayChargedBlockTailStepV2_time {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (m : FamilyServerMove) :
    (grayChargedBlockTailStepV2 q L a e sigma A st m).time = st.time + 1 := by
  by_cases hd : st.done = true
  · simp [grayChargedBlockTailStepV2, hd]
  · by_cases hs : st.slots.isEmpty = true
    · simp [grayChargedBlockTailStepV2, hd, hs]
    · by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots m) = true
      · simp [grayChargedBlockTailStepV2, hd, hs, hg]
      · simp [grayChargedBlockTailStepV2, hd, hs, hg]

/-- A strict block step from an active state that ends `done` is a freeze:
fresh round start and empty history. -/
lemma grayChargedBlockTailStepV2_done_fresh {n b : Nat}
    {q L a e : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {st : GrayTailStateV2 n b} {m : FamilyServerMove}
    (hactive : st.done = false)
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A st m).done = true) :
    (grayChargedBlockTailStepV2 q L a e sigma A st m).roundStart = st.time + 1 ∧
      (grayChargedBlockTailStepV2 q L a e sigma A st m).history = ([], []) := by
  by_cases hslots : st.slots.isEmpty = true
  · simp [grayChargedBlockTailStepV2, hactive, hslots] at hdone
  · have hs' : st.slots.isEmpty = false := by simpa using hslots
    by_cases hgoal : grayChargedBlockGoalAtB q L e st.frozen.length
        st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots m) = true
    · simp [grayChargedBlockTailStepV2, hactive, hs', hgoal]
    · simp [grayChargedBlockTailStepV2, hactive, hs', hgoal] at hdone

/-- **The spend replay step**: a certified state whose successor is in
`.spend pass` yields a replay-consistent successor core; when the pass is
newly entered, the successor's history is empty. -/
lemma grayChargedSpendReplayOKV2_step {n q L a e t pass : Nat}
    {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    {st : GrayChargedStateV2 n (grayTailBranch q L a e)}
    (hcert : GrayChargedCertifiedV2 q L a e sigma A sm t st)
    (hphase : (grayChargedStepV2 q L a e sigma A st (sm t)).phase = .spend pass)
    (hprev : st.phase = .spend pass ->
      GrayChargedSpendReplayOKV2 q L a e pass sigma sm t st.core) :
    GrayChargedSpendReplayOKV2 q L a e pass sigma sm (t + 1)
        (grayChargedStepV2 q L a e sigma A st (sm t)).core ∧
      (st.phase ≠ .spend pass ->
        (grayChargedStepV2 q L a e sigma A st (sm t)).core.history = ([], [])) := by
  cases hcert with
  | advantage core hcore hsource hdone =>
      have htime : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).time =
          core.time + 1 := grayChargedBlockTailStepV2_time q L a e sigma A core (sm t)
      simp only [grayChargedStepV2] at hphase ⊢
      generalize hnext :
        grayChargedBlockTailStepV2 q L a e sigma A core (sm t) = next at hphase htime ⊢
      by_cases hnd : next.done = true
      · by_cases hsv : grayChargedWaitServedB q a e next (sm t) = true
        · simp only [hnd, hsv, ↓reduceIte, grayChargedStartSpendV2] at hphase ⊢
          by_cases hs0 : (grayChargedSlotsForPassV2 q L a e 0 next.frozen).isEmpty = true
          · simp [hs0] at hphase
          · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hphase ⊢
            refine ⟨grayChargedSpendReplayOKV2_fresh rfl ?_, by simp⟩
            change next.time = t + 1
            rw [htime, hcore.time_eq]
        · simp [hnd, hsv] at hphase
      · simp [hnd] at hphase
  | wait core hcore hsource hdoneCore =>
      have htick := grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t)
        hdoneCore
      have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true := by
        rw [htick]
        exact hdoneCore
      have hphase' : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
      by_cases hsv : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
      · rw [grayChargedStepV2_advantage_exit q L a e sigma A _ (sm t) hphase' hnd hsv]
          at hphase ⊢
        unfold grayChargedStartSpendV2 at hphase ⊢
        by_cases hs0 : (grayChargedSlotsForPassV2 q L a e 0
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).frozen).isEmpty =
              true
        · simp [hs0] at hphase
        · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hphase ⊢
          refine ⟨grayChargedSpendReplayOKV2_fresh rfl ?_, by simp⟩
          change (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).time = t + 1
          rw [htick]
          simp only
          rw [hcore.time_eq]
      · have hsv' : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = false := by
          simpa using hsv
        rw [grayChargedStepV2_advantage_wait q L a e sigma A _ (sm t) hphase' hnd hsv']
          at hphase
        simp at hphase
  | spend pass' core hspend =>
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      simp only [grayChargedStepV2, hslots, Bool.false_eq_true, ↓reduceIte] at hphase ⊢
      by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass' core.slots.length
          core.unavailable (grayBlockSpendMoveV2 q L a e pass' sigma core)
          (grayTailLocalServerMove (grayChargedSpendDelta a L e pass') core.slots
            (sm t)) = true
      · simp only [hgoal, ↓reduceIte] at hphase ⊢
        by_cases h8 : pass' + 1 < 8
        · simp only [h8, ↓reduceIte] at hphase ⊢
          split at hphase
          · simp at hphase
          · rename_i hnil
            simp only [hnil, Bool.false_eq_true, ↓reduceIte] at hphase ⊢
            refine ⟨grayChargedSpendReplayOKV2_fresh rfl ?_, by simp⟩
            change core.time + 1 = t + 1
            rw [hspend.core.time_eq]
        · simp only [h8, ↓reduceIte] at hphase
          simp at hphase
      · simp only [hgoal, Bool.false_eq_true, ↓reduceIte] at hphase ⊢
        have hpass : pass' = pass := GrayChargedPhase.spend.inj (by simpa using hphase)
        subst hpass
        refine ⟨?_, fun hne => (hne rfl).elim⟩
        exact grayChargedSpendReplayOKV2_append (hprev rfl) rfl
  | done core hdone2 =>
      simp [grayChargedStepV2] at hphase

/-- **Run-level spend replay consistency**: at every time in `.spend pass`
the core is replay-consistent for the pass. -/
theorem grayChargedRunStateV2_spendReplayOK {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t pass : Nat)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass) :
    GrayChargedSpendReplayOKV2 q L a e pass sigma sm t
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core := by
  induction t with
  | zero =>
      simp [grayChargedRunStateV2, grayChargedFoldV2, grayChargedInitialStateV2,
        grayTailServerPrefix] at hphase
  | succ t ih =>
      rw [grayChargedRunStateV2_succ] at hphase ⊢
      exact (grayChargedSpendReplayOKV2_step
        (grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t) hphase ih).1

/-- A newly entered spend pass has an empty history. -/
theorem grayChargedRunStateV2_spend_fresh_of_new {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t pass : Nat)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).phase = .spend pass)
    (hprev : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase ≠ .spend pass) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).core.history = ([], []) := by
  rw [grayChargedRunStateV2_succ] at hphase ⊢
  exact (grayChargedSpendReplayOKV2_step
    (grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t) hphase
    (fun h => (hprev h).elim)).2 hprev

/-- A newly entered spend pass starts its round at the entry time. -/
theorem grayChargedRunStateV2_spend_roundStart_of_new {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t pass : Nat)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).phase = .spend pass)
    (hprev : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase ≠ .spend pass) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).core.roundStart = t + 1 := by
  have hok := grayChargedRunStateV2_spendReplayOK q L a e sigma A sm (t + 1) pass hphase
  have hfresh := grayChargedRunStateV2_spend_fresh_of_new q L a e sigma A sm t pass
    hphase hprev
  have htime := hok.active_time
  rw [hfresh] at htime
  simpa using htime

end Kolmogorov
