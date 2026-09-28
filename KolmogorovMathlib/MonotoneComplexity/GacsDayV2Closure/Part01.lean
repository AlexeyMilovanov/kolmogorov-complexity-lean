import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureCore

/-!
# Closing the V2 charged strategy

`grayChargedStrategyV2` is the outer client strategy realised by the V2 charged controller, with
`grayChargedRunMoveV2` its displayed move and `GrayChargedFinalAtV2` the last time before the
controller enters `done`. The lemmas track what a V2 step does to the state — block tail steps,
spend openings and charged steps only append to the frozen rounds
(`grayChargedBlockTailStepV2_frozen_prefix`, `grayChargedStartSpendV2_frozen`,
`grayChargedStepV2_frozen_prefix`) — and what happens at and after a final time: the displayed
move repeats (`grayChargedFinalAtV2_successor_move_eq`, `grayChargedFinalAtV2_move_stable`), and
`grayChargedV2_exit_done_time` locates the advantage time at which an exit occurs.
-/



namespace Kolmogorov

/-- The outer client strategy realised by the V2 charged controller. In the raised-service wait,
that is the advantage phase over a done core, the client repeats the terminal display: the
requests of the frozen ledger with the raised sons and no current round, the terminal core's
`slots` being the never-run next wide block, which is not displayed. -/
def grayChargedStrategyV2
    (q L a e : Nat) (sigma : FamilyStrategyScheme) : ClientFamilyStrategy :=
  fun A n history =>
    let st : GrayChargedStateV2 n (grayTailBranch q L a e) :=
      grayChargedFoldV2 q L a e sigma A history.2
    let current := match st.phase with
      | .done => []
      | .advantage => if st.core.done || st.core.slots.isEmpty then []
        else grayBlockCurrentMoveV2 q L e sigma st.core
      | .spend pass => if st.core.slots.isEmpty then []
        else grayBlockSpendMoveV2 q L a e pass sigma st.core
    grayChargedTailFamilyMove (grayChargedSourceCount a e)
      (grayChargedThreshold q e) (dyadicScale e)
      (st.core.frozen.map GrayTailRoundV2.toV1)
      (if st.core.done then [] else st.core.slots) current

/-- The outer client move displayed by the V2 charged controller at `t`. -/
abbrev grayChargedRunMoveV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : FamilyClientMove :=
  playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t

/-- The last time before the V2 controller enters `done`. -/
def GrayChargedFinalAtV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : Prop :=
  let st := grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  st.phase ≠ .done ∧
    (grayChargedStepV2 q L a e sigma A st (sm t)).phase = .done

/-- A V2 block tail step only appends to the frozen rounds. -/
lemma grayChargedBlockTailStepV2_frozen_prefix {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (m : FamilyServerMove) :
    st.frozen <+:
      (grayChargedBlockTailStepV2 q L a e sigma A st m).frozen := by
  by_cases hd : st.done = true
  · simp [grayChargedBlockTailStepV2, hd]
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · simp [grayChargedBlockTailStepV2, hd', hs]
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable
          (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots m) = true
      · simp [grayChargedBlockTailStepV2, hd', hs', hg]
      · simp [grayChargedBlockTailStepV2, hd', hs', hg]

/-- Opening a V2 spend pass leaves the frozen rounds unchanged. -/
lemma grayChargedStartSpendV2_frozen {n b : Nat}
    (q L a e : Nat) (A : Allocation) (st : GrayTailStateV2 n b)
    (m : FamilyServerMove) :
    (grayChargedStartSpendV2 q L a e A st m).core.frozen = st.frozen := by
  by_cases hslots : (grayChargedSlotsForPassV2 q L a e 0 st.frozen).isEmpty
  · simp [grayChargedStartSpendV2, hslots]
  · simp [grayChargedStartSpendV2, hslots]

/-- A V2 charged step only appends to the frozen rounds. -/
lemma grayChargedStepV2_frozen_prefix {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedStateV2 n b) (m : FamilyServerMove) :
    st.core.frozen <+:
      (grayChargedStepV2 q L a e sigma A st m).core.frozen := by
  cases hphase : st.phase with
  | done => simp [grayChargedStepV2, hphase]
  | advantage =>
      simp only [grayChargedStepV2, hphase]
      by_cases hdone :
          (grayChargedBlockTailStepV2 q L a e sigma A st.core m).done = true
      · rw [if_pos hdone]
        by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A st.core m) m = true
        · rw [if_pos hserved, grayChargedStartSpendV2_frozen]
          exact grayChargedBlockTailStepV2_frozen_prefix q L a e sigma A st.core m
        · rw [if_neg hserved]
          exact grayChargedBlockTailStepV2_frozen_prefix q L a e sigma A st.core m
      · simpa [hdone] using
          grayChargedBlockTailStepV2_frozen_prefix q L a e sigma A st.core m
  | spend pass =>
      by_cases hslots : st.core.slots.isEmpty = true
      · simp [grayChargedStepV2, hphase, hslots]
      · by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
            st.core.slots.length st.core.unavailable
            (grayBlockSpendMoveV2 q L a e pass sigma st.core)
            (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
              st.core.slots m) = true
        · simp only [grayChargedStepV2, hphase, hslots, Bool.false_eq_true,
            ↓reduceIte, hgoal]
          split
          · split <;> simp
          · simp
        · simp [grayChargedStepV2, hphase, hslots, hgoal]

/-- From the `done` phase a further V2 step stays in `done` and leaves the frozen rounds
unchanged. -/
lemma grayChargedStepV2_done_frozen {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayChargedStateV2 n b) (m : FamilyServerMove)
    (hdone : st.phase = .done) :
    (grayChargedStepV2 q L a e sigma A st m).phase = .done ∧
      (grayChargedStepV2 q L a e sigma A st m).core.frozen =
        st.core.frozen := by
  simp [grayChargedStepV2, hdone]

/-- Once the V2 controller is in the `done` phase, it stays there with the same frozen rounds. -/
lemma grayChargedRunStateV2_done_stable {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .done) :
    forall d,
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).phase = .done ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).core.frozen =
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen := by
  intro d
  induction d with
  | zero => exact ⟨hdone, rfl⟩
  | succ d ih =>
      rw [Nat.add_succ, grayChargedRunStateV2_succ]
      have hstep := grayChargedStepV2_done_frozen q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (t + d)) (sm (t + d)) ih.1
      exact ⟨hstep.1, hstep.2.trans ih.2⟩

/-- The V2 run's frozen ledger grows monotonically (prefix order). -/
lemma grayChargedRunStateV2_frozen_prefix_succ {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen <+:
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).core.frozen := by
  rw [grayChargedRunStateV2_succ]
  exact grayChargedStepV2_frozen_prefix q L a e sigma A _ (sm t)

/-- One step after a final time the V2 run is in the `done` phase. -/
lemma grayChargedFinalAtV2_successor_done
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (T + 1)).phase = .done := by
  rw [grayChargedRunStateV2_succ]
  exact hfinal.2

/-- The V2 core certificate of the run state, in any phase. -/
lemma grayChargedRunStateV2_coreCertified {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedCoreCertifiedV2 q L a e A sm t
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core := by
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hst : grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t = st at hcert
  cases hcert with
  | advantage core hcore hsource hactive => exact hcore.toCore (a := a) hsource
  | wait core hcore hsource hdone => exact hcore.toCore (a := a) hsource
  | spend pass core hspend => exact hspend.core
  | done core hdone => exact hdone.core

/-- Every round frozen by time `t` in a V2 run was closed against a server move before `t`. -/
lemma grayChargedRunStateV2_frozen_serverTime_lt {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) :
    p.serverTime < t :=
  ((grayChargedRunStateV2_coreCertified q L a e sigma A sm t).round_valid
    p hp).2.1

/-- The codewords a frozen V2 round recorded as allocated are still allocated by every later
legal server move. -/
lemma grayChargedRunStateV2_frozen_alloc_subset_late {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (t U : Nat) (htU : t <= U)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen) :
    allocationSubset p.allocated
      (grayTailLocalAllocatedList
        (grayTailLocalServerMove p.fineEnd p.slots (sm U))) := by
  have hvalid := (grayChargedRunStateV2_coreCertified
    q L a e sigma A sm t).round_valid p hp
  rw [hvalid.2.2.2.1]
  exact grayTailLocalAllocatedList_mono hsm
    (le_trans (Nat.le_of_lt hvalid.2.1) htU) p.slots

/-- After a final time `T` the V2 run is in the `done` phase at every time `U ≥ T + 1`, with the
frozen rounds it had at `T + 1`. -/
lemma grayChargedFinalAtV2_done_stable
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    forall U, T + 1 <= U ->
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm U).phase = .done ∧
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm U).core.frozen =
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (T + 1)).core.frozen := by
  intro U hU
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hU
  exact grayChargedRunStateV2_done_stable q L a e sigma A sm (T + 1)
    (grayChargedFinalAtV2_successor_done hfinal) d

/-- A V2 run with a final time `T` leaves the `advantage` phase at some time `t ≤ T`. -/
lemma grayChargedFinalAtV2_advantage_exit
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    exists t, t <= T ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .advantage ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).phase ≠ .advantage := by
  let P : Nat -> Prop := fun u =>
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm u).phase ≠ .advantage
  have hP : exists u, P u := by
    refine ⟨T + 1, ?_⟩
    simp only [P]
    rw [grayChargedFinalAtV2_successor_done hfinal]
    simp
  let d := Nat.find hP
  have hdP : P d := Nat.find_spec hP
  have hzero :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm 0).phase = .advantage := by
    simp [grayChargedRunStateV2, grayChargedFoldV2,
      grayTailServerPrefix, grayChargedInitialStateV2]
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0] at hdP
    exact hdP hzero
  let t := d - 1
  have htd : t + 1 = d := by
    dsimp [t]
    omega
  have htBefore :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .advantage := by
    by_contra ht
    have htP : P t := ht
    have hmin : d <= t := Nat.find_min' hP htP
    dsimp [t] at hmin
    omega
  have hdBound : d <= T + 1 := by
    apply Nat.find_min' hP
    simp only [P]
    rw [grayChargedFinalAtV2_successor_done hfinal]
    simp
  refine ⟨t, ?_, htBefore, ?_⟩
  · dsimp [t]
    omega
  · rw [htd]
    exact hdP

/-- At the time the V2 run leaves the `advantage` phase, the underlying block tail step reports
the tail as finished. -/
lemma grayChargedV2_advantage_exit_terminal_done
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hbefore :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .advantage)
    (hafter :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).phase ≠ .advantage) :
    (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core
      (sm t)).done = true := by
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hstate :
    grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t = st at hcert hbefore ⊢
  cases hcert with
  | advantage core hcore hsource hactive =>
      by_cases hnext :
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true
      · exact hnext
      · apply (hafter ?_).elim
        rw [grayChargedRunStateV2_succ, hstate]
        simp [grayChargedStepV2, hnext]
  | wait core hcore hsource hdone =>
      simp [grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t) hdone,
        hdone]
  | spend pass core hspend =>
      simp at hbefore
  | done core hdone =>
      simp at hbefore

/-- The advantage core of the V2 run equals the strict tail trajectory while
the phase is `.advantage`. -/
lemma grayChargedRunStateV2_core_eq_tailStateAt {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core =
      grayChargedBlockTailStateAtV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t := by
  induction t with
  | zero =>
      simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
        grayChargedInitialStateV2, grayChargedBlockTailStateAtV2,
        grayChargedBlockTailFoldV2]
  | succ t ih =>
      have hbefore : (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t).phase =
          .advantage := by
        by_contra hb
        -- once not advantage, the phase never returns to advantage
        have hcert := grayChargedCertifiedV2_stateAt (n := n)
          q L a e sigma A sm t
        generalize hstate : grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t = st at hcert hb
        rw [grayChargedRunStateV2_succ, hstate] at hphase
        cases hcert with
        | advantage core hcore hsource hactive => exact hb rfl
        | wait core hcore hsource hdone => exact hb rfl
        | spend pass core hspend =>
            by_cases hslots : core.slots.isEmpty = true
            · simp [grayChargedStepV2, hslots] at hphase
            · by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
                  core.slots.length core.unavailable
                  (grayBlockSpendMoveV2 q L a e pass sigma core)
                  (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                    core.slots (sm t)) = true
              · simp only [grayChargedStepV2, hslots, Bool.false_eq_true,
                  ↓reduceIte, hgoal] at hphase
                split at hphase
                · split at hphase <;> simp_all
                · simp_all
              · simp [grayChargedStepV2, hslots, hgoal] at hphase
        | done core hdone =>
            simp [grayChargedStepV2] at hphase
      rw [grayChargedRunStateV2_succ] at hphase ⊢
      by_cases hd : (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core (sm t)).done = true
      · by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm t).core (sm t)) (sm t) = true
        · exfalso
          rw [grayChargedStepV2_advantage_exit q L a e sigma A _ (sm t)
            hbefore hd hserved] at hphase
          unfold grayChargedStartSpendV2 at hphase
          by_cases hemp : (grayChargedSlotsForPassV2 q L a e 0
              (grayChargedBlockTailStepV2 q L a e sigma A
                (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm t).core (sm t)).frozen).isEmpty
          · simp [hemp] at hphase
          · simp [hemp] at hphase
        · have hserved' : grayChargedWaitServedB q a e
              (grayChargedBlockTailStepV2 q L a e sigma A
                (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm t).core (sm t)) (sm t) = false := by
            simpa using hserved
          rw [grayChargedStepV2_advantage_wait q L a e sigma A _ (sm t)
            hbefore hd hserved', grayChargedBlockTailStateAtV2_succ, ih hbefore]
      · have hnext : (grayChargedBlockTailStepV2 q L a e sigma A
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core (sm t)).done = false := by
          simpa using hd
        rw [grayChargedStepV2_advantage_continue q L a e sigma A _ (sm t)
          hbefore hnext, grayChargedBlockTailStateAtV2_succ, ih hbefore]

/-- The advantage round bound stays below the V2 branching. -/
lemma grayChargedAdvantageRoundCount_lt_branch (q L a e : Nat) :
    grayChargedAdvantageRoundCount q + 1 <= grayTailBranch q L a e := by
  have h1 : grayChargedAdvantageRoundCount q + 8 = grayTailRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq, grayTailRoundCount]
    have h1 : 1 <= (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : 8 <= 256 * (q + 1) ^ 2 := by nlinarith
    omega
  have h2 := grayTailRoundCount_le_baseBranch q L
  have h3 : grayTailBaseBranch q L <= grayTailBranch q L a e :=
    le_max_right _ _
  omega

/-- **The V2 terminal width at an advantage terminal step** (mult-scaled wide
form): if the active advantage core at `t` becomes done at its step, the
terminal wide block satisfies `4·|slots| ≤ n·source·mult`.  In the narrow
reading this is the fibre quarter: at most a quarter of the `n·2^{e-a}`
source fibres survive. -/
lemma grayChargedV2_terminal_width_of_step
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hbefore :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .advantage)
    (hactive : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.done = false)
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core (sm t)).done = true) :
    4 * (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core (sm t)).slots.length <=
      n * grayChargedSourceCount a e *
        (grayAdvBlockGrandsons (grayTailBranch q L a e) q L
          (grayChargedBlockTailStepV2 q L a e sigma A
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core (sm t)).frozen.length).length := by
  -- the active-phase certificate at time t
  have key : ∀ st : GrayChargedStateV2 n (grayTailBranch q L a e),
      GrayChargedCertifiedV2 q L a e sigma A sm t st ->
      st.phase = .advantage -> st.core.done = false ->
      st.core.frozen.length < grayChargedAdvantageRoundCount q := by
    intro st hcert hb ha
    cases hcert with
    | advantage core hcore hsource hact =>
        exact hcore.frozen_bound.2 hact
    | wait core hcore hsource hdone2 =>
        simp only at ha
        rw [ha] at hdone2
        exact Bool.noConfusion hdone2
    | spend pass core hspend => simp at hb
    | done core hdone2 => simp at hb
  have hbound : (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen.length <
        grayChargedAdvantageRoundCount q :=
    key _ (grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t)
      hbefore hactive
  have hr : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen.length + 1 <
      grayTailBranch q L a e := by
    have hb := grayChargedAdvantageRoundCount_lt_branch q L a e
    omega
  rcases grayChargedBlockTailStepV2_wideWidth_or_roundCount_of_done
    q L a e sigma A _ (sm t) hactive hdone hr with hw | hrc
  · exact hw
  · -- round-count exit: the terminal slots are empty
    have hcoreEq := grayChargedRunStateV2_core_eq_tailStateAt
      q L a e sigma A sm t hbefore
    rw [hcoreEq, ← grayChargedBlockTailStateAtV2_succ] at hrc ⊢
    rw [grayChargedBlockTail_slots_eq_nil_of_roundCount_stateAt_global hrc]
    simp

/-- **The origin of a wait** (v15.1 A7, the advantage done time): a run state
in the advantage phase over a done core arose from an advantage terminal step
at an earlier time `t₀` (active core whose step is done), and the core only
ticked since (same slots and frozen ledger). -/
lemma grayChargedV2_wait_origin {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true) :
    ∃ t₀, t₀ < t ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t₀).phase = .advantage ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t₀).core.done = false ∧
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t₀).core (sm t₀)).done = true ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.slots =
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t₀).core (sm t₀)).slots ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.frozen =
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t₀).core (sm t₀)).frozen := by
  induction t with
  | zero =>
      exfalso
      have h0 : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm 0).core.done = false := by
        simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
          grayChargedInitialStateV2, grayChargedBlockTailInitialStateV2]
      rw [h0] at hdone
      exact Bool.noConfusion hdone
  | succ t ih =>
      -- the phase at t is advantage (no return to advantage)
      have hbefore : (grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t).phase =
          .advantage := by
        by_contra hb
        have hcert := grayChargedCertifiedV2_stateAt (n := n)
          q L a e sigma A sm t
        generalize hstate : grayChargedRunStateV2 (n := n)
          (b := grayTailBranch q L a e) q L a e sigma A sm t = st at hcert hb
        rw [grayChargedRunStateV2_succ, hstate] at hphase
        cases hcert with
        | advantage core hcore hsource hactive => exact hb rfl
        | wait core hcore hsource hdone2 => exact hb rfl
        | spend pass core hspend =>
            by_cases hslots : core.slots.isEmpty = true
            · simp [grayChargedStepV2, hslots] at hphase
            · by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
                  core.slots.length core.unavailable
                  (grayBlockSpendMoveV2 q L a e pass sigma core)
                  (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                    core.slots (sm t)) = true
              · simp only [grayChargedStepV2, hslots, Bool.false_eq_true,
                  ↓reduceIte, hgoal] at hphase
                split at hphase
                · split at hphase <;> simp_all
                · simp_all
              · simp [grayChargedStepV2, hslots, hgoal] at hphase
        | done core hdone2 =>
            simp [grayChargedStepV2] at hphase
      rw [grayChargedRunStateV2_succ] at hphase hdone ⊢
      by_cases hd : (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core (sm t)).done = true
      · -- the step at t is a wait step (an exit would leave the phase)
        have hserved' : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm t).core (sm t)) (sm t) = false := by
          by_contra hbad
          have hserved : grayChargedWaitServedB q a e
              (grayChargedBlockTailStepV2 q L a e sigma A
                (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm t).core (sm t)) (sm t) = true := by
            simpa using hbad
          rw [grayChargedStepV2_advantage_exit q L a e sigma A _ (sm t)
            hbefore hd hserved] at hphase
          unfold grayChargedStartSpendV2 at hphase
          by_cases hemp : (grayChargedSlotsForPassV2 q L a e 0
              (grayChargedBlockTailStepV2 q L a e sigma A
                (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                  q L a e sigma A sm t).core (sm t)).frozen).isEmpty
          · simp [hemp] at hphase
          · simp [hemp] at hphase
        rw [grayChargedStepV2_advantage_wait q L a e sigma A _ (sm t)
          hbefore hd hserved'] at hdone ⊢
        by_cases hcoreDone : (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e) q L a e sigma A sm t).core.done = true
        · -- already waiting at t: reuse the origin, the step is a tick
          obtain ⟨t₀, ht₀, hph₀, hact₀, hstep₀, hslots₀, hfrozen₀⟩ :=
            ih hbefore hcoreDone
          refine ⟨t₀, by omega, hph₀, hact₀, hstep₀, ?_, ?_⟩
          · rw [grayChargedBlockTailStepV2_of_done q L a e sigma A _ (sm t)
              hcoreDone]
            exact hslots₀
          · rw [grayChargedBlockTailStepV2_of_done q L a e sigma A _ (sm t)
              hcoreDone]
            exact hfrozen₀
        · -- the terminal step happens at t
          have hact : (grayChargedRunStateV2 (n := n)
              (b := grayTailBranch q L a e) q L a e sigma A sm t).core.done =
              false := by
            simpa using hcoreDone
          exact ⟨t, Nat.lt_succ_self t, hbefore, hact, hd, rfl, rfl⟩
      · -- the step continues the active round: the core at t + 1 is not done
        exfalso
        have hnext : (grayChargedBlockTailStepV2 q L a e sigma A
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core (sm t)).done = false := by
          simpa using hd
        rw [grayChargedStepV2_advantage_continue q L a e sigma A _ (sm t)
          hbefore hnext] at hdone
        simp only at hdone
        rw [hnext] at hdone
        exact Bool.noConfusion hdone

/-- **The V2 terminal width at the advantage exit** (mult-scaled wide form),
through the raised-service wait: the exit's stepped core has the slots and
ledger of the advantage terminal. -/
lemma grayChargedV2_advantage_exit_terminal_width
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hbefore :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .advantage)
    (hafter :
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).phase ≠ .advantage) :
    4 * (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core (sm t)).slots.length <=
      n * grayChargedSourceCount a e *
        (grayAdvBlockGrandsons (grayTailBranch q L a e) q L
          (grayChargedBlockTailStepV2 q L a e sigma A
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core (sm t)).frozen.length).length := by
  have hdone := grayChargedV2_advantage_exit_terminal_done hbefore hafter
  by_cases hcoreDone : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).core.done = true
  · -- the exit leaves a wait: transport the terminal width from its origin
    obtain ⟨t₀, -, hph₀, hact₀, hstep₀, hslots₀, hfrozen₀⟩ :=
      grayChargedV2_wait_origin q L a e sigma A sm t hbefore hcoreDone
    have hw := grayChargedV2_terminal_width_of_step hph₀ hact₀ hstep₀
    rw [grayChargedBlockTailStepV2_of_done q L a e sigma A _ (sm t) hcoreDone]
    simp only
    rw [hslots₀, hfrozen₀]
    exact hw
  · have hactive : (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t).core.done = false := by
      simpa using hcoreDone
    exact grayChargedV2_terminal_width_of_step hbefore hactive hdone

/-- The V2 displayed family move at one state (the wait displays the
terminal ledger only). -/
def grayChargedDisplayedMoveV2 {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (st : GrayChargedStateV2 n b) : FamilyClientMove :=
  let current := match st.phase with
    | .done => []
    | .advantage => if st.core.done || st.core.slots.isEmpty then []
      else grayBlockCurrentMoveV2 q L e sigma st.core
    | .spend pass => if st.core.slots.isEmpty then []
      else grayBlockSpendMoveV2 q L a e pass sigma st.core
  grayChargedTailFamilyMove (grayChargedSourceCount a e)
    (grayChargedThreshold q e) (dyadicScale e)
    (st.core.frozen.map GrayTailRoundV2.toV1)
    (if st.core.done then [] else st.core.slots) current

/-- The move the V2 charged strategy plays at time `t` is the move displayed by its controller
state at time `t`. -/
lemma playClientFamily_grayChargedStrategyV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t =
      grayChargedDisplayedMoveV2 q L a e sigma
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t) := by
  dsimp [grayChargedDisplayedMoveV2]
  cases t with
  | zero =>
      rw [playClientFamily]
      rfl
  | succ t =>
      rw [playClientFamily]
      rfl

/-- A V2 controller in the `done` phase has no active slots left. -/
lemma grayChargedRunStateV2_slots_eq_nil_of_done {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove) (t : Nat)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .done) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.slots = [] := by
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hst :
    grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t = st at hcert hdone ⊢
  cases hcert with
  | advantage core hcore hsource hactive => simp_all
  | wait core hcore hsource hdoneCore => simp_all
  | spend pass core hspend => simp_all
  | done core hdoneCert => exact hdoneCert.slots_empty

/-- Once the V2 controller is in the `done` phase, the strategy keeps displaying the move it
displayed then. -/
lemma playClientFamily_grayChargedStrategyV2_done_stable
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t d : Nat)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .done) :
    playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm (t + d) =
      playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t := by
  have hstable := grayChargedRunStateV2_done_stable
    q L a e sigma A sm t hdone d
  have hslotsT := grayChargedRunStateV2_slots_eq_nil_of_done
    q L a e sigma A sm t hdone
  have hslotsU := grayChargedRunStateV2_slots_eq_nil_of_done
    q L a e sigma A sm (t + d) hstable.1
  rw [playClientFamily_grayChargedStrategyV2,
    playClientFamily_grayChargedStrategyV2]
  simp [grayChargedDisplayedMoveV2, hdone, hstable.1,
    hslotsT, hslotsU, hstable.2]

/-- Freezing one V2 round leaves the projected family display unchanged. -/
lemma grayChargedBlockTailFamilyMove_freeze {n b : Nat}
    (source : Nat) (threshold eps : Rat)
    (frozen : List (GrayTailRoundV2 n b)) (p : GrayTailRoundV2 n b) :
    grayChargedTailFamilyMove source threshold eps
        ((frozen ++ [p]).map GrayTailRoundV2.toV1) [] [] =
      grayChargedTailFamilyMove source threshold eps
        (frozen.map GrayTailRoundV2.toV1) p.slots p.move := by
  rw [List.map_append, List.map_cons, List.map_nil]
  have h := grayChargedTailFamilyMove_freeze source threshold eps
    (frozen.map GrayTailRoundV2.toV1) p.toV1
  simpa [GrayTailRoundV2.toV1] using h

/-- The V2 advantage tail's display is unchanged on the terminal step. -/
lemma grayChargedBlockTailStepV2_done_display_eq
    {n b : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (st : GrayTailStateV2 n b) (m : FamilyServerMove)
    (hactive : st.done = false)
    (hdone : (grayChargedBlockTailStepV2 q L a e sigma A st m).done = true) :
    grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        ((grayChargedBlockTailStepV2 q L a e sigma A st m).frozen.map
          GrayTailRoundV2.toV1) [] [] =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        (st.frozen.map GrayTailRoundV2.toV1) st.slots
        (if st.slots.isEmpty then []
          else grayBlockCurrentMoveV2 q L e sigma st) := by
  by_cases hslots : st.slots.isEmpty = true
  · have hnil : st.slots = [] := List.isEmpty_iff.mp hslots
    simp [grayChargedBlockTailStepV2, hactive, hnil]
  · have hslots' : st.slots.isEmpty = false := by simpa using hslots
    by_cases hgoal : grayChargedBlockGoalAtB q L e st.frozen.length
        st.slots.length st.unavailable
        (grayBlockCurrentMoveV2 q L e sigma st)
        (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
          st.slots m) = true
    · simp only [grayChargedBlockTailStepV2, hactive, hslots',
        Bool.false_eq_true, ↓reduceIte, hgoal]
      exact grayChargedBlockTailFamilyMove_freeze _ _ _ st.frozen _
    · simp [grayChargedBlockTailStepV2, hactive, hslots', hgoal] at hdone

/-- The V2 displayed move is unchanged across the final transition. -/
lemma grayChargedStepV2_done_display_eq
    {n t : Nat} (q L a e : Nat) (sigma : FamilyStrategyScheme)
    (A : Allocation) (sm : Nat -> FamilyServerMove)
    (st : GrayChargedStateV2 n (grayTailBranch q L a e))
    (hcert : GrayChargedCertifiedV2 q L a e sigma A sm t st)
    (hdone : (grayChargedStepV2 q L a e sigma A st (sm t)).phase = .done) :
    grayChargedDisplayedMoveV2 q L a e sigma
        (grayChargedStepV2 q L a e sigma A st (sm t)) =
      grayChargedDisplayedMoveV2 q L a e sigma st := by
  cases hcert with
  | done core hdoneCert =>
      simp [grayChargedDisplayedMoveV2, grayChargedStepV2]
  | advantage core hcore hsource hactive =>
      by_cases hnext :
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true
      · have htail := grayChargedBlockTailStepV2_done_display_eq
          q L a e sigma A core (sm t) hactive hnext
        have hphase : ({ phase := .advantage, core := core } :
            GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage :=
          rfl
        by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
        · rw [grayChargedStepV2_advantage_exit q L a e sigma A
            { phase := .advantage, core := core } (sm t) hphase hnext hserved]
            at hdone ⊢
          by_cases hslots :
              (grayChargedSlotsForPassV2 q L a e 0
                (grayChargedBlockTailStepV2 q L a e sigma A core
                  (sm t)).frozen).isEmpty = true
          · simpa [grayChargedStartSpendV2, hslots, grayChargedDisplayedMoveV2,
              hactive] using htail
          · simp [grayChargedStartSpendV2, hslots] at hdone
        · have hserved' : grayChargedWaitServedB q a e
              (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) =
                false := by
            simpa using hserved
          rw [grayChargedStepV2_advantage_wait q L a e sigma A
            { phase := .advantage, core := core } (sm t) hphase hnext hserved']
            at hdone
          simp at hdone
      · simp [grayChargedStepV2, hnext] at hdone
  | wait core hcore hsource hdoneCore =>
      -- a wait state only leaves through the exit; the display is the ledger
      have hnext : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done =
          true := by
        simp [grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t)
          hdoneCore, hdoneCore]
      have hphase : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage :=
        rfl
      by_cases hserved : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
      · rw [grayChargedStepV2_advantage_exit q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase hnext hserved]
          at hdone ⊢
        rw [grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t)
          hdoneCore] at hdone ⊢
        by_cases hslots :
            (grayChargedSlotsForPassV2 q L a e 0 core.frozen).isEmpty = true
        · simp [grayChargedStartSpendV2, hslots, grayChargedDisplayedMoveV2,
            hdoneCore]
        · simp [grayChargedStartSpendV2, hslots] at hdone
      · have hserved' : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) =
              false := by
          simpa using hserved
        rw [grayChargedStepV2_advantage_wait q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase hnext hserved']
          at hdone
        simp at hdone
  | spend pass core hspend =>
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      let epsRound := grayChargedSpendEps a L e pass
      let deltaRound := grayChargedSpendDelta a L e pass
      let current := grayBlockSpendMoveV2 q L a e pass sigma core
      let localSM := grayTailLocalServerMove deltaRound core.slots (sm t)
      by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass
          core.slots.length core.unavailable current localSM = true
      · let p : GrayTailRoundV2 n (grayTailBranch q L a e) :=
          { serverTime := core.time
            roundIndex := core.frozen.length
            blockAnchor := epsRound
            childEps := epsRound + graySpendSpan q
            fineEnd := deltaRound
            slots := core.slots
            move := current
            allocated := grayTailLocalAllocatedList localSM
            unavailable := core.unavailable }
        let frozen' := core.frozen ++ [p]
        have hfreeze := grayChargedBlockTailFamilyMove_freeze
          (grayChargedSourceCount a e) (grayChargedThreshold q e)
          (dyadicScale e) core.frozen p
        by_cases hpass : pass + 1 < 8
        · by_cases hnext :
              (grayChargedSlotsForPassV2 q L a e (pass + 1)
                frozen').isEmpty = true
          · simpa [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound,
              current, localSM, p, frozen', hpass, hnext,
              grayChargedDisplayedMoveV2, hspend.done_false] using hfreeze
          · simp [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound,
              current, localSM, p, frozen', hpass, hnext] at hdone
        · simpa [grayChargedStepV2, hslots, hgoal, epsRound, deltaRound,
            current, localSM, p, frozen', hpass,
            grayChargedDisplayedMoveV2, hspend.done_false] using hfreeze
      · simp [grayChargedStepV2, hslots, hgoal, deltaRound,
          current, localSM] at hdone

/-- One step after a final time the V2 run displays the move it displayed at that time. -/
lemma grayChargedFinalAtV2_successor_move_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    grayChargedRunMoveV2 q L a e n sigma A sm (T + 1) =
      grayChargedRunMoveV2 q L a e n sigma A sm T := by
  change playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm (T + 1) =
    playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm T
  rw [playClientFamily_grayChargedStrategyV2,
    playClientFamily_grayChargedStrategyV2]
  rw [grayChargedRunStateV2_succ]
  exact grayChargedStepV2_done_display_eq q L a e sigma A sm
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm T)
    (grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm T) hfinal.2

/-- After a final time `T` the V2 run displays, at every later time, the move it displayed at
`T`. -/
lemma grayChargedFinalAtV2_move_stable
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hfinal : GrayChargedFinalAtV2 q L a e n sigma A sm T) :
    forall U, T + 1 <= U ->
      grayChargedRunMoveV2 q L a e n sigma A sm U =
        grayChargedRunMoveV2 q L a e n sigma A sm T := by
  intro U hU
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hU
  calc
    grayChargedRunMoveV2 q L a e n sigma A sm (T + 1 + d) =
        grayChargedRunMoveV2 q L a e n sigma A sm (T + 1) := by
      exact playClientFamily_grayChargedStrategyV2_done_stable
        q L a e n sigma A sm (T + 1) d
          (grayChargedFinalAtV2_successor_done hfinal)
    _ = grayChargedRunMoveV2 q L a e n sigma A sm T :=
      grayChargedFinalAtV2_successor_move_eq hfinal

/-- **The advantage done time of an exit** (v15.1 A7′): the last advantage
time `t` (exit at `t + 1`) has an advantage terminal at some `t₀ ≤ t` — `t`
itself when its core is still active, the wait's origin otherwise — whose
step's slots and frozen ledger are those of the exit's stepped core. -/
lemma grayChargedV2_exit_done_time {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (hbefore : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hafter : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).phase ≠ .advantage) :
    ∃ t₀, t₀ <= t ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t₀).phase = .advantage ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t₀).core.done = false ∧
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t₀).core (sm t₀)).done = true ∧
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core (sm t)).slots =
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t₀).core (sm t₀)).slots ∧
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core (sm t)).frozen =
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t₀).core (sm t₀)).frozen := by
  by_cases hcoreDone : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).core.done = true
  · obtain ⟨t₀, ht₀, hph₀, hact₀, hstep₀, hslots₀, hfrozen₀⟩ :=
      grayChargedV2_wait_origin q L a e sigma A sm t hbefore hcoreDone
    refine ⟨t₀, le_of_lt ht₀, hph₀, hact₀, hstep₀, ?_, ?_⟩
    · rw [grayChargedBlockTailStepV2_of_done q L a e sigma A _ (sm t) hcoreDone]
      exact hslots₀
    · rw [grayChargedBlockTailStepV2_of_done q L a e sigma A _ (sm t) hcoreDone]
      exact hfrozen₀
  · have hactive : (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm t).core.done = false := by
      simpa using hcoreDone
    exact ⟨t, le_rfl, hbefore, hactive,
      grayChargedV2_advantage_exit_terminal_done hbefore hafter, rfl, rfl⟩

end Kolmogorov
