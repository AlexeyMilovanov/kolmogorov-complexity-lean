import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Closure

/-!
# v15 step 2: spend-round snapshots lie after the advantage phase

Proof document v15.1, A7′ (audit R7, Q4): the raised class of the source
ledger is served DURING the raised-service wait, so the kill of spend cells
against a served reserve needs every spend pass's harvest snapshot to be at
or after the wait exit — the last advantage time.  This module proves the
run-level invariant behind it: every frozen spend round (block anchor below
the call depth) records a harvest snapshot `u` with `phase (u + 1) ≠
.advantage`, and so does the current spend state.  Pass 0 is created by the
exit step at the wait exit (`u` = that time); later passes are created by
spend freezes at their own time; ticks preserve the datum.
-/

namespace Kolmogorov

/-- The frozen half of the snapshot-after-advantage datum: every frozen spend round `p` of the
run at time `t` records the harvest of its own slots at a server time `u` strictly before `p`
was frozen, at which the run had already left the advantage phase. -/
def GrayChargedFrozenSnapAfterV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : Prop :=
  ∀ p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen,
    ¬ grayCallDepth q e <= p.blockAnchor ->
      ∃ u, u < p.serverTime ∧
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm (u + 1)).phase ≠ .advantage ∧
        p.unavailable = A ++ grayHarvest p.fineEnd p.slots n (sm u)

/-- The active half of the snapshot-after-advantage datum: if the run is in a spend pass at
time `t`, its unavailable list is the allocation `A` extended by the harvest of its current
slots at some earlier server time `u` at which the run had already left the advantage
phase. -/
def GrayChargedSpendPhaseSnapAfterV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : Prop :=
  ∀ pass, (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass ->
    ∃ u, u < t ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (u + 1)).phase ≠ .advantage ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core.unavailable =
        A ++ grayHarvest (grayChargedSpendDelta a L e pass)
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.slots n (sm u)

/-- The snapshot-after-advantage datum of the run at time `t`. -/
def GrayChargedSpendSnapAfterV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) : Prop :=
  GrayChargedFrozenSnapAfterV2 q L a e n sigma A sm t ∧
    GrayChargedSpendPhaseSnapAfterV2 q L a e n sigma A sm t

/-- An accepted advantage round is not a spend round. -/
lemma grayChargedV2_advantage_round_not_coarse {q L e r : Nat} :
    ¬ ¬ grayCallDepth q e <= grayTailRoundEps q L e r := by
  intro h
  exact h (grayTailRoundEps_lower q L e r)

/-- The frozen ledger of the strict block step: every member is an old member
or the accepted advantage round (which is not a spend round). -/
lemma grayChargedBlockTailStepV2_frozen_mem_spend {n : Nat}
    {q L a e : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (core : GrayTailStateV2 n (grayTailBranch q L a e)) (m : FamilyServerMove)
    (hactive : core.done = false)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedBlockTailStepV2 q L a e sigma A core m).frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor) :
    p ∈ core.frozen := by
  by_cases hs : core.slots.isEmpty = true
  · simpa [grayChargedBlockTailStepV2, hactive, hs] using hp
  · have hs' : core.slots.isEmpty = false := by simpa using hs
    by_cases hg : grayChargedBlockGoalAtB q L e core.frozen.length
        core.slots.length core.unavailable
        (grayBlockCurrentMoveV2 q L e sigma core)
        (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
          core.slots m) = true
    · rw [grayChargedBlockTailStepV2_accept_frozen_eq q L a e sigma A core m hactive hs' hg]
        at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hp
      · exfalso
        have hpe : p.blockAnchor = grayTailRoundEps q L e core.frozen.length := by
          rw [List.mem_singleton.mp hp]
        rw [hpe] at hcoarse
        exact hcoarse (grayTailRoundEps_lower q L e core.frozen.length)
    · simpa [grayChargedBlockTailStepV2, hactive, hs', hg] using hp

/-- Preservation of frozen spend snapshots across a step. -/
private lemma grayChargedRunStateV2_spendSnapAfter_frozen_succ {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (ih : GrayChargedSpendSnapAfterV2 q L a e n sigma A sm t)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor) :
    ∃ u, u < p.serverTime ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (u + 1)).phase ≠ .advantage ∧
      p.unavailable = A ++ grayHarvest p.fineEnd p.slots n (sm u) := by
  obtain ⟨ihF, ihS⟩ := ih
  unfold GrayChargedFrozenSnapAfterV2 at ihF
  unfold GrayChargedSpendPhaseSnapAfterV2 at ihS
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  rw [grayChargedRunStateV2_succ] at hp
  revert hp
  generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcert ihF ihS
  intro hp
  cases hcert with
  | advantage core hcore hsource hactive =>
      have hphase' : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
      by_cases hdone : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true
      · by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
        · rw [grayChargedStepV2_advantage_exit q L a e sigma A
            { phase := .advantage, core := core } (sm t) hphase' hdone hserved,
            grayChargedStartSpendV2_frozen] at hp
          exact ihF p (grayChargedBlockTailStepV2_frozen_mem_spend core (sm t) hactive
            hp hcoarse) hcoarse
        · have hserved' : grayChargedWaitServedB q a e
              (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = false := by
            simpa using hserved
          rw [grayChargedStepV2_advantage_wait q L a e sigma A
            { phase := .advantage, core := core } (sm t) hphase' hdone hserved'] at hp
          exact ihF p (grayChargedBlockTailStepV2_frozen_mem_spend core (sm t) hactive
            hp hcoarse) hcoarse
      · have hnext : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done =
            false := by simpa using hdone
        rw [grayChargedStepV2_advantage_continue q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase' hnext] at hp
        exact ihF p (grayChargedBlockTailStepV2_frozen_mem_spend core (sm t) hactive
          hp hcoarse) hcoarse
  | wait core hcore hsource hdoneCore =>
      have htick := grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t)
        hdoneCore
      have hphase' : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
      have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true := by
        rw [htick]
        exact hdoneCore
      by_cases hserved : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
      · rw [grayChargedStepV2_advantage_exit q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase' hnd hserved,
          grayChargedStartSpendV2_frozen, htick] at hp
        exact ihF p hp hcoarse
      · have hserved' : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = false := by
          simpa using hserved
        rw [grayChargedStepV2_advantage_wait q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase' hnd hserved'] at hp
        simp only at hp
        rw [htick] at hp
        exact ihF p hp hcoarse
  | done core hdone2 =>
      simp only [grayChargedStepV2] at hp
      exact ihF p hp hcoarse
  | spend pass core hspend =>
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      simp only [grayChargedStepV2, hslots, Bool.false_eq_true, ↓reduceIte] at hp
      by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass core.slots.length
          core.unavailable (grayBlockSpendMoveV2 q L a e pass sigma core)
          (grayTailLocalServerMove (grayChargedSpendDelta a L e pass) core.slots
            (sm t)) = true
      · simp only [hgoal, ↓reduceIte] at hp
        have hpmem : p ∈ core.frozen ++
            [{ serverTime := core.time
               roundIndex := core.frozen.length
               blockAnchor := grayChargedSpendEps a L e pass
               childEps := grayChargedSpendEps a L e pass + graySpendSpan q
               fineEnd := grayChargedSpendDelta a L e pass
               slots := core.slots
               move := grayBlockSpendMoveV2 q L a e pass sigma core
               allocated := grayTailLocalAllocatedList
                 (grayTailLocalServerMove (grayChargedSpendDelta a L e pass)
                   core.slots (sm t))
               unavailable := core.unavailable }] := by
          split at hp
          · split at hp
            · exact hp
            · exact hp
          · exact hp
        rcases List.mem_append.mp hpmem with hpold | hpnew
        · exact ihF p hpold hcoarse
        · obtain ⟨u, hu, hphaseU, hunav⟩ := ihS pass rfl
          have hpeq := List.mem_singleton.mp hpnew
          refine ⟨u, ?_, hphaseU, ?_⟩
          · rw [hpeq]
            simp only
            rw [hspend.core.time_eq]
            exact hu
          · rw [hpeq]
            simp only
            exact hunav
      · simp only [hgoal, Bool.false_eq_true, ↓reduceIte] at hp
        exact ihF p hp hcoarse

/-- Preservation of active spend phase snapshots across a step. -/
private lemma grayChargedRunStateV2_spendSnapAfter_spend_succ {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat)
    (ihS : GrayChargedSpendPhaseSnapAfterV2 q L a e n sigma A sm t) :
    GrayChargedSpendPhaseSnapAfterV2 q L a e n sigma A sm (t + 1) := by
  intro pass hpass
  unfold GrayChargedSpendPhaseSnapAfterV2 at ihS
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  rw [grayChargedRunStateV2_succ] at hpass ⊢
  generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t = st at hcert ihS hpass ⊢
  cases hcert with
  | advantage core hcore hsource hactive =>
      have hphase' : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
      by_cases hdone : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true
      · by_cases hserved : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
        · rw [grayChargedStepV2_advantage_exit q L a e sigma A
            { phase := .advantage, core := core } (sm t) hphase' hdone hserved] at hpass ⊢
          unfold grayChargedStartSpendV2 at hpass ⊢
          by_cases hemp : (grayChargedSlotsForPassV2 q L a e 0
              (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).frozen).isEmpty
          · simp [hemp] at hpass
          · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hpass ⊢
            have h0 : 0 = pass := GrayChargedPhase.spend.inj hpass
            subst h0
            refine ⟨t, Nat.lt_succ_self t, ?_, rfl⟩
            rw [grayChargedRunStateV2_succ, hst,
              grayChargedStepV2_advantage_exit q L a e sigma A
                { phase := .advantage, core := core } (sm t) hphase' hdone hserved]
            unfold grayChargedStartSpendV2
            simp [hemp]
        · have hserved' : grayChargedWaitServedB q a e
              (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = false := by
            simpa using hserved
          rw [grayChargedStepV2_advantage_wait q L a e sigma A
            { phase := .advantage, core := core } (sm t) hphase' hdone hserved'] at hpass
          simp at hpass
      · have hnext : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done =
            false := by simpa using hdone
        rw [grayChargedStepV2_advantage_continue q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase' hnext] at hpass
        simp at hpass
  | wait core hcore hsource hdoneCore =>
      have htick := grayChargedBlockTailStepV2_of_done q L a e sigma A core (sm t)
        hdoneCore
      have hphase' : ({ phase := .advantage, core := core } :
          GrayChargedStateV2 n (grayTailBranch q L a e)).phase = .advantage := rfl
      have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).done = true := by
        rw [htick]
        exact hdoneCore
      by_cases hserved : grayChargedWaitServedB q a e
          (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = true
      · rw [grayChargedStepV2_advantage_exit q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase' hnd hserved] at hpass ⊢
        unfold grayChargedStartSpendV2 at hpass ⊢
        by_cases hemp : (grayChargedSlotsForPassV2 q L a e 0
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)).frozen).isEmpty
        · simp [hemp] at hpass
        · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hpass ⊢
          have h0 : 0 = pass := GrayChargedPhase.spend.inj hpass
          subst h0
          refine ⟨t, Nat.lt_succ_self t, ?_, rfl⟩
          rw [grayChargedRunStateV2_succ, hst,
            grayChargedStepV2_advantage_exit q L a e sigma A
              { phase := .advantage, core := core } (sm t) hphase' hnd hserved]
          unfold grayChargedStartSpendV2
          simp [hemp]
      · have hserved' : grayChargedWaitServedB q a e
            (grayChargedBlockTailStepV2 q L a e sigma A core (sm t)) (sm t) = false := by
          simpa using hserved
        rw [grayChargedStepV2_advantage_wait q L a e sigma A
          { phase := .advantage, core := core } (sm t) hphase' hnd hserved'] at hpass
        simp at hpass
  | done core hdone2 =>
      simp [grayChargedStepV2] at hpass
  | spend pass' core hspend =>
      have hslots : core.slots.isEmpty = false := hspend.slots_nonempty
      simp only [grayChargedStepV2, hslots, Bool.false_eq_true, ↓reduceIte] at hpass ⊢
      by_cases hgoal : grayChargedBlockSpendGoalAtB q L a e pass' core.slots.length
          core.unavailable (grayBlockSpendMoveV2 q L a e pass' sigma core)
          (grayTailLocalServerMove (grayChargedSpendDelta a L e pass') core.slots
            (sm t)) = true
      · simp only [hgoal, ↓reduceIte] at hpass ⊢
        split at hpass
        · split at hpass
          · simp at hpass
          · rename_i h8 hnil
            simp only [h8, hnil, Bool.false_eq_true, ↓reduceIte] at hpass ⊢
            have hpassEq : pass' + 1 = pass := GrayChargedPhase.spend.inj hpass
            subst hpassEq
            refine ⟨t, Nat.lt_succ_self t, ?_, rfl⟩
            rw [grayChargedRunStateV2_succ, hst]
            simp [grayChargedStepV2, hslots, hgoal, h8, hnil]
        · simp at hpass
      · simp only [hgoal, Bool.false_eq_true, ↓reduceIte] at hpass ⊢
        have hpassEq : pass' = pass := GrayChargedPhase.spend.inj hpass
        subst hpassEq
        obtain ⟨u, hu, hphaseU, hunav⟩ := ihS pass' rfl
        exact ⟨u, by omega, hphaseU, hunav⟩

/-- **The datum holds along the run.** -/
theorem grayChargedRunStateV2_spendSnapAfter {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayChargedSpendSnapAfterV2 q L a e n sigma A sm t := by
  induction t with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro p hp
        simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
          grayChargedInitialStateV2, grayChargedBlockTailInitialStateV2] at hp
      · intro pass hpass
        simp [grayChargedRunStateV2, grayChargedFoldV2, grayTailServerPrefix,
          grayChargedInitialStateV2] at hpass
  | succ t ih =>
      exact ⟨grayChargedRunStateV2_spendSnapAfter_frozen_succ q L a e sigma A sm t ih,
        grayChargedRunStateV2_spendSnapAfter_spend_succ q L a e sigma A sm t ih.2⟩

end Kolmogorov
