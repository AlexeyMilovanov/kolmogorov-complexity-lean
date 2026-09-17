import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Finalization
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2WaitCore

/-!
# O3 reduced: the block advantage phase exits, from the per-round step

`GrayChargedAdvantageLeavesV2` (the advantage phase is eventually left, unless
the client wins) follows by a budget induction from the rung-dependent
**per-round step** `GrayChargedAdvantageStepV2`: from any ACTIVE advantage
time, the client wins, or some later time either leaves the advantage phase
or carries strictly more frozen rounds.  The budget is the certified core's
`frozen_bound` (`frozen.length < grayChargedAdvantageRoundCount q` while the
core is active).  The **raised-service wait** (v15.1 A3) is the advantage
phase over a done core; it exits by the common service horizon of the
repeated terminal display (`grayChargedV2_wait_exits`): unless the client
wins the positive game, every SUV-raised son is served at some time, and the
first such time leaves the advantage phase.
-/

namespace Kolmogorov

/-- At every time `t` at which the V2 charged run is in the advantage phase with an active core,
either the run makes a positive request forever (`GrayChargedPositiveV2`), or there is a later
time `u > t` at which the phase is no longer the advantage phase or a further round has been
frozen. -/
def GrayChargedAdvantageStepV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  forall t,
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage ->
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = false ->
      GrayChargedPositiveV2 q L a e n sigma A sm ∨
        exists u, t < u ∧
          ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm u).phase ≠ .advantage ∨
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm t).core.frozen.length <
              (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
                q L a e sigma A sm u).core.frozen.length)

/-- While the advantage core is active, the frozen list is below the round
budget (the certified core's `frozen_bound`). -/
lemma grayChargedRunStateV2_frozen_lt_of_advantage
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hactive : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = false) :
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen.length <
      grayChargedAdvantageRoundCount q := by
  have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm t
  generalize hstate : grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e) q L a e sigma A sm t = st at hcert hphase hactive ⊢
  cases hcert with
  | advantage core hcore hsource hact => exact hcore.frozen_bound.2 hact
  | wait core hcore hsource hd =>
      simp only at hactive
      rw [hactive] at hd
      exact Bool.noConfusion hd
  | spend pass core hspend => simp at hphase
  | done core hdone2 => simp at hphase

/-! ### The raised-service wait: display, stability, exit -/

/-- The wait displays the terminal ledger: no current round. -/
lemma grayChargedRunMoveV2_eq_of_wait
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true) :
    grayChargedRunMoveV2 q L a e n sigma A sm t =
      grayChargedTailFamilyMove (grayChargedSourceCount a e)
        (grayChargedThreshold q e) (dyadicScale e)
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1) [] [] := by
  rw [show grayChargedRunMoveV2 q L a e n sigma A sm t =
      playClientFamily A n (grayChargedStrategyV2 q L a e sigma) sm t from rfl,
    playClientFamily_grayChargedStrategyV2]
  simp [grayChargedDisplayedMoveV2, hphase, hdone]

/-- In the wait, every SUV-raised source son of the frozen ledger displays one
coarse unit `dyadicScale e`. -/
lemma grayChargedV2_wait_raised_display_eq
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true)
    {z : Fin n × Fin (grayTailBranch q L a e)}
    (hz : z ∈ grayChargedRaisedSources (grayChargedSourceCount a e)
      (grayChargedThreshold q e)
      (frozenV1OfV2 (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core)) :
    getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm t) z.1.val [z.2.val] =
      dyadicScale e := by
  classical
  have hmem := Finset.mem_filter.mp hz
  have hsrc : z.2.val < grayChargedSourceCount a e := hmem.2.1
  have hraise : grayChargedThreshold q e <
      grayTailSonBase (grayTailFrozenEntries
        ((grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen.map GrayTailRoundV2.toV1)) z.1 z.2 := by
    have h := hmem.2.2
    simpa [frozenV1OfV2, grayTailFrozenSonBase] using h
  rw [grayChargedRunMoveV2_eq_of_wait hphase hdone]
  rw [getFamilyReq_grayChargedTailFamilyMove_son _ _ _ _ _ _ z.1 z.2]
  simp only [grayTailEntries, grayTailSlotEntries, List.ofFn_zero, List.append_nil]
  simp only [grayChargedSonRequest, hsrc, if_pos, grayTailSonRequest]
  rw [if_pos hraise]

/-- One wait step that keeps the advantage phase is a tick: the raised sons
were not all served, and the core's frozen ledger and `done` flag persist. -/
lemma grayChargedV2_wait_step
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true)
    (hnext : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (t + 1)).phase = .advantage) :
    grayChargedRaisedServedB e (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (frozenV1OfV2 (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core) (sm t) = false ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).core.frozen =
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + 1)).core.done = true := by
  have htick := grayChargedBlockTailStepV2_of_done q L a e sigma A
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core (sm t) hdone
  have hnd : (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core (sm t)).done = true := by
    rw [htick]
    exact hdone
  -- the served test of the stepped (ticked) core is the test of the core
  have htest : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core (sm t)) (sm t) =
      grayChargedRaisedServedB e (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (frozenV1OfV2 (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core) (sm t) := by
    rw [htick]
    simp [grayChargedWaitServedB, frozenV1OfV2]
  by_cases hserved : grayChargedWaitServedB q a e
      (grayChargedBlockTailStepV2 q L a e sigma A
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core (sm t)) (sm t) = true
  · exfalso
    rw [grayChargedRunStateV2_succ,
      grayChargedStepV2_advantage_exit q L a e sigma A _ (sm t) hphase hnd hserved]
      at hnext
    unfold grayChargedStartSpendV2 at hnext
    by_cases hemp : (grayChargedSlotsForPassV2 q L a e 0
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core (sm t)).frozen).isEmpty
    · simp [hemp] at hnext
    · simp [hemp] at hnext
  · have hserved' : grayChargedWaitServedB q a e
        (grayChargedBlockTailStepV2 q L a e sigma A
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core (sm t)) (sm t) = false := by
      simpa using hserved
    refine ⟨by rw [← htest]; exact hserved', ?_, ?_⟩
    · rw [grayChargedRunStateV2_succ,
        grayChargedStepV2_advantage_wait q L a e sigma A _ (sm t) hphase hnd hserved']
      simp only
      rw [htick]
    · rw [grayChargedRunStateV2_succ,
        grayChargedStepV2_advantage_wait q L a e sigma A _ (sm t) hphase hnd hserved']
      simp only
      rw [htick]
      exact hdone

/-- While the phase stays `advantage` from a wait state on, the run keeps the
terminal ledger and the raised sons are never all served. -/
lemma grayChargedV2_wait_stays
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true)
    (hall : forall u, t <= u ->
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm u).phase = .advantage) :
    forall d,
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).core.frozen =
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.frozen ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (t + d)).core.done = true ∧
      grayChargedRaisedServedB e (grayChargedSourceCount a e) (grayChargedThreshold q e)
        (frozenV1OfV2 (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core) (sm (t + d)) = false := by
  intro d
  induction d with
  | zero =>
      have hstep := grayChargedV2_wait_step hphase hdone (hall (t + 1) (by omega))
      exact ⟨rfl, hdone, hstep.1⟩
  | succ d ih =>
      obtain ⟨hfr, hdn, -⟩ := ih
      have hstep := grayChargedV2_wait_step (hall (t + d) (by omega)) hdn
        (by rw [show t + d + 1 = t + (d + 1) by omega]; exact hall (t + (d + 1)) (by omega))
      refine ⟨?_, ?_, ?_⟩
      · rw [show t + (d + 1) = t + d + 1 by omega, hstep.2.1, hfr]
      · rw [show t + (d + 1) = t + d + 1 by omega]
        exact hstep.2.2
      · -- the served test at t + d + 1 is false by the step from t + d + 1
        have hstep' := grayChargedV2_wait_step (hall (t + (d + 1)) (by omega))
          (by rw [show t + (d + 1) = t + d + 1 by omega]; exact hstep.2.2)
          (hall (t + (d + 1) + 1) (by omega))
        have hfr' : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (t + (d + 1))).core.frozen =
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm t).core.frozen := by
          rw [show t + (d + 1) = t + d + 1 by omega, hstep.2.1, hfr]
        have h1 := hstep'.1
        simp only [frozenV1OfV2] at h1 ⊢
        rw [hfr'] at h1
        exact h1

/-- **The wait exits** (v15.1 A3, run level): from an advantage state over a
done core, either the client wins the positive game, or the advantage phase
is left at some later time — because the repeated terminal display keeps
every raised son's request at `dyadicScale e`, all of them are served at a
common horizon unless the client wins, and the first such time exits. -/
theorem grayChargedV2_wait_exits
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hphase : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .advantage)
    (hdone : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.done = true) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      exists u, t < u ∧
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm u).phase ≠ .advantage := by
  classical
  by_cases hpos : GrayChargedPositiveV2 q L a e n sigma A sm
  · exact Or.inl hpos
  by_cases hex : exists u, t < u ∧
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm u).phase ≠ .advantage
  · exact Or.inr hex
  exfalso
  push Not at hex
  have hall : forall u, t <= u ->
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm u).phase = .advantage := by
    intro u hu
    rcases Nat.eq_or_lt_of_le hu with h | h
    · rw [← h]; exact hphase
    · exact hex u h
  -- the common service horizon of the raised sons displayed at time t
  let zs := (grayChargedRaisedSources (grayChargedSourceCount a e)
    (grayChargedThreshold q e)
    (frozenV1OfV2 (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core)).toList
  have hpos' : ∀ z ∈ zs, 0 < getFamilyReq
      (grayChargedRunMoveV2 q L a e n sigma A sm t) z.1.val [z.2.val] := by
    intro z hz
    rw [grayChargedV2_wait_raised_display_eq hphase hdone (Finset.mem_toList.mp hz)]
    exact dyadicScale_pos e
  obtain ⟨u0, hu0⟩ := grayChargedV2_all_served_of_not_positive (T := t) hsm hpos zs hpos'
  -- served at the later time max u0 t, contradicting the wait
  have hserved : grayChargedRaisedServedB e (grayChargedSourceCount a e)
      (grayChargedThreshold q e)
      (frozenV1OfV2 (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).core) (sm (max u0 t)) = true := by
    rw [grayChargedRaisedServedB_eq_true_iff]
    intro z hz
    have h := hu0 z (Finset.mem_toList.mpr hz)
    rw [grayChargedV2_wait_raised_display_eq hphase hdone hz] at h
    exact serves_mono_time (hsm.1 z.1.val z.1.isLt) (le_max_left u0 t) h
  have hstays := (grayChargedV2_wait_stays hphase hdone hall (max u0 t - t)).2.2
  rw [show t + (max u0 t - t) = max u0 t by omega] at hstays
  rw [hstays] at hserved
  exact Bool.noConfusion hserved

/-- **O3 from the per-round step**: the advantage phase is eventually left
(or the client wins), by induction on the remaining round budget; a done
core (the wait) exits by the service horizon. -/
theorem grayChargedV2_advantageLeaves_of_step
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hstep : GrayChargedAdvantageStepV2 q L a e n sigma A sm) :
    GrayChargedAdvantageLeavesV2 q L a e n sigma A sm := by
  classical
  by_cases hex : exists u,
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm u).phase ≠ .advantage
  · exact Or.inr hex
  · push Not at hex
    -- a done core exits by the wait, contradicting `hex`
    have hactiveAll : forall t,
        (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done = false ∨
        GrayChargedPositiveV2 q L a e n sigma A sm := by
      intro t
      by_cases hd : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).core.done = true
      · rcases grayChargedV2_wait_exits hsm (hex t) hd with hpos | ⟨u, -, hu⟩
        · exact Or.inr hpos
        · exact absurd (hex u) hu
      · left
        simpa using hd
    have key : forall fuel t,
        grayChargedAdvantageRoundCount q <=
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm t).core.frozen.length + fuel ->
        GrayChargedPositiveV2 q L a e n sigma A sm := by
      intro fuel
      induction fuel with
      | zero =>
          intro t ht
          rcases hactiveAll t with hact | hpos
          · have hlt := grayChargedRunStateV2_frozen_lt_of_advantage (hex t) hact
            omega
          · exact hpos
      | succ fuel ih =>
          intro t ht
          rcases hactiveAll t with hact | hpos
          · rcases hstep t (hex t) hact with hpos | ⟨u, _htu, hu⟩
            · exact hpos
            · rcases hu with hne | hlt
              · exact absurd (hex u) hne
              · exact ih u (by omega)
          · exact hpos
    exact Or.inl (key (grayChargedAdvantageRoundCount q) 0 (by omega))

end Kolmogorov
