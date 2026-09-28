import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedGoalOfReplay

/-!
# D5: the V2 finalization assembly and the pinned remaining device

The V2 closure at the pinned gap is assembled here from two finalization
facts (each the V2 analogue of a proved V1 device, and both proved from the
pinned child rung in `GacsDayV2AdvantageCore` / `GacsDayV2SpendCore`):

* `GrayChargedAdvantageLeavesV2` — the block advantage phase is eventually left
  (V1: `grayChargedTail_eventually_terminal_or_positive`, transferred through
  the son-base multiplicity bound of `GacsDayV2Progress`);
* `GrayChargedSpendProgressV2` — every spend pass is eventually left
  (V1: `grayCharged_spend_progress`, from the recursive rung).

Everything else — the spend-pass loop, the first-done predecessor, the replay,
the geometry, and the charged goal at the call's anchor `a` — is proved; the
anchored server-resolved datum of v14 (`hSRanch`) is retired (v15.1).
-/

namespace Kolmogorov

/-- At every time `t` at which the V2 charged run is in the spend pass `pass`, either the run makes
a positive request forever (`GrayChargedPositiveV2`), or there is a time `u ≥ t` after which the
phase is no longer `.spend pass`. -/
def GrayChargedSpendProgressV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  forall t pass,
    (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).phase = .spend pass ->
      GrayChargedPositiveV2 q L a e n sigma A sm ∨
        exists u, t <= u ∧
          (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
            q L a e sigma A sm (u + 1)).phase ≠ .spend pass

/-- Either the V2 charged run makes a positive request forever (`GrayChargedPositiveV2`), or at some
time its phase is no longer the advantage phase. -/
def GrayChargedAdvantageLeavesV2
    (q L a e n : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) : Prop :=
  GrayChargedPositiveV2 q L a e n sigma A sm ∨
    exists u, (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm u).phase ≠ .advantage

/-- Past the last pass, a V2 spend step either stays or finishes. -/
lemma grayChargedStepV2_spend_phase_of_ge
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayChargedStateV2 n b} {pass : Nat}
    {sm : FamilyServerMove}
    (hst : st.phase = .spend pass) (hpass : 8 <= pass) :
    (grayChargedStepV2 q L a e sigma A st sm).phase = .spend pass ∨
      (grayChargedStepV2 q L a e sigma A st sm).phase = .done := by
  simp only [grayChargedStepV2, hst]
  have hlt : ¬ (pass + 1 < 8) := by omega
  split
  · exact Or.inr rfl
  · split
    · right
      simp
    · exact Or.inl rfl

/-- A V2 spend step that changes pass advances it. -/
lemma grayChargedStepV2_spend_advances
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayChargedStateV2 n b} {pass pass' : Nat}
    {sm : FamilyServerMove}
    (hst : st.phase = .spend pass)
    (h : (grayChargedStepV2 q L a e sigma A st sm).phase = .spend pass')
    (hne : pass' ≠ pass) :
    pass < pass' := by
  simp only [grayChargedStepV2, hst] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · have := GrayChargedPhase.spend.inj h
          omega
      · exact absurd h (by simp)
    · have := GrayChargedPhase.spend.inj h
      exact absurd this.symm hne

/-- The V2 spend-pass loop: with progress, eight passes reach `done` (or the
client wins). -/
lemma grayChargedV2_spend_pass_loop
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hprogress : GrayChargedSpendProgressV2 q L a e n sigma A sm)
    (fuel pass t : Nat)
    (hfuel : 8 - pass <= fuel)
    (hst : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm t).phase = .spend pass) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      exists d, (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm d).phase = .done := by
  induction fuel generalizing pass t with
  | zero =>
      have hpass4 : 8 <= pass := by omega
      rcases hprogress t pass hst with hpos | ⟨u, htu, hu⟩
      · exact Or.inl hpos
      · have hex : exists w, t < w ∧
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm w).phase ≠ .spend pass :=
          ⟨u + 1, by omega, hu⟩
        let w := Nat.find hex
        have hw_spec := Nat.find_spec hex
        have hw_min : forall j, t < j -> j < Nat.find hex ->
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm j).phase = .spend pass := by
          intro j ht hj
          have h := Nat.find_min hex hj
          tauto
        have hpred_lt : w - 1 < w := by omega
        have hprev : (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (w - 1)).phase = .spend pass := by
          by_cases htw : t = w - 1
          · rw [← htw]
            exact hst
          · have htlt : t < w - 1 := by omega
            exact hw_min (w - 1) htlt hpred_lt
        have hstep : grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e) q L a e sigma A sm w =
          grayChargedStepV2 q L a e sigma A
            (grayChargedRunStateV2 q L a e sigma A sm (w - 1)) (sm (w - 1)) := by
          rw [← grayChargedRunStateV2_succ]
          congr 1
          omega
        rcases grayChargedStepV2_spend_phase_of_ge (q := q) (L := L) (a := a)
            (e := e) (sigma := sigma) (A := A) hprev hpass4 with hsame | hdone
        · exfalso
          apply hw_spec.2
          rw [hstep, hsame]
        · exact Or.inr ⟨w, by rw [hstep, hdone]⟩
  | succ fuel ih =>
      rcases hprogress t pass hst with hpos | ⟨u, htu, hu⟩
      · exact Or.inl hpos
      · have hex : exists w, t < w ∧
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm w).phase ≠ .spend pass :=
          ⟨u + 1, by omega, hu⟩
        let w := Nat.find hex
        have hw_spec := Nat.find_spec hex
        have hw_min : forall j, t < j -> j < Nat.find hex ->
            (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
              q L a e sigma A sm j).phase = .spend pass := by
          intro j ht hj
          have h := Nat.find_min hex hj
          tauto
        have hpred_lt : w - 1 < w := by omega
        have hprev : (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e)
            q L a e sigma A sm (w - 1)).phase = .spend pass := by
          by_cases htw : t = w - 1
          · rw [← htw]
            exact hst
          · have htlt : t < w - 1 := by omega
            exact hw_min (w - 1) htlt hpred_lt
        have hstep : grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e) q L a e sigma A sm w =
          grayChargedStepV2 q L a e sigma A
            (grayChargedRunStateV2 q L a e sigma A sm (w - 1)) (sm (w - 1)) := by
          rw [← grayChargedRunStateV2_succ]
          congr 1
          omega
        -- the phase at `w` is not `spend pass`; it is either a later pass or done
        cases hw : (grayChargedRunStateV2 (n := n)
            (b := grayTailBranch q L a e) q L a e sigma A sm w).phase with
        | advantage =>
            exfalso
            rw [hstep] at hw
            exact grayChargedStepV2_no_return_to_advantage' hprev hw
        | spend pass' =>
            by_cases hpp : pass' = pass
            · exfalso
              apply hw_spec.2
              rw [hw, hpp]
            · have hlt : pass < pass' :=
                grayChargedStepV2_spend_advances hprev (by rw [← hstep]; exact hw)
                  hpp
              exact ih pass' w (by omega) hw
        | done =>
            exact Or.inr ⟨w, hw⟩

/-- From any `done` time, the first `done` time has a final predecessor. -/
lemma grayChargedV2_first_done_has_final_predecessor
    {q L a e n d : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (sm : Nat -> FamilyServerMove)
    (hd : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm d).phase = .done) :
    exists T, GrayChargedFinalAtV2 q L a e n sigma A sm T := by
  have hex : exists t, (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm t).phase = .done :=
    ⟨d, hd⟩
  let D := Nat.find hex
  have hD : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm D).phase = .done := Nat.find_spec hex
  have hDmin : forall j, j < D -> (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e) q L a e sigma A sm j).phase ≠ .done :=
    fun j hj => Nat.find_min hex hj
  have hDpos : 0 < D := by
    by_contra h0
    have h0' : D = 0 := by omega
    have hD0 : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm 0).phase = .done := by
      rw [← h0']
      exact hD
    simp [grayChargedRunStateV2, grayChargedFoldV2, grayChargedInitialStateV2,
      grayTailServerPrefix] at hD0
  refine ⟨D - 1, ?_⟩
  have hpred : D - 1 < D := by omega
  have hT : D - 1 + 1 = D := by omega
  dsimp only [GrayChargedFinalAtV2]
  refine ⟨hDmin (D - 1) hpred, ?_⟩
  rw [← grayChargedRunStateV2_succ, hT]
  exact hD

/-- **V2 finalization from the two controller obligations**: the run finishes
(some final time), unless the client wins. -/
theorem grayChargedV2_finalizes_or_positive
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hadv : GrayChargedAdvantageLeavesV2 q L a e n sigma A sm)
    (hprogress : GrayChargedSpendProgressV2 q L a e n sigma A sm) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      exists T, GrayChargedFinalAtV2 q L a e n sigma A sm T := by
  rcases hadv with hpos | ⟨u, hu⟩
  · exact Or.inl hpos
  · cases hphase : (grayChargedRunStateV2 (n := n)
        (b := grayTailBranch q L a e) q L a e sigma A sm u).phase with
    | advantage => exact absurd hphase hu
    | spend pass =>
        rcases grayChargedV2_spend_pass_loop hprogress 8 pass u (by omega)
            hphase with hpositive | ⟨d, hdone⟩
        · exact Or.inl hpositive
        · exact Or.inr (grayChargedV2_first_done_has_final_predecessor sm hdone)
    | done =>
        exact Or.inr (grayChargedV2_first_done_has_final_predecessor sm hphase)

/-- **The pinned V2 remaining device**: for every legal server, either the
client wins the positive game, or the executable charged gray goal at the
call's anchor `a` holds at some late time — from the two finalization facts. -/
theorem grayChargedV2_remaining_devices_pinned
    {q L a e n : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    (hpin : e = a + 8 * L + 3) (hae : a <= e)
    (sm : Nat -> FamilyServerMove)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hadv : GrayChargedAdvantageLeavesV2 q L a e n sigma A sm)
    (hprogress : GrayChargedSpendProgressV2 q L a e n sigma A sm) :
    GrayChargedPositiveV2 q L a e n sigma A sm ∨
      exists U, familyChargedGrayGoalAtB 4 (halfAmplification (q + 1))
        (dyadicScale a) ((3 / 4 : Rat) * dyadicScale a) a
        (e + grayTailNewLoss q L) n A
        (grayChargedRunMoveV2 q L a e n sigma A sm U) (sm U) = true := by
  by_cases hpos : GrayChargedPositiveV2 q L a e n sigma A sm
  · exact Or.inl hpos
  · rcases grayChargedV2_finalizes_or_positive hadv hprogress with h | ⟨T, hT⟩
    · exact Or.inl h
    · right
      obtain ⟨U, -, hgoal⟩ := grayChargedV2_chargedGoal_of_replay hsm hpin hae
        hpos (grayChargedFinalReplayV2OfFinal hsm hT)
      exact ⟨U, hgoal⟩

end Kolmogorov
