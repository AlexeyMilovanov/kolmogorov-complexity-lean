import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendSnapshotAfter
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailAnchor
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SpendKillEarlier
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ServerResolvedKill

/-!
# v15: leaf 1, the raised class — the served reserve at the wait horizon

Proof document v15.1, A3/A4(a)/A7′.  A threshold-raised source son of the
final ledger is served at scale `2^-e` during the raised-service wait, at
some time `u ≤ advantageExitTime` (the wait exit).  Every spend pass takes its
harvest at a snapshot at or after the wait exit
(`grayChargedReplayV2_spend_round_snapshot_exit`, from the run-level datum
`grayChargedRunStateV2_spendSnapAfter`), so the served bin `v` is present in
the pass's harvest: the designated cells of every frozen spend round avoid the
served reserve cylinder anchored by `v` (`GacsDayV2SpendKillEarlier`).
-/

namespace Kolmogorov

/-- A spend step never returns to the advantage phase (local copy of the
finalization lemma). -/
lemma grayChargedStepV2_no_return_to_advantage'
    {n b q L a e : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {st : GrayChargedStateV2 n b} {pass : Nat}
    {sm : FamilyServerMove}
    (hst : st.phase = .spend pass)
    (h : (grayChargedStepV2 q L a e sigma A st sm).phase = .advantage) :
    False := by
  simp only [grayChargedStepV2, hst] at h
  split at h
  · exact GrayChargedPhase.noConfusion h
  · split at h
    · split at h
      · split at h
        · exact GrayChargedPhase.noConfusion h
        · exact GrayChargedPhase.noConfusion h
      · exact GrayChargedPhase.noConfusion h
    · exact GrayChargedPhase.noConfusion h

/-- Once the phase is not `advantage`, it never is again. -/
lemma grayChargedRunStateV2_not_advantage_stable {n : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (v : Nat)
    (hv : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm v).phase ≠ .advantage) :
    ∀ d, (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (v + d)).phase ≠ .advantage := by
  intro d
  induction d with
  | zero => simpa using hv
  | succ d ih =>
      rw [show v + (d + 1) = v + d + 1 by omega, grayChargedRunStateV2_succ]
      have hcert := grayChargedCertifiedV2_stateAt (n := n) q L a e sigma A sm (v + d)
      generalize hst : grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm (v + d) = st at hcert ih
      cases hcert with
      | advantage core hcore hsource hactive => exact absurd rfl ih
      | wait core hcore hsource hdone => exact absurd rfl ih
      | spend pass core hspend =>
          exact fun h => grayChargedStepV2_no_return_to_advantage' rfl h
      | done core hdone2 =>
          intro h
          simp [grayChargedStepV2] at h

/-- A time whose successor is out of the advantage phase is at or after the
last advantage time (the wait exit). -/
lemma grayChargedReplayV2_exit_le_of_phase_ne
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) {u : Nat}
    (hu : (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm (u + 1)).phase ≠ .advantage) :
    replay.advantageExitTime <= u := by
  by_contra hlt
  push Not at hlt
  have hstable := grayChargedRunStateV2_not_advantage_stable q L a e sigma A sm (u + 1) hu
    (replay.advantageExitTime - (u + 1))
  rw [show u + 1 + (replay.advantageExitTime - (u + 1)) = replay.advantageExitTime by
    omega] at hstable
  exact hstable replay.advantage_before

/-- **The snapshot of a spend round of the final ledger is taken at or after
the wait exit** (v15.1 A7′). -/
theorem grayChargedReplayV2_spend_round_snapshot_exit
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    {p : GrayTailRoundV2 n (grayTailBranch q L a e)}
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor) :
    ∃ t₁, replay.advantageExitTime <= t₁ ∧
      p.unavailable = A ++ grayHarvest p.fineEnd p.slots n (sm t₁) := by
  obtain ⟨u, -, hphase, hunav⟩ :=
    (grayChargedRunStateV2_spendSnapAfter q L a e sigma A sm U).1 p hp hcoarse
  exact ⟨u, grayChargedReplayV2_exit_le_of_phase_ne replay hphase, hunav⟩

/-- **Leaf 1, raised class, anchoring-free**: the designated cells of every
frozen spend round of the final ledger avoid the reserve cylinder anchored by
the bin serving a source son's raised request at a time `u ≤ advantageExitTime`
(the wait exit). -/
theorem grayChargedReplayV2_spendRound_cell_avoids_served_reserve
    {q L a e n T U u : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hae : a <= e) (hroom : a + 3 + L <= e)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm U).core.frozen)
    (hcoarse : ¬ grayCallDepth q e <= p.blockAnchor)
    {i c : Nat} (hi : i < n) (hc : c < grayTailBranch q L a e)
    (hsrc : c < grayChargedSourceCount a e)
    (hu : u <= replay.advantageExitTime)
    (hserve : Serves (getFamilyAlloc (sm u) i [c]) (dyadicScale e)) :
    ∃ R, IsAnchoredTailFamilyReserve e (grayTailBranch q L a e) A n i (sm u) [c] R ∧
      ∀ w ∈ grayChargedRoundLocalChargeV2 hae p hp, ¬ (w.2 <+: R ∨ R <+: w.2) := by
  have hx : ∀ d ∈ [c], d < grayTailBranch q L a e := by
    intro d hd
    rw [List.mem_singleton] at hd
    rw [hd]
    exact hc
  obtain ⟨R, hR⟩ := exists_anchoredTailFamilyReserve_of_serves hsm hi hx hserve
  refine ⟨R, hR, fun w hw => ?_⟩
  obtain ⟨t₁, ht, hsnap⟩ :=
    grayChargedReplayV2_spend_round_snapshot_exit replay hp hcoarse
  exact grayChargedSpendRoundV2_cell_incomparable_of_earlier_reserve hsm hae hroom p hp
    hcoarse hsnap (le_trans hu ht) hi hc hsrc hR.toIsTailFamilyReserve w hw

end Kolmogorov
