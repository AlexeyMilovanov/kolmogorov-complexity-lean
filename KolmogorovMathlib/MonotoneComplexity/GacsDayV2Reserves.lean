import KolmogorovMathlib.MonotoneComplexity.GacsDayV2MixedChase
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ResolutionExact
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport

/-!
# The V2 reserve ledger (Stage D2): resolved classes at the advantage exit

The two disjoint resolved classes (threshold-raised and server-resolved) of
the V2 run, computed on the projected frozen ledger of the saved advantage
terminal; the exact count identity against the narrow fibre list; and the
three-quarters estimate — the V2 wide terminal width divided by the common
grandson multiplicity.
-/

namespace Kolmogorov

/-- The V2 raised classes at the saved advantage exit. -/
noncomputable def grayChargedReplayV2RaisedSources
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    Finset (Fin n × Fin (grayTailBranch q L a e)) :=
  grayChargedRaisedSources (grayChargedSourceCount a e)
    (grayChargedThreshold q e)
    (frozenV1OfV2 replay.advantageTerminal)

/-- The set of source coordinates that the server has already resolved at the terminal state of a
final charged V2 replay. -/
noncomputable def grayChargedReplayV2ServerResolvedSources
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    Finset (Fin n × Fin (grayTailBranch q L a e)) :=
  grayChargedServerResolvedSources e (grayChargedSourceCount a e)
    (grayChargedThreshold q e) A
    (frozenV1OfV2 replay.advantageTerminal)
    (sm replay.advantageDoneTime)

/-- The accept facts of the exit step: the terminal slots are the wide block
over the extended frozen list. -/
lemma grayChargedReplayV2_terminal_accept
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    replay.advantageTerminal.slots =
      grayBlockNextSlots q L e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (dyadicScale e - dyadicScale e / (6 * halfAmplification q)) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime) := by
  have hdone : (grayChargedBlockTailStepV2 q L a e sigma A
      (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
        q L a e sigma A sm replay.advantageDoneTime).core
      (sm replay.advantageDoneTime)).done = true :=
    replay.advantageDone_step
  -- the terminal state is active with nonempty slots and a fired goal
  have hactive : (grayChargedRunStateV2 (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm replay.advantageDoneTime).core.done = false :=
    replay.advantageDone_active
  set core := (grayChargedRunStateV2 (n := n)
    (b := grayTailBranch q L a e)
    q L a e sigma A sm replay.advantageDoneTime).core with hcoreDef
  have hs : core.slots.isEmpty = false := by
    by_contra hbad
    have hemp : core.slots.isEmpty = true := by
      cases h : core.slots.isEmpty <;> simp_all
    have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core
        (sm replay.advantageDoneTime)).done = false := by
      simp [grayChargedBlockTailStepV2, hactive, hemp]
    rw [hnd] at hdone
    exact Bool.noConfusion hdone
  have hg : grayChargedBlockGoalAtB q L e core.frozen.length
      core.slots.length core.unavailable
      (grayBlockCurrentMoveV2 q L e sigma core)
      (grayTailLocalServerMove (grayTailRoundDelta q L e core.frozen.length)
        core.slots (sm replay.advantageDoneTime)) = true := by
    by_contra hbad
    have hnd : (grayChargedBlockTailStepV2 q L a e sigma A core
        (sm replay.advantageDoneTime)).done = false := by
      simp [grayChargedBlockTailStepV2, hactive, hs, hbad]
    rw [hnd] at hdone
    exact Bool.noConfusion hdone
  have hslots := grayChargedBlockTailStepV2_accept_slots
    q L a e sigma A core (sm replay.advantageDoneTime) hactive hs hg
  rw [replay.advantageTerminal_slots_eq, hslots]
  simp only [frozenV1OfV2]
  rw [replay.advantageTerminal_frozen_eq]
  try rfl

/-- **The V2 resolved-source count identity at the exit**: resolved classes
plus surviving narrow fibres partition the source population. -/
theorem grayChargedReplayV2_resolvedSourceCount_eq
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    (grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card +
      (grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime)).length =
      n * grayChargedSourceCount a e := by
  apply grayCharged_resolved_card_add_nextSlots_length
  · -- the terminal round index is below the branching
    have hbound := (grayChargedBlockTailCertifiedV2_stateAt (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (replay.advantageDoneTime + 1)).frozen_bound.1
    have hterm : replay.advantageTerminal.frozen =
        (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (replay.advantageDoneTime + 1)).frozen := by
      rw [replay.advantageTerminal_frozen_eq,
        grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm
          replay.advantageDoneTime replay.advantageDone_before,
        ← grayChargedBlockTailStateAtV2_succ]
    rw [hterm]
    have := grayChargedAdvantageRoundCount_lt_branch q L a e
    omega
  · exact grayChargedSourceCount_le_grayTailBranch q L a e

/-- **The V2 three-quarters estimate**: at least three quarters of the
sources are resolved at the exit (the wide terminal width divided by the
common grandson multiplicity). -/
theorem grayChargedReplayV2_resolved_three_quarters
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T) :
    3 * (n * grayChargedSourceCount a e) <=
      4 * (grayChargedReplayV2RaisedSources replay ∪
        grayChargedReplayV2ServerResolvedSources replay).card := by
  have heq := grayChargedReplayV2_resolvedSourceCount_eq replay
  -- the wide terminal width, and its narrow quotient
  have hw := replay.terminal_width
  have haccept := grayChargedReplayV2_terminal_accept replay
  -- terminal round bound: frozen.length ≤ advCount
  have hbound : replay.advantageTerminal.frozen.length <=
      grayChargedAdvantageRoundCount q := by
    have hb := (grayChargedBlockTailCertifiedV2_stateAt (n := n)
      (b := grayTailBranch q L a e)
      q L a e sigma A sm (replay.advantageDoneTime + 1)).frozen_bound.1
    have hterm : replay.advantageTerminal.frozen =
        (grayChargedBlockTailStateAtV2 (n := n)
          (b := grayTailBranch q L a e)
          q L a e sigma A sm (replay.advantageDoneTime + 1)).frozen := by
      rw [replay.advantageTerminal_frozen_eq,
        grayChargedRunStateV2_core_eq_tailStateAt q L a e sigma A sm
          replay.advantageDoneTime replay.advantageDone_before,
        ← grayChargedBlockTailStateAtV2_succ]
    rw [hterm]
    exact hb
  have hrb : replay.advantageTerminal.frozen.length <
      grayTailBranch q L a e := by
    have := grayChargedAdvantageRoundCount_lt_branch q L a e
    omega
  have hwide : replay.advantageTerminal.slots.length =
      (grayTailNextSlots e (grayChargedSourceCount a e)
        replay.advantageTerminal.frozen.length
        (grayChargedThreshold q e) A
        (frozenV1OfV2 replay.advantageTerminal)
        (sm replay.advantageDoneTime)).length *
      (grayAdvBlockGrandsons (grayTailBranch q L a e) q L
        replay.advantageTerminal.frozen.length).length := by
    rw [haccept]
    exact grayBlockNextSlots_length q L e (grayChargedSourceCount a e)
      replay.advantageTerminal.frozen.length
      (grayChargedThreshold q e) A
      (frozenV1OfV2 replay.advantageTerminal)
      (sm replay.advantageDoneTime) hrb
  have hGlen : (grayAdvBlockGrandsons (grayTailBranch q L a e) q L
      replay.advantageTerminal.frozen.length).length =
      grayAdvBlockMult q L replay.advantageTerminal.frozen.length :=
    grayAdvBlockGrandsons_length
      (grayAdvBlock_fit_of_le_advCount (L := L) (a := a) (e := e) hbound)
  have hGpos : 0 < grayAdvBlockMult q L
      replay.advantageTerminal.frozen.length :=
    grayAdvBlockMult_pos q L _
  -- divide the wide width by the multiplicity
  have hnarrow : 4 * (grayTailNextSlots e (grayChargedSourceCount a e)
      replay.advantageTerminal.frozen.length
      (grayChargedThreshold q e) A
      (frozenV1OfV2 replay.advantageTerminal)
      (sm replay.advantageDoneTime)).length <=
      n * grayChargedSourceCount a e := by
    rw [hwide, hGlen] at hw
    set N := (grayTailNextSlots e (grayChargedSourceCount a e)
      replay.advantageTerminal.frozen.length
      (grayChargedThreshold q e) A
      (frozenV1OfV2 replay.advantageTerminal)
      (sm replay.advantageDoneTime)).length
    set G := grayAdvBlockMult q L replay.advantageTerminal.frozen.length
    have h4 : 4 * N * G <= n * grayChargedSourceCount a e * G := by
      calc 4 * N * G = 4 * (N * G) := by ring
        _ <= n * grayChargedSourceCount a e * G := hw
    exact Nat.le_of_mul_le_mul_right
      (by calc 4 * N * G <= n * grayChargedSourceCount a e * G := h4) hGpos
  omega

end Kolmogorov
