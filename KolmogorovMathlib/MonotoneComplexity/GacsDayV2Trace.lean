import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReplayStrict
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay

/-!
# Server-trace consistency of the strict V2 block controller

Stage C4 (replay equalities): the V2 analogue of `GrayTailTrace` — the
recorded server list is the canonical local-server play, frozen rounds are
chronologically before the current round window, and the history is empty at
a terminal state.  Faithful mirror of the V1 development on the V2 records.
-/

namespace Kolmogorov

/-- Server-trace consistency of a V2 state at time `t`: the clock is `t`; while the round is active
the round start plus the stored history length is `t`; the stored server moves are the outer
moves from the round start on, localised to the current slots at the round's delta depth; every
frozen round was frozen before the round start; and a terminal state stores the empty history. -/
structure GrayTailTraceV2 {n b : ℕ}
    (q L e : ℕ) (sm : ℕ → FamilyServerMove)
    (t : ℕ) (st : GrayTailStateV2 n b) : Prop where
  time_eq : st.time = t
  active_time :
    (st.done || st.slots.isEmpty) ≠ true →
      st.roundStart + st.history.2.length = t
  servers_eq :
    st.history.2 =
      List.ofFn fun j : Fin st.history.2.length =>
        grayTailLocalServerMove
          (grayTailRoundDelta q L e st.frozen.length) st.slots
          (sm (st.roundStart + j.val))
  frozen_before :
    ∀ p ∈ st.frozen, p.serverTime < st.roundStart
  terminal_empty :
    (st.done || st.slots.isEmpty) = true →
      st.history = ([], [])

/-- The initial V2 state is trace-consistent. -/
lemma grayTailTraceV2_initial {n b : Nat}
    (q L a e : Nat) (A : Allocation) (sm : Nat -> FamilyServerMove) :
    GrayTailTraceV2 (n := n) (b := b) q L e sm 0
      (grayChargedBlockTailInitialStateV2 n b a e q L A) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [grayChargedBlockTailInitialStateV2]

/-- Trace consistency is preserved by the V2 controller step. -/
lemma grayChargedBlockTailTraceV2_step {n b q L a e t : Nat}
    {A : Allocation} {sm : Nat -> FamilyServerMove}
    {st : GrayTailStateV2 n b} (sigma : FamilyStrategyScheme)
    (hst : GrayTailTraceV2 q L e sm t st) :
    GrayTailTraceV2 q L e sm (t + 1)
      (grayChargedBlockTailStepV2 q L a e sigma A st (sm t)) := by
  by_cases hd : st.done = true
  · have hterminal : (st.done || st.slots.isEmpty) = true := by simp [hd]
    simp only [grayChargedBlockTailStepV2, hd, ↓reduceIte]
    refine ⟨by simp [hst.time_eq], ?_, hst.servers_eq,
      hst.frozen_before, ?_⟩
    · intro hactive; simp at hactive
    · intro _; exact hst.terminal_empty hterminal
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · have hterminal : (st.done || st.slots.isEmpty) = true := by simp [hs]
      simp only [grayChargedBlockTailStepV2, hd', hs, Bool.false_eq_true,
        ↓reduceIte]
      refine ⟨by simp [hst.time_eq], ?_, hst.servers_eq,
        hst.frozen_before, ?_⟩
      · intro hactive; exact (hactive (by simp [hs])).elim
      · intro _; exact hst.terminal_empty hterminal
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      have hactive : (st.done || st.slots.isEmpty) ≠ true := by
        simp [hd', hs']
      have hbefore : ∀ p, p ∈ st.frozen -> p.serverTime < st.time + 1 := by
        intro p hp
        have htime := hst.active_time hactive
        have hpStart := hst.frozen_before p hp
        rw [hst.time_eq]
        omega
      by_cases hg : grayChargedBlockGoalAtB q L e st.frozen.length
          st.slots.length st.unavailable (grayBlockCurrentMoveV2 q L e sigma st)
          (grayTailLocalServerMove (grayTailRoundDelta q L e st.frozen.length)
            st.slots (sm t)) = true
      · simp only [grayChargedBlockTailStepV2, hd', hs', hg,
          Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simp [hst.time_eq], ?_, by simp, ?_, ?_⟩
        · intro _; simp [hst.time_eq]
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hbefore p hp
          · rw [List.mem_singleton] at hp
            subst hp
            simp
        · intro _; rfl
      · simp only [grayChargedBlockTailStepV2, hd', hs', hg,
          Bool.false_eq_true, ↓reduceIte]
        refine ⟨by simp [hst.time_eq], ?_, ?_, hst.frozen_before, ?_⟩
        · intro _
          have htime := hst.active_time hactive
          simp only [List.length_append, List.length_singleton]
          omega
        · simp only [List.length_append, List.length_singleton]
          change
            st.history.2 ++
                [grayTailLocalServerMove
                  (grayTailRoundDelta q L e st.frozen.length)
                  st.slots (sm t)] =
              List.ofFn
                (fun j : Fin (st.history.2.length + 1) =>
                  grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots (sm (st.roundStart + j.val)))
          have hdecomp :
              List.ofFn
                  (fun j : Fin (st.history.2.length + 1) =>
                    grayTailLocalServerMove
                      (grayTailRoundDelta q L e st.frozen.length)
                      st.slots (sm (st.roundStart + j.val))) =
                (List.ofFn
                  (fun j : Fin st.history.2.length =>
                    grayTailLocalServerMove
                      (grayTailRoundDelta q L e st.frozen.length)
                      st.slots (sm (st.roundStart + j.val)))) ++
                  [grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots
                    (sm (st.roundStart + st.history.2.length))] := by
            simpa only using
              (grayTail_ofFn_succ_last_nat st.history.2.length
                (fun u =>
                  grayTailLocalServerMove
                    (grayTailRoundDelta q L e st.frozen.length)
                    st.slots (sm (st.roundStart + u))))
          rw [hdecomp, ← hst.servers_eq]
          congr 2
          rw [hst.active_time hactive]
        · intro hterminal; simp [hs'] at hterminal

/-- Trace consistency holds at every point of the V2 trajectory. -/
lemma grayChargedBlockTailTraceV2_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayTailTraceV2 q L e sm t
      (grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayTailTraceV2_initial q L a e A sm
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayChargedBlockTailTraceV2_step sigma ih

end Kolmogorov
