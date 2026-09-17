import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReplayStrict
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay

/-!
# History consistency of the strict V2 block controller

Stage C4 (replay/history equalities): the V2 analogue of `GrayTailHistoryOK`.
The recorded client history is exactly the canonical play of the V2 round
strategy (two-anchor block move `sigma ε_r (ε_r + graySpendSpan q)`) against
the recorded server list.  A faithful mirror of the V1 development; all the
`playClientFamily` / `grayTailServerOfList` helpers are state-generic.
-/

namespace Kolmogorov

/-- The V2 round strategy: `sigma` at the block anchor `ε_r` and child anchor
`ε_r + graySpendSpan q` (schedule-correct). -/
def grayBlockRoundStrategyV2 {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b) : ClientFamilyStrategy :=
  sigma (grayTailRoundEps q L e st.frozen.length)
    (grayTailRoundEps q L e st.frozen.length + graySpendSpan q)

/-- The client half of the stored history is exactly the replay of the V2 round strategy
`grayBlockRoundStrategyV2` against the stored server moves, for every recorded time. -/
def GrayBlockHistoryOKV2 {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b) : Prop :=
  st.history.1 =
    List.ofFn fun j : Fin st.history.2.length =>
      playClientFamily st.unavailable st.slots.length
        (grayBlockRoundStrategyV2 q L e sigma st)
        (grayTailServerOfList st.history.2) j.val

/-- The current V2 move is the canonical play of the round strategy. -/
lemma grayBlockCurrentMoveV2_eq_play {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b)
    (hst : GrayBlockHistoryOKV2 q L e sigma st) :
    grayBlockCurrentMoveV2 q L e sigma st =
      playClientFamily st.unavailable st.slots.length
        (grayBlockRoundStrategyV2 q L e sigma st)
        (grayTailServerOfList st.history.2) st.history.2.length := by
  rw [playClientFamily_eq_canonicalHistory]
  unfold grayBlockCurrentMoveV2 grayBlockRoundStrategyV2
  apply congrArg
  unfold GrayBlockHistoryOKV2 at hst
  exact Prod.ext hst (grayTailServerOfList_ofFn st.history.2).symm

/-- Appending one served round preserves V2 history consistency. -/
lemma grayBlockHistoryOKV2_append {n b : ℕ}
    (q L e : ℕ) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b)
    (hst : GrayBlockHistoryOKV2 q L e sigma st)
    (m : FamilyServerMove) (time : ℕ) :
    GrayBlockHistoryOKV2 q L e sigma
      { st with
        time := time
        history :=
          (st.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma st],
            st.history.2 ++ [m]) } := by
  have hcurrent := grayBlockCurrentMoveV2_eq_play q L e sigma st hst
  have hfirst :
      (List.ofFn fun i : Fin st.history.2.length =>
        playClientFamily st.unavailable st.slots.length
          (grayBlockRoundStrategyV2 q L e sigma st)
          (grayTailServerOfList (st.history.2 ++ [m])) i.val) =
        List.ofFn fun i : Fin st.history.2.length =>
          playClientFamily st.unavailable st.slots.length
            (grayBlockRoundStrategyV2 q L e sigma st)
            (grayTailServerOfList st.history.2) i.val := by
    apply congrArg List.ofFn
    funext i
    apply playClientFamily_congr_before
    intro j hj
    apply grayTailServerOfList_append_before
    omega
  have hlast :
      playClientFamily st.unavailable st.slots.length
          (grayBlockRoundStrategyV2 q L e sigma st)
          (grayTailServerOfList (st.history.2 ++ [m]))
          st.history.2.length =
        grayBlockCurrentMoveV2 q L e sigma st := by
    rw [hcurrent]
    apply playClientFamily_congr_before
    intro j hj
    apply grayTailServerOfList_append_before
    exact hj
  unfold GrayBlockHistoryOKV2 at hst ⊢
  change st.history.1 ++ [grayBlockCurrentMoveV2 q L e sigma st] =
    List.ofFn (fun j : Fin (st.history.2 ++ [m]).length =>
      playClientFamily st.unavailable st.slots.length
        (grayBlockRoundStrategyV2 q L e sigma st)
        (grayTailServerOfList (st.history.2 ++ [m])) j.val)
  rw [show (st.history.2 ++ [m]).length = st.history.2.length + 1 by simp]
  rw [grayTail_ofFn_succ_last_nat, hfirst, ← hst, hlast]

/-- History consistency is preserved by the V2 controller step. -/
lemma grayChargedBlockHistoryOKV2_step {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailStateV2 n b) (sm : FamilyServerMove)
    (hst : GrayBlockHistoryOKV2 q L e sigma st) :
    GrayBlockHistoryOKV2 q L e sigma
      (grayChargedBlockTailStepV2 q L a e sigma A st sm) := by
  by_cases hd : st.done = true
  · unfold grayChargedBlockTailStepV2
    dsimp only
    split_ifs
    exact hst
  · have hd' : st.done = false := by simpa using hd
    by_cases hs : st.slots.isEmpty = true
    · unfold grayChargedBlockTailStepV2
      dsimp only
      split_ifs
      exact hst
    · have hs' : st.slots.isEmpty = false := by simpa using hs
      unfold grayChargedBlockTailStepV2
      dsimp only
      split_ifs with hg
      · exact rfl
      · exact grayBlockHistoryOKV2_append q L e sigma st hst _ _

/-- The V2 initial state is history-consistent (empty history). -/
lemma grayBlockHistoryOKV2_initial {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation) :
    GrayBlockHistoryOKV2 (n := n) (b := b) q L e sigma
      (grayChargedBlockTailInitialStateV2 n b a e q L A) := by
  simp [GrayBlockHistoryOKV2, grayChargedBlockTailInitialStateV2]

/-- History consistency holds at every point of the V2 trajectory. -/
lemma grayChargedBlockHistoryOKV2_stateAt {n b : Nat}
    (q L a e : Nat) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : Nat -> FamilyServerMove) (t : Nat) :
    GrayBlockHistoryOKV2 q L e sigma
      (grayChargedBlockTailStateAtV2 (n := n) (b := b) q L a e sigma A sm t) := by
  induction t with
  | zero => exact grayBlockHistoryOKV2_initial q L a e sigma A
  | succ t ih =>
      rw [grayChargedBlockTailStateAtV2_succ]
      exact grayChargedBlockHistoryOKV2_step q L a e sigma A _ (sm t) ih

end Kolmogorov
