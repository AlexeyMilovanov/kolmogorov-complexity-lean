import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay.Part02
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailReplay

/-!
# Stability of the tail controller after it has stopped

Once the controller is terminal -- either because `done` has been set or
because there is no unresolved slot left -- `grayTailStep` only advances the
clock.  Every later state therefore agrees with the terminal one in all
fields except `time`, and the displayed family move is literally the same
move at every later time.

This is the "Leaf 3" plumbing of the Gacs-Day tail blueprint: it is
what allows all the subfamily certificates to be stated at one *fixed*
terminal time `T`, before the selected outer-root list is introduced.  The
Boolean `List.all` inside `familyRobustGrayGoalAtB` is evaluated at a single
client/server pair, so the time really has to be fixed first.
-/

namespace Kolmogorov

/-- A terminal controller state only advances its clock. -/
lemma grayTailStep_of_terminal {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (st : GrayTailState n b) (sm : FamilyServerMove)
    (hterminal : (st.done || st.slots.isEmpty) = true) :
    grayTailStep q L a e sigma A st sm = { st with time := st.time + 1 } := by
  cases hdone : st.done <;> cases hslots : st.slots.isEmpty <;>
    simp [grayTailStep, grayTailWaitingB, hdone, hslots] at hterminal ⊢

/-- **The terminal snapshot is stable.**  Every state after a terminal one is
the terminal state with a later clock. -/
theorem grayTailStateAt_add_of_terminal {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) (t : ℕ)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true)
    (k : ℕ) :
    grayTailStateAt (n := n) (b := b) q L a e sigma A sm (t + k) =
      { grayTailStateAt (n := n) (b := b) q L a e sigma A sm t with
        time := (grayTailStateAt (n := n) (b := b)
          q L a e sigma A sm t).time + k } := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← Nat.add_assoc, grayTailStateAt_succ, ih]
      rw [grayTailStep_of_terminal (hterminal := by simpa using hterminal)]
      simp [Nat.add_assoc]

/-- The terminal flag persists. -/
theorem grayTailStateAt_terminal_of_le {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true) :
    ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).slots.isEmpty) = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  rw [grayTailStateAt_add_of_terminal q L a e sigma A sm t hterminal k]
  simpa using hterminal

/-- Frozen rounds are frozen: they never change after the controller stops. -/
theorem grayTailStateAt_frozen_of_le {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).frozen =
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).frozen := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  rw [grayTailStateAt_add_of_terminal q L a e sigma A sm t hterminal k]

/-- The residual unresolved slot list is stable too. -/
theorem grayTailStateAt_slots_of_le {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).slots =
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  rw [grayTailStateAt_add_of_terminal q L a e sigma A sm t hterminal k]

/-- After a terminal time the finished flag of a tail run no longer changes. -/
theorem grayTailStateAt_done_of_le {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).done =
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  rw [grayTailStateAt_add_of_terminal q L a e sigma A sm t hterminal k]

/-- After a terminal time the unavailable allocation of a tail run no longer changes. -/
theorem grayTailStateAt_unavailable_of_le {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true) :
    (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T).unavailable =
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).unavailable := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  rw [grayTailStateAt_add_of_terminal q L a e sigma A sm t hterminal k]

/-- `grayTailOutput` only reads the fields that are stable after the stop, so
the client's displayed family move is literally constant from a terminal time
on.  This is what lets every subfamily certificate be stated at one time. -/
theorem grayTailOutput_stable_of_terminal {n b : ℕ}
    (q L a e : ℕ) (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal : ((grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).done ||
      (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t).slots.isEmpty) = true) :
    grayTailOutput q L a e sigma
        (grayTailStateAt (n := n) (b := b) q L a e sigma A sm T) =
      grayTailOutput q L a e sigma
        (grayTailStateAt (n := n) (b := b) q L a e sigma A sm t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htT
  rw [grayTailStateAt_add_of_terminal q L a e sigma A sm t hterminal k]
  set st := grayTailStateAt (n := n) (b := b) q L a e sigma A sm t with hst
  unfold grayTailOutput grayTailCurrentMove
  cases st
  rfl

/-- **The client play is stable after the controller stops.** -/
theorem playClientFamily_grayTailStrategy_stable
    {q L a e n : ℕ} (sigma : FamilyStrategyScheme) (A : Allocation)
    (sm : ℕ → FamilyServerMove) {t T : ℕ} (htT : t ≤ T)
    (hterminal :
      ((grayTailStateAt (n := n)
          (b := ladderBranching (grayTailBaseBranch q L) a e)
          q L a e sigma A sm t).done ||
        (grayTailStateAt (n := n)
          (b := ladderBranching (grayTailBaseBranch q L) a e)
          q L a e sigma A sm t).slots.isEmpty) = true) :
    playClientFamily A n (grayTailStrategy q L a e sigma) sm T =
      playClientFamily A n (grayTailStrategy q L a e sigma) sm t := by
  rw [playClientFamily_grayTailStrategy q L a e n sigma A sm T,
    playClientFamily_grayTailStrategy q L a e n sigma A sm t]
  exact grayTailOutput_stable_of_terminal q L a e sigma A sm htT hterminal

end Kolmogorov
