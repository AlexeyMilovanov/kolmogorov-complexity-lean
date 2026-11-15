/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Verification

/-!
# Lemma 4.4: the global measure accounting

The proof of Lemma 4.4 in the paper splits our spending into "useful", "wasted" and "lost" measure,
and charges the lost measure to the opponent.  Here each requirement divides its history into
consecutive *windows*, recorded as ghost data (`Epoch`): no decision of the construction reads them.

* `charged I e`: the opponent's strings on the board of the requirement, first compressed in the
  window.
* `ours_cost_le_epochs`: all our spending is recorded in the windows.
* `epoch_spent_le`: in a window, on each board, we spend at most twice the charged measure, plus
  `2 ^ (-c)` if the window ended in a reset or is still open (`spend_invariant`).  This covers the
  paper's two cases where we can spend more than the opponent: `G(δ, δ)` against `G(δ/2, δ/2)`, and
  knight and bishop.
* `charged_pairwise_disjoint`: an opponent's string is charged at most once, including across
  requirements.  This is the no-double-counting claim of the paper, and it is what the hit rule
  (`pendingHit`) is for (`charged_disjoint_of_lt`).
* `final_c_nodup`: each value of `c` is left open at most once, and `c ≥ 7`.

`lemma_4_4` follows: the charged measure is at most `1/32`, so the lost part is at most `1/16`; the
uncharged part is at most `∑_{c ≥ 7} 2 ^ (-c) = 1/64`; in all `5/64 ≤ 3/32`.  Nothing here is open.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable (I : Input)

/-- The opponent's strings charged to a window. -/
def charged (e : Epoch) : Finset Str :=
  e.board.filter fun τ => I.opp e.stop τ && !(I.opp e.start τ)

/-- The open window of a requirement, closed at its last visit. -/
def openEpoch (s i : ℕ) : List Epoch :=
  match (rsAt I s i).c with
  | some c =>
    [⟨i, c, (rsAt I s i).epochStart, (rsAt I s i).lastVisit, boardOf (rsAt I s i).tables,
      (rsAt I s i).epochSpent, true⟩]
  | none => []

/-- All windows up to stage `s`: only the requirements below `s` have been visited. -/
def allEpochs (s : ℕ) : List Epoch :=
  (List.range s).flatMap fun i => openEpoch I s i ++ (rsAt I s i).closed

/-! ### All of our spending is recorded -/

/-- What a requirement has recorded as spent on board `j`. -/
def spentPot (rs : ReqState) (j : Fin 3) : ℚ :=
  rs.epochSpent j + (rs.closed.map fun e => e.spent j).sum

/-- Closing the current window does not change what is recorded as spent: its spending moves to the
closed windows. -/
theorem closeEpoch_pot (rs : ReqState) (i c stop t : ℕ) (f : Bool) (j : Fin 3) :
    spentPot (rs.closeEpoch i c stop t f) j = spentPot rs j := by
  simp [spentPot, ReqState.closeEpoch]

/-- Case 1 does not change what is recorded as spent. -/
theorem caseOne_pot (st : ConState) (i t : ℕ) (j : Fin 3) :
    spentPot (caseOne st i t).1 j = spentPot (st.req i) j := by
  unfold caseOne
  dsimp only
  split
  · simp [spentPot, ReqState.closeEpoch]
  · rfl

/-- The first part of Case 2 does not change what is recorded as spent, whether it ends the visit or
returns an agreed value. -/
theorem examineTop_pot {st : ConState} {i t c : ℕ} {rs : ReqState} {j : Fin 3} :
    (∀ r, examineTop I st i t c rs = .inl r → spentPot r.1 j = spentPot rs j) ∧
      ∀ r, examineTop I st i t c rs = .inr r → spentPot r.1 j = spentPot rs j := by
  constructor
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
        exact closeEpoch_pot _ _ _ _ _ _ _
      · split at hr
        · cases hr
          rfl
        · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
          rfl
        · cases hr
          rfl
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · cases hr
          exact closeEpoch_pot _ _ _ _ _ _ _
    · split at hr
      · cases hr
        exact closeEpoch_pot _ _ _ _ _ _ _
      · split at hr
        · cases hr
        · cases hr

/-- Case 2 does not change what is recorded as spent: it makes no move. -/
theorem caseTwo_pot {st : ConState} {i t c : ℕ} {rs : ReqState} {j : Fin 3} :
    spentPot (caseTwo I st i t c rs).1 j = spentPot rs j := by
  have hex := examineTop_pot I (st := st) (i := i) (t := t) (c := c) (rs := rs) (j := j)
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    exact hex.1 r hr
  · rename_i rs₁ σ hr
    have h₁ := hex.2 _ hr
    dsimp only at h₁
    split
    · exact h₁
    · split
      · exact h₁
      · split
        · exact h₁
        · split
          · exact h₁
          · split
            · exact h₁
            · exact h₁

/-- Moves are recorded: the fold of Case 3. -/
theorem fold_cost_le {O : Finset Str} {b : ℚ} {j : Fin 3} (moves : List (BoardGame × Finset Str)) :
    trueCost (moves.foldr (fun q acc => if q.1.board = j then q.2 ∪ acc else acc) O) - trueCost O ≤
      moves.foldr (fun q acc => if q.1.board = j then trueCost q.2 + acc else acc) b - b := by
  induction moves with
  | nil => simp
  | cons q moves ih =>
    simp only [List.foldr_cons]
    split_ifs
    · have hunion : ∀ A B : Finset Str, trueCost (A ∪ B) ≤ trueCost A + trueCost B := by
        intro A B
        have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := realCost)
        have hn : 0 ≤ ∑ x ∈ A ∩ B, realCost x :=
          Finset.sum_nonneg fun x _ => (realCost_pos x).le
        unfold trueCost
        linarith
      have := hunion q.2 (moves.foldr (fun q acc => if q.1.board = j then q.2 ∪ acc else acc) O)
      linarith
    · exact ih

/-- Case 3 records its new spending: on board `j`, the true measure of our strings grows by at most
the growth of what is recorded as spent. -/
theorem caseThree_pot {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play} {j : Fin 3} :
    trueCost ((caseThree I st i t c rs pl).2.1 j) - trueCost (st.ours j) ≤
      spentPot (caseThree I st i t c rs pl).1 j - spentPot rs j := by
  unfold caseThree
  dsimp only
  split_ifs
  · have := fold_cost_le (O := st.ours j) (b := rs.epochSpent j) (j := j)
      (pl.games.map fun g => (g, respond pl.arena g (st.positionList I pl.arena t g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent)))
    simp only [spentPot]
    linarith
  · split
    · split
      · simp [spentPot]
      · simp [spentPot]
    · simp [spentPot, ReqState.closeEpoch]
  · split
    · simp [spentPot, ReqState.closeEpoch]
    · simp [spentPot, ReqState.closeEpoch]

/-- A stage records all new spending. -/
theorem stepCore_pot (st : ConState) (j : Fin 3) :
    trueCost ((stepCore I st).2.1 j) - trueCost (st.ours j) ≤
      spentPot (stepCore I st).1 j - spentPot (st.req (Nat.unpair st.stage).1) j := by
  unfold stepCore
  dsimp only
  split
  · simp [caseOne_pot]
  · split
    · simp
    · split
      · simp [caseTwo_pot]
      · exact caseThree_pot I

/-- The record is unchanged by the fields of the schedule. -/
theorem spentPot_rsAt_succ_self (s : ℕ) (j : Fin 3) :
    spentPot (rsAt I (s + 1) (Nat.unpair s).1) j = spentPot (stepCore I (stateAt I s)).1 j := by
  rw [rsAt_succ_self]
  rfl

/-- What a requirement has recorded as spent on a board is nonnegative, at every stage. -/
theorem spentPot_nonneg (s i : ℕ) (j : Fin 3) : 0 ≤ spentPot (rsAt I s i) j := by
  induction s with
  | zero => simp [spentPot, rsAt, stateAt]
  | succ s ih =>
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      have h := stepCore_pot I (stateAt I s) j
      rw [stage_stateAt] at h
      have hc : (stateAt I s).ours j ⊆ (stepCore I (stateAt I s)).2.1 j :=
        step_ours_superset I (stateAt I s) j
      have hcost : trueCost ((stateAt I s).ours j) ≤ trueCost ((stepCore I (stateAt I s)).2.1 j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hc fun x _ _ => (realCost_pos x).le
      rw [spentPot_rsAt_succ_self]
      have := ih
      unfold rsAt at this
      linarith
    · rw [rsAt_succ_of_ne I hi]
      exact ih

/-- A requirement with no `c` has not been visited, and has spent nothing. -/
theorem epochSpent_of_c_none {s i : ℕ} (h : (rsAt I s i).c = none) (j : Fin 3) :
    (rsAt I s i).epochSpent j = 0 := by
  rcases visited_spec I s i with h0 | ⟨u, -, hui, -, hsame, -⟩
  · rw [h0]
    rfl
  · exfalso
    have := c_isSome_after_visit I u
    rw [hui, ← hsame, h] at this
    cases this

/-- The windows of a requirement record what it has spent. -/
theorem sum_epochs_eq (s i : ℕ) (j : Fin 3) :
    ((openEpoch I s i ++ (rsAt I s i).closed).map fun e => e.spent j).sum =
      spentPot (rsAt I s i) j := by
  unfold openEpoch spentPot
  cases hc : (rsAt I s i).c with
  | none => simp [epochSpent_of_c_none I hc j]
  | some c => simp

/-- The sum over the windows, by requirements. -/
theorem sum_allEpochs (s : ℕ) (j : Fin 3) :
    ((allEpochs I s).map fun e => e.spent j).sum =
      ∑ i ∈ Finset.range s, spentPot (rsAt I s i) j := by
  unfold allEpochs
  have hgen : ∀ l : List ℕ, ((l.flatMap fun i => openEpoch I s i ++ (rsAt I s i).closed).map
      fun e => e.spent j).sum = (l.map fun i => spentPot (rsAt I s i) j).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      rw [← ih, ← sum_epochs_eq I s a j, List.map_append, List.sum_append]
  rw [hgen, ← List.sum_toFinset _ List.nodup_range]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp

/-- **All of our spending is recorded in the windows.** -/
theorem ours_cost_le_epochs (s : ℕ) (j : Fin 3) :
    trueCost (oursAt I j s) ≤ ((allEpochs I s).map fun e => e.spent j).sum := by
  rw [sum_allEpochs]
  induction s with
  | zero => simp [oursAt, stateAt, trueCost]
  | succ s ih =>
    set i₀ := (Nat.unpair s).1 with hi₀
    have hi₀s : i₀ < s + 1 := Nat.lt_succ_of_le (Nat.unpair_left_le s)
    have hrest : ∀ i ∈ Finset.range (s + 1), i ≠ i₀ → spentPot (rsAt I (s + 1) i) j =
        spentPot (rsAt I s i) j := fun i _ hi => by rw [rsAt_succ_of_ne I hi]
    have hstep := stepCore_pot I (stateAt I s) j
    rw [stage_stateAt] at hstep
    have hsum : ∑ i ∈ Finset.range (s + 1), spentPot (rsAt I (s + 1) i) j =
        ∑ i ∈ Finset.range (s + 1), spentPot (rsAt I s i) j +
          (spentPot (rsAt I (s + 1) i₀) j - spentPot (rsAt I s i₀) j) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi₀s),
        ← Finset.add_sum_erase (Finset.range (s + 1)) (fun i => spentPot (rsAt I s i) j)
          (Finset.mem_range.2 hi₀s)]
      have : ∑ i ∈ (Finset.range (s + 1)).erase i₀, spentPot (rsAt I (s + 1) i) j =
          ∑ i ∈ (Finset.range (s + 1)).erase i₀, spentPot (rsAt I s i) j :=
        Finset.sum_congr rfl fun i hi =>
          hrest i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      rw [this]
      ring
    have hmono : ∑ i ∈ Finset.range s, spentPot (rsAt I s i) j ≤
        ∑ i ∈ Finset.range (s + 1), spentPot (rsAt I s i) j := by
      rw [Finset.sum_range_succ]
      have := spentPot_nonneg I s s j
      linarith
    rw [hsum, spentPot_rsAt_succ_self]
    have hours : trueCost (oursAt I j (s + 1)) = trueCost ((stepCore I (stateAt I s)).2.1 j) := rfl
    have h0 : trueCost (oursAt I j s) = trueCost ((stateAt I s).ours j) := rfl
    have h1 : spentPot (rsAt I s i₀) j = spentPot ((stateAt I s).req (Nat.unpair s).1) j := rfl
    rw [hours, h1]
    rw [h0] at ih
    linarith

/-! ### The values of `c` -/

/-- The values of `c` left by resets or still open, for a requirement. -/
def finalsOf (rs : ReqState) : List ℕ :=
  (rs.c.toList) ++ ((rs.closed.filter fun e => e.final).map Epoch.c)

/-- Closing a window that did not end in a reset does not change the values of `c` left by resets or
still open. -/
theorem closeEpoch_finalsOf {rs : ReqState} {i c stop t : ℕ} :
    finalsOf (rs.closeEpoch i c stop t false) = finalsOf rs := by
  simp [finalsOf, ReqState.closeEpoch]

/-- Case 1 puts the new value `newC st i t` in front of the values of `c` left by resets or still
open; the old value of `c`, if any, stays among them as the value of a window ended by a reset. -/
theorem caseOne_finalsOf (st : ConState) (i t : ℕ) :
    finalsOf (caseOne st i t).1 = newC st i t :: finalsOf (st.req i) := by
  unfold caseOne
  dsimp only
  split
  · rename_i c hcc
    simp [finalsOf, ReqState.closeEpoch, hcc]
  · rename_i hcc
    simp [finalsOf, hcc]

/-- The first part of Case 2 keeps `c` and the values of `c` left by resets or still open, whether
it ends the visit or returns an agreed value. -/
theorem examineTop_finalsOf {st : ConState} {i t c : ℕ} {rs : ReqState} :
    (∀ r, examineTop I st i t c rs = .inl r → finalsOf r.1 = finalsOf rs ∧ r.1.c = rs.c) ∧
      ∀ r, examineTop I st i t c rs = .inr r → finalsOf r.1 = finalsOf rs ∧ r.1.c = rs.c := by
  constructor
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
        exact ⟨closeEpoch_finalsOf, rfl⟩
      · split at hr
        · cases hr
          exact ⟨rfl, rfl⟩
        · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
          exact ⟨rfl, rfl⟩
        · cases hr
          exact ⟨rfl, rfl⟩
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · cases hr
          exact ⟨closeEpoch_finalsOf, rfl⟩
    · split at hr
      · cases hr
        exact ⟨closeEpoch_finalsOf, rfl⟩
      · split at hr
        · cases hr
        · cases hr

/-- Case 2 does not change the values of `c` left by resets or still open. -/
theorem caseTwo_finalsOf {st : ConState} {i t c : ℕ} {rs : ReqState} :
    finalsOf (caseTwo I st i t c rs).1 = finalsOf rs := by
  have hex := examineTop_finalsOf I (st := st) (i := i) (t := t) (c := c) (rs := rs)
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    exact (hex.1 r hr).1
  · rename_i rs₁ σ hr
    have h₁ := (hex.2 _ hr).1
    dsimp only at h₁
    split
    · exact h₁
    · split
      · exact h₁
      · split
        · exact h₁
        · split
          · exact h₁
          · split
            · exact h₁
            · exact h₁

/-- Case 3 does not change the values of `c` left by resets or still open. -/
theorem caseThree_finalsOf {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play} :
    finalsOf (caseThree I st i t c rs pl).1 = finalsOf rs := by
  unfold caseThree
  dsimp only
  split_ifs
  · rfl
  · split
    · split <;> rfl
    · exact closeEpoch_finalsOf
  · split <;> exact closeEpoch_finalsOf

/-- Before the first stage, no requirement has a value of `c`. -/
theorem finalsOf_rsAt_zero (i : ℕ) : finalsOf (rsAt I 0 i) = [] := rfl

/-- A stage changes the values of `c` by at most one new value, above all earlier ones. -/
theorem stepCore_finalsOf (st : ConState) :
    (finalsOf (stepCore I st).1 = finalsOf (st.req (Nat.unpair st.stage).1) ∧
        (stepCore I st).2.2.1 = st.nextC) ∨
      (∃ c', st.nextC ≤ c' ∧ (Nat.unpair st.stage).1 + 7 ≤ c' ∧
        finalsOf (stepCore I st).1 = c' :: finalsOf (st.req (Nat.unpair st.stage).1) ∧
        (stepCore I st).2.2.1 = c' + 2) := by
  unfold stepCore
  dsimp only
  split
  · refine Or.inr ⟨newC st (Nat.unpair st.stage).1 (st.stage + 1), ?_, ?_, caseOne_finalsOf _ _ _,
        rfl⟩
    · unfold newC
      exact (le_max_left _ _).trans (le_max_right _ _)
    · unfold newC
      exact le_max_left _ _
  · split
    · exact Or.inl ⟨rfl, rfl⟩
    · split
      · exact Or.inl ⟨caseTwo_finalsOf I, rfl⟩
      · exact Or.inl ⟨caseThree_finalsOf I, rfl⟩

/-- The values of `c` are unchanged by the fields of the schedule: for the requirement visited at
stage `s + 1`, they are those computed by `stepCore`. -/
theorem finalsOf_rsAt_succ_self (s : ℕ) :
    finalsOf (rsAt I (s + 1) (Nat.unpair s).1) = finalsOf (stepCore I (stateAt I s)).1 := by
  rw [rsAt_succ_self]
  rfl

/-- The invariant of the values of `c`. -/
theorem finals_invariant (s : ℕ) :
    (∀ i, (finalsOf (rsAt I s i)).Nodup ∧ (∀ c ∈ finalsOf (rsAt I s i), c < (stateAt I s).nextC) ∧
      ∀ c ∈ finalsOf (rsAt I s i), 7 ≤ c) ∧
      ∀ i i', i ≠ i' → List.Disjoint (finalsOf (rsAt I s i)) (finalsOf (rsAt I s i')) := by
  induction s with
  | zero =>
    refine ⟨fun i => ?_, fun i i' _ => ?_⟩
    · simp [finalsOf_rsAt_zero]
    · simp [finalsOf_rsAt_zero]
  | succ s ih =>
    obtain ⟨h1, h2⟩ := ih
    have hstep := stepCore_finalsOf I (stateAt I s)
    rw [stage_stateAt] at hstep
    have hnext : (stateAt I (s + 1)).nextC = (stepCore I (stateAt I s)).2.2.1 := rfl
    have hfin := finalsOf_rsAt_succ_self I s
    rcases hstep with ⟨hsame, hn⟩ | ⟨c', hlow, hfl, hnew, hn⟩
    · have hall : ∀ i, finalsOf (rsAt I (s + 1) i) = finalsOf (rsAt I s i) := by
        intro i
        by_cases hi : i = (Nat.unpair s).1
        · subst hi
          rw [hfin, hsame]
          rfl
        · rw [rsAt_succ_of_ne I hi]
      refine ⟨fun i => ?_, fun i i' hne => ?_⟩
      · rw [hall, hnext, hn]
        exact h1 i
      · rw [hall, hall]
        exact h2 i i' hne
    · have hall : ∀ i, i ≠ (Nat.unpair s).1 → finalsOf (rsAt I (s + 1) i) = finalsOf (rsAt I s i) :=
        fun i hi => by rw [rsAt_succ_of_ne I hi]
      have hself : finalsOf (rsAt I (s + 1) (Nat.unpair s).1) =
          c' :: finalsOf (rsAt I s (Nat.unpair s).1) := by
        rw [hfin, hnew]
        rfl
      have hnotin : ∀ i, c' ∉ finalsOf (rsAt I s i) := fun i hmem => by
        have := (h1 i).2.1 c' hmem
        omega
      refine ⟨fun i => ?_, fun i i' hne => ?_⟩
      · rw [hnext, hn]
        by_cases hi : i = (Nat.unpair s).1
        · subst hi
          rw [hself]
          refine ⟨List.nodup_cons.2 ⟨hnotin _, (h1 _).1⟩, fun c hc => ?_, fun c hc => ?_⟩
          · rcases List.mem_cons.1 hc with rfl | hmem
            · omega
            · have := (h1 _).2.1 c hmem
              omega
          · rcases List.mem_cons.1 hc with rfl | hmem
            · omega
            · exact (h1 _).2.2 c hmem
        · rw [hall i hi]
          refine ⟨(h1 i).1, fun c hc => ?_, (h1 i).2.2⟩
          have := (h1 i).2.1 c hc
          omega
      · by_cases hi : i = (Nat.unpair s).1
        · subst hi
          rw [hself, hall i' (Ne.symm hne)]
          intro c hc hc'
          rcases List.mem_cons.1 hc with rfl | hmem
          · exact hnotin i' hc'
          · exact h2 _ i' hne hmem hc'
        · by_cases hi' : i' = (Nat.unpair s).1
          · subst hi'
            rw [hself, hall i hi]
            intro c hc hc'
            rcases List.mem_cons.1 hc' with rfl | hmem
            · exact hnotin i hc
            · exact h2 i _ hne hc hmem
          · rw [hall i hi, hall i' hi']
            exact h2 i i' hne

/-! ### No double counting -/

/-- A stage keeps the current window, or closes it at `t`. -/
def KeepsOrCloses (i c t : ℕ) (rs r : ReqState) : Prop :=
  (r.closed = rs.closed ∧ r.epochStart = rs.epochStart ∧ r.tables = rs.tables) ∨
    (r.closed = ⟨i, c, rs.epochStart, t, boardOf rs.tables, rs.epochSpent, false⟩ :: rs.closed ∧
      r.epochStart = t)

/-- The first part of Case 2 keeps the current window or closes it at `t`; when it returns an agreed
value, it closes the window, not as a reset. -/
theorem examineTop_window {st : ConState} {i t c : ℕ} {rs : ReqState} :
    (∀ r, examineTop I st i t c rs = .inl r → KeepsOrCloses i c t rs r.1) ∧
      ∀ r, examineTop I st i t c rs = .inr r →
        r.1.closed = ⟨i, c, rs.epochStart, t, boardOf rs.tables, rs.epochSpent, false⟩ ::
            rs.closed ∧
          r.1.epochStart = t := by
  constructor
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
        exact Or.inr ⟨rfl, rfl⟩
      · split at hr
        · cases hr
          exact Or.inl ⟨rfl, rfl, rfl⟩
        · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
          exact Or.inl ⟨rfl, rfl, rfl⟩
        · cases hr
          exact Or.inl ⟨rfl, rfl, rfl⟩
  · intro r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · cases hr
          exact ⟨rfl, rfl⟩
    · split at hr
      · cases hr
        exact ⟨rfl, rfl⟩
      · split at hr
        · cases hr
        · cases hr

/-- Case 2 keeps the current window, or closes it at `t`. -/
theorem caseTwo_window {st : ConState} {i t c : ℕ} {rs : ReqState} :
    KeepsOrCloses i c t rs (caseTwo I st i t c rs).1 := by
  have hex := examineTop_window I (st := st) (i := i) (t := t) (c := c) (rs := rs)
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    exact hex.1 r hr
  · rename_i rs₁ σ hr
    have h₁ := hex.2 _ hr
    dsimp only at h₁
    split
    · exact Or.inr h₁
    · split
      · exact Or.inr h₁
      · split
        · exact Or.inr h₁
        · split
          · exact Or.inr h₁
          · split
            · exact Or.inr h₁
            · exact Or.inr h₁

/-- Case 3 keeps the current window (Cases 3a and 3b), or closes it at `t` (Case 3c). -/
theorem caseThree_window {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play} :
    KeepsOrCloses i c t rs (caseThree I st i t c rs pl).1 := by
  unfold caseThree
  dsimp only
  split_ifs
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · split
    · split
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Case 1 keeps the tables and starts a new window at `t`; the closed windows are kept, or the
current window is added to them, closed at the last visit and marked as ended by a reset. -/
theorem caseOne_window (st : ConState) (i t : ℕ) :
    (caseOne st i t).1.tables = (st.req i).tables ∧ (caseOne st i t).1.epochStart = t ∧
      ((caseOne st i t).1.closed = (st.req i).closed ∨
        ∃ c, (caseOne st i t).1.closed = ⟨i, c, (st.req i).epochStart, (st.req i).lastVisit,
          boardOf (st.req i).tables, (st.req i).epochSpent, true⟩ :: (st.req i).closed) := by
  unfold caseOne
  dsimp only
  split
  · exact ⟨rfl, rfl, Or.inr ⟨_, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl rfl⟩

/-- How a stage moves the windows of the requirement visited. -/
theorem stepCore_window (st : ConState) :
    (mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) = false ∧
      ∃ c, KeepsOrCloses (Nat.unpair st.stage).1 c (st.stage + 1) (st.req (Nat.unpair st.stage).1)
        (stepCore I st).1) ∨
    (mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) = true ∧
      (stepCore I st).1.tables = (st.req (Nat.unpair st.stage).1).tables ∧
      (stepCore I st).1.epochStart = st.stage + 1 ∧
      ((stepCore I st).1.closed = (st.req (Nat.unpair st.stage).1).closed ∨
        ∃ c, (stepCore I st).1.closed = ⟨(Nat.unpair st.stage).1, c,
          (st.req (Nat.unpair st.stage).1).epochStart, (st.req (Nat.unpair st.stage).1).lastVisit,
          boardOf (st.req (Nat.unpair st.stage).1).tables,
          (st.req (Nat.unpair st.stage).1).epochSpent, true⟩ ::
            (st.req (Nat.unpair st.stage).1).closed)) := by
  unfold stepCore
  dsimp only
  split
  · rename_i hr
    exact Or.inr ⟨hr, caseOne_window st _ _⟩
  · rename_i hr
    refine Or.inl ⟨by simpa using hr, ?_⟩
    split
    · exact ⟨0, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · rename_i c _
      split
      · exact ⟨c, caseTwo_window I⟩
      · exact ⟨c, caseThree_window I⟩

/-- The facts about a window that do not depend on its spending: it ends at a visit, the board is
constant in it, and all visits in it are not resets. -/
structure WinOK (i start stop : ℕ) (board : Finset Str) : Prop where
  le : start ≤ stop
  visit : start < stop → (Nat.unpair (stop - 1)).1 = i
  board_eq : ∀ u, start ≤ u → u < stop → boardOf (rsAt I u i).tables = board
  noReset : ∀ u, start ≤ u → u < stop → (Nat.unpair u).1 = i →
    mustReset I (stateAt I u) i (Nat.unpair u).2 (u + 1) = false

/-- An empty window, from `t` to `t`, satisfies `WinOK` for any board. -/
theorem winOK_empty (i t : ℕ) (board : Finset Str) : WinOK I i t t board :=
  ⟨le_rfl, fun h => absurd h (lt_irrefl _), fun _ h1 h2 => absurd h2 (not_lt.2 h1),
    fun _ h1 h2 => absurd h2 (not_lt.2 h1)⟩

/-- There are no visits after the last one. -/
theorem no_visit_after_last {s u i : ℕ} (h1 : (rsAt I s i).lastVisit ≤ u) (h2 : u < s) :
    (Nat.unpair u).1 ≠ i := by
  intro hu
  have h3 := lastVisit_self I u
  rw [hu] at h3
  have h4 := lastVisit_mono I i (show u + 1 ≤ s from h2)
  omega

/-- A requirement does not change after its last visit: if its last visit by stage `s` is at most
`u ≤ s`, its state at `u` is its state at `s`. -/
theorem rsAt_eq_of_lastVisit_le {s u i : ℕ} (h1 : (rsAt I s i).lastVisit ≤ u) (h2 : u ≤ s) :
    rsAt I s i = rsAt I u i :=
  rsAt_const I h2 fun _ h3 h4 => no_visit_after_last I (h1.trans h3) h4

/-- The current window, extended by a visit with no reset. -/
theorem WinOK.extend {s i : ℕ} (hi : (Nat.unpair s).1 = i)
    (h : WinOK I i (rsAt I s i).epochStart (rsAt I s i).lastVisit (boardOf (rsAt I s i).tables))
    (hr : mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) = false) :
    WinOK I i (rsAt I s i).epochStart (s + 1) (boardOf (rsAt I s i).tables) := by
  have hlv := lastVisit_le I s i
  refine ⟨by have := h.le; omega, fun _ => by
      simpa using hi, fun u h1 h2 => ?_, fun u h1 h2 h3 => ?_⟩
  · by_cases hu : u < (rsAt I s i).lastVisit
    · exact h.board_eq u h1 hu
    · rw [rsAt_eq_of_lastVisit_le I (not_lt.1 hu) (Nat.lt_succ_iff.1 h2)]
  · by_cases hu : u < (rsAt I s i).lastVisit
    · exact h.noReset u h1 hu h3
    · by_cases hus : u = s
      · subst hus
        exact hr
      · exact absurd h3 (no_visit_after_last I (not_lt.1 hu) (by omega))

/-- The invariant of the windows of a requirement. -/
structure WinInv (s i : ℕ) : Prop where
  opn : WinOK I i (rsAt I s i).epochStart (rsAt I s i).lastVisit (boardOf (rsAt I s i).tables)
  closed : ∀ e ∈ (rsAt I s i).closed,
    WinOK I i e.start e.stop e.board ∧ e.stop ≤ (rsAt I s i).epochStart
  chain : (rsAt I s i).closed.Pairwise fun e' e => e.stop ≤ e'.start

/-- The invariant of the windows holds at every stage, for every requirement. -/
theorem winInv (s i : ℕ) : WinInv I s i := by
  induction s with
  | zero => exact ⟨winOK_empty I i 0 _, fun e he => absurd he List.not_mem_nil, List.Pairwise.nil⟩
  | succ s ih =>
    by_cases hi : (Nat.unpair s).1 = i
    · have hspec := stepCore_window I (stateAt I s)
      rw [stage_stateAt, hi] at hspec
      have hrs : (stateAt I s).req i = rsAt I s i := rfl
      rw [hrs] at hspec
      have hsucc := rsAt_succ_self I s
      rw [hi] at hsucc
      have hclosed : (rsAt I (s + 1) i).closed = (stepCore I (stateAt I s)).1.closed := by
        rw [hsucc]
      have hstart : (rsAt I (s + 1) i).epochStart = (stepCore I (stateAt I s)).1.epochStart := by
        rw [hsucc]
      have htables : (rsAt I (s + 1) i).tables = (stepCore I (stateAt I s)).1.tables := by
        rw [hsucc]
      have hlast : (rsAt I (s + 1) i).lastVisit = s + 1 := by rw [hsucc]
      have hlv := lastVisit_le I s i
      have hle := ih.opn.le
      rcases hspec with ⟨hr, c, ⟨hc, hst, htb⟩ | ⟨hc, hst⟩⟩ | ⟨hr, htb, hst, hcl⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [hstart, hst, hlast, htables, htb]
          exact WinOK.extend I hi ih.opn hr
        · rw [hclosed, hc, hstart, hst]
          exact ih.closed
        · rw [hclosed, hc]
          exact ih.chain
      · refine ⟨?_, ?_, ?_⟩
        · rw [hstart, hst, hlast]
          exact winOK_empty I i _ _
        · rw [hclosed, hc, hstart, hst]
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨WinOK.extend I hi ih.opn hr, le_rfl⟩
          · exact ⟨(ih.closed e he).1, by have := (ih.closed e he).2; omega⟩
        · rw [hclosed, hc]
          exact List.pairwise_cons.2 ⟨fun e he => (ih.closed e he).2, ih.chain⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [hstart, hst, hlast]
          exact winOK_empty I i _ _
        · rw [hclosed, hstart, hst]
          rcases hcl with hc | ⟨c, hc⟩
          · rw [hc]
            exact fun e he => ⟨(ih.closed e he).1, by have := (ih.closed e he).2; omega⟩
          · rw [hc]
            intro e he
            rcases List.mem_cons.1 he with rfl | he
            · exact ⟨ih.opn, by dsimp only; omega⟩
            · exact ⟨(ih.closed e he).1, by have := (ih.closed e he).2; omega⟩
        · rw [hclosed]
          rcases hcl with hc | ⟨c, hc⟩
          · rw [hc]
            exact ih.chain
          · rw [hc]
            exact List.pairwise_cons.2 ⟨fun e he => (ih.closed e he).2, ih.chain⟩
    · have h := rsAt_succ_of_ne I (i := i) (s := s) (Ne.symm hi)
      exact ⟨by rw [h]; exact ih.opn, by rw [h]; exact ih.closed, by rw [h]; exact ih.chain⟩

/-- All the windows of a requirement satisfy `WinOK`. -/
theorem winOK_of_mem (s i : ℕ) {e : Epoch} (he : e ∈ openEpoch I s i ++ (rsAt I s i).closed) :
    WinOK I i e.start e.stop e.board := by
  have hinv := winInv I s i
  rcases List.mem_append.1 he with h | h
  · unfold openEpoch at h
    split at h
    · rcases List.mem_singleton.1 h with rfl
      exact hinv.opn
    · cases h
  · exact (hinv.closed e h).1

/-- Windows consecutive in time are charged disjoint sets. -/
theorem charged_disjoint_of_stop_le (hI : I.Valid) {e e' : Epoch} (h : e.stop ≤ e'.start) :
    Disjoint (charged I e) (charged I e') := by
  refine Finset.disjoint_left.2 fun τ h1 h2 => ?_
  simp only [charged, mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h1 h2
  have := hI.opp_mono h h1.2.1
  rw [h2.2.2] at this
  cases this

/-- A condition of `mustReset`. -/
theorem mustReset_of_lt {st : ConState} {i e t m : ℕ} (hm : m < i)
    (h : (st.req i).lastVisit < (st.req m).lastActed ∨ pendingHit I (st.req m) t = true) :
    mustReset I st i e t = true := by
  unfold mustReset
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  exact Or.inr ⟨m, hm, h⟩

/-- The first visit in an interval. -/
theorem exists_first_visit {i a b : ℕ} (h : a ≤ b) (hb : (Nat.unpair b).1 = i) :
    ∃ u, a ≤ u ∧ u ≤ b ∧ (Nat.unpair u).1 = i ∧ ∀ w, a ≤ w → w < u → (Nat.unpair w).1 ≠ i := by
  classical
  have hex : ∃ u, a ≤ u ∧ (Nat.unpair u).1 = i := ⟨b, h, hb⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨h, hb⟩, (Nat.find_spec hex).2,
    fun w h1 h2 h3 => Nat.find_min hex h2 ⟨h1, h3⟩⟩

/-- A hit, from a string. -/
theorem pendingHit_of_mem {rs : ReqState} {t : ℕ} {τ : Str} (hb : τ ∈ boardOf rs.tables)
    (h1 : I.opp t τ = true) (h2 : I.opp rs.lastVisit τ = false) : pendingHit I rs t = true := by
  simp only [pendingHit, decide_eq_true_eq]
  exact ⟨τ, mem_filter.2 ⟨hb, by simp [h1, h2]⟩⟩

/-- **The hit rule.**  A window of `R_i` and a window of `R_m`, `m < i`, are charged disjoint sets.
If a string on the board of `R_m` is compressed during a window of `R_m`, then at the first visit of
`R_m` after it, this is a hit, so `R_m` acts.  If `R_i` has its last visit of the window before
this, it sees the hit as pending and is reset there; otherwise it is reset at its first visit
afterwards.  Either way the window of `R_i` does not contain the string's stage. -/
theorem charged_disjoint_of_lt (hI : I.Valid) {m i : ℕ} (hm : m < i) {e e' : Epoch}
    (he : WinOK I i e.start e.stop e.board) (he' : WinOK I m e'.start e'.stop e'.board) :
    Disjoint (charged I e) (charged I e') := by
  classical
  refine Finset.disjoint_left.2 fun τ h h' => ?_
  simp only [charged, mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h h'
  obtain ⟨-, hstop, hstart⟩ := h
  obtain ⟨hb', hstop', hstart'⟩ := h'
  have hex : ∃ n, I.opp n τ = true := ⟨_, hstop⟩
  obtain ⟨t₀, hfind, hmin⟩ : ∃ t₀, I.opp t₀ τ = true ∧ ∀ n, n < t₀ → I.opp n τ = false :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n hn => by simpa using Nat.find_min hex hn⟩
  have hge : ∀ n, t₀ ≤ n → I.opp n τ = true := fun n hn => hI.opp_mono hn hfind
  have hlow : ∀ n, I.opp n τ = true → t₀ ≤ n := fun n hn => by
    by_contra hc
    rw [hmin n (not_le.1 hc)] at hn
    cases hn
  have hlt : ∀ n, I.opp n τ = false → n < t₀ := fun n hn => by
    by_contra hc
    rw [hge n (not_lt.1 hc)] at hn
    cases hn
  have h1 := hlt _ hstart
  have h2 := hlow _ hstop
  have h1' := hlt _ hstart'
  have h2' := hlow _ hstop'
  obtain ⟨v, hv⟩ : ∃ v, e.stop = v + 1 := ⟨e.stop - 1, by omega⟩
  obtain ⟨v', hv'⟩ : ∃ v', e'.stop = v' + 1 := ⟨e'.stop - 1, by omega⟩
  have hvi : (Nat.unpair v).1 = i := by
    have := he.visit (by omega)
    rwa [hv] at this
  have hvm : (Nat.unpair v').1 = m := by
    have := he'.visit (by omega)
    rwa [hv'] at this
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := exists_first_visit (show t₀ - 1 ≤ v' by omega) hvm
  have hne : u ≠ v := by
    rintro rfl
    omega
  rcases lt_or_gt_of_ne hne with huv | hvu
  · -- `R_m` acted before the last visit of the window of `R_i`.
    have hlvu : (rsAt I u m).lastVisit ≤ t₀ - 1 := by
      rw [rsAt_const I hu1 hu4]
      exact lastVisit_le I _ _
    have hhit : pendingHit I (rsAt I u m) (u + 1) = true :=
      pendingHit_of_mem I (by rw [he'.board_eq u (by omega) (by omega)]; exact hb')
        (hge _ (by omega)) (hmin _ (by omega))
    have hact : (rsAt I (u + 1) m).lastActed = u + 1 := by
      have := lastActed_of_hit I (s := u) (by rw [hu3]; exact hhit)
      rwa [hu3] at this
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := exists_first_visit (show u + 1 ≤ v by omega) hvi
    have hlvw : (rsAt I w i).lastVisit ≤ u := by
      rw [rsAt_const I hw1 hw4, rsAt_succ_of_ne I (by rw [hu3]; omega)]
      exact lastVisit_le I _ _
    have hactw := lastActed_mono I m hw1
    have hreset : mustReset I (stateAt I w) i (Nat.unpair w).2 (w + 1) = true :=
      mustReset_of_lt I hm (Or.inl (by
        change (rsAt I w i).lastVisit < (rsAt I w m).lastActed
        omega))
    rw [he.noReset w (by omega) (by omega) hw3] at hreset
    cases hreset
  · -- `R_m` has not been visited since: the last visit of the window of `R_i` sees a pending hit.
    have hlvv : (rsAt I v m).lastVisit ≤ t₀ - 1 := by
      rw [rsAt_const I (show t₀ - 1 ≤ v by omega) fun w hw1 hw2 => hu4 w hw1 (by omega)]
      exact lastVisit_le I _ _
    have hhit : pendingHit I (rsAt I v m) (v + 1) = true :=
      pendingHit_of_mem I (by rw [he'.board_eq v (by omega) (by omega)]; exact hb')
        (hge _ (by omega)) (hmin _ (by omega))
    have hreset : mustReset I (stateAt I v) i (Nat.unpair v).2 (v + 1) = true :=
      mustReset_of_lt I hm (Or.inr hhit)
    rw [he.noReset v (by omega) (by omega) hvi] at hreset
    cases hreset

/-- **No double counting (§4.4).**  The charged sets are pairwise disjoint: within a requirement
because the windows are consecutive in time, across requirements by the hit rule. -/
theorem charged_pairwise_disjoint (hI : I.Valid) (s : ℕ) :
    (allEpochs I s).Pairwise fun e e' => Disjoint (charged I e) (charged I e') := by
  unfold allEpochs
  refine List.pairwise_flatMap.2 ⟨fun i _ => ?_, ?_⟩
  · have hinv := winInv I s i
    refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
    · unfold openEpoch
      split <;> simp
    · exact hinv.chain.imp fun h => (charged_disjoint_of_stop_le I hI h).symm
    · intro a ha b hb
      unfold openEpoch at ha
      split at ha
      · rcases List.mem_singleton.1 ha with rfl
        exact (charged_disjoint_of_stop_le I hI (hinv.closed b hb).2).symm
      · cases ha
  · refine List.pairwise_lt_range.imp fun {a b} hab x hx y hy => ?_
    exact (charged_disjoint_of_lt I hI hab (winOK_of_mem I s b hy) (winOK_of_mem I s a hx)).symm

/-! ### Our spending in a window -/

/-- Our spending in the current window, in units. -/
abbrev unitsOf (c : ℕ) (rs : ReqState) (j : Fin 3) : ℚ :=
  rs.epochSpent j * 2 ^ (c + maxLen rs.tables + 1)

/-- The opponent's spending in the current window up to stage `t`, in units. -/
abbrev lamOf (c : ℕ) (rs : ReqState) (t : ℕ) : ℕ :=
  oppSpend I (arenaOf c rs.tables) rs.epochStart t

/-- Our spending in a list of games, on one board. -/
def onBoard (gs : List BoardGame) (j : Fin 3) : ℕ :=
  gs.foldr (fun g acc => if g.board = j then g.spent + acc else acc) 0

/-- The recursive equation of `onBoard`: the first game counts only if it is on board `j`. -/
theorem onBoard_cons (g : BoardGame) (gs : List BoardGame) (j : Fin 3) :
    onBoard (g :: gs) j = if g.board = j then g.spent + onBoard gs j else onBoard gs j := rfl

/-- With no game on board `j`, our spending on `j` is zero. -/
theorem onBoard_eq_zero_of_not_mem {gs : List BoardGame} {j : Fin 3}
    (h : j ∉ gs.map BoardGame.board) : onBoard gs j = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : ¬ g.board = j := fun hh => h.1 hh.symm
    rw [onBoard_cons, ite_eq_right hne]
    exact ih h.2

/-- If no game has spent anything, our spending on every board is zero. -/
theorem onBoard_eq_zero_of_spent {gs : List BoardGame} (h : ∀ g ∈ gs, g.spent = 0) (j : Fin 3) :
    onBoard gs j = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have h1 := ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    rw [onBoard_cons, h1, h g List.mem_cons_self]
    simp

/-- If the games are on distinct boards and each has spent at most `B`, our spending on every board
is at most `B`. -/
theorem onBoard_le {gs : List BoardGame} (hn : (gs.map BoardGame.board).Nodup) {B : ℕ}
    (hB : ∀ g ∈ gs, g.spent ≤ B) (j : Fin 3) : onBoard gs j ≤ B := by
  induction gs with
  | nil => exact Nat.zero_le _
  | cons g gs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rw [onBoard_cons]
    by_cases hj : g.board = j
    · have h0 : onBoard gs j = 0 := onBoard_eq_zero_of_not_mem (by rw [← hj]; exact hn.1)
      have hg := hB g List.mem_cons_self
      rw [ite_eq_left hj, h0]
      omega
    · rw [ite_eq_right hj]
      exact ih hn.2 fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')

/-- The opponent's limit in a play. -/
abbrev playLimit (pl : Play) : ℕ :=
  pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)

/-- The bound of a window. -/
def WindowBound (e : Epoch) : Prop :=
  ∀ j, e.spent j ≤ 2 * trueCost (charged I e) + if e.final then 1 / 2 ^ e.c else 0

/-- All closed windows of a requirement satisfy the bound. -/
def ClosedOK (rs : ReqState) : Prop := ∀ e ∈ rs.closed, WindowBound I e

/-- The spending invariant of the current window, right after a visit at stage `t`.

* With no game in progress, we have spent at most `2 λ` and at most `ε`, where `λ` is what the
  opponent has spent in the window.
* A play began with such a spending `P₀`, and since then we have spent what its games record.
* Stacked games begin a window, and their budgets are at most twice the opponent's limit.  In the
  other games, exceeding the limit means that the opponent has spent more than `ε` in the window. -/
structure SpendInvAt (c t : ℕ) (rs : ReqState) : Prop where
  baseGe : ∀ bl, rs.baseline = some bl → ∀ k, rs.epochStart ≤ bl.base k
  idle : rs.play = none → ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ) ∧
    unitsOf c rs j ≤ (levelBudget rs.tables 0 : ℚ)
  active : ∀ pl, rs.play = some pl → rs.epochStart ≤ pl.start ∧
    (∀ g ∈ pl.games, g.spent ≤ g.ourLimit) ∧
    ∃ P₀ : Fin 3 → ℚ,
      (∀ j, P₀ j ≤ 2 * (lamOf I c rs pl.start : ℚ) ∧ P₀ j ≤ (levelBudget rs.tables 0 : ℚ)) ∧
      (∀ j, unitsOf c rs j = P₀ j + (onBoard pl.games j : ℚ)) ∧
      ((∃ σ b, pl.kind = .stacked σ b) →
        (∀ j, P₀ j = 0) ∧ ∀ g ∈ pl.games, g.ourLimit ≤ 2 * playLimit pl) ∧
      ((¬ ∃ σ b, pl.kind = .stacked σ b) →
        levelBudget rs.tables 0 ≤ playLimit pl + lamOf I c rs pl.start)

/-- For valid inputs, the opponent's spending since `t₀` is monotone in the current stage. -/
theorem oppSpend_mono_right (hI : I.Valid) (ar : Arena) (t₀ : ℕ) {t t' : ℕ} (h : t ≤ t') :
    oppSpend I ar t₀ t ≤ oppSpend I ar t₀ t' := by
  unfold oppSpend
  refine cost_mono _ fun τ hτ => ?_
  simp only [mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hτ ⊢
  exact ⟨hτ.1, hI.opp_mono h hτ.2.1, hτ.2.2⟩

/-- For valid inputs, the opponent's spending up to `t`, counted from a later stage `t₁ ≥ t₀`, is at
most the spending counted from `t₀`. -/
theorem oppSpend_mono_left (hI : I.Valid) (ar : Arena) {t₀ t₁ : ℕ} (t : ℕ) (h : t₀ ≤ t₁) :
    oppSpend I ar t₁ t ≤ oppSpend I ar t₀ t := by
  unfold oppSpend
  refine cost_mono _ fun τ hτ => ?_
  simp only [mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hτ ⊢
  refine ⟨hτ.1, hτ.2.1, ?_⟩
  cases ho : I.opp t₀ τ with
  | false => rfl
  | true =>
    have := hI.opp_mono h ho
    rw [hτ.2.2] at this
    cases this

/-- The opponent's spending in a window is the charged measure, in units. -/
theorem oppSpend_eq_charged (i c t₀ t : ℕ) (tables : List TTable) (sp : Fin 3 → ℚ) (f : Bool) :
    (oppSpend I (arenaOf c tables) t₀ t : ℚ) =
      trueCost (charged I ⟨i, c, t₀, t, boardOf tables, sp, f⟩) * 2 ^ (c + maxLen tables + 1) := by
  unfold oppSpend
  rw [cost_eq_trueCost (filter_subset _ _)]
  rfl

/-- A window closed with the opponent's spending at least half of ours. -/
theorem closedOK_close {i c t : ℕ} {rs r : ReqState} (hcl : ClosedOK I rs)
    (hr : r.closed = ⟨i, c, rs.epochStart, t, boardOf rs.tables, rs.epochSpent, false⟩ :: rs.closed)
    (h : ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ)) : ClosedOK I r := by
  intro e he
  rw [hr] at he
  rcases List.mem_cons.1 he with rfl | he
  · intro j
    have hj : rs.epochSpent j * 2 ^ (c + maxLen rs.tables + 1) ≤
        2 * (oppSpend I (arenaOf c rs.tables) rs.epochStart t : ℚ) := h j
    rw [oppSpend_eq_charged I i c rs.epochStart t rs.tables rs.epochSpent false, ← mul_assoc] at hj
    have hpos : (0 : ℚ) < 2 ^ (c + maxLen rs.tables + 1) := by positivity
    have := le_of_mul_le_mul_right hj hpos
    simpa using this
  · exact hcl e he

/-- A window left open, or by a reset: one starting measure may be uncharged. -/
theorem windowBound_final {i c t : ℕ} {rs : ReqState}
    (h : ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ) + (levelBudget rs.tables 0 : ℚ)) :
    WindowBound I ⟨i, c, rs.epochStart, t, boardOf rs.tables, rs.epochSpent, true⟩ := by
  intro j
  have hj : rs.epochSpent j * 2 ^ (c + maxLen rs.tables + 1) ≤
      2 * (oppSpend I (arenaOf c rs.tables) rs.epochStart t : ℚ) +
        (levelBudget rs.tables 0 : ℚ) := h j
  rw [oppSpend_eq_charged I i c rs.epochStart t rs.tables rs.epochSpent true] at hj
  have hpos : (0 : ℚ) < 2 ^ (c + maxLen rs.tables + 1) := by positivity
  have hE : ((levelBudget rs.tables 0 : ℕ) : ℚ) = 1 / 2 ^ c * 2 ^ (c + maxLen rs.tables + 1) := by
    unfold levelBudget
    rw [Nat.sub_zero]
    push_cast
    rw [show c + maxLen rs.tables + 1 = c + (maxLen rs.tables + 1) by
        omega, pow_add (2 : ℚ) c, one_div,
      inv_mul_cancel_left₀ (by positivity)]
  rw [hE] at hj
  have h2 : rs.epochSpent j * 2 ^ (c + maxLen rs.tables + 1) ≤
      (2 * trueCost (charged I ⟨i, c, rs.epochStart, t, boardOf rs.tables, rs.epochSpent, true⟩) +
        1 / 2 ^ c) * 2 ^ (c + maxLen rs.tables + 1) := by
    rw [add_mul, mul_assoc]
    exact hj
  have h3 := le_of_mul_le_mul_right h2 hpos
  simpa using h3

/-- The moves of Case 3a. -/
def movesOf (st : ConState) (t : ℕ) (pl : Play) : List (BoardGame × Finset Str) :=
  pl.games.map fun g => (g, respond pl.arena g (st.positionList I pl.arena t g.board)
    (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent))

/-- The games after the moves of Case 3a. -/
def gamesAfter (st : ConState) (t : ℕ) (pl : Play) : List BoardGame :=
  (movesOf I st t pl).map fun q => { q.1 with spent := q.1.spent + cost pl.arena.w q.2 }

/-- Pairing each game with a value and projecting back gives the list of games. -/
theorem map_fst_pair (gs : List BoardGame) (f : BoardGame → Finset Str) :
    (gs.map fun g => (g, f g)).map (fun q => q.1) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, ih]

/-- Charging each game for a move keeps the minimum of `E` and of the opponent's limits. -/
theorem foldr_min_after (w : Str → ℕ) (gs : List BoardGame) (f : BoardGame → Finset Str) (E : ℕ) :
    ((gs.map fun g => (g, f g)).map fun q => { q.1 with spent := q.1.spent + cost w q.2 }).foldr
        (fun g n => min g.oppLimit n) E = gs.foldr (fun g n => min g.oppLimit n) E := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.foldr_cons, ih]

/-- The moves of Case 3a do not change the opponent's limit in the play. -/
theorem playLimit_after (st : ConState) (t : ℕ) (pl : Play) :
    playLimit { pl with games := gamesAfter I st t pl } = playLimit pl :=
  foldr_min_after _ _ _ _

/-- If all games are within our budgets, so are the games after the moves of Case 3a, and each of
their budgets is the budget of a game before the moves. -/
theorem gamesAfter_spec {st : ConState} {t : ℕ} {pl : Play} {g' : BoardGame}
    (hs : ∀ g ∈ pl.games, g.spent ≤ g.ourLimit) (hg' : g' ∈ gamesAfter I st t pl) :
    g'.spent ≤ g'.ourLimit ∧ ∃ g ∈ pl.games, g'.ourLimit = g.ourLimit := by
  unfold gamesAfter movesOf at hg'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hq
  have h1 := (respond_legal pl.arena g (st.positionList I pl.arena t g.board)
    (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent)).2
  have h2 := hs g hg
  refine ⟨?_, g, hg, rfl⟩
  dsimp only
  omega

/-- Our moves are on the board. -/
theorem respond_subset_board (st : ConState) (ar : Arena) (t : ℕ) (g : BoardGame) (a b : ℕ) :
    respond ar g (st.positionList I ar t g.board) a b ⊆ ar.board := fun _ hz =>
  (mem_position (st := st) (I := I) (ar := ar) (t := t) (j := g.board)).1
    ((respond_legal ar g _ a b).1 hz) |>.1

/-- The record of Case 3a in units: the spending of the window grows by the spending of the
games. -/
theorem fold_units {w : Str → ℕ} {S b : ℚ} {j : Fin 3} (moves : List (BoardGame × Finset Str))
    (hS : ∀ q ∈ moves, (cost w q.2 : ℚ) = trueCost q.2 * S) :
    moves.foldr (fun q acc => if q.1.board = j then trueCost q.2 + acc else acc) b * S +
        (onBoard (moves.map fun q => q.1) j : ℚ) =
      b * S +
          (onBoard (moves.map fun q => { q.1 with spent := q.1.spent + cost w q.2 }) j : ℚ) := by
  induction moves with
  | nil => simp [onBoard]
  | cons q moves ih =>
    have h1 := ih fun q' hq' => hS q' (List.mem_cons_of_mem _ hq')
    have h2 := hS q List.mem_cons_self
    simp only [List.foldr_cons, List.map_cons, onBoard_cons]
    by_cases hj : q.1.board = j
    · simp only [hj, ↓reduceIte]
      push_cast
      rw [add_mul, ← h2]
      linarith
    · simp only [hj, ↓reduceIte]
      exact h1

/-- If nothing is spent in the current window, the spending recorded on each board is within both
bounds of an idle window: at most twice the opponent's spending `lamOf`, and at most the budget
`levelBudget r.tables 0`. -/
theorem units_zero {c : ℕ} {r : ReqState} (hs : r.epochSpent = fun _ => 0) (t : ℕ) (j : Fin 3) :
    unitsOf c r j ≤ 2 * (lamOf I c r t : ℚ) ∧ unitsOf c r j ≤ (levelBudget r.tables 0 : ℚ) := by
  have h0 : unitsOf c r j = 0 := by
    change r.epochSpent j * _ = 0
    rw [hs]
    simp
  rw [h0]
  exact ⟨by positivity, by positivity⟩

/-- A window with nothing spent and no game. -/
theorem spendInv_fresh {c t : ℕ} {r : ReqState} (hs : r.epochSpent = fun _ => 0)
    (hp : r.play = none) (hb : ∀ bl, r.baseline = some bl → ∀ k, r.epochStart ≤ bl.base k) :
    SpendInvAt I c t r :=
  ⟨hb, fun _ j => units_zero I hs t j, fun _ h => by rw [hp] at h; cases h⟩

/-- Balanced games are on the given arena, start at `t` and are of kind `balanced`; in each game
nothing is spent yet, and the opponent's limit is `E`. -/
theorem balancedPlay_fields {ar : Arena} {t E : ℕ} {v : TopOutcome} {pl : Play}
    (h : balancedPlay ar t E v = some pl) :
    pl.arena = ar ∧ pl.start = t ∧ pl.kind = .balanced ∧
      ∀ g ∈ pl.games, g.spent = 0 ∧ g.oppLimit = E := by
  unfold balancedPlay at h
  split at h
  · cases h
    refine ⟨rfl, rfl, rfl, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · cases h
    refine ⟨rfl, rfl, rfl, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · cases h

/-- If every game has the opponent's limit `E`, the minimum of `E` and of these limits is `E`. -/
theorem foldr_min_eq {gs : List BoardGame} {E : ℕ} (h : ∀ g ∈ gs, g.oppLimit = E) :
    gs.foldr (fun g n => min g.oppLimit n) E = E := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldr_cons]
    rw [ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg'), h g List.mem_cons_self, min_self]

/-- Balanced games, started with the spending allowed with no game in progress. -/
theorem spendInv_balanced {c t : ℕ} {r : ReqState} {pl : Play} {v : TopOutcome}
    (hr : r.play = some pl)
    (hb : balancedPlay (arenaOf c r.tables) t (levelBudget r.tables 0) v = some pl)
    (hstart : r.epochStart ≤ t) (hbase : ∀ bl, r.baseline = some bl → ∀ k, r.epochStart ≤ bl.base k)
    (hP : ∀ j, unitsOf c r j ≤ 2 * (lamOf I c r t : ℚ) ∧
      unitsOf c r j ≤ (levelBudget r.tables 0 : ℚ)) :
    SpendInvAt I c t r := by
  obtain ⟨ha, hs, hk, hg⟩ := balancedPlay_fields hb
  refine ⟨hbase, fun h => (by rw [hr] at h; cases h), fun pl' hpl' => ?_⟩
  rw [hr] at hpl'
  have hpp : pl = pl' := Option.some.inj hpl'
  subst hpp
  have hE : levelBudget pl.arena.tables 0 = levelBudget r.tables 0 := by
    rw [ha]
    rfl
  have hlim : playLimit pl = levelBudget r.tables 0 := by
    change pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) = _
    rw [hE]
    exact foldr_min_eq fun g hg' => (hg g hg').2
  refine ⟨by rw [hs]; exact hstart, fun g hg' => ?_, unitsOf c r, fun j => ?_, fun j => ?_,
    fun h => ?_, fun _ => ?_⟩
  · rw [(hg g hg').1]
    exact Nat.zero_le _
  · rw [hs]
    exact hP j
  · rw [onBoard_eq_zero_of_spent fun g hg' => (hg g hg').1]
    simp
  · obtain ⟨σ, b, hk'⟩ := h
    rw [hk] at hk'
    cases hk'
  · rw [hlim]
    exact Nat.le_add_right _ _

/-- Balanced games, started with nothing spent. -/
theorem spendInv_balanced_fresh {c t : ℕ} {r : ReqState} {pl : Play} {v : TopOutcome}
    (hr : r.play = some pl)
    (hb : balancedPlay (arenaOf c r.tables) t (levelBudget r.tables 0) v = some pl)
    (hstart : r.epochStart ≤ t) (hbase : ∀ bl, r.baseline = some bl → ∀ k, r.epochStart ≤ bl.base k)
    (hs : r.epochSpent = fun _ => 0) : SpendInvAt I c t r :=
  spendInv_balanced I hr hb hstart hbase (units_zero I hs t)

/-- When the first part of Case 2 returns an agreed value `σ`, the window is closed at `t`, not as a
reset, and a new one starts at `t` with nothing spent; the tables and the play are kept, and the
baseline is `σ` with all base stages at `t`. -/
theorem examineTop_inr {st : ConState} {i t c : ℕ} {rs : ReqState} {r : ReqState × List Bool}
    (h : examineTop I st i t c rs = .inr r) :
    r.1.closed = ⟨i, c, rs.epochStart, t, boardOf rs.tables, rs.epochSpent, false⟩ :: rs.closed ∧
      r.1.epochStart = t ∧ r.1.epochSpent = (fun _ => 0) ∧ r.1.tables = rs.tables ∧
      r.1.play = rs.play ∧ r.1.baseline = some ⟨r.2, fun _ => t⟩ := by
  unfold examineTop at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at h
      · cases h
      · cases h

/-- **The first part of Case 2, ending the visit.**  The repair of Case 2: the games against the old
value, `G(ε, ε)` against `G(ε - λ, ε)`, are charged like the games of Case 3b. -/
theorem examineTop_inl_spend (hI : I.Valid) {st : ConState} {i t t₀ c : ℕ} {rs : ReqState}
    {r : ReqState × Bool} (hinv : SpendInvAt I c t₀ rs) (hcl : ClosedOK I rs) (hnp : rs.play = none)
    (hidle : ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ) ∧
      unitsOf c rs j ≤ (levelBudget rs.tables 0 : ℚ))
    (hstart : rs.epochStart ≤ t) (hr : examineTop I st i t c rs = .inl r) :
    SpendInvAt I c t r.1 ∧ ClosedOK I r.1 := by
  unfold examineTop at hr
  dsimp only at hr
  split at hr
  · rename_i bl hbl
    split at hr
    · cases hr
      exact ⟨spendInv_fresh I rfl hnp (fun _ h => by cases h),
        closedOK_close I hcl rfl fun j => (hidle j).1⟩
    · split at hr
      · rename_i j₀ _
        cases hr
        refine ⟨⟨hinv.baseGe, fun h => (by cases h), fun pl' hpl' => ?_⟩, hcl⟩
        cases hpl'
        refine ⟨hstart, fun g hg => ?_, unitsOf c rs, hidle, fun j => ?_, fun h => ?_, fun _ => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> exact Nat.zero_le _
        · rw [onBoard_eq_zero_of_spent]
          · simp
          · intro g hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl <;> rfl
        · obtain ⟨σ, b, hk⟩ := h
          cases hk
        · have hl := oppSpend_mono_left I hI (arenaOf c rs.tables) t
            (hinv.baseGe bl hbl (otherBoard j₀))
          change levelBudget rs.tables 0 ≤
            min (levelBudget rs.tables 0)
              (min (levelBudget rs.tables 0 -
                  oppSpend I (arenaOf c rs.tables) (bl.base (otherBoard j₀)) t)
                (levelBudget rs.tables 0)) +
              oppSpend I (arenaOf c rs.tables) rs.epochStart t
          omega
      · cases hr
  · split at hr
    · cases hr
    · split at hr
      · rename_i pl hb
        cases hr
        exact ⟨spendInv_balanced I (r := { rs with play := some pl }) rfl hb hstart hinv.baseGe
            hidle,
          hcl⟩
      · cases hr
        exact ⟨⟨hinv.baseGe, fun _ j => hidle j, hinv.active⟩, hcl⟩

/-- The budget of level `ℓ - 1` is at most twice the budget of level `ℓ`. -/
theorem levelBudget_pred_le (tables : List TTable) (ℓ : ℕ) :
    levelBudget tables (ℓ - 1) ≤ 2 * levelBudget tables ℓ := by
  unfold levelBudget
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The budget of level `ℓ` is at most the budget of level `ℓ - 1`. -/
theorem levelBudget_le_pred (tables : List TTable) (ℓ : ℕ) :
    levelBudget tables ℓ ≤ levelBudget tables (ℓ - 1) := by
  unfold levelBudget
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Case 2.**  Closing a window with no game in progress costs nothing new: we have spent at most
twice what the opponent has spent in it. -/
theorem caseTwo_spend (hI : I.Valid) {st : ConState} {i t t₀ c : ℕ} {rs : ReqState}
    (hinv : SpendInvAt I c t₀ rs) (hcl : ClosedOK I rs) (hnp : rs.play = none) (ht : t₀ ≤ t)
    (hst₀ : rs.epochStart ≤ t₀) :
    SpendInvAt I c t (caseTwo I st i t c rs).1 ∧ ClosedOK I (caseTwo I st i t c rs).1 := by
  have hidle : ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ) ∧
      unitsOf c rs j ≤ (levelBudget rs.tables 0 : ℚ) := fun j => by
    have h := hinv.idle hnp j
    have hm : (lamOf I c rs t₀ : ℚ) ≤ lamOf I c rs t := by
      exact_mod_cast oppSpend_mono_right I hI _ _ ht
    exact ⟨by linarith [h.1], h.2⟩
  have hstart : rs.epochStart ≤ t := hst₀.trans ht
  unfold caseTwo
  dsimp only
  split
  · rename_i r hr
    exact examineTop_inl_spend I hI hinv hcl hnp hidle hstart hr
  · rename_i rs₁ σ hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := examineTop_inr I hr
    dsimp only at h1 h2 h3 h4 h5 h6
    have hcl₁ : ClosedOK I rs₁ := closedOK_close I hcl h1 fun j => (hidle j).1
    have hnp₁ : rs₁.play = none := h5.trans hnp
    have hb₁ : ∀ bl, rs₁.baseline = some bl → ∀ k, rs₁.epochStart ≤ bl.base k := by
      intro bl hbl k
      rw [h6] at hbl
      cases hbl
      exact h2.le
    have hdone : SpendInvAt I c t rs₁ ∧ ClosedOK I rs₁ := ⟨spendInv_fresh I h3 hnp₁ hb₁, hcl₁⟩
    split
    · rename_i ℓ j _
      refine ⟨⟨hb₁, fun h => (by cases h), fun pl' hpl' => ?_⟩, hcl₁⟩
      cases hpl'
      have h7 := levelBudget_le_pred rs.tables ℓ
      have h8 := levelBudget_pred_le rs.tables ℓ
      have h9 := levelBudget_le_zero rs.tables ℓ
      have h10 := levelBudget_le_zero rs.tables (ℓ - 1)
      refine ⟨h2.le, fun g hg => ?_, fun _ => 0, fun _ => ⟨?_, ?_⟩, fun j' => ?_,
        fun _ => ⟨fun _ => rfl, fun g hg => ?_⟩, fun h => absurd ⟨_, _, rfl⟩ h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> exact Nat.zero_le _
      · change (0 : ℚ) ≤ _
        positivity
      · change (0 : ℚ) ≤ _
        positivity
      · have h0 : unitsOf c rs₁ j' = 0 := by
          change rs₁.epochSpent j' * _ = 0
          rw [h3]
          simp
        rw [onBoard_eq_zero_of_spent]
        · change unitsOf c rs₁ j' = 0 + ((0 : ℕ) : ℚ)
          rw [h0]
          simp
        · intro g hg
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · change levelBudget rs.tables ℓ ≤ 2 * min (levelBudget rs.tables ℓ)
            (min (levelBudget rs.tables (ℓ - 1)) (levelBudget rs.tables 0))
          omega
        · change levelBudget rs.tables (ℓ - 1) ≤ 2 * min (levelBudget rs.tables ℓ)
            (min (levelBudget rs.tables (ℓ - 1)) (levelBudget rs.tables 0))
          omega
    · split
      · exact hdone
      · split
        · exact hdone
        · split
          · exact ⟨spendInv_fresh I h3 hnp₁ (fun bl hbl k => by cases hbl; exact h2.le), hcl₁⟩
          · split
            · rename_i pl hb
              exact ⟨spendInv_balanced_fresh I rfl hb h2.le (fun _ h => by cases h) h3, hcl₁⟩
            · exact hdone

/-- **Case 3.** -/
theorem caseThree_spend (hI : I.Valid) {st : ConState} {i t t₀ c : ℕ} {rs : ReqState} {pl : Play}
    (hinv : SpendInvAt I c t₀ rs) (hcl : ClosedOK I rs) (hp : rs.play = some pl)
    (ha : pl.arena = arenaOf c rs.tables)
    (hlim : ∀ g ∈ pl.games, g.ourLimit ≤ levelBudget rs.tables 0)
    (hboards : (pl.games.map BoardGame.board).Nodup) (hstart : pl.start ≤ t) :
    SpendInvAt I c t (caseThree I st i t c rs pl).1 ∧
        ClosedOK I (caseThree I st i t c rs pl).1 := by
  obtain ⟨hs, hspent, P₀, hP, hU, hstk, hns⟩ := hinv.active pl hp
  have hsum : lamOf I c rs t = lamOf I c rs pl.start + oppSpend I pl.arena pl.start t := by
    rw [ha]
    exact oppSpend_add hI _ hs hstart
  have hE : levelBudget pl.arena.tables 0 = levelBudget rs.tables 0 := by
    rw [ha]
    rfl
  have hon : ∀ j, onBoard pl.games j ≤ levelBudget rs.tables 0 := fun j =>
    onBoard_le hboards (fun g hg => (hspent g hg).trans (hlim g hg)) j
  have hstop : (∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ)) →
      SpendInvAt I c t (({ rs with play := none, baseline := none } : ReqState).closeEpoch
        i c t t false) ∧
      ClosedOK I (({ rs with play := none, baseline := none } : ReqState).closeEpoch
        i c t t false) := fun h =>
    ⟨spendInv_fresh I rfl rfl (fun _ h' => by cases h'), closedOK_close I hcl rfl h⟩
  have hnsBound : (¬ ∃ σ b, pl.kind = .stacked σ b) →
      playLimit pl < oppSpend I pl.arena pl.start t →
      ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ) := by
    intro hk hlt j
    have h1 := hns hk
    have h2 : levelBudget rs.tables 0 ≤ lamOf I c rs t := by omega
    have h3 : (levelBudget rs.tables 0 : ℚ) ≤ lamOf I c rs t := by exact_mod_cast h2
    have h4 : (onBoard pl.games j : ℚ) ≤ levelBudget rs.tables 0 := by exact_mod_cast hon j
    rw [hU j]
    linarith [(hP j).2]
  unfold caseThree
  dsimp only
  split_ifs with h1 h2
  · -- Case 3a.
    have hcostS : ∀ S : Finset Str, S ⊆ pl.arena.board →
        (cost pl.arena.w S : ℚ) = trueCost S * 2 ^ (c + maxLen rs.tables + 1) := by
      rw [ha]
      exact fun S hS => cost_eq_trueCost hS
    have hcost : ∀ q ∈ movesOf I st t pl,
        (cost pl.arena.w q.2 : ℚ) = trueCost q.2 * 2 ^ (c + maxLen rs.tables + 1) := by
      intro q hq
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hq
      exact hcostS _ (respond_subset_board I st pl.arena t g _ _)
    refine ⟨⟨hinv.baseGe, fun h => (by cases h), fun pl' hpl' => ?_⟩, hcl⟩
    have hpp : { pl with games := gamesAfter I st t pl } = pl' := Option.some.inj hpl'
    subst hpp
    have hlimit := playLimit_after I st t pl
    refine ⟨hs, fun g' hg' => (gamesAfter_spec I hspent hg').1, P₀, hP, fun j => ?_,
      fun hk => ⟨(hstk hk).1, fun g' hg' => ?_⟩, fun hk => ?_⟩
    · have key := fold_units (w := pl.arena.w) (S := 2 ^ (c + maxLen rs.tables + 1))
        (b := rs.epochSpent j) (j := j) (movesOf I st t pl) hcost
      rw [show (movesOf I st t pl).map (fun q => q.1) = pl.games from map_fst_pair _ _] at key
      have hUj : rs.epochSpent j * 2 ^ (c + maxLen rs.tables + 1) =
          P₀ j + (onBoard pl.games j : ℚ) := hU j
      have hgoal : (movesOf I st t pl).foldr
            (fun q acc => if q.1.board = j then trueCost q.2 + acc else acc) (rs.epochSpent j) *
            2 ^ (c + maxLen rs.tables + 1) =
          P₀ j + (onBoard (gamesAfter I st t pl) j : ℚ) := by
        unfold gamesAfter
        linarith
      exact hgoal
    · obtain ⟨-, g, hg, hl⟩ := gamesAfter_spec I hspent hg'
      rw [hl, hlimit]
      exact (hstk hk).2 g hg
    · change levelBudget rs.tables 0 ≤
        playLimit { pl with games := gamesAfter I st t pl } + lamOf I c rs pl.start
      rw [hlimit]
      exact hns hk
  · split
    · -- Case 3b: knight and bishop.
      rename_i _ σ b hk
      have hst' := hstk ⟨σ, b, hk⟩
      have hlt : playLimit pl < oppSpend I pl.arena pl.start t := not_le.1 h1
      have hUj : ∀ j, unitsOf c rs j ≤ 2 * (lamOf I c rs t : ℚ) ∧
          unitsOf c rs j ≤ (levelBudget rs.tables 0 : ℚ) := by
        intro j
        have h3 := hU j
        rw [hst'.1 j, zero_add] at h3
        have h4 : onBoard pl.games j ≤ 2 * playLimit pl :=
          onBoard_le hboards (fun g hg => (hspent g hg).trans (hst'.2 g hg)) j
        have h5 := hon j
        have h6 : onBoard pl.games j ≤ 2 * lamOf I c rs t := by omega
        rw [h3]
        exact ⟨by exact_mod_cast h6, by exact_mod_cast h5⟩
      split
      · rename_i j₀ _
        refine ⟨⟨hinv.baseGe, fun h => (by cases h), fun pl' hpl' => ?_⟩, hcl⟩
        cases hpl'
        refine ⟨hs.trans hstart, fun g hg => ?_, unitsOf c rs, hUj, fun j => ?_, fun h => ?_,
          fun _ => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> exact Nat.zero_le _
        · rw [onBoard_eq_zero_of_spent]
          · simp
          · intro g hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl <;> rfl
        · obtain ⟨σ', b', hk'⟩ := h
          cases hk'
        · change levelBudget rs.tables 0 ≤
            min (levelBudget pl.arena.tables 0)
              (min (levelBudget pl.arena.tables 0 - oppSpend I pl.arena pl.start t)
                (levelBudget pl.arena.tables 0)) +
              lamOf I c rs t
          omega
      · refine ⟨⟨?_, fun _ j => hUj j, fun pl' hpl' => by cases hpl'⟩, hcl⟩
        intro bl' hbl' k
        cases hbl0 : rs.baseline with
        | none =>
          rw [hbl0] at hbl'
          cases hbl'
        | some bl =>
          rw [hbl0] at hbl'
          cases hbl'
          change rs.epochStart ≤ if k = b then bl.base k else t
          split_ifs
          · exact hinv.baseGe bl hbl0 k
          · exact hs.trans hstart
    · rename_i _ hk
      exact hstop (hnsBound (fun ⟨σ, b, h⟩ => hk σ b h) (not_le.1 h1))
  · split
    · -- Case 3c, from stacked games.
      rename_i _ σ b hk
      have hst' := hstk ⟨σ, b, hk⟩
      exact hstop fun j => by
        have h3 := hU j
        rw [hst'.1 j, zero_add] at h3
        have h5 := hon j
        have h6 : onBoard pl.games j ≤ lamOf I c rs t := by
          have := not_le.1 h2
          omega
        have h7 : (onBoard pl.games j : ℚ) ≤ lamOf I c rs t := by exact_mod_cast h6
        have h8 : (0 : ℚ) ≤ lamOf I c rs t := by positivity
        rw [h3]
        linarith
    · -- Case 3c, from the other games.
      rename_i _ hk
      exact hstop (hnsBound (fun ⟨σ, b, h⟩ => hk σ b h) (not_le.1 h1))

/-- **Case 1.**  What is left uncharged is at most the old starting measure, and we start afresh. -/
theorem caseOne_spend {st : ConState} {i t : ℕ}
    (hc0 : (st.req i).c = none → ∀ j, (st.req i).epochSpent j = 0)
    (hfinal : ∀ c, (st.req i).c = some c →
      WindowBound I ⟨i, c, (st.req i).epochStart, (st.req i).lastVisit, boardOf (st.req i).tables,
        (st.req i).epochSpent, true⟩)
    (hcl : ClosedOK I (st.req i)) :
    ClosedOK I (caseOne st i t).1 ∧
      ∀ c, (caseOne st i t).1.c = some c → SpendInvAt I c t (caseOne st i t).1 := by
  unfold caseOne
  dsimp only
  split
  · rename_i c hc
    refine ⟨fun e he => ?_, fun c' _ => spendInv_fresh I rfl rfl fun _ h => by cases h⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hfinal c hc
    · exact hcl e he
  · rename_i hc
    exact ⟨hcl, fun c' _ => spendInv_fresh I (funext (hc0 hc)) rfl fun _ h => by cases h⟩

/-- A window left open satisfies the bound of a final window. -/
theorem final_of_inv (hI : I.Valid) {i s c : ℕ}
    (hinv : SpendInvAt I c (rsAt I s i).lastVisit (rsAt I s i)) :
    WindowBound I
        ⟨i, c, (rsAt I s i).epochStart, (rsAt I s i).lastVisit, boardOf (rsAt I s i).tables,
      (rsAt I s i).epochSpent, true⟩ := by
  refine windowBound_final I (rs := rsAt I s i) (t := (rsAt I s i).lastVisit) fun j => ?_
  cases hp : (rsAt I s i).play with
  | none =>
    have h := (hinv.idle hp j).1
    have hE : (0 : ℚ) ≤ levelBudget (rsAt I s i).tables 0 := by positivity
    linarith
  | some pl =>
    obtain ⟨hs, hspent, P₀, hP, hU, -, -⟩ := hinv.active pl hp
    obtain ⟨-, -, -, hlim⟩ := (reqWF_rsAt I s i).play pl hp
    have hon : onBoard pl.games j ≤ levelBudget (rsAt I s i).tables 0 :=
      onBoard_le (run_invariant_boards hI pl hp) (fun g hg => (hspent g hg).trans (hlim g hg)) j
    have hon' : (onBoard pl.games j : ℚ) ≤ levelBudget (rsAt I s i).tables 0 := by
      exact_mod_cast hon
    have hstartLe : pl.start ≤ (rsAt I s i).lastVisit := (run_invariant hI s i).startLe pl hp
    have hm : (lamOf I c (rsAt I s i) pl.start : ℚ) ≤
        lamOf I c (rsAt I s i) (rsAt I s i).lastVisit := by
      exact_mod_cast oppSpend_mono_right I hI _ _ hstartLe
    rw [hU j]
    linarith [(hP j).1]

/-- A stage keeps the spending invariants. -/
theorem stepCore_spend (hI : I.Valid) {s : ℕ} (hcl : ClosedOK I (rsAt I s (Nat.unpair s).1))
    (hinv : ∀ c, (rsAt I s (Nat.unpair s).1).c = some c →
      SpendInvAt I c (rsAt I s (Nat.unpair s).1).lastVisit (rsAt I s (Nat.unpair s).1)) :
    ClosedOK I (stepCore I (stateAt I s)).1 ∧
      ∀ c, (stepCore I (stateAt I s)).1.c = some c →
        SpendInvAt I c (s + 1) (stepCore I (stateAt I s)).1 := by
  have hst := stage_stateAt I s
  have hlv := lastVisit_le I s (Nat.unpair s).1
  have hle := (winInv I s (Nat.unpair s).1).opn.le
  cases hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) with
  | true =>
    have hcore : (stepCore I (stateAt I s)).1 =
        (caseOne (stateAt I s) (Nat.unpair s).1 (s + 1)).1 := by
      unfold stepCore
      dsimp only
      rw [hst, hr]
      simp only [ite_true]
    rw [hcore]
    exact caseOne_spend I (fun h j => epochSpent_of_c_none I h j)
      (fun c hc => final_of_inv I hI (hinv c hc)) hcl
  | false =>
    cases hc : (rsAt I s (Nat.unpair s).1).c with
    | none =>
      exfalso
      have hc' : ((stateAt I s).req (Nat.unpair s).1).c = none := hc
      have h1 : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = true := by
        unfold mustReset
        simp [hc']
      rw [hr] at h1
      cases h1
    | some c =>
      have hinvc := hinv c hc
      cases hp : (rsAt I s (Nat.unpair s).1).play with
      | none =>
        have hcore := stepCore_eq_two (I := I) (st := stateAt I s) (c := c)
          (by rw [hst]; exact hr) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
        rw [hst] at hcore
        have hR : (stepCore I (stateAt I s)).1 = (caseTwo I (stateAt I s) (Nat.unpair s).1 (s + 1) c
            (rsAt I s (Nat.unpair s).1)).1 := congrArg Prod.fst hcore
        have hnew := caseTwo_spend I hI (st := stateAt I s) (i := (Nat.unpair s).1) (t := s + 1)
          hinvc hcl hp (by omega) hle
        rw [hR]
        refine ⟨hnew.2, fun c' hc' => ?_⟩
        have hcc : c = c' := Option.some.inj (hc.symm.trans (caseTwo_c.symm.trans hc'))
        subst hcc
        exact hnew.1
      | some pl =>
        have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
          (by rw [hst]; exact hr) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
        rw [hst] at hcore
        have hR : (stepCore I (stateAt I s)).1 =
            (caseThree I (stateAt I s) (Nat.unpair s).1 (s + 1) c
            (rsAt I s (Nat.unpair s).1) pl).1 := congrArg Prod.fst hcore
        obtain ⟨-, -, -, hlim⟩ := (reqWF_rsAt I s (Nat.unpair s).1).play pl hp
        have hstartLe : pl.start ≤ (rsAt I s (Nat.unpair s).1).lastVisit :=
          (run_invariant hI s (Nat.unpair s).1).startLe pl hp
        have hnew := caseThree_spend I hI (st := stateAt I s) (i := (Nat.unpair s).1) (t := s + 1)
          hinvc hcl hp (arena_of_play hc hp) hlim (run_invariant_boards hI pl hp) (by omega)
        rw [hR]
        refine ⟨hnew.2, fun c' hc' => ?_⟩
        have hcc : c = c' := Option.some.inj (hc.symm.trans (caseThree_c.symm.trans hc'))
        subst hcc
        exact hnew.1

/-- **The spending invariants hold along the run.** -/
theorem spend_invariant (hI : I.Valid) (s i : ℕ) :
    ClosedOK I (rsAt I s i) ∧
      ∀ c, (rsAt I s i).c = some c → SpendInvAt I c (rsAt I s i).lastVisit (rsAt I s i) := by
  induction s with
  | zero => exact ⟨fun e he => absurd he List.not_mem_nil, fun c hc => by cases hc⟩
  | succ s ih =>
    by_cases hi : (Nat.unpair s).1 = i
    · subst hi
      obtain ⟨h1, h2⟩ := stepCore_spend I hI ih.1 ih.2
      have hsucc := rsAt_succ_self I s
      refine ⟨?_, fun c hc => ?_⟩
      · rw [hsucc]
        exact fun e he => h1 e he
      · rw [hsucc] at hc ⊢
        have h := h2 c hc
        exact ⟨h.baseGe, h.idle, h.active⟩
    · rw [rsAt_succ_of_ne I (Ne.symm hi)]
      exact ih

/-- **The lost and wasted measure (§4.4).**  In a window we spend at most twice the charged measure,
plus possibly one starting measure if the window was left by a reset or is still open.  This covers
the paper's two cases where we can spend more than the opponent: `G(δ, δ)` against `G(δ/2, δ/2)`,
and knight and bishop. -/
theorem epoch_spent_le (hI : I.Valid) {s : ℕ} {e : Epoch} (he : e ∈ allEpochs I s) (j : Fin 3) :
    e.spent j ≤ 2 * trueCost (charged I e) + if e.final then 1 / 2 ^ e.c else 0 := by
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 he
  obtain ⟨hcl, hinv⟩ := spend_invariant I hI s i
  rcases List.mem_append.1 hi with h | h
  · unfold openEpoch at h
    split at h
    · rename_i c hc
      rcases List.mem_singleton.1 h with rfl
      exact final_of_inv I hI (hinv c hc) j
    · cases h
  · exact hcl e h j

/-- The filter of the windows of a requirement, by values of `c`. -/
theorem filter_map_epochs (s i : ℕ) :
    ((openEpoch I s i ++ (rsAt I s i).closed).filter fun e => e.final).map Epoch.c =
      finalsOf (rsAt I s i) := by
  unfold openEpoch finalsOf
  cases hc : (rsAt I s i).c <;> simp

/-- **The choice of `ε` (§4.3, Case 1).**  The values of `c` of the windows left by a reset or still
open are distinct and at least `7`. -/
theorem final_c_nodup (s : ℕ) :
    (((allEpochs I s).filter fun e => e.final).map Epoch.c).Nodup ∧
      ∀ e ∈ (allEpochs I s).filter (fun e => e.final), 7 ≤ e.c := by
  obtain ⟨h1, h2⟩ := finals_invariant I s
  have hgen : ∀ l : List ℕ, (((l.flatMap fun i => openEpoch I s i ++ (rsAt I s i).closed).filter
      fun e => e.final).map Epoch.c) = l.flatMap fun i => finalsOf (rsAt I s i) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.filter_append, List.map_append, ih]
      rw [← filter_map_epochs I s a]
      simp only [List.filter_append, List.map_append]
  constructor
  · unfold allEpochs
    rw [hgen]
    refine List.nodup_flatMap.2 ⟨fun i _ => (h1 i).1, ?_⟩
    refine (List.nodup_range).imp fun {a b} hne => ?_
    exact h2 a b hne
  · intro e he
    have hmem : e.c ∈ ((allEpochs I s).filter fun e => e.final).map Epoch.c :=
      List.mem_map.2 ⟨e, he, rfl⟩
    unfold allEpochs at hmem
    rw [hgen] at hmem
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hmem
    exact (h1 i).2.2 _ hi

/-- Charged strings are strings compressed by the opponent. -/
theorem charged_compressed (e : Epoch) : ∀ τ ∈ charged I e, ∃ s, I.opp s τ = true := by
  intro τ hτ
  have := (mem_filter.1 hτ).2
  simp only [Bool.and_eq_true] at this
  exact ⟨e.stop, this.1⟩

/-- The total charged measure of pairwise disjoint windows is at most the opponent's budget. -/
theorem sum_charged_le (hI : I.Valid) (l : List Epoch)
    (hl : l.Pairwise fun e e' => Disjoint (charged I e) (charged I e')) :
    (l.map fun e => trueCost (charged I e)).sum ≤ 1 / 32 := by
  classical
  have key : ∀ l : List Epoch, (l.Pairwise fun e e' => Disjoint (charged I e) (charged I e')) →
      (l.map fun e => trueCost (charged I e)).sum =
        trueCost (l.foldr (fun e acc => charged I e ∪ acc) ∅) ∧
      ∀ τ ∈ l.foldr (fun e acc => charged I e ∪ acc) ∅, ∃ e ∈ l, τ ∈ charged I e := by
    intro l
    induction l with
    | nil => simp [trueCost]
    | cons e l ih =>
      intro hp
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hp
      obtain ⟨hsum, hmem⟩ := ih htail
      refine ⟨?_, fun τ hτ => ?_⟩
      · simp only [List.map_cons, List.sum_cons, List.foldr_cons, hsum]
        have hd : Disjoint (charged I e) (l.foldr (fun e acc => charged I e ∪ acc) ∅) := by
          refine disjoint_left.2 fun τ h h' => ?_
          obtain ⟨e', he', hτ'⟩ := hmem τ h'
          exact disjoint_left.1 (hhead e' he') h hτ'
        exact (sum_union hd).symm
      · simp only [List.foldr_cons, mem_union] at hτ
        rcases hτ with h | h
        · exact ⟨e, List.mem_cons_self, h⟩
        · obtain ⟨e', he', hτ'⟩ := hmem τ h
          exact ⟨e', List.mem_cons_of_mem _ he', hτ'⟩
  obtain ⟨hsum, hmem⟩ := key l hl
  rw [hsum]
  refine hI.opp_budget _ fun τ hτ => ?_
  obtain ⟨e, -, hτe⟩ := hmem τ hτ
  exact charged_compressed I e τ hτe

/-- A duplicate-free list of naturals at least `7` has `∑ 2 ^ (-c) ≤ 1/64`. -/
theorem sum_pow_le_of_nodup {l : List ℕ} (hl : l.Nodup) (h7 : ∀ c ∈ l, 7 ≤ c) :
    (l.map fun c => (1 : ℚ) / 2 ^ c).sum ≤ 1 / 64 := by
  classical
  have hrange : ∀ M : ℕ, ∑ c ∈ range M, (1 : ℚ) / 2 ^ (c + 7) ≤ 1 / 64 := by
    intro M
    have hexact : ∀ M : ℕ, ∑ c ∈ range M, (1 : ℚ) / 2 ^ (c + 7) = 1 / 64 - 1 / 2 ^ (M + 6) := by
      intro M
      induction M with
      | zero => norm_num
      | succ M ih =>
        rw [sum_range_succ, ih]
        field_simp
        ring
    rw [hexact]
    have : (0 : ℚ) ≤ 1 / 2 ^ (M + 6) := by positivity
    linarith
  obtain ⟨M, hM⟩ : ∃ M, ∀ c ∈ l, c < M + 7 := by
    refine ⟨l.foldr max 0 + 1, fun c hc => ?_⟩
    have : c ≤ l.foldr max 0 := by
      clear hl h7
      induction l with
      | nil => simp at hc
      | cons a l ih =>
        rcases List.mem_cons.1 hc with rfl | h
        · exact le_max_left _ _
        · exact (ih h).trans (le_max_right _ _)
    omega
  have hsum : (l.map fun c => (1 : ℚ) / 2 ^ c).sum = ∑ c ∈ l.toFinset, (1 : ℚ) / 2 ^ c :=
    (List.sum_toFinset _ hl).symm
  rw [hsum]
  have himage : l.toFinset ⊆ (range M).image (· + 7) := by
    intro c hc
    have hc' := List.mem_toFinset.1 hc
    have h1 := h7 c hc'
    have h2 := hM c hc'
    exact mem_image.2 ⟨c - 7, mem_range.2 (by omega), by omega⟩
  calc ∑ c ∈ l.toFinset, (1 : ℚ) / 2 ^ c
      ≤ ∑ c ∈ (range M).image (· + 7), (1 : ℚ) / 2 ^ c :=
        sum_le_sum_of_subset_of_nonneg himage fun _ _ _ => by positivity
    _ = ∑ c ∈ range M, (1 : ℚ) / 2 ^ (c + 7) :=
        sum_image fun a _ b _ h => by simpa using h
    _ ≤ 1 / 64 := hrange M

/-- Summing the bound of the windows. -/
theorem sum_spent_le (j : Fin 3) (l : List Epoch)
    (hbound : ∀ e ∈ l, e.spent j ≤
      2 * trueCost (charged I e) + if e.final then (1 : ℚ) / 2 ^ e.c else 0) :
    (l.map fun e => e.spent j).sum ≤
      2 * (l.map fun e => trueCost (charged I e)).sum +
        (l.map fun e => if e.final then (1 : ℚ) / 2 ^ e.c else 0).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h := hbound e List.mem_cons_self
    have h' := ih fun e' he' => hbound e' (List.mem_cons_of_mem _ he')
    linarith

/-- The uncharged part, as a sum over the values of `c`. -/
theorem sum_final_eq (l : List Epoch) :
    (l.map fun e => if e.final then (1 : ℚ) / 2 ^ e.c else 0).sum =
      (((l.filter fun e => e.final).map Epoch.c).map fun c => (1 : ℚ) / 2 ^ c).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases he : e.final <;> simp

/-- **Lemma 4.4.**  We do not exceed the measure we are allowed to use.  In the paper's
normalization the bound is `1/4 + 1/4` against `7/8`; here, with `min (K_V + 5, F + 3)`, it is
`1/32 + 1/16` against `3/32` (so that `8` times it, plus `1/4` for the default of `F`, is at most
`1`). -/
theorem lemma_4_4 (hI : I.Valid) (s : ℕ) (j : Fin 3) : trueCost (oursAt I j s) ≤ 3 / 32 := by
  have h1 := ours_cost_le_epochs I s j
  have hstep := sum_spent_le I j (allEpochs I s) fun e he => epoch_spent_le I hI he j
  have hfinal : ((allEpochs I s).map fun e => if e.final then (1 : ℚ) / 2 ^ e.c else 0).sum ≤
      1 / 64 := by
    obtain ⟨hnodup, h7⟩ := final_c_nodup I s
    rw [sum_final_eq]
    refine sum_pow_le_of_nodup hnodup fun c hc => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact h7 e he
  have hcharged := sum_charged_le I hI _ (charged_pairwise_disjoint I hI s)
  linarith

end Kolmogorov.RandomStrings.TTMeet
