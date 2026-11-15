/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Requirements

/-!
# A game that never stops wins

The ingredients of `permanent_disagreement` (`Verification.lean`): if a play runs forever, two
boards disagree on some table.

* `stepCore_eq_two`, `stepCore_eq_three`: a stage without a reset is a visit in Case 2 or Case 3.
* `current_game`: at a visit, the games are winning at the current position (the invariant at the
  last visit, transferred over the opponent's moves).
* `exists_stable_position`: positions are antitone, so eventually constant.
* `mem_finalR_iff_of_stable`: an eventually constant position is the final oracle on the board.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {I : Input}

/-- A stage in Case 2. -/
theorem stepCore_eq_two {st : ConState} {c : ℕ}
    (hr : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) = false)
    (hc : (st.req (Nat.unpair st.stage).1).c = some c)
    (hp : (st.req (Nat.unpair st.stage).1).play = none) :
    stepCore I st =
      ((caseTwo I st (Nat.unpair st.stage).1 (st.stage + 1) c (st.req (Nat.unpair st.stage).1)).1,
        st.ours, st.nextC,
        (caseTwo I st (Nat.unpair st.stage).1 (st.stage + 1) c
          (st.req (Nat.unpair st.stage).1)).2) := by
  unfold stepCore
  dsimp only
  rw [hr]
  simp only [Bool.false_eq_true, ite_false, hc, hp]

/-- A stage in Case 3. -/
theorem stepCore_eq_three {st : ConState} {c : ℕ} {pl : Play}
    (hr : mustReset I st (Nat.unpair st.stage).1 (Nat.unpair st.stage).2 (st.stage + 1) = false)
    (hc : (st.req (Nat.unpair st.stage).1).c = some c)
    (hp : (st.req (Nat.unpair st.stage).1).play = some pl) :
    stepCore I st =
      ((caseThree I st (Nat.unpair st.stage).1 (st.stage + 1) c
          (st.req (Nat.unpair st.stage).1) pl).1,
        (caseThree I st (Nat.unpair st.stage).1 (st.stage + 1) c
          (st.req (Nat.unpair st.stage).1) pl).2.1,
        st.nextC,
        (caseThree I st (Nat.unpair st.stage).1 (st.stage + 1) c
          (st.req (Nat.unpair st.stage).1) pl).2.2) := by
  unfold stepCore
  dsimp only
  rw [hr]
  simp only [Bool.false_eq_true, ite_false, hc, hp]

/-- A reset removes the play. -/
theorem play_eq_none_of_reset {s : ℕ}
    (hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = true) :
    (rsAt I (s + 1) (Nat.unpair s).1).play = none := by
  rw [rsAt_succ_self]
  change (stepCore I (stateAt I s)).1.play = none
  unfold stepCore
  dsimp only
  rw [stage_stateAt, hr]
  simp only [ite_true]
  exact (caseOne_spec ((reqWF_rsAt I s _).mono (Nat.le_succ s))).2.1

/-- A play that survives a visit with the same start: no reset, and within the limit. -/
theorem visit_of_permanent (hI : I.Valid) {s : ℕ} {pl pl' : Play}
    (hp : (rsAt I s (Nat.unpair s).1).play = some pl)
    (hp' : (rsAt I (s + 1) (Nat.unpair s).1).play = some pl') (hstart : pl.start = pl'.start) :
    mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = false ∧
      oppSpend I pl.arena pl.start (s + 1) ≤
        pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0) := by
  set i := (Nat.unpair s).1 with hidef
  have hres : mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) = false := by
    cases hr : mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) with
    | false => rfl
    | true =>
      have := play_eq_none_of_reset (I := I) hr
      rw [hp'] at this
      cases this
  refine ⟨hres, ?_⟩
  by_contra hl
  obtain ⟨c, hc, -, -⟩ := (reqWF_rsAt I s i).play pl hp
  have hst := stage_stateAt I s
  have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
    (by rw [hst]; exact hres) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
  rw [hst] at hcore
  have hfield : (rsAt I (s + 1) i).play = (stepCore I (stateAt I s)).1.play := by
    rw [rsAt_succ_self]
  rw [hfield, hcore] at hp'
  dsimp only at hp'
  have hle := (run_invariant hI s i).startLe pl hp
  have hlast := lastVisit_le I s i
  unfold caseThree at hp'
  dsimp only at hp'
  rw [ite_eq_right hl] at hp'
  split at hp'
  · split_ifs at hp'
    · split at hp'
      · cases hp'
        have : pl.start = s + 1 := hstart
        omega
      · cases hp'
    · cases hp'
  · cases hp'

/-- Within the limit, the play continues with the same shape. -/
theorem play_after_limit {s c : ℕ} {pl : Play}
    (hres : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = false)
    (hc : (rsAt I s (Nat.unpair s).1).c = some c)
    (hp : (rsAt I s (Nat.unpair s).1).play = some pl)
    (hl : oppSpend I pl.arena pl.start (s + 1) ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)) :
    (rsAt I (s + 1) (Nat.unpair s).1).play = some { pl with games :=
      (pl.games.map fun g => (g, respond pl.arena g
        ((stateAt I s).positionList I pl.arena (s + 1) g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent))).map fun q =>
          { q.1 with spent := q.1.spent + cost pl.arena.w q.2 } } := by
  have hst := stage_stateAt I s
  have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
    (by rw [hst]; exact hres) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
  rw [hst] at hcore
  have hfield : (rsAt I (s + 1) (Nat.unpair s).1).play = (stepCore I (stateAt I s)).1.play := by
    rw [rsAt_succ_self]
  rw [hfield, hcore]
  dsimp only
  unfold caseThree
  dsimp only
  rw [ite_eq_left hl]

/-- **At a visit, the games are winning at the current position.** -/
theorem current_game (hI : I.Valid) {s : ℕ} {pl : Play}
    (hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = false)
    (hp : (rsAt I s (Nat.unpair s).1).play = some pl) {g : BoardGame} (hg : g ∈ pl.games)
    (hle : oppSpend I pl.arena pl.start (s + 1) ≤ g.oppLimit) :
    pl.arena.Forces g.target ((stateAt I s).position I pl.arena (s + 1) g.board)
      (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent) := by
  set i := (Nat.unpair s).1 with hidef
  obtain ⟨c, hc, ha, -⟩ := (reqWF_rsAt I s i).play pl hp
  have hprev : ∃ u, u < s ∧ (Nat.unpair u).1 = i ∧ (rsAt I s i).lastVisit = u + 1 ∧
      rsAt I s i = rsAt I (u + 1) i ∧ ∀ s'', u < s'' → s'' < s → (Nat.unpair s'').1 ≠ i := by
    rcases visited_spec I s i with h0 | h1
    · exfalso
      rw [h0] at hc
      cases hc
    · exact h1
  obtain ⟨u, hus, hui, hlast, hsame, hbetween⟩ := hprev
  have hold : VisitInv I (stateAt I (u + 1)) (u + 1) (rsAt I s i) := by
    have := run_invariant hI s i
    unfold RunInv at this
    rwa [hlast] at this
  have hstart := hold.startLe pl hp
  obtain ⟨-, hF⟩ := hold.game pl hp g hg
  have hadd := oppSpend_add hI pl.arena hstart (show u + 1 ≤ s + 1 by omega)
  have hpos := position_between_visits (c := c) hI hui hus hbetween hr
    (show (rsAt I (u + 1) i).tables = (rsAt I s i).tables by rw [← hsame]) g.board
  rw [← ha] at hpos
  exact forces_transfer hpos hF (by omega)

/-- Positions shrink along the run. -/
theorem position_antitone (hI : I.Valid) (ar : Arena) (j : Fin 3) {t t' : ℕ} (h : t ≤ t') :
    (stateAt I t').position I ar t' j ⊆ (stateAt I t).position I ar t j := by
  intro z hz
  obtain ⟨hb, ho, hn⟩ := mem_position.1 hz
  refine mem_position.2 ⟨hb, ?_, fun hmem => hn (oursAt_mono I j h hmem)⟩
  cases ho' : I.opp t z with
  | false => rfl
  | true =>
    have := hI.opp_mono h ho'
    rw [ho] at this
    cases this

/-- An antitone sequence of finite sets is eventually constant. -/
theorem exists_stable_of_antitone {α : Type*} (f : ℕ → Finset α)
    (hf : ∀ {t t' : ℕ}, t ≤ t' → f t' ⊆ f t) (s₀ : ℕ) :
    ∃ s₁ ≥ s₀, ∀ t ≥ s₁, f t = f s₁ := by
  classical
  induction hn : (f s₀).card using Nat.strong_induction_on generalizing s₀ with
  | _ n ih =>
    by_cases hstable : ∀ t ≥ s₀, f t = f s₀
    · exact ⟨s₀, le_rfl, hstable⟩
    · simp only [not_forall] at hstable
      obtain ⟨t, ht, hne⟩ := hstable
      have hsub : f t ⊂ f s₀ := Finset.ssubset_iff_subset_ne.2 ⟨hf ht, hne⟩
      obtain ⟨s₁, hs₁, h⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) t rfl
      exact ⟨s₁, ht.trans hs₁, h⟩

/-- **Positions are eventually constant, on all boards.** -/
theorem exists_stable_position (hI : I.Valid) (ar : Arena) (s₀ : ℕ) :
    ∃ s₁ ≥ s₀, ∀ t ≥ s₁, ∀ j, (stateAt I t).position I ar t j =
      (stateAt I s₁).position I ar s₁ j := by
  obtain ⟨s₁, h₁, H₁⟩ := exists_stable_of_antitone
    (fun t => (stateAt I t).position I ar t 0) (fun h => position_antitone hI ar 0 h) s₀
  obtain ⟨s₂, h₂, H₂⟩ := exists_stable_of_antitone
    (fun t => (stateAt I t).position I ar t 1) (fun h => position_antitone hI ar 1 h) s₁
  obtain ⟨s₃, h₃, H₃⟩ := exists_stable_of_antitone
    (fun t => (stateAt I t).position I ar t 2) (fun h => position_antitone hI ar 2 h) s₂
  refine ⟨s₃, h₁.trans (h₂.trans h₃), fun t ht j => ?_⟩
  fin_cases j
  · exact (H₁ t (h₂.trans (h₃.trans ht))).trans (H₁ s₃ (h₂.trans h₃)).symm
  · exact (H₂ t (h₃.trans ht)).trans (H₂ s₃ h₃).symm
  · exact H₃ t ht

/-- A stable position is the final oracle on the board. -/
theorem mem_finalR_iff_of_stable (hI : I.Valid) {ar : Arena} {s₁ : ℕ} {j : Fin 3}
    (h : ∀ t ≥ s₁, (stateAt I t).position I ar t j = (stateAt I s₁).position I ar s₁ j)
    {z : Str} (hz : z ∈ ar.board) :
    z ∈ (stateAt I s₁).position I ar s₁ j ↔ z ∈ finalR I j := by
  constructor
  · intro hmem
    refine ⟨fun s => ?_, ?_⟩
    · have h1 := (h (max s s₁) (le_max_right _ _)).symm ▸ hmem
      have h2 := (mem_position.1 h1).2.1
      cases h3 : I.opp s z with
      | false => rfl
      | true =>
        have := hI.opp_mono (le_max_left s s₁) h3
        rw [h2] at this
        cases this
    · rintro ⟨s, hs⟩
      have h1 := (h (max s s₁) (le_max_right _ _)).symm ▸ hmem
      exact (mem_position.1 h1).2.2 (oursAt_mono I j (le_max_left s s₁) hs)
  · rintro ⟨h1, h2⟩
    exact mem_position.2 ⟨hz, h1 s₁, fun hmem => h2 ⟨s₁, hmem⟩⟩

/-- The value of a table on a stable position is its value on the final oracle. -/
theorem value_stable_eq (hI : I.Valid) {ar : Arena} {s₁ : ℕ} {j : Fin 3}
    (h : ∀ t ≥ s₁, (stateAt I t).position I ar t j = (stateAt I s₁).position I ar s₁ j)
    {tt : TTable} (htt : tt ∈ ar.tables) :
    (tt.evalB fun z => decide (z ∈ (stateAt I s₁).position I ar s₁ j)) =
      tt.evalB (chi (finalR I j)) := by
  refine TTable.evalB_congr fun z hz => ?_
  have hb : z ∈ ar.board := Arena.mem_board.2 ⟨tt, htt, hz⟩
  have := mem_finalR_iff_of_stable hI h hb
  rw [Bool.eq_iff_iff, decide_eq_true_iff, chi_eq_true]
  exact this

/-- A nonempty move at a stable position is impossible, so the outcome is on target. -/
theorem target_of_stable (hI : I.Valid) {s s₁ : ℕ} {pl : Play}
    (hs : s₁ ≤ s) (hstable : ∀ t ≥ s₁, ∀ j, (stateAt I t).position I pl.arena t j =
      (stateAt I s₁).position I pl.arena s₁ j)
    (hr : mustReset I (stateAt I s) (Nat.unpair s).1 (Nat.unpair s).2 (s + 1) = false)
    (hp : (rsAt I s (Nat.unpair s).1).play = some pl)
    (hl : oppSpend I pl.arena pl.start (s + 1) ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0))
    {g : BoardGame} (hg : g ∈ pl.games) :
    respond pl.arena g ((stateAt I s).positionList I pl.arena (s + 1) g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent) = ∅ ∧
      pl.arena.value ((stateAt I s₁).position I pl.arena s₁ g.board) ∈ g.target := by
  set i := (Nat.unpair s).1 with hidef
  obtain ⟨c, hc, -, -⟩ := (reqWF_rsAt I s i).play pl hp
  have hlim : oppSpend I pl.arena pl.start (s + 1) ≤ g.oppLimit := hl.trans (foldr_min_le hg)
  have hF := current_game hI hr hp hg hlim
  -- The position before the move.
  set A := (stateAt I s).position I pl.arena (s + 1) g.board with hA
  have hA₁ : A ⊆ (stateAt I s).position I pl.arena s g.board := by
    intro z hz
    obtain ⟨hb, ho, hn⟩ := mem_position.1 hz
    refine mem_position.2 ⟨hb, ?_, hn⟩
    cases ho' : I.opp s z with
    | false => rfl
    | true =>
      have := hI.opp_mono (Nat.le_succ s) ho'
      rw [ho] at this
      cases this
  -- The position after the move.
  have hboards := (run_invariant_boards hI (s := s) (i := i) pl hp)
  have hours : (stateAt I (s + 1)).ours g.board =
      respond pl.arena g ((stateAt I s).positionList I pl.arena (s + 1) g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent) ∪
        (stateAt I s).ours g.board := by
    have hst := stage_stateAt I s
    have hcore := stepCore_eq_three (I := I) (st := stateAt I s) (c := c) (pl := pl)
      (by rw [hst]; exact hr) (by rw [hst]; exact hc) (by rw [hst]; exact hp)
    change (stepCore I (stateAt I s)).2.1 g.board = _
    rw [hcore]
    dsimp only
    rw [hst]
    unfold caseThree
    dsimp only
    rw [ite_eq_left hl]
    exact fold_board_eq (mv := fun g => respond pl.arena g
      ((stateAt I s).positionList I pl.arena (s + 1) g.board)
      (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent)) _ hboards hg
  have hA₂ : (stateAt I (s + 1)).position I pl.arena (s + 1) g.board = A \ respond pl.arena g
      ((stateAt I s).positionList I pl.arena (s + 1) g.board)
      (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent) :=
    position_of_union hours
  have hP₀ := hstable s hs g.board
  have hP₁ := hstable (s + 1) (by omega) g.board
  rcases respond_spec (La := (stateAt I s).positionList I pl.arena (s + 1) g.board) hF with
    ⟨hem, hval, -⟩ | ⟨hne, -⟩
  · -- A pass: the outcome is on target.
    have hAeq : A = (stateAt I s₁).position I pl.arena s₁ g.board := by
      refine Finset.Subset.antisymm (hP₀ ▸ hA₁) ?_
      rw [← hP₁]
      intro z hz
      rw [hA₂] at hz
      exact (mem_sdiff.1 hz).1
    rw [← hAeq]
    exact ⟨hem, hval⟩
  · -- A nonempty move would shrink the position.
    exfalso
    obtain ⟨τ, hτ⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hτA : τ ∈ A := (respond_legal _ _ _ _ _).1 hτ
    have h1 : τ ∈ (stateAt I s₁).position I pl.arena s₁ g.board := by
      rw [← hP₀]
      exact hA₁ hτA
    rw [← hP₁, hA₂] at h1
    exact (mem_sdiff.1 h1).2 hτ

end Kolmogorov.RandomStrings.TTMeet
