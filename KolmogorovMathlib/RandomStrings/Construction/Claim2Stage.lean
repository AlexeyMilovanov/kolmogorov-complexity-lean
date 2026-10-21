/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Evolution
import KolmogorovMathlib.RandomStrings.Construction.LiveInv

/-!
# Claim 2, limit lemmas: one stage seen from a requirement

A stage processes `R_1, …, R_s` in order; until some requirement acts, the processed requirements
only charge `K` on their own record, and the first acting requirement changes its own record and
destroys the lower ones.  The module follows the stage requirement by requirement, the game of `e`
when `e` is processed, and the values.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! ### Claim 2, limit lemmas: one stage seen from a requirement

Helper lemmas for `inj_const_of_lower`, `game_eventually_exists` and
`game_eventually_const_of_exists`.  A stage processes `R_1, …, R_s` in order; until some
requirement acts (flag `true`), the processed requirements only charge `K` on their own record
(`lim_processReq_nonact`); the first acting requirement `a` changes its own record and destroys the
games of all `e' > a` (`lim_processReq_act`); afterwards nothing changes (`lim_processReq_of_snd`).
`lim_stage_cases` sums this up for one requirement `e`. -/

/-- `lim_processReq_of_snd` states that processing a requirement with flag `true`
    returns the same state. -/
theorem lim_processReq_of_snd (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) (h : p.2 = true) : processReq A Γ σ₀ e p = p := by
  unfold processReq
  rw [ite_eq_left h]

/-- `lim_processReq_false_none` states that processing a requirement with a `none`
    game starts the game. -/
theorem lim_processReq_false_none (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (τ : CState) (h : τ.game e = none) :
    processReq A Γ σ₀ e (τ, false) = startGame A Γ e τ := by
  simp only [processReq, h, Bool.false_eq_true, ↓reduceIte]

/-- `lim_processReq_false_some` states that processing a requirement with a `some`
    game processes the game. -/
theorem lim_processReq_false_some (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (τ : CState) (g : BitString × Finset BitString × ℕ × GState) (h : τ.game e = some g) :
    processReq A Γ σ₀ e (τ, false) = processGame A Γ σ₀ e g τ := by
  simp only [processReq, h, Bool.false_eq_true, ↓reduceIte]

/-- `lim_startGame_none` states that if there is no witness, starting the game
    returns the initial state with a `false` flag. -/
theorem lim_startGame_none (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (e : ℕ) (τ : CState)
    (h : chooseWitness A Γ τ e = none) : startGame A Γ e τ = (τ, false) := by
  unfold startGame
  rw [h]

/-- `lim_startGame_some` shows that `startGame` evaluates to `startOn`
    when a witness is available. -/
theorem lim_startGame_some (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (e : ℕ)
    (τ : CState) (x : BitString) (h : chooseWitness A Γ τ e = some x) :
    startGame A Γ e τ = startOn A Γ e τ x := by
  unfold startGame
  rw [h]

section

omit [Family]

/-- `lim_ourReply_subset` shows that `ourReply` is bounded between the state's
    elements and the union with the game data. -/
theorem lim_ourReply_subset (d : GameData) (we : Bool) (st : GState) :
    st.S ⊆ ourReply d we st ∧ ourReply d we st ⊆ st.S ∪ d.X := by
  classical
  unfold ourReply
  split
  · next h =>
    have hs := (Nat.find_spec h).1
    exact ⟨hs.1, hs.2.1.trans Finset.subset_union_right⟩
  · exact ⟨subset_rfl, Finset.subset_union_left⟩

/-- `lim_charge_zero` states that charging zero leaves the game state unchanged. -/
theorem lim_charge_zero (st : GState) : st.charge 0 = st := by
  cases st with
  | mk S y n t => cases t <;> simp [GState.charge]

/-- `lim_moverScore_charge` states that charging a cost increases the mover score
    by that cost. -/
theorem lim_moverScore_charge (st : GState) (c : ℝ) :
    (st.charge c).moverScore = st.moverScore + c := by
  cases st with
  | mk S y n t => cases t <;> simp [GState.charge, GState.moverScore]

/-- `lim_S_charge` states that charging a cost leaves the set `S` unchanged. -/
theorem lim_S_charge (st : GState) (c : ℝ) : (st.charge c).S = st.S := by
  cases st with
  | mk S y n t => cases t <;> simp [GState.charge]

/-- `lim_moverScore_applyMove_kMove` states that applying a `kMove` updates
    the mover score by the specified cost. -/
theorem lim_moverScore_applyMove_kMove (d : GameData) (st : GState) (S' R : Finset BitString)
    (c : ℝ) : (applyMove d (st.kMove S' c) R).moverScore = st.moverScore + c := by
  cases st with
  | mk S y n t => cases t <;> simp [applyMove, GState.kMove, GState.charge, GState.moverScore]

/-- `lim_moverScore_applyMove_firstState` states that the mover score of the
    first state applied is zero. -/
theorem lim_moverScore_applyMove_firstState (d : GameData) (we : Bool) (R : Finset BitString) :
    (applyMove d (firstState d we) R).moverScore = 0 := by
  cases we <;> simp [firstState, applyMove, GState.init, GState.moverScore, moveCost_self]

end

/-- Processing `e'` does not touch the games of `e < e'`. -/
theorem lim_processReq_game_of_lt (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState)
    (e e' : ℕ) (p : CState × Bool) (h : e < e') :
    (processReq A Γ σ₀ e' p).1.game e = p.1.game e := by
  have hne : e ≠ e' := Nat.ne_of_lt h
  have hlt : ¬ e' < e := Nat.not_lt.2 h.le
  unfold processReq
  split
  · rfl
  · split
    · unfold startGame
      split
      · rfl
      · simp [startOn, injure, applyFlips, setGame, hlt, Function.update_of_ne hne]
    · unfold processGame
      split_ifs <;> simp [injure, destroy, applyFlips, setGame, hlt, Function.update_of_ne hne]

/-- Processing `e'` does not touch the injury counters of `e ≤ e'`. -/
theorem lim_processReq_inj_of_le (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState)
    (e e' : ℕ) (p : CState × Bool) (h : e ≤ e') :
    (processReq A Γ σ₀ e' p).1.inj e = p.1.inj e := by
  have hlt : ¬ e' < e := Nat.not_lt.2 h
  unfold processReq
  split
  · rfl
  · split
    · unfold startGame
      split
      · rfl
      · simp [startOn, injure, applyFlips, setGame, hlt]
    · unfold processGame
      split_ifs <;> simp [injure, destroy, applyFlips, setGame, hlt]

/-- A requirement that does not act only changes its own record. -/
theorem lim_processReq_nonact (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) (h : (processReq A Γ σ₀ e p).2 = false) :
    p.2 = false ∧ (processReq A Γ σ₀ e p).1.inj = p.1.inj ∧
      (processReq A Γ σ₀ e p).1.Fstar = p.1.Fstar ∧
      (processReq A Γ σ₀ e p).1.Kstar = p.1.Kstar ∧
      ∀ e', e' ≠ e → (processReq A Γ σ₀ e p).1.game e' = p.1.game e' := by
  obtain ⟨τ, b⟩ := p
  cases b with
  | true => rw [lim_processReq_of_snd A Γ σ₀ e _ rfl] at h; exact absurd h (by simp)
  | false =>
    refine ⟨rfl, ?_⟩
    cases hg : τ.game e with
    | none =>
      rw [lim_processReq_false_none A Γ σ₀ e τ hg] at h ⊢
      cases hc : chooseWitness A Γ τ e with
      | none => rw [lim_startGame_none A Γ e τ hc]; exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
      | some x => rw [lim_startGame_some A Γ e τ x hc] at h; simp [startOn] at h
    | some g =>
      rw [lim_processReq_false_some A Γ σ₀ e τ g hg] at h ⊢
      revert h
      unfold processGame
      split_ifs with h1 h2
      · intro h; simp at h
      · intro _
        refine ⟨rfl, rfl, rfl, fun e' he' => ?_⟩
        simp [setGame, Function.update_of_ne he']
      · intro h; simp at h

/-- The first acting requirement changes its own record and destroys the games of lower
priority. -/
theorem lim_processReq_act (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) (hp : p.2 = false) (h : (processReq A Γ σ₀ e p).2 = true) :
    (processReq A Γ σ₀ e p).1.game e ≠ p.1.game e ∧
      ∀ e', e < e' → (processReq A Γ σ₀ e p).1.game e' = none := by
  obtain ⟨τ, b⟩ := p
  simp only at hp
  subst hp
  cases hg : τ.game e with
  | none =>
    rw [lim_processReq_false_none A Γ σ₀ e τ hg] at h ⊢
    cases hc : chooseWitness A Γ τ e with
    | none => rw [lim_startGame_none A Γ e τ hc] at h; simp at h
    | some x =>
      rw [lim_startGame_some A Γ e τ x hc]
      refine ⟨?_, fun e' he' => ?_⟩
      · simp [startOn, injure, applyFlips, setGame]
      · simp [startOn, injure, applyFlips, setGame, he']
  | some g =>
    rw [lim_processReq_false_some A Γ σ₀ e τ g hg] at h ⊢
    revert h
    unfold processGame
    split_ifs with h1 h2
    · intro _
      refine ⟨?_, fun e' he' => ?_⟩
      · simp [injure, destroy]
      · simp [injure, destroy, he']
    · intro h; simp at h
    · intro _
      refine ⟨?_, fun e' he' => ?_⟩
      · simp only [injure, applyFlips, setGame, lt_irrefl, ite_false, Function.update_self,
          ne_eq, Option.some.injEq]
        intro heq
        apply h2
        have hS := congrArg (fun r => r.2.2.2.S) heq
        have hR : ourReply (curGame A Γ τ e g) (!g.2.2.2.yesTurn)
            (g.2.2.2.kMove (g.2.2.2.S ∪ flipped τ g.2.1) (kCost σ₀ τ g.2.1)) = g.2.2.2.S := hS
        have hsub := (lim_ourReply_subset (curGame A Γ τ e g) (!g.2.2.2.yesTurn)
          (g.2.2.2.kMove (g.2.2.2.S ∪ flipped τ g.2.1) (kCost σ₀ τ g.2.1))).1
        rw [hR] at hsub
        exact Finset.Subset.antisymm hsub Finset.subset_union_left
      · simp [injure, applyFlips, setGame, he']

/-! #### The stage, requirement by requirement -/

/-- `lim_foldl_range_succ` gives the recursive unfolding of folding over `List.range (n + 1)`. -/
theorem lim_foldl_range_succ (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState)
    (p₀ : CState × Bool) (k : ℕ) :
    (List.range (k + 1)).foldl (fun p e => processReq A Γ σ₀ (e + 1) p) p₀ =
      processReq A Γ σ₀ (k + 1)
        ((List.range k).foldl (fun p e => processReq A Γ σ₀ (e + 1) p) p₀) := by
  rw [List.range_succ, List.foldl_append]
  rfl

/-- Once some requirement has acted, the stage does not change any more. -/
theorem lim_accR_persist {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ : CState}
    {F : ℕ → CState × Bool} (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) {k : ℕ}
    (hk : (F k).2 = true) : ∀ j, k ≤ j → F j = F k := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih => rw [hF, ih, lim_processReq_of_snd _ _ _ _ _ hk]

/-- The requirements processed after `e` do not touch the game and the injury counter of `e`. -/
theorem lim_accR_high {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ : CState}
    {F : ℕ → CState × Bool} (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) {e k : ℕ}
    (hek : e ≤ k) : ∀ j, k ≤ j →
      (F j).1.game e = (F k).1.game e ∧ (F j).1.inj e = (F k).1.inj e := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ j hkj ih =>
    rw [hF]
    exact ⟨(lim_processReq_game_of_lt A Γ σ₀ e (j + 1) (F j) (by omega)).trans ih.1,
      (lim_processReq_inj_of_le A Γ σ₀ e (j + 1) (F j) (by omega)).trans ih.2⟩

/-- Before the first action, the processed requirements only changed their own records. -/
theorem lim_accR_nonact {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ σ₁ : CState}
    {F : ℕ → CState × Bool} (hF0 : F 0 = (σ₁, false))
    (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) :
    ∀ k, (F k).2 = false → (F k).1.inj = σ₁.inj ∧ (F k).1.Fstar = σ₁.Fstar ∧
      (F k).1.Kstar = σ₁.Kstar ∧ ∀ e', k < e' → (F k).1.game e' = σ₁.game e' := by
  intro k
  induction k with
  | zero => intro _; rw [hF0]; exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    intro hk
    rw [hF] at hk ⊢
    obtain ⟨hk', i1, i2, i3, i4⟩ := lim_processReq_nonact A Γ σ₀ (k + 1) (F k) hk
    obtain ⟨h1, h2, h3, h4⟩ := ih hk'
    exact ⟨i1.trans h1, i2.trans h2, i3.trans h3,
      fun e' he' => (i4 e' (by omega)).trans (h4 e' (by omega))⟩

/-- The first action of a stage. -/
theorem lim_accR_first {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ σ₁ : CState}
    {F : ℕ → CState × Bool} (hF0 : F 0 = (σ₁, false))
    (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) :
    ∀ k, (F k).2 = true → ∃ b, b + 1 ≤ k ∧ F k = F (b + 1) ∧ (F b).2 = false ∧
      (F (b + 1)).2 = true := by
  intro k
  induction k with
  | zero => intro h; rw [hF0] at h; exact absurd h (by simp)
  | succ k ih =>
    intro hk
    by_cases hk' : (F k).2 = true
    · obtain ⟨b, hb1, hb2, hb3, hb4⟩ := ih hk'
      refine ⟨b, by omega, ?_, hb3, hb4⟩
      rw [hF, lim_processReq_of_snd _ _ _ _ _ hk', hb2]
    · exact ⟨k, le_rfl, rfl, by simpa using hk', hk⟩

/-- One stage seen from requirement `e ≥ 1`: either a requirement `a < e` acted (it changed its
record and destroyed the game of `e`), or the injury counter of `e` is unchanged and the game of
`e` is unchanged (`e` not processed) or is the result of processing `e` on a state `τ` that differs
from the initial one only in `K*` (updated) and in the records of `e' < e`. -/
theorem lim_accR_cases {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ σ₁ : CState}
    {F : ℕ → CState × Bool} (hF0 : F 0 = (σ₁, false))
    (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) (e s : ℕ) (he : 1 ≤ e) :
    (∃ a, 1 ≤ a ∧ a < e ∧ (F s).1.game e = none ∧ (F s).1.game a ≠ σ₁.game a) ∨
    ((F s).1.inj e = σ₁.inj e ∧
      ((s < e ∧ (F s).1.game e = σ₁.game e) ∨
       (e ≤ s ∧ ∃ τ : CState, τ.Fstar = σ₁.Fstar ∧ τ.Kstar = σ₁.Kstar ∧ τ.inj = σ₁.inj ∧
          τ.game e = σ₁.game e ∧
          (F s).1.game e = (processReq A Γ σ₀ e (τ, false)).1.game e))) := by
  have L1 := lim_accR_nonact hF0 hF
  by_cases hact : (F (min s (e - 1))).2 = true
  · left
    obtain ⟨b, hb1, hb2, hb3, hb4⟩ := lim_accR_first hF0 hF _ hact
    have hb4' : (processReq A Γ σ₀ (b + 1) (F b)).2 = true := by rw [← hF]; exact hb4
    obtain ⟨hch, hnone⟩ := lim_processReq_act A Γ σ₀ (b + 1) (F b) hb3 hb4'
    have hbσ := (L1 b hb3).2.2.2 (b + 1) (by omega)
    have hsn : F s = F (min s (e - 1)) := lim_accR_persist hF hact s (by omega)
    refine ⟨b + 1, by omega, by omega, ?_, ?_⟩
    · rw [hsn, hb2, hF]; exact hnone e (by omega)
    · rw [hsn, hb2, hF, ← hbσ]; exact hch
  · right
    have hact' : (F (min s (e - 1))).2 = false := by simpa using hact
    rcases Nat.lt_or_ge s e with hse | hes
    · have hns : min s (e - 1) = s := by omega
      rw [hns] at hact'
      obtain ⟨h1, -, -, h4⟩ := L1 s hact'
      exact ⟨by rw [h1], Or.inl ⟨hse, h4 e hse⟩⟩
    · have hne : min s (e - 1) = e - 1 := by omega
      rw [hne] at hact'
      obtain ⟨h1, h2, h3, h4⟩ := L1 (e - 1) hact'
      have hFe : F e = processReq A Γ σ₀ e ((F (e - 1)).1, false) := by
        have := hF (e - 1)
        rw [Nat.sub_add_cancel he] at this
        rw [this]
        congr 1
        exact Prod.ext rfl hact'
      obtain ⟨hg5, hi5⟩ := lim_accR_high hF (le_refl e) s hes
      refine ⟨?_, Or.inr ⟨hes, (F (e - 1)).1, h2, h3, h1, h4 e (by omega), ?_⟩⟩
      · rw [hi5, hFe, lim_processReq_inj_of_le A Γ σ₀ e e _ le_rfl]
        simp [h1]
      · rw [hg5, hFe]

/-- Requirement `0` is never processed. -/
theorem lim_accR_zero {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ σ₁ : CState}
    {F : ℕ → CState × Bool} (hF0 : F 0 = (σ₁, false))
    (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) (s : ℕ) :
    (F s).1.game 0 = σ₁.game 0 ∧ (F s).1.inj 0 = σ₁.inj 0 := by
  have := lim_accR_high hF (le_refl 0) s (Nat.zero_le s)
  rw [hF0] at this
  exact this

/-- `lim_stage_succ_eq` expresses the state at stage `t + 1` in terms of `foldl`. -/
theorem lim_stage_succ_eq (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ) :
    stage A γ enumK (t + 1) = ((List.range (t + 1)).foldl
        (fun p e => processReq A (reqγ γ) (stage A γ enumK t) (e + 1) p)
        (updateK enumK t (stage A γ enumK t), false)).1 := by
  change stageStep A γ enumK (t + 1) (stage A γ enumK t) = _
  unfold stageStep
  rw [Nat.add_sub_cancel]

/-- `lim_accR_cases` for the stages of the construction. -/
theorem lim_stage_cases (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t e : ℕ)
    (he : 1 ≤ e) :
    (∃ a, 1 ≤ a ∧ a < e ∧ (stage A γ enumK (t + 1)).game e = none ∧
        (stage A γ enumK (t + 1)).game a ≠ (stage A γ enumK t).game a) ∨
    ((stage A γ enumK (t + 1)).inj e = (stage A γ enumK t).inj e ∧
      ((t + 1 < e ∧ (stage A γ enumK (t + 1)).game e = (stage A γ enumK t).game e) ∨
       (e ≤ t + 1 ∧ ∃ τ : CState, τ.Fstar = (stage A γ enumK t).Fstar ∧
          τ.Kstar = (updateK enumK t (stage A γ enumK t)).Kstar ∧
          τ.inj = (stage A γ enumK t).inj ∧ τ.game e = (stage A γ enumK t).game e ∧
          (stage A γ enumK (t + 1)).game e =
            (processReq A (reqγ γ) (stage A γ enumK t) e (τ, false)).1.game e))) := by
  rw [lim_stage_succ_eq]
  exact lim_accR_cases (A := A) (Γ := reqγ γ) (σ₀ := stage A γ enumK t)
    (σ₁ := updateK enumK t (stage A γ enumK t))
    (F := fun k => (List.range k).foldl
      (fun p e => processReq A (reqγ γ) (stage A γ enumK t) (e + 1) p)
      (updateK enumK t (stage A γ enumK t), false)) rfl
    (fun k => lim_foldl_range_succ _ _ _ _ k) e (t + 1) he

/-- The game and the injury counter of requirement `0` never change. -/
theorem lim_stage_zero (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ) :
    (stage A γ enumK (t + 1)).game 0 = (stage A γ enumK t).game 0 ∧
      (stage A γ enumK (t + 1)).inj 0 = (stage A γ enumK t).inj 0 := by
  rw [lim_stage_succ_eq]
  exact lim_accR_zero (A := A) (Γ := reqγ γ) (σ₀ := stage A γ enumK t)
    (σ₁ := updateK enumK t (stage A γ enumK t))
    (F := fun k => (List.range k).foldl
      (fun p e => processReq A (reqγ γ) (stage A γ enumK t) (e + 1) p)
      (updateK enumK t (stage A γ enumK t), false)) rfl
    (fun k => lim_foldl_range_succ _ _ _ _ k) (t + 1)

/-- `lim_stage_game_zero` proves that the game at index 0 is `none` at any stage. -/
theorem lim_stage_game_zero (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (s : ℕ) : (stage A γ enumK s).game 0 = none := by
  induction s with
  | zero => rfl
  | succ s ih => rw [(lim_stage_zero A γ enumK s).1, ih]

/-! #### The game of `e` when `e` is processed -/

/-- A game lost while processing `e` was lost to a cheat of `K`. -/
theorem lim_processReq_some_none (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (τ : CState) (g : BitString × Finset BitString × ℕ × GState) (hg : τ.game e = some g)
    (h : (processReq A Γ σ₀ e (τ, false)).1.game e = none) :
    Cheats ((2 : ℝ)⁻¹ ^ g.2.2.1) g.2.2.2 (kCost σ₀ τ g.2.1) := by
  rw [lim_processReq_false_some A Γ σ₀ e τ g hg] at h
  revert h
  unfold processGame
  split_ifs with h1 h2
  · intro _; exact h1
  · intro h; simp [setGame] at h
  · intro h; simp [injure, applyFlips, setGame] at h

/-- A game kept while processing `e`: same witness, play set and budget; `K` is charged the real
cost of its changes; the flipped set is unchanged (a charge) or grows inside the play set. -/
theorem lim_processReq_some_some (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (τ : CState) (g g' : BitString × Finset BitString × ℕ × GState) (hg : τ.game e = some g)
    (h : (processReq A Γ σ₀ e (τ, false)).1.game e = some g') :
    g'.1 = g.1 ∧ g'.2.1 = g.2.1 ∧ g'.2.2.1 = g.2.2.1 ∧
      g'.2.2.2.moverScore = g.2.2.2.moverScore + kCost σ₀ τ g.2.1 ∧
      (g'.2.2.2 = g.2.2.2.charge (kCost σ₀ τ g.2.1) ∨
        (g.2.2.2.S ⊂ g'.2.2.2.S ∧ g'.2.2.2.S ⊆ g.2.2.2.S ∪ g.2.1)) := by
  rw [lim_processReq_false_some A Γ σ₀ e τ g hg] at h
  revert h
  unfold processGame
  split_ifs with h1 h2
  · intro h; simp [injure, destroy] at h
  · intro h
    simp only [setGame, Function.update_self, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, lim_moverScore_charge _ _, Or.inl rfl⟩
  · intro h
    simp only [injure, applyFlips, setGame, lt_irrefl, ite_false, Function.update_self,
      Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, rfl, lim_moverScore_applyMove_kMove _ _ _ _ _, Or.inr ?_⟩
    obtain ⟨hsub1, hsub2⟩ := lim_ourReply_subset (curGame A Γ τ e g) (!g.2.2.2.yesTurn)
      (g.2.2.2.kMove (g.2.2.2.S ∪ flipped τ g.2.1) (kCost σ₀ τ g.2.1))
    have hfl : flipped τ g.2.1 ⊆ g.2.1 := Finset.filter_subset _ _
    refine ⟨?_, ?_⟩
    · exact Finset.ssubset_of_ssubset_of_subset
        (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, fun h => h2 h.symm⟩) hsub1
    · refine hsub2.trans (Finset.union_subset (Finset.union_subset Finset.subset_union_left
        (hfl.trans Finset.subset_union_right)) Finset.subset_union_right)

/-- A new game starts with budget exponent `e + i_e + 6` and `K`'s score `0`. -/
theorem lim_processReq_none_some (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (τ : CState) (g' : BitString × Finset BitString × ℕ × GState) (hg : τ.game e = none)
    (h : (processReq A Γ σ₀ e (τ, false)).1.game e = some g') :
    g'.2.2.1 = e + τ.inj e + 6 ∧ g'.2.2.2.moverScore = 0 := by
  rw [lim_processReq_false_none A Γ σ₀ e τ hg] at h
  cases hc : chooseWitness A Γ τ e with
  | none => rw [lim_startGame_none A Γ e τ hc, hg] at h; simp at h
  | some x =>
    rw [lim_startGame_some A Γ e τ x hc] at h
    simp only [startOn, injure, applyFlips, setGame, lt_irrefl, ite_false, Function.update_self,
      Option.some.injEq] at h
    subst h
    exact ⟨rfl, lim_moverScore_applyMove_firstState _ _ _⟩

/-- With a witness available, processing `e` without a game starts one. -/
theorem lim_processReq_none_witness (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (τ : CState) (hg : τ.game e = none) (hw : ∃ x, IsWitness A Γ τ e x) :
    ∃ g', (processReq A Γ σ₀ e (τ, false)).1.game e = some g' := by
  rw [lim_processReq_false_none A Γ σ₀ e τ hg]
  have hc : ∃ x, chooseWitness A Γ τ e = some x := by
    obtain ⟨x, hx⟩ := hw
    unfold chooseWitness
    rw [dite_eq_left ⟨Encodable.encode x, by simpa using hx⟩]
    exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hc
  rw [lim_startGame_some A Γ e τ x hx]
  simp [startOn, injure, applyFlips, setGame]

/-! #### Values -/

section

omit [Family]

/-- `lim_hval_le_of_le` states that `hval` is monotone with respect to the prefix-free condition. -/
theorem lim_hval_le_of_le (σ σ' : CState) (x : BitString) (hK : σ'.Kstar x ≤ σ.Kstar x)
    (hF : σ'.Fstar x ≤ σ.Fstar x) : σ'.hval x ≤ σ.hval x := by
  unfold CState.hval CState.Hstar
  apply ENat.toNat_le_toNat
  · exact min_le_min (add_le_add hK le_rfl) (add_le_add (by exact_mod_cast hF) le_rfl)
  · exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)

/-- `lim_hval_eq_of` states that `hval` is equal when the `Fstar` conditions agree. -/
theorem lim_hval_eq_of (σ σ' : CState) (hK : σ'.Kstar = σ.Kstar) (hF : σ'.Fstar = σ.Fstar) :
    σ'.hval = σ.hval := by
  funext x
  unfold CState.hval CState.Hstar
  rw [hK, hF]

/-- `lim_updateK_Kstar_le` states that `updateK` monotonically increases `Kstar`. -/
theorem lim_updateK_Kstar_le (enumK : ℕ → BitString × ℕ) (t : ℕ) (σ : CState) (x : BitString) :
    (updateK enumK t σ).Kstar x ≤ σ.Kstar x := by
  unfold updateK
  dsimp only
  by_cases hx : x = (enumK t).1
  · subst hx; rw [Function.update_self]; exact min_le_left _ _
  · rw [Function.update_of_ne hx]
/-- `lim_updateK_hval_le` states that `updateK` does not increase `hval`. -/
theorem lim_updateK_hval_le (enumK : ℕ → BitString × ℕ) (t : ℕ) (σ : CState) (x : BitString) :
    (updateK enumK t σ).hval x ≤ σ.hval x :=
  lim_hval_le_of_le σ _ x (lim_updateK_Kstar_le enumK t σ x) le_rfl

end

/-- `lim_stage_hval_succ_le_updateK` states that the `hval` at `t + 1` is bounded
    by the updated `K` at `t`. -/
theorem lim_stage_hval_succ_le_updateK (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ) (x : BitString) :
    (stage A γ enumK (t + 1)).hval x ≤ (updateK enumK t (stage A γ enumK t)).hval x := by
  apply lim_hval_le_of_le
  · have h := stageStep_Kstar A γ enumK (t + 1) (stage A γ enumK t)
    rw [Nat.add_sub_cancel] at h
    exact le_of_eq (congrFun h x)
  · exact stage_Fstar_antitone A γ enumK t x

/-- `lim_stage_hval_succ_le` states that `hval` does not increase across stages. -/
theorem lim_stage_hval_succ_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t : ℕ) (x : BitString) : (stage A γ enumK (t + 1)).hval x ≤ (stage A γ enumK t).hval x :=
  (lim_stage_hval_succ_le_updateK A γ enumK t x).trans (lim_updateK_hval_le enumK t _ x)

/-- `lim_kIncr_term_nonneg` shows that the individual term of the `K` increment is non-negative. -/
theorem lim_kIncr_term_nonneg (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t : ℕ) (x : BitString) : 0 ≤ (2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x -
      (2 : ℝ)⁻¹ ^ (stage A γ enumK t).hval x := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
    (lim_updateK_hval_le enumK t (stage A γ enumK t) x)
  linarith

/-- `lim_kIncr_nonneg` proves that `kIncr` is always non-negative. -/
theorem lim_kIncr_nonneg (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ) (S : Finset BitString) :
    0 ≤ kIncr A γ enumK t S :=
  Finset.sum_nonneg fun x _ => lim_kIncr_term_nonneg A γ enumK t x

/-- `lim_kIncr_mono` shows that `kIncr` is monotone with respect to the set `S`. -/
theorem lim_kIncr_mono (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ) (t : ℕ)
    {S S' : Finset BitString} (h : S ⊆ S') : kIncr A γ enumK t S ≤ kIncr A γ enumK t S' :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => lim_kIncr_term_nonneg A γ enumK t x

/-- The real cost charged to `K` when `e` is processed in stage `t + 1` is `kIncr t`. -/
theorem lim_kCost_eq_kIncr (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ)
    (τ : CState) (hF : τ.Fstar = (stage A γ enumK t).Fstar)
    (hK : τ.Kstar = (updateK enumK t (stage A γ enumK t)).Kstar) (X : Finset BitString) :
    kCost (stage A γ enumK t) τ X = kIncr A γ enumK t X := by
  have h := lim_hval_eq_of (updateK enumK t (stage A γ enumK t)) τ hK hF
  unfold kCost kIncr
  rw [h]

end Kolmogorov.RandomStrings
