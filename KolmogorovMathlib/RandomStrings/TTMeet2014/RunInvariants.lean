/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.GameInvariants

/-!
# The invariants of the games and of the agreement (§4.1.1, §4.1.2 of the paper)

`VisitInv` is what holds right after a visit of a requirement:

* every game in progress is within the opponent's limit, and its position is winning for the
  remaining budgets;
* on every *clean* board (all boards if no game runs, the bishop during stacked games) the agreed
  value is winning against the opponent's remaining allowance since the base stage.  This is the
  generalized bishop lemma, the repair of Case 2 (`docs/random_strings_tt_meet_2014.md`, section 3).

`caseTwo_visit` and `caseThree_visit` prove that a visit establishes `VisitInv`, from the invariant
at the previous visit, transferred to the current stage by `forces_current` (unanswered opponent
moves). `run_invariant` is the induction over the run.
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Finset

variable {I : Input}

/-- The boards with no move of ours since their base stage: all of them when no game runs, and the
bishop during stacked games. -/
def Clean (rs : ReqState) (j : Fin 3) : Prop :=
  rs.play = none ∨ ∃ pl σ, rs.play = some pl ∧ pl.kind = .stacked σ j

/-- What holds right after a visit at stage `t`, in the state `st`. -/
structure VisitInv (I : Input) (st : ConState) (t : ℕ) (r : ReqState) : Prop where
  /-- Every game is within the limit, and winning for the remaining budgets. -/
  game : ∀ pl, r.play = some pl → ∀ g ∈ pl.games,
    oppSpend I pl.arena pl.start t ≤ g.oppLimit ∧
      pl.arena.Forces g.target (st.position I pl.arena t g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent)
  /-- The agreed value is winning on the clean boards. -/
  base : ∀ c bl j, r.c = some c → r.baseline = some bl → Clean r j →
    oppSpend I (arenaOf c r.tables) (bl.base j) t ≤ levelBudget r.tables 0 →
      (arenaOf c r.tables).Forces {bl.σ} (st.position I (arenaOf c r.tables) t j)
        (levelBudget r.tables 0 - oppSpend I (arenaOf c r.tables) (bl.base j) t)
        (levelBudget r.tables 0)
  /-- A play has at most one game per board. -/
  boards : ∀ pl, r.play = some pl → (pl.games.map BoardGame.board).Nodup
  /-- The shape of stacked games. -/
  stacked : ∀ pl σ b, r.play = some pl → pl.kind = .stacked σ b →
    (∃ bl, r.baseline = some bl ∧ bl.σ = σ ∧ bl.base b = pl.start) ∧
      (∀ j, j ≠ b → j ∈ pl.games.map BoardGame.board) ∧ b ∉ pl.games.map BoardGame.board
  /-- The start of a play is in the past. -/
  startLe : ∀ pl, r.play = some pl → pl.start ≤ t
  /-- The base stages are in the past. -/
  baseLe : ∀ bl, r.baseline = some bl → ∀ j, bl.base j ≤ t
  /-- No outcome vector is on target in all the games of a play. -/
  incompat : ∀ pl, r.play = some pl → ¬ ∃ v, ∀ g ∈ pl.games, v ∈ g.target
  /-- Balanced games have the opponent's limit `ε`, and there is no agreement. -/
  balancedNone : ∀ pl, r.play = some pl → pl.kind = .balanced → r.baseline = none ∧
    ∀ g ∈ pl.games, g.oppLimit = levelBudget pl.arena.tables 0
  /-- Unbalanced games have the opponent's limit `ε`, or `ε - λ` for a base stage of the
      agreement. -/
  unbalancedLim : ∀ pl, r.play = some pl → pl.kind = .unbalanced → ∃ bl, r.baseline = some bl ∧
    (∀ k, bl.base k ≤ pl.start) ∧ ∀ g ∈ pl.games, g.oppLimit = levelBudget pl.arena.tables 0 ∨
      ∃ k, g.oppLimit = levelBudget pl.arena.tables 0 - oppSpend I pl.arena (bl.base k) pl.start

/-- With nothing in progress there is nothing to check. -/
theorem visitInv_trivial {st : ConState} {t : ℕ} {r : ReqState} (hp : r.play = none)
    (hb : r.baseline = none) : VisitInv I st t r := by
  refine ⟨fun pl h => ?_, fun _ bl _ _ h => ?_, fun pl h => ?_, fun pl _ _ h => ?_,
    fun pl h => ?_, fun bl h => ?_, fun pl h => ?_, fun pl h _ => ?_, fun pl h _ => ?_⟩
  all_goals first
    | (rw [hp] at h; cases h)
    | (rw [hb] at h; cases h)

/-- An agreement just established, with no game. -/
theorem visitInv_agreement {st : ConState} {t c : ℕ} {r : ReqState} {σ : List Bool}
    (hp : r.play = none) (hc : r.c = some c) (hb : r.baseline = some ⟨σ, fun _ => t⟩)
    (hf : ∀ j, (arenaOf c r.tables).Forces {σ} (st.position I (arenaOf c r.tables) t j)
      (levelBudget r.tables 0) (levelBudget r.tables 0)) : VisitInv I st t r := by
  refine ⟨fun pl h => ?_, fun c' bl j hc' hbl _ _ => ?_, fun pl h => ?_, fun pl _ _ h => ?_,
    fun pl h => ?_, fun bl hbl j => ?_, fun pl h => ?_, fun pl h _ => ?_, fun pl h _ => ?_⟩
  · rw [hp] at h
    cases h
  · rw [hc] at hc'
    cases hc'
    rw [hb] at hbl
    cases hbl
    simp only [oppSpend_self, Nat.sub_zero]
    exact hf j
  · rw [hp] at h
    cases h
  · rw [hp] at h
    cases h
  · rw [hp] at h
    cases h
  · rw [hb] at hbl
    cases hbl
    exact le_rfl
  · rw [hp] at h
    cases h
  · rw [hp] at h
    cases h
  · rw [hp] at h
    cases h

/-- The balanced games started on a verdict are winning. -/
theorem balancedPlay_inv {st : ConState} {t E : ℕ} {ar : Arena} {pl : Play}
    (h : balancedPlay ar t E (topOutcome ar (st.position I ar t) E) = some pl) :
    pl.start = t ∧ pl.arena = ar ∧ pl.kind = .balanced ∧ (pl.games.map BoardGame.board).Nodup ∧
      (¬ ∃ v, ∀ g ∈ pl.games, v ∈ g.target) ∧
      ∀ g ∈ pl.games, g.oppLimit = E ∧ g.ourLimit = E ∧ g.spent = 0 ∧
        ar.Forces g.target (st.position I ar t g.board) E E := by
  generalize hv : topOutcome ar (st.position I ar t) E = v at h
  cases v with
  | split j k S =>
    obtain ⟨hne, hS, hC⟩ := topOutcome_split_forces hv
    simp only [balancedPlay, Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, rfl, ?_, ?_, fun g hg => ?_⟩
    · simp [symGame, hne]
    · rintro ⟨v, hv'⟩
      have h1 := hv' _ List.mem_cons_self
      have h2 := hv' _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact (mem_sdiff.1 h2).2 h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨rfl, rfl, rfl, hS⟩
      · exact ⟨rfl, rfl, rfl, hC⟩
  | meet S T =>
    obtain ⟨hS, hT, hC⟩ := topOutcome_meet_forces hv
    simp only [balancedPlay, Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, rfl, ?_, ?_, fun g hg => ?_⟩
    · simp [symGame]
    · rintro ⟨v, hv'⟩
      have h1 := hv' _ List.mem_cons_self
      have h2 := hv' _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have h3 := hv' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      exact (mem_sdiff.1 h3).2 (mem_inter.2 ⟨h1, h2⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨rfl, rfl, rfl, hS⟩
      · exact ⟨rfl, rfl, rfl, hT⟩
      · exact ⟨rfl, rfl, rfl, hC⟩
  | principal σ => simp [balancedPlay] at h
  | stuck => simp [balancedPlay] at h

/-- A balanced play, with no agreement. -/
theorem visitInv_balanced {st : ConState} {t c : ℕ} {r : ReqState} {pl : Play}
    (hp : r.play = some pl) (hb : r.baseline = none)
    (h : balancedPlay (arenaOf c r.tables) t (levelBudget r.tables 0)
      (topOutcome (arenaOf c r.tables) (st.position I (arenaOf c r.tables) t)
        (levelBudget r.tables 0)) = some pl) : VisitInv I st t r := by
  obtain ⟨hs, ha, hk, hn, hinc, hg⟩ := balancedPlay_inv h
  refine ⟨fun pl' h' g hg' => ?_, fun _ bl _ _ h' => ?_, fun pl' h' => ?_, fun pl' _ _ h' hk' => ?_,
    fun pl' h' => ?_, fun bl h' => ?_, fun pl' h' => ?_, fun pl' h' _ => ?_, fun pl' h' hk' => ?_⟩
  rotate_right 3
  · rw [hp] at h'
    cases h'
    exact hinc
  · rw [hp] at h'
    cases h'
    refine ⟨hb, fun g hg' => ?_⟩
    rw [ha]
    exact (hg g hg').1
  · rw [hp] at h'
    cases h'
    rw [hk] at hk'
    cases hk'
  · rw [hp] at h'
    cases h'
    obtain ⟨h1, h2, h3, h4⟩ := hg g hg'
    rw [hs, oppSpend_self, h1, h2, h3, ha]
    exact ⟨Nat.zero_le _, by simpa using h4⟩
  · rw [hb] at h'
    cases h'
  · rw [hp] at h'
    cases h'
    exact hn
  · rw [hp] at h'
    cases h'
    rw [hk] at hk'
    cases hk'
  · rw [hp] at h'
    cases h'
    exact hs.le
  · rw [hb] at h'
    cases h'

/-- **A visit in Case 2 establishes the invariant.** -/
theorem caseTwo_visit {st : ConState} {i t c : ℕ} {rs : ReqState} (hw : ReqWF i t rs)
    (hc : rs.c = some c) (hnp : rs.play = none)
    (hcur : ∀ bl j, rs.baseline = some bl →
      oppSpend I (arenaOf c rs.tables) (bl.base j) t ≤ levelBudget rs.tables 0 →
      (arenaOf c rs.tables).Forces {bl.σ} (st.position I (arenaOf c rs.tables) t j)
        (levelBudget rs.tables 0 - oppSpend I (arenaOf c rs.tables) (bl.base j) t)
        (levelBudget rs.tables 0))
    (hbaseLe : ∀ bl, rs.baseline = some bl → ∀ j, bl.base j ≤ t) :
    VisitInv I st t (caseTwo I st i t c rs).1 := by
  obtain ⟨-, hspec⟩ := examineTop_spec (I := I) (st := st) hw hc
  unfold caseTwo
  dsimp only
  split
  · -- The visit is over after the first part.
    rename_i r hr
    unfold examineTop at hr
    dsimp only at hr
    split at hr
    · rename_i bl hbl
      split at hr
      · cases hr
        exact visitInv_trivial hnp rfl
      · rename_i hdrop
        split at hr
        · rename_i j hj
          cases hr
          have hk := otherBoard_ne j
          have hlam : oppSpend I (arenaOf c rs.tables) (bl.base (otherBoard j)) t ≤
              levelBudget rs.tables 0 := by
            by_contra hbig
            apply hdrop
            exact List.any_eq_true.2 ⟨otherBoard j, mem_allBoards _,
              decide_eq_true (not_le.1 hbig)⟩
          have hF : (arenaOf c rs.tables).Forces (vectors rs.tables.length \ {bl.σ})
              (st.position I (arenaOf c rs.tables) t j) (levelBudget rs.tables 0)
              (levelBudget rs.tables 0) := by
            have h' := List.find?_some hj
            exact of_decide_eq_true h'
          refine ⟨fun pl' h' g hg' => ?_, fun _ bl' j' _ _ hcl _ => ?_, fun pl' h' => ?_,
            fun pl' _ _ h' hk' => ?_, fun pl' h' => ?_, fun bl' h' => hbaseLe bl' h',
            fun pl' h' => ?_, fun pl' h' hk' => ?_, fun pl' h' _ => ?_⟩
          · cases h'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl | rfl
            · simp only [oppSpend_self, Nat.sub_zero]
              exact ⟨Nat.zero_le _, hF⟩
            · simp only [oppSpend_self, Nat.sub_zero]
              exact ⟨Nat.zero_le _, hcur bl _ hbl hlam⟩
          · rcases hcl with hcl | ⟨pl', σ', hcl, hk'⟩
            · cases hcl
            · cases hcl
              cases hk'
          · cases h'
            simp [symGame, Ne.symm hk]
          · cases h'
            cases hk'
          · cases h'
            exact le_rfl
          · cases h'
            rintro ⟨v, hv⟩
            have h1 := hv _ List.mem_cons_self
            have h2 := hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
            exact (mem_sdiff.1 h1).2 h2
          · cases h'
            cases hk'
          · cases h'
            refine ⟨bl, hbl, fun k => hbaseLe bl hbl k, fun g hg' => ?_⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr ⟨otherBoard j, rfl⟩
        · cases hr
    · rename_i hbn
      split at hr
      · cases hr
      · split at hr
        · rename_i pl hpl
          cases hr
          exact visitInv_balanced (c := c) rfl hbn hpl
        · cases hr
          exact visitInv_trivial hnp hbn
  · -- An agreement.
    rename_i rs₁ σ hex
    obtain ⟨ht, hc₁, hp₁, hb₁, -⟩ := hspec _ hex
    dsimp only at ht hc₁ hp₁ hb₁
    have hf : ∀ j, (arenaOf c rs.tables).Forces {σ} (st.position I (arenaOf c rs.tables) t j)
        (levelBudget rs.tables 0) (levelBudget rs.tables 0) := fun j => examineTop_forces hex j
    have hc₁' : rs₁.c = some c := hc₁.trans hc
    have hp₁' : rs₁.play = none := hp₁.trans hnp
    have hagree : VisitInv I st t rs₁ := visitInv_agreement hp₁' hc₁' hb₁ (by rw [ht]; exact hf)
    split
    · rename_i ℓ j hsplit
      obtain ⟨hℓ, hj, hk⟩ := firstStackSplit_some hsplit hf
      have hkj := otherBoard_ne j
      obtain ⟨h3j, h3k, h3⟩ := thirdBoard_spec j (otherBoard j) hkj
      refine ⟨fun pl' h' g hg' => ?_, fun c' bl j' hc' hbl _ _ => ?_, fun pl' h' => ?_,
        fun pl' σ' b h' hk' => ?_, fun pl' h' => ?_, fun bl hbl j' => ?_,
        fun pl' h' => ?_, fun pl' h' hk' => ?_, fun pl' h' hk' => ?_⟩
      rotate_right 3
      · cases h'
        rintro ⟨v, hv⟩
        have h1 := hv _ List.mem_cons_self
        have h2 := hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
        exact (mem_sdiff.1 h1).2 h2
      · cases h'
        cases hk'
      · cases h'
        cases hk'
      · cases h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        · simp only [oppSpend_self, Nat.sub_zero]
          exact ⟨Nat.zero_le _, hj⟩
        · simp only [oppSpend_self, Nat.sub_zero]
          exact ⟨Nat.zero_le _, hk _⟩
      · change rs₁.c = some c' at hc'
        change rs₁.baseline = some bl at hbl
        rw [hc₁'] at hc'
        cases hc'
        rw [hb₁] at hbl
        cases hbl
        simp only [oppSpend_self, Nat.sub_zero]
        rw [ht]
        exact hf j'
      · cases h'
        simp [symGame, Ne.symm hkj]
      · cases h'
        cases hk'
        refine ⟨⟨⟨σ, fun _ => t⟩, hb₁, rfl, rfl⟩, fun j' hj' => ?_, ?_⟩
        · rcases h3 j' hj' with rfl | rfl <;> simp [symGame]
        · simp only [symGame, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
              or_false,
            not_or]
          exact ⟨h3j, h3k⟩
      · cases h'
        exact le_rfl
      · change rs₁.baseline = some bl at hbl
        rw [hb₁] at hbl
        cases hbl
        exact le_rfl
    · split
      · exact hagree
      · split
        · exact hagree
        · rename_i tbl htbl
          generalize hv : topOutcome (arenaOf c (rs.tables ++ [tbl]))
            (st.position I (arenaOf c (rs.tables ++ [tbl])) t)
            (levelBudget (rs.tables ++ [tbl]) 0) = v
          cases v with
          | principal σ' =>
            exact visitInv_agreement hp₁' hc₁' rfl fun j => topOutcome_principal_forces hv j
          | split j k S =>
            dsimp only
            split
            · rename_i pl hpl
              exact visitInv_balanced (c := c) rfl rfl (by
                rw [hv]
                exact hpl)
            · exact hagree
          | meet S T =>
            dsimp only
            split
            · rename_i pl hpl
              exact visitInv_balanced (c := c) rfl rfl (by
                rw [hv]
                exact hpl)
            · exact hagree
          | stuck =>
            dsimp only
            split
            · rename_i pl hpl
              simp [balancedPlay] at hpl
            · exact hagree

/-- The strings compressed on a board in a move of a play. -/
theorem fold_board_eq {O : Finset Str} {mv : BoardGame → Finset Str} {g : BoardGame} :
    ∀ l : List BoardGame, (l.map BoardGame.board).Nodup → g ∈ l →
      (l.map fun g => (g, mv g)).foldr
        (fun q acc => if q.1.board = g.board then q.2 ∪ acc else acc) O = mv g ∪ O := by
  intro l
  have hnone : ∀ l : List BoardGame, (∀ a ∈ l, a.board ≠ g.board) →
      (l.map fun g => (g, mv g)).foldr
        (fun q acc => if q.1.board = g.board then q.2 ∪ acc else acc) O = O := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      rw [ite_eq_right (h a List.mem_cons_self)]
      exact ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
  induction l with
  | nil => intro _ hg; simp at hg
  | cons a l ih =>
    intro hn hg
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hg with rfl | hmem
    · rw [ite_eq_left rfl]
      congr 1
      exact hnone l fun a' ha' heq => hn.1 a' ha' heq
    · have hne : a.board ≠ g.board := fun heq => hn.1 g hmem heq.symm
      rw [ite_eq_right hne]
      exact ih hn.2 hmem

/-- The boards not in a play are not touched by it. -/
theorem fold_board_none {O : Finset Str} {mv : BoardGame → Finset Str} {b : Fin 3} :
    ∀ l : List BoardGame, (∀ a ∈ l, a.board ≠ b) →
      (l.map fun g => (g, mv g)).foldr
        (fun q acc => if q.1.board = b then q.2 ∪ acc else acc) O = O := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.map_cons, List.foldr_cons]
    rw [ite_eq_right (h a List.mem_cons_self)]
    exact ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')

/-- Positions depend on the state only through `ours`. -/
theorem position_congr {st st' : ConState} {ar : Arena} {t : ℕ} {j : Fin 3}
    (h : st'.ours j = st.ours j) : st'.position I ar t j = st.position I ar t j := by
  ext z
  rw [mem_position, mem_position, h]

/-- A position after a move. -/
theorem position_of_union {st st' : ConState} {ar : Arena} {t : ℕ} {j : Fin 3} {p : Finset Str}
    (h : st'.ours j = p ∪ st.ours j) : st'.position I ar t j = st.position I ar t j \ p := by
  ext z
  simp only [mem_position, mem_sdiff, h, mem_union, not_or]
  tauto

/-- Over the limit, Case 3 makes no move. -/
theorem caseThree_ours_of_not_le {st : ConState} {i t c : ℕ} {rs : ReqState} {pl : Play}
    (hl : ¬ oppSpend I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)) :
    (caseThree I st i t c rs pl).2.1 = st.ours := by
  unfold caseThree
  dsimp only
  rw [ite_eq_right hl]
  split
  · split_ifs
    · split <;> rfl
    · rfl
  · rfl

/-- **A visit in Case 3 establishes the invariant.** -/
theorem caseThree_visit {st st' : ConState} {i t c c' : ℕ} {rs : ReqState} {pl : Play}
    (hc : rs.c = some c') (ha : pl.arena = arenaOf c' rs.tables)
    (hours : st'.ours = (caseThree I st i t c rs pl).2.1)
    (hboards : (pl.games.map BoardGame.board).Nodup)
    (hstacked : ∀ σ b, pl.kind = .stacked σ b →
      (∃ bl, rs.baseline = some bl ∧ bl.σ = σ ∧ bl.base b = pl.start) ∧
        (∀ j, j ≠ b → j ∈ pl.games.map BoardGame.board) ∧ b ∉ pl.games.map BoardGame.board)
    (hstart : pl.start ≤ t) (hbaseLe : ∀ bl, rs.baseline = some bl → ∀ j, bl.base j ≤ t)
    (hcurG : ∀ g ∈ pl.games, oppSpend I pl.arena pl.start t ≤ g.oppLimit →
      pl.arena.Forces g.target (st.position I pl.arena t g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent))
    (hcurB : ∀ σ b bl, pl.kind = .stacked σ b → rs.baseline = some bl →
      oppSpend I pl.arena (bl.base b) t ≤ levelBudget rs.tables 0 →
      pl.arena.Forces {bl.σ} (st.position I pl.arena t b)
        (levelBudget rs.tables 0 - oppSpend I pl.arena (bl.base b) t) (levelBudget rs.tables 0))
    (hinc : ¬ ∃ v, ∀ g ∈ pl.games, v ∈ g.target)
    (hbal : pl.kind = .balanced → rs.baseline = none ∧
      ∀ g ∈ pl.games, g.oppLimit = levelBudget pl.arena.tables 0)
    (hunb : pl.kind = .unbalanced → ∃ bl, rs.baseline = some bl ∧ (∀ k, bl.base k ≤ pl.start) ∧
      ∀ g ∈ pl.games, g.oppLimit = levelBudget pl.arena.tables 0 ∨
        ∃ k, g.oppLimit = levelBudget pl.arena.tables 0 -
            oppSpend I pl.arena (bl.base k) pl.start) :
    VisitInv I st' t (caseThree I st i t c rs pl).1 := by
  have hplt : pl.arena.tables = rs.tables := by rw [ha]; rfl
  by_cases hl : oppSpend I pl.arena pl.start t ≤
      pl.games.foldr (fun g n => min g.oppLimit n) (levelBudget pl.arena.tables 0)
  · -- Case 3a.
    set mv : BoardGame → Finset Str := fun g =>
      respond pl.arena g (st.positionList I pl.arena t g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start t) (g.ourLimit - g.spent) with hmv
    have hoursj : ∀ j, st'.ours j = (pl.games.map fun g => (g, mv g)).foldr
        (fun q acc => if q.1.board = j then q.2 ∪ acc else acc) (st.ours j) := by
      intro j
      rw [hours]
      unfold caseThree
      dsimp only
      rw [ite_eq_left hl]
    unfold caseThree
    dsimp only
    rw [ite_eq_left hl]
    have hgames' : ∀ g ∈ pl.games, ∃ g' ∈ (pl.games.map fun g => (g, mv g)).map (fun q =>
        ({ q.1 with spent := q.1.spent + cost pl.arena.w q.2 } : BoardGame)),
        g'.target = g.target ∧ g'.oppLimit = g.oppLimit := fun g hg =>
      ⟨_, List.mem_map.2 ⟨(g, mv g), List.mem_map.2 ⟨g, hg, rfl⟩, rfl⟩, rfl, rfl⟩
    have hgames : ∀ g' ∈ (pl.games.map fun g => (g, mv g)).map (fun q =>
        ({ q.1 with spent := q.1.spent + cost pl.arena.w q.2 } : BoardGame)),
        ∃ g ∈ pl.games, g'.target = g.target ∧ g'.oppLimit = g.oppLimit := by
      intro g' hg'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hq
      exact ⟨g, hg, rfl, rfl⟩
    refine ⟨fun pl' h' g' hg' => ?_, fun c'' bl j hc'' hbl hcl hle => ?_, fun pl' h' => ?_,
      fun pl' σ b h' hk => ?_, fun pl' h' => ?_, fun bl hbl j => hbaseLe bl hbl j,
      fun pl' h' => ?_, fun pl' h' hk => ?_, fun pl' h' hk => ?_⟩
    rotate_right 3
    · cases h'
      rintro ⟨v, hv⟩
      refine hinc ⟨v, fun g hg => ?_⟩
      obtain ⟨g', hg', ht, -⟩ := hgames' g hg
      rw [← ht]
      exact hv g' hg'
    · cases h'
      obtain ⟨hb, hl'⟩ := hbal hk
      refine ⟨hb, fun g' hg' => ?_⟩
      obtain ⟨g, hg, -, ho⟩ := hgames g' hg'
      rw [ho]
      exact hl' g hg
    · cases h'
      obtain ⟨bl, hbl, hk0, hl'⟩ := hunb hk
      refine ⟨bl, hbl, hk0, fun g' hg' => ?_⟩
      obtain ⟨g, hg, -, ho⟩ := hgames g' hg'
      rw [ho]
      exact hl' g hg
    · cases h'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hq
      have hlim : oppSpend I pl.arena pl.start t ≤ g.oppLimit := hl.trans (foldr_min_le hg)
      refine ⟨hlim, ?_⟩
      have hforces := hcurG g hg hlim
      have hpos : st'.position I pl.arena t g.board = st.position I pl.arena t g.board \ mv g :=
        position_of_union (by
          rw [hoursj]
          exact fold_board_eq _ hboards hg)
      rw [hpos]
      change pl.arena.Forces g.target (st.position I pl.arena t g.board \ mv g)
        (g.oppLimit - oppSpend I pl.arena pl.start t)
        (g.ourLimit - (g.spent + cost pl.arena.w (mv g)))
      rcases respond_spec (La := st.positionList I pl.arena t g.board) hforces with
        ⟨h0, -, hF⟩ | ⟨-, hF⟩
      · have hm0 : mv g = ∅ := h0
        rw [hm0, sdiff_empty, cost_empty, Nat.add_zero]
        exact hF
      · have hsub : g.ourLimit - (g.spent + cost pl.arena.w (mv g)) =
            g.ourLimit - g.spent - cost pl.arena.w (mv g) := (Nat.sub_sub _ _ _).symm
        rw [hsub]
        exact hF
    · rcases hcl with hcl | ⟨pl', σ, hcl, hk⟩
      · cases hcl
      · cases hcl
        change rs.c = some c'' at hc''
        rw [hc] at hc''
        cases hc''
        change rs.baseline = some bl at hbl
        change oppSpend I (arenaOf c' rs.tables) (bl.base j) t ≤ levelBudget rs.tables 0 at hle
        rw [← ha] at hle ⊢
        obtain ⟨-, -, hnot⟩ := hstacked σ j hk
        have hours' : st'.ours j = st.ours j := by
          rw [hoursj]
          refine fold_board_none _ fun a ha' heq => hnot ?_
          exact List.mem_map.2 ⟨a, ha', heq⟩
        rw [position_congr hours']
        exact hcurB σ j bl hk hbl hle
    · cases h'
      have hmap : ((pl.games.map fun g => (g, mv g)).map fun q =>
          ({ q.1 with spent := q.1.spent + cost pl.arena.w q.2 } : BoardGame)).map BoardGame.board =
          pl.games.map BoardGame.board := by
        simp only [List.map_map]
        rfl
      change (List.map BoardGame.board _).Nodup
      rw [hmap]
      exact hboards
    · cases h'
      obtain ⟨⟨bl, hbl, hσ, hbase⟩, hall, hnot⟩ := hstacked σ b hk
      have hmap : ((pl.games.map fun g => (g, mv g)).map fun q =>
          ({ q.1 with spent := q.1.spent + cost pl.arena.w q.2 } : BoardGame)).map BoardGame.board =
          pl.games.map BoardGame.board := by
        simp only [List.map_map]
        rfl
      refine ⟨⟨bl, hbl, hσ, hbase⟩, fun j hj => ?_, ?_⟩
      · rw [hmap]
        exact hall j hj
      · rw [hmap]
        exact hnot
    · cases h'
      exact hstart
  · -- Case 3b, or a stop.
    have hours' : ∀ j', st'.ours j' = st.ours j' := fun j' => by
      rw [hours, caseThree_ours_of_not_le hl]
    unfold caseThree
    dsimp only
    rw [ite_eq_right hl]
    split
    · rename_i σ b hk
      have hk' : pl.kind = .stacked σ b := hk
      obtain ⟨⟨bl, hbl, hσ, hbase⟩, hall, hnot⟩ := hstacked σ b hk'
      split_ifs with hE
      swap
      · exact visitInv_trivial rfl rfl
      have hlam : oppSpend I pl.arena pl.start t ≤ levelBudget rs.tables 0 := by
        rw [← hplt]
        exact hE
      have hF := hcurB σ b bl hk' hbl (by rw [hbase]; exact hlam)
      rw [hbase, hσ] at hF
      split
      · rename_i j hj
        have hjF : pl.arena.Forces (vectors pl.arena.tables.length \ {σ})
            (st.position I pl.arena t j) (levelBudget pl.arena.tables 0)
            (levelBudget pl.arena.tables 0) := by
          have h' := List.find?_some hj
          exact of_decide_eq_true h'
        have hjmem := List.mem_of_find?_eq_some hj
        refine ⟨fun pl' h' g hg' => ?_, fun _ bl' j' _ _ hcl _ => ?_, fun pl' h' => ?_,
          fun pl' _ _ h' hk'' => ?_, fun pl' h' => ?_, fun bl' h' => hbaseLe bl' h',
          fun pl' h' => ?_, fun pl' h' hk'' => ?_, fun pl' h' _ => ?_⟩
        rotate_right 3
        · cases h'
          rintro ⟨v, hv⟩
          have h1 := hv _ List.mem_cons_self
          have h2 := hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
          exact (mem_sdiff.1 h1).2 h2
        · cases h'
          cases hk''
        · cases h'
          refine ⟨bl, hbl, fun k => hbaseLe bl hbl k, fun g hg' => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
          rcases hg' with rfl | rfl
          · exact Or.inl rfl
          · refine Or.inr ⟨b, ?_⟩
            dsimp only
            rw [hbase]
        · cases h'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
          rcases hg' with rfl | rfl
          · simp only [oppSpend_self, Nat.sub_zero]
            rw [position_congr (hours' _)]
            exact ⟨Nat.zero_le _, hjF⟩
          · simp only [oppSpend_self, Nat.sub_zero]
            rw [position_congr (hours' _)]
            refine ⟨Nat.zero_le _, ?_⟩
            rw [hplt]
            exact hF
        · rcases hcl with hcl | ⟨pl', σ', hcl, hk''⟩
          · cases hcl
          · cases hcl
            cases hk''
        · cases h'
          have hjb : j ≠ b := fun heq => hnot (heq ▸ hjmem)
          simp [symGame, hjb]
        · cases h'
          cases hk''
        · cases h'
          exact le_rfl
      · rename_i hnone
        refine ⟨fun pl' h' => ?_, fun c'' bl' j hc'' hbl' _ hle => ?_, fun pl' h' => ?_,
          fun pl' _ _ h' => ?_, fun pl' h' => ?_, fun bl' hbl' j => ?_,
          fun pl' h' => ?_, fun pl' h' => ?_, fun pl' h' => ?_⟩
        rotate_right 3
        · cases h'
        · cases h'
        · cases h'
        · cases h'
        · change rs.c = some c'' at hc''
          rw [hc] at hc''
          cases hc''
          change rs.baseline.map _ = some bl' at hbl'
          rw [hbl] at hbl'
          cases hbl'
          rw [position_congr (hours' _)]
          change oppSpend I (arenaOf c' rs.tables) _ t ≤ levelBudget rs.tables 0 at hle
          change (arenaOf c' rs.tables).Forces {bl.σ} (st.position I (arenaOf c' rs.tables) t j) _
            (levelBudget rs.tables 0)
          rw [← ha] at hle ⊢
          by_cases hjb : j = b
          · subst hjb
            simp only [ite_true] at hle ⊢
            rw [hσ, hbase]
            exact hF
          · simp only [hjb, ite_false] at hle ⊢
            rw [oppSpend_self, Nat.sub_zero, hσ]
            rcases forces_or_compl (w := pl.arena.w) (Arena.value_mem_vectors pl.arena) {σ}
                (st.position I pl.arena t j) (levelBudget pl.arena.tables 0) with h' | h'
            · rw [hplt] at h'
              exact h'
            · exfalso
              exact List.find?_eq_none.1 hnone j (hall j hjb)
                (decide_eq_true (show pl.arena.Forces _ _ _ _ from h'))
        · cases h'
        · cases h'
        · cases h'
        · change rs.baseline.map _ = some bl' at hbl'
          rw [hbl] at hbl'
          cases hbl'
          by_cases hjb : j = b
          · simp only [hjb, ite_true]
            exact hbaseLe bl hbl b
          · simp only [hjb, ite_false]
            exact le_rfl
    · exact visitInv_trivial rfl rfl

/-! ### The induction over the run -/

/-- The previous visit of a requirement. -/
theorem visited_spec (I : Input) (s i : ℕ) :
    rsAt I s i = rsAt I 0 i ∨ ∃ u, u < s ∧ (Nat.unpair u).1 = i ∧ (rsAt I s i).lastVisit = u + 1 ∧
      rsAt I s i = rsAt I (u + 1) i ∧ ∀ s'', u < s'' → s'' < s → (Nat.unpair s'').1 ≠ i := by
  induction s with
  | zero => exact Or.inl rfl
  | succ s ih =>
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      exact Or.inr ⟨s, Nat.lt_succ_self s, rfl, lastVisit_self I s, rfl, fun s'' h1 h2 => by omega⟩
    · rw [rsAt_succ_of_ne I hi]
      rcases ih with h | ⟨u, hu, hui, hv, hr, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨u, by omega, hui, hv, hr, fun s'' h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
        · exact hb s'' h1 h3
        · exact fun h => hi h.symm

/-- `VisitInv` depends on the state only through `ours`. -/
theorem VisitInv.congr {st st' : ConState} {t : ℕ} {r : ReqState} (h : VisitInv I st t r)
    (hours : ∀ j, st'.ours j = st.ours j) : VisitInv I st' t r := by
  refine ⟨fun pl hp g hg => ?_, fun c bl j hc hbl hcl hle => ?_, h.boards, h.stacked, h.startLe,
    h.baseLe, h.incompat, h.balancedNone, h.unbalancedLim⟩
  · rw [position_congr (hours _)]
    exact h.game pl hp g hg
  · rw [position_congr (hours _)]
    exact h.base c bl j hc hbl hcl hle

/-- `VisitInv` does not depend on the fields of the schedule. -/
theorem VisitInv.schedule {st : ConState} {t v a : ℕ} {r : ReqState} (h : VisitInv I st t r) :
    VisitInv I st t { r with lastVisit := v, lastActed := a } :=
  ⟨h.game, h.base, h.boards, h.stacked, h.startLe, h.baseLe, h.incompat, h.balancedNone,
    h.unbalancedLim⟩

/-- Transfer to the current stage. -/
theorem forces_transfer {ar : Arena} {T : Finset (List Bool)} {a a' b t₀ t : ℕ} {st₀ st : ConState}
    {j : Fin 3} (hpos : st.position I ar t j = (st₀.position I ar t₀ j).filter fun τ =>
        !(I.opp t τ))
    (h : ar.Forces T (st₀.position I ar t₀ j) a b) (ha : a' + oppSpend I ar t₀ t ≤ a) :
    ar.Forces T (st.position I ar t j) a' b := by
  rw [hpos]
  exact forces_after_stage (fun τ hτ => ⟨(mem_position.1 hτ).1, (mem_position.1 hτ).2.1⟩) h ha

/-- The invariant of a requirement along the run, as of its last visit. -/
def RunInv (I : Input) (s i : ℕ) : Prop :=
  VisitInv I (stateAt I (rsAt I s i).lastVisit) (rsAt I s i).lastVisit (rsAt I s i)

/-- **The invariants of the games and of the agreement hold along the run.** -/
theorem run_invariant (hI : I.Valid) : ∀ s i, RunInv I s i := by
  intro s
  induction s with
  | zero =>
    intro i
    exact visitInv_trivial rfl rfl
  | succ s ih =>
    intro i
    by_cases hi : i = (Nat.unpair s).1
    · subst hi
      unfold RunInv
      rw [lastVisit_self]
      rw [rsAt_succ_self]
      refine VisitInv.schedule ?_
      set i := (Nat.unpair s).1 with hidef
      have hw : ReqWF i (s + 1) (rsAt I s i) := (reqWF_rsAt I s i).mono (Nat.le_succ s)
      have hst := stage_stateAt I s
      have hcore : stepCore I (stateAt I s) =
          if mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) = true then
            ((caseOne (stateAt I s) i (s + 1)).1, (stateAt I s).ours,
              (caseOne (stateAt I s) i (s + 1)).2, true)
          else
            match (rsAt I s i).c with
            | none => (rsAt I s i, (stateAt I s).ours, (stateAt I s).nextC, false)
            | some c =>
              match (rsAt I s i).play with
              | none =>
                ((caseTwo I (stateAt I s) i (s + 1) c (rsAt I s i)).1, (stateAt I s).ours,
                  (stateAt I s).nextC, (caseTwo I (stateAt I s) i (s + 1) c (rsAt I s i)).2)
              | some pl =>
                ((caseThree I (stateAt I s) i (s + 1) c (rsAt I s i) pl).1,
                  (caseThree I (stateAt I s) i (s + 1) c (rsAt I s i) pl).2.1,
                  (stateAt I s).nextC,
                  (caseThree I (stateAt I s) i (s + 1) c (rsAt I s i) pl).2.2) := by
        unfold stepCore
        dsimp only
        rw [hst]
        rfl
      have hstep : (stateAt I (s + 1)).ours = (stepCore I (stateAt I s)).2.1 := rfl
      cases hr : mustReset I (stateAt I s) i (Nat.unpair s).2 (s + 1) with
      | true =>
        rw [hcore, hr]
        obtain ⟨-, hp, hb, -, -⟩ := caseOne_spec (st := stateAt I s) hw
        exact visitInv_trivial hp hb
      | false =>
        have hnotnone : (rsAt I s i).c ≠ none := by
          intro hnone
          simp only [mustReset, Bool.or_eq_false_iff] at hr
          have h2 := hr.1.2
          have h3 : (rsAt I s i).c.isNone = false := h2
          rw [hnone] at h3
          cases h3
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hnotnone
        -- The previous visit.
        have hprev : ∃ u, u < s ∧ (Nat.unpair u).1 = i ∧ (rsAt I s i).lastVisit = u + 1 ∧
            rsAt I s i = rsAt I (u + 1) i ∧ ∀ s'', u < s'' → s'' < s → (Nat.unpair s'').1 ≠ i := by
          rcases visited_spec I s i with h0 | h1
          · exfalso
            rw [h0] at hc
            cases hc
          · exact h1
        obtain ⟨u, hus, hui, hlast, hsame, hbetween⟩ := hprev
        have hold : VisitInv I (stateAt I (u + 1)) (u + 1) (rsAt I s i) := by
          have := ih i
          unfold RunInv at this
          rwa [hlast] at this
        have hpos : ∀ c' j, (stateAt I s).position I (arenaOf c' (rsAt I s i).tables) (s + 1) j =
            ((stateAt I (u + 1)).position I (arenaOf c' (rsAt I s i).tables) (u + 1) j).filter
              fun τ => !(I.opp (s + 1) τ) := fun c' j =>
          position_between_visits hI hui hus hbetween hr (by rw [← hsame]) j
        have hbaseLe : ∀ bl, (rsAt I s i).baseline = some bl → ∀ j, bl.base j ≤ s + 1 :=
          fun bl hbl j => (hold.baseLe bl hbl j).trans (by omega)
        rw [hcore, hr]
        simp only [Bool.false_eq_true, ite_false, hc]
        cases hp : (rsAt I s i).play with
        | none =>
          simp only
          have hcur : ∀ bl j, (rsAt I s i).baseline = some bl →
              oppSpend I (arenaOf c (rsAt I s i).tables) (bl.base j) (s + 1) ≤
                levelBudget (rsAt I s i).tables 0 →
              (arenaOf c (rsAt I s i).tables).Forces {bl.σ}
                ((stateAt I s).position I (arenaOf c (rsAt I s i).tables) (s + 1) j)
                (levelBudget (rsAt I s i).tables 0 -
                  oppSpend I (arenaOf c (rsAt I s i).tables) (bl.base j) (s + 1))
                (levelBudget (rsAt I s i).tables 0) := by
            intro bl j hbl hle
            have hadd := oppSpend_add hI (arenaOf c (rsAt I s i).tables)
              (hold.baseLe bl hbl j) (show u + 1 ≤ s + 1 by omega)
            have hF := hold.base c bl j hc hbl (Or.inl hp) (by omega)
            exact forces_transfer (hpos c j) hF (by omega)
          have hv := caseTwo_visit (st := stateAt I s) (i := i) hw hc hp hcur hbaseLe
          refine hv.congr fun j => ?_
          rw [hstep, hcore, hr]
          simp only [Bool.false_eq_true, ite_false, hc, hp]
        | some pl =>
          simp only
          obtain ⟨c', hc', ha, -⟩ := (reqWF_rsAt I s i).play pl hp
          have hcc : c' = c := by
            rw [hc] at hc'
            exact (Option.some.inj hc').symm
          rw [hcc] at ha
          have hstart := hold.startLe pl hp
          have hcurG : ∀ g ∈ pl.games, oppSpend I pl.arena pl.start (s + 1) ≤ g.oppLimit →
              pl.arena.Forces g.target ((stateAt I s).position I pl.arena (s + 1) g.board)
                (g.oppLimit - oppSpend I pl.arena pl.start (s + 1)) (g.ourLimit - g.spent) := by
            intro g hg hle
            obtain ⟨hold1, hF⟩ := hold.game pl hp g hg
            have hadd := oppSpend_add hI pl.arena hstart (show u + 1 ≤ s + 1 by omega)
            have hpos' := hpos c g.board
            rw [← ha] at hpos'
            exact forces_transfer hpos' hF (by omega)
          have hcurB : ∀ σ b bl, pl.kind = .stacked σ b → (rsAt I s i).baseline = some bl →
              oppSpend I pl.arena (bl.base b) (s + 1) ≤ levelBudget (rsAt I s i).tables 0 →
              pl.arena.Forces {bl.σ} ((stateAt I s).position I pl.arena (s + 1) b)
                (levelBudget (rsAt I s i).tables 0 - oppSpend I pl.arena (bl.base b) (s + 1))
                (levelBudget (rsAt I s i).tables 0) := by
            intro σ b bl hk hbl hle
            have hadd := oppSpend_add hI pl.arena (hold.baseLe bl hbl b)
              (show u + 1 ≤ s + 1 by omega)
            have hF := hold.base c bl b hc hbl (Or.inr ⟨pl, σ, hp, hk⟩) (by
              rw [← ha]
              omega)
            rw [← ha] at hF
            have hpos' := hpos c b
            rw [← ha] at hpos'
            exact forces_transfer hpos' hF (by omega)
          refine caseThree_visit (c := c) hc ha ?_ (hold.boards pl hp)
            (fun σ b hk => hold.stacked pl σ b hp hk) (hstart.trans (by omega)) hbaseLe hcurG hcurB
            (hold.incompat pl hp) (hold.balancedNone pl hp) (hold.unbalancedLim pl hp)
          rw [hstep, hcore, hr]
          simp only [Bool.false_eq_true, ite_false, hc, hp]
    · unfold RunInv
      rw [rsAt_succ_of_ne I hi]
      exact ih i

/-- A play has one game per board, along the run. -/
theorem run_invariant_boards (hI : I.Valid) {s i : ℕ} (pl : Play)
    (hp : (rsAt I s i).play = some pl) : (pl.games.map BoardGame.board).Nodup :=
  (run_invariant hI s i).boards pl hp

/-- The invariant of a play at the last visit, in the form used for the verification. -/
theorem game_invariant (hI : I.Valid) {s i : ℕ} {pl : Play} (hp : (rsAt I s i).play = some pl) :
    ∀ g ∈ pl.games, oppSpend I pl.arena pl.start (rsAt I s i).lastVisit ≤ g.oppLimit ∧
      pl.arena.Forces g.target
        ((stateAt I (rsAt I s i).lastVisit).position I pl.arena (rsAt I s i).lastVisit g.board)
        (g.oppLimit - oppSpend I pl.arena pl.start (rsAt I s i).lastVisit) (g.ourLimit - g.spent) :=
  (run_invariant hI s i).game pl hp

/-- The invariant of an agreement at the last visit, in the form used for the verification. -/
theorem baseline_invariant (hI : I.Valid) {s i c : ℕ} {bl : Baseline} {j : Fin 3}
    (hc : (rsAt I s i).c = some c) (hbl : (rsAt I s i).baseline = some bl)
    (hcl : Clean (rsAt I s i) j)
    (hle : oppSpend I (arenaOf c (rsAt I s i).tables) (bl.base j) (rsAt I s i).lastVisit ≤
      levelBudget (rsAt I s i).tables 0) :
    (arenaOf c (rsAt I s i).tables).Forces {bl.σ}
      ((stateAt I (rsAt I s i).lastVisit).position I (arenaOf c (rsAt I s i).tables)
        (rsAt I s i).lastVisit j)
      (levelBudget (rsAt I s i).tables 0 -
        oppSpend I (arenaOf c (rsAt I s i).tables) (bl.base j) (rsAt I s i).lastVisit)
      (levelBudget (rsAt I s i).tables 0) :=
  (run_invariant hI s i).base c bl j hc hbl hcl hle

end Kolmogorov.RandomStrings.TTMeet
