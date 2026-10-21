/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.LiveGames

/-!
# Claim 2, second layer: the live-game invariants

The invariant `LGInv` of the live games, its shape and mid-stage versions (`LGShape`, `LGMid`,
`LGFold`), its preservation along the fold over the requirements, and the resulting facts
`lg_stage_liveInv`, `live_playSets_disjoint`, `live_game_side`, `live_game_flipped`,
`live_game_safe`.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-- The invariant of the live games at the beginning of stage `s`. -/
structure LGInv (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (s : ℕ) (σ : CState) : Prop where
  pos : ∀ e g, σ.game e = some g → 1 ≤ e ∧ e ≤ s
  disj : ∀ e e' g g', e ≠ e' → σ.game e = some g → σ.game e' = some g' →
    Disjoint g.2.1 g'.2.1
  nest : ∀ e g, σ.game e = some g → ∀ z ∈ lgQ γ e g,
    z ∈ g.2.1 ∨ ∃ e' < e, ∃ g', σ.game e' = some g' ∧ z ∈ g'.2.1
  good : ∀ e g, σ.game e = some g → LGood A γ σ.hval e g

/-- Two states have live games with the same witnesses and play sets. -/
def LGShape (σ₀ σ : CState) : Prop :=
  ∀ e, (∀ g, σ.game e = some g → ∃ g₀, σ₀.game e = some g₀ ∧ g.1 = g₀.1 ∧ g.2.1 = g₀.2.1) ∧
    (∀ g₀, σ₀.game e = some g₀ → ∃ g, σ.game e = some g ∧ g.1 = g₀.1 ∧ g.2.1 = g₀.2.1)

/-- The query set `lgQ` is invariant under replacing the game with one that has
the same first component. -/
theorem lgQ_congr (γ : ℕ → OTMCode × ℕ) (e : ℕ) {g g' : BitString × Finset BitString × ℕ × GState}
    (h : g.1 = g'.1) : lgQ γ e g = lgQ γ e g' := by
  unfold lgQ; rw [h]

/-- If two states have the same game shape, and the first state satisfies the positional
bounds of `LGInv`, then the second state does too. -/
theorem LGShape.pos {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s : ℕ} {σ₀ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hs : LGShape σ₀ σ) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState)
    (hg : σ.game e = some g) : 1 ≤ e ∧ e ≤ s := by
  obtain ⟨g₀, hg₀, -, -⟩ := (hs e).1 g hg
  exact hσ₀.pos e g₀ hg₀

/-- If two states have the same game shape, and the first state satisfies the
disjointness condition of `LGInv`, then the second state does too. -/
theorem LGShape.disj {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s : ℕ} {σ₀ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hs : LGShape σ₀ σ) (e e' : ℕ)
    (g g' : BitString × Finset BitString × ℕ × GState) (hne : e ≠ e') (hg : σ.game e = some g)
    (hg' : σ.game e' = some g') : Disjoint g.2.1 g'.2.1 := by
  obtain ⟨g₀, hg₀, -, h₀⟩ := (hs e).1 g hg
  obtain ⟨g₀', hg₀', -, h₀'⟩ := (hs e').1 g' hg'
  rw [h₀, h₀']
  exact hσ₀.disj e e' g₀ g₀' hne hg₀ hg₀'

/-- If two states have the same game shape, and the first state satisfies the nesting
condition of `LGInv`, then the second state does too. -/
theorem LGShape.nest {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s : ℕ} {σ₀ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hs : LGShape σ₀ σ) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState)
    (hg : σ.game e = some g) : ∀ z ∈ lgQ γ e g,
      z ∈ g.2.1 ∨ ∃ e' < e, ∃ g', σ.game e' = some g' ∧ z ∈ g'.2.1 := by
  intro z hz
  obtain ⟨g₀, hg₀, h1, h₀⟩ := (hs e).1 g hg
  rw [lgQ_congr γ e h1] at hz
  rcases hσ₀.nest e g₀ hg₀ z hz with h | ⟨e', he', g₀', hg₀', hz'⟩
  · left; rw [h₀]; exact h
  · right
    obtain ⟨g', hg', -, h'⟩ := (hs e').2 g₀' hg₀'
    exact ⟨e', he', g', hg', by rw [h']; exact hz'⟩

/-- Inside a stage (beginning state `σ₀`, `σ₁` after the update of `K*`), after the requirements
`1, …, n` have been processed without acting. -/
structure LGMid (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ σ₁ : CState) (n : ℕ) (σ : CState) :
    Prop where
  hval : σ.hval = σ₁.hval
  shape : LGShape σ₀ σ
  unproc : ∀ e, n < e → σ.game e = σ₀.game e
  good : ∀ e g, e ≤ n → σ.game e = some g → LGood A γ σ₁.hval e g
  stable : ∀ e g, e ≤ n → σ.game e = some g → ∀ z ∈ g.2.1, σ₁.hval z < z.length →
    σ₀.hval z < z.length

section

omit [Family]

/-- Injuring a requirement `e` does not affect the games of requirements `e' ≤ e`. -/
theorem lg_injure_game_of_le (e e' : ℕ) (σ : CState) (h : e' ≤ e) :
    (injure e σ).game e' = σ.game e' := by
  simp [injure, not_lt.2 h]

/-- Injuring a requirement `e` destroys the games of all requirements `e' > e`. -/
theorem lg_injure_game_of_lt (e e' : ℕ) (σ : CState) (h : e < e') :
    (injure e σ).game e' = none := by
  simp [injure, h]

/-- Applying a set of flips to a state does not change the active games. -/
theorem lg_applyFlips_game (T : Finset BitString) (σ : CState) :
    (applyFlips T σ).game = σ.game := rfl

/-- Setting the game of a requirement `e` does not affect the games of other
requirements `e' ≠ e`. -/
theorem lg_setGame_game_ne (e e' : ℕ) (g : BitString × Finset BitString × ℕ × GState) (σ : CState)
    (h : e' ≠ e) : (setGame e g σ).game e' = σ.game e' := by
  simp [setGame, Function.update_of_ne h]

/-- Setting the game of a requirement `e` to `g` makes its game equal to `some g`. -/
theorem lg_setGame_game_self (e : ℕ) (g : BitString × Finset BitString × ℕ × GState) (σ : CState) :
    (setGame e g σ).game e = some g := by
  simp [setGame]

/-- Destroying the game of a requirement `e` does not affect the games of other
requirements `e' ≠ e`. -/
theorem lg_destroy_game_ne (e e' : ℕ) (σ : CState) (h : e' ≠ e) :
    (destroy e σ).game e' = σ.game e' := by
  simp [destroy, Function.update_of_ne h]

/-- Destroying the game of a requirement `e` makes its game equal to `none`. -/
theorem lg_destroy_game_self (e : ℕ) (σ : CState) : (destroy e σ).game e = none := by
  simp [destroy]

end

/-- The state after the action of requirement `n + 1` satisfies the invariant of the next stage,
given the facts about the new game (if any) and about the strings whose values changed. -/
theorem lg_liveInv_act {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s n : ℕ} {σ₀ σ₁ σ σ₂ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hm : LGMid A γ σ₀ σ₁ n σ)
    (hlow : ∀ e', e' < n + 1 → σ₂.game e' = σ.game e')
    (hhigh : ∀ e', n + 1 < e' → σ₂.game e' = none)
    (T : Finset BitString) (hT : ∀ z, z ∉ T → σ₂.hval z = σ.hval z)
    (hTd : ∀ e' g', e' < n + 1 → σ.game e' = some g' → Disjoint T g'.2.1)
    (hns : n + 1 ≤ s + 1)
    (hnew : ∀ g, σ₂.game (n + 1) = some g → LGood A γ σ₂.hval (n + 1) g ∧
      (∀ e' g', e' < n + 1 → σ.game e' = some g' → Disjoint g.2.1 g'.2.1) ∧
      (∀ z ∈ lgQ γ (n + 1) g,
        z ∈ g.2.1 ∨ ∃ e' < n + 1, ∃ g', σ.game e' = some g' ∧ z ∈ g'.2.1)) :
    LGInv A γ (s + 1) σ₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e g hg
    rcases lt_trichotomy e (n + 1) with hlt | heq | hgt
    · rw [hlow e hlt] at hg
      have := hm.shape.pos hσ₀ e g hg
      omega
    · subst heq; exact ⟨by omega, hns⟩
    · rw [hhigh e hgt] at hg; exact absurd hg (by simp)
  · intro e e' g g' hne hg hg'
    rcases lt_trichotomy e (n + 1) with hlt | heq | hgt
    · rw [hlow e hlt] at hg
      rcases lt_trichotomy e' (n + 1) with hlt' | heq' | hgt'
      · rw [hlow e' hlt'] at hg'
        exact hm.shape.disj hσ₀ e e' g g' hne hg hg'
      · subst heq'
        exact ((hnew g' hg').2.1 e g hlt hg).symm
      · rw [hhigh e' hgt'] at hg'; exact absurd hg' (by simp)
    · subst heq
      rcases lt_trichotomy e' (n + 1) with hlt' | heq' | hgt'
      · rw [hlow e' hlt'] at hg'
        exact (hnew g hg).2.1 e' g' hlt' hg'
      · exact absurd heq'.symm hne
      · rw [hhigh e' hgt'] at hg'; exact absurd hg' (by simp)
    · rw [hhigh e hgt] at hg; exact absurd hg (by simp)
  · intro e g hg z hz
    rcases lt_trichotomy e (n + 1) with hlt | heq | hgt
    · rw [hlow e hlt] at hg
      rcases hm.shape.nest hσ₀ e g hg z hz with h | ⟨e', he', g', hg', hz'⟩
      · exact Or.inl h
      · exact Or.inr ⟨e', he', g', by rw [hlow e' (by omega)]; exact hg', hz'⟩
    · subst heq
      rcases (hnew g hg).2.2 z hz with h | ⟨e', he', g', hg', hz'⟩
      · exact Or.inl h
      · exact Or.inr ⟨e', he', g', by rw [hlow e' he']; exact hg', hz'⟩
    · rw [hhigh e hgt] at hg; exact absurd hg (by simp)
  · intro e g hg
    rcases lt_trichotomy e (n + 1) with hlt | heq | hgt
    · rw [hlow e hlt] at hg
      have hg1 := hm.good e g (by omega) hg
      rw [← hm.hval] at hg1
      refine hg1.of_eq fun z hz => hT z ?_
      intro hzT
      rcases hm.shape.nest hσ₀ e g hg z hz with h | ⟨e', he', g', hg', hz'⟩
      · exact Finset.disjoint_left.1 (hTd e g hlt hg) hzT h
      · exact Finset.disjoint_left.1 (hTd e' g' (by omega) hg') hzT hz'
    · subst heq; exact (hnew g hg).1
    · rw [hhigh e hgt] at hg; exact absurd hg (by simp)

/-- For strings outside the play set of a game, randomness is unchanged between
two mid-stage states. -/
theorem lg_rand_outside {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s n : ℕ} {σ₀ σ₁ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hm : LGMid A γ σ₀ σ₁ n σ) (hle1 : ∀ z, σ₁.hval z ≤ σ₀.hval z)
    (g : BitString × Finset BitString × ℕ × GState) (hg : σ₀.game (n + 1) = some g) :
    ∀ z ∈ lgQ γ (n + 1) g, z ∉ g.2.1 → (z.length ≤ σ₀.hval z ↔ z.length ≤ σ₁.hval z) := by
  intro z hz hzX
  rcases hσ₀.nest (n + 1) g hg z hz with h | ⟨e', he', g₀', hg₀', hz'⟩
  · exact absurd h hzX
  · obtain ⟨g', hg', -, h'⟩ := (hm.shape e').2 g₀' hg₀'
    have hst := hm.stable e' g' (by omega) hg' z (by rw [h']; exact hz')
    constructor
    · intro h1
      rcases Nat.lt_or_ge (σ₁.hval z) z.length with h2 | h2
      · have := hst h2; omega
      · exact h2
    · intro h1; exact h1.trans (hle1 z)

/-- If the current requirement has no active game, the mid-stage invariant is preserved
when skipping to the next requirement. -/
theorem lg_midInv_skip {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {n : ℕ} {σ₀ σ₁ σ : CState}
    (hm : LGMid A γ σ₀ σ₁ n σ) (hnone : σ.game (n + 1) = none) :
    LGMid A γ σ₀ σ₁ (n + 1) σ := by
  refine ⟨hm.hval, hm.shape, fun e he => hm.unproc e (by omega), fun e g he hg => ?_,
    fun e g he hg => ?_⟩
  · rcases Nat.lt_or_ge e (n + 1) with h | h
    · exact hm.good e g (by omega) hg
    · have : e = n + 1 := by omega
      subst this; rw [hnone] at hg; exact absurd hg (by simp)
  · rcases Nat.lt_or_ge e (n + 1) with h | h
    · exact hm.stable e g (by omega) hg
    · have : e = n + 1 := by omega
      subst this; rw [hnone] at hg; exact absurd hg (by simp)

/-- If the opponent cheats, destroying and injuring games preserves the live games invariant
for the next stage. -/
theorem lg_liveInv_cheat {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s n : ℕ} {σ₀ σ₁ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hm : LGMid A γ σ₀ σ₁ n σ) (hns : n ≤ s) :
    LGInv A γ (s + 1) (injure (n + 1) (destroy (n + 1) σ)) := by
  refine lg_liveInv_act hσ₀ hm (fun e' he' => ?_) (fun e' he' => lg_injure_game_of_lt _ _ _ he') ∅
    (fun z _ => rfl) (fun e' g' _ _ => Finset.disjoint_empty_left _) (by omega) (fun g hg => ?_)
  · rw [lg_injure_game_of_le _ _ _ (by omega), lg_destroy_game_ne _ _ _ (by omega)]
  · rw [lg_injure_game_of_le _ _ _ le_rfl, lg_destroy_game_self] at hg; exact absurd hg (by simp)

/-- Charging the opponent's move cost to a game preserves the mid-stage invariant. -/
theorem lg_midInv_charge {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s n : ℕ} {σ₀ σ₁ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hm : LGMid A γ σ₀ σ₁ n σ) (hle1 : ∀ z, σ₁.hval z ≤ σ₀.hval z)
    (g : BitString × Finset BitString × ℕ × GState) (hge : σ.game (n + 1) = some g)
    (hnf : g.2.2.2.S ∪ flipped σ g.2.1 = g.2.2.2.S) :
    LGMid A γ σ₀ σ₁ (n + 1)
      (setGame (n + 1) (g.1, g.2.1, g.2.2.1, g.2.2.2.charge (kCost σ₀ σ g.2.1)) σ) := by
  have hg₀ : σ₀.game (n + 1) = some g := by rw [← hm.unproc (n + 1) (by omega)]; exact hge
  have hgood := hσ₀.good _ _ hg₀
  have hfl : ∀ z ∈ g.2.1, σ₁.hval z < z.length → z ∈ g.2.2.2.S := by
    intro z hz hlt
    have : z ∈ flipped σ g.2.1 := Finset.mem_filter.2 ⟨hz, by rw [hm.hval]; exact hlt⟩
    exact Finset.union_eq_left.1 hnf this
  have hk : kCost σ₀ σ g.2.1 =
      ∑ z ∈ g.2.1, ((2 : ℝ)⁻¹ ^ σ₁.hval z - (2 : ℝ)⁻¹ ^ σ₀.hval z) := by
    unfold kCost; rw [hm.hval]
  refine ⟨hm.hval, fun e => ?_, fun e he => ?_, fun e g' he hg' => ?_, fun e g' he hg' => ?_⟩
  · by_cases he : e = n + 1
    · subst he
      refine ⟨fun g' hg' => ?_, fun g₀ hg₀' => ?_⟩
      · rw [lg_setGame_game_self] at hg'
        cases hg'
        exact ⟨g, hg₀, rfl, rfl⟩
      · rw [hg₀] at hg₀'
        cases hg₀'
        exact ⟨_, lg_setGame_game_self _ _ _, rfl, rfl⟩
    · rw [lg_setGame_game_ne _ _ _ _ he]
      exact hm.shape e
  · rw [lg_setGame_game_ne _ _ _ _ (by omega)]; exact hm.unproc e (by omega)
  · by_cases he' : e = n + 1
    · subst he'
      rw [lg_setGame_game_self] at hg'
      cases hg'
      rw [hk]
      refine hgood.charge hle1 fun z hz hzS => ?_
      by_cases hzX : z ∈ g.2.1
      · have h1 : z.length ≤ σ₁.hval z := by
          rcases Nat.lt_or_ge (σ₁.hval z) z.length with h | h
          · exact absurd (hfl z hzX h) hzS
          · exact h
        exact ⟨fun _ => h1, fun _ => h1.trans (hle1 z)⟩
      · exact lg_rand_outside hσ₀ hm hle1 g hg₀ z hz hzX
    · rw [lg_setGame_game_ne _ _ _ _ he'] at hg'
      exact hm.good e g' (by omega) hg'
  · by_cases he' : e = n + 1
    · subst he'
      rw [lg_setGame_game_self] at hg'
      cases hg'
      intro z hz hlt
      exact hgood.nonrand z (hfl z hz hlt)
    · rw [lg_setGame_game_ne _ _ _ _ he'] at hg'
      exact hm.stable e g' (by omega) hg'

/-- The play set created for a new game is disjoint from the play sets of all games
of lower index requirements. -/
theorem lg_playSet_disjoint (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ) (x : BitString) (e' : ℕ)
    (g' : BitString × Finset BitString × ℕ × GState) (he' : e' < e) (hg' : σ.game e' = some g') :
    Disjoint (playSet γ σ e x) g'.2.1 := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  unfold playSet at hz
  rw [Finset.mem_sdiff] at hz
  apply hz.2
  rw [Finset.mem_biUnion]
  exact ⟨e', Finset.mem_range.2 he', by rw [hg']; exact hz'⟩

/-- Any string queried by a game is either in its play set, or in the play set
of a game of a lower index requirement. -/
theorem lg_mem_playSet_or (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ) (x z : BitString)
    (hz : z ∈ qsetF (γ e).1 (γ e).2 x) :
    z ∈ playSet γ σ e x ∨ ∃ e' < e, ∃ g', σ.game e' = some g' ∧ z ∈ g'.2.1 := by
  by_cases h : z ∈ playSet γ σ e x
  · exact Or.inl h
  · right
    have h2 : z ∈ (Finset.range e).biUnion fun e' => (σ.game e').elim ∅ fun g => g.2.1 := by
      by_contra hc
      exact h (Finset.mem_sdiff.2 ⟨hz, hc⟩)
    rw [Finset.mem_biUnion] at h2
    obtain ⟨e', he', hz'⟩ := h2
    cases hg : σ.game e' with
    | none => rw [hg] at hz'; simp at hz'
    | some g' => rw [hg] at hz'; exact ⟨e', Finset.mem_range.1 he', g', hg, hz'⟩

omit [Family] in
/-- In the initial state of a game, it is the `YES` player's turn if and only if
the game value is true. -/
theorem lg_firstState_yesTurn (d : GameData) (v : Bool) : (firstState d v).yesTurn = v := by
  cases v <;> rfl

omit [Family] in
/-- The set of flipped strings in the initial state of a game is empty. -/
theorem lg_firstState_S (d : GameData) (v : Bool) : (firstState d v).S = ∅ := by
  cases v <;> rfl

omit [Family] in
/-- In the initial state of a game, the scores of both the `YES` and `NO`
players are non-negative. -/
theorem lg_firstState_scores (d : GameData) (v : Bool) :
    0 ≤ (firstState d v).scoreY ∧ 0 ≤ (firstState d v).scoreN := by
  cases v
  · change 0 ≤ 0 + moveCost d ∅ ∅ ∧ (0 : ℝ) ≤ 0
    rw [moveCost_self]; norm_num
  · exact ⟨le_rfl, le_rfl⟩

/-- Starting a new game preserves the live games invariant for the next stage. -/
theorem lg_liveInv_startOn {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s n : ℕ} {σ₀ σ₁ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hm : LGMid A γ σ₀ σ₁ n σ) (hns : n ≤ s)
    (_hnone : σ.game (n + 1) = none) (x : BitString) (hw : chooseWitness A γ σ (n + 1) = some x) :
    LGInv A γ (s + 1) (startOn A γ (n + 1) σ x).1 := by
  classical
  have hwit : IsWitness A γ σ (n + 1) x := by
    unfold chooseWitness at hw
    split_ifs at hw with h
    · have hx := Option.some.inj hw
      rw [← hx]
      exact Nat.find_spec h
  have hex : ∀ v : Bool, val (newGame A γ σ (n + 1) x) = v → ∃ r,
      LegalMove (newGame A γ σ (n + 1) x) (firstState (newGame A γ σ (n + 1) x) v) r ∧
      SafeFor (newGame A γ σ (n + 1) x) v
        (applyMove (newGame A γ σ (n + 1) x) (firstState (newGame A γ σ (n + 1) x) v) r) := by
    intro v hv
    cases v with
    | true =>
      obtain ⟨S₁, hL, hS⟩ := (determined _).1 hv
      exact ⟨S₁, hL, hS⟩
    | false =>
      have hny : ¬ YesWinsInit (newGame A γ σ (n + 1) x) := fun hy => by
        rw [(determined _).2 hy] at hv; exact Bool.noConfusion hv
      have hL0 : LegalMove (newGame A γ σ (n + 1) x) GState.init ∅ := by
        refine ⟨subset_rfl, Finset.empty_subset _, ?_⟩
        change (0 : ℝ) + moveCost (newGame A γ σ (n + 1) x) ∅ ∅ ≤
          (2 : ℝ)⁻¹ ^ (n + 1 + σ.inj (n + 1) + 6)
        rw [moveCost_self, zero_add]; positivity
      obtain ⟨S₂, hL, hS⟩ := noWinsInit_of_not_yesWinsInit _ hny ∅ hL0
      exact ⟨S₂, hL, hS⟩
  set d := newGame A γ σ (n + 1) x with hd
  set v := val d with hv
  set st₀ := firstState d v with hst₀
  set R := ourReply d v st₀ with hR
  set rec := (x, playSet γ σ (n + 1) x, n + 1 + σ.inj (n + 1) + 6, applyMove d st₀ R) with hrec
  have hstart : (startOn A γ (n + 1) σ x).1 =
      injure (n + 1) (applyFlips R (setGame (n + 1) rec σ)) := rfl
  rw [hstart]
  have hspec : LegalMove d st₀ R ∧ SafeFor d v (applyMove d st₀ R) :=
    lg_ourReply_spec d v st₀ (hex v rfl)
  have hRX : R ⊆ playSet γ σ (n + 1) x := hspec.1.2.1
  have hsc := lg_firstState_scores d v
  have hhv : (injure (n + 1) (applyFlips R (setGame (n + 1) rec σ))).hval =
      (applyFlips R σ).hval := rfl
  refine lg_liveInv_act hσ₀ hm (fun e' he' => ?_) (fun e' he' => lg_injure_game_of_lt _ _ _ he') R
    (fun z hz => ?_) (fun e' g' he' hg' => ?_) (by omega) (fun g hg => ?_)
  · rw [lg_injure_game_of_le _ _ _ (by omega), lg_applyFlips_game,
      lg_setGame_game_ne _ _ _ _ (by omega)]
  · rw [hhv]; exact lg_applyFlips_hval_of_not_mem R σ z hz
  · exact Finset.disjoint_of_subset_left hRX (lg_playSet_disjoint γ σ (n + 1) x e' g' he' hg')
  · rw [lg_injure_game_of_le _ _ _ le_rfl, lg_applyFlips_game, lg_setGame_game_self] at hg
    cases hg
    refine ⟨?_, fun e' g' he' hg' => lg_playSet_disjoint γ σ (n + 1) x e' g' he' hg',
      fun z hz => lg_mem_playSet_or γ σ (n + 1) x z hz⟩
    rw [hhv]
    have hS0 : st₀.S = ∅ := lg_firstState_S d v
    have hgg : LGood A γ (applyFlips R σ).hval (n + 1)
        (x, playSet γ σ (n + 1) x, n + 1 + σ.inj (n + 1) + 6,
          applyMove (gameOfF A (γ (n + 1)).1 (γ (n + 1)).2 x σ.hval
            ((2 : ℝ)⁻¹ ^ (n + 1 + σ.inj (n + 1) + 6)) (playSet γ σ (n + 1) x)) st₀ R) := by
      refine lg_goodGame_after_reply (h := σ.hval) (h'' := (applyFlips R σ).hval) hspec.1
        (by rw [lg_firstState_yesTurn]; exact hspec.2) ?_ Finset.sdiff_subset ?_ hsc.1 hsc.2
        (by omega) σ.lg_three_le_hval (fun z => lg_applyFlips_hval_le R σ z) (fun z hz => ?_)
        (fun z hz => ?_)
      · rw [lg_firstState_yesTurn]; exact hwit
      · intro z hz; rw [hS0] at hz; simp at hz
      · rw [hS0, Finset.sdiff_empty] at hz
        exact lg_applyFlips_hval_of_not_mem R σ z hz
      · rw [hS0, Finset.sdiff_empty] at hz
        exact lg_applyFlips_hval_le_length R σ z hz
    exact hgg
omit [Family] in
/-- Applying the opponent's move with a non-negative charge preserves the non-negativity
of both players' scores. -/
theorem lg_kMove_scores (st : GState) (S' : Finset BitString) (c : ℝ) (hc : 0 ≤ c)
    (hY : 0 ≤ st.scoreY) (hN : 0 ≤ st.scoreN) :
    0 ≤ (st.kMove S' c).scoreY ∧ 0 ≤ (st.kMove S' c).scoreN := by
  obtain ⟨S, y, n, t⟩ := st
  cases t
  · rw [lg_kMove_false]
    exact ⟨hY, by dsimp only at hN ⊢; linarith⟩
  · rw [lg_kMove_true]
    exact ⟨by dsimp only at hY ⊢; linarith, hN⟩

/-- Replying to a valid opponent move preserves the live games invariant for the next stage. -/
theorem lg_liveInv_move {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s n : ℕ} {σ₀ σ₁ σ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hm : LGMid A γ σ₀ σ₁ n σ) (hle1 : ∀ z, σ₁.hval z ≤ σ₀.hval z)
    (hns : n ≤ s) (g : BitString × Finset BitString × ℕ × GState) (hge : σ.game (n + 1) = some g)
    (hnc : ¬ Cheats ((2 : ℝ)⁻¹ ^ g.2.2.1) g.2.2.2 (kCost σ₀ σ g.2.1))
    (hnf : ¬ g.2.2.2.S ∪ flipped σ g.2.1 = g.2.2.2.S) :
    LGInv A γ (s + 1) (injure (n + 1) (applyFlips
        (ourReply (curGame A γ σ (n + 1) g) (!g.2.2.2.yesTurn)
            (g.2.2.2.kMove (g.2.2.2.S ∪ flipped σ g.2.1) (kCost σ₀ σ g.2.1)) \
          (g.2.2.2.S ∪ flipped σ g.2.1))
        (setGame (n + 1) (g.1, g.2.1, g.2.2.1,
          applyMove (curGame A γ σ (n + 1) g)
            (g.2.2.2.kMove (g.2.2.2.S ∪ flipped σ g.2.1) (kCost σ₀ σ g.2.1))
            (ourReply (curGame A γ σ (n + 1) g) (!g.2.2.2.yesTurn)
              (g.2.2.2.kMove (g.2.2.2.S ∪ flipped σ g.2.1) (kCost σ₀ σ g.2.1)))) σ))) := by
  have hg₀ : σ₀.game (n + 1) = some g := by rw [← hm.unproc (n + 1) (by omega)]; exact hge
  have hgood := hσ₀.good _ _ hg₀
  have hleσ : ∀ z, σ.hval z ≤ σ₀.hval z := fun z => by rw [hm.hval]; exact hle1 z
  set S' := g.2.2.2.S ∪ flipped σ g.2.1 with hS'
  set c := kCost σ₀ σ g.2.1 with hc
  set st₁ := g.2.2.2.kMove S' c with hst₁
  set d' := curGame A γ σ (n + 1) g with hd'
  set R := ourReply d' (!g.2.2.2.yesTurn) st₁ with hR
  set g₂ := (g.1, g.2.1, g.2.2.1, applyMove d' st₁ R) with hg₂
  have h1 : g.2.2.2.S ⊆ S' := Finset.subset_union_left
  have h2 : S' ⊆ g.2.1 := Finset.union_subset hgood.SX (Finset.filter_subset _ _)
  have hflS' : ∀ z ∈ S', σ.hval z < z.length := by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact lt_of_le_of_lt (hleσ z) (hgood.nonrand z h)
    · exact (Finset.mem_filter.1 h).2
  have hrand : ∀ z ∈ qsetF (γ (n + 1)).1 (γ (n + 1)).2 g.1,
      z ∉ S' → (z.length ≤ σ₀.hval z ↔ z.length ≤ σ.hval z) := by
    intro z hz hzS'
    by_cases hzX : z ∈ g.2.1
    · have h1 : z.length ≤ σ.hval z := by
        rcases Nat.lt_or_ge (σ.hval z) z.length with h | h
        · exact absurd (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzX, h⟩)) hzS'
        · exact h
      exact ⟨fun _ => h1, fun _ => h1.trans (hleσ z)⟩
    · rw [hm.hval]; exact lg_rand_outside hσ₀ hm hle1 g hg₀ z hz hzX
  have hcheat : g.2.2.2.moverScore +
      ∑ z ∈ g.2.1, ((2 : ℝ)⁻¹ ^ σ.hval z - (2 : ℝ)⁻¹ ^ σ₀.hval z) ≤ (2 : ℝ)⁻¹ ^ g.2.2.1 :=
    not_lt.1 hnc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun z _ => lg_two_inv_pow_sub_nonneg z (hleσ z)
  obtain ⟨r, hr⟩ := lg_move_reply (c := (γ (n + 1)).1) (k := (γ (n + 1)).2) (x := g.1)
    (X := g.2.1) (ε := (2 : ℝ)⁻¹ ^ g.2.2.1) hleσ g.2.2.2 hgood.safe S' h1 h2 hnf
    (fun z hz => hflS' z (Finset.mem_sdiff.1 hz).1) hrand hcheat
  have hspec : LegalMove d' st₁ R ∧ SafeFor d' (!g.2.2.2.yesTurn) (applyMove d' st₁ R) :=
    lg_ourReply_spec d' (!g.2.2.2.yesTurn) st₁ ⟨r, hr⟩
  have hRX : R ⊆ g.2.1 := hspec.1.2.1
  have hhv : (injure (n + 1) (applyFlips (R \ S') (setGame (n + 1) g₂ σ))).hval =
      (applyFlips (R \ S') σ).hval := rfl
  have hsc := lg_kMove_scores g.2.2.2 S' c hc0 hgood.scY hgood.scN
  refine lg_liveInv_act hσ₀ hm (fun e' he' => ?_) (fun e' he' => lg_injure_game_of_lt _ _ _ he')
    (R \ S') (fun z hz => ?_) (fun e' g' he' hg' => ?_) (by omega) (fun g' hg' => ?_)
  · rw [lg_injure_game_of_le _ _ _ (by omega), lg_applyFlips_game,
      lg_setGame_game_ne _ _ _ _ (by omega)]
  · rw [hhv]; exact lg_applyFlips_hval_of_not_mem _ σ z hz
  · exact Finset.disjoint_of_subset_left (Finset.sdiff_subset.trans hRX)
      (hm.shape.disj hσ₀ (n + 1) e' g g' (by omega) hge hg')
  · rw [lg_injure_game_of_le _ _ _ le_rfl, lg_applyFlips_game, lg_setGame_game_self] at hg'
    cases hg'
    refine ⟨?_, fun e' g'' he' hg'' => hm.shape.disj hσ₀ (n + 1) e' g g'' (by omega) hge hg'',
      hm.shape.nest hσ₀ (n + 1) g hge⟩
    rw [hhv]
    have hgg : LGood A γ (applyFlips (R \ S') σ).hval (n + 1)
        (g.1, g.2.1, g.2.2.1,
          applyMove (gameOfF A (γ (n + 1)).1 (γ (n + 1)).2 g.1 σ.hval
            ((2 : ℝ)⁻¹ ^ g.2.2.1) g.2.1) st₁ R) := by
      refine lg_goodGame_after_reply (h := σ.hval) (h'' := (applyFlips (R \ S') σ).hval) hspec.1
        hspec.2 ?_ hgood.XQ hflS' hsc.1 hsc.2 hgood.m7 σ.lg_three_le_hval
        (fun z => lg_applyFlips_hval_le _ σ z) (fun z hz => lg_applyFlips_hval_of_not_mem _ σ z hz)
        (fun z hz => lg_applyFlips_hval_le_length _ σ z hz)
      change (!g.2.2.2.yesTurn) = true ↔ g.1 ∉ A
      rw [← hgood.side]
      cases g.2.2.2.yesTurn <;> simp
    exact hgg

/-- The invariant along the fold over the requirements of a stage. -/
def LGFold (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (s : ℕ) (σ₀ σ₁ : CState) (n : ℕ)
    (p : CState × Bool) : Prop :=
  (p.2 = true → LGInv A γ (s + 1) p.1) ∧ (p.2 = false → LGMid A γ σ₀ σ₁ n p.1)

/-- The fold invariant is preserved after processing one requirement in a stage. -/
theorem lg_foldInv_step {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s : ℕ} {σ₀ σ₁ : CState}
    (hσ₀ : LGInv A γ s σ₀) (hle1 : ∀ z, σ₁.hval z ≤ σ₀.hval z) (n : ℕ) (hn : n ≤ s)
    (p : CState × Bool) (hp : LGFold A γ s σ₀ σ₁ n p) :
    LGFold A γ s σ₀ σ₁ (n + 1) (processReq A γ σ₀ (n + 1) p) := by
  obtain ⟨σ, b⟩ := p
  cases b with
  | true =>
    have h : processReq A γ σ₀ (n + 1) (σ, true) = (σ, true) := by simp [processReq]
    rw [h]
    exact ⟨hp.1, fun h => absurd h (by simp)⟩
  | false =>
    have hm := hp.2 rfl
    rcases hge : σ.game (n + 1) with _ | g
    · have h : processReq A γ σ₀ (n + 1) (σ, false) = startGame A γ (n + 1) σ := by
        simp [processReq, hge]
      rw [h]
      rcases hw : chooseWitness A γ σ (n + 1) with _ | x
      · have h' : startGame A γ (n + 1) σ = (σ, false) := by simp [startGame, hw]
        rw [h']
        exact ⟨fun h => absurd h (by simp), fun _ => lg_midInv_skip hm hge⟩
      · have h' : startGame A γ (n + 1) σ = startOn A γ (n + 1) σ x := by simp [startGame, hw]
        rw [h']
        exact ⟨fun _ => lg_liveInv_startOn hσ₀ hm hn hge x hw,
          fun h => absurd h (by simp [startOn])⟩
    · have h : processReq A γ σ₀ (n + 1) (σ, false) = processGame A γ σ₀ (n + 1) g σ := by
        simp [processReq, hge]
      rw [h]
      unfold processGame
      split_ifs with h1 h2
      · exact ⟨fun _ => lg_liveInv_cheat hσ₀ hm hn, fun h => absurd h (by simp)⟩
      · exact ⟨fun h => absurd h (by simp), fun _ => lg_midInv_charge hσ₀ hm hle1 g hge h2⟩
      · exact ⟨fun _ => lg_liveInv_move hσ₀ hm hle1 hn g hge h1 h2, fun h => absurd h (by simp)⟩

/-- The fold invariant is preserved after processing any number of requirements
up to the current stage limit. -/
theorem lg_foldInv_range {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s : ℕ} {σ₀ : CState}
    (hσ₀ : LGInv A γ s σ₀) (σ₁ : CState) (hle1 : ∀ z, σ₁.hval z ≤ σ₀.hval z)
    (hg1 : σ₁.game = σ₀.game) :
    ∀ n, n ≤ s + 1 → LGFold A γ s σ₀ σ₁ n
      ((List.range n).foldl (fun p e => processReq A γ σ₀ (e + 1) p) (σ₁, false))
  | 0, _ => by
    refine ⟨fun h => absurd h (by simp), fun _ => ⟨rfl, fun e => ⟨fun g hg => ?_, fun g hg => ?_⟩,
      fun e _ => by simp [hg1], fun e g he hg => ?_, fun e g he hg => ?_⟩⟩
    · exact ⟨g, by rw [← hg1]; exact hg, rfl, rfl⟩
    · exact ⟨g, by simp only [List.range_zero, List.foldl_nil]; rw [hg1]; exact hg, rfl, rfl⟩
    · have : e = 0 := by omega
      subst this
      simp only [List.range_zero, List.foldl_nil] at hg
      rw [hg1] at hg
      exact absurd (hσ₀.pos 0 g hg).1 (by omega)
    · have : e = 0 := by omega
      subst this
      simp only [List.range_zero, List.foldl_nil] at hg
      rw [hg1] at hg
      exact absurd (hσ₀.pos 0 g hg).1 (by omega)
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append]
    exact lg_foldInv_step hσ₀ hle1 n (by omega) _ (lg_foldInv_range hσ₀ σ₁ hle1 hg1 n (by omega))

/-- At the end of processing all requirements for a stage, the fold invariant implies
the live games invariant for the next stage. -/
theorem lg_liveInv_of_foldInv {A : Set BitString} {γ : ℕ → OTMCode × ℕ} {s : ℕ} {σ₀ σ₁ : CState}
    (hσ₀ : LGInv A γ s σ₀) (p : CState × Bool) (hp : LGFold A γ s σ₀ σ₁ (s + 1) p) :
    LGInv A γ (s + 1) p.1 := by
  obtain ⟨σ, b⟩ := p
  cases b with
  | true => exact hp.1 rfl
  | false =>
    have hm := hp.2 rfl
    refine ⟨fun e g hg => ?_, fun e e' g g' hne hg hg' => hm.shape.disj hσ₀ e e' g g' hne hg hg',
      fun e g hg => hm.shape.nest hσ₀ e g hg, fun e g hg => ?_⟩
    · have := hm.shape.pos hσ₀ e g hg; omega
    · have := hm.shape.pos hσ₀ e g hg
      have h := hm.good e g (by omega) hg
      rw [← hm.hval] at h
      exact h

/-- The invariants hold at the beginning of every stage. -/
theorem lg_stage_liveInv (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ) :
    ∀ s, LGInv A (reqγ γ) s (stage A γ enumK s)
  | 0 => by
    have h0 : ∀ e g, (stage A γ enumK 0).game e = some g → False := fun e g hg => by
      rw [show (stage A γ enumK 0).game e = none from rfl] at hg
      exact absurd hg (by simp)
    exact ⟨fun e g hg => (h0 e g hg).elim, fun e _ g _ _ hg _ => (h0 e g hg).elim,
      fun e g hg => (h0 e g hg).elim, fun e g hg => (h0 e g hg).elim⟩
  | s + 1 => by
    have hσ₀ := lg_stage_liveInv A γ enumK s
    have hst : stage A γ enumK (s + 1) = ((List.range (s + 1)).foldl
        (fun p e => processReq A (reqγ γ) (stage A γ enumK s) (e + 1) p)
        (updateK enumK s (stage A γ enumK s), false)).1 := by
      change stageStep A γ enumK (s + 1) (stage A γ enumK s) = _
      unfold stageStep
      rw [Nat.add_sub_cancel]
    rw [hst]
    exact lg_liveInv_of_foldInv hσ₀ _
      (lg_foldInv_range hσ₀ _ (lg_updateK_hval_le enumK s _) rfl (s + 1) le_rfl)

/-- (C2-i) The play sets of the live games are pairwise disjoint: a game of `e` is created with
`playSet`, which avoids the play sets of the live games of all `e' < e`, and its creation acts,
destroying all games of `e'' > e`; a requirement `e' < e` can only obtain a new game by acting,
which destroys the game of `e`; the play set of a game never changes. -/
theorem live_playSets_disjoint (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s e e' : ℕ) (g g' : BitString × Finset BitString × ℕ × GState) (hne : e ≠ e')
    (hg : (stage A γ enumK s).game e = some g) (hg' : (stage A γ enumK s).game e' = some g') :
    Disjoint g.2.1 g'.2.1 := by
  exact (lg_stage_liveInv A γ enumK s).disj e e' g g' hne hg hg'

/-- (C2-ii) Which side we play: in the stored state of a live game `K` is to move; we play YES
(`K` = NO, `yesTurn = false`) iff the witness is not in `A` (at the creation `val (newGame) = true`
iff `x ∉ A`, `IsWitness`; `firstState` + our first move give `yesTurn = !val`; later a `K` move
and our answer flip the turn twice, a charge keeps it). -/
theorem live_game_side (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (hg : (stage A γ enumK s).game e = some g) :
    (g.2.2.2.yesTurn = false ↔ g.1 ∉ A) := by
  exact ((lg_stage_liveInv A γ enumK s).good e g hg).side

/-- (C2-iii) The flipped set of a live game lies in its play set and consists of strings that are
non-random at the current stage: `K`'s flips are non-random by definition of `flipped`; our
flips are legal moves, so each new random string `z` has `2^{-|z|} ≤ flipCost ≤ 2^{-7}` (note
`hval ≥ 3`), hence `|z| ≥ 7` and `applyFlips` lowers `H*(z)` to `≤ |z| - 1`; `H*` only
decreases. -/
theorem live_game_flipped (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (hg : (stage A γ enumK s).game e = some g) :
    g.2.2.2.S ⊆ g.2.1 ∧ ∀ z ∈ g.2.2.2.S, (stage A γ enumK s).hval z < z.length := by
  exact ⟨((lg_stage_liveInv A γ enumK s).good e g hg).SX,
    ((lg_stage_liveInv A γ enumK s).good e g hg).nonrand⟩

/-- (C2-iv) Safety: the stored state of a live game is safe for us in the game evaluated with the
current values (`SafeYes` if `K` = NO is to move, `SafeNo` if `K` = YES is to move).  At the
creation this is the choice of `ourReply` (`val = true`: `YesWinsInit`; `val = false`:
`noWinsInit_of_not_yesWinsInit` applied to the pass of `K`); our flips and `K`'s partial
decreases are absorbed by `safeYes_transfer` / `safeNo_transfer` (with
`δ z = 2^{-h' z} - 2^{-h z} ≥ 0`, charged to `K` through `kCost`; for our flips the potential
vanishes); a non-cheating flip move of `K` is a legal non-passing opponent move in the
transferred game, answered by `ourReply`.  The outcome functions agree on the positions above the
current one because the other queried strings lie in live play sets of higher priority
(`live_playSets_disjoint`) whose randomness changes only when that requirement acts, which
destroys the game. -/
theorem live_game_safe (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (hg : (stage A γ enumK s).game e = some g) :
    SafeFor (curGame A (reqγ γ) (stage A γ enumK s) e g) (!g.2.2.2.yesTurn) g.2.2.2 := by
  exact ((lg_stage_liveInv A γ enumK s).good e g hg).safe

end Kolmogorov.RandomStrings
