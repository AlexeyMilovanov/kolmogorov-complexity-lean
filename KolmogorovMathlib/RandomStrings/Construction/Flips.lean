/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Mirror
import KolmogorovMathlib.RandomStrings.Construction.Claim3

/-!
# Accounting of our flips: a potential argument

The potential `massPsi σ e` of a requirement (budgets of its destroyed games plus, for its live
game, our score minus `K`'s score) and the stage step `mass_stage_step`: the increase of the mass
caused by our flips is at most the `K`-mass charged to the live games plus the increase of the
potential.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! #### Accounting of our flips: a potential argument

`massPsi σ e` is the potential of requirement `e`: the budgets `2^{-(e+i+6)}` of its games
destroyed by injuries (`i < inj e`) plus, for its live game, our score minus `K`'s score.  In
every stage the increase of the mass caused by our flips is at most the real `K`-mass charged to
the live games plus the increase of the potential (`mass_stage_step`); the charges are disjoint
pieces of `kIncr` (`massDisj_stage`), and the potential stays below `1/32`. -/

/-- Our score in a stored game state (in which `K` is the player to move). -/
def massOurScore (st : GState) : ℝ := if st.yesTurn then st.scoreN else st.scoreY

/-- The potential of requirement `e` at `σ`. -/
noncomputable def massPsi (σ : CState) (e : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (σ.inj e), (2 : ℝ)⁻¹ ^ (e + i + 6) +
    (σ.game e).elim 0 fun g => massOurScore g.2.2.2 - g.2.2.2.moverScore

/-- The potential of the requirements `1, …, N`. -/
noncomputable def massPot (N : ℕ) (σ : CState) : ℝ :=
  ∑ e ∈ Finset.range N, massPsi σ (e + 1)

/-- The increase of `∑_{x ∈ S} 2^{-H*(x)}` from `σ` to `τ`. -/
noncomputable def massIncr (S : Finset BitString) (σ τ : CState) : ℝ :=
  ∑ x ∈ S, ((2 : ℝ)⁻¹ ^ τ.hval x - (2 : ℝ)⁻¹ ^ σ.hval x)

/-- The requirements' part of a stage after processing `R_1, …, R_k`. -/
noncomputable def massFold (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ σ₁ : CState) (k : ℕ) :
    CState × Bool :=
  (List.range k).foldl (fun p e => processReq A γ σ₀ (e + 1) p) (σ₁, false)

/-- Processing one more requirement: the fold over `k + 1` requirements is `processReq` of the
requirement `k + 1` applied to the fold over the first `k` requirements. -/
theorem massFold_succ (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ σ₁ : CState) (k : ℕ) :
    massFold A γ σ₀ σ₁ (k + 1) = processReq A γ σ₀ (k + 1) (massFold A γ σ₀ σ₁ k) := by
  simp [massFold, List.range_succ, List.foldl_append]

section

omit [Family]

/-- The increase of `∑_{x ∈ S} 2^{-H*(x)}` is additive along a chain of states: the increase from
`σ` to `ρ` is the increase from `σ` to `τ` plus the increase from `τ` to `ρ`. -/
theorem massIncr_trans (S : Finset BitString) (σ τ ρ : CState) :
    massIncr S σ ρ = massIncr S σ τ + massIncr S τ ρ := by
  unfold massIncr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- States with the same `F*` and `K*` have the same `H*`, so the mass does not change between
them. -/
theorem massIncr_eq_zero (S : Finset BitString) {σ τ : CState} (hF : τ.Fstar = σ.Fstar)
    (hK : τ.Kstar = σ.Kstar) : massIncr S σ τ = 0 := by
  unfold massIncr
  rw [mass_hval_congr hF hK]
  simp

/-- Our flips `T`, made after the game `g` of `e` has been recorded and followed by the injury of
the requirements of lower priority, raise the mass by at most the flip costs of `T` (exactly
`flipCost` for `|z| ≥ 4`; shorter strings are only lowered to `H* ≥ 3`). -/
theorem massIncr_applyFlips (S T : Finset BitString) (σ : CState) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) :
    massIncr S σ (injure e (applyFlips T (setGame e g σ))) ≤
      ∑ z ∈ T, max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval z) := by
  classical
  generalize hτ : injure e (applyFlips T (setGame e g σ)) = τ
  have hF : τ.Fstar = (applyFlips T σ).Fstar := by subst hτ; rfl
  have hK : τ.Kstar = σ.Kstar := by subst hτ; rfl
  have hpt : ∀ x, (2 : ℝ)⁻¹ ^ τ.hval x - (2 : ℝ)⁻¹ ^ σ.hval x ≤
      if x ∈ T then max 0 ((2 : ℝ)⁻¹ ^ (x.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval x) else 0 := by
    intro x
    split_ifs with hx
    · have hge : min (σ.hval x) (x.length - 1) ≤ τ.hval x := by
        apply mass_le_hval
        rw [mass_coe_min, mass_coe_hval]
        unfold CState.Hstar
        rw [hF, hK]
        simp only [applyFlips, ite_eq_left hx]
        refine le_min ((min_le_left _ _).trans (min_le_left _ _)) ?_
        rcases min_choice (σ.Fstar x) (x.length - 4) with hm | hm
        · rw [hm]; exact (min_le_left _ _).trans (min_le_right _ _)
        · rw [hm]
          refine (min_le_right _ _).trans ?_
          have : x.length - 1 ≤ x.length - 4 + 3 := by omega
          exact_mod_cast this
      have hp : (2 : ℝ)⁻¹ ^ τ.hval x ≤ (2 : ℝ)⁻¹ ^ min (σ.hval x) (x.length - 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hge
      have hm0 := le_max_left (0 : ℝ) ((2 : ℝ)⁻¹ ^ (x.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval x)
      have hm1 := le_max_right (0 : ℝ) ((2 : ℝ)⁻¹ ^ (x.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval x)
      rcases min_choice (σ.hval x) (x.length - 1) with hm | hm
      · rw [hm] at hp; linarith
      · rw [hm] at hp; linarith
    · have hF' : τ.Fstar x = σ.Fstar x := by rw [hF]; simp only [applyFlips, ite_eq_right hx]
      have : τ.hval x = σ.hval x := by
        unfold CState.hval CState.Hstar; rw [hF', hK]
      rw [this]; simp
  calc massIncr S σ τ ≤ ∑ x ∈ S, (if x ∈ T then
          max 0 ((2 : ℝ)⁻¹ ^ (x.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval x) else 0) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x ∈ S.filter (· ∈ T), max 0 ((2 : ℝ)⁻¹ ^ (x.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval x) :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ z ∈ T, max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval z) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.1 hx).2)
          (fun _ _ _ => le_max_left _ _)

/-- After our first move `T` in a new game `d`, our score exceeds the score of `K` (the player to
move) by exactly the cost `moveCost d ∅ T` of the move. -/
theorem massScores_start (d : GameData) (we : Bool) (T : Finset BitString) :
    massOurScore (applyMove d (firstState d we) T) -
      (applyMove d (firstState d we) T).moverScore = moveCost d ∅ T := by
  cases we <;>
    simp [firstState, applyMove, GState.init, massOurScore, GState.moverScore, moveCost_self]

/-- Charging `K`, the player to move, the amount `c` lowers our score minus the score of `K` by
exactly `c`. -/
theorem massScores_charge (st : GState) (c : ℝ) :
    massOurScore (st.charge c) - (st.charge c).moverScore =
      massOurScore st - st.moverScore - c := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [GState.charge, massOurScore, GState.moverScore] <;> ring

/-- When `K` moves to `S'` and is charged `c`, and we answer with the move `T`, our score minus
the score of `K` changes by the cost `moveCost d S' T` of our answer minus `c`. -/
theorem massScores_answer (d : GameData) (st : GState) (S' T : Finset BitString) (c : ℝ) :
    massOurScore (applyMove d (st.kMove S' c) T) - (applyMove d (st.kMove S' c) T).moverScore =
      massOurScore st - st.moverScore + moveCost d S' T - c := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [GState.kMove, GState.charge, applyMove, massOurScore, GState.moverScore] <;>
    ring

/-- The potential `massPsi σ e` of a requirement depends only on its game and on its injury
counter. -/
theorem massPsi_congr {σ τ : CState} {e : ℕ} (hg : σ.game e = τ.game e)
    (hi : σ.inj e = τ.inj e) : massPsi σ e = massPsi τ e := by
  unfold massPsi; rw [hg, hi]

/-- The potential of a requirement whose live game is `g` is the sum of the budgets of its
destroyed games plus our score minus the score of `K` in `g`. -/
theorem massPsi_some {σ : CState} {e : ℕ} {g : BitString × Finset BitString × ℕ × GState}
    (hg : σ.game e = some g) :
    massPsi σ e = ∑ i ∈ Finset.range (σ.inj e), (2 : ℝ)⁻¹ ^ (e + i + 6) +
      (massOurScore g.2.2.2 - g.2.2.2.moverScore) := by
  unfold massPsi; rw [hg]; try rfl

/-- The potential of a requirement without a live game is the sum of the budgets of its destroyed
games. -/
theorem massPsi_none {σ : CState} {e : ℕ} (hg : σ.game e = none) :
    massPsi σ e = ∑ i ∈ Finset.range (σ.inj e), (2 : ℝ)⁻¹ ^ (e + i + 6) := by
  unfold massPsi; rw [hg]; simp

/-- If no requirement other than `e ∈ [1, N]` loses potential from `σ` to `σ'`, the increase of the
total potential `massPot N` is at least the increase of the potential of `e`. -/
theorem massPot_sub_ge (N e : ℕ) (he : 1 ≤ e) (heN : e ≤ N) (σ σ' : CState)
    (h : ∀ e', e' ≠ e → massPsi σ e' ≤ massPsi σ' e') :
    massPsi σ' e - massPsi σ e ≤ massPot N σ' - massPot N σ := by
  classical
  unfold massPot
  rw [← Finset.sum_sub_distrib]
  have hmem : e - 1 ∈ Finset.range N := Finset.mem_range.2 (by omega)
  rw [← Finset.add_sum_erase _ _ hmem]
  have he1 : e - 1 + 1 = e := by omega
  rw [he1]
  have : 0 ≤ ∑ x ∈ (Finset.range N).erase (e - 1),
      (massPsi σ' (x + 1) - massPsi σ (x + 1)) := by
    apply Finset.sum_nonneg
    intro x hx
    have hx' : x ≠ e - 1 := Finset.ne_of_mem_erase hx
    have := h (x + 1) (by omega)
    linarith
  linarith

/-- When a requirement `e < e'` acts, the potential of `e'` does not decrease, provided that in its
live game (if any) our score minus the score of `K` is at most the budget `2^{-(e'+i+6)}`: the
game is destroyed and this budget is added to the sum over the destroyed games. -/
theorem massPsi_injure_ge (e e' : ℕ) (hee : e < e') (τ : CState)
    (hb : ∀ g, τ.game e' = some g →
      massOurScore g.2.2.2 - g.2.2.2.moverScore ≤ (2 : ℝ)⁻¹ ^ (e' + τ.inj e' + 6)) :
    massPsi τ e' ≤ massPsi (injure e τ) e' := by
  have h1 : (injure e τ).game e' = none := by simp [injure, hee]
  have h2 : (injure e τ).inj e' = τ.inj e' + 1 := by simp [injure, hee]
  rw [massPsi_none h1, h2, Finset.sum_range_succ]
  cases hg : τ.game e' with
  | none =>
    rw [massPsi_none hg]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) (e' + τ.inj e' + 6)]
  | some g => rw [massPsi_some hg]; linarith [hb g hg]

/-- Let `τ` agree with `σ` off `e`, with the same injury counters.  If in every live game of lower
priority our score minus the score of `K` is at most its budget, then the increase of the potential
of `e` from `σ` to `τ` is at most the increase of the total potential `massPot N` from `σ` to the
injured state `injure e τ`. -/
theorem massPot_injure_ge (N e : ℕ) (he : 1 ≤ e) (heN : e ≤ N) (σ τ : CState)
    (hτg : ∀ e', e' ≠ e → τ.game e' = σ.game e') (hτi : τ.inj = σ.inj)
    (hb : ∀ e', e < e' → ∀ g, σ.game e' = some g →
      massOurScore g.2.2.2 - g.2.2.2.moverScore ≤ (2 : ℝ)⁻¹ ^ (e' + σ.inj e' + 6)) :
    massPsi τ e - massPsi σ e ≤ massPot N (injure e τ) - massPot N σ := by
  have hτe : massPsi (injure e τ) e = massPsi τ e :=
    massPsi_congr (by simp [injure]) (by simp [injure])
  rw [← hτe]
  refine massPot_sub_ge N e he heN σ (injure e τ) fun e' hne => ?_
  have hc : massPsi σ e' = massPsi τ e' := massPsi_congr (hτg e' hne).symm (by rw [hτi])
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [hc]
    exact le_of_eq (massPsi_congr (by simp [injure, not_lt.2 hlt.le])
      (by simp [injure, not_lt.2 hlt.le])).symm
  · rw [hc]
    refine massPsi_injure_ge e e' hgt τ fun g hg => ?_
    rw [hτg e' hne] at hg
    rw [hτi]
    exact hb e' hgt g hg

end

/-- Starting a game on the witness `x` for the requirement `e ∈ [1, N]`, where `σ` has no game for
`e`, raises the mass by at most the increase of the potential `massPot N`: the increase caused by
our first flips is their flip cost, which is our score in the new game.  This assumes that in every
live game of lower priority our score minus the score of `K` is at most its budget. -/
theorem mass_start_step (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (N e : ℕ) (he : 1 ≤ e)
    (heN : e ≤ N) (S : Finset BitString) (σ : CState) (hg : σ.game e = none) (x : BitString)
    (hb : ∀ e', e < e' → ∀ g, σ.game e' = some g →
      massOurScore g.2.2.2 - g.2.2.2.moverScore ≤ (2 : ℝ)⁻¹ ^ (e' + σ.inj e' + 6)) :
    massIncr S σ (startOn A γ e σ x).1 ≤ massPot N (startOn A γ e σ x).1 - massPot N σ := by
  have hd : (newGame A γ σ e x).h₀ = σ.hval := rfl
  unfold startOn
  dsimp only
  generalize newGame A γ σ e x = d at hd ⊢
  generalize val d = we
  generalize playSet γ σ e x = X
  generalize e + σ.inj e + 6 = m
  generalize ourReply d we (firstState d we) = T
  have h1 := massIncr_applyFlips S T σ e (x, X, m, applyMove d (firstState d we) T)
  have h2 := massPot_injure_ge N e he heN σ
    (applyFlips T (setGame e (x, X, m, applyMove d (firstState d we) T) σ))
    (fun e' hne => by simp only [applyFlips, setGame]; exact Function.update_of_ne hne _ _) rfl hb
  have h3 : massPsi (applyFlips T (setGame e (x, X, m, applyMove d (firstState d we) T) σ)) e -
      massPsi σ e = moveCost d ∅ T := by
    rw [massPsi_some (g := (x, X, m, applyMove d (firstState d we) T))
      (by simp [applyFlips, setGame]), massPsi_none hg]
    simp only [show (applyFlips T (setGame e (x, X, m, applyMove d (firstState d we) T) σ)).inj =
      σ.inj from rfl]
    have := massScores_start d we T
    linarith
  have h4 : moveCost d ∅ T =
      ∑ z ∈ T, max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval z) := by
    unfold moveCost flipCost; rw [Finset.sdiff_empty, hd]
  linarith

section

omit [Family]

/-- When `K` cheats in the live game `g` of `e` (its score plus the real charge `c` exceeds the
budget while our score is within it), the game is destroyed and the requirements of lower priority
are injured.  No mass is created, so the mass increase is at most `c` plus the increase of the
potential. -/
theorem mass_cheat_step (N e : ℕ) (he : 1 ≤ e) (heN : e ≤ N) (S : Finset BitString) (σ : CState)
    (g : BitString × Finset BitString × ℕ × GState) (hg : σ.game e = some g) (c : ℝ)
    (hcheat : (2 : ℝ)⁻¹ ^ g.2.2.1 < g.2.2.2.moverScore + c)
    (hour : massOurScore g.2.2.2 ≤ (2 : ℝ)⁻¹ ^ g.2.2.1)
    (hb : ∀ e', e < e' → ∀ g, σ.game e' = some g →
      massOurScore g.2.2.2 - g.2.2.2.moverScore ≤ (2 : ℝ)⁻¹ ^ (e' + σ.inj e' + 6)) :
    massIncr S σ (injure e (destroy e σ)) ≤
      c + (massPot N (injure e (destroy e σ)) - massPot N σ) := by
  have h1 : massIncr S σ (injure e (destroy e σ)) = 0 := massIncr_eq_zero S rfl rfl
  have h2 := massPot_injure_ge N e he heN σ (destroy e σ)
    (fun e' hne => by simp only [destroy]; exact Function.update_of_ne hne _ _) rfl hb
  have h3 : massPsi (destroy e σ) e - massPsi σ e =
      -(massOurScore g.2.2.2 - g.2.2.2.moverScore) := by
    rw [massPsi_none (by simp [destroy]), massPsi_some hg]
    simp only [show (destroy e σ).inj = σ.inj from rfl]
    ring
  linarith

/-- Recording the real charge `c` against `K` in the live game `g` of `e` creates no mass; the
mass increase is at most `c` plus the increase of the potential. -/
theorem mass_charge_step (N e : ℕ) (he : 1 ≤ e) (heN : e ≤ N) (S : Finset BitString) (σ : CState)
    (g : BitString × Finset BitString × ℕ × GState) (hg : σ.game e = some g) (c : ℝ) :
    massIncr S σ (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c) σ) ≤
      c + (massPot N (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c) σ) - massPot N σ) := by
  have h1 : massIncr S σ (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c) σ) = 0 :=
    massIncr_eq_zero S rfl rfl
  have h2 := massPot_sub_ge N e he heN σ (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c) σ)
    (fun e' hne => le_of_eq (massPsi_congr
      (by simp only [setGame]; exact (Function.update_of_ne hne _ _).symm) rfl))
  have h3 : massPsi (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c) σ) e - massPsi σ e =
      -c := by
    rw [massPsi_some (g := (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c)) (by simp [setGame]),
      massPsi_some hg]
    simp only [show (setGame e (g.1, g.2.1, g.2.2.1, g.2.2.2.charge c) σ).inj = σ.inj from rfl]
    have := massScores_charge g.2.2.2 c
    linarith
  linarith

end

/-- When `K` moves to `S'` in the live game `g` of `e` and is charged `c`, and we answer with the
move `T` of the game `curGame A γ σ e g` and flip the strings of `T \ S'`, the mass increase is at
most `c` plus the increase of the potential. -/
theorem mass_answer_step (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (N e : ℕ) (he : 1 ≤ e)
    (heN : e ≤ N) (S : Finset BitString) (σ : CState)
    (g : BitString × Finset BitString × ℕ × GState) (hg : σ.game e = some g)
    (S' T : Finset BitString) (c : ℝ)
    (hb : ∀ e', e < e' → ∀ g, σ.game e' = some g →
      massOurScore g.2.2.2 - g.2.2.2.moverScore ≤ (2 : ℝ)⁻¹ ^ (e' + σ.inj e' + 6)) :
    massIncr S σ (injure e (applyFlips (T \ S') (setGame e (g.1, g.2.1, g.2.2.1,
      applyMove (curGame A γ σ e g) (g.2.2.2.kMove S' c) T) σ))) ≤
      c + (massPot N (injure e (applyFlips (T \ S') (setGame e (g.1, g.2.1, g.2.2.1,
        applyMove (curGame A γ σ e g) (g.2.2.2.kMove S' c) T) σ))) - massPot N σ) := by
  have hd : (curGame A γ σ e g).h₀ = σ.hval := rfl
  generalize curGame A γ σ e g = d at hd ⊢
  have h1 := massIncr_applyFlips S (T \ S') σ e
    (g.1, g.2.1, g.2.2.1, applyMove d (g.2.2.2.kMove S' c) T)
  have h2 := massPot_injure_ge N e he heN σ (applyFlips (T \ S')
      (setGame e (g.1, g.2.1, g.2.2.1, applyMove d (g.2.2.2.kMove S' c) T) σ))
    (fun e' hne => by simp only [applyFlips, setGame]; exact Function.update_of_ne hne _ _) rfl hb
  have h3 : massPsi (applyFlips (T \ S')
      (setGame e (g.1, g.2.1, g.2.2.1, applyMove d (g.2.2.2.kMove S' c) T) σ)) e -
      massPsi σ e = moveCost d S' T - c := by
    rw [massPsi_some (g := (g.1, g.2.1, g.2.2.1, applyMove d (g.2.2.2.kMove S' c) T))
      (by simp [applyFlips, setGame]), massPsi_some hg]
    simp only [show (applyFlips (T \ S') (setGame e (g.1, g.2.1, g.2.2.1,
      applyMove d (g.2.2.2.kMove S' c) T) σ)).inj = σ.inj from rfl]
    have := massScores_answer d g.2.2.2 S' T c
    linarith
  have h4 : moveCost d S' T =
      ∑ z ∈ T \ S', max 0 ((2 : ℝ)⁻¹ ^ (z.length - 1) - (2 : ℝ)⁻¹ ^ σ.hval z) := by
    unfold moveCost flipCost; rw [hd]
  linarith

/-- One requirement step of a stage: processing the requirement `k + 1` raises the mass by at most
the real `K`-mass charged to its game plus the increase of the potential.  Moreover, as long as
nobody has acted, the state agrees with the `K`-updated state `σ₁` on `F*` and `K*`, and with the
initial state `σ₀` of the stage on the games and injury counters of the requirements not yet
processed. -/
theorem mass_processReq_step (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ σ₁ : CState) (N : ℕ)
    (S : Finset BitString)
    (hbound : ∀ e g, σ₀.game e = some g → g.2.2.1 = e + σ₀.inj e + 6 ∧
      massOurScore g.2.2.2 ≤ (2 : ℝ)⁻¹ ^ g.2.2.1 ∧ 0 ≤ g.2.2.2.moverScore)
    (k : ℕ) (heN : k + 1 ≤ N) (p : CState × Bool)
    (hinv : p.2 = false → p.1.Fstar = σ₁.Fstar ∧ p.1.Kstar = σ₁.Kstar ∧
      ∀ e', k + 1 ≤ e' → p.1.game e' = σ₀.game e' ∧ p.1.inj e' = σ₀.inj e')
    (hch : 0 ≤ (σ₀.game (k + 1)).elim 0 fun g => kCost σ₀ σ₁ g.2.1) :
    massIncr S p.1 (processReq A γ σ₀ (k + 1) p).1 ≤
        ((σ₀.game (k + 1)).elim 0 fun g => kCost σ₀ σ₁ g.2.1) +
        (massPot N (processReq A γ σ₀ (k + 1) p).1 - massPot N p.1) ∧
      ((processReq A γ σ₀ (k + 1) p).2 = false →
        (processReq A γ σ₀ (k + 1) p).1.Fstar = σ₁.Fstar ∧
        (processReq A γ σ₀ (k + 1) p).1.Kstar = σ₁.Kstar ∧
        ∀ e', k + 1 + 1 ≤ e' → (processReq A γ σ₀ (k + 1) p).1.game e' = σ₀.game e' ∧
          (processReq A γ σ₀ (k + 1) p).1.inj e' = σ₀.inj e') := by
  classical
  generalize hek : k + 1 = e at heN hinv hch ⊢
  have he : 1 ≤ e := by omega
  by_cases hp : p.2 = true
  · have hpr : processReq A γ σ₀ e p = p := by unfold processReq; rw [ite_eq_left hp]
    rw [hpr, massIncr_eq_zero S rfl rfl, sub_self, add_zero]
    exact ⟨hch, fun h => absurd (h.symm.trans hp) (by decide)⟩
  have hpf : p.2 = false := by simpa using hp
  obtain ⟨hF, hK, hG⟩ := hinv hpf
  have hval : p.1.hval = σ₁.hval := mass_hval_congr hF hK
  have hb : ∀ e', e < e' → ∀ g, p.1.game e' = some g →
      massOurScore g.2.2.2 - g.2.2.2.moverScore ≤ (2 : ℝ)⁻¹ ^ (e' + p.1.inj e' + 6) := by
    intro e' hee g hg'
    obtain ⟨hg1, hi1⟩ := hG e' hee.le
    rw [hg1] at hg'
    obtain ⟨hm, hour, hK0⟩ := hbound e' g hg'
    rw [hi1, ← hm]
    linarith
  obtain ⟨hGe, -⟩ := hG e le_rfl
  cases hge : p.1.game e with
  | none =>
    have hσ₀ : σ₀.game e = none := hGe.symm.trans hge
    have hpr : processReq A γ σ₀ e p = startGame A γ e p.1 := by
      unfold processReq; simp [hpf, hge]
    rw [hpr, hσ₀]
    simp only [Option.elim]
    unfold startGame
    cases hw : chooseWitness A γ p.1 e with
    | none =>
      dsimp only
      refine ⟨by simp [massIncr], fun _ => ⟨hF, hK, fun e' he' => hG e' (by omega)⟩⟩
    | some x =>
      dsimp only
      refine ⟨?_, fun h => by simp [startOn] at h⟩
      rw [zero_add]
      exact mass_start_step A γ N e he heN S p.1 hge x hb
  | some g =>
    have hσ₀ : σ₀.game e = some g := hGe.symm.trans hge
    have hpr : processReq A γ σ₀ e p = processGame A γ σ₀ e g p.1 := by
      unfold processReq; simp [hpf, hge]
    have hkc : kCost σ₀ p.1 g.2.1 = kCost σ₀ σ₁ g.2.1 := by unfold kCost; rw [hval]
    obtain ⟨hm, hour, hK0⟩ := hbound e g hσ₀
    rw [hpr, hσ₀]
    simp only [Option.elim]
    rw [← hkc]
    unfold processGame
    split_ifs with h1 h2
    · refine ⟨?_, fun h => by simp at h⟩
      exact mass_cheat_step N e he heN S p.1 g hge _ h1 hour hb
    · refine ⟨mass_charge_step N e he heN S p.1 g hge _, fun _ => ⟨hF, hK, fun e' he' => ?_⟩⟩
      obtain ⟨h3, h4⟩ := hG e' (by omega)
      refine ⟨?_, h4⟩
      simp only [setGame]
      rw [Function.update_of_ne (by omega)]
      exact h3
    · refine ⟨?_, fun h => by simp at h⟩
      exact mass_answer_step A γ N e he heN S p.1 g hge _ _ _ hb

/-- The mass increase over the first `k` requirements of a stage, started from the `K`-updated
state `σ₁`, is at most the `K`-mass charged to their live games plus the increase of the potential.
Moreover, as long as nobody has acted, the state agrees with `σ₁` on `F*` and `K*`, and with the
initial state `σ₀` of the stage on the games and injury counters of the requirements not yet
processed. -/
theorem massFold_bound (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ σ₁ : CState) (N : ℕ)
    (S : Finset BitString)
    (hbound : ∀ e g, σ₀.game e = some g → g.2.2.1 = e + σ₀.inj e + 6 ∧
      massOurScore g.2.2.2 ≤ (2 : ℝ)⁻¹ ^ g.2.2.1 ∧ 0 ≤ g.2.2.2.moverScore)
    (hgame : σ₁.game = σ₀.game) (hinj : σ₁.inj = σ₀.inj)
    (hch : ∀ e, 0 ≤ (σ₀.game e).elim 0 fun g => kCost σ₀ σ₁ g.2.1) (k : ℕ) (hk : k ≤ N) :
    massIncr S σ₁ (massFold A γ σ₀ σ₁ k).1 ≤
        ∑ e ∈ Finset.range k, ((σ₀.game (e + 1)).elim 0 fun g => kCost σ₀ σ₁ g.2.1) +
          (massPot N (massFold A γ σ₀ σ₁ k).1 - massPot N σ₁) ∧
      ((massFold A γ σ₀ σ₁ k).2 = false →
        (massFold A γ σ₀ σ₁ k).1.Fstar = σ₁.Fstar ∧ (massFold A γ σ₀ σ₁ k).1.Kstar = σ₁.Kstar ∧
        ∀ e', k + 1 ≤ e' → (massFold A γ σ₀ σ₁ k).1.game e' = σ₀.game e' ∧
          (massFold A γ σ₀ σ₁ k).1.inj e' = σ₀.inj e') := by
  induction k with
  | zero =>
    have h0 : massFold A γ σ₀ σ₁ 0 = (σ₁, false) := rfl
    rw [h0]
    exact ⟨by simp [massIncr], fun _ => ⟨rfl, rfl, fun e' _ =>
      ⟨congrFun hgame e', congrFun hinj e'⟩⟩⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [massFold_succ]
    obtain ⟨h1, h2⟩ := mass_processReq_step A γ σ₀ σ₁ N S hbound k hk _ ih2 (hch _)
    refine ⟨?_, h2⟩
    rw [massIncr_trans S σ₁ (massFold A γ σ₀ σ₁ k).1, Finset.sum_range_succ]
    linarith

/-- Stage `t + 1` is obtained from stage `t` by updating `K*` with the `t`-th enumerated pair of
`ov K` and then processing the requirements `R_1, …, R_{t+1}` in turn (`massFold`). -/
theorem mass_stage_succ_eq (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ) :
    stage A γ enumK (t + 1) = (massFold A (reqγ γ) (stage A γ enumK t)
      (updateK enumK t (stage A γ enumK t)) (t + 1)).1 := by
  change stageStep A γ enumK (t + 1) (stage A γ enumK t) = _
  unfold stageStep massFold
  rw [Nat.add_sub_cancel]

/-- The invariant of the live games used by the accounting: a live game `g = (x, X, m, st)` of
`e` has budget exponent `m = e + i_e + 6`, our score in it is within its budget `2^{-m}`, and
`K`'s score in it is nonnegative. -/
def MassLive (σ : CState) : Prop :=
  ∀ e g, σ.game e = some g → g.2.2.1 = e + σ.inj e + 6 ∧
    massOurScore g.2.2.2 ≤ (2 : ℝ)⁻¹ ^ g.2.2.1 ∧ 0 ≤ g.2.2.2.moverScore

section

omit [Family]

/-- After the player to move in `st` plays `T`, the score of the player who has just moved is their
previous score plus the cost `moveCost d st.S T` of the move. -/
theorem mass_our_applyMove (d : GameData) (st : GState) (T : Finset BitString) :
    massOurScore (applyMove d st T) = st.moverScore + moveCost d st.S T := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [applyMove, massOurScore, GState.moverScore]

/-- A move changes only the score of the player who makes it: after the move, the score of the
new player to move is the score `massOurScore st` of the player who was not to move in `st`. -/
theorem mass_mover_applyMove (d : GameData) (st : GState) (T : Finset BitString) :
    (applyMove d st T).moverScore = massOurScore st := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [applyMove, massOurScore, GState.moverScore]

/-- Charging the player to move does not change the score of the other player. -/
theorem mass_our_charge (st : GState) (c : ℝ) : massOurScore (st.charge c) = massOurScore st := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [GState.charge, massOurScore]

/-- Charging the player to move the amount `c` raises their score by exactly `c`. -/
theorem mass_mover_charge (st : GState) (c : ℝ) :
    (st.charge c).moverScore = st.moverScore + c := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [GState.charge, GState.moverScore]

/-- After the move `kMove S' c` of `K`, the player to move is the one who was not to move in `st`,
with the same score `massOurScore st`. -/
theorem mass_mover_kMove (st : GState) (S' : Finset BitString) (c : ℝ) :
    (st.kMove S' c).moverScore = massOurScore st := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [GState.kMove, GState.charge, GState.moverScore, massOurScore]

/-- After the move `kMove S' c` of `K`, the score of the player who is not to move, namely `K`, is
its previous score plus the charge `c`. -/
theorem mass_our_kMove (st : GState) (S' : Finset BitString) (c : ℝ) :
    massOurScore (st.kMove S' c) = st.moverScore + c := by
  rcases st with ⟨S, y, n, b⟩
  cases b <;> simp [GState.kMove, GState.charge, GState.moverScore, massOurScore]

/-- `ourReply` is a legal move or a pass. -/
theorem mass_ourReply_spec (d : GameData) (we : Bool) (st : GState) :
    LegalMove d st (ourReply d we st) ∨ ourReply d we st = st.S := by
  classical
  unfold ourReply
  split_ifs with h
  · exact Or.inl (Nat.find_spec h).1
  · exact Or.inr rfl

/-- After our reply our score is within the budget. -/
theorem mass_our_reply_le (d : GameData) (we : Bool) (st : GState) (h : st.moverScore ≤ d.ε) :
    massOurScore (applyMove d st (ourReply d we st)) ≤ d.ε := by
  rw [mass_our_applyMove]
  rcases mass_ourReply_spec d we st with hL | hS
  · obtain ⟨-, -, h3⟩ := hL
    unfold GState.moverScore
    split_ifs at h3 ⊢ <;> linarith
  · rw [hS, moveCost_self, add_zero]; exact h

end

/-- Starting a game keeps `MassLive`: the new game has budget exponent `e + i_e + 6`, our first
reply keeps our score within the budget `2^{-(e+i_e+6)}`, the score of `K` is `0`, and the games of
lower priority are destroyed. -/
theorem mass_live_start (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ)
    (hI : MassLive σ) (x : BitString) : MassLive (startOn A γ e σ x).1 := by
  have hε : (newGame A γ σ e x).ε = (2 : ℝ)⁻¹ ^ (e + σ.inj e + 6) := rfl
  unfold startOn
  dsimp only
  generalize newGame A γ σ e x = d at hε ⊢
  generalize val d = we
  generalize playSet γ σ e x = X
  generalize hT : ourReply d we (firstState d we) = T
  intro e' g hg
  simp only [injure, applyFlips, setGame] at hg ⊢
  by_cases hlt : e < e'
  · rw [ite_eq_left hlt] at hg; simp at hg
  · rw [ite_eq_right hlt] at hg ⊢
    by_cases he' : e' = e
    · rw [he'] at hg ⊢
      rw [Function.update_self] at hg
      cases hg
      have hm0 : (firstState d we).moverScore = 0 := by
        cases we <;> simp [firstState, GState.init, applyMove, GState.moverScore]
      have hK0 : massOurScore (firstState d we) = 0 := by
        cases we <;> simp [firstState, GState.init, applyMove, massOurScore, moveCost_self]
      refine ⟨rfl, ?_, ?_⟩
      · change massOurScore (applyMove d (firstState d we) T) ≤ (2 : ℝ)⁻¹ ^ (e + σ.inj e + 6)
        rw [← hε, ← hT]
        exact mass_our_reply_le d we _ (by rw [hm0, hε]; positivity)
      · change 0 ≤ (applyMove d (firstState d we) T).moverScore
        simp [mass_mover_applyMove, hK0]
    · rw [Function.update_of_ne he'] at hg
      exact hI e' g hg

section

omit [Family]

/-- Destroying the game of `e` and injuring the requirements of lower priority preserves
`MassLive`. -/
theorem mass_live_destroy (σ : CState) (e : ℕ) (hI : MassLive σ) :
    MassLive (injure e (destroy e σ)) := by
  intro e' g hg
  simp only [injure, destroy] at hg ⊢
  by_cases hlt : e < e'
  · rw [ite_eq_left hlt] at hg; simp at hg
  · rw [ite_eq_right hlt] at hg ⊢
    by_cases he' : e' = e
    · rw [he', Function.update_self] at hg; simp at hg
    · rw [Function.update_of_ne he'] at hg
      exact hI e' g hg

/-- Charging `K` a nonnegative amount `c` in the live game of `e` preserves `MassLive`. -/
theorem mass_live_charge (σ : CState) (e : ℕ) (hI : MassLive σ)
    (g₀ : BitString × Finset BitString × ℕ × GState) (hg₀ : σ.game e = some g₀) (c : ℝ)
    (hc : 0 ≤ c) :
    MassLive (setGame e (g₀.1, g₀.2.1, g₀.2.2.1, g₀.2.2.2.charge c) σ) := by
  intro e' g hg
  simp only [setGame] at hg ⊢
  by_cases he' : e' = e
  · rw [he'] at hg ⊢
    rw [Function.update_self] at hg
    cases hg
    obtain ⟨hm, hour, hK0⟩ := hI e g₀ hg₀
    refine ⟨hm, ?_, ?_⟩
    · change massOurScore (g₀.2.2.2.charge c) ≤ (2 : ℝ)⁻¹ ^ g₀.2.2.1
      rw [mass_our_charge]; exact hour
    · change 0 ≤ (g₀.2.2.2.charge c).moverScore
      rw [mass_mover_charge]; linarith
  · rw [Function.update_of_ne he'] at hg
    exact hI e' g hg

end

/-- Answering a move of `K` in the live game of `e` with `ourReply`, then flipping any set `U` and
injuring the requirements of lower priority, preserves `MassLive`: our reply keeps our score within
the budget and the score of `K` stays nonnegative. -/
theorem mass_live_answer (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ : CState) (e : ℕ)
    (hI : MassLive σ) (g₀ : BitString × Finset BitString × ℕ × GState)
    (hg₀ : σ.game e = some g₀) (we : Bool) (S' : Finset BitString) (c : ℝ) (hc : 0 ≤ c)
    (U : Finset BitString) :
    MassLive (injure e (applyFlips U (setGame e (g₀.1, g₀.2.1, g₀.2.2.1,
      applyMove (curGame A γ σ e g₀) (g₀.2.2.2.kMove S' c)
        (ourReply (curGame A γ σ e g₀) we (g₀.2.2.2.kMove S' c))) σ))) := by
  have hε : (curGame A γ σ e g₀).ε = (2 : ℝ)⁻¹ ^ g₀.2.2.1 := rfl
  generalize curGame A γ σ e g₀ = d at hε ⊢
  generalize hT : ourReply d we (g₀.2.2.2.kMove S' c) = T
  intro e' g hg
  simp only [injure, applyFlips, setGame] at hg ⊢
  by_cases hlt : e < e'
  · rw [ite_eq_left hlt] at hg; simp at hg
  · rw [ite_eq_right hlt] at hg ⊢
    by_cases he' : e' = e
    · rw [he'] at hg ⊢
      rw [Function.update_self] at hg
      cases hg
      obtain ⟨hm, hour, hK0⟩ := hI e g₀ hg₀
      refine ⟨hm, ?_, ?_⟩
      · change massOurScore (applyMove d (g₀.2.2.2.kMove S' c) T) ≤ (2 : ℝ)⁻¹ ^ g₀.2.2.1
        rw [← hε, ← hT]
        exact mass_our_reply_le d we _ (by rw [mass_mover_kMove, hε]; exact hour)
      · change 0 ≤ (applyMove d (g₀.2.2.2.kMove S' c) T).moverScore
        rw [mass_mover_applyMove, mass_our_kMove]; linarith
    · rw [Function.update_of_ne he'] at hg
      exact hI e' g hg

/-- One requirement step preserves `MassLive` (before anybody acts in the stage, `H*` is the
`K`-updated `H*`, which is below the `H*` of the beginning of the stage, so `kCost ≥ 0`). -/
theorem mass_processReq_live (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ σ₁ : CState) (e : ℕ)
    (hle : ∀ z, σ₁.hval z ≤ σ₀.hval z) (p : CState × Bool)
    (hval : p.2 = false → p.1.hval = σ₁.hval) (hI : MassLive p.1) :
    MassLive (processReq A γ σ₀ e p).1 := by
  classical
  by_cases hp : p.2 = true
  · have hpr : processReq A γ σ₀ e p = p := by unfold processReq; rw [ite_eq_left hp]
    rw [hpr]; exact hI
  have hpf : p.2 = false := by simpa using hp
  have hv := hval hpf
  have hc0 : ∀ X, 0 ≤ kCost σ₀ p.1 X := by
    intro X; unfold kCost; apply Finset.sum_nonneg; intro z _
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
      (show p.1.hval z ≤ σ₀.hval z by rw [hv]; exact hle z)
    linarith
  cases hge : p.1.game e with
  | none =>
    have hpr : processReq A γ σ₀ e p = startGame A γ e p.1 := by
      unfold processReq; simp [hpf, hge]
    rw [hpr]
    unfold startGame
    cases hw : chooseWitness A γ p.1 e with
    | none => exact hI
    | some x => exact mass_live_start A γ p.1 e hI x
  | some g =>
    have hpr : processReq A γ σ₀ e p = processGame A γ σ₀ e g p.1 := by
      unfold processReq; simp [hpf, hge]
    rw [hpr]
    unfold processGame
    split_ifs with h1 h2
    · exact mass_live_destroy p.1 e hI
    · exact mass_live_charge p.1 e hI g hge _ (hc0 _)
    · exact mass_live_answer A γ p.1 e hI g hge _ _ _ (hc0 _) _

omit [Family] in
/-- The `K`-update of a stage leaves the games in progress unchanged. -/
theorem mass_updateK_game (enumK : ℕ → BitString × ℕ) (t : ℕ) (σ : CState) :
    (updateK enumK t σ).game = σ.game :=
  rfl

omit [Family] in
/-- The `K`-update of a stage leaves the injury counters unchanged. -/
theorem mass_updateK_inj (enumK : ℕ → BitString × ℕ) (t : ℕ) (σ : CState) :
    (updateK enumK t σ).inj = σ.inj :=
  rfl

/-- Processing the first `k` requirements of a stage, from the state `updateK enumK t σ₀` obtained
from `σ₀` by the `K`-update, preserves `MassLive`. -/
theorem mass_fold_live (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t : ℕ) (σ₀ : CState) (hI : MassLive σ₀) (k : ℕ) :
    MassLive (massFold A γ σ₀ (updateK enumK t σ₀) k).1 := by
  have hch : ∀ e, 0 ≤ (σ₀.game e).elim 0 fun g => kCost σ₀ (updateK enumK t σ₀) g.2.1 := by
    intro e
    cases hg : σ₀.game e with
    | none => exact le_rfl
    | some g =>
      change 0 ≤ kCost σ₀ (updateK enumK t σ₀) g.2.1
      unfold kCost; apply Finset.sum_nonneg; intro z _
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
        (mass_hval_updateK_le enumK t σ₀ z)
      linarith
  induction k with
  | zero =>
    change MassLive (updateK enumK t σ₀)
    intro e g hg
    rw [mass_updateK_game] at hg
    rw [mass_updateK_inj]
    exact hI e g hg
  | succ k ih =>
    rw [massFold_succ]
    have hinv := (massFold_bound A γ σ₀ (updateK enumK t σ₀) k ∅ hI
      (mass_updateK_game enumK t σ₀) (mass_updateK_inj enumK t σ₀) hch k le_rfl).2
    exact mass_processReq_live A γ σ₀ (updateK enumK t σ₀) (k + 1)
      (mass_hval_updateK_le enumK t σ₀) _
      (fun h => mass_hval_congr (hinv h).1 (hinv h).2.1) ih

/-- At every stage, a live game `g = (x, X, m, st)` of `e` has budget exponent `m = e + i_e + 6`,
our score in it is within its budget `2^{-m}`, and `K`'s score in it is nonnegative. -/
theorem mass_live_bound (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (s e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (hg : (stage A γ enumK s).game e = some g) :
    g.2.2.1 = e + (stage A γ enumK s).inj e + 6 ∧ massOurScore g.2.2.2 ≤ (2 : ℝ)⁻¹ ^ g.2.2.1 ∧
      0 ≤ g.2.2.2.moverScore := by
  have key : ∀ s, MassLive (stage A γ enumK s) := by
    intro s
    induction s with
    | zero => intro e g hg; simp [stage, CState.init] at hg
    | succ t ih =>
      rw [mass_stage_succ_eq]
      exact mass_fold_live A (reqγ γ) enumK t (stage A γ enumK t) ih (t + 1)
  exact key s e g hg

/-- The play set of the game of `e` (empty if there is none). -/
noncomputable def massX (σ : CState) (e : ℕ) : Finset BitString := (σ.game e).elim ∅ fun g => g.2.1

/-- The play sets of distinct requirements are disjoint. -/
def MassDisj (σ : CState) : Prop := ∀ e e', e ≠ e' → Disjoint (massX σ e) (massX σ e')

section

omit [Family]

/-- `MassDisj` passes from a state to any state whose play sets are contained in its play sets. -/
theorem massDisj_mono {σ σ' : CState} (h : ∀ e, massX σ' e ⊆ massX σ e) (hD : MassDisj σ) :
    MassDisj σ' :=
  fun e e' hne => (hD e e' hne).mono (h e) (h e')

/-- `MassDisj` depends only on the games in progress: of two states with the same games, one
satisfies it as soon as the other does. -/
theorem massDisj_congr {σ τ : CState} (h : σ.game = τ.game) (hD : MassDisj σ) : MassDisj τ := by
  intro e e' hne
  have := hD e e' hne
  unfold massX at this ⊢
  rwa [h] at this

/-- Injuring the requirements of lower priority never enlarges a play set. -/
theorem massX_injure (e : ℕ) (τ : CState) (e' : ℕ) : massX (injure e τ) e' ⊆ massX τ e' := by
  unfold massX
  simp only [injure]
  split_ifs
  · exact Finset.empty_subset _
  · exact subset_rfl

/-- Destroying a game never enlarges a play set. -/
theorem massX_destroy (e : ℕ) (τ : CState) (e' : ℕ) : massX (destroy e τ) e' ⊆ massX τ e' := by
  unfold massX
  simp only [destroy]
  by_cases he : e' = e
  · rw [he, Function.update_self]; exact Finset.empty_subset _
  · rw [Function.update_of_ne he]

/-- Our flips leave the games untouched, so they do not enlarge any play set. -/
theorem massX_applyFlips (T : Finset BitString) (τ : CState) (e' : ℕ) :
    massX (applyFlips T τ) e' ⊆ massX τ e' := subset_rfl

/-- Replacing the live game `g` of `e` by a game on the same strings (with another witness,
budget exponent or state) does not enlarge any play set. -/
theorem massX_setGame_le (τ : CState) (e : ℕ) (g : BitString × Finset BitString × ℕ × GState)
    (hg : τ.game e = some g) (x : BitString) (m : ℕ) (st : GState) (e' : ℕ) :
    massX (setGame e (x, g.2.1, m, st) τ) e' ⊆ massX τ e' := by
  unfold massX
  simp only [setGame]
  by_cases he : e' = e
  · rw [he, Function.update_self, hg]; exact subset_rfl
  · rw [Function.update_of_ne he]

/-- A new game avoids the play sets of the live games of higher priority and destroys those of
lower priority. -/
theorem massDisj_start (σ : CState) (e : ℕ) (hD : MassDisj σ) (T Q : Finset BitString)
    (x : BitString) (m : ℕ) (st : GState) :
    MassDisj (injure e (applyFlips T (setGame e (x, Q \ (Finset.range e).biUnion
      (fun e' => (σ.game e').elim ∅ fun g => g.2.1), m, st) σ))) := by
  classical
  have hX : ∀ i, massX (injure e (applyFlips T (setGame e (x, Q \ (Finset.range e).biUnion
      (fun e' => (σ.game e').elim ∅ fun g => g.2.1), m, st) σ))) i =
      if e < i then ∅ else if i = e then
        Q \ (Finset.range e).biUnion (fun e' => (σ.game e').elim ∅ fun g => g.2.1)
      else massX σ i := by
    intro i
    unfold massX
    simp only [injure, applyFlips, setGame]
    split_ifs with h1 h2
    · rfl
    · rw [h2, Function.update_self]; rfl
    · rw [Function.update_of_ne h2]
  have hB : ∀ k, k < e → massX σ k ⊆
      (Finset.range e).biUnion (fun e' => (σ.game e').elim ∅ fun g => g.2.1) :=
    fun k hk => Finset.subset_biUnion_of_mem (fun e' => (σ.game e').elim ∅ fun g => g.2.1)
      (Finset.mem_range.2 hk)
  intro i j hij
  rw [hX i, hX j]
  by_cases hi : e < i
  · rw [ite_eq_left hi]; exact Finset.disjoint_empty_left _
  by_cases hj : e < j
  · rw [ite_eq_left hj]; exact Finset.disjoint_empty_right _
  rw [ite_eq_right hi, ite_eq_right hj]
  by_cases hie : i = e
  · have hje : j ≠ e := fun h => hij (hie.trans h.symm)
    rw [ite_eq_left hie, ite_eq_right hje]
    exact Finset.sdiff_disjoint.mono_right (hB j (by omega))
  · rw [ite_eq_right hie]
    by_cases hje : j = e
    · rw [ite_eq_left hje]
      exact (Finset.sdiff_disjoint.mono_right (hB i (by omega))).symm
    · rw [ite_eq_right hje]
      exact hD i j hij

end

/-- Processing one requirement preserves the disjointness of the play sets. -/
theorem massDisj_processReq (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) (hD : MassDisj p.1) : MassDisj (processReq A γ σ₀ e p).1 := by
  classical
  by_cases hp : p.2 = true
  · have hpr : processReq A γ σ₀ e p = p := by unfold processReq; rw [ite_eq_left hp]
    rw [hpr]; exact hD
  have hpf : p.2 = false := by simpa using hp
  cases hge : p.1.game e with
  | none =>
    have hpr : processReq A γ σ₀ e p = startGame A γ e p.1 := by
      unfold processReq; simp [hpf, hge]
    rw [hpr]
    unfold startGame
    cases hw : chooseWitness A γ p.1 e with
    | none => exact hD
    | some x => exact massDisj_start p.1 e hD _ _ x _ _
  | some g =>
    have hpr : processReq A γ σ₀ e p = processGame A γ σ₀ e g p.1 := by
      unfold processReq; simp [hpf, hge]
    rw [hpr]
    unfold processGame
    split_ifs with h1 h2
    · exact massDisj_mono (fun e' => (massX_injure e _ e').trans (massX_destroy e p.1 e')) hD
    · exact massDisj_mono (fun e' => massX_setGame_le p.1 e g hge _ _ _ e') hD
    · exact massDisj_mono (fun e' => (massX_injure e _ e').trans
        ((massX_applyFlips _ _ e').trans (massX_setGame_le p.1 e g hge _ _ _ e'))) hD

/-- The play sets of the requirements are pairwise disjoint at every stage. -/
theorem massDisj_stage (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) : MassDisj (stage A γ enumK s) := by
  induction s with
  | zero => intro e e' _; simp [massX, stage, CState.init]
  | succ t ih =>
    rw [mass_stage_succ_eq]
    have h : ∀ k, MassDisj (massFold A (reqγ γ) (stage A γ enumK t)
        (updateK enumK t (stage A γ enumK t)) k).1 := by
      intro k
      induction k with
      | zero => exact massDisj_congr rfl ih
      | succ k ihk => rw [massFold_succ]; exact massDisj_processReq _ _ _ _ _ ihk
    exact h (t + 1)

/-- One stage: our flips raise the mass by at most the `K`-mass charged to the live games plus
the increase of the potential. -/
theorem mass_stage_step (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t N : ℕ) (S : Finset BitString) (htN : t + 1 ≤ N) :
    fIncr A γ enumK t S ≤ ∑ e ∈ Finset.range (t + 1),
        (((stage A γ enumK t).game (e + 1)).elim 0 fun g => kIncr A γ enumK t g.2.1) +
      (massPot N (stage A γ enumK (t + 1)) - massPot N (stage A γ enumK t)) := by
  have hch : ∀ e, 0 ≤ ((stage A γ enumK t).game e).elim 0
      fun g => kCost (stage A γ enumK t) (updateK enumK t (stage A γ enumK t)) g.2.1 := by
    intro e
    cases hg : (stage A γ enumK t).game e with
    | none => exact le_rfl
    | some g =>
      change 0 ≤ kCost (stage A γ enumK t) (updateK enumK t (stage A γ enumK t)) g.2.1
      unfold kCost
      apply Finset.sum_nonneg
      intro z _
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
        (mass_hval_updateK_le enumK t (stage A γ enumK t) z)
      linarith
  have h := (massFold_bound A (reqγ γ) (stage A γ enumK t) (updateK enumK t (stage A γ enumK t))
    N S (fun e g hg => mass_live_bound A γ enumK t e g hg)
    (mass_updateK_game enumK t _) (mass_updateK_inj enumK t _) hch (t + 1) htN).1
  rw [← mass_stage_succ_eq] at h
  exact h

omit [Family] in
/-- A geometric sum bound: `∑_{i < n} 2^{-(a+i)} ≤ 2 · 2^{-a}`. -/
theorem mass_geom (a n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℝ)⁻¹ ^ (a + i) ≤ 2 * (2 : ℝ)⁻¹ ^ a := by
  have h := sum_geometric_two_le n
  rw [one_div] at h
  calc ∑ i ∈ Finset.range n, (2 : ℝ)⁻¹ ^ (a + i)
      = (2 : ℝ)⁻¹ ^ a * ∑ i ∈ Finset.range n, (2 : ℝ)⁻¹ ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_add _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ a * 2 := by gcongr
    _ = 2 * (2 : ℝ)⁻¹ ^ a := mul_comm _ _

/-- The potential is at most `∑_{e ≥ 1} 2^{-(e+5)} = 1/32`. -/
theorem mass_pot_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s N : ℕ) : massPot N (stage A γ enumK s) ≤ 1 / 32 := by
  have hpsi : ∀ e, massPsi (stage A γ enumK s) (e + 1) ≤ (2 : ℝ)⁻¹ ^ (6 + e) := by
    intro e
    have hsum : massPsi (stage A γ enumK s) (e + 1) ≤
        ∑ i ∈ Finset.range ((stage A γ enumK s).inj (e + 1) + 1),
          (2 : ℝ)⁻¹ ^ (e + 1 + i + 6) := by
      rw [Finset.sum_range_succ]
      cases hg : (stage A γ enumK s).game (e + 1) with
      | none =>
        rw [massPsi_none hg]
        linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (e + 1 + (stage A γ enumK s).inj (e + 1) + 6)]
      | some g =>
        rw [massPsi_some hg]
        obtain ⟨hm, hour, hK0⟩ := mass_live_bound A γ enumK s (e + 1) g hg
        rw [hm] at hour
        linarith
    have hgeo := mass_geom (e + 7) ((stage A γ enumK s).inj (e + 1) + 1)
    have heq : ∑ i ∈ Finset.range ((stage A γ enumK s).inj (e + 1) + 1),
        (2 : ℝ)⁻¹ ^ (e + 1 + i + 6) =
        ∑ i ∈ Finset.range ((stage A γ enumK s).inj (e + 1) + 1), (2 : ℝ)⁻¹ ^ (e + 7 + i) :=
      Finset.sum_congr rfl fun i _ => by rw [show e + 1 + i + 6 = e + 7 + i by ring]
    have h2 : 2 * (2 : ℝ)⁻¹ ^ (e + 7) = (2 : ℝ)⁻¹ ^ (6 + e) := by
      rw [show e + 7 = (6 + e) + 1 by ring, pow_succ]; ring
    linarith
  calc massPot N (stage A γ enumK s) ≤ ∑ e ∈ Finset.range N, (2 : ℝ)⁻¹ ^ (6 + e) :=
        Finset.sum_le_sum fun e _ => hpsi e
    _ ≤ 2 * (2 : ℝ)⁻¹ ^ 6 := mass_geom 6 N
    _ = 1 / 32 := by norm_num

/-- The total increase caused by our flips is at most `1/16`.  In each stage at most one
requirement flips, and the real increase equals the `moveCost` of our answer in the current game
(`flipCost` is exactly the real increase of `2^{-H*(z)}` when `H*(z)` is lowered to
`min (H*(z), |z| - 1)`; flipped random strings have `|z| ≥ 7`), which is recorded in our score of
that game, so our total spending on a game is at most its budget.  Games of `e` with injury count
`i` that are not destroyed by a cheat: at most one per `(e, i)`, total `≤ ∑_{e ≥ 1} ∑_i
2^{-(e+i+6)} = 1/32`; games destroyed by a cheat of `K`: our spending is at most the budget, which
is less than the real `K`-mass charged on that game, and these charges are disjoint pieces of the
total increase caused by `K` (the play sets are pairwise disjoint, `massDisj_stage`), at most
`1/32` (as in `kIncr_sum_le`). -/
theorem fIncr_sum_le (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (s : ℕ) (S : Finset BitString) :
    ∑ t ∈ Finset.range s, fIncr A γ enumK t S ≤ 1 / 16 := by
  classical
  set U : Finset BitString := (Finset.range s).biUnion fun t => (Finset.range (t + 1)).biUnion
    fun e => ((stage A γ enumK t).game (e + 1)).elim ∅ fun g => g.2.1 with hU
  have hk0 : ∀ t x, 0 ≤ (2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x -
      (2 : ℝ)⁻¹ ^ (stage A γ enumK t).hval x := by
    intro t x
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
      (mass_hval_updateK_le enumK t (stage A γ enumK t) x)
    linarith
  have hch : ∀ t, t < s → ∑ e ∈ Finset.range (t + 1),
      (((stage A γ enumK t).game (e + 1)).elim 0 fun g => kIncr A γ enumK t g.2.1) ≤
        kIncr A γ enumK t U := by
    intro t ht
    have hY : ∀ e, (((stage A γ enumK t).game (e + 1)).elim 0 fun g => kIncr A γ enumK t g.2.1) =
        kIncr A γ enumK t (((stage A γ enumK t).game (e + 1)).elim ∅ fun g => g.2.1) := by
      intro e
      cases (stage A γ enumK t).game (e + 1) with
      | none => simp [kIncr]
      | some g => rfl
    simp only [hY]
    have hdisj : ((Finset.range (t + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        fun e => ((stage A γ enumK t).game (e + 1)).elim ∅ fun g => g.2.1 := by
      intro i _ j _ hij
      exact massDisj_stage A γ enumK t (i + 1) (j + 1) (by omega)
    unfold kIncr
    rw [← Finset.sum_biUnion hdisj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [hU, Finset.mem_biUnion]
      exact ⟨t, Finset.mem_range.2 ht, hx⟩
    · intro x _ _; exact hk0 t x
  have htel : ∀ n, n ≤ s → ∑ t ∈ Finset.range n, fIncr A γ enumK t S ≤
      ∑ t ∈ Finset.range n, kIncr A γ enumK t U + massPot s (stage A γ enumK n) := by
    intro n
    induction n with
    | zero => intro _; simp [massPot, massPsi, stage, CState.init]
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 := mass_stage_step A γ enumK n s S hn
      have h2 := hch n (by omega)
      have h3 := ih (by omega)
      linarith
  have h1 := htel s le_rfl
  have h2 := kIncr_sum_le A K γ enumK henum s U
  have h3 := mass_pot_le A γ enumK s s
  linarith

/-- Claim 3, stage-wise: `∑_{x ∈ S} 2^{-H*_s(x)} ≤ 1/32 + 1/32 + 1/16 = 1/8` (the initial values,
the moves of `K`, and our flips on cheated and on the other games). -/
theorem stage_mass (A : Set BitString)
    (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p) (s : ℕ) (S : Finset BitString) :
    ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (stage A γ enumK s).hval x ≤ 1 / 8 := by
  rw [mass_telescope, Finset.sum_add_distrib]
  have h1 := kraft_init S
  have h2 := kIncr_sum_le A K γ enumK henum s S
  have h3 := fIncr_sum_le A K γ enumK henum s S
  linarith

end Kolmogorov.RandomStrings
