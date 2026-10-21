/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Claim2Stage

/-!
# Finitely many changes at every stage

Every stage changes `F*` and `K*` at finitely many strings, and the games of every requirement
eventually exist and are eventually constant (`game_eventually_exists`,
`game_eventually_const`), using the hypothesis `WitnessesExist`.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! #### Finitely many changes at every stage (for `WitnessesExist`) -/

/-- Processing a requirement `e` changes the constructed values `F*` on at most finitely many
strings compared to the input state. -/
theorem lim_processReq_Fstar_finite (A : Set BitString) (Γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) : {x | (processReq A Γ σ₀ e p).1.Fstar x ≠ p.1.Fstar x}.Finite := by
  obtain ⟨τ, b⟩ := p
  cases b with
  | true => rw [lim_processReq_of_snd A Γ σ₀ e _ rfl]; simp
  | false =>
    cases hg : τ.game e with
    | none =>
      rw [lim_processReq_false_none A Γ σ₀ e τ hg]
      cases hc : chooseWitness A Γ τ e with
      | none => rw [lim_startGame_none A Γ e τ hc]; simp
      | some x =>
        rw [lim_startGame_some A Γ e τ x hc]
        refine (Finset.finite_toSet (ourReply (newGame A Γ τ e x) (val (newGame A Γ τ e x))
          (firstState (newGame A Γ τ e x) (val (newGame A Γ τ e x))))).subset ?_
        intro y hy
        by_contra hyT
        rw [Finset.mem_coe] at hyT
        exact hy (by simp [startOn, injure, applyFlips, setGame, hyT])
    | some g =>
      rw [lim_processReq_false_some A Γ σ₀ e τ g hg]
      unfold processGame
      split_ifs with h1 h2
      · simp [injure, destroy]
      · simp [setGame]
      · refine (Finset.finite_toSet (ourReply (curGame A Γ τ e g) (!g.2.2.2.yesTurn)
            (g.2.2.2.kMove (g.2.2.2.S ∪ flipped τ g.2.1) (kCost σ₀ τ g.2.1)) \
          (g.2.2.2.S ∪ flipped τ g.2.1))).subset ?_
        intro y hy
        by_contra hyT
        rw [Finset.mem_coe] at hyT
        exact hy (by simp only [injure, applyFlips, setGame]; rw [ite_eq_right hyT])

/-- Processing `k` requirements consecutively from a state `σ₁` changes the constructed values `F*`
on at most finitely many strings compared to `σ₁`. -/
theorem lim_accR_Fstar_finite {A : Set BitString} {Γ : ℕ → OTMCode × ℕ} {σ₀ σ₁ : CState}
    {F : ℕ → CState × Bool} (hF0 : F 0 = (σ₁, false))
    (hF : ∀ k, F (k + 1) = processReq A Γ σ₀ (k + 1) (F k)) :
    ∀ k, {x | (F k).1.Fstar x ≠ σ₁.Fstar x}.Finite := by
  intro k
  induction k with
  | zero => rw [hF0]; simp
  | succ k ih =>
    refine (ih.union (lim_processReq_Fstar_finite A Γ σ₀ (k + 1) (F k))).subset ?_
    intro x hx
    rw [hF] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
    exact hx (hcon.2.trans hcon.1)

/-- After `s` stages of the construction, the constructed values `F*` differ from the initial state
`F₀` on at most finitely many strings. -/
theorem lim_stage_Fstar_finite (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) : {x | (stage A γ enumK s).Fstar x ≠ F₀ x}.Finite := by
  induction s with
  | zero => simp [stage, CState.init]
  | succ s ih =>
    have hstep : {x | (stage A γ enumK (s + 1)).Fstar x ≠ (stage A γ enumK s).Fstar x}.Finite := by
      rw [lim_stage_succ_eq]
      exact lim_accR_Fstar_finite (A := A) (Γ := reqγ γ) (σ₀ := stage A γ enumK s)
        (σ₁ := updateK enumK s (stage A γ enumK s))
        (F := fun k => (List.range k).foldl
          (fun p e => processReq A (reqγ γ) (stage A γ enumK s) (e + 1) p)
          (updateK enumK s (stage A γ enumK s), false)) rfl
        (fun k => lim_foldl_range_succ _ _ _ _ k) (s + 1)
    refine (ih.union hstep).subset ?_
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
    exact hx (hcon.2.trans hcon.1)

/-- After `s` stages of the construction, the values `K*` differ from the initial state
`⊤` on at most finitely many strings. -/
theorem lim_stage_Kstar_finite (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) : {x | (stage A γ enumK s).Kstar x ≠ ⊤}.Finite := by
  induction s with
  | zero => simp [stage, CState.init]
  | succ s ih =>
    refine (ih.union (Set.finite_singleton (enumK s).1)).subset ?_
    intro x hx
    rw [Set.mem_ofPred_eq, stage_Kstar_succ] at hx
    by_cases hxs : x = (enumK s).1
    · exact Or.inr hxs
    · rw [Function.update_of_ne hxs] at hx
      exact Or.inl hx

/-- From one stage to the next, a surviving game of `e ≥ 1` keeps its play set, and either its
record is unchanged, or its flipped set is unchanged while `H*` strictly decreased somewhere on the
play set (a nonzero charge), or its flipped set strictly grows inside `S ∪ X`. -/
theorem lim_stage_some_some (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t e : ℕ) (he : 1 ≤ e) (g g' : BitString × Finset BitString × ℕ × GState)
    (hg : (stage A γ enumK t).game e = some g)
    (hg' : (stage A γ enumK (t + 1)).game e = some g') :
    g' = g ∨ (g'.2.1 = g.2.1 ∧
      ((g'.2.2.2.S = g.2.2.2.S ∧
          ∃ z ∈ g.2.1, (stage A γ enumK (t + 1)).hval z < (stage A γ enumK t).hval z) ∨
        (g.2.2.2.S ⊂ g'.2.2.2.S ∧ g'.2.2.2.S ⊆ g.2.2.2.S ∪ g.2.1))) := by
  rcases lim_stage_cases A γ enumK t e he with ⟨a, -, -, hnone, -⟩ | ⟨-, hcase⟩
  · rw [hnone] at hg'; exact absurd hg' (by simp)
  · rcases hcase with ⟨-, hsame⟩ | ⟨-, τ, hτF, hτK, -, hτg, hτeq⟩
    · left; rw [hsame, hg] at hg'; exact (Option.some.inj hg').symm
    · rw [hg] at hτg
      rw [hτeq] at hg'
      obtain ⟨h1, h2, h3, -, h5⟩ :=
        lim_processReq_some_some A (reqγ γ) (stage A γ enumK t) e τ g g' hτg hg'
      rcases h5 with h5 | h5
      · by_cases hc : kCost (stage A γ enumK t) τ g.2.1 = 0
        · left
          rw [hc, lim_charge_zero] at h5
          exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h5))
        · right
          refine ⟨h2, Or.inl ⟨by rw [h5, lim_S_charge], ?_⟩⟩
          by_contra hcon
          push Not at hcon
          apply hc
          rw [lim_kCost_eq_kIncr A γ enumK t τ hτF hτK]
          unfold kIncr
          apply Finset.sum_eq_zero
          intro z hz
          have h1' := lim_stage_hval_succ_le_updateK A γ enumK t z
          have h2' := lim_updateK_hval_le enumK t (stage A γ enumK t) z
          have h3' := hcon z hz
          have : (updateK enumK t (stage A γ enumK t)).hval z = (stage A γ enumK t).hval z := by
            omega
          rw [this, sub_self]
      · right; exact ⟨h2, Or.inr h5⟩

omit [Family] in
/-- An `ℕ`-valued potential that never increases and strictly decreases at every change of `r`
forces `r` to be eventually constant. -/
theorem lim_eventually_const_of_potential {α : Type*} (r : ℕ → α) (Φ : ℕ → ℕ) (s₀ : ℕ)
    (h : ∀ t, s₀ ≤ t → Φ (t + 1) ≤ Φ t ∧ (r (t + 1) ≠ r t → Φ (t + 1) < Φ t)) :
    ∃ s₁, s₀ ≤ s₁ ∧ ∀ t, s₁ ≤ t → r t = r s₁ := by
  classical
  have hex : ∃ n, ∃ s, s₀ ≤ s ∧ Φ s = n := ⟨Φ s₀, s₀, le_rfl, rfl⟩
  obtain ⟨s₁, hs₁, hΦs₁⟩ := Nat.find_spec hex
  have hmin : ∀ s, s₀ ≤ s → Nat.find hex ≤ Φ s := fun s hs => Nat.find_min' hex ⟨s, hs, rfl⟩
  have hanti : ∀ t, s₁ ≤ t → Φ t ≤ Φ s₁ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t hst ih => exact (h t (by omega)).1.trans ih
  have heq : ∀ t, s₁ ≤ t → Φ t = Φ s₁ := fun t ht =>
    le_antisymm (hanti t ht) (hΦs₁ ▸ hmin t (by omega))
  refine ⟨s₁, hs₁, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    by_contra hne
    have hlt := (h t (by omega)).2 (fun h' => hne (h'.trans ih))
    rw [heq t hst, heq (t + 1) (by omega)] at hlt
    exact lt_irrefl _ hlt

/-- (C2-v) Injuries come only from acting requirements of higher priority: if the records of the
games of all `1 ≤ e' < e` are constant from stage `s₁` on (so none of them acts from `s₁` on;
requirement `0` never acts), the injury counter of `e` is constant from `s₁` on. -/
theorem inj_const_of_lower (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (e s₁ : ℕ)
    (hlow : ∀ e', 1 ≤ e' → e' < e → ∃ g, ∀ s, s₁ ≤ s → (stage A γ enumK s).game e' = some g) :
    ∀ s, s₁ ≤ s → (stage A γ enumK s).inj e = (stage A γ enumK s₁).inj e := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact (lim_stage_zero A γ enumK t).2
    · rcases lim_stage_cases A γ enumK t e he with ⟨a, ha1, hae, -, hch⟩ | ⟨hinj, -⟩
      · obtain ⟨g, hg⟩ := hlow a ha1 hae
        exact absurd ((hg (t + 1) (by omega)).trans (hg t hst).symm) hch
      · exact hinj

/-- (C2-vi) Kraft bounds the cheats: if the records of the games of all `1 ≤ e' < e` are constant
from stage `s₁` on, then from some stage on `e` always has a game.  From `s₁` on `e` is not injured
(`inj_const_of_lower`, so its budget `2^{-(e+i+6)}` is fixed), it is processed at every stage
`≥ e`, a lost game is replaced at the next stage (a witness exists, `WitnessesExist`), and each
loss is a destruction by a cheat of `K`, which has charged more than
`2^{-(e+i+6)}` of real `K`-mass (`kCost`) on the play set of that game during its lifetime; by
`live_playSets_disjoint` these charges are disjoint pieces of the total increase caused by `K`,
which is at most `∑_x 2^{-(K x + 5)} ≤ 1/32` (see `kIncr_sum_le`). -/
theorem game_eventually_exists (A : Set BitString) (hW : ∀ γ', WitnessesExist A γ')
    (K : AprioriComplexity)
    (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p) (e s₁ : ℕ) (he : 1 ≤ e)
    (hlow : ∀ e', 1 ≤ e' → e' < e → ∃ g, ∀ s, s₁ ≤ s → (stage A γ enumK s).game e' = some g) :
    ∃ s₂, ∀ s, s₂ ≤ s → ∃ g, (stage A γ enumK s).game e = some g := by
  classical
  -- from `s₁` on no requirement of higher priority acts
  have hstep : ∀ t, s₁ ≤ t →
      ((t + 1 < e ∧ (stage A γ enumK (t + 1)).game e = (stage A γ enumK t).game e) ∨
       (e ≤ t + 1 ∧ ∃ τ : CState, τ.Fstar = (stage A γ enumK t).Fstar ∧
          τ.Kstar = (updateK enumK t (stage A γ enumK t)).Kstar ∧
          τ.inj = (stage A γ enumK t).inj ∧ τ.game e = (stage A γ enumK t).game e ∧
          (stage A γ enumK (t + 1)).game e =
            (processReq A (reqγ γ) (stage A γ enumK t) e (τ, false)).1.game e)) := by
    intro t ht
    rcases lim_stage_cases A γ enumK t e he with ⟨a, ha1, hae, -, hch⟩ | ⟨-, h⟩
    · obtain ⟨g, hg⟩ := hlow a ha1 hae
      exact absurd ((hg (t + 1) (by omega)).trans (hg t ht).symm) hch
    · exact h
  have hinj := inj_const_of_lower A γ enumK e s₁ hlow
  by_cases hall : ∀ s, s₁ ≤ s → ∃ g, (stage A γ enumK s).game e = some g
  · exact ⟨s₁, hall⟩
  push Not at hall
  obtain ⟨s₀, hs₀, hnone⟩ := hall
  have hnone₀ : (stage A γ enumK s₀).game e = none := by
    cases h : (stage A γ enumK s₀).game e with
    | none => rfl
    | some g => exact absurd h (hnone g)
  -- the budget exponent of the games of `e` started from `s₀` on
  set m := e + (stage A γ enumK s₀).inj e + 6 with hm
  have hm' : ∀ t, s₀ ≤ t → e + (stage A γ enumK t).inj e + 6 = m := by
    intro t ht
    rw [hm, hinj t (by omega), hinj s₀ hs₀]
  -- losses of the game of `e`, their number from `s₀` on, and `K`'s score in the current game
  let loss : ℕ → Prop := fun t =>
    (stage A γ enumK t).game e ≠ none ∧ (stage A γ enumK (t + 1)).game e = none
  let L : ℕ → ℝ := fun s => ∑ t ∈ Finset.Ico s₀ s, if loss t then (1 : ℝ) else 0
  let ks : ℕ → ℝ := fun s => ((stage A γ enumK s).game e).elim 0 fun g => g.2.2.2.moverScore
  have hLsucc : ∀ s, s₀ ≤ s → L (s + 1) = L s + if loss s then 1 else 0 := by
    intro s hs
    simp only [L]
    rw [Finset.sum_Ico_succ_top hs]
  have hLmono : ∀ s t, s ≤ t → L s ≤ L t := by
    intro s t hst
    simp only [L]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hst)
    intro i _ _
    split_ifs <;> norm_num
  have hks_none : ∀ s, (stage A γ enumK s).game e = none → ks s = 0 := by
    intro s h; simp only [ks, h, Option.elim]
  have hks_some : ∀ s g, (stage A γ enumK s).game e = some g → ks s = g.2.2.2.moverScore := by
    intro s g h; simp only [ks, h, Option.elim]
  -- each loss is a cheat, which has cost `K` more than the budget `2^{-m}` on the play set
  have hinv : ∀ s, s₀ ≤ s → ∃ U : Finset BitString,
      (∀ g, (stage A γ enumK s).game e = some g →
        g.2.1 ⊆ U ∧ g.2.2.1 = m ∧ 0 ≤ g.2.2.2.moverScore) ∧
      L s * (2 : ℝ)⁻¹ ^ m + ks s ≤ ∑ t ∈ Finset.Ico s₀ s, kIncr A γ enumK t U := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      refine ⟨∅, fun g hg => by rw [hnone₀] at hg; exact absurd hg (by simp), ?_⟩
      simp [L, hks_none s₀ hnone₀]
    | succ t hst ih =>
      obtain ⟨U, hU, hineq⟩ := ih
      have hst1 : s₁ ≤ t := le_trans hs₀ hst
      have hcase := hstep t hst1
      have hsplit : ∀ U : Finset BitString, ∑ i ∈ Finset.Ico s₀ (t + 1), kIncr A γ enumK i U =
          ∑ i ∈ Finset.Ico s₀ t, kIncr A γ enumK i U + kIncr A γ enumK t U :=
        fun U => Finset.sum_Ico_succ_top hst _
      rw [hLsucc t hst]
      have hkU := lim_kIncr_nonneg A γ enumK t U
      rcases Option.eq_none_or_eq_some ((stage A γ enumK t).game e) with hgt | ⟨g, hgt⟩
      · have hnl : ¬ loss t := fun h => h.1 hgt
        rw [ite_eq_right hnl, add_zero]
        rw [hks_none t hgt] at hineq
        rcases Option.eq_none_or_eq_some ((stage A γ enumK (t + 1)).game e) with hgt1 | ⟨g', hgt1⟩
        · refine ⟨U, fun g hg => by rw [hgt1] at hg; exact absurd hg (by simp), ?_⟩
          rw [hks_none (t + 1) hgt1, hsplit]
          linarith
        · rcases hcase with ⟨-, hsame⟩ | ⟨-, τ, hτF, hτK, hτi, hτg, hτeq⟩
          · rw [hsame, hgt] at hgt1; exact absurd hgt1 (by simp)
          · rw [hgt] at hτg
            have hp : (processReq A (reqγ γ) (stage A γ enumK t) e (τ, false)).1.game e =
                some g' := hτeq.symm.trans hgt1
            obtain ⟨h1, h2⟩ :=
              lim_processReq_none_some A (reqγ γ) (stage A γ enumK t) e τ g' hτg hp
            refine ⟨U ∪ g'.2.1, fun g hg => ?_, ?_⟩
            · rw [hgt1] at hg
              obtain rfl := Option.some.inj hg
              refine ⟨Finset.subset_union_right, ?_, by rw [h2]⟩
              rw [h1, hτi]
              exact hm' t hst
            · rw [hks_some (t + 1) g' hgt1, h2, hsplit]
              have hmono : ∑ i ∈ Finset.Ico s₀ t, kIncr A γ enumK i U ≤
                  ∑ i ∈ Finset.Ico s₀ t, kIncr A γ enumK i (U ∪ g'.2.1) :=
                Finset.sum_le_sum fun i _ => lim_kIncr_mono A γ enumK i Finset.subset_union_left
              have hk' := lim_kIncr_nonneg A γ enumK t (U ∪ g'.2.1)
              linarith
      · obtain ⟨hgU, hgm, hg0⟩ := hU g hgt
        rw [hks_some t g hgt] at hineq
        rcases Option.eq_none_or_eq_some ((stage A γ enumK (t + 1)).game e) with hgt1 | ⟨g', hgt1⟩
        · have hl : loss t := ⟨by rw [hgt]; simp, hgt1⟩
          rw [ite_eq_left hl]
          rcases hcase with ⟨-, hsame⟩ | ⟨-, τ, hτF, hτK, hτi, hτg, hτeq⟩
          · rw [hsame, hgt] at hgt1; exact absurd hgt1 (by simp)
          · rw [hgt] at hτg
            have hp : (processReq A (reqγ γ) (stage A γ enumK t) e (τ, false)).1.game e =
                none := hτeq.symm.trans hgt1
            have hcheat := lim_processReq_some_none A (reqγ γ) (stage A γ enumK t) e τ g hτg hp
            unfold Cheats at hcheat
            rw [lim_kCost_eq_kIncr A γ enumK t τ hτF hτK, hgm] at hcheat
            have h3 := lim_kIncr_mono A γ enumK t hgU
            refine ⟨U, fun g hg => by rw [hgt1] at hg; exact absurd hg (by simp), ?_⟩
            rw [hks_none (t + 1) hgt1, hsplit]
            have hexp : (L t + 1) * (2 : ℝ)⁻¹ ^ m = L t * (2 : ℝ)⁻¹ ^ m + (2 : ℝ)⁻¹ ^ m := by ring
            rw [hexp]
            linarith
        · have hnl : ¬ loss t := fun h => by
            have h2 : (stage A γ enumK (t + 1)).game e = none := h.2
            rw [hgt1] at h2
            exact absurd h2 (by simp)
          rw [ite_eq_right hnl, add_zero]
          rcases hcase with ⟨-, hsame⟩ | ⟨-, τ, hτF, hτK, hτi, hτg, hτeq⟩
          · have hgg : g' = g := Option.some.inj (hgt1.symm.trans (hsame.trans hgt))
            subst hgg
            refine ⟨U, fun g'' hg'' => ?_, ?_⟩
            · rw [hgt1] at hg''
              obtain rfl := Option.some.inj hg''
              exact ⟨hgU, hgm, hg0⟩
            · rw [hks_some (t + 1) _ hgt1, hsplit]
              linarith
          · rw [hgt] at hτg
            have hp : (processReq A (reqγ γ) (stage A γ enumK t) e (τ, false)).1.game e =
                some g' := hτeq.symm.trans hgt1
            obtain ⟨-, h2, h3, h4, -⟩ :=
              lim_processReq_some_some A (reqγ γ) (stage A γ enumK t) e τ g g' hτg hp
            rw [lim_kCost_eq_kIncr A γ enumK t τ hτF hτK] at h4
            have h5 := lim_kIncr_mono A γ enumK t hgU
            have h6 := lim_kIncr_nonneg A γ enumK t g.2.1
            refine ⟨U, fun g'' hg'' => ?_, ?_⟩
            · rw [hgt1] at hg''
              obtain rfl := Option.some.inj hg''
              refine ⟨by rw [h2]; exact hgU, h3.trans hgm, ?_⟩
              rw [h4]; linarith
            · rw [hks_some (t + 1) g' hgt1, h4, hsplit]
              linarith
  -- hence the number of losses is bounded (Kraft for `K`, `kIncr_sum_le`) ...
  have hbound : ∀ s, s₀ ≤ s → L s * (2 : ℝ)⁻¹ ^ m ≤ 1 / 32 := by
    intro s hs
    obtain ⟨U, hU, hineq⟩ := hinv s hs
    have hks : 0 ≤ ks s := by
      cases h : (stage A γ enumK s).game e with
      | none => rw [hks_none s h]
      | some g => rw [hks_some s g h]; exact (hU g h).2.2
    have h1 : ∑ t ∈ Finset.Ico s₀ s, kIncr A γ enumK t U ≤
        ∑ t ∈ Finset.range s, kIncr A γ enumK t U := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        rw [Finset.mem_Ico] at ht
        rw [Finset.mem_range]; omega
      · intro t _ _; exact lim_kIncr_nonneg A γ enumK t U
    have h2 := kIncr_sum_le A K γ enumK henum s U
    linarith
  -- ... so the losses stop
  have hstop : ∃ s₃, ∀ t, s₃ ≤ t → ¬ loss t := by
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ n : ℕ, ∃ s, s₀ ≤ s ∧ (n : ℝ) ≤ L s := by
      intro n
      induction n with
      | zero => exact ⟨s₀, le_rfl, by simp [L]⟩
      | succ n ih =>
        obtain ⟨s, hs, hn⟩ := ih
        obtain ⟨t, ht, hl⟩ := hcon s
        refine ⟨t + 1, by omega, ?_⟩
        rw [hLsucc t (by omega), ite_eq_left hl]
        have := hLmono s t ht
        push_cast
        linarith
    obtain ⟨s, hs, hn⟩ := hgrow (2 ^ m)
    have hb := hbound s hs
    have hw : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
    have h1 : ((2 ^ m : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ m = 1 := by
      push_cast
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    have h2 := mul_le_mul_of_nonneg_right hn hw.le
    linarith
  -- after the last loss, a missing game is started at once (a witness exists, `hW`)
  obtain ⟨s₃, hs₃⟩ := hstop
  refine ⟨max s₃ (max s₀ e) + 1, fun s hs => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have ht1 : s₁ ≤ t := by omega
  cases hgt : (stage A γ enumK t).game e with
  | some g =>
    have hnl := hs₃ t (by omega)
    cases hgt1 : (stage A γ enumK (t + 1)).game e with
    | none => exact absurd ⟨by rw [hgt]; simp, hgt1⟩ hnl
    | some g' => exact ⟨g', rfl⟩
  | none =>
    rcases hstep t ht1 with ⟨hlt, -⟩ | ⟨-, τ, hτF, hτK, -, hτg, hτeq⟩
    · omega
    · rw [hτeq]
      rw [hgt] at hτg
      apply lim_processReq_none_witness A (reqγ γ) (stage A γ enumK t) e τ hτg
      have hfin : {x | τ.Fstar x ≠ F₀ x}.Finite := by
        rw [hτF]; exact lim_stage_Fstar_finite A γ enumK t
      have hfinK : {x | τ.Kstar x ≠ ⊤}.Finite := by
        have h' : (updateK enumK t (stage A γ enumK t)).Kstar = (stage A γ enumK (t + 1)).Kstar :=
          (stage_Kstar_succ A γ enumK t).symm
        rw [hτK, h']
        exact lim_stage_Kstar_finite A γ enumK (t + 1)
      obtain ⟨x, -, hx⟩ := hW (reqγ γ) τ e 0 hfin hfinK
      exact ⟨x, hx⟩

/-- (C2-vii) A game that is never lost eventually has a constant record: from `s₂` on the game is
never destroyed, so its witness, play set and budget stay fixed; the stored state changes only
when `K` flips a string of the play set (at most `|X|` times, each flip enlarges `S ⊆ X`; our
answer follows at once) or when `H*` decreases on `X` (finitely often: `H*` is `ℕ`-valued and
antitone, `stage_Kstar_antitone`, `stage_Fstar_antitone'`); a charge `kCost = 0` leaves the
stored state unchanged (`GState.charge` with `0`). -/
theorem game_eventually_const_of_exists (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (e s₂ : ℕ)
    (hex : ∀ s, s₂ ≤ s → ∃ g, (stage A γ enumK s).game e = some g) :
    ∃ s₀ g, ∀ s, s₀ ≤ s → (stage A γ enumK s).game e = some g := by
  classical
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨g, hg⟩ := hex s₂ le_rfl
    rw [lim_stage_game_zero] at hg
    exact absurd hg (by simp)
  obtain ⟨g₀, hg₀⟩ := hex s₂ le_rfl
  -- the play set never changes and the flipped set stays inside `S₀ ∪ X`
  have hJ : ∀ t, s₂ ≤ t → ∃ g, (stage A γ enumK t).game e = some g ∧ g.2.1 = g₀.2.1 ∧
      g.2.2.2.S ⊆ g₀.2.2.2.S ∪ g₀.2.1 := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨g₀, hg₀, rfl, Finset.subset_union_left⟩
    | succ t hst ih =>
      obtain ⟨g, hg, hX, hS⟩ := ih
      obtain ⟨g', hg'⟩ := hex (t + 1) (by omega)
      refine ⟨g', hg', ?_⟩
      rcases lim_stage_some_some A γ enumK t e he g g' hg hg' with rfl | ⟨hX', hcase⟩
      · exact ⟨hX, hS⟩
      · refine ⟨hX'.trans hX, ?_⟩
        rcases hcase with ⟨hS', -⟩ | ⟨-, hS'⟩
        · rw [hS']; exact hS
        · refine hS'.trans ?_
          rw [hX]
          exact Finset.union_subset hS Finset.subset_union_right
  -- the potential: total `H*` on the play set plus the number of unflipped strings
  let Φ : ℕ → ℕ := fun t => ∑ z ∈ g₀.2.1, (stage A γ enumK t).hval z +
    ((g₀.2.2.2.S ∪ g₀.2.1) \ ((stage A γ enumK t).game e).elim ∅ fun g => g.2.2.2.S).card
  have hΦ : ∀ t, s₂ ≤ t → Φ (t + 1) ≤ Φ t ∧
      ((stage A γ enumK (t + 1)).game e ≠ (stage A γ enumK t).game e → Φ (t + 1) < Φ t) := by
    intro t ht
    obtain ⟨g, hg, hX, hS⟩ := hJ t ht
    obtain ⟨g', hg', hX', hS'⟩ := hJ (t + 1) (by omega)
    have hsum : ∑ z ∈ g₀.2.1, (stage A γ enumK (t + 1)).hval z ≤
        ∑ z ∈ g₀.2.1, (stage A γ enumK t).hval z :=
      Finset.sum_le_sum fun z _ => lim_stage_hval_succ_le A γ enumK t z
    have hΦt : Φ t = ∑ z ∈ g₀.2.1, (stage A γ enumK t).hval z +
        ((g₀.2.2.2.S ∪ g₀.2.1) \ g.2.2.2.S).card := by
      simp only [Φ, hg, Option.elim]
    have hΦt1 : Φ (t + 1) = ∑ z ∈ g₀.2.1, (stage A γ enumK (t + 1)).hval z +
        ((g₀.2.2.2.S ∪ g₀.2.1) \ g'.2.2.2.S).card := by
      simp only [Φ, hg', Option.elim]
    rw [hΦt, hΦt1, hg, hg']
    rcases lim_stage_some_some A γ enumK t e he g g' hg hg' with rfl | ⟨hXg, hcase⟩
    · exact ⟨by omega, fun h => absurd rfl h⟩
    · rcases hcase with ⟨hSeq, z, hzX, hz⟩ | ⟨hss, -⟩
      · have hlt : ∑ z ∈ g₀.2.1, (stage A γ enumK (t + 1)).hval z <
            ∑ z ∈ g₀.2.1, (stage A γ enumK t).hval z :=
          Finset.sum_lt_sum (fun z _ => lim_stage_hval_succ_le A γ enumK t z)
            ⟨z, hX ▸ hzX, hz⟩
        rw [hSeq]
        exact ⟨by omega, fun _ => by omega⟩
      · have hcard : ((g₀.2.2.2.S ∪ g₀.2.1) \ g'.2.2.2.S).card <
            ((g₀.2.2.2.S ∪ g₀.2.1) \ g.2.2.2.S).card :=
          card_sdiff_lt hss.subset hS' hss.ne'
        exact ⟨by omega, fun _ => by omega⟩
  obtain ⟨s₃, hs₃, hconst⟩ :=
    lim_eventually_const_of_potential (fun t => (stage A γ enumK t).game e) Φ s₂ hΦ
  obtain ⟨g, hg⟩ := hex s₃ hs₃
  exact ⟨s₃, g, fun s hs => (hconst s hs).trans hg⟩

/-- Claim 2, induction on `e`: every requirement `e ≥ 1` eventually keeps one game record forever
(`game_eventually_exists` and `game_eventually_const_of_exists`, with the induction hypothesis for
the requirements `1 ≤ e' < e`). -/
theorem game_eventually_const (A : Set BitString)
    (hW : ∀ γ', WitnessesExist A γ') (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ)
    (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p) (e : ℕ) (he : 1 ≤ e) :
    ∃ s₀ g, ∀ s, s₀ ≤ s → (stage A γ enumK s).game e = some g := by
  classical
  revert he
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he
  have hlow : ∃ s₁, ∀ e', 1 ≤ e' → e' < e →
      ∃ g, ∀ s, s₁ ≤ s → (stage A γ enumK s).game e' = some g := by
    have hpt : ∀ e' ∈ Finset.range e, ∃ s₀, 1 ≤ e' →
        ∃ g, ∀ s, s₀ ≤ s → (stage A γ enumK s).game e' = some g := by
      intro e' he'
      by_cases h1 : 1 ≤ e'
      · obtain ⟨s₀, g, hg⟩ := ih e' (Finset.mem_range.1 he') h1
        exact ⟨s₀, fun _ => ⟨g, hg⟩⟩
      · exact ⟨0, fun h => absurd h h1⟩
    choose! f hf using hpt
    refine ⟨(Finset.range e).sup f, fun e' h1 hlt => ?_⟩
    obtain ⟨g, hg⟩ := hf e' (Finset.mem_range.2 hlt) h1
    exact ⟨g, fun s hs => hg s ((Finset.le_sup (Finset.mem_range.2 hlt)).trans hs)⟩
  obtain ⟨s₁, hs₁⟩ := hlow
  obtain ⟨s₂, hs₂⟩ := game_eventually_exists A hW K γ enumK henum e s₁ he hs₁
  exact game_eventually_const_of_exists A γ enumK e s₂ hs₂

end Kolmogorov.RandomStrings
