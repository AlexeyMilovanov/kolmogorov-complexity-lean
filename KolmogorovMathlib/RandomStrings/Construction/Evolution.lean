/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.MirrorBookkeeping
import KolmogorovMathlib.RandomStrings.Construction.Flips

/-!
# The evolution of `K*` and `F*`

How the stages change the current values `K*` and `F*`: monotonicity, eventual stabilisation,
`hval_eventually_eq_Hmin`, and the conclusion of Claim 3, `Flim_entropy`.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! ### The evolution of `K*` and `F*` -/

/-- The step of starting a game on a string `x` leaves `K*` unchanged. -/
theorem startOn_Kstar {A : Set BitString} (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σ : CState)
    (x : BitString) : (startOn A γ e σ x).1.Kstar = σ.Kstar := rfl

/-- The step of starting a game leaves `K*` unchanged. -/
theorem startGame_Kstar (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (e : ℕ) (σ : CState) :
    (startGame A γ e σ).1.Kstar = σ.Kstar := by
  unfold startGame
  split
  · rfl
  · exact startOn_Kstar _ _ _ _

/-- The step of processing an active game leaves `K*` unchanged. -/
theorem processGame_Kstar {A : Set BitString} (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (g : BitString × Finset BitString × ℕ × GState) (σ : CState) :
    (processGame A γ σ₀ e g σ).1.Kstar = σ.Kstar := by
  unfold processGame; split_ifs <;> rfl

/-- The step of processing a requirement leaves `K*` unchanged. -/
theorem processReq_Kstar (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) : (processReq A γ σ₀ e p).1.Kstar = p.1.Kstar := by
  unfold processReq
  split
  · rfl
  · split
    · exact startGame_Kstar _ _ _ _
    · exact processGame_Kstar _ _ _ _ _

/-- Iterating `processReq` over a list of requirements leaves `K*` unchanged. -/
theorem foldl_processReq_Kstar (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState)
    (l : List ℕ) (p : CState × Bool) :
    (l.foldl (fun p e => processReq A γ σ₀ (e + 1) p) p).1.Kstar = p.1.Kstar := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih => exact (ih _).trans (processReq_Kstar _ _ _ _ _)

/-- The requirements do not touch `K*`: a stage only performs the update with `enumK (s - 1)`. -/
theorem stageStep_Kstar (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) (σ : CState) : (stageStep A γ enumK s σ).Kstar = (updateK enumK (s - 1) σ).Kstar :=
  foldl_processReq_Kstar A (reqγ γ) σ (List.range s) _

/-- At a successor stage, `K*` is updated by taking the minimum with the newly enumerated value for
the newly enumerated string, and left unchanged elsewhere. -/
theorem stage_Kstar_succ (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) : (stage A γ enumK (s + 1)).Kstar =
      Function.update (stage A γ enumK s).Kstar (enumK s).1
        (min ((stage A γ enumK s).Kstar (enumK s).1) ((enumK s).2 : ℕ∞)) := by
  change (stageStep A γ enumK (s + 1) (stage A γ enumK s)).Kstar = _
  rw [stageStep_Kstar, Nat.add_sub_cancel]
  rfl

/-- The value of `K*` pointwise monotonically decreases from a stage to its successor. -/
theorem stage_Kstar_succ_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) (x : BitString) : (stage A γ enumK (s + 1)).Kstar x ≤ (stage A γ enumK s).Kstar x := by
  rw [stage_Kstar_succ]
  by_cases hx : x = (enumK s).1
  · subst hx; rw [Function.update_self]; exact min_le_left _ _
  · rw [Function.update_of_ne hx]

/-- `K*` only decreases. -/
theorem stage_Kstar_antitone (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (x : BitString) : Antitone fun s => (stage A γ enumK s).Kstar x :=
  antitone_nat_of_succ_le fun s => stage_Kstar_succ_le A γ enumK s x

/-- The pair `enumK s` is taken into account from stage `s + 1` on. -/
theorem stage_Kstar_le_enum (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (s : ℕ) : (stage A γ enumK (s + 1)).Kstar (enumK s).1 ≤ (enumK s).2 := by
  rw [stage_Kstar_succ, Function.update_self]
  exact min_le_right _ _

/-- `K* ≥ K` at every stage (only pairs of `ov K` are enumerated). -/
theorem stage_Kstar_ge (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (s : ℕ) (x : BitString) : (K.H x : ℕ∞) ≤ (stage A γ enumK s).Kstar x := by
  induction s with
  | zero => exact le_top
  | succ s ih =>
    rw [stage_Kstar_succ]
    by_cases hx : x = (enumK s).1
    · subst hx
      rw [Function.update_self]
      refine le_min ih ?_
      exact_mod_cast (henum (enumK s)).2 ⟨s, rfl⟩
    · rw [Function.update_of_ne hx]; exact ih

/-- `K*(x) = K(x)` from some stage on. -/
theorem stage_Kstar_eventually (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (x : BitString) : ∃ s₀, ∀ s, s₀ ≤ s → (stage A γ enumK s).Kstar x = K.H x := by
  obtain ⟨t, ht⟩ := (henum (x, K.H x)).1 le_rfl
  refine ⟨t + 1, fun s hs => le_antisymm ?_ (stage_Kstar_ge A K γ enumK henum s x)⟩
  calc (stage A γ enumK s).Kstar x ≤ (stage A γ enumK (t + 1)).Kstar x :=
        stage_Kstar_antitone A γ enumK x hs
    _ = (stage A γ enumK (t + 1)).Kstar (enumK t).1 := by rw [ht]
    _ ≤ (enumK t).2 := stage_Kstar_le_enum A γ enumK t
    _ = K.H x := by rw [ht]

/-- `F*` only decreases. -/
theorem stage_Fstar_antitone' (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (x : BitString) : Antitone fun s => (stage A γ enumK s).Fstar x :=
  antitone_nat_of_succ_le fun s => stage_Fstar_antitone A γ enumK s x

/-- `F*(x) = F(x)` from some stage on. -/
theorem stage_Fstar_eventually (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (x : BitString) : ∃ s₀, ∀ s, s₀ ≤ s → (stage A γ enumK s).Fstar x = Flim A γ enumK x := by
  obtain ⟨s₁, hs₁⟩ := Nat.sInf_mem (Set.range_nonempty fun s => (stage A γ enumK s).Fstar x)
  refine ⟨s₁, fun s hs => le_antisymm ?_ (ciInf_le (OrderBot.bddBelow _) s)⟩
  calc (stage A γ enumK s).Fstar x ≤ (stage A γ enumK s₁).Fstar x :=
        stage_Fstar_antitone' A γ enumK x hs
    _ = Flim A γ enumK x := hs₁

/-- Pointwise, `H*_s` eventually equals `H = min (K + 5, F + 3)` (`K*` reaches `K.H x` once the
pair `(x, K.H x)` is enumerated; `F*` is antitone in `ℕ`, hence eventually constant). -/
theorem hval_eventually_eq_Hmin (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (x : BitString) :
    ∃ s₀, ∀ s, s₀ ≤ s → (stage A γ enumK s).hval x = Hmin K (Flim A γ enumK) x := by
  obtain ⟨s₁, h₁⟩ := stage_Kstar_eventually A K γ enumK henum x
  obtain ⟨s₂, h₂⟩ := stage_Fstar_eventually A γ enumK x
  refine ⟨max s₁ s₂, fun s hs => ?_⟩
  have hK := h₁ s (le_of_max_le_left hs)
  have hF := h₂ s (le_of_max_le_right hs)
  unfold CState.hval CState.Hstar
  rw [hK, hF]
  unfold Hmin
  rw [show min ((K.H x : ℕ∞) + 5) ((Flim A γ enumK x : ℕ∞) + 3) =
      ((min (K.H x + 5) (Flim A γ enumK x + 3) : ℕ) : ℕ∞) by rfl]
  exact ENat.toNat_natCast _

/-- Claim 3: `∑_x 2^{-H(x)} ≤ 1/8` for `H = min (K + 5, F + 3)` (four contributions of at most
`1/32`: the initial values `2|x| + 6`, the moves of `K`, the moves of `F` on games destroyed by a
cheating `K`, and the moves of `F` on the other games). -/
theorem Flim_mass (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (S : Finset BitString) : ∑ x ∈ S, (2 : ℝ)⁻¹ ^ Hmin K (Flim A γ enumK) x ≤ 1 / 8 := by
  choose f hf using fun x => hval_eventually_eq_Hmin A K γ enumK henum x
  calc ∑ x ∈ S, (2 : ℝ)⁻¹ ^ Hmin K (Flim A γ enumK) x
      = ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (stage A γ enumK (S.sup f)).hval x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hf x _ (Finset.le_sup hx)]
    _ ≤ 1 / 8 := stage_mass A K γ enumK henum _ S

omit [Family] in
/-- `2^{-F} = 8 · 2^{-(F+3)} ≤ 8 · 2^{-Hmin K F}`, so the Kraft sum of `F` is at most `1`. -/
theorem kraft_of_Hmin_mass (K : AprioriComplexity) (F : BitString → ℕ)
    (h : ∀ S : Finset BitString, ∑ x ∈ S, (2 : ℝ)⁻¹ ^ Hmin K F x ≤ 1 / 8) (S : Finset BitString) :
    ∑ x ∈ S, (2 : ℝ)⁻¹ ^ F x ≤ 1 := by
  have hpt : ∀ x, (2 : ℝ)⁻¹ ^ F x ≤ 8 * (2 : ℝ)⁻¹ ^ Hmin K F x := by
    intro x
    have h1 : Hmin K F x ≤ F x + 3 := min_le_right _ _
    have h2 : (2 : ℝ)⁻¹ ^ (F x + 3) ≤ (2 : ℝ)⁻¹ ^ Hmin K F x :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
    have h3 : (2 : ℝ)⁻¹ ^ (F x + 3) = (2 : ℝ)⁻¹ ^ F x / 8 := by
      rw [pow_add]; ring
    linarith
  calc ∑ x ∈ S, (2 : ℝ)⁻¹ ^ F x ≤ ∑ x ∈ S, 8 * (2 : ℝ)⁻¹ ^ Hmin K F x :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = 8 * ∑ x ∈ S, (2 : ℝ)⁻¹ ^ Hmin K F x := by rw [Finset.mul_sum]
    _ ≤ 8 * (1 / 8) := by gcongr; exact h S
    _ = 1 := by norm_num

/-- Consequently `F` is an entropy function (`2^{-F-3} ≤ 2^{-H}` and Property 1).  (The
effectiveness hypotheses `hγ`, `hK` are necessary: for arbitrary enumerations the overgraph of
`F` need not be c.e.) -/
theorem Flim_entropy (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ')
    (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) (enumK : ℕ → BitString × ℕ)
    (hK : Computable enumK) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p) :
    IsEntropyFun (Flim A γ enumK) :=
  ⟨kraft_of_Hmin_mass K _ (Flim_mass A K γ enumK henum),
    Flim_re A hA hW γ hγ enumK hK⟩

end Kolmogorov.RandomStrings
