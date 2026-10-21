/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.Stages

/-!
# Claim 3, second layer, and the mass accounting helpers

The second layer of Claim 3 (the total mass `∑_x 2^{-H(x)} ≤ 1/8`) and the helper lemmas for
`kIncr_sum_le` and `fIncr_sum_le`.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

/-! ### Claim 3, second layer -/

/-- The increase of `∑_{x ∈ S} 2^{-H*(x)}` caused by `K` in stage `t + 1` (the update of `K*` with
the pair `enumK t`). -/
noncomputable def kIncr (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t : ℕ) (S : Finset BitString) : ℝ :=
  ∑ x ∈ S, ((2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x -
    (2 : ℝ)⁻¹ ^ (stage A γ enumK t).hval x)

/-- The increase of `∑_{x ∈ S} 2^{-H*(x)}` caused by our flips in stage `t + 1` (the requirements
do not change `K*`, `stageStep_Kstar`). -/
noncomputable def fIncr (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t : ℕ) (S : Finset BitString) : ℝ :=
  ∑ x ∈ S, ((2 : ℝ)⁻¹ ^ (stage A γ enumK (t + 1)).hval x -
    (2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x)

/-- The initial values: `H*_0(x) = 2|x| + 6`. -/
theorem stage_zero_hval (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (x : BitString) :
    (stage A γ enumK 0).hval x = 2 * x.length + 6 := by
  change (min ((⊤ : ℕ∞) + 5) (((2 * x.length + 3 : ℕ) : ℕ∞) + 3)).toNat = 2 * x.length + 6
  rw [top_add, min_eq_right le_top]
  rw [show ((2 * x.length + 3 : ℕ) : ℕ∞) + 3 = ((2 * x.length + 6 : ℕ) : ℕ∞) by
    push_cast; ring]
  exact ENat.toNat_natCast _

/-- Telescoping: the mass at stage `s` is the initial mass plus the increases of the stages. -/
theorem mass_telescope (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (S : Finset BitString) (s : ℕ) :
    ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (stage A γ enumK s).hval x =
      ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 6) +
        ∑ t ∈ Finset.range s, (kIncr A γ enumK t S + fIncr A γ enumK t S) := by
  induction s with
  | zero => simp [stage_zero_hval]
  | succ s ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    unfold kIncr fIncr
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

section

omit [Family]

/-- The initial mass: `∑_x 2^{-(2|x|+6)} ≤ ∑_n 2^n 2^{-(2n+6)} = 1/32`. -/
theorem kraft_init (S : Finset BitString) : ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 6) ≤ 1 / 32 := by
  classical
  obtain ⟨M, hmaps⟩ : ∃ M, ∀ x ∈ S, x.length ∈ Finset.range M := by
    refine ⟨(S.image List.length).sup id + 1, fun x hx => ?_⟩
    rw [Finset.mem_range]
    have : x.length ≤ (S.image List.length).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hx)
    omega
  calc ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (2 * x.length + 6)
      = ∑ n ∈ Finset.range M, ∑ x ∈ S with x.length = n, (2 : ℝ)⁻¹ ^ (2 * x.length + 6) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ n ∈ Finset.range M, (64 : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n := by
        apply Finset.sum_le_sum
        intro n _
        have hc : ∑ x ∈ S with x.length = n, (2 : ℝ)⁻¹ ^ (2 * x.length + 6)
            = ((S.filter fun x => x.length = n).card : ℝ) * (2 : ℝ)⁻¹ ^ (2 * n + 6) := by
          rw [Finset.sum_congr rfl (g := fun _ => (2 : ℝ)⁻¹ ^ (2 * n + 6))
            (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
        rw [hc]
        have hcard : ((S.filter fun x => x.length = n).card : ℝ) ≤ 2 ^ n := by
          exact_mod_cast card_filter_length_le S n
        have hpos : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (2 * n + 6) := by positivity
        calc ((S.filter fun x => x.length = n).card : ℝ) * (2 : ℝ)⁻¹ ^ (2 * n + 6)
            ≤ 2 ^ n * (2 : ℝ)⁻¹ ^ (2 * n + 6) := mul_le_mul_of_nonneg_right hcard hpos
          _ = (64 : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n := by
            have h2 : (2 : ℝ)⁻¹ ^ (2 * n + 6) = (2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ n * (64 : ℝ)⁻¹ := by
              rw [show 2 * n + 6 = n + n + 6 by ring, pow_add, pow_add]; norm_num
            have h3 : (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
            rw [h2, one_div]
            calc (2 : ℝ) ^ n * ((2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ n * (64 : ℝ)⁻¹)
                = ((2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n) * ((64 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n) := by ring
              _ = (64 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n := by rw [h3, one_mul]
    _ = (64 : ℝ)⁻¹ * ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ (64 : ℝ)⁻¹ * 2 := by gcongr; exact sum_geometric_two_le M
    _ = 1 / 32 := by norm_num

/-! ### Mass accounting: helpers for `kIncr_sum_le` and `fIncr_sum_le` -/

/-- `H*` is finite: its value is `hval`. -/
theorem mass_coe_hval (σ : CState) (x : BitString) : ((σ.hval x : ℕ) : ℕ∞) = σ.Hstar x := by
  have h2 : (σ.Fstar x : ℕ∞) + 3 ≠ ⊤ := by
    rw [show (σ.Fstar x : ℕ∞) + 3 = ((σ.Fstar x + 3 : ℕ) : ℕ∞) by push_cast; ring]
    exact ENat.natCast_ne_top _
  exact ENat.natCast_toNat (ne_top_of_le_ne_top h2 (by unfold CState.Hstar; exact min_le_right _ _))

/-- The minimum of two natural numbers coerces to the minimum of their coercions in `ℕ∞`. -/
theorem mass_coe_min (a b : ℕ) : ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) (b : ℕ∞) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
/-- An integer lower bound on `H*` implies the same lower bound on its finite value `hval`. -/
theorem mass_le_hval (σ : CState) (x : BitString) (m : ℕ) (h : (m : ℕ∞) ≤ σ.Hstar x) :
    m ≤ σ.hval x := by
  rw [← mass_coe_hval] at h
  exact_mod_cast h

/-- The finite value `hval` is monotonic with respect to `K*` and `F*`. -/
theorem mass_hval_le_hval {σ τ : CState} {x : BitString} (hK : σ.Kstar x ≤ τ.Kstar x)
    (hF : σ.Fstar x ≤ τ.Fstar x) : σ.hval x ≤ τ.hval x := by
  apply mass_le_hval
  rw [mass_coe_hval]
  unfold CState.Hstar
  exact min_le_min (add_le_add hK le_rfl) (add_le_add (by exact_mod_cast hF) le_rfl)

/-- Two states with identical `F*` and `K*` components have identical `hval` components. -/
theorem mass_hval_congr {σ τ : CState} (hF : σ.Fstar = τ.Fstar) (hK : σ.Kstar = τ.Kstar) :
    σ.hval = τ.hval := by
  funext x
  unfold CState.hval CState.Hstar
  rw [hF, hK]

end

/-- Processing a requirement does not change the `K*` component of the state. -/
theorem mass_processReq_Kstar (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (σ₀ : CState) (e : ℕ)
    (p : CState × Bool) : (processReq A γ σ₀ e p).1.Kstar = p.1.Kstar := by
  unfold processReq
  split
  · rfl
  · split
    · unfold startGame
      split
      · rfl
      · rfl
    · unfold processGame
      split_ifs <;> rfl

/-- The `K*` component after stage `t + 1` is exactly the `K*` component after the `K`-update. -/
theorem mass_stage_succ_Kstar (A : Set BitString) (γ : ℕ → OTMCode × ℕ) (enumK : ℕ → BitString × ℕ)
    (t : ℕ) : (stage A γ enumK (t + 1)).Kstar = (updateK enumK t (stage A γ enumK t)).Kstar := by
  have h : ∀ (l : List ℕ) (p : CState × Bool),
      (l.foldl (fun p e => processReq A (reqγ γ) (stage A γ enumK t) (e + 1) p) p).1.Kstar =
        p.1.Kstar := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons a l ih => intro p; exact (ih _).trans (mass_processReq_Kstar _ _ _ _ _)
  change (stageStep A γ enumK (t + 1) (stage A γ enumK t)).Kstar = _
  unfold stageStep
  rw [h, Nat.add_sub_cancel]

omit [Family] in
/-- Updating `K*` does not increase the `hval` component. -/
theorem mass_hval_updateK_le (enumK : ℕ → BitString × ℕ) (t : ℕ) (σ : CState) (x : BitString) :
    (updateK enumK t σ).hval x ≤ σ.hval x := by
  refine mass_hval_le_hval ?_ le_rfl
  change Function.update σ.Kstar (enumK t).1 (min (σ.Kstar (enumK t).1) ((enumK t).2 : ℕ∞)) x ≤
    σ.Kstar x
  by_cases hx : x = (enumK t).1
  · subst hx; rw [Function.update_self]; exact min_le_left _ _
  · rw [Function.update_of_ne hx]

/-- The `hval` component after stage `t + 1` is at most its value after the `K`-update. -/
theorem mass_hval_stage_succ_le (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (t : ℕ) (x : BitString) :
    (stage A γ enumK (t + 1)).hval x ≤ (updateK enumK t (stage A γ enumK t)).hval x := by
  apply mass_hval_le_hval
  · rw [mass_stage_succ_Kstar]
  · exact stage_Fstar_antitone A γ enumK t x

/-- After a `K`-update, `H*(x) ≥ min (K(x) + 5, H*_{old}(x))`. -/
theorem mass_hval_updateK_ge (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (t : ℕ) (x : BitString) :
    min (K.H x + 5) ((stage A γ enumK t).hval x) ≤
      (updateK enumK t (stage A γ enumK t)).hval x := by
  have hK : ∀ s, (K.H x : ℕ∞) ≤ (stage A γ enumK s).Kstar x := by
    intro s
    induction s with
    | zero => exact le_top
    | succ s ih =>
      rw [mass_stage_succ_Kstar]
      change (K.H x : ℕ∞) ≤ Function.update (stage A γ enumK s).Kstar (enumK s).1
        (min ((stage A γ enumK s).Kstar (enumK s).1) ((enumK s).2 : ℕ∞)) x
      by_cases hx : x = (enumK s).1
      · subst hx
        rw [Function.update_self]
        exact le_min ih (by exact_mod_cast (henum (enumK s)).2 ⟨s, rfl⟩)
      · rw [Function.update_of_ne hx]; exact ih
  have hK' : (K.H x : ℕ∞) ≤ (updateK enumK t (stage A γ enumK t)).Kstar x := by
    rw [← mass_stage_succ_Kstar]; exact hK (t + 1)
  apply mass_le_hval
  rw [mass_coe_min, mass_coe_hval]
  unfold CState.Hstar
  refine le_min ?_ ?_
  · refine (min_le_left _ _).trans ?_
    push_cast
    exact add_le_add hK' le_rfl
  · exact (min_le_right _ _).trans (min_le_right _ _)

omit [Family] in
/-- Disjoint increments: if `a t ≤ b t ≤ a (t + 1)` and every proper increment ends below `c`,
then the increments sum to at most `min (a s) c`. -/
theorem mass_sum_steps_le (a b : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a 0)
    (hab : ∀ t, a t ≤ b t) (hba : ∀ t, b t ≤ a (t + 1)) (hbc : ∀ t, a t < b t → b t ≤ c) :
    ∀ s, ∑ t ∈ Finset.range s, (b t - a t) ≤ a s ∧ ∑ t ∈ Finset.range s, (b t - a t) ≤ c := by
  intro s
  induction s with
  | zero => simp [ha, hc]
  | succ s ih =>
    rw [Finset.sum_range_succ]
    obtain ⟨ih1, ih2⟩ := ih
    have h1 := hab s
    have h2 := hba s
    rcases lt_or_ge (a s) (b s) with h | h
    · have h3 := hbc s h
      constructor <;> linarith
    · constructor <;> linarith
/-- (C3-K) The total increase caused by `K` is at most `1/32`: for each string the increases
caused by `K` occupy disjoint subintervals of `[0, 2^{-(K x + 5)}]` (`H*` is antitone, and after a
`K`-increase `H*(x) = K*(x) + 5 ≥ K(x) + 5`, `stage_Kstar_ge`), and `∑_x 2^{-(K x + 5)} ≤ 1/32` by
Kraft for `K`. -/
theorem kIncr_sum_le (A : Set BitString) (K : AprioriComplexity) (γ : ℕ → OTMCode × ℕ)
    (enumK : ℕ → BitString × ℕ) (henum : ∀ p : BitString × ℕ, K.H p.1 ≤ p.2 ↔ ∃ s, enumK s = p)
    (s : ℕ) (S : Finset BitString) : ∑ t ∈ Finset.range s, kIncr A γ enumK t S ≤ 1 / 32 := by
  have hpt : ∀ x : BitString, ∑ t ∈ Finset.range s,
      ((2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x -
        (2 : ℝ)⁻¹ ^ (stage A γ enumK t).hval x) ≤ (2 : ℝ)⁻¹ ^ (K.H x + 5) := by
    intro x
    refine (mass_sum_steps_le (fun t => (2 : ℝ)⁻¹ ^ (stage A γ enumK t).hval x)
      (fun t => (2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x)
      ((2 : ℝ)⁻¹ ^ (K.H x + 5)) (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
      ?_ ?_ ?_ s).2
    · intro t
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (mass_hval_updateK_le enumK t _ x)
    · intro t
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (mass_hval_stage_succ_le A γ enumK t x)
    · intro t ht
      have hp : (2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x ≤
          (2 : ℝ)⁻¹ ^ min (K.H x + 5) ((stage A γ enumK t).hval x) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (mass_hval_updateK_ge A K γ enumK henum t x)
      rcases min_choice (K.H x + 5) ((stage A γ enumK t).hval x) with hm | hm
      · rw [hm] at hp; exact hp
      · rw [hm] at hp; exact absurd ht (not_lt.2 hp)
  calc ∑ t ∈ Finset.range s, kIncr A γ enumK t S
      = ∑ x ∈ S, ∑ t ∈ Finset.range s,
          ((2 : ℝ)⁻¹ ^ (updateK enumK t (stage A γ enumK t)).hval x -
            (2 : ℝ)⁻¹ ^ (stage A γ enumK t).hval x) := by
        unfold kIncr; exact Finset.sum_comm
    _ ≤ ∑ x ∈ S, (2 : ℝ)⁻¹ ^ (K.H x + 5) := Finset.sum_le_sum fun x _ => hpt x
    _ = (2 : ℝ)⁻¹ ^ 5 * ∑ x ∈ S, (2 : ℝ)⁻¹ ^ K.H x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by rw [pow_add, mul_comm]
    _ ≤ (2 : ℝ)⁻¹ ^ 5 * 1 := by gcongr; exact K.kraft S
    _ = 1 / 32 := by norm_num

end Kolmogorov.RandomStrings
