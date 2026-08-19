import KolmogorovMathlib.CommonInformation.FiniteQuadruple
import KolmogorovMathlib.CommonInformation.ChainHistogram

namespace Kolmogorov
open Finset

/-- `highWeight` at `p = 3 / 4` scaled by 32 gives an integer. -/
theorem highWeight_threeFour_rationalAtom (a b g d : Bool) :
    ∃ m : ℕ, (32 : ℝ) * highWeight (3 / 4) a b g d = (m : ℝ) := by
  revert a b g d
  exact fun a b g d =>
    match a, b, g, d with
    | false, false, false, false => ⟨8, by norm_num [highWeight]⟩
    | false, true, false, false => ⟨0, by norm_num [highWeight]⟩
    | true, false, false, false => ⟨0, by norm_num [highWeight]⟩
    | true, true, false, false => ⟨0, by norm_num [highWeight]⟩
    | false, false, true, true => ⟨0, by norm_num [highWeight]⟩
    | false, true, true, true => ⟨0, by norm_num [highWeight]⟩
    | true, false, true, true => ⟨0, by norm_num [highWeight]⟩
    | true, true, true, true => ⟨8, by norm_num [highWeight]⟩
    | false, false, false, true => ⟨1, by norm_num [highWeight]⟩
    | false, true, false, true => ⟨3, by norm_num [highWeight]⟩
    | true, false, false, true => ⟨3, by norm_num [highWeight]⟩
    | true, true, false, true => ⟨1, by norm_num [highWeight]⟩
    | false, false, true, false => ⟨1, by norm_num [highWeight]⟩
    | false, true, true, false => ⟨3, by norm_num [highWeight]⟩
    | true, false, true, false => ⟨3, by norm_num [highWeight]⟩
    | true, true, true, false => ⟨1, by norm_num [highWeight]⟩

/-- If `E` has rational atoms with denominator `Q`, then `chainOfQuad E` has
rational atoms with denominator `Q`. -/
theorem chainOfQuad_rationalAtoms (Q : ℕ) (E : QuadDist) (hQ : 0 < Q)
    (hE : ∀ a b g d, ∃ m : ℕ, (Q : ℝ) * E.w a b g d = m) :
    (chainOfQuad E).RationalAtoms Q := by
  refine ⟨hQ, fun v => ?_⟩
  exact hE _ _ _ _

/-- The concrete rational-atom chain. -/
theorem exists_fiveEighths_rationalAtom_chain :
    ∃ D : ChainDist 1, D.RationalAtoms 32 ∧ D.IsIndep315Chain ∧
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧ D.prAgree01 = 5 / 8 := by
  let E := highDist (3 / 4) (by norm_num) (by norm_num)
  let D := chainOfQuad E
  have hE_atoms : ∀ a b g d, ∃ m : ℕ, (32 : ℝ) * E.w a b g d = m :=
    highWeight_threeFour_rationalAtom
  have hD_atoms : D.RationalAtoms 32 := chainOfQuad_rationalAtoms 32 E (by norm_num) hE_atoms
  have hD_chain : D.IsIndep315Chain := by
    refine ⟨?_, ?_, ?_⟩
    · refine Fin.forall_fin_one.mpr ?_
      change (chainOfQuad E).CondIndepCoords (0 : Fin 4) (2 : Fin 4) (1 : Fin 4)
      intro v₁ v₂ v₃
      rw [chainOfQuad.prAt3_021, chainOfQuad.prAt1, chainOfQuad.prAt2_01, chainOfQuad.prAt2_21]
      exact highDist_condIndepGivenGamma (p := 3 / 4) (by norm_num) (by norm_num) v₁ v₂ v₃
    · refine Fin.forall_fin_one.mpr ?_
      change (chainOfQuad E).CondIndepCoords (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
      intro v₁ v₂ v₃
      rw [chainOfQuad.prAt3_023, chainOfQuad.prAt3c, chainOfQuad.prAt2_03, chainOfQuad.prAt2_23]
      exact highDist_condIndepGivenDelta (p := 3 / 4) (by norm_num) (by norm_num) v₁ v₂ v₃
    · change (chainOfQuad E).IndepCoords (1 : Fin 4) (3 : Fin 4)
      intro v₁ v₂
      rw [chainOfQuad.prAt2_13, chainOfQuad.prAt1, chainOfQuad.prAt3c]
      exact highDist_gammaDeltaIndep (p := 3 / 4) (by norm_num) (by norm_num) v₁ v₂
  have h_alpha : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2 := fun a => by
    change (chainOfQuad E).prAt 0 a = 1 / 2
    rw [chainOfQuad.prAt0]
    exact highDist_prAlpha (p := 3 / 4) (by norm_num) (by norm_num) a
  have h_beta : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2 := fun b => by
    change (chainOfQuad E).prAt 2 b = 1 / 2
    rw [chainOfQuad.prAt2c]
    exact highDist_prBeta (p := 3 / 4) (by norm_num) (by norm_num) b
  have h_agree : D.prAgree01 = 5 / 8 := by
    rw [chainOfQuad.prAgree01_eq]
    have h := highDist_prAgree (p := 3 / 4) (by norm_num) (by norm_num)
    rw [h]
    norm_num
  exact ⟨D, hD_atoms, hD_chain, h_alpha, h_beta, h_agree⟩

/-- Concrete bottom histogram counts for the 5 / 8 chain. -/
theorem fiveEighths_bottom_histogram1 {N : ℕ} {D : ChainDist 1}
    (hQ : D.RationalAtoms 32) (h_alpha : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hdiv : 32 ∣ N) (a : Bool) :
    chainHistogram1 D hQ N (chainAlphaIdx 0) a = N / 2 := by
  have H := chainMarginal_eq_nat_of_pr D hQ (fun v => v (chainAlphaIdx 0) == a)
    (q := 2) (m := 1) (by norm_num) hdiv (by
      obtain ⟨c, hc⟩ := hdiv
      exact ⟨16 * c, by omega⟩)
    (by
      have h1 : D.pr (fun v => v (chainAlphaIdx 0) == a) = D.prAt (chainAlphaIdx 0) a := rfl
      rw [h1, h_alpha a]
      norm_num)
  unfold chainHistogram1
  rw [H]
  have h2 : (N / 2) * 1 = N / 2 := by omega
  exact h2

private lemma prAt_eq_sum_prAt2 {k : ℕ} (D : ChainDist k) (i j : Fin (2 * k + 2)) (a : Bool) :
    D.prAt i a = D.prAt2 i j a true + D.prAt2 i j a false := by
  unfold ChainDist.prAt ChainDist.prAt2 ChainDist.pr
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases h : v i = a
  · have h1 : (v i == a) = true := by simp [h]
    by_cases h2 : v j = true
    · have h3 : (v j == true) = true := by simp [h2]
      have h4 : (v j == false) = false := by simp [h2]
      simp [h1, h3, h4]
    · have h3 : (v j == true) = false := by simp [h2]
      have h4 : (v j == false) = true := by simp [h2]
      simp [h1, h3, h4]
  · have h1 : (v i == a) = false := by simp [h]
    simp [h1]

private lemma prAt_eq_sum_prAt2_left {k : ℕ} (D : ChainDist k) (i j : Fin (2 * k + 2)) (b : Bool) :
    D.prAt j b = D.prAt2 i j true b + D.prAt2 i j false b := by
  unfold ChainDist.prAt ChainDist.prAt2 ChainDist.pr
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases h : v j = b
  · have h1 : (v j == b) = true := by simp [h]
    by_cases h2 : v i = true
    · have h3 : (v i == true) = true := by simp [h2]
      have h4 : (v i == false) = false := by simp [h2]
      simp [h1, h3, h4]
    · have h3 : (v i == true) = false := by simp [h2]
      have h4 : (v i == false) = true := by simp [h2]
      simp [h1, h3, h4]
  · have h1 : (v j == b) = false := by simp [h]
    simp [h1]

private lemma prAgree_eq_sum_prAt2 {k : ℕ} (D : ChainDist k) (i j : Fin (2 * k + 2)) :
    D.pr (fun v => v i == v j) = D.prAt2 i j true true + D.prAt2 i j false false := by
  unfold ChainDist.prAt2 ChainDist.pr
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases h1 : v i = true <;> by_cases h2 : v j = true <;> simp_all

theorem fiveEighths_bottom_histogram2 {N : ℕ} {D : ChainDist 1}
    (hQ : D.RationalAtoms 32) (h_agree : D.prAgree01 = 5 / 8)
    (h_alpha : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (h_beta : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hdiv : 32 ∣ N) (a b : Bool) :
    chainHistogram2 D hQ N (chainAlphaIdx 0) (chainBetaIdx 0) a b =
      if a = b then 10 * (N / 32) else 6 * (N / 32) := by
  have H := chainMarginal_eq_nat_of_pr D hQ
    (fun v => (v (chainAlphaIdx 0) == a) && (v (chainBetaIdx 0) == b))
    (q := 32)
    (m := if a = b then 10 else 6)
    (by norm_num) hdiv (by
      obtain ⟨c, hc⟩ := hdiv
      exact ⟨c, by omega⟩)
    (by
      have h_pr : D.pr (fun v => (v (chainAlphaIdx 0) == a) && (v (chainBetaIdx 0) == b))
        = D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) a b := rfl
      rw [h_pr]
      have h_symm : ∀ (x y : Bool), D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) x y =
          if x = y then (10 : ℝ) / 32 else (6 : ℝ) / 32 := by
        intro x y
        have ht := prAt_eq_sum_prAt2 D (chainAlphaIdx 0) (chainBetaIdx 0) true
        have hf := prAt_eq_sum_prAt2 D (chainAlphaIdx 0) (chainBetaIdx 0) false
        have hl_t := prAt_eq_sum_prAt2_left D (chainAlphaIdx 0) (chainBetaIdx 0) true
        have hl_f := prAt_eq_sum_prAt2_left D (chainAlphaIdx 0) (chainBetaIdx 0) false
        have hag := prAgree_eq_sum_prAt2 D (chainAlphaIdx 0) (chainBetaIdx 0)
        rw [h_alpha true] at ht
        rw [h_alpha false] at hf
        rw [h_beta true] at hl_t
        rw [h_beta false] at hl_f
        have h_agree_eq :
            D.pr (fun v => v (chainAlphaIdx 0) == v (chainBetaIdx 0)) = 5 / 8 := h_agree
        rw [h_agree_eq] at hag
        cases x <;> cases y <;> simp <;> linarith
      rw [h_symm a b]
      split_ifs <;> norm_num)
  unfold chainHistogram2
  rw [H]
  split_ifs
  · omega
  · omega

end Kolmogorov
