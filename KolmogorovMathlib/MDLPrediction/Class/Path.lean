/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Charge

/-!
# Polynomial pathwise error for effective mixture classes

Every minimizer choice is covered. The path budget may depend on the path, while
the polynomial constants depend only on the fixed machine and presentation.
Blueprint nodes: `enum:theorem9`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- The squared error of a class predictor on one path and one bit.
Blueprint node `enum:theorem9`. -/
noncomputable def classPathError (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (P : Measure CantorSeq)
    (choose : BitString → Measure CantorSeq) (w : CantorSeq) (b : Bool) : ℝ :=
  ∑' n : ℕ, (classPredictor U hU A choose (cantorPrefix w n) b -
    condProb (cantorMass P) (cantorPrefix w n) b) ^ 2

/-- A class minimizer on a budgeted path has bounded relative complexity. -/
private lemma class_choice_complexity_bound
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ cU cA : ℕ, ∀ (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ)
      (choose : BitString → Measure CantorSeq),
      P ∈ A.carrier → PathBudget P w D → IsClassChoice U hU A choose →
      ∀ n : ℕ, choose (cantorPrefix w n) ∈ A.carrier ∧
        IsClassWinner U hU A (choose (cantorPrefix w n)) (cantorPrefix w n) ∧
        classComplexity U hU A (choose (cantorPrefix w n)) ≤
          3 * classComplexity U hU A P + D + cU + cA := by
  obtain ⟨cU, cA, -, -, hwin⟩ := class_winner_bounds U hU A
  refine ⟨cU, cA, fun P w D choose hP hD hch n => ?_⟩
  have hQ : IsClassWinner U hU A (choose (cantorPrefix w n)) (cantorPrefix w n) :=
    hch _ ⟨P, hP, base_budget_positive P w D n hD⟩
  have h2 := (hwin P (choose (cantorPrefix w n)) w D (cantorPrefix w n) hP ⟨n, rfl⟩ hD hQ).2
  exact ⟨hQ.1, hQ, by omega⟩

/-- Partition prediction error among finitely many selected class measures. -/
private lemma classPathError_le_finite_partition
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU)
    (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ)
    (choose : BitString → Measure CantorSeq)
    (hP : P ∈ A.carrier) (hD : PathBudget P w D)
    (S : Set (Measure CantorSeq))
    (hS : ∀ n : ℕ, choose (cantorPrefix w n) ∈ S)
    (hS_fin : S.Finite)
    (C_charge : ℝ)
    (h_charge : ∀ Q ∈ S,
      Summable (fun n : {n : ℕ // choose (cantorPrefix w n) = Q} =>
        (condProb (cantorMass Q) (cantorPrefix w n.1) false -
          condProb (cantorMass P) (cantorPrefix w n.1) false) ^ 2) ∧
      (∑' n : {n : ℕ // choose (cantorPrefix w n) = Q},
        (condProb (cantorMass Q) (cantorPrefix w n.1) false -
          condProb (cantorMass P) (cantorPrefix w n.1) false) ^ 2) ≤
        C_charge * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ)) :
    Summable (fun n : ℕ =>
      (classPredictor U hU A choose (cantorPrefix w n) false -
        condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ∧
    classPathError U hU A P choose w false ≤
      (S.ncard : ℝ) * C_charge * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) := by
  classical
  have hmem : ∀ n : ℕ, choose (cantorPrefix w n) ∈ hS_fin.toFinset := by
    intro n
    exact (Set.Finite.mem_toFinset hS_fin).mpr (hS n)
  have hf : ∀ n : ℕ, (classPredictor U hU A choose (cantorPrefix w n) false - condProb
    (cantorMass P) (cantorPrefix w n) false) ^ 2 = (condProb (cantorMass (choose (cantorPrefix
      w n))) (cantorPrefix w n) false - condProb (cantorMass P) (cantorPrefix w n) false) ^ 2 := by
    intro n
    have hex : ∃ Q ∈ A.carrier, 0 < cantorMass Q (cantorPrefix w n) := ⟨P, hP,
      base_budget_positive P w D n hD⟩
    unfold classPredictor
    rw [ite_eq_left_of_eq_true _ _ (eq_true hex)]
  have hfin : ∀ s : Finset ℕ, ∑ n ∈ s, (classPredictor U hU A choose (cantorPrefix w n) false -
    condProb (cantorMass P) (cantorPrefix w n) false) ^ 2 ≤ (S.ncard : ℝ) * C_charge *
      ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) := by
    intro s
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => choose (cantorPrefix w n)) (t :=
      hS_fin.toFinset) (fun n _ => hmem n)]
    calc
      ∑ Q ∈ hS_fin.toFinset, ∑ n ∈ s with choose (cantorPrefix w n) = Q, (classPredictor U hU A
        choose (cantorPrefix w n) false - condProb (cantorMass P) (cantorPrefix w n) false) ^ 2
      _ ≤ ∑ Q ∈ hS_fin.toFinset, C_charge * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro Q hQ
        obtain ⟨hsum, hle⟩ := h_charge Q (hS_fin.mem_toFinset.mp hQ)
        refine le_trans (le_of_eq ?_) (le_trans (Summable.sum_le_tsum (s.subtype (fun n =>
          choose (cantorPrefix w n) = Q)) (fun _ _ => sq_nonneg _) hsum) hle)
        rw [Finset.sum_subtype_eq_sum_filter (fun n => (condProb (cantorMass Q) (cantorPrefix w
          n) false - condProb (cantorMass P) (cantorPrefix w n) false) ^ 2)]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [hf n, hn.2]
      _ = (S.ncard : ℝ) * C_charge * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card S hS_fin]
        ring
  have hsum : Summable (fun n => (classPredictor U hU A choose (cantorPrefix w n) false -
    condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) := summable_of_sum_le (fun n =>
      sq_nonneg _) hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

/-- Absorb the finite partition count into a polynomial bound. -/
private lemma classPathError_polynomial_bound
    (C_charge : ℝ) (hC_charge_pos : 0 < C_charge)
    (C_count e cU cA : ℕ) :
    ∃ (C : ℝ) (e_out : ℕ), 0 < C ∧
      ∀ (P_comp D : ℕ) (B : ℕ) (S_card : ℕ),
        B ≤ 3 * P_comp + D + cU + cA →
        S_card ≤ C_count * (B + 2) ^ (e + 1) →
        (S_card : ℝ) * C_charge * ((P_comp + D + 1 : ℕ) : ℝ) ≤
          C * ((P_comp + D + 1 : ℕ) : ℝ) ^ e_out := by
  refine ⟨((C_count * (3 + cU + cA) ^ (e + 1) : ℕ) : ℝ) * C_charge + 1, e + 2, by positivity, ?_⟩
  intro P_comp D B S_card hB hS
  have hB2 : B + 2 ≤ (3 + cU + cA) * (P_comp + D + 1) := by nlinarith
  have hS' : S_card ≤ C_count * (3 + cU + cA) ^ (e + 1) * (P_comp + D + 1) ^ (e + 1) := by
    calc S_card
      _ ≤ C_count * (B + 2) ^ (e + 1) := hS
      _ ≤ C_count * ((3 + cU + cA) * (P_comp + D + 1)) ^ (e + 1) := by gcongr
      _ = C_count * ((3 + cU + cA) ^ (e + 1) * (P_comp + D + 1) ^ (e + 1)) := by rw [mul_pow]
      _ = C_count * (3 + cU + cA) ^ (e + 1) * (P_comp + D + 1) ^ (e + 1) := by ring
  have hSR : (S_card : ℝ) ≤ ((C_count * (3 + cU + cA) ^ (e + 1) : ℕ) : ℝ) * ((P_comp + D + 1 :
    ℕ) : ℝ) ^ (e + 1) := by
    exact_mod_cast hS'
  have hm : (0 : ℝ) ≤ ((P_comp + D + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h_charge_nonneg : 0 ≤ C_charge := le_of_lt hC_charge_pos
  calc (S_card : ℝ) * C_charge * ((P_comp + D + 1 : ℕ) : ℝ)
    _ ≤ (((C_count * (3 + cU + cA) ^ (e + 1) : ℕ) : ℝ) * ((P_comp + D + 1 : ℕ) : ℝ) ^ (e + 1))
      * C_charge * ((P_comp + D + 1 : ℕ) : ℝ) := by
      gcongr
    _ = (((C_count * (3 + cU + cA) ^ (e + 1) : ℕ) : ℝ) * C_charge) * ((P_comp + D + 1 : ℕ) : ℝ)
      ^ (e + 2) := by ring
    _ ≤ (((C_count * (3 + cU + cA) ^ (e + 1) : ℕ) : ℝ) * C_charge + 1) * ((P_comp + D + 1 : ℕ)
      : ℝ) ^ (e + 2) := by
      gcongr
      linarith

/-- Corrected Theorem 9: every budgeted path has a polynomial square-sum bound
for bit zero. Blueprint node `enum:theorem9`. -/
theorem class_pathwise_sq_polynomial (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ (C : ℝ) (e : ℕ), 0 < C ∧
      ∀ (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ)
        (choose : BitString → Measure CantorSeq),
        P ∈ A.carrier → PathBudget P w D → IsClassChoice U hU A choose →
          Summable (fun n : ℕ =>
            (classPredictor U hU A choose (cantorPrefix w n) false -
              condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ∧
          classPathError U hU A P choose w false ≤
            C * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) ^ e := by
  obtain ⟨cU, cA, hcUcA⟩ := class_choice_complexity_bound U hU A
  obtain ⟨C_charge, hC_charge_pos, h_charge_bound⟩ := enum_class_charge U hU A
  obtain ⟨C_count, e, hever⟩ := enum_ever_count U hU A
  obtain ⟨C, e_out, hC_pos, hC_bound⟩ := classPathError_polynomial_bound C_charge hC_charge_pos
    C_count e cU cA
  use C, e_out
  refine ⟨hC_pos, ?_⟩
  intro P w D choose hP hD hChoice
  have h_win := hcUcA P w D choose hP hD hChoice
  let B := 3 * classComplexity U hU A P + D + cU + cA
  have hB : ∀ n : ℕ, classComplexity U hU A (choose (cantorPrefix w n)) ≤ B ∧
      IsClassWinner U hU A (choose (cantorPrefix w n)) (cantorPrefix w n) := by
    intro n
    exact ⟨(h_win n).2.2, (h_win n).2.1⟩
  let S := {Q | Q ∈ A.carrier ∧ classComplexity U hU A Q ≤ B ∧ ∃ x : BitString, IsClassWinner U
    hU A Q x}
  have hS_fin : S.Finite := (hever B).1
  have hS_card : S.ncard ≤ C_count * (B + 2) ^ (e + 1) := (hever B).2
  have h_charge_all : ∀ Q ∈ S,
    Summable (fun n : {n : ℕ // choose (cantorPrefix w n) = Q} =>
      (condProb (cantorMass Q) (cantorPrefix w n.1) false -
        condProb (cantorMass P) (cantorPrefix w n.1) false) ^ 2) ∧
    (∑' n : {n : ℕ // choose (cantorPrefix w n) = Q},
      (condProb (cantorMass Q) (cantorPrefix w n.1) false -
        condProb (cantorMass P) (cantorPrefix w n.1) false) ^ 2) ≤
      C_charge * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) := by
    intro Q hQ
    have h_charge_q := h_charge_bound P w D Q choose hP hD hChoice
    have h_eq : C_charge * (↑(classComplexity U hU A P) + ↑D + 1) =
      C_charge * ↑(classComplexity U hU A P + D + 1) := by
      push_cast
      rfl
    rw [←h_eq]
    exact h_charge_q
  have hS : ∀ n : ℕ, choose (cantorPrefix w n) ∈ S := by
    intro n
    exact ⟨(h_win n).1, (hB n).1, cantorPrefix w n, (hB n).2⟩
  obtain ⟨h_sum, h_err⟩ := classPathError_le_finite_partition
    U hU A P w D choose hP hD S hS hS_fin C_charge h_charge_all
  refine ⟨h_sum, ?_⟩
  apply le_trans h_err
  exact hC_bound (classComplexity U hU A P) D B S.ncard (le_refl B) hS_card

/-- Bit-one and bit-zero squared prediction errors agree on a budgeted path. -/
private lemma classPathError_true_sq_eq (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ)
    (choose : BitString → Measure CantorSeq) (hP : P ∈ A.carrier) (hB : PathBudget P w D)
    (hch : IsClassChoice U hU A choose) (n : ℕ) :
    (classPredictor U hU A choose (cantorPrefix w n) true -
      condProb (cantorMass P) (cantorPrefix w n) true) ^ 2 =
    (classPredictor U hU A choose (cantorPrefix w n) false -
      condProb (cantorMass P) (cantorPrefix w n) false) ^ 2 := by
  have hPx : 0 < cantorMass P (cantorPrefix w n) := base_budget_positive P w D n hB
  have hex : ∃ Q ∈ A.carrier, 0 < cantorMass Q (cantorPrefix w n) := ⟨P, hP, hPx⟩
  obtain ⟨⟨i, hi⟩, hQx, -⟩ := hch _ hex
  obtain ⟨j, hj⟩ := hP
  have : IsProbabilityMeasure P := by
    rw [← hj]
    exact (A.A j).probability
  have : IsProbabilityMeasure (choose (cantorPrefix w n)) := by
    rw [← hi]
    exact (A.A i).probability
  have h1 := condProb_cantorMass_add_eq_one P hPx.ne'
  have h2 := condProb_cantorMass_add_eq_one (choose (cantorPrefix w n)) hQx.ne'
  have hcp : ∀ b, classPredictor U hU A choose (cantorPrefix w n) b =
      condProb (cantorMass (choose (cantorPrefix w n))) (cantorPrefix w n) b := by
    intro b
    unfold classPredictor
    exact ite_eq_left_of_eq_true _ _ (eq_true hex)
  rw [hcp, hcp]
  have hd : condProb (cantorMass (choose (cantorPrefix w n))) (cantorPrefix w n) true -
      condProb (cantorMass P) (cantorPrefix w n) true =
    -(condProb (cantorMass (choose (cantorPrefix w n))) (cantorPrefix w n) false -
      condProb (cantorMass P) (cantorPrefix w n) false) := by
    linarith
  rw [hd, neg_sq]

/-- The same polynomial square-sum bound holds for bit one.
Blueprint node `enum:theorem9`. -/
theorem class_pathwise_sq_polynomial_true (U : Map)
    (hU : IsOptimalPrefixConditional U) (A : EffectiveMixtureClass U hU) :
    ∃ (C : ℝ) (e : ℕ), 0 < C ∧
      ∀ (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ)
        (choose : BitString → Measure CantorSeq),
        P ∈ A.carrier → PathBudget P w D → IsClassChoice U hU A choose →
          Summable (fun n : ℕ =>
            (classPredictor U hU A choose (cantorPrefix w n) true -
              condProb (cantorMass P) (cantorPrefix w n) true) ^ 2) ∧
          classPathError U hU A P choose w true ≤
            C * ((classComplexity U hU A P + D + 1 : ℕ) : ℝ) ^ e := by
  obtain ⟨C, e, hC, h⟩ := class_pathwise_sq_polynomial U hU A
  refine ⟨C, e, hC, fun P w D choose hP hB hch => ?_⟩
  have key := funext (classPathError_true_sq_eq U hU A P w D choose hP hB hch)
  obtain ⟨hs, hle⟩ := h P w D choose hP hB hch
  refine ⟨key ▸ hs, ?_⟩
  unfold classPathError at hle ⊢
  rw [key]
  exact hle
end Kolmogorov.MDLPrediction
