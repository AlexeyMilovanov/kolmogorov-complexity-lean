/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Class.Exclusion
import KolmogorovMathlib.MDLPrediction.Class.Winner
import KolmogorovMathlib.MDLPrediction.Pairwise.Bound
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Polynomial winner count and one-winner path charge

The charge is restricted to times when the specified choice actually selects the
specified model. The empty selected-time set contributes zero.
Blueprint nodes: `enum:class-charge`, `enum:ever-count`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal BigOperators

/-- The total number of ever-winning class measures through complexity `B` is
bounded by one fixed polynomial. Blueprint node `enum:ever-count`. -/
theorem enum_ever_count (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ C e : ℕ, ∀ B : ℕ,
      (Set.Finite {Q : Measure CantorSeq | Q ∈ A.carrier ∧
        classComplexity U hU A Q ≤ B ∧
          ∃ x : BitString, IsClassWinner U hU A Q x}) ∧
      Set.ncard {Q : Measure CantorSeq | Q ∈ A.carrier ∧
        classComplexity U hU A Q ≤ B ∧
          ∃ x : BitString, IsClassWinner U hU A Q x} ≤ C * (B + 2) ^ (e + 1) := by
  obtain ⟨C, e, h⟩ := everWinners_layer_polynomial U hU A
  use C, e
  intro B
  let S (a : ℕ) := {Q : Measure CantorSeq | Q ∈ A.carrier ∧ classComplexity U hU A Q = a ∧
    ∃ x : BitString, IsClassWinner U hU A Q x}
  have H_eq : {Q : Measure CantorSeq | Q ∈ A.carrier ∧ classComplexity U hU A Q ≤ B ∧
    ∃ x, IsClassWinner U hU A Q x} = ⋃ (a : ℕ) (_ : a ∈ Finset.range (B + 1)), S a := by
    ext Q
    simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      use classComplexity U hU A Q
      constructor
      · omega
      · exact ⟨h1, rfl, h3⟩
    · rintro ⟨a, ha, h1, rfl, h3⟩
      constructor
      · exact h1
      · constructor
        · omega
        · exact h3
  rw [H_eq]
  have H_fin : (⋃ (a : ℕ) (ha : a ∈ Finset.range (B + 1)), S a).Finite := by
    apply Set.Finite.biUnion
    · exact (Finset.finite_toSet (Finset.range (B + 1)))
    · intro a _
      exact (h a).1
  constructor
  · exact H_fin
  · have H_ncard_le : Set.ncard (⋃ (a : ℕ) (ha : a ∈ Finset.range (B + 1)), S a) ≤
      ∑ a ∈ Finset.range (B + 1), Set.ncard (S a) := by
      exact Finset.set_ncard_biUnion_le (Finset.range (B + 1)) S
    have H_sum : ∑ a ∈ Finset.range (B + 1), Set.ncard (S a) ≤
      ∑ a ∈ Finset.range (B + 1), C * (B + 2) ^ e := by
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (h a).2
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have : a ≤ B := by
        rw [Finset.mem_range] at ha
        omega
      omega
    apply le_trans H_ncard_le
    apply le_trans H_sum
    have H_eq2 : ∑ a ∈ Finset.range (B + 1), C * (B + 2) ^ e = (B + 1) * (C * (B + 2) ^ e) := by
      simp
    rw [H_eq2]
    have H_pow : (B + 2) ^ (e + 1) = (B + 2) * (B + 2) ^ e := by
      exact pow_succ' (B + 2) e
    rw [H_pow]
    calc
      (B + 1) * (C * (B + 2) ^ e) = (B + 1) * C * (B + 2) ^ e := by ring
      _ ≤ (B + 2) * C * (B + 2) ^ e := by gcongr; omega
      _ = C * ((B + 2) * (B + 2) ^ e) := by ring

/-- A single selected class winner contributes at most linear squared path error.
Blueprint node `enum:class-charge`. -/
theorem enum_class_charge (U : Map) (hU : IsOptimalPrefixConditional U)
    (A : EffectiveMixtureClass U hU) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure CantorSeq) (w : CantorSeq) (D : ℕ)
        (Q : Measure CantorSeq) (choose : BitString → Measure CantorSeq),
        P ∈ A.carrier → PathBudget P w D →
          IsClassChoice U hU A choose →
          Summable (fun n : {n : ℕ // choose (cantorPrefix w n) = Q} =>
            (condProb (cantorMass Q) (cantorPrefix w n.1) false -
              condProb (cantorMass P) (cantorPrefix w n.1) false) ^ 2) ∧
          (∑' n : {n : ℕ // choose (cantorPrefix w n) = Q},
            (condProb (cantorMass Q) (cantorPrefix w n.1) false -
              condProb (cantorMass P) (cantorPrefix w n.1) false) ^ 2) ≤
                C * (classComplexity U hU A P + D + 1) := by
  obtain ⟨cU, cA, -, -, hwin⟩ := class_winner_bounds U hU A
  obtain ⟨_, cB, -, hbridge⟩ := measureComplexity_le_classComplexity U hU A
  obtain ⟨C0, hC0, hpair⟩ := pairwise_prefix_sq_bound U hU
  use C0 * (7 + cU + cA + 2 * cB) + 1
  have hC : 0 < C0 * (7 + (cU : ℝ) + (cA : ℝ) + 2 * (cB : ℝ)) + 1 := by
    positivity
  refine ⟨hC, fun P w D Q choose hP hbudget hchoose => ?_⟩
  let f := fun (n : ℕ) => (condProb (cantorMass Q) (cantorPrefix w n) false - condProb
    (cantorMass P) (cantorPrefix w n) false) ^ 2
  have step1 : ∀ F : Finset ℕ, (∀ n ∈ F, choose (cantorPrefix w n) = Q) →
      ∑ i ∈ F, f i ≤ (C0 * (7 + cU + cA + 2 * cB) + 1) * (classComplexity U hU A P + D + 1) := by
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.sum_empty]
      apply mul_nonneg
      · linarith
      · positivity
    let N := F.max' hne
    have hQN : choose (cantorPrefix w N) = Q := hF N (Finset.max'_mem F hne)
    have hPpos := base_budget_positive P w D N hbudget
    have hwinN : IsClassWinner U hU A Q (cantorPrefix w N) := by
      have h := hchoose (cantorPrefix w N) ⟨P, hP, hPpos⟩
      rwa [hQN] at h
    have hQ_in := hwinN.1
    have hQpos := hwinN.2.1
    obtain ⟨iP, hiP⟩ := id hP
    have hP_prob : IsProbabilityMeasure P := by rw [← hiP]; exact (A.A iP).probability
    have hPcomp : IsComputableMeasure P := by rw [← hiP]; exact (A.A iP).computable
    obtain ⟨iQ, hiQ⟩ := id hQ_in
    have hQ_prob : IsProbabilityMeasure Q := by rw [← hiQ]; exact (A.A iQ).probability
    have hQcomp : IsComputableMeasure Q := by rw [← hiQ]; exact (A.A iQ).computable
    obtain ⟨hMQ, hkQ⟩ := hwin P Q w D (cantorPrefix w N) hP ⟨N, rfl⟩ hbudget hwinN
    have hMP : universalContinuousSemimeasure (cantorPrefix w N) ≤
        (2 : ℝ≥0∞) ^ (3 * classComplexity U hU A P + D) * cantorMass P (cantorPrefix w N) := by
      have h1 := hbudget N
      apply le_trans h1
      have hz : D ≤ 3 * classComplexity U hU A P + D := by omega
      gcongr
      norm_num
    have hpairN := hpair P Q hPcomp hQcomp (cantorPrefix w N) hPpos hQpos
        (3 * classComplexity U hU A P + D) hMP hMQ
    have h_range : ∑ i ∈ Finset.range N, f i = pairwiseError P Q (cantorPrefix w N) := by
      unfold pairwiseError
      have hlen : (cantorPrefix w N).length = N := cantorPrefix_length w N
      rw [Fin.sum_univ_eq_sum_range (fun i => (condProb (cantorMass P) ((cantorPrefix w N).take
        i) false - condProb (cantorMass Q) ((cantorPrefix w N).take i) false) ^ 2)
          (cantorPrefix w N).length]
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      have h_le : (i : ℕ) ≤ N := (Finset.mem_range.mp hi).le
      rw [cantorPrefix_take w i N h_le]
      ring
    have hf_N : f N ≤ 1 := by
      have hp : 0 ≤ condProb (cantorMass P) (cantorPrefix w N) false := condProb_nonneg
        (cantorMass P) (cantorPrefix w N) false
      have hq : 0 ≤ condProb (cantorMass Q) (cantorPrefix w N) false := condProb_nonneg
        (cantorMass Q) (cantorPrefix w N) false
      have hp1 : condProb (cantorMass P) (cantorPrefix w N) false ≤ 1 := by
        by_cases h0 : cantorMass P (cantorPrefix w N) = 0
        · simp [condProb, h0]
        · have h_add := condProb_cantorMass_add_eq_one P h0
          have hp_true := condProb_nonneg (cantorMass P) (cantorPrefix w N) true
          linarith
      have hq1 : condProb (cantorMass Q) (cantorPrefix w N) false ≤ 1 := by
        by_cases h0 : cantorMass Q (cantorPrefix w N) = 0
        · simp [condProb, h0]
        · have h_add := condProb_cantorMass_add_eq_one Q h0
          have hq_true := condProb_nonneg (cantorMass Q) (cantorPrefix w N) true
          linarith
      dsimp [f]
      nlinarith
    have h_sumF : ∑ i ∈ F, f i ≤ pairwiseError P Q (cantorPrefix w N) + 1 := by
      have h_sub : F ⊆ Finset.range (N + 1) := by
        intro x hx
        rw [Finset.mem_range]
        have h_le := Finset.le_max' F x hx
        linarith
      have h_nonneg : ∀ i, 0 ≤ f i := by intro i; exact sq_nonneg _
      have h_le1 := Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun i _ _ => h_nonneg i)
      rw [Finset.sum_range_succ] at h_le1
      rw [h_range] at h_le1
      apply le_trans h_le1
      gcongr
    have hkP_bound := (hbridge P hP).1
    have hkQ_bound := (hbridge Q hQ_in).1
    have hkP_R : (computableMeasureComplexity U P).toNat ≤ (classComplexity U hU A P : ℝ) + cB
      := by exact_mod_cast hkP_bound
    have hkQ_R : (computableMeasureComplexity U Q).toNat ≤ (classComplexity U hU A Q : ℝ) + cB
      := by exact_mod_cast hkQ_bound
    have hkQ2_R : 2 * (classComplexity U hU A Q : ℝ) ≤ 3 * (classComplexity U hU A P : ℝ) + D +
      cU + cA := by exact_mod_cast hkQ
    have H : (computableMeasureComplexity U P).toNat + (computableMeasureComplexity U Q).toNat
      + (3 * (classComplexity U hU A P : ℝ) + D) + 1 ≤
        (7 + cU + cA + 2 * cB) * (classComplexity U hU A P + D + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (classComplexity U hU A P),
        Nat.cast_nonneg (α := ℝ) D, Nat.cast_nonneg (α := ℝ) cU,
        Nat.cast_nonneg (α := ℝ) cA, Nat.cast_nonneg (α := ℝ) cB]
    have h_final : pairwiseError P Q (cantorPrefix w N) + 1 ≤ (C0 * (7 + cU + cA + 2 * cB) + 1)
      * (classComplexity U hU A P + D + 1) := by
      have hr1 : pairwiseError P Q (cantorPrefix w N) ≤ C0 * ((computableMeasureComplexity U
        P).toNat + (computableMeasureComplexity U Q).toNat + (3 * classComplexity U hU A P + D)
          + 1) := by exact_mod_cast hpairN
      have hr2 : C0 * ((computableMeasureComplexity U P).toNat + (computableMeasureComplexity U
        Q).toNat + (3 * classComplexity U hU A P + D) + 1) ≤ C0 * ((7 + cU + cA + 2 * cB) *
          (classComplexity U hU A P + D + 1)) := mul_le_mul_of_nonneg_left H hC0.le
      have hr3 : (C0 * (7 + cU + cA + 2 * cB) + 1) * (classComplexity U hU A P + D + 1) = C0 *
        ((7 + cU + cA + 2 * cB) * (classComplexity U hU A P + D + 1)) + (classComplexity U hU A
          P + D + 1) := by ring
      have hr4 : 1 ≤ (classComplexity U hU A P + D + 1 : ℝ) := by
        have h_k : 0 ≤ (classComplexity U hU A P : ℝ) := Nat.cast_nonneg _
        have h_d : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    linarith
  let S := {n : ℕ | choose (cantorPrefix w n) = Q}
  let B := (C0 * (7 + cU + cA + 2 * cB) + 1) * (classComplexity U hU A P + D + 1)
  have hB : 0 ≤ B := by apply mul_nonneg hC.le; positivity
  have hF : ∀ F : Finset S, ∑ i ∈ F, f i.val ≤ B := by
    intro F
    let F' : Finset ℕ := Finset.map (Function.Embedding.subtype (fun n => n ∈ S)) F
    have h1 : ∀ n ∈ F', choose (cantorPrefix w n) = Q := by
      intro n hn
      rw [Finset.mem_map] at hn
      rcases hn with ⟨a, ha, ha_eq⟩
      rw [← ha_eq]
      exact a.property
    have h2 := step1 F' h1
    have h3 : ∑ i ∈ F, f i.val = ∑ i ∈ F', f i := by rw [Finset.sum_map]; rfl
    rw [h3]
    exact h2
  have hf : ∀ n : S, 0 ≤ f n.val := by intro n; exact sq_nonneg _
  have h_sum : Summable (fun n : S => f n.val) := summable_of_sum_le hf hF
  refine ⟨h_sum, ?_⟩
  apply tsum_le_of_sum_le' hB hF
end Kolmogorov.MDLPrediction
