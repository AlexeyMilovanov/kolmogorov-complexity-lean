/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Random.Vovk
import KolmogorovMathlib.MDLPrediction.Random.BadCandidate

/-!
# Global MDL predictor merging on a random path

The choice function may switch arbitrarily among tied minimizers. Eventual exclusion
leaves a finite family of candidates random on the path, each covered by Vovk merging.

Blueprint nodes: `rand:theorem4`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory

/-- Uniformly combine convergence over a finite family of random winners. -/
private lemma tendsto_predictor_of_finite_winners (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (hPc : IsComputableMeasure P) (w : CantorSeq)
    (hP : IsMartinLofRandom P w)
    (choose : BitString → Measure CantorSeq)
    (F : Set (Measure CantorSeq)) (hF_fin : F.Finite)
    (hF_models : ∀ Q ∈ F, IsProbabilityMeasure Q ∧ IsComputableMeasure Q)
    (hchoose_F : ∀ n, choose (cantorPrefix w n) ∈ F)
    (N : ℕ) (hN : ∀ Q ∈ F, ¬IsMartinLofRandom Q w → ∀ n ≥ N, choose (cantorPrefix w n) ≠ Q) :
    Filter.Tendsto (fun n =>
      predictor U hU choose (cantorPrefix w n) false -
        condProb (cantorMass P) (cantorPrefix w n) false)
      Filter.atTop (nhds 0) := by
  let F_rand : Set (Measure CantorSeq) := {Q ∈ F | IsMartinLofRandom Q w}
  have hF_rand_fin : F_rand.Finite := Set.Finite.subset hF_fin (fun Q hQ => hQ.1)
  have H1 : ∀ Q ∈ F_rand, Filter.Tendsto (fun n => condProb (cantorMass Q) (cantorPrefix
      w n) false - condProb (cantorMass P) (cantorPrefix w n) false) Filter.atTop (nhds 0) := by
    intro Q hQ
    have hQ_in_F : Q ∈ F := hQ.1
    have hQ_rand : IsMartinLofRandom Q w := hQ.2
    have _inst_Q : IsProbabilityMeasure Q := (hF_models Q hQ_in_F).1
    have H_vovk := vovk_merging U hU Q P (hF_models Q hQ_in_F).2 hPc w hQ_rand hP
    exact H_vovk
  
  have H2 : ∀ (ε : ℝ), 0 < ε → ∃ N', ∀ n ≥ N',
    |predictor U hU choose (cantorPrefix w n) false - condProb (cantorMass P)
        (cantorPrefix w n) false| < ε := by
    intro ε hε
    have H_eventually : ∀ Q ∈ F_rand, ∃ N_Q, ∀ n ≥ N_Q,
      |condProb (cantorMass Q) (cantorPrefix w n) false - condProb (cantorMass P)
          (cantorPrefix w n) false| < ε := by
      intro Q hQ
      have H_tendsto := H1 Q hQ
      rw [Metric.tendsto_atTop] at H_tendsto
      have H_tendsto_eps := H_tendsto ε hε
      rcases H_tendsto_eps with ⟨N_Q, hN_Q⟩
      use N_Q
      intro n hn
      have hn_dist := hN_Q n hn
      rw [Real.dist_eq, sub_zero] at hn_dist
      exact hn_dist
    
    have _inst_dec : DecidablePred (fun Q => Q ∈ F_rand) := fun Q => Classical.dec (Q ∈ F_rand)
    let f_N_Q : Measure CantorSeq → ℕ := fun Q => if h : Q ∈ F_rand then
        Classical.choose (H_eventually Q h) else 0
    let max_N_Q : ℕ := Finset.sup hF_rand_fin.toFinset f_N_Q
    
    use max N max_N_Q
    intro n hn
    have hn_N : n ≥ N := le_trans (le_max_left N max_N_Q) hn
    have hn_max : n ≥ max_N_Q := le_trans (le_max_right N max_N_Q) hn
    
    let Q_n := choose (cantorPrefix w n)
    have hQ_n_F : Q_n ∈ F := hchoose_F n
    have hQ_n_rand : IsMartinLofRandom Q_n w := by
      by_contra h_not_rand
      have hN_Q_n := hN Q_n hQ_n_F h_not_rand n hn_N
      exact hN_Q_n rfl
      
    have hQ_n_F_rand : Q_n ∈ F_rand := ⟨hQ_n_F, hQ_n_rand⟩
    have h_N_Q_n := Classical.choose_spec (H_eventually Q_n hQ_n_F_rand)
    
    have h_f_Q_n : f_N_Q Q_n = Classical.choose (H_eventually Q_n hQ_n_F_rand) := by
      dsimp [f_N_Q]
      rw [dite_eq_left hQ_n_F_rand]
      
    have hn_Q_n : n ≥ Classical.choose (H_eventually Q_n hQ_n_F_rand) := by
      rw [← h_f_Q_n]
      have h_in_finset : Q_n ∈ hF_rand_fin.toFinset := (Set.Finite.mem_toFinset
          hF_rand_fin).mpr hQ_n_F_rand
      have h_le_sup := @Finset.le_sup ℕ (Measure CantorSeq) _ _ hF_rand_fin.toFinset
          f_N_Q Q_n h_in_finset
      exact le_trans h_le_sup hn_max
      
    have h_eps := h_N_Q_n n hn_Q_n
    unfold predictor
    exact h_eps
  
  rw [Metric.tendsto_atTop]
  intro ε hε
  have ⟨N', hN'⟩ := H2 ε hε
  use N'
  intro n hn
  rw [Real.dist_eq, sub_zero]
  exact hN' n hn


/-- Every global minimizer choice merges with a computable proper source on each
source-random path, for bit zero. Blueprint node `rand:theorem4`. -/
theorem predictor_merges_on_random (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (hPc : IsComputableMeasure P) (w : CantorSeq)
    (hP : IsMartinLofRandom P w)
    (choose : BitString → Measure CantorSeq)
    (hchoose : IsGlobalChoice U hU choose) :
    Filter.Tendsto (fun n =>
      predictor U hU choose (cantorPrefix w n) false -
        condProb (cantorMass P) (cantorPrefix w n) false)
      Filter.atTop (nhds 0) := by
  have ⟨F, hF_fin, hF_models, hchoose_F, N, hN⟩ := eventually_no_bad_winner U hU P hPc w
      hP choose hchoose
  exact tendsto_predictor_of_finite_winners U hU P hPc w hP choose F hF_fin hF_models hchoose_F N hN

/-- The global minimizer predictor also merges for bit one.
Blueprint node `rand:theorem4`. -/
theorem predictor_merges_on_random_true (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (hPc : IsComputableMeasure P) (w : CantorSeq)
    (hP : IsMartinLofRandom P w)
    (choose : BitString → Measure CantorSeq)
    (hchoose : IsGlobalChoice U hU choose) :
    Filter.Tendsto (fun n =>
      predictor U hU choose (cantorPrefix w n) true -
        condProb (cantorMass P) (cantorPrefix w n) true)
      Filter.atTop (nhds 0) := by
  have h0 := predictor_merges_on_random U hU P hPc w hP choose hchoose
  have h1 : ∀ n, predictor U hU choose (cantorPrefix w n) true =
            1 - predictor U hU choose (cantorPrefix w n) false := by
    intro n
    have h_add := predictor_add_eq_one U hU choose hchoose (cantorPrefix w n)
    linarith
  have h2 : ∀ n, condProb (cantorMass P) (cantorPrefix w n) true =
            1 - condProb (cantorMass P) (cantorPrefix w n) false := by
    intro n
    have h_mass_pos := random_prefix_mass_pos U hU P hPc w hP n
    have h_mass_ne_zero : cantorMass P (cantorPrefix w n) ≠ 0 := ne_of_gt h_mass_pos
    have h_add := condProb_cantorMass_add_eq_one P h_mass_ne_zero
    linarith
  have h3 : (fun n => predictor U hU choose (cantorPrefix w n) true -
            condProb (cantorMass P) (cantorPrefix w n) true) =
            (fun n => -(predictor U hU choose (cantorPrefix w n) false -
            condProb (cantorMass P) (cantorPrefix w n) false)) := by
    ext n
    rw [h1 n, h2 n]
    ring
  rw [h3]
  have h4 : nhds (0 : ℝ) = nhds (-0 : ℝ) := by rw [neg_zero]
  rw [h4]
  exact Filter.Tendsto.neg h0

end Kolmogorov.MDLPrediction
