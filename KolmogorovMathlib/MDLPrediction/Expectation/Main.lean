/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Expectation.Tonelli
import KolmogorovMathlib.MDLPrediction.Expectation.Layers
import KolmogorovMathlib.MDLPrediction.Path.Main
import KolmogorovMathlib.MDLPrediction.Analysis.Series

/-!
# Expected squared error for the global MDL predictor

The natural budget is finite almost surely. Integrating the pathwise bound
over its least-budget layers yields the exponential measure-complexity bound.
The real tree series is explicitly summable before its `tsum` is compared.

Blueprint node: `exp:theorem3`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped BigOperators
open scoped ENNReal

/-! ## Tonelli and measurable budget layers -/

/-- The Tonelli identity for the bit-zero predictor: the path lintegral of the
squared errors equals the weighted tree sum. -/
private lemma lintegral_sq_error_eq_tsum
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (choose : BitString → Measure CantorSeq) :
    (∫⁻ w, ∑' n : ℕ, ENNReal.ofReal
      ((predictor U hU choose (cantorPrefix w n) false -
        condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ∂P) =
    ∑' x : BitString, cantorMass P x * ENNReal.ofReal
      ((predictor U hU choose x false - condProb (cantorMass P) x false) ^ 2) := by
  have H := integral_path_error_eq_tsum P (fun x => predictor U hU choose x false)
  exact H.1

/-- A path budget is a countable intersection of prefix conditions, hence measurable. -/
private theorem measurableSet_pathBudget (P : Measure CantorSeq) (D : ℕ) :
    MeasurableSet {w | PathBudget P w D} := by
  have hset : {w | PathBudget P w D} = ⋂ n, {w | universalContinuousSemimeasure
      (cantorPrefix w n) ≤ (2 : ℝ≥0∞) ^ D * cantorMass P (cantorPrefix w n)} := by
    ext w
    simp [PathBudget]
  rw [hset]
  exact MeasurableSet.iInter fun n =>
    measurableSet_le (measurable_comp_cantorPrefix n _)
      (measurable_comp_cantorPrefix n (fun x => (2 : ℝ≥0∞) ^ D * cantorMass P x))

/-- The least-budget layer `d` is "budget `d` holds and no smaller budget holds". -/
private theorem leastBudget_layer_eq (P : Measure CantorSeq) (d : ℕ) :
    {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d} =
      {w | PathBudget P w d} ∩ ⋂ j ∈ Finset.range d, {w | PathBudget P w j}ᶜ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range,
    Set.mem_ofPred_eq]
  unfold leastBudget
  classical
  constructor
  · rintro ⟨h1, h2⟩
    split_ifs at h2
    rw [Nat.find_eq_iff] at h2
    exact ⟨h2.1, fun j hj => h2.2 j hj⟩
  · rintro ⟨h1, h2⟩
    have h : ∃ D, PathBudget P w D := ⟨d, h1⟩
    refine ⟨h, ?_⟩
    split_ifs
    rw [Nat.find_eq_iff]
    exact ⟨h1, fun j hj => h2 j hj⟩

/-! ## Integrating the pathwise bound -/

/-- Integration of Theorem 7 over the least-budget layers: the path lintegral of
the squared errors is bounded by `C (k + 1) 2^(3k/2)` in `ℝ≥0∞`. -/
private lemma lintegral_sq_error_le (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C_const : ℝ, 0 < C_const ∧
    ∀ (P : Measure CantorSeq) [IsProbabilityMeasure P] (_ : IsComputableMeasure P)
      (choose : BitString → Measure CantorSeq) (_ : IsGlobalChoice U hU choose),
    (∫⁻ w, ∑' n : ℕ, ENNReal.ofReal ((predictor U hU choose (cantorPrefix w n) false -
      condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ∂P) ≤
      ENNReal.ofReal (C_const * ((computableMeasureComplexity U P).toNat + 1) *
        (2 : ℝ) ^ (((3 * (computableMeasureComplexity U P).toNat : ℕ) : ℝ) / (2 : ℝ))) := by
  obtain ⟨c, C, hC, h7⟩ := pathwise_sq_bound U hU
  obtain ⟨Cg, hCg, hgeo⟩ := exp_geometric
  refine ⟨2 * C * (2 : ℝ) ^ ((c : ℝ) / 2) * Cg, by positivity, ?_⟩
  intro P _ hPc choose hchoose
  set k := (computableMeasureComplexity U P).toNat with hk
  set sq : BitString → ℝ := fun x =>
    (predictor U hU choose x false - condProb (cantorMass P) x false) ^ 2 with hsq
  -- Theorem 7 on one path, moved to ENNReal through its summability conjunct
  let B : ℕ → ℝ := fun D =>
    C * ((k : ℝ) + D + 1) * (2 : ℝ) ^ (((3 * k + D + c : ℕ) : ℝ) / 2)
  have hpath : ∀ w D, PathBudget P w D →
      ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ≤ ENNReal.ofReal (B D) := by
    intro w D hw
    obtain ⟨hs, hb⟩ := h7 P hPc w D hw choose hchoose
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hb
  -- least-budget layers
  let L : ℕ → Set CantorSeq := fun d =>
    {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d}
  have hLmeas : ∀ d, MeasurableSet (L d) := fun d => by
    change MeasurableSet {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d}
    rw [leastBudget_layer_eq]
    exact (measurableSet_pathBudget P d).inter
      (Finset.measurableSet_biInter _ fun j _ => (measurableSet_pathBudget P j).compl)
  have hLmem : ∀ w d, w ∈ L d → PathBudget P w d := by
    intro w d hw
    have hw' : w ∈ {w | (∃ D : ℕ, PathBudget P w D) ∧ leastBudget P w = d} := hw
    rw [leastBudget_layer_eq] at hw'
    exact hw'.1
  let c' : ℕ → ℝ≥0∞ := fun d => ENNReal.ofReal (B d)
  have hae : ∀ᵐ w ∂P, ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ≤
      ∑' d, (L d).indicator (fun _ => c' d) w := by
    filter_upwards [ae_exists_budget P] with w hw
    have hmem : w ∈ L (leastBudget P w) := ⟨hw, rfl⟩
    calc ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ≤ c' (leastBudget P w) :=
          hpath w _ (hLmem w _ hmem)
      _ = (L (leastBudget P w)).indicator (fun _ => c' (leastBudget P w)) w :=
          (Set.indicator_of_mem hmem (fun _ => c' (leastBudget P w))).symm
      _ ≤ ∑' d, (L d).indicator (fun _ => c' d) w :=
          ENNReal.le_tsum (f := fun d => (L d).indicator (fun _ => c' d) w) _
  have hPL : ∀ d, P (L d) ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ d := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [pow_zero, mul_one]
      exact prob_le_one.trans (by norm_num)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
      calc P (L (1 + m)) ≤ (2 : ℝ≥0∞)⁻¹ ^ (1 + m - 1) := exp_budget_layers P _ hd
        _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ (1 + m) := by
          rw [Nat.add_sub_cancel_left, pow_add, pow_one, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hint : (∫⁻ w, ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ∂P) ≤
      ∑' d, c' d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) := by
    calc (∫⁻ w, ∑' n, ENNReal.ofReal (sq (cantorPrefix w n)) ∂P)
        ≤ ∫⁻ w, ∑' d, (L d).indicator (fun _ => c' d) w ∂P := lintegral_mono_ae hae
      _ = ∑' d, ∫⁻ w, (L d).indicator (fun _ => c' d) w ∂P :=
          lintegral_tsum fun d => (measurable_const.indicator (hLmeas d)).aemeasurable
      _ = ∑' d, c' d * P (L d) := by
          congr 1
          ext d
          exact lintegral_indicator_const (hLmeas d) _
      _ ≤ ∑' d, c' d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) := ENNReal.tsum_le_tsum fun d => by
          gcongr
          exact hPL d
  -- the layer series, in real numbers
  set K : ℝ := 2 * C * (2 : ℝ) ^ ((c : ℝ) / 2) * (2 : ℝ) ^ (((3 * k : ℕ) : ℝ) / 2) with hK
  have hterm : ∀ d, c' d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) =
      ENNReal.ofReal (K * (((k + d + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(d : ℝ) / 2))) := by
    intro d
    have h2 : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ d = ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ d) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    have hB : 0 ≤ B d := by positivity
    simp only [c']
    rw [h2, ← ENNReal.ofReal_mul hB]
    congr 1
    have ht : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ ((d : ℝ) / 2) = (2 : ℝ) ^ d := by
      rw [← Real.rpow_add (by norm_num), add_halves, Real.rpow_natCast]
    have hsplit : (2 : ℝ) ^ (((3 * k + d + c : ℕ) : ℝ) / 2) =
        (2 : ℝ) ^ (((3 * k : ℕ) : ℝ) / 2) * (2 : ℝ) ^ ((d : ℝ) / 2) *
          (2 : ℝ) ^ ((c : ℝ) / 2) := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have hneg : (2 : ℝ) ^ (-(d : ℝ) / 2) = ((2 : ℝ) ^ ((d : ℝ) / 2))⁻¹ := by
      rw [neg_div, Real.rpow_neg (by norm_num)]
    have htpos : 0 < (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
    simp only [B, hK]
    rw [hsplit, hneg, inv_pow, ← ht]
    push_cast
    field_simp
  have hsum := (hgeo k).1
  have hle := (hgeo k).2
  calc (∫⁻ w, ∑' n : ℕ, ENNReal.ofReal ((predictor U hU choose (cantorPrefix w n) false -
        condProb (cantorMass P) (cantorPrefix w n) false) ^ 2) ∂P)
      ≤ ∑' d, c' d * (2 * (2 : ℝ≥0∞)⁻¹ ^ d) := hint
    _ = ∑' d, ENNReal.ofReal (K * (((k + d + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(d : ℝ) / 2))) :=
        tsum_congr hterm
    _ = ENNReal.ofReal (∑' d, K * (((k + d + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(d : ℝ) / 2))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun d => by positivity) (hsum.mul_left K)).symm
    _ ≤ ENNReal.ofReal (2 * C * (2 : ℝ) ^ ((c : ℝ) / 2) * Cg * ((k : ℝ) + 1) *
          (2 : ℝ) ^ (((3 * k : ℕ) : ℝ) / (2 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [tsum_mul_left]
        calc K * ∑' d, ((k + d + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(d : ℝ) / 2)
            ≤ K * (Cg * (k + 1)) := by
              have hKnn : 0 ≤ K := by positivity
              exact mul_le_mul_of_nonneg_left hle hKnn
          _ = 2 * C * (2 : ℝ) ^ ((c : ℝ) / 2) * Cg * ((k : ℝ) + 1) *
                (2 : ℝ) ^ (((3 * k : ℕ) : ℝ) / (2 : ℝ)) := by
              rw [hK]
              ring

/-! ## Real summability and expected error -/

/-- Transfer of an `ℝ≥0∞` bound on the weighted tree sum to real summability
and a real bound. -/
private lemma summable_weighted_of_tsum_le (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (f : BitString → ℝ) (hf : ∀ x, 0 ≤ f x) (C : ℝ) (hC : 0 ≤ C)
    (h_bound :
      (∑' x : BitString, cantorMass P x * ENNReal.ofReal (f x)) ≤ ENNReal.ofReal C) :
    Summable (fun x : BitString => (cantorMass P x).toReal * f x) ∧
    (∑' x : BitString, (cantorMass P x).toReal * f x) ≤ C := by
  have H : (∑' x : BitString, cantorMass P x * ENNReal.ofReal (f x)) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_bound
  have h_eq (x : BitString) : cantorMass P x * ENNReal.ofReal (f x) =
      ENNReal.ofReal ((cantorMass P x).toReal * f x) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hne : cantorMass P x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
    exact (ENNReal.ofReal_toReal hne).symm
  have H_sum : Summable (fun x : BitString => (cantorMass P x).toReal * f x) := by
    have h1 := ENNReal.summable_toReal H
    have h2 : (fun x => ENNReal.toReal (cantorMass P x * ENNReal.ofReal (f x))) =
        fun x => (cantorMass P x).toReal * f x := by
      ext x
      rw [h_eq x]
      apply ENNReal.toReal_ofReal
      apply mul_nonneg (by positivity) (hf x)
    rw [h2] at h1
    exact h1
  constructor
  · exact H_sum
  · have h_tsum_eq : ENNReal.toReal (∑' x : BitString, cantorMass P x * ENNReal.ofReal (f x)) =
        ∑' x : BitString, (cantorMass P x).toReal * f x := by
      have h1 := ENNReal.tsum_toReal_eq (f := fun x => cantorMass P x * ENNReal.ofReal (f x)) (by
        intro x
        have hne : cantorMass P x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
        have hf_ne : ENNReal.ofReal (f x) ≠ ∞ := ENNReal.ofReal_ne_top
        exact ENNReal.mul_ne_top hne hf_ne
      )
      rw [h1]
      apply tsum_congr
      intro x
      rw [h_eq x]
      apply ENNReal.toReal_ofReal
      apply mul_nonneg (by positivity) (hf x)
    rw [← h_tsum_eq]
    have H2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound
    rw [ENNReal.toReal_ofReal hC] at H2
    exact H2

/-- The weighted squared error of the bit-zero global predictor is summable
and has the stated exponential bound. Blueprint node `exp:theorem3`. -/
theorem expected_sq_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure CantorSeq) [IsProbabilityMeasure P],
      IsComputableMeasure P →
        ∀ (choose : BitString → Measure CantorSeq),
          IsGlobalChoice U hU choose →
            Summable (fun x : BitString =>
              (cantorMass P x).toReal *
                (predictor U hU choose x false - condProb (cantorMass P) x false) ^ 2) ∧
            (∑' x : BitString, (cantorMass P x).toReal *
              (predictor U hU choose x false - condProb (cantorMass P) x false) ^ 2) ≤
                C * ((computableMeasureComplexity U P).toNat + 1) *
                  (2 : ℝ) ^ ((3 * (computableMeasureComplexity U P).toNat : ℕ) /
                    (2 : ℝ)) := by
  rcases lintegral_sq_error_le U hU with ⟨C, hC, h_int⟩
  use C, hC
  intro P _ hPc choose hchoose
  have h1 := h_int P hPc choose hchoose
  have h2 := lintegral_sq_error_eq_tsum U hU P choose
  rw [h2] at h1
  have H_C_pos : 0 ≤ C * (↑(computableMeasureComplexity U P).toNat + 1) *
        (2 : ℝ) ^ (((3 * (computableMeasureComplexity U P).toNat : ℕ) : ℝ) / (2 : ℝ)) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact hC.le
      · positivity
    · positivity
  apply summable_weighted_of_tsum_le P _ _ _ H_C_pos h1
  · intro x
    positivity

/-- The bit-one weighted square sum equals the bit-zero sum.
Blueprint node `exp:theorem3`. -/
theorem expected_sq_bound_true (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (choose : BitString → Measure CantorSeq)
    (hchoose : IsGlobalChoice U hU choose) :
    (∑' x : BitString, (cantorMass P x).toReal *
      (predictor U hU choose x true - condProb (cantorMass P) x true) ^ 2) =
    (∑' x : BitString, (cantorMass P x).toReal *
      (predictor U hU choose x false - condProb (cantorMass P) x false) ^ 2) := by
  have h_pred_sum : ∀ x : BitString, predictor U hU choose x false +
      predictor U hU choose x true = 1 := by
    intro x
    apply predictor_add_eq_one U hU choose hchoose x
  apply tsum_congr
  intro x
  by_cases hx : cantorMass P x = 0
  · have hx_real : (cantorMass P x).toReal = 0 := by rw [hx, ENNReal.toReal_zero]
    rw [hx_real, zero_mul, zero_mul]
  · have hx_ne : cantorMass P x ≠ 0 := hx
    have h_cond_sum : condProb (cantorMass P) x false + condProb (cantorMass P) x true = 1 := by
      apply condProb_cantorMass_add_eq_one P hx_ne
    have h1 : predictor U hU choose x true = 1 - predictor U hU choose x false := by
      linarith [h_pred_sum x]
    have h2 : condProb (cantorMass P) x true = 1 - condProb (cantorMass P) x false := by
      linarith [h_cond_sum]
    rw [h1, h2]
    congr 1
    ring

end Kolmogorov.MDLPrediction
