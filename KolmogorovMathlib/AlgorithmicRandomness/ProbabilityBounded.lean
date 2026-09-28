import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.DeficiencyCore

/-!
# Probability-bounded randomness tests

`IsProbabilityBoundedRandomnessTest` is a lower-semicomputable `t : CantorSeq → ℝ≥0∞` whose
superlevel set at height `2 ^ n` has measure at most `2 ^ (-n)`.  This module shows that such
tests and Martin-Löf tests describe the same deficiency, in both directions.

From a test to a Martin-Löf test: `isMartinLofTest_superlevel_of_probabilityBounded` takes the
dyadic superlevel sets, and `le_mlTestValue_superlevel` shows nothing worse than a factor four
is lost.

From a Martin-Löf test to a test: `mlTestValue` is the exponential-scale value `2 ^ deficiency`
of a test, shown lower semicomputable (`isLowerSemicomputableFun_mlTestValue`) and with the
right measure bounds (`measure_two_pow_lt_mlTestValue`), so that after the rational rescaling
of `exists_rat_scaling` it becomes a probability-bounded test
(`isProbabilityBoundedRandomnessTest_rat_smul_mlTestValue`).  The dictionary between additive
deficiency bounds and multiplicative bounds on values is
`mlTestValue_le_of_mlDeficiency_le`.
-/

namespace Kolmogorov

open MeasureTheory Topology
open scoped ENNReal NNReal

/-- A probability-bounded randomness test: a lower semicomputable function whose superlevel set
at height `2^n` has measure at most `2^{-n}` for every `n`. -/
def IsProbabilityBoundedRandomnessTest (μ : Measure CantorSeq) (u : CantorSeq → ℝ≥0∞) : Prop :=
  IsLowerSemicomputableFun u ∧ ∀ c : ℚ, 0 < c →
    μ {w | u w > ENNReal.ofReal (c : ℝ)} < (ENNReal.ofReal (c : ℝ))⁻¹

/-- Exponential-scale value of the deficiency represented by a Martin-Löf
test.  The baseline `1` corresponds to deficiency zero. -/
noncomputable def mlTestValue (U : ℕ → Set CantorSeq) (w : CantorSeq) : ℝ≥0∞ :=
  by
    classical
    exact ⨆ n : ℕ, if w ∈ U n then (2 : ℝ≥0∞) ^ n else 1

/-- A computable measure is finite. -/
lemma IsComputableMeasure.measure_univ_ne_top {μ : Measure CantorSeq} (h : IsComputableMeasure μ) :
    μ Set.univ ≠ ⊤ := by
  have h_comp := h.isComputableENNReal_mass []
  rcases h_comp with ⟨approx, hbound, _⟩
  have h_bound := (hbound 0).1
  unfold cantorMass at h_bound
  have h_cyl : cantorCylinder [] = Set.univ := by ext w; simp [cantorCylinder, IsCantorPrefix]
  rw [h_cyl] at h_bound
  have h_fin : dyadicValue (approx 0) 0 + dyadicValue 1 0 < ⊤ := by
    apply ENNReal.add_lt_top.2
    constructor
    · apply lt_top_iff_ne_top.2
      unfold dyadicValue
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top (approx 0))
        (ENNReal.inv_ne_top.2 (by norm_num))
    · apply lt_top_iff_ne_top.2
      unfold dyadicValue
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top 1) (ENNReal.inv_ne_top.2 (by norm_num))
  intro h_top
  rw [h_top] at h_bound
  exact (lt_self_iff_false ⊤).1 (lt_of_le_of_lt h_bound h_fin)

/-- The value function of a Martin-Löf test is at least one everywhere. -/
lemma one_le_mlTestValue (U : ℕ → Set CantorSeq) (w : CantorSeq) :
    1 ≤ mlTestValue U w := by
  unfold mlTestValue
  apply le_iSup_of_le 0
  split_ifs
  · norm_num
  · exact le_rfl

/-- The rational powers of two form a computable sequence. -/
lemma computable_two_pow_rat : Computable (fun n : ℕ => (2 : ℚ) ^ n) := by
  have hnat : Primrec (fun n : ℕ => 2 ^ n) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  refine computable_of_num_den (f := fun n : ℕ => (2 : ℚ) ^ n)
    (N := fun n : ℕ => ((2 ^ n : ℕ) : ℤ)) (D := fun _ : ℕ => 1)
    (ComputableReals.primrec_natCastInt.to_comp.comp hnat.to_comp) (Computable.const 1)
    (fun _ => one_pos) (fun n => by push_cast; ring)

/-- The extended-real image of the rational `2^n` is `2^n`. -/
lemma ofReal_rat_two_pow (n : ℕ) :
    ENNReal.ofReal ((((2 : ℚ) ^ n : ℚ)) : ℝ) = (2 : ℝ≥0∞) ^ n := by
  have hr : ((((2 : ℚ) ^ n : ℚ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hr, ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- Comparing a rational with `2^n` in the extended reals is the same as comparing it there. -/
lemma ofReal_lt_two_pow_iff (q : ℚ) (n : ℕ) :
    ENNReal.ofReal ((q : ℝ)) < (2 : ℝ≥0∞) ^ n ↔ q < 2 ^ n := by
  have hpos : (0 : ℝ) < ((((2 : ℚ) ^ n : ℚ)) : ℝ) := by
    exact_mod_cast pow_pos (by norm_num : (0 : ℚ) < 2) n
  rw [← ofReal_rat_two_pow n, ENNReal.ofReal_lt_ofReal_iff hpos]
  exact_mod_cast Iff.rfl

/-- The value function of a uniformly effectively open family is lower semicomputable. -/
lemma isLowerSemicomputableFun_mlTestValue {U : ℕ → Set CantorSeq}
    (hU : IsUniformlyEffectiveOpen U) : IsLowerSemicomputableFun (mlTestValue U) := by
  classical
  obtain ⟨f, hf, hUspec⟩ := hU
  have hcyl : cantorCylinder ([] : BitString) = Set.univ := by
    ext w; simp [cantorCylinder, IsCantorPrefix]
  refine ⟨fun q i => if q < 1 then some [] else
      (if q < (2 : ℚ) ^ (Nat.unpair i).1 then f (Nat.unpair i).1 (Nat.unpair i).2 else none),
    ?_, ?_⟩
  · have hfstu : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).1) :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hsndu : Computable (fun p : ℚ × ℕ => (Nat.unpair p.2).2) :=
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have hb1 : Computable (fun p : ℚ × ℕ => decide (p.1 < 1)) :=
      (computable_ratLtConst 1).comp Computable.fst
    have hb2 : Computable (fun p : ℚ × ℕ => decide (p.1 < (2 : ℚ) ^ (Nat.unpair p.2).1)) :=
      Computable₂.comp (f := fun a b : ℚ => decide (a < b)) computable₂_ratLt
        Computable.fst (computable_two_pow_rat.comp hfstu)
    have hinner : Computable (fun p : ℚ × ℕ => f (Nat.unpair p.2).1 (Nat.unpair p.2).2) :=
      Computable₂.comp hf hfstu hsndu
    have hc2 := Computable.cond hb2 hinner (Computable.const (none : Option BitString))
    have hc1 := Computable.cond hb1 (Computable.const (some ([] : BitString))) hc2
    refine hc1.of_eq (fun p => ?_)
    by_cases h1 : p.1 < 1
    · simp [h1]
    · by_cases h2 : p.1 < (2 : ℚ) ^ (Nat.unpair p.2).1 <;> simp [h1, h2]
  · intro q
    by_cases hq1 : q < 1
    · have hlt1 : ENNReal.ofReal (q : ℝ) < 1 := by
        rw [ENNReal.ofReal_lt_one]
        exact_mod_cast hq1
      have hL : {w : CantorSeq | (q : ℝ) < 0 ∨
          ENNReal.ofReal (q : ℝ) < mlTestValue U w} = Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Or.inr (lt_of_lt_of_le hlt1 (one_le_mlTestValue U w))
      rw [hL]
      ext w
      simp [hq1, hcyl]
    · have hq1' : (1 : ℚ) ≤ q := not_lt.1 hq1
      have hq0 : ¬ ((q : ℝ) < 0) := by
        have h1q : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1'
        linarith
      have hone_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (q : ℝ) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hq1')
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro (h | h)
        · exact absurd h hq0
        · unfold mlTestValue at h
          obtain ⟨n, hn⟩ := lt_iSup_iff.1 h
          by_cases hw : w ∈ U n
          · rw [if_pos hw] at hn
            have hqn : q < 2 ^ n := (ofReal_lt_two_pow_iff q n).1 hn
            have hwU : w ∈ ⋃ j, (f n j).elim ∅ cantorCylinder := by
              rw [← hUspec n]; exact hw
            obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hwU
            refine ⟨Nat.pair n j, ?_⟩
            simp only [Nat.unpair_pair, if_neg hq1, if_pos hqn]
            exact hj
          · rw [if_neg hw] at hn
            exact absurd (lt_of_le_of_lt hone_le hn) (lt_irrefl 1)
      · rintro ⟨i, hi⟩
        simp only [if_neg hq1] at hi
        by_cases h2 : q < (2 : ℚ) ^ (Nat.unpair i).1
        · rw [if_pos h2] at hi
          have hwU : w ∈ U (Nat.unpair i).1 := by
            rw [hUspec (Nat.unpair i).1]
            exact Set.mem_iUnion.2 ⟨(Nat.unpair i).2, hi⟩
          refine Or.inr ?_
          have hlt : ENNReal.ofReal (q : ℝ) < (2 : ℝ≥0∞) ^ (Nat.unpair i).1 :=
            (ofReal_lt_two_pow_iff q (Nat.unpair i).1).2 h2
          refine lt_of_lt_of_le hlt ?_
          unfold mlTestValue
          refine le_iSup_of_le (Nat.unpair i).1 ?_
          rw [if_pos hwU]
        · rw [if_neg h2] at hi
          exact absurd hi (Set.notMem_empty w)

/-- The set where the test value exceeds `2^n` is the union of the levels of the test beyond
index `n`. -/
lemma setOf_two_pow_lt_mlTestValue (U : ℕ → Set CantorSeq) (n : ℕ) :
    {w | (2 : ℝ≥0∞) ^ n < mlTestValue U w} = ⋃ m, U (n + m + 1) := by
  classical
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    unfold mlTestValue at h
    have h_lt : ∃ (k : ℕ), (2 : ℝ≥0∞) ^ n < if w ∈ U k then (2 : ℝ≥0∞) ^ k else 1 := by
      apply lt_iSup_iff.1 h
    rcases h_lt with ⟨k, hk⟩
    split_ifs at hk with hw
    · have h_pow : n < k := by
        by_contra h_ge
        have h_ge_pow : (2 : ℝ≥0∞) ^ k ≤ (2 : ℝ≥0∞) ^ n := by
          apply pow_le_pow_right₀ (by norm_num) (not_lt.1 h_ge)
        exact (lt_irrefl ((2 : ℝ≥0∞) ^ n) (lt_of_lt_of_le hk h_ge_pow)).elim
      have h_m : k = n + (k - n - 1) + 1 := by omega
      use (k - n - 1)
      rw [← h_m]
      exact hw
    · have h_false : (2 : ℝ≥0∞) ^ n < 1 := hk
      have h_ge : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
        have h_one : (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 0 := by norm_num
        rw [h_one]
        apply pow_le_pow_right₀ (by norm_num) (by omega)
      exact (lt_irrefl 1 (lt_of_le_of_lt h_ge h_false)).elim
  · rintro ⟨m, hm⟩
    unfold mlTestValue
    have h_le : (2 : ℝ≥0∞) ^ (n + m + 1) ≤ ⨆ k, if w ∈ U k then (2 : ℝ≥0∞) ^ k else 1 := by
      apply le_iSup_of_le (n + m + 1)
      rw [if_pos hm]
    have h_lt : (2 : ℝ≥0∞) ^ n < (2 : ℝ≥0∞) ^ (n + m + 1) := by
      have h_coe1 : (2 : ℝ≥0∞) ^ n = ((2 ^ n : ℕ) : ℝ≥0∞) := by norm_num
      have h_coe2 : (2 : ℝ≥0∞) ^ (n + m + 1) = ((2 ^ (n + m + 1) : ℕ) : ℝ≥0∞) := by norm_num
      rw [h_coe1, h_coe2]
      have h_lt_nat : 2 ^ n < 2 ^ (n + m + 1) := by
        apply pow_lt_pow_right₀ (by norm_num) (by omega)
      exact_mod_cast h_lt_nat
    exact lt_of_lt_of_le h_lt h_le

/-- For a Martin-Löf test the set where its value exceeds `2^n` has measure at most `2^{-n}`. -/
lemma measure_two_pow_lt_mlTestValue {μ : Measure CantorSeq} {U : ℕ → Set CantorSeq}
    (hU : IsMartinLofTest μ U) (n : ℕ) :
    μ {w | (2 : ℝ≥0∞) ^ n < mlTestValue U w} ≤ dyadicValue 1 n := by
  rw [setOf_two_pow_lt_mlTestValue]
  set W : ℕ → Set CantorSeq := fun p => U (Nat.unpair p).2
  have h_eq : (⋃ m, U (n + m + 1)) = (⋃ m, W (Nat.pair m (n + m + 1))) := by
    ext w
    simp only [W, Set.mem_iUnion, Nat.unpair_pair]
  rw [h_eq]
  apply measure_shifted_iUnion_le
  intro k m
  have hW : W (Nat.pair k m) = U m := by
    simp only [W, Nat.unpair_pair]
  rw [hW]
  exact hU.2 m

/-- The sequence of dyadic thresholds `2 ^ (n + 1)` is computable as a rational function. -/
lemma computable_two_pow_succ_rat : Computable (fun n : ℕ => (2 : ℚ) ^ (n + 1)) := by
  have hnat : Primrec (fun n : ℕ => 2 ^ (n + 1)) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ
  refine computable_of_num_den (f := fun n : ℕ => (2 : ℚ) ^ (n + 1))
    (N := fun n : ℕ => ((2 ^ (n + 1) : ℕ) : ℤ)) (D := fun _ : ℕ => 1)
    (ComputableReals.primrec_natCastInt.to_comp.comp hnat.to_comp) (Computable.const 1)
    (fun _ => one_pos) (fun n => by push_cast; ring)

/-- The dyadic superlevel sets of a probability-bounded test form a Martin-Löf test. -/
lemma isMartinLofTest_superlevel_of_probabilityBounded {μ : Measure CantorSeq}
    {v : CantorSeq → ℝ≥0∞} (hv : IsProbabilityBoundedRandomnessTest μ v) :
    IsMartinLofTest μ (fun n => {w | ENNReal.ofReal (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) < v w}) := by
  obtain ⟨hlsc, hbound⟩ := hv
  have hcast : ∀ n : ℕ, ENNReal.ofReal (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) = (2 : ℝ≥0∞) ^ (n + 1) := by
    intro n
    have hr : (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) = (2 : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hr, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  refine ⟨hlsc.isUniformlyEffectiveOpen_superlevel (fun n => (2 : ℚ) ^ (n + 1))
    computable_two_pow_succ_rat (fun n => by positivity), fun n => ?_⟩
  have h := hbound ((2 : ℚ) ^ (n + 1)) (by positivity)
  refine le_trans h.le ?_
  rw [hcast n]
  simp only [dyadicValue, Nat.cast_one, one_div]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))

/-- Every natural number is at most `2^k` for `k` itself. -/
lemma k_le_two_pow_k (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : k + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
    have h2 : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
      have h3 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
        rw [pow_succ, mul_two]
      rw [h3]
      apply Nat.add_le_add_left
      have h4 : 1 ≤ 2 ^ k := by
        have h5 : 2 ^ 0 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le k)
        exact h5
      exact h4
    exact le_trans h1 h2

/-- Every finite extended nonnegative real is bounded by some power of two. -/
lemma exists_nat_pow_ge {x : ℝ≥0∞} (hx : x ≠ ⊤) : ∃ k : ℕ, x ≤ (2 : ℝ≥0∞) ^ k := by
  have ⟨M, hM⟩ := ENNReal.exists_nat_gt hx
  use M
  have hM_pow : (M : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ M := by
    have h1 : M ≤ 2 ^ M := k_le_two_pow_k M
    have h1_coe : (M : ℝ≥0∞) = ((M : ℕ) : ℝ≥0∞) := rfl
    have h2_coe : (2 : ℝ≥0∞) ^ M = ((2 ^ M : ℕ) : ℝ≥0∞) := by norm_num
    rw [h1_coe, h2_coe]
    exact Nat.cast_le.2 h1
  exact le_trans (le_of_lt hM) hM_pow

/-- A function is bounded by four times the value function of the Martin-Löf test formed by its
dyadic superlevel sets. -/
lemma le_mlTestValue_superlevel (v : CantorSeq → ℝ≥0∞) (w : CantorSeq) :
    v w ≤ 4 * mlTestValue
      (fun n => {w' | ENNReal.ofReal (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) < v w'}) w := by
  set U := (fun n => {w' | ENNReal.ofReal (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) < v w'})
  by_cases h_inf : v w = ⊤
  case pos =>
    have h_top : mlTestValue U w = ⊤ := by
      apply eq_top_iff.2
      by_contra h_not_top
      have ⟨M, hM_lt⟩ := ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 (not_le.1 h_not_top))
      have h_bound : (2 : ℝ≥0∞) ^ M ≤ mlTestValue U w := by
        unfold mlTestValue
        apply le_iSup_of_le M
        have h_mem : w ∈ U M := by
          simp only [U, Set.mem_setOf_eq, h_inf]
          exact ENNReal.coe_lt_top
        rw [if_pos h_mem]
      have hM_pow : (M : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ M := by
        have h1 : M ≤ 2 ^ M := k_le_two_pow_k M
        have h1_coe : (M : ℝ≥0∞) = ((M : ℕ) : ℝ≥0∞) := rfl
        have h2_coe : (2 : ℝ≥0∞) ^ M = ((2 ^ M : ℕ) : ℝ≥0∞) := by norm_num
        rw [h1_coe, h2_coe]
        exact Nat.cast_le.2 h1
      have h_contra := lt_of_le_of_lt (le_trans hM_pow h_bound) hM_lt
      exact (lt_self_iff_false _).1 h_contra
    rw [h_top]
    have h_four : (4 : ℝ≥0∞) * ⊤ = ⊤ := by
      apply ENNReal.mul_top
      norm_num
    rw [h_inf, h_four]
  case neg =>
    by_cases h_le4 : v w ≤ 4
    case pos =>
      have h_sup : (1 : ℝ≥0∞) ≤ mlTestValue U w := one_le_mlTestValue U w
      have h_mul : (4 : ℝ≥0∞) * 1 ≤ 4 * mlTestValue U w := mul_le_mul' le_rfl h_sup
      have h_mul_rw : (4 : ℝ≥0∞) * 1 = 4 := mul_one 4
      rw [h_mul_rw] at h_mul
      exact le_trans h_le4 h_mul
    case neg =>
      push_neg at h_le4
      have ⟨k, hk⟩ : ∃ k, v w ≤ (2 : ℝ≥0∞) ^ k := exists_nat_pow_ge h_inf
      let S := {k : ℕ | v w ≤ (2 : ℝ≥0∞) ^ k}
      have h_nonempty : S.Nonempty := ⟨k, hk⟩
      let min_k := Nat.find h_nonempty
      have h_min_k : v w ≤ (2 : ℝ≥0∞) ^ min_k := Nat.find_spec h_nonempty
      have h_min_k_gt_2 : 2 < min_k := by
        by_contra h_le2
        push_neg at h_le2
        have h_pow_le : (2 : ℝ≥0∞) ^ min_k ≤ 4 := by
          have h2 : (2 : ℝ≥0∞) ^ 2 = 4 := by norm_num
          rw [← h2]
          apply pow_le_pow_right₀ (by norm_num) h_le2
        have h_contra := le_trans h_min_k h_pow_le
        exact (lt_self_iff_false _).1 (lt_of_le_of_lt h_contra h_le4)
      have h_n_exists : ∃ n : ℕ, min_k = n + 2 := by
        use min_k - 2
        exact (Nat.sub_add_cancel (le_of_lt h_min_k_gt_2)).symm
      rcases h_n_exists with ⟨n, hn⟩
      have hn_min : ¬ (v w ≤ (2 : ℝ≥0∞) ^ (n + 1)) := by
        have h_lt : n + 1 < min_k := by omega
        intro h_contra
        exact Nat.find_min h_nonempty h_lt h_contra
      push_neg at hn_min
      have h_mem : w ∈ U n := by
        simp only [U, Set.mem_setOf_eq]
        have h_coe : ENNReal.ofReal (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) = (2 : ℝ≥0∞) ^ (n + 1) := by
          have h1 : (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) = (2 : ℝ) ^ (n + 1) := by norm_cast
          rw [h1]
          have h2 : ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) = (ENNReal.ofReal 2) ^ (n + 1) := by
            apply ENNReal.ofReal_pow
            norm_num
          have h3 : ENNReal.ofReal 2 = 2 := by norm_num
          rw [h2, h3]
        rw [h_coe]
        exact hn_min
      have h_val : (2 : ℝ≥0∞) ^ n ≤ mlTestValue U w := by
        unfold mlTestValue
        apply le_iSup_of_le n
        rw [if_pos h_mem]
      calc
        v w ≤ (2 : ℝ≥0∞) ^ min_k := h_min_k
        _ = (2 : ℝ≥0∞) ^ (n + 2) := by rw [hn]
        _ = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ 2 := by rw [pow_add]
        _ = (2 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ n := mul_comm _ _
        _ = 4 * (2 : ℝ≥0∞) ^ n := by norm_num
        _ ≤ 4 * mlTestValue U w := mul_le_mul' le_rfl h_val

/-- A point of infinite deficiency has infinite test value. -/
lemma mlTestValue_top_of_mlDeficiency_top {U : ℕ → Set CantorSeq} {w : CantorSeq}
    (h : mlDeficiency U w = ⊤) : mlTestValue U w = ⊤ := by
  classical
  unfold mlDeficiency at h
  unfold mlTestValue
  apply eq_top_iff.2
  by_contra h_neg
  push_neg at h_neg
  have h_unb : ∀ k : ℕ, ∃ m ≥ k, w ∈ U m := by
    intro k
    by_contra h_neg_unb
    push_neg at h_neg_unb
    have h_le : (⨆ (n : ℕ) (_ : w ∈ U n), (n : ENat)) ≤ (k : ENat) := by
      apply iSup_le
      intro n
      apply iSup_le
      intro hw
      have hn_lt : n < k := by
        by_contra hn_ge
        push_neg at hn_ge
        exact h_neg_unb n hn_ge hw
      exact ENat.coe_le_coe.2 (le_of_lt hn_lt)
    rw [h] at h_le
    exact ENat.top_ne_coe k (top_le_iff.1 h_le).symm
  rcases ENNReal.exists_nat_gt h_neg.ne with ⟨k, hk⟩
  rcases h_unb k with ⟨m, hm, hwm⟩
  have h_bound : (2 : ℝ≥0∞) ^ m ≤ ⨆ n, if w ∈ U n then (2 : ℝ≥0∞) ^ n else 1 := by
    apply le_iSup_of_le m
    rw [if_pos hwm]
  have h_m : (k : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ m := by
    have h1 : (k : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ k := by
      have hk_le : k ≤ 2 ^ k := k_le_two_pow_k k
      have hk_coe : (k : ℝ≥0∞) = ((k : ℕ) : ℝ≥0∞) := rfl
      have h2_coe : (2 : ℝ≥0∞) ^ k = ((2 ^ k : ℕ) : ℝ≥0∞) := by norm_num
      rw [hk_coe, h2_coe]
      exact Nat.cast_le.2 hk_le
    have h2 : (2 : ℝ≥0∞) ^ k ≤ (2 : ℝ≥0∞) ^ m := by
      apply pow_le_pow_right₀ (by norm_num) hm
    exact le_trans h1 h2
  have h_contra : (k : ℝ≥0∞) < (k : ℝ≥0∞) := lt_of_le_of_lt (le_trans h_m h_bound) hk
  exact (lt_self_iff_false _).1 h_contra

/-- A point of finite nonzero deficiency `m` belongs to the level `m` of the test. -/
lemma mlTestValue_m_of_mlDeficiency {U : ℕ → Set CantorSeq} {w : CantorSeq} {m : ℕ}
    (h : mlDeficiency U w = m) : m = 0 ∨ w ∈ U m := by
  classical
  unfold mlDeficiency at h
  by_cases h0 : m = 0
  · left; exact h0
  · right
    by_contra hm
    have h_le : (⨆ n, ⨆ _ : w ∈ U n, (n : ENat)) ≤ (m - 1 : ENat) := by
      apply iSup_le
      intro n
      apply iSup_le
      intro hn
      have hn_le : n ≤ m := by
        have h1 : (n : ENat) ≤ m := by
          rw [← h]
          exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)
        exact ENat.coe_le_coe.1 h1
      have hn_neq : n ≠ m := by
        intro heq
        rw [heq] at hn
        exact hm hn
      have hn_lt : n < m := lt_of_le_of_ne hn_le hn_neq
      have hn_le_sub : n ≤ m - 1 := Nat.le_sub_one_of_lt hn_lt
      exact ENat.coe_le_coe.2 hn_le_sub
    rw [h] at h_le
    have h_contra_nat : m ≤ m - 1 := ENat.coe_le_coe.1 h_le
    omega

/-- A deficiency bound with additive constant `c` becomes a multiplicative bound by `2^c` on the
test values. -/
lemma mlTestValue_le_of_mlDeficiency_le {U V : ℕ → Set CantorSeq} {c : ℕ}
    (h : ∀ w, mlDeficiency V w ≤ mlDeficiency U w + (c : ENat)) (w : CantorSeq) :
    mlTestValue V w ≤ 2 ^ c * mlTestValue U w := by
  classical
  have h_bound : ∀ n, w ∈ V n → (2 : ℝ≥0∞) ^ n ≤ 2 ^ c * mlTestValue U w := by
    intro n hV
    have h1 : (n : ENat) ≤ mlDeficiency V w := by
      unfold mlDeficiency
      exact le_iSup_of_le n (le_iSup_of_le hV le_rfl)
    have h2 : (n : ENat) ≤ mlDeficiency U w + (c : ENat) := le_trans h1 (h w)
    cases hU : mlDeficiency U w with
    | top =>
      have htop := mlTestValue_top_of_mlDeficiency_top hU
      rw [htop]
      have hc : (2 : ℝ≥0∞) ^ c > 0 := by
        apply ENNReal.pow_pos (by norm_num)
      rw [ENNReal.mul_top hc.ne_bot]
      exact le_top
    | coe m =>
      rw [hU] at h2
      have hn_le : n ≤ m + c := by
        rw [← ENat.coe_add, ENat.coe_le_coe] at h2
        exact h2
      have h_pow : (2 : ℝ≥0∞) ^ n ≤ (2 : ℝ≥0∞) ^ (m + c) := by
        apply pow_le_pow_right₀ (by norm_num) hn_le
      have h_pow_add : (2 : ℝ≥0∞) ^ (m + c) = (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ m := by
        rw [pow_add, mul_comm]
      rw [h_pow_add] at h_pow
      have h_m : (2 : ℝ≥0∞) ^ m ≤ mlTestValue U w := by
        rcases mlTestValue_m_of_mlDeficiency hU with h0 | hmem
        · rw [h0]
          have h0_pow : (2 : ℝ≥0∞) ^ 0 = 1 := by norm_num
          rw [h0_pow]
          exact one_le_mlTestValue U w
        · unfold mlTestValue
          apply le_iSup_of_le m
          rw [if_pos hmem]
      have h_mul : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞) ^ m ≤ (2 : ℝ≥0∞) ^ c * mlTestValue U w := by
        apply mul_le_mul' le_rfl h_m
      exact le_trans h_pow h_mul
  unfold mlTestValue
  apply iSup_le
  intro n
  split_ifs with hV
  · exact h_bound n hV
  · have hc : (1 : ℝ≥0∞) ≤ 2 ^ c := by
      have h1 : (1 : ℝ≥0∞) = 2 ^ 0 := by norm_num
      rw [h1]
      apply pow_le_pow_right₀ (by norm_num) (by omega)
    have hU_val : (1 : ℝ≥0∞) ≤ mlTestValue U w := one_le_mlTestValue U w
    have hmul : (1 : ℝ≥0∞) * 1 ≤ 2 ^ c * mlTestValue U w :=
      mul_le_mul' hc hU_val
    rwa [one_mul] at hmul

/-- A finite measure admits a positive rational `e` with `2e < 1` for which `2e · μ(univ) ≤ 1`. -/
lemma exists_rat_scaling {μ : Measure CantorSeq} (h : μ Set.univ ≠ ⊤) :
    ∃ e : ℚ, 0 < e ∧ 2 * e < 1 ∧ ENNReal.ofReal ((2 * e : ℚ) : ℝ) * μ Set.univ ≤ 1 := by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
  have hn_pos : 0 < n := by
    by_contra h0; push_neg at h0
    obtain rfl := Nat.le_zero.1 h0
    simp at hn
  set e : ℚ := 1 / (4 * n) with he_def
  have hn_cast_pos : (0 : ℚ) < n := Nat.cast_pos.2 hn_pos
  have he_pos : 0 < e := by rw [he_def]; exact div_pos one_pos (by positivity)
  have h2e_lt : 2 * e < 1 := by
    rw [he_def]
    show 2 * (1 / (4 * (n : ℚ))) < 1
    rw [show (2 : ℚ) * (1 / (4 * ↑n)) = 1 / (2 * ↑n) from by field_simp; ring]
    rw [div_lt_one (by positivity : (0 : ℚ) < 2 * ↑n)]
    have : (1 : ℚ) ≤ n := Nat.one_le_cast.2 hn_pos
    linarith
  refine ⟨e, he_pos, h2e_lt, ?_⟩
  have h2e_le : ENNReal.ofReal ((2 * e : ℚ) : ℝ) ≤ ((n : ℝ≥0∞))⁻¹ := by
    rw [he_def]
    show ENNReal.ofReal ((2 * (1 / (4 * (n : ℚ))) : ℚ) : ℝ) ≤ _
    have h_simp : ((2 * (1 / (4 * (n : ℚ))) : ℚ) : ℝ) = 1 / (2 * (n : ℝ)) := by
      push_cast; field_simp; ring
    rw [h_simp]
    have h_inv : ((n : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 hn_pos)]
      congr 1
      exact (ENNReal.ofReal_natCast n).symm
    rw [h_inv]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv, one_mul]
    exact inv_anti₀ (by positivity) (by linarith [show (0 : ℝ) < n from Nat.cast_pos.2 hn_pos])
  calc ENNReal.ofReal ((2 * e : ℚ) : ℝ) * μ Set.univ
        ≤ (↑n)⁻¹ * μ Set.univ := mul_le_mul' h2e_le le_rfl
      _ ≤ (↑n)⁻¹ * ↑n := mul_le_mul' le_rfl (le_of_lt hn)
      _ = 1 := ENNReal.inv_mul_cancel
            (Nat.cast_ne_zero.2 (by omega))
            (ENNReal.natCast_ne_top n)

/-- Suitably scaled by a positive rational, the value function of a Martin-Löf test is a
probability-bounded randomness test. -/
lemma isProbabilityBoundedRandomnessTest_rat_smul_mlTestValue {μ : Measure CantorSeq}
    {U : ℕ → Set CantorSeq} (hU : IsMartinLofTest μ U) {e : ℚ} (he_pos : 0 < e) (he_lt : 2 * e < 1)
    (he_meas : ENNReal.ofReal ((2 * e : ℚ) : ℝ) * μ Set.univ ≤ 1) :
    IsProbabilityBoundedRandomnessTest μ (fun w => ENNReal.ofReal (e : ℝ) * mlTestValue U w) := by
  have he' : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he_pos
  refine ⟨(isLowerSemicomputableFun_mlTestValue hU.1).rat_smul he_pos, ?_⟩
  intro c hc
  have hct : c = e * (c / e) := by field_simp
  set t : ℚ := c / e with ht_def
  have ht_pos : 0 < t := div_pos hc he_pos
  have hne0 : ENNReal.ofReal (e : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 he').ne'
  have hnet : ENNReal.ofReal (e : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ENNReal.ofReal (e : ℝ) * ENNReal.ofReal (t : ℝ) = ENNReal.ofReal (c : ℝ) := by
    rw [← ENNReal.ofReal_mul he'.le]
    congr 1
    rw [show (c : ℝ) = ((e * t : ℚ) : ℝ) from by exact_mod_cast congrArg (fun x : ℚ => x) hct]
    push_cast
    ring
  have hset : {w | ENNReal.ofReal (e : ℝ) * mlTestValue U w > ENNReal.ofReal (c : ℝ)}
      = {w | ENNReal.ofReal (t : ℝ) < mlTestValue U w} := by
    ext w
    simp only [Set.mem_setOf_eq, gt_iff_lt, ← key]
    exact ENNReal.mul_lt_mul_iff_right hne0 hnet
  rw [hset]
  by_cases htlt : t < 1
  · have huniv : {w | ENNReal.ofReal (t : ℝ) < mlTestValue U w} = Set.univ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hlt1 : ENNReal.ofReal (t : ℝ) < 1 := by
        rw [ENNReal.ofReal_lt_one]; exact_mod_cast htlt
      exact lt_of_lt_of_le hlt1 (one_le_mlTestValue U w)
    rw [huniv]
    have h2e : (0 : ℝ) < ((2 * e : ℚ) : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) < 2 * e)
    have hne0' : ENNReal.ofReal ((2 * e : ℚ) : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 h2e).ne'
    have hnet' : ENNReal.ofReal ((2 * e : ℚ) : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmu : μ Set.univ ≤ (ENNReal.ofReal ((2 * e : ℚ) : ℝ))⁻¹ := by
      calc μ Set.univ
          = (ENNReal.ofReal ((2 * e : ℚ) : ℝ))⁻¹ *
              (ENNReal.ofReal ((2 * e : ℚ) : ℝ) * μ Set.univ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hne0' hnet', one_mul]
        _ ≤ (ENNReal.ofReal ((2 * e : ℚ) : ℝ))⁻¹ * 1 := mul_le_mul' le_rfl he_meas
        _ = (ENNReal.ofReal ((2 * e : ℚ) : ℝ))⁻¹ := mul_one _
    have hclt : c < 2 * e := by nlinarith [hct, ht_pos, he_pos]
    have hclt' : ENNReal.ofReal (c : ℝ) < ENNReal.ofReal ((2 * e : ℚ) : ℝ) := by
      refine (ENNReal.ofReal_lt_ofReal_iff h2e).2 ?_
      exact_mod_cast hclt
    exact lt_of_le_of_lt hmu (ENNReal.inv_lt_inv.2 hclt')
  · push_neg at htlt
    have hex : ∃ n : ℕ, t < 2 ^ (n + 1) := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℚ) < 2)
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact absurd hm (by simpa using not_lt.2 htlt)
      · exact ⟨m - 1, by rwa [Nat.sub_add_cancel hmpos]⟩
    classical
    set n := Nat.find hex with hn_def
    have hlt : t < 2 ^ (n + 1) := Nat.find_spec hex
    have hge : (2 : ℚ) ^ n ≤ t := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0]; simpa using htlt
      · have hmin := Nat.find_min hex (m := n - 1) (by omega)
        push_neg at hmin
        have hn1 : n - 1 + 1 = n := by omega
        rwa [hn1] at hmin
    have h2n : (2 : ℝ≥0∞) ^ n ≤ ENNReal.ofReal (t : ℝ) := by
      rw [← ofReal_rat_two_pow n]
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hge)
    have hsub : {w | ENNReal.ofReal (t : ℝ) < mlTestValue U w}
        ⊆ {w | (2 : ℝ≥0∞) ^ n < mlTestValue U w} :=
      fun w hw => lt_of_le_of_lt h2n hw
    have hcn : c < 2 ^ n := by
      have h1 : e * t < e * 2 ^ (n + 1) := mul_lt_mul_of_pos_left hlt he_pos
      have h3 : (2 * e) * 2 ^ n < 1 * 2 ^ n :=
        mul_lt_mul_of_pos_right he_lt (by positivity)
      calc c = e * t := hct
        _ < e * 2 ^ (n + 1) := h1
        _ = (2 * e) * 2 ^ n := by ring
        _ < 1 * 2 ^ n := h3
        _ = 2 ^ n := one_mul _
    have hcn' : ENNReal.ofReal (c : ℝ) < (2 : ℝ≥0∞) ^ n := by
      rw [← ofReal_rat_two_pow n]
      refine (ENNReal.ofReal_lt_ofReal_iff ?_).2 (by exact_mod_cast hcn)
      exact_mod_cast pow_pos (by norm_num : (0 : ℚ) < 2) n
    calc μ {w | ENNReal.ofReal (t : ℝ) < mlTestValue U w}
        ≤ μ {w | (2 : ℝ≥0∞) ^ n < mlTestValue U w} := measure_mono hsub
      _ ≤ dyadicValue 1 n := measure_two_pow_lt_mlTestValue hU n
      _ = ((2 : ℝ≥0∞) ^ n)⁻¹ := by simp [dyadicValue, one_div]
      _ < (ENNReal.ofReal (c : ℝ))⁻¹ := ENNReal.inv_lt_inv.2 hcn'

-- Theorem 41
/-- Every computable measure has a probability-bounded randomness test that dominates all others
up to a multiplicative constant, and it is equivalent to the value function of a Martin-Löf test
of maximal deficiency. -/
theorem exists_maximal_probability_bounded_test {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) :
    ∃ u : CantorSeq → ℝ≥0∞, ∃ U : ℕ → Set CantorSeq,
      IsProbabilityBoundedRandomnessTest μ u ∧
      (∀ v, IsProbabilityBoundedRandomnessTest μ v →
        ∃ c : NNReal, ∀ w, v w ≤ c * u w) ∧
      IsMaximalMLDeficiencyTest μ U ∧
      ∃ c1 c2 : NNReal, ∀ w,
        mlTestValue U w ≤ c1 * u w ∧ u w ≤ c2 * mlTestValue U w := by
  obtain ⟨U, hUmax⟩ := exists_maximal_mlDeficiency hμ
  obtain ⟨e, he_pos, he_lt, he_meas⟩ := exists_rat_scaling hμ.measure_univ_ne_top
  have he' : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he_pos
  refine ⟨fun w => ENNReal.ofReal (e : ℝ) * mlTestValue U w, U,
    isProbabilityBoundedRandomnessTest_rat_smul_mlTestValue hUmax.1 he_pos he_lt he_meas,
    ?_, hUmax, ?_⟩
  · intro v hv
    obtain ⟨k, hk⟩ := hUmax.2 _ (isMartinLofTest_superlevel_of_probabilityBounded hv)
    refine ⟨Real.toNNReal ((4 * 2 ^ k : ℝ) / (e : ℝ)), fun w => ?_⟩
    have hcoe : ((Real.toNNReal ((4 * 2 ^ k : ℝ) / (e : ℝ)) : NNReal) : ℝ≥0∞)
        * ENNReal.ofReal (e : ℝ) = 4 * (2 : ℝ≥0∞) ^ k := by
      change ENNReal.ofReal ((4 * 2 ^ k : ℝ) / (e : ℝ)) * ENNReal.ofReal (e : ℝ) = _
      rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ he'.ne',
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    calc v w
        ≤ 4 * mlTestValue
            (fun n => {w' | ENNReal.ofReal (((2 : ℚ) ^ (n + 1) : ℚ) : ℝ) < v w'}) w :=
          le_mlTestValue_superlevel v w
      _ ≤ 4 * ((2 : ℝ≥0∞) ^ k * mlTestValue U w) :=
          mul_le_mul' le_rfl (mlTestValue_le_of_mlDeficiency_le hk w)
      _ = (4 * (2 : ℝ≥0∞) ^ k) * mlTestValue U w := by ring
      _ = ((Real.toNNReal ((4 * 2 ^ k : ℝ) / (e : ℝ)) : NNReal) : ℝ≥0∞)
            * (ENNReal.ofReal (e : ℝ) * mlTestValue U w) := by rw [← hcoe]; ring
  · refine ⟨Real.toNNReal ((e : ℝ)⁻¹), Real.toNNReal (e : ℝ), fun w => ?_⟩
    have hinv : ((Real.toNNReal ((e : ℝ)⁻¹) : NNReal) : ℝ≥0∞) * ENNReal.ofReal (e : ℝ) = 1 := by
      change ENNReal.ofReal ((e : ℝ)⁻¹) * ENNReal.ofReal (e : ℝ) = 1
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 he'.le), inv_mul_cancel₀ he'.ne']
      simp
    constructor
    · have heq : mlTestValue U w = ((Real.toNNReal ((e : ℝ)⁻¹) : NNReal) : ℝ≥0∞)
          * (ENNReal.ofReal (e : ℝ) * mlTestValue U w) := by
        rw [← mul_assoc, hinv, one_mul]
      exact heq.le
    · change ENNReal.ofReal (e : ℝ) * mlTestValue U w ≤ _
      exact le_rfl

end Kolmogorov
