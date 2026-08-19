import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.DescriptionSnapshot
import KolmogorovMathlib.Prefix.ConditionalSymmetry

namespace Kolmogorov

open scoped ENNReal

/-!
# Section 3 Paper-Facing Theorem Statements

This module provides the clean, paper-facing wrappers for the already-proved
Section 3 results, avoiding the heavy internal API.
-/

/-- The complexity-improvement half of the Improving Descriptions Theorem. -/
theorem improving_descriptions_complexity_thm (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x n i j k,
      x.length = n →
      ManyIJDescriptions U x i j k →
      k ≤ i →
      InDescriptionProfile U x (i - k + logSlack c (n + i + j)) (j + logSlack c (n + i + j)) :=
  exists_description_smaller_complexity_of_many_logSlack U hU

/-- The size-improvement half of the Improving Descriptions Theorem. -/
theorem improving_descriptions_size_thm (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x n i j k,
      x.length = n →
      ManyIJDescriptions U x i j k →
      k ≤ j →
      InDescriptionProfile U x (i + logSlack c (n + i + j)) (j - k + logSlack c (n + i + j)) :=
  improvingDescriptionsSize_of_complexity U hU
    (exists_description_smaller_complexity_of_many_logSlack U hU)

/-- Theorem 4: The Deficiencies Theorem (Tight Version). -/
theorem deficiencies_theorem_tight_thm (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString)
        (n delta d i j kx c_soi : ℕ),
      x.length = n →
      RealizedSetOptimalityGap U A hA x delta i j kx →
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d →
      d ≤ delta + c_soi →
      ∃ (B : Finset BitString) (hB : B.Nonempty), x ∈ B ∧
        setComplexity U B hB + (delta - d : ℕ) ≤
          setComplexity U A hA + (logSlack c (n + delta + d) : ENat) ∧
        SetOptimalityDeficiencyLe U B hB x (d + logSlack c (n + delta + d)) :=
  deficiencies_theorem_tight_of_optimal U hU

/-- Theorem 5: Optimal set stochasticity implies an explicit description profile. -/
theorem optimal_stochasticity_imp_profile_thm (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (alpha beta j : ℕ),
      IsOptimalSetStochastic U x alpha beta →
      KPPlain U x + beta ≤ (alpha : ENat) + j →
      InDescriptionProfile U x (alpha + logSlack c (alpha + beta + j)) (j + 1) :=
  isOptimalSetStochastic_imp_profile U hU

/- **Gate D Note:** The randomness deficiency of the uniform level-set model is bounded by the
randomness deficiency of the original distribution plus `O(log k)`, provided `k`
dyadically brackets `P.mass x`. -/

/-- Gate D (corrected): the randomness deficiency of the uniform
level-set model is bounded by the randomness deficiency of the original distribution
plus `O(log k)`, **provided `k` dyadically brackets `P.mass x`** (both
`2⁻ᵏ ≤ P.mass x` and `P.mass x ≤ 2·2⁻ᵏ`).  The extra upper bound `h_mass_ub` fixes
the overstrong original (see the comment above).  This still encapsulates the
condition-change bound `KP(x | A.code) ≥ KP(x | P.code) − O(log k)` (`A.code` is
computable from `(P.code, k)`), whose "remove known short info `k` from the
condition" direction is the key machine-model ingredient, discharged via
`KP_cond_remove_short_info`. -/
theorem levelSet_randomness_deficiency_le_gate (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (x : BitString) (k : ℕ)
      (_ : P.IsProbability) (h_supp : x ∈ P.support) (h_mass : (2 : ℝ≥0∞)⁻¹ ^ k ≤ P.mass x)
      (_h_mass_ub : P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k)
      (beta : ℕ),
      CodedFiniteDistribution.DeficiencyLe U P x beta →
      ∃ d : ℕ,
        CodedFiniteDistribution.DeficiencyLe U (codedUniformOn (levelSet P k)
          (levelSet_nonempty_of_mass_ge P x k h_supp h_mass)) x d ∧
        d ≤ beta + logSlack c k := by
  obtain ⟨c_rem, hc_rem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨c_map, hc_map⟩ := KP_cond_map_le U hU levelSetUniformCode levelSetUniformCode_computable
  obtain ⟨c_nat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  use c_rem + c_map + c_nat + 2
  intro P x k h_prob h_supp h_mass h_mass_ub beta h_def_P
  let A := codedUniformOn (levelSet P k) (levelSet_nonempty_of_mass_ge P x k h_supp h_mass)
  have hA_code : A.code = levelSetUniformCode (pairCode P.code (natCode k)) :=
    (levelSetUniformCode_eq P k _).symm
  have hkp1 : KP U x P.code ≤ KP U x A.code + c_map + KPPlain U (natCode k) + c_rem := by
    calc KP U x P.code ≤
        KP U x (pairCode P.code (natCode k)) + KPPlain U (natCode k) + c_rem :=
          hc_rem x P.code (natCode k)
      _ ≤ (KP U x A.code + c_map) + KPPlain U (natCode k) + c_rem := by
        have : KP U x (pairCode P.code (natCode k)) ≤ KP U x A.code + c_map := by
          rw [hA_code]
          exact hc_map x (pairCode P.code (natCode k))
        gcongr
      _ = KP U x A.code + c_map + KPPlain U (natCode k) + c_rem := by ac_rfl
  let C := 2 * k.bits.length + c_rem + c_map + c_nat
  have hkp2 : KP U x P.code ≤ KP U x A.code + (C : ENat) := by
    calc KP U x P.code ≤ KP U x A.code + c_map + KPPlain U (natCode k) + c_rem := hkp1
      _ ≤ KP U x A.code + c_map + (2 * (k.bits.length : ENat) + c_nat) + c_rem := by
        gcongr
        exact hc_nat k
      _ = KP U x A.code + (C : ENat) := by dsimp [C]; push_cast; ring_nf
  use beta + C + 2
  constructor
  · unfold CodedFiniteDistribution.DeficiencyLe
    have h_supp' : x ∈ levelSet P k := mem_levelSet h_supp h_mass
    have hA_mass : A.mass x = ((levelSet P k).card : ℝ≥0∞)⁻¹ :=
      codedUniformOn_mass_of_mem _ _ x h_supp'
    have h_card_le : ((levelSet P k).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ k :=
      levelSet_card_le P k h_prob
    have hA_mass_lb : (2 : ℝ≥0∞)⁻¹ ^ k ≤ A.mass x := by
      rw [hA_mass, ← ENNReal.inv_pow]
      exact ENNReal.inv_le_inv.mpr h_card_le
    have hcw1 : complexityWeight (KP U x A.code) * (2 : ℝ≥0∞)⁻¹ ^ C ≤ complexityWeight
        (KP U x P.code) := by
      calc complexityWeight (KP U x A.code) * (2 : ℝ≥0∞)⁻¹ ^ C =
          complexityWeight (KP U x A.code + (C : ENat)) := by
            rw [complexityWeight_add_nat]
        _ ≤ complexityWeight (KP U x P.code) := complexityWeight_le_of_le hkp2
    have h_mass_chain : P.mass x ≤ (2 : ℝ≥0∞) * A.mass x := by
      calc P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k := h_mass_ub
        _ ≤ 2 * A.mass x := by gcongr
    have h_def_chain : complexityWeight (KP U x P.code) ≤ (2 : ℝ≥0∞) ^ beta *
        ((2 : ℝ≥0∞) * A.mass x) := by
      calc complexityWeight (KP U x P.code) ≤ (2 : ℝ≥0∞) ^ beta * P.mass x := h_def_P
        _ ≤ (2 : ℝ≥0∞) ^ beta * (2 * A.mass x) := by gcongr
    have hcw_bound : complexityWeight (KP U x A.code) * (2 : ℝ≥0∞)⁻¹ ^ C ≤ (2 : ℝ≥0∞) ^ beta * 2 *
        A.mass x := by
      calc complexityWeight (KP U x A.code) * (2 : ℝ≥0∞)⁻¹ ^ C ≤
          complexityWeight (KP U x P.code) := hcw1
        _ ≤ (2 : ℝ≥0∞) ^ beta * (2 * A.mass x) := h_def_chain
        _ = (2 : ℝ≥0∞) ^ beta * 2 * A.mass x := by rw [mul_assoc]
    have h_mul_pow : complexityWeight (KP U x A.code) ≤ (2 : ℝ≥0∞) ^ beta * 2 * (2 : ℝ≥0∞) ^ C *
        A.mass x := by
      have h1 : (2 : ℝ≥0∞)⁻¹ ^ C = ((2 : ℝ≥0∞) ^ C)⁻¹ := by rw [ENNReal.inv_pow]
      have h2 : ((2 : ℝ≥0∞) ^ C)⁻¹ * (2 : ℝ≥0∞) ^ C = 1 :=
        ENNReal.inv_mul_cancel (by simp) (by simp)
      calc complexityWeight (KP U x A.code) =
          complexityWeight (KP U x A.code) * 1 := by rw [mul_one]
        _ = complexityWeight (KP U x A.code) * (((2 : ℝ≥0∞) ^ C)⁻¹ * (2 : ℝ≥0∞) ^ C) := by rw [← h2]
        _ = (complexityWeight (KP U x A.code) * ((2 : ℝ≥0∞) ^ C)⁻¹) *
            (2 : ℝ≥0∞) ^ C := by rw [mul_assoc]
        _ = (complexityWeight (KP U x A.code) * (2 : ℝ≥0∞)⁻¹ ^ C) * (2 : ℝ≥0∞) ^ C := by rw [h1]
        _ ≤ ((2 : ℝ≥0∞) ^ beta * 2 * A.mass x) * (2 : ℝ≥0∞) ^ C := by gcongr
        _ = (2 : ℝ≥0∞) ^ beta * 2 * (2 : ℝ≥0∞) ^ C * A.mass x := by ring
    calc complexityWeight (KP U x A.code) ≤
        (2 : ℝ≥0∞) ^ beta * 2 * (2 : ℝ≥0∞) ^ C * A.mass x := h_mul_pow
      _ = (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞) ^ 1 * (2 : ℝ≥0∞) ^ C * A.mass x := by rw [pow_one]
      _ = (2 : ℝ≥0∞) ^ (beta + 1) * (2 : ℝ≥0∞) ^ C * A.mass x := by rw [← pow_add]
      _ = (2 : ℝ≥0∞) ^ (beta + 1 + C) * A.mass x := by rw [← pow_add]
      _ = (2 : ℝ≥0∞) ^ (beta + C + 1) * A.mass x := by congr 2; omega
      _ ≤ (2 : ℝ≥0∞) ^ (beta + C + 2) * A.mass x := by
        have h_exp : beta + C + 1 ≤ beta + C + 2 := by omega
        have h_pow : (2 : ℝ≥0∞) ^ (beta + C + 1) ≤ (2 : ℝ≥0∞) ^ (beta + C + 2) :=
          pow_le_pow_right' (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_exp
        gcongr
  · unfold logSlack
    have h1 : 2 ≤ c_rem + c_map + c_nat + 2 := by omega
    have h2 : 2 * k.bits.length ≤
        (c_rem + c_map + c_nat + 2) * k.bits.length :=
      Nat.mul_le_mul_right _ h1
    omega

/- **Distribution-to-uniform-set interface.**

Distribution-to-uniform-set step of Theorem 3.  From an `(alpha, beta)`-stochastic
string `x` (a probability model `P` with `P.complexity U ≤ alpha` and randomness
deficiency `≤ beta`) one extracts, via the dyadic level set `A = levelSet P k` at
the level `k` bracketing `P.mass x`, a *uniform* finite-set model realizing a tight
optimality gap:

* `RealizedSetOptimalityGap U A hA x delta i j kx` — `A` has set complexity `i`,
  dyadic size bracket `2^j/2 ≤ |A| ≤ 2^j`, `KP(x)=kx`, and gap `delta = i+j-kx`;
* `DeficiencyLe U (codedUniformOn A hA) x d` — the uniform model on `A` has
  randomness deficiency `d`;
* `d ≤ delta` (the deficiency never exceeds the gap);
* `i ≤ alpha + O(log)` (the level set is no more complex than `P`, via
  `levelSetModel_setComplexity_le`);
* `d ≤ beta + O(log)` (the uniform level set inherits `P`'s randomness deficiency up
  to `O(log)`, the standard level-set randomness-deficiency bound);
* `n + delta + d ≤ 4·(n+alpha+beta) + c` — the internal budget is linearly
  controlled by the visible budget (`k ≤ n + beta + O(log)` since
  `P.mass x ≥ 2^{-(KP(x|P.code)+beta)}` and `KP(x|P.code) ≤ n + O(log)`).

This is exactly the hypothesis package consumed by the fully-proved tight
deficiencies theorem `deficiencies_theorem_tight_of_optimal`.  The conditional
complexity bound giving `d ≤ beta + O(log)` is encapsulated in
`levelSet_randomness_deficiency_le_gate`. -/

/-- Every atom of a probability distribution has mass at most `1`: it is one of the
nonnegative summands of the total mass `∑_{y ∈ support} P.mass y = 1`. -/
theorem mass_le_one_of_isProbability (P : CodedFiniteDistribution)
    (hP : P.IsProbability) (x : BitString) : P.mass x ≤ 1 := by
  by_cases hx : x ∈ P.support
  · calc P.mass x ≤ ∑ y ∈ P.support, P.mass y :=
          Finset.single_le_sum (f := fun y => P.mass y) (fun _ _ => zero_le) hx
      _ = 1 := hP
  · rw [CodedFiniteDistribution.mass_eq_zero_of_not_mem_support P x hx]; exact zero_le

/-
For a probability atom with `0 < mass ≤ 1`, there is a dyadic level `k`
bracketing the mass: `2⁻ᵏ ≤ mass ≤ 2·2⁻ᵏ`.  (Take `k` the least level whose
dyadic interval `[2⁻ᵏ, 2·2⁻ᵏ]` contains `mass`.)
-/
theorem exists_k_mass (P : CodedFiniteDistribution) (x : BitString)
    (hx : P.mass x > 0) (hx1 : P.mass x ≤ 1) :
    ∃ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k ≤ P.mass x ∧ P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (2 : ENNReal)⁻¹ ^ k ≤ P.mass x ∧ ∀ j : ℕ, j < k →
      ¬((2 : ENNReal)⁻¹ ^ j ≤ P.mass x) := by
    have h_exists_k : ∃ k : ℕ, (2 : ENNReal)⁻¹ ^ k ≤ P.mass x := by
      have h_exists_k :
          Filter.Tendsto (fun k : ℕ => (2 : ENNReal)⁻¹ ^ k) Filter.atTop (nhds 0) := by
        norm_num +zetaDelta at *;
      exact ( h_exists_k.eventually ( ge_mem_nhds hx ) ) |> fun h => h.exists;
    exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k, fun j hj => Nat.find_min h_exists_k hj ⟩;
  refine ⟨k, hk.1, ?_⟩
  cases k with
  | zero => simpa using hx1.trans (by norm_num)
  | succ k =>
    have hlt : P.mass x < (2 : ℝ≥0∞)⁻¹ ^ k := not_le.mp (hk.2 k (Nat.lt_succ_self k))
    have heq : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = (2 : ℝ≥0∞)⁻¹ ^ k := by
      rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    rw [heq]; exact hlt.le

/-- Conditional prefix complexity is finite for an optimal machine: `x` always has
*some* program relative to any condition `y`, so `KP U x y ≠ ⊤`. -/
theorem KP_ne_top_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U)
    (x y : BitString) : KP U x y ≠ ⊤ := by
  obtain ⟨c_plain, h_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  have hbound : KP U x y ≤
      (x.length + 2 * (Nat.bits x.length).length + c_len : ℕ) + (c_plain : ENat) :=
    (h_plain x y).trans (by gcongr; exact_mod_cast h_len x)
  exact ne_top_of_le_ne_top (by exact_mod_cast (ENat.coe_ne_top _)) hbound

/-- Plain prefix complexity is finite for an optimal machine. -/
theorem KPPlain_ne_top_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) : KPPlain U x ≠ ⊤ := by
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  exact ne_top_of_le_ne_top (by exact_mod_cast (ENat.coe_ne_top
    (x.length + 2 * (Nat.bits x.length).length + c_len))) (by exact_mod_cast h_len x)

/-- Set complexity is finite for an optimal machine (it is the plain complexity of a
concrete bit string, the canonical uniform code of the set). -/
theorem setComplexity_ne_top_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U)
    (S : Finset BitString) (hS : S.Nonempty) : setComplexity U S hS ≠ ⊤ :=
  KPPlain_ne_top_of_optimal U hU _

/-
**Level bound.**  If `x` (of length `n`) has randomness deficiency `≤ beta`
under `P` and `k` dyadically over-brackets its mass (`P.mass x ≤ 2·2⁻ᵏ`), then
`k ≤ n + beta + O(log n)`.  Proof: the deficiency `2^{-KP(x|P.code)} ≤ 2^beta·P.mass x`
together with `KP(x|P.code) ≤ KPPlain(x) + O(1) ≤ n + 2·log n + O(1) =: M` gives
`2^{-M} ≤ 2^beta·P.mass x ≤ 2^{beta+1}·2⁻ᵏ`, i.e. `2^k ≤ 2^{M+beta+1}`, so
`k ≤ M + beta + 1 = n + beta + O(log n)`.
-/
theorem levelSet_level_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (x : BitString) (n beta k : ℕ),
      x.length = n →
      CodedFiniteDistribution.DeficiencyLe U P x beta →
      P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k →
      k ≤ n + beta + logSlack c n := by
  obtain ⟨c₁, hc₁⟩ :=KP_le_KPPlain U hU
  obtain ⟨c₂, hc₂⟩ :=KPPlain_le_length_add_log U hU
  use 2 + c₂ + c₁ + 1;
  intro P x n beta k hn hdef hub
  set M := n + 2 * (Nat.bits n).length + c₂ + c₁ with hM_def
  have hM : KP U x P.code ≤ (M : ENat) := by
    have step1 : KP U x P.code ≤ KPPlain U x + (c₁ : ENat) := hc₁ x P.code
    have step2 : KPPlain U x + (c₁ : ENat) ≤ ((x.length : ENat)
        + 2 * (x.length.bits.length : ENat) + c₂) + c₁ := by
      have h_le := hc₂ x
      gcongr
    have step3 : ((x.length : ENat) + 2 * (x.length.bits.length : ENat) + c₂) + (c₁ : ENat)
        = (M : ENat) := by
      rw [hn]
      rfl
    exact step1.trans (step2.trans step3.le)
  have h_exp : (2 : ℝ≥0∞)⁻¹ ^ M ≤ (2 : ℝ≥0∞) ^ beta * P.mass x := by
    exact (complexityWeight_le_of_le hM).trans hdef
  have h_exp : (2 : ℝ≥0∞)⁻¹ ^ M ≤ (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) := by
    have h_le : P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k := hub
    exact h_exp.trans (by gcongr)
  have h_exp : (2 : ℝ≥0∞) ^ k ≤ (2 : ℝ≥0∞) ^ (M + beta + 1) := by
    have step1 := mul_le_mul_left h_exp (2 ^ k * 2 ^ M)
    have lhs_eq : (2 : ℝ≥0∞)⁻¹ ^ M * (2 ^ k * 2 ^ M) = (2 : ℝ≥0∞) ^ k := by
      calc (2 : ℝ≥0∞)⁻¹ ^ M * (2 ^ k * 2 ^ M)
        _ = 2 ^ k * ((2 : ℝ≥0∞)⁻¹ ^ M * 2 ^ M) := by ring
        _ = 2 ^ k * 1 := by congr 1; rw [← mul_pow, ENNReal.inv_mul_cancel] <;> norm_num
        _ = 2 ^ k := by ring
    have rhs_eq : (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) * (2 ^ k * 2 ^ M)
        = (2 : ℝ≥0∞) ^ (M + beta + 1) := by
      calc (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) * (2 ^ k * 2 ^ M)
        _ = (2 : ℝ≥0∞) ^ beta * (2 * (2 : ℝ≥0∞)⁻¹ ^ k) * (2 ^ k * 2 ^ M) := rfl
        _ = 2 ^ beta * 2 * 2 ^ M * ((2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k) := by
          ring
        _ = 2 ^ beta * 2 * 2 ^ M * 1 := by
          congr 1; rw [← mul_pow, ENNReal.inv_mul_cancel] <;> norm_num
        _ = 2 ^ beta * 2 ^ 1 * 2 ^ M := by ring
        _ = 2 ^ (M + beta + 1) := by rw [← pow_add, ← pow_add]; congr 1; omega
    rwa [lhs_eq, rhs_eq] at step1
  have h_exp : k ≤ M + beta + 1 := by
    contrapose! h_exp; norm_cast at *; simp_all +decide [ pow_lt_pow_iff_right₀ ] ;
  unfold logSlack; simp +arith +decide [ Nat.bits ] at *;
  grind

/-- Gate G5a: Conditional two-part decoder lemma.
The plain complexity of an element `x` in a set `A` is bounded by the set's complexity
plus the conditional complexity of `x` given the set's canonical code. -/
theorem KP_le_setComplexity_add_condKP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString),
      x ∈ A →
      KPPlain U x ≤ setComplexity U A hA + KP U x (codedUniformOn A hA).code + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_le_KPPlain_add_KP U hU
  refine ⟨c, fun A hA x _ => ?_⟩
  exact hc x (codedUniformOn A hA).code

/-- Gate G5a, `ℕ`-truncated form: the exact inequality consumed by the optimality-gap
bookkeeping, where `delta = i + j - kx` lives at the `ℕ` level.  All three complexities
are finite for an optimal machine (`KPPlain_ne_top_of_optimal`,
`setComplexity_ne_top_of_optimal`, `KP_ne_top_of_optimal`), so the `ENat` bound of
`KP_le_setComplexity_add_condKP` transfers verbatim to `ℕ`:
`kx ≤ i + KP(x | A.code).toNat + c`.

This is the honest content behind the `d ≤ delta` gate below: writing `kx := KPPlain(x).toNat`
and `i := setComplexity(A).toNat`, it forces the true randomness deficiency
`δ(x|A) = j - KP(x|A.code).toNat` to obey `δ ≤ (i + j - kx) + c = delta + c`.  The additive
`c` is the irreducible constant of the "easy" (subadditivity) direction of symmetry of
information — SOI has no constant-free easy direction — which is exactly why a faithful
`d ≤ delta` statement must let `delta` absorb this `O(1)` slack. -/
theorem KPPlain_toNat_le_setComplexity_add_condKP (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString),
      x ∈ A →
      (KPPlain U x).toNat ≤
        (setComplexity U A hA).toNat + (KP U x (codedUniformOn A hA).code).toNat + c := by
  obtain ⟨c, hc⟩ := KP_le_setComplexity_add_condKP U hU
  refine ⟨c, fun A hA x hx => ?_⟩
  have hbound := hc A hA x hx
  have h1 : ((KPPlain U x).toNat : ENat) = KPPlain U x :=
    ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU x)
  have h2 : ((setComplexity U A hA).toNat : ENat) = setComplexity U A hA :=
    ENat.coe_toNat (setComplexity_ne_top_of_optimal U hU A hA)
  have h3 : ((KP U x (codedUniformOn A hA).code).toNat : ENat) =
      KP U x (codedUniformOn A hA).code :=
    ENat.coe_toNat (KP_ne_top_of_optimal U hU x _)
  rw [← h1, ← h2, ← h3] at hbound
  exact_mod_cast hbound

theorem exists_realizedGap_uniformSet_of_stochastic
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n alpha beta : ℕ),
      x.length = n →
      IsStochastic U x alpha beta →
      ∃ (A : Finset BitString) (hA : A.Nonempty) (delta i j kx d : ℕ),
        RealizedSetOptimalityGap U A hA x delta i j kx ∧
        CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d ∧
        d ≤ delta + c ∧
        (i : ℕ) ≤ alpha + logSlack c (n + alpha + beta) ∧
        d ≤ beta + logSlack c (n + alpha + beta) ∧
        n + delta + d ≤ 4 * (n + alpha + beta) + c := by
  obtain ⟨c_gate, h_gate⟩ := levelSet_randomness_deficiency_le_gate U hU
  obtain ⟨c_comp, h_comp⟩ := levelSetModel_setComplexity_le U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_plain, h_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_lb, h_lb⟩ := levelSet_level_bound U hU
  obtain ⟨c_soi, h_soi⟩ := KPPlain_toNat_le_setComplexity_add_condKP U hU
  obtain ⟨C2, hC2⟩ := logSlack_fold_level c_comp c_lb
  obtain ⟨C3, hC3⟩ := logSlack_fold_level c_gate c_lb
  obtain ⟨Csum, hCsum⟩ := logSlack_fold_level (c_comp + c_gate) c_lb
  -- The witness constant must dominate the folding constants, so we choose it after
  -- they are produced.  `bsum` converts the single *combined* log-slack overhead at
  -- the visible budget into a linear `≤ M + bsum` for the final budget inequality.
  obtain ⟨bsum, hbsum⟩ := logSlack_le_add_const (Csum + c_lb)
  use c_lb + C2 + C3 + Csum + bsum + c_gate + c_comp + c_len + c_plain + c_soi + 100
  intro x n alpha beta h_len_x h_stoch
  obtain ⟨P, h_prob, h_comp_P, h_def_P⟩ := h_stoch
  have h_mass_pos : P.mass x > 0 :=
    mass_pos_of_deficiencyLe_of_KP_ne_top h_def_P (KP_ne_top_of_optimal U hU x P.code)
  have h_mass_le1 : P.mass x ≤ 1 := mass_le_one_of_isProbability P h_prob x
  obtain ⟨k, h_k_lower, h_k_upper⟩ := exists_k_mass P x h_mass_pos h_mass_le1
  have h_supp : x ∈ P.support := by
    by_contra hx
    exact absurd (CodedFiniteDistribution.mass_eq_zero_of_not_mem_support P x hx)
      (ne_of_gt h_mass_pos)
  obtain ⟨d0, hd0_def, hd0_le⟩ := h_gate P x k h_prob h_supp h_k_lower h_k_upper beta h_def_P
  let A := levelSet P k
  have hA : A.Nonempty := levelSet_nonempty_of_mass_ge P x k h_supp h_k_lower
  obtain ⟨j, hj_lower, hj_upper⟩ := exists_card_dyadic_bracket A hA
  let i := (setComplexity U A hA).toNat
  let kx := (KPPlain U x).toNat
  let delta := i + j - kx
  -- Use the minimal valid deficiency. The uniform model's deficiency is closed below
  -- by combining the level-set bound `d0` with the `delta + c_soi` bound from SOI.
  let d := min d0 (delta + c_soi)
  use A, hA, delta, i, j, kx, d
  have hi_eq : setComplexity U A hA = (i : ENat) :=
    (ENat.coe_toNat (setComplexity_ne_top_of_optimal U hU A hA)).symm
  have hkx_eq : (kx : ENat) = KPPlain U x :=
    ENat.coe_toNat (KPPlain_ne_top_of_optimal U hU x)
  have h_realized : RealizedSetOptimalityGap U A hA x delta i j kx :=
    ⟨mem_levelSet h_supp h_k_lower, hi_eq, hj_upper, hj_lower, hkx_eq, rfl⟩
  -- The `delta + c_soi` deficiency bound from Symmetry of Information.
  have h_def_soi :
      CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x
        (delta + c_soi) := by
    unfold CodedFiniteDistribution.DeficiencyLe
    have h_mass : (codedUniformOn A hA).mass x = ((A.card : ℝ≥0∞)⁻¹) :=
      codedUniformOn_mass_of_mem _ _ _ (mem_levelSet h_supp h_k_lower)
    rw [h_mass]
    have h_soi_bound := h_soi A hA x (mem_levelSet h_supp h_k_lower)
    have h_i : (setComplexity U A hA).toNat = i := by
      have h : setComplexity U A hA = (i : ENat) := hi_eq
      rw [h, ENat.toNat_coe]
    have h_kx : (KPPlain U x).toNat = kx := by
      have h : KPPlain U x = (kx : ENat) := hkx_eq.symm
      rw [h, ENat.toNat_coe]
    rw [h_i, h_kx] at h_soi_bound
    have h_delta : delta = i + j - kx := rfl
    have h_kp : (KP U x (codedUniformOn A hA).code).toNat + c_soi + delta ≥ j := by omega
    have h4 : ((2 : ℝ≥0∞) ^ j)⁻¹ ≤ (A.card : ℝ≥0∞)⁻¹ := by
      apply ENNReal.inv_le_inv.mpr
      exact_mod_cast hj_upper
    have hkp_eq : complexityWeight (KP U x (codedUniformOn A hA).code) = (2 : ℝ≥0∞)⁻¹ ^
        (KP U x (codedUniformOn A hA).code).toNat := by
      have : KP U x (codedUniformOn A hA).code =
          ((KP U x (codedUniformOn A hA).code).toNat : ENat) :=
        (ENat.coe_toNat (KP_ne_top_of_optimal U hU x _)).symm
      rw [this]
      rfl
    rw [hkp_eq]
    have h1_inv : (2 : ℝ≥0∞)⁻¹ ^ (KP U x (codedUniformOn A hA).code).toNat =
        ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
      rw [ENNReal.inv_pow]
    rw [h1_inv]
    have h2_pow : (2 : ℝ≥0∞) ^ j ≤ (2 : ℝ≥0∞) ^ (delta + c_soi) * (2 : ℝ≥0∞) ^
        (KP U x (codedUniformOn A hA).code).toNat := by
      rw [← pow_add]
      apply pow_le_pow_right' (by norm_num)
      omega
    have h3_inv :
        ((2 : ℝ≥0∞) ^ (delta + c_soi) * (2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ ≤
        ((2 : ℝ≥0∞) ^ j)⁻¹ := by
      apply ENNReal.inv_le_inv.mpr
      exact h2_pow
    have h4_inv :
        ((2 : ℝ≥0∞) ^ (delta + c_soi) * (2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ =
        ((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹ *
        ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
      exact ENNReal.mul_inv (by norm_num) (by norm_num)
    have h6 : ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ ≤ (2 : ℝ≥0∞) ^
        (delta + c_soi) * ((2 : ℝ≥0∞) ^ j)⁻¹ := by
      calc ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹
        _ = 1 * ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by rw [one_mul]
        _ = ((2 : ℝ≥0∞) ^ (delta + c_soi) * ((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹) *
            ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
          have : (2 : ℝ≥0∞) ^ (delta + c_soi) *
              ((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹ = 1 :=
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          rw [this]
        _ = (2 : ℝ≥0∞) ^ (delta + c_soi) *
            (((2 : ℝ≥0∞) ^ (delta + c_soi))⁻¹ *
              ((2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹) := by
                rw [mul_assoc]
        _ = (2 : ℝ≥0∞) ^ (delta + c_soi) *
            ((2 : ℝ≥0∞) ^ (delta + c_soi) *
              (2 : ℝ≥0∞) ^ (KP U x (codedUniformOn A hA).code).toNat)⁻¹ := by
                rw [h4_inv]
        _ ≤ (2 : ℝ≥0∞) ^ (delta + c_soi) * ((2 : ℝ≥0∞) ^ j)⁻¹ := by gcongr
    exact le_trans h6 (mul_le_mul_right h4 _)
  -- `d` satisfies the deficiency bound by taking the minimum.
  have h_def_d : CodedFiniteDistribution.DeficiencyLe U (codedUniformOn A hA) x d := by
    unfold CodedFiniteDistribution.DeficiencyLe at *
    change complexityWeight (KP U x (codedUniformOn A hA).code) ≤
      2 ^ (min d0 (delta + c_soi)) * (codedUniformOn A hA).mass x
    by_cases h_min : d0 ≤ delta + c_soi
    · rw [Nat.min_eq_left h_min]
      exact hd0_def
    · rw [Nat.min_eq_right (le_of_not_ge h_min)]
      exact h_def_soi
  -- GATE (closed): randomness deficiency never exceeds the optimality gap plus SOI constant.
  have h_d_le_delta : d ≤ delta +
      (c_lb + C2 + C3 + Csum + bsum + c_gate + c_comp + c_len + c_plain + c_soi + 100) := by
    have h_min : d ≤ delta + c_soi := Nat.min_le_right _ _
    omega
  -- GATE (closed): the level set is no more complex than `P`, `i ≤ alpha + O(log)`.
  -- From `levelSetModel_setComplexity_le` (`setComplexity A ≤ P.complexity + O(log k)`),
  -- `h_comp_P` (`P.complexity ≤ alpha`), and the level bound `k ≤ n + alpha + beta + O(log)`.
  -- The level bound `k ≤ n + beta + O(log n)` and its fold to the visible budget `M`.
  set W := c_lb + C2 + C3 + Csum + bsum + c_gate + c_comp + c_len + c_plain + c_soi + 100 with hW
  have hk_bd : k ≤ n + beta + logSlack c_lb n := h_lb P x n beta k h_len_x h_def_P h_k_upper
  -- `i ≤ alpha + O(log)` (Gate: level set no more complex than `P`).
  have h_i_raw : (i : ℕ) ≤ alpha + logSlack c_comp k := by
    have h1 : setComplexity U A hA ≤ (alpha : ENat) + (logSlack c_comp k : ENat) := by
      refine le_trans (h_comp P k hA) ?_
      gcongr
    rw [hi_eq] at h1
    exact_mod_cast h1
  have h_i_bound : i ≤ alpha + logSlack W (n + alpha + beta) := by
    have hfold : logSlack c_comp k ≤ logSlack W (n + alpha + beta) :=
      le_trans (hC2 n alpha beta k hk_bd) (logSlack_mono_left (by omega) _)
    omega
  -- `d = min d0 (delta + c_soi) ≤ d0 ≤ beta + O(log)`.
  have h_d_bound : d ≤ beta + logSlack W (n + alpha + beta) := by
    have hfold : logSlack c_gate k ≤ logSlack W (n + alpha + beta) :=
      le_trans (hC3 n alpha beta k hk_bd) (logSlack_mono_left (by omega) _)
    have : d ≤ beta + logSlack c_gate k := le_trans (Nat.min_le_left _ _) hd0_le
    omega
  -- Linear budget control.  Bound `j ≤ k + 1` from the dyadic bracket and
  -- `levelSet_card_le`, then collect *all* the logarithmic overhead
  -- (`logSlack c_comp k + logSlack c_gate k + logSlack c_lb n`) into a single
  -- log-slack at the visible budget and convert it to `≤ M + bsum`.
  have hj_k : j ≤ k + 1 := by
    have hcard_k : A.card ≤ 2 ^ k := by
      have h := levelSet_card_le P k h_prob
      exact_mod_cast h
    have hj2 : 2 ^ j ≤ 2 * A.card := by
      have h := hj_lower
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)] at h
      have h' : (2 : ℝ≥0∞) ^ j ≤ ((2 * A.card : ℕ) : ℝ≥0∞) := by
        push_cast; simpa [mul_comm] using h
      exact_mod_cast h'
    have hpow : 2 ^ j ≤ 2 ^ (k + 1) := by
      calc 2 ^ j ≤ 2 * A.card := hj2
        _ ≤ 2 * 2 ^ k := by gcongr
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow
  have hd : d ≤ beta + logSlack c_gate k := le_trans (Nat.min_le_left _ _) hd0_le
  have hsum :
      logSlack c_comp k + logSlack c_gate k + logSlack c_lb n
        ≤ (n + alpha + beta) + bsum := by
    calc logSlack c_comp k + logSlack c_gate k + logSlack c_lb n
        = logSlack (c_comp + c_gate) k + logSlack c_lb n := by
          rw [logSlack_add_const]
      _ ≤ logSlack Csum (n + alpha + beta) + logSlack c_lb (n + alpha + beta) := by
          gcongr
          · exact hCsum n alpha beta k hk_bd
          · exact logSlack_mono_right c_lb (by omega)
      _ = logSlack (Csum + c_lb) (n + alpha + beta) := by rw [logSlack_add_const]
      _ ≤ (n + alpha + beta) + bsum := hbsum (n + alpha + beta)
  have h_linear : n + delta + d ≤ 4 * (n + alpha + beta) + W := by
    have hdelta : delta ≤ i + j := Nat.sub_le _ _
    omega
  exact ⟨h_realized, h_def_d, h_d_le_delta, h_i_bound, h_d_bound, h_linear⟩

/-
Theorem 3: Stochasticity to Optimal Set Model.
This is the main direction of the deficiency theorem chain. It converts
an arbitrary stochasticity witness into an optimal finite set witness.

Assembled from the distribution-to-uniform-set bridge
`exists_realizedGap_uniformSet_of_stochastic` and the fully-proved tight
deficiencies theorem `deficiencies_theorem_tight_of_optimal`.
-/
theorem stochasticity_to_optimal_set_thm (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString, ∀ n alpha beta : ℕ,
      x.length = n →
      IsStochastic U x alpha beta →
      IsOptimalSetStochastic U x (alpha + logSlack c (n + alpha + beta))
          (beta + logSlack c (n + alpha + beta)) := by
  obtain ⟨c_def, hc_def⟩ := deficiencies_theorem_tight_thm U hU
  obtain ⟨c_br, hc_br⟩ := exists_realizedGap_uniformSet_of_stochastic U hU
  obtain ⟨C0, hC0⟩ := logSlack_linear_bound c_def 4 c_br
  refine ⟨max (c_br + C0) (c_def + c_br + 1) + 1, ?_⟩
  intro x n alpha beta hn hst
  obtain ⟨A, hA, delta, i, j, kx, d, hgap, hdef, hdd, hi, hd, hlin⟩ := hc_br x n alpha beta hn hst
  obtain ⟨B, hB, hxB, hcompB, hoptB⟩ := hc_def A hA x n delta d i j kx c_br hn hgap hdef hdd
  have hlogSlack : logSlack c_def (n + delta + d) ≤ logSlack C0 (n + alpha + beta) :=
    le_trans (logSlack_mono_right _ hlin) (hC0 _)
  have hcompA : setComplexity U A hA = (i : ENat) := hgap.2.1
  -- Both `O(log)` slacks fold into the single final constant.
  have hslack : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
      ≤ logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by
    have h1 : logSlack c_br (n + alpha + beta) + logSlack C0 (n + alpha + beta)
        ≤ logSlack (c_br + C0 + 1) (n + alpha + beta) := by
      unfold logSlack; ring_nf; linarith
    exact le_trans h1 (logSlack_mono_left (Nat.succ_le_succ (le_max_left _ _)) _)
  refine ⟨B, hB, hxB, ?_, ?_⟩
  · rw [hcompA] at hcompB
    have hcompB' : setComplexity U B hB ≤ (i : ENat) + (logSlack c_def (n + delta + d) : ENat) :=
      le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hcompB
    refine le_trans hcompB' ?_
    have hnat : i + logSlack c_def (n + delta + d)
        ≤ alpha + logSlack (max (c_br + C0) (c_def + c_br + 1) + 1) (n + alpha + beta) := by
      omega
    exact_mod_cast hnat
  · refine hoptB.mono_beta ?_
    omega

end Kolmogorov
