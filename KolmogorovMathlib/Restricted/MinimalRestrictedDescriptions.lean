/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicProbability.CompatibleGraphs
import KolmogorovMathlib.AlgorithmicProbability.HaltingProbabilityApproximation
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part01
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinApplications.Part02
import KolmogorovMathlib.Interface.ComputableReals.LowerSemicomputableReals
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse
import KolmogorovMathlib.Prefix.BlockingReadMachines
import KolmogorovMathlib.Prefix.ExtensionTheorem
import KolmogorovMathlib.Prefix.NumericalValues
import KolmogorovMathlib.Prefix.PairComplexity
import KolmogorovMathlib.Prefix.SelfDelimitingMachines
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.Restricted.HammingGap
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.NonStochasticFinal
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedStochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CubeStochasticity
import KolmogorovMathlib.Restricted.DeficiencyEquiv
import KolmogorovMathlib.MonotoneComplexity.Dimension.ChangeOfMeasure
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyValue
import KolmogorovMathlib.AlgorithmicStatistics.StochasticityProfile
import KolmogorovMathlib.AlgorithmicStatistics.DescriptionProfileInvariance

/-!
# Minimal restricted descriptions

The description profile of a string restricted to a family of descriptions
(`InDescriptionProfileInPre`), and the two improvement steps that such a family
admits when the conditional complexity of the string given the description is
high: the description can be improved in its complexity coordinate
(`descriptionFamily_improves_i_of_high_condK`) and in its size coordinate
(`descriptionFamily_improves_j_of_high_condK`).

SUV Theorem 259, p. 421.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-- The binary size of a sum is at most the sum of the binary sizes. -/
theorem size_add_size_le (A B : ℕ) : (A + B).size ≤ A.size + B.size := by
  by_cases hA : A = 0
  · subst hA; rw [zero_add, Nat.size_zero, zero_add]
  · by_cases hB : B = 0
    · subst hB; rw [add_zero, Nat.size_zero, add_zero]
    · have hA0 : A.size ≠ 0 := fun h => hA (Nat.size_eq_zero.mp h)
      have hB0 : B.size ≠ 0 := fun h => hB (Nat.size_eq_zero.mp h)
      have hA_size : 1 ≤ A.size := Nat.pos_of_ne_zero hA0
      have hB_size : 1 ≤ B.size := Nat.pos_of_ne_zero hB0
      have h1 : 2 ≤ 2 ^ A.size := Nat.pow_le_pow_right (by decide : 0 < 2) hA_size
      have h2 : 2 ≤ 2 ^ B.size := Nat.pow_le_pow_right (by decide : 0 < 2) hB_size
      have h_sum : A + B < 2 ^ (A.size + B.size) := by
        calc A + B < 2 ^ A.size + 2 ^ B.size := by
               have hA_lt := Nat.lt_size_self A
               have hB_lt := Nat.lt_size_self B
               omega
             _ ≤ 2 ^ A.size * 2 ^ B.size := by nlinarith
             _ = 2 ^ (A.size + B.size) := by rw [pow_add]
      exact Nat.size_le.mpr h_sum

/-! ### Theorem 259: minimal restricted descriptions are simple given `x` -/

/-- The restricted description profile of a family satisfying only condition (1)
(an enumerable family of nonempty finite sets). -/
noncomputable def InDescriptionProfileInPre (𝒜 : PreDescriptionFamily) (U : Map)
    (x : BitString) (i j : ℕ) : Prop :=
  ∃ (S : Finset BitString) (hS : S.Nonempty), 𝒜.mem S ∧ IsIJDescription U x S hS i j

/-- The plain complexity `kx = (KPPlain U x).toNat` of a string `x` of length `n` with an
`(i, j)`-description `A` is bounded by `i + n + 2 * (Nat.bits n).length + c_k`. -/
private theorem high_condK_kx_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) (n i : ℕ) (A : Finset BitString) (hA : A.Nonempty)
    (hx : x.length = n) (hcompA : setComplexity U A hA ≤ (i : ENat))
    (c_sub c_plain c_len c_k : ℕ)
    (hc_len : ∀ x : BitString, KPPlain U x ≤
      (x.length : ENat) + 2 * ((Nat.bits x.length).length : ENat) + (c_len : ENat))
    (hc_plain : ∀ x y : BitString, KP U x y ≤ KPPlain U x + (c_plain : ENat))
    (h_sub : ∀ x y : BitString, KPPlain U x ≤ KPPlain U y + KP U x y + (c_sub : ENat))
    (hc_k : c_sub + c_plain + c_len + 1 ≤ c_k) :
    (KPPlain U x).toNat ≤ i + n + 2 * (Nat.bits n).length + c_k := by
  have hkx_ne_top : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
  set kx := (KPPlain U x).toNat
  have hkx_eq : (kx : ENat) = KPPlain U x := ENat.natCast_toNat hkx_ne_top
  have h_len_x : KPPlain U x ≤
      (n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len : ENat) := by
    have h0 := hc_len x
    rw [hx] at h0
    exact h0
  have h_cond : KP U x (codedUniformOn A hA).code ≤
      (n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len + c_plain : ENat) := by
    have h0 := hc_plain x (codedUniformOn A hA).code
    have h1 : KPPlain U x + (c_plain : ENat) ≤
        (n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len : ENat) + (c_plain : ENat) :=
      add_le_add_left h_len_x (c_plain : ENat)
    have h2 : (n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len : ENat) + (c_plain : ENat) =
        (n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len + c_plain : ENat) := by
      ring
    exact h0.trans (h1.trans (by rw [h2]))
  have h_sub_x := h_sub x (codedUniformOn A hA).code
  have h_sub_le : setComplexity U A hA + KP U x (codedUniformOn A hA).code + (c_sub : ENat) ≤
      (i : ENat) + ((n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len + c_plain : ENat)) +
        (c_sub : ENat) := by
    have h0 : setComplexity U A hA + KP U x (codedUniformOn A hA).code ≤
        (i : ENat) + ((n : ENat) + 2 * ((Nat.bits n).length : ENat) + (c_len + c_plain : ENat)) :=
      add_le_add hcompA h_cond
    exact add_le_add_left h0 (c_sub : ENat)
  have h_kx_enat : (kx : ENat) ≤ ((i + n + 2 * (Nat.bits n).length + c_k : ℕ) : ENat) := by
    have h_ring : (i : ENat) + ((n : ENat) + 2 * ((Nat.bits n).length : ENat) +
          (c_len + c_plain : ENat)) + (c_sub : ENat) =
        ((i + n + 2 * (Nat.bits n).length + (c_len + c_plain + c_sub) : ℕ) : ENat) := by
      push_cast; ring
    have h_step := h_sub_x.trans (h_sub_le.trans (by rw [h_ring]))
    rw [hkx_eq]
    refine h_step.trans ?_
    gcongr
    omega
  exact_mod_cast h_kx_enat

/-- **Theorem 259, first part** (with the sign of the conditional-complexity
hypothesis corrected: the relevant condition is *high* conditional complexity).
Let `𝒜` be an enumerable family of finite sets.  If `x` has an
`(i * j)`-description `A ∈ 𝒜` whose conditional complexity `K(A | x)` is at least
`k`, then `x` has an `((i - k) * j)`-description in `𝒜`. -/
theorem descriptionFamily_improves_i_of_high_condK (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ) (A : Finset BitString) (hA : A.Nonempty),
      x.length = n → 𝒜.mem A → IsIJDescription U x A hA i j →
      (k : ℕ∞) ≤ KP U (codedUniformOn A hA).code x →
      InDescriptionProfileInPre 𝒜 U x
        (i - k + logSlack c (n + i + j + k)) (j + logSlack c (n + i + j + k)) := by
  obtain ⟨c_count, hc_count⟩ :=
    restricted_description_count_of_conditional_complexity_gap_aux U hU 𝒜
  obtain ⟨c_ctx, hc_ctx⟩ := KP_le_prefixComplexityContext_add_logSlack U hU
  obtain ⟨c_sel, hc_sel⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  set c_k := c_sub + c_plain + c_len + c_count + 1
  obtain ⟨C_ctx, hC_ctx⟩ := logSlack_linear_bound c_ctx 3 (c_k + 1)
  set c := c_count + C_ctx + c_sel + 1
  refine ⟨c, fun x n i j k A hA hx hmem hdesc hk_cond => ?_⟩
  rcases hdesc with ⟨hxA, hcompA, hcardA⟩
  have hkx_ne_top : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
  set kx := (KPPlain U x).toNat
  have hkx_eq : (kx : ENat) = KPPlain U x := ENat.natCast_toNat hkx_ne_top
  have hkx : HasPrefixComplexityValue U x kx := by
    dsimp [HasPrefixComplexityValue]
    exact ENat.natCast_toNat hkx_ne_top
  set s := logSlack c_count (n + i + j) + logSlack c_ctx (kx + 1) + 1
  have hkx_le : kx ≤ i + n + 2 * (Nat.bits n).length + c_k :=
    high_condK_kx_bound U hU x n i A hA hx hcompA c_sub c_plain c_len c_k
      hc_len hc_plain h_sub (by omega)
  have hkx1 : kx + 1 ≤ 3 * (n + i + j + k) + (c_k + 1) := by
    have h_bits_n : (Nat.bits n).length ≤ n := length_natBits_le n
    dsimp [c_k] at hkx_le ⊢
    omega
  have h_ctx1 : logSlack c_ctx (kx + 1) ≤ logSlack C_ctx (n + i + j + k) :=
    (logSlack_mono_right c_ctx hkx1).trans (hC_ctx (n + i + j + k))
  have hs_bound : s ≤ logSlack (c_count + C_ctx + 1) (n + i + j + k) := by
    dsimp [s]
    have h1 : logSlack c_count (n + i + j) ≤ logSlack c_count (n + i + j + k) :=
      logSlack_mono_right c_count (by omega)
    have h2 : logSlack c_count (n + i + j + k) + logSlack C_ctx (n + i + j + k) =
        logSlack (c_count + C_ctx) (n + i + j + k) :=
      logSlack_add_const c_count C_ctx (n + i + j + k)
    have h3 : logSlack (c_count + C_ctx) (n + i + j + k) + 1 ≤
        logSlack (c_count + C_ctx + 1) (n + i + j + k) :=
      logSlack_add_const_le (c_count + C_ctx) 1 (n + i + j + k)
    omega
  by_cases hsk : k ≤ s
  · refine ⟨A, hA, hmem, hxA, ?_, ?_⟩
    · have hkL : k ≤ logSlack c (n + i + j + k) :=
        hsk.trans (hs_bound.trans (logSlack_mono_left (by dsimp [c]; omega) _))
      have h1 : i ≤ i - k + logSlack c (n + i + j + k) := by
        by_cases hik : k ≤ i <;> omega
      exact hcompA.trans (by exact_mod_cast h1)
    · have h1 : j ≤ j + logSlack c (n + i + j + k) := by omega
      exact hcardA.trans (Nat.pow_le_pow_right (by decide) h1)
  · have hks : s < k := by omega
    set k' := min (k - s) i
    have hk_le_i : k' ≤ i := Nat.min_le_right _ _
    by_cases h_many : ManyIJDescriptionsIn 𝒜 U x i j k'
    · obtain ⟨S, hS, hmemS, hxS, hcompS, hcardS⟩ :=
        hc_sel x n i j k' hx h_many hk_le_i
      refine ⟨S, hS, hmemS, ⟨hxS, ?_, ?_⟩⟩
      · have hsub : i - k' + logSlack c_sel (n + i + j)
            ≤ i - k + logSlack c (n + i + j + k) := by
          have hs_sel : s + logSlack c_sel (n + i + j) ≤ logSlack c (n + i + j + k) := by
            have h1 : logSlack c_sel (n + i + j) ≤ logSlack c_sel (n + i + j + k) :=
              logSlack_mono_right c_sel (by omega)
            have h2 : logSlack (c_count + C_ctx + 1) (n + i + j + k) +
                logSlack c_sel (n + i + j + k) =
                logSlack (c_count + C_ctx + 1 + c_sel) (n + i + j + k) :=
              logSlack_add_const (c_count + C_ctx + 1) c_sel (n + i + j + k)
            have h3 : logSlack (c_count + C_ctx + 1 + c_sel) (n + i + j + k) ≤
                logSlack c (n + i + j + k) :=
              logSlack_mono_left (by dsimp [c]; omega) (n + i + j + k)
            linarith [hs_bound, h1, h2, h3]
          dsimp [k']
          omega
        exact hcompS.trans (by exact_mod_cast hsub)
      · have hcard_le : j + logSlack c_sel (n + i + j) ≤ j + logSlack c (n + i + j + k) := by
          have h1 : logSlack c_sel (n + i + j) ≤ logSlack c (n + i + j + k) := by
            exact (logSlack_le_logSlack_add_right c_sel (n + i + j) k).trans
              (logSlack_mono_left (by dsimp [c]; omega) _)
          omega
        exact hcardS.trans (Nat.pow_le_pow_right (by decide) hcard_le)
    · have h_not_many : ¬ ManyIJDescriptionsIn 𝒜 U x i j (k - s) := fun h =>
        h_many (ManyIJDescriptionsIn.mono_k h (Nat.min_le_left _ _))
      have hbound := hc_count A hA x n i j (k - s) kx hx hmem hxA hcompA hcardA hkx h_not_many
      have hctx := hc_ctx (codedUniformOn A hA).code x kx
      have h1 : (k : ENat) ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
            (logSlack c_ctx (kx + 1) : ENat) := hk_cond.trans hctx
      have h2 : KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
          ((k - s : ℕ) : ENat) + (logSlack c_count (n + i + j) : ENat) := hbound
      have h2' : KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
          (logSlack c_ctx (kx + 1) : ENat) ≤ ((k - s : ℕ) : ENat) +
          (logSlack c_count (n + i + j) : ENat) + (logSlack c_ctx (kx + 1) : ENat) := by
        gcongr
      have h3 : (k : ENat) ≤ ((k - s : ℕ) : ENat) + (logSlack c_count (n + i + j) : ENat) +
          (logSlack c_ctx (kx + 1) : ENat) :=
        h1.trans h2'
      have h_arith : (k - s) + logSlack c_count (n + i + j) + logSlack c_ctx (kx + 1) =
          (k - s) + (s - 1) := by dsimp [s]; omega
      have h_comb : (k : ENat) ≤ (((k - s) + (s - 1) : ℕ) : ENat) := by
        have h3' : (k : ENat) ≤ (((k - s) + logSlack c_count (n + i + j) +
            logSlack c_ctx (kx + 1) : ℕ) : ENat) := by
          push_cast
          exact h3
        rw [h_arith] at h3'
        exact h3'
      have h_lt : (k - s) + (s - 1) < k := by omega
      have h4 : (((k - s) + (s - 1) : ℕ) : ENat) < (k : ENat) := by exact_mod_cast h_lt
      exact False.elim (lt_irrefl (k : ENat) (h_comb.trans_lt h4))

/-- If `KP(A|x) ≥ k` for an `(i, j)`-description `A` of `x`, then `k` is bounded by `i + s + 1`,
where `s` is the log-slack upper bound. -/
private theorem high_condK_k_le_i_add_s (U : Map) (𝒜 : PreDescriptionFamily)
    (c_count c_ctx kx n i j k : ℕ) (x : BitString) (A : Finset BitString) (hA : A.Nonempty)
    (hx : x.length = n) (hmem : 𝒜.mem A) (hdesc : IsIJDescription U x A hA i j)
    (hkx : HasPrefixComplexityValue U x kx)
    (hc_count : ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n i j m kx : ℕ),
      x.length = n → 𝒜.mem A → x ∈ A → setComplexity U A hA ≤ (i : ENat) → A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx → ¬ ManyIJDescriptionsIn 𝒜 U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
        (m + logSlack c_count (n + i + j) : ENat))
    (hc_ctx : ∀ (c x : BitString) (kx : ℕ),
      KP U c x ≤ KP U c (prefixComplexityContext x kx) + (logSlack c_ctx (kx + 1) : ENat))
    (hk_cond : (k : ℕ∞) ≤ KP U (codedUniformOn A hA).code x) :
    k ≤ i + (logSlack c_count (n + i + j) + logSlack c_ctx (kx + 1) + 1) + 1 := by
  set s := logSlack c_count (n + i + j) + logSlack c_ctx (kx + 1) + 1 with hs
  by_cases hsk : k ≤ i + s + 1
  · exact hsk
  · have hks : i + s + 1 < k := by omega
    have h_not_many : ¬ ManyIJDescriptionsIn 𝒜 U x i j (k - s) := fun h => by
      have := manyIJDescriptionsIn_k_le_i_add_one h
      omega
    rcases hdesc with ⟨hxA, hcompA, hcardA⟩
    have hbound := hc_count A hA x n i j (k - s) kx hx hmem hxA hcompA hcardA hkx h_not_many
    have hctx := hc_ctx (codedUniformOn A hA).code x kx
    have h1 : (k : ENat) ≤ KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
          (logSlack c_ctx (kx + 1) : ENat) := hk_cond.trans hctx
    have h2 : KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) ≤
        ((k - s : ℕ) : ENat) + (logSlack c_count (n + i + j) : ENat) := hbound
    have h2' : KP U (codedUniformOn A hA).code (prefixComplexityContext x kx) +
        (logSlack c_ctx (kx + 1) : ENat) ≤ ((k - s : ℕ) : ENat) +
        (logSlack c_count (n + i + j) : ENat) + (logSlack c_ctx (kx + 1) : ENat) := by
      gcongr
    have h3 : (k : ENat) ≤ ((k - s : ℕ) : ENat) + (logSlack c_count (n + i + j) : ENat) +
        (logSlack c_ctx (kx + 1) : ENat) :=
      h1.trans h2'
    have h_arith : (k - s) + logSlack c_count (n + i + j) + logSlack c_ctx (kx + 1) =
        (k - s) + (s - 1) := by omega
    have h_comb : (k : ENat) ≤ (((k - s) + (s - 1) : ℕ) : ENat) := by
      have h3' : (k : ENat) ≤ (((k - s) + logSlack c_count (n + i + j) +
          logSlack c_ctx (kx + 1) : ℕ) : ENat) := by
        push_cast
        exact h3
      rw [h_arith] at h3'
      exact h3'
    have h_lt : (k - s) + (s - 1) < k := by omega
    have h4 : (((k - s) + (s - 1) : ℕ) : ENat) < (k : ENat) := by exact_mod_cast h_lt
    exact False.elim (lt_irrefl (k : ENat) (h_comb.trans_lt h4))

/-- Polynomial overhead bound for description family size shifts. -/
private theorem descriptionFamily_overhead_shift_bound (𝒜 : DescriptionFamily)
    (c_oh c_shift n i j k m : ℕ) (hmk : m ≤ k)
    (hc_oh : ∀ n, (Nat.bits (𝒜.overhead n)).length ≤ logSlack c_oh n) :
    logSlack c_shift (n + m + 𝒜.overhead n) ≤
      logSlack (c_shift * (c_oh + 1) + c_shift * c_oh + c_shift) (n + i + j + k) := by
  have h_nm : (Nat.bits (n + m)).length ≤ (Nat.bits (n + i + j + k)).length :=
    length_natBits_mono (by omega)
  have h_oh_le : (Nat.bits (𝒜.overhead n)).length ≤ logSlack c_oh n := hc_oh n
  have h_oh_M : logSlack c_oh n ≤ logSlack c_oh (n + i + j + k) :=
    logSlack_mono_right c_oh (by omega)
  have h_oh : (Nat.bits (𝒜.overhead n)).length ≤ logSlack c_oh (n + i + j + k) :=
    h_oh_le.trans h_oh_M
  have h_sum_size : (Nat.bits (n + m + 𝒜.overhead n)).length ≤
      (Nat.bits (n + m)).length + (Nat.bits (𝒜.overhead n)).length := by
    simpa [← Nat.size_eq_bits_len] using size_add_size_le (n + m) (𝒜.overhead n)
  dsimp [logSlack]
  dsimp [logSlack] at h_oh
  nlinarith [h_sum_size, h_nm, h_oh]

/-- Linear slack upper bound for the complexity coordinate in `descriptionFamily_improves_j`. -/
private theorem descriptionFamily_improves_j_comp_bound (c_i C_shift c_count C_ctx
    c_shift : ℕ) (𝒜 : DescriptionFamily) (n i j k m s : ℕ) (h_m_le : m ≤ k)
    (hk_le_is : k ≤ i + s + 1)
    (hs_bound : s ≤ logSlack (c_count + C_ctx + 1) (n + i + j + k))
    (h_shift_bound :
      logSlack c_shift (n + m + 𝒜.overhead n) ≤ logSlack C_shift (n + i + j + k)) :
    i - k + logSlack c_i (n + i + j + k) + m + logSlack c_shift (n + m + 𝒜.overhead n) ≤
      i + logSlack (c_i + C_shift + (c_count + C_ctx + 2)) (n + i + j + k) := by
  set s_const := c_count + C_ctx + 2 with hs_const_eq
  have hs_const : c_count + C_ctx + 2 ≤ s_const := hs_const_eq.ge
  set c := c_i + C_shift + s_const with hc_eq
  have hc : c_i + C_shift + s_const ≤ c := hc_eq.ge
  have h_sum1 : logSlack c_i (n + i + j + k) + logSlack C_shift (n + i + j + k) =
      logSlack (c_i + C_shift) (n + i + j + k) :=
    logSlack_add_const c_i C_shift (n + i + j + k)
  have h_sum2 : logSlack (c_i + C_shift) (n + i + j + k) + logSlack s_const (n + i + j + k) =
      logSlack (c_i + C_shift + s_const) (n + i + j + k) :=
    logSlack_add_const (c_i + C_shift) s_const (n + i + j + k)
  have h_mono : logSlack (c_i + C_shift + s_const) (n + i + j + k) ≤
      logSlack c (n + i + j + k) :=
    logSlack_mono_left hc (n + i + j + k)
  have h_m_bound : i - k + m ≤ i + logSlack s_const (n + i + j + k) := by
    by_cases hik : k ≤ i
    · omega
    · have : i - k = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [this, zero_add]
      have h_s1 : s + 1 ≤ logSlack s_const (n + i + j + k) := by
        have h_step : logSlack (c_count + C_ctx + 1) (n + i + j + k) + 1 ≤
            logSlack (c_count + C_ctx + 2) (n + i + j + k) :=
          logSlack_add_const_le (c_count + C_ctx + 1) 1 _
        have h_s2 : logSlack (c_count + C_ctx + 2) (n + i + j + k) ≤
            logSlack s_const (n + i + j + k) :=
          logSlack_mono_left hs_const _
        linarith [hs_bound, h_step, h_s2]
      linarith [h_m_le, hk_le_is, h_s1]
  linarith [h_shift_bound, h_sum1, h_sum2, h_mono, h_m_bound]

/-- Upper bound for the set size exponent in `descriptionFamily_improves_j`. -/
private theorem descriptionFamily_improves_j_card_bound (c_i c n i j k : ℕ)
    (hc : c_i ≤ c) :
    j + logSlack c_i (n + i + j + k) - min k (j + logSlack c_i (n + i + j + k)) ≤
      j - k + logSlack c (n + i + j + k) := by
  have h_c_le : logSlack c_i (n + i + j + k) ≤ logSlack c (n + i + j + k) :=
    logSlack_mono_left hc _
  set j' := j + logSlack c_i (n + i + j + k)
  by_cases hkj : k ≤ j
  · have : min k j' = k := Nat.min_eq_left (by omega)
    rw [this]
    omega
  · by_cases hkj' : k ≤ j'
    · have : min k j' = k := Nat.min_eq_left hkj'
      rw [this]
      have : j - k = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [this, zero_add]
      omega
    · have : min k j' = j' := Nat.min_eq_right (by omega)
      rw [this, tsub_self]
      exact zero_le

/-- **Theorem 259, second part.** If in addition the family satisfies condition
(3) (the covering condition, part of `DescriptionFamily`), then `x` has an
`(i * (j - k))`-description in the family. -/
theorem descriptionFamily_improves_j_of_high_condK (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily)
    (hpoly : 𝒜.HasPolynomialOverhead) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ) (A : Finset BitString) (hA : A.Nonempty),
      x.length = n → 𝒜.mem A → IsIJDescription U x A hA i j →
      (k : ℕ∞) ≤ KP U (codedUniformOn A hA).code x →
      InDescriptionProfileIn 𝒜 U x
        (i + logSlack c (n + i + j + k)) (j - k + logSlack c (n + i + j + k)) := by
  obtain ⟨c_count, hc_count⟩ :=
    restricted_description_count_of_conditional_complexity_gap_aux U hU 𝒜.toPre
  obtain ⟨c_ctx, hc_ctx⟩ := KP_le_prefixComplexityContext_add_logSlack U hU
  obtain ⟨c_i, hc_i⟩ := descriptionFamily_improves_i_of_high_condK U hU 𝒜.toPre
  obtain ⟨c_shift, hc_shift⟩ := inDescriptionProfileIn_improving_size U hU 𝒜
  obtain ⟨c_oh, hc_oh⟩ := 𝒜.overhead_bits_le_logSlack hpoly
  obtain ⟨c_sub, h_sub⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨c_plain, hc_plain⟩ := KP_le_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  set c_k := c_sub + c_plain + c_len + c_count + 1
  obtain ⟨C_ctx, hC_ctx⟩ := logSlack_linear_bound c_ctx 3 (c_k + 1)
  set s_const := c_count + C_ctx + 2
  set C_shift := c_shift * (c_oh + 1) + c_shift * c_oh + c_shift
  set c := c_i + C_shift + s_const + 20
  refine ⟨c, fun x n i j k A hA hx hmem hdesc hk_cond => ?_⟩
  rcases hdesc with ⟨hxA, hcompA, hcardA⟩
  have hkx_ne_top : KPPlain U x ≠ ⊤ := KPPlain_ne_top_of_optimal U hU x
  set kx := (KPPlain U x).toNat
  have hkx_eq : (kx : ENat) = KPPlain U x := ENat.natCast_toNat hkx_ne_top
  have hkx : HasPrefixComplexityValue U x kx := by
    dsimp [HasPrefixComplexityValue]
    exact ENat.natCast_toNat hkx_ne_top
  set s := logSlack c_count (n + i + j) + logSlack c_ctx (kx + 1) + 1
  obtain ⟨S', hS', hmemS', hxS', hcompS', hcardS'⟩ :=
    hc_i x n i j k A hA hx hmem ⟨hxA, hcompA, hcardA⟩ hk_cond
  have hprofS' : InDescriptionProfileIn 𝒜 U x
      (i - k + logSlack c_i (n + i + j + k)) (j + logSlack c_i (n + i + j + k)) :=
    ⟨S', hS', hmemS', ⟨hxS', hcompS', hcardS'⟩⟩
  set j' := j + logSlack c_i (n + i + j + k)
  set m := min k j'
  have hmk : m ≤ j' := Nat.min_le_right _ _
  have hshift := hc_shift x n (i - k + logSlack c_i (n + i + j + k)) j' m hx hprofS' hmk
  obtain ⟨S_res, hS_res, hmem_res, hx_res, hcomp_res, hcard_res⟩ := hshift
  refine ⟨S_res, hS_res, hmem_res, ⟨hx_res, ?_, ?_⟩⟩
  · have h_m_le : m ≤ k := Nat.min_le_left _ _
    have h_shift_bound := descriptionFamily_overhead_shift_bound 𝒜 c_oh c_shift
      n i j k m h_m_le hc_oh
    have hk_le_is := high_condK_k_le_i_add_s U 𝒜.toPre c_count c_ctx kx n i j k x A hA
      hx hmem ⟨hxA, hcompA, hcardA⟩ hkx hc_count hc_ctx hk_cond
    have hkx_le : kx ≤ i + n + 2 * (Nat.bits n).length + c_k :=
      high_condK_kx_bound U hU x n i A hA hx hcompA c_sub c_plain c_len c_k
        hc_len hc_plain h_sub (by omega)
    have hkx1 : kx + 1 ≤ 3 * (n + i + j + k) + (c_k + 1) := by
      have h_bits_n : (Nat.bits n).length ≤ n := length_natBits_le n
      dsimp [c_k] at hkx_le ⊢
      omega
    have hs_bound : s ≤ logSlack (c_count + C_ctx + 1) (n + i + j + k) := by
      dsimp [s]
      have h1 : logSlack c_count (n + i + j) ≤ logSlack c_count (n + i + j + k) :=
        logSlack_mono_right c_count (by omega)
      have h2 : logSlack c_ctx (kx + 1) ≤ logSlack C_ctx (n + i + j + k) :=
        (logSlack_mono_right c_ctx hkx1).trans (hC_ctx (n + i + j + k))
      have h3 : logSlack c_count (n + i + j + k) + logSlack C_ctx (n + i + j + k) =
          logSlack (c_count + C_ctx) (n + i + j + k) :=
        logSlack_add_const c_count C_ctx (n + i + j + k)
      have h4 : logSlack (c_count + C_ctx) (n + i + j + k) + 1 ≤
          logSlack (c_count + C_ctx + 1) (n + i + j + k) :=
        logSlack_add_const_le (c_count + C_ctx) 1 (n + i + j + k)
      omega
    have h1 := descriptionFamily_improves_j_comp_bound c_i C_shift c_count C_ctx c_shift 𝒜
      n i j k m s h_m_le hk_le_is hs_bound h_shift_bound
    have hmono : logSlack (c_i + C_shift + (c_count + C_ctx + 2)) (n + i + j + k) ≤
        logSlack c (n + i + j + k) := logSlack_mono_left (by omega) _
    have h1' : i - k + logSlack c_i (n + i + j + k) + m +
        logSlack c_shift (n + m + 𝒜.overhead n) ≤ i + logSlack c (n + i + j + k) := by
      omega
    exact hcomp_res.trans (by exact_mod_cast h1')
  · have h2 := descriptionFamily_improves_j_card_bound c_i c n i j k (by omega)
    exact hcard_res.trans (Nat.pow_le_pow_right (by decide) h2)

end Kolmogorov
