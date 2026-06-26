/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Defs

/-!
# Universal Lower-Semicomputable Semimeasures: Basic API

SUV Chapter 4 defines the universal a priori probability as a maximal
lower-semicomputable semimeasure on strings. The unary interface lives in
`UniversalSemimeasure.Defs`; this file proves the basic closure, domination, and
prefix-complexity facts for that interface.
-/

namespace Kolmogorov

open scoped ENNReal

theorem unaryMixture_isSemimeasure (w : ℕ → ℝ≥0∞)
    (μ : ℕ → BitString → ℝ≥0∞) (hw : (∑' i, w i) ≤ 1)
    (hμ : ∀ i, IsSemimeasure (μ i)) :
    IsSemimeasure (unaryMixture w μ) := by
  change (∑' x : BitString, mixture w (fun i out _ => μ i out) x []) ≤ 1
  exact mixture_isConditionalSemimeasure w (fun i out _ => μ i out) hw
    (fun i _ => hμ i) []

/-- A unary mixture dominates each component by that component's weight. -/
theorem unaryMixture_dominates_component (w : ℕ → ℝ≥0∞)
    (μ : ℕ → BitString → ℝ≥0∞) (i : ℕ) :
    DominatesUnary (unaryMixture w μ) (μ i) (w i) :=
  fun x => show w i * μ i x ≤ unaryMixture w μ x from ENNReal.le_tsum i

/-- A subnormalized unary mixture with strictly positive weights is universal
for its countable family. -/
theorem unaryMixture_isUniversalFor (w : ℕ → ℝ≥0∞)
    (μ : ℕ → BitString → ℝ≥0∞) (hw_sum : (∑' i, w i) ≤ 1)
    (hw_pos : ∀ i, 0 < w i) (hμ : ∀ i, IsSemimeasure (μ i)) :
    IsUniversalForUnary (unaryMixture w μ) μ :=
  ⟨unaryMixture_isSemimeasure w μ hw_sum hμ,
   fun i => ⟨w i, hw_pos i, unaryMixture_dominates_component w μ i⟩⟩

/-! ### Structural Facts -/

/-- A conditional semimeasure yields a unary semimeasure at the empty context. -/
theorem isSemimeasure_of_isConditionalSemimeasure_empty {μ : BitString → BitString → ℝ≥0∞}
    (h : IsConditionalSemimeasure μ) : IsSemimeasure (fun x => μ x []) :=
  h []

/-- A conditional lower-semicomputable semimeasure yields a unary
lower-semicomputable semimeasure at the empty context. -/
theorem isLowerSemicomputableSemimeasure_of_empty
    {μ : BitString → BitString → ℝ≥0∞}
    (hμ : IsConditionalSemimeasure μ) (hlsc : IsLSC μ) :
    IsLowerSemicomputableSemimeasure (fun x => μ x []) :=
  ⟨isSemimeasure_of_isConditionalSemimeasure_empty hμ, by
    obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
    refine ⟨fun s out _ => approx s out [], ?_, ?_, ?_⟩
    · intro s out ctx
      exact hmono s out []
    · intro out ctx
      exact hsup out []
    · exact hcomp.comp
        ((Computable.fst).pair
          (((Computable.fst).comp Computable.snd).pair (Computable.const [])))⟩

/-- The machine-induced a priori semimeasure of a prefix decompressor, restricted
to the empty context, is a unary lower-semicomputable semimeasure. -/
theorem aprioriMeasure_empty_isLowerSemicomputableSemimeasure
    (M : Map) (hM : IsPrefixDecompressor M) :
    IsLowerSemicomputableSemimeasure (fun x => aprioriMeasure M x []) :=
  isLowerSemicomputableSemimeasure_of_empty
    (aprioriMeasure_isConditionalSemimeasure M hM.isPrefixMachine)
    (aprioriMeasure_isLSC M hM)

/-- Reflexivity of unary domination. -/
theorem DominatesUnary.refl (m : BitString → ℝ≥0∞) :
    DominatesUnary m m 1 := fun x => by rw [one_mul]

/-- Constant weakening for unary domination. -/
theorem DominatesUnary.mono_const {m₁ m₂ : BitString → ℝ≥0∞} {c d : ℝ≥0∞}
    (hcd : d ≤ c) (h : DominatesUnary m₁ m₂ c) : DominatesUnary m₁ m₂ d :=
  fun x => le_trans (by gcongr) (h x)

/-- Transitivity of unary domination. -/
theorem DominatesUnary.trans {m₁ m₂ m₃ : BitString → ℝ≥0∞} {c d : ℝ≥0∞}
    (h1 : DominatesUnary m₁ m₂ c) (h2 : DominatesUnary m₂ m₃ d) :
    DominatesUnary m₁ m₃ (c * d) :=
  fun x => calc
    (c * d) * m₃ x = c * (d * m₃ x) := by rw [mul_assoc]
    _ ≤ c * m₂ x := by gcongr; exact h2 x
    _ ≤ m₁ x := h1 x

/-- Conditional domination restricts to unary domination at the empty context. -/
theorem DominatesUnary.of_conditional_empty
    {μ ν : BitString → BitString → ℝ≥0∞} {c : ℝ≥0∞}
    (h : Dominates μ ν c) :
    DominatesUnary (fun x => μ x []) (fun x => ν x []) c :=
  fun x => h x []

/-! ### Prefix-complexity weight and abstract semimeasures -/

/-- The easy coding direction makes `2^{-KP_U(x|[])}` a unary semimeasure for a
prefix decompressor `U`, because it is pointwise below the machine-induced
`aprioriMeasure U x []`. -/
theorem prefixComplexityWeight_isSemimeasure
    (U : Map) (hU : IsPrefixDecompressor U) :
    IsSemimeasure (prefixComplexityWeight U) := by
  calc
    (∑' x : BitString, prefixComplexityWeight U x)
        ≤ ∑' x : BitString, aprioriMeasure U x [] := by
          exact ENNReal.tsum_le_tsum fun x =>
            complexityWeight_KP_le_aprioriMeasure U x []
    _ ≤ 1 := tsum_aprioriMeasure_le_one U [] hU.isPrefixMachine

/-- Every lower-semicomputable unary semimeasure is dominated by the optimal
prefix-complexity weight. This is the Kraft-Chaitin coding direction applied to
the dummy-context conditional function `fun x _ => m x`, followed by optimality
of `U`. -/
theorem lowerSemicomputableSemimeasure_le_prefixComplexityWeight
    {m : BitString → ℝ≥0∞} (hm : IsLowerSemicomputableSemimeasure m)
    {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x,
      (2 : ℝ≥0∞)⁻¹ ^ c * m x ≤ prefixComplexityWeight U x := by
  obtain ⟨M, hM, c₀, hreal⟩ :=
    kraftChaitin_realization_bound hm.2 0 (fun _ => by simpa [IsSemimeasure] using hm.1)
  obtain ⟨c, hc⟩ := complexityWeight_dominates_of_prefix_realization hU hM hreal
  exact ⟨c, fun x => hc x []⟩

/-- A universal semimeasure dominates the prefix-complexity weight of any optimal
prefix decompressor. This uses universality only on the machine-induced
semimeasure `aprioriMeasure U · []`; the pointwise bound
`2^{-KP_U} ≤ aprioriMeasure U` supplies the final comparison. -/
theorem prefixComplexityWeight_le_universalSemimeasure
    {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m)
    {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ x, c * prefixComplexityWeight U x ≤ m x := by
  obtain ⟨c, hc_pos, hc⟩ :=
    hm.2 (fun x => aprioriMeasure U x [])
      (aprioriMeasure_empty_isLowerSemicomputableSemimeasure U
        hU.isPrefixDecompressor)
  refine ⟨c, hc_pos, fun x => ?_⟩
  calc
    c * prefixComplexityWeight U x
        ≤ c * aprioriMeasure U x [] := by
          gcongr
          exact complexityWeight_KP_le_aprioriMeasure U x []
    _ ≤ m x := hc x


end Kolmogorov
