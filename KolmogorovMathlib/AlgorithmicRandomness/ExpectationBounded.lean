import KolmogorovMathlib.AlgorithmicRandomness.LowerSemicomputableFun
import KolmogorovMathlib.AlgorithmicRandomness.LSCCharacterizations
import KolmogorovMathlib.AlgorithmicRandomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicRandomness.StageIntegral
import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import KolmogorovMathlib.AlgorithmicRandomness.UniversalStages
import KolmogorovMathlib.AlgorithmicRandomness.ExpectationMixture
import KolmogorovMathlib.AlgorithmicProbability.UniversalMixture

/-!
# Expectation-bounded randomness tests and Theorem 42

An *expectation-bounded randomness test* with respect to a computable measure
`μ` is a lower semicomputable function `u : CantorSeq → ℝ≥0∞` with `∫ u dμ ≤ 1`.

**Theorem 42** (SUV §3.5): for every computable measure there exists a *maximal*
expectation-bounded test — one that dominates every other test up to a constant
factor.

## Architecture

The construction itself lives in `ExpectationMixture.lean`, which is where the
universal mixture

```
mixVal a w = ∑' e, 2 ^ -(e + 2) * ⨆ s, dyadicValue (trimTable a e (w ↾ s) s) s
```

is built from the universal family `patchTable` of monotone dyadic stage tables
(`UniversalStages.lean`) and the `stageAccept` trimming test
(`StageIntegral.lean`).  This file packages that construction under the
`IsExpectationBoundedRandomnessTest` interface:

* `expUniversalMixture hμ` is `mixVal` for the computable approximation family
  of `μ`;
* `isLowerSemicomputableFun_mixture` and `lintegral_mixture_le` say it is an
  expectation-bounded test;
* `expUniversalMixture_dominates_component` says it dominates every monotone
  limit of computable basic functions whose stages have integral at most `1`;
* `exists_maximal_expectation_bounded_test` is Theorem 42.

Note. Earlier drafts of this file carried a second, independent copy of the
trimming construction (`expFreezeStage` / `expSanitize`). It has been dropped in
favour of the proved `trimTable` machinery of `ExpectationMixture.lean`: apart
from being redundant, its stage `0` was left unguarded, so the intended
soundness bound `∫ ≤ 2` was in fact false for it.
-/

namespace Kolmogorov

open MeasureTheory Topology
open scoped ENNReal NNReal

/-- An expectation-bounded randomness test with respect to `μ`. -/
def IsExpectationBoundedRandomnessTest (μ : Measure CantorSeq) (u : CantorSeq → ℝ≥0∞) : Prop :=
  IsLowerSemicomputableFun u ∧ ∫⁻ w, u w ∂μ ≤ 1

/-! ## Stage-table integral infrastructure -/

/-- The integral of a function that depends only on the length-`s` prefix is the finite sum of
its values weighted by the measures of the length-`s` cylinders. -/
lemma lintegral_basicStage_eq_finsum (μ : Measure CantorSeq) (term : ℕ → BitString → ℕ) (s : ℕ) :
    ∫⁻ w, dyadicValue (term s (cantorPrefix w s)) s ∂μ =
    ∑ x ∈ (bitStringsOfLength s).toFinset, dyadicValue (term s x) s * cantorMass μ x := by
  have H : (bitStringsOfLength s).toFinset = levelFinset s := by
    ext x
    simp [mem_bitStringsOfLength_iff]
  rw [H, ← lintegral_comp_cantorPrefix μ s (fun x => dyadicValue (term s x) s)]

/-! ## The computable approximation family of a computable measure -/

/-- Extract the computable approximation family from `IsComputableMeasure μ`. -/
noncomputable def IsComputableMeasure.approx {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) : BitString → ℕ → ℕ :=
  Classical.choose hμ

/-- The dyadic approximation function supplied by a computable measure is computable in the
string and the stage jointly. -/
lemma IsComputableMeasure.approx_computable {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) : Computable₂ hμ.approx :=
  (Classical.choose_spec hμ).1

/-- The stage-`s` approximation of a computable measure differs from the true cylinder mass by
at most `2^{-s}` in either direction. -/
lemma IsComputableMeasure.approx_bound {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) (x : BitString) (s : ℕ) :
    dyadicValue (hμ.approx x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (hμ.approx x s) s + dyadicValue 1 s :=
  (Classical.choose_spec hμ).2 x s

/-! ## The universal mixture -/

/-- The universal mixture of trimmed expectation-bounded test candidates: the
`mixVal` construction of `ExpectationMixture.lean`, instantiated at the
computable approximation family of `μ`. -/
noncomputable def expUniversalMixture {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) : CantorSeq → ℝ≥0∞ :=
  mixVal hμ.approx

/-! ### Properties of the mixture -/

/-- The universal expectation-bounded mixture attached to a computable measure is a lower
semicomputable function on Cantor space. -/
lemma isLowerSemicomputableFun_mixture {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) :
    IsLowerSemicomputableFun (expUniversalMixture hμ) :=
  isLowerSemicomputableFun_of_isSupremum
    ⟨mixTable hμ.approx, computable_mixTable hμ.approx_computable,
      fun w => mixVal_eq_iSup hμ.approx w⟩

/-- The universal expectation-bounded mixture has integral at most one against its measure, so
it is an expectation-bounded randomness test. -/
lemma lintegral_mixture_le {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ) :
    ∫⁻ w, expUniversalMixture hμ w ∂μ ≤ 1 :=
  lintegral_mixVal_le_one hμ.approx_bound

/-- The mixture dominates each of its components, with constant `2 ^ (e + 2)`. -/
lemma compVal_le_mixVal_mul {μ : Measure CantorSeq} (hμ : IsComputableMeasure μ) (e : ℕ)
    (w : CantorSeq) :
    compVal hμ.approx e w ≤ (2 : ℝ≥0∞) ^ (e + 2) * expUniversalMixture hμ w := by
  have hle : dyadicValue 1 (e + 2) * compVal hμ.approx e w ≤ expUniversalMixture hμ w :=
    ENNReal.le_tsum e
  calc compVal hμ.approx e w
      = (2 : ℝ≥0∞) ^ (e + 2) * (dyadicValue 1 (e + 2) * compVal hμ.approx e w) := by
        rw [← mul_assoc, dyadicValue_eq_mul_inv_pow]
        simp only [Nat.cast_one, one_mul]
        rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ (e + 2) * expUniversalMixture hμ w := by gcongr

/-- Every honest test (one whose table `A` is total computable, monotone, and has
stage integrals ≤ 1) is dominated by the universal mixture. -/
lemma expUniversalMixture_dominates_component {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) (A : ℕ → BitString → ℕ)
    (hA : Computable₂ A)
    (hmono : ∀ s w,
      dyadicValue (A s (cantorPrefix w s)) s
        ≤ dyadicValue (A (s + 1) (cantorPrefix w (s + 1))) (s + 1))
    (h_int : ∀ s, ∫⁻ w, dyadicValue (A s (cantorPrefix w s)) s ∂μ ≤ 1) :
    ∃ c : NNReal, ∀ w, (⨆ s, dyadicValue (A s (cantorPrefix w s)) s : ℝ≥0∞)
      ≤ c * expUniversalMixture hμ w := by
  set v : CantorSeq → ℝ≥0∞ := fun w => ⨆ s, dyadicValue (A s (cantorPrefix w s)) s with hv_def
  -- `v` is lower semicomputable, being a supremum of computable basic functions.
  have hv_lsc : IsLowerSemicomputableFun v :=
    isLowerSemicomputableFun_of_isSupremum ⟨A, hA, fun _ => rfl⟩
  -- The stagewise bounds and monotone convergence give `∫ v ≤ 1`.
  have hmeas : ∀ s, Measurable (fun w => dyadicValue (A s (cantorPrefix w s)) s) :=
    fun s => measurable_comp_cantorPrefix s (fun x => dyadicValue (A s x) s)
  have hmono' : Monotone (fun s (w : CantorSeq) => dyadicValue (A s (cantorPrefix w s)) s) :=
    monotone_nat_of_le_succ fun s w => hmono s w
  have hv_int : ∫⁻ w, v w ∂μ ≤ 1 := by
    rw [hv_def, lintegral_iSup hmeas hmono']
    exact iSup_le h_int
  obtain ⟨e, he⟩ := exists_index_compVal_ge hμ.approx_bound hv_lsc hv_int
  refine ⟨(2 : NNReal) ^ (e + 2), fun w => ?_⟩
  have hcast : ((((2 : NNReal) ^ (e + 2) : NNReal)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (e + 2) := by
    push_cast
    rfl
  rw [hcast]
  exact (he w).trans (compVal_le_mixVal_mul hμ e w)

/-! ## Theorem 42 -/

/-- **Theorem 42** (SUV §3.5). For every computable measure on Cantor space
there is a maximal (up to a constant factor) expectation-bounded randomness
test with respect to this measure.

The proof uses the monotone-limit characterization of lower semicomputable
functions (Theorem 40): a function is lower semicomputable iff it is the
monotone limit of computable basic functions. The universal enumeration of
computable tables via `patchTable` (from `UniversalStages`), the
`stageAccept`-based trimming, and the dyadic mixture together construct the
maximal test. -/
theorem exists_maximal_expectation_bounded_test {μ : Measure CantorSeq}
    (hμ : IsComputableMeasure μ) :
    ∃ u : CantorSeq → ℝ≥0∞, IsExpectationBoundedRandomnessTest μ u ∧
      ∀ v, IsExpectationBoundedRandomnessTest μ v →
        ∃ c : NNReal, ∀ w, v w ≤ c * u w := by
  refine ⟨expUniversalMixture hμ,
    ⟨isLowerSemicomputableFun_mixture hμ, lintegral_mixture_le hμ⟩,
    fun v ⟨hv_lsc, hv_int⟩ => ?_⟩
  -- By Theorem 40, v is a monotone limit of computable basic functions
  obtain ⟨A, hA_comp, hA_mono, hA_eq⟩ :=
    (lowerSemicomputableFun_characterizations v).2.1.mp hv_lsc
  -- The function v has integral ≤ 1, so each stage has integral ≤ 1
  have h_stage_int : ∀ s, ∫⁻ w, dyadicValue (A s (cantorPrefix w s)) s ∂μ ≤ 1 := by
    intro s
    calc ∫⁻ w, dyadicValue (A s (cantorPrefix w s)) s ∂μ
        ≤ ∫⁻ w, v w ∂μ := by
          apply lintegral_mono
          intro w
          rw [hA_eq w]
          exact le_iSup (fun s => dyadicValue (A s (cantorPrefix w s)) s) s
      _ ≤ 1 := hv_int
  -- By domination, the mixture dominates each component
  obtain ⟨c, hc⟩ :=
    expUniversalMixture_dominates_component hμ A hA_comp hA_mono h_stage_int
  refine ⟨c, fun w => ?_⟩
  calc v w = ⨆ s, dyadicValue (A s (cantorPrefix w s)) s := hA_eq w
    _ ≤ c * expUniversalMixture hμ w := hc w

end Kolmogorov
