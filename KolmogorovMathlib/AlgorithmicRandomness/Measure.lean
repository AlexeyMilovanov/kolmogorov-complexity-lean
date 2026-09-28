import KolmogorovMathlib.AlgorithmicRandomness.Cylinders
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measures on Cantor space

This module implements the measure-theoretic foundations of SUV Chapter 3.1.
We define cylinder masses, prove their additivity, and state the uniqueness of measures
determined by their values on cylinders.

## Conflation guard
Cylinder mass `p(x) = p(x0) + p(x1)` (equality, §3.1) ≠ tree semimeasure
`a(x) ≥ a(x0) + a(x1)` (inequality, Thm 75) ≠ the existing discrete
`aprioriMeasure`. No identification without a proved bridge.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The cylinder mass function `p(x) = μ(Ω_x)` associated to a measure `μ` on Cantor space. -/
noncomputable def cantorMass (μ : Measure CantorSeq) (x : BitString) : ℝ≥0∞ :=
  μ (cantorCylinder x)

/-- A sequence extends `x ++ [b]` iff it extends `x` and has bit `b` at position `x.length`. -/
lemma isCantorPrefix_append_singleton (x : BitString) (b : Bool) (w : CantorSeq) :
    IsCantorPrefix (x ++ [b]) w ↔ IsCantorPrefix x w ∧ w x.length = b := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have h' := h i (by rw [List.length_append, List.length_singleton]; omega)
      rwa [List.getElem_append_left hi] at h'
    · have h' := h x.length (by rw [List.length_append, List.length_singleton]; omega)
      rw [List.getElem_append_right (le_refl _)] at h'
      simpa using h'
  · rintro ⟨h1, h2⟩ i hi
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · rw [List.getElem_append_left hlt]; exact h1 i hlt
    · subst heq
      rw [List.getElem_append_right (le_refl _)]
      simpa using h2

/-- The additivity property of cylinder masses: `p(x) = p(x0) + p(x1)`.
This holds for *every* measure, since `Ω_x` is the disjoint union of `Ω_{x0}`
and `Ω_{x1}` (SUV §3.1: the cylinder-mass additivity constraint). -/
lemma cantorMass_add (μ : Measure CantorSeq) (x : BitString) :
    cantorMass μ x = cantorMass μ (x ++ [false]) + cantorMass μ (x ++ [true]) := by
  have hunion : cantorCylinder x
      = cantorCylinder (x ++ [false]) ∪ cantorCylinder (x ++ [true]) := by
    ext w
    simp only [Set.mem_union, cantorCylinder, Set.mem_setOf_eq]
    rw [isCantorPrefix_append_singleton, isCantorPrefix_append_singleton]
    constructor
    · intro hw
      by_cases hb : w x.length = true
      · exact Or.inr ⟨hw, hb⟩
      · exact Or.inl ⟨hw, by simpa using hb⟩
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  have hne : ∀ (b1 b2 : Bool), b1 ≠ b2 → ¬ (x ++ [b1]) <+: (x ++ [b2]) := by
    intro b1 b2 hb hpref
    have hlen : (x ++ [b1]).length = (x ++ [b2]).length := by simp
    have heq := List.IsPrefix.eq_of_length hpref hlen
    have hbb := List.append_cancel_left heq
    rw [List.cons.injEq] at hbb
    exact hb hbb.1
  have hdisj : Disjoint (cantorCylinder (x ++ [false])) (cantorCylinder (x ++ [true])) :=
    cantorCylinder_disjoint_of_incompatible (hne false true (by decide))
      (hne true false (by decide))
  unfold cantorMass
  rw [hunion, measure_union hdisj (measurableSet_cantorCylinder _)]

/-- The coordinate set `{w | w a = b}` is the countable union of the cylinders
`Ω_{y ++ [b]}` taken over all strings `y` of length `a`. -/
lemma coordSet_eq_iUnion_cylinder (a : ℕ) (b : Bool) :
    {w : CantorSeq | w a = b}
      = ⋃ y : {y : BitString // y.length = a}, cantorCylinder (y.val ++ [b]) := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, cantorCylinder]
  constructor
  · intro hw
    refine ⟨⟨cantorPrefix w a, by simp⟩, ?_⟩
    rw [isCantorPrefix_append_singleton]
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [cantorPrefix_length] at hi
      simp
    · simpa using hw
  · rintro ⟨⟨y, hy⟩, hmem⟩
    rw [isCantorPrefix_append_singleton] at hmem
    have := hmem.2
    rwa [hy] at this

/-- The cylinders form a π-system: two cylinders are either disjoint or nested,
and in the nested case their intersection is again a cylinder. -/
lemma isPiSystem_range_cantorCylinder : IsPiSystem (Set.range cantorCylinder) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
  by_cases hxy : x <+: y
  · rw [cantorCylinder_inter_of_prefix hxy]
    exact ⟨y, rfl⟩
  · by_cases hyx : y <+: x
    · rw [Set.inter_comm, cantorCylinder_inter_of_prefix hyx]
      exact ⟨x, rfl⟩
    · exact absurd ((cantorCylinder_disjoint_of_incompatible hxy hyx).inter_eq ▸ hne)
        (by simp)

/-- The cylinders generate the product σ-algebra on Cantor space. -/
lemma generateFrom_range_cantorCylinder :
    MeasurableSpace.generateFrom (Set.range cantorCylinder)
      = (inferInstance : MeasurableSpace CantorSeq) := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro _ ⟨x, rfl⟩
    exact measurableSet_cantorCylinder x
  · have hcoord : ∀ (a : ℕ) (b : Bool),
        MeasurableSet[MeasurableSpace.generateFrom (Set.range cantorCylinder)]
          {w : CantorSeq | w a = b} := by
      intro a b
      rw [coordSet_eq_iUnion_cylinder]
      exact MeasurableSet.iUnion fun y =>
        MeasurableSpace.measurableSet_generateFrom ⟨y.val ++ [b], rfl⟩
    refine iSup_le fun a => ?_
    rintro s ⟨t, -, rfl⟩
    have ht : (fun w : CantorSeq => w a) ⁻¹' t = ⋃ b ∈ t, {w : CantorSeq | w a = b} := by
      ext w; simp
    rw [ht]
    exact MeasurableSet.biUnion t.to_countable fun b _ => hcoord a b

/-- Uniqueness: if two probability measures agree on all cylinders, they are equal.

The cylinders `cantorCylinder x` form a π-system generating the product
σ-algebra on `CantorSeq = ℕ → Bool`, so the π-system uniqueness lemma applies. -/
lemma cantorMeasure_unique (μ ν : Measure CantorSeq)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, cantorMass μ x = cantorMass ν x) : μ = ν := by
  refine MeasureTheory.ext_of_generate_finite (Set.range cantorCylinder)
    generateFrom_range_cantorCylinder.symm isPiSystem_range_cantorCylinder ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact h x
  · simp [measure_univ]

/-- The Bernoulli measure on Cantor space with parameter `p`. -/
noncomputable def bernoulliMeasure (p : NNReal) (hp : p ≤ 1) : Measure CantorSeq :=
  Measure.infinitePi (fun _ => (PMF.bernoulli p hp).toMeasure)

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (bernoulliMeasure p hp) := by
  dsimp [bernoulliMeasure]; infer_instance

/-- The uniform measure on Cantor space. -/
noncomputable def uniformMeasure : Measure CantorSeq :=
  bernoulliMeasure (1/2) (by norm_num)

instance : IsProbabilityMeasure uniformMeasure := by
  dsimp [uniformMeasure]; infer_instance

/-- The Bernoulli measure with parameter `p` gives the cylinder of the one-bit string `[false]`
mass `1 - p`. -/
lemma bernoulliMeasure_mass_false (p : NNReal) (hp : p ≤ 1) :
    cantorMass (bernoulliMeasure p hp) [false] = 1 - p := by
  have hcyl : cantorCylinder [false] = (Function.eval 0 : CantorSeq → Bool) ⁻¹' {false} := by
    ext w
    simp only [cantorCylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      Function.eval]
    constructor
    · intro hw
      have := hw 0 (by simp)
      simpa using this
    · intro hw i hi
      have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst this; simpa using hw
  unfold cantorMass bernoulliMeasure
  rw [hcyl, (measurePreserving_eval_infinitePi
        (fun _ : ℕ => (PMF.bernoulli p hp).toMeasure) 0).measure_preimage
      (measurableSet_singleton false).nullMeasurableSet,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton false)]
  simp

/-- The Bernoulli measure with parameter `p` gives the cylinder of the one-bit string `[true]`
mass `p`. -/
lemma bernoulliMeasure_mass_true (p : NNReal) (hp : p ≤ 1) :
    cantorMass (bernoulliMeasure p hp) [true] = p := by
  have hcyl : cantorCylinder [true] = (Function.eval 0 : CantorSeq → Bool) ⁻¹' {true} := by
    ext w
    simp only [cantorCylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      Function.eval]
    constructor
    · intro hw
      have := hw 0 (by simp)
      simpa using this
    · intro hw i hi
      have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst this; simpa using hw
  unfold cantorMass bernoulliMeasure
  rw [hcyl, (measurePreserving_eval_infinitePi
        (fun _ : ℕ => (PMF.bernoulli p hp).toMeasure) 0).measure_preimage
      (measurableSet_singleton true).nullMeasurableSet,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true)]
  simp

end Kolmogorov
