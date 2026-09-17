import KolmogorovMathlib.AlgorithmicRandomness.MartinLof
import KolmogorovMathlib.AlgorithmicRandomness.Measure
import KolmogorovMathlib.AlgorithmicRandomness.Complement

/-!
# Randomness under measure-preserving cylinder maps

`isMartinLofRandom_of_cylinderPullback` is the conservation principle: a map of Cantor space
whose cylinder preimages are computably given cylinders, and which preserves the measure,
sends random sequences to random sequences.  Its test-side half is
`isUniformlyEffectiveOpen_pullback`, which pulls a uniformly effectively open family back
along such a map.

The worked instance is bitwise complementation: `computable_bitStringComplement`,
`preimage_bitComplement_cantorCylinder`, `measurable_bitComplement` and
`map_bitComplement_uniformMeasure_eq` verify the hypotheses, and
`measurePreserving_bitComplement_uniform` records the conclusion for the uniform measure.
-/

namespace Kolmogorov

open MeasureTheory ProbabilityTheory

/-- Complementing every bit of a finite bit string is a computable operation. -/
theorem computable_bitStringComplement : Computable (List.map not : BitString → BitString) :=
  primrec_map_not.to_comp

/-- The preimage of a cylinder under bitwise complementation is the cylinder of the
complemented string. -/
theorem preimage_bitComplement_cantorCylinder (s : BitString) :
    (fun (x : CantorSeq) n => !(x n)) ⁻¹' cantorCylinder s = cantorCylinder (s.map not) := by
  ext x
  exact mem_cantorCylinder_complementSeq s x

/-- Bitwise complementation of Cantor sequences is measurable. -/
theorem measurable_bitComplement : Measurable (fun (x : CantorSeq) n => !(x n)) := by
  measurability

/-- The uniform measure on Cantor space is invariant under bitwise complementation. -/
theorem map_bitComplement_uniformMeasure_eq :
    Measure.map (fun (x : CantorSeq) n => !(x n)) uniformMeasure = uniformMeasure := by
  have hmeas : Measurable (fun (x : CantorSeq) n => !(x n)) := measurable_bitComplement
  have : IsProbabilityMeasure (Measure.map (fun (x : CantorSeq) n => !(x n)) uniformMeasure) := ⟨by
    rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  apply cantorMeasure_unique
  intro s
  rw [cantorMass, Measure.map_apply hmeas (measurableSet_cantorCylinder s)]
  rw [preimage_bitComplement_cantorCylinder]
  exact cantorMass_uniformMeasure_map_not s

/-- Pulling a uniformly effectively open family back along a map whose cylinder preimages are
cylinders given by a computable string map again yields a uniformly effectively open family. -/
theorem isUniformlyEffectiveOpen_pullback {U : ℕ → Set CantorSeq} (hU : IsUniformlyEffectiveOpen U)
    {F : CantorSeq → CantorSeq} {phi : BitString → BitString}
    (hphi : Computable phi)
    (hpre : ∀ s, F ⁻¹' cantorCylinder s = cantorCylinder (phi s)) :
    IsUniformlyEffectiveOpen (fun n => F ⁻¹' U n) := by
  rcases hU with ⟨f, hf_comp, hf_eq⟩
  use fun n i => (f n i).map phi
  constructor
  · exact Computable.option_map hf_comp (Computable.comp hphi Computable.snd)
  · intro n
    change F ⁻¹' U n = _
    have h : U n = ⋃ i, (f n i).elim ∅ cantorCylinder := hf_eq n
    rw [h, Set.preimage_iUnion]
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    apply exists_congr
    intro i
    cases f n i
    · simp
    · simp only [Option.elim_some, Option.map_some]
      rw [← Set.mem_preimage, hpre]

/-- Randomness is conserved by a map whose cylinder preimages are computably given cylinders and
which does not increase measure: the image of a `μ`-random point is `ν`-random. -/
theorem isMartinLofRandom_of_cylinderPullback
    {μ ν : Measure CantorSeq} {F : CantorSeq → CantorSeq} {phi : BitString → BitString}
    (hphi : Computable phi)
    (hpre : ∀ s, F ⁻¹' cantorCylinder s = cantorCylinder (phi s))
    (hmeas : ∀ (A : Set CantorSeq), MeasurableSet A → μ (F ⁻¹' A) ≤ ν A)
    {x : CantorSeq} (hx : IsMartinLofRandom μ x) :
    IsMartinLofRandom ν (F x) := by
  intro U hU
  have hU_open : IsUniformlyEffectiveOpen U := hU.1
  have hV_open : IsUniformlyEffectiveOpen (fun n => F ⁻¹' U n) :=
    isUniformlyEffectiveOpen_pullback hU_open hphi hpre
  have hV_test : IsMartinLofTest μ (fun n => F ⁻¹' U n) := by
    constructor
    · exact hV_open
    · intro n
      have : MeasurableSet (U n) := by
        rcases hU_open with ⟨f, -, hf_eq⟩
        rw [hf_eq n]
        apply MeasurableSet.iUnion
        intro i
        cases f n i
        · exact MeasurableSet.empty
        · exact (isOpen_cantorCylinder _).measurableSet
      calc μ (F ⁻¹' U n) ≤ ν (U n) := hmeas (U n) this
        _ ≤ dyadicValue 1 n := hU.2 n
  intro h_mem
  apply hx _ hV_test
  simp only [Set.mem_iInter, Set.mem_preimage] at h_mem ⊢
  exact h_mem

/-- Bitwise complementation preserves the uniform measure on Cantor space. -/
theorem measurePreserving_bitComplement_uniform :
    MeasurePreserving (fun (x : CantorSeq) n => !(x n)) uniformMeasure uniformMeasure :=
  ⟨measurable_bitComplement, map_bitComplement_uniformMeasure_eq⟩

end Kolmogorov
