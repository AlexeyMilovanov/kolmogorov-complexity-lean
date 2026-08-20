import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.DistributionProjection
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UniformNoiseExtension

/-!
# Projection laws for uniform noise extensions

First-coordinate projection removes the independent uniform coordinate added by
`codedPairUniformExtension`, both at the level of support and represented mass.
-/

namespace Kolmogorov

/-- Projecting a uniform-noise extension onto its first coordinate recovers the
original support. -/
theorem codedFstPushforward_codedPairUniformExtension_support
    (P : CodedFiniteDistribution) (m : Nat) :
    (codedFstPushforward (codedPairUniformExtension P m)).support =
      P.support := by
  ext a
  simp only [CodedFiniteDistribution.mem_support_iff]
  simp only [codedFstPushforward, codedPairUniformExtension, List.map_flatMap,
    List.map_map, List.mem_flatMap, List.mem_map, Function.comp_apply,
    decodeFirst_pairCode]
  constructor
  · rintro ⟨e, he, u, hu, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, List.replicate m false, ?_, rfl⟩
    simp

/-- Projecting a uniform-noise extension onto its first coordinate recovers the
original mass function, including when the input raw list contains duplicates. -/
theorem codedFstPushforward_codedPairUniformExtension_mass
    (P : CodedFiniteDistribution) (m : Nat) (a : BitString) :
    (codedFstPushforward (codedPairUniformExtension P m)).mass a =
      P.mass a := by
  have foldr_const (l : List BitString) (q r : ENNReal) :
      l.foldr (fun _ acc => q + acc) r = (l.length : ENNReal) * q + r := by
    induction l with
    | nil => simp
    | cons u us ih =>
        simp only [List.foldr_cons, ih, List.length_cons]
        push_cast
        ring
  have hcancel : (2 : ENNReal) ^ m * (2 : ENNReal)⁻¹ ^ m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have block (e : CodedDistributionEntry) (r : ENNReal) :
      (((allStrings m).map fun u =>
          ({ point := decodeFirst (pairCode e.point u),
             mass := e.mass.scaleInvPow2 m } : CodedDistributionEntry)).foldr
        (fun f acc => (if f.point = a then f.mass.value else 0) + acc) r) =
      (if e.point = a then e.mass.value else 0) + r := by
    simp only [decodeFirst_pairCode, List.foldr_map]
    by_cases h : e.point = a
    · simp only [h, ↓reduceIte]
      rw [foldr_const, length_allStrings, RatMass.scaleInvPow2_value]
      push_cast
      rw [show (2 : ENNReal) ^ m * (e.mass.value * (2 : ENNReal)⁻¹ ^ m) =
          e.mass.value * ((2 : ENNReal) ^ m * (2 : ENNReal)⁻¹ ^ m) by ring]
      rw [hcancel, mul_one]
    · simp only [h, ↓reduceIte, zero_add]
      induction allStrings m with
      | nil => rfl
      | cons u us ih => simp [ih]
  unfold CodedFiniteDistribution.mass codedFstPushforward codedPairUniformExtension
  simp only [List.map_flatMap, List.map_map]
  change (P.data.flatMap fun e =>
      (allStrings m).map fun u =>
        ({ point := decodeFirst (pairCode e.point u),
           mass := e.mass.scaleInvPow2 m } : CodedDistributionEntry)).foldr
      (fun e acc => (if e.point = a then e.mass.value else 0) + acc) 0 =
    P.data.foldr (fun e acc => (if e.point = a then e.mass.value else 0) + acc) 0
  induction P.data with
  | nil => simp
  | cons e es ih =>
      simp only [List.flatMap_cons, List.foldr_append, List.foldr_cons]
      rw [block, ih]

end Kolmogorov
