import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.Prefix.OptimalExistence

/-!
# Full-cube models

The full set of strings of a fixed length has logarithmic plain set complexity,
and is uniformly a strong model for each of its members.
-/

namespace Kolmogorov

open CodedFiniteDistribution

/-- The canonical full length-`n` cube has logarithmic ordinary plain
set complexity. -/
theorem plainSetComplexity_fullCube_le_logSlack
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ n : Nat,
      plainSetComplexity V (stringsOfLength n)
        (codedStringsOfLength_nonempty n) ≤
          (logSlack c n : ENat) := by
  let U : Map := Classical.choose exists_isOptimalPrefixConditional
  have hU : IsOptimalPrefixConditional U :=
    Classical.choose_spec exists_isOptimalPrefixConditional
  obtain ⟨cCube, hcCube⟩ := fullSetComplexityGate U hU
  obtain ⟨cBridge, hcBridge⟩ :=
    plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  refine ⟨cCube + cBridge, fun n => ?_⟩
  unfold plainSetComplexity
  calc
    plainK V (codedUniformOn (stringsOfLength n)
          (codedStringsOfLength_nonempty n)).code
        ≤ KPPlain U (codedUniformOn (stringsOfLength n)
            (codedStringsOfLength_nonempty n)).code +
              (cBridge : ENat) := hcBridge _
    _ ≤ (logSlack cCube n : ENat) + (cBridge : ENat) := by
      gcongr
      exact hcCube n (codedStringsOfLength_nonempty n)
    _ ≤ (logSlack (cCube + cBridge) n : ENat) := by
      exact_mod_cast (show
        logSlack cCube n + cBridge ≤
          logSlack (cCube + cBridge) n by
        simp [logSlack]
        nlinarith [Nat.zero_le (Nat.bits n).length])

/-- The full cube at the length of `x` is a strong set model for `x`, with a
constant total-description budget. -/
theorem fullCube_isStrongSetModel_const
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x : BitString,
      IsStrongSetModel T x (stringsOfLength x.length)
        (codedStringsOfLength_nonempty x.length) c := by
  obtain ⟨c, hc⟩ :=
    hT.2 cylinderModelDecompressor cylinderModelDecompressor_partrec
  refine ⟨c, fun x => ?_⟩
  have hx : x ∈ cylinder x.length [] := by
    rw [mem_cylinder]
    exact ⟨rfl, List.nil_prefix⟩
  have hprod :
      produces cylinderModelDecompressor (Nat.bits 0) x
        (codedUniformOn (stringsOfLength x.length)
          (codedStringsOfLength_nonempty x.length)).code := by
    have hp :=
      cylinderModelDecompressor_produces x.length [] x (by simp) hx
    convert hp using 1
    all_goals simp [cylinder]
  unfold IsStrongSetModel
  calc
    totalCondK T (codedUniformOn (stringsOfLength x.length)
          (codedStringsOfLength_nonempty x.length)).code x
        ≤ totalCondK cylinderModelDecompressor
            (codedUniformOn (stringsOfLength x.length)
              (codedStringsOfLength_nonempty x.length)).code x +
                (c : ENat) := hc _ _
    _ ≤ ((Nat.bits 0).length : ENat) + (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength
        (cylinderModelDecompressor_total (Nat.bits 0)) hprod
    _ = (c : ENat) := by simp

end Kolmogorov
