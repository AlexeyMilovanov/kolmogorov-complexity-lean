import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic

/-!
# Canonical first-coordinate truncation for add-noise

This is the executable finite-set projection used by the direct add-noise
route.  It deliberately works with canonical finite-set codes: decoded points
are mapped through `decodeFirst`, deduplicated, sorted, and re-encoded as a
uniform finite-set model.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The distinct first coordinates represented by a finite set of pair codes. -/
def finiteSetFstTruncation (B : Finset BitString) : Finset BitString :=
  B.image decodeFirst

/-- Decode a canonical finite-set code, project every point to its first
coordinate, and canonically re-encode the resulting extensional finite set. -/
noncomputable def finiteSetFstTruncationCode (w : BitString) : BitString :=
  canonicalImageCodeOfList
    ((canonicalPointListOfCode w).map decodeFirst)

theorem finiteSetFstTruncation_mem
    {B : Finset BitString} {x y : BitString}
    (hxy : pairCode x y ∈ B) :
    x ∈ finiteSetFstTruncation B := by
  rw [finiteSetFstTruncation, Finset.mem_image]
  exact ⟨pairCode x y, hxy, decodeFirst_pairCode x y⟩

theorem finiteSetFstTruncation_nonempty
    {B : Finset BitString} (hB : B.Nonempty) :
    (finiteSetFstTruncation B).Nonempty := by
  obtain ⟨z, hz⟩ := hB
  exact ⟨decodeFirst z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩

theorem finiteSetFstTruncation_card_le (B : Finset BitString) :
    (finiteSetFstTruncation B).card ≤ B.card := by
  exact Finset.card_image_le

theorem finiteSetFstTruncation_logCard_le (B : Finset BitString) :
    finiteSetLogCard (finiteSetFstTruncation B) ≤
      finiteSetLogCard B :=
  finiteSetLogCard_mono (finiteSetFstTruncation_card_le B)

theorem finiteSetFstTruncationCode_computable :
    Computable finiteSetFstTruncationCode := by
  unfold finiteSetFstTruncationCode
  exact canonicalImageCodeOfList_computable.comp
    ((Primrec.list_map canonicalPointListOfCode_primrec
      (decodeFirst_primrec.comp Primrec.snd).to₂).to_comp)

private theorem finiteSetFstTruncation_list_toFinset
    (B : Finset BitString) :
    ((canonicalFinsetList B).map decodeFirst).toFinset =
      finiteSetFstTruncation B := by
  ext x
  simp [finiteSetFstTruncation]

theorem finiteSetFstTruncationCode_codedUniformOn
    (B : Finset BitString) (hB : B.Nonempty) :
    finiteSetFstTruncationCode (codedUniformOn B hB).code =
      (codedUniformOn (finiteSetFstTruncation B)
        (finiteSetFstTruncation_nonempty hB)).code := by
  let L := (canonicalFinsetList B).map decodeFirst
  have hL : L.toFinset.Nonempty := by
    rw [show L.toFinset = finiteSetFstTruncation B by
      exact finiteSetFstTruncation_list_toFinset B]
    exact finiteSetFstTruncation_nonempty hB
  unfold finiteSetFstTruncationCode
  rw [canonicalPointListOfCode_codedUniformOn]
  change canonicalImageCodeOfList L = _
  rw [canonicalImageCodeOfList_eq_codedUniformOn L hL]
  exact codedUniformOn_code_congr hL
    (finiteSetFstTruncation_nonempty hB)
    (finiteSetFstTruncation_list_toFinset B)

/-- Canonical first-coordinate truncation costs only a uniform additive
constant in ordinary plain set complexity. -/
theorem finiteSetFstTruncation_plainSetComplexity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B : Finset BitString) (hB : B.Nonempty),
      plainSetComplexity V (finiteSetFstTruncation B)
          (finiteSetFstTruncation_nonempty hB) ≤
        plainSetComplexity V B hB + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    plainKMapLe V hV finiteSetFstTruncationCode
      finiteSetFstTruncationCode_computable
  refine ⟨c, fun B hB => ?_⟩
  unfold plainSetComplexity
  rw [← finiteSetFstTruncationCode_codedUniformOn B hB]
  exact hc (codedUniformOn B hB).code

/-- Prefix set-complexity companion to the ordinary truncation bound. -/
theorem finiteSetFstTruncation_setComplexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (B : Finset BitString) (hB : B.Nonempty),
      setComplexity U (finiteSetFstTruncation B)
          (finiteSetFstTruncation_nonempty hB) ≤
        setComplexity U B hB + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    KPPlain_map_le U hU finiteSetFstTruncationCode
      finiteSetFstTruncationCode_computable
  refine ⟨c, fun B hB => ?_⟩
  unfold setComplexity
  rw [← finiteSetFstTruncationCode_codedUniformOn B hB]
  exact hc (codedUniformOn B hB).code

end Kolmogorov
