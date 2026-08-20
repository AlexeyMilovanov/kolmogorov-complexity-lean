import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicProbability.PairProjection

/-!
# First-coordinate projection of coded finite distributions

This chapter-local constructor pushes every raw atom through `decodeFirst`
without changing its rational mass.  Duplicate projected points remain as
duplicate raw entries and are aggregated by `CodedFiniteDistribution.mass`.
The accompanying code map is total on arbitrary bit strings.
-/

namespace Kolmogorov

/-- Push every atom of a coded finite distribution through `decodeFirst`,
retaining the original raw-list order and exact rational masses. -/
def codedFstPushforward (P : CodedFiniteDistribution) : CodedFiniteDistribution where
  data := P.data.map fun e => { point := decodeFirst e.point, mass := e.mass }

/-- Executable raw-code transformer for `codedFstPushforward`. -/
def codedFstPushforwardCode (w : BitString) : BitString :=
  codedDistributionDataCode ((CodedFiniteDistribution.decodeDistributionData w).map fun e =>
    { point := decodeFirst e.point, mass := e.mass })

/-- Projection can only increase the mass at the image of a point, since other
points may share the same first coordinate. -/
theorem codedFstPushforward_mass_ge
    (P : CodedFiniteDistribution) (x : BitString) :
    P.mass x ≤ (codedFstPushforward P).mass (decodeFirst x) := by
  unfold CodedFiniteDistribution.mass codedFstPushforward
  induction P.data with
  | nil => simp
  | cons e data ih =>
      simp only [List.map_cons, List.foldr_cons]
      by_cases hx : e.point = x
      · simpa [hx] using add_le_add (le_refl e.mass.value) ih
      · by_cases hfst : decodeFirst e.point = decodeFirst x
        · simp only [hx, ↓reduceIte, zero_add, hfst]
          exact ih.trans (le_add_of_nonneg_left (zero_le e.mass.value))
        · simpa [hx, hfst] using ih

/-- Projection retains every raw rational mass, so the exact rational raw total
is unchanged even when several projected points coincide. -/
theorem codedFstPushforward_totalMassRat
    (P : CodedFiniteDistribution) :
    totalMassRat (codedFstPushforward P).data = totalMassRat P.data := by
  unfold totalMassRat
  change (P.data.map (fun e =>
      ({ point := decodeFirst e.point, mass := e.mass } : CodedDistributionEntry))).foldr
        (fun e acc => e.mass.add acc) RatMass.zero =
    P.data.foldr (fun e acc => e.mass.add acc) RatMass.zero
  induction P.data with
  | nil => rfl
  | cons e data ih => simp [ih]

/-- First-coordinate projection preserves total represented mass. -/
theorem codedFstPushforward_totalMass
    (P : CodedFiniteDistribution) :
    (∑ y ∈ (codedFstPushforward P).support,
      (codedFstPushforward P).mass y) =
    ∑ x ∈ P.support, P.mass x := by
  rw [mass_total, mass_total, codedFstPushforward_totalMassRat]

/-- Projection of a probability model is again a probability model. -/
theorem codedFstPushforward_isProbability
    (P : CodedFiniteDistribution) :
    P.IsProbability → (codedFstPushforward P).IsProbability := by
  intro h
  unfold CodedFiniteDistribution.IsProbability at *
  rw [codedFstPushforward_totalMass]
  exact h

/-- The raw-code projection transformer is computable on every bit string. -/
theorem codedFstPushforwardCode_computable :
    Computable codedFstPushforwardCode := by
  have hentry : Primrec (fun e : CodedDistributionEntry =>
      ({ point := decodeFirst e.point, mass := e.mass } : CodedDistributionEntry)) := by
    have hpair : Primrec (fun e : CodedDistributionEntry =>
        (decodeFirst e.point, e.mass)) :=
      (CodedFiniteDistribution.decodeFirst_primrec.comp
        CodedFiniteDistribution.entry_point_primrec).pair
        CodedFiniteDistribution.entry_mass_primrec
    convert Primrec.of_equiv_symm.comp hpair using 1
  exact (CodedFiniteDistribution.codedDistributionDataCode_primrec.comp
    (Primrec.list_map CodedFiniteDistribution.decodeDistributionData_primrec
      (hentry.comp Primrec.snd).to₂)).to_comp

/-- Applying the executable transformer to a genuine distribution code returns
the exact raw-list code of its projection. -/
@[simp] theorem codedFstPushforwardCode_eq
    (P : CodedFiniteDistribution) :
    codedFstPushforwardCode P.code = (codedFstPushforward P).code := by
  simp [codedFstPushforwardCode, CodedFiniteDistribution.code,
    codedFstPushforward, CodedFiniteDistribution.decodeDistributionData_code]

/-- Canonical projection increases model complexity by at most a uniform
machine constant. -/
theorem codedFstPushforward_complexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P,
      (codedFstPushforward P).complexity U ≤
        P.complexity U + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    KPPlain_map_le U hU codedFstPushforwardCode codedFstPushforwardCode_computable
  refine ⟨c, fun P => ?_⟩
  unfold CodedFiniteDistribution.complexity
  rw [← codedFstPushforwardCode_eq]
  exact hc P.code

end Kolmogorov
