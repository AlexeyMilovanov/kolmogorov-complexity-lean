import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

namespace Kolmogorov

def RatMass.scaleInvPow2 (q : RatMass) (m : Nat) : RatMass where
  num := q.num
  den := q.den * 2 ^ m
  den_pos := by
    have h := q.den_pos
    have h2 : 0 < 2 ^ m := by positivity
    exact Nat.mul_pos h h2

@[simp] theorem RatMass.scaleInvPow2_value
    (q : RatMass) (m : Nat) :
    (q.scaleInvPow2 m).value =
      q.value * (2 : ENNReal)⁻¹ ^ m := by
  unfold RatMass.scaleInvPow2 RatMass.value
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast q.den_pos.ne'))
    (Or.inl (by simp))]
  rw [ENNReal.inv_pow]
  ring

/-- Exact scaling by `2⁻ᵐ` is primitive recursive in the rational mass and
the exponent. -/
theorem RatMass.scaleInvPow2_primrec :
    Primrec₂ RatMass.scaleInvPow2 := by
  have h : Primrec (fun p : RatMass × Nat =>
      (⟨(p.1.num, p.1.den * 2 ^ p.2), by
        exact Nat.mul_pos p.1.den_pos (by positivity)⟩ :
        {p : Nat × Nat // 0 < p.2})) := by
    refine Primrec.subtype_mk ?_
    exact Primrec.pair
      (CodedFiniteDistribution.ratMass_num_primrec.comp Primrec.fst)
      (Primrec.nat_mul.comp
        (CodedFiniteDistribution.ratMass_den_primrec.comp Primrec.fst)
        (CodedFiniteDistribution.twoPow_primrec.comp Primrec.snd))
  generalize_proofs at *
  convert Primrec.of_equiv_symm.comp h using 1

def codedPairUniformExtension
    (P : CodedFiniteDistribution) (m : Nat) :
    CodedFiniteDistribution where
  data := P.data.flatMap fun e =>
    (allStrings m).map fun u =>
      { point := pairCode e.point u, mass := e.mass.scaleInvPow2 m }

def codedPairUniformExtensionCode (w : BitString) : BitString :=
  codedDistributionDataCode
    ((CodedFiniteDistribution.decodeDistributionData (decodeFirst w)).flatMap fun e =>
      (allStrings (CodedFiniteDistribution.decodeNatCode (decodeSecond w))).map fun u =>
        { point := pairCode e.point u,
          mass := e.mass.scaleInvPow2
            (CodedFiniteDistribution.decodeNatCode (decodeSecond w)) })

theorem codedPairUniformExtension_mass_pairCode
    (P : CodedFiniteDistribution) (m : Nat)
    (a u : BitString) (hu : u.length = m) :
    (codedPairUniformExtension P m).mass (pairCode a u) =
      P.mass a * (2 : ENNReal)⁻¹ ^ m := by
  have foldr_ite_eq_add_of_nodup
      (l : List BitString) (v : BitString) (q r : ENNReal)
      (hl : l.Nodup) :
      l.foldr (fun w acc => (if w = v then q else 0) + acc) r =
        (if v ∈ l then q else 0) + r := by
    induction l with
    | nil => simp
    | cons w l ih =>
        rw [List.nodup_cons] at hl
        by_cases hw : w = v
        · subst w
          simp only [List.foldr_cons]
          rw [ih hl.2]
          simp [hl.1]
        · simp only [List.foldr_cons]
          rw [ih hl.2]
          simp [hw, Ne.symm hw]
  have foldr_uniform_pair_mass
      (e : CodedDistributionEntry) (r : ENNReal) :
      ((allStrings m).map fun v =>
          ({ point := pairCode e.point v, mass := e.mass.scaleInvPow2 m } :
            CodedDistributionEntry)).foldr
        (fun f acc =>
          (if f.point = pairCode a u then f.mass.value else 0) + acc) r =
        (if e.point = a then e.mass.value * (2 : ENNReal)⁻¹ ^ m else 0) + r := by
    rw [List.foldr_map]
    have hpair : ∀ v : BitString,
        pairCode e.point v = pairCode a u ↔ e.point = a ∧ v = u := by
      intro v
      constructor
      · intro h
        exact Prod.ext_iff.mp (@pairCode_injective (e.point, v) (a, u) h)
      · rintro ⟨rfl, rfl⟩
        rfl
    simp_rw [hpair]
    by_cases he : e.point = a
    · simp only [he, true_and]
      rw [foldr_ite_eq_add_of_nodup _ _ _ _ (allStrings_nodup m)]
      rw [if_pos ((mem_allStrings m u).mpr hu)]
      rw [RatMass.scaleInvPow2_value]
      simp
    · simp [he]
  unfold CodedFiniteDistribution.mass codedPairUniformExtension
  induction P.data with
  | nil => simp
  | cons e data ih =>
      rw [List.flatMap_cons, List.foldr_append, List.foldr_cons]
      rw [foldr_uniform_pair_mass e]
      rw [ih]
      by_cases he : e.point = a
      · simp [he, add_mul]
      · simp [he]

/-- Expanding one raw atom over all width-`m` strings preserves its represented
mass, even with an arbitrary rational fold accumulator. -/
theorem codedPairUniformExtension_foldr_total_value
    (e : CodedDistributionEntry) (m : Nat) (r : RatMass) :
    (((allStrings m).map fun v =>
        ({ point := pairCode e.point v, mass := e.mass.scaleInvPow2 m } :
          CodedDistributionEntry)).foldr
      (fun f acc => f.mass.add acc) r).value = e.mass.value + r.value := by
  have foldr_constant_mass_value
      (l : List BitString) (f : BitString → BitString) (q r : RatMass) :
      ((l.map fun v =>
          ({ point := f v, mass := q } : CodedDistributionEntry)).foldr
        (fun e acc => e.mass.add acc) r).value =
        (l.length : ENNReal) * q.value + r.value := by
    induction l with
    | nil => simp
    | cons v l ih =>
        simp only [List.map_cons, List.foldr_cons, RatMass.add_value, ih,
          List.length_cons]
        push_cast
        ring
  have h := foldr_constant_mass_value (allStrings m) (pairCode e.point)
    (e.mass.scaleInvPow2 m) r
  simp only [length_allStrings, RatMass.scaleInvPow2_value] at h
  rw [h]
  push_cast
  have hcancel : (2 : ENNReal) ^ m * (2 : ENNReal)⁻¹ ^ m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  calc
    (2 : ENNReal) ^ m * (e.mass.value * (2 : ENNReal)⁻¹ ^ m) + r.value =
        e.mass.value * ((2 : ENNReal) ^ m * (2 : ENNReal)⁻¹ ^ m) + r.value := by
          ring
    _ = e.mass.value + r.value := by rw [hcancel, mul_one]

/-- The raw rational total of the product list has exactly the same represented
value as the input raw list. -/
theorem codedPairUniformExtension_totalMassValue
    (P : CodedFiniteDistribution) (m : Nat) :
    (totalMassRat (codedPairUniformExtension P m).data).value =
      (totalMassRat P.data).value := by
  unfold codedPairUniformExtension totalMassRat
  induction P.data with
  | nil => rfl
  | cons e data ih =>
      simp only [List.flatMap_cons, List.foldr_append, List.foldr_cons]
      rw [codedPairUniformExtension_foldr_total_value]
      rw [RatMass.add_value, ih]

theorem codedPairUniformExtension_totalMass
    (P : CodedFiniteDistribution) (m : Nat) :
    (∑ z ∈ (codedPairUniformExtension P m).support,
        (codedPairUniformExtension P m).mass z) =
      ∑ a ∈ P.support, P.mass a := by
  rw [mass_total, mass_total, codedPairUniformExtension_totalMassValue]

theorem codedPairUniformExtension_isProbability
    (P : CodedFiniteDistribution) (m : Nat) :
    P.IsProbability →
      (codedPairUniformExtension P m).IsProbability := by
  intro h
  unfold CodedFiniteDistribution.IsProbability at *
  rw [codedPairUniformExtension_totalMass]
  exact h

theorem codedPairUniformExtensionCode_computable :
    Computable codedPairUniformExtensionCode := by
  have hm : Primrec (fun w : BitString =>
      CodedFiniteDistribution.decodeNatCode (decodeSecond w)) :=
    CodedFiniteDistribution.decodeNatCode_primrec.comp
      CodedFiniteDistribution.decodeSecond_primrec
  have hdata : Primrec (fun w : BitString =>
      CodedFiniteDistribution.decodeDistributionData (decodeFirst w)) :=
    CodedFiniteDistribution.decodeDistributionData_primrec.comp
      CodedFiniteDistribution.decodeFirst_primrec
  have hblock : Primrec (fun q : BitString × CodedDistributionEntry =>
      (allStrings (CodedFiniteDistribution.decodeNatCode (decodeSecond q.1))).map fun u =>
        ({ point := pairCode q.2.point u, mass := q.2.mass.scaleInvPow2
            (CodedFiniteDistribution.decodeNatCode (decodeSecond q.1)) } :
          CodedDistributionEntry)) := by
    refine Primrec.list_map
      (CodedFiniteDistribution.allStrings_primrec.comp (hm.comp Primrec.fst)) ?_
    have hpoint : Primrec
        (fun r : (BitString × CodedDistributionEntry) × BitString =>
          pairCode r.1.2.point r.2) :=
      CodedFiniteDistribution.pairCode_primrec.comp
        (CodedFiniteDistribution.entry_point_primrec.comp
          (Primrec.snd.comp Primrec.fst)) Primrec.snd
    have hmass : Primrec
        (fun r : (BitString × CodedDistributionEntry) × BitString =>
          r.1.2.mass.scaleInvPow2
            (CodedFiniteDistribution.decodeNatCode (decodeSecond r.1.1))) :=
      RatMass.scaleInvPow2_primrec.comp
        (CodedFiniteDistribution.entry_mass_primrec.comp
          (Primrec.snd.comp Primrec.fst))
        (hm.comp (Primrec.fst.comp Primrec.fst))
    exact (Primrec.of_equiv_symm.comp (hpoint.pair hmass)).to₂
  have hflat : Primrec (fun w : BitString =>
      (CodedFiniteDistribution.decodeDistributionData (decodeFirst w)).flatMap fun e =>
        (allStrings (CodedFiniteDistribution.decodeNatCode (decodeSecond w))).map fun u =>
          ({ point := pairCode e.point u, mass := e.mass.scaleInvPow2
              (CodedFiniteDistribution.decodeNatCode (decodeSecond w)) } :
            CodedDistributionEntry)) :=
    Primrec.list_flatMap hdata hblock.to₂
  exact (CodedFiniteDistribution.codedDistributionDataCode_primrec.comp hflat).to_comp

@[simp] theorem codedPairUniformExtensionCode_eq
    (P : CodedFiniteDistribution) (m : Nat) :
    codedPairUniformExtensionCode
        (pairCode P.code (natCode m)) =
      (codedPairUniformExtension P m).code := by
  simp [codedPairUniformExtensionCode, codedPairUniformExtension,
    CodedFiniteDistribution.code,
    CodedFiniteDistribution.decodeDistributionData_code,
    CodedFiniteDistribution.decodeNatCode_natCode,
    decodeFirst_pairCode, decodeSecond_pairCode]

theorem codedPairUniformExtension_complexity_le
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P m,
      (codedPairUniformExtension P m).complexity U ≤
        P.complexity U + (logSlack c m : ENat) := by
  obtain ⟨c_map, h_map⟩ := KPPlain_map_le U hU
    codedPairUniformExtensionCode codedPairUniformExtensionCode_computable
  obtain ⟨c_pair, h_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_nat, h_nat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c_map + c_pair + c_nat + 2, fun P m => ?_⟩
  unfold CodedFiniteDistribution.complexity
  rw [← codedPairUniformExtensionCode_eq P m]
  calc
    KPPlain U (codedPairUniformExtensionCode (pairCode P.code (natCode m)))
        ≤ KPPlain U (pairCode P.code (natCode m)) + (c_map : ENat) :=
          h_map _
    _ = KPPair U P.code (natCode m) + (c_map : ENat) := rfl
    _ ≤ (KPPlain U P.code + KPPlain U (natCode m) + (c_pair : ENat)) +
          (c_map : ENat) := by
        gcongr
        exact h_pair _ _
    _ ≤ (KPPlain U P.code +
          (2 * (Nat.bits m).length + (c_nat : ENat)) + (c_pair : ENat)) +
          (c_map : ENat) := by
        gcongr
        exact h_nat m
    _ ≤ KPPlain U P.code +
          (logSlack (c_map + c_pair + c_nat + 2) m : ENat) := by
        have hslack :
            2 * (Nat.bits m).length + c_nat + c_pair + c_map ≤
              logSlack (c_map + c_pair + c_nat + 2) m := by
          unfold logSlack
          nlinarith [Nat.zero_le ((Nat.bits m).length)]
        rw [show (KPPlain U P.code +
              ((2 * (Nat.bits m).length : ENat) + (c_nat : ENat))) +
              (c_pair : ENat) + (c_map : ENat) =
            KPPlain U P.code +
              ((2 * (Nat.bits m).length + c_nat + c_pair + c_map : Nat) : ENat) by
          push_cast
          ring]
        gcongr

end Kolmogorov
