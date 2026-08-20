import KolmogorovMathlib.CommonInformation.IncidenceRectangleCapacity
import KolmogorovMathlib.CommonInformation.IncidenceCapacityCover
import KolmogorovMathlib.CommonInformation.RegionConsequences

/-!
# Exercise 312: the common-information region is the same for all high-complexity edges

This file completes SUV Exercise 312, including the effective-sufficiency
construction `incidence_capacity_sufficient`.

The two directions of the source's capacity criterion are:

* **Necessity** — `incidence_region_capacity_necessary`
  (proved in `IncidenceRectangleCapacity.lean`): every triple in the region of a
  high-complexity concrete incident edge forces
  `2^{3n} ≤ 2^{α + O(log n)} · concreteIncidenceCapacity n (2^β) (2^γ)`.
* **Sufficiency** — `incidence_capacity_sufficient` (proved in this file): the
  capacity criterion `2^{3n} ≤ 2^α · capacity` puts the
  inflated triple back inside the region of *every* concrete incident edge, via
  the computable `incidenceCapacityShearCover` and its rank decoders.

Because the capacity `concreteIncidenceCapacity n (2^β) (2^γ)` depends only on
`n, β, γ` and **never on the edge**, chaining necessity (for the source edge)
with sufficiency (for the target edge) shows the two regions coincide up to a
uniform `logSlack C n`.  This is the content of
`exercise_312_incidence_region_criterion` (the two-directional criterion, fully
derived here) and `exercise_312_incidence_region_uniformity` (the public
uniformity endpoint, fully derived here).  The `α`-shift in the derivation is
absorbed by the additivity `logSlack c₁ n + logSlack c₂ n = logSlack (c₁+c₂) n`.
-/

namespace Kolmogorov

open AffineIncidence

/-- Selector input: fixed-width rank and the region parameters. -/
def incidenceCapacityCoverRankInput (n β γ : Nat) (rank : BitString) : BitString :=
  pairCode (listCode [Nat.bits n, Nat.bits β, Nat.bits γ]) rank

lemma incidenceCapacityCoverRankInput_length (n β γ : Nat) (rank : BitString) :
    (incidenceCapacityCoverRankInput n β γ rank).length =
      rank.length + 4 * ((Nat.bits n).length + (Nat.bits β).length +
        (Nat.bits γ).length) + 7 := by
  simp [incidenceCapacityCoverRankInput, length_pairCode]
  omega

private def incidenceCapacityCoverParameters (input : BitString) : Nat × Nat × Nat :=
  let pList := decodeListCode (decodeFirst input)
  (bitsToNat (pList.getD 0 []),
    bitsToNat (pList.getD 1 []),
    bitsToNat (pList.getD 2 []))

private lemma incidenceCapacityCoverParameters_primrec :
    Primrec incidenceCapacityCoverParameters := by
  have hpList : Primrec (fun input : BitString =>
      decodeListCode (decodeFirst input)) :=
    decodeListCode_primrec.comp decodeFirst_primrec'
  have hget (i : Nat) : Primrec (fun input : BitString =>
      (decodeListCode (decodeFirst input)).getD i []) :=
    (Primrec.list_getD ([] : BitString)).comp hpList (Primrec.const i)
  have hn (i : Nat) : Primrec (fun input : BitString =>
      bitsToNat ((decodeListCode (decodeFirst input)).getD i [])) :=
    bitsToNat_primrec.comp (hget i)
  exact (Primrec.pair (hn 0) (Primrec.pair (hn 1) (hn 2))).of_eq
    (fun _ => rfl)

private def incidenceCapacityCoverRankValue (input : BitString) : Nat :=
  decodeFixedWidthNatCode (decodeSecond input)

private lemma incidenceCapacityCoverRankValue_primrec :
    Primrec incidenceCapacityCoverRankValue :=
  (decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec').of_eq
    (fun _ => rfl)

@[simp] private lemma incidenceCapacityCoverParameters_rankInput
    (n β γ : Nat) (rank : BitString) :
    incidenceCapacityCoverParameters
      (incidenceCapacityCoverRankInput n β γ rank) = (n, β, γ) := by
  simp only [incidenceCapacityCoverParameters, incidenceCapacityCoverRankInput,
    decodeFirst_pairCode, decodeListCode_listCode, List.getD_cons_zero,
    List.getD_cons_succ, bitsToNat_bits]

@[simp] private lemma incidenceCapacityCoverRankValue_rankInput
    (n β γ : Nat) (rank : BitString) :
    incidenceCapacityCoverRankValue
      (incidenceCapacityCoverRankInput n β γ rank) =
        decodeFixedWidthNatCode rank := by
  rw [incidenceCapacityCoverRankValue, incidenceCapacityCoverRankInput,
    decodeSecond_pairCode]

private def incidenceCapacityCoverBudgets (input : BitString) : Nat × Nat × Nat :=
  let params := incidenceCapacityCoverParameters input
  (params.1, 2 ^ params.2.1, 2 ^ params.2.2)

private lemma incidenceCapacityCoverBudgets_primrec :
    Primrec incidenceCapacityCoverBudgets := by
  have hn : Primrec (fun input : BitString =>
      (incidenceCapacityCoverParameters input).1) :=
    Primrec.fst.comp incidenceCapacityCoverParameters_primrec
  have hβ : Primrec (fun input : BitString =>
      (incidenceCapacityCoverParameters input).2.1) :=
    (Primrec.fst.comp Primrec.snd).comp incidenceCapacityCoverParameters_primrec
  have hγ : Primrec (fun input : BitString =>
      (incidenceCapacityCoverParameters input).2.2) :=
    (Primrec.snd.comp Primrec.snd).comp incidenceCapacityCoverParameters_primrec
  exact (Primrec.pair hn
    (Primrec.pair (CodedFiniteDistribution.twoPow_primrec.comp hβ)
      (CodedFiniteDistribution.twoPow_primrec.comp hγ))).of_eq
      (fun _ => rfl)

private def incidenceCapacityCoverCodeAt (input : BitString) : BitString :=
  let params := incidenceCapacityCoverBudgets input
  (incidenceCapacityShearCoverCode params.1 params.2.1 params.2.2).getD
    (incidenceCapacityCoverRankValue input) []

private lemma incidenceCapacityCoverCodeAt_primrec :
    Primrec incidenceCapacityCoverCodeAt := by
  have hcover : Primrec (fun input : BitString =>
      incidenceCapacityShearCoverCode
        (incidenceCapacityCoverBudgets input).1
        (incidenceCapacityCoverBudgets input).2.1
        (incidenceCapacityCoverBudgets input).2.2) :=
    incidenceCapacityShearCover_primrec.comp incidenceCapacityCoverBudgets_primrec
  exact ((Primrec.list_getD ([] : BitString)).comp hcover
    incidenceCapacityCoverRankValue_primrec).of_eq (fun _ => rfl)

/-- Partrec selector recovering the cover member code from its fixed-width rank. -/
def incidenceCapacityCoverSelector : BitString →. BitString := fun input =>
  Part.some (incidenceCapacityCoverCodeAt input)

lemma incidenceCapacityCoverSelector_partrec :
    Partrec incidenceCapacityCoverSelector := by
  exact incidenceCapacityCoverCodeAt_primrec.to_comp.partrec

lemma incidenceCapacityCoverSelector_recovers_cover (n β γ s rank : Nat) :
    rank < (incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).length →
    rank < 2 ^ s →
    (incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).getD rank [] ∈
      incidenceCapacityCoverSelector
        (incidenceCapacityCoverRankInput n β γ (fixedWidthNatCode rank s)) := by
  intro _ _
  simp [incidenceCapacityCoverSelector, incidenceCapacityCoverCodeAt,
    incidenceCapacityCoverBudgets, decodeFixedWidthNatCode_encode]

lemma plainK_incidenceCapacityCoverRank_le (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ n β γ s rank,
      rank < (incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).length →
      rank < 2 ^ s →
      plainK V (incidenceCapacityCoverRankInput n β γ (fixedWidthNatCode rank s))
        ≤ ((s + 4 * ((Nat.bits n).length + (Nat.bits β).length +
                   (Nat.bits γ).length) + 9 + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := plainKLeLength V hV
  refine ⟨C, ?_⟩
  intro n β γ s rank _ hrank
  have hlen :
      (incidenceCapacityCoverRankInput n β γ
        (fixedWidthNatCode rank s)).length =
        s + 4 * ((Nat.bits n).length + (Nat.bits β).length +
          (Nat.bits γ).length) + 7 := by
    rw [incidenceCapacityCoverRankInput_length, fixedWidthNatCode_length hrank]
  calc
    plainK V (incidenceCapacityCoverRankInput n β γ
        (fixedWidthNatCode rank s))
        ≤ ((incidenceCapacityCoverRankInput n β γ
            (fixedWidthNatCode rank s)).length : ENat) + (C : ENat) := hC _
    _ ≤ ((s + 4 * ((Nat.bits n).length + (Nat.bits β).length +
          (Nat.bits γ).length) + 9 + C : Nat) : ENat) := by
      rw [hlen]
      exact_mod_cast (by omega :
        s + 4 * ((Nat.bits n).length + (Nat.bits β).length +
          (Nat.bits γ).length) + 7 + C ≤
        s + 4 * ((Nat.bits n).length + (Nat.bits β).length +
          (Nat.bits γ).length) + 9 + C)

private lemma incidenceCapacityShearCoverCode_decode_mem
    (n b c : Nat) {w : BitString}
    (hw : w ∈ incidenceCapacityShearCoverCode n b c) :
    concreteIncidenceRectangleDecode n w ∈ incidenceCapacityShearCover n b c := by
  rw [incidenceCapacityShearCover, concreteIncidenceRectangleFamilyDecode,
    List.mem_toFinset, List.mem_map]
  exact ⟨w, hw, rfl⟩

private lemma point_mem_rectangleCode_side_iff (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)))
    (P : Point (ConcreteField n)) :
    concretePointCode n P ∈
        decodeListCode (decodeFirst (concreteIncidenceRectangleCode n R)) ↔
      P ∈ R.1 := by
  rw [concreteIncidenceRectangleCode, decodeFirst_pairCode,
    decodeListCode_listCode, mem_canonicalFinsetList]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨Q, hQ, hcode⟩
    have hQP : Q = P := concretePointCode_injective n hcode
    simpa [hQP] using hQ
  · intro hP
    exact ⟨P, hP, rfl⟩

private lemma line_mem_rectangleCode_side_iff (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n)))
    (L : Line (ConcreteField n)) :
    concreteLineCode n L ∈
        decodeListCode (decodeSecond (concreteIncidenceRectangleCode n R)) ↔
      L ∈ R.2 := by
  rw [concreteIncidenceRectangleCode, decodeSecond_pairCode,
    decodeListCode_listCode, mem_canonicalFinsetList]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨M, hM, hcode⟩
    have hML : M = L := concreteLineCode_injective n hcode
    simpa [hML] using hM
  · intro hL
    exact ⟨L, hL, rfl⟩

private lemma point_rectangleCode_side_length (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    (decodeListCode (decodeFirst (concreteIncidenceRectangleCode n R))).length =
      R.1.card := by
  rw [concreteIncidenceRectangleCode, decodeFirst_pairCode,
    decodeListCode_listCode, length_canonicalFinsetList,
    Finset.card_image_of_injective _ (concretePointCode_injective n)]

private lemma line_rectangleCode_side_length (n : Nat)
    (R : CombinatorialRectangle (Point (ConcreteField n)) (Line (ConcreteField n))) :
    (decodeListCode (decodeSecond (concreteIncidenceRectangleCode n R))).length =
      R.2.card := by
  rw [concreteIncidenceRectangleCode, decodeSecond_pairCode,
    decodeListCode_listCode, length_canonicalFinsetList,
    Finset.card_image_of_injective _ (concreteLineCode_injective n)]

/-- Partrec selector recovering the point from the cover member's point side. -/
def incidenceCapacityPointSelector : BitString → BitString →. BitString :=
  fun context program => Part.some
    ((decodeListCode (decodeFirst (incidenceCapacityCoverCodeAt context))).getD
      (decodeFixedWidthNatCode program) [])

lemma incidenceCapacityPointSelector_partrec :
    Partrec₂ incidenceCapacityPointSelector := by
  have hside : Primrec (fun q : BitString × BitString =>
      decodeListCode (decodeFirst (incidenceCapacityCoverCodeAt q.1))) :=
    decodeListCode_primrec.comp
      (decodeFirst_primrec'.comp
        (incidenceCapacityCoverCodeAt_primrec.comp Primrec.fst))
  have hrank : Primrec (fun q : BitString × BitString =>
      decodeFixedWidthNatCode q.2) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.snd
  exact ((Primrec.list_getD ([] : BitString)).comp hside hrank).to_comp.partrec

lemma condK_concretePoint_given_coverRank_le (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ n β γ s rank P,
      rank < (incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).length →
      P ∈ (concreteIncidenceRectangleDecode n
        ((incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).getD rank [])).1 →
      condK V (concretePointCode n P)
        (incidenceCapacityCoverRankInput n β γ (fixedWidthNatCode rank s))
        ≤ ((β + 2 * (Nat.bits β).length + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
    incidenceCapacityPointSelector incidenceCapacityPointSelector_partrec
  refine ⟨C, ?_⟩
  intro n β γ s rank P hrank hP
  let codes := incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)
  let w := codes.getD rank []
  have hw : w ∈ codes := by
    dsimp only [w]
    rw [List.getD_eq_getElem codes [] hrank]
    exact List.getElem_mem hrank
  have hcap : 0 < concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) :=
    capacity_pos n (2 ^ β) (2 ^ γ) (pow_pos (by omega) _) (pow_pos (by omega) _)
  have hRmem := incidenceCapacityShearCoverCode_decode_mem n (2 ^ β) (2 ^ γ) hw
  have hwCanonical := hw
  dsimp only [codes] at hwCanonical
  rw [incidenceCapacityShearCoverCode,
    if_neg (Nat.ne_of_gt hcap), List.mem_map] at hwCanonical
  obtain ⟨g, _hg, hgw⟩ := hwCanonical
  let R := shearRectangle g (incidenceCapacityRectangle n (2 ^ β) (2 ^ γ))
  have hgw' : concreteIncidenceRectangleCode n R = w := by
    simpa only [R] using hgw
  rw [← hgw', concreteIncidenceRectangleDecode_code] at hRmem
  have hRcard : R.1.card ≤ 2 ^ β :=
    (incidenceCapacityShearCover_member_spec n (2 ^ β) (2 ^ γ) hcap R hRmem).1
  have hPR : P ∈ R.1 := by
    have := hP
    change P ∈ (concreteIncidenceRectangleDecode n w).1 at this
    rwa [← hgw', concreteIncidenceRectangleDecode_code] at this
  let side := decodeListCode (decodeFirst w)
  have hPointCode : concretePointCode n P ∈ side := by
    dsimp only [side]
    rw [← hgw']
    exact (point_mem_rectangleCode_side_iff n R P).2 hPR
  let endpointRank := side.idxOf (concretePointCode n P)
  have hEndpointRank : endpointRank < side.length :=
    List.idxOf_lt_length_of_mem hPointCode
  have hsideLength : side.length = R.1.card := by
    dsimp only [side]
    rw [← hgw']
    exact point_rectangleCode_side_length n R
  have hEndpointPow : endpointRank < 2 ^ β := by omega
  have hget : side.getD endpointRank [] = concretePointCode n P := by
    rw [List.getD_eq_getElem side [] hEndpointRank]
    exact List.idxOf_get hEndpointRank
  let context := incidenceCapacityCoverRankInput n β γ (fixedWidthNatCode rank s)
  let program := fixedWidthNatCode endpointRank β
  have hrec : concretePointCode n P ∈ incidenceCapacityPointSelector context program := by
    rw [incidenceCapacityPointSelector, Part.mem_some_iff]
    dsimp only [context, program]
    simp only [incidenceCapacityCoverCodeAt, incidenceCapacityCoverBudgets,
      incidenceCapacityCoverParameters_rankInput, incidenceCapacityCoverRankValue_rankInput,
      decodeFixedWidthNatCode_encode]
    change concretePointCode n P = side.getD endpointRank []
    exact hget.symm
  calc
    condK V (concretePointCode n P) context
        ≤ (program.length : ENat) + (C : ENat) := hC context program _ hrec
    _ = ((β + C : Nat) : ENat) := by
      rw [show program.length = β by
        exact fixedWidthNatCode_length hEndpointPow]
      push_cast
      rfl
    _ ≤ ((β + 2 * (Nat.bits β).length + C : Nat) : ENat) := by
      exact_mod_cast (by omega : β + C ≤ β + 2 * (Nat.bits β).length + C)

/-- Partrec selector recovering the line from the cover member's line side. -/
def incidenceCapacityLineSelector : BitString → BitString →. BitString :=
  fun context program => Part.some
    ((decodeListCode (decodeSecond (incidenceCapacityCoverCodeAt context))).getD
      (decodeFixedWidthNatCode program) [])

lemma incidenceCapacityLineSelector_partrec :
    Partrec₂ incidenceCapacityLineSelector := by
  have hside : Primrec (fun q : BitString × BitString =>
      decodeListCode (decodeSecond (incidenceCapacityCoverCodeAt q.1))) :=
    decodeListCode_primrec.comp
      (decodeSecond_primrec'.comp
        (incidenceCapacityCoverCodeAt_primrec.comp Primrec.fst))
  have hrank : Primrec (fun q : BitString × BitString =>
      decodeFixedWidthNatCode q.2) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.snd
  exact ((Primrec.list_getD ([] : BitString)).comp hside hrank).to_comp.partrec

lemma condK_concreteLine_given_coverRank_le (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ n β γ s rank L,
      rank < (incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).length →
      L ∈ (concreteIncidenceRectangleDecode n
        ((incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)).getD rank [])).2 →
      condK V (concreteLineCode n L)
        (incidenceCapacityCoverRankInput n β γ (fixedWidthNatCode rank s))
        ≤ ((γ + 2 * (Nat.bits γ).length + C : Nat) : ENat) := by
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le V hV
    incidenceCapacityLineSelector incidenceCapacityLineSelector_partrec
  refine ⟨C, ?_⟩
  intro n β γ s rank L hrank hL
  let codes := incidenceCapacityShearCoverCode n (2 ^ β) (2 ^ γ)
  let w := codes.getD rank []
  have hw : w ∈ codes := by
    dsimp only [w]
    rw [List.getD_eq_getElem codes [] hrank]
    exact List.getElem_mem hrank
  have hcap : 0 < concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) :=
    capacity_pos n (2 ^ β) (2 ^ γ) (pow_pos (by omega) _) (pow_pos (by omega) _)
  have hRmem := incidenceCapacityShearCoverCode_decode_mem n (2 ^ β) (2 ^ γ) hw
  have hwCanonical := hw
  dsimp only [codes] at hwCanonical
  rw [incidenceCapacityShearCoverCode,
    if_neg (Nat.ne_of_gt hcap), List.mem_map] at hwCanonical
  obtain ⟨g, _hg, hgw⟩ := hwCanonical
  let R := shearRectangle g (incidenceCapacityRectangle n (2 ^ β) (2 ^ γ))
  have hgw' : concreteIncidenceRectangleCode n R = w := by
    simpa only [R] using hgw
  rw [← hgw', concreteIncidenceRectangleDecode_code] at hRmem
  have hRcard : R.2.card ≤ 2 ^ γ :=
    (incidenceCapacityShearCover_member_spec n (2 ^ β) (2 ^ γ) hcap R hRmem).2.1
  have hLR : L ∈ R.2 := by
    have := hL
    change L ∈ (concreteIncidenceRectangleDecode n w).2 at this
    rwa [← hgw', concreteIncidenceRectangleDecode_code] at this
  let side := decodeListCode (decodeSecond w)
  have hLineCode : concreteLineCode n L ∈ side := by
    dsimp only [side]
    rw [← hgw']
    exact (line_mem_rectangleCode_side_iff n R L).2 hLR
  let endpointRank := side.idxOf (concreteLineCode n L)
  have hEndpointRank : endpointRank < side.length :=
    List.idxOf_lt_length_of_mem hLineCode
  have hsideLength : side.length = R.2.card := by
    dsimp only [side]
    rw [← hgw']
    exact line_rectangleCode_side_length n R
  have hEndpointPow : endpointRank < 2 ^ γ := by omega
  have hget : side.getD endpointRank [] = concreteLineCode n L := by
    rw [List.getD_eq_getElem side [] hEndpointRank]
    exact List.idxOf_get hEndpointRank
  let context := incidenceCapacityCoverRankInput n β γ (fixedWidthNatCode rank s)
  let program := fixedWidthNatCode endpointRank γ
  have hrec : concreteLineCode n L ∈ incidenceCapacityLineSelector context program := by
    rw [incidenceCapacityLineSelector, Part.mem_some_iff]
    dsimp only [context, program]
    simp only [incidenceCapacityCoverCodeAt, incidenceCapacityCoverBudgets,
      incidenceCapacityCoverParameters_rankInput, incidenceCapacityCoverRankValue_rankInput,
      decodeFixedWidthNatCode_encode]
    change concreteLineCode n L = side.getD endpointRank []
    exact hget.symm
  calc
    condK V (concreteLineCode n L) context
        ≤ (program.length : ENat) + (C : ENat) := hC context program _ hrec
    _ = ((γ + C : Nat) : ENat) := by
      rw [show program.length = γ by
        exact fixedWidthNatCode_length hEndpointPow]
      push_cast
      rfl
    _ ≤ ((γ + 2 * (Nat.bits γ).length + C : Nat) : ENat) := by
      exact_mod_cast (by omega : γ + C ≤ γ + 2 * (Nat.bits γ).length + C)

/-- Conditional-budget clamp for the common-information region. -/
lemma incidence_region_large_coordinate (V : Map) (hV : isOptimalConditional V) :
    ∃ c₀ : Nat, ∀ (α β γ : Nat) (x y : BitString),
      (α, β, γ) ∈ CommonInformationRegion V x y →
      (α, min β (x.length + c₀), min γ (y.length + c₀)) ∈ CommonInformationRegion V x y := by
  obtain ⟨cLength, hLength⟩ := plainKLeLength V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  refine ⟨cLength + cCond + 1, ?_⟩
  rintro α β γ x y ⟨z, hz, hx, hy⟩
  refine ⟨z, hz, ?_, ?_⟩
  · have hxLength : condK V x z <
        ((x.length + (cLength + cCond + 1) : Nat) : ENat) := by
      calc
        condK V x z ≤ plainK V x + (cCond : ENat) := hCond x z
        _ ≤ ((x.length : ENat) + (cLength : ENat)) + (cCond : ENat) := by
          gcongr
          exact hLength x
        _ = ((x.length + cLength + cCond : Nat) : ENat) := by
          push_cast
          rfl
        _ < ((x.length + (cLength + cCond + 1) : Nat) : ENat) := by
          exact_mod_cast (by omega :
            x.length + cLength + cCond < x.length + (cLength + cCond + 1))
    exact lt_min hx hxLength
  · have hyLength : condK V y z <
        ((y.length + (cLength + cCond + 1) : Nat) : ENat) := by
      calc
        condK V y z ≤ plainK V y + (cCond : ENat) := hCond y z
        _ ≤ ((y.length : ENat) + (cLength : ENat)) + (cCond : ENat) := by
          gcongr
          exact hLength y
        _ = ((y.length + cLength + cCond : Nat) : ENat) := by
          push_cast
          rfl
        _ < ((y.length + (cLength + cCond + 1) : Nat) : ENat) := by
          exact_mod_cast (by omega :
            y.length + cLength + cCond < y.length + (cLength + cCond + 1))
    exact lt_min hy hyLength

/-- Exponent-level form of the rectangle-capacity clamp.  Conditional budgets
larger than the fixed point/line code length `2*(n+1)` do not change the
capacity, because the plane has at most `2^(2*(n+1))` vertices on either side. -/
lemma concreteIncidenceCapacity_pow_clamp (n β γ : Nat) :
    concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) =
      concreteIncidenceCapacity n (2 ^ min β (2 * (n + 1)))
        (2 ^ min γ (2 * (n + 1))) := by
  let q := concretePrime n
  have hqpow : q ^ 2 ≤ 2 ^ (2 * (n + 1)) := by
    calc
      q ^ 2 ≤ (2 ^ (n + 1)) ^ 2 := Nat.pow_le_pow_left (concretePrime_upper n) 2
      _ = 2 ^ (2 * (n + 1)) := by rw [← pow_mul]; congr 1; omega
  have clampPow (k : Nat) :
      min (2 ^ k) (q ^ 2) = min (2 ^ min k (2 * (n + 1))) (q ^ 2) := by
    by_cases hk : k ≤ 2 * (n + 1)
    · rw [min_eq_left hk]
    · have hbound : 2 * (n + 1) ≤ k := by omega
      have hqk : q ^ 2 ≤ 2 ^ k :=
        hqpow.trans (Nat.pow_le_pow_right (by decide) hbound)
      rw [min_eq_right hqk, min_eq_right hbound, min_eq_right hqpow]
  calc
    concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) =
        concreteIncidenceCapacity n (min (2 ^ β) (q ^ 2))
          (min (2 ^ γ) (q ^ 2)) := concreteIncidenceCapacity_clamp n _ _
    _ = concreteIncidenceCapacity n
          (min (2 ^ min β (2 * (n + 1))) (q ^ 2))
          (min (2 ^ min γ (2 * (n + 1))) (q ^ 2)) := by
        rw [clampPow β, clampPow γ]
    _ = concreteIncidenceCapacity n (2 ^ min β (2 * (n + 1)))
          (2 ^ min γ (2 * (n + 1))) :=
      (concreteIncidenceCapacity_clamp n _ _).symm

/-- The executable cover-code list satisfies the same weighted polynomial
bound as the geometric cover.  This list-length form is what the fixed-width
rank decoder actually needs; a finset-cardinality bound would not suffice in
the presence of duplicate codes. -/
lemma incidenceCapacityShearCoverCode_length_mul_le (n b c : Nat) :
    (incidenceCapacityShearCoverCode n b c).length *
        concreteIncidenceCapacity n b c ≤
      (incidentEdges (ConcreteField n)).card *
        (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) := by
  by_cases hK : concreteIncidenceCapacity n b c = 0
  · simp [hK]
  have hcodeLength : (incidenceCapacityShearCoverCode n b c).length =
      (incidenceCapacityShearParams n b c).length := by
    rw [incidenceCapacityShearCoverCode, if_neg hK, List.length_map]
  have hparamLength : (incidenceCapacityShearParams n b c).length ≤
      (incidentEdges (ConcreteField n)).card *
        (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) /
          concreteIncidenceCapacity n b c := by
    have h := computableGreedyCover_length_le
      (concreteIncidentEdgeList n) (concreteShearParams n)
      (shearRectangleEdgeList n (incidenceCapacityRectangle n b c))
      (concreteIncidenceCapacity n b c)
      ((concreteIncidentEdgeList n).length *
        (Nat.log2 (concreteIncidentEdgeList n).length + 1) /
          concreteIncidenceCapacity n b c)
    simpa [incidenceCapacityShearParams, incidentEdges_card,
      concreteField_card_eq] using h
  calc
    (incidenceCapacityShearCoverCode n b c).length *
          concreteIncidenceCapacity n b c
        ≤ ((incidentEdges (ConcreteField n)).card *
            (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) /
              concreteIncidenceCapacity n b c) *
            concreteIncidenceCapacity n b c := by
          apply Nat.mul_le_mul_right
          exact hcodeLength.le.trans hparamLength
    _ ≤ (incidentEdges (ConcreteField n)).card *
          (Nat.log2 (incidentEdges (ConcreteField n)).card + 1) :=
      Nat.div_mul_le_self _ _

/-- A capacity-sufficient cover has an `α + O(log n)`-bit fixed-width rank
after clamping the two side exponents. -/
lemma incidenceCapacityShearCoverCode_length_lt_pow
    (n α β γ : Nat)
    (hcap : 2 ^ (3 * n) ≤
      2 ^ α * concreteIncidenceCapacity n (2 ^ β) (2 ^ γ)) :
    let β' := min β (2 * (n + 1))
    let γ' := min γ (2 * (n + 1))
    (incidenceCapacityShearCoverCode n (2 ^ β') (2 ^ γ')).length <
      2 ^ (α + (Nat.bits n).length + 8) := by
  intro β' γ'
  let K := concreteIncidenceCapacity n (2 ^ β') (2 ^ γ')
  let E := (incidentEdges (ConcreteField n)).card
  let B := (Nat.bits n).length
  let L := (incidenceCapacityShearCoverCode n (2 ^ β') (2 ^ γ')).length
  have hK : 0 < K := by
    exact capacity_pos n (2 ^ β') (2 ^ γ')
      (pow_pos (by omega) _) (pow_pos (by omega) _)
  have hcap' : 2 ^ (3 * n) ≤ 2 ^ α * K := by
    dsimp only [K, β', γ']
    rw [← concreteIncidenceCapacity_pow_clamp n β γ]
    exact hcap
  have hweighted : L * K ≤ E * (Nat.log2 E + 1) := by
    simpa only [L, K, E] using
      incidenceCapacityShearCoverCode_length_mul_le n (2 ^ β') (2 ^ γ')
  have hEbounds := concreteIncidentEdges_card_bounds n
  have hEupper : E ≤ 2 ^ (3 * n + 3) := by
    simpa only [E] using hEbounds.2
  have hEne : E ≠ 0 := by
    have hElower : 2 ^ (3 * n) < E := by
      simpa only [E] using hEbounds.1
    exact Nat.ne_of_gt ((pow_pos (by omega) _).trans hElower)
  have hlog : Nat.log2 E + 1 ≤ 3 * n + 4 := by
    have hltpow : E < 2 ^ (3 * n + 4) :=
      hEupper.trans_lt (Nat.pow_lt_pow_succ (by norm_num : 1 < 2))
    have hloglt : Nat.log 2 E < 3 * n + 4 :=
      Nat.log_lt_of_lt_pow hEne hltpow
    rw [Nat.log2_eq_log_two]
    omega
  have hEcap : E ≤ 2 ^ (α + 3) * K := by
    calc
      E ≤ 2 ^ (3 * n + 3) := hEupper
      _ = 8 * 2 ^ (3 * n) := by rw [pow_add]; norm_num; ring
      _ ≤ 8 * (2 ^ α * K) := Nat.mul_le_mul_left 8 hcap'
      _ = 2 ^ (α + 3) * K := by rw [pow_add]; norm_num; ring
  have hnBits : n + 1 ≤ 2 ^ B := by
    have := lt_two_pow_length_natBits n
    dsimp only [B]
    omega
  have hpoly : 3 * n + 4 < 2 ^ (B + 5) := by
    calc
      3 * n + 4 ≤ 4 * (n + 1) := by omega
      _ ≤ 4 * 2 ^ B := Nat.mul_le_mul_left 4 hnBits
      _ = 2 ^ (B + 2) := by rw [pow_add]; norm_num; ring
      _ < 2 ^ (B + 5) := by
        apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
        omega
  have hmul : L * K < 2 ^ (α + B + 8) * K := by
    calc
      L * K ≤ E * (Nat.log2 E + 1) := hweighted
      _ ≤ (2 ^ (α + 3) * K) * (3 * n + 4) :=
        Nat.mul_le_mul hEcap hlog
      _ < (2 ^ (α + 3) * K) * 2 ^ (B + 5) :=
        Nat.mul_lt_mul_of_pos_left hpoly (mul_pos (pow_pos (by omega) _) hK)
      _ = (2 ^ (α + 3) * 2 ^ (B + 5)) * K := by ring
      _ = 2 ^ ((α + 3) + (B + 5)) * K := by
        exact congrArg (fun x : Nat => x * K) (pow_add 2 (α + 3) (B + 5)).symm
      _ = 2 ^ (α + B + 8) * K := by
        exact congrArg (fun exponent : Nat => 2 ^ exponent * K) (by omega)
  exact (Nat.mul_lt_mul_right hK).mp hmul

/-- Every concrete incident edge has a genuine list rank in the executable
capacity cover, with both endpoints in the decoded rectangle at that rank. -/
lemma exists_incidenceCapacityShearCoverCode_rank (n b c : Nat)
    (e : ConcreteIncidentEdge n) :
    ∃ rank,
      rank < (incidenceCapacityShearCoverCode n b c).length ∧
      e.1.1 ∈ (concreteIncidenceRectangleDecode n
        ((incidenceCapacityShearCoverCode n b c).getD rank [])).1 ∧
      e.1.2 ∈ (concreteIncidenceRectangleDecode n
        ((incidenceCapacityShearCoverCode n b c).getD rank [])).2 := by
  classical
  have heCover := incidenceCapacityShearCover_covers n b c e.2
  letI : DecidableEq (Point (ConcreteField n) × Line (ConcreteField n)) :=
    @instDecidableEqProd _ _ (Classical.decEq _) (Classical.decEq _)
  rw [rectangleFamilyEdges, Finset.mem_biUnion] at heCover
  obtain ⟨R, hR, heR⟩ := heCover
  rw [incidenceCapacityShearCover, concreteIncidenceRectangleFamilyDecode,
    List.mem_toFinset, List.mem_map] at hR
  obtain ⟨w, hw, rfl⟩ := hR
  let rank := (incidenceCapacityShearCoverCode n b c).idxOf w
  have hrank : rank < (incidenceCapacityShearCoverCode n b c).length :=
    List.idxOf_lt_length_of_mem hw
  have hget : (incidenceCapacityShearCoverCode n b c).getD rank [] = w := by
    rw [List.getD_eq_getElem _ _ hrank]
    exact List.idxOf_get hrank
  rw [mem_interedges_iff_of_decidable] at heR
  refine ⟨rank, hrank, ?_, ?_⟩
  · rw [hget]
    exact heR.1
  · rw [hget]
    exact heR.2.1

/-- **Exercise 312, effective sufficiency direction.**

If the capacity criterion `2^{3n} ≤ 2^α · concreteIncidenceCapacity n (2^β) (2^γ)`
holds, then the triple `(α, β, γ)`, inflated by a uniform `logSlack C' n`, lies in
the common-information region of *every* concrete incident edge of the plane over
`GF(concretePrime n)`.

The intended witness `z` is the fixed-width rank, in `incidenceCapacityShearCover`,
of the first cover member containing the edge:

* `plainK V z ≤ α + O(log n)` because the cover has `≤ 2^α · poly` members
  (`incidenceCapacityShearCover_card_mul_le` combined with the capacity criterion);
* `condK V x z ≤ β + O(log n)` and `condK V y z ≤ γ + O(log n)` because, given the
  cover-member rank, the point `x` and line `y` are determined by their ranks
  inside that member's two sides, of sizes `≤ 2^β`, `≤ 2^γ`
  (`incidenceCapacityShearCover_member_spec`).

This is the one genuinely effective (decoder-constructing) step of Exercise 312;
the necessity direction and the two public endpoints below are pure assembly. -/
lemma incidence_capacity_sufficient
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C' N, ∀ n, N ≤ n →
      ∀ (e : ConcreteIncidentEdge n) (α β γ : Nat),
        2 ^ (3 * n) ≤ 2 ^ α * concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) →
        commonInformationTripleInflate (logSlack C' n) (α, β, γ) ∈
          CommonInformationRegion V
            (concretePointCode n e.1.1) (concreteLineCode n e.1.2) := by
  obtain ⟨Cplain, hplain⟩ := plainK_incidenceCapacityCoverRank_le V hV
  obtain ⟨Cpoint, hpoint⟩ := condK_concretePoint_given_coverRank_le V hV
  obtain ⟨Cline, hline⟩ := condK_concreteLine_given_coverRank_le V hV
  obtain ⟨CplainFold, hplainFold⟩ := logSlack_linear_bound 13 2 2
  obtain ⟨CcoordFold, hcoordFold⟩ := logSlack_linear_bound 2 2 2
  let CplainTotal := CplainFold + (4 + Cplain)
  let CpointTotal := CcoordFold + Cpoint
  let ClineTotal := CcoordFold + Cline
  let Cbase := max CplainTotal (max CpointTotal ClineTotal)
  let Cfinal := Cbase + 1
  refine ⟨Cfinal, 0, ?_⟩
  intro n _hn e α β γ hcap
  let β' := min β (2 * (n + 1))
  let γ' := min γ (2 * (n + 1))
  let B := (Nat.bits n).length
  let s := α + B + 8
  obtain ⟨rank, hrank, hpointMem, hlineMem⟩ :=
    exists_incidenceCapacityShearCoverCode_rank n (2 ^ β') (2 ^ γ') e
  have hrankPow : rank < 2 ^ s := by
    exact hrank.trans (by
      simpa only [s, B] using
        incidenceCapacityShearCoverCode_length_lt_pow n α β γ hcap)
  let z := incidenceCapacityCoverRankInput n β' γ' (fixedWidthNatCode rank s)
  have hzBound := hplain n β' γ' s rank hrank hrankPow
  have hxBound := hpoint n β' γ' s rank e.1.1 hrank hpointMem
  have hyBound := hline n β' γ' s rank e.1.2 hrank hlineMem
  have hnM : n ≤ 2 * n + 2 := by omega
  have hβM : β' ≤ 2 * n + 2 := by
    dsimp only [β']
    omega
  have hγM : γ' ≤ 2 * n + 2 := by
    dsimp only [γ']
    omega
  have hbitsN := length_natBits_mono hnM
  have hbitsβ := length_natBits_mono hβM
  have hbitsγ := length_natBits_mono hγM
  have hplainOverhead :
      s + 4 * ((Nat.bits n).length + (Nat.bits β').length +
          (Nat.bits γ').length) + 9 + Cplain ≤
        α + logSlack CplainTotal n := by
    calc
      s + 4 * ((Nat.bits n).length + (Nat.bits β').length +
            (Nat.bits γ').length) + 9 + Cplain
          ≤ α + (logSlack 13 (2 * n + 2) + (4 + Cplain)) := by
            dsimp only [s, B]
            unfold logSlack
            omega
      _ ≤ α + (logSlack CplainFold n + (4 + Cplain)) := by
            have := hplainFold n
            omega
      _ ≤ α + logSlack CplainTotal n := by
            dsimp only [CplainTotal]
            exact Nat.add_le_add_left
              (logSlack_add_const_le CplainFold (4 + Cplain) n) α
  have hpointOverhead :
      2 * (Nat.bits β').length + Cpoint ≤ logSlack CpointTotal n := by
    calc
      2 * (Nat.bits β').length + Cpoint
          ≤ logSlack 2 β' + Cpoint := by unfold logSlack; omega
      _ ≤ logSlack 2 (2 * n + 2) + Cpoint := by
            have := logSlack_mono_right 2 hβM
            omega
      _ ≤ logSlack CcoordFold n + Cpoint := by
            have := hcoordFold n
            omega
      _ ≤ logSlack CpointTotal n := by
            dsimp only [CpointTotal]
            exact logSlack_add_const_le CcoordFold Cpoint n
  have hlineOverhead :
      2 * (Nat.bits γ').length + Cline ≤ logSlack ClineTotal n := by
    calc
      2 * (Nat.bits γ').length + Cline
          ≤ logSlack 2 γ' + Cline := by unfold logSlack; omega
      _ ≤ logSlack 2 (2 * n + 2) + Cline := by
            have := logSlack_mono_right 2 hγM
            omega
      _ ≤ logSlack CcoordFold n + Cline := by
            have := hcoordFold n
            omega
      _ ≤ logSlack ClineTotal n := by
            dsimp only [ClineTotal]
            exact logSlack_add_const_le CcoordFold Cline n
  have hplainBase : logSlack CplainTotal n ≤ logSlack Cbase n := by
    exact logSlack_mono_left (le_max_left _ _) n
  have hpointBase : logSlack CpointTotal n ≤ logSlack Cbase n := by
    exact logSlack_mono_left ((le_max_left _ _).trans (le_max_right _ _)) n
  have hlineBase : logSlack ClineTotal n ≤ logSlack Cbase n := by
    exact logSlack_mono_left ((le_max_right _ _).trans (le_max_right _ _)) n
  have hbaseFinal : logSlack Cbase n < logSlack Cfinal n := by
    dsimp only [Cfinal]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  change ∃ witness,
    plainK V witness < ((α + logSlack Cfinal n : Nat) : ENat) ∧
    condK V (concretePointCode n e.1.1) witness <
      ((β + logSlack Cfinal n : Nat) : ENat) ∧
    condK V (concreteLineCode n e.1.2) witness <
      ((γ + logSlack Cfinal n : Nat) : ENat)
  refine ⟨z, ?_, ?_, ?_⟩
  · calc
      plainK V z ≤
          ((s + 4 * ((Nat.bits n).length + (Nat.bits β').length +
            (Nat.bits γ').length) + 9 + Cplain : Nat) : ENat) := hzBound
      _ ≤ ((α + logSlack Cbase n : Nat) : ENat) := by
            exact_mod_cast hplainOverhead.trans
              (Nat.add_le_add_left hplainBase α)
      _ < ((α + logSlack Cfinal n : Nat) : ENat) := by
            exact_mod_cast (Nat.add_lt_add_left hbaseFinal α)
  · calc
      condK V (concretePointCode n e.1.1) z ≤
          ((β' + 2 * (Nat.bits β').length + Cpoint : Nat) : ENat) := hxBound
      _ ≤ ((β + logSlack Cbase n : Nat) : ENat) := by
            exact_mod_cast (by
              have hβ'β : β' ≤ β := min_le_left _ _
              omega)
      _ < ((β + logSlack Cfinal n : Nat) : ENat) := by
            exact_mod_cast (Nat.add_lt_add_left hbaseFinal β)
  · calc
      condK V (concreteLineCode n e.1.2) z ≤
          ((γ' + 2 * (Nat.bits γ').length + Cline : Nat) : ENat) := hyBound
      _ ≤ ((γ + logSlack Cbase n : Nat) : ENat) := by
            exact_mod_cast (by
              have hγ'γ : γ' ≤ γ := min_le_left _ _
              omega)
      _ < ((γ + logSlack Cfinal n : Nat) : ENat) := by
            exact_mod_cast (Nat.add_lt_add_left hbaseFinal γ)

/-- **Exercise 312, two-directional capacity criterion.**  For a high-complexity
concrete incident edge, membership of `(α, β, γ)` in its common-information region
is equivalent — up to a uniform `logSlack C n` — to the capacity criterion
`2^{3n} ≤ 2^α · concreteIncidenceCapacity n (2^β) (2^γ)`.

Assembled from the necessity half (`incidence_region_capacity_necessary`) and the
sufficiency half (`incidence_capacity_sufficient`); the shared constant is the
sum of the two half-constants. -/
lemma exercise_312_incidence_region_criterion
    (V : Map) (hV : isOptimalConditional V) (d : Nat) :
    ∃ C N, ∀ n, N ≤ n →
      ∀ (e : ConcreteIncidentEdge n) (kxy : Nat),
        HasPlainComplexityValue V
          (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy →
        3 * n ≤ kxy + logSlack d n →
        ∀ (α β γ : Nat),
        ((α, β, γ) ∈ CommonInformationRegion V
            (concretePointCode n e.1.1) (concreteLineCode n e.1.2) →
          2 ^ (3 * n) ≤ 2 ^ (α + logSlack C n) *
            concreteIncidenceCapacity n (2 ^ β) (2 ^ γ)) ∧
        (2 ^ (3 * n) ≤ 2 ^ α * concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) →
          commonInformationTripleInflate (logSlack C n) (α, β, γ) ∈
            CommonInformationRegion V
              (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) := by
  obtain ⟨Cnec, Nnec, hnec⟩ := incidence_region_capacity_necessary V hV d
  obtain ⟨Csuf, Nsuf, hsuf⟩ := incidence_capacity_sufficient V hV
  refine ⟨Cnec + Csuf, max Nnec Nsuf, ?_⟩
  intro n hn e kxy hkxy hhigh α β γ
  have hn1 : Nnec ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : Nsuf ≤ n := le_trans (le_max_right _ _) hn
  refine ⟨?_, ?_⟩
  · -- Necessity: widen the slack constant `Cnec ≤ Cnec + Csuf`.
    intro hmem
    refine le_trans (hnec n hn1 e kxy hkxy hhigh α β γ hmem) ?_
    have hmono : logSlack Cnec n ≤ logSlack (Cnec + Csuf) n :=
      logSlack_mono_left (Nat.le_add_right _ _) n
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · -- Sufficiency: widen the inflation `logSlack Csuf n ≤ logSlack (Cnec+Csuf) n`.
    intro hcap
    have hmono : logSlack Csuf n ≤ logSlack (Cnec + Csuf) n :=
      logSlack_mono_left (Nat.le_add_left _ _) n
    have hIM := commonInformationTripleInflate_mono hmono (α, β, γ)
    exact commonInformationRegion_upward_closed hIM.1 hIM.2.1 hIM.2.2
      (hsuf n hn2 e α β γ hcap)

/-- **Exercise 312, public uniformity endpoint.**  For any two high-complexity
concrete incident edges of the plane over `GF(concretePrime n)`, the two
common-information regions coincide up to a single uniform `logSlack C n`
inflation, in both directions.

This is the precise `O(log n)`-precision equality of `C(x, y)` across all
high-complexity incident edges asserted by SUV Exercise 312.  It is derived by
chaining necessity for the source edge with sufficiency for the target edge; the
capacity `concreteIncidenceCapacity n (2^β) (2^γ)` is the *same* function of
`n, β, γ` for both edges, which is exactly why the regions match. -/
lemma exercise_312_incidence_region_uniformity
    (V : Map) (hV : isOptimalConditional V) (d : Nat) :
    ∃ C N, ∀ n, N ≤ n →
      ∀ (e₁ e₂ : ConcreteIncidentEdge n) (kxy₁ kxy₂ : Nat),
        HasPlainComplexityValue V
          (pairCode (concretePointCode n e₁.1.1) (concreteLineCode n e₁.1.2)) kxy₁ →
        3 * n ≤ kxy₁ + logSlack d n →
        HasPlainComplexityValue V
          (pairCode (concretePointCode n e₂.1.1) (concreteLineCode n e₂.1.2)) kxy₂ →
        3 * n ≤ kxy₂ + logSlack d n →
        (∀ t, t ∈ CommonInformationRegion V
            (concretePointCode n e₁.1.1) (concreteLineCode n e₁.1.2) →
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationRegion V
              (concretePointCode n e₂.1.1) (concreteLineCode n e₂.1.2)) ∧
        (∀ t, t ∈ CommonInformationRegion V
            (concretePointCode n e₂.1.1) (concreteLineCode n e₂.1.2) →
          commonInformationTripleInflate (logSlack C n) t ∈
            CommonInformationRegion V
              (concretePointCode n e₁.1.1) (concreteLineCode n e₁.1.2)) := by
  obtain ⟨Cnec, Nnec, hnec⟩ := incidence_region_capacity_necessary V hV d
  obtain ⟨Csuf, Nsuf, hsuf⟩ := incidence_capacity_sufficient V hV
  refine ⟨Cnec + Csuf, max Nnec Nsuf, ?_⟩
  intro n hn e₁ e₂ kxy₁ kxy₂ hkxy₁ hhigh₁ hkxy₂ hhigh₂
  have hn1 : Nnec ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : Nsuf ≤ n := le_trans (le_max_right _ _) hn
  -- One directional transport, applied twice (source `ea` → target `eb`).
  have step : ∀ (ea eb : ConcreteIncidentEdge n) (kxya : Nat),
      HasPlainComplexityValue V
        (pairCode (concretePointCode n ea.1.1) (concreteLineCode n ea.1.2)) kxya →
      3 * n ≤ kxya + logSlack d n →
      ∀ t, t ∈ CommonInformationRegion V
          (concretePointCode n ea.1.1) (concreteLineCode n ea.1.2) →
        commonInformationTripleInflate (logSlack (Cnec + Csuf) n) t ∈
          CommonInformationRegion V
            (concretePointCode n eb.1.1) (concreteLineCode n eb.1.2) := by
    intro ea eb kxya hkxya hhigha t ht
    obtain ⟨α, β, γ⟩ := t
    -- Necessity for the source edge yields the capacity criterion at level `α`.
    have hcap := hnec n hn1 ea kxya hkxya hhigha α β γ ht
    -- Sufficiency for the target edge, with the shifted first coordinate `α'`.
    have hsufb := hsuf n hn2 eb (α + logSlack Cnec n) β γ hcap
    -- Absorb the shift `α'` and the two slack terms into `logSlack (Cnec+Csuf) n`.
    have hadd : logSlack Cnec n + logSlack Csuf n = logSlack (Cnec + Csuf) n :=
      logSlack_add_const _ _ _
    have hmono : logSlack Csuf n ≤ logSlack (Cnec + Csuf) n :=
      logSlack_mono_left (Nat.le_add_left _ _) n
    have e1 :
        (commonInformationTripleInflate (logSlack Csuf n)
            (α + logSlack Cnec n, β, γ)).1 ≤
          (commonInformationTripleInflate (logSlack (Cnec + Csuf) n) (α, β, γ)).1 := by
      change α + logSlack Cnec n + logSlack Csuf n ≤ α + logSlack (Cnec + Csuf) n
      omega
    have e2 :
        (commonInformationTripleInflate (logSlack Csuf n)
            (α + logSlack Cnec n, β, γ)).2.1 ≤
          (commonInformationTripleInflate (logSlack (Cnec + Csuf) n) (α, β, γ)).2.1 := by
      change β + logSlack Csuf n ≤ β + logSlack (Cnec + Csuf) n
      omega
    have e3 :
        (commonInformationTripleInflate (logSlack Csuf n)
            (α + logSlack Cnec n, β, γ)).2.2 ≤
          (commonInformationTripleInflate (logSlack (Cnec + Csuf) n) (α, β, γ)).2.2 := by
      change γ + logSlack Csuf n ≤ γ + logSlack (Cnec + Csuf) n
      omega
    exact commonInformationRegion_upward_closed e1 e2 e3 hsufb
  exact ⟨step e₁ e₂ kxy₁ hkxy₁ hhigh₁, step e₂ e₁ kxy₂ hkxy₂ hhigh₂⟩

end Kolmogorov
