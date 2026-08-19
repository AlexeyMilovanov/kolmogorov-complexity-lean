import KolmogorovMathlib.CommonInformation.Definitions
import KolmogorovMathlib.CommonInformation.IncidenceWitnessSelector
import KolmogorovMathlib.CommonInformation.RegionEnvelopes

/-!
# SUV Theorem 227: the incidence-graph common-information region envelope

This module packages the Figure-37 upper bound on the common-information region
`C(x,y)` for a high-complexity incident point/line edge in the concrete affine
incidence graph over a finite field of size about `2 ^ n`.

* `IncidenceRegionEnvelope n` is the set `S` of Figure 37, written as the
  conjunction of the two asymmetric inequalities
  `3n ≤ α + γ/2 + max (γ/2) β` and `3n ≤ α + β/2 + max (β/2) γ`
  (the source's piecewise `β ≤ γ` / `γ ≤ β` split is equivalent to holding both
  simultaneously).
* `theorem_227_incidence_region_containment` shows that, after the uniform
  logarithmic inflation, every triple of `CommonInformationRegion V x y` for such
  an edge lands in `IncidenceRegionEnvelope n`.

The two Figure-37 pair-complexity legs come from
`pairPlainK_incidentCommonWitness_source_bounds`; the region → witness-pair
bridge is `mem_incidentCommonWitnessPairsLe_of_mem_region`.
-/

namespace Kolmogorov

/-- The set `S` of Figure 37: the two asymmetric linear constraints that bound
the common-information region of a random incident point/line edge. -/
def IncidenceRegionEnvelope (n : Nat) :
    Set CommonInformationTriple :=
  {t |
    3 * n ≤ t.1 + t.2.2 / 2 + max (t.2.2 / 2) t.2.1 ∧
    3 * n ≤ t.1 + t.2.1 / 2 + max (t.2.1 / 2) t.2.2}

theorem incidenceRegionEnvelope_upward_closed
    (n : Nat) {s t : CommonInformationTriple} :
  s ∈ IncidenceRegionEnvelope n →
  s.1 ≤ t.1 → s.2.1 ≤ t.2.1 → s.2.2 ≤ t.2.2 →
  t ∈ IncidenceRegionEnvelope n := by
  rintro ⟨h1, h2⟩ hs1 hs21 hs22
  constructor
  · calc
      3 * n ≤ s.1 + s.2.2 / 2 + max (s.2.2 / 2) s.2.1 := h1
      _ ≤ t.1 + t.2.2 / 2 + max (t.2.2 / 2) t.2.1 := by
        have h3 : s.2.2 / 2 ≤ t.2.2 / 2 := Nat.div_le_div_right hs22
        have h4 : max (s.2.2 / 2) s.2.1 ≤ max (t.2.2 / 2) t.2.1 := by
          apply max_le_max h3 hs21
        omega
  · calc
      3 * n ≤ s.1 + s.2.1 / 2 + max (s.2.1 / 2) s.2.2 := h2
      _ ≤ t.1 + t.2.1 / 2 + max (t.2.1 / 2) t.2.2 := by
        have h3 : s.2.1 / 2 ≤ t.2.1 / 2 := Nat.div_le_div_right hs21
        have h4 : max (s.2.1 / 2) s.2.2 ≤ max (t.2.1 / 2) t.2.2 := by
          apply max_le_max h3 hs22
        omega

/-- Every triple in a common-information region has strictly positive
coordinates: a witness `z` would otherwise need `C(z) < 0`, `C(x|z) < 0`, or
`C(y|z) < 0`, all impossible in `ENat`. -/
theorem commonInformationRegion_coords_pos {V : Map} {x y : BitString}
    {t : CommonInformationTriple}
    (ht : t ∈ CommonInformationRegion V x y) :
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 := by
  obtain ⟨z, hz, hx, hy⟩ := ht
  refine ⟨?_, ?_, ?_⟩
  · have h : (0 : ENat) < (t.1 : ENat) := lt_of_le_of_lt (zero_le) hz
    exact_mod_cast h
  · have h : (0 : ENat) < (t.2.1 : ENat) := lt_of_le_of_lt (zero_le) hx
    exact_mod_cast h
  · have h : (0 : ENat) < (t.2.2 : ENat) := lt_of_le_of_lt (zero_le) hy
    exact_mod_cast h

/-- The two Figure-37 pair-complexity bounds transported to an arbitrary triple
of the common-information region of a concrete incident edge.  This turns the
witness-pair rank bound `pairPlainK_incidentCommonWitness_source_bounds` into a
region-coordinate statement, folding the fixed-width incidence overhead into a
single uniform `logSlack`. -/
lemma pairPlainK_incident_region_source_bounds
    (V : Map) (hV : isOptimalConditional V) :
  ∃ C, ∀ n (e : ConcreteIncidentEdge n) t,
    t ∈ CommonInformationRegion V
      (concretePointCode n e.1.1) (concreteLineCode n e.1.2) →
    pairPlainK V (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2) ≤
      ((t.1 + t.2.2 / 2 + max (t.2.2 / 2) t.2.1 +
        logSlack C (n + t.1 + t.2.1 + t.2.2 + 1) : Nat) : ENat) ∧
    pairPlainK V (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2) ≤
      ((t.1 + t.2.1 / 2 + max (t.2.1 / 2) t.2.2 +
        logSlack C (n + t.1 + t.2.1 + t.2.2 + 1) : Nat) : ENat) := by
  obtain ⟨C₀, hC₀⟩ := pairPlainK_incidentCommonWitness_source_bounds V hV
  refine ⟨16 + C₀, ?_⟩
  intro n e t ht
  obtain ⟨hα, hβ, hγ⟩ := commonInformationRegion_coords_pos ht
  have hinc : concreteIncidentCodeRel n
      (concretePointCode n e.1.1) (concreteLineCode n e.1.2) :=
    concreteIncidentCodeRel_iff_exists_edge.mpr ⟨e, rfl, rfl⟩
  have hmem : (concretePointCode n e.1.1, concreteLineCode n e.1.2) ∈
      incidentCommonWitnessPairsLe V n (t.1 - 1) (t.2.1 - 1) (t.2.2 - 1) :=
    mem_incidentCommonWitnessPairsLe_of_mem_region hα hβ hγ hinc ht
  obtain ⟨hb1, hb2⟩ := hC₀ n (t.1 - 1) (t.2.1 - 1) (t.2.2 - 1) _ _ hmem
  set M := n + t.1 + t.2.1 + t.2.2 + 1 with hM
  -- The fixed-width incidence overhead folds into a single logarithmic slack.
  have hoverhead :
      4 * ((Nat.bits n).length + (Nat.bits (t.1 - 1)).length +
           (Nat.bits (t.2.1 - 1)).length + (Nat.bits (t.2.2 - 1)).length) + C₀ ≤
        logSlack (16 + C₀) M := by
    have hbn : (Nat.bits n).length ≤ (Nat.bits M).length :=
      length_natBits_mono (by omega)
    have hb_1 : (Nat.bits (t.1 - 1)).length ≤ (Nat.bits M).length :=
      length_natBits_mono (by omega)
    have hb_21 : (Nat.bits (t.2.1 - 1)).length ≤ (Nat.bits M).length :=
      length_natBits_mono (by omega)
    have hb_22 : (Nat.bits (t.2.2 - 1)).length ≤ (Nat.bits M).length :=
      length_natBits_mono (by omega)
    have hstep1 :
        4 * ((Nat.bits n).length + (Nat.bits (t.1 - 1)).length +
             (Nat.bits (t.2.1 - 1)).length + (Nat.bits (t.2.2 - 1)).length) + C₀ ≤
          16 * (Nat.bits M).length + C₀ := by omega
    have hstep2 :
        16 * (Nat.bits M).length + C₀ ≤ logSlack (16 + C₀) M := by
      have h : logSlack (16 + C₀) M
          = (16 * (Nat.bits M).length + C₀) + (C₀ * (Nat.bits M).length + 16) := by
        unfold logSlack; ring
      rw [h]; exact Nat.le_add_right _ _
    exact le_trans hstep1 hstep2
  refine ⟨le_trans hb1 (Nat.cast_le.mpr ?_), le_trans hb2 (Nat.cast_le.mpr ?_)⟩
  · have hd : (t.2.2 - 1) / 2 ≤ t.2.2 / 2 := Nat.div_le_div_right (by omega)
    have hmx : max ((t.2.2 - 1) / 2) (t.2.1 - 1) ≤ max (t.2.2 / 2) t.2.1 :=
      max_le_max hd (by omega)
    omega
  · have hd : (t.2.1 - 1) / 2 ≤ t.2.1 / 2 := Nat.div_le_div_right (by omega)
    have hmx : max ((t.2.1 - 1) / 2) (t.2.2 - 1) ≤ max (t.2.1 / 2) t.2.2 :=
      max_le_max hd (by omega)
    omega

/-- **SUV Theorem 227, region containment.** For every high-complexity incident
edge (its joint plain complexity within `logSlack d n` of `3n`), the entire
common-information region of the edge lands, after the uniform inflation
`logSlack C (n + α + β + γ + 1)`, inside the Figure-37 envelope
`IncidenceRegionEnvelope n`.

This is the geometric heart of Theorem 227: it combines the two Figure-37
pair-complexity legs with the high-complexity hypothesis `3n ≤ kxy + logSlack d n`
and folds both logarithmic error terms into a single inflation. -/
theorem theorem_227_incidence_region_containment
    (V : Map) (hV : isOptimalConditional V) :
  ∀ d, ∃ C, ∀ n (e : ConcreteIncidentEdge n) kxy,
    HasPlainComplexityValue V
      (pairCode (concretePointCode n e.1.1)
        (concreteLineCode n e.1.2)) kxy →
    3 * n ≤ kxy + logSlack d n →
    ∀ t ∈ CommonInformationRegion V
      (concretePointCode n e.1.1) (concreteLineCode n e.1.2),
      commonInformationTripleInflate
        (logSlack C (n + t.1 + t.2.1 + t.2.2 + 1)) t ∈
          IncidenceRegionEnvelope n := by
  obtain ⟨Ch, hCh⟩ := pairPlainK_incident_region_source_bounds V hV
  intro d
  refine ⟨Ch + d, ?_⟩
  intro n e kxy hkxy hhigh t ht
  obtain ⟨hb1, hb2⟩ := hCh n e t ht
  have hpair : pairPlainK V (concretePointCode n e.1.1)
      (concreteLineCode n e.1.2) = (kxy : ENat) := hkxy
  rw [hpair] at hb1 hb2
  have hb1' : kxy ≤ t.1 + t.2.2 / 2 + max (t.2.2 / 2) t.2.1 +
      logSlack Ch (n + t.1 + t.2.1 + t.2.2 + 1) := by exact_mod_cast hb1
  have hb2' : kxy ≤ t.1 + t.2.1 / 2 + max (t.2.1 / 2) t.2.2 +
      logSlack Ch (n + t.1 + t.2.1 + t.2.2 + 1) := by exact_mod_cast hb2
  set M := n + t.1 + t.2.1 + t.2.2 + 1 with hM
  set s := logSlack (Ch + d) M with hs
  -- Fold the two logarithmic error terms into the single inflation slack `s`.
  have hslack : logSlack Ch M + logSlack d n ≤ s := by
    have h1 : logSlack d n ≤ logSlack d M := logSlack_mono_right d (by omega)
    have h2 : logSlack Ch M + logSlack d M = logSlack (Ch + d) M := by
      unfold logSlack; ring
    rw [hs]; omega
  change
    3 * n ≤ (t.1 + s) + (t.2.2 + s) / 2 + max ((t.2.2 + s) / 2) (t.2.1 + s) ∧
    3 * n ≤ (t.1 + s) + (t.2.1 + s) / 2 + max ((t.2.1 + s) / 2) (t.2.2 + s)
  refine ⟨?_, ?_⟩
  · have hd : t.2.2 / 2 ≤ (t.2.2 + s) / 2 := Nat.div_le_div_right (by omega)
    have hmx : max (t.2.2 / 2) t.2.1 ≤ max ((t.2.2 + s) / 2) (t.2.1 + s) :=
      max_le_max hd (by omega)
    omega
  · have hd : t.2.1 / 2 ≤ (t.2.1 + s) / 2 := Nat.div_le_div_right (by omega)
    have hmx : max (t.2.1 / 2) t.2.2 ≤ max ((t.2.1 + s) / 2) (t.2.2 + s) :=
      max_le_max hd (by omega)
    omega

end Kolmogorov
