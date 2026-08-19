import KolmogorovMathlib.CommonInformation.IncidenceWitnessRectangles
import KolmogorovMathlib.CommonInformation.IncidenceWitnessSelector
import KolmogorovMathlib.CommonInformation.IncidenceCodecs
import KolmogorovMathlib.CommonInformation.ConcreteField
import KolmogorovMathlib.CommonInformation.AffineIncidence

/-!
# Exercise 312: the concrete rectangle-capacity criterion (necessity half)

This file introduces `concreteIncidenceCapacity n b c`, the maximal number of
incident edges in a point/line combinatorial rectangle of side cardinalities
`≤ b`, `≤ c` in the concrete affine plane over `GF(concretePrime n)`.  This is
exactly the source's "maximal possible number of edges in a combinatorial
rectangle of size `2^β × 2^γ`" (SUV Exercise 312).

The leaf lemmas here are the arithmetic and transport facts that feed the
necessity direction of the capacity criterion:

* `concreteIncidenceCapacity_mono`, `concreteIncidenceCapacity_clamp`,
  `interedges_card_le_concreteIncidenceCapacity`, `capacity_pos` — the maximality
  interface of the capacity;
* `commonWitnessRectangle_interedges_card_le_capacity` — transports a
  code-rectangle of common witnesses to a concrete point/line rectangle, bounding
  its incident-code-pair count by the capacity;
* `card_incidentCommonWitnessPairsLe_le_pow_mul_capacity` — the `2^{α+1}·capacity`
  cardinality bound on the incident common-witness pairs;
* `pairPlainK_incidentCommonWitness_capacity_le` — the staged-selector pair
  complexity bound (identical to `pairPlainK_incidentCommonWitness_le`);
* `incidence_region_capacity_necessary` — the packaged necessity direction (still
  open; see the comment above it for the remaining assembly).
-/

namespace Kolmogorov

open AffineIncidence

/-- The finset of point/line combinatorial rectangles in the concrete affine
plane over `GF(concretePrime n)` whose side cardinalities are bounded by `b` and
`c`.  `Incident` uses the registered decidable instance
`AffineIncidence.instDecidableIncident`, so no classical choice enters the
definition. -/
def boundedIncidenceRectangles (n b c : Nat) :
    Finset (Finset (Point (ConcreteField n)) × Finset (Line (ConcreteField n))) :=
  Finset.univ.filter fun R => R.1.card ≤ b ∧ R.2.card ≤ c

lemma boundedIncidenceRectangles_nonempty (n b c : Nat) :
    (boundedIncidenceRectangles n b c).Nonempty :=
  ⟨(∅, ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩

/-- **Concrete incidence rectangle capacity.**  The maximum, over point/line
rectangles with side cardinalities `≤ b`, `≤ c`, of the number of incident edges
in the rectangle.  This is the source's maximal number of edges in a rectangle of
size `2^β × 2^γ`. -/
def concreteIncidenceCapacity (n b c : Nat) : Nat :=
  ((boundedIncidenceRectangles n b c).image
      fun R => (Rel.interedges Incident R.1 R.2).card).max'
    ((boundedIncidenceRectangles_nonempty n b c).image _)

/-- **Defining maximality property.**  Any point/line rectangle of side
cardinalities `≤ b`, `≤ c` has at most `concreteIncidenceCapacity n b c` incident
edges. -/
lemma interedges_card_le_concreteIncidenceCapacity (n b c : Nat)
    (A : Finset (Point (ConcreteField n)))
    (B : Finset (Line (ConcreteField n)))
    (hA : A.card ≤ b) (hB : B.card ≤ c) :
    (Rel.interedges Incident A B).card ≤ concreteIncidenceCapacity n b c := by
  apply Finset.le_max'
  rw [Finset.mem_image]
  exact ⟨(A, B), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA, hB⟩, rfl⟩

/-- The capacity is monotone in both size budgets. -/
lemma concreteIncidenceCapacity_mono {n b₁ c₁ b₂ c₂ : Nat}
    (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) :
    concreteIncidenceCapacity n b₁ c₁ ≤ concreteIncidenceCapacity n b₂ c₂ := by
  apply Finset.max'_le
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨R, hR, rfl⟩ := hv
  rw [boundedIncidenceRectangles, Finset.mem_filter] at hR
  exact interedges_card_le_concreteIncidenceCapacity n b₂ c₂ R.1 R.2
    (hR.2.1.trans hb) (hR.2.2.trans hc)

/-- **Clamp at the total point/line count.**  Since any side of a rectangle in
the concrete plane has cardinality `≤ q^2` (where `q = concretePrime n` is the
field size), enlarging a size budget beyond `q^2` cannot increase the capacity.
This removes the oversized-coordinate risk so no `log β`/`log γ` term is forced. -/
lemma concreteIncidenceCapacity_clamp (n b c : Nat) :
    let q := concretePrime n
    concreteIncidenceCapacity n b c =
      concreteIncidenceCapacity n (min b (q^2)) (min c (q^2)) := by
  intro q
  have hpcard : Fintype.card (Point (ConcreteField n)) = q ^ 2 := by
    rw [AffineIncidence.point_card, concreteField_card_eq]
  have hlcard : Fintype.card (Line (ConcreteField n)) = q ^ 2 := by
    rw [AffineIncidence.line_card, concreteField_card_eq]
  apply le_antisymm
  · apply Finset.max'_le
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨R, hR, rfl⟩ := hv
    rw [boundedIncidenceRectangles, Finset.mem_filter] at hR
    have hR1 : R.1.card ≤ q ^ 2 := (Finset.card_le_univ R.1).trans_eq hpcard
    have hR2 : R.2.card ≤ q ^ 2 := (Finset.card_le_univ R.2).trans_eq hlcard
    exact interedges_card_le_concreteIncidenceCapacity n (min b (q^2)) (min c (q^2))
      R.1 R.2 (le_min hR.2.1 hR1) (le_min hR.2.2 hR2)
  · apply Finset.max'_le
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨R, hR, rfl⟩ := hv
    rw [boundedIncidenceRectangles, Finset.mem_filter] at hR
    exact interedges_card_le_concreteIncidenceCapacity n b c R.1 R.2
      (hR.2.1.trans (min_le_left _ _)) (hR.2.2.trans (min_le_left _ _))

/-- The capacity is positive whenever both budgets are positive: the singleton
rectangle `{(0,0)} × {(0,0)}` already contributes one incident edge. -/
lemma capacity_pos (n b c : Nat) (hb : 0 < b) (hc : 0 < c) :
    0 < concreteIncidenceCapacity n b c := by
  have hinc : Incident ((0, 0) : Point (ConcreteField n))
      ((0, 0) : Line (ConcreteField n)) := by
    simp [AffineIncidence.Incident]
  have hmem : ((0, 0), (0, 0)) ∈
      Rel.interedges Incident ({(0, 0)} : Finset (Point (ConcreteField n)))
        ({(0, 0)} : Finset (Line (ConcreteField n))) :=
    Rel.mem_interedges_iff.mpr
      ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _, hinc⟩
  have h1 : 0 < (Rel.interedges Incident
      ({(0, 0)} : Finset (Point (ConcreteField n)))
      ({(0, 0)} : Finset (Line (ConcreteField n)))).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  refine lt_of_lt_of_le h1 ?_
  exact interedges_card_le_concreteIncidenceCapacity n b c _ _
    (by rw [Finset.card_singleton]; omega) (by rw [Finset.card_singleton]; omega)

open Classical in
/-- **Code-to-geometry transport.**  A common-witness code rectangle `R` of the
incident-code relation transports (via the injective total decoders
`concretePointDecode`/`concreteLineDecode`) to a concrete point/line rectangle of
the same side cardinality budgets, so its incident-code-pair count is bounded by
`concreteIncidenceCapacity n (2^{β+1}) (2^{γ+1})`. -/
lemma commonWitnessRectangle_interedges_card_le_capacity
    {V : Map} {n α β γ : Nat}
    {R : Finset BitString × Finset BitString}
    (hR : R ∈ commonWitnessRectanglesLe V α β γ) :
    (Rel.interedges (concreteIncidentCodeRel n) R.1 R.2).card ≤
      concreteIncidenceCapacity n (2 ^ (β + 1)) (2 ^ (γ + 1)) := by
  have hRcard := commonWitnessRectanglesLe_side_card_lt hR
  set A' := R.1.image (concretePointDecode n) with hA'def
  set B' := R.2.image (concreteLineDecode n) with hB'def
  have hA'card : A'.card ≤ 2 ^ (β + 1) := le_trans Finset.card_image_le hRcard.1.le
  have hB'card : B'.card ≤ 2 ^ (γ + 1) := le_trans Finset.card_image_le hRcard.2.le
  have hcard_le :
      (Rel.interedges (concreteIncidentCodeRel n) R.1 R.2).card ≤
        (Rel.interedges Incident A' B').card := by
    apply Finset.card_le_card_of_injOn
      (f := fun p => (concretePointDecode n p.1, concreteLineDecode n p.2))
    · intro p hp
      rw [Finset.mem_coe, Rel.mem_interedges_iff] at hp
      obtain ⟨hp1, hp2, hpr⟩ := hp
      obtain ⟨e, hex, hey⟩ := concreteIncidentCodeRel_iff_exists_edge.mp hpr
      rw [Finset.mem_coe, Rel.mem_interedges_iff]
      refine ⟨Finset.mem_image_of_mem _ hp1, Finset.mem_image_of_mem _ hp2, ?_⟩
      change Incident (concretePointDecode n p.1) (concreteLineDecode n p.2)
      rw [hex, hey, concretePointDecode_code, concreteLineDecode_code]
      exact AffineIncidence.mem_incidentEdges_iff.mp e.2
    · intro p hp p' hp' heq
      rw [Finset.mem_coe, Rel.mem_interedges_iff] at hp hp'
      obtain ⟨e, hex, hey⟩ := concreteIncidentCodeRel_iff_exists_edge.mp hp.2.2
      obtain ⟨e', hex', hey'⟩ := concreteIncidentCodeRel_iff_exists_edge.mp hp'.2.2
      have h1 : concretePointDecode n p.1 = concretePointDecode n p'.1 :=
        (Prod.ext_iff.mp heq).1
      have h2 : concreteLineDecode n p.2 = concreteLineDecode n p'.2 :=
        (Prod.ext_iff.mp heq).2
      rw [hex, hex', concretePointDecode_code, concretePointDecode_code] at h1
      rw [hey, hey', concreteLineDecode_code, concreteLineDecode_code] at h2
      have hp1 : p.1 = p'.1 := by rw [hex, hex', h1]
      have hp2 : p.2 = p'.2 := by rw [hey, hey', h2]
      exact Prod.ext_iff.mpr ⟨hp1, hp2⟩
  exact le_trans hcard_le
    (interedges_card_le_concreteIncidenceCapacity n (2 ^ (β + 1)) (2 ^ (γ + 1))
      A' B' hA'card hB'card)

/-- **Cardinality bound via the capacity.**  The incident common-witness pairs at
level `(α, β, γ)` number at most `2^{α+1}` rectangles, each with at most
`concreteIncidenceCapacity n (2^{β+1}) (2^{γ+1})` incident edges. -/
lemma card_incidentCommonWitnessPairsLe_le_pow_mul_capacity
    {V : Map} {n α β γ : Nat} :
    (incidentCommonWitnessPairsLe V n α β γ).card ≤
      2 ^ (α + 1) * concreteIncidenceCapacity n (2 ^ (β + 1)) (2 ^ (γ + 1)) := by
  classical
  rw [← rectangleFamilyEdges_commonWitnessRectanglesLe]
  set K := concreteIncidenceCapacity n (2 ^ (β + 1)) (2 ^ (γ + 1)) with hK
  calc
    (rectangleFamilyEdges (concreteIncidentCodeRel n)
          (commonWitnessRectanglesLe V α β γ)).card
        ≤ ∑ R ∈ commonWitnessRectanglesLe V α β γ,
            (Rel.interedges (concreteIncidentCodeRel n) R.1 R.2).card :=
      card_rectangleFamilyEdges_le_sum _ _
    _ ≤ ∑ _R ∈ commonWitnessRectanglesLe V α β γ, K :=
      Finset.sum_le_sum fun R hR =>
        commonWitnessRectangle_interedges_card_le_capacity hR
    _ = (commonWitnessRectanglesLe V α β γ).card * K := by simp
    _ ≤ 2 ^ (α + 1) * K :=
      Nat.mul_le_mul_right K commonWitnessRectanglesLe_card_lt.le

/-- **Staged-selector pair complexity bound.**  Every incident common-witness
pair `(x, y)` at level `(α, β, γ)` whose enumeration has fewer than `2^s` members
has plain pair complexity at most `s + 4·(bit lengths) + 9 + O(1)`.  This is the
same statement as `pairPlainK_incidentCommonWitness_le`, restated in this file for
the capacity necessity argument. -/
lemma pairPlainK_incidentCommonWitness_capacity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ C, ∀ n α β γ s x y,
      (x, y) ∈ incidentCommonWitnessPairsLe V n α β γ →
      (incidentCommonWitnessPairsLe V n α β γ).card < 2 ^ s →
      pairPlainK V x y ≤
        ((s + 4 * ((Nat.bits n).length + (Nat.bits α).length +
                   (Nat.bits β).length + (Nat.bits γ).length) + 9 + C : Nat) : ENat) :=
  pairPlainK_incidentCommonWitness_le V hV

/-- **Conditional-budget clamp for incident common-witness pairs.**  A witness
pair stays a witness pair when the two conditional budgets are capped at the
universal bound `|x| + O(1)`, `|y| + O(1)` on the conditional complexity of the
(fixed-length) codes.  The same witness `z` realizes the clamped budgets because
`condK V x z ≤ |x| + O(1)` for every `z`.  This keeps the selector overhead
`O(log n)` even when the region coordinates `β, γ` are arbitrarily large. -/
lemma incidentCommonWitness_cond_clamp (V : Map) (hV : isOptimalConditional V) :
    ∃ c₀ : Nat, ∀ n a b c x y,
      (x, y) ∈ incidentCommonWitnessPairsLe V n a b c →
      (x, y) ∈ incidentCommonWitnessPairsLe V n a
        (min b (x.length + c₀)) (min c (y.length + c₀)) := by
  obtain ⟨cL, hcL⟩ := plainKLeLength V hV
  obtain ⟨cC, hcC⟩ := condKLePlainK V hV
  refine ⟨cL + cC, ?_⟩
  intro n a b c x y hmem
  rw [incidentCommonWitnessPairsLe, Finset.mem_filter] at hmem ⊢
  refine ⟨?_, hmem.2⟩
  obtain ⟨z, hz, hx, hy⟩ := (mem_commonWitnessPairsLe_iff V a b c x y).mp hmem.1
  rw [mem_commonWitnessPairsLe_iff]
  refine ⟨z, hz, ?_, ?_⟩
  · rcases le_total b (x.length + (cL + cC)) with hb | hb
    · rw [min_eq_left hb]; exact hx
    · rw [min_eq_right hb]
      calc condK V x z ≤ plainK V x + (cC : ENat) := hcC x z
        _ ≤ ((x.length : ENat) + (cL : ENat)) + (cC : ENat) := by gcongr; exact hcL x
        _ = ((x.length + (cL + cC) : Nat) : ENat) := by push_cast; ring
  · rcases le_total c (y.length + (cL + cC)) with hc' | hc'
    · rw [min_eq_left hc']; exact hy
    · rw [min_eq_right hc']
      calc condK V y z ≤ plainK V y + (cC : ENat) := hcC y z
        _ ≤ ((y.length : ENat) + (cL : ENat)) + (cC : ENat) := by gcongr; exact hcL y
        _ = ((y.length + (cL + cC) : Nat) : ENat) := by push_cast; ring

/-- **Exercise 312, necessity direction (packaged).**  For a high-complexity
concrete incident edge, every triple `(α, β, γ)` in its common-information region
forces the capacity criterion
`2^{3n} ≤ 2^{α + O(log n)} · concreteIncidenceCapacity n (2^β) (2^γ)`.

The `-1`/`+1` cancellation between the region→witness bridge
(`mem_incidentCommonWitnessPairsLe_of_mem_region`, at level `(α-1,β-1,γ-1)`) and
the `2^{α+1}·capacity(2^{β+1},2^{γ+1})` cardinality bound produces exactly the
capacity `concreteIncidenceCapacity n (2^β) (2^γ)`.  The uniform `logSlack C n`
(independent of `α, β, γ`) is obtained by clamping the conditional budgets via
`incidentCommonWitness_cond_clamp` and splitting on `3n ≤ α`. -/
lemma incidence_region_capacity_necessary
    (V : Map) (hV : isOptimalConditional V) (d : Nat) :
    ∃ C N, ∀ n, N ≤ n →
      ∀ (e : ConcreteIncidentEdge n) (kxy : Nat),
        HasPlainComplexityValue V
          (pairCode (concretePointCode n e.1.1) (concreteLineCode n e.1.2)) kxy →
        3 * n ≤ kxy + logSlack d n →
        ∀ (α β γ : Nat),
        (α, β, γ) ∈ CommonInformationRegion V
          (concretePointCode n e.1.1) (concreteLineCode n e.1.2) →
        2 ^ (3 * n) ≤ 2 ^ (α + logSlack C n) *
          concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) := by
  obtain ⟨c₀, hclamp⟩ := incidentCommonWitness_cond_clamp V hV
  obtain ⟨cSel, hSel⟩ := pairPlainK_incidentCommonWitness_capacity_le V hV
  refine ⟨66 + 8 * (Nat.bits c₀).length + cSel + d, 1, ?_⟩
  intro n _hn e kxy hkxy hhigh α β γ hregion
  set x := concretePointCode n e.1.1 with hx_def
  set y := concreteLineCode n e.1.2 with hy_def
  set K := concreteIncidenceCapacity n (2 ^ β) (2 ^ γ) with hK_def
  set C := 66 + 8 * (Nat.bits c₀).length + cSel + d with hC_def
  have hKpos : 0 < K :=
    capacity_pos n (2 ^ β) (2 ^ γ) (by positivity) (by positivity)
  clear_value K
  rcases le_total (3 * n) α with hαbig | hαsmall
  · -- Large-`α` branch: `2^{α+logSlack}·K ≥ 2^{3n}·1`.
    calc 2 ^ (3 * n) ≤ 2 ^ (α + logSlack C n) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ (α + logSlack C n) * K := Nat.le_mul_of_pos_right _ hKpos
  · -- Counting branch.
    have hαpos : 0 < α := by
      obtain ⟨z, hz, -, -⟩ := hregion
      have : (0 : ENat) < (α : ENat) := lt_of_le_of_lt (zero_le) hz
      exact_mod_cast this
    have hβpos : 0 < β := by
      obtain ⟨z, -, hxz, -⟩ := hregion
      have : (0 : ENat) < (β : ENat) := lt_of_le_of_lt (zero_le) hxz
      exact_mod_cast this
    have hγpos : 0 < γ := by
      obtain ⟨z, -, -, hyz⟩ := hregion
      have : (0 : ENat) < (γ : ENat) := lt_of_le_of_lt (zero_le) hyz
      exact_mod_cast this
    have hinc : concreteIncidentCodeRel n x y :=
      concreteIncidentCodeRel_iff_exists_edge.mpr ⟨e, hx_def, hy_def⟩
    have hmem0 : (x, y) ∈ incidentCommonWitnessPairsLe V n (α - 1) (β - 1) (γ - 1) :=
      mem_incidentCommonWitnessPairsLe_of_mem_region hαpos hβpos hγpos hinc hregion
    have hxlen : x.length = 2 * (n + 1) := by
      rw [hx_def]; exact concretePointCode_length n e.1.1
    have hylen : y.length = 2 * (n + 1) := by
      rw [hy_def]; exact concreteLineCode_length n e.1.2
    set β'' := min (β - 1) (x.length + c₀) with hβ''_def
    set γ'' := min (γ - 1) (y.length + c₀) with hγ''_def
    have hmem : (x, y) ∈ incidentCommonWitnessPairsLe V n (α - 1) β'' γ'' :=
      hclamp n (α - 1) (β - 1) (γ - 1) x y hmem0
    have hcap_le :
        concreteIncidenceCapacity n (2 ^ (β'' + 1)) (2 ^ (γ'' + 1)) ≤ K := by
      rw [hK_def]
      apply concreteIncidenceCapacity_mono
      · exact Nat.pow_le_pow_right (by norm_num) (by rw [hβ''_def]; omega)
      · exact Nat.pow_le_pow_right (by norm_num) (by rw [hγ''_def]; omega)
    have hcard :
        (incidentCommonWitnessPairsLe V n (α - 1) β'' γ'').card ≤ 2 ^ α * K := by
      have h5 := card_incidentCommonWitnessPairsLe_le_pow_mul_capacity
        (V := V) (n := n) (α := α - 1) (β := β'') (γ := γ'')
      have hαe : (α - 1) + 1 = α := by omega
      rw [hαe] at h5
      exact h5.trans (Nat.mul_le_mul_left _ hcap_le)
    set s := α + Nat.size K with hs_def
    have hlt : (incidentCommonWitnessPairsLe V n (α - 1) β'' γ'').card < 2 ^ s := by
      calc (incidentCommonWitnessPairsLe V n (α - 1) β'' γ'').card
            ≤ 2 ^ α * K := hcard
        _ < 2 ^ α * 2 ^ Nat.size K :=
            Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self K) (by positivity)
        _ = 2 ^ s := by rw [hs_def, pow_add]
    have hpair := hSel n (α - 1) β'' γ'' s x y hmem hlt
    have hkxyEq : plainK V (pairCode x y) = (kxy : ENat) := hkxy
    have hpairNat :
        kxy ≤ s + 4 * ((Nat.bits n).length + (Nat.bits (α - 1)).length +
          (Nat.bits β'').length + (Nat.bits γ'').length) + 9 + cSel := by
      have h : (kxy : ENat) ≤
          ((s + 4 * ((Nat.bits n).length + (Nat.bits (α - 1)).length +
            (Nat.bits β'').length + (Nat.bits γ'').length) + 9 + cSel : Nat) : ENat) := by
        rw [← hkxyEq]; exact hpair
      exact_mod_cast h
    -- Bit-length bounds keeping the overhead `O(log n)`.
    have hbα : (Nat.bits (α - 1)).length ≤ 3 * (Nat.bits n).length + 2 := by
      have hmono : (Nat.bits (α - 1)).length ≤ (Nat.bits (3 * n)).length :=
        length_natBits_mono (by omega)
      have hE : 3 * n = n + n + n := by ring
      rw [hE] at hmono
      have hA := length_natBits_add_le (n + n) n
      have hB := length_natBits_add_le n n
      omega
    have hβ''le : β'' ≤ 2 * (n + 1) + c₀ := by
      have := min_le_right (β - 1) (x.length + c₀)
      rw [← hβ''_def, hxlen] at this; omega
    have hγ''le : γ'' ≤ 2 * (n + 1) + c₀ := by
      have := min_le_right (γ - 1) (y.length + c₀)
      rw [← hγ''_def, hylen] at this; omega
    have hbβ : (Nat.bits β'').length ≤ 2 * (Nat.bits n).length + (6 + (Nat.bits c₀).length) := by
      have hmono : (Nat.bits β'').length ≤ (Nat.bits (2 * (n + 1) + c₀)).length :=
        length_natBits_mono hβ''le
      have hEq : 2 * (n + 1) + c₀ = (n + 1) + ((n + 1) + c₀) := by ring
      rw [hEq] at hmono
      have hA := length_natBits_add_le (n + 1) ((n + 1) + c₀)
      have hB := length_natBits_add_le (n + 1) c₀
      have hC1 := length_natBits_add_le n 1
      have h1 : (Nat.bits 1).length = 1 := by decide
      omega
    have hbγ : (Nat.bits γ'').length ≤ 2 * (Nat.bits n).length + (6 + (Nat.bits c₀).length) := by
      have hmono : (Nat.bits γ'').length ≤ (Nat.bits (2 * (n + 1) + c₀)).length :=
        length_natBits_mono hγ''le
      have hEq : 2 * (n + 1) + c₀ = (n + 1) + ((n + 1) + c₀) := by ring
      rw [hEq] at hmono
      have hA := length_natBits_add_le (n + 1) ((n + 1) + c₀)
      have hB := length_natBits_add_le (n + 1) c₀
      have hC1 := length_natBits_add_le n 1
      have h1 : (Nat.bits 1).length = 1 := by decide
      omega
    have hcomb : 3 * n ≤ α + Nat.size K +
        4 * ((Nat.bits n).length + (Nat.bits (α - 1)).length +
          (Nat.bits β'').length + (Nat.bits γ'').length) + 9 + cSel + logSlack d n := by
      omega
    have hslack :
        4 * ((Nat.bits n).length + (Nat.bits (α - 1)).length +
          (Nat.bits β'').length + (Nat.bits γ'').length) + 9 + cSel + logSlack d n + 1
          ≤ logSlack C n := by
      have hlogd : logSlack d n = d * (Nat.bits n).length + d := rfl
      have hlogC : logSlack C n = C * (Nat.bits n).length + C := rfl
      have hCge : 32 + d ≤ C := by omega
      rw [hlogC]
      calc 4 * ((Nat.bits n).length + (Nat.bits (α - 1)).length +
            (Nat.bits β'').length + (Nat.bits γ'').length) + 9 + cSel + logSlack d n + 1
          ≤ (32 + d) * (Nat.bits n).length + C := by rw [hlogd, Nat.add_mul]; omega
        _ ≤ C * (Nat.bits n).length + C := by gcongr
    have hexp : 3 * n + 1 ≤ α + logSlack C n + Nat.size K := by omega
    have hSizeKpos : 0 < Nat.size K := Nat.size_pos.mpr hKpos
    have h2K : 2 ^ Nat.size K ≤ 2 * K := by
      have hlow : 2 ^ (Nat.size K - 1) ≤ K :=
        Nat.lt_size.mp (by omega : Nat.size K - 1 < Nat.size K)
      calc 2 ^ Nat.size K = 2 * 2 ^ (Nat.size K - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hSizeKpos]
        _ ≤ 2 * K := by gcongr
    have hchain : 2 * 2 ^ (3 * n) ≤ 2 * (2 ^ (α + logSlack C n) * K) := by
      calc 2 * 2 ^ (3 * n) = 2 ^ (3 * n + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ (α + logSlack C n + Nat.size K) :=
            Nat.pow_le_pow_right (by norm_num) hexp
        _ = 2 ^ (α + logSlack C n) * 2 ^ Nat.size K := by rw [pow_add]
        _ ≤ 2 ^ (α + logSlack C n) * (2 * K) := by gcongr
        _ = 2 * (2 ^ (α + logSlack C n) * K) := by ring
    exact Nat.le_of_mul_le_mul_left hchain (by norm_num)

end Kolmogorov
