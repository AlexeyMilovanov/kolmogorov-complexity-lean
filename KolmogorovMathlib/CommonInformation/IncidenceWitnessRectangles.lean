import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.CommonInformation.IncidenceCoding
import KolmogorovMathlib.CommonInformation.RectangleCover
import KolmogorovMathlib.CommonInformation.NoFourCycleDensity
import KolmogorovMathlib.CommonInformation.WorstCaseRegionBounds

open Kolmogorov

namespace Kolmogorov

def concreteIncidentCodeRel (n : Nat) (x y : BitString) : Prop :=
  pairCode x y ∈ concreteIncidentPairCodes n

noncomputable def commonWitnessRectanglesLe
    (V : Map) (α β γ : Nat) :
    Finset (Finset BitString × Finset BitString) :=
  (compressibleWords V [] α).image fun z =>
    (compressibleWords V z β, compressibleWords V z γ)

noncomputable def incidentCommonWitnessPairsLe
    (V : Map) (n α β γ : Nat) : Finset (BitString × BitString) :=
  (commonWitnessPairsLe V α β γ).filter fun p => pairCode p.1 p.2 ∈ concreteIncidentPairCodes n

lemma concreteIncidentCodeRel_iff_exists_edge {n : Nat} {x y : BitString} :
    concreteIncidentCodeRel n x y ↔
      ∃ e : ConcreteIncidentEdge n,
        x = concretePointCode n e.1.1 ∧
        y = concreteLineCode n e.1.2 := by
  rw [concreteIncidentCodeRel, concreteIncidentPairCodes_mem_iff]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_, ?_⟩
    · simpa only [decodeFirst_pairCode] using congrArg decodeFirst he
    · simpa only [decodeSecond_pairCode] using congrArg decodeSecond he
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨e, rfl⟩

lemma concreteIncidentCodeRel_noFourCycle {n : Nat} :
    NoFourCycle (concreteIncidentCodeRel n) := by
  intro x₁ x₂ y₁ y₂ h₁₁ h₁₂ h₂₁ h₂₂
  obtain ⟨e₁₁, hx₁₁, hy₁₁⟩ := concreteIncidentCodeRel_iff_exists_edge.mp h₁₁
  obtain ⟨e₁₂, hx₁₂, hy₁₂⟩ := concreteIncidentCodeRel_iff_exists_edge.mp h₁₂
  obtain ⟨e₂₁, hx₂₁, hy₂₁⟩ := concreteIncidentCodeRel_iff_exists_edge.mp h₂₁
  obtain ⟨e₂₂, hx₂₂, hy₂₂⟩ := concreteIncidentCodeRel_iff_exists_edge.mp h₂₂
  have hp₁ : e₁₁.1.1 = e₁₂.1.1 :=
    concretePointCode_injective n (hx₁₁.symm.trans hx₁₂)
  have hp₂ : e₂₁.1.1 = e₂₂.1.1 :=
    concretePointCode_injective n (hx₂₁.symm.trans hx₂₂)
  have hell₁ : e₁₁.1.2 = e₂₁.1.2 :=
    concreteLineCode_injective n (hy₁₁.symm.trans hy₂₁)
  have hell₂ : e₁₂.1.2 = e₂₂.1.2 :=
    concreteLineCode_injective n (hy₁₂.symm.trans hy₂₂)
  have hfour := concreteIncidentEdges_noFourCycle n
    (AffineIncidence.mem_incidentEdges_iff.mp e₁₁.2)
    (hp₁ ▸ AffineIncidence.mem_incidentEdges_iff.mp e₁₂.2)
    (hell₁ ▸ AffineIncidence.mem_incidentEdges_iff.mp e₂₁.2)
    (hp₂ ▸ hell₂ ▸ AffineIncidence.mem_incidentEdges_iff.mp e₂₂.2)
  rcases hfour with hpoints | hlines
  · left
    rw [hx₁₁, hx₂₁, hpoints]
  · right
    rw [hy₁₁, hy₁₂, hlines]

lemma commonWitnessRectanglesLe_card_lt {V : Map} {α β γ : Nat} :
    (commonWitnessRectanglesLe V α β γ).card < 2 ^ (α + 1) := by
  classical
  exact (Finset.card_image_le.trans_lt (cardCompressibleWordsLt V [] α))

lemma commonWitnessRectanglesLe_side_card_lt
    {V : Map} {α β γ : Nat}
    {R : Finset BitString × Finset BitString} :
    R ∈ commonWitnessRectanglesLe V α β γ →
    R.1.card < 2 ^ (β + 1) ∧ R.2.card < 2 ^ (γ + 1) := by
  classical
  rw [commonWitnessRectanglesLe, Finset.mem_image]
  rintro ⟨z, _hz, rfl⟩
  exact ⟨cardCompressibleWordsLt V z β, cardCompressibleWordsLt V z γ⟩

lemma rectangleFamilyEdges_commonWitnessRectanglesLe {V : Map} {n α β γ : Nat} :
    rectangleFamilyEdges (concreteIncidentCodeRel n) (commonWitnessRectanglesLe V α β γ) =
      incidentCommonWitnessPairsLe V n α β γ := by
  classical
  ext p
  rcases p with ⟨x, y⟩
  simp only [rectangleFamilyEdges, Finset.mem_biUnion, commonWitnessRectanglesLe,
    Finset.mem_image, Rel.mem_interedges_iff, incidentCommonWitnessPairsLe,
    Finset.mem_filter, commonWitnessPairsLe]
  constructor
  · rintro ⟨R, ⟨z, hz, rfl⟩, hx, hy, hinc⟩
    exact ⟨⟨z, hz, Finset.mem_product.mpr ⟨hx, hy⟩⟩, hinc⟩
  · rintro ⟨⟨z, hz, hxy⟩, hinc⟩
    change (x, y) ∈
      compressibleWords V z β ×ˢ compressibleWords V z γ at hxy
    rw [Finset.mem_product] at hxy
    exact ⟨_, ⟨z, hz, rfl⟩, hxy.1, hxy.2,
      show concreteIncidentCodeRel n x y from hinc⟩

lemma muchnikThreshold_gap_exponents {n : Nat} :
    64 ≤ n →
    let t := muchnikThreshold n - 1
    let s := 3 * n - n / 8
    (t + 1) + (t + 1) + 1 ≤ s - 2 ∧
    (t + 1) + (t + 1) + (t + 2) / 2 + 1 ≤ s - 2 := by
  intro hn
  dsimp
  unfold muchnikThreshold
  omega

lemma card_incidentCommonWitnessPairsLe_bound1 {V : Map} {n α β γ : Nat} :
    (incidentCommonWitnessPairsLe V n α β γ).card ≤
      2 ^ ((α + 1) + (γ + 1) + 1) +
      2 ^ ((α + 1) + (β + 1) + (γ + 2) / 2 + 1) := by
  rw [← rectangleFamilyEdges_commonWitnessRectanglesLe]
  apply noFourCycle_rectangleFamilyEdges_card_le_pow
  · exact concreteIncidentCodeRel_noFourCycle
  · exact commonWitnessRectanglesLe_card_lt.le
  · intro R hR
    exact ⟨(commonWitnessRectanglesLe_side_card_lt hR).1.le,
      (commonWitnessRectanglesLe_side_card_lt hR).2.le⟩

lemma card_incidentCommonWitnessPairsLe_lt_source_bound1
    {V : Map} {n α β γ : Nat} :
    (incidentCommonWitnessPairsLe V n α β γ).card <
      2 ^ (α + γ / 2 + max (γ / 2) β + 6) := by
  let E := α + γ / 2 + max (γ / 2) β + 6
  have hm₁ : γ / 2 ≤ max (γ / 2) β := le_max_left _ _
  have hm₂ : β ≤ max (γ / 2) β := le_max_right _ _
  have hE : 2 ≤ E := by simp [E]
  have hA : (α + 1) + (γ + 1) + 1 ≤ E - 2 := by
    dsimp [E]
    omega
  have hB : (α + 1) + (β + 1) + (γ + 2) / 2 + 1 ≤ E - 2 := by
    dsimp [E]
    omega
  have hpA : 2 ^ ((α + 1) + (γ + 1) + 1) ≤ 2 ^ (E - 2) :=
    Nat.pow_le_pow_right (by norm_num) hA
  have hpB : 2 ^ ((α + 1) + (β + 1) + (γ + 2) / 2 + 1) ≤ 2 ^ (E - 2) :=
    Nat.pow_le_pow_right (by norm_num) hB
  calc
    (incidentCommonWitnessPairsLe V n α β γ).card
        ≤ 2 ^ ((α + 1) + (γ + 1) + 1) +
            2 ^ ((α + 1) + (β + 1) + (γ + 2) / 2 + 1) :=
      card_incidentCommonWitnessPairsLe_bound1
    _ ≤ 2 ^ (E - 2) + 2 ^ (E - 2) := Nat.add_le_add hpA hpB
    _ = 2 ^ (E - 1) := by
      rw [show E - 1 = (E - 2) + 1 by omega, pow_succ]
      omega
    _ < 2 ^ E := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = 2 ^ (α + γ / 2 + max (γ / 2) β + 6) := by rfl

lemma card_incidentCommonWitnessPairsLe_bound2 {V : Map} {n α β γ : Nat} :
    (incidentCommonWitnessPairsLe V n α β γ).card ≤
      2 ^ ((α + 1) + (β + 1) + 1) +
      2 ^ ((α + 1) + (γ + 1) + (β + 2) / 2 + 1) := by
  classical
  rw [← rectangleFamilyEdges_commonWitnessRectanglesLe]
  let M := 2 ^ ((β + 1) + 1) +
    2 ^ ((γ + 1) + ((β + 1) + 1) / 2 + 1)
  have heach : ∀ R ∈ commonWitnessRectanglesLe V α β γ,
      (Rel.interedges (concreteIncidentCodeRel n) R.1 R.2).card ≤ M := by
    intro R hR
    exact noFourCycle_interedges_card_le_pow_transpose
      (concreteIncidentCodeRel n) concreteIncidentCodeRel_noFourCycle
      (commonWitnessRectanglesLe_side_card_lt hR).1.le
      (commonWitnessRectanglesLe_side_card_lt hR).2.le
  calc
    (rectangleFamilyEdges (concreteIncidentCodeRel n)
          (commonWitnessRectanglesLe V α β γ)).card
        ≤ ∑ R ∈ commonWitnessRectanglesLe V α β γ,
            (Rel.interedges (concreteIncidentCodeRel n) R.1 R.2).card :=
      card_rectangleFamilyEdges_le_sum _ _
    _ ≤ ∑ _R ∈ commonWitnessRectanglesLe V α β γ, M :=
      Finset.sum_le_sum fun R hR => heach R hR
    _ = (commonWitnessRectanglesLe V α β γ).card * M := by simp
    _ ≤ 2 ^ (α + 1) * M := Nat.mul_le_mul_right M commonWitnessRectanglesLe_card_lt.le
    _ = 2 ^ ((α + 1) + (β + 1) + 1) +
        2 ^ ((α + 1) + (γ + 1) + (β + 2) / 2 + 1) := by
      dsimp [M]
      rw [mul_add]
      apply congrArg₂ (· + ·)
      · calc
          2 ^ (α + 1) * 2 ^ (β + 1 + 1) =
              2 ^ ((α + 1) + (β + 1 + 1)) :=
            (pow_add 2 (α + 1) (β + 1 + 1)).symm
          _ = 2 ^ ((α + 1) + (β + 1) + 1) := by
            congr 1
      · calc
          2 ^ (α + 1) * 2 ^ (γ + 1 + (β + 1 + 1) / 2 + 1) =
              2 ^ ((α + 1) + (γ + 1 + (β + 1 + 1) / 2 + 1)) :=
            (pow_add 2 (α + 1) (γ + 1 + (β + 1 + 1) / 2 + 1)).symm
          _ = 2 ^ ((α + 1) + (γ + 1) + (β + 2) / 2 + 1) := by
            congr 1
            omega

lemma card_incidentCommonWitnessPairsLe_lt_source_bound2
    {V : Map} {n α β γ : Nat} :
    (incidentCommonWitnessPairsLe V n α β γ).card <
      2 ^ (α + β / 2 + max (β / 2) γ + 6) := by
  let E := α + β / 2 + max (β / 2) γ + 6
  have hm₁ : β / 2 ≤ max (β / 2) γ := le_max_left _ _
  have hm₂ : γ ≤ max (β / 2) γ := le_max_right _ _
  have hE : 2 ≤ E := by simp [E]
  have hA : (α + 1) + (β + 1) + 1 ≤ E - 2 := by
    dsimp [E]
    omega
  have hB : (α + 1) + (γ + 1) + (β + 2) / 2 + 1 ≤ E - 2 := by
    dsimp [E]
    omega
  have hpA : 2 ^ ((α + 1) + (β + 1) + 1) ≤ 2 ^ (E - 2) :=
    Nat.pow_le_pow_right (by norm_num) hA
  have hpB : 2 ^ ((α + 1) + (γ + 1) + (β + 2) / 2 + 1) ≤ 2 ^ (E - 2) :=
    Nat.pow_le_pow_right (by norm_num) hB
  calc
    (incidentCommonWitnessPairsLe V n α β γ).card
        ≤ 2 ^ ((α + 1) + (β + 1) + 1) +
            2 ^ ((α + 1) + (γ + 1) + (β + 2) / 2 + 1) :=
      card_incidentCommonWitnessPairsLe_bound2
    _ ≤ 2 ^ (E - 2) + 2 ^ (E - 2) := Nat.add_le_add hpA hpB
    _ = 2 ^ (E - 1) := by
      rw [show E - 1 = (E - 2) + 1 by omega, pow_succ]
      omega
    _ < 2 ^ E := Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = 2 ^ (α + β / 2 + max (β / 2) γ + 6) := by rfl

lemma muchnikThreshold_incidentCommonWitness_card_lt_gap {V : Map} {n : Nat} (h : 64 ≤ n) :
    (incidentCommonWitnessPairsLe V n (muchnikThreshold n - 1)
        (muchnikThreshold n - 1) (muchnikThreshold n - 1)).card <
      2 ^ (3 * n - n / 8) := by
  let t := muchnikThreshold n - 1
  let s := 3 * n - n / 8
  have hs : 2 ≤ s := by
    dsimp [s]
    omega
  have hexp := muchnikThreshold_gap_exponents h
  have hbound := card_incidentCommonWitnessPairsLe_bound1
    (V := V) (n := n) (α := t) (β := t) (γ := t)
  have hpow₁ : 2 ^ ((t + 1) + (t + 1) + 1) ≤ 2 ^ (s - 2) :=
    Nat.pow_le_pow_right (by norm_num) hexp.1
  have hpow₂ : 2 ^ ((t + 1) + (t + 1) + (t + 2) / 2 + 1) ≤
      2 ^ (s - 2) :=
    Nat.pow_le_pow_right (by norm_num) hexp.2
  have hdouble : 2 ^ (s - 2) + 2 ^ (s - 2) = 2 ^ (s - 1) := by
    rw [show s - 1 = (s - 2) + 1 by omega, pow_succ]
    omega
  change (incidentCommonWitnessPairsLe V n t t t).card < 2 ^ s
  calc
    (incidentCommonWitnessPairsLe V n t t t).card
        ≤ 2 ^ ((t + 1) + (t + 1) + 1) +
            2 ^ ((t + 1) + (t + 1) + (t + 2) / 2 + 1) := hbound
    _ ≤ 2 ^ (s - 2) + 2 ^ (s - 2) := Nat.add_le_add hpow₁ hpow₂
    _ = 2 ^ (s - 1) := hdouble
    _ < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)

end Kolmogorov
