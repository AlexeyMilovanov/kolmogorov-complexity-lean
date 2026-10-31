/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Upper.EffectiveEqSup

/-!
# The point-to-set principle for upper pressure and upper entropy

This module proves the upper half of Main A of the point-to-set principle: for a pressure
datum `D` and any set `Z`, the classical upper pressure of `Z` is the minimum, over all
oracles `A`, of the supremum over `x ∈ Z` of the `A`-relative pointwise upper pressure, and
the minimum is attained on a whole upper cone of oracles.

* `exists_oracle_effectiveUpper_eq` and `exists_oracle_effectiveUpper_eq_cone` (blueprint node
  `pressure:upper-attainment`): the countably many uniform nets of rational exponents above
  the upper pressure are encoded into one oracle; joined with an admissibility oracle, it
  makes the effective upper pressure equal to the classical one, and so does every stronger
  oracle.
* `upperPressure_pointToSet`, `upperPressure_pointToSet_all_oracles` and
  `upperPressure_pointToSet_cone` (blueprint node `pressure:upper-pts`): combining attainment
  with the effective-equals-supremum theorem of `Upper.EffectiveEqSup` gives the principle.
* `upperEntropy_pointToSet`, `upperEntropy_pointToSet_effective`,
  `upperEntropy_pointToSet_cone` and `upperEntropy_pointToSet_simultaneous` (blueprint node
  `pressure:upper-entropy`): the same statements for the upper entropy, obtained from the
  zero potential, and a single oracle that attains lower and upper entropy and lower and
  upper pressure for a countable family of potentials at once.

The results are used by the packing equivalences, the Bowen equations and the conformal
dimension theorem, which need one oracle witnessing several of these equalities together.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-! ### Encoding a family of enumerable sets into an oracle -/

/-- One oracle makes every member of a rationally indexed family of relations recursively
enumerable, and so does every oracle computing it. -/
private lemma exists_oracle_isREIn_family {α : Type*} [Primcodable α] (F : ℚ → α → Prop) :
    ∃ B : Set ℕ, ∀ (s : ℚ) (A : Set ℕ), charOracle B ≤ᵀ charOracle A → IsREIn A (F s) := by
  choose C hC using fun s ↦ exists_oracle_isREIn (F s)
  refine ⟨oracleCountableJoin fun j ↦ C ((Denumerable.eqv ℚ).symm j), fun s A hA ↦ hC s A ?_⟩
  have hs := oracle_joins_countable (fun j ↦ C ((Denumerable.eqv ℚ).symm j)) (Denumerable.eqv ℚ s)
  rw [Equiv.symm_apply_apply] at hs
  exact hs.trans hA

/-! ### Attainment of the upper pressure -/

/-- Effective upper attainment and admissibility persist on an upper cone.
Blueprint node `pressure:upper-attainment`. -/
theorem exists_oracle_effectiveUpper_eq_cone (D : PressureData X) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A ∧
      effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z =
        upperPressure D.T D.φ D.p₀ Z := by
  have hnet (s : ℚ) : ∃ E, upperPressure D.T D.φ D.p₀ Z < ((s : ℝ) : EReal) →
      IsUniformPressureNet D.presentation D.T D.φ D.p₀ Z (s : ℝ) E := by
    by_cases hs : upperPressure D.T D.φ D.p₀ Z < ((s : ℝ) : EReal)
    · obtain ⟨E, hE⟩ := exists_uniformNet_of_upperPressure_lt D Z (s : ℝ) hs
      exact ⟨E, fun _ ↦ hE⟩
    · exact ⟨∅, fun h ↦ (hs h).elim⟩
  choose E hE using hnet
  obtain ⟨B₀, hB₀⟩ := exists_oracle_isREIn_family E
  obtain ⟨C, hC⟩ := exists_admissible_base D.presentation D.T D.continuous_T
    (fun _ : Fin 1 => D.φ) (fun _ ↦ D.uniformContinuous_φ.continuous)
  refine ⟨oracleJoin C B₀, fun A hA ↦ ⟨hC A ((oracle_joins C B₀).trans hA), ?_⟩⟩
  refine le_antisymm (not_lt.mp fun h_lt ↦ ?_) (effectiveUpperPressure_ge D A Z)
  obtain ⟨s, hs1, hs2⟩ := EReal.exists_rat_btwn_of_lt h_lt
  have hREIn : IsREIn A (E s) := hB₀ s A ((oracle_joins_right C B₀).trans hA)
  have h_inf : effectiveUpperPressure D.presentation D.T D.φ D.p₀ A Z ≤ ((s : ℝ) : EReal) :=
    iInf_le_of_le (s : ℝ) <| iInf_le_of_le (E s) <| iInf_le_of_le ⟨hE s hs1, hREIn⟩ le_rfl
  exact lt_irrefl _ (h_inf.trans_lt hs2)

/-- Some admissible oracle attains classical upper pressure by its effective value.
Blueprint node `pressure:upper-attainment`. -/
theorem exists_oracle_effectiveUpper_eq (D : PressureData X) (Z : Set X) :
    ∃ B : Set ℕ, IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) B ∧
      effectiveUpperPressure D.presentation D.T D.φ D.p₀ B Z =
        upperPressure D.T D.φ D.p₀ Z := by
  obtain ⟨B, hB⟩ := exists_oracle_effectiveUpper_eq_cone D Z
  exact ⟨B, hB B (TuringReducible.refl _)⟩

/-! ### The point-to-set principle for upper pressure -/

/-- An entire upper cone realizes the upper point-to-set minimum.
Blueprint node `pressure:upper-pts`. -/
theorem upperPressure_pointToSet_cone (D : PressureData X) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      upperPressure D.T D.φ D.p₀ Z =
        ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).2 := by
  obtain ⟨B, hB⟩ := exists_oracle_effectiveUpper_eq_cone D Z
  refine ⟨B, fun A hA ↦ ?_⟩
  obtain ⟨hA_admissible, hA_eq⟩ := hB A hA
  rw [← hA_eq]
  exact effectiveUpperPressure_eq_iSup_pointwise D A hA_admissible Z

/-- No oracle gives a pointwise upper supremum below the classical upper pressure.
Blueprint node `pressure:upper-pts`. -/
theorem upperPressure_pointToSet_all_oracles (D : PressureData X) (Z : Set X) (A : Set ℕ) :
    upperPressure D.T D.φ D.p₀ Z ≤
      ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).2 := by
  obtain ⟨B, hB⟩ := upperPressure_pointToSet_cone D Z
  rw [hB (oracleJoin A B) (oracle_joins_right A B)]
  exact iSup₂_mono fun x _ ↦
    pointwisePressure_mono_oracle_upper D A (oracleJoin A B) (oracle_joins A B) x

/-- The upper pressure point-to-set infimum ranges over every oracle.
Blueprint node `pressure:upper-pts`. -/
theorem upperPressure_pointToSet (D : PressureData X) (Z : Set X) :
    upperPressure D.T D.φ D.p₀ Z =
      ⨅ A : Set ℕ, ⨆ x ∈ Z, (pointwisePressure D.presentation D.T D.φ A x).2 := by
  refine le_antisymm (le_iInf (upperPressure_pointToSet_all_oracles D Z)) ?_
  obtain ⟨B, hB⟩ := upperPressure_pointToSet_cone D Z
  exact (iInf_le _ B).trans (hB B (TuringReducible.refl _)).ge

/-! ### Coercions from `ℝ≥0∞` to `EReal` -/

/-! ### Upper entropy as pressure of the zero potential -/

/-- For the zero potential, the upper pointwise pressure is the upper orbit complexity,
viewed in `EReal`. -/
private lemma pointwisePressure_zero_snd (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X) :
    (pointwisePressure P T (fun _ ↦ 0) A x).2 = ((orbitComplexities P T A x).2 : EReal) := by
  unfold pointwisePressure orbitComplexities pointwiseBSDimension
  dsimp only
  rw [EReal.coe_ennreal_iSup]
  refine iSup_congr fun p ↦ ?_
  rw [EReal.coe_ennreal_limsup]
  simp only [finiteScalePressureRate_zero]

/-- Upper entropy is the all-oracle infimum of nonnegative upper orbit-rate suprema.
Blueprint node `pressure:upper-entropy`. -/
theorem upperEntropy_pointToSet (P : Presentation X) (T : X → X) (hT : Continuous T)
    (Z : Set X) :
    upperEntropy P T Z = ⨅ A : Set ℕ, ⨆ x ∈ Z, (orbitComplexities P T A x).2 := by
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · rw [entropiesAndOrbitComplexities_empty_upper]
    simp
  · refine EReal.coe_ennreal_injective ?_
    rw [entropy_eq_zeroPotentialPressure_of_nonempty_upper P T hT Z hZ, EReal.coe_ennreal_iInf]
    refine (upperPressure_pointToSet (zeroPotentialData P T hT) Z).trans (iInf_congr fun A ↦ ?_)
    rw [EReal.coe_ennreal_biSup hZ]
    exact iSup_congr fun x ↦ iSup_congr fun _ ↦ pointwisePressure_zero_snd P T A x

/-- The effective upper entropy equality holds for arbitrary oracles in this corollary too.
Blueprint node `pressure:upper-entropy`. -/
theorem upperEntropy_pointToSet_effective (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (Z : Set X) :
    effectiveUpperEntropy P T A Z = ⨆ x ∈ Z, (orbitComplexities P T A x).2 :=
  entropy_effectiveCharacterization_allOracles_upper P T hT A Z

/-- Upper entropy attainment persists under every further oracle strengthening.
Blueprint node `pressure:upper-entropy`. -/
theorem upperEntropy_pointToSet_cone (P : Presentation X) (T : X → X)
    (hT : Continuous T) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      upperEntropy P T Z = ⨆ x ∈ Z, (orbitComplexities P T A x).2 := by
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · exact ⟨∅, fun A _ ↦ by
      rw [entropiesAndOrbitComplexities_empty_upper, iSup_emptyset, bot_eq_zero]⟩
  · obtain ⟨B, hB⟩ := exists_oracle_effectiveUpper_eq_cone (zeroPotentialData P T hT) Z
    refine ⟨B, fun A hA ↦ ?_⟩
    rw [← upperEntropy_pointToSet_effective P T hT A Z]
    refine EReal.coe_ennreal_injective ?_
    rw [entropy_eq_zeroPotentialPressure_of_nonempty_upper P T hT Z hZ,
      entropy_eq_zeroPotentialPressure_of_nonempty_effective_upper P T A Z hZ]
    exact (hB A hA).2.symm

/-! ### One oracle for entropies and pressures of countably many potentials -/

/-- Every uniformly continuous potential carries a pressure datum on a given presentation and
dynamics, with the first valid scale as large as desired. -/
private lemma exists_pressureData_of_uniformContinuous (P : Presentation X) (T : X → X)
    (hT : Continuous T) (ψ : X → ℝ) (hψ : UniformContinuous ψ) (p : ℕ) :
    ∃ D : PressureData X, D.presentation = P ∧ D.T = T ∧ D.φ = ψ ∧ p ≤ D.p₀ := by
  obtain ⟨ω, hω_pos, hω_tendsto, p₁, hosc⟩ := small_scale_oscillation ψ hψ
  refine ⟨
    { presentation := P
      T := T
      continuous_T := hT
      φ := ψ
      uniformContinuous_φ := hψ
      p₀ := max p p₁
      ω := ω
      ω_pos := fun q _ ↦ hω_pos q
      ω_tendsto := hω_tendsto
      oscillation := fun q hq x y hxy ↦
        hosc q ((le_max_right p p₁).trans hq) x y
          (hxy.trans (lt_two_mul_self (pow_pos (by norm_num) q))) },
    rfl, rfl, rfl, le_max_left p p₁⟩

/-- Lower pressure does not depend on the first scale of the supremum. -/
private lemma lowerPressure_eq_of_first_scale (D : PressureData X) (p q : ℕ) (Z : Set X) :
    lowerPressure D.T D.φ p Z = lowerPressure D.T D.φ q Z := by
  have hmono : Monotone fun k ↦ lowerPressureAt D.T D.φ .centered Z (dyadicRadius k) :=
    fun m n hmn ↦ lowerPressure_eq_centered_radius D Z _ _
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)
  unfold lowerPressure
  rw [iSup_ge_eq_iSup_nat_add, iSup_ge_eq_iSup_nat_add, hmono.iSup_nat_add, hmono.iSup_nat_add]

/-- Upper pressure does not depend on the first scale of the supremum. -/
private lemma upperPressure_eq_of_first_scale (D : PressureData X) (p q : ℕ) (Z : Set X) :
    upperPressure D.T D.φ p Z = upperPressure D.T D.φ q Z := by
  have hmono : Monotone fun k ↦ modifiedUpperPressure D.T D.φ .centered Z (dyadicRadius k) :=
    fun m n hmn ↦ upperPressure_scale_comparison_modified_radius D Z _ _
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)
  unfold upperPressure
  rw [iSup_ge_eq_iSup_nat_add, iSup_ge_eq_iSup_nat_add, hmono.iSup_nat_add, hmono.iSup_nat_add]

/-- One oracle, and every oracle above it, attains the lower and the upper pressure of any
uniformly continuous potential from any first scale. -/
private lemma exists_oracle_lowerPressure_upperPressure_cone (P : Presentation X) (T : X → X)
    (hT : Continuous T) (ψ : X → ℝ) (hψ : UniformContinuous ψ) (p₀ : ℕ) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      lowerPressure T ψ p₀ Z = (⨆ x ∈ Z, (pointwisePressure P T ψ A x).1) ∧
      upperPressure T ψ p₀ Z = (⨆ x ∈ Z, (pointwisePressure P T ψ A x).2) := by
  obtain ⟨D, rfl, rfl, rfl, -⟩ := exists_pressureData_of_uniformContinuous P T hT ψ hψ p₀
  obtain ⟨B₁, hB₁⟩ := lowerPressure_pointToSet_cone D Z
  obtain ⟨B₂, hB₂⟩ := upperPressure_pointToSet_cone D Z
  refine ⟨oracleJoin B₁ B₂, fun A hA ↦ ?_⟩
  rw [lowerPressure_eq_of_first_scale D p₀ D.p₀, upperPressure_eq_of_first_scale D p₀ D.p₀]
  exact ⟨hB₁ A ((oracle_joins B₁ B₂).trans hA), hB₂ A ((oracle_joins_right B₁ B₂).trans hA)⟩

/-- One oracle and every stronger oracle simultaneously attain both entropies and both
pressures for a countable list of potentials on the same fixed presentation. Each
potential may use its own cofinal scale cutoff. Blueprint node `pressure:upper-entropy`. -/
theorem upperEntropy_pointToSet_simultaneous (P : Presentation X) (T : X → X)
    (hT : Continuous T) (φ : ℕ → X → ℝ) (hφ : ∀ j, UniformContinuous (φ j))
    (p₀ : ℕ → ℕ) (Z : Set X) :
    ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      lowerEntropy T Z = (⨆ x ∈ Z, (orbitComplexities P T A x).1) ∧
      upperEntropy P T Z = (⨆ x ∈ Z, (orbitComplexities P T A x).2) ∧
      ∀ j, lowerPressure T (φ j) (p₀ j) Z =
          (⨆ x ∈ Z, (pointwisePressure P T (φ j) A x).1) ∧
        upperPressure T (φ j) (p₀ j) Z =
          (⨆ x ∈ Z, (pointwisePressure P T (φ j) A x).2) := by
  obtain ⟨B_L, hB_L⟩ := entropy_effectiveCharacterization_allOracles_cone P T hT Z
  obtain ⟨B_U, hB_U⟩ := upperEntropy_pointToSet_cone P T hT Z
  choose B hB using fun j ↦
    exists_oracle_lowerPressure_upperPressure_cone P T hT (φ j) (hφ j) (p₀ j) Z
  refine ⟨oracleJoin (oracleJoin B_L B_U) (oracleCountableJoin B), fun A hA ↦ ?_⟩
  have hA_entropy := (oracle_joins (oracleJoin B_L B_U) (oracleCountableJoin B)).trans hA
  have hA_pressure := (oracle_joins_right (oracleJoin B_L B_U) (oracleCountableJoin B)).trans hA
  exact ⟨hB_L A ((oracle_joins B_L B_U).trans hA_entropy),
    hB_U A ((oracle_joins_right B_L B_U).trans hA_entropy),
    fun j ↦ hB j A ((oracle_joins_countable B j).trans hA_pressure)⟩

end Kolmogorov.PointToSet
