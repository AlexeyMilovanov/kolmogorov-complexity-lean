/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.BowenGeometry

/-!
# Pointwise pressure and lower-complexity threshold covers

The lower and upper pointwise pressures are monotone in scale and decrease when the
oracle is strengthened. Their scale suprema can be restricted to the small radii where
finite-scale infima are attained (blueprint nodes `pressure:pointwise` and
`pressure:pointwise-monotone`).

For `pressure:lower-threshold`, the strict complexity threshold is a null pressure cover
of the lower pointwise sublevel set and is enumerable relative to an admissible oracle.
The covering argument absorbs the logarithmic tuple overhead in an intermediate exponent;
the mass bound follows from Kraft's inequality. The entropy characterization and the lower
point-to-set principle use these covers.

-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- Restricting the Bowen ball increases the infimum of normalized costs. -/
private lemma finiteScalePressureRate_mono_scale (D : PressureData X) (A : Set ℕ) (x : X) (n : ℕ) :
    Monotone (fun p ↦ finiteScalePressureRate D.presentation D.T D.φ A x n (dyadicRadius p)) := by
  intro p q hpq
  dsimp [finiteScalePressureRate]
  split_ifs with hn
  · rfl
  · apply iInf_mono
    intro i
    apply iInf_mono'
    intro h_mem
    have h_rad : dyadicRadius q ≤ dyadicRadius p := dyadicRadius_antitone hpq
    have h_mem' : D.presentation.ι i ∈ bowenBall D.T n x (dyadicRadius p) := by
      dsimp [bowenBall] at *
      rw [Dynamics.mem_dynEntourage] at *
      intro k hk
      have h_lt := h_mem k hk
      exact lt_of_lt_of_le h_lt h_rad
    use h_mem'

/-- Lower time rates increase with precision. Blueprint node `pressure:pointwise-monotone`. -/
theorem pointwisePressure_mono_oracle_scale (D : PressureData X) (A : Set ℕ) (x : X) :
    Monotone (fun p => liminf (fun n => finiteScalePressureRate D.presentation D.T D.φ A x n
      (dyadicRadius p)) atTop) := by
  intro p q hpq
  exact liminf_le_liminf (Eventually.of_forall fun n ↦
    finiteScalePressureRate_mono_scale D A x n hpq)

/-- Upper time rates increase with precision. Blueprint node `pressure:pointwise-monotone`. -/
theorem pointwisePressure_mono_oracle_scale_upper (D : PressureData X) (A : Set ℕ)
    (x : X) :
    Monotone (fun p => limsup (fun n => finiteScalePressureRate D.presentation D.T D.φ A x n
      (dyadicRadius p)) atTop) := by
  intro p q hpq
  exact limsup_le_limsup (Eventually.of_forall fun n ↦
    finiteScalePressureRate_mono_scale D A x n hpq)

/-- Lower pointwise pressure is unchanged by discarding finitely many coarse scales.
Blueprint node `pressure:pointwise`. -/
theorem pointwisePressure_eq_tail (D : PressureData X) (A : Set ℕ) (x : X) :
    (pointwisePressure D.presentation D.T D.φ A x).1 =
      ⨆ p : ℕ, ⨆ (_ : D.p₀ ≤ p),
        liminf (fun n => finiteScalePressureRate D.presentation D.T D.φ A x n
          (dyadicRadius p)) atTop := by
  dsimp [pointwisePressure]
  rw [iSup_ge_eq_iSup_nat_add, (pointwisePressure_mono_oracle_scale D A x).iSup_nat_add]

/-- Upper pointwise pressure is unchanged by discarding finitely many coarse scales.
Blueprint node `pressure:pointwise`. -/
theorem pointwisePressure_eq_tail_upper (D : PressureData X) (A : Set ℕ) (x : X) :
    (pointwisePressure D.presentation D.T D.φ A x).2 =
      ⨆ p : ℕ, ⨆ (_ : D.p₀ ≤ p),
        limsup (fun n => finiteScalePressureRate D.presentation D.T D.φ A x n
          (dyadicRadius p)) atTop := by
  dsimp [pointwisePressure]
  rw [iSup_ge_eq_iSup_nat_add, (pointwisePressure_mono_oracle_scale_upper D A x).iSup_nat_add]

/-- The normalized finite-scale infimum is attained at every valid positive order.
Blueprint node `pressure:pointwise`. -/
theorem pointwisePressure_attained (D : PressureData X) (A : Set ℕ) (x : X)
    (p : ℕ) (hp : D.p₀ ≤ p) (n : ℕ) (hn : 1 ≤ n) :
    ∃ i, D.presentation.ι i ∈ bowenBall D.T n x (dyadicRadius p) ∧
      finiteScalePressureRate D.presentation D.T D.φ A x n (dyadicRadius p) =
        (((oracleNatComplexity A i + birkhoffSum D.T D.φ n (D.presentation.ι i)) / n : ℝ) :
          EReal) := by
  have hε : 0 < dyadicRadius p := by
    dsimp [dyadicRadius]
    positivity
  have hω : ∀ y z, dist y z < dyadicRadius p → |D.φ y - D.φ z| ≤ D.ω p := fun y z hyz ↦
    D.oscillation p hp y z hyz
  obtain ⟨i, hi, hmin⟩ := finite_scale_min_attained D.presentation D.T D.continuous_T D.φ A x n hn
    (dyadicRadius p) hε (D.ω p) hω
  use i, hi
  let c (j : ℕ) : ℝ := (oracleNatComplexity A j : ℝ) + birkhoffSum D.T D.φ n (D.presentation.ι j)
  have hle (j : ℕ) (hj : D.presentation.ι j ∈ bowenBall D.T n x (dyadicRadius p)) :
      c i ≤ c j := by
    apply EReal.coe_le_coe_iff.mp
    rw [← hmin]
    dsimp [finiteScalePressureCost]
    exact iInf₂_le j hj
  have hdiv (j : ℕ) (hj : D.presentation.ι j ∈ bowenBall D.T n x (dyadicRadius p)) :
      c i / n ≤ c j / n :=
    div_le_div_of_nonneg_right (hle j hj) (Nat.cast_nonneg n)
  dsimp [finiteScalePressureRate]
  have hn_ne_zero : n ≠ 0 := by omega
  rw [ite_eq_right_iff.mpr (fun h ↦ (hn_ne_zero h).elim)]
  apply le_antisymm
  · exact iInf₂_le i hi
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    exact EReal.coe_le_coe_iff.mpr (hdiv j hj)

/-- Lower pointwise pressure decreases when the oracle is strengthened.
Blueprint node `pressure:pointwise-monotone`. -/
theorem pointwisePressure_mono_oracle (D : PressureData X) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X) :
    (pointwisePressure D.presentation D.T D.φ B x).1 ≤
      (pointwisePressure D.presentation D.T D.φ A x).1 := by
  exact normalized_additive_slack_pressure D.presentation D.T D.φ A B hAB x

/-- Upper pointwise pressure has the same oracle monotonicity.
Blueprint node `pressure:pointwise-monotone`. -/
theorem pointwisePressure_mono_oracle_upper (D : PressureData X) (A B : Set ℕ)
    (hAB : charOracle A ≤ᵀ charOracle B) (x : X) :
    (pointwisePressure D.presentation D.T D.φ B x).2 ≤
      (pointwisePressure D.presentation D.T D.φ A x).2 := by
  exact normalized_additive_slack_pressure_upper D.presentation D.T D.φ A B hAB x

/-- Each threshold-cover weight is bounded by the corresponding complexity weight. -/
private lemma threshold_weight_le_complexity_weight (D : PressureData X) (A : Set ℕ)
    (s : ℚ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s) :
    (2 : ℝ≥0∞) ^ (- (s : ℝ) * t.2.1 + birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ (oracleComplexity A
        (pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2))) : ℝ) := by
  rw [show -(s : ℝ) * t.2.1 + birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1) =
    -((s : ℝ) * t.2.1 - birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1)) by ring,
    ENNReal.rpow_neg]
  rw [← ENNReal.inv_rpow]
  exact ENNReal.rpow_le_rpow_of_exponent_ge
    (ENNReal.inv_le_one.mpr (by norm_num)) ht.2.2.le

/-- The complexity weights of all bit strings have total mass at most one. -/
private lemma tsum_oracleComplexity_weight_le_one (A : Set ℕ) :
    (∑' w : BitString, (2 : ℝ≥0∞)⁻¹ ^ (oracleComplexity A w : ℝ)) ≤ 1 := by
  have hweight (w : BitString) :
      (2 : ℝ≥0∞)⁻¹ ^ (oracleComplexity A w : ℝ) =
        complexityWeight (KP (optimalOraclePrefix A) w []) := by
    rw [ENNReal.rpow_natCast, ← complexityWeight_coe]
    congr 1
    exact oraclePrefixComplexity_coe A w []
  simp_rw [hweight]
  exact (ENNReal.tsum_le_tsum fun w ↦
    complexityWeight_KP_le_aprioriMeasure (optimalOraclePrefix A) w []).trans
    (tsum_aprioriMeasure_le_one _ [] (exists_optimalOraclePrefix_spec A).2.1)

/-- The Kraft inequality bounds the mass of the lower-pressure threshold cover. -/
private lemma lowerPressureThreshold_mass_lt_top (D : PressureData X) (A : Set ℕ)
    (s : ℚ) :
    nullPressureMass D.presentation D.T D.φ (s : ℝ)
      (lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s) < ⊤ := by
  let code (t : ℕ × ℕ × ℕ) :=
    pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2))
  have hcode : Function.Injective code := by
    intro a b hab
    have hpair := @pairCode_injective
      (natBits a.1, pairCode (natBits a.2.1) (natBits a.2.2))
      (natBits b.1, pairCode (natBits b.2.1) (natBits b.2.2)) hab
    have hfirst := natBits_injective (Prod.ext_iff.mp hpair).1
    have htail := @pairCode_injective (natBits a.2.1, natBits a.2.2)
      (natBits b.2.1, natBits b.2.2) (Prod.ext_iff.mp hpair).2
    exact Prod.ext hfirst (Prod.ext (natBits_injective (Prod.ext_iff.mp htail).1)
      (natBits_injective (Prod.ext_iff.mp htail).2))
  let weight (w : BitString) := (2 : ℝ≥0∞)⁻¹ ^ (oracleComplexity A w : ℝ)
  have hmass : nullPressureMass D.presentation D.T D.φ s
      (lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s) ≤ 1 := calc
    _ ≤ ∑' t : lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s,
        weight (code t.val) :=
      ENNReal.tsum_le_tsum fun t ↦ threshold_weight_le_complexity_weight D A s t.val t.property
    _ ≤ ∑' w : BitString, weight w :=
      ENNReal.tsum_comp_le_tsum_of_injective (hcode.comp Subtype.val_injective) weight
    _ ≤ 1 := tsum_oracleComplexity_weight_le_one A
  exact hmass.trans_lt ENNReal.one_lt_top

/-- A strict pointwise pressure bound admits an intermediate exponent at every scale. -/
private lemma exists_rate_lt_of_pointwisePressure_lt
    (D : PressureData X) (A : Set ℕ) (s : ℚ) (x : X) (p : ℕ)
    (hx : (pointwisePressure D.presentation D.T D.φ A x).1 <
      ((s : ℝ) : EReal)) :
    ∃ b : ℝ, Filter.liminf (fun n ↦ finiteScalePressureRate
      D.presentation D.T D.φ A x n (dyadicRadius p)) Filter.atTop <
      (b : EReal) ∧ b < s := by
  have hle : liminf (fun n ↦ finiteScalePressureRate
      D.presentation D.T D.φ A x n (dyadicRadius p)) atTop ≤
      (pointwisePressure D.presentation D.T D.φ A x).1 := by
    unfold pointwisePressure
    exact le_iSup (fun q : ℕ ↦ liminf (fun n ↦
      finiteScalePressureRate D.presentation D.T D.φ A x n (dyadicRadius q)) atTop) p
  obtain ⟨q, hq, hqs⟩ := EReal.exists_rat_btwn_of_lt (hle.trans_lt hx)
  exact ⟨q, hq, EReal.coe_lt_coe_iff.mp hqs⟩

/-- A strict liminf bound yields arbitrarily late Bowen realizers with smaller normalized cost. -/
private lemma exists_late_realizer_of_liminf_lt
    (D : PressureData X) (A : Set ℕ) (x : X) (p : ℕ) (b : ℝ)
    (hb : Filter.liminf (fun n ↦ finiteScalePressureRate
      D.presentation D.T D.φ A x n (dyadicRadius p)) Filter.atTop <
      (b : EReal)) (N : ℕ) :
    ∃ n i, N ≤ n ∧ 1 ≤ n ∧
      x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p) ∧
      (oracleNatComplexity A i : ℝ) +
        birkhoffSum D.T D.φ n (D.presentation.ι i) < b * n := by
  have hfrequent : ∃ᶠ n in atTop,
      finiteScalePressureRate D.presentation D.T D.φ A x n (dyadicRadius p) < b :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hb
  obtain ⟨n, hn, hrate⟩ :=
    ((eventually_ge_atTop (max N 1)).and_frequently hfrequent).exists
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  unfold finiteScalePressureRate at hrate
  rw [ite_eq_right (by omega : n ≠ 0)] at hrate
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp hrate
  obtain ⟨hball, hcost⟩ := iInf_lt_iff.mp hi
  refine ⟨n, i, (le_max_left N 1).trans hn, hn1,
    (bowen_geometry_symm D n hn1 _ _ _).mp hball, ?_⟩
  exact (div_lt_iff₀ hnpos).mp (EReal.coe_lt_coe_iff.mp hcost)

/-- Encoding a time and a fixed scale adds at most logarithmic time overhead to complexity. -/
lemma oracle_triple_complexity_le
    (A : Set ℕ) (p : ℕ) :
    ∃ c : ℝ, ∀ i n : ℕ,
      (oracleComplexity A
        (pairCode (natBits i) (pairCode (natBits n) (natBits p))) : ℝ) ≤
        oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c := by
  let F : List BitString →. BitString := fun xs ↦
    Part.some (pairCode (decodeFirst (xs.headI)) (pairCode (decodeSecond (xs.headI)) (natBits p)))
  have hhead : Computable (fun xs : List BitString ↦ xs.headI) :=
    Primrec.list_headI.to_comp
  have hfirst : Computable (fun xs : List BitString ↦ decodeFirst xs.headI) :=
    (decodeFirst_computable.comp hhead).of_eq fun _ ↦ rfl
  have hsecond : Computable (fun xs : List BitString ↦ decodeSecond xs.headI) :=
    (decodeSecond_computable.comp hhead).of_eq fun _ ↦ rfl
  have htail : Computable (fun xs : List BitString ↦
      pairCode (decodeSecond xs.headI) (natBits p)) :=
    (pairCode_computable.comp (hsecond.pair (Computable.const (natBits p)))).of_eq fun _ ↦ rfl
  have hcomp : Computable (fun xs : List BitString ↦
      pairCode (decodeFirst xs.headI) (pairCode (decodeSecond xs.headI) (natBits p))) :=
    (pairCode_computable.comp (hfirst.pair htail)).of_eq fun _ ↦ rfl
  have hF : PartrecIn {charOracle A} F := PartrecIn.some.comp hcomp.computableIn
  obtain ⟨c1, hc1⟩ := oracle_tuple_bounds_composition A 1 F hF
  obtain ⟨c2, hc2⟩ := oracle_tuple_bounds_overhead A
  use c1 + c2
  intro i n
  have hF_eval : pairCode (natBits i) (pairCode (natBits n) (natBits p)) ∈
      F [pairCode (natBits i) (natBits n)] := by
    dsimp [F, List.headI, List.head?]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_some _
  have h1 := hc1 [pairCode (natBits i) (natBits n)] _ rfl hF_eval
  have h2 := hc2 i n
  have h3 : (oracleComplexity A (pairCode (natBits i) (pairCode (natBits n) (natBits p))) : ℝ) ≤
    (oracleComplexity A (pairCode (natBits i) (natBits n)) : ℝ) + c1 := by
    exact_mod_cast h1
  have h4 : (oraclePairComplexity A i n : ℝ) =
      (oracleComplexity A (pairCode (natBits i) (natBits n)) : ℝ) := rfl
  linarith

/-- The logarithmic coding overhead divided by time tends to zero. -/
private lemma tendsto_logarithmic_overhead_div
    (c : ℝ) :
    Tendsto (fun n : ℕ ↦
      (2 * Real.logb 2 (n + 1) + c) / (n : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2)
    1 (-1) 1 one_ne_zero).comp hshift
  have hlog' : Tendsto (fun n : ℕ ↦ Real.logb 2 (n + 1) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlog
  have hc : Tendsto (fun n : ℕ ↦ c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [zero_add, mul_zero, add_div, mul_div_assoc] using
    (hlog'.const_mul 2).add hc

/-- Every positive linear gap eventually absorbs the logarithmic coding overhead. -/
lemma eventually_logarithmic_overhead_lt_linear
    (s b c : ℝ) (h : b < s) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * Real.logb 2 (n + 1) + c < (s - b) * n := by
  have hlim := tendsto_logarithmic_overhead_div c
  have hδ : 0 < s - b := sub_pos.mpr h
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (2 * Real.logb 2 (n + 1) + c) / (n : ℝ) < s - b :=
    hlim.eventually (gt_mem_nhds hδ)
  filter_upwards [hsmall, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  exact (div_lt_iff₀ hnR).mp hn

/-- The lower-pressure threshold supplies arbitrarily late covers at every valid scale. -/
private lemma lowerPressureThreshold_covers_sublevel (D : PressureData X) (A : Set ℕ)
    (s : ℚ) :
    ∀ p ≥ D.p₀, ∀ N ≥ 1,
      ∀ x ∈ {x | (pointwisePressure D.presentation D.T D.φ A x).1 < ((s : ℝ) : EReal)},
        ∃ i n, N ≤ n ∧ (i, n, p) ∈ lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s ∧
          x ∈ bowenBall D.T n (D.presentation.ι i) (dyadicRadius p) := by
  intro p hp N _ x hx
  obtain ⟨b, hb, hbs⟩ := exists_rate_lt_of_pointwisePressure_lt D A s x p hx
  obtain ⟨c, hc⟩ := oracle_triple_complexity_le A p
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (eventually_logarithmic_overhead_lt_linear (s : ℝ) b c hbs)
  obtain ⟨n, i, hn, hn1, hball, hcost⟩ :=
    exists_late_realizer_of_liminf_lt D A x p b hb (max N M)
  have hNn : N ≤ n := (le_max_left N M).trans hn
  have hMn : M ≤ n := (le_max_right N M).trans hn
  refine ⟨i, n, hNn, ?_, hball⟩
  change 1 ≤ n ∧ D.p₀ ≤ p ∧ _
  refine ⟨hn1, hp, ?_⟩
  have ht := hc i n
  have ho := hM n hMn
  nlinarith [hcost]

/-- The rational lower-complexity threshold covers its strict pointwise sublevel set.
Blueprint node `pressure:lower-threshold`. -/
theorem lowerThreshold_isNullCover (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (s : ℚ) :
    IsNullPressureCover D.presentation D.T D.φ D.p₀
      {x | (pointwisePressure D.presentation D.T D.φ A x).1 < ((s : ℝ) : EReal)} s
      (lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s) := by
  rcases hA with ⟨_, _, _⟩
  refine ⟨fun t ht ↦ ⟨ht.1, ht.2.1⟩, ?_, ?_⟩
  · exact lowerPressureThreshold_mass_lt_top D A s
  · exact lowerPressureThreshold_covers_sublevel D A s

/-- The Birkhoff threshold has an enumerable strict rational lower cut in an admissible oracle. -/
private lemma birkhoff_threshold_lower_cut_re (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 ↦ D.φ) A) (s : ℚ) :
    IsREIn A (fun tq : (ℕ × ℕ × ℕ) × ℚ ↦
      (tq.2 : ℝ) < (s : ℝ) * tq.1.2.1 -
        birkhoffSum D.T D.φ tq.1.2.1 (D.presentation.ι tq.1.1)) := by
  obtain ⟨q, hq, hqerr⟩ := birkhoff_computableIn D.presentation D.T (fun _ : Fin 1 ↦ D.φ) A hA
  let v : ℕ × ℕ × ℕ → ℝ := fun t ↦
    (s : ℝ) * t.2.1 - birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1)
  have hv : IsComputableRealFamilyIn A v := by
    refine ⟨fun tm ↦ s * (tm.1.2.1 : ℚ) - q (((0 : Fin 1), tm.1.2.1, tm.1.1), tm.2), ?_, ?_⟩
    · have hargs : Computable (fun tm : (ℕ × ℕ × ℕ) × ℕ ↦
          (((0 : Fin 1), tm.1.2.1, tm.1.1), tm.2)) :=
        ((Computable.const (0 : Fin 1)).pair
          ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
           (Computable.fst.comp Computable.fst))).pair Computable.snd
      have hlinear : Computable (fun tm : (ℕ × ℕ × ℕ) × ℕ ↦ s * (tm.1.2.1 : ℚ)) :=
        computable₂_ratMul.comp (Computable.const s)
          (computable_nat_to_rat.comp (Computable.fst.comp (Computable.snd.comp Computable.fst)))
      exact computable₂_ratSub.computableIn₂.comp hlinear.computableIn (hq.comp hargs.computableIn)
    · intro t m
      dsimp [v]
      push_cast
      rw [show (s : ℝ) * (t.2.1 : ℝ) - (q (((0 : Fin 1), t.2.1, t.1), m) : ℝ) -
          ((s : ℝ) * t.2.1 - birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1)) =
          -((q (((0 : Fin 1), t.2.1, t.1), m) : ℝ) -
            birkhoffSum D.T D.φ t.2.1 (D.presentation.ι t.1)) by ring, abs_neg]
      exact hqerr ((0 : Fin 1), t.2.1, t.1) m
  exact birkhoff_computableIn_gt A v hv

/-- Encoding three natural numbers as a nested pair of bit strings is computable. -/
lemma computable_tripleCode :
    Computable (fun t : ℕ × ℕ × ℕ ↦
      pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2))) := by
  have hi : Computable (fun t : ℕ × ℕ × ℕ ↦ natBits t.1) :=
    (natBits_computable.comp (Computable.fst :
      Computable (fun t : ℕ × ℕ × ℕ ↦ t.1))).of_eq fun _ ↦ rfl
  have hn : Computable (fun t : ℕ × ℕ × ℕ ↦ natBits t.2.1) :=
    (natBits_computable.comp (Computable.fst.comp Computable.snd :
      Computable (fun t : ℕ × ℕ × ℕ ↦ t.2.1))).of_eq fun _ ↦ rfl
  have hp : Computable (fun t : ℕ × ℕ × ℕ ↦ natBits t.2.2) :=
    (natBits_computable.comp (Computable.snd.comp Computable.snd :
      Computable (fun t : ℕ × ℕ × ℕ ↦ t.2.2))).of_eq fun _ ↦ rfl
  have hnp : Computable (fun t : ℕ × ℕ × ℕ ↦ pairCode (natBits t.2.1) (natBits t.2.2)) :=
    (pairCode_computable.comp (hn.pair hp)).of_eq fun _ ↦ rfl
  exact (pairCode_computable.comp (hi.pair hnp)).of_eq fun _ ↦ rfl

/-- Admissibility makes the lower strict threshold enumerable.
Blueprint node `pressure:lower-threshold`. -/
theorem lowerThreshold_isNullCover_re (D : PressureData X) (A : Set ℕ)
    (hA : IsAdmissible D.presentation D.T (fun _ : Fin 1 => D.φ) A) (s : ℚ) :
    IsREIn A (lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s) := by
  let code (t : ℕ × ℕ × ℕ) :=
    pairCode (natBits t.1) (pairCode (natBits t.2.1) (natBits t.2.2))
  let cut (tq : (ℕ × ℕ × ℕ) × ℚ) := (oracleComplexity A (code tq.1) : ℝ) < tq.2
  let rhs (tq : (ℕ × ℕ × ℕ) × ℚ) :=
    (tq.2 : ℝ) < (s : ℝ) * tq.1.2.1 - birkhoffSum D.T D.φ tq.1.2.1 (D.presentation.ι tq.1.1)
  have hencoded : Computable (fun tq : (ℕ × ℕ × ℕ) × ℚ ↦ code tq.1) :=
    (computable_tripleCode.comp (Computable.fst :
      Computable (fun tq : (ℕ × ℕ × ℕ) × ℚ ↦ tq.1))).of_eq fun _ ↦ rfl
  have hcode : Computable (fun tq : (ℕ × ℕ × ℕ) × ℚ ↦ (code tq.1, tq.2)) :=
    hencoded.pair Computable.snd
  have hcut : IsREIn A cut := (isREIn_oracleComplexity_lt A).comp
    (f := fun tq : (ℕ × ℕ × ℕ) × ℚ ↦ (code tq.1, tq.2)) hcode.computableIn
  have hrhs : IsREIn A rhs := birkhoff_threshold_lower_cut_re D A hA s
  have hexists := (hcut.and hrhs).exists
  have horder : Computable (fun t : ℕ × ℕ × ℕ ↦ decide (1 ≤ t.2.1)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd))).to_comp
  have hscale : Computable (fun t : ℕ × ℕ × ℕ ↦ decide (D.p₀ ≤ t.2.2)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp (Primrec.const D.p₀) (Primrec.snd.comp Primrec.snd))).to_comp
  have hvalid := IsREIn.and
    (isREIn_of_computableIn_decide A _ horder.computableIn)
    (isREIn_of_computableIn_decide A _ hscale.computableIn)
  have hresult := hvalid.and hexists
  have heq :
      (fun t : ℕ × ℕ × ℕ ↦ (1 ≤ t.2.1 ∧ D.p₀ ≤ t.2.2) ∧ ∃ q, cut (t, q) ∧ rhs (t, q)) =
        lowerPressureThreshold D.presentation D.T D.φ D.p₀ A s := by
    ext t
    dsimp [lowerPressureThreshold, cut, rhs, code]
    constructor
    · rintro ⟨⟨hn, hp⟩, q, hq, hqs⟩
      exact ⟨hn, hp, hq.trans hqs⟩
    · rintro ⟨hn, hp, hlt⟩
      obtain ⟨q, hq, hqs⟩ := exists_rat_btwn hlt
      exact ⟨⟨hn, hp⟩, q, hq, hqs⟩
  rwa [heq] at hresult

end Kolmogorov.PointToSet
