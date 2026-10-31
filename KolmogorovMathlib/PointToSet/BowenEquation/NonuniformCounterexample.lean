/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BowenEquation.SetRoot

/-!
# Existence of the Bowen root under a uniform bound, and a nonuniform counterexample

This module closes the discussion of the set-level Bowen equation for the
Barreira–Schmeling dimension with two results.

* `setBowenRootUniqueness_exists` (blueprint node `bs:set-root-unique`): if the entropy of `Z` is
  finite, the Birkhoff averages of the potential are bounded below by a positive constant on `Z`
  and above by a common constant `β`, then Bowen's equation has a unique real solution, namely
  the Barreira–Schmeling dimension of `Z`.  It combines the finite-dimension and uniqueness
  statements with the existence statement `setBowenRootOfFiniteBSDimension` of
  `KolmogorovMathlib.PointToSet.BowenEquation.SetRoot`.
* `counterexampleNonuniformBowenExistence` (blueprint node `bs:counterexample-existence`): the
  hypotheses "finite entropy and `0 < ℓ(x) ≤ b(x) ≤ 1`" do not suffice without the *uniform*
  positive lower bound: there is a complete separable system with both entropies equal to `1`,
  infinite Barreira–Schmeling dimensions and a pressure function that never vanishes.

The counterexample is the countable disjoint union `ℕ × {0,1}^ℕ` of Cantor spaces, with the
product metric (distinct components are at distance at least one), the shift on every component
and the potential `1 / (j + 1)` on component `j`.  At dyadic radius `2⁻ᵖ` the Bowen ball of order
`n ≥ 1` is a cylinder of length `n + p` inside one component.  Counting such cylinders bounds the
pressure of a component from above, and the Bernoulli measure of the cylinders bounds it from
below, so both pressures of component `j` equal `1 - s / (j + 1)`.  By countable stability of
pressure, which follows from the point-to-set principle for pressure, the pressure of the union is
the supremum over the components, which is `1` for every `s ≥ 0`.

The module is imported by `KolmogorovMathlib.PointToSet.BowenEquation`.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]
section UniformLower
variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (Z : Set X) (hne : Z.Nonempty) (α : ℝ) (hα : 0 < α)
  (hZ : ∀ x ∈ Z, (α : EReal) ≤ lowerBirkhoffAverage T u x ∧
    upperBirkhoffAverage T u x < ⊤) (σ : LimitSide)
  (hfinite : σ.choose (lowerEntropy T Z, upperEntropy P T Z) < ⊤)
include hT hu hne hα hZ hfinite

/-- With a common finite upper-average bound the unique real root exists and is the dimension.
Blueprint node `bs:set-root-unique`. -/
theorem setBowenRootUniqueness_exists (β : ℝ)
    (hupper : ∀ x ∈ Z, upperBirkhoffAverage T u x ≤ (β : EReal)) :
    ∃ d : ℝ, 0 ≤ d ∧
      ENNReal.ofReal d = σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) ∧
      ∀ s : ℝ, σ.choose (lowerPressure T (fun y => -s * u y) 0 Z,
        upperPressure T (fun y => -s * u y) 0 Z) = 0 ↔ s = d := by
  have Hdim_finite := setBowenRootUniqueness_dimension_finite P T hT u hu Z hne α hα hZ σ hfinite
  have Hcond : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x ∧
      upperBirkhoffAverage T u x ≤ (β : EReal) := fun x hx ↦
    ⟨lt_of_lt_of_le (EReal.coe_pos.mpr hα) (hZ x hx).1, hupper x hx⟩
  have Hroot := setBowenRootOfFiniteBSDimension P T hT u hu Z hne β Hcond σ Hdim_finite
  let d := (σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z)).toReal
  have Hdim_eq : ENNReal.ofReal d = σ.choose (lowerBSDimension T u Z, upperBSDimension T u Z) :=
    ENNReal.ofReal_toReal (ne_top_of_lt Hdim_finite)
  refine ⟨d, ENNReal.toReal_nonneg, Hdim_eq, fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩⟩
  · exact setBowenRootUniqueness P T hT u hu Z hne α hα hZ σ hfinite s d hs Hroot
  · rw [hs]
    exact Hroot

end UniformLower

namespace NonuniformCounterexample

/-- The countable separated union of copies of the one-sided binary shift space. -/
private abbrev Space := ℕ × (ℕ → Bool)

/-- Use the product metric: distinct natural-number components are at least distance one
apart, and each component has the standard binary ultrametric. -/
private noncomputable abbrev spaceMetric : MetricSpace Space := by
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpaceOfDiscreteUniformity (fun _ ↦ rfl)
  exact inferInstanceAs (MetricSpace (ℕ × (ℕ → Bool)))

attribute [local instance] spaceMetric

/-- Completeness and a fixed dense sequence for the concrete union. -/
private noncomputable def presentation : Presentation Space := by
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpaceOfDiscreteUniformity (fun _ ↦ rfl)
  letI : CompleteSpace (ℕ → Bool) := inferInstance
  exact { ι := TopologicalSpace.denseSeq (ℕ × (ℕ → Bool))
          dense := TopologicalSpace.denseRange_denseSeq _
          complete := inferInstance }

/-- The componentwise left shift. -/
private def shift (x : Space) : Space := (x.1, fun k ↦ x.2 (k + 1))

/-- The potential equal to `1 / (j + 1)` on the `j`-th component. -/
private noncomputable def potential (x : Space) : ℝ := 1 / (x.1 + 1 : ℝ)

/-- The `j`-th component of the union. -/
private def component (j : ℕ) : Set Space := {x | x.1 = j}

/-- The componentwise left shift is continuous in the product topology. -/
private theorem continuous_shift : Continuous shift := by
  let _ : MetricSpace (ℕ → Bool) := PiNat.metricSpaceOfDiscreteUniformity (fun _ ↦ rfl)
  change Continuous (fun x : ℕ × (ℕ → Bool) ↦ (x.1, fun k ↦ x.2 (k + 1)))
  exact continuous_fst.prodMk (continuous_pi (fun k ↦
    (continuous_apply (k + 1)).comp continuous_snd))

/-- Two natural numbers at distance less than one are equal. -/
private theorem eq_of_dist_lt_one {a b : ℕ} (h : dist a b < 1) : a = b := by
  rw [Nat.dist_eq, abs_lt] at h
  have hab : a < b + 1 := by
    exact_mod_cast (show (a : ℝ) < (b : ℝ) + 1 by linarith [h.2])
  have hba : b < a + 1 := by
    exact_mod_cast (show (b : ℝ) < (a : ℝ) + 1 by linarith [h.1])
  omega

/-- The reciprocal component potential is uniformly continuous because components are
separated. -/
private theorem uniformContinuous_potential : UniformContinuous potential := by
  let _ : MetricSpace (ℕ → Bool) := PiNat.metricSpaceOfDiscreteUniformity (fun _ ↦ rfl)
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro x y hxy
  have h : x.1 = y.1 := eq_of_dist_lt_one (lt_of_le_of_lt (le_max_left _ _) hxy)
  simp only [potential, h, dist_self]
  exact hε

/-- Iteration of the shift preserves the component and shifts the binary coordinates. -/
private theorem shift_iterate (n : ℕ) (x : Space) :
    shift^[n] x = (x.1, fun k ↦ x.2 (k + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [shift, Nat.add_left_comm, Nat.add_comm]

/-- A potential depending only on the component has constant orbit averages. -/
private theorem birkhoffSum_shift_comp_fst (g : ℕ → ℝ) (n : ℕ) (x : Space) :
    birkhoffSum shift (fun y ↦ g y.1) n x = n * g x.1 := by
  simp [birkhoffSum, shift_iterate]

/-- Both Birkhoff averages of the potential are exactly the positive reciprocal component
index. -/
private theorem birkhoffAverage_potential (x : Space) :
    lowerBirkhoffAverage shift potential x = ((1 / (x.1 + 1 : ℝ) : ℝ) : EReal) ∧
    upperBirkhoffAverage shift potential x = ((1 / (x.1 + 1 : ℝ) : ℝ) : EReal) := by
  have h : (fun n ↦ ((birkhoffSum shift potential n x / n : ℝ) : EReal)) =ᶠ[atTop]
      fun _ ↦ ((1 / (x.1 + 1 : ℝ) : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    change (((birkhoffSum shift (fun y ↦ 1 / (y.1 + 1 : ℝ)) n x) / n : ℝ) : EReal) = _
    rw [birkhoffSum_shift_comp_fst (fun j : ℕ ↦ 1 / (j + 1 : ℝ)) n x]
    congr 1
    field_simp
  exact ⟨(liminf_congr h).trans (liminf_const _), (limsup_congr h).trans (limsup_const _)⟩

/-- Two points of the Cantor space are closer than `2⁻ᵖ` iff they agree up to coordinate `p`. -/
private theorem dist_lt_dyadicRadius_iff (a b : ℕ → Bool) (p : ℕ) :
    @dist (ℕ → Bool) PiNat.dist a b < dyadicRadius p ↔ ∀ i ≤ p, a i = b i := by
  constructor
  · intro h i hi
    apply PiNat.apply_eq_of_dist_lt (n := p) _ hi
    simpa [dyadicRadius, one_div] using h
  · intro h
    have hb : b ∈ PiNat.cylinder a (p + 1) := by
      intro i hi
      exact (h i (by omega)).symm
    have hd := PiNat.mem_cylinder_iff_dist_le.mp hb
    rw [PiNat.dist_comm] at hd
    apply hd.trans_lt
    simp only [dyadicRadius, one_div, pow_succ]
    have hp : 0 < (2⁻¹ : ℝ) ^ p := by positivity
    nlinarith

/-- An order-`n` ball at dyadic radius `p` is exactly a length-`n+p` binary cylinder in its
component; the positive-order hypothesis also separates components. -/
private theorem bowenBall_shift_dyadicRadius (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (x : Space) :
    bowenBall shift n x (dyadicRadius p) = {y | y.1 = x.1 ∧ ∀ k < n + p, y.2 k = x.2 k} := by
  have hr : dyadicRadius p ≤ 1 := by
    unfold dyadicRadius
    exact pow_le_one₀ (by norm_num) (by norm_num)
  ext y
  simp only [bowenBall, Dynamics.mem_dynEntourage, Set.mem_ofPred_eq]
  constructor
  · intro h
    have hdist (t : ℕ) (ht : t < n) :
        max (dist x.1 y.1)
          (@dist (ℕ → Bool) PiNat.dist (fun k ↦ x.2 (k + t))
            (fun k ↦ y.2 (k + t))) < dyadicRadius p := by
      simpa only [shift_iterate, Prod.dist_eq, Prod.fst, Prod.snd] using h t ht
    have hxy : x.1 = y.1 :=
      eq_of_dist_lt_one ((max_lt_iff.mp (hdist 0 (by omega))).1.trans_le hr)
    refine ⟨hxy.symm, ?_⟩
    intro k hk
    let t := min k (n - 1)
    have ht : t < n := by dsimp [t]; omega
    have hi : k - t ≤ p := by dsimp [t]; omega
    have htk : (k - t) + t = k := by dsimp [t]; omega
    have heq := (dist_lt_dyadicRadius_iff _ _ p).mp (max_lt_iff.mp (hdist t ht)).2 (k - t) hi
    simpa only [htk] using heq.symm
  · rintro ⟨hxy, hprefix⟩ t ht
    rw [shift_iterate, shift_iterate]
    change max (dist x.1 y.1)
      (@dist (ℕ → Bool) PiNat.dist (fun k ↦ x.2 (k + t)) (fun k ↦ y.2 (k + t))) <
        dyadicRadius p
    apply max_lt_iff.mpr
    constructor
    · rw [hxy, dist_self]
      unfold dyadicRadius
      positivity
    · apply (dist_lt_dyadicRadius_iff _ _ p).mpr
      intro i hi
      exact (hprefix (i + t) (by omega)).symm

/-- The inverse of a power of two in `ℝ≥0∞` as a real power with negative exponent. -/
private theorem inv_pow_eq_rpow_neg (L : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ L = (2 : ℝ≥0∞) ^ (-(L : ℝ)) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]

/-- A sequence `a * 2 ^ (b * n + c)` with `a` finite and nonzero has pressure rate `b`. -/
private theorem tendsto_pressureRate_mul_two_rpow (a : ℝ≥0∞) (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (b c : ℝ) :
    Tendsto (pressureRate (fun n ↦ a * (2 : ℝ≥0∞) ^ (b * n + c))) atTop (𝓝 (b : EReal)) := by
  have hlog2 : ENNReal.log 2 = ((Real.log 2 : ℝ) : EReal) := by
    simpa using ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hformula (n : ℕ) (hn : n ≠ 0) :
      pressureRate (fun n ↦ a * (2 : ℝ≥0∞) ^ (b * n + c)) n =
        ((b + (Real.log a.toReal / Real.log 2 + c) / n : ℝ) : EReal) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [pressureRate, hn, ↓reduceIte, pressureLog, ENNReal.log_mul_add,
      ENNReal.log_rpow, ENNReal.log_pos_real ha0 hatop, hlog2,
      ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    field_simp
    ring
  have ht : Tendsto (fun n : ℕ ↦ b + (Real.log a.toReal / Real.log 2 + c) / n)
      atTop (𝓝 b) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log a.toReal / Real.log 2 + c))
  apply (continuous_coe_real_ereal.tendsto b |>.comp ht).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hformula n (by omega)).symm

/-- The Bernoulli measure of a cylinder of length `L` is `2⁻ᴸ`. -/
private theorem uniformMeasure_cylinder (a : ℕ → Bool) (L : ℕ) :
    uniformMeasure {b : ℕ → Bool | ∀ k < L, b k = a k} = (2 : ℝ≥0∞)⁻¹ ^ L := by
  have hset : {b : ℕ → Bool | ∀ k < L, b k = a k} = cantorCylinder (cantorPrefix a L) := by
    ext b
    simp [cantorCylinder, IsCantorPrefix]
  rw [hset]
  simpa only [cantorMass, cantorPrefix_length] using cantorMass_uniformMeasure (cantorPrefix a L)

/-- The Birkhoff sum of the slope-`s` potential is the constant `-(s / (j + 1)) * n`. -/
private theorem birkhoffSum_shift_potential (s : ℝ) (n : ℕ) (x : Space) :
    birkhoffSum shift (fun y ↦ -s * potential y) n x = -(s / (x.1 + 1 : ℝ)) * n := by
  change birkhoffSum shift (fun y ↦ -s * (1 / (y.1 + 1 : ℝ))) n x = _
  rw [birkhoffSum_shift_comp_fst (fun j ↦ -s * (1 / (j + 1 : ℝ))) n x]
  ring

/-- Component `j` is covered by `2 ^ (n + p)` Bowen balls of order `n` and radius `2⁻ᵖ`
centered in the component. -/
private theorem exists_finset_cover_component (j n p : ℕ) (hn : 1 ≤ n) :
    ∃ F : Finset Space, F.card ≤ 2 ^ (n + p) ∧ (∀ y ∈ F, y.1 = j) ∧
      component j ⊆ ⋃ y ∈ (F : Set Space), bowenBall shift n y (dyadicRadius p) := by
  classical
  let c : (Fin (n + p) → Bool) → Space :=
    fun a ↦ (j, fun i ↦ if h : i < n + p then a ⟨i, h⟩ else false)
  let F : Finset Space := Finset.univ.image c
  refine ⟨F, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
    rfl
  · intro x hx
    let a : Fin (n + p) → Bool := fun i ↦ x.2 i
    apply Set.mem_iUnion.mpr
    refine ⟨c a, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    · rw [bowenBall_shift_dyadicRadius n hn p (c a)]
      refine ⟨hx, ?_⟩
      intro k hk
      simp [c, a, hk]

/-- The Bernoulli measure of the slice in component `j` of an order-`n` Bowen ball is `2⁻⁽ⁿ⁺ᵖ⁾`
if the ball is centered in component `j` and `0` otherwise. -/
private theorem uniformMeasure_bowenBall_slice (j n p : ℕ) (hn : 1 ≤ n) (x : Space) :
    uniformMeasure {a : ℕ → Bool | (j, a) ∈ bowenBall shift n x (dyadicRadius p)} =
      if x.1 = j then (2 : ℝ≥0∞)⁻¹ ^ (n + p) else 0 := by
  rw [bowenBall_shift_dyadicRadius n hn p x]
  change uniformMeasure {a : ℕ → Bool | j = x.1 ∧ ∀ k < n + p, a k = x.2 k} = _
  by_cases h : x.1 = j
  · simp only [h, ite_true, true_and]
    exact uniformMeasure_cylinder x.2 (n + p)
  · simp [h, Ne.symm h]

/-- Component `j` has a finite cover by order-`n` balls of radius `2⁻ᵖ` whose partition cover
cost at the potential `-s * potential` is at most `2 ^ ((1 - s / (j + 1)) * n + p)`. -/
private theorem exists_finset_partitionCoverCost_le (j n p : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    ∃ F : Finset Space,
      (component j ⊆ ⋃ y ∈ (F : Set Space), bowenBall shift n y (dyadicRadius p)) ∧
      partitionCoverCost shift (fun y ↦ -s * potential y) .centered
        (F : Set Space) n (dyadicRadius p) ≤
        (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ)) * n + p) := by
  classical
  obtain ⟨F, hcard, hmem, hcov⟩ := exists_finset_cover_component j n p hn
  let w : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-(s / (j + 1 : ℝ)) * n)
  have hcost : partitionCoverCost shift (fun y ↦ -s * potential y) .centered
      (F : Set Space) n (dyadicRadius p) = (F.card : ℝ≥0∞) * w := by
    unfold partitionCoverCost
    have hconst (y : (F : Set Space)) :
        pressureBallWeight shift (fun y ↦ -s * potential y) .centered n y (dyadicRadius p) =
          w := by
      simp only [pressureBallWeight, birkhoffSum_shift_potential, hmem y y.property, w]
    simp only [hconst, tsum_fintype]
    simp
  refine ⟨F, hcov, ?_⟩
  calc
    _ = (F.card : ℝ≥0∞) * w := hcost
    _ ≤ (2 : ℝ≥0∞) ^ (n + p) * w := by
      apply mul_le_mul_of_nonneg_right _ bot_le
      exact_mod_cast hcard
    _ = _ := by
      dsimp only [w]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      push_cast
      ring

/-- The partition sum of component `j` at order `n` and radius `2⁻ᵖ` is at most
`2 ^ ((1 - s / (j + 1)) * n + p)`. -/
private theorem partitionSum_component_le (j n p : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    partitionSum shift (fun y ↦ -s * potential y) .centered (component j) n (dyadicRadius p) ≤
      (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ)) * n + p) := by
  obtain ⟨F, hF, hcost⟩ := exists_finset_partitionCoverCost_le j n p hn s
  apply le_trans ?_ hcost
  exact iInf_le_of_le (F : Set Space) (iInf_le_of_le ⟨F.countable_toSet, hF⟩ le_rfl)

/-- A finite family of order-`n` balls covering `Z` bounds the lower content of `Z` by the
partition cover cost of that family, weighted by `2 ^ (-t * n)`. -/
private theorem lowerContent_le_of_finset_cover (s t : ℝ) (p n N : ℕ) (hn : max 1 N ≤ n)
    (Z : Set Space) (F : Finset Space)
    (hF : Z ⊆ ⋃ y ∈ (F : Set Space), bowenBall shift n y (dyadicRadius p)) :
    lowerContent shift (fun y ↦ -s * potential y) .centered Z t (dyadicRadius p) N ≤
    (2 : ℝ≥0∞) ^ (-t * n) * partitionCoverCost shift (fun y ↦ -s * potential y) .centered
      (F : Set Space) n (dyadicRadius p) := by
  classical
  let e : {i : ℕ // i < F.card} ≃ (F : Set Space) := {
    toFun i := F.equivFin.symm ⟨i.1, i.2⟩
    invFun y := ⟨(F.equivFin y).1, (F.equivFin y).2⟩
    left_inv i := by
      apply Subtype.ext
      exact congrArg Fin.val (F.equivFin.apply_symm_apply ⟨i.1, i.2⟩)
    right_inv y := F.equivFin.symm_apply_apply y }
  let C : BowenCoverFamily Space := {
    index := {i | i < F.card}
    center i := (e i).1
    order _ := n }
  have hC : IsBowenCover shift Z (dyadicRadius p) N C := by
    refine ⟨fun _ ↦ hn, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF hx)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, ?_⟩
    change x ∈ bowenBall shift n (e (e.symm ⟨y, hy⟩)).1 (dyadicRadius p)
    simpa using hxy
  apply (iInf_le_of_le C (iInf_le_of_le hC le_rfl)).trans_eq
  change (∑' i : {i : ℕ // i < F.card}, (2 : ℝ≥0∞) ^ (-t * n) *
    pressureBallWeight shift (fun y ↦ -s * potential y) .centered n (e i).1
      (dyadicRadius p)) = _
  rw [ENNReal.tsum_mul_left]
  congr 1
  exact e.tsum_eq (fun y ↦ pressureBallWeight shift (fun y ↦ -s * potential y) .centered
    n y.1 (dyadicRadius p))

/-- Equal-order covers by the `2^(n+p)` binary cylinders make the lower content of a component
vanish above the component rate. -/
private theorem lowerContentLimit_component_eq_zero (j p : ℕ) (s t : ℝ)
    (ht : 1 - s / (j + 1 : ℝ) < t) :
    lowerContentLimit shift (fun y ↦ -s * potential y) .centered (component j) t
      (dyadicRadius p) = 0 := by
  have hcut (N : ℕ) : lowerContent shift (fun y ↦ -s * potential y) .centered (component j) t
      (dyadicRadius p) N = 0 := by
    apply le_antisymm _ bot_le
    have hbound : ∀ᶠ (n : ℕ) in atTop,
        lowerContent shift (fun y ↦ -s * potential y) .centered (component j) t
          (dyadicRadius p) N ≤ (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ) - t) * n + p) := by
      filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
      obtain ⟨F, hcov, hcost⟩ :=
        exists_finset_partitionCoverCost_le j n p ((le_max_left 1 N).trans hn) s
      calc
        _ ≤ (2 : ℝ≥0∞) ^ (-t * n) * partitionCoverCost shift (fun y ↦ -s * potential y)
            .centered (F : Set Space) n (dyadicRadius p) :=
          lowerContent_le_of_finset_cover s t p n N hn _ F hcov
        _ ≤ (2 : ℝ≥0∞) ^ (-t * n) * (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ)) * n + p) := by
          gcongr
        _ = _ := by
          rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
          congr 1
          ring
    have hneg : 1 - s / (j + 1 : ℝ) - t < 0 := sub_neg.mpr ht
    have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hexp : Tendsto (fun n : ℕ ↦ (1 - s / (j + 1 : ℝ) - t) * n + p) atTop atBot :=
      tendsto_atBot_add_const_right _ (p : ℝ) (hnat.const_mul_atTop_of_neg hneg)
    exact ge_of_tendsto
      ((ENNReal.tendsto_rpow_atBot_of_one_lt_base (by norm_num : (1 : ℝ≥0∞) < 2)).comp hexp)
      hbound
  exact iSup_eq_bot.mpr fun N ↦ iSup_eq_bot.mpr fun _ ↦ hcut N

/-- Bernoulli cylinder masses give a positive lower bound for variable-order content
at and below the component rate, for every dyadic radius. -/
private theorem one_le_lowerContentLimit_component (j p : ℕ) (s t : ℝ)
    (ht : t ≤ 1 - s / (j + 1 : ℝ)) :
    1 ≤ lowerContentLimit shift (fun y ↦ -s * potential y) .centered (component j) t
      (dyadicRadius p) := by
  have hcut : 1 ≤ lowerContent shift (fun y ↦ -s * potential y) .centered (component j) t
      (dyadicRadius p) 1 := by
    refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
    have hcov : (Set.univ : Set (ℕ → Bool)) ⊆ ⋃ i : C.index,
        {a : ℕ → Bool | (j, a) ∈ bowenBall shift (C.order i) (C.center i) (dyadicRadius p)} := by
      intro a _
      simpa using hC.2 (show (j, a) ∈ component j from rfl)
    have hmass : 1 ≤ ∑' i : C.index, uniformMeasure
        {a : ℕ → Bool | (j, a) ∈ bowenBall shift (C.order i) (C.center i) (dyadicRadius p)} := by
      calc
        1 = uniformMeasure Set.univ := by simp
        _ ≤ uniformMeasure (⋃ i : C.index,
            {a : ℕ → Bool | (j, a) ∈
              bowenBall shift (C.order i) (C.center i) (dyadicRadius p)}) :=
          MeasureTheory.measure_mono hcov
        _ ≤ _ := MeasureTheory.measure_iUnion_le _
    apply hmass.trans
    apply ENNReal.tsum_le_tsum
    intro i
    have hn : 1 ≤ C.order i := by simpa using hC.1 i
    rw [uniformMeasure_bowenBall_slice j (C.order i) p hn]
    change (if (C.center i).1 = j then (2 : ℝ≥0∞)⁻¹ ^ (C.order i + p) else 0) ≤
      (2 : ℝ≥0∞) ^ (-t * C.order i) * pressureBallWeight shift
        (fun y ↦ -s * potential y) .centered (C.order i) (C.center i) (dyadicRadius p)
    by_cases hi : (C.center i).1 = j
    · rw [ite_eq_left hi, pressureBallWeight, birkhoffSum_shift_potential, hi,
        inv_pow_eq_rpow_neg, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      have htn : (t + s / (j + 1 : ℝ)) * (C.order i : ℝ) ≤ C.order i := by
        nlinarith [mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (C.order i))]
      push_cast
      nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
    · rw [ite_eq_right hi]
      exact bot_le
  exact hcut.trans (le_iSup_of_le 1 (le_iSup_of_le le_rfl le_rfl))

/-- Equal-order binary cylinder covers bound the upper capacity of one entire component. -/
private theorem upperCapacity_component_le (j p : ℕ) (s : ℝ) :
    upperCapacity shift (fun y ↦ -s * potential y) .centered (component j) (dyadicRadius p) ≤
      ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) := by
  have hrate : ∀ᶠ n in atTop,
      pressureRate (fun n ↦ partitionSum shift (fun y ↦ -s * potential y) .centered
        (component j) n (dyadicRadius p)) n ≤
      pressureRate (fun n ↦ (1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ)) * n + p)) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply pressureRate_le_of_le
    simpa only [one_mul] using partitionSum_component_le j n p hn s
  exact (limsup_le_limsup hrate).trans_eq
    (tendsto_pressureRate_mul_two_rpow 1 (by norm_num) (by norm_num)
      (1 - s / (j + 1 : ℝ)) p).limsup_eq

/-- Any subset whose slice in component `j` has positive Bernoulli outer measure has
upper capacity at least the component rate. No measurability is assumed for the subset. -/
private theorem le_upperCapacity_of_measure_pos (j p : ℕ) (s : ℝ) (Z : Set Space)
    (hZ : 0 < uniformMeasure {a : ℕ → Bool | (j, a) ∈ Z}) :
    ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) ≤
      upperCapacity shift (fun y ↦ -s * potential y) .centered Z (dyadicRadius p) := by
  have hpart (n : ℕ) (hn : 1 ≤ n) :
      uniformMeasure {a : ℕ → Bool | (j, a) ∈ Z} *
        (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ)) * n + p) ≤
      partitionSum shift (fun y ↦ -s * potential y) .centered Z n (dyadicRadius p) := by
    refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
    let _ : Countable F := hF.1.to_subtype
    have hcov : {a : ℕ → Bool | (j, a) ∈ Z} ⊆ ⋃ y : F,
        {a : ℕ → Bool | (j, a) ∈ bowenBall shift n y (dyadicRadius p)} := by
      intro a ha
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF.2 ha)
      obtain ⟨hy, hya⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hya⟩
    have hmass : uniformMeasure {a : ℕ → Bool | (j, a) ∈ Z} ≤
        ∑' y : F, uniformMeasure
          {a : ℕ → Bool | (j, a) ∈ bowenBall shift n y (dyadicRadius p)} :=
      (MeasureTheory.measure_mono hcov).trans (MeasureTheory.measure_iUnion_le _)
    apply (mul_le_mul_of_nonneg_right hmass bot_le).trans
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro y
    rw [uniformMeasure_bowenBall_slice j n p hn]
    by_cases hy : y.1.1 = j
    · rw [ite_eq_left hy, inv_pow_eq_rpow_neg, pressureBallWeight, birkhoffSum_shift_potential,
        hy, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      apply le_of_eq
      congr 1
      push_cast
      ring
    · rw [ite_eq_right hy, zero_mul]
      exact bot_le
  have hrate : ∀ᶠ n in atTop,
      pressureRate (fun n ↦ uniformMeasure {a : ℕ → Bool | (j, a) ∈ Z} *
        (2 : ℝ≥0∞) ^ ((1 - s / (j + 1 : ℝ)) * n + p)) n ≤
      pressureRate (fun n ↦ partitionSum shift (fun y ↦ -s * potential y) .centered
        Z n (dyadicRadius p)) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pressureRate_le_of_le _ _ n (hpart n hn)
  exact (tendsto_pressureRate_mul_two_rpow (uniformMeasure {a : ℕ → Bool | (j, a) ∈ Z})
    hZ.ne' (MeasureTheory.measure_ne_top _ _) (1 - s / (j + 1 : ℝ)) p).limsup_eq.symm.le.trans
      (limsup_le_limsup hrate)

/-- Both the lower pressure and the modified upper pressure of the `j`-th component equal
`1 - s / (j + 1)`: the covering estimates identify lower pressure, and positive Bernoulli outer
measure in some member of every countable cover identifies modified upper pressure. -/
private theorem pressure_component (j : ℕ) (s : ℝ) (σ : LimitSide) :
    σ.choose
      (lowerPressure shift (fun y ↦ -s * potential y) 0 (component j),
      upperPressure shift (fun y ↦ -s * potential y) 0 (component j)) =
      ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) := by
  have hlower (p : ℕ) :
      lowerPressureAt shift (fun y ↦ -s * potential y) .centered (component j)
        (dyadicRadius p) = ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) := by
    apply le_antisymm
    · apply EReal.le_of_forall_lt_iff_le.mp
      intro t ht
      exact iInf_le_of_le t (iInf_le_of_le
        (lowerContentLimit_component_eq_zero j p s t (EReal.coe_lt_coe_iff.mp ht)) le_rfl)
    · refine le_iInf fun t ↦ le_iInf fun ht ↦ ?_
      apply EReal.coe_le_coe_iff.mpr
      by_contra h
      have hmass := one_le_lowerContentLimit_component j p s t (not_le.mp h).le
      rw [ht] at hmass
      exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hmass
  have hupper (p : ℕ) :
      modifiedUpperPressure shift (fun y ↦ -s * potential y) .centered (component j)
        (dyadicRadius p) = ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) := by
    apply le_antisymm
    · apply iInf_le_of_le (fun _ ↦ component j)
      apply iInf_le_of_le (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨0, hx⟩)
      simpa using upperCapacity_component_le j p s
    · refine le_iInf fun Y ↦ le_iInf fun hY ↦ ?_
      have hcov : (Set.univ : Set (ℕ → Bool)) ⊆ ⋃ k, {a : ℕ → Bool | (j, a) ∈ Y k} := by
        intro a _
        have ha := hY (show (j, a) ∈ component j from rfl)
        simpa using ha
      have hpos : ∃ k, 0 < uniformMeasure {a : ℕ → Bool | (j, a) ∈ Y k} := by
        by_contra h
        push Not at h
        have hz : uniformMeasure (⋃ k, {a : ℕ → Bool | (j, a) ∈ Y k}) = 0 :=
          le_antisymm ((MeasureTheory.measure_iUnion_le _).trans
            (by simp only [le_zero_iff.mp (h _), tsum_zero]; exact le_rfl)) bot_le
        have := (MeasureTheory.measure_mono hcov).trans_eq hz
        simp at this
      obtain ⟨k, hk⟩ := hpos
      exact le_iSup_of_le k (le_upperCapacity_of_measure_pos j p s (Y k) hk)
  cases σ with
  | lower => simp only [LimitSide.choose, lowerPressure, hlower, Nat.zero_le, iSup_pos, iSup_const]
  | upper => simp only [LimitSide.choose, upperPressure, hupper, Nat.zero_le, iSup_pos, iSup_const]

/-- Lower and upper pressure are monotone with respect to inclusion of sets. -/
private theorem pressure_mono {Y : Type*} [MetricSpace Y] (D : PressureData Y) (σ : LimitSide)
    (Z W : Set Y) (hZW : Z ⊆ W) :
    σ.choose (lowerPressure D.T D.φ D.p₀ Z, upperPressure D.T D.φ D.p₀ Z) ≤
      σ.choose (lowerPressure D.T D.φ D.p₀ W, upperPressure D.T D.φ D.p₀ W) := by
  cases σ with
  | lower =>
    change lowerPressure D.T D.φ D.p₀ Z ≤ lowerPressure D.T D.φ D.p₀ W
    rw [lowerPressure_pointToSet D Z, lowerPressure_pointToSet D W]
    exact iInf_mono fun A ↦ iSup_le fun x ↦ iSup_le fun hx ↦
      le_iSup_of_le x (le_iSup_of_le (hZW hx) le_rfl)
  | upper =>
    change upperPressure D.T D.φ D.p₀ Z ≤ upperPressure D.T D.φ D.p₀ W
    rw [upperPressure_pointToSet D Z, upperPressure_pointToSet D W]
    exact iInf_mono fun A ↦ iSup_le fun x ↦ iSup_le fun hx ↦
      le_iSup_of_le x (le_iSup_of_le (hZW hx) le_rfl)

/-- Countable stability: the pressure of a countable union is the supremum of the pressures of
the pieces (empty pieces allowed).  It follows by joining the oracles that attain the pressure of
the pieces. -/
private theorem pressure_iUnion_eq_iSup {Y : Type*} [MetricSpace Y] (D : PressureData Y)
    (σ : LimitSide) (Z : ℕ → Set Y) :
    σ.choose (lowerPressure D.T D.φ D.p₀ (⋃ j, Z j),
      upperPressure D.T D.φ D.p₀ (⋃ j, Z j)) =
    ⨆ j, σ.choose (lowerPressure D.T D.φ D.p₀ (Z j), upperPressure D.T D.φ D.p₀ (Z j)) := by
  have hcones : ∀ j, ∃ B : Set ℕ, ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
      σ.choose (lowerPressure D.T D.φ D.p₀ (Z j), upperPressure D.T D.φ D.p₀ (Z j)) =
      ⨆ x ∈ Z j, σ.choose (pointwisePressure D.presentation D.T D.φ A x) := by
    intro j
    cases σ with
    | lower => exact lowerPressure_pointToSet_cone D (Z j)
    | upper => exact upperPressure_pointToSet_cone D (Z j)
  choose B hB using hcones
  let A := oracleCountableJoin B
  have hA (j : ℕ) := hB j A (oracle_joins_countable B j)
  have hall : σ.choose (lowerPressure D.T D.φ D.p₀ (⋃ j, Z j),
      upperPressure D.T D.φ D.p₀ (⋃ j, Z j)) ≤
      ⨆ x ∈ ⋃ j, Z j, σ.choose (pointwisePressure D.presentation D.T D.φ A x) := by
    cases σ with
    | lower => exact lowerPressure_pointToSet_all_oracles D _ A
    | upper => exact upperPressure_pointToSet_all_oracles D _ A
  apply le_antisymm
  · apply hall.trans
    refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    apply le_iSup_of_le j
    rw [hA j]
    exact le_iSup_of_le x (le_iSup_of_le hj le_rfl)
  · refine iSup_le fun j ↦ ?_
    exact pressure_mono D σ _ _ (Set.subset_iUnion Z j)

/-- The pressure data of the concrete union at the slope `s`, with dyadic radii. -/
private noncomputable def pressureData (s : ℝ) : PressureData Space where
  presentation := presentation
  T := shift
  continuous_T := continuous_shift
  φ := fun y ↦ -s * potential y
  uniformContinuous_φ := uniformContinuous_potential.const_smul (-s)
  p₀ := 0
  ω := dyadicRadius
  ω_pos := fun p _ ↦ by unfold dyadicRadius; positivity
  ω_tendsto := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  oscillation := by
    intro p _ x y hxy
    have hr : dyadicRadius p ≤ 1 := by
      unfold dyadicRadius
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have h : x.1 = y.1 := eq_of_dist_lt_one ((lt_of_le_of_lt (le_max_left _ _) hxy).trans_le hr)
    simp only [potential, h, sub_self, abs_zero]
    unfold dyadicRadius
    positivity

/-- The supremum of the component rates `1 - s / (j + 1)` is one for every nonnegative `s`. -/
private theorem iSup_one_sub_div_eq_one (s : ℝ) (hs : 0 ≤ s) :
    (⨆ j : ℕ, ((1 - s / (j + 1 : ℝ) : ℝ) : EReal)) = 1 := by
  have hlim : Tendsto (fun j : ℕ ↦ (1 - s / (j + 1 : ℝ) : ℝ)) atTop (𝓝 1) := by
    have hdiv := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul s
    simpa only [mul_zero, sub_zero, mul_one_div] using tendsto_const_nhds.sub hdiv
  apply le_antisymm
  · refine iSup_le fun j ↦ ?_
    exact EReal.coe_le_coe_iff.mpr (sub_le_self _ (div_nonneg hs (by positivity)))
  · exact le_of_tendsto (continuous_coe_real_ereal.tendsto 1 |>.comp hlim)
      (Eventually.of_forall fun j ↦ le_iSup _ j)

/-- The pressure of the whole union is the supremum of the pressures of its components. -/
private theorem pressure_univ_eq_iSup (σ : LimitSide) (s : ℝ) :
    σ.choose
      (lowerPressure shift (fun y ↦ -s * potential y) 0 Set.univ,
      upperPressure shift (fun y ↦ -s * potential y) 0 Set.univ) =
      ⨆ j : ℕ, ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) := by
  have hcov : (⋃ j, component j) = Set.univ := by
    ext x
    simp [component]
  have h := pressure_iUnion_eq_iSup (pressureData s) σ component
  change σ.choose
    (lowerPressure shift (fun y ↦ -s * potential y) 0 (⋃ j, component j),
    upperPressure shift (fun y ↦ -s * potential y) 0 (⋃ j, component j)) = _ at h
  rw [hcov] at h
  rw [h]
  exact iSup_congr fun j ↦ pressure_component j s σ

end NonuniformCounterexample

open NonuniformCounterexample in
/-- A complete separable nonempty system has positive averages at most one, both entropies
equal to one, infinite BS dimensions, and no real pressure zero. The witness in the
blueprint is the separated union of binary shifts with potential `1 / j` on component `j`.
Blueprint node `bs:counterexample-existence`. -/
theorem counterexampleNonuniformBowenExistence :
    ∃ (Y : Type) (_m : MetricSpace Y) (P : Presentation Y) (T : Y → Y) (u : Y → ℝ),
      Continuous T ∧ UniformContinuous u ∧
      (∀ x, 0 < lowerBirkhoffAverage T u x ∧ upperBirkhoffAverage T u x ≤ (1 : EReal)) ∧
      ∀ σ : LimitSide,
        σ.choose (lowerEntropy T Set.univ, upperEntropy P T Set.univ) = 1 ∧
        σ.choose (lowerBSDimension T u Set.univ, upperBSDimension T u Set.univ) = ⊤ ∧
        (∀ s : ℝ, 0 ≤ s →
          σ.choose (lowerPressure T (fun y => -s * u y) 0 Set.univ,
            upperPressure T (fun y => -s * u y) 0 Set.univ) = 1) ∧
        ∀ s : ℝ, σ.choose (lowerPressure T (fun y => -s * u y) 0 Set.univ,
          upperPressure T (fun y => -s * u y) 0 Set.univ) ≠ 0 := by
  let _ := spaceMetric
  have havg (x : Space) : 0 < lowerBirkhoffAverage shift potential x ∧
      upperBirkhoffAverage shift potential x ≤ 1 := by
    rw [(birkhoffAverage_potential x).1, (birkhoffAverage_potential x).2]
    refine ⟨EReal.coe_pos.mpr (by positivity), EReal.coe_le_coe_iff.mpr ?_⟩
    exact (div_le_one (by positivity : (0 : ℝ) < x.1 + 1)).mpr (by simp)
  refine ⟨Space, spaceMetric, presentation, shift, potential, continuous_shift,
    uniformContinuous_potential, havg, ?_⟩
  intro σ
  let f : ℝ → EReal := fun s ↦ σ.choose
    (lowerPressure shift (fun y ↦ -s * potential y) 0 Set.univ,
    upperPressure shift (fun y ↦ -s * potential y) 0 Set.univ)
  have hf (s : ℝ) : f s = ⨆ j : ℕ, ((1 - s / (j + 1 : ℝ) : ℝ) : EReal) :=
    pressure_univ_eq_iSup σ s
  have hnonneg (s : ℝ) (hs : 0 ≤ s) : f s = 1 := (hf s).trans (iSup_one_sub_div_eq_one s hs)
  have hne : (Set.univ : Set Space).Nonempty := ⟨(0, fun _ ↦ false), Set.mem_univ _⟩
  have hentropy : σ.choose (lowerEntropy shift Set.univ,
      upperEntropy presentation shift Set.univ) = 1 := by
    apply EReal.coe_ennreal_strictMono.injective
    have hzero : ((σ.choose (lowerEntropy shift Set.univ,
        upperEntropy presentation shift Set.univ) : ℝ≥0∞) : EReal) = f 0 := by
      cases σ with
      | lower =>
        simpa only [f, LimitSide.choose, neg_zero, zero_mul] using
          entropy_eq_zeroPotentialPressure_of_nonempty presentation shift continuous_shift
            Set.univ hne
      | upper =>
        simpa only [f, LimitSide.choose, neg_zero, zero_mul] using
          entropy_eq_zeroPotentialPressure_of_nonempty_upper presentation shift continuous_shift
            Set.univ hne
    exact hzero.trans (hnonneg 0 le_rfl)
  have hdim : σ.choose (lowerBSDimension shift potential Set.univ,
      upperBSDimension shift potential Set.univ) = ⊤ := by
    rw [setBowenCriticalValue_nonpositive presentation shift continuous_shift potential
      uniformContinuous_potential Set.univ
      (fun x _ ↦ ⟨(havg x).1, (havg x).2.trans_lt (EReal.coe_lt_top 1)⟩) σ]
    apply top_unique
    change ⊤ ≤ nonpositivePressureThreshold f
    unfold nonpositivePressureThreshold
    refine le_iInf fun s ↦ le_iInf fun hs ↦ le_iInf fun hle ↦ ?_
    have h : f s ≤ 0 := hle
    rw [hnonneg s hs] at h
    exact ((not_le_of_gt (EReal.coe_pos.mpr (show (0 : ℝ) < 1 by norm_num))) h).elim
  refine ⟨hentropy, hdim, hnonneg, ?_⟩
  intro s
  change f s ≠ 0
  by_cases hs : 0 ≤ s
  · rw [hnonneg s hs]
    norm_num
  · have hbound : ((1 - s : ℝ) : EReal) ≤ f s := by
      rw [hf s]
      simpa using le_iSup (fun j : ℕ ↦ ((1 - s / (j + 1 : ℝ) : ℝ) : EReal)) 0
    exact ((EReal.coe_pos.mpr (by linarith : 0 < 1 - s)).trans_le hbound).ne'

end Kolmogorov.PointToSet
