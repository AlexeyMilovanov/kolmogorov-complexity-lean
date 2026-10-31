/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Upper.ScaleLimits

/-!
# Uniform nets for upper Barreira–Schmeling dimension

For a continuous map on a presented metric space and a uniformly continuous potential
with positive lower Birkhoff average on a set, every exponent above its modified upper
BS dimension admits a uniform net. Positive-average exhaustion and recentering of cheap
covers give the classical characterization in blueprint node `bs:net-construction`.

For an admissible oracle, strict complexity thresholds yield enumerable nets whose slice
masses are bounded by the Kraft inequality. This proves the effective upper bound in
`bs:effective-upper-upper`, alongside the classical lower bound from `bs:effective`.
The oracle-attainment and point-to-set modules use these bounds to identify the minimum
effective upper dimension with the classical one.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- A strict upper dimension bound gives a countable cover whose capacities at any fixed
dyadic radius lie below the same exponent. -/
private lemma exists_cover_upperBSCapacityAt_lt
    (T : X → X) (u : X → ℝ) (Z : Set X) (s : ℝ)
    (hlt : upperBSDimension T u Z < ENNReal.ofReal s) (q : ℕ) :
    ∃ Y : ℕ → Set X, (∀ k, Y k ⊆ Z) ∧ Z ⊆ ⋃ k, Y k ∧
      ∀ k, upperBSCapacityAt T u (Y k) (dyadicRadius q) < ENNReal.ofReal s := by
  have hdim : modifiedUpperBSDimension T u Z (dyadicRadius q) < ENNReal.ofReal s :=
    (le_iSup (fun p ↦ modifiedUpperBSDimension T u Z (dyadicRadius p)) q).trans_lt hlt
  simp only [modifiedUpperBSDimension, iInf_lt_iff] at hdim
  obtain ⟨Y, hY, hcap⟩ := hdim
  exact ⟨Y, hY.1, hY.2, fun k ↦
    (le_iSup (fun k ↦ upperBSCapacityAt T u (Y k) (dyadicRadius q)) k).trans_lt hcap⟩

/-- On a uniform positive-average piece, an exponent above capacity has partition sums
tending to zero. -/
private lemma bsPartitionSum_tendsto_zero_of_capacity_lt
    (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z C : Set X)
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (ρ : ℚ) (hρ : 0 < ρ)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ) (s r : ℝ) (hr : 0 < r)
    (hcap : upperBSCapacityAt T u C r < ENNReal.ofReal s) :
    Tendsto (bsPartitionSum T u C s r) atTop (𝓝 0) := by
  simp only [upperBSCapacityAt, iInf_lt_iff] at hcap
  obtain ⟨t, ht, hfinite, hts⟩ := hcap
  have htsReal : t < s := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp hts
  exact upperCapacityPositiveRefinement_tendsto P T hT u hu Z C
    N₀ hN₀ ρ hρ hC t s r ht htsReal hr hfinite

/-- A cover with finite Birkhoff suprema can be recentered at ideal points. Doubling the
radius preserves coverage, and the center-weight mass increases by at most `2 ^ s`. -/
private lemma exists_ideal_cover_mass_le
    (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (r : ℝ) (p : ℕ)
    (hscale : 2 * r ≤ dyadicRadius p) (F : Set X)
    (hfinite : ∀ y ∈ F, ∃ w : ℝ, bowenPotentialSup T u n y r = (w : EReal)) :
    ∃ J : Set ℕ,
      (⋃ y ∈ F, bowenBall T n y r) ⊆
        ⋃ i ∈ J, bowenBall T n (P.ι i) (dyadicRadius p) ∧
      (∑' i : J, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι i))) ≤
        (2 : ℝ≥0∞) ^ s * bsPartitionCoverCost T u s r n F := by
  classical
  have hf : ∀ y : F, ∃ w : ℝ,
      bowenPotentialSup T u n y.val r = (w : EReal) := fun y ↦ hfinite y.val y.property
  choose w hw using hf
  have hcenters : ∀ y : F, ∃ i : ℕ,
      w y - 1 < birkhoffSum T u n (P.ι i) ∧
      bowenBall T n y.val r ⊆ bowenBall T n (P.ι i) (2 * r) := by
    intro y
    have hcont : Continuous (fun z ↦ birkhoffSum T u n z) :=
      continuous_finsetSum (Finset.range n) (fun k _ ↦ hu.continuous.comp (hT.iterate k))
    have hopen : IsOpen (bowenBall T n y.val r ∩
        {z : X | w y - 1 < birkhoffSum T u n z}) :=
      (bowen_ball_dense_open T hT n y.val r).inter (isOpen_lt continuous_const hcont)
    have hnonempty : (bowenBall T n y.val r ∩
        {z : X | w y - 1 < birkhoffSum T u n z}).Nonempty := by
      have hlt : ((w y - 1 : ℝ) : EReal) < bowenPotentialSup T u n y.val r := by
        rw [hw y]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      simp only [bowenPotentialSup, lt_iSup_iff] at hlt
      obtain ⟨z, hz, hval⟩ := hlt
      exact ⟨z, hz, EReal.coe_lt_coe_iff.mp hval⟩
    obtain ⟨i, hiball, hival⟩ := P.dense.exists_mem_open hopen hnonempty
    refine ⟨i, hival, ?_⟩
    intro x hx
    dsimp [bowenBall] at hiball hx ⊢
    rw [Dynamics.mem_dynEntourage] at hiball hx ⊢
    intro k hk
    have hi' : dist (T^[k] (P.ι i)) (T^[k] y.val) < r := by
      simpa only [Set.mem_ofPred_eq, dist_comm] using hiball k hk
    exact (dist_triangle (T^[k] (P.ι i)) (T^[k] y.val) (T^[k] x)).trans_lt
      (by simpa only [two_mul] using add_lt_add hi' (hx k hk))
  choose i hi hsub using hcenters
  refine ⟨Set.range i, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨i ⟨y, hy⟩, Set.mem_range_self _, ?_⟩
    exact bowenBall_subset_of_le T n _ hscale (hsub ⟨y, hy⟩ hxy)
  · calc
      (∑' j : Set.range i, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι j))) ≤
          ∑' y : F, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι (i y))) := by
        exact ENNReal.tsum_le_tsum_comp_of_surjective
          (f := fun y ↦ (⟨i y, Set.mem_range_self y⟩ : Set.range i))
          (by rintro ⟨j, y, rfl⟩; exact ⟨y, rfl⟩) _
      _ ≤ ∑' y : F, (2 : ℝ≥0∞) ^ s * bsBallWeight T u s n y.val r := by
        apply ENNReal.tsum_le_tsum
        intro y
        rw [lowerBSMass_weight T u s n y.val r (w y) (hw y),
          ← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
        apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
        have := mul_le_mul_of_nonneg_left (hi y).le hs
        nlinarith
      _ = (2 : ℝ≥0∞) ^ s * bsPartitionCoverCost T u s r n F :=
        ENNReal.tsum_mul_left

/-- Countable covers at each scale with eventually bounded ideal-center masses assemble
into a uniform net. -/
private lemma exists_uniformBSNet_of_slices
    (P : Presentation X) (T : X → X) (u : X → ℝ) (Z : Set X) (s : ℝ)
    (C : ℕ → ℕ → Set X) (hC : ∀ p, Z ⊆ ⋃ k, C p k)
    (J : ℕ → ℕ → ℕ → Set ℕ)
    (hcover : ∀ p k n, 1 ≤ n →
      C p k ⊆ ⋃ i ∈ J p k n, bowenBall T n (P.ι i) (dyadicRadius p))
    (hmass : ∀ p k, ∀ᶠ n in atTop, (∑' i : J p k n,
      (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι i))) ≤ (2 : ℝ≥0∞) ^ s) :
    ∃ E : Set (ℕ × ℕ × ℕ × ℕ), IsUniformBSNet P T u Z s E := by
  let E : Set (ℕ × ℕ × ℕ × ℕ) :=
    {e | e.1 ∈ J e.2.2.1 e.2.2.2 e.2.1}
  have hsum (n p k : ℕ) : uniformBSSum P T u s E n p k =
      ∑' i : J p k n, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι i)) := by
    change (∑' i : J p k n,
      (2 : ℝ≥0∞) ^ birkhoffSum T (fun y ↦ -s * u y) n (P.ι i)) = _
    simp only [birkhoffSum, Finset.mul_sum]
  refine ⟨E, ?_, ?_⟩
  · intro p k
    have hbound : ∀ᶠ n in atTop,
        uniformBSSum P T u s E n p k ≤ (2 : ℝ≥0∞) ^ s := by
      simpa only [hsum] using hmass p k
    exact (limsup_le_of_le (h := hbound)).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)))
  · intro p x hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (hC p hx)
    refine ⟨k, ?_⟩
    intro n hn
    have hxcover := hcover p k n hn hxk
    simp only [Set.mem_iUnion] at hxcover
    obtain ⟨i, hi, hball⟩ := hxcover
    exact ⟨i, hi, hball⟩

/-- Every finite exponent above modified upper dimension has a classical uniform net.
Blueprint node `bs:net-construction`. -/
theorem upperBSUniformNetCharacterization (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s : ℝ) (hs : 0 ≤ s)
    (hlt : upperBSDimension T u Z < ENNReal.ofReal s) :
    ∃ E : Set (ℕ × ℕ × ℕ × ℕ), IsUniformBSNet P T u Z s E := by
  classical
  choose q hscale hfinite using exists_dyadicRadius_double_le_finite_bowenPotentialSup T u hu
  have hpieces : ∀ p : ℕ, ∃ C : ℕ → Set X, Z ⊆ ⋃ k, C k ∧
      ∀ k, Tendsto (bsPartitionSum T u (C k) s (dyadicRadius (q p))) atTop (𝓝 0) := by
    intro p
    obtain ⟨Y, _, hY, hcap⟩ :=
      exists_cover_upperBSCapacityAt_lt T u Z s hlt (q p)
    let I := ℕ × {N : ℕ // 1 ≤ N} × {ρ : ℚ // 0 < ρ}
    have hI : Nonempty I := ⟨⟨0, ⟨1, le_rfl⟩, ⟨1, by norm_num⟩⟩⟩
    obtain ⟨e, he⟩ := @exists_surjective_nat I hI inferInstance
    let C : ℕ → Set X := fun j ↦ Y (e j).1 ∩
      positiveAveragePiece T u Z (e j).2.1.1 (e j).2.2.1
    refine ⟨C, ?_, ?_⟩
    · intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hY hx)
      have hx' := hx
      rw [positiveAverageExhaustion P T hT u hu Z hZ] at hx'
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨N, hN, ρ, hρ, hxpiece⟩ := hx'
      obtain ⟨j, hj⟩ := he ⟨k, ⟨N, hN⟩, ⟨ρ, hρ⟩⟩
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      dsimp [C]
      rw [hj]
      exact ⟨hk, hxpiece⟩
    · intro j
      apply bsPartitionSum_tendsto_zero_of_capacity_lt P T hT u hu Z (C j)
        (e j).2.1.1 (e j).2.1.2 (e j).2.2.1 (e j).2.2.2
        Set.inter_subset_right s (dyadicRadius (q p)) (by unfold dyadicRadius; positivity)
      exact (upperBSDimension_mono_capacity T u (dyadicRadius (q p))
        Set.inter_subset_left).trans_lt (hcap (e j).1)
  choose C hC hdecay using hpieces
  have hslices : ∀ p k : ℕ, ∃ J : ℕ → Set ℕ,
      (∀ n ≥ 1, C p k ⊆ ⋃ i ∈ J n, bowenBall T n (P.ι i) (dyadicRadius p)) ∧
      ∀ᶠ n in atTop, (∑' i : J n,
        (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι i))) ≤ (2 : ℝ≥0∞) ^ s := by
    intro p k
    have hlocal : ∀ n : ℕ, ∃ J : Set ℕ,
        (1 ≤ n → (C p k) ⊆ ⋃ i ∈ J, bowenBall T n (P.ι i) (dyadicRadius p)) ∧
        (1 ≤ n ∧ bsPartitionSum T u (C p k) s (dyadicRadius (q p)) n < 1 →
          (∑' i : J, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n (P.ι i))) ≤
            (2 : ℝ≥0∞) ^ s) := by
      intro n
      by_cases hn : 1 ≤ n
      · by_cases hsmall : bsPartitionSum T u (C p k) s (dyadicRadius (q p)) n < 1
        · have hsmall' := hsmall
          simp only [bsPartitionSum, iInf_lt_iff] at hsmall'
          obtain ⟨F, hF, hcost⟩ := hsmall'
          obtain ⟨J, hcover, hmass⟩ := exists_ideal_cover_mass_le
            P T hT u hu s hs n (dyadicRadius (q p)) p (hscale p) F (fun y _ ↦ (hfinite p) n y)
          refine ⟨J, fun _ ↦ hF.2.trans hcover, fun _ ↦ ?_⟩
          calc
            _ ≤ (2 : ℝ≥0∞) ^ s * bsPartitionCoverCost T u s (dyadicRadius (q p)) n F := hmass
            _ ≤ (2 : ℝ≥0∞) ^ s * 1 := by gcongr
            _ = (2 : ℝ≥0∞) ^ s := mul_one _
        · refine ⟨Set.univ, ?_, fun h ↦ (hsmall h.2).elim⟩
          intro _ x _
          obtain ⟨i, hi⟩ := bowen_ball_dense P T hT x n hn (dyadicRadius p)
            (by unfold dyadicRadius; positivity)
          simp only [Set.mem_iUnion]
          refine ⟨i, Set.mem_univ _, ?_⟩
          dsimp [bowenBall] at hi ⊢
          rw [Dynamics.mem_dynEntourage] at hi ⊢
          intro k hk
          simpa only [Set.mem_ofPred_eq, dist_comm] using hi k hk
      · exact ⟨∅, fun hn' ↦ (hn hn').elim, fun h ↦ (hn h.1).elim⟩
    choose J hcover hmass using hlocal
    refine ⟨J, hcover, ?_⟩
    filter_upwards [eventually_ge_atTop 1, (tendsto_order.mp (hdecay p k)).2 1 zero_lt_one]
      with n hn hsmall
    exact hmass n ⟨hn, hsmall⟩
  choose J hcover hmass using hslices
  exact exists_uniformBSNet_of_slices P T u Z s C hC J hcover hmass

/-- Modified upper dimension is the nonnegative infimum of uniform-net exponents.
Blueprint node `bs:net-construction`. -/
theorem upperBSUniformNetCharacterization_iInf (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    upperBSDimension T u Z = ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
      ⨅ (_ : IsUniformBSNet P T u Z s E), ENNReal.ofReal s := by
  apply le_antisymm
  · apply le_iInf; intro s
    apply le_iInf; intro hs
    apply le_iInf; intro E
    apply le_iInf; intro hE
    exact uniformNetBoundsUpperBS P T hT u hu Z s hs E hE
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    by_cases hr_top : r = ⊤
    · exact hr_top ▸ le_top
    obtain ⟨E, hE⟩ := upperBSUniformNetCharacterization P T hT u hu Z hZ r.toReal
      ENNReal.toReal_nonneg (by rwa [ENNReal.ofReal_toReal hr_top])
    calc
      _ ≤ ENNReal.ofReal r.toReal := by
        apply iInf_le_of_le r.toReal
        apply iInf_le_of_le ENNReal.toReal_nonneg
        apply iInf_le_of_le E
        exact iInf_le_of_le hE le_rfl
      _ = r := ENNReal.ofReal_toReal hr_top

/-- The effective upper dimension bounds classical modified upper dimension.
Blueprint node `bs:effective`. -/
theorem effectiveBSDimensions_ge_upper (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    upperBSDimension T u Z ≤ effectiveUpperBSDimension P T u A Z := by
  obtain ⟨_, _, _⟩ := hA
  rw [upperBSUniformNetCharacterization_iInf P T hT u hu Z hZ]
  unfold effectiveUpperBSDimension
  apply iInf_mono
  intro s
  apply iInf_mono
  intro hs
  apply iInf_mono
  intro E
  apply iInf_mono'
  intro hE
  exact ⟨hE.1, le_rfl⟩

/-- Rational affine Birkhoff thresholds are uniformly lower semicomputable relative
to an admissible oracle, for coefficients of either sign. -/
private lemma lowerSemicomputable_birkhoff_threshold
    (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 ↦ u) A)
    (s : ℚ) :
    IsLowerSemicomputableIn A
      (fun e : ℕ × ℕ × ℕ × ℕ ↦
        (s : ℝ) * birkhoffSum T u e.2.1 (P.ι e.1) +
          (e.2.2.2 : ℝ)) := by
  have hv := birkhoff_computableIn P T (fun _ : Fin 1 ↦ u) A hA
  have hindex : Computable (fun e : ℕ × ℕ × ℕ × ℕ ↦
      ((0 : Fin 1), e.2.1, e.1)) :=
    (Computable.const (0 : Fin 1)).pair
      ((Computable.fst.comp Computable.snd).pair Computable.fst)
  have hk : Computable (fun eq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦
      (eq.1.2.2.2 : ℚ)) :=
    computable_nat_to_rat.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  let g : (ℕ × ℕ × ℕ × ℕ) × ℚ → (Fin 1 × ℕ × ℕ) × ℚ := fun eq ↦
    (((0 : Fin 1), eq.1.2.1, eq.1.1), (eq.2 - (eq.1.2.2.2 : ℚ)) * s⁻¹)
  have hg : Computable g :=
    (hindex.comp Computable.fst).pair
      (computable₂_ratMul.comp (computable₂_ratSub.comp Computable.snd hk)
        (Computable.const s⁻¹))
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hsR : (s : ℝ) < 0 := by exact_mod_cast hs
    obtain ⟨f, hf, hdom⟩ := birkhoff_computableIn_lt A _ hv
    refine ⟨fun eq ↦ f (g eq), hf.comp hg.computableIn, ?_⟩
    intro eq
    rw [← hdom]
    change (eq.2 : ℝ) < (s : ℝ) * birkhoffSum T u eq.1.2.1 (P.ι eq.1.1) +
        (eq.1.2.2.2 : ℝ) ↔
      birkhoffSum T u eq.1.2.1 (P.ι eq.1.1) <
        (((eq.2 - (eq.1.2.2.2 : ℚ)) * s⁻¹ : ℚ) : ℝ)
    rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_inv,
      ← div_eq_mul_inv, lt_div_iff_of_neg' hsR]
    exact (sub_lt_iff_lt_add).symm
  · have hc : Computable (fun eq : (ℕ × ℕ × ℕ × ℕ) × ℚ ↦
        decide (eq.2 < (eq.1.2.2.2 : ℚ))) :=
      computable₂_ratLt.comp Computable.snd hk
    refine ⟨fun eq ↦ cond (decide (eq.2 < (eq.1.2.2.2 : ℚ)))
      (Part.some 0) Part.none, ?_, ?_⟩
    · exact PartrecIn.cond hc.computableIn (ComputableIn.const (0 : ℕ)) PartrecIn.none
    · intro eq
      simp only [Rat.cast_zero, zero_mul, zero_add]
      have hcast : (eq.2 : ℝ) < (eq.1.2.2.2 : ℝ) ↔
          eq.2 < (eq.1.2.2.2 : ℚ) := by
        exact_mod_cast (Iff.rfl : eq.2 < (eq.1.2.2.2 : ℚ) ↔
          eq.2 < (eq.1.2.2.2 : ℚ))
      rw [hcast]
      by_cases h : eq.2 < (eq.1.2.2.2 : ℚ) <;> simp [h]
  · have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    obtain ⟨f, hf, hdom⟩ := birkhoff_computableIn_gt A _ hv
    refine ⟨fun eq ↦ f (g eq), hf.comp hg.computableIn, ?_⟩
    intro eq
    rw [← hdom]
    change (eq.2 : ℝ) < (s : ℝ) * birkhoffSum T u eq.1.2.1 (P.ι eq.1.1) +
        (eq.1.2.2.2 : ℝ) ↔
      (((eq.2 - (eq.1.2.2.2 : ℚ)) * s⁻¹ : ℚ) : ℝ) <
        birkhoffSum T u eq.1.2.1 (P.ι eq.1.1)
    rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_inv,
      ← div_eq_mul_inv, div_lt_iff₀' hsR]
    exact (sub_lt_iff_lt_add).symm

/-- Ideal indices whose oracle complexity is below a Birkhoff threshold with natural slack. -/
private def complexityNet (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (s : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {e | 1 ≤ e.2.1 ∧ (oracleNatComplexity A e.1 : ℝ) <
    s * birkhoffSum T u e.2.1 (P.ι e.1) + e.2.2.2}

/-- Strict Birkhoff thresholds on oracle complexity define a relatively enumerable net. -/
private lemma isREIn_complexityNet (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (hA : IsAdmissible P T (fun _ : Fin 1 ↦ u) A) (s : ℚ) :
    IsREIn A (complexityNet P T u A s) := by
  have h_dec : Computable (fun e : ℕ × ℕ × ℕ × ℕ ↦ decide (1 ≤ e.2.1)) :=
    Primrec.nat_le.decide.to_comp.comp (Computable.const 1) (Computable.fst.comp Computable.snd)
  have horder : IsREIn A (fun e : ℕ × ℕ × ℕ × ℕ ↦ 1 ≤ e.2.1) :=
    isREIn_of_computable_decide h_dec
  let F : (ℕ × ℕ × ℕ × ℕ) × ℚ → Prop :=
    fun eq ↦ (oracleNatComplexity A eq.1.1 : ℝ) < (eq.2 : ℝ)
  let G : (ℕ × ℕ × ℕ × ℕ) × ℚ → Prop := fun eq ↦
    (eq.2 : ℝ) < (s : ℝ) * birkhoffSum T u eq.1.2.1 (P.ι eq.1.1) + eq.1.2.2.2
  have hcomplexity : IsREIn A F := by
    let g : (ℕ × ℕ × ℕ × ℕ) × ℚ → ℕ × ℚ := fun eq ↦ (eq.1.1, eq.2)
    have hg : Computable g :=
      (Computable.fst.comp Computable.fst).pair Computable.snd
    exact (isREIn_oracleNatComplexity_lt A).comp (f := g) hg.computableIn
  have hthreshold : IsREIn A G := lowerSemicomputable_birkhoff_threshold P T u A hA s
  have hboth : IsREIn A (fun eq ↦ F eq ∧ G eq) := hcomplexity.and hthreshold
  obtain ⟨f, hf, hdom⟩ := IsREIn.exists (F := fun eq ↦ F eq ∧ G eq) hboth
  have hlt : IsREIn A (fun e : ℕ × ℕ × ℕ × ℕ ↦ (oracleNatComplexity A e.1 : ℝ) <
      (s : ℝ) * birkhoffSum T u e.2.1 (P.ι e.1) + e.2.2.2) := by
    refine ⟨f, hf, fun e ↦ ?_⟩
    rw [← hdom]
    exact ⟨exists_rat_btwn, fun ⟨_, h₁, h₂⟩ ↦ h₁.trans h₂⟩
  exact horder.and hlt

/-- The Kraft inequality bounds weights on any set of indices satisfying a complexity
threshold, with a factor `2 ^ k` for the slack. -/
private lemma tsum_rpow_neg_le_of_complexity_lt (A : Set ℕ) (v : ℕ → ℝ)
    (J : Set ℕ) (k : ℕ) (hJ : ∀ i ∈ J, (oracleNatComplexity A i : ℝ) < v i + k) :
    (∑' i : J, (2 : ℝ≥0∞) ^ (-v i)) ≤ (2 : ℝ≥0∞) ^ k := by
  calc
    _ ≤ ∑' i : J, (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hi := hJ i i.property
      calc
        _ ≤ (2 : ℝ≥0∞) ^ ((k : ℝ) - oracleNatComplexity A i) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by
          rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
            ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.rpow_natCast,
            ENNReal.inv_pow]
    _ ≤ ∑' i : ℕ, (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun i : ℕ ↦ (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i)
    _ = (2 : ℝ≥0∞) ^ k * ∑' i : ℕ,
        (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i := ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞) ^ k * 1 := mul_le_mul' le_rfl (oracle_kraft A)
    _ = _ := mul_one _

/-- An exponent above the upper pointwise dimension eventually bounds the costs at
every fixed dyadic scale. -/
private lemma eventually_finiteScaleBSCost_lt
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) (p : ℕ) (s : ℝ)
    (hdim : (pointwiseBSDimension P T u A x).2 < ENNReal.ofReal s) :
    ∀ᶠ n in atTop, finiteScaleBSCost P T u A x n (dyadicRadius p) < ENNReal.ofReal s := by
  dsimp [pointwiseBSDimension] at hdim
  have hlimsup := lt_of_le_of_lt (le_iSup _ p) hdim
  exact eventually_lt_of_limsup_lt (hu := isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩) hlimsup

/-- A strict finite-scale cost bound supplies a realizer with zero complexity slack. -/
private lemma exists_complexityNet_realizer_of_cost_lt
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X)
    (s : ℝ) (p n : ℕ) (hn : 1 ≤ n)
    (hcost : finiteScaleBSCost P T u A x n (dyadicRadius p) < ENNReal.ofReal s) :
    ∃ i, (i, n, p, 0) ∈ complexityNet P T u A s ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  have hn0 : n ≠ 0 := by omega
  simp only [finiteScaleBSCost, ite_eq_right hn0, iInf_lt_iff] at hcost
  obtain ⟨i, hball, hsum, hcost⟩ := hcost
  have hs : 0 < s := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hcost)
  have hsum0 : ENNReal.ofReal (birkhoffSum T u n (P.ι i)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hsum)
  have hK := (ENNReal.div_lt_iff (Or.inl hsum0) (Or.inl ENNReal.ofReal_ne_top)).mp hcost
  rw [← ENNReal.ofReal_mul hs.le, ENNReal.natCast_lt_ofReal] at hK
  refine ⟨i, ⟨hn, ?_⟩, ?_⟩
  · simpa only [Nat.cast_zero, add_zero] using hK
  · exact mem_bowenBall_iff.mpr fun j hj ↦ by
      simpa only [dist_comm] using mem_bowenBall_iff.mp hball j hj

/-- A finite prefix with arbitrary complexity slacks and a tail with zero slack admit a
common slack for all positive orders. -/
private lemma exists_uniform_complexity_slack
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (x : X) (s : ℝ) (p N : ℕ)
    (htail : ∀ n ≥ max 1 N, ∃ i, (i, n, p, 0) ∈ complexityNet P T u A s ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p))
    (hprefix : ∀ n, 1 ≤ n → n < max 1 N → ∃ i k,
      (i, n, p, k) ∈ complexityNet P T u A s ∧
        x ∈ bowenBall T n (P.ι i) (dyadicRadius p)) :
    ∃ k, ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ complexityNet P T u A s ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  classical
  choose i k hk using hprefix
  let slack : ℕ → ℕ := fun n ↦ if h : 1 ≤ n ∧ n < max 1 N then k n h.1 h.2 else 0
  let K := Finset.sup (Finset.Ico 1 (max 1 N)) slack
  refine ⟨K, fun n hn ↦ ?_⟩
  by_cases hnN : max 1 N ≤ n
  · obtain ⟨j, hj, hball⟩ := htail n hnN
    refine ⟨j, ⟨hj.1, hj.2.trans_le ?_⟩, hball⟩
    exact add_le_add_right (Nat.cast_le.mpr (Nat.zero_le K)) _
  · have hnN' : n < max 1 N := lt_of_not_ge hnN
    obtain ⟨hmem, hball⟩ := hk n hn hnN'
    have hle : k n hn hnN' ≤ K := by
      have hsup := Finset.le_sup (f := slack) (Finset.mem_Ico.mpr ⟨hn, hnN'⟩)
      simpa only [slack, hn, hnN', and_self, dite_true] using hsup
    refine ⟨i n hn hnN', ⟨hmem.1, hmem.2.trans_le ?_⟩, hball⟩
    exact add_le_add_right (Nat.cast_le.mpr hle) _

/-- Above the upper pointwise dimension, a single complexity slack covers a point at
every positive order of a fixed scale. -/
private lemma complexityNet_covers_of_dimension_lt
    (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ) (A : Set ℕ)
    (s : ℝ) (x : X) (p : ℕ)
    (hdim : (pointwiseBSDimension P T u A x).2 < ENNReal.ofReal s) :
    ∃ k, ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ complexityNet P T u A s ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_finiteScaleBSCost_lt P T u A x p s hdim)
  apply exists_uniform_complexity_slack P T u A x s p N
  · intro n hn
    exact exists_complexityNet_realizer_of_cost_lt P T u A x s p n
      ((le_max_left 1 N).trans hn) (hN n ((le_max_right 1 N).trans hn))
  · intro n hn _
    obtain ⟨i, hi⟩ := bowen_ball_dense P T hT x n hn (dyadicRadius p)
      (by unfold dyadicRadius; positivity)
    obtain ⟨k, hk⟩ := exists_nat_gt
      ((oracleNatComplexity A i : ℝ) - s * birkhoffSum T u n (P.ι i))
    refine ⟨i, k, ⟨hn, by linarith⟩, ?_⟩
    exact mem_bowenBall_iff.mpr fun j hj ↦ by
      simpa only [dist_comm] using mem_bowenBall_iff.mp hi j hj

/-- A complexity-threshold net satisfying the covering condition is a uniform BS net
by the Kraft inequality. -/
private lemma isUniformBSNet_complexityNet
    (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ) (Z : Set X) (s : ℝ)
    (hcover : ∀ x ∈ Z, ∀ p, ∃ k, ∀ n ≥ 1, ∃ i,
      (i, n, p, k) ∈ complexityNet P T u A s ∧
        x ∈ bowenBall T n (P.ι i) (dyadicRadius p)) :
    IsUniformBSNet P T u Z s (complexityNet P T u A s) := by
  refine ⟨?_, fun p x hx ↦ hcover x hx p⟩
  intro p k
  have hbound (n : ℕ) :
      uniformBSSum P T u s (complexityNet P T u A s) n p k ≤ (2 : ℝ≥0∞) ^ k := by
    unfold uniformBSSum uniformPressureSum
    have hsum (i : ℕ) : birkhoffSum T (fun y ↦ -s * u y) n (P.ι i) =
        -(s * birkhoffSum T u n (P.ι i)) := by
      calc
        _ = -s * birkhoffSum T u n (P.ι i) := by
          simp only [birkhoffSum, Finset.mul_sum]
        _ = _ := neg_mul _ _
    simp only [hsum]
    exact tsum_rpow_neg_le_of_complexity_lt A (fun i ↦ s * birkhoffSum T u n (P.ι i))
      {i : ℕ | (i, n, p, k) ∈ complexityNet P T u A s} k (fun _ hi ↦ hi.2)
  exact (limsup_le_of_le (h := Eventually.of_forall hbound)).trans_lt
    (ENNReal.pow_lt_top (by norm_num))

/-- The Kraft net construction bounds effective upper dimension by the pointwise supremum.
Blueprint node `bs:effective-upper-upper`. -/
theorem effectiveUpperBSLeSup (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (A : Set ℕ)
    (hA : IsAdmissible P T (fun _ : Fin 1 => u) A) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    effectiveUpperBSDimension P T u A Z ≤ ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).2 := by
  -- These hypotheses are retained in the public interface; finite-scale costs already
  -- restrict to positive denominators.
  have _ := hu
  have _ := hZ
  let RHS := ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).2
  by_contra hcontra
  have hlt : RHS < effectiveUpperBSDimension P T u A Z := not_le.mp hcontra
  obtain ⟨q, hq, hq₁, hq₂⟩ :=
    ENNReal.lt_iff_exists_rat_btwn.mp hlt
  have hs : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hRE := isREIn_complexityNet P T u A hA q
  have hcover : ∀ x ∈ Z, ∀ p, ∃ k, ∀ n ≥ 1, ∃ i,
      (i, n, p, k) ∈ complexityNet P T u A q ∧
        x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
    intro x hx p
    have hdim : (pointwiseBSDimension P T u A x).2 < ENNReal.ofReal (q : ℝ) :=
      (le_iSup₂_of_le x hx le_rfl).trans_lt hq₁
    exact complexityNet_covers_of_dimension_lt P T hT u A q x p hdim
  have hnet := isUniformBSNet_complexityNet P T u A Z q hcover
  have hbound : effectiveUpperBSDimension P T u A Z ≤ ENNReal.ofReal (q : ℝ) := by
    unfold effectiveUpperBSDimension
    exact iInf_le_of_le (q : ℝ) (iInf_le_of_le hs
      (iInf_le_of_le (complexityNet P T u A q) (iInf_le_of_le ⟨hnet, hRE⟩ le_rfl)))
  exact (not_lt_of_ge hbound) hq₂

end Kolmogorov.PointToSet
