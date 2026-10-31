/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Pressure.Lower.PointToSetPrinciple

/-!
# Entropy as zero-potential pressure

For a nonempty set, classical lower and upper entropy, embedded from `ENNReal` into
`EReal`, agree with the corresponding signed pressures at zero potential. This proves
the classical identifications in blueprint node `pressure:entropy-nonnegative`, used by
the lower-pressure point-to-set results to pass between pressure and entropy.

Negative exponents cannot have vanishing lower covering content or support a uniform
zero-potential net on a nonempty set. For upper pressure, countable decompositions and
recentring of Bowen covers identify the pressure with the infimum of uniform-net exponents.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- At a nonpositive exponent, covering a nonempty set has cost at least one. -/
private lemma one_le_lowerContentLimit_of_nonpos (T : X → X) {Z : Set X}
    (hZ : Z.Nonempty) {s : ℝ} (hs : s ≤ 0) (r : ℝ) :
    (1 : ℝ≥0∞) ≤ lowerContentLimit T (fun _ ↦ 0) .centered Z s r := by
  have hcontent : (1 : ℝ≥0∞) ≤ lowerContent T (fun _ ↦ 0) .centered Z s r 1 := by
    refine le_iInf fun C ↦ le_iInf fun hC ↦ ?_
    obtain ⟨z, hz⟩ := hZ
    obtain ⟨j, _⟩ := Set.mem_iUnion.mp (hC.2 hz)
    have hweight : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ)) := by
      simpa only [ENNReal.rpow_zero] using
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (mul_nonneg (neg_nonneg.mpr hs) (Nat.cast_nonneg (C.order j)))
    calc
      (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ)) := hweight
      _ = (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ)) *
          pressureBallWeight T (fun _ ↦ 0) .centered (C.order j) (C.center j) r := by
        simp [pressureBallWeight, birkhoffSum]
      _ ≤ bowenCoverCost T (fun _ ↦ 0) .centered s r C := by
        unfold bowenCoverCost
        exact ENNReal.le_tsum (f := fun j ↦ (2 : ℝ≥0∞) ^ (-s * (C.order j : ℝ)) *
          pressureBallWeight T (fun _ ↦ 0) .centered (C.order j) (C.center j) r) j
  exact hcontent.trans (le_iSup_of_le 1 (le_iSup_of_le le_rfl le_rfl))

/-- Vanishing zero-potential content on a nonempty set requires a nonnegative exponent. -/
private lemma lowerContentLimit_inf_eq_nonneg (T : X → X) {Z : Set X}
    (hZ : Z.Nonempty) (r : ℝ) :
    (⨅ s : ℝ, ⨅ (_ : 0 ≤ s),
      ⨅ (_ : lowerContentLimit T (fun _ ↦ 0) .centered Z s r = 0), (s : EReal)) =
    ⨅ s : ℝ, ⨅ (_ : lowerContentLimit T (fun _ ↦ 0) .centered Z s r = 0),
      (s : EReal) := by
  apply le_antisymm
  · refine le_iInf fun s ↦ le_iInf fun hzero ↦ ?_
    have hs : 0 ≤ s := by
      by_contra h
      have hone := one_le_lowerContentLimit_of_nonpos T hZ (not_le.mp h).le r
      rw [hzero] at hone
      exact one_ne_zero (le_zero_iff.mp hone)
    exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le hzero le_rfl))
  · exact le_iInf fun s ↦ le_iInf fun _ ↦ le_iInf fun hzero ↦ iInf₂_le s hzero

/-- On nonempty sets, lower entropy embeds as the zero-potential signed lower pressure.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty (P : Presentation X) (T : X → X)
    (hT : Continuous T) (Z : Set X) (hZ : Z.Nonempty) :
    (lowerEntropy T Z : EReal) = lowerPressure T (fun _ => 0) 0 Z := by
  -- The public interface retains these assumptions; this identity needs only nonemptiness.
  have _ := P
  have _ := hT
  unfold lowerEntropy lowerPressure lowerPressureAt
  rw [EReal.coe_ennreal_iSup]
  apply iSup_congr
  intro p
  rw [iSup_pos (Nat.zero_le p), ← lowerContentLimit_inf_eq_nonneg T hZ (dyadicRadius p)]
  simp_rw [EReal.coe_ennreal_iInf]
  apply iInf_congr
  intro s
  apply iInf_congr
  intro hs
  simp only [EReal.coe_ennreal_ofReal, max_eq_left hs]

/-- A uniform net covering a nonempty set has a nonnegative exponent: some slice contains
at least one center at every positive order. -/
private lemma uniformPressureNet_exponent_nonneg
    (P : Presentation X) (T : X → X) (Z : Set X) (hZ : Z.Nonempty)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ)) (hE : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E) :
    0 ≤ s := by
  rcases hZ with ⟨x, hx⟩
  rcases hE with ⟨_, hE_rate, hE_cover⟩
  rcases hE_cover 0 le_rfl x hx with ⟨k, hk⟩
  have h_sum : ∀ (n : ℕ), 1 ≤ n → (1 : ENNReal) ≤ uniformPressureSum P T (fun _ ↦ 0) E n 0 k := by
    intro n hn
    rcases hk n hn with ⟨i, hi, _⟩
    have h_le := ENNReal.le_tsum
      (f := fun _ : {j : ℕ // (j, n, 0, k) ∈ E} ↦ (1 : ENNReal)) (a := ⟨i, hi⟩)
    dsimp [uniformPressureSum]
    simp only [birkhoffSum, Finset.sum_const_zero, ENNReal.rpow_zero]
    exact h_le
  have h_rate := hE_rate 0 le_rfl k
  have h_rate_nonneg : ∀ᶠ n in atTop, (0 : EReal) ≤
      pressureRate (fun n ↦ uniformPressureSum P T (fun _ ↦ 0) E n 0 k) n := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    have h1 := h_sum n hn
    dsimp [pressureRate, pressureLog]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    have hlog : (0 : EReal) ≤ ENNReal.log (uniformPressureSum P T (fun _ ↦ 0) E n 0 k) :=
      ENNReal.zero_le_log_iff.2 h1
    have hinv2 : (0 : EReal) ≤ ((Real.log 2)⁻¹ : ℝ) := by
      rw [EReal.coe_nonneg]
      exact inv_nonneg.mpr (Real.log_nonneg (by norm_num))
    have hinvn : (0 : EReal) ≤ ((n : ℝ)⁻¹ : ℝ) := by
      rw [EReal.coe_nonneg]
      positivity
    have hm1 := EReal.mul_nonneg hlog hinv2
    exact EReal.mul_nonneg hm1 hinvn
  have h_limsup_nonneg : (0 : EReal) ≤
      limsup (pressureRate (fun n ↦ uniformPressureSum P T (fun _ ↦ 0) E n 0 k)) atTop :=
    le_limsup_of_frequently_le (hu_le := by isBoundedDefault) h_rate_nonneg.frequently
  have : (0 : EReal) ≤ (s : EReal) := le_trans h_limsup_nonneg h_rate
  exact EReal.coe_nonneg.mp this

/-- Restricting uniform-net exponents to nonnegative reals does not change their infimum
on a nonempty set. -/
private lemma uniformPressureNet_inf_eq_nonneg (P : Presentation X) (T : X → X)
    (Z : Set X) (hZ : Z.Nonempty) :
    (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
      ⨅ (_ : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E), (s : EReal)) =
  ⨅ s : ℝ, ⨅ (_ : ∃ E, IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E), (s : EReal) := by
  apply le_antisymm
  · refine le_iInf fun s ↦ le_iInf fun ⟨E, hE⟩ ↦ ?_
    have hs : 0 ≤ s := uniformPressureNet_exponent_nonneg P T Z hZ s E hE
    exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le E (iInf_le_of_le hE le_rfl)))
  · refine le_iInf fun s ↦ le_iInf fun _ ↦ le_iInf fun E ↦ le_iInf fun hE ↦ ?_
    exact iInf_le_of_le s (iInf_le_of_le ⟨E, hE⟩ le_rfl)

/-- The nonnegative embedding commutes with the infimum of nonnegative uniform-net exponents. -/
private lemma coe_uniformPressureNet_inf (P : Presentation X) (T : X → X) (Z : Set X) :
    (↑(⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
      ⨅ (_ : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E), ENNReal.ofReal s) : EReal) =
    (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ × ℕ),
      ⨅ (_ : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E), (s : EReal)) := by
  rw [EReal.coe_ennreal_iInf]
  congr 1; funext s
  rw [EReal.coe_ennreal_iInf]
  congr 1; funext hs
  rw [EReal.coe_ennreal_iInf]
  congr 1; funext E
  rw [EReal.coe_ennreal_iInf]
  congr 1; funext hE
  simp [EReal.coe_ennreal_ofReal, hs]

/-- The distinct ideal centers of a slice give a cover whose cost is at most the slice sum. -/
private lemma partitionSum_le_uniformPressureSum (P : Presentation X) (T : X → X)
    (E : Set (ℕ × ℕ × ℕ × ℕ)) (p k n : ℕ) {Y : Set X}
    (hY : Y ⊆ ⋃ i ∈ {i | (i, n, p, k) ∈ E}, bowenBall T n (P.ι i) (dyadicRadius p)) :
    partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius p) ≤
      uniformPressureSum P T (fun _ ↦ 0) E n p k := by
  let I : Set ℕ := {i | (i, n, p, k) ∈ E}
  have hcover : Y ⊆ ⋃ y ∈ P.ι '' I, bowenBall T n y (dyadicRadius p) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hY hx)
    exact Set.mem_iUnion₂.mpr ⟨P.ι i, ⟨i, hi, rfl⟩, hxi⟩
  refine iInf_le_of_le (P.ι '' I)
    (iInf_le_of_le ⟨(Set.to_countable I).image P.ι, hcover⟩ ?_)
  exact ENNReal.tsum_le_tsum_comp_of_surjective
    (Set.surjective_mapsTo_image_restrict P.ι I)
    (fun y ↦ (2 : ℝ≥0∞) ^ birkhoffSum T (fun _ ↦ 0) n y)

/-- A uniform zero-potential net bounds the upper pressure of the covered set. -/
private lemma upperPressure_le_of_net (P : Presentation X) (T : X → X) (Z : Set X)
    (s : ℝ) (E : Set (ℕ × ℕ × ℕ × ℕ))
    (hE : IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E) :
    upperPressure T (fun _ ↦ 0) 0 Z ≤ (s : EReal) := by
  refine iSup_le fun p ↦ iSup_le fun _ ↦ ?_
  let Y (k : ℕ) : Set X :=
    {x | ∀ n ≥ 1, ∃ i, (i, n, p, k) ∈ E ∧ x ∈ bowenBall T n (P.ι i) (dyadicRadius p)}
  have hcover : Z ⊆ ⋃ k, Y k := by
    intro x hx
    obtain ⟨k, hk⟩ := hE.2.2 p (Nat.zero_le p) x hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  refine iInf_le_of_le Y (iInf_le_of_le hcover (iSup_le fun k ↦ ?_))
  refine le_trans ?_ (hE.2.1 p (Nat.zero_le p) k)
  apply limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply pressureRate_le_of_le
  apply partitionSum_le_uniformPressureSum
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hx n hn
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩

/-- A strict modified-pressure bound yields a countable cover with the same capacity bound. -/
private lemma exists_cover_of_modifiedUpperPressure_lt
    (T : X → X) (Z : Set X) (a : ℝ) (q : ℕ)
    (h : modifiedUpperPressure T (fun _ ↦ 0) .centered Z (dyadicRadius q) < (a : EReal)) :
    ∃ Y : ℕ → Set X, Z ⊆ ⋃ k, Y k ∧
      ∀ k, upperCapacity T (fun _ ↦ 0) .centered (Y k) (dyadicRadius q) < (a : EReal) := by
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp h
  obtain ⟨hcover, hcapacity⟩ := iInf_lt_iff.mp hY
  exact ⟨Y, hcover, fun k ↦ (le_iSup _ k).trans_lt hcapacity⟩

/-- A strict capacity bound eventually bounds the partition rates by a smaller real number. -/
private lemma exists_eventual_partitionRate_bound (T : X → X) (Y : Set X) (q : ℕ) (a : ℝ)
    (h : upperCapacity T (fun _ ↦ 0) .centered Y (dyadicRadius q) < (a : EReal)) :
    ∃ N : ℕ, ∃ b : ℝ, (b : EReal) < (a : EReal) ∧ ∀ n ≥ N,
      pressureRate (fun n ↦ partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q)) n ≤
        (b : EReal) := by
  obtain ⟨b, hb, hba⟩ := EReal.exists_between_coe_real h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_lt_of_limsup_lt hb (by isBoundedDefault))
  exact ⟨N, b, hba, fun n hn ↦ (hN n hn).le⟩

/-- A finite partition sum on a nonempty set admits a cover costing less than twice the infimum. -/
private lemma exists_partitionCover_cost_lt_double (T : X → X) (Y : Set X) (q n : ℕ)
    (hY : Y.Nonempty)
    (hfin : partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) < ⊤) :
    ∃ F : Set X, F.Countable ∧ Y ⊆ ⋃ y ∈ F, bowenBall T n y (dyadicRadius q) ∧
      partitionCoverCost T (fun _ ↦ 0) .centered F n (dyadicRadius q) <
        2 * partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) := by
  have hone : (1 : ℝ≥0∞) ≤
      partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) := by
    refine le_iInf fun F ↦ le_iInf fun hF ↦ ?_
    obtain ⟨x, hx⟩ := hY
    obtain ⟨y, hy, _⟩ := Set.mem_iUnion₂.mp (hF.2 hx)
    simpa only [partitionCoverCost, pressureBallWeight, birkhoffSum,
      Finset.sum_const_zero, ENNReal.rpow_zero] using
      (ENNReal.le_tsum (f := fun _ : F ↦ (1 : ℝ≥0∞)) ⟨y, hy⟩)
  have hpos := zero_lt_one.trans_le hone
  have hdouble : partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) <
      2 * partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) := by
    simpa [mul_comm] using
      ENNReal.mul_lt_mul_right hpos.ne' hfin.ne (by norm_num : (1 : ℝ≥0∞) < 2)
  obtain ⟨F, hF⟩ := iInf_lt_iff.mp hdouble
  obtain ⟨hcover, hcost⟩ := iInf_lt_iff.mp hF
  exact ⟨F, hcover.1, hcover.2, hcost⟩

/-- Eventually finite partition sums yield countable covers at every positive order, with
cost eventually less than twice the corresponding partition sum. -/
private lemma exists_partitionCovers_cost_lt_double (T : X → X) (Y : Set X) (q N : ℕ)
    (hY : Y.Nonempty)
    (hfin : ∀ n ≥ max 1 N, partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) < ⊤) :
    ∃ F : ℕ → Set X, ∀ n ≥ 1, (F n).Countable ∧ Y ⊆ ⋃ y ∈ F n, bowenBall T n y (dyadicRadius q) ∧
      (n ≥ max 1 N → partitionCoverCost T (fun _ ↦ 0) .centered (F n) n (dyadicRadius q) <
        2 * partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q)) := by
  choose F hcount hcover hcost using fun n ↦
    exists_partitionCover_cost_lt_double T Y q (max n (max 1 N)) hY
      (hfin _ (le_max_right _ _))
  refine ⟨F, fun n _ ↦ ⟨hcount n, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover n hx)
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    exact Dynamics.dynEntourage_antitone T _ (le_max_left n (max 1 N)) hxy
  · intro hn
    simpa only [max_eq_left hn] using hcost n

/-- A factor of two in the costs does not affect a strict asymptotic rate bound. -/
private lemma limsup_pressureRate_lt_of_eventually_le_double (f g : ℕ → ℝ≥0∞)
    {a b : ℝ} (hb : (b : EReal) < (a : EReal))
    (hf : ∀ᶠ n in atTop, pressureRate f n ≤ (b : EReal))
    (hg : ∀ᶠ n in atTop, g n ≤ 2 * f n) :
    limsup (pressureRate g) atTop < (a : EReal) := by
  obtain ⟨c, hbc, hca⟩ := EReal.exists_between_coe_real hb
  have hdiff : 0 < c - b := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hbc)
  have hev : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < c - b :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds hdiff)
  have hbound : ∀ᶠ n in atTop, pressureRate g n ≤ (c : EReal) := by
    filter_upwards [hev, hf, hg, eventually_ge_atTop 1] with n hn_diff hfn hgn hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hcost : g n ≤ f n * (2 : ℝ≥0∞) ^ ((n : ℝ) * (n : ℝ)⁻¹) := by
      rw [mul_inv_cancel₀ hn0, ENNReal.rpow_one, mul_comm]
      exact hgn
    calc
      pressureRate g n ≤ pressureRate f n + ((n : ℝ)⁻¹ : EReal) :=
        pressureRate_le_add_of_le_mul f g _ n hn hcost
      _ ≤ (b : EReal) + ((c - b : ℝ) : EReal) := by
        apply add_le_add hfn
        exact EReal.coe_le_coe_iff.mpr (by simpa only [one_div] using hn_diff.le)
      _ = (c : EReal) := by rw [← EReal.coe_add, add_sub_cancel]
  exact (limsup_le_of_le (hf := by isBoundedDefault) hbound).trans_lt hca

/-- A strict capacity bound can be realized by a sequence of countable Bowen covers
whose costs satisfy the same strict asymptotic bound. -/
private lemma exists_partitionCovers_rate_lt
    (T : X → X) (a : ℝ) (q : ℕ)
    (Y : Set X) (hY : upperCapacity T (fun _ ↦ 0) .centered Y (dyadicRadius q) < (a : EReal)) :
    ∃ F : ℕ → Set X,
      (∀ n ≥ 1, (F n).Countable ∧ Y ⊆ ⋃ y ∈ F n, bowenBall T n y (dyadicRadius q)) ∧
      limsup (pressureRate (fun n ↦
        partitionCoverCost T (fun _ ↦ 0) .centered (F n) n (dyadicRadius q))) atTop <
          (a : EReal) := by
  rcases Set.eq_empty_or_nonempty Y with hY_emp | hY_ne
  · subst Y
    refine ⟨fun _ ↦ ∅, fun _ _ ↦ ⟨Set.countable_empty, Set.empty_subset _⟩, ?_⟩
    simp only [partitionCoverCost, tsum_empty]
    rw [funext pressureRate_zero, limsup_const]
    exact EReal.bot_lt_coe a
  · rcases exists_eventual_partitionRate_bound T Y q a hY with ⟨N, b, hb, hN⟩
    have hfin (n : ℕ) (hn : max 1 N ≤ n) :
        partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) < ⊤ :=
      lt_top_of_pressureRate_le ((le_max_left 1 N).trans hn)
        (hN n ((le_max_right 1 N).trans hn))
    rcases exists_partitionCovers_cost_lt_double T Y q N hY_ne hfin with ⟨F, hF_prop⟩
    use F
    refine ⟨fun n hn ↦ ⟨(hF_prop n hn).1, (hF_prop n hn).2.1⟩, ?_⟩
    have hF_cost : ∀ n ≥ max 1 N,
        partitionCoverCost T (fun _ ↦ 0) .centered (F n) n (dyadicRadius q) ≤
          2 * partitionSum T (fun _ ↦ 0) .centered Y n (dyadicRadius q) := by
      intro n hn
      exact le_of_lt ((hF_prop n (by linarith [le_max_left 1 N])).2.2 hn)
    exact limsup_pressureRate_lt_of_eventually_le_double _ _ hb
      (eventually_atTop.mpr ⟨N, hN⟩) (eventually_atTop.mpr ⟨max 1 N, hF_cost⟩)

/-- Recentring a Bowen cover at ideal points doubles the radius without increasing its
zero-potential cost, even when several centers are sent to the same ideal point. -/
private lemma exists_ideal_bowenCover (P : Presentation X) (T : X → X)
    (hT : Continuous T) (F : Set X) {n p : ℕ} (hn : 1 ≤ n) :
    ∃ I : Set ℕ,
      (∑' _ : I, (1 : ℝ≥0∞)) ≤
        partitionCoverCost T (fun _ ↦ 0) .centered F n (dyadicRadius (p + 1)) ∧
      (⋃ y ∈ F, bowenBall T n y (dyadicRadius (p + 1))) ⊆
        ⋃ i ∈ I, bowenBall T n (P.ι i) (dyadicRadius p) := by
  have hr : 0 < dyadicRadius (p + 1) := by unfold dyadicRadius; positivity
  have hcenter (y : F) : ∃ i, P.ι i ∈ bowenBall T n y (dyadicRadius (p + 1)) :=
    bowen_ball_dense P T hT y n hn _ hr
  choose c hc using hcenter
  refine ⟨Set.range c, ?_, ?_⟩
  · simpa only [partitionCoverCost, pressureBallWeight, birkhoffSum,
      Finset.sum_const_zero, ENNReal.rpow_zero] using
      ENNReal.tsum_le_tsum_comp_of_surjective (Set.rangeFactorization_surjective (f := c))
        (fun _ : Set.range c ↦ (1 : ℝ≥0∞))
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨c ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    have hiy := hc ⟨y, hy⟩
    have hdouble : dyadicRadius (p + 1) + dyadicRadius (p + 1) =
        dyadicRadius p := by
      unfold dyadicRadius
      rw [pow_succ]
      ring
    dsimp [bowenBall] at hiy hxy ⊢
    rw [Dynamics.mem_dynEntourage] at hiy hxy ⊢
    intro j hj
    have hi := hiy j hj
    have hxj := hxy j hj
    change dist (T^[j] y) (T^[j] (P.ι (c ⟨y, hy⟩))) < dyadicRadius (p + 1) at hi
    change dist (T^[j] y) (T^[j] x) < dyadicRadius (p + 1) at hxj
    change dist (T^[j] (P.ι (c ⟨y, hy⟩))) (T^[j] x) < dyadicRadius p
    calc
      dist (T^[j] (P.ι (c ⟨y, hy⟩))) (T^[j] x) ≤
          dist (T^[j] (P.ι (c ⟨y, hy⟩))) (T^[j] y) + dist (T^[j] y) (T^[j] x) :=
        dist_triangle _ _ _
      _ < dyadicRadius (p + 1) + dyadicRadius (p + 1) :=
        add_lt_add (by simpa only [dist_comm] using hi) hxj
      _ = dyadicRadius p := hdouble

/-- Every strict upper bound on zero-potential upper pressure admits a uniform net. -/
private lemma exists_uniformPressureNet_of_upperPressure_lt
    (P : Presentation X) (T : X → X) (hT : Continuous T) (Z : Set X)
    (s : ℝ) (hs : upperPressure T (fun _ ↦ 0) 0 Z < (s : EReal)) :
    ∃ E, IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E := by
  have hmodified (p : ℕ) :
      modifiedUpperPressure T (fun _ ↦ 0) .centered Z (dyadicRadius (p + 1)) <
        (s : EReal) :=
    (le_iSup₂ (p + 1) (Nat.zero_le (p + 1))).trans_lt hs
  choose Y hcover hcapacity using
    fun p ↦ exists_cover_of_modifiedUpperPressure_lt T Z s (p + 1) (hmodified p)
  choose F hF hrate using
    fun p k ↦ exists_partitionCovers_rate_lt T s (p + 1) (Y p k) (hcapacity p k)
  choose I hcost hball using
    fun p k n (hn : 1 ≤ n) ↦ exists_ideal_bowenCover P T hT (F p k n) hn (p := p)
  let E : Set (ℕ × ℕ × ℕ × ℕ) :=
    {t | ∃ hn : 1 ≤ t.2.1, t.1 ∈ I t.2.2.1 t.2.2.2 t.2.1 hn}
  have hsum (p k n : ℕ) (hn : 1 ≤ n) :
      uniformPressureSum P T (fun _ ↦ 0) E n p k ≤
        partitionCoverCost T (fun _ ↦ 0) .centered (F p k n) n (dyadicRadius (p + 1)) := by
    have hslice : {i | (i, n, p, k) ∈ E} = I p k n hn := by
      ext i
      exact ⟨fun ⟨_, hi⟩ ↦ hi, fun hi ↦ ⟨hn, hi⟩⟩
    simp only [uniformPressureSum, birkhoffSum, Finset.sum_const_zero, ENNReal.rpow_zero]
    change (∑' _ : {i | (i, n, p, k) ∈ E}, (1 : ℝ≥0∞)) ≤ _
    rw [hslice]
    exact hcost p k n hn
  refine ⟨E, ?_, ?_, ?_⟩
  · rintro t ⟨hn, _⟩
    exact ⟨hn, Nat.zero_le _⟩
  · intro p _ k
    refine le_trans ?_ (hrate p k).le
    apply limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pressureRate_le_of_le _ _ n (hsum p k n hn)
  · intro p _ x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover p hx)
    refine ⟨k, fun n hn ↦ ?_⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hball p k n hn ((hF p k n hn).2 hk))
    exact ⟨i, ⟨hn, hi⟩, hxi⟩

/-- Zero-potential upper pressure is the infimum of uniform-net exponents. -/
private theorem upperPressure_eq_iInf_uniformPressureNet
    (P : Presentation X) (T : X → X) (hT : Continuous T) (Z : Set X) :
    upperPressure T (fun _ ↦ 0) 0 Z =
      ⨅ s : ℝ, ⨅ (_ : ∃ E, IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E), (s : EReal) := by
  apply le_antisymm
  · refine le_iInf fun s ↦ le_iInf fun ⟨E, hE⟩ ↦ ?_
    exact upperPressure_le_of_net P T Z s E hE
  · by_contra h
    obtain ⟨r, hpressure, hr⟩ := EReal.exists_between_coe_real (not_le.mp h)
    have hnet := exists_uniformPressureNet_of_upperPressure_lt P T hT Z r hpressure
    have hle : (⨅ s : ℝ, ⨅ (_ : ∃ E, IsUniformPressureNet P T (fun _ ↦ 0) 0 Z s E),
        (s : EReal)) ≤ (r : EReal) := iInf₂_le r hnet
    exact (not_lt_of_ge hle) hr

/-- Nonempty-set upper entropy embeds as zero-potential signed upper pressure.
Blueprint node `pressure:entropy-nonnegative`. -/
theorem entropy_eq_zeroPotentialPressure_of_nonempty_upper (P : Presentation X)
    (T : X → X) (hT : Continuous T) (Z : Set X) (hZ : Z.Nonempty) :
    (upperEntropy P T Z : EReal) = upperPressure T (fun _ => 0) 0 Z := by
  rw [upperPressure_eq_iInf_uniformPressureNet P T hT Z]
  dsimp [upperEntropy]
  rw [coe_uniformPressureNet_inf P T Z]
  rw [uniformPressureNet_inf_eq_nonneg P T Z hZ]

end Kolmogorov.PointToSet
