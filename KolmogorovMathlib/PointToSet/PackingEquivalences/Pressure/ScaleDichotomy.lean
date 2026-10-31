/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure.PackingSeparatedDefs

/-!
# Packing pressure thresholds and scale comparisons

The packing outer envelope `pressureOuterEnvelope T f Z s r` is antitone in the exponent `s`,
and it jumps from `⊤` to `0` at a single threshold, which is the packing pressure
`packingPressureAt T f Z r` at scale `r`
(`pressureDichotomyScaleLimit_threshold`, blueprint node `pack:pressure-dichotomy`).
Shrinking the radius from `r` to `r'` changes this threshold by at most the potential variation
`ω_f(r)` (`pressureDichotomyScaleLimit_radius`), and for a uniformly continuous potential the
variation tends to `0` with the radius, so the packing pressure converges at scale zero
(`pressureDichotomyScaleLimit_limit`).

The remaining results compare packings with separated sets.  `extractOrder` extracts one large
slice from a geometrically weighted mass (blueprint node `pack:order-extraction`), and
`packBoundsModifiedSeparatedPressure` bounds the modified separated pressure at radius `2 * r`
by the packing pressure at radius `r` plus the variation `ω_f(2 * r)` (blueprint node
`pack:pack-to-sep`).  These results feed the pressure equivalence theorem in the modules
importing this one.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X]

/-- The packing outer envelope decreases as the real exponent increases. -/
lemma pressureOuterEnvelope_antitone_exponent (T : X → X) (f : X → ℝ)
    (Z : Set X) (r : ℝ) : Antitone (fun s ↦ pressureOuterEnvelope T f Z s r) := by
  intro s t hst
  dsimp [pressureOuterEnvelope]
  refine iInf_mono (fun Y ↦ ?_)
  refine iInf_mono (fun H ↦ ?_)
  refine ENNReal.tsum_le_tsum (fun j ↦ ?_)
  dsimp [packingPressurePrecontent]
  refine iInf_mono (fun N ↦ ?_)
  refine iInf_mono (fun hN ↦ ?_)
  dsimp [packingPressureContent]
  refine iSup_mono (fun F ↦ ?_)
  refine iSup_mono (fun hF ↦ ?_)
  dsimp [packingPressureSum]
  refine ENNReal.tsum_le_tsum (fun a ↦ ?_)
  gcongr ?_ * _
  exact ENNReal.rpow_le_rpow_of_exponent_le (by simp)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) a.val.2])

/-- An exponent with infinite envelope is a lower bound for the packing pressure. -/
private lemma le_packingPressureAt_of_pressureOuterEnvelope_eq_top (T : X → X) (f : X → ℝ)
    (Z : Set X) (r s : ℝ) (hs : pressureOuterEnvelope T f Z s r = ⊤) :
    (s : EReal) ≤ packingPressureAt T f Z r := by
  refine le_iInf fun t ↦ le_iInf fun ht ↦ ?_
  by_contra h_contra
  push Not at h_contra
  have hmono : pressureOuterEnvelope T f Z s r ≤ pressureOuterEnvelope T f Z t r :=
    pressureOuterEnvelope_antitone_exponent T f Z r (EReal.coe_lt_coe_iff.mp h_contra).le
  rw [hs, ht] at hmono
  exact absurd hmono (by simp)

/-- Every exponent above the supremum of the exponents with infinite envelope has zero
envelope. -/
private lemma pressureOuterEnvelope_eq_zero_of_iSup_lt (T : X → X) (f : X → ℝ) (Z : Set X) (r t : ℝ)
    (hSup : (⨆ s : ℝ, ⨆ (_ : pressureOuterEnvelope T f Z s r = ⊤), (s : EReal)) < (t : EReal)) :
    pressureOuterEnvelope T f Z t r = 0 := by
  obtain ⟨s, hSupS, hST⟩ := EReal.exists_between_coe_real hSup
  have hfinite : pressureOuterEnvelope T f Z s r < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop ↦ ?_
    exact not_lt_of_ge (le_iSup₂_of_le s htop le_rfl) hSupS
  exact pressureDichotomyScaleLimit T f Z s t r (EReal.coe_lt_coe_iff.mp hST) hfinite

/-- The packing pressure is at most the supremum of the exponents with infinite envelope. -/
private lemma packingPressureAt_le_iSup_pressureOuterEnvelope_eq_top (T : X → X) (f : X → ℝ)
    (Z : Set X) (r : ℝ) :
    packingPressureAt T f Z r ≤
      ⨆ s : ℝ, ⨆ (_ : pressureOuterEnvelope T f Z s r = ⊤), (s : EReal) := by
  refine EReal.le_of_forall_lt_iff_le.mp fun t ht ↦ ?_
  have hzero := pressureOuterEnvelope_eq_zero_of_iSup_lt T f Z r t ht
  unfold packingPressureAt
  exact (iInf_le (fun s : ℝ ↦ ⨅ (_ : pressureOuterEnvelope T f Z s r = 0), (s : EReal)) t).trans
    (iInf_le _ hzero)

/-- The infinity and zero critical thresholds agree, including both signed endpoints.
Blueprint node `pack:pressure-dichotomy`. -/
theorem pressureDichotomyScaleLimit_threshold (T : X → X) (f : X → ℝ)
    (Z : Set X) (r : ℝ) :
    packingPressureAt T f Z r =
      ⨆ s : ℝ, ⨆ (_ : pressureOuterEnvelope T f Z s r = ⊤), (s : EReal) :=
  le_antisymm (packingPressureAt_le_iSup_pressureOuterEnvelope_eq_top T f Z r)
    (iSup₂_le fun s hs ↦ le_packingPressureAt_of_pressureOuterEnvelope_eq_top T f Z r s hs)

/-- Shrinking the radius preserves the disjointness condition of a decorated packing. -/
private lemma isBowenPacking_of_le (T : X → X) (Z : Set X) {r' r : ℝ} (hrr : r' ≤ r) {N : ℕ}
    {F : Set (X × ℕ)} (hF : IsBowenPacking T Z r N F) : IsBowenPacking T Z r' N F :=
  ⟨hF.1, hF.2.1, fun _ ha _ hb hab ↦ (hF.2.2 ha hb hab).mono
    (bowenBall_subset_of_le T _ _ hrr) (bowenBall_subset_of_le T _ _ hrr)⟩

/-- Shrinking the Bowen-ball radius from `r` to `r'` lowers the supremum weight by at most the
factor `2 ^ (n * ω_f(r))`. -/
private lemma two_rpow_neg_mul_pressureBallWeight_le (T : X → X) (f : X → ℝ) (x : X)
    (n : ℕ) {r' r : ℝ} (hr' : 0 < r') (hω : potentialVariation f r < ⊤) :
    (2 : ℝ≥0∞) ^ (-(n : ℝ) * (potentialVariation f r).toReal) *
        pressureBallWeight T f .supremum n x r ≤
      pressureBallWeight T f .supremum n x r' := by
  dsimp [pressureBallWeight]
  have hsup : ⨆ z ∈ bowenBall T n x r, (2 : ℝ≥0∞) ^ (birkhoffSum T f n z : ℝ) ≤
      (2 : ℝ≥0∞) ^ (birkhoffSum T f n x + n * (potentialVariation f r).toReal : ℝ) :=
    iSup₂_le fun z hz ↦ ENNReal.rpow_le_rpow_of_exponent_le one_le_two
      (by linarith [(abs_le.mp (abs_birkhoffSum_sub_le_mul_variation T f n x z r hω hz)).2])
  calc (2 : ℝ≥0∞) ^ (-(n : ℝ) * (potentialVariation f r).toReal) *
        ⨆ z ∈ bowenBall T n x r, (2 : ℝ≥0∞) ^ (birkhoffSum T f n z : ℝ)
    _ ≤ (2 : ℝ≥0∞) ^ (-(n : ℝ) * (potentialVariation f r).toReal) *
        (2 : ℝ≥0∞) ^ (birkhoffSum T f n x + n * (potentialVariation f r).toReal : ℝ) := by
      gcongr
    _ = (2 : ℝ≥0∞) ^ (birkhoffSum T f n x : ℝ) := by
      rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      ring
    _ ≤ ⨆ z ∈ bowenBall T n x r', (2 : ℝ≥0∞) ^ (birkhoffSum T f n z : ℝ) :=
      le_iSup₂_of_le x (self_mem_bowenBall T n x r' hr') le_rfl

/-- A packing sum at the larger radius `r` and exponent `s + ω_f(r)` is bounded by the packing
sum at the smaller radius `r'` and exponent `s`. -/
private lemma packingPressureSum_shift_le (T : X → X) (f : X → ℝ) (s : ℝ) {r' r : ℝ}
    (hr' : 0 < r') (hω : potentialVariation f r < ⊤) {F : Set (X × ℕ)} :
    packingPressureSum T f (s + (potentialVariation f r).toReal) r F ≤
      packingPressureSum T f s r' F := by
  dsimp [packingPressureSum]
  refine ENNReal.tsum_le_tsum fun a ↦ ?_
  have hexp : -(s + (potentialVariation f r).toReal) * a.val.2 =
      -s * a.val.2 + -(a.val.2 : ℝ) * (potentialVariation f r).toReal := by ring
  rw [hexp, ENNReal.rpow_add (x := 2) _ _ (by norm_num) (by norm_num), mul_assoc]
  gcongr
  exact two_rpow_neg_mul_pressureBallWeight_le T f a.1.1 a.1.2 hr' hω

/-- The cutoff packing content at the larger radius `r` and exponent `s + ω_f(r)` is bounded by
the one at the smaller radius `r'` and exponent `s`. -/
private lemma packingPressureContent_shift_le (T : X → X) (f : X → ℝ) (Z : Set X) (s : ℝ)
    {r' r : ℝ} (hrr : r' ≤ r) (hr' : 0 < r') (hω : potentialVariation f r < ⊤) (N : ℕ) :
    packingPressureContent T f Z (s + (potentialVariation f r).toReal) r N ≤
      packingPressureContent T f Z s r' N := by
  dsimp [packingPressureContent]
  refine iSup_mono fun F ↦ iSup_mono' fun hF ↦ ⟨isBowenPacking_of_le T Z hrr hF, ?_⟩
  exact packingPressureSum_shift_le T f s hr' hω

/-- The packing pre-content at the larger radius `r` and exponent `s + ω_f(r)` is bounded by
the one at the smaller radius `r'` and exponent `s`. -/
private lemma packingPressurePrecontent_shift_le (T : X → X) (f : X → ℝ) (Z : Set X) (s : ℝ)
    {r' r : ℝ} (hrr : r' ≤ r) (hr' : 0 < r') (hω : potentialVariation f r < ⊤) :
    packingPressurePrecontent T f Z (s + (potentialVariation f r).toReal) r ≤
      packingPressurePrecontent T f Z s r' := by
  dsimp [packingPressurePrecontent]
  exact iInf_mono fun N ↦ iInf_mono fun _ ↦ packingPressureContent_shift_le T f Z s hrr hr' hω N

/-- The packing outer envelope at the larger radius `r` and exponent `s + ω_f(r)` is bounded by
the one at the smaller radius `r'` and exponent `s`. -/
private lemma pressureOuterEnvelope_shift_le (T : X → X) (f : X → ℝ) (Z : Set X) (s : ℝ)
    {r' r : ℝ} (hrr : r' ≤ r) (hr' : 0 < r') (hω : potentialVariation f r < ⊤) :
    pressureOuterEnvelope T f Z (s + (potentialVariation f r).toReal) r ≤
      pressureOuterEnvelope T f Z s r' := by
  dsimp [pressureOuterEnvelope]
  exact iInf_mono fun Y ↦ iInf_mono fun _ ↦ ENNReal.tsum_le_tsum fun j ↦
    packingPressurePrecontent_shift_le T f (Y j) s hrr hr' hω

/-- Taking the infimum over the exponents satisfying a predicate `P` and shifting by a real
amount `c` is bounded by the infimum over exponents satisfying `Q`, provided a `Q`-exponent
`s` makes `s + c` satisfy `P`. -/
private lemma iInf_sub_le_iInf_of_shift (c : ℝ) (P Q : ℝ → Prop)
    (hshift : ∀ s : ℝ, Q s → P (s + c)) :
    (⨅ t : ℝ, ⨅ (_ : P t), (t : EReal)) - (c : EReal) ≤
      ⨅ s : ℝ, ⨅ (_ : Q s), (s : EReal) := by
  refine le_iInf₂ fun s hs ↦ ?_
  refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c))).2 ?_
  calc (⨅ t : ℝ, ⨅ (_ : P t), (t : EReal)) ≤ ((s + c : ℝ) : EReal) :=
      iInf₂_le (s + c) (hshift s hs)
    _ = (s : EReal) + (c : EReal) := by rw [EReal.coe_add]

/-- Shrinking the radius loses at most the finite variation in critical pressure.
Blueprint node `pack:pressure-dichotomy`. -/
theorem pressureDichotomyScaleLimit_radius (T : X → X) (f : X → ℝ) (Z : Set X)
    (r' r : ℝ) (hr' : 0 < r') (hrr : r' ≤ r) (hω : potentialVariation f r < ⊤) :
    packingPressureAt T f Z r - ((potentialVariation f r).toReal : EReal) ≤
      packingPressureAt T f Z r' := by
  dsimp [packingPressureAt]
  refine iInf_sub_le_iInf_of_shift _ _ _ fun s hs ↦ ?_
  have hle := pressureOuterEnvelope_shift_le T f Z s hrr hr' hω
  rw [hs] at hle
  exact le_antisymm hle bot_le

/-- The potential variation is monotone in the radius. -/
private lemma potentialVariation_mono (f : X → ℝ) {r r' : ℝ} (h : r ≤ r') :
    potentialVariation f r ≤ potentialVariation f r' :=
  iSup_mono fun _ ↦ iSup_mono fun _ ↦ iSup_mono' fun hxy ↦ ⟨hxy.trans h, le_rfl⟩

/-- The packing pressure at a fixed small radius, corrected by the variation, bounds the
`liminf` of the packing pressure as the radius tends to zero. -/
private lemma packingPressureAt_sub_le_liminf (T : X → X) (f : X → ℝ) (Z : Set X)
    {r : ℝ} (hr : 0 < r) (hω : potentialVariation f r < ⊤) :
    packingPressureAt T f Z r - ((potentialVariation f r).toReal : EReal) ≤
      liminf (packingPressureAt T f Z) (𝓝[Set.Ioi 0] 0) := by
  refine Filter.le_liminf_of_le (hf := Filter.isCobounded_ge_of_top) ?_
  have hsmall : ∀ᶠ r' : ℝ in 𝓝[Set.Ioi 0] 0, r' < r :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hsmall] with r' hr' hrr
  exact pressureDichotomyScaleLimit_radius T f Z r' r hr' hrr.le hω

/-- For a uniformly continuous potential, the `limsup` of the packing pressure at scale zero is
at most its `liminf`. -/
private lemma limsup_packingPressureAt_le_liminf (T : X → X) (f : X → ℝ)
    (hf : UniformContinuous f) (Z : Set X) :
    limsup (packingPressureAt T f Z) (𝓝[Set.Ioi 0] 0) ≤
      liminf (packingPressureAt T f Z) (𝓝[Set.Ioi 0] 0) := by
  set L : EReal := liminf (packingPressureAt T f Z) (𝓝[Set.Ioi 0] 0) with hL
  have hbound : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      packingPressureAt T f Z r ≤ L + ((potentialVariation f r).toReal : EReal) := by
    filter_upwards [eventually_potentialVariation_lt_top hf, self_mem_nhdsWithin] with r hfin hpos
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mp (packingPressureAt_sub_le_liminf T f Z hpos hfin)
  have htendsto : Tendsto (fun r : ℝ ↦ L + ((potentialVariation f r).toReal : EReal))
      (𝓝[Set.Ioi 0] 0) (𝓝 L) := by
    have hp : Tendsto (fun r : ℝ ↦ (L, ((potentialVariation f r).toReal : EReal)))
        (𝓝[Set.Ioi 0] 0) (𝓝 (L, (0 : EReal))) :=
      tendsto_const_nhds.prodMk_nhds (tendsto_potentialVariation_toReal hf)
    simpa only [Function.comp_def, add_zero] using
      (EReal.continuousAt_add (p := (L, (0 : EReal)))
        (Or.inr (by norm_num)) (Or.inr (by norm_num))).tendsto.comp hp
  have hcobound : IsCoboundedUnder (· ≤ ·) (𝓝[Set.Ioi 0] 0) (packingPressureAt T f Z) :=
    Filter.isCoboundedUnder_le_of_le _ fun _ ↦ bot_le
  have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[Set.Ioi 0] 0)
      (fun r : ℝ ↦ L + ((potentialVariation f r).toReal : EReal)) :=
    Filter.isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩
  simpa [htendsto.limsup_eq] using Filter.limsup_le_limsup hbound hcobound hbdd

/-- Uniform continuity gives convergence over all positive radii tending to zero.
Blueprint node `pack:pressure-dichotomy`. -/
theorem pressureDichotomyScaleLimit_limit (T : X → X)
    (f : X → ℝ) (hf : UniformContinuous f) (Z : Set X) :
    Tendsto (packingPressureAt T f Z) (𝓝[Set.Ioi 0] 0) (𝓝 (packingPressure T f Z)) := by
  unfold packingPressure
  exact tendsto_of_le_liminf_of_limsup_le (limsup_packingPressureAt_le_liminf T f hf Z) le_rfl
    (Filter.isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩) (Filter.isBoundedUnder_of ⟨⊥, fun _ ↦ bot_le⟩)

/-- A geometric mixed-order mass forces one large slice; both exponents may be negative.
Blueprint node `pack:order-extraction`. -/
theorem extractOrder (s t a : ℝ) (hts : t < s) (ha : 0 < a) (b : ℕ → ℝ≥0∞)
    (N : ℕ) (hN : 1 ≤ N)
    (hmass : ENNReal.ofReal a ≤
      ∑' k : {k : ℕ // N ≤ k}, (2 : ℝ≥0∞) ^ (-(s - t) * (k.val : ℝ)) * b k.val) :
    ∃ k ≥ N, ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(s - t))) * a) ≤ b k := by
  classical
  let q : ℝ := (2 : ℝ) ^ (-(s - t))
  let Q : ℝ≥0∞ := ENNReal.ofReal q
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hQ1 : Q < 1 := ENNReal.ofReal_lt_one.mpr hq1
  have hQ : Q = (2 : ℝ≥0∞) ^ (-(s - t)) := by
    dsimp [Q, q]
    simpa using (ENNReal.ofReal_rpow_of_pos (x := 2) (p := -(s - t)) (by norm_num)).symm
  have hweight (k : ℕ) : (2 : ℝ≥0∞) ^ (-(s - t) * (k : ℝ)) = Q ^ k := by
    rw [ENNReal.rpow_mul_natCast, ← hQ]
  simp_rw [hweight] at hmass
  change ∃ k ≥ N, ENNReal.ofReal ((1 - q) * a) ≤ b k
  by_contra hnone
  push Not at hnone
  have htail : (∑' k : {k : ℕ // N ≤ k}, Q ^ k.val) ≤ Q * (1 - Q)⁻¹ := by
    calc
      (∑' k : {k : ℕ // N ≤ k}, Q ^ k.val) =
          ∑' k : {k : ℕ // N ≤ k}, Q ^ ((k.val - 1) + 1) := by
        apply tsum_congr
        intro k
        rw [Nat.sub_add_cancel (hN.trans k.property)]
      _ ≤ ∑' n : ℕ, Q ^ (n + 1) := by
        refine ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun k : {k : ℕ // N ≤ k} ↦ k.val - 1) ?_ (fun n : ℕ ↦ Q ^ (n + 1))
        intro j k hjk
        change j.val - 1 = k.val - 1 at hjk
        apply Subtype.ext
        have hj := hN.trans j.property
        have hk := hN.trans k.property
        omega
      _ = Q * (1 - Q)⁻¹ := ENNReal.tsum_geometric_add_one Q
  have hc : ENNReal.ofReal ((1 - q) * a) = (1 - Q) * ENNReal.ofReal a := by
    rw [ENNReal.ofReal_mul (sub_nonneg.mpr hq1.le), ENNReal.ofReal_sub 1 hq0.le,
      ENNReal.ofReal_one]
  have hsum : (∑' k : {k : ℕ // N ≤ k}, Q ^ k.val * b k.val) ≤
      Q * ENNReal.ofReal a := by
    calc
      (∑' k : {k : ℕ // N ≤ k}, Q ^ k.val * b k.val) ≤
          ∑' k : {k : ℕ // N ≤ k}, Q ^ k.val * ENNReal.ofReal ((1 - q) * a) := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact mul_le_mul_right (hnone k.val k.property).le _
      _ = (∑' k : {k : ℕ // N ≤ k}, Q ^ k.val) * ENNReal.ofReal ((1 - q) * a) :=
        ENNReal.tsum_mul_right
      _ ≤ (Q * (1 - Q)⁻¹) * ENNReal.ofReal ((1 - q) * a) :=
        mul_le_mul_left htail _
      _ = Q * ENNReal.ofReal a := by
        rw [hc, mul_assoc, ← mul_assoc ((1 - Q)⁻¹),
          ENNReal.inv_mul_cancel (ne_of_gt (tsub_pos_iff_lt.mpr hQ1))
            (ne_top_of_le_ne_top (by simp) tsub_le_self), one_mul]
  have hlt : Q * ENNReal.ofReal a < ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_mul hq0.le]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).mpr (by nlinarith)
  exact (not_lt_of_ge hmass) (hsum.trans_lt hlt)

/-- An order-`n`, `2 * r`-separated subset of `Z` has total sup-weight at most the
packing content at radius `r`, times the factor `2 ^ (a * n + n * ω_f(2 * r))`. -/
private lemma partitionCoverCost_le_mul_packingPressureContent (T : X → X) (f : X → ℝ)
    (Z : Set X) (r a : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N)
    (hω : potentialVariation f (2 * r) < ⊤) (n : ℕ) (hn : N ≤ n)
    (F : Set X) (hF : F ⊆ Z) (hsep : IsBowenSeparated T n (2 * r) F) :
    partitionCoverCost T f .supremum F n (2 * r) ≤
      (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        packingPressureContent T f Z a r N := by
  classical
  have hn1 : 1 ≤ n := hN.trans hn
  have hscale :
      (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        (2 : ℝ≥0∞) ^ (-a * (n : ℝ)) =
      (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) := by
    rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    congr 1
    ring
  unfold partitionCoverCost
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  -- Decorate each center in the finite subset with the common order n.
  let P : Set (X × ℕ) := (fun x : F ↦ ((x : X), n)) '' (s : Set F)
  have hP : IsBowenPacking T Z r N P := by
    refine ⟨(s.finite_toSet.image _).countable, ?_, ?_⟩
    · rintro p ⟨x, hx, rfl⟩
      exact ⟨hF x.property, max_le hn1 hn⟩
    · rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hxy
      have hne : (x : X) ≠ (y : X) := by
        intro h
        exact hxy (Prod.ext h rfl)
      rw [Set.disjoint_left]
      intro z hxball hyball
      have hx' := (bowen_ball_dense_iff T n hn1 x z r).mp hxball
      have hy' := (bowen_ball_dense_iff T n hn1 y z r).mp hyball
      have hsep' : 2 * r ≤ bowenDist T n x y := hsep x.property y.property hne
      have htri := bowen_ball_dense_triangle T n (x : X) z (y : X)
      rw [bowen_dist_comm T n z y] at htri
      linarith
  let π : s → P := fun x ↦ ⟨((x.val : X), n), ⟨x.val, x.property, rfl⟩⟩
  have hπ : Function.Injective π := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : P ↦ p.val.1) h
  have hsum : (∑' x : s, pressureBallWeight T f .supremum n (x.val : X) (2 * r)) ≤
      (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        packingPressureSum T f a r P := by
    unfold packingPressureSum
    apply tsum_le_mul_tsum_of_injective π hπ
    intro x
    change pressureBallWeight T f .supremum n (x.val : X) (2 * r) ≤
      (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        ((2 : ℝ≥0∞) ^ (-a * (n : ℝ)) *
          pressureBallWeight T f .supremum n (x.val : X) r)
    rw [← mul_assoc, hscale]
    exact pressureBallWeight_le_mul_of_mem_bowenBall T f n r hω x.val x.val
      (self_mem_bowenBall T n x.val r hr)
  rw [Finset.tsum_subtype s (fun x : F ↦
    pressureBallWeight T f .supremum n (x : X) (2 * r))] at hsum
  refine hsum.trans (mul_le_mul' le_rfl ?_)
  unfold packingPressureContent
  exact le_iSup₂_of_le P hP le_rfl

/-- If the cutoff packing content at radius `r` is less than one, then the separated upper
pressure at radius `2 * r` is at most `a + ω_f(2 * r)`. -/
private lemma separatedUpperPressureAt_le_of_packingPressureContent_lt_one (T : X → X)
    (f : X → ℝ) (Z : Set X) (r a : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N)
    (hω : potentialVariation f (2 * r) < ⊤)
    (H : packingPressureContent T f Z a r N < 1) :
    separatedUpperPressureAt T f Z (2 * r) ≤
      (a : EReal) + ((potentialVariation f (2 * r)).toReal : EReal) := by
  dsimp [separatedUpperPressureAt]
  refine le_trans (b := limsup (fun _ : ℕ ↦ (a : EReal) +
    ((potentialVariation f (2 * r)).toReal : EReal)) Filter.atTop)
    (Filter.limsup_le_limsup (Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩)
      (Filter.isCoboundedUnder_le_of_le Filter.atTop fun _ ↦ bot_le)
      (Filter.isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)) (by simp)
  have hn1 : 1 ≤ n := hN.trans hn
  have hsum : separatedPressureSum T f Z n (2 * r) ≤
      (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) := by
    refine iSup₂_le fun F hF ↦ ?_
    calc partitionCoverCost T f .supremum F n (2 * r)
      _ ≤ (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) *
          packingPressureContent T f Z a r N :=
        partitionCoverCost_le_mul_packingPressureContent T f Z r a hr N hN hω n hn F hF.1 hF.2
      _ ≤ (2 : ℝ≥0∞) ^ (a * (n : ℝ) + (n : ℝ) * (potentialVariation f (2 * r)).toReal) * 1 := by
        gcongr
      _ = _ := mul_one _
  refine (pressureRate_le_of_le_rpow hn1 hsum).trans_eq ?_
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [← EReal.coe_add]
  congr 1
  field_simp

/-- If the packing outer envelope at radius `r` and exponent `a` is less than one, then the
modified separated pressure at radius `2 * r` is at most `a + ω_f(2 * r)`. -/
private lemma modifiedSeparatedPressureAt_le_of_pressureOuterEnvelope_lt_one (T : X → X)
    (f : X → ℝ) (Z : Set X) (r a : ℝ) (hr : 0 < r) (hω : potentialVariation f (2 * r) < ⊤)
    (H : pressureOuterEnvelope T f Z a r < 1) :
    modifiedSeparatedPressureAt T f Z (2 * r) ≤
      (a : EReal) + ((potentialVariation f (2 * r)).toReal : EReal) := by
  unfold pressureOuterEnvelope at H
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp H
  obtain ⟨hcover, hsum⟩ := iInf_lt_iff.mp hY
  unfold modifiedSeparatedPressureAt
  refine iInf_le_of_le Y (iInf_le_of_le hcover (iSup_le fun j ↦ ?_))
  have hj : packingPressurePrecontent T f (Y j) a r < 1 :=
    (ENNReal.le_tsum (f := fun j ↦ packingPressurePrecontent T f (Y j) a r) j).trans_lt hsum
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp hj
  obtain ⟨hNpos, hNval⟩ := iInf_lt_iff.mp hN
  exact separatedUpperPressureAt_le_of_packingPressureContent_lt_one T f (Y j) r a hr N
    (by exact_mod_cast hNpos) hω hNval

/-- Packing bounds the modified separated pressure with the doubled-radius variation.
Blueprint node `pack:pack-to-sep`. -/
theorem packBoundsModifiedSeparatedPressure (T : X → X) (f : X → ℝ) (Z : Set X) (r : ℝ) (hr : 0 < r)
    (hω : potentialVariation f (2 * r) < ⊤) :
    modifiedSeparatedPressureAt T f Z (2 * r) ≤
      packingPressureAt T f Z r + ((potentialVariation f (2 * r)).toReal : EReal) := by
  refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp (EReal.le_of_forall_lt_iff_le.mp fun a ha ↦ ?_)
  refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mpr ?_
  apply modifiedSeparatedPressureAt_le_of_pressureOuterEnvelope_lt_one T f Z r a hr hω
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp ha
  obtain ⟨hz, hsa⟩ := iInf_lt_iff.mp hs
  have hωr : potentialVariation f r < ⊤ :=
    (potentialVariation_mono f (by linarith)).trans_lt hω
  rw [pressureDichotomyScaleLimit T f Z s a r (by exact_mod_cast hsa)
    (by rw [hz]; simp)]
  exact zero_lt_one

end Kolmogorov.PointToSet
