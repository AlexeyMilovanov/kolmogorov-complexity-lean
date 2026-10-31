/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.PointToSet.ComputableMetric
import KolmogorovMathlib.PointToSet.Conformal.Defs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Packing dimension equals modified upper box dimension

For the specified-radius classical packing convention (disjoint open balls with centers in the
set, prescribed radii `0 < r ≤ δ`, weights `(2r)^s`), the packing dimension of any subset of a
separable metric space equals its countably modified upper box dimension
(`Kolmogorov.PointToSet.packingEqModifiedUpperBox`, blueprint node
`conf:packing-box-interface`).

The inequality "modified box ≤ packing" comes from a maximal separated net: a piece with finite
packing premeasure has covering numbers `N(2r) ≲ r^(-s)`, hence upper box dimension at most `s`
(`upperBoxDimension_le_of_premeasure_lt_top`); a countable cover by such pieces then bounds the
modified box dimension.  The converse groups a packing into dyadic radius shells.  The centers of
one shell are separated, so a fine cover contains at most one of them in each ball, and the shell
mass is bounded by a geometric term (`tsum_shell_le`); the geometric tail tends to zero
(`metricPackingPremeasure_eq_zero_of_upperBoxDimension_lt`).

The theorem is used by the point-to-set principle for packing dimension and by the identification
of the packing dimension with the effective one.  No compactness or doubling assumption is
needed, and the formal diameter `2r` is never replaced by the actual diameter of a ball.
-/

namespace Kolmogorov.PointToSet
open Filter TopologicalSpace
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X]

/-! ### Dyadic radii -/

/-- The dyadic radii decrease. -/
private lemma dyadicRadius_le_dyadicRadius {n m : ℕ} (h : n ≤ m) :
    dyadicRadius m ≤ dyadicRadius n :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

private lemma dyadicRadius_eq_rpow (n : ℕ) : dyadicRadius n = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [dyadicRadius, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg zero_le_two]

/-- Two balls of the dyadic radius `2⁻⁽ⁿ⁺³⁾` together are no wider than the radius `2⁻⁽ⁿ⁺¹⁾`. -/
private lemma dyadicRadius_add_dyadicRadius_le (n : ℕ) :
    dyadicRadius (n + 3) + dyadicRadius (n + 3) ≤ dyadicRadius (n + 1) := by
  unfold dyadicRadius
  have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
  calc (2 : ℝ)⁻¹ ^ (n + 3) + (2 : ℝ)⁻¹ ^ (n + 3) = (2 : ℝ)⁻¹ ^ (n + 1) / 2 := by ring
    _ ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by linarith

/-- The radius `r ∈ (0, 2⁻ᴺ]` lies in a unique dyadic shell `(2⁻⁽ᵏ⁺ᴺ⁺¹⁾, 2⁻⁽ᵏ⁺ᴺ⁾]`; this is
the existence part. -/
private lemma exists_dyadicRadius_shell {r : ℝ} {N : ℕ} (hr : 0 < r) (hrN : r ≤ dyadicRadius N) :
    ∃ k : ℕ, dyadicRadius (k + N + 1) < r ∧ r ≤ dyadicRadius (k + N) := by
  have hN := dyadicRadius_pos N
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near_of_lt_one (x := r / dyadicRadius N) (y := 2⁻¹)
    (div_pos hr hN) ((div_le_one hN).2 hrN) (by norm_num) (by norm_num)
  rw [lt_div_iff₀ hN] at hk₁
  rw [div_le_iff₀ hN] at hk₂
  refine ⟨k, ?_, ?_⟩
  · calc dyadicRadius (k + N + 1) = (2⁻¹ : ℝ) ^ (k + 1) * dyadicRadius N := by
          unfold dyadicRadius; ring
      _ < r := hk₁
  · calc r ≤ (2⁻¹ : ℝ) ^ k * dyadicRadius N := hk₂
      _ = dyadicRadius (k + N) := by unfold dyadicRadius; ring

/-! ### Covering numbers and packings -/

/-- The radius-`ρ` covering number of `Z`: the order-one, zero-potential partition sum, i.e. the
infimum of the cardinalities of countable sets of centers whose open `ρ`-balls cover `Z`. -/
private noncomputable abbrev coverCount (Z : Set X) (ρ : ℝ) : ℝ≥0∞ :=
  partitionSum id (fun _ : X ↦ 0) .centered Z 1 ρ

/-- The covering number is the infimum of the cardinalities of countable covers by open balls. -/
private lemma coverCount_eq_iInf (Z : Set X) (ρ : ℝ) :
    coverCount Z ρ =
      ⨅ C : Set X, ⨅ (_ : C.Countable ∧ Z ⊆ ⋃ x ∈ C, Metric.ball x ρ), (C.encard : ℝ≥0∞) := by
  simp only [coverCount, partitionSum, partitionCoverCost, pressureBallWeight, birkhoffSum,
    bowenBall_id_one, Finset.sum_const_zero, ENNReal.rpow_zero, ENNReal.tsum_set_one]

private lemma coverCount_le_encard {Z C : Set X} {ρ : ℝ} (hC : C.Countable)
    (hcover : Z ⊆ ⋃ x ∈ C, Metric.ball x ρ) : coverCount Z ρ ≤ C.encard := by
  rw [coverCount_eq_iInf]
  exact iInf₂_le C ⟨hC, hcover⟩

/-- The part of a decorated family of balls whose radii lie in `(2⁻⁽ⁿ⁺¹⁾, 2⁻ⁿ]`. -/
private def shell (F : Set (X × ℝ)) (n : ℕ) : Set (X × ℝ) :=
  {a ∈ F | dyadicRadius (n + 1) < a.2 ∧ a.2 ≤ dyadicRadius n}

omit [MetricSpace X] in
/-- Shells of different indices are disjoint. -/
private lemma disjoint_shell (F : Set (X × ℝ)) {n m : ℕ} (h : n < m) :
    Disjoint (shell F n) (shell F m) :=
  Set.disjoint_left.2 fun _ hn hm ↦
    lt_irrefl _
      ((hm.2.2.trans (dyadicRadius_le_dyadicRadius (Nat.succ_le_of_lt h))).trans_lt hn.2.1)

/-- Distinct balls of a shell of a disjoint family have centers further apart than the lower
radius bound of the shell. -/
private lemma dyadicRadius_lt_dist_of_mem_shell {Z : Set X} {F : Set (X × ℝ)}
    (hF : IsDisjointMetricBallFamily Z F) {n : ℕ} {a b : X × ℝ} (ha : a ∈ shell F n)
    (hb : b ∈ shell F n) (hab : a ≠ b) : dyadicRadius (n + 1) < dist a.1 b.1 := by
  by_contra h
  have hpos := dyadicRadius_pos (n + 1)
  exact Set.disjoint_left.mp (hF.2.2 ha.1 hb.1 hab)
    (Metric.mem_ball_self (hpos.trans ha.2.1))
    (Metric.mem_ball.mpr ((not_lt.mp h).trans_lt hb.2.1))

/-- A family in `X` that is separated at the scale `2⁻⁽ⁿ⁺¹⁾` has at most as many members as any
cover of the ambient set by balls of radius `2⁻⁽ⁿ⁺³⁾`. -/
private lemma tsum_one_le_encard_of_separated {S : Type*} {Z : Set X} {n : ℕ} {c : S → X}
    (hcZ : ∀ s, c s ∈ Z) (hsep : ∀ s t, s ≠ t → dyadicRadius (n + 1) < dist (c s) (c t))
    {C : Set X} (hcover : Z ⊆ ⋃ y ∈ C, Metric.ball y (dyadicRadius (n + 3))) :
    ∑' _ : S, (1 : ℝ≥0∞) ≤ C.encard := by
  have hex : ∀ s, ∃ y ∈ C, c s ∈ Metric.ball y (dyadicRadius (n + 3)) := fun s ↦ by
    simpa only [Set.mem_iUnion, exists_prop] using hcover (hcZ s)
  choose f hfC hfball using hex
  have hinj : Function.Injective fun s ↦ (⟨f s, hfC s⟩ : C) := by
    intro s t hst
    by_contra hne
    have hft : f s = f t := congrArg Subtype.val hst
    have hs := hfball s
    rw [hft, Metric.mem_ball] at hs
    have ht := Metric.mem_ball.mp (hfball t)
    have htri := dist_triangle (c s) (f t) (c t)
    rw [dist_comm (f t) (c t)] at htri
    linarith [hsep s t hne, dyadicRadius_add_dyadicRadius_le n]
  calc ∑' _ : S, (1 : ℝ≥0∞) ≤ ∑' _ : C, (1 : ℝ≥0∞) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ ↦ 1
    _ = C.encard := ENNReal.tsum_set_one C

/-- A shell of a packing has at most as many balls as there are centers in a cover of the set by
balls of radius `2⁻⁽ⁿ⁺³⁾`. -/
private lemma tsum_one_shell_le_coverCount {Z : Set X} {F : Set (X × ℝ)}
    (hF : IsDisjointMetricBallFamily Z F) (n : ℕ) :
    ∑' _ : shell F n, (1 : ℝ≥0∞) ≤ coverCount Z (dyadicRadius (n + 3)) := by
  rw [coverCount_eq_iInf]
  refine le_iInf₂ fun C hC ↦ ?_
  exact tsum_one_le_encard_of_separated (c := fun a : shell F n ↦ a.1.1)
    (fun a ↦ (hF.2.1 a.1 a.2.1).1)
    (fun a b hab ↦ dyadicRadius_lt_dist_of_mem_shell hF a.2 b.2 fun h ↦ hab (Subtype.ext h))
    hC.2

/-! ### Zero packing premeasure below the upper box dimension -/

/-- The bound for the `s`-mass of the `n`-th dyadic shell when the cover bound
`N(2⁻⁽ⁿ⁺³⁾) ≤ 2^(t(n+3))` holds. -/
private noncomputable def packingShellBound (s t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ (s + 3 * t)) * ENNReal.ofReal (2 ^ (-(s - t))) ^ n

private lemma real_two_pow_mul_eq (s t : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (t * (n + 3)) * (2 * dyadicRadius n) ^ s =
      2 ^ (s + 3 * t) * ((2 : ℝ) ^ (-(s - t))) ^ n := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have h : 2 * dyadicRadius n = (2 : ℝ) ^ (1 - (n : ℝ)) := by
    rw [dyadicRadius_eq_rpow, sub_eq_add_neg, Real.rpow_add h2, Real.rpow_one]
  rw [h, ← Real.rpow_mul h2.le, ← Real.rpow_natCast, ← Real.rpow_mul h2.le,
    ← Real.rpow_add h2, ← Real.rpow_add h2]
  congr 1
  ring

private lemma ofReal_two_pow_mul_eq_packingShellBound (s t : ℝ) (n : ℕ) :
    ENNReal.ofReal (2 ^ (t * (n + 3))) * ENNReal.ofReal (2 * dyadicRadius n) ^ s =
      packingShellBound s t n := by
  have hpos : 0 < 2 * dyadicRadius n := mul_pos two_pos (dyadicRadius_pos n)
  rw [ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul (by positivity),
    real_two_pow_mul_eq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    packingShellBound]

/-- The `s`-mass of a dyadic shell of a packing is at most `packingShellBound s t n`, provided the
set is covered by `2^(t(n+3))` balls of radius `2⁻⁽ⁿ⁺³⁾`. -/
private lemma tsum_shell_le {Z : Set X} {s t : ℝ} (hts : t < s) (ht : 0 ≤ t) {F : Set (X × ℝ)}
    (hF : IsDisjointMetricBallFamily Z F) (n : ℕ)
    (hcover : coverCount Z (dyadicRadius (n + 3)) ≤ ENNReal.ofReal (2 ^ (t * (n + 3)))) :
    ∑' a : shell F n, ENNReal.ofReal (2 * a.val.2) ^ s ≤ packingShellBound s t n := by
  have hs : 0 ≤ s := by linarith
  calc ∑' a : shell F n, ENNReal.ofReal (2 * a.val.2) ^ s
      ≤ ∑' _ : shell F n, ENNReal.ofReal (2 * dyadicRadius n) ^ s :=
        ENNReal.tsum_le_tsum fun a ↦ ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (by linarith [a.2.2.2])) hs
    _ = (∑' _ : shell F n, (1 : ℝ≥0∞)) * ENNReal.ofReal (2 * dyadicRadius n) ^ s := by
        simp only [ENNReal.tsum_set_const, mul_one]
    _ ≤ ENNReal.ofReal (2 ^ (t * (n + 3))) * ENNReal.ofReal (2 * dyadicRadius n) ^ s := by
        gcongr
        exact (tsum_one_shell_le_coverCount hF n).trans hcover
    _ = packingShellBound s t n := ofReal_two_pow_mul_eq_packingShellBound s t n

/-- A packing with radii below `2⁻ᴺ` is the disjoint union of its dyadic shells of index at least
`N`, so its `s`-mass is the sum of the masses of the shells. -/
private lemma tsum_eq_tsum_shell {Z : Set X} {N : ℕ} {F : Set (X × ℝ)}
    (hF : IsMetricPacking Z (dyadicRadius N) F) (s : ℝ) :
    ∑' a : F, ENNReal.ofReal (2 * a.val.2) ^ s =
      ∑' k : ℕ, ∑' a : shell F (k + N), ENNReal.ofReal (2 * a.val.2) ^ s := by
  have hpart : ∀ a ∈ F, ∃! k : ℕ, a ∈ shell F (k + N) := by
    intro a ha
    obtain ⟨k, hk⟩ := exists_dyadicRadius_shell (hF.1.2.1 a ha).2 (hF.2 a ha)
    refine ⟨k, ⟨ha, hk⟩, fun l hl ↦ ?_⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.mp (disjoint_shell F (by omega : l + N < k + N)) hl ⟨ha, hk⟩
    · exact Set.disjoint_left.mp (disjoint_shell F (by omega : k + N < l + N)) ⟨ha, hk⟩ hl
  have hdisj : Set.univ.PairwiseDisjoint fun k : ℕ ↦ shell F (k + N) := by
    intro k _ l _ hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact disjoint_shell F (by omega)
    · exact (disjoint_shell F (by omega)).symm
  have hunion : (⋃ k : ℕ, shell F (k + N)) = F := by
    ext a
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      exact hk.1
    · obtain ⟨k, hk, _⟩ := hpart a h
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  exact (tsum_congr_set_coe (fun a : X × ℝ ↦ ENNReal.ofReal (2 * a.2) ^ s) hunion.symm).trans
    (ENNReal.tsum_biUnion (f := fun a : X × ℝ ↦ ENNReal.ofReal (2 * a.2) ^ s) hdisj)

/-- The packing content at the cutoff `2⁻ᴺ` is bounded by the sum of the shell bounds from the
index `N` on, provided the covering bounds hold from `N₀ ≤ N` on. -/
private lemma metricPackingContent_le_tsum_packingShellBound {Z : Set X} {s t : ℝ} (hts : t < s)
    (ht : 0 ≤ t) {N₀ : ℕ}
    (hcover : ∀ n ≥ N₀, coverCount Z (dyadicRadius (n + 3)) ≤ ENNReal.ofReal (2 ^ (t * (n + 3))))
    {N : ℕ} (hN : N₀ ≤ N) :
    metricPackingContent Z s (dyadicRadius N) ≤ ∑' k : ℕ, packingShellBound s t (k + N) := by
  unfold metricPackingContent
  refine iSup₂_le fun F hF ↦ ?_
  rw [metricPackingSum, tsum_eq_tsum_shell hF]
  exact ENNReal.tsum_le_tsum fun k ↦ tsum_shell_le hts ht hF.1 (k + N) (hcover _ (by omega))

/-- The geometric series of shell bounds converges. -/
private lemma tsum_packingShellBound_ne_top {s t : ℝ} (hts : t < s) :
    ∑' n, packingShellBound s t n ≠ ⊤ := by
  have hq : ENNReal.ofReal (2 ^ (-(s - t))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  unfold packingShellBound
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  rw [ENNReal.tsum_geometric, ENNReal.inv_ne_top]
  exact (tsub_pos_of_lt hq).ne'

/-! ### Finite packing premeasure bounds the upper box dimension -/

private lemma exists_pos_cutoff_of_premeasure_lt_top {Z : Set X} {s : ℝ}
    (h : metricPackingPremeasure Z s < ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ metricPackingContent Z s δ < ⊤ := by
  unfold metricPackingPremeasure at h
  obtain ⟨δ, hδ⟩ := iInf_lt_iff.mp h
  obtain ⟨hpos, hC⟩ := iInf_lt_iff.mp hδ
  exact ⟨δ, hpos, hC⟩

private lemma bowenDist_id_one (x y : X) : bowenDist id 1 x y = dist x y := by
  simp [bowenDist, Finset.sup_singleton]

/-- A countable family of centers in `Z` that is `2r`-separated, with `r ≤ δ`, gives a packing
by equal balls of radius `r`, so its total mass is at most the packing content. -/
private lemma encard_mul_le_metricPackingContent {Z F : Set X} {s δ r : ℝ} (hr : 0 < r)
    (hrδ : r ≤ δ) (hFZ : F ⊆ Z) (hsep : IsBowenSeparated id 1 (2 * r) F) (hF : F.Countable) :
    (F.encard : ℝ≥0∞) * ENNReal.ofReal (2 * r) ^ s ≤ metricPackingContent Z s δ := by
  set G : Set (X × ℝ) := (fun x ↦ (x, r)) '' F with hG
  have hpack : IsMetricPacking Z δ G := by
    refine ⟨⟨hF.image _, ?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hFZ hx, hr⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
      have hxy : x ≠ y := fun h ↦ hne (by rw [h])
      have hdist : 2 * r ≤ bowenDist id 1 x y := hsep hx hy hxy
      rw [bowenDist_id_one] at hdist
      exact Metric.ball_disjoint_ball (by linarith)
    · rintro _ ⟨x, hx, rfl⟩
      exact hrδ
  have hw : ∀ a : G, ENNReal.ofReal (2 * a.val.2) ^ s = ENNReal.ofReal (2 * r) ^ s := by
    rintro ⟨_, x, _, rfl⟩
    rfl
  have hinj : Function.Injective fun x : X ↦ (x, r) := fun _ _ h ↦ congrArg Prod.fst h
  calc (F.encard : ℝ≥0∞) * ENNReal.ofReal (2 * r) ^ s = metricPackingSum s G := by
        rw [metricPackingSum, tsum_congr hw, ENNReal.tsum_set_const, hG, hinj.encard_image]
    _ ≤ metricPackingContent Z s δ := le_iSup₂_of_le G hpack le_rfl

/-- The dyadic covering numbers are bounded by `C 2^(sn)` from some scale on, if the packing
content bounds the covering numbers `N(2r) ≤ P (2r)^(-s)` at all radii `2r ≤ δ`. -/
private lemma exists_coverCount_dyadic_le {Z : Set X} {s δ : ℝ} (hδ : 0 < δ)
    (hC : metricPackingContent Z s δ < ⊤)
    (H : ∀ r : ℝ, 0 < r → 2 * r ≤ δ →
      coverCount Z (2 * r) ≤ metricPackingContent Z s δ * ENNReal.ofReal (2 * r) ^ (-s)) :
    ∃ (C : ℝ≥0∞) (K : ℕ), C ≠ 0 ∧ C < ⊤ ∧
      ∀ n ≥ K, coverCount Z (dyadicRadius n) ≤ C * 2 ^ (s * n) := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨max (metricPackingContent Z s δ) 1, K, by simp, max_lt hC ENNReal.one_lt_top,
    fun n hn ↦ ?_⟩
  have hpos := dyadicRadius_pos n
  have hle : dyadicRadius n ≤ δ :=
    ((dyadicRadius_le_dyadicRadius hn).trans hK.le : dyadicRadius n ≤ δ)
  have h2 : 2 * (dyadicRadius n / 2) = dyadicRadius n := by ring
  have h := H (dyadicRadius n / 2) (by positivity) (by linarith)
  rw [h2] at h
  have hpow : ENNReal.ofReal (dyadicRadius n) ^ (-s) = 2 ^ (s * n) := by
    rw [dyadicRadius, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ENNReal.inv_rpow,
      ← ENNReal.rpow_neg]
    congr 1
    ring
  rw [hpow] at h
  exact h.trans (by gcongr; exact le_max_left _ _)

/-- A bound `q n ≤ C 2^(sn)` for large `n` gives a bound `s + B/n` for the logarithmic rate. -/
private lemma exists_pressureRate_le {q : ℕ → ℝ≥0∞} {s : ℝ} {C : ℝ≥0∞} (hC0 : C ≠ 0)
    (hCtop : C < ⊤) {K : ℕ} (hq : ∀ n ≥ K, q n ≤ C * 2 ^ (s * n)) :
    ∃ (K' : ℕ) (B : ℝ), ∀ n ≥ K', pressureRate q n ≤ ((B / n + s : ℝ) : EReal) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2 : ENNReal.log 2 = (Real.log 2 : EReal) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.log_ofReal_of_pos two_pos
  refine ⟨max K 1, Real.log C.toReal / Real.log 2, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : ENNReal.log (q n) ≤ ((Real.log C.toReal + s * n * Real.log 2 : ℝ) : EReal) :=
    calc ENNReal.log (q n) ≤ ENNReal.log (C * 2 ^ (s * n)) :=
          ENNReal.log_le_log (hq n ((le_max_left _ _).trans hn))
      _ = ENNReal.log C + ((s * n : ℝ) : EReal) * ENNReal.log 2 := by
          rw [ENNReal.log_mul_add, ENNReal.log_rpow]
      _ = _ := by
          rw [ENNReal.log_pos_real hC0 hCtop.ne, hlog2]
          norm_cast
  have hL' : (0 : EReal) ≤ ((Real.log 2)⁻¹ : ℝ) := EReal.coe_nonneg.mpr (inv_nonneg.mpr hL.le)
  have hn' : (0 : EReal) ≤ ((n : ℝ)⁻¹ : ℝ) := EReal.coe_nonneg.mpr (inv_nonneg.mpr n.cast_nonneg)
  have hn0' : n ≠ 0 := by omega
  simp only [pressureRate, hn0', ↓reduceIte, pressureLog]
  calc ENNReal.log (q n) * ((Real.log 2)⁻¹ : ℝ) * ((n : ℝ)⁻¹ : ℝ)
      ≤ ((Real.log C.toReal + s * n * Real.log 2 : ℝ) : EReal) * ((Real.log 2)⁻¹ : ℝ) *
          ((n : ℝ)⁻¹ : ℝ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlog hL') hn'
    _ = (((Real.log C.toReal + s * n * Real.log 2) * (Real.log 2)⁻¹ * (n : ℝ)⁻¹ : ℝ) : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul]
    _ = ((Real.log C.toReal / Real.log 2 / n + s : ℝ) : EReal) := by
        congr 1
        field_simp

/-- A bound `s + B/n` for the logarithmic rate of covering numbers bounds the upper box
dimension by `s`. -/
private lemma limsup_toENNReal_pressureRate_le {q : ℕ → ℝ≥0∞} {s B : ℝ} {K : ℕ}
    (hq : ∀ n ≥ K, pressureRate q n ≤ ((B / n + s : ℝ) : EReal)) :
    limsup (fun n ↦ (pressureRate q n).toENNReal) atTop ≤ ENNReal.ofReal s := by
  calc limsup (fun n ↦ (pressureRate q n).toENNReal) atTop
      ≤ limsup (fun n : ℕ ↦ ENNReal.ofReal (B / n + s)) atTop := by
        refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [eventually_ge_atTop K] with n hn
        exact EReal.toENNReal_le_toENNReal (hq n hn)
    _ = ENNReal.ofReal s := by
        refine Tendsto.limsup_eq ?_
        have h : Tendsto (fun n : ℕ ↦ B / n + s) atTop (𝓝 (0 + s)) :=
          (tendsto_const_div_atTop_nhds_zero_nat B).add_const s
        rw [zero_add] at h
        exact (ENNReal.continuous_ofReal.tendsto s).comp h

/-- Covering numbers `N(2r) ≤ P (2r)^(-s)` at all small radii bound the upper box dimension
by `s`. -/
private lemma upperBoxDimension_le_of_coverCount_le {Z : Set X} {s δ : ℝ} (hδ : 0 < δ)
    (hC : metricPackingContent Z s δ < ⊤)
    (H : ∀ r : ℝ, 0 < r → 2 * r ≤ δ →
      coverCount Z (2 * r) ≤ metricPackingContent Z s δ * ENNReal.ofReal (2 * r) ^ (-s)) :
    upperBoxDimension Z ≤ ENNReal.ofReal s := by
  obtain ⟨C, K, hC0, hCtop, hbound⟩ := exists_coverCount_dyadic_le hδ hC H
  obtain ⟨K', B, hrate⟩ :=
    exists_pressureRate_le (q := fun n ↦ coverCount Z (dyadicRadius n)) hC0 hCtop hbound
  exact limsup_toENNReal_pressureRate_le hrate

/-- A set of finite packing premeasure in dimension `s` has upper box dimension at most `s`. -/
private lemma upperBoxDimension_le_of_premeasure_lt_top [SeparableSpace X] (Z : Set X) {s : ℝ}
    (hfinite : metricPackingPremeasure Z s < ⊤) : upperBoxDimension Z ≤ ENNReal.ofReal s := by
  obtain ⟨δ, hδ, hC⟩ := exists_pos_cutoff_of_premeasure_lt_top hfinite
  refine upperBoxDimension_le_of_coverCount_le hδ hC fun r hr hrδ ↦ ?_
  obtain ⟨F, hFZ, hsep, hcount, -, hcover⟩ :=
    countableSeparatedMaximalNet id continuous_id Z 1 le_rfl (2 * r) (by linarith)
  have hmass : (F.encard : ℝ≥0∞) * ENNReal.ofReal (2 * r) ^ s ≤ metricPackingContent Z s δ :=
    encard_mul_le_metricPackingContent hr (by linarith) hFZ hsep hcount
  have hpos : ENNReal.ofReal (2 * r) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  calc coverCount Z (2 * r) ≤ F.encard :=
        coverCount_le_encard hcount (by simpa only [bowenBall_id_one] using hcover)
    _ = F.encard * ENNReal.ofReal (2 * r) ^ s * ENNReal.ofReal (2 * r) ^ (-s) := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hpos ENNReal.ofReal_ne_top, add_neg_cancel,
          ENNReal.rpow_zero, mul_one]
    _ ≤ metricPackingContent Z s δ * ENNReal.ofReal (2 * r) ^ (-s) := by gcongr

/-! ### From the upper box dimension to covering numbers -/

/-- If the logarithmic rate of `q k` is below `t`, then `q k ≤ 2^(tk)`. -/
private lemma le_ofReal_rpow_of_pressureRate_lt {q : ℕ → ℝ≥0∞} {t : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h : (pressureRate q k).toENNReal < ENNReal.ofReal t) : q k ≤ ENNReal.ofReal (2 ^ (t * k)) := by
  have hk0 : k ≠ 0 := by omega
  have hle : pressureRate q k ≤ (t : EReal) := by
    by_contra hcont
    exact absurd (EReal.toENNReal_le_toENNReal (not_le.mp hcont).le) (not_le.mpr h)
  have hr : ENNReal.log (q k) * (((Real.log 2)⁻¹ * (k : ℝ)⁻¹ : ℝ) : EReal) ≤ t := by
    simpa only [pressureRate, ite_eq_right hk0, pressureLog, mul_assoc, ← EReal.coe_mul]
      using hle
  apply ENNReal.log_strictMono.le_iff_le.mp
  calc ENNReal.log (q k)
      = (ENNReal.log (q k) * (((Real.log 2)⁻¹ * (k : ℝ)⁻¹ : ℝ) : EReal)) *
          (((k : ℝ) * Real.log 2 : ℝ) : EReal) := by
        rw [mul_assoc, ← EReal.coe_mul]
        have he : (Real.log 2)⁻¹ * (k : ℝ)⁻¹ * ((k : ℝ) * Real.log 2) = 1 := by
          have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
          have hnR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
          field_simp
        rw [he, EReal.coe_one, mul_one]
    _ ≤ (t : EReal) * (((k : ℝ) * Real.log 2 : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_right hr (EReal.coe_nonneg.mpr
          (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)))
    _ = ENNReal.log (ENNReal.ofReal (2 ^ (t * k))) := by
        have hpow : (0 : ℝ) < 2 ^ (t * k) := Real.rpow_pos_of_pos two_pos _
        rw [ENNReal.log_ofReal, ite_eq_right (not_le.mpr hpow), ← EReal.coe_mul]
        congr 1
        rw [Real.log_rpow two_pos]
        ring

/-- Below an upper box dimension bound `t`, the covering numbers at the radii `2⁻⁽ⁿ⁺³⁾` are
eventually at most `2^(t(n+3))`. -/
private lemma eventually_coverCount_le_of_upperBoxDimension_lt {Z : Set X} {t : ℝ}
    (hbox : upperBoxDimension Z < ENNReal.ofReal t) :
    ∃ N : ℕ, ∀ n ≥ N,
      coverCount Z (dyadicRadius (n + 3)) ≤ ENNReal.ofReal (2 ^ (t * (n + 3))) := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hbox)
  refine ⟨K, fun n hn ↦ ?_⟩
  have h := le_ofReal_rpow_of_pressureRate_lt
    (q := fun m ↦ coverCount Z (dyadicRadius m)) (k := n + 3) (by omega) (hK (n + 3) (by omega))
  push_cast at h
  exact h

/-- An upper box dimension below `t < s` forces zero packing premeasure in dimension `s`: the
packing is cut into dyadic shells whose masses form a convergent geometric series. -/
private lemma metricPackingPremeasure_eq_zero_of_upperBoxDimension_lt {Z : Set X} {t s : ℝ}
    (ht : 0 ≤ t) (hts : t < s) (hbox : upperBoxDimension Z < ENNReal.ofReal t) :
    metricPackingPremeasure Z s = 0 := by
  obtain ⟨N₀, hN₀⟩ := eventually_coverCount_le_of_upperBoxDimension_lt hbox
  refine le_antisymm ?_ zero_le
  refine ge_of_tendsto (ENNReal.tendsto_sum_nat_add (packingShellBound s t)
    (tsum_packingShellBound_ne_top hts)) ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  calc metricPackingPremeasure Z s ≤ metricPackingContent Z s (dyadicRadius N) :=
        iInf₂_le (f := fun δ (_ : 0 < δ) ↦ metricPackingContent Z s δ) _ (dyadicRadius_pos N)
    _ ≤ _ := metricPackingContent_le_tsum_packingShellBound hts ht hN₀ hN

/-! ### Packing dimension equals modified upper box dimension -/

/-- A zero packing outer measure gives a countable cover by sets of finite packing premeasure. -/
private lemma exists_cover_premeasure_lt_top {Z : Set X} {s : ℝ}
    (hzero : metricPackingOuterMeasure Z s = 0) :
    ∃ Y : ℕ → Set X, Z ⊆ ⋃ j, Y j ∧ ∀ j, metricPackingPremeasure (Y j) s < ⊤ := by
  have h : metricPackingOuterMeasure Z s < 1 := by
    rw [hzero]
    exact zero_lt_one
  unfold metricPackingOuterMeasure at h
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp h
  obtain ⟨hZ, hsum⟩ := iInf_lt_iff.mp hY
  exact ⟨Y, hZ, fun j ↦ (ENNReal.le_tsum j).trans_lt (hsum.trans ENNReal.one_lt_top)⟩

/-- A zero packing outer measure in dimension `s` bounds the modified upper box dimension by `s`. -/
private lemma modifiedUpperBoxDimension_le_of_outerMeasure_eq_zero [SeparableSpace X]
    (Z : Set X) {s : ℝ} (hzero : metricPackingOuterMeasure Z s = 0) :
    modifiedUpperBoxDimension Z ≤ ENNReal.ofReal s := by
  obtain ⟨Y, hcover, hfinite⟩ := exists_cover_premeasure_lt_top hzero
  unfold modifiedUpperBoxDimension
  exact (iInf₂_le Y hcover).trans
    (iSup_le fun j ↦ upperBoxDimension_le_of_premeasure_lt_top (Y j) (hfinite j))

/-- A modified upper box dimension below `t < s` gives zero packing outer measure in dimension
`s`. -/
private lemma metricPackingOuterMeasure_eq_zero_of_modifiedUpperBoxDimension_lt {Z : Set X}
    {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    (hmod : modifiedUpperBoxDimension Z < ENNReal.ofReal t) :
    metricPackingOuterMeasure Z s = 0 := by
  unfold modifiedUpperBoxDimension at hmod
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp hmod
  obtain ⟨hcover, hsup⟩ := iInf_lt_iff.mp hY
  have hzero : ∀ j, metricPackingPremeasure (Y j) s = 0 := fun j ↦
    metricPackingPremeasure_eq_zero_of_upperBoxDimension_lt ht hts
      ((le_iSup (fun j ↦ upperBoxDimension (Y j)) j).trans_lt hsup)
  refine le_antisymm ?_ bot_le
  calc metricPackingOuterMeasure Z s ≤ ∑' j, metricPackingPremeasure (Y j) s := iInf₂_le Y hcover
    _ = 0 := by simp only [hzero, tsum_zero]

/-- Below any bound `u` exceeding the modified upper box dimension there is a dimension `s < u`
with zero packing outer measure. -/
private lemma exists_outerMeasure_eq_zero_ofReal_lt {Z : Set X} {u : ℝ≥0∞}
    (hmod : modifiedUpperBoxDimension Z < u) :
    ∃ s : ℝ, 0 ≤ s ∧ metricPackingOuterMeasure Z s = 0 ∧ ENNReal.ofReal s < u := by
  obtain ⟨t, ht, hmt, htu⟩ := ENNReal.lt_iff_exists_real_btwn.mp hmod
  obtain ⟨s, hs, hts, hsu⟩ := ENNReal.lt_iff_exists_real_btwn.mp htu
  exact ⟨s, hs, metricPackingOuterMeasure_eq_zero_of_modifiedUpperBoxDimension_lt ht
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp hts) hmt, hsu⟩

/-- Specified-radius packing dimension equals countably modified upper box dimension
on every separable metric space. Blueprint node `conf:packing-box-interface`. -/
theorem packingEqModifiedUpperBox [SeparableSpace X] (Z : Set X) :
    metricPackingDimension Z = modifiedUpperBoxDimension Z := by
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun u hu ↦ ?_) ?_
  · obtain ⟨s, hs, hzero, hsu⟩ := exists_outerMeasure_eq_zero_ofReal_lt hu
    refine le_trans ?_ hsu.le
    unfold metricPackingDimension
    exact iInf_le_of_le s (iInf_le_of_le hs (iInf_le _ hzero))
  · unfold metricPackingDimension
    exact le_iInf fun s ↦ le_iInf fun _ ↦ le_iInf fun hzero ↦
      modifiedUpperBoxDimension_le_of_outerMeasure_eq_zero Z hzero

end Kolmogorov.PointToSet
