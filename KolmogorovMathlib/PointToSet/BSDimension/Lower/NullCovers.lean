/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Lower.MassDichotomy

/-!
# Null covers and the lower Barreira–Schmeling dimension

A *null `s`-cover* of a set `Z` is a set `E` of triples `(i, n, p)` of finite total
center-weight mass `∑ 2 ^ (-s * S_n u (ι i))` such that, for every dyadic scale `p` and every
order cutoff `k`, each point of `Z` lies in the Bowen ball of order `n ≥ max 1 k` around `ι i`
for some triple `(i, n, p) ∈ E` (`IsNullBSCover`).  This module relates null covers to the
classical lower Barreira–Schmeling dimension and to its effective version.

* `nullCoverBoundsLowerBS` (blueprint node `bs:null-lower`): a null `s`-cover bounds the lower
  dimension by `s`.
* `lowerBSNullCoverCharacterization` and `lowerBSNullCoverCharacterization_iInf` (blueprint
  node `bs:null-construction`): conversely, every finite `s` above the lower dimension admits a
  null `s`-cover, so the lower dimension is the infimum of the exponents of null covers.
* `effectiveBSDimensions_ge` and `effectiveBSDimensions_null_upward` (blueprint node
  `bs:effective`): the effective lower dimension bounds the classical one, and null covers of
  positive exponent persist at larger exponents.
* `effectiveLowerBSLeSup` (blueprint node `bs:effective-lower-upper`): the Kraft construction of
  an oracle-enumerable null cover bounds the effective lower dimension by the supremum of the
  pointwise dimensions.

The point-to-set principle for the lower Barreira–Schmeling dimension in
`KolmogorovMathlib.PointToSet.BSDimension.Lower.EffectiveEqSup` combines these bounds.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- Nonpositive powers reverse the order on `ℝ≥0∞`. -/
private lemma rpow_le_rpow_of_nonpos_ennreal {x y : ℝ≥0∞} {z : ℝ} (hz : z ≤ 0) (hxy : x ≤ y) :
    y ^ z ≤ x ^ z := by
  rw [← neg_neg z, ENNReal.rpow_neg y, ENNReal.rpow_neg x]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hxy (neg_nonneg.mpr hz))

/-- The mass of a set of triples is the sum of the weights `2 ^ (-s * S_n u (ι i))` of its
elements. -/
private lemma nullBSMass_eq_tsum (P : Presentation X) (T : X → X) (u : X → ℝ) (s : ℝ)
    (E : Set (ℕ × ℕ × ℕ)) :
    nullBSMass P T u s E =
      ∑' t : E, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u t.val.2.1 (P.ι t.val.1)) := by
  simp only [nullBSMass, nullPressureMass, neg_zero, zero_mul, zero_add, birkhoffSum,
    Finset.mul_sum]

/-- The mass of a union of sets of triples is at most the sum of the masses. -/
private lemma nullBSMass_iUnion_le {ι : Type*} (P : Presentation X) (T : X → X) (u : X → ℝ)
    (s : ℝ) (E : ι → Set (ℕ × ℕ × ℕ)) :
    nullBSMass P T u s (⋃ i, E i) ≤ ∑' i, nullBSMass P T u s (E i) := by
  simp only [nullBSMass_eq_tsum]
  exact ENNReal.tsum_iUnion_le_tsum
    (fun t : ℕ × ℕ × ℕ ↦ (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u t.2.1 (P.ι t.1))) E

/-- For `s ≥ 0`, the supremum weight of a Bowen ball is bounded by the weight at its center. -/
private lemma bsBallWeight_le_center (T : X → X) (u : X → ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℕ)
    (x : X) {r : ℝ} (hr : 0 < r) :
    bsBallWeight T u s n x r ≤ (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n x) := by
  have hx : x ∈ bowenBall T n x r := mem_bowenBall_iff.2 fun k _ ↦ by simpa using hr
  have hle : (2 : ℝ≥0∞) ^ birkhoffSum T u n x ≤ pressureBallWeight T u .supremum n x r :=
    le_iSup₂ (f := fun z _ ↦ (2 : ℝ≥0∞) ^ birkhoffSum T u n z) x hx
  calc
    bsBallWeight T u s n x r ≤ ((2 : ℝ≥0∞) ^ birkhoffSum T u n x) ^ (-s) :=
      rpow_le_rpow_of_nonpos_ennreal (neg_nonpos.mpr hs) hle
    _ = (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u n x) := by
      rw [← ENNReal.rpow_mul, mul_comm]

/-- The family of Bowen balls of order `n ≥ max 1 k` around the ideal points `ι i` for the
triples `(i, n, p)` of `E` with the given scale code `p`; the pair `(i, n)` is stored under
the index `Nat.pair i n`. -/
private noncomputable def nullCoverFamily (P : Presentation X) (E : Set (ℕ × ℕ × ℕ))
    (p k : ℕ) : BowenCoverFamily X where
  index := {t : ℕ | ∃ i n : ℕ, t = Nat.pair i n ∧ (i, n, p) ∈ E ∧ max 1 k ≤ n}
  order := fun t ↦ (Nat.unpair t.val).2
  center := fun t ↦ P.ι (Nat.unpair t.val).1

/-- The balls of the family built from a null cover cover the set at the scale `p`. -/
private lemma isBowenCover_nullCoverFamily (P : Presentation X) (T : X → X) (u : X → ℝ)
    (Z : Set X) (s : ℝ) (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullBSCover P T u Z s E) (p k : ℕ) :
    IsBowenCover T Z (dyadicRadius p) k (nullCoverFamily P E p k) := by
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rintro ⟨_, i, n, rfl, -, hn⟩
    simpa only [nullCoverFamily, Nat.unpair_pair] using hn
  · obtain ⟨i, n, hn, hmem, hball⟩ := hE.2 p k x hx
    refine Set.mem_iUnion.2 ⟨⟨Nat.pair i n, i, n, rfl, hmem, hn⟩, ?_⟩
    simpa only [nullCoverFamily, Nat.unpair_pair] using hball

/-- The cost of the family built from a null cover is bounded by the mass of the cover. -/
private lemma bsCoverCost_nullCoverFamily_le (P : Presentation X) (T : X → X) (u : X → ℝ)
    {s : ℝ} (hs : 0 ≤ s) (E : Set (ℕ × ℕ × ℕ)) (p k : ℕ) :
    bsCoverCost T u s (dyadicRadius p) (nullCoverFamily P E p k) ≤ nullBSMass P T u s E := by
  have hmem : ∀ j : (nullCoverFamily P E p k).index,
      ((Nat.unpair j.val).1, (Nat.unpair j.val).2, p) ∈ E := by
    rintro ⟨_, i, n, rfl, h, -⟩
    simpa only [Nat.unpair_pair] using h
  let f : (nullCoverFamily P E p k).index → E := fun j ↦ ⟨_, hmem j⟩
  have hf : Function.Injective f := by
    intro j₁ j₂ h
    have h' := congrArg Subtype.val h
    simp only [f, Prod.mk.injEq, and_true] at h'
    refine Subtype.ext ?_
    calc
      j₁.val = Nat.pair (Nat.unpair j₁.val).1 (Nat.unpair j₁.val).2 := (Nat.pair_unpair _).symm
      _ = Nat.pair (Nat.unpair j₂.val).1 (Nat.unpair j₂.val).2 := by rw [h'.1, h'.2]
      _ = j₂.val := Nat.pair_unpair _
  rw [nullBSMass_eq_tsum]
  calc
    bsCoverCost T u s (dyadicRadius p) (nullCoverFamily P E p k)
        ≤ ∑' j : (nullCoverFamily P E p k).index, (2 : ℝ≥0∞) ^
            (-s * birkhoffSum T u (Nat.unpair j.val).2 (P.ι (Nat.unpair j.val).1)) :=
      ENNReal.tsum_le_tsum fun j ↦ bsBallWeight_le_center T u hs _ _ (dyadicRadius_pos p)
    _ ≤ ∑' t : E, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u t.val.2.1 (P.ι t.val.1)) :=
      ENNReal.tsum_comp_le_tsum_of_injective hf
        (fun t : E ↦ (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u t.val.2.1 (P.ι t.val.1)))

/-- A null cover bounds the lower mass at every scale and every order cutoff. -/
private lemma lowerBSMass_le_nullBSMass (P : Presentation X) (T : X → X) (u : X → ℝ)
    (Z : Set X) {s : ℝ} (hs : 0 ≤ s) (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullBSCover P T u Z s E)
    (p N : ℕ) : lowerBSMass T u Z s (dyadicRadius p) N ≤ nullBSMass P T u s E :=
  (iInf_le _ (nullCoverFamily P E p N)).trans <|
    (iInf_le _ (isBowenCover_nullCoverFamily P T u Z s E hE p N)).trans <|
      bsCoverCost_nullCoverFamily_le P T u hs E p N

/-- A null witness bounds classical lower dimension on the positive-average locus.
Blueprint node `bs:null-lower`. -/
theorem nullCoverBoundsLowerBS (P : Presentation X) (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (s : ℝ) (hs : 0 ≤ s) (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullBSCover P T u Z s E) :
    lowerBSDimension T u Z ≤ ENNReal.ofReal s := by
  refine iSup_le fun p ↦ ?_
  by_contra hlt
  have htop := lowerBSDichotomy_top T u Z hZ s (dyadicRadius p) hs
    (not_le.mp hlt)
  have hfin : lowerBSMassLimit T u Z s (dyadicRadius p) < ⊤ :=
    (iSup_le fun N ↦ iSup_le fun _ ↦ lowerBSMass_le_nullBSMass P T u Z hs E hE p N).trans_lt hE.1
  rw [htop] at hfin
  exact lt_irrefl _ hfin

/-- Some dyadic radius `dyadicRadius q` has double at most `dyadicRadius p` and, at that
radius, all Birkhoff suprema over Bowen balls are finite.  Uniform continuity of `u` is only
used at this smaller radius. -/
theorem exists_dyadicRadius_double_le_finite_bowenPotentialSup
    (T : X → X) (u : X → ℝ) (hu : UniformContinuous u) (p : ℕ) :
    ∃ q : ℕ, 2 * dyadicRadius q ≤ dyadicRadius p ∧
      ∀ n : ℕ, ∀ y : X, ∃ w : ℝ,
        bowenPotentialSup T u n y (dyadicRadius q) = (w : EReal) := by
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp hu 1 zero_lt_one
  obtain ⟨q, hq⟩ := exists_dyadicRadius_lt
    (lt_min hδ (half_pos (dyadicRadius_pos p)))
  refine ⟨q, ?_, fun n y ↦ ?_⟩
  · linarith [hq.trans_le (min_le_right _ _)]
  · have hω : ∀ z v : X, dist z v < dyadicRadius q → |u z - u v| ≤ 1 := fun z v hzv ↦
      (hosc (hzv.trans (hq.trans_le (min_le_left _ _)))).le
    have hupper : bowenPotentialSup T u n y (dyadicRadius q) ≤
        ((birkhoffSum T u n y + n * 1 : ℝ) : EReal) :=
      iSup₂_le fun z hz ↦
        EReal.coe_le_coe_iff.mpr (birkhoffSum_le_add_of_mem_bowenBall T u hω hz)
    have hy : y ∈ bowenBall T n y (dyadicRadius q) :=
      mem_bowenBall_iff.2 fun k _ ↦ by simpa using dyadicRadius_pos q
    have hlower : ((birkhoffSum T u n y : ℝ) : EReal) ≤
        bowenPotentialSup T u n y (dyadicRadius q) :=
      le_iSup₂ (f := fun z _ ↦ ((birkhoffSum T u n z : ℝ) : EReal)) y hy
    exact ⟨(bowenPotentialSup T u n y (dyadicRadius q)).toReal,
      (EReal.coe_toReal (ne_top_of_lt (hupper.trans_lt (EReal.coe_lt_top _)))
        (ne_bot_of_gt ((EReal.bot_lt_coe _).trans_le hlower))).symm⟩

/-- At a fixed dyadic scale below the lower dimension bound `s`, every order cutoff admits a
Bowen cover of arbitrarily small positive cost. -/
private lemma exists_bowenCover_cost_lt (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s : ℝ)
    (hlt : lowerBSDimension T u Z < ENNReal.ofReal s) (q N : ℕ) (hN : 1 ≤ N)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ C : BowenCoverFamily X, IsBowenCover T Z (dyadicRadius q) N C ∧
      bsCoverCost T u s (dyadicRadius q) C < ε := by
  have hdim : lowerBSDimensionAt T u Z (dyadicRadius q) < ENNReal.ofReal s :=
    (le_iSup (fun p ↦ lowerBSDimensionAt T u Z (dyadicRadius p)) q).trans_lt hlt
  have hzero := lowerBSDichotomy_zero T u Z hZ s (dyadicRadius q)
    hdim
  have hmass : lowerBSMass T u Z s (dyadicRadius q) N < ε := by
    refine lt_of_le_of_lt ?_ hε
    rw [← hzero]
    exact le_iSup_of_le N (le_iSup_of_le hN le_rfl)
  simpa only [lowerBSMass, iInf_lt_iff, exists_prop] using hmass

/-- Recentering a Bowen cover whose Birkhoff suprema are finite at ideal points: its balls
are encoded by pairwise distinct triples whose center-weight mass is at most `2 ^ s` times
the cost of the cover, and which cover `Z` at the coarser scale `p` whenever `2 * r` is at
most the radius of scale `p`. -/
private lemma exists_triples_of_bowenCover (P : Presentation X) (T : X → X) (hT : Continuous T)
    (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (p N : ℕ)
    (hscale : 2 * r ≤ dyadicRadius p) (C : BowenCoverFamily X) (hC : IsBowenCover T Z r N C)
    (hfinite : ∀ j : C.index, ∃ w : ℝ,
      bowenPotentialSup T u (C.order j) (C.center j) r = (w : EReal)) :
    ∃ E : Set (ℕ × ℕ × ℕ),
      nullBSMass P T u s E ≤ (2 : ℝ≥0∞) ^ s * bsCoverCost T u s r C ∧
      ∀ x ∈ Z, ∃ i n, max 1 N ≤ n ∧ (i, n, p) ∈ E ∧
        x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  classical
  choose w hw using hfinite
  have hcenters : ∀ j : C.index, ∃ i : ℕ,
      w j - 1 < birkhoffSum T u (C.order j) (P.ι i) ∧
      bowenBall T (C.order j) (C.center j) r ⊆
        bowenBall T (C.order j) (P.ι i) (2 * r) := by
    intro j
    obtain ⟨i, _, hi, hsub⟩ := recenterNearBirkhoffSupremum P T hT u hu
      (C.order j) (C.center j) r
      (w j) (hw j) 1 zero_lt_one
    exact ⟨i, hi, hsub⟩
  choose i hi hsub using hcenters
  let f : C.index → ℕ × ℕ × ℕ := fun j ↦ (i j, C.order j, p)
  refine ⟨Set.range f, ?_, fun x hx ↦ ?_⟩
  · rw [nullBSMass_eq_tsum]
    calc
      _ ≤ ∑' j : C.index, (2 : ℝ≥0∞) ^ (-s * birkhoffSum T u (C.order j) (P.ι (i j))) :=
        ENNReal.tsum_le_tsum_comp_of_surjective
          (f := fun j ↦ (⟨f j, Set.mem_range_self j⟩ : Set.range f))
          (by rintro ⟨t, j, rfl⟩; exact ⟨j, rfl⟩) _
      _ ≤ ∑' j : C.index, (2 : ℝ≥0∞) ^ s *
          bsBallWeight T u s (C.order j) (C.center j) r := by
        refine ENNReal.tsum_le_tsum fun j ↦ ?_
        rw [lowerBSMass_weight T u s (C.order j) (C.center j) r (w j) (hw j),
          ← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
        refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        nlinarith [mul_le_mul_of_nonneg_left (hi j).le hs]
      _ = (2 : ℝ≥0∞) ^ s * bsCoverCost T u s r C := ENNReal.tsum_mul_left
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hC.2 hx)
    exact ⟨i j, C.order j, hC.1 j, Set.mem_range_self j,
      bowenBall_subset_of_le T (C.order j) (P.ι (i j)) hscale (hsub j hj)⟩

/-- The geometric budgets `2 ^ s * (1 / 2) ^ (p + N + 2)` over all scales `p` and cutoffs `N`
have finite total. -/
private lemma tsum_tsum_two_rpow_mul_inv_pow_lt_top (s : ℝ) (hs : 0 ≤ s) :
    (∑' p : ℕ, ∑' N : ℕ, (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ (p + N + 2)) < ⊤ := by
  have hterm : ∀ p N : ℕ, (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ (p + N + 2) =
      ((2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ p) * (2 : ℝ≥0∞)⁻¹ ^ N := by
    intro p N
    rw [pow_add, pow_add]
    ring
  simp only [hterm, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have hgeom : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n) < ⊤ := tsum_geometric_lt_top.mpr (by norm_num)
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hs (by norm_num))
      (ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr two_pos))) hgeom) hgeom

/-- Every finite exponent strictly above lower dimension has a classical null witness.
Blueprint node `bs:null-construction`. -/
theorem lowerBSNullCoverCharacterization (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (s : ℝ) (hs : 0 ≤ s)
    (hlt : lowerBSDimension T u Z < ENNReal.ofReal s) :
    ∃ E : Set (ℕ × ℕ × ℕ), IsNullBSCover P T u Z s E := by
  classical
  choose q hscale hfinite using
    exists_dyadicRadius_double_le_finite_bowenPotentialSup T u hu
  have hpieces : ∀ p N : ℕ, ∃ E : Set (ℕ × ℕ × ℕ),
      nullBSMass P T u s E ≤ (2 : ℝ≥0∞) ^ s * (2 : ℝ≥0∞)⁻¹ ^ (p + N + 2) ∧
      ∀ x ∈ Z, ∃ i n, max 1 N ≤ n ∧ (i, n, p) ∈ E ∧
        x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
    intro p N
    have hbudget : 0 < (2 : ℝ≥0∞)⁻¹ ^ (p + N + 2) :=
      bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
    obtain ⟨C, hC, hcost⟩ := exists_bowenCover_cost_lt T u Z hZ s hlt (q p)
      (max 1 N) (le_max_left _ _) ((2 : ℝ≥0∞)⁻¹ ^ (p + N + 2)) hbudget
    have hC' : IsBowenCover T Z (dyadicRadius (q p)) N C := by
      simpa only [IsBowenCover, ← max_assoc, max_self] using hC
    obtain ⟨E, hmass, hcover⟩ := exists_triples_of_bowenCover P T hT u hu Z s hs
      (dyadicRadius (q p)) p N (hscale p) C hC'
      (fun j ↦ hfinite p (C.order j) (C.center j))
    exact ⟨E, hmass.trans (mul_le_mul_right hcost.le _), hcover⟩
  choose E hmass hcover using hpieces
  refine ⟨⋃ p, ⋃ N, E p N, ?_, fun p k x hx ↦ ?_⟩
  · have hsub : nullBSMass P T u s (⋃ p, ⋃ N, E p N) ≤
        ∑' p : ℕ, ∑' N : ℕ, nullBSMass P T u s (E p N) :=
      (nullBSMass_iUnion_le P T u s _).trans <|
        ENNReal.tsum_le_tsum fun p ↦ nullBSMass_iUnion_le P T u s _
    exact hsub.trans_lt <|
      (ENNReal.tsum_le_tsum fun p ↦ ENNReal.tsum_le_tsum (hmass p)).trans_lt
        (tsum_tsum_two_rpow_mul_inv_pow_lt_top s hs)
  · obtain ⟨i, n, hn, ht, hball⟩ := hcover p k x hx
    exact ⟨i, n, hn, Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨k, ht⟩⟩, hball⟩

/-- Lower dimension is the nonnegative infimum of null-witness exponents.
Blueprint node `bs:null-construction`. -/
theorem lowerBSNullCoverCharacterization_iInf (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (hu : UniformContinuous u) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    lowerBSDimension T u Z = ⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ E : Set (ℕ × ℕ × ℕ),
      ⨅ (_ : IsNullBSCover P T u Z s E), ENNReal.ofReal s := by
  refine le_antisymm
    (le_iInf₂ fun s hs ↦ le_iInf₂ fun E hE ↦ nullCoverBoundsLowerBS P T u Z hZ s hs E hE) ?_
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  rcases eq_or_ne a ⊤ with rfl | hne
  · exact le_top
  rw [← ENNReal.ofReal_toReal hne] at ha ⊢
  obtain ⟨E, hE⟩ := lowerBSNullCoverCharacterization P T hT u hu Z hZ a.toReal
    ENNReal.toReal_nonneg ha
  exact iInf₂_le_of_le a.toReal ENNReal.toReal_nonneg (iInf₂_le_of_le E hE le_rfl)

/-- The effective lower dimension bounds classical lower dimension.
Blueprint node `bs:effective`. -/
theorem effectiveBSDimensions_ge (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
    (hu : UniformContinuous u) (A : Set ℕ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    lowerBSDimension T u Z ≤ effectiveLowerBSDimension P T u A Z := by
  rw [lowerBSNullCoverCharacterization_iInf P T hT u hu Z hZ]
  exact iInf_mono fun s ↦ iInf_mono fun hs ↦ iInf_mono fun E ↦
    iInf_mono' fun hE ↦ ⟨hE.1, le_rfl⟩

/-- Positive-exponent null witnesses remain witnesses at larger exponents even when
finitely many of their Birkhoff sums are nonpositive. Blueprint node `bs:effective`. -/
theorem effectiveBSDimensions_null_upward (P : Presentation X) (T : X → X)
    (u : X → ℝ) (Z : Set X) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (E : Set (ℕ × ℕ × ℕ)) (hE : IsNullBSCover P T u Z s E) :
    IsNullBSCover P T u Z t E := by
  classical
  refine ⟨?_, hE.2⟩
  let U : E → ℝ := fun a ↦ birkhoffSum T u a.val.2.1 (P.ι a.val.1)
  let w : ℝ → E → ℝ≥0∞ := fun r a ↦ (2 : ℝ≥0∞) ^ (-r * U a)
  have hmass_eq (r : ℝ) : nullBSMass P T u r E = ∑' a : E, w r a :=
    nullBSMass_eq_tsum P T u r E
  have hmass : (∑' a : E, w s a) < ⊤ := by
    rw [← hmass_eq]
    exact hE.1
  -- Every nonpositive sum contributes at least one to the original finite mass.
  have hbad : {a : E | U a ≤ 0}.Finite := by
    refine (ENNReal.finite_const_le_of_tsum_ne_top hmass.ne
      (by norm_num : (1 : ℝ≥0∞) ≠ 0)).subset fun a ha ↦ ?_
    calc
      1 = (2 : ℝ≥0∞) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
      _ ≤ (2 : ℝ≥0∞) ^ (-s * U a) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hs.le) ha)
  let F : Finset E := hbad.toFinset
  have hfinite : (∑ a ∈ F, w t a) < ⊤ :=
    ENNReal.sum_lt_top.mpr fun a _ ↦
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
  -- Outside the finite exceptional set, increasing the exponent decreases the weight.
  have htail : (∑' a : ↥(F : Set E)ᶜ, w t a.val) ≤ ∑' a : E, w s a := by
    calc
      (∑' a : ↥(F : Set E)ᶜ, w t a.val) ≤ ∑' a : ↥(F : Set E)ᶜ, w s a.val := by
        refine ENNReal.tsum_le_tsum fun a ↦ ?_
        have ha : 0 ≤ U a.val :=
          (lt_of_not_ge fun hle ↦ a.property (hbad.mem_toFinset.mpr hle)).le
        exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (neg_le_neg hst) ha)
      _ ≤ ∑' a : E, w s a :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (w s)
  rw [hmass_eq, ← ENNReal.sum_add_tsum_compl F (w t)]
  exact ENNReal.add_lt_top.mpr ⟨hfinite, htail.trans_lt hmass⟩

/-- The explicit set of triples `(i, n, p)` with `n ≥ 1` whose code has oracle complexity
below `s * S_n u (ι i)`; this is the null cover built by the Kraft construction. -/
private def kraftThresholdSet (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (s : ℚ) : Set (ℕ × ℕ × ℕ) :=
  {t | 1 ≤ t.2.1 ∧ (oracleNatComplexity A (Encodable.encode t) : ℝ) <
    (s : ℝ) * birkhoffSum T u t.2.1 (P.ι t.1)}

/-- For an admissible oracle `A` and a positive rational exponent `s`, the threshold set is
enumerable in `A`.  The exponent is rational, so no oracle for an arbitrary real threshold is
needed. -/
private lemma isREIn_kraftThresholdSet (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (hA : IsAdmissible P T (fun _ : Fin 1 => u) A)
    (s : ℚ) (hs : 0 < s) :
    IsREIn A (kraftThresholdSet P T u A s) := by
  let D : BitString → ℕ × ℕ × ℕ := fun w ↦
    (Encodable.decode (decodeBits w)).getD (0, 0, 0)
  let g : BitString → ℝ := fun w ↦
    (s : ℝ) * birkhoffSum T u (D w).2.1 (P.ι (D w).1)
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hD : Computable D := Computable.option_getD
    (Computable.decode.comp decodeBits_computable) (Computable.const (0, 0, 0))
  have hindex : Computable (fun w : BitString ↦
      ((0 : Fin 1), (D w).2.1, (D w).1)) :=
    (Computable.const (0 : Fin 1)).pair
      ((Computable.fst.comp (Computable.snd.comp hD)).pair (Computable.fst.comp hD))
  have harg : Computable (fun wq : BitString × ℚ ↦
      (((0 : Fin 1), (D wq.1).2.1, (D wq.1).1), wq.2 * s⁻¹)) :=
    (hindex.comp Computable.fst).pair
      (computable₂_ratMul.comp Computable.snd (Computable.const s⁻¹))
  have hg : IsLowerSemicomputableIn A g := by
    obtain ⟨f, hf, hdom⟩ := birkhoff_computableIn_gt A _
      (birkhoff_computableIn P T (fun _ : Fin 1 => u) A hA)
    refine ⟨fun wq ↦ f (((0 : Fin 1), (D wq.1).2.1, (D wq.1).1), wq.2 * s⁻¹),
      hf.comp harg.computableIn, fun wq ↦ ?_⟩
    rw [← hdom]
    change (wq.2 : ℝ) < (s : ℝ) * birkhoffSum T u (D wq.1).2.1 (P.ι (D wq.1).1) ↔
      ((wq.2 * s⁻¹ : ℚ) : ℝ) < birkhoffSum T u (D wq.1).2.1 (P.ι (D wq.1).1)
    rw [Rat.cast_mul, Rat.cast_inv, ← div_eq_mul_inv, div_lt_iff₀ hsReal, mul_comm]
  obtain ⟨f, hf, hdom⟩ := oracle_monotonicity_threshold A g hg
  have hin : Computable (fun t : ℕ × ℕ × ℕ ↦ natBits (Encodable.encode t)) :=
    natBits_computable.comp Computable.encode
  have htest : Computable (fun t : ℕ × ℕ × ℕ ↦ decide (1 ≤ t.2.1)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp (Primrec.const 1)
      (Primrec.fst.comp Primrec.snd))).to_comp
  let F : (ℕ × ℕ × ℕ) →. ℕ := fun t ↦
    if 1 ≤ t.2.1 then f (natBits (Encodable.encode t)) else Part.none
  have hF : PartrecIn {charOracle A} F :=
    (PartrecIn.cond htest.computableIn (hf.comp hin.computableIn) PartrecIn.none).of_eq
      (fun t ↦ by simp only [Bool.cond_decide]; rfl)
  refine ⟨F, hF, fun t ↦ ?_⟩
  change (1 ≤ t.2.1 ∧ _) ↔ (F t).Dom
  by_cases hn : 1 ≤ t.2.1
  · have hFt : F t = f (natBits (Encodable.encode t)) := by simp only [F, hn, ↓reduceIte]
    rw [hFt, ← hdom]
    simp only [hn, true_and, g, D, natBits, decodeBits_natBits, Encodable.encodek,
      Option.getD_some]
    rfl
  · simp [F, hn]

/-- The threshold set has total mass at most one: each triple's center weight is bounded by
its Kraft weight, and the encoding of triples is injective. -/
private lemma nullBSMass_kraftThresholdSet_le_one (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (s : ℚ) :
    nullBSMass P T u (s : ℝ) (kraftThresholdSet P T u A s) ≤ 1 := by
  rw [nullBSMass_eq_tsum]
  calc
    (∑' t : kraftThresholdSet P T u A s,
        (2 : ℝ≥0∞) ^ (-(s : ℝ) * birkhoffSum T u t.val.2.1 (P.ι t.val.1)))
        ≤ ∑' t : kraftThresholdSet P T u A s,
          (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A (Encodable.encode t.val) := by
      refine ENNReal.tsum_le_tsum fun t ↦ ?_
      have ht := t.property.2
      calc
        (2 : ℝ≥0∞) ^ (-(s : ℝ) * birkhoffSum T u t.val.2.1 (P.ι t.val.1))
            ≤ (2 : ℝ≥0∞) ^ (-(oracleNatComplexity A (Encodable.encode t.val) : ℝ)) :=
          ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A (Encodable.encode t.val) := by
          rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
    _ ≤ ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A j :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun t : kraftThresholdSet P T u A s ↦ Encodable.encode t.val)
        (Encodable.encode_injective.comp Subtype.val_injective)
        (fun j : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A j)
    _ ≤ 1 := oracle_kraft A

/-- For each fixed scale code `p`, encoding the triple `(i, n, p)` adds only logarithmic
overhead to the oracle complexity of `i`. -/
private lemma exists_oracleNatComplexity_triple_le (A : Set ℕ) (p : ℕ) :
    ∃ c : ℕ, ∀ i n : ℕ,
      (oracleNatComplexity A (Encodable.encode (i, n, p)) : ℝ) ≤
        oracleNatComplexity A i + 2 * Real.logb 2 (n + 1) + c := by
  let G : List BitString →. BitString := fun ws ↦ Part.some
    (natBits (Encodable.encode (decodeBits (decodeFirst (ws.headD [])),
      decodeBits (decodeSecond (ws.headD [])), p)))
  have hd : Computable (fun ws : List BitString ↦ ws.headD []) :=
    (Computable.option_getD Primrec.list_head?.to_comp (Computable.const [])).of_eq
      (fun ws ↦ by cases ws <;> rfl)
  have hi := decodeBits_computable.comp
    (CodedFiniteDistribution.decodeFirst_primrec.to_comp.comp hd)
  have hn := decodeBits_computable.comp
    (CodedFiniteDistribution.decodeSecond_primrec.to_comp.comp hd)
  have hG : PartrecIn {charOracle A} G :=
    (natBits_computable.comp (Computable.encode.comp
      (hi.pair (hn.pair (Computable.const p))))).computableIn.partrecIn
  obtain ⟨c₁, hc₁⟩ := oracle_tuple_bounds_composition A 1 G hG
  obtain ⟨c₂, hc₂⟩ := oracle_tuple_bounds_overhead A
  refine ⟨c₁ + c₂, fun i n ↦ ?_⟩
  have hmem : natBits (Encodable.encode (i, n, p)) ∈
      G [pairCode (natBits i) (natBits n)] := by
    simp [G, decodeFirst_pairCode, decodeSecond_pairCode, natBits]
  have hc := hc₁ [pairCode (natBits i) (natBits n)] _ rfl hmem
  have hnat : oracleNatComplexity A (Encodable.encode (i, n, p)) ≤
      oraclePairComplexity A i n + c₁ := by
    simpa [oracleNatComplexity, oraclePairComplexity] using hc
  have hreal : (oracleNatComplexity A (Encodable.encode (i, n, p)) : ℝ) ≤
      oraclePairComplexity A i n + c₁ := by exact_mod_cast hnat
  have hb := hc₂ i n
  push_cast
  linarith

/-- Logarithmic overhead plus a constant is eventually smaller than any prescribed positive
linear slack. -/
private lemma exists_forall_two_mul_logb_add_lt_mul (c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, 2 * Real.logb 2 (n + 1) + c < ε * n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.logb 2 (n + 1) / n) atTop (𝓝 0) := by
    have h := normalized_additive_slack_log.div_const (Real.log 2)
    simpa only [Real.logb, div_right_comm, zero_div] using h
  have hc : Tendsto (fun n : ℕ ↦ (c : ℝ) / n) atTop (𝓝 0) :=
    normalized_additive_slack (fun n : ℕ ↦ (n : ℝ)) 1 zero_lt_one
      (by filter_upwards with n; simp) c
  have hlim : Tendsto (fun n : ℕ ↦ (2 * Real.logb 2 (n + 1) + c) / n)
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, zero_add] using (hlog.const_mul 2).add hc
  have hev := (tendsto_order.1 hlim).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  exact ⟨N, fun n hn ↦ (div_lt_iff₀ (Nat.cast_pos.mpr (hN n hn).2)).mp (hN n hn).1⟩

/-- A strict bound on the pointwise dimension gives arbitrarily late positive realizers below
the same threshold at any fixed dyadic radius.  No attainment assumption is required. -/
private lemma exists_late_realizer_of_pointwiseBSDimension_lt
    (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) (t : ℝ)
    (ht : (pointwiseBSDimension P T u A x).1 < ENNReal.ofReal t) (p N : ℕ) :
    ∃ n ≥ max 1 N, ∃ i, P.ι i ∈ bowenBall T n x (dyadicRadius p) ∧
      0 < birkhoffSum T u n (P.ι i) ∧
      (oracleNatComplexity A i : ℝ) < t * birkhoffSum T u n (P.ι i) := by
  have hl : liminf (fun n ↦ finiteScaleBSCost P T u A x n (dyadicRadius p)) atTop <
      ENNReal.ofReal t := (le_iSup _ p).trans_lt ht
  have hf := frequently_lt_of_liminf_lt (h := hl)
  obtain ⟨n, hn, hcost⟩ := frequently_atTop.1 hf (max 1 N)
  have hn0 : n ≠ 0 := by omega
  simp only [finiteScaleBSCost, ite_eq_right hn0, iInf_lt_iff] at hcost
  obtain ⟨i, hi, hpos, hratio⟩ := hcost
  refine ⟨n, hn, i, hi, hpos, ?_⟩
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hpos] at hratio
  have hratioReal : (oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) < t :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (div_nonneg (Nat.cast_nonneg _) hpos.le)).mp hratio
  exact (div_lt_iff₀ hpos).mp hratioReal

/-- If the pointwise dimension of `x` is below the positive rational `s`, then at every scale
code `p` and cutoff `k` the threshold set contains a triple `(i, n, p)` with `n ≥ max 1 k`
whose ball around `ι i` contains `x`. -/
private lemma exists_late_triple_mem_kraftThresholdSet (P : Presentation X) (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (A : Set ℕ) (x : X) (hx : 0 < lowerBirkhoffAverage T u x) (s : ℚ)
    (hs : (pointwiseBSDimension P T u A x).1 < ENNReal.ofReal (s : ℝ)) :
    ∀ p k, ∃ i n, max 1 k ≤ n ∧
      (i, n, p) ∈ kraftThresholdSet P T u A s ∧
      x ∈ bowenBall T n (P.ι i) (dyadicRadius p) := by
  obtain ⟨t, ht0, hdt, hts⟩ := ENNReal.lt_iff_exists_real_btwn.1 hs
  have htsReal : t < (s : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).mp hts
  obtain ⟨ρ, hρ, r₀, hr₀, hbounds⟩ := birkhoffRealizerBounds_positive P T u hu x hx
  have hρReal : (0 : ℝ) < ρ := by exact_mod_cast hρ
  intro p k
  obtain ⟨q, hq⟩ := exists_dyadicRadius_lt (lt_min hr₀ (dyadicRadius_pos p))
  obtain ⟨N, hN, hNb⟩ := hbounds (dyadicRadius q) (dyadicRadius_pos q)
    (hq.le.trans (min_le_left _ _))
  obtain ⟨c, hc⟩ := exists_oracleNatComplexity_triple_le A p
  obtain ⟨M, hM⟩ := exists_forall_two_mul_logb_add_lt_mul c (((s : ℝ) - t) * ρ)
    (mul_pos (sub_pos.mpr htsReal) hρReal)
  obtain ⟨n, hn, i, hi, hpos, hK⟩ :=
    exists_late_realizer_of_pointwiseBSDimension_lt P T u A x t hdt q (max k (max N M))
  have hnk : max 1 k ≤ n := by omega
  have hb := (hNb n (by omega) i hi).1
  have ho := hM n (by omega)
  have htuple := hc i n
  have hthreshold : (oracleNatComplexity A (Encodable.encode (i, n, p)) : ℝ) <
      (s : ℝ) * birkhoffSum T u n (P.ι i) := by
    have hgap := mul_le_mul_of_nonneg_left hb (sub_pos.mpr htsReal).le
    nlinarith
  have hi' : P.ι i ∈ bowenBall T n x (dyadicRadius p) :=
    bowenBall_subset_of_le T n x (hq.le.trans (min_le_right _ _)) hi
  exact ⟨i, n, hnk, ⟨(le_max_left 1 k).trans hnk, hthreshold⟩,
    mem_bowenBall_iff.2 fun j hj ↦ (dist_comm _ _).trans_lt (mem_bowenBall_iff.1 hi' j hj)⟩

/-- To bound the effective lower dimension by `d` it suffices to exhibit, for every positive
rational `s` with `d < s`, an `A`-enumerable null `s`-cover. -/
private lemma effectiveLowerBSDimension_le_of_rat_isREIn_nullBSCover
    (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (Z : Set X) (d : ℝ≥0∞)
    (H : ∀ s : ℚ, 0 < s → d < ENNReal.ofReal (s : ℝ) →
      ∃ E : Set (ℕ × ℕ × ℕ), IsNullBSCover P T u Z (s : ℝ) E ∧ IsREIn A E) :
    effectiveLowerBSDimension P T u A Z ≤ d := by
  refine not_lt.mp fun hlt ↦ ?_
  obtain ⟨s, hs0, hds, hse⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hposReal : 0 < (s : ℝ) := ENNReal.ofReal_pos.mp (bot_le.trans_lt hds)
  obtain ⟨E, hE, hRE⟩ := H s (by exact_mod_cast hposReal) hds
  have heff : effectiveLowerBSDimension P T u A Z ≤ ENNReal.ofReal (s : ℝ) :=
    iInf_le_of_le (s : ℝ) (iInf_le_of_le hposReal.le
      (iInf_le_of_le E (iInf_le_of_le ⟨hE, hRE⟩ le_rfl)))
  exact not_lt_of_ge heff hse

/-- The Kraft construction bounds effective lower dimension by the pointwise supremum.
Blueprint node `bs:effective-lower-upper`. -/
theorem effectiveLowerBSLeSup (P : Presentation X) (T : X → X) (u : X → ℝ)
    (hu : UniformContinuous u) (A : Set ℕ) (hA : IsAdmissible P T (fun _ : Fin 1 => u) A)
    (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    effectiveLowerBSDimension P T u A Z ≤ ⨆ x ∈ Z, (pointwiseBSDimension P T u A x).1 := by
  refine effectiveLowerBSDimension_le_of_rat_isREIn_nullBSCover P T u A Z _ fun s hs hsup ↦ ?_
  refine ⟨kraftThresholdSet P T u A s, ⟨?_, fun p k x hx ↦ ?_⟩,
    isREIn_kraftThresholdSet P T u A hA s hs⟩
  · exact (nullBSMass_kraftThresholdSet_le_one P T u A s).trans_lt ENNReal.one_lt_top
  · refine exists_late_triple_mem_kraftThresholdSet P T u hu A x (hZ x hx) s ?_ p k
    exact (le_iSup₂_of_le x hx le_rfl).trans_lt hsup

end Kolmogorov.PointToSet
