/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Defs
import KolmogorovMathlib.PointToSet.BSDimension.Lower
import KolmogorovMathlib.PointToSet.BSDimension.Upper
import KolmogorovMathlib.PointToSet.PackingEquivalences.Defs
import KolmogorovMathlib.PointToSet.PackingEquivalences.Pressure
import KolmogorovMathlib.PointToSet.Pressure.Defs
import Mathlib.Topology.Bases
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.Set

/-!
# Packing and separated Barreira–Schmeling contents

This module defines the packing contents, outer envelope, and separated capacities used
in the Barreira–Schmeling packing equivalences (blueprint node `pack:bs-definitions`).
Positive lower Birkhoff averages give a countable exhaustion by uniform positive-average
pieces (`pack:positive-pieces`). On these pieces, increasing the exponent introduces a
geometrically decaying factor in the covering and packing costs.

Countable subadditivity of lower covering mass (`pack:lower-bs-subadditive`) and refinement
of packing covers then give the finite-to-zero dichotomies and equality of the zero and
infinity thresholds (`pack:lower-bs-dichotomy`). The radius and covering comparison modules
use these definitions and thresholds to compare packing and modified separated dimensions.
-/

namespace Kolmogorov.PointToSet

open Filter TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-- The BS cost of a decorated family, using the supplied radius in every sup-weight.
Blueprint node `pack:bs-definitions`. -/
noncomputable def bsPackingSum (T : X → X) (u : X → ℝ) (a r : ℝ)
    (F : Set (X × ℕ)) : ℝ≥0∞ :=
  ∑' p : F, bsBallWeight T u a p.val.2 p.val.1 r

/-- The supremum of BS costs of countable packings above a positive order cutoff.
Blueprint node `pack:bs-definitions`. -/
noncomputable def bsPackingContent (T : X → X) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ F : Set (X × ℕ), ⨆ (_ : IsBowenPacking T Z r N F), bsPackingSum T u a r F

/-- The decreasing order-cutoff infimum of BS packing content.
Blueprint node `pack:bs-definitions`. -/
noncomputable def bsPackingPrecontent (T : X → X) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) : ℝ≥0∞ :=
  ⨅ N : ℕ, ⨅ (_ : 1 ≤ N), bsPackingContent T u Z a r N

/-- The outer BS envelope uses countable covers with every piece inside the target set.
Blueprint node `pack:bs-definitions`. -/
noncomputable def bsPackingOuterEnvelope (T : X → X) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
    ∑' j, bsPackingPrecontent T u (Y j) a r

/-- The nonnegative zero threshold of the BS packing outer envelope at one radius.
Blueprint node `pack:bs-definitions`. -/
noncomputable def packingBSDimensionAt (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ a : ℝ, ⨅ (_ : 0 ≤ a), ⨅ (_ : bsPackingOuterEnvelope T u Z a r = 0),
    ENNReal.ofReal a

/-- The increasing dyadic scale supremum of the packing BS thresholds.
Blueprint node `pack:bs-definitions`. -/
noncomputable def packingBSDimension (T : X → X) (u : X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, packingBSDimensionAt T u Z (dyadicRadius p)

/-- The supremum of fixed-order BS costs over separated subsets.
Blueprint node `pack:bs-definitions`. -/
noncomputable def separatedBSSum (T : X → X) (u : X → ℝ) (Z : Set X)
    (a r : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ F : Set X, ⨆ (_ : F ⊆ Z ∧ IsBowenSeparated T n r F),
    bsPartitionCoverCost T u a r n F

/-- The nonnegative zero threshold for the limiting superior of separated BS sums.
Blueprint node `pack:bs-definitions`. -/
noncomputable def separatedBSZeroCapacityAt (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ a : ℝ, ⨅ (_ : 0 ≤ a),
    ⨅ (_ : limsup (separatedBSSum T u Z a r) atTop = 0), ENNReal.ofReal a

/-- The nonnegative finiteness threshold for the limiting superior of separated BS sums.
Blueprint node `pack:bs-finite-zero`. -/
noncomputable def separatedBSFiniteCapacityAt (T : X → X) (u : X → ℝ) (Z : Set X)
    (r : ℝ) : ℝ≥0∞ :=
  ⨅ a : ℝ, ⨅ (_ : 0 ≤ a),
    ⨅ (_ : limsup (separatedBSSum T u Z a r) atTop < ⊤), ENNReal.ofReal a

/-- Countable modification of the separated zero threshold at a fixed radius.
Blueprint node `pack:bs-definitions`. -/
noncomputable def modifiedSeparatedBSDimension (T : X → X) (u : X → ℝ)
    (Z : Set X) (r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
    ⨆ j, separatedBSZeroCapacityAt T u (Y j) r

/-- The separated scale-zero dimension takes the scale supremum after modification.
Blueprint node `pack:bs-definitions`. -/
noncomputable def separatedBSDimension (T : X → X) (u : X → ℝ) (Z : Set X) : ℝ≥0∞ :=
  ⨆ p : ℕ, modifiedSeparatedBSDimension T u Z (dyadicRadius p)

/-- The packing and modified separated thresholds at the specified radius, in that order.
Blueprint node `pack:bs-definitions`. -/
noncomputable def bsPackingSeparatedDefinitions (T : X → X) (u : X → ℝ)
    (Z : Set X) (r : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (packingBSDimensionAt T u Z r, modifiedSeparatedBSDimension T u Z r)

omit [MetricSpace X] in
/-- Positive lower averages exhaust the set by the existing rational uniform pieces.
Blueprint node `pack:positive-pieces`. -/
theorem uniformPositivePieces (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) :
    Z = ⋃ N : ℕ, ⋃ (_ : 1 ≤ N), ⋃ ρ : ℚ, ⋃ (_ : 0 < ρ),
      positiveAveragePiece T u Z N ρ := by
  ext x
  simp only [Set.mem_iUnion]
  refine ⟨fun hx ↦ ?_, fun ⟨_, _, _, _, hx⟩ ↦ hx.1⟩
  obtain ⟨ρ, hρ, hρx⟩ := EReal.exists_rat_btwn_of_lt (hZ x hx)
  have hρ_pos : 0 < ρ := by exact_mod_cast hρ
  unfold lowerBirkhoffAverage at hρx
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_lt_liminf hρx)
  refine ⟨max 1 N, le_max_left _ _, ρ, hρ_pos, hx, fun n hn ↦ ?_⟩
  have hn_pos : (0 : ℝ) < n :=
    Nat.cast_pos.2 (lt_of_lt_of_le one_pos ((le_max_left _ _).trans hn))
  have hbound : (ρ : ℝ) ≤ birkhoffSum T u n x / n :=
    (EReal.coe_lt_coe_iff.1 (hN n ((le_max_right _ _).trans hn))).le
  exact (le_div_iff₀ hn_pos).1 hbound

/-- A ball meeting a uniform piece has a supremum at least its uniform Birkhoff bound.
Blueprint node `pack:positive-pieces`. -/
theorem uniformPositivePieces_meeting (T : X → X) (u : X → ℝ) (Z : Set X) (N n : ℕ) (hn : N ≤ n)
    (ρ : ℚ) (y : X) (r : ℝ)
    (hmeets : (bowenBall T n y r ∩ positiveAveragePiece T u Z N ρ).Nonempty) :
    (((ρ : ℝ) * n : ℝ) : EReal) ≤ bowenPotentialSup T u n y r := by
  rcases hmeets with ⟨z, hz_ball, hz_piece⟩
  dsimp [bowenPotentialSup]
  have h1 : (ρ : ℝ) * n ≤ birkhoffSum T u n z := hz_piece.2 n hn
  calc
    (((ρ : ℝ) * (n : ℝ) : ℝ) : EReal) ≤ ((birkhoffSum T u n z : ℝ) : EReal) := by exact_mod_cast h1
    _ ≤ ⨆ z_1 ∈ bowenBall T n y r, ((birkhoffSum T u n z_1 : ℝ) : EReal) := by
      apply le_iSup_of_le z
      apply le_iSup_of_le hz_ball
      rfl

/-- The same supremum bound holds when the center lies in the uniform piece.
Blueprint node `pack:positive-pieces`. -/
theorem uniformPositivePieces_centered (T : X → X) (u : X → ℝ) (Z : Set X) (N n : ℕ) (hn : N ≤ n)
    (ρ : ℚ)
    (y : X) (hy : y ∈ positiveAveragePiece T u Z N ρ) (r : ℝ) (hr : 0 < r) :
    (((ρ : ℝ) * n : ℝ) : EReal) ≤ bowenPotentialSup T u n y r := by
  exact uniformPositivePieces_meeting T u Z N n hn ρ y r
    ⟨y, self_mem_bowenBall T n y r hr, hy⟩

/-- A sequence of sets with finite total lower mass admits covers with summable errors. -/
private lemma exists_bs_covers_with_geometric_error
    (T : X → X) (u : X → ℝ) (Y : ℕ → Set X) (a r : ℝ) (N : ℕ)
    (h_sum : ∑' j, lowerBSMass T u (Y j) a r N < ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ → BowenCoverFamily X,
      (∀ j, IsBowenCover T (Y j) r N (C j)) ∧
      (∀ j, bsCoverCost T u a r (C j) ≤
        lowerBSMass T u (Y j) a r N + ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1))) := by
  have H (j : ℕ) : ∃ C : BowenCoverFamily X, IsBowenCover T (Y j) r N C ∧
      bsCoverCost T u a r C ≤
        lowerBSMass T u (Y j) a r N + ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1)) := by
    have h_eps_pos : 0 < ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1)) := by
      apply ENNReal.ofReal_pos.mpr
      apply mul_pos hε
      exact pow_pos (by norm_num) (j + 1)
    have h_lt : lowerBSMass T u (Y j) a r N <
        lowerBSMass T u (Y j) a r N + ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1)) := by
      apply ENNReal.lt_add_right
      · have h_le : lowerBSMass T u (Y j) a r N ≤ ∑' k, lowerBSMass T u (Y k) a r N :=
          ENNReal.le_tsum (f := fun k ↦ lowerBSMass T u (Y k) a r N) j
        exact h_le.trans_lt h_sum |>.ne
      · exact h_eps_pos.ne.symm
    simp only [lowerBSMass, iInf_lt_iff] at h_lt
    rcases h_lt with ⟨C, hC1, hC2⟩
    use C, hC1, hC2.le
  choose C hC1 hC2 using H
  use C, hC1, hC2

/-- Countably many Bowen covers can be combined into one cover with the same total cost. -/
private lemma exists_union_bowenCover_cost_eq_tsum
    (T : X → X) (u : X → ℝ) (Y : ℕ → Set X)
    (a r : ℝ) (N : ℕ) (C : ℕ → BowenCoverFamily X)
    (hC : ∀ j, IsBowenCover T (Y j) r N (C j)) :
    ∃ D : BowenCoverFamily X,
      IsBowenCover T (⋃ j, Y j) r N D ∧
      bsCoverCost T u a r D = ∑' j, bsCoverCost T u a r (C j) := by
  classical
  let S := Σ j : ℕ, (C j).index
  let code : S → ℕ := fun p ↦ Nat.pair p.1 p.2.val
  have hcode : Function.Injective code := by
    rintro ⟨j, ⟨i, hi⟩⟩ ⟨k, ⟨l, hl⟩⟩ h
    have hp : Nat.pair j i = Nat.pair k l := h
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hp
    rfl
  let I : Set ℕ := Set.range code
  let e : I ≃ S := (Equiv.ofInjective code hcode).symm
  let D : BowenCoverFamily X :=
    { index := I
      center := fun k ↦ (C (e k).1).center (e k).2
      order := fun k ↦ (C (e k).1).order (e k).2 }
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · intro k
    exact (hC (e k).1).1 (e k).2
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((hC j).2 hj)
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨j, i⟩, ?_⟩
    change x ∈ bowenBall T
      ((C (e (e.symm ⟨j, i⟩)).1).order
        (e (e.symm ⟨j, i⟩)).2)
      ((C (e (e.symm ⟨j, i⟩)).1).center
        (e (e.symm ⟨j, i⟩)).2) r
    have heq : e (e.symm ⟨j, i⟩) = ⟨j, i⟩ := Equiv.apply_symm_apply e ⟨j, i⟩
    rw [heq]
    exact hi
  · calc
      bsCoverCost T u a r D =
          ∑' p : S, bsBallWeight T u a
            ((C p.1).order p.2) ((C p.1).center p.2) r :=
        e.tsum_eq (fun p ↦ bsBallWeight T u a
          ((C p.1).order p.2) ((C p.1).center p.2) r)
      _ = ∑' j, bsCoverCost T u a r (C j) :=
        ENNReal.tsum_sigma' _

/-- The geometric error budget sums to the prescribed positive real number. -/
private lemma tsum_ofReal_mul_inv_two_pow_succ
    (ε : ℝ) (hε : 0 < ε) :
    ∑' j : ℕ, ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1)) = ENNReal.ofReal ε := by
  simp only [ENNReal.ofReal_mul hε.le, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2⁻¹),
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
    ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
    inv_inv]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

/-- Lower BS contents are countably subadditive before the order limit.
Blueprint node `pack:lower-bs-subadditive`. -/
theorem lowerBSCountableSubadditive (T : X → X) (u : X → ℝ) (Y : ℕ → Set X)
    (a r : ℝ) (N : ℕ) :
    lowerBSMass T u (⋃ j, Y j) a r N ≤ ∑' j, lowerBSMass T u (Y j) a r N := by
  by_cases h_top : ∑' j, lowerBSMass T u (Y j) a r N = ⊤
  · simp only [h_top, le_top]
  · have h_sum : ∑' j, lowerBSMass T u (Y j) a r N < ⊤ := lt_top_iff_ne_top.mpr h_top
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεR : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    rw [← ENNReal.ofReal_coe_nnreal]
    have ⟨C, hC_cov, hC_cost⟩ := exists_bs_covers_with_geometric_error T u Y a r N h_sum ε hεR
    have ⟨U, hU_cov, hU_cost⟩ := exists_union_bowenCover_cost_eq_tsum T u Y a r N C hC_cov
    have h1 : lowerBSMass T u (⋃ j, Y j) a r N ≤ bsCoverCost T u a r U := by
      unfold lowerBSMass
      apply iInf_le_of_le U
      exact iInf_le _ hU_cov
    have h2 : bsCoverCost T u a r U ≤ ∑' j, lowerBSMass T u (Y j) a r N + ENNReal.ofReal ε := by
      rw [hU_cost]
      calc
        ∑' j, bsCoverCost T u a r (C j) ≤
            ∑' j, (lowerBSMass T u (Y j) a r N +
              ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1))) := by
          apply ENNReal.tsum_le_tsum
          intro j
          exact hC_cost j
        _ = ∑' j, lowerBSMass T u (Y j) a r N + ∑' j, ENNReal.ofReal (ε * 2⁻¹ ^ (j + 1)) := by
          exact ENNReal.tsum_add
        _ = ∑' j, lowerBSMass T u (Y j) a r N + ENNReal.ofReal ε := by
          rw [tsum_ofReal_mul_inv_two_pow_succ ε hεR]
    exact le_trans h1 h2

/-- Countable subadditivity persists after the increasing lower order-cutoff limit.
Blueprint node `pack:lower-bs-subadditive`. -/
theorem lowerBSCountableSubadditive_limit (T : X → X) (u : X → ℝ)
    (Y : ℕ → Set X) (a r : ℝ) :
    lowerBSMassLimit T u (⋃ j, Y j) a r ≤ ∑' j, lowerBSMassLimit T u (Y j) a r := by
  unfold lowerBSMassLimit
  apply iSup_le
  intro N
  apply iSup_le
  intro hN
  calc
    lowerBSMass T u (⋃ j, Y j) a r N ≤ ∑' j, lowerBSMass T u (Y j) a r N :=
      lowerBSCountableSubadditive T u Y a r N
    _ ≤ ∑' j, ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), lowerBSMass T u (Y j) a r N := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply le_iSup_of_le N
      apply le_iSup_of_le hN
      rfl

/-- Retain only the balls of a cover family that meet the specified set. -/
private def restrictCoverToMeetingBalls
    (cov : BowenCoverFamily X) (A : Set X) (T : X → X) (r : ℝ) : BowenCoverFamily X :=
  { index := {j : ℕ | ∃ h : j ∈ cov.index,
      (bowenBall T (cov.order ⟨j, h⟩) (cov.center ⟨j, h⟩) r ∩ A).Nonempty},
    center := fun j ↦ cov.center ⟨j.val, j.property.elim (fun h _ ↦ h)⟩,
    order := fun j ↦ cov.order ⟨j.val, j.property.elim (fun h _ ↦ h)⟩ }

/-- Discarding balls disjoint from the covered set preserves the covering property. -/
private lemma isBowenCover_restrictCoverToMeetingBalls
    (T : X → X) (A : Set X) (r : ℝ) (L : ℕ) (cov : BowenCoverFamily X)
    (hcov : IsBowenCover T A r L cov) :
    IsBowenCover T A r L (restrictCoverToMeetingBalls cov A T r) := by
  classical
  dsimp [restrictCoverToMeetingBalls, IsBowenCover] at *
  constructor
  · intro j
    exact hcov.1 ⟨j.val, j.property.elim (fun h _ ↦ h)⟩
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov.2 hx)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨j.val, ⟨j.property, x, hj, hx⟩⟩, ?_⟩
    exact hj

/-- An exponential lower bound on a base gives geometric decay when increasing
the magnitude of a nonpositive exponent. -/
private lemma rpow_neg_le_two_rpow_mul
    (S : ℝ≥0∞) (q a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hS : (2 : ℝ≥0∞) ^ q ≤ S) :
    S ^ (-b) ≤ (2 : ℝ≥0∞) ^ (-((b - a) * q)) * S ^ (-a) := by
  by_cases htop : S = ⊤
  · subst htop
    have hb : 0 < b := lt_of_le_of_lt ha hab
    have h1 : (⊤ : ENNReal) ^ (-b) = 0 := ENNReal.top_rpow_of_neg (neg_lt_zero.mpr hb)
    rw [h1]
    exact bot_le
  · have hS_pos : 0 < S := by
      calc 0 < (2 : ENNReal) ^ q := ENNReal.rpow_pos (by norm_num) (by norm_num)
           _ ≤ S := hS
    have h_split : S ^ (-b) = S ^ (-(b - a)) * S ^ (-a) := by
      rw [← ENNReal.rpow_add _ _ (ne_of_gt hS_pos) htop]
      congr 1
      ring
    rw [h_split]
    apply mul_le_mul'
    · rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      apply ENNReal.inv_le_inv.mpr
      have h2 : (2 : ENNReal) ^ ((b - a) * q) = ((2 : ENNReal) ^ q) ^ (b - a) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
      rw [h2]
      apply ENNReal.rpow_le_rpow hS (sub_nonneg.mpr (le_of_lt hab))
    · exact le_rfl

/-- On a uniform positive-average piece, restricting a cover and increasing its exponent
bounds its cost by an exponentially decreasing multiple of the original cost. -/
private lemma bsCoverCost_restrict_le
    (T : X → X) (u : X → ℝ) (Z : Set X) (N : ℕ) (ρ : ℚ) (hρ : 0 < ρ)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (L : ℕ) (hL : N ≤ L)
    (cov : BowenCoverFamily X)
    (hcov : IsBowenCover T (positiveAveragePiece T u Z N ρ) r L cov) :
    bsCoverCost T u b r (restrictCoverToMeetingBalls cov (positiveAveragePiece T u Z N ρ) T r) ≤
    (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) * bsCoverCost T u a r cov := by
  let A := positiveAveragePiece T u Z N ρ
  let c : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ)))
  let cov' := restrictCoverToMeetingBalls cov A T r
  let inj : cov'.index → cov.index := fun j ↦ ⟨j.val, j.property.1⟩
  have hinj : Function.Injective inj := by
    intro j1 j2 h
    have h' : (inj j1).val = (inj j2).val := congrArg Subtype.val h
    exact Subtype.ext h'
  have hρ' : (0 : ℝ) ≤ (ρ : ℝ) := Rat.cast_nonneg.mpr hρ.le
  have h_pointwise : ∀ j : cov'.index,
      bsBallWeight T u b (cov'.order j) (cov'.center j) r ≤
      c * bsBallWeight T u a (cov.order (inj j)) (cov.center (inj j)) r := by
    intro j
    obtain ⟨hj_in, z, hz_ball, hz_piece⟩ := j.property
    have hn_L : max 1 L ≤ cov.order (inj j) := hcov.1 (inj j)
    have hL_n : L ≤ cov.order (inj j) := le_trans (le_max_right 1 L) hn_L
    have hN_n : N ≤ cov.order (inj j) := le_trans hL hL_n
    have hz_bound : (ρ : ℝ) * (cov.order (inj j) : ℝ) ≤ birkhoffSum T u (cov.order (inj j)) z :=
      hz_piece.2 _ hN_n
    have h_bound : (ρ : ℝ) * (L : ℝ) ≤ birkhoffSum T u (cov.order (inj j)) z :=
      le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hL_n) hρ') hz_bound
    have hS : (2 : ℝ≥0∞) ^ ((ρ : ℝ) * (L : ℝ)) ≤
        pressureBallWeight T u .supremum (cov.order (inj j)) (cov.center (inj j)) r := by
      change (2 : ℝ≥0∞) ^ ((ρ : ℝ) * (L : ℝ)) ≤
        ⨆ y ∈ bowenBall T (cov.order (inj j)) (cov.center (inj j)) r,
          (2 : ℝ≥0∞) ^ birkhoffSum T u (cov.order (inj j)) y
      refine le_iSup₂_of_le z hz_ball ?_
      exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two h_bound
    have h_power := rpow_neg_le_two_rpow_mul
      (pressureBallWeight T u .supremum (cov.order (inj j)) (cov.center (inj j)) r)
      ((ρ : ℝ) * (L : ℝ)) a b ha hab hS
    have h_exp : -((b - a) * ((ρ : ℝ) * (L : ℝ))) = -((b - a) * (ρ : ℝ) * (L : ℝ)) := by ring
    rw [h_exp] at h_power
    exact h_power
  unfold bsCoverCost
  calc ∑' j : cov'.index, bsBallWeight T u b (cov'.order j) (cov'.center j) r
      ≤ ∑' j : cov'.index, c * bsBallWeight T u a (cov.order (inj j)) (cov.center (inj j)) r :=
        ENNReal.tsum_le_tsum h_pointwise
    _ = c * ∑' j : cov'.index, bsBallWeight T u a (cov.order (inj j)) (cov.center (inj j)) r :=
        ENNReal.tsum_mul_left
    _ ≤ c * ∑' i : cov.index, bsBallWeight T u a (cov.order i) (cov.center i) r := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hinj
          (fun i : cov.index ↦ bsBallWeight T u a (cov.order i) (cov.center i) r)

/-- Increasing the exponent bounds the mass of a uniform positive-average piece
by an exponentially decreasing multiple of its original mass. -/
private lemma lowerBSMass_positive_piece_le (T : X → X) (u : X → ℝ) (Z : Set X)
    (N : ℕ) (ρ : ℚ) (hρ : 0 < ρ) (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (L : ℕ) (hL : N ≤ L) :
    lowerBSMass T u (positiveAveragePiece T u Z N ρ) b r L ≤
      (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) *
        lowerBSMass T u (positiveAveragePiece T u Z N ρ) a r L := by
  have hc0 : (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) ≠ 0 :=
    (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have hctop : (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  unfold lowerBSMass
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun cov ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun hcov ↦ ?_
  exact (iInf₂_le
    (restrictCoverToMeetingBalls cov
      (positiveAveragePiece T u Z N ρ) T r)
    (isBowenCover_restrictCoverToMeetingBalls T _ r L cov hcov)).trans
    (bsCoverCost_restrict_le
      T u Z N ρ hρ a b r ha hab L hL cov hcov)

/-- Enlarging the covered set can only increase its lower covering mass. -/
private lemma lowerBSMass_mono_set (T : X → X) (u : X → ℝ) (s r : ℝ) (Z1 Z2 : Set X)
    (h_sub : Z1 ⊆ Z2) (N : ℕ) : lowerBSMass T u Z1 s r N ≤ lowerBSMass T u Z2 s r N := by
  unfold lowerBSMass
  apply iInf_mono
  intro C
  apply iInf_mono'
  intro hC
  have hC' : IsBowenCover T Z1 r N C := by
    unfold IsBowenCover at hC ⊢
    exact ⟨hC.1, h_sub.trans hC.2⟩
  exact ⟨hC', le_rfl⟩

/-- Finite lower mass on the ambient set forces zero mass at larger exponents
on each uniform positive-average piece. -/
private lemma lowerBSMassLimit_positive_piece_eq_zero (T : X → X) (u : X → ℝ) (Z : Set X)
    (N : ℕ) (hN : 1 ≤ N) (ρ : ℚ) (hρ : 0 < ρ) (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hfinite : lowerBSMassLimit T u Z a r < ⊤) :
    lowerBSMassLimit T u (positiveAveragePiece T u Z N ρ) b r = 0 := by
  let q : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ)))
  have hexp : -((b - a) * (ρ : ℝ)) < 0 := by
    have hρ' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
    have : 0 < (b - a) * (ρ : ℝ) := mul_pos (sub_pos.mpr hab) hρ'
    linarith
  have hq : q < 1 := by
    dsimp [q]
    exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hpow : Tendsto (fun L : ℕ ↦ q ^ L) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hK : lowerBSMassLimit T u Z a r ≠ ⊤ := ne_of_lt hfinite
  have hprod : Tendsto
      (fun L : ℕ ↦ q ^ L * lowerBSMassLimit T u Z a r) atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.mul_const hpow (Or.inr hK))
  have h_mass : ∀ L ≥ N, lowerBSMass T u (positiveAveragePiece T u Z N ρ) b r L ≤
      q ^ L * lowerBSMassLimit T u Z a r := by
    intro L hL
    calc
      lowerBSMass T u (positiveAveragePiece T u Z N ρ) b r L ≤
          (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) *
            lowerBSMass T u (positiveAveragePiece T u Z N ρ) a r L :=
        lowerBSMass_positive_piece_le T u Z N ρ hρ a b r ha hab L hL
      _ ≤ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) * lowerBSMass T u Z a r L := by
        gcongr
        exact lowerBSMass_mono_set T u a r (positiveAveragePiece T u Z N ρ) Z (fun _ hx ↦ hx.1) L
      _ ≤ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * (L : ℝ))) * lowerBSMassLimit T u Z a r := by
        gcongr
        have h_limit : lowerBSMass T u Z a r L ≤ lowerBSMassLimit T u Z a r := by
          unfold lowerBSMassLimit
          exact le_iSup₂_of_le (i := L) (j := le_trans hN hL) (le_rfl)
        exact h_limit
      _ = q ^ L * lowerBSMassLimit T u Z a r := by
        congr 1
        dsimp [q]
        rw [← ENNReal.rpow_natCast]
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
  have h_tendsto2 : Tendsto
      (fun L : ℕ ↦ lowerBSMass T u (positiveAveragePiece T u Z N ρ) b r L)
      atTop (𝓝 (lowerBSMassLimit T u (positiveAveragePiece T u Z N ρ) b r)) := by
    exact lowerBSMass_cutoff_limit T u (positiveAveragePiece T u Z N ρ) b r
  have h_le : ∀ᶠ L in atTop, lowerBSMass T u (positiveAveragePiece T u Z N ρ) b r L ≤
      q ^ L * lowerBSMassLimit T u Z a r := by
    apply eventually_atTop.mpr
    exact ⟨N, h_mass⟩
  exact le_antisymm (tendsto_le_of_eventuallyLE h_tendsto2 hprod h_le) bot_le

/-- If every uniform positive-average piece has zero lower mass, so does their union. -/
private lemma lowerBSMassLimit_eq_zero_of_positive_pieces (T : X → X) (u : X → ℝ) (Z : Set X)
    (b r : ℝ)
    (h_pieces : ∀ N, 1 ≤ N → ∀ ρ : ℚ, 0 < ρ →
      lowerBSMassLimit T u (positiveAveragePiece T u Z N ρ) b r = 0)
    (hZ_eq : Z = ⋃ N : ℕ, ⋃ (_ : 1 ≤ N), ⋃ ρ : ℚ, ⋃ (_ : 0 < ρ), positiveAveragePiece T u Z N ρ) :
    lowerBSMassLimit T u Z b r = 0 := by
  let I := {N : ℕ // 1 ≤ N} × {ρ : ℚ // 0 < ρ}
  have hI : Nonempty I := ⟨⟨⟨1, le_rfl⟩, ⟨1, by norm_num⟩⟩⟩
  obtain ⟨e, he⟩ := @exists_surjective_nat I hI inferInstance
  let Y : ℕ → Set X := fun j ↦ positiveAveragePiece T u Z (e j).1.1 (e j).2.1
  have hZ_Y : Z = ⋃ j, Y j := by
    ext x
    simp only [Set.mem_iUnion]
    rw [hZ_eq]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hN, ρ, hρ, hx⟩
      obtain ⟨j, hj⟩ := he ⟨⟨N, hN⟩, ⟨ρ, hρ⟩⟩
      use j
      have heq : Y j = positiveAveragePiece T u Z N ρ := by
        dsimp [Y]
        rw [hj]
      rw [heq]
      exact hx
    · rintro ⟨j, hj⟩
      exact ⟨(e j).1.1, (e j).1.2, (e j).2.1, (e j).2.2, hj⟩
  rw [hZ_Y]
  have h_le := lowerBSCountableSubadditive_limit T u Y b r
  apply le_antisymm
  · calc
      lowerBSMassLimit T u (⋃ (j : ℕ), Y j) b r ≤ ∑' j, lowerBSMassLimit T u (Y j) b r := h_le
      _ = ∑' (j : ℕ), (0 : ℝ≥0∞) := by
        congr 1
        ext j
        dsimp [Y]
        exact h_pieces (e j).1.1 (e j).1.2 (e j).2.1 (e j).2.2
      _ = 0 := tsum_zero
  · exact bot_le

/-- Finite lower covering mass becomes zero at every larger exponent on the
positive-average locus.
Blueprint node `pack:lower-bs-dichotomy`. -/
theorem lowerBSDichotomy_packing (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hfinite : lowerBSMassLimit T u Z a r < ⊤) : lowerBSMassLimit T u Z b r = 0 := by
  apply lowerBSMassLimit_eq_zero_of_positive_pieces T u Z b r
  · intro N hN ρ hρ
    exact lowerBSMassLimit_positive_piece_eq_zero T u Z N hN ρ hρ a b r ha hab hfinite
  · exact uniformPositivePieces T u Z hZ

/-- A finite-to-zero dichotomy identifies the nonnegative zero and infinity thresholds. -/
private lemma iInf_zero_eq_iSup_top_of_dichotomy {f : ℝ → ℝ≥0∞}
  (h_dichotomy : ∀ a b, 0 ≤ a → a < b → f a < ⊤ → f b = 0) :
  (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : f s = 0), ENNReal.ofReal s) =
  (⨆ a : ℝ, ⨆ (_ : 0 ≤ a), ⨆ (_ : f a = ⊤), ENNReal.ofReal a) := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε h_L_not_top
    set L := ⨆ a : ℝ, ⨆ (_ : 0 ≤ a), ⨆ (_ : f a = ⊤), ENNReal.ofReal a
    have h_L_ne_top : L ≠ ⊤ := by exact (lt_top_iff_ne_top.mp h_L_not_top)
    have L_toReal_pos : 0 ≤ L.toReal := ENNReal.toReal_nonneg
    set L_real := L.toReal
    have h_L_eq : L = ENNReal.ofReal L_real := by rw [ENNReal.ofReal_toReal h_L_ne_top]
    set s := L_real + (ε : ℝ)
    have hs : 0 ≤ s := add_nonneg L_toReal_pos ε.2
    have h_fs_zero : f s = 0 := by
      set a := L_real + (ε : ℝ) / 2
      have ha : 0 ≤ a := add_nonneg L_toReal_pos (half_pos (NNReal.coe_pos.mpr hε)).le
      have ha_lt_s : a < s := by
        dsimp [a, s]
        linarith [NNReal.coe_pos.mpr hε]
      have h_fa_not_top : f a < ⊤ := by
        by_contra! h_fa_top
        have h_fa_eq_top : f a = ⊤ := top_le_iff.mp h_fa_top
        have h_a_le_L : ENNReal.ofReal a ≤ L := by
          apply le_iSup_of_le a
          apply le_iSup_of_le ha
          apply le_iSup_of_le h_fa_eq_top
          rfl
        have h_a_le_L_real : a ≤ L_real := by
          have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal L_real := by
            have h2 : ENNReal.ofReal L_real = L := h_L_eq.symm
            rwa [h2]
          have h3 : ENNReal.ofReal a ≤ ENNReal.ofReal L_real ↔ a ≤ L_real :=
            ENNReal.ofReal_le_ofReal_iff L_toReal_pos
          rwa [←h3]
        dsimp [a] at h_a_le_L_real
        linarith [NNReal.coe_pos.mpr hε]
      exact h_dichotomy a s ha ha_lt_s h_fa_not_top
    have h_s_val : ENNReal.ofReal s ≤ L + ε := by
      have h_eps_eq : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by
        exact (ENNReal.ofReal_coe_nnreal).symm
      rw [h_L_eq, h_eps_eq]
      have h_add : ENNReal.ofReal s = ENNReal.ofReal L_real + ENNReal.ofReal (ε : ℝ) := by
        apply ENNReal.ofReal_add L_toReal_pos ε.2
      rw [h_add]
    calc (⨅ s : ℝ, ⨅ (_ : 0 ≤ s), ⨅ (_ : f s = 0), ENNReal.ofReal s)
      _ ≤ ⨅ (_ : 0 ≤ s), ⨅ (_ : f s = 0), ENNReal.ofReal s := iInf_le _ s
      _ ≤ ⨅ (_ : f s = 0), ENNReal.ofReal s := iInf_le _ hs
      _ ≤ ENNReal.ofReal s := iInf_le _ h_fs_zero
      _ ≤ L + ε := h_s_val
  · apply iSup_le; intro a
    apply iSup_le; intro ha
    apply iSup_le; intro h_a_top
    apply le_iInf; intro s
    apply le_iInf; intro hs
    apply le_iInf; intro h_s_zero
    by_contra! h
    have h_s_lt_a : s < a := by
      have h_lt : ENNReal.ofReal s < ENNReal.ofReal a := h
      rwa [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs] at h_lt
    have h2 : f a = 0 := h_dichotomy s a hs h_s_lt_a (by rw [h_s_zero]; exact ENNReal.zero_lt_top)
    rw [h2] at h_a_top
    exact ENNReal.zero_ne_top h_a_top

/-- The lower BS zero threshold equals the nonnegative infinity threshold.
Blueprint node `pack:lower-bs-dichotomy`. -/
theorem lowerBSDichotomy_threshold (T : X → X) (u : X → ℝ) (Z : Set X)
    (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x) (r : ℝ) :
    lowerBSDimensionAt T u Z r =
      ⨆ a : ℝ, ⨆ (_ : 0 ≤ a), ⨆ (_ : lowerBSMassLimit T u Z a r = ⊤),
        ENNReal.ofReal a := by
  dsimp [lowerBSDimensionAt]
  apply iInf_zero_eq_iSup_top_of_dichotomy
  intro a b ha hab h_finite
  exact lowerBSDichotomy_packing T u Z hZ a b r ha hab h_finite

/-- Increasing the exponent gives a geometric bound on packing sums
whose centers lie in a uniform positive-average piece. -/
private lemma bsPackingSum_positive_piece_le (T : X → X) (u : X → ℝ)
    (Z C : Set X) (N₀ M : ℕ) (hM : N₀ ≤ M) (ρ : ℚ) (hρ : 0 < ρ)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ) (F : Set (X × ℕ))
    (hF : IsBowenPacking T C r M F) :
    bsPackingSum T u b r F ≤
      (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) * bsPackingSum T u a r F := by
  have H : ∀ p : F,
      bsBallWeight T u b p.val.2 p.val.1 r ≤
        (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) *
          bsBallWeight T u a p.val.2 p.val.1 r := by
    intro p
    have hx : p.val.1 ∈ C := (hF.2.1 p.val p.property).1
    have hn : M ≤ p.val.2 :=
      (le_max_right 1 M).trans (hF.2.1 p.val p.property).2
    have hMN : (M : ℝ) ≤ (p.val.2 : ℝ) := by
      exact_mod_cast hn
    have hρR : 0 ≤ (ρ : ℝ) := (Rat.cast_pos.mpr hρ).le
    have hbound : (ρ : ℝ) * M ≤ birkhoffSum T u p.val.2 p.val.1 :=
      (mul_le_mul_of_nonneg_left hMN hρR).trans
        ((hC hx).2 p.val.2 (hM.trans hn))
    let S := pressureBallWeight T u .supremum p.val.2 p.val.1 r
    have hxx : p.val.1 ∈ bowenBall T p.val.2 p.val.1 r := by
      simp only [bowenBall, Set.mem_ofPred_eq,
        Dynamics.mem_dynEntourage, dist_self]
      exact fun _ _ ↦ hr
    have hbase : (2 : ℝ≥0∞) ^ ((ρ : ℝ) * M) ≤ S :=
      (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hbound).trans
        (le_iSup_of_le p.val.1 (le_iSup_of_le hxx le_rfl))
    have hpower := rpow_neg_le_two_rpow_mul
      S ((ρ : ℝ) * M) a b ha hab hbase
    simpa only [bsBallWeight, S, mul_assoc] using hpower
  unfold bsPackingSum
  exact (ENNReal.tsum_le_tsum H).trans_eq ENNReal.tsum_mul_left

/-- The geometric comparison of packing sums passes to packing content. -/
private lemma bsPackingContent_positive_piece_le (T : X → X) (u : X → ℝ)
    (Z C : Set X) (N₀ M : ℕ) (hM : N₀ ≤ M) (ρ : ℚ) (hρ : 0 < ρ)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ) :
    bsPackingContent T u C b r M ≤
      (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) * bsPackingContent T u C a r M := by
  dsimp [bsPackingContent]
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  calc
    bsPackingSum T u b r F ≤ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) * bsPackingSum T u a r F :=
      bsPackingSum_positive_piece_le T u Z C N₀ M hM ρ hρ a b r ha hab hr hC F hF
    _ ≤ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) * bsPackingContent T u C a r M := by
      gcongr
      apply le_iSup_of_le F
      apply le_iSup_of_le hF
      exact le_rfl

/-- Increasing the order cutoff decreases the packing content. -/
private lemma antitone_bsPackingContent (T : X → X) (u : X → ℝ) (Z : Set X) (a r : ℝ) :
    Antitone (bsPackingContent T u Z a r) := by
  intro N M hNM
  dsimp [bsPackingContent]
  refine iSup_le fun F ↦ ?_
  refine iSup_le fun hF ↦ ?_
  apply le_iSup_of_le F
  apply le_iSup_of_le _
  · exact le_rfl
  · obtain ⟨hF1, hF2, hF3⟩ := hF
    exact ⟨hF1, fun x hx ↦ ⟨(hF2 x hx).1, (max_le_max le_rfl hNM).trans (hF2 x hx).2⟩, hF3⟩

/-- Enlarging the set of permitted centers increases the packing content. -/
private lemma bsPackingContent_mono_set (T : X → X) (u : X → ℝ) {Z W : Set X}
    (hZW : Z ⊆ W) (a r : ℝ) (N : ℕ) :
    bsPackingContent T u Z a r N ≤ bsPackingContent T u W a r N := by
  dsimp [bsPackingContent]
  refine iSup_le fun F ↦ ?_
  refine iSup_le fun hF ↦ ?_
  apply le_iSup_of_le F
  apply le_iSup_of_le _
  · exact le_rfl
  · obtain ⟨hF1, hF2, hF3⟩ := hF
    exact ⟨hF1, fun x hx ↦ ⟨hZW (hF2 x hx).1, (hF2 x hx).2⟩, hF3⟩

/-- Finite packing precontent on an ambient set forces zero precontent at larger exponents
on subsets of its uniform positive-average pieces. -/
private lemma bsPackingPrecontent_positive_piece_eq_zero (T : X → X) (u : X → ℝ)
    (Z C : Set X) (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (ρ : ℚ) (hρ : 0 < ρ)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hC : C ⊆ positiveAveragePiece T u Z N₀ ρ)
    (W : Set X) (hC_sub_W : C ⊆ W)
    (hfinite : bsPackingPrecontent T u W a r < ⊤) :
    bsPackingPrecontent T u C b r = 0 := by
  unfold bsPackingPrecontent at hfinite ⊢
  obtain ⟨L, hL⟩ := iInf_lt_iff.mp hfinite
  obtain ⟨_, hL2⟩ := iInf_lt_iff.mp hL
  apply le_antisymm _ bot_le
  have H_pow : Tendsto (fun M : ℕ ↦ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ))) atTop (𝓝 0) := by
    have heq : (fun M : ℕ ↦ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ))) =
        fun M : ℕ ↦ ((2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ)))) ^ M := by
      ext M
      rw [← ENNReal.rpow_natCast]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    rw [heq]
    apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    apply ENNReal.rpow_lt_one_of_one_lt_of_neg
    · exact ENNReal.one_lt_two
    · apply neg_lt_zero.mpr
      apply mul_pos
      · exact sub_pos.mpr hab
      · exact Rat.cast_pos.mpr hρ
  have hprod : Tendsto
      (fun M : ℕ ↦ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) *
        bsPackingContent T u W a r L) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const H_pow (Or.inr hL2.ne)
  apply ge_of_tendsto hprod
  filter_upwards [Ici_mem_atTop (max N₀ L)] with M hM
  have hM_N₀ : N₀ ≤ M := (le_max_left _ _).trans hM
  have hM_L : L ≤ M := (le_max_right _ _).trans hM
  calc
    ⨅ N, ⨅ (_ : 1 ≤ N), bsPackingContent T u C b r N ≤ bsPackingContent T u C b r M :=
      iInf₂_le M (hN₀.trans hM_N₀)
    _ ≤ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) * bsPackingContent T u C a r M :=
      bsPackingContent_positive_piece_le T u Z C N₀ M hM_N₀ ρ hρ a b r ha hab hr hC
    _ ≤ (2 : ℝ≥0∞) ^ (-((b - a) * (ρ : ℝ) * M : ℝ)) * bsPackingContent T u W a r L := by
      exact mul_le_mul' le_rfl
        ((bsPackingContent_mono_set T u hC_sub_W a r M).trans
          (antitone_bsPackingContent T u W a r hM_L))

/-- A countable cover whose intersections with all uniform positive-average pieces
have zero precontent gives a zero outer envelope. -/
private lemma bsPackingOuterEnvelope_eq_zero_of_refinement (T : X → X) (u : X → ℝ)
    (Z : Set X) (b r : ℝ)
    (Y : ℕ → Set X) (hY_sub : ∀ j, Y j ⊆ Z) (hY_cover : Z ⊆ ⋃ j, Y j)
    (h_zero : ∀ j N (_ : 1 ≤ N) ρ (_ : 0 < ρ),
      bsPackingPrecontent T u (Y j ∩ positiveAveragePiece T u Z N ρ) b r = 0)
    (hZ_exhaust : Z = ⋃ N : ℕ, ⋃ (_ : 1 ≤ N), ⋃ ρ : ℚ, ⋃ (_ : 0 < ρ),
      positiveAveragePiece T u Z N ρ) :
    bsPackingOuterEnvelope T u Z b r = 0 := by
  unfold bsPackingOuterEnvelope
  apply le_antisymm
  · let I := ℕ × {N : ℕ // 1 ≤ N} × {ρ : ℚ // 0 < ρ}
    have : Nonempty I := ⟨(0, ⟨1, le_refl 1⟩, ⟨1, by norm_num⟩)⟩
    obtain ⟨f, hf⟩ := exists_surjective_nat I
    let Y' := fun k ↦ Y (f k).1 ∩ positiveAveragePiece T u Z (f k).2.1.val (f k).2.2.val
    refine iInf_le_of_le Y' ?_
    refine iInf_le_of_le ?_ ?_
    · refine ⟨fun j ↦ ?_, ?_⟩
      · exact Set.inter_subset_left.trans (hY_sub (f j).1)
      · intro x hx
        have hx' := hx
        rw [hZ_exhaust] at hx'
        simp only [Set.mem_iUnion] at hx' ⊢
        obtain ⟨N, hN, ρ, hρ, hxNρ⟩ := hx'
        have hxy : x ∈ ⋃ j, Y j := hY_cover hx
        simp only [Set.mem_iUnion] at hxy
        obtain ⟨j, hj⟩ := hxy
        let idx : I := (j, ⟨N, hN⟩, ⟨ρ, hρ⟩)
        obtain ⟨k, hk⟩ := hf idx
        use k
        have : Y' k = Y j ∩ positiveAveragePiece T u Z N ρ := by
          dsimp [Y']
          rw [hk]
        rw [this]
        exact ⟨hj, hxNρ⟩
    · have h_zero' : ∀ k, bsPackingPrecontent T u (Y' k) b r = 0 := by
        intro k
        exact h_zero (f k).1 (f k).2.1.val (f k).2.1.property (f k).2.2.val (f k).2.2.property
      simp only [h_zero', tsum_zero]
      exact le_rfl
  · exact bot_le

/-- A finite BS outer envelope becomes zero at every larger nonnegative exponent.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_dichotomy (T : X → X) (u : X → ℝ)
    (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (a b r : ℝ) (ha : 0 ≤ a) (hab : a < b) (hr : 0 < r)
    (hfinite : bsPackingOuterEnvelope T u Z a r < ⊤) :
    bsPackingOuterEnvelope T u Z b r = 0 := by
  obtain ⟨Y, hcov, hsum⟩ :=
    (by simpa only [bsPackingOuterEnvelope, iInf_lt_iff] using hfinite)
  apply bsPackingOuterEnvelope_eq_zero_of_refinement T u Z b r Y hcov.1 hcov.2
  · intro j N hN ρ hρ
    have h_le : bsPackingPrecontent T u (Y j) a r ≤ ∑' k, bsPackingPrecontent T u (Y k) a r :=
      @ENNReal.le_tsum _ (fun k ↦ bsPackingPrecontent T u (Y k) a r) j
    have h_fin : bsPackingPrecontent T u (Y j) a r < ⊤ := lt_of_le_of_lt h_le hsum
    exact bsPackingPrecontent_positive_piece_eq_zero T u Z
      (Y j ∩ positiveAveragePiece T u Z N ρ) N hN ρ hρ a b r ha hab hr
      Set.inter_subset_right (Y j) Set.inter_subset_left h_fin
  · exact uniformPositivePieces T u Z hZ

/-- The packing BS zero and infinity thresholds agree on the positive-average locus.
Blueprint node `pack:bs-definitions`. -/
theorem bsPackingSeparatedDefinitions_threshold (T : X → X) (u : X → ℝ)
    (Z : Set X) (hZ : ∀ x ∈ Z, 0 < lowerBirkhoffAverage T u x)
    (r : ℝ) (hr : 0 < r) :
    packingBSDimensionAt T u Z r =
      ⨆ a : ℝ, ⨆ (_ : 0 ≤ a), ⨆ (_ : bsPackingOuterEnvelope T u Z a r = ⊤),
        ENNReal.ofReal a := by
  dsimp only [packingBSDimensionAt]
  apply iInf_zero_eq_iSup_top_of_dichotomy
  intro a b ha hab h_finite
  exact bsPackingSeparatedDefinitions_dichotomy T u Z hZ a b r ha hab hr h_finite

end Kolmogorov.PointToSet
