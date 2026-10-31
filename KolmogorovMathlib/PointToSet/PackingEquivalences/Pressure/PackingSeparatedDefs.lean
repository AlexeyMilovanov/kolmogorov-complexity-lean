/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.PackingEquivalences.Defs
import KolmogorovMathlib.PointToSet.Pressure.Defs
import KolmogorovMathlib.PointToSet.Pressure.Upper
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.OuterMeasure.OfFunction

/-!
# Packing content and separated pressure

This module defines the weighted packing content, its countably subadditive outer
envelope, and the countable modification of separated upper capacity pressure.
For a continuous map on a separable metric space, maximal separated sets are countable
and give Bowen-ball covers (`pack:countable-net`). Finite potential variation controls
supremum weights (`pack:supweight`), yielding the spanning--separated comparison
(`pack:span-sep`).

The outer-envelope properties (`pack:outer`) and the vanishing result after a strict
exponent increase (`pack:pressure-dichotomy`) support the scale comparisons in
`Pressure.ScaleDichotomy` and the pressure identifications in `Pressure.Equivalence`.
-/

namespace Kolmogorov.PointToSet

open Filter TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

/-- The supremum of fixed-order sup-weight sums over separated subsets of the set.
Blueprint node `pack:span-sep`. -/
noncomputable def separatedPressureSum (T : X → X) (f : X → ℝ) (Z : Set X)
    (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ F : Set X, ⨆ (_ : F ⊆ Z ∧ IsBowenSeparated T n r F),
    partitionCoverCost T f .supremum F n r

/-- The pressure cost of a decorated family, with the specified weight radius.
Blueprint node `pack:outer`. -/
noncomputable def packingPressureSum (T : X → X) (f : X → ℝ) (s r : ℝ)
    (F : Set (X × ℕ)) : ℝ≥0∞ :=
  ∑' a : F, (2 : ℝ≥0∞) ^ (-s * a.val.2) *
    pressureBallWeight T f .supremum a.val.2 a.val.1 r

/-- Packing content with orders above a positive cutoff, including the empty packing.
Blueprint node `pack:outer`. -/
noncomputable def packingPressureContent (T : X → X) (f : X → ℝ) (Z : Set X)
    (s r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨆ F : Set (X × ℕ), ⨆ (_ : IsBowenPacking T Z r N F), packingPressureSum T f s r F

/-- The decreasing cutoff infimum of packing contents, before countable modification.
Blueprint node `pack:outer`. -/
noncomputable def packingPressurePrecontent (T : X → X) (f : X → ℝ) (Z : Set X)
    (s r : ℝ) : ℝ≥0∞ :=
  ⨅ N : ℕ, ⨅ (_ : 1 ≤ N), packingPressureContent T f Z s r N

/-- The packing outer envelope infimizes sums of pre-contents over countable covers.
Every piece lies in the covered set, as in the appendix convention.
Blueprint node `pack:outer`. -/
noncomputable def pressureOuterEnvelope (T : X → X) (f : X → ℝ) (Z : Set X)
    (s r : ℝ) : ℝ≥0∞ :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
    ∑' j, packingPressurePrecontent T f (Y j) s r

/-- The signed zero threshold of the packing outer envelope at one radius.
Blueprint node `pack:outer`. -/
noncomputable def packingPressureAt (T : X → X) (f : X → ℝ) (Z : Set X)
    (r : ℝ) : EReal :=
  ⨅ s : ℝ, ⨅ (_ : pressureOuterEnvelope T f Z s r = 0), (s : EReal)

/-- Scale-zero packing pressure; convergence of this limsup is a separate obligation.
Blueprint node `pack:pressure-dichotomy`. -/
noncomputable def packingPressure (T : X → X) (f : X → ℝ) (Z : Set X) : EReal :=
  limsup (packingPressureAt T f Z) (𝓝[Set.Ioi 0] 0)

/-- Upper capacity from separated sums, using the existing extended logarithmic rate.
Blueprint node `pack:pack-to-sep`. -/
noncomputable def separatedUpperPressureAt (T : X → X) (f : X → ℝ) (Z : Set X)
    (r : ℝ) : EReal :=
  limsup (pressureRate (fun n ↦ separatedPressureSum T f Z n r)) atTop

/-- The countable modification of separated upper capacity at a fixed radius.
Blueprint node `pack:pack-to-sep`. -/
noncomputable def modifiedSeparatedPressureAt (T : X → X) (f : X → ℝ) (Z : Set X)
    (r : ℝ) : EReal :=
  ⨅ Y : ℕ → Set X, ⨅ (_ : (∀ j, Y j ⊆ Z) ∧ Z ⊆ ⋃ j, Y j),
    ⨆ j, separatedUpperPressureAt T f (Y j) r

/-- The radius-zero limsup is taken after countable modification of separated pressure.
Blueprint node `pack:pressure-equivalence`. -/
noncomputable def modifiedSeparatedPressure (T : X → X) (f : X → ℝ)
    (Z : Set X) : EReal :=
  limsup (modifiedSeparatedPressureAt T f Z) (𝓝[Set.Ioi 0] 0)


/-- Unions of chains of separated subsets remain separated subsets. -/
private lemma isBowenSeparated_sUnion_of_isChain
    (T : X → X) (Z : Set X) (n : ℕ) (r : ℝ) (C : Set (Set X))
    (hC : IsChain (· ⊆ ·) C)
    (hCmem : ∀ S ∈ C, S ⊆ Z ∧ IsBowenSeparated T n r S) :
    (⋃₀ C) ⊆ Z ∧ IsBowenSeparated T n r (⋃₀ C) := by
  constructor
  · rintro x ⟨S, hS, hx⟩
    exact (hCmem S hS).1 hx
  · rintro x ⟨Sx, hSx, hx⟩ y ⟨Sy, hSy, hy⟩ hxy
    cases hC.total hSx hSy with
    | inl h => exact (hCmem Sy hSy).2 (h hx) hy hxy
    | inr h => exact (hCmem Sx hSx).2 hx (h hy) hxy

/-- Every set has an inclusion-maximal separated subset. -/
private lemma exists_maximal_bowenSeparated_subset
    (T : X → X) (Z : Set X) (n : ℕ) (r : ℝ) :
    ∃ F : Set X, F ⊆ Z ∧ IsBowenSeparated T n r F ∧
      ∀ G : Set X, F ⊆ G → G ⊆ Z → IsBowenSeparated T n r G → G = F := by
  let S := {s : Set X | s ⊆ Z ∧ IsBowenSeparated T n r s}
  have hZorn : ∃ m, ∅ ⊆ m ∧ Maximal (· ∈ S) m := by
    refine zorn_subset_nonempty S ?_ ∅ ?_
    · intro C hC hchain _
      exact ⟨⋃₀ C, isBowenSeparated_sUnion_of_isChain T Z n r C hchain hC,
        fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    · exact ⟨Set.empty_subset Z, Set.pairwise_empty _⟩
  obtain ⟨F, _, hmax⟩ := hZorn
  exact ⟨F, hmax.prop.1, hmax.prop.2,
    fun G hFG hGZ hGsep ↦ (hmax.eq_of_le ⟨hGZ, hGsep⟩ hFG).symm⟩

/-- An inclusion-maximal separated subset covers the original set by open Bowen balls. -/
private lemma subset_iUnion_bowenBall_of_maximal_separated
    (T : X → X) (Z F : Set X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (hF : F ⊆ Z) (hsep : IsBowenSeparated T n r F)
    (hmax : ∀ G : Set X, F ⊆ G → G ⊆ Z → IsBowenSeparated T n r G → G = F) :
    Z ⊆ ⋃ x ∈ F, bowenBall T n x r := by
  intro z hz
  by_contra hnot
  have hout : ∀ x ∈ F, r ≤ bowenDist T n x z := by
    intro x hx
    apply le_of_not_gt
    intro hdist
    exact hnot (Set.mem_iUnion₂.mpr
      ⟨x, hx, (bowen_ball_dense_iff T n hn x z r).mpr hdist⟩)
  have hinsert : IsBowenSeparated T n r (insert z F) := by
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · rw [bowen_dist_comm]
      exact hout y hy
    · exact hout x hx
    · exact hsep hx hy hxy
  have heq := hmax (insert z F) (Set.subset_insert z F) (Set.insert_subset hz hF) hinsert
  have hzF : z ∈ F := heq ▸ Set.mem_insert z F
  have hself : bowenDist T n z z = 0 := by simp [bowenDist]
  exact (not_le_of_gt hr) (hself ▸ hout z hzF)

/-- Every positively separated set for a positive Bowen order is countable.
Blueprint node `pack:countable-net`. -/
theorem countableSeparatedMaximalNet_countable [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (F : Set X) (hF : IsBowenSeparated T n r F) : F.Countable := by
  have hopen : ∀ x ∈ F, IsOpen (bowenBall T n x (r / 3)) :=
    fun x _ ↦ bowen_ball_dense_open T hT n x (r / 3)
  have hne : ∀ x ∈ F, (bowenBall T n x (r / 3)).Nonempty :=
    fun x _ ↦ bowen_ball_dense_nonempty T n x (r / 3) (by positivity)
  have hdisj : F.PairwiseDisjoint (fun x ↦ bowenBall T n x (r / 3)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    rw [bowen_ball_dense_iff T n hn x z] at hzx
    rw [bowen_ball_dense_iff T n hn y z] at hzy
    have hsep := hF hx hy hxy
    have htri := bowen_ball_dense_triangle T n x z y
    rw [bowen_dist_comm T n z y] at htri
    linarith
  exact Set.PairwiseDisjoint.countable_of_isOpen hdisj hopen hne

/-- A maximal separated subset is countable and spans the set by open Bowen balls.
Blueprint node `pack:countable-net`. -/
theorem countableSeparatedMaximalNet [SeparableSpace X] (T : X → X)
    (hT : Continuous T) (Z : Set X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ F : Set X, F ⊆ Z ∧ IsBowenSeparated T n r F ∧ F.Countable ∧
      (∀ G : Set X, F ⊆ G → G ⊆ Z → IsBowenSeparated T n r G → G = F) ∧
      Z ⊆ ⋃ x ∈ F, bowenBall T n x r := by
  obtain ⟨F, hF, hsep, hmax⟩ := exists_maximal_bowenSeparated_subset T Z n r
  exact ⟨F, hF, hsep, countableSeparatedMaximalNet_countable T hT n hn r hr F hsep,
    hmax, subset_iUnion_bowenBall_of_maximal_separated T Z F n hn r hr hF hsep hmax⟩

/-- The center sum is bounded by the extended supremum at every valid radius.
Blueprint node `pack:supweight`. -/
theorem supWeightBounds (T : X → X) (f : X → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (x : X) (r : ℝ) (hr : 0 < r) (hω : potentialVariation f r < ⊤) :
    ((birkhoffSum T f n x : ℝ) : EReal) ≤ bowenPotentialSup T f n x r := by
  have _ := hn
  have _ := hω
  unfold bowenPotentialSup
  refine le_iSup₂_of_le x ?_ le_rfl
  dsimp [bowenBall]
  rw [Dynamics.mem_dynEntourage]
  intro k _
  simpa only [Set.mem_ofPred_eq, dist_self] using hr

/-- On a Bowen ball, Birkhoff sums differ by at most the order times potential variation.
Blueprint node `pack:supweight`. -/
lemma abs_birkhoffSum_sub_le_mul_variation
    (T : X → X) (f : X → ℝ) (n : ℕ) (x z : X) (r : ℝ)
    (hω : potentialVariation f r < ⊤) (hz : z ∈ bowenBall T n x r) :
    |birkhoffSum T f n z - birkhoffSum T f n x| ≤ n * (potentialVariation f r).toReal := by
  rw [birkhoffSum, birkhoffSum, ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ Finset.range n, (f (T^[i] z) - f (T^[i] x))| ≤
        ∑ i ∈ Finset.range n, |f (T^[i] z) - f (T^[i] x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (potentialVariation f r).toReal := by
      apply Finset.sum_le_sum
      intro i hi
      have hdist : dist (T^[i] z) (T^[i] x) ≤ r := by
        rw [dist_comm]
        exact le_of_lt (Dynamics.mem_dynEntourage.mp hz i (Finset.mem_range.mp hi))
      have hvar : ENNReal.ofReal |f (T^[i] z) - f (T^[i] x)| ≤
          potentialVariation f r :=
        le_iSup_of_le (T^[i] z) (le_iSup₂_of_le (T^[i] x) hdist le_rfl)
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
        ENNReal.toReal_mono (ne_of_lt hω) hvar
    _ = n * (potentialVariation f r).toReal := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Finite variation bounds the supremum by the center sum plus the order times variation.
Blueprint node `pack:supweight`. -/
theorem supWeightBounds_upper (T : X → X) (f : X → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (x : X) (r : ℝ) (hr : 0 < r) (hω : potentialVariation f r < ⊤) :
    bowenPotentialSup T f n x r ≤
      ((birkhoffSum T f n x + n * (potentialVariation f r).toReal : ℝ) : EReal) := by
  have _ := hn
  have _ := hr
  unfold bowenPotentialSup
  refine iSup₂_le fun z hz ↦ EReal.coe_le_coe_iff.mpr ?_
  have hdiff := abs_birkhoffSum_sub_le_mul_variation T f n x z r hω hz
  linarith [(abs_le.mp hdiff).2]

/-- Finite variation gives a real supremum before any real-valued reduction is used.
Blueprint node `pack:supweight`. -/
theorem supWeightBounds_finite (T : X → X) (f : X → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (x : X) (r : ℝ) (hr : 0 < r) (hω : potentialVariation f r < ⊤) :
    ∃ w : ℝ, bowenPotentialSup T f n x r = (w : EReal) := by
  have htop : bowenPotentialSup T f n x r < ⊤ :=
    (supWeightBounds_upper T f n hn x r hr hω).trans_lt (EReal.coe_lt_top _)
  have hbot : ⊥ < bowenPotentialSup T f n x r :=
    (EReal.bot_lt_coe _).trans_le (supWeightBounds T f n hn x r hr hω)
  exact ⟨(bowenPotentialSup T f n x r).toReal,
    (EReal.coe_toReal htop.ne hbot.ne').symm⟩

/-- Bowen-close centers have Birkhoff sums differing by at most the order times variation.
Blueprint node `pack:supweight`. -/
theorem supWeightBounds_birkhoff (T : X → X) (f : X → ℝ) (n : ℕ)
    (x y : X) (r : ℝ) (hω : potentialVariation f r < ⊤)
    (hxy : bowenDist T n x y < r) :
    |birkhoffSum T f n x - birkhoffSum T f n y| ≤
      n * (potentialVariation f r).toReal := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [abs_sub_comm]
  exact abs_birkhoffSum_sub_le_mul_variation T f n x y r hω
    ((bowen_ball_dense_iff T n hn x y r).mpr hxy)

/-- A maximal separated net bounds the covering sum at the doubled radius.
Blueprint node `pack:span-sep`. -/
theorem pressureSpanSep [SeparableSpace X] (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (Z : Set X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (hω : potentialVariation f (2 * r) < ⊤) :
    partitionSum T f .supremum Z n (2 * r) ≤ separatedPressureSum T f Z n (2 * r) := by
  have _ := hω
  obtain ⟨F, hF, hsep, hcount, _, hcover⟩ :=
    countableSeparatedMaximalNet T hT Z n hn (2 * r) (mul_pos zero_lt_two hr)
  calc
    partitionSum T f .supremum Z n (2 * r) ≤
        partitionCoverCost T f .supremum F n (2 * r) :=
      iInf_le_of_le F (iInf_le_of_le ⟨hcount, hcover⟩ le_rfl)
    _ ≤ separatedPressureSum T f Z n (2 * r) :=
      le_iSup₂_of_le F ⟨hF, hsep⟩ le_rfl

/-- A separated set assigns injectively to the centers of a cover of half its separation. -/
private lemma exists_injective_bowenBall_assignment
    (T : X → X) (F E : Set X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ)
    (hcover : F ⊆ ⋃ x ∈ E, bowenBall T n x r)
    (hsep : IsBowenSeparated T n (2 * r) F) :
    ∃ π : F → E, Function.Injective π ∧
      ∀ y : F, (y : X) ∈ bowenBall T n (π y) r := by
  have hcovered : ∀ y : F, ∃ e : E, (y : X) ∈ bowenBall T n (e : X) r := by
    intro y
    obtain ⟨e, he, hy⟩ := Set.mem_iUnion₂.mp (hcover y.property)
    exact ⟨⟨e, he⟩, hy⟩
  choose π hπ using hcovered
  refine ⟨π, ?_, hπ⟩
  intro y₁ y₂ heq
  by_contra hne
  have hsep' := hsep y₁.property y₂.property (Subtype.coe_ne_coe.mpr hne)
  have hy₁ := hπ y₁
  rw [heq] at hy₁
  have hd₁ := (bowen_ball_dense_iff T n hn (π y₂) y₁ r).mp hy₁
  have hd₂ := (bowen_ball_dense_iff T n hn (π y₂) y₂ r).mp (hπ y₂)
  rw [bowen_dist_comm T n (π y₂) y₁] at hd₁
  have htri := bowen_ball_dense_triangle T n (y₁ : X) (π y₂) y₂
  linarith

/-- Moving the center within a Bowen ball and doubling the weight radius costs at most
an exponential factor given by the potential variation. Blueprint node `pack:span-sep`. -/
theorem pressureBallWeight_le_mul_of_mem_bowenBall
    (T : X → X) (f : X → ℝ) (n : ℕ) (r : ℝ)
    (hω : potentialVariation f (2 * r) < ⊤)
    (y x : X) (hy : y ∈ bowenBall T n x r) :
    pressureBallWeight T f .supremum n y (2 * r) ≤
      (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        pressureBallWeight T f .supremum n x r := by
  dsimp [pressureBallWeight]
  refine iSup₂_le fun z hz ↦ ?_
  have hdiff := abs_birkhoffSum_sub_le_mul_variation T f n y z (2 * r) hω hz
  have hb : birkhoffSum T f n z ≤
      (n : ℝ) * (potentialVariation f (2 * r)).toReal + birkhoffSum T f n y := by
    linarith [(abs_le.mp hdiff).2]
  calc
    (2 : ℝ≥0∞) ^ (birkhoffSum T f n z : ℝ) ≤ (2 : ℝ≥0∞) ^
        ((n : ℝ) * (potentialVariation f (2 * r)).toReal + birkhoffSum T f n y) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hb
    _ = (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        (2 : ℝ≥0∞) ^ (birkhoffSum T f n y : ℝ) :=
      ENNReal.rpow_add _ _ (by norm_num) (by norm_num)
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup₂_of_le y hy le_rfl)

/-- A pointwise bound along an injection bounds the sum by the scaled sum on the target. -/
theorem tsum_le_mul_tsum_of_injective
    {α β : Type*} (π : α → β) (hπ : Function.Injective π)
    (a : α → ℝ≥0∞) (b : β → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ y, a y ≤ c * b (π y)) :
    (∑' y, a y) ≤ c * ∑' x, b x := by
  calc
    (∑' y, a y) ≤ ∑' y, c * b (π y) := ENNReal.tsum_le_tsum h
    _ = c * ∑' y, b (π y) := ENNReal.tsum_mul_left
    _ ≤ c * ∑' x, b x :=
      mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hπ b)

/-- A Bowen cover bounds the weighted sum on a separated set with twice the radius. -/
private lemma partitionCoverCost_le_mul_of_separated
    (T : X → X) (f : X → ℝ) (n : ℕ) (hn : 1 ≤ n) (r : ℝ)
    (hω : potentialVariation f (2 * r) < ⊤)
    (F E : Set X) (hsep : IsBowenSeparated T n (2 * r) F)
    (hcover : F ⊆ ⋃ y ∈ E, bowenBall T n y r) :
    partitionCoverCost T f .supremum F n (2 * r) ≤
      (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        partitionCoverCost T f .supremum E n r := by
  obtain ⟨π, hπ, hball⟩ := exists_injective_bowenBall_assignment T F E n hn r hcover hsep
  exact tsum_le_mul_tsum_of_injective π hπ _ _ _ fun y ↦
    pressureBallWeight_le_mul_of_mem_bowenBall T f n r hω y (π y) (hball y)

/-- Injective assignment to covering centers bounds separated sums with the precise error.
Blueprint node `pack:span-sep`. -/
theorem pressureSpanSep_upper [SeparableSpace X] (T : X → X) (hT : Continuous T)
    (f : X → ℝ) (Z : Set X) (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (hω : potentialVariation f (2 * r) < ⊤) :
    separatedPressureSum T f Z n (2 * r) ≤
      (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) *
        partitionSum T f .supremum Z n r := by
  have _ := hT
  have _ := hr
  unfold separatedPressureSum
  refine iSup₂_le fun F hF ↦ ?_
  have hc0 : (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) ≠ 0 :=
    (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have hct : (2 : ℝ≥0∞) ^ ((n : ℝ) * (potentialVariation f (2 * r)).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  unfold partitionSum
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun E ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  exact le_iInf fun hE ↦
    partitionCoverCost_le_mul_of_separated T f n hn r hω F E hF.2 (hF.1.trans hE.2)

/-- Increasing the order cutoff decreases packing content.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_antitone_cutoff (T : X → X) (f : X → ℝ)
    (Z : Set X) (s r : ℝ) : Antitone (packingPressureContent T f Z s r) := by
  intro N₁ N₂ hN
  unfold packingPressureContent
  apply iSup_mono
  intro F
  apply iSup_mono'
  intro hF
  refine ⟨?_, le_rfl⟩
  unfold IsBowenPacking at *
  obtain ⟨hF_count, hF_prop, hF_disj⟩ := hF
  refine ⟨hF_count, fun a ha ↦ ?_, hF_disj⟩
  obtain ⟨ha1, ha2⟩ := hF_prop a ha
  exact ⟨ha1, le_trans (max_le_max_left 1 hN) ha2⟩

/-- Enlarging the set increases cutoff packing content.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_mono_content (T : X → X) (f : X → ℝ)
    (s r : ℝ) (N : ℕ) : Monotone (fun Z => packingPressureContent T f Z s r N) := by
  intro Z1 Z2 hZ
  unfold packingPressureContent
  refine iSup_mono (fun F ↦ ?_)
  refine iSup_mono' (fun hF ↦ ?_)
  refine ⟨?_, le_rfl⟩
  rcases hF with ⟨hF1, hF2, hF3⟩
  refine ⟨hF1, ?_, hF3⟩
  intro a ha
  have h := hF2 a ha
  exact ⟨hZ h.1, h.2⟩

/-- The cutoff content of the empty set is zero.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_empty_content (T : X → X) (f : X → ℝ)
    (s r : ℝ) (N : ℕ) : packingPressureContent T f ∅ s r N = 0 := by
  dsimp [packingPressureContent]
  apply le_antisymm
  · apply iSup_le
    intro F
    apply iSup_le
    intro hF
    have h_emp : F = ∅ := by
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      rcases hF.2.1 a ha with ⟨ha1, ha2⟩
      exact ha1
    rw [h_emp]
    dsimp [packingPressureSum]
    rw [tsum_empty]
  · apply zero_le

/-- The packing pre-content is monotone in the covered set. -/
private lemma packingPressurePrecontent_mono (T : X → X) (f : X → ℝ) (s r : ℝ) :
    Monotone (fun Z ↦ packingPressurePrecontent T f Z s r) := by
  intro Z₁ Z₂ hZ
  exact iInf_mono fun N ↦ iInf_mono fun _ ↦ pressureOuterEnvelope_mono_content T f s r N hZ

/-- The packing pre-content vanishes on the empty set. -/
private lemma packingPressurePrecontent_empty (T : X → X) (f : X → ℝ) (s r : ℝ) :
    packingPressurePrecontent T f ∅ s r = 0 := by
  apply le_antisymm _ bot_le
  exact iInf_le_of_le 1 (iInf_le_of_le le_rfl
    (le_of_eq (pressureOuterEnvelope_empty_content T f s r 1)))

/-- The outer measure generated by packing pre-content. -/
private noncomputable def packingPressureOuterMeasure
    (T : X → X) (f : X → ℝ) (s r : ℝ) : MeasureTheory.OuterMeasure X :=
  MeasureTheory.OuterMeasure.ofFunction (packingPressurePrecontent T f · s r)
    (packingPressurePrecontent_empty T f s r)

/-- Restricting covering pieces to the covered set preserves the outer-measure infimum. -/
private lemma pressureOuterEnvelope_eq_outerMeasure
    (T : X → X) (f : X → ℝ) (Z : Set X) (s r : ℝ) :
    pressureOuterEnvelope T f Z s r = packingPressureOuterMeasure T f s r Z := by
  unfold pressureOuterEnvelope packingPressureOuterMeasure
  rw [MeasureTheory.OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · refine le_iInf fun Y ↦ le_iInf fun hcover ↦ ?_
    have hrestricted : (∀ j, Y j ∩ Z ⊆ Z) ∧ Z ⊆ ⋃ j, Y j ∩ Z := by
      refine ⟨fun _ ↦ Set.inter_subset_right, ?_⟩
      intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hz)
      exact Set.mem_iUnion.mpr ⟨j, hj, hz⟩
    apply le_trans (b := ∑' j, packingPressurePrecontent T f (Y j ∩ Z) s r)
    · exact iInf_le_of_le (fun j ↦ Y j ∩ Z) (iInf_le_of_le hrestricted le_rfl)
    · exact ENNReal.tsum_le_tsum fun j ↦
        packingPressurePrecontent_mono T f s r Set.inter_subset_left
  · exact le_iInf fun Y ↦ le_iInf fun hcover ↦
      iInf_le_of_le Y (iInf_le_of_le hcover.2 le_rfl)

/-- The outer envelope is monotone in the covered set.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_mono (T : X → X) (f : X → ℝ) (s r : ℝ) :
    Monotone (fun Z => pressureOuterEnvelope T f Z s r) := by
  intro Z₁ Z₂ hZ
  dsimp only
  rw [pressureOuterEnvelope_eq_outerMeasure, pressureOuterEnvelope_eq_outerMeasure]
  exact (packingPressureOuterMeasure T f s r).mono hZ

/-- Countable subadditivity belongs to the outer envelope, not to the pre-content.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_subadditive (T : X → X) (f : X → ℝ)
    (Y : ℕ → Set X) (s r : ℝ) :
    pressureOuterEnvelope T f (⋃ j, Y j) s r ≤ ∑' j, pressureOuterEnvelope T f (Y j) s r := by
  simp_rw [pressureOuterEnvelope_eq_outerMeasure]
  exact MeasureTheory.measure_iUnion_le Y

/-- A countable union of zero-envelope sets has zero envelope.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_countable_zero (T : X → X) (f : X → ℝ)
    (Y : ℕ → Set X) (s r : ℝ) (hY : ∀ j, pressureOuterEnvelope T f (Y j) s r = 0) :
    pressureOuterEnvelope T f (⋃ j, Y j) s r = 0 := by
  refine le_antisymm ?_ zero_le
  simpa only [hY, tsum_zero] using pressureOuterEnvelope_subadditive T f Y s r

/-- The signed critical pressure of the empty set is negative infinity.
Blueprint node `pack:outer`. -/
theorem pressureOuterEnvelope_empty (T : X → X) (f : X → ℝ) (r : ℝ) :
    packingPressureAt T f ∅ r = ⊥ := by
  have hzero : ∀ s, pressureOuterEnvelope T f ∅ s r = 0 := by
    intro s
    rw [pressureOuterEnvelope_eq_outerMeasure]
    exact (packingPressureOuterMeasure T f s r).empty
  simp only [packingPressureAt, hzero, iInf_pos]
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro y
  exact (iInf_le (fun s : ℝ ↦ (s : EReal)) (y - 1)).trans_lt
    (EReal.coe_lt_coe_iff.mpr (sub_one_lt y))

/-- Increasing the exponent decreases a packing sum by the cutoff exponential factor. -/
private lemma packingPressureSum_le_mul_of_lt
    (T : X → X) (f : X → ℝ) (Z : Set X) (s t r : ℝ)
    (hst : s < t) (N : ℕ) (F : Set (X × ℕ))
    (hF : IsBowenPacking T Z r N F) :
    packingPressureSum T f t r F ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) * packingPressureSum T f s r F := by
  unfold packingPressureSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a ↦ ?_
  have hn : (N : ℝ) ≤ a.val.2 := by
    exact_mod_cast (le_max_right 1 N).trans (hF.2.1 a a.property).2
  have hexp : -(t - s) * (a.val.2 : ℝ) ≤ -(t - s) * (N : ℝ) :=
    mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr (sub_nonneg.mpr hst.le))
  have hsplit : -t * (a.val.2 : ℝ) = -(t - s) * (a.val.2 : ℝ) + -s * (a.val.2 : ℝ) := by
    ring
  rw [hsplit, ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ← mul_assoc]
  exact mul_le_mul' (mul_le_mul'
    (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp) le_rfl) le_rfl

/-- Increasing the exponent decreases cutoff content by an exponential factor. -/
private lemma packingPressureContent_le_mul_of_lt
    (T : X → X) (f : X → ℝ) (Z : Set X) (s t r : ℝ)
    (hst : s < t) (N : ℕ) :
    packingPressureContent T f Z t r N ≤
      (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) * packingPressureContent T f Z s r N := by
  refine iSup₂_le fun F hF ↦ ?_
  exact (packingPressureSum_le_mul_of_lt T f Z s t r hst N F hF).trans
    (mul_le_mul' le_rfl (le_iSup₂_of_le F hF le_rfl))

/-- Finite cutoff content forces pre-content to vanish at every larger exponent. -/
private lemma packingPressurePrecontent_eq_zero_of_finite_content
    (T : X → X) (f : X → ℝ) (Z : Set X) (s t r : ℝ)
    (hst : s < t) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hfinite : packingPressureContent T f Z s r N₀ < ⊤) :
    packingPressurePrecontent T f Z t r = 0 := by
  have hq : (2 : ℝ≥0∞) ^ (-(t - s)) < 1 :=
    ENNReal.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (neg_neg_of_pos (sub_pos.mpr hst))
  have hlim : Tendsto
      (fun N : ℕ ↦ (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) *
        packingPressureContent T f Z s r N₀)
      atTop (𝓝 0) := by
    simpa only [ENNReal.rpow_mul_natCast, zero_mul] using
      (ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
        (Or.inr (ne_of_lt hfinite)))
  have hb : ∀ᶠ N : ℕ in atTop,
      packingPressurePrecontent T f Z t r ≤
        (2 : ℝ≥0∞) ^ (-(t - s) * (N : ℝ)) *
          packingPressureContent T f Z s r N₀ := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hpos : 1 ≤ N := hN₀.trans hN
    have hp : packingPressurePrecontent T f Z t r ≤
        packingPressureContent T f Z t r N := by
      unfold packingPressurePrecontent
      exact iInf_le_of_le N (iInf_le_of_le hpos le_rfl)
    exact hp.trans
      ((packingPressureContent_le_mul_of_lt T f Z s t r hst N).trans
        (mul_le_mul' le_rfl
          (pressureOuterEnvelope_antitone_cutoff T f Z s r hN)))
  exact le_antisymm (ge_of_tendsto hlim hb) bot_le

/-- Finite packing outer content becomes zero after any strict real exponent increase.
Blueprint node `pack:pressure-dichotomy`. -/
theorem pressureDichotomyScaleLimit (T : X → X) (f : X → ℝ) (Z : Set X)
    (s t r : ℝ) (hst : s < t) (hr : 0 < r) (hω : potentialVariation f r < ⊤)
    (hfinite : pressureOuterEnvelope T f Z s r < ⊤) :
    pressureOuterEnvelope T f Z t r = 0 := by
  have _ := hr
  have _ := hω
  obtain ⟨Y, hY⟩ := iInf_lt_iff.mp hfinite
  obtain ⟨hcover, hsum⟩ := iInf_lt_iff.mp hY
  apply le_antisymm _ bot_le
  apply le_trans (b := ∑' j, packingPressurePrecontent T f (Y j) t r)
  · exact iInf_le_of_le Y (iInf_le_of_le hcover le_rfl)
  apply le_of_eq
  apply ENNReal.tsum_eq_zero.mpr
  intro j
  have hj : packingPressurePrecontent T f (Y j) s r < ⊤ :=
    (ENNReal.le_tsum (f := fun i ↦ packingPressurePrecontent T f (Y i) s r) j).trans_lt hsum
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp hj
  obtain ⟨hpos, hfin⟩ := iInf_lt_iff.mp hN
  exact packingPressurePrecontent_eq_zero_of_finite_content T f (Y j) s t r hst N hpos hfin

end Kolmogorov.PointToSet
