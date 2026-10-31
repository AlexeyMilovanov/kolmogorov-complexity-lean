/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.Dynamics.BirkhoffComputability

/-!
# Bowen balls and finite-scale costs

For continuous dynamics on a presented metric space, positive-order Bowen distances
induce the original topology, and positive-radius Bowen balls contain ideal points.
Uniformly continuous potentials have vanishing small-scale oscillation, which also
controls their Birkhoff sums. These facts implement blueprint nodes `metric:bowen`
and `metric:oscillation`.

We also prove enumerability of strict comparisons with computable real families
(`metric:birkhoff`) and define finite-scale pressure and BS costs as indexed infima.
Finite complexity sublevels give attainment under local bounds (`metric:min`).
The pointwise quantities and presentation-change results use these comparisons,
dense realizers, and attained costs.
-/

namespace Kolmogorov.PointToSet
open Filter
open scoped Topology ENNReal Computability
variable {X : Type*} [MetricSpace X]

/-- Twice an inverse power of two is smaller than any positive real tolerance. -/
lemma exists_two_mul_inv_two_pow_lt (d : ℝ) (hd : 0 < d) : ∃ p : ℕ, (2 : ℝ) * (2^p : ℝ)⁻¹ < d := by
  have ⟨p, hp⟩ : ∃ p : ℕ, (2:ℝ)⁻¹ ^ p < d / 2 := by
    exact exists_pow_lt_of_lt_one (half_pos hd) (by norm_num)
  use p
  have h_pow : (2⁻¹ : ℝ) ^ p = (2^p : ℝ)⁻¹ := by simp [inv_pow]
  rw [h_pow] at hp
  linarith

/-- The rational sequence of inverse powers of two is computable. -/
lemma computable_rat_inv_two_pow : Computable (fun (p : ℕ) ↦ (2^p : ℚ)⁻¹) := by
  have H : (fun (p : ℕ) ↦ (2^p : ℚ)⁻¹) = fun p ↦ (1 : ℚ) / ((2^p : ℕ) : ℚ) := by
    ext p
    have h2 : ((2^p : ℕ) : ℚ) = (2:ℚ)^p := by simp
    rw [h2, inv_eq_one_div]
  rw [H]
  apply computable_of_num_den (Computable.const (1 : ℤ)) comp_pow
  · intro p
    positivity
  · intro p
    rfl

/-- A Boolean conditional preserves computability relative to a fixed oracle family. -/
lemma computable_in_cond {α σ : Type*} [Primcodable α] [Primcodable σ]
    {O : Set (ℕ →. ℕ)} {c : α → Bool} {f g : α → σ}
    (hc : ComputableIn O c) (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a ↦ cond (c a) (f a) (g a)) :=
  (Computable.cond Computable.fst (Computable.fst.comp Computable.snd)
    (Computable.snd.comp Computable.snd)).computableIn.comp (hc.pair (hf.pair hg))

/-- Strict rational upper comparisons with a uniform computable real family are enumerable,
with the threshold part of the ambient index.
Blueprint node `metric:birkhoff`. -/
theorem birkhoff_computableIn_lt {α : Type*} [Primcodable α] (A : Set ℕ) (v : α → ℝ)
    (hv : IsComputableRealFamilyIn A v) :
    IsREIn A (fun iq : α × ℚ => v iq.1 < (iq.2 : ℝ)) := by
  rcases hv with ⟨q, hq_comp, hq_approx⟩
  let f : α × ℚ →. ℕ := fun iq ↦
    Nat.rfindOpt (fun p ↦ cond (decide (q (iq.1, p) + (2^p : ℚ)⁻¹ < iq.2)) (some p) none)
  have hf : PartrecIn {charOracle A} f := by
    apply PartrecIn.rfindOpt
    have hqArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ q (w.1.1, w.2)) :=
      hq_comp.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    have hεArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (2^w.2 : ℚ)⁻¹) :=
      computable_rat_inv_two_pow.computableIn.comp Computable.snd.computableIn
    have hsum : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ q (w.1.1, w.2) + (2^w.2 : ℚ)⁻¹) :=
      (Computable₂.computableIn₂ computable₂_ratAdd).comp hqArg hεArg
    have hrArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ w.1.2) :=
      (Computable.snd.comp Computable.fst).computableIn
    have hcmp : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ decide (q (w.1.1, w.2) + (2^w.2 : ℚ)⁻¹ < w.1.2)) :=
      (Computable₂.computableIn₂ computable₂_ratLt).comp hsum hrArg
    have hsome : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ some w.2) :=
      (Primrec.option_some.to_comp.comp Computable.snd).computableIn
    have hnone : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (none : Option ℕ)) :=
      (Computable.const none).computableIn
    have H : ComputableIn {charOracle A}
        (fun (w : (α × ℚ) × ℕ) ↦
          cond (decide (q (w.1.1, w.2) + (2^w.2 : ℚ)⁻¹ < w.1.2)) (some w.2) none) :=
      computable_in_cond hcmp hsome hnone
    exact ComputableIn₂.mk H
  use f
  constructor
  · exact hf
  · intro ⟨i, r⟩
    simp only [f]
    rw [Nat.rfindOpt_dom]
    constructor
    · intro h
      have h_sub : 0 < (r : ℝ) - v i := sub_pos.mpr h
      obtain ⟨p, hp⟩ := exists_two_mul_inv_two_pow_lt _ h_sub
      use p, p
      have h_lt : q (i, p) + (2^p : ℚ)⁻¹ < r := by
        rw [← Rat.cast_lt (K := ℝ)]
        push_cast
        have h1 := hq_approx i p
        have h1' : (q (i, p) : ℝ) < v i + 2⁻¹ ^ p := sub_lt_iff_lt_add'.mp (abs_lt.mp h1).2
        have h_pow : (2⁻¹ : ℝ) ^ p = (2^p : ℝ)⁻¹ := by simp [inv_pow]
        rw [h_pow] at h1'
        linarith
      simp [h_lt, Option.mem_def]
    · intro h_dom
      rcases h_dom with ⟨p, a, hhp⟩
      simp only [Option.mem_def, Bool.cond_decide] at hhp
      split_ifs at hhp with h_lt
      have h_approx := hq_approx i p
      have h_pow : (2⁻¹ : ℝ) ^ p = (2^p : ℝ)⁻¹ := by simp [inv_pow]
      rw [h_pow] at h_approx
      have h_lt' : (q (i, p) : ℝ) + (2^p : ℝ)⁻¹ < (r : ℝ) := by
        have h2 : ((q (i, p) + (2^p : ℚ)⁻¹ : ℚ) : ℝ) < (r : ℝ) :=
          Rat.cast_lt.mpr (decide_eq_true_iff.mp h_lt)
        push_cast at h2
        exact h2
      have h_approx2 : -(2^p : ℝ)⁻¹ < (q (i, p) : ℝ) - v i := (abs_lt.mp h_approx).1
      linarith

/-- A strict lower comparison holds exactly when some rational approximation is separated. -/
private lemma rat_lt_iff_exists_separated_approx {α : Type*}
    (v : α → ℝ) (q : α × ℕ → ℚ)
    (hq_err : ∀ i p, |(q (i, p) : ℝ) - v i| < (2 : ℝ)⁻¹ ^ p)
    (iq : α × ℚ) :
    (iq.2 : ℝ) < v iq.1 ↔ ∃ p : ℕ, iq.2 + (2 : ℚ)⁻¹ ^ p < q (iq.1, p) := by
  constructor
  · intro h
    have h_sub : 0 < v iq.1 - (iq.2 : ℝ) := sub_pos.mpr h
    obtain ⟨p, hp⟩ := exists_two_mul_inv_two_pow_lt _ h_sub
    use p
    rw [← Rat.cast_lt (K := ℝ)]
    push_cast
    have h1 := hq_err iq.1 p
    have h1' : v iq.1 - (2:ℝ)⁻¹ ^ p < (q (iq.1, p) : ℝ) := by
      have h2 : -(2:ℝ)⁻¹ ^ p < (q (iq.1, p) : ℝ) - v iq.1 := (abs_lt.mp h1).1
      linarith
    have h_pow : (2^p : ℝ)⁻¹ = (2⁻¹ : ℝ) ^ p := by simp [inv_pow]
    rw [h_pow] at hp
    linarith
  · intro h
    rcases h with ⟨p, hp⟩
    have hp' : (iq.2 : ℝ) + (2:ℝ)⁻¹ ^ p < (q (iq.1, p) : ℝ) := by
      have : ((iq.2 + (2 : ℚ)⁻¹ ^ p : ℚ) : ℝ) < (q (iq.1, p) : ℝ) := Rat.cast_lt.mpr hp
      push_cast at this
      exact this
    have h1 := hq_err iq.1 p
    have h1' : (q (iq.1, p) : ℝ) < v iq.1 + (2:ℝ)⁻¹ ^ p := by
      have h2 : (q (iq.1, p) : ℝ) - v iq.1 < (2:ℝ)⁻¹ ^ p := (abs_lt.mp h1).2
      linarith
    linarith

/-- Searching for a rational approximation above a threshold is relatively enumerable. -/
private lemma isREIn_exists_separated_approx {α : Type*} [Primcodable α] (A : Set ℕ)
    (q : α × ℕ → ℚ) (hq : ComputableIn {charOracle A} q) :
    IsREIn A (fun iq : α × ℚ ↦ ∃ p : ℕ, iq.2 + (2 : ℚ)⁻¹ ^ p < q (iq.1, p)) := by
  let f : α × ℚ →. ℕ := fun iq ↦
    Nat.rfindOpt (fun p ↦ cond (decide (iq.2 + (2^p : ℚ)⁻¹ < q (iq.1, p))) (some p) none)
  have hf : PartrecIn {charOracle A} f := by
    apply PartrecIn.rfindOpt
    have hqArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ q (w.1.1, w.2)) :=
      hq.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    have hεArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (2^w.2 : ℚ)⁻¹) :=
      computable_rat_inv_two_pow.computableIn.comp Computable.snd.computableIn
    have hrArg : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ w.1.2) :=
      (Computable.snd.comp Computable.fst).computableIn
    have hsum : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ w.1.2 + (2^w.2 : ℚ)⁻¹) :=
      (Computable₂.computableIn₂ computable₂_ratAdd).comp hrArg hεArg
    have hcmp : ComputableIn {charOracle A}
        (fun w : (α × ℚ) × ℕ ↦ decide (w.1.2 + (2^w.2 : ℚ)⁻¹ < q (w.1.1, w.2))) :=
      (Computable₂.computableIn₂ computable₂_ratLt).comp hsum hqArg
    have hsome : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ some w.2) :=
      (Primrec.option_some.to_comp.comp Computable.snd).computableIn
    have hnone : ComputableIn {charOracle A} (fun w : (α × ℚ) × ℕ ↦ (none : Option ℕ)) :=
      (Computable.const none).computableIn
    have H : ComputableIn {charOracle A}
        (fun (w : (α × ℚ) × ℕ) ↦
          cond (decide (w.1.2 + (2^w.2 : ℚ)⁻¹ < q (w.1.1, w.2))) (some w.2) none) :=
      computable_in_cond hcmp hsome hnone
    exact ComputableIn₂.mk H
  use f
  constructor
  · exact hf
  · intro ⟨i, r⟩
    simp only [f]
    rw [Nat.rfindOpt_dom]
    constructor
    · intro h
      rcases h with ⟨p, hp⟩
      use p, p
      have h_lt : r + (2^p : ℚ)⁻¹ < q (i, p) := by
        have h_pow : (2 : ℚ)⁻¹ ^ p = (2^p : ℚ)⁻¹ := by simp [inv_pow]
        rwa [← h_pow]
      simp [h_lt, Option.mem_def]
    · intro h_dom
      rcases h_dom with ⟨p, a, hhp⟩
      simp only [Option.mem_def, Bool.cond_decide] at hhp
      split_ifs at hhp with h_lt
      use p
      have h_pow : (2 : ℚ)⁻¹ ^ p = (2^p : ℚ)⁻¹ := by simp [inv_pow]
      rwa [h_pow]

/-- Strict rational lower comparisons with a uniform computable real family are also
enumerable. Blueprint node `metric:birkhoff`. -/
theorem birkhoff_computableIn_gt {α : Type*} [Primcodable α] (A : Set ℕ) (v : α → ℝ)
    (hv : IsComputableRealFamilyIn A v) :
    IsREIn A (fun iq : α × ℚ => (iq.2 : ℝ) < v iq.1) := by
  rcases hv with ⟨q, hq, hq_err⟩
  have h_equiv : (fun iq : α × ℚ ↦ (iq.2 : ℝ) < v iq.1) =
                 (fun iq : α × ℚ ↦ ∃ p : ℕ, iq.2 + (2 : ℚ)⁻¹ ^ p < q (iq.1, p)) := by
    funext iq
    exact propext (rat_lt_iff_exists_separated_approx v q hq_err iq)
  rw [h_equiv]
  exact isREIn_exists_separated_approx A q hq

/-- Every finite-order Bowen distance vanishes on the diagonal. -/
private lemma bowenDist_self (T : X → X) (n : ℕ) (x : X) : bowenDist T n x x = 0 := by
  dsimp [bowenDist]
  simp

/-- Every finite-order Bowen distance is symmetric. -/
lemma bowen_dist_comm (T : X → X) (n : ℕ) (x y : X) : bowenDist T n x y = bowenDist T n y x := by
  dsimp [bowenDist]
  simp [nndist_comm]

/-- A point lies in a Bowen ball iff its first `n` iterates stay `ε`-close to those of the
center. Blueprint node `metric:bowen`. -/
lemma mem_bowenBall_iff {T : X → X} {n : ℕ} {x y : X} {ε : ℝ} :
    y ∈ bowenBall T n x ε ↔ ∀ k < n, dist (T^[k] x) (T^[k] y) < ε := by
  simp only [bowenBall, Set.mem_ofPred_eq, Dynamics.mem_dynEntourage]

/-- A point belongs to its own Bowen ball of every positive radius. -/
lemma self_mem_bowenBall (T : X → X) (n : ℕ) (x : X) (ε : ℝ) (hε : 0 < ε) :
    x ∈ bowenBall T n x ε :=
  Dynamics.mem_dynEntourage.mpr fun _ _ ↦ by simpa only [Set.mem_ofPred_eq, dist_self] using hε

/-- Membership in a Bowen ball is symmetric in the center and the point. -/
lemma mem_bowenBall_symm {T : X → X} {n : ℕ} {x y : X} {r : ℝ}
    (h : y ∈ bowenBall T n x r) : x ∈ bowenBall T n y r :=
  mem_bowenBall_iff.2 fun k hk ↦ by rw [dist_comm]; exact mem_bowenBall_iff.1 h k hk

/-- Bowen balls are monotone in the radius. Blueprint node `metric:bowen`. -/
lemma bowenBall_subset_of_le (T : X → X) (n : ℕ) (x : X) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    bowenBall T n x ε₁ ⊆ bowenBall T n x ε₂ := fun _ hy ↦
  mem_bowenBall_iff.2 fun k hk ↦ (mem_bowenBall_iff.1 hy k hk).trans_le h

/-- The Bowen ball of order one of the identity is the metric ball. -/
lemma bowenBall_id_one (x : X) (r : ℝ) : bowenBall id 1 x r = Metric.ball x r := by
  ext y
  simp only [bowenBall, Dynamics.dynEntourage_one, Set.mem_ofPred_eq, Metric.mem_ball]
  rw [dist_comm]

/-- Bowen distance obeys the triangle inequality with coefficient one.
Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_triangle (T : X → X) (n : ℕ) (x y z : X) :
    bowenDist T n x z ≤ bowenDist T n x y + bowenDist T n y z := by
  dsimp [bowenDist]
  rw [← NNReal.coe_add, NNReal.coe_le_coe]
  apply Finset.sup_le
  intro k hk
  exact (nndist_triangle (T^[k] x) (T^[k] y) (T^[k] z)).trans
    (add_le_add (Finset.le_sup (f := fun j ↦ nndist (T^[j] x) (T^[j] y)) hk)
      (Finset.le_sup (f := fun j ↦ nndist (T^[j] y) (T^[j] z)) hk))

/-- Bowen balls are open for continuous dynamics. Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_open (T : X → X) (hT : Continuous T) (n : ℕ) (x : X) (ε : ℝ) :
    IsOpen (bowenBall T n x ε) := by
  have H : IsOpen {z : X × X | dist z.1 z.2 < ε} := isOpen_lt continuous_dist continuous_const
  have H2 := isOpen.dynEntourage hT H n
  exact H2.preimage (Continuous.prodMk_right x)

/-- A positive-order Bowen ball is the strict sublevel of its Bowen distance.
Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_iff (T : X → X) (n : ℕ) (hn : 1 ≤ n) (x y : X) (ε : ℝ) :
    y ∈ bowenBall T n x ε ↔ bowenDist T n x y < ε := by
  unfold bowenBall bowenDist
  simp only [Set.mem_ofPred_eq, Dynamics.mem_dynEntourage]
  by_cases hε : 0 < ε
  · lift ε to NNReal using hε.le
    rw [NNReal.coe_lt_coe]
    rw [Finset.sup_lt_iff]
    · constructor
      · intro h k hk
        rw [Finset.mem_range] at hk
        have := h k hk
        exact this
      · intro h k hk
        have := h k (Finset.mem_range.mpr hk)
        exact this
    · exact hε
  · constructor
    · intro h
      have h1 := h 0 (by omega)
      dsimp at h1
      have h2 := dist_nonneg (x := x) (y := y)
      linarith
    · intro h
      have h1 : ↑((Finset.range n).sup fun k ↦ nndist (T^[k] x) (T^[k] y)) ≥ (0:ℝ) :=
        NNReal.coe_nonneg _
      linarith

/-- The zeroth observation bounds the original distance by the Bowen distance. -/
private lemma dist_le_bowenDist (T : X → X) (n : ℕ) (hn : 1 ≤ n) (x y : X) :
    dist x y ≤ bowenDist T n x y := by
  exact NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun k ↦ nndist (T^[k] x) (T^[k] y))
      (Finset.mem_range.mpr hn))

/-- Bowen distance neighborhoods characterize the original open sets. -/
private lemma isOpen_iff_bowenDist (T : X → X) (hT : Continuous T)
    (n : ℕ) (hn : 1 ≤ n) (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, bowenDist T n x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hs x hx
    refine ⟨ε, hε, fun y hy ↦ hsub ?_⟩
    exact Metric.mem_ball.mpr (by
      rw [dist_comm]
      exact lt_of_le_of_lt (dist_le_bowenDist T n hn x y) hy)
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := h x hx
    refine ⟨bowenBall T n x ε, ?_, bowen_ball_dense_open T hT n x ε, ?_⟩
    · intro y hy
      exact hsub y ((bowen_ball_dense_iff T n hn x y ε).mp hy)
    · exact (bowen_ball_dense_iff T n hn x x ε).mpr (by rwa [bowenDist_self])

/-- Finite-order Bowen distance is a metric inducing the original topology for positive
orders and continuous dynamics. Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_metric (T : X → X) (hT : Continuous T) (n : ℕ) (hn : 1 ≤ n) :
    let d := bowenDist T n
    let τ := (inferInstance : TopologicalSpace X)
    ∃ m : MetricSpace X, (∀ x y, m.dist x y = d x y) ∧
      m.toUniformSpace.toTopologicalSpace = τ := by
  let m := MetricSpace.ofDistTopology (bowenDist T n) (bowenDist_self T n)
    (bowen_dist_comm T n) (bowen_ball_dense_triangle T n)
    (isOpen_iff_bowenDist T hT n hn)
    (fun x y h ↦ dist_eq_zero.mp
      (le_antisymm (h ▸ dist_le_bowenDist T n hn x y) dist_nonneg))
  exact ⟨m, fun _ _ ↦ rfl, rfl⟩

/-- Positive-radius Bowen balls contain their centers. Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_nonempty (T : X → X) (n : ℕ) (x : X) (ε : ℝ) (hε : 0 < ε) :
    (bowenBall T n x ε).Nonempty := by
  use x
  dsimp [bowenBall]
  rw [Dynamics.mem_dynEntourage]
  intro k _
  simp only [Set.mem_ofPred_eq]
  rw [dist_self]
  exact hε

/-- Every positive-radius Bowen ball of positive order contains an ideal point.
Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense (P : Presentation X) (T : X → X) (hT : Continuous T)
    (x : X) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ i, P.ι i ∈ bowenBall T n x ε := by
  apply P.dense.exists_mem_open (bowen_ball_dense_open T hT n x ε)
  exact ⟨x, (bowen_ball_dense_iff T n hn x x ε).mpr (by rwa [bowenDist_self])⟩

/-- Observing one more time can only shrink a Bowen ball. Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_succ (T : X → X) (n : ℕ) (x : X) (ε : ℝ) :
    bowenBall T (n + 1) x ε ⊆ bowenBall T n x ε := by
  intro y hy
  exact Dynamics.dynEntourage_mono subset_rfl (Nat.le_succ n) hy

/-- The order-zero ball is universal, matching observation of no times.
Blueprint node `metric:bowen`. -/
theorem bowen_ball_dense_zero (T : X → X) (x : X) (ε : ℝ) :
    bowenBall T 0 x ε = Set.univ := by
  dsimp [bowenBall]
  rw [Dynamics.dynEntourage_zero]
  rfl

/-- A uniformly continuous potential admits increasing scales for dyadic oscillation bounds. -/
private lemma exists_strictMono_oscillation_modulus
    (v : X → ℝ) (hv : UniformContinuous v) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      ∀ n p, q n ≤ p → ∀ x y,
        dist x y < 2 * dyadicRadius p →
          |v x - v y| ≤ (2 : ℝ)⁻¹ ^ n := by
  have h_tol : ∀ n : ℕ, 0 < (2 : ℝ)⁻¹ ^ n := fun n ↦ by positivity
  have h_delta : ∀ n : ℕ, ∃ δ > 0, ∀ x y, dist x y < δ → |v x - v y| ≤ (2 : ℝ)⁻¹ ^ n := by
    intro n
    have := Metric.uniformContinuous_iff.mp hv ((2 : ℝ)⁻¹ ^ n) (h_tol n)
    rcases this with ⟨δ, hδ_pos, hδ_prop⟩
    use δ, hδ_pos
    intro x y hxy
    have dist_eq : dist (v x) (v y) = |v x - v y| := Real.dist_eq (v x) (v y)
    rw [← dist_eq]
    exact (hδ_prop hxy).le
  choose δ hδ_pos hδ_prop using h_delta
  have h_tendsto : Tendsto (fun p ↦ 2 * dyadicRadius p) atTop (𝓝 0) := by
    have h1 : Tendsto (fun p ↦ dyadicRadius p) atTop (𝓝 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    have h2 : Tendsto (fun p ↦ 2 * dyadicRadius p) atTop (𝓝 (2 * 0)) :=
      Tendsto.const_mul 2 h1
    simpa using h2
  have h_c : ∀ n : ℕ, ∃ c : ℕ, ∀ p ≥ c, 2 * dyadicRadius p < δ n := by
    intro n
    have h_nhds := Metric.tendsto_atTop.mp h_tendsto (δ n) (hδ_pos n)
    rcases h_nhds with ⟨c, hc⟩
    use c
    intro p hp
    have := hc p hp
    rw [Real.dist_0_eq_abs] at this
    have h_pos : 0 ≤ 2 * dyadicRadius p := by
      dsimp [dyadicRadius]; positivity
    rwa [abs_of_nonneg h_pos] at this
  choose c hc using h_c
  let q : ℕ → ℕ := fun n ↦ Nat.recOn n (c 0) (fun m qm ↦ max (c (m + 1)) (qm + 1))
  have hq_strict_mono : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [q]
    exact lt_of_lt_of_le (Nat.lt_succ_self (q n)) (le_max_right (c (n + 1)) (q n + 1))
  have hq_c : ∀ n, c n ≤ q n := by
    intro n
    cases n
    · exact le_rfl
    · dsimp [q]
      exact le_max_left _ _
  use q, hq_strict_mono
  intro n p hqp x y hxy
  have hp_c : c n ≤ p := le_trans (hq_c n) hqp
  have h_dist_lt_delta : dist x y < δ n := by
    calc
      dist x y < 2 * dyadicRadius p := hxy
      _ < δ n := hc n p hp_c
  exact hδ_prop n x y h_dist_lt_delta

/-- Uniform continuity supplies strictly positive errors tending to zero on a cofinal
small-scale tail, at twice the dyadic radius. Blueprint node `metric:oscillation`. -/
theorem small_scale_oscillation (v : X → ℝ) (hv : UniformContinuous v) :
    ∃ ω : ℕ → ℝ, (∀ p, 0 < ω p) ∧ Tendsto ω atTop (𝓝 0) ∧
      ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ x y,
        dist x y < 2 * dyadicRadius p → |v x - v y| ≤ ω p := by
  obtain ⟨q, hq_mono, hq_spec⟩ := exists_strictMono_oscillation_modulus v hv
  let cond (p n : ℕ) : Prop := q n ≤ p
  let N (p : ℕ) : ℕ := Nat.findGreatest (cond p) p
  let ω (p : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ N p + (2 : ℝ)⁻¹ ^ p
  use ω
  refine ⟨?_, ?_, q 0, ?_⟩
  · intro p
    dsimp [ω]
    have h_pos1 : 0 < (2 : ℝ)⁻¹ ^ N p := by positivity
    have h_pos2 : 0 < (2 : ℝ)⁻¹ ^ p := by positivity
    linarith
  · have h_tendsto_N : Tendsto N atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro k
      use q k
      intro p hp
      have h_cond : cond p k := hp
      have h_le_p : k ≤ p := le_trans (hq_mono.id_le k) hp
      exact Nat.le_findGreatest h_le_p h_cond
    have h_tendsto_div1 : Tendsto (fun p ↦ (2 : ℝ)⁻¹ ^ N p) atTop (𝓝 0) := by
      have h2 : |(2 : ℝ)⁻¹| < 1 := by norm_num
      have h_pow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one h2
      exact Tendsto.comp h_pow h_tendsto_N
    have h_tendsto_div2 : Tendsto (fun p ↦ (2 : ℝ)⁻¹ ^ p) atTop (𝓝 0) := by
      have h2 : |(2 : ℝ)⁻¹| < 1 := by norm_num
      exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one h2
    have h_add := Tendsto.add h_tendsto_div1 h_tendsto_div2
    have h_eq : 𝓝 (0 : ℝ) = 𝓝 (0 + 0) := by congr 1; norm_num
    rw [h_eq]
    exact h_add
  · intro p hp x y hxy
    have h_find : cond p (N p) := by
      have h_P0 : cond p 0 := hp
      have h0 : 0 ≤ p := Nat.zero_le p
      exact Nat.findGreatest_spec h0 h_P0
    have h_v : |v x - v y| ≤ (2 : ℝ)⁻¹ ^ N p := hq_spec (N p) p h_find x y hxy
    have h_pos : 0 ≤ (2 : ℝ)⁻¹ ^ p := by positivity
    calc
      |v x - v y| ≤ (2 : ℝ)⁻¹ ^ N p := h_v
      _ ≤ (2 : ℝ)⁻¹ ^ N p + (2 : ℝ)⁻¹ ^ p := by linarith

/-- A local oscillation bound sums to a Birkhoff bound on a Bowen ball. -/
private lemma abs_birkhoffSum_sub_le_of_mem_bowenBall (T : X → X) (φ : X → ℝ)
    (x : X) (n : ℕ) (ε ω : ℝ) (hω : ∀ y z, dist y z < ε → |φ y - φ z| ≤ ω)
    (y : X) (hy : y ∈ bowenBall T n x ε) :
    |birkhoffSum T φ n y - birkhoffSum T φ n x| ≤ n * ω := by
  rw [birkhoffSum, birkhoffSum, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range n, (φ (T^[k] y) - φ (T^[k] x))|
        ≤ ∑ k ∈ Finset.range n, |φ (T^[k] y) - φ (T^[k] x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, ω := by
      apply Finset.sum_le_sum
      intro k hk
      apply hω
      rw [dist_comm]
      exact (Dynamics.mem_dynEntourage.mp hy) k (Finset.mem_range.mp hk)
    _ = n * ω := by simp

/-- A finite oscillation bound at twice a dyadic radius controls Birkhoff variation on
each Bowen ball of that radius. Blueprint node `metric:oscillation`. -/
theorem small_scale_oscillation_birkhoff (T : X → X) (v : X → ℝ) (p : ℕ) (ω : ℝ)
    (hω : ∀ x y, dist x y < 2 * dyadicRadius p → |v x - v y| ≤ ω)
    (n : ℕ) (x y : X) (hy : y ∈ bowenBall T n x (dyadicRadius p)) :
    |birkhoffSum T v n y - birkhoffSum T v n x| ≤ n * ω := by
  apply abs_birkhoffSum_sub_le_of_mem_bowenBall T v x n (dyadicRadius p) ω _ y hy
  intro z w hzw
  apply hω
  exact lt_of_lt_of_le hzw (by
    have : 0 < dyadicRadius p := by unfold dyadicRadius; positivity
    linarith)

/-- The signed finite-scale pressure cost is an infimum in `EReal`, allowing exceptional
large scales without an asserted minimum. Blueprint node `metric:min`. -/
noncomputable def finiteScalePressureCost (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (A : Set ℕ) (x : X) (n : ℕ) (ε : ℝ) : EReal :=
  ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x ε),
    ((oracleNatComplexity A i + birkhoffSum T φ n (P.ι i) : ℝ) : EReal)

/-- The BS cost filters out nonpositive real denominators, uses an `ENNReal` infimum,
and assigns infinity to order zero. Blueprint node `metric:min`. -/
noncomputable def finiteScaleBSCost (P : Presentation X) (T : X → X) (u : X → ℝ)
    (A : Set ℕ) (x : X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  if n = 0 then ⊤ else
    ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x ε),
      ⨅ (_ : 0 < birkhoffSum T u n (P.ι i)),
        (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i))

/-- The frozen total BS cost is antitone in radius, including its order-zero value.
Blueprint node `bs:pointwise`. -/
theorem pointwiseBSDimension_antitone_radius (P : Presentation X) (T : X → X)
    (u : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) :
    Antitone (finiteScaleBSCost P T u A x n) := by
  intro r₁ r₂ hr
  unfold finiteScaleBSCost
  split_ifs with hn
  · rfl
  · exact iInf_mono fun i ↦ iInf_mono' fun h ↦
      ⟨bowenBall_subset_of_le T n x hr h, le_rfl⟩

/-- An ideal center in the Bowen ball with positive Birkhoff sum bounds the finite-scale BS
cost by its normalized complexity. -/
theorem finiteScaleBSCost_le_div (P : Presentation X) (T : X → X) (u : X → ℝ) (A : Set ℕ)
    {x : X} {n : ℕ} (hn : n ≠ 0) {ε : ℝ} {i : ℕ} (hi : P.ι i ∈ bowenBall T n x ε)
    (hpos : 0 < birkhoffSum T u n (P.ι i)) :
    finiteScaleBSCost P T u A x n ε ≤
      (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
  simp only [finiteScaleBSCost, hn, ↓reduceIte]
  exact iInf_le_of_le i (iInf_le_of_le hi (iInf_le_of_le hpos le_rfl))

/-- A common lower bound on admissible Birkhoff sums ensures pressure-cost attainment. -/
private lemma exists_pressure_min_of_birkhoffSum_bounded_below
    (P : Presentation X) (T : X → X) (φ : X → ℝ)
    (A : Set ℕ) (x : X) (n : ℕ) (ε : ℝ)
    (L : ℝ) (hL : ∀ i, P.ι i ∈ bowenBall T n x ε → L ≤ birkhoffSum T φ n (P.ι i))
    (i₀ : ℕ) (hi₀ : P.ι i₀ ∈ bowenBall T n x ε) :
    ∃ i_min, P.ι i_min ∈ bowenBall T n x ε ∧ finiteScalePressureCost P T φ A x n ε =
      ((oracleNatComplexity A i_min + birkhoffSum T φ n (P.ι i_min) : ℝ) : EReal) := by
  let cost (i : ℕ) : ℝ := oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)
  let b := cost i₀ - L
  let S := {i | P.ι i ∈ bowenBall T n x ε ∧ (oracleNatComplexity A i : ℝ) ≤ b}
  have hS : S.Finite := by
    apply (oracle_kraft_finite_sublevels A ⌈b⌉₊).subset
    intro i hi
    exact Nat.cast_le.mp (hi.2.trans (Nat.le_ceil b))
  have hi₀S : i₀ ∈ S := by
    refine ⟨hi₀, ?_⟩
    have := hL i₀ hi₀
    dsimp [b, cost]
    linarith
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image S cost hS ⟨i₀, hi₀S⟩
  refine ⟨m, hm.1, le_antisymm (iInf₂_le m hm.1) ?_⟩
  apply le_iInf₂
  intro i hi
  apply EReal.coe_le_coe_iff.mpr
  by_cases hiS : i ∈ S
  · exact hmin i hiS
  · have hb : b < (oracleNatComplexity A i : ℝ) := by
      exact lt_of_not_ge (fun h ↦ hiS ⟨hi, h⟩)
    have hLi := hL i hi
    have hm₀ := hmin i₀ hi₀S
    dsimp [b, cost] at hb hm₀ ⊢
    linarith

/-- At a positive scale of finite oscillation, the pressure infimum equals the finite
real cost of an ideal realizer. Blueprint node `metric:min`. -/
theorem finite_scale_min_attained (P : Presentation X) (T : X → X) (hT : Continuous T)
    (φ : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (ω : ℝ) (hω : ∀ y z, dist y z < ε → |φ y - φ z| ≤ ω) :
    ∃ i, P.ι i ∈ bowenBall T n x ε ∧ finiteScalePressureCost P T φ A x n ε =
      ((oracleNatComplexity A i + birkhoffSum T φ n (P.ι i) : ℝ) : EReal) := by
  have ⟨i₀, hi₀⟩ := bowen_ball_dense P T hT x n hn ε hε
  let L := birkhoffSum T φ n x - n * ω
  have hL : ∀ i, P.ι i ∈ bowenBall T n x ε → L ≤ birkhoffSum T φ n (P.ι i) := by
    intro i hi
    have H := abs_birkhoffSum_sub_le_of_mem_bowenBall T φ x n ε ω hω (P.ι i) hi
    have H2 : - (n * ω) ≤ birkhoffSum T φ n (P.ι i) - birkhoffSum T φ n x := by
      exact neg_le_of_abs_le H
    dsimp [L]
    linarith
  exact exists_pressure_min_of_birkhoffSum_bounded_below P T φ A x n ε L hL i₀ hi₀

/-- A bounded ratio with positive denominator gives a natural-number numerator bound. -/
private lemma nat_le_ceil_of_ennreal_div_le (k : ℕ) {d b : ℝ} {r : ℝ≥0∞}
    (hd : 0 < d) (hdb : d ≤ b) (hr : r ≠ ⊤)
    (h : (k : ℝ≥0∞) / ENNReal.ofReal d ≤ r) :
    k ≤ ⌈r.toReal * b⌉₊ := by
  have hk : (k : ℝ≥0∞) ≤ r * ENNReal.ofReal b :=
    ((ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hd))
      ENNReal.ofReal_ne_top).mp h).trans
      (mul_le_mul_right (ENNReal.ofReal_le_ofReal hdb) r)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hr ENNReal.ofReal_ne_top) hk
  rw [ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hd.le.trans hdb)] at hreal
  exact Nat.cast_le.mp (hreal.trans (Nat.le_ceil _))

/-- An indexed infimum is attained if a nonempty sublevel lies in a finite set. -/
private theorem exists_iInf_eq_of_finite_sublevel
    (f : ℕ → ℝ≥0∞) (s : ℕ → Prop) (F : Finset ℕ) (r : ℝ≥0∞)
    (h_nonempty : ∃ i, i ∈ F ∧ s i ∧ f i ≤ r)
    (h_captures : ∀ i, s i → f i ≤ r → i ∈ F) :
    ∃ i, s i ∧ (⨅ j, ⨅ (_ : s j), f j) = f i := by
  classical
  let G := F.filter s
  have hG_nonempty : G.Nonempty := by
    rcases h_nonempty with ⟨i, hiF, hsi, _⟩
    use i
    rw [Finset.mem_filter]
    exact ⟨hiF, hsi⟩
  obtain ⟨m, hmG, hm_min⟩ := Finset.exists_min_image G f hG_nonempty
  use m
  have hsm : s m := by
    rw [Finset.mem_filter] at hmG
    exact hmG.2
  refine ⟨hsm, ?_⟩
  apply le_antisymm
  · exact iInf_le_of_le m (iInf_le _ hsm)
  · apply le_iInf
    intro j
    apply le_iInf
    intro hsj
    by_cases hle : f j ≤ r
    · have hjF : j ∈ F := h_captures j hsj hle
      have hjG : j ∈ G := by
        rw [Finset.mem_filter]
        exact ⟨hjF, hsj⟩
      exact hm_min j hjG
    · have hle_lt : r < f j := not_le.mp hle
      rcases h_nonempty with ⟨i, hiF, hsi, hfir⟩
      have hiG : i ∈ G := by
        rw [Finset.mem_filter]
        exact ⟨hiF, hsi⟩
      have hfm_le_fi : f m ≤ f i := hm_min i hiG
      calc f m ≤ f i := hfm_le_fi
        _ ≤ r := hfir
        _ ≤ f j := le_of_lt hle_lt

/-- Uniform positive lower and finite upper bounds on the realizer denominators imply
attainment of the BS ratio infimum. Blueprint node `metric:min`. -/
theorem finite_scale_min_attained_ratio (P : Presentation X) (T : X → X)
    (hT : Continuous T) (u : X → ℝ) (A : Set ℕ) (x : X) (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ i, P.ι i ∈ bowenBall T n x ε →
      a ≤ birkhoffSum T u n (P.ι i) ∧ birkhoffSum T u n (P.ι i) ≤ b) :
    ∃ i, P.ι i ∈ bowenBall T n x ε ∧ finiteScaleBSCost P T u A x n ε =
      (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i)) := by
  have Hn : n ≠ 0 := by omega
  have H2 := bowen_ball_dense P T hT x n hn ε hε
  rcases H2 with ⟨i₀, hi₀⟩
  let f : ℕ → ℝ≥0∞ := fun i ↦
    (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i))
  let s : ℕ → Prop := fun i ↦ P.ι i ∈ bowenBall T n x ε ∧ 0 < birkhoffSum T u n (P.ι i)
  have H_f : finiteScaleBSCost P T u A x n ε = ⨅ j, ⨅ (_ : s j), f j := by
    dsimp [finiteScaleBSCost, f, s]
    rw [ite_eq_right Hn]
    apply iInf_congr
    intro i
    apply le_antisymm
    · apply le_iInf
      intro H_and
      apply iInf_le_of_le H_and.1
      apply iInf_le_of_le H_and.2
      rfl
    · apply le_iInf
      intro h1
      apply le_iInf
      intro h2
      apply iInf_le_of_le ⟨h1, h2⟩
      rfl
  have H_bound_i0 := hbounds i₀ hi₀
  have hi0_pos : 0 < birkhoffSum T u n (P.ι i₀) := by linarith
  let r := f i₀
  have hr : r ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hi0_pos))
  let N := Nat.ceil ((r.toReal) * b)
  have hF_finite := oracle_kraft_finite_sublevels A N
  let F := hF_finite.toFinset
  have h_nonempty : ∃ i, i ∈ F ∧ s i ∧ f i ≤ r := by
    use i₀
    have hs_i0 : s i₀ := ⟨hi₀, hi0_pos⟩
    have H_f_i0 : f i₀ ≤ r := le_refl _
    have h_comp_bound := nat_le_ceil_of_ennreal_div_le
      (oracleNatComplexity A i₀) hi0_pos H_bound_i0.2 hr H_f_i0
    have h_in_F : i₀ ∈ F := by
      rw [Set.Finite.mem_toFinset]
      exact h_comp_bound
    exact ⟨h_in_F, hs_i0, H_f_i0⟩
  have h_captures : ∀ i, s i → f i ≤ r → i ∈ F := by
    intro i hs_i h_le
    rw [Set.Finite.mem_toFinset]
    exact nat_le_ceil_of_ennreal_div_le (oracleNatComplexity A i)
      hs_i.2 (hbounds i hs_i.1).2 hr h_le
  have ⟨m, hm_s, hm_min⟩ := exists_iInf_eq_of_finite_sublevel f s F r h_nonempty h_captures
  use m
  exact ⟨hm_s.1, by rw [H_f, hm_min]⟩

end Kolmogorov.PointToSet
