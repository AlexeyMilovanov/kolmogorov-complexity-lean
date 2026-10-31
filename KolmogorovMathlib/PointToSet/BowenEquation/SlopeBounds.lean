/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.BSDimension.Upper
import KolmogorovMathlib.PointToSet.Pressure.Lower
import KolmogorovMathlib.PointToSet.Pressure.Upper

/-!
# Slope bounds and the finite-scale Bowen equation

Fix a presentation `P` of the space, a continuous map `T`, a potential `u`, an oracle `A` and a
point `x`.  For a radius `r` and an order `n` the normalized pressure
`finiteScalePressureRate P T (-s u) A x n r` is an infimum over the ideal points in the Bowen
ball of `(K^A(i) - s U_n(P.ι i)) / n`, where `U_n` is the Birkhoff sum of `u`, while the BS cost
`finiteScaleBSCost P T u A x n r` is the infimum of the ratios `K^A(i) / U_n(P.ι i)`.  This module
compares the two under the hypothesis that all averages `U_n(P.ι i) / n` in the Bowen ball lie in
an interval `[a, b]` with `0 < a`.

* `pointwisePressureSlopeBounds` and `pointwisePressureSlopeBounds_time` (blueprint node
  `bs:affine-slope`) show that the pressure, at a fixed order and after either time limit, drops
  with the parameter `s` at a rate between `a` and `b`.
* `ratioPressureSignedComparison` and its corollaries (blueprint node `bs:signed-comparison`)
  sandwich the pressure between the multiples of the ratio minus `s`, which gives the sign of
  the pressure from the position of `s` relative to the ratio, and transfer positive and
  negative time-limit pressures to bounds on the time limit of the ratio.
* `finiteScalePointwiseBowenEquation` (blueprint node `bs:finite-scale-root`) shows that, when
  the time limit of the zero-potential pressure is finite, the time limit `d` of the BS cost is
  finite and is a zero of the pressure `s ↦ P(-s u)`.

The scale-zero slope bounds and the pointwise Bowen equation of
`KolmogorovMathlib.PointToSet.BowenEquation.Pointwise` are built on these results.
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

section TimeLimits

/-- A lower bound that holds for every member bounds the time limit from below. -/
private lemma le_timeLimit_of_forall_le {α : Type*} [CompleteLattice α] (σ : LimitSide)
    {f : ℕ → α} {c : α} (h : ∀ n, c ≤ f n) : c ≤ σ.timeLimit f := by
  cases σ <;> dsimp only [LimitSide.timeLimit, LimitSide.choose]
  · exact le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall h)
  · exact le_limsup_of_frequently_le (Frequently.of_forall h)

/-- If the time limit of `g` is below `m`, and `f n ≤ c` follows from `g n < m` for all large
`n`, then the time limit of `f` is at most `c`. -/
private lemma timeLimit_le_of_lt_imp_le {α β : Type*} [CompleteLinearOrder α] [CompleteLattice β]
    (σ : LimitSide) {f : ℕ → β} {g : ℕ → α} {m : α} {c : β} (hg : σ.timeLimit g < m)
    (h : ∀ᶠ n in atTop, g n < m → f n ≤ c) : σ.timeLimit f ≤ c := by
  cases σ <;> dsimp only [LimitSide.timeLimit, LimitSide.choose] at hg ⊢
  · exact liminf_le_of_frequently_le
      ((frequently_lt_of_liminf_lt (by isBoundedDefault) hg).and_eventually h
        |>.mono fun _ h ↦ h.2 h.1)
  · exact limsup_le_of_le (by isBoundedDefault)
      ((eventually_lt_of_limsup_lt hg).and h |>.mono fun _ h ↦ h.2 h.1)

/-- If the time limit of `g` is above `m`, and `c ≤ f n` follows from `m < g n` for all large
`n`, then the time limit of `f` is at least `c`. -/
private lemma le_timeLimit_of_lt_imp_le {α β : Type*} [CompleteLinearOrder α] [CompleteLattice β]
    (σ : LimitSide) {f : ℕ → β} {g : ℕ → α} {m : α} {c : β} (hg : m < σ.timeLimit g)
    (h : ∀ᶠ n in atTop, m < g n → c ≤ f n) : c ≤ σ.timeLimit f := by
  cases σ <;> dsimp only [LimitSide.timeLimit, LimitSide.choose] at hg ⊢
  · exact le_liminf_of_le (by isBoundedDefault)
      ((eventually_lt_of_lt_liminf hg).and h |>.mono fun _ h ↦ h.2 h.1)
  · exact le_limsup_of_frequently_le
      ((frequently_lt_of_lt_limsup (by isBoundedDefault) hg).and_eventually h
        |>.mono fun _ h ↦ h.2 h.1)

/-- Both time limits commute with the coercion `ℝ≥0∞ → EReal`. -/
private lemma coe_timeLimit_ennreal (σ : LimitSide) (C : ℕ → ℝ≥0∞) :
    ((σ.timeLimit C : ℝ≥0∞) : EReal) = σ.timeLimit (fun n ↦ (C n : EReal)) := by
  cases σ <;> dsimp only [LimitSide.timeLimit, LimitSide.choose]
  · exact EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt C
      continuous_coe_ennreal_ereal.continuousAt (by isBoundedDefault) (by isBoundedDefault)
  · exact EReal.coe_ennreal_strictMono.monotone.map_limsup_of_continuousAt C
      continuous_coe_ennreal_ereal.continuousAt (by isBoundedDefault) (by isBoundedDefault)

/-- Time limits commute with translation by a real constant, so a two-sided eventual bound by
translates of `f` passes to the time limits. -/
private lemma timeLimit_sub_coe_sandwich {f g : ℕ → EReal} {c₁ c₂ : ℝ} (σ : LimitSide)
    (h : ∀ᶠ n in atTop, f n - (c₁ : EReal) ≤ g n ∧ g n ≤ f n - (c₂ : EReal)) :
    σ.timeLimit f - (c₁ : EReal) ≤ σ.timeLimit g ∧
      σ.timeLimit g ≤ σ.timeLimit f - (c₂ : EReal) := by
  let e (c : ℝ) : EReal ≃o EReal :=
    { toFun := fun z ↦ z - (c : EReal)
      invFun := fun z ↦ z + (c : EReal)
      left_inv := fun _ ↦ EReal.sub_add_cancel
      right_inv := fun _ ↦ EReal.add_sub_cancel_right
      map_rel_iff' := by
        intro z w
        change z - (c : EReal) ≤ w - (c : EReal) ↔ z ≤ w
        rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c)),
          EReal.sub_add_cancel] }
  have shift (c : ℝ) : σ.timeLimit (fun n ↦ e c (f n)) = e c (σ.timeLimit f) := by
    cases σ <;> dsimp only [LimitSide.timeLimit, LimitSide.choose]
    · exact (OrderIso.liminf_apply (e c)).symm
    · exact (OrderIso.limsup_apply (e c)).symm
  constructor
  · calc
      σ.timeLimit f - (c₁ : EReal) = σ.timeLimit (fun n ↦ e c₁ (f n)) := (shift c₁).symm
      _ ≤ σ.timeLimit g := σ.timeLimit_mono (h.mono fun _ hn ↦ hn.1)
  · calc
      σ.timeLimit g ≤ σ.timeLimit (fun n ↦ e c₂ (f n)) := σ.timeLimit_mono (h.mono fun _ hn ↦ hn.2)
      _ = σ.timeLimit f - (c₂ : EReal) := shift c₂

/-- An extended real that is squeezed between two translates of a real number is real, in the
case where it appears on the left of the translates. -/
private lemma exists_coe_eq_of_sub_coe_le {x : EReal} {k c c' : ℝ}
    (h : x - (c : EReal) ≤ k ∧ (k : EReal) ≤ x - (c' : EReal)) : ∃ v : ℝ, x = v := by
  induction x using EReal.rec with
  | bot => simp at h
  | coe v => exact ⟨v, rfl⟩
  | top => simp at h

/-- An extended real that is squeezed between two translates of a real number is real, in the
case where it appears between the translates. -/
private lemma exists_coe_eq_of_le_sub_coe {x : EReal} {k c c' : ℝ}
    (h : (k : EReal) - (c : EReal) ≤ x ∧ x ≤ (k : EReal) - (c' : EReal)) : ∃ v : ℝ, x = v := by
  induction x using EReal.rec with
  | bot => simp [← EReal.coe_sub] at h
  | coe v => exact ⟨v, rfl⟩
  | top => simp [← EReal.coe_sub] at h

end TimeLimits

section Realizers

variable {P : Presentation X} {T : X → X} {u : X → ℝ} {a b : ℝ} {A : Set ℕ} {x : X} {n : ℕ}
  {r : ℝ}

omit [MetricSpace X] in
/-- The Birkhoff sum of `-s u` is `-s` times the Birkhoff sum of `u`. -/
private lemma birkhoffSum_neg_mul (s : ℝ) (y : X) :
    birkhoffSum T (fun z ↦ -s * u z) n y = -s * birkhoffSum T u n y := by
  simp only [birkhoffSum, Finset.mul_sum]

/-- A positive lower bound on an average makes the sum positive. -/
private lemma pos_of_le_div_natCast {S : ℝ} (ha : 0 < a) (hn : 1 ≤ n) (h : a ≤ S / n) :
    0 < S := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact (mul_pos ha hn').trans_le ((le_div_iff₀ hn').mp h)

/-- Bounds on an average are bounds on the sum, with the order as a factor. -/
private lemma mul_bounds_of_div_bounds {S : ℝ} (hn : 1 ≤ n) (h : a ≤ S / n ∧ S / n ≤ b) :
    a * n ≤ S ∧ S ≤ b * n :=
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  ⟨(le_div_iff₀ hn').mp h.1, (div_le_iff₀ hn').mp h.2⟩

/-- The lower and upper bounds on the averages in a nonempty Bowen ball are ordered. -/
private lemma le_of_realizer_bounds (hT : Continuous T) (hn : 1 ≤ n) (hr : 0 < r)
    (hbounds : ∀ i, P.ι i ∈ bowenBall T n x r →
      a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b) : a ≤ b := by
  obtain ⟨i, hi⟩ := bowen_ball_dense P T hT x n hn r hr
  exact (hbounds i hi).1.trans (hbounds i hi).2

/-- If the averages are eventually bounded below by `a > 0`, the upper bound is positive. -/
private lemma pos_of_eventually_realizer_bounds (hT : Continuous T) (ha : 0 < a) (hr : 0 < r)
    (hbounds : ∀ᶠ n in atTop, ∀ i, P.ι i ∈ bowenBall T n x r →
      a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b) : 0 < b := by
  obtain ⟨n, hn, hbn⟩ := ((eventually_ge_atTop 1).and hbounds).exists
  exact ha.trans_le (le_of_realizer_bounds hT hn hr hbn)

/-- Unfolding of the normalized pressure at a positive order. -/
private lemma finiteScalePressureRate_of_ne_zero (φ : X → ℝ) (hn : n ≠ 0) :
    finiteScalePressureRate P T φ A x n r = ⨅ i : ℕ, ⨅ (_ : P.ι i ∈ bowenBall T n x r),
      (((oracleNatComplexity A i + birkhoffSum T φ n (P.ι i)) / n : ℝ) : EReal) := by
  simp only [finiteScalePressureRate, hn, ↓reduceIte]

/-- The zero-potential normalized pressure is nonnegative. -/
private lemma zero_le_finiteScalePressureRate_zero :
    0 ≤ finiteScalePressureRate P T (fun _ ↦ 0) A x n r := by
  by_cases hn : n = 0
  · simp only [finiteScalePressureRate, hn, ↓reduceIte, le_top]
  · rw [finiteScalePressureRate_of_ne_zero _ hn]
    refine le_iInf fun i ↦ le_iInf fun _ ↦ ?_
    simp only [birkhoffSum, Finset.sum_const_zero, add_zero]
    exact EReal.coe_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The real value of a ratio of a natural number to the extended-real image of `U`. -/
private lemma toReal_natCast_div_ofReal (k : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    ((k : ℝ≥0∞) / ENNReal.ofReal U).toReal = k / U := by
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hU]

/-- The normalized affine cost of a realizer is its average times the ratio minus `s`. -/
private lemma realizer_cost_eq (hn : 1 ≤ n) (s : ℝ) {i : ℕ}
    (hU : 0 < birkhoffSum T u n (P.ι i)) :
    ((oracleNatComplexity A i : ℝ) + birkhoffSum T (fun y ↦ -s * u y) n (P.ι i)) / n =
      birkhoffSum T u n (P.ι i) / n *
        ((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) - s) := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  rw [birkhoffSum_neg_mul]
  field_simp
  ring

/-- A weight in `[a, b]` times `q` lies between `min (a q) (b q)` and `max (a q) (b q)`. -/
private lemma min_mul_le_mul_le_max_mul {a b w q : ℝ} (hw : a ≤ w ∧ w ≤ b) :
    min (a * q) (b * q) ≤ w * q ∧ w * q ≤ max (a * q) (b * q) := by
  rcases le_total 0 q with hq | hq
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hw.1 hq),
      (mul_le_mul_of_nonneg_right hw.2 hq).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hw.2 hq),
      (mul_le_mul_of_nonpos_right hw.1 hq).trans (le_max_left _ _)⟩

/-- Every realizer's normalized affine cost is at least the lower end of the signed sandwich. -/
private lemma min_mul_le_realizer_cost (ha : 0 < a) (hn : 1 ≤ n) (s : ℝ) {i : ℕ}
    (hbi : a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)
    (hi : P.ι i ∈ bowenBall T n x r) :
    min (a * ((finiteScaleBSCost P T u A x n r).toReal - s))
        (b * ((finiteScaleBSCost P T u A x n r).toReal - s)) ≤
      ((oracleNatComplexity A i : ℝ) + birkhoffSum T (fun y ↦ -s * u y) n (P.ι i)) / n := by
  have hU := pos_of_le_div_natCast ha hn hbi.1
  have hfinite : (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i))
      ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (ENNReal.ofReal_pos.mpr hU).ne').ne
  have hratio := ENNReal.toReal_mono hfinite
    (finiteScaleBSCost_le_div P T u A (Nat.one_le_iff_ne_zero.mp hn) hi hU)
  rw [toReal_natCast_div_ofReal _ hU.le] at hratio
  rw [realizer_cost_eq hn s hU]
  refine (min_mul_le_mul_le_max_mul hbi).1.trans ?_
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hratio s) (ha.trans_le hbi.1).le

/-- If the BS cost is attained at a realizer, that realizer's normalized affine cost is at most
the upper end of the signed sandwich. -/
private lemma realizer_cost_le_max_mul (ha : 0 < a) (hn : 1 ≤ n) (s : ℝ) {i : ℕ}
    (hbi : a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)
    (hcost : finiteScaleBSCost P T u A x n r =
      (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i))) :
    ((oracleNatComplexity A i : ℝ) + birkhoffSum T (fun y ↦ -s * u y) n (P.ι i)) / n ≤
      max (a * ((finiteScaleBSCost P T u A x n r).toReal - s))
        (b * ((finiteScaleBSCost P T u A x n r).toReal - s)) := by
  have hU := pos_of_le_div_natCast ha hn hbi.1
  rw [realizer_cost_eq hn s hU, hcost, toReal_natCast_div_ofReal _ hU.le]
  exact (min_mul_le_mul_le_max_mul hbi).2

/-- Under a negative bound on the pressure at order `n`, the BS cost at that order is at most
the parameter plus the bound divided by `b`. -/
private lemma finiteScaleBSCost_le_add_div (ha : 0 < a) (hn : 1 ≤ n)
    (hbounds : ∀ i, P.ι i ∈ bowenBall T n x r →
      a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)
    {s t : ℝ} (ht : t < 0)
    (h : finiteScalePressureRate P T (fun y => -s * u y) A x n r < (t : EReal)) :
    (finiteScaleBSCost P T u A x n r : EReal) ≤ ((s + t / b : ℝ) : EReal) := by
  rw [finiteScalePressureRate_of_ne_zero _ (by omega)] at h
  obtain ⟨i, hi'⟩ := iInf_lt_iff.mp h
  obtain ⟨hi, hRi⟩ := iInf_lt_iff.mp hi'
  have hbi := hbounds i hi
  have hU := pos_of_le_div_natCast ha hn hbi.1
  have hb : 0 < b := ha.trans_le (hbi.1.trans hbi.2)
  have hw : 0 < birkhoffSum T u n (P.ι i) / n := ha.trans_le hbi.1
  rw [realizer_cost_eq hn s hU] at hRi
  have hRi := EReal.coe_lt_coe_iff.mp hRi
  have hp : (oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) - s < 0 := by
    by_contra hp
    have := mul_nonneg hw.le (not_lt.mp hp)
    linarith
  have hbp : b * ((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) - s) < t :=
    lt_of_le_of_lt (mul_le_mul_of_nonpos_right hbi.2 hp.le) hRi
  have hratio : (oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) ≤ s + t / b := by
    have : (oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) - s < t / b :=
      (lt_div_iff₀ hb).2 (by rwa [mul_comm])
    linarith
  have hfinite : (oracleNatComplexity A i : ℝ≥0∞) / ENNReal.ofReal (birkhoffSum T u n (P.ι i))
      ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (ENNReal.ofReal_pos.mpr hU).ne').ne
  calc
    (finiteScaleBSCost P T u A x n r : EReal) ≤
        (((oracleNatComplexity A i : ℝ≥0∞) /
          ENNReal.ofReal (birkhoffSum T u n (P.ι i)) : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (finiteScaleBSCost_le_div P T u A (Nat.one_le_iff_ne_zero.mp hn) hi hU)
    _ = (((oracleNatComplexity A i : ℝ) / birkhoffSum T u n (P.ι i) : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hfinite, toReal_natCast_div_ofReal _ hU.le]
    _ ≤ ((s + t / b : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hratio

end Realizers

section FixedOrder

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (a b : ℝ) (ha : 0 < a) (A : Set ℕ) (x : X) (n : ℕ) (hn : 1 ≤ n)
  (r : ℝ) (hr : 0 < r)
  (hbounds : ∀ i, P.ι i ∈ bowenBall T n x r →
    a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)

include hT hu ha hn hr hbounds

omit hT hu ha hr in
/-- If every Birkhoff average over the order-`n` Bowen ball lies in `[a, b]`, then for `s < t`
the finite-order pressure at the parameter `t` lies between the pressure at `s` minus `(t - s) b`
and the pressure at `s` minus `(t - s) a`.  Blueprint node `bs:affine-slope`. -/
theorem pointwisePressureSlopeBounds (s t : ℝ) (hst : s < t) :
    finiteScalePressureRate P T (fun y => -s * u y) A x n r - ((t - s) * b : ℝ) ≤
      finiteScalePressureRate P T (fun y => -t * u y) A x n r ∧
    finiteScalePressureRate P T (fun y => -t * u y) A x n r ≤
      finiteScalePressureRate P T (fun y => -s * u y) A x n r - ((t - s) * a : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  let f : ℝ → ℕ → ℝ := fun v i ↦
    ((oracleNatComplexity A i : ℝ) + birkhoffSum T (fun y ↦ -v * u y) n (P.ι i)) / n
  have hf (v : ℝ) (i : ℕ) : f v i = (oracleNatComplexity A i : ℝ) / n -
      v * (birkhoffSum T u n (P.ι i) / n) := by
    dsimp only [f]
    rw [birkhoffSum_neg_mul]
    ring
  simp only [finiteScalePressureRate, hn0, ↓reduceIte]
  constructor
  · refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    calc
      _ ≤ (f s i : EReal) - ((t - s) * b : ℝ) :=
        EReal.sub_le_sub (iInf_le_of_le i (iInf_le_of_le hi le_rfl)) le_rfl
      _ ≤ (f t i : EReal) := by
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff, hf, hf]
        have h := mul_le_mul_of_nonneg_left (hbounds i hi).2 (sub_nonneg.mpr hst.le)
        nlinarith only [h]
  · apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))).2
    refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    calc
      _ ≤ (f t i : EReal) + ((t - s) * a : ℝ) :=
        add_le_add (iInf_le_of_le i (iInf_le_of_le hi le_rfl)) le_rfl
      _ ≤ (f s i : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff, hf, hf]
        have h := mul_le_mul_of_nonneg_left (hbounds i hi).1 (sub_nonneg.mpr hst.le)
        nlinarith only [h]

omit hu in
/-- Positive bounded realizer denominators make the frozen ratio infimum finite.
Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison_finite : finiteScaleBSCost P T u A x n r < ⊤ := by
  obtain ⟨i₀, hi₀⟩ := bowen_ball_dense P T hT x n hn r hr
  have hU := pos_of_le_div_natCast ha hn (hbounds i₀ hi₀).1
  exact (finiteScaleBSCost_le_div P T u A (Nat.one_le_iff_ne_zero.mp hn) hi₀ hU).trans_lt
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (ENNReal.ofReal_pos.mpr hU).ne')

omit hu in
/-- The signed finite-order sandwich compares pressure to the finite ratio minus the
real parameter, with the order of the two slopes determined by its sign.
Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison (s : ℝ) :
    let q := (finiteScaleBSCost P T u A x n r).toReal - s
    ((min (a * q) (b * q) : ℝ) : EReal) ≤
      finiteScalePressureRate P T (fun y => -s * u y) A x n r ∧
    finiteScalePressureRate P T (fun y => -s * u y) A x n r ≤
      ((max (a * q) (b * q) : ℝ) : EReal) := by
  intro q
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨i₀, hi₀, hcost⟩ := finite_scale_min_attained_ratio P T hT u A x n hn r hr (a * n)
    (b * n) (mul_pos ha hn') fun i hi ↦ mul_bounds_of_div_bounds hn (hbounds i hi)
  rw [finiteScalePressureRate_of_ne_zero _ (by omega)]
  exact ⟨le_iInf fun i ↦ le_iInf fun hi ↦
      EReal.coe_le_coe_iff.mpr (min_mul_le_realizer_cost ha hn s (hbounds i hi) hi),
    iInf_le_of_le i₀ (iInf_le_of_le hi₀ (EReal.coe_le_coe_iff.mpr
      (realizer_cost_le_max_mul ha hn s (hbounds i₀ hi₀) hcost)))⟩

omit hu in
/-- Finite-order pressure is positive exactly when the ratio exceeds the parameter.
Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison_positive (s : ℝ) :
    0 < finiteScalePressureRate P T (fun y => -s * u y) A x n r ↔
      s < (finiteScaleBSCost P T u A x n r).toReal := by
  have H := ratioPressureSignedComparison P T hT u a b ha A x n hn r hr hbounds s
  have hab := le_of_realizer_bounds hT hn hr hbounds
  dsimp only at H
  constructor
  · intro hpos
    by_contra hle
    have hq : (finiteScaleBSCost P T u A x n r).toReal - s ≤ 0 :=
      sub_nonpos.mpr (not_lt.mp hle)
    have hmax := max_le (mul_nonpos_of_nonneg_of_nonpos ha.le hq)
      (mul_nonpos_of_nonneg_of_nonpos (ha.le.trans hab) hq)
    exact absurd (hpos.trans_le H.2) (not_lt.mpr (EReal.coe_nonpos.mpr hmax))
  · intro hlt
    have hq := sub_pos.mpr hlt
    have hmin := lt_min (mul_pos ha hq) (mul_pos (ha.trans_le hab) hq)
    exact (EReal.coe_pos.mpr hmin).trans_le H.1

omit hu in
/-- Finite-order pressure is zero exactly at the attained ratio.
Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison_zero (s : ℝ) :
    finiteScalePressureRate P T (fun y => -s * u y) A x n r = 0 ↔
      s = (finiteScaleBSCost P T u A x n r).toReal := by
  have hb : 0 < b := ha.trans_le (le_of_realizer_bounds hT hn hr hbounds)
  have hsand := ratioPressureSignedComparison P T hT u a b ha A x n hn r hr hbounds s
  dsimp only at hsand
  constructor
  · intro hzero
    rw [hzero] at hsand
    have hmin := EReal.coe_nonpos.mp hsand.1
    have hmax := EReal.coe_nonneg.mp hsand.2
    apply le_antisymm
    · rcases le_max_iff.mp hmax with h | h
      · exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h ha)
      · exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h hb)
    · rcases min_le_iff.mp hmin with h | h
      · exact sub_nonpos.mp (nonpos_of_mul_nonpos_right h ha)
      · exact sub_nonpos.mp (nonpos_of_mul_nonpos_right h hb)
  · intro hs
    rw [hs] at hsand ⊢
    simp only [sub_self, mul_zero, min_self, max_self, EReal.coe_zero] at hsand
    exact le_antisymm hsand.2 hsand.1

omit hu in
/-- Finite-order pressure is negative exactly when the ratio is below the parameter.
Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison_negative (s : ℝ) :
    finiteScalePressureRate P T (fun y => -s * u y) A x n r < 0 ↔
      (finiteScaleBSCost P T u A x n r).toReal < s := by
  have hb : 0 < b := ha.trans_le (le_of_realizer_bounds hT hn hr hbounds)
  have H := ratioPressureSignedComparison P T hT u a b ha A x n hn r hr hbounds s
  dsimp only at H
  constructor
  · intro hneg
    by_contra hge
    have hq : 0 ≤ (finiteScaleBSCost P T u A x n r).toReal - s :=
      sub_nonneg.mpr (not_lt.mp hge)
    have hmin := le_min (mul_nonneg ha.le hq) (mul_nonneg hb.le hq)
    exact absurd hneg (not_lt.mpr ((EReal.coe_nonneg.mpr hmin).trans H.1))
  · intro hlt
    have hq := sub_neg.mpr hlt
    have hmax := max_lt (mul_neg_of_pos_of_neg ha hq) (mul_neg_of_pos_of_neg hb hq)
    exact H.2.trans_lt (by exact_mod_cast hmax)

omit hu in
/-- At an order whose averages satisfy the bounds, a finite pressure above `t > 0` bounds the BS
cost below by the parameter plus `t / b`. -/
private lemma add_div_le_finiteScaleBSCost (s t : ℝ) (ht : 0 < t)
    (h : (t : EReal) < finiteScalePressureRate P T (fun y => -s * u y) A x n r) :
    ((s + t / b : ℝ) : EReal) ≤ (finiteScaleBSCost P T u A x n r : EReal) := by
  have hab := le_of_realizer_bounds hT hn hr hbounds
  have hb : 0 < b := ha.trans_le hab
  have H := ratioPressureSignedComparison P T hT u a b ha A x n hn r hr hbounds s
  dsimp only at H
  have hs : s < (finiteScaleBSCost P T u A x n r).toReal :=
    (ratioPressureSignedComparison_positive P T hT u a b ha A x n hn r hr hbounds s).mp
      ((EReal.coe_pos.mpr ht).trans h)
  have hq : 0 ≤ (finiteScaleBSCost P T u A x n r).toReal - s := sub_nonneg.mpr hs.le
  rw [max_eq_right (mul_le_mul_of_nonneg_right hab hq)] at H
  have htr : t < b * ((finiteScaleBSCost P T u A x n r).toReal - s) :=
    EReal.coe_lt_coe_iff.mp (h.trans_le H.2)
  have hdiv : t / b ≤ (finiteScaleBSCost P T u A x n r).toReal - s :=
    (div_le_iff₀ hb).2 (by linarith [mul_comm b ((finiteScaleBSCost P T u A x n r).toReal - s)])
  calc
    ((s + t / b : ℝ) : EReal) ≤ ((finiteScaleBSCost P T u A x n r).toReal : EReal) :=
      EReal.coe_le_coe_iff.mpr (by linarith)
    _ = (finiteScaleBSCost P T u A x n r : EReal) := EReal.coe_ennreal_toReal
      (ratioPressureSignedComparison_finite P T hT u a b ha A x n hn r hr hbounds).ne

end FixedOrder

section FixedRadius

variable (P : Presentation X) (T : X → X) (hT : Continuous T) (u : X → ℝ)
  (hu : UniformContinuous u) (a b : ℝ) (ha : 0 < a) (A : Set ℕ) (x : X) (r : ℝ) (hr : 0 < r)
  (hbounds : ∀ᶠ n in atTop, ∀ i, P.ι i ∈ bowenBall T n x r →
    a ≤ birkhoffSum T u n (P.ι i) / n ∧ birkhoffSum T u n (P.ι i) / n ≤ b)

include hT hu ha hr hbounds

omit hT hu ha hr in
/-- Eventual average bounds pass the two-sided affine slope inequality to either time limit.
Blueprint node `bs:affine-slope`. -/
theorem pointwisePressureSlopeBounds_time (σ : LimitSide) (s t : ℝ) (hst : s < t) :
    let f := fun v : ℝ =>
      σ.timeLimit (fun n => finiteScalePressureRate P T (fun y => -v * u y) A x n r)
    f s - ((t - s) * b : ℝ) ≤ f t ∧ f t ≤ f s - ((t - s) * a : ℝ) := by
  refine timeLimit_sub_coe_sandwich σ ?_
  filter_upwards [hbounds, eventually_ge_atTop 1] with n hbn hn
  exact pointwisePressureSlopeBounds P T u a b A x n hn r hbn s t hst

omit hu in
/-- A finite positive time-limit pressure at the parameter `s` gives the lower bound
`s + v / b` on the time limit of the BS cost.  Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison_limit_positive (σ : LimitSide) (s v : ℝ)
    (hv : σ.timeLimit (fun n =>
      finiteScalePressureRate P T (fun y => -s * u y) A x n r) = (v : EReal))
    (hpos : 0 < v) :
    ((s + v / b : ℝ) : EReal) ≤
      (σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r) : EReal) := by
  have hb := pos_of_eventually_realizer_bounds hT ha hr hbounds
  apply EReal.ge_of_forall_gt_iff_ge.mp
  intro w hw
  have hw' : w < s + v / b := EReal.coe_lt_coe_iff.mp hw
  have hwv : (w - s) * b < v := (lt_div_iff₀ hb).mp (by linarith)
  obtain ⟨t, ht, htv⟩ := exists_between (max_lt hpos hwv)
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  have hwt : w ≤ s + t / b := by
    have hd : w - s ≤ t / b := (le_div_iff₀ hb).2 ((le_max_right _ _).trans ht.le)
    linarith
  have hlt : (t : EReal) < σ.timeLimit
      (fun n => finiteScalePressureRate P T (fun y => -s * u y) A x n r) :=
    (EReal.coe_lt_coe_iff.mpr htv).trans_eq hv.symm
  refine le_timeLimit_of_lt_imp_le σ hlt ?_
  filter_upwards [hbounds, eventually_ge_atTop 1] with n hbn hn hRn
  exact (EReal.coe_le_coe_iff.mpr hwt).trans
    (add_div_le_finiteScaleBSCost P T hT u a b ha A x n hn r hr hbn s t ht0 hRn)

omit hu in
/-- A finite negative time-limit pressure at the parameter `s` gives the upper bound
`s + v / b` on the time limit of the BS cost.  Blueprint node `bs:signed-comparison`. -/
theorem ratioPressureSignedComparison_limit_negative (σ : LimitSide) (s v : ℝ)
    (hv : σ.timeLimit (fun n =>
      finiteScalePressureRate P T (fun y => -s * u y) A x n r) = (v : EReal))
    (hneg : v < 0) :
    (σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r) : EReal) ≤
      ((s + v / b : ℝ) : EReal) := by
  have hb := pos_of_eventually_realizer_bounds hT ha hr hbounds
  apply EReal.le_of_forall_lt_iff_le.mp
  intro w hw
  have hw' : s + v / b < w := EReal.coe_lt_coe_iff.mp hw
  have hvb : v < (w - s) * b := (div_lt_iff₀ hb).mp (by linarith)
  obtain ⟨t, hvt, ht⟩ := exists_between (lt_min hneg hvb)
  have ht0 : t < 0 := ht.trans_le (min_le_left _ _)
  have htw : s + t / b ≤ w := by
    have : t / b ≤ w - s := (div_le_iff₀ hb).2 (ht.le.trans (min_le_right _ _))
    linarith
  have hlt : σ.timeLimit
      (fun n => finiteScalePressureRate P T (fun y => -s * u y) A x n r) < (t : EReal) :=
    hv.trans_lt (EReal.coe_lt_coe_iff.mpr hvt)
  refine (timeLimit_le_of_lt_imp_le σ hlt ?_).trans (EReal.coe_le_coe_iff.mpr htw)
  filter_upwards [hbounds, eventually_ge_atTop 1] with n hbn hn hRn
  exact finiteScaleBSCost_le_add_div ha hn hbn ht0 hRn

variable (σ : LimitSide)
  (hfinite : σ.timeLimit (fun n => finiteScalePressureRate P T (fun _ => 0) A x n r) < ⊤)

include hfinite

omit hu in
/-- Finite orbit complexity and positive bounded denominators imply finite BS dimension
at a fixed radius. Blueprint node `bs:finite-scale-root`. -/
theorem finiteScalePointwiseBowenEquation_finite :
    σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r) < ⊤ := by
  obtain ⟨M, hM, -⟩ := EReal.exists_between_coe_real hfinite
  refine (timeLimit_le_of_lt_imp_le σ (m := (M : EReal)) (c := ENNReal.ofReal (M / a)) hM
    ?_).trans_lt ENNReal.ofReal_lt_top
  filter_upwards [hbounds, eventually_ge_atTop 1] with n hbn hn hg
  have hab := le_of_realizer_bounds hT hn hr hbn
  have hcmp := (ratioPressureSignedComparison P T hT u a b ha A x n hn r hr hbn 0).1
  simp only [neg_zero, zero_mul, sub_zero,
    min_eq_left (mul_le_mul_of_nonneg_right hab ENNReal.toReal_nonneg)] at hcmp
  have hcost := ratioPressureSignedComparison_finite P T hT u a b ha A x n hn r hr hbn
  have hlt : a * (finiteScaleBSCost P T u A x n r).toReal < M :=
    EReal.coe_lt_coe_iff.mp (hcmp.trans_lt hg)
  have hle : (finiteScaleBSCost P T u A x n r).toReal ≤ M / a :=
    (le_div_iff₀ ha).mpr (by linarith)
  rw [← ENNReal.ofReal_toReal hcost.ne]
  exact ENNReal.ofReal_le_ofReal hle

omit hT hu ha hr in
/-- The time limits of the pressure at every real parameter are finite. -/
private lemma exists_coe_eq_timeLimit_pressureRate (s : ℝ) :
    ∃ v : ℝ, σ.timeLimit
      (fun n => finiteScalePressureRate P T (fun y => -s * u y) A x n r) = (v : EReal) := by
  have h0 : σ.timeLimit
      (fun n => finiteScalePressureRate P T (fun y => -(0 : ℝ) * u y) A x n r) =
      σ.timeLimit (fun n => finiteScalePressureRate P T (fun _ => 0) A x n r) := by
    simp only [neg_zero, zero_mul]
  have hlow : 0 ≤ σ.timeLimit
      (fun n => finiteScalePressureRate P T (fun _ => 0) A x n r) :=
    le_timeLimit_of_forall_le σ fun _ ↦ zero_le_finiteScalePressureRate_zero
  obtain ⟨k, hk⟩ : ∃ k : ℝ, σ.timeLimit
      (fun n => finiteScalePressureRate P T (fun y => -(0 : ℝ) * u y) A x n r) = (k : EReal) :=
    ⟨_, (EReal.coe_toReal (h0 ▸ hfinite.ne)
      (h0 ▸ (lt_of_lt_of_le EReal.bot_lt_zero hlow).ne')).symm⟩
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have h := pointwisePressureSlopeBounds_time P T u a b A x r hbounds σ s 0 hs
    dsimp only at h
    rw [hk] at h
    exact exists_coe_eq_of_sub_coe_le h
  · exact ⟨k, hk⟩
  · have h := pointwisePressureSlopeBounds_time P T u a b A x r hbounds σ 0 s hs
    dsimp only at h
    rw [hk] at h
    exact exists_coe_eq_of_le_sub_coe h

omit hu in
/-- The finite fixed-radius dimension is a zero of the corresponding pressure.
Blueprint node `bs:finite-scale-root`. -/
theorem finiteScalePointwiseBowenEquation :
    let d := (σ.timeLimit (fun n => finiteScaleBSCost P T u A x n r)).toReal
    σ.timeLimit (fun n => finiteScalePressureRate P T (fun y => -d * u y) A x n r) = 0 := by
  intro d
  obtain ⟨v, hv⟩ := exists_coe_eq_timeLimit_pressureRate P T u a b A x r hbounds σ
    hfinite d
  have hb := pos_of_eventually_realizer_bounds hT ha hr hbounds
  have hd : (d : EReal) = σ.timeLimit (fun n => (finiteScaleBSCost P T u A x n r : EReal)) := by
    rw [← coe_timeLimit_ennreal]
    exact (EReal.coe_ennreal_toReal
      (finiteScalePointwiseBowenEquation_finite P T hT u a b ha A x r hr hbounds σ hfinite).ne)
  have hle : v ≤ 0 := by
    by_contra hpos
    have H := ratioPressureSignedComparison_limit_positive P T hT u a b ha A x r hr hbounds σ
      d v hv (not_le.mp hpos)
    rw [← hd] at H
    have := EReal.coe_le_coe_iff.mp H
    have := div_pos (not_le.mp hpos) hb
    linarith
  have hge : 0 ≤ v := by
    by_contra hneg
    have H := ratioPressureSignedComparison_limit_negative P T hT u a b ha A x r hr hbounds σ
      d v hv (not_le.mp hneg)
    rw [← hd] at H
    have := EReal.coe_le_coe_iff.mp H
    have := div_neg_of_neg_of_pos (not_le.mp hneg) hb
    linarith
  rw [hv, le_antisymm hle hge]
  rfl

end FixedRadius
end Kolmogorov.PointToSet
