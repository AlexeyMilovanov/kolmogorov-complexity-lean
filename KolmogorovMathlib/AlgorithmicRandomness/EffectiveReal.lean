import Mathlib.Data.Rat.Denumerable
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.Interface.ComputableReals.ClosureProperties

/-!
# Effective Reals

This module implements the computable and lower-semicomputable nonnegative reals
with explicit approximations, as required for SUV Chapter 3.

## Conflation guard
Cylinder mass `p(x) = p(x0) + p(x1)` (equality, §3.1) ≠ tree semimeasure
`a(x) ≥ a(x0) + a(x1)` (inequality, Thm 75) ≠ the existing discrete
`aprioriMeasure`. No identification without a proved bridge.
-/

namespace Kolmogorov

open ENNReal

/-- A nonnegative real `x` is lower-semicomputable if it is the supremum of a
computable monotone sequence of dyadic rationals. -/
def IsLowerSemicomputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → ℕ,
    (∀ s, dyadicValue (approx s) s ≤ dyadicValue (approx (s + 1)) (s + 1)) ∧
    (⨆ s, dyadicValue (approx s) s = x) ∧
    Computable approx

/-- A nonnegative real `x` is computable if it has a computable sequence of
dyadic rational approximations that converges effectively. -/
def IsComputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → ℕ,
    (∀ s, x ≤ dyadicValue (approx s) s + dyadicValue 1 s ∧
          dyadicValue (approx s) s ≤ x + dyadicValue 1 s) ∧
    Computable approx

/-- From two-sided dyadic approximations of a number, the non-decreasing sequence of numerators
whose dyadic values converge to it from below. -/
def computableENNRealToLowerApprox (approx : ℕ → ℕ) : ℕ → ℕ :=
  fun s => Nat.rec (approx 0 - 1)
    (fun n ih => max (2 * ih) (approx (n + 1) - 1)) s

/-- At stage zero the lower approximation is the two-sided one decreased by one. -/
lemma computableENNRealToLowerApprox_zero (approx : ℕ → ℕ) :
    computableENNRealToLowerApprox approx 0 = approx 0 - 1 := rfl

/-- At each further stage the lower approximation is the larger of the doubled previous value and
the new two-sided approximation decreased by one. -/
lemma computableENNRealToLowerApprox_succ (approx : ℕ → ℕ) (s : ℕ) :
    computableENNRealToLowerApprox approx (s + 1) =
      max (2 * computableENNRealToLowerApprox approx s) (approx (s + 1) - 1) := rfl

private lemma dyadicValue_one_eq_inv_two_pow (s : ℕ) :
    dyadicValue 1 s = (2⁻¹ : ℝ≥0∞) ^ s :=
  dyadicValue_one_eq_inv_two_pow' s

private lemma dyadicValue_sub_one_le {x : ℝ≥0∞} {n s : ℕ}
    (h : dyadicValue n s ≤ x + dyadicValue 1 s) :
    dyadicValue (n - 1) s ≤ x := by
  by_cases hn : n = 0
  · simp [hn, dyadicValue]
  have hn1 : n - 1 + 1 = n :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
  apply (ENNReal.add_le_add_iff_right
    (a := dyadicValue 1 s) (b := dyadicValue (n - 1) s) (c := x)
    (by simp [dyadicValue])).mp
  rw [← dyadicValue_add, hn1]
  exact h

private lemma dyadicValue_le_sub_one_add (n s : ℕ) :
    dyadicValue n s ≤ dyadicValue (n - 1) s + dyadicValue 1 s := by
  rw [← dyadicValue_add]
  unfold dyadicValue
  gcongr
  exact_mod_cast (by omega : n ≤ n - 1 + 1)

/-- The dyadic values of the lower approximations are non-decreasing in the stage. -/
lemma computableENNRealToLowerApprox_mono (approx : ℕ → ℕ) (s : ℕ) :
    dyadicValue (computableENNRealToLowerApprox approx s) s ≤
      dyadicValue (computableENNRealToLowerApprox approx (s + 1)) (s + 1) := by
  rw [computableENNRealToLowerApprox_succ]
  rw [← dyadicValue_two_mul_succ]
  unfold dyadicValue
  gcongr
  exact_mod_cast Nat.le_max_left (2 * computableENNRealToLowerApprox approx s)
    (approx (s + 1) - 1)

/-- The lower approximation dominates the two-sided approximation decreased by one. -/
lemma computableENNRealToLowerApprox_ge (approx : ℕ → ℕ) (s : ℕ) :
    dyadicValue (approx s - 1) s ≤
      dyadicValue (computableENNRealToLowerApprox approx s) s := by
  cases s with
  | zero => rfl
  | succ s =>
      rw [computableENNRealToLowerApprox_succ]
      unfold dyadicValue
      gcongr
      exact_mod_cast Nat.le_max_right (2 * computableENNRealToLowerApprox approx s)
        (approx (s + 1) - 1)

/-- The lower approximations never exceed the number they approximate. -/
lemma computableENNRealToLowerApprox_le_x {x : ℝ≥0∞} {approx : ℕ → ℕ}
    (hbound : ∀ s, x ≤ dyadicValue (approx s) s + dyadicValue 1 s ∧
      dyadicValue (approx s) s ≤ x + dyadicValue 1 s)
    (s : ℕ) : dyadicValue (computableENNRealToLowerApprox approx s) s ≤ x := by
  induction s with
  | zero => exact dyadicValue_sub_one_le (hbound 0).2
  | succ s ih =>
      rw [computableENNRealToLowerApprox_succ]
      by_cases hmax :
          2 * computableENNRealToLowerApprox approx s ≤ approx (s + 1) - 1
      · rw [Nat.max_eq_right hmax]
        exact dyadicValue_sub_one_le (hbound (s + 1)).2
      · rw [Nat.max_eq_left (Nat.le_of_not_ge hmax)]
        rwa [dyadicValue_two_mul_succ]

private lemma le_computableENNRealToLowerApprox_add_error
    {x : ℝ≥0∞} {approx : ℕ → ℕ}
    (hbound : ∀ s, x ≤ dyadicValue (approx s) s + dyadicValue 1 s ∧
      dyadicValue (approx s) s ≤ x + dyadicValue 1 s)
    (s : ℕ) :
    x ≤ dyadicValue (computableENNRealToLowerApprox approx s) s +
      dyadicValue 1 s + dyadicValue 1 s := by
  calc
    x ≤ dyadicValue (approx s) s + dyadicValue 1 s := (hbound s).1
    _ ≤ (dyadicValue (approx s - 1) s + dyadicValue 1 s) +
        dyadicValue 1 s := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (dyadicValue_le_sub_one_add (approx s) s)
          (dyadicValue 1 s)
    _ ≤ (dyadicValue (computableENNRealToLowerApprox approx s) s +
        dyadicValue 1 s) + dyadicValue 1 s := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (computableENNRealToLowerApprox_ge approx s)
          (dyadicValue 1 s + dyadicValue 1 s)

/-- The lower approximations converge to the number: their supremum is exactly it. -/
lemma computableENNRealToLowerApprox_limit {x : ℝ≥0∞} {approx : ℕ → ℕ}
    (hbound : ∀ s, x ≤ dyadicValue (approx s) s + dyadicValue 1 s ∧
      dyadicValue (approx s) s ≤ x + dyadicValue 1 s) :
    (⨆ s, dyadicValue (computableENNRealToLowerApprox approx s) s) = x := by
  apply le_antisymm
  · exact iSup_le fun s => computableENNRealToLowerApprox_le_x hbound s
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hhalf : (↑ε / 2 : ℝ≥0∞) ≠ 0 := by
      exact ENNReal.div_ne_zero.mpr
        ⟨ENNReal.coe_ne_zero.mpr hε.ne', by norm_num⟩
    obtain ⟨s, hs⟩ := ENNReal.exists_inv_two_pow_lt hhalf
    have herr : dyadicValue 1 s + dyadicValue 1 s ≤ (ε : ℝ≥0∞) := by
      rw [dyadicValue_one_eq_inv_two_pow]
      calc
        (2⁻¹ : ℝ≥0∞) ^ s + 2⁻¹ ^ s ≤ ↑ε / 2 + ↑ε / 2 :=
          add_le_add hs.le hs.le
        _ = ε := by
          rw [ENNReal.div_eq_inv_mul]
          rw [mul_comm (2⁻¹ : ℝ≥0∞) (ε : ℝ≥0∞), ← mul_two]
          exact ENNReal.inv_mul_cancel_right (a := (ε : ℝ≥0∞)) (b := 2)
            (by norm_num) (by norm_num)
    calc
      x ≤ (dyadicValue (computableENNRealToLowerApprox approx s) s +
          dyadicValue 1 s) + dyadicValue 1 s :=
        le_computableENNRealToLowerApprox_add_error hbound s
      _ = dyadicValue (computableENNRealToLowerApprox approx s) s +
          (dyadicValue 1 s + dyadicValue 1 s) := add_assoc _ _ _
      _ ≤ (⨆ t, dyadicValue (computableENNRealToLowerApprox approx t) t) +
          (dyadicValue 1 s + dyadicValue 1 s) := by
        simpa [add_comm] using add_le_add_right
          (le_iSup (fun t => dyadicValue (computableENNRealToLowerApprox approx t) t) s)
          (dyadicValue 1 s + dyadicValue 1 s)
      _ ≤ (⨆ t, dyadicValue (computableENNRealToLowerApprox approx t) t) + ε := by
        simpa [add_comm] using add_le_add_right herr
          (⨆ t, dyadicValue (computableENNRealToLowerApprox approx t) t)

/-- The lower approximation sequence is computable when the two-sided one is. -/
lemma computable_computableENNRealToLowerApprox {approx : ℕ → ℕ}
    (hcomp : Computable approx) :
    Computable (computableENNRealToLowerApprox approx) := by
  let step : ℕ → ℕ × ℕ → ℕ :=
    fun _ q => max (2 * q.2) (approx (q.1 + 1) - 1)
  have hmul : Computable (fun n : ℕ => 2 * n) :=
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp
  have hstep : Computable (fun r : ℕ × (ℕ × ℕ) => step r.1 r.2) := by
    have hleft : Computable (fun r : ℕ × (ℕ × ℕ) => 2 * r.2.2) :=
      hmul.comp (Computable.snd.comp Computable.snd)
    have hright : Computable (fun r : ℕ × (ℕ × ℕ) =>
        approx (r.2.1 + 1) - 1) := by
      have hstage : Computable (fun r : ℕ × (ℕ × ℕ) => r.2.1 + 1) :=
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.const 1)).to_comp
      exact (Primrec.nat_sub.to_comp.comp (hcomp.comp hstage)
        (Computable.const 1)).of_eq (fun _ => rfl)
    exact Primrec.nat_max.to_comp.comp hleft hright
  have hrec : Computable (fun p : ℕ =>
      Nat.rec (motive := fun _ => ℕ) (approx 0 - 1)
        (fun n ih => step p (n, ih)) p) :=
    Computable.nat_rec Computable.id (Computable.const (approx 0 - 1)) hstep.to₂
  exact hrec.of_eq (fun _ => rfl)

/-- The lower approximation sequence is computable uniformly in a parameter. -/
lemma computable₂_computableENNRealToLowerApprox
    {alpha : Type*} [Primcodable alpha] (approx : alpha → ℕ → ℕ)
    (hcomp : Computable₂ approx) :
    Computable₂ (fun a s => computableENNRealToLowerApprox (approx a) s) := by
  let base : alpha × ℕ → ℕ := fun p => approx p.1 0 - 1
  let step : alpha × ℕ → ℕ × ℕ → ℕ :=
    fun p q => max (2 * q.2) (approx p.1 (q.1 + 1) - 1)
  have hbase : Computable base := by
    have hzero : Computable (fun p : alpha × ℕ => approx p.1 0) :=
      hcomp.comp Computable.fst (Computable.const 0)
    exact (Primrec.nat_sub.to_comp.comp hzero (Computable.const 1)).of_eq
      (fun _ => rfl)
  have hmul : Computable (fun n : ℕ => 2 * n) :=
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp
  have hstep : Computable (fun r : (alpha × ℕ) × (ℕ × ℕ) =>
      step r.1 r.2) := by
    have hleft : Computable (fun r : (alpha × ℕ) × (ℕ × ℕ) =>
        2 * r.2.2) := hmul.comp (Computable.snd.comp Computable.snd)
    have hstage : Computable (fun r : (alpha × ℕ) × (ℕ × ℕ) =>
        r.2.1 + 1) := (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.const 1)).to_comp
    have hright : Computable (fun r : (alpha × ℕ) × (ℕ × ℕ) =>
        approx r.1.1 (r.2.1 + 1) - 1) := by
      have happ : Computable (fun r : (alpha × ℕ) × (ℕ × ℕ) =>
          approx r.1.1 (r.2.1 + 1)) :=
        hcomp.comp (Computable.fst.comp Computable.fst) hstage
      exact (Primrec.nat_sub.to_comp.comp happ (Computable.const 1)).of_eq
        (fun _ => rfl)
    exact Primrec.nat_max.to_comp.comp hleft hright
  have hrec : Computable (fun p : alpha × ℕ =>
      Nat.rec (motive := fun _ => ℕ) (base p)
        (fun n ih => step p (n, ih)) p.2) :=
    Computable.nat_rec Computable.snd hbase hstep.to₂
  exact hrec.of_eq (fun _ => rfl)

/-- A computable extended nonnegative real is lower semicomputable. -/
lemma isLowerSemicomputableENNReal_of_isComputableENNReal {x : ℝ≥0∞}
    (h : IsComputableENNReal x) : IsLowerSemicomputableENNReal x := by
  rcases h with ⟨approx, hbound, hcomp⟩
  use computableENNRealToLowerApprox approx
  refine ⟨computableENNRealToLowerApprox_mono approx,
    computableENNRealToLowerApprox_limit hbound,
    computable_computableENNRealToLowerApprox hcomp⟩

end Kolmogorov



open Kolmogorov.ComputableReals

/-- Every natural number is strictly below `2^n`. -/
lemma two_pow_gt (n : ℕ) : n < 2 ^ n := by
  exact Nat.lt_two_pow_self

/-- For every positive rational there is a negative power of two below it. -/
lemma exists_inv_two_pow_lt_posRat (ε : ℚ) (hε : 0 < ε) :
    ∃ s : ℕ, (2⁻¹ : ℚ) ^ s < ε :=
  ⟨ε.den, by
    have h1 : (1 : ℚ) / 2 ^ (ε.den : ℕ) < 1 / ε.den := by
      apply one_div_lt_one_div_of_lt (by exact_mod_cast ε.pos)
      exact_mod_cast two_pow_gt ε.den
    have h2 : (1 : ℚ) / ε.den ≤ ε := by
      nth_rw 2 [← Rat.num_div_den ε]
      apply div_le_div_of_nonneg_right
      · have : 0 < ε.num := Rat.num_pos.mpr hε
        exact_mod_cast this
      · exact_mod_cast (le_of_lt ε.pos)
    have h3 : (2⁻¹ : ℚ) ^ (ε.den : ℕ) = (1 : ℚ) / 2 ^ (ε.den : ℕ) := by
      simp [inv_pow]
    rw [h3]
    exact lt_of_lt_of_le h1 h2⟩

/-- The denominator of a positive rational precision, used as a computable index for it. -/
def precisionIndex (ε : ℚ) : ℕ := ε.den

/-- The precision index of a rational is computable. -/
lemma computable_precisionIndex : Computable precisionIndex :=
  Kolmogorov.computable_ratDen

/-- Shifting a two-sided `ε/2`-approximation down by `ε/2` yields a lower approximation with
error at most `ε`. -/
lemma computableReal_lowerApprox_bound (x : ℝ) (approx : ℚ → ℚ) (ε : ℚ) (hε : 0 < ε)
    (h_approx : ∀ δ : ℚ, 0 < δ → |(approx δ : ℝ) - x| ≤ δ) :
    (approx (ε / 2) : ℝ) - ε / 2 ≤ x ∧ x ≤ (approx (ε / 2) : ℝ) - ε / 2 + ε := by
  have h_pos : (0 : ℚ) < ε / 2 := half_pos hε
  have h_bound := h_approx (ε / 2) h_pos
  rw [abs_le] at h_bound
  have h1 := h_bound.1
  have h2 := h_bound.2
  constructor
  · push_cast at h1 h2 ⊢
    linarith
  · push_cast at h1 h2 ⊢
    linarith

/-- A real is computable exactly when it has a computable family of rational lower approximations
of arbitrary prescribed accuracy. -/
lemma isComputableReal_iff_exists_computable_lowerApprox (x : ℝ) :
    IsComputableReal x ↔ ∃ approx : ℚ → ℚ, Computable approx ∧
      ∀ (ε : ℚ), 0 < ε → (approx ε : ℝ) ≤ x ∧ x ≤ (approx ε : ℝ) + ε := by
  constructor
  · rintro ⟨approx, hcomp, hbound⟩
    replace hbound : ∀ δ : ℚ, 0 < δ → |((approx δ : ℚ) : ℝ) - x| ≤ (δ : ℝ) :=
      fun δ hδ => by rw [abs_sub_comm]; exact hbound δ hδ
    use fun ε => approx (ε / 2) - ε / 2
    constructor
    · exact Computable₂.comp Kolmogorov.computable₂_ratSub
        (hcomp.comp Kolmogorov.computable_ratHalf) Kolmogorov.computable_ratHalf
    · intro ε hε
      have := computableReal_lowerApprox_bound x approx ε hε hbound
      push_cast at this ⊢
      exact this
  · rintro ⟨approx, hcomp, hbound⟩
    use fun ε => approx (ε / 2) + ε / 2
    constructor
    · exact Computable₂.comp Kolmogorov.computable₂_ratAdd
        (hcomp.comp Kolmogorov.computable_ratHalf) Kolmogorov.computable_ratHalf
    · intro ε hε
      have h := hbound (ε / 2) (half_pos hε)
      rw [abs_le]
      constructor
      · push_cast at h ⊢; linarith
      · push_cast at h ⊢; linarith

/-- Computable reals are closed under addition: run both approximations at
half the requested precision. -/
lemma Kolmogorov.ComputableReals.IsComputableReal.add {x y : ℝ}
    (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x + y) := by
  obtain ⟨f, hfc, hf⟩ := hx
  obtain ⟨g, hgc, hg⟩ := hy
  refine ⟨fun ε => f (ε / 2) + g (ε / 2), ?_, ?_⟩
  · exact Computable₂.comp Kolmogorov.computable₂_ratAdd
      (hfc.comp Kolmogorov.computable_ratHalf)
      (hgc.comp Kolmogorov.computable_ratHalf)
  · intro ε hε
    have h1 := hf (ε / 2) (half_pos hε)
    have h2 := hg (ε / 2) (half_pos hε)
    rw [abs_le] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    constructor <;> [linarith [h1.1, h2.1]; linarith [h1.2, h2.2]]

/-- Computable reals are closed under subtraction. -/
lemma Kolmogorov.ComputableReals.IsComputableReal.sub {x y : ℝ}
    (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

/-- Precision schedule used for products: `mulPrecision t ε` is bounded by the
constant `t` and, for `ε ≤ 1`, equals `t * ε`. -/
def mulPrecision (t ε : ℚ) : ℚ := bif decide (ε ≤ 1) then ε * t else t

/-- The precision rescaling used for products is computable. -/
lemma computable_mulPrecision (t : ℚ) : Computable (mulPrecision t) :=
  Computable.cond Kolmogorov.computable_ratLeOne
    (Computable₂.comp Kolmogorov.computable₂_ratMul Computable.id
      (Computable.const t)) (Computable.const t)

/-- The rescaled precision is positive when both the factor and the target precision are. -/
lemma mulPrecision_pos {t ε : ℚ} (ht : 0 < t) (hε : 0 < ε) :
    0 < mulPrecision t ε := by
  by_cases h : ε ≤ 1 <;> simp [mulPrecision, h, mul_pos hε ht, ht]

/-- The rescaled precision is at most one for a factor in `(0, 1]`. -/
lemma mulPrecision_le_one {t ε : ℚ} (ht : 0 < t) (ht1 : t ≤ 1) :
    mulPrecision t ε ≤ 1 := by
  by_cases h : ε ≤ 1
  · simp only [mulPrecision, h, decide_true, Bool.cond_true]
    nlinarith
  · simpa [mulPrecision, h] using ht1

/-- Multiplying the rescaled precision by the reciprocal factor gives back at most the target
precision. -/
lemma mulPrecision_mul_le {t c ε : ℚ} (htc : t * c = 1) (hε : 0 < ε) :
    mulPrecision t ε * c ≤ ε := by
  by_cases h : ε ≤ 1
  · simp only [mulPrecision, h, decide_true, Bool.cond_true]
    nlinarith
  · simp only [mulPrecision, h, decide_false, Bool.cond_false]
    push Not at h
    linarith

/-- Computable reals are closed under multiplication. -/
lemma Kolmogorov.ComputableReals.IsComputableReal.mul {x y : ℝ}
    (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x * y) := by
  obtain ⟨f, hfc, hf⟩ := hx
  obtain ⟨g, hgc, hg⟩ := hy
  replace hf : ∀ ε : ℚ, 0 < ε → |((f ε : ℚ) : ℝ) - x| ≤ (ε : ℝ) :=
    fun ε hε => by rw [abs_sub_comm]; exact hf ε hε
  replace hg : ∀ ε : ℚ, 0 < ε → |((g ε : ℚ) : ℝ) - y| ≤ (ε : ℝ) :=
    fun ε hε => by rw [abs_sub_comm]; exact hg ε hε
  have hf1 : (0 : ℚ) ≤ |f 1| := abs_nonneg _
  have hg1 : (0 : ℚ) ≤ |g 1| := abs_nonneg _
  set c : ℚ := |f 1| + |g 1| + 3 with hc_def
  have hcpos : (0 : ℚ) < c := by rw [hc_def]; linarith
  set t : ℚ := 1 / c with ht_def
  have htpos : (0 : ℚ) < t := by rw [ht_def]; positivity
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hcpos, hc_def]; linarith
  have htc : t * c = 1 := by rw [ht_def]; field_simp
  refine ⟨fun ε => f (mulPrecision t ε) * g (mulPrecision t ε), ?_, ?_⟩
  · exact Computable₂.comp Kolmogorov.computable₂_ratMul
      (hfc.comp (computable_mulPrecision t)) (hgc.comp (computable_mulPrecision t))
  · intro ε hε
    rw [abs_sub_comm]
    set d : ℚ := mulPrecision t ε with hd_def
    have hdpos : (0 : ℚ) < d := mulPrecision_pos htpos hε
    have hd1 : d ≤ 1 := mulPrecision_le_one htpos ht1
    have hdc : d * c ≤ ε := mulPrecision_mul_le htc hε
    have hdposR : (0 : ℝ) < (d : ℚ) := by exact_mod_cast hdpos
    have hd1R : ((d : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hd1
    have hfd := hf d hdpos
    have hgd := hg d hdpos
    have hxM : |x| ≤ ((|f 1| : ℚ) : ℝ) + 1 := by
      have h1 := hf 1 one_pos
      have h2 : |x| - |((f 1 : ℚ) : ℝ)| ≤ |((f 1 : ℚ) : ℝ) - x| := by
        rw [abs_sub_comm]
        exact abs_sub_abs_le_abs_sub x _
      push_cast at h1 h2 ⊢
      linarith
    have hyN : |y| ≤ ((|g 1| : ℚ) : ℝ) + 1 := by
      have h1 := hg 1 one_pos
      have h2 : |y| - |((g 1 : ℚ) : ℝ)| ≤ |((g 1 : ℚ) : ℝ) - y| := by
        rw [abs_sub_comm]
        exact abs_sub_abs_le_abs_sub y _
      push_cast at h1 h2 ⊢
      linarith
    have hfdabs : |((f d : ℚ) : ℝ)| ≤ ((|f 1| : ℚ) : ℝ) + 1 + (d : ℝ) := by
      have := abs_sub_abs_le_abs_sub ((f d : ℚ) : ℝ) x
      linarith
    have hsplit : |((f d : ℚ) : ℝ) * ((g d : ℚ) : ℝ) - x * y| ≤
        |((f d : ℚ) : ℝ)| * |((g d : ℚ) : ℝ) - y| + |y| * |((f d : ℚ) : ℝ) - x| := by
      have hrw : ((f d : ℚ) : ℝ) * ((g d : ℚ) : ℝ) - x * y =
          ((f d : ℚ) : ℝ) * (((g d : ℚ) : ℝ) - y) + y * (((f d : ℚ) : ℝ) - x) := by
        ring
      rw [hrw]
      calc |((f d : ℚ) : ℝ) * (((g d : ℚ) : ℝ) - y) + y * (((f d : ℚ) : ℝ) - x)|
          ≤ |((f d : ℚ) : ℝ) * (((g d : ℚ) : ℝ) - y)| + |y * (((f d : ℚ) : ℝ) - x)| :=
            abs_add_le _ _
        _ = |((f d : ℚ) : ℝ)| * |((g d : ℚ) : ℝ) - y| + |y| * |((f d : ℚ) : ℝ) - x| := by
            rw [abs_mul, abs_mul]
    have hb1 : |((f d : ℚ) : ℝ)| * |((g d : ℚ) : ℝ) - y| ≤
        (((|f 1| : ℚ) : ℝ) + 1 + (d : ℝ)) * (d : ℝ) :=
      mul_le_mul hfdabs hgd (abs_nonneg _) (by positivity)
    have hb2 : |y| * |((f d : ℚ) : ℝ) - x| ≤ (((|g 1| : ℚ) : ℝ) + 1) * (d : ℝ) :=
      mul_le_mul hyN hfd (abs_nonneg _) (by positivity)
    have hdcR : (d : ℝ) * ((c : ℚ) : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hdc
    have hcR : ((c : ℚ) : ℝ) = ((|f 1| : ℚ) : ℝ) + ((|g 1| : ℚ) : ℝ) + 3 := by
      rw [hc_def]; push_cast; ring
    rw [hcR] at hdcR
    have hfin : (((|f 1| : ℚ) : ℝ) + 1 + (d : ℝ)) * (d : ℝ) +
        (((|g 1| : ℚ) : ℝ) + 1) * (d : ℝ) ≤ (ε : ℝ) := by nlinarith
    calc |((fun ε : ℚ => f (mulPrecision t ε) * g (mulPrecision t ε)) ε : ℚ) - x * y|
        = |((f d : ℚ) : ℝ) * ((g d : ℚ) : ℝ) - x * y| := by
          simp only [← hd_def]
          push_cast
          ring_nf
      _ ≤ _ := hsplit
      _ ≤ (ε : ℝ) := by linarith

/-- Every rational number is a computable real. -/
lemma Kolmogorov.ComputableReals.isComputableReal_ratCast (q : ℚ) : IsComputableReal (q : ℝ) :=
  ⟨fun _ => q, Computable.const q, fun ε hε => by simp [le_of_lt hε]⟩
