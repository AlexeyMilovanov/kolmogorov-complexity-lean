import KolmogorovMathlib.AlgorithmicRandomness.LSCAux
import KolmogorovMathlib.AlgorithmicRandomness.LevelStrings

/-!
# Integrals of dyadic stage functions and their computable approximation

A *stage function* of level `s` is determined by a table `G : BitString → ℕ`:
its value at `w` is `G (w ↾ s) / 2 ^ s`.  Its integral against a measure `μ` is
the finite sum `∑_{|x| = s} G x / 2 ^ s * μ (Ω_x)`.

If `μ` is computable with approximation family `a`, the dyadic rational
`stageNum G a s p / 2 ^ (s + p)` approximates that integral with error at most
`stageMass G s / 2 ^ (s + p)`.  Choosing the precision `stagePrec G s` makes the
error at most `1/4`, which yields a decidable test `stageAccept` that

* accepts whenever the integral is at most `1`, and
* guarantees an integral of at most `2` whenever it accepts.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ## Dyadic arithmetic -/

/-- Comparison of two dyadic rationals `m / 2^k` and `n / 2^j` reduces to the integer inequality
`m · 2^j ≤ n · 2^k`. -/
lemma dyadicValue_le_dyadicValue_iff (m k n j : ℕ) :
    dyadicValue m k ≤ dyadicValue n j ↔ m * 2 ^ j ≤ n * 2 ^ k := by
  have hc : ((2 : ℝ≥0∞) ^ (k + j)) ≠ 0 := by positivity
  have hc' : ((2 : ℝ≥0∞) ^ (k + j)) ≠ ⊤ := by simp
  have key : ∀ x y : ℝ≥0∞, x ≤ y ↔ x * (2 : ℝ≥0∞) ^ (k + j) ≤ y * (2 : ℝ≥0∞) ^ (k + j) :=
    fun x y => (ENNReal.mul_le_mul_iff_left hc hc').symm
  rw [key]
  have e1 : dyadicValue m k * (2 : ℝ≥0∞) ^ (k + j) = (m : ℝ≥0∞) * 2 ^ j := by
    unfold dyadicValue
    rw [pow_add, ← mul_assoc, ENNReal.div_mul_cancel (by positivity) (by simp)]
  have e2 : dyadicValue n j * (2 : ℝ≥0∞) ^ (k + j) = (n : ℝ≥0∞) * 2 ^ k := by
    unfold dyadicValue
    rw [add_comm k j, pow_add, ← mul_assoc, ENNReal.div_mul_cancel (by positivity) (by simp)]
  rw [e1, e2]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- Dyadic values at a common denominator add by adding numerators. -/
lemma dyadicValue_add_dyadicValue (m n k : ℕ) :
    dyadicValue m k + dyadicValue n k = dyadicValue (m + n) k :=
  (dyadicValue_add m n k).symm

/-- At denominator zero the dyadic value is the numerator itself. -/
lemma dyadicValue_zero_denom (m : ℕ) : dyadicValue m 0 = (m : ℝ≥0∞) := by
  simp [dyadicValue]

/-- Multiplying dyadic values multiplies numerators and adds denominators. -/
lemma dyadicValue_mul_dyadicValue (m n s p : ℕ) :
    dyadicValue m s * dyadicValue n p = dyadicValue (m * n) (s + p) := by
  rw [dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow, dyadicValue_eq_mul_inv_pow, pow_add]
  push_cast
  ring

/-- The dyadic value of a finite sum of numerators is the sum of the dyadic values. -/
lemma dyadicValue_finset_sum {ι : Type*} (t : Finset ι) (f : ι → ℕ) (k : ℕ) :
    dyadicValue (∑ x ∈ t, f x) k = ∑ x ∈ t, dyadicValue (f x) k := by
  classical
  induction t using Finset.induction with
  | empty => simp [dyadicValue]
  | insert x t hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih, dyadicValue_add_dyadicValue]

/-! ## Stage functions -/

/-- The level-`s` basic function determined by the table `G`. -/
noncomputable def stageFun (G : BitString → ℕ) (s : ℕ) (w : CantorSeq) : ℝ≥0∞ :=
  dyadicValue (G (cantorPrefix w s)) s

/-- The numerator of the approximate integral of a stage function, at precision
`p`. -/
def stageNum (G : BitString → ℕ) (a : BitString → ℕ → ℕ) (s p : ℕ) : ℕ :=
  ((levelList s).map (fun x => G x * a x p)).sum

/-- The total numerator mass of a stage table: the error of the approximate
integral is `stageMass / 2 ^ (s + p)`. -/
def stageMass (G : BitString → ℕ) (s : ℕ) : ℕ :=
  ((levelList s).map G).sum

/-- The stage numerator is the sum over all length-`s` strings of the weight `G x` times the
approximation `a x p`. -/
lemma stageNum_eq_sum (G : BitString → ℕ) (a : BitString → ℕ → ℕ) (s p : ℕ) :
    stageNum G a s p = ∑ x ∈ levelFinset s, G x * a x p :=
  (sum_levelFinset_eq_sum_levelList s _).symm

/-- The stage mass is the sum of the weights `G x` over all strings of length `s`. -/
lemma stageMass_eq_sum (G : BitString → ℕ) (s : ℕ) :
    stageMass G s = ∑ x ∈ levelFinset s, G x :=
  (sum_levelFinset_eq_sum_levelList s _).symm

variable {μ : Measure CantorSeq}

/-- The integral of a stage function is the sum of its dyadic values weighted by the measures of
the length-`s` cylinders. -/
lemma lintegral_stageFun (μ : Measure CantorSeq) (G : BitString → ℕ) (s : ℕ) :
    ∫⁻ w, stageFun G s w ∂μ = ∑ x ∈ levelFinset s, dyadicValue (G x) s * cantorMass μ x :=
  lintegral_comp_cantorPrefix μ s (fun x => dyadicValue (G x) s)

/-- Stage functions are monotone in their weight table. -/
lemma stageFun_mono {G H : BitString → ℕ} {s : ℕ} (h : ∀ x, G x ≤ H x) (w : CantorSeq) :
    stageFun G s w ≤ stageFun H s w :=
  lscDyadicValue_mono s (h _)

/-- The integral of a stage function is at most its approximation plus the
error term. -/
lemma lintegral_stageFun_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (G : BitString → ℕ) (s p : ℕ) :
    ∫⁻ w, stageFun G s w ∂μ
      ≤ dyadicValue (stageNum G a s p) (s + p) + dyadicValue (stageMass G s) (s + p) := by
  rw [lintegral_stageFun, stageNum_eq_sum, stageMass_eq_sum, dyadicValue_finset_sum,
    dyadicValue_finset_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  calc dyadicValue (G x) s * cantorMass μ x
      ≤ dyadicValue (G x) s * (dyadicValue (a x p) p + dyadicValue 1 p) := by
        gcongr
        exact (ha x p).2
    _ = dyadicValue (G x * a x p) (s + p) + dyadicValue (G x * 1) (s + p) := by
        rw [mul_add, dyadicValue_mul_dyadicValue, dyadicValue_mul_dyadicValue]
    _ = dyadicValue (G x * a x p) (s + p) + dyadicValue (G x) (s + p) := by rw [mul_one]

/-- The approximate integral of a stage function is at most the integral plus
the error term. -/
lemma dyadicValue_stageNum_le {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (G : BitString → ℕ) (s p : ℕ) :
    dyadicValue (stageNum G a s p) (s + p)
      ≤ ∫⁻ w, stageFun G s w ∂μ + dyadicValue (stageMass G s) (s + p) := by
  rw [lintegral_stageFun, stageNum_eq_sum, stageMass_eq_sum, dyadicValue_finset_sum,
    dyadicValue_finset_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  calc dyadicValue (G x * a x p) (s + p)
      = dyadicValue (G x) s * dyadicValue (a x p) p := (dyadicValue_mul_dyadicValue _ _ _ _).symm
    _ ≤ dyadicValue (G x) s * (cantorMass μ x + dyadicValue 1 p) := by
        gcongr
        exact (ha x p).1
    _ = dyadicValue (G x) s * cantorMass μ x + dyadicValue (G x * 1) (s + p) := by
        rw [mul_add, dyadicValue_mul_dyadicValue]
    _ = dyadicValue (G x) s * cantorMass μ x + dyadicValue (G x) (s + p) := by rw [mul_one]

/-! ## The acceptance test -/

/-- The precision at which the approximate integral of the stage `s` table `G`
is computed: it makes the approximation error at most `1/4`. -/
def stagePrec (G : BitString → ℕ) (s : ℕ) : ℕ := Nat.log 2 (stageMass G s + 1) + 3

/-- The chosen stage precision is large enough that four times the stage mass fits below
`2^{stagePrec G s}`. -/
lemma four_mul_stageMass_le (G : BitString → ℕ) (s : ℕ) :
    4 * stageMass G s ≤ 2 ^ stagePrec G s := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (stageMass G s + 1)
  have h2 : (2 : ℕ) ^ stagePrec G s = 4 * (2 * 2 ^ (Nat.log 2 (stageMass G s + 1))) := by
    unfold stagePrec
    ring
  simp only [Nat.succ_eq_add_one, pow_succ] at h
  omega

/-- The stage mass, measured at the combined precision, is at most `1/4`. -/
lemma dyadicValue_stageMass_le_quarter (G : BitString → ℕ) (s : ℕ) :
    dyadicValue (stageMass G s) (s + stagePrec G s) ≤ dyadicValue 1 2 := by
  rw [dyadicValue_le_dyadicValue_iff]
  calc stageMass G s * 2 ^ 2 = 4 * stageMass G s := by ring
    _ ≤ 2 ^ stagePrec G s := four_mul_stageMass_le G s
    _ ≤ 1 * 2 ^ (s + stagePrec G s) := by
        rw [one_mul, pow_add]
        exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)

/-- The stage `s` table `G` is accepted if its approximate integral is at most
`3/2`. -/
def stageAccept (G : BitString → ℕ) (a : BitString → ℕ → ℕ) (s : ℕ) : Bool :=
  decide (stageNum G a s (stagePrec G s) * 2 ^ 2 ≤ 6 * 2 ^ (s + stagePrec G s))

/-- An accepted stage has integral at most `2`. -/
lemma lintegral_stageFun_le_of_accept {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {G : BitString → ℕ} {s : ℕ} (h : stageAccept G a s = true) :
    ∫⁻ w, stageFun G s w ∂μ ≤ 2 := by
  have hnum : stageNum G a s (stagePrec G s) * 2 ^ 2 ≤ 6 * 2 ^ (s + stagePrec G s) := by
    simpa [stageAccept] using h
  have h1 : dyadicValue (stageNum G a s (stagePrec G s)) (s + stagePrec G s)
      ≤ dyadicValue 6 2 := (dyadicValue_le_dyadicValue_iff _ _ _ _).2 hnum
  have h2 := lintegral_stageFun_le ha G s (stagePrec G s)
  have h3 := dyadicValue_stageMass_le_quarter G s
  have hfinal : dyadicValue 6 2 + dyadicValue 1 2 ≤ (2 : ℝ≥0∞) := by
    rw [dyadicValue_add_dyadicValue, show ((2 : ℝ≥0∞)) = dyadicValue 2 0 by
      rw [dyadicValue_zero_denom]; norm_num, dyadicValue_le_dyadicValue_iff]
    norm_num
  exact h2.trans ((add_le_add h1 h3).trans hfinal)

/-- A stage with integral at most `1` is accepted. -/
lemma stageAccept_of_lintegral_le_one {a : BitString → ℕ → ℕ}
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass μ x + dyadicValue 1 s ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {G : BitString → ℕ} {s : ℕ} (h : ∫⁻ w, stageFun G s w ∂μ ≤ 1) :
    stageAccept G a s = true := by
  have hone : (1 : ℝ≥0∞) = dyadicValue 4 2 := by
    have h4 : dyadicValue 4 2 = dyadicValue 1 0 :=
      le_antisymm ((dyadicValue_le_dyadicValue_iff _ _ _ _).2 (by norm_num))
        ((dyadicValue_le_dyadicValue_iff _ _ _ _).2 (by norm_num))
    rw [h4, dyadicValue_zero_denom]
    norm_num
  have hchain : dyadicValue (stageNum G a s (stagePrec G s)) (s + stagePrec G s)
      ≤ dyadicValue 6 2 := by
    refine (dyadicValue_stageNum_le ha G s (stagePrec G s)).trans ?_
    refine (add_le_add h (dyadicValue_stageMass_le_quarter G s)).trans ?_
    rw [hone, dyadicValue_add_dyadicValue]
    exact lscDyadicValue_mono 2 (by norm_num)
  have := (dyadicValue_le_dyadicValue_iff _ _ _ _).1 hchain
  simpa [stageAccept] using this

end Kolmogorov
