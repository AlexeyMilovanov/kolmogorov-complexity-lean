import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal

/-!
# Computability of Euler's number

This module proves that `Real.exp 1` is a computable real in the sense of
`IsComputableReal` (SUV Problem 75, the `e` half): there is a computable map
`ℚ → ℚ` sending each positive rational precision `ε` to a rational within `ε`
of `e`.

The approximation is the partial sum `expPartial n = ∑_{k < n} 1 / k!` of the
exponential series at `1`, evaluated at `n = ε.den + 2`.

Main declarations:

* `Kolmogorov.computable_factorial` : the factorial function is computable;
* `Kolmogorov.expPartial`, `Kolmogorov.computable_expPartial` : the rational
  partial sums of the exponential series at `1` and their computability;
* `Kolmogorov.expPartial_error` : the truncation error at `n + 2` terms is at
  most `2⁻ⁿ`;
* `Kolmogorov.expApprox`, `Kolmogorov.computable_expApprox` : the resulting
  precision-indexed approximation scheme;
* `Kolmogorov.isComputableReal_exp_one` : `e` is a computable real.
-/

namespace Kolmogorov


open ComputableReals
/-- The factorial function is computable. -/
lemma computable_factorial : Computable Nat.factorial := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => (p.1 + 1) * p.2) :=
    (Primrec₂.comp Primrec.nat_mul (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to_comp.to₂
  have h : Computable (fun n : ℕ =>
      Nat.rec (motive := fun _ => ℕ) 1 (fun k ih => (k + 1) * ih) n) :=
    Computable.nat_rec Computable.id (Computable.const 1) hh
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.factorial_succ]; exact congrArg (fun t => (n + 1) * t) ih

/-- The reciprocals of the factorials form a computable sequence of rationals. -/
lemma computable_invFactorial :
    Computable (fun n : ℕ => (1 : ℚ) / (Nat.factorial n : ℚ)) :=
  computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun n : ℕ => Nat.factorial n)
    (Computable.const 1) computable_factorial (fun n => Nat.factorial_pos n)
    (fun n => by push_cast; ring)

/-- The `n`-th partial sum `∑_{k < n} 1 / k!` of the exponential series at `1`,
as a rational number. -/
def expPartial (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, (1 : ℚ) / (Nat.factorial k : ℚ)

/-- The partial sums of the exponential series at `1` are uniformly computable. -/
lemma computable_expPartial : Computable expPartial := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 + (1 : ℚ) / (Nat.factorial p.1 : ℚ)) :=
    (Computable₂.comp computable₂_ratAdd (Computable.snd.comp Computable.snd)
      (computable_invFactorial.comp (Computable.fst.comp Computable.snd))).to₂
  have h : Computable (fun n : ℕ =>
      Nat.rec (motive := fun _ => ℚ) 0
        (fun k ih => ih + (1 : ℚ) / (Nat.factorial k : ℚ)) n) :=
    Computable.nat_rec Computable.id (Computable.const 0) hh
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => simp [expPartial]
  | succ n ih =>
      have hstep : Nat.rec (motive := fun _ => ℚ) 0
          (fun k ih => ih + (1 : ℚ) / (Nat.factorial k : ℚ)) (n + 1)
          = expPartial n + (1 : ℚ) / (Nat.factorial n : ℚ) := by rw [← ih]
      rw [hstep, expPartial, expPartial, Finset.sum_range_succ]

/-- The real number represented by `expPartial n` is the `n`-th partial sum of the
exponential series at `1`. -/
lemma cast_expPartial (n : ℕ) :
    ((expPartial n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (1 : ℝ) ^ m / (Nat.factorial m : ℝ) := by
  simp [expPartial]

/-- Factorials grow at least as fast as powers of two. -/
lemma two_pow_le_factorial_succ (n : ℕ) : 2 ^ n ≤ Nat.factorial (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfac : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := Nat.factorial_succ _
      rw [hfac, pow_succ]
      calc 2 ^ n * 2 ≤ Nat.factorial (n + 1) * 2 := Nat.mul_le_mul ih (le_refl 2)
        _ = 2 * Nat.factorial (n + 1) := Nat.mul_comm _ _
        _ ≤ (n + 2) * Nat.factorial (n + 1) := Nat.mul_le_mul (by omega) (le_refl _)

/-- Truncating the exponential series at `1` after `n + 2` terms commits an error of
at most `2⁻ⁿ`. -/
lemma expPartial_error (n : ℕ) :
    |((expPartial (n + 2) : ℚ) : ℝ) - Real.exp 1| ≤ 1 / 2 ^ n := by
  have hb := Real.exp_bound (x := 1) (by norm_num) (n := n + 2) (by omega)
  rw [cast_expPartial, abs_sub_comm]
  refine hb.trans ?_
  have hfac : (2 : ℝ) ^ (n + 1) ≤ (Nat.factorial (n + 2) : ℝ) := by
    exact_mod_cast two_pow_le_factorial_succ (n + 1)
  have hfacpos : (0 : ℝ) < (Nat.factorial (n + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 2)
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((Nat.succ (n + 2) : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
  have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
  rw [abs_one, one_pow, one_mul, hcast, hcast2,
    div_le_div_iff₀ (by positivity) h2pos, one_mul]
  nlinarith [hfac, h2pos, pow_succ (2 : ℝ) n]

/-- The rational approximation scheme for `e`: at precision `ε` return the partial
sum with `ε.den + 2` terms. -/
def expApprox (eps : ℚ) : ℚ := expPartial (eps.den + 2)

/-- The approximation scheme for `e` is computable. -/
lemma computable_expApprox : Computable expApprox :=
  computable_expPartial.comp
    (Computable₂.comp Primrec.nat_add.to_comp computable_ratDen (Computable.const 2))

/-- **SUV Problem 75 (the `e` half).** Euler's number is a computable real. -/
theorem isComputableReal_exp_one : IsComputableReal (Real.exp 1) := by
  refine ⟨expApprox, computable_expApprox, fun eps heps => ?_⟩
  rw [abs_sub_comm]
  have hden : 0 < eps.den := eps.pos
  have hq : (1 : ℚ) / (eps.den : ℚ) ≤ eps := by
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    have h : eps * (eps.den : ℚ) = (eps.num : ℚ) := by exact_mod_cast Rat.mul_den_eq_num eps
    rw [h]
    exact_mod_cast Rat.num_pos.mpr heps
  have hR : (1 : ℝ) / (eps.den : ℝ) ≤ (eps : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at h
    exact h
  have hlt : ((eps.den : ℕ) : ℝ) ≤ 2 ^ (eps.den : ℕ) := by
    exact_mod_cast (two_pow_gt eps.den).le
  have hdenR : (0 : ℝ) < (eps.den : ℝ) := by exact_mod_cast hden
  calc |((expApprox eps : ℚ) : ℝ) - Real.exp 1| ≤ 1 / 2 ^ (eps.den : ℕ) :=
        expPartial_error eps.den
    _ ≤ 1 / (eps.den : ℝ) := one_div_le_one_div_of_le hdenR hlt
    _ ≤ (eps : ℝ) := hR

end Kolmogorov
