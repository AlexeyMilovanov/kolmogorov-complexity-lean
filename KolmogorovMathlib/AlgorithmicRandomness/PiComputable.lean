import KolmogorovMathlib.AlgorithmicRandomness.EffectiveReal
import Mathlib.Analysis.Real.Pi.Leibniz

/-!
# Computability of `π`

This module proves that `Real.pi` is a computable real in the sense of
`IsComputableReal` (SUV Problem 75, the `π` half): there is a computable map
`ℚ → ℚ` sending each positive rational precision `ε` to a rational within `ε`
of `π`.

The approximation used is the Leibniz series `π / 4 = ∑ (-1)^i / (2 i + 1)`,
truncated after an even number of terms.  Truncating an alternating series with
antitone terms after an even number of terms underestimates the limit by at most
the first omitted term, which gives the explicit error bound
`piPartial_two_mul_error`.

Main declarations:

* `Kolmogorov.oddInvSigned`, `Kolmogorov.computable_oddInvSigned` : the signed
  reciprocals of the odd numbers, as a computable sequence of rationals;
* `Kolmogorov.piPartial`, `Kolmogorov.computable_piPartial` : the partial sums
  of the Leibniz series and their computability;
* `Kolmogorov.piPartial_two_mul_error` : the truncation error after `2 k` terms
  is at most `1 / (4 k + 1)`;
* `Kolmogorov.piApprox`, `Kolmogorov.computable_piApprox` : the resulting
  precision-indexed approximation scheme;
* `Kolmogorov.isComputableReal_pi` : `π` is a computable real.
-/

namespace Kolmogorov


open ComputableReals
/-- The alternating sign `(-1) ^ i`, as a computable integer sequence. -/
lemma computable_negOnePow : Computable (fun i : ℕ => (-1 : ℤ) ^ i) := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℤ) => -p.2) :=
    (primrec_intNeg.to_comp.comp (Computable.snd.comp Computable.snd)).to₂
  have h : Computable (fun i : ℕ =>
      Nat.rec (motive := fun _ => ℤ) 1 (fun _ ih => -ih) i) :=
    Computable.nat_rec Computable.id (Computable.const 1) hh
  refine h.of_eq (fun i => ?_)
  induction i with
  | zero => rfl
  | succ i ih =>
      change -(Nat.rec (motive := fun _ => ℤ) 1 (fun _ ih => -ih) i) = (-1 : ℤ) ^ (i + 1)
      rw [ih, pow_succ]
      ring

/-- The `i`-th term `(-1) ^ i / (2 i + 1)` of the Leibniz series, as a rational. -/
def oddInvSigned (i : ℕ) : ℚ := (-1 : ℚ) ^ i / (2 * i + 1)

/-- The terms of the Leibniz series form a computable sequence of rationals. -/
lemma computable_oddInvSigned : Computable oddInvSigned :=
  computable_of_num_den (N := fun i : ℕ => (-1 : ℤ) ^ i) (D := fun i : ℕ => 2 * i + 1)
    computable_negOnePow
    ((Primrec₂.comp Primrec.nat_add
      (Primrec₂.comp Primrec.nat_mul (Primrec.const 2) Primrec.id) (Primrec.const 1)).to_comp)
    (fun i => Nat.succ_pos _)
    (fun i => by rw [oddInvSigned]; push_cast; ring)

/-- The `n`-th partial sum of the Leibniz series, as a rational number. -/
def piPartial (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, oddInvSigned i

/-- The partial sums of the Leibniz series are uniformly computable. -/
lemma computable_piPartial : Computable piPartial := by
  have hh : Computable₂ (fun (_ : ℕ) (p : ℕ × ℚ) => p.2 + oddInvSigned p.1) :=
    (Computable₂.comp computable₂_ratAdd (Computable.snd.comp Computable.snd)
      (computable_oddInvSigned.comp (Computable.fst.comp Computable.snd))).to₂
  have h : Computable (fun n : ℕ =>
      Nat.rec (motive := fun _ => ℚ) 0 (fun k ih => ih + oddInvSigned k) n) :=
    Computable.nat_rec Computable.id (Computable.const 0) hh
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => simp [piPartial]
  | succ n ih =>
      have hstep : Nat.rec (motive := fun _ => ℚ) 0
          (fun k ih => ih + oddInvSigned k) (n + 1)
          = piPartial n + oddInvSigned n := by rw [← ih]
      rw [hstep, piPartial, piPartial, Finset.sum_range_succ]

/-- The real number represented by `piPartial n` is the `n`-th partial sum of the
Leibniz series. -/
lemma cast_piPartial (n : ℕ) :
    ((piPartial n : ℚ) : ℝ)
      = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (1 / (2 * (i : ℝ) + 1)) := by
  simp [piPartial, oddInvSigned, div_eq_mul_inv]

/-- The magnitudes of the Leibniz terms are antitone. -/
lemma antitone_oddInv : Antitone (fun i : ℕ => 1 / (2 * (i : ℝ) + 1)) :=
  antitone_iff_forall_lt.mpr fun _ _ h => by
    have : ((_ : ℕ) : ℝ) ≤ _ := Nat.cast_le.mpr h.le
    gcongr

/-- The Leibniz series, written in the `∑ (-1) ^ i * f i` normal form, converges
to `π / 4`. -/
lemma tendsto_leibniz :
    Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (1 / (2 * (i : ℝ) + 1)))
      Filter.atTop (nhds (Real.pi / 4)) := by
  have h := Real.tendsto_sum_pi_div_four
  refine h.congr (fun n => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_one_div]

/-- Truncating the Leibniz series after `2 k` terms underestimates `π / 4` by at most
`1 / (4 k + 1)`. -/
lemma piPartial_two_mul_error (k : ℕ) :
    |((piPartial (2 * k) : ℚ) : ℝ) - Real.pi / 4| ≤ 1 / (4 * (k : ℝ) + 1) := by
  have hlow := antitone_oddInv.alternating_series_le_tendsto tendsto_leibniz k
  have hup := antitone_oddInv.tendsto_le_alternating_series tendsto_leibniz k
  rw [Finset.sum_range_succ] at hup
  have hsign : (-1 : ℝ) ^ (2 * k) = 1 := (even_two_mul k).neg_one_pow
  rw [hsign, one_mul] at hup
  have hcast : (2 * ((2 * k : ℕ) : ℝ) + 1) = 4 * (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hup
  rw [cast_piPartial, abs_le]
  constructor
  · have hpos : (0 : ℝ) ≤ 1 / (4 * (k : ℝ) + 1) := by positivity
    linarith
  · linarith

/-- The rational approximation scheme for `π`: at precision `ε` return four times the
Leibniz partial sum with `2 ε.den` terms. -/
def piApprox (eps : ℚ) : ℚ := 4 * piPartial (2 * eps.den)

/-- The approximation scheme for `π` is computable. -/
lemma computable_piApprox : Computable piApprox :=
  Computable₂.comp computable₂_ratMul (Computable.const 4)
    (computable_piPartial.comp
      (Computable₂.comp Primrec.nat_mul.to_comp (Computable.const 2) computable_ratDen))

/-- **SUV Problem 75 (the `π` half).** `π` is a computable real. -/
theorem isComputableReal_pi : IsComputableReal Real.pi := by
  refine ⟨piApprox, computable_piApprox, fun eps heps => ?_⟩
  rw [abs_sub_comm]
  have hden : 0 < eps.den := eps.pos
  have hdenR : (0 : ℝ) < (eps.den : ℝ) := by exact_mod_cast hden
  have hq : (1 : ℚ) / (eps.den : ℚ) ≤ eps := by
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    have h : eps * (eps.den : ℚ) = (eps.num : ℚ) := by exact_mod_cast Rat.mul_den_eq_num eps
    rw [h]
    exact_mod_cast Rat.num_pos.mpr heps
  have hR : (1 : ℝ) / (eps.den : ℝ) ≤ (eps : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at h
    exact h
  have herr := piPartial_two_mul_error eps.den
  have hval : ((piApprox eps : ℚ) : ℝ) = 4 * ((piPartial (2 * eps.den) : ℚ) : ℝ) := by
    rw [piApprox]; push_cast; ring
  have hstep : |((piApprox eps : ℚ) : ℝ) - Real.pi|
      = 4 * |((piPartial (2 * eps.den) : ℚ) : ℝ) - Real.pi / 4| := by
    rw [hval, show (4 : ℝ) * ((piPartial (2 * eps.den) : ℚ) : ℝ) - Real.pi
        = 4 * ((((piPartial (2 * eps.den) : ℚ) : ℝ)) - Real.pi / 4) by ring, abs_mul]
    norm_num
  rw [hstep]
  have hbound : 4 * |((piPartial (2 * eps.den) : ℚ) : ℝ) - Real.pi / 4|
      ≤ 4 * (1 / (4 * (eps.den : ℝ) + 1)) := by
    linarith
  refine hbound.trans (le_trans ?_ hR)
  have h4 : (4 : ℝ) * (1 / (4 * (eps.den : ℝ) + 1)) = 4 / (4 * (eps.den : ℝ) + 1) := by
    ring
  rw [h4, div_le_div_iff₀ (by positivity) hdenR]
  nlinarith [hdenR]

end Kolmogorov
