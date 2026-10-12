import KolmogorovMathlib.Solomonoff.SelectedBits.Gain

/-!
# The square gain

The gain `1 + r ^ 2` at sibling ratio `r`, with limit multiplier `1 + e ^ 2`, logarithmic
constant `log 2` and exponent `2`.  It is the instance behind the square-loss endpoint: the
logarithmic estimate `log (1 + e ^ 2) ≥ e ^ 2 log 2` makes the factor `log 2` cancel against
the `log 2` of the description length.

* `squared_error_block_le_credit`, `sum_squared_error_blocks_le`: the telescoping estimate of
  the squared-error charges of consecutive mass blocks against a reciprocal potential, the
  integral-free form of `∫₀^a (b / (u + b)) ^ 2 du ≤ b`.
* `squareGain`, `computable₂_squareGain`, `squareGain_packing`: the rational gain, its
  computability and its packing inequality.
* `squareGainFamily`: the gain family, with `squareGainFamily_kappa` and
  `squareGainFamily_beta`.
-/

namespace Kolmogorov.SelectedBits

open Filter Topology

/-! ### The scalar telescoping estimate -/

/-- A finite mass block `[p, q]` below the available mass `a` is charged to a telescoping
reciprocal potential: `(q - p) (b / (a + b)) ^ 2 ≤ b ^ 2 / (p + b) - b ^ 2 / (q + b)`. -/
theorem squared_error_block_le_credit {p q a b : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hqa : q ≤ a) (hb : 0 < b) :
    (q - p) * (b / (a + b)) ^ 2 ≤
      b ^ 2 / (p + b) - b ^ 2 / (q + b) := by
  have hp_b : 0 < p + b := add_pos_of_nonneg_of_pos hp hb
  have hq_b : 0 < q + b := add_pos_of_nonneg_of_pos (hp.trans hpq) hb
  have ha_b : 0 < a + b := add_pos_of_nonneg_of_pos (hp.trans (hpq.trans hqa)) hb
  have h₁ : b / (a + b) ≤ b / (p + b) :=
    div_le_div_of_nonneg_left hb.le hp_b (by linarith)
  have h₂ : b / (a + b) ≤ b / (q + b) :=
    div_le_div_of_nonneg_left hb.le hq_b (by linarith)
  have hsquare : (b / (a + b)) ^ 2 ≤
      (b / (p + b)) * (b / (q + b)) := by
    rw [pow_two]
    exact mul_le_mul h₁ h₂ (div_nonneg hb.le ha_b.le) (div_nonneg hb.le hp_b.le)
  calc
    (q - p) * (b / (a + b)) ^ 2 ≤
        (q - p) * ((b / (p + b)) * (b / (q + b))) :=
      mul_le_mul_of_nonneg_left hsquare (sub_nonneg.mpr hpq)
    _ = b ^ 2 / (p + b) - b ^ 2 / (q + b) := by
      field_simp
      ring

/-- The squared-error charges of finitely many consecutive blocks `[w i, w (i + 1)]`, each
ending below its available mass `a i`, fit into the single budget `b`. -/
theorem sum_squared_error_blocks_le {n : ℕ} {w a : ℕ → ℝ} {b : ℝ}
    (hb : 0 < b) (hw : Monotone w) (hw0 : w 0 = 0)
    (hwa : ∀ i < n, w (i + 1) ≤ a i) :
    ∑ i ∈ Finset.range n, (w (i + 1) - w i) * (b / (a i + b)) ^ 2 ≤ b := by
  have hw_nonneg (i : ℕ) : 0 ≤ w i := by
    rw [← hw0]
    exact hw (Nat.zero_le i)
  calc
    ∑ i ∈ Finset.range n, (w (i + 1) - w i) * (b / (a i + b)) ^ 2 ≤
        ∑ i ∈ Finset.range n, (b ^ 2 / (w i + b) - b ^ 2 / (w (i + 1) + b)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact squared_error_block_le_credit (hw_nonneg i)
        (hw (Nat.le_succ i)) (hwa i (Finset.mem_range.mp hi)) hb
    _ = b - b ^ 2 / (w n + b) := by
      rw [Finset.sum_range_sub', hw0, zero_add]
      congr 1
      field_simp
    _ ≤ b := sub_le_self _ (div_nonneg (sq_nonneg b)
      (add_nonneg (hw_nonneg n) hb.le))

/-! ### The square gain -/

/-- The square gain `1 + r ^ 2`, independent of the stage. -/
def squareGain : ℕ → ℚ → ℚ := fun _ r => 1 + r ^ 2

/-- Unfolding the square gain. -/
@[simp] theorem squareGain_apply (s : ℕ) (r : ℚ) : squareGain s r = 1 + r ^ 2 := rfl

/-- The square gain is at least `1`. -/
theorem one_le_squareGain (s : ℕ) (r : ℚ) : 1 ≤ squareGain s r :=
  le_add_of_nonneg_right (sq_nonneg r)

/-- The square gain is computable. -/
theorem computable₂_squareGain : Computable₂ squareGain := by
  have hsq : Computable (fun p : ℕ × ℚ => p.2 * p.2) :=
    computable₂_ratMul.comp Computable.snd Computable.snd
  have h : Computable (fun p : ℕ × ℚ => (1 : ℚ) + p.2 * p.2) :=
    computable₂_ratAdd.comp (Computable.const 1) hsq
  exact h.of_eq fun p => by simp [sq]

/-- **Packing for the square gain.**  In the setting of `GainFamily.packing`, the blocks
weighted by `1 + r t ^ 2` fit into `a s + b s`: the unit parts telescope to `w (s + 1) ≤ a s`,
and since `r t ≤ b s / (a t + b s)` the squared parts are bounded by `b s` through
`sum_squared_error_blocks_le` (they vanish when `b s = 0`). -/
theorem squareGain_packing (s : ℕ) (a b w : ℕ → ℝ) (r : ℕ → ℚ)
    (_ha : Monotone a) (hb : Monotone b) (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t)
    (hw : Monotone w) (hw0 : w 0 = 0) (hwa : ∀ t ≤ s, w (t + 1) ≤ a t)
    (hr : ∀ t ≤ s, (r t : ℝ) = ratioOf (a t) (b t)) :
    ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (squareGain t (r t) : ℝ) ≤ a s + b s := by
  have hsplit : ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (squareGain t (r t) : ℝ) =
      ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) +
        ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (r t : ℝ) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast [squareGain_apply]
    ring
  have htel : ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) = w (s + 1) := by
    rw [Finset.sum_range_sub, hw0, sub_zero]
  have herr : ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (r t : ℝ) ^ 2 ≤ b s := by
    rcases (hb0 s).eq_or_lt with hbs | hbs
    · rw [← hbs]
      refine le_of_eq (Finset.sum_eq_zero fun t ht => ?_)
      have hts : t ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      have hbt : b t = 0 := le_antisymm (by rw [hbs]; exact hb hts) (hb0 t)
      simp [hr t hts, hbt, ratioOf]
    · calc ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (r t : ℝ) ^ 2
          ≤ ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (b s / (a t + b s)) ^ 2 := by
            refine Finset.sum_le_sum fun t ht => ?_
            have hts : t ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
            refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (hw (Nat.le_succ t)))
            rw [hr t hts]
            exact pow_le_pow_left₀ (ratioOf_nonneg (ha0 t) (hb0 t))
              (ratioOf_le_ratioOf (ha0 t) (hb0 t) (hb hts)) 2
        _ ≤ b s := sum_squared_error_blocks_le hbs hw hw0
            (fun i hi => hwa i (Nat.lt_succ_iff.mp hi))
  rw [hsplit, htel]
  linarith [hwa s le_rfl]

/-- The square gains along rational errors converging to `e` eventually exceed every value
below `1 + e ^ 2`, by continuity of `x ↦ 1 + x ^ 2`. -/
theorem squareGain_target_liminf (e : ℝ) (es : ℕ → ℚ)
    (hes : Tendsto (fun s => (es s : ℝ)) atTop (𝓝 e)) (c : ℝ) (hc : c < 1 + e ^ 2) :
    ∀ᶠ s in atTop, c < (squareGain s (es s) : ℝ) := by
  have hlim : Tendsto (fun s => (squareGain s (es s) : ℝ)) atTop (𝓝 (1 + e ^ 2)) := by
    have h : Tendsto (fun s => 1 + (es s : ℝ) ^ 2) atTop (𝓝 (1 + e ^ 2)) :=
      tendsto_const_nhds.add (hes.pow 2)
    refine h.congr fun s => ?_
    push_cast [squareGain_apply]
    rfl
  exact hlim.eventually (lt_mem_nhds hc)

/-- The logarithmic estimate of the square gain: `log 2 · e ^ 2 ≤ log (1 + e ^ 2)` on
`[0, 1]`. -/
theorem squareGain_log_target (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    Real.log 2 * e ^ (2 : ℝ) ≤ Real.log (1 + e ^ 2) := by
  rw [Real.rpow_two, mul_comm]
  exact mul_log_two_le_log_one_add (sq_nonneg e) (pow_le_one₀ he0 he1)

/-- The **square gain family**: gain `1 + r ^ 2`, limit multiplier `1 + e ^ 2`, logarithmic
constant `log 2` and exponent `2`. -/
noncomputable def squareGainFamily : GainFamily where
  gain := squareGain
  one_le := one_le_squareGain
  computable := computable₂_squareGain
  packing := squareGain_packing
  target := fun e => 1 + e ^ 2
  one_le_target := fun e _ _ => le_add_of_nonneg_right (sq_nonneg e)
  target_liminf := fun e _ _ => squareGain_target_liminf e
  kappa := Real.log 2
  beta := 2
  kappa_pos := Real.log_pos one_lt_two
  log_target := squareGain_log_target

/-- The gain of the square family. -/
@[simp] theorem squareGainFamily_gain : squareGainFamily.gain = squareGain := rfl

/-- The limit multiplier of the square family. -/
@[simp] theorem squareGainFamily_target : squareGainFamily.target = fun e => 1 + e ^ 2 := rfl

/-- The logarithmic constant of the square family is `log 2`. -/
@[simp] theorem squareGainFamily_kappa : squareGainFamily.kappa = Real.log 2 := rfl

/-- The exponent of the square family is `2`. -/
@[simp] theorem squareGainFamily_beta : squareGainFamily.beta = 2 := rfl

end Kolmogorov.SelectedBits
