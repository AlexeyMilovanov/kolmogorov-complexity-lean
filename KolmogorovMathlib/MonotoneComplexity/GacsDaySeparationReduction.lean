import KolmogorovMathlib.MonotoneComplexity.GacsDayGame

/-!
# Reducing the Day separation statement to its quantitative half

`GacsDaySeparationStatement D` is a conjunction:

* the *qualitative* half: the gap `KM_D(x) - KA(x)` is unbounded;
* the *quantitative* half: for infinitely many lengths `n` there is an `n`-bit string with
  `KM_D(x) ≥ KA(x) + log log n - c · log log log n`.

The qualitative half is a formal consequence of the quantitative one, because
`u - c · log₂ u → ∞`.  This file proves that implication, so that a construction only has to
supply the quantitative half.
-/

namespace Kolmogorov

open Filter Real Asymptotics

/-- For every real `c`, the function `u ↦ u - c * log₂ u` tends to `+∞`. -/
lemma tendsto_sub_const_mul_logb_atTop (c : ℝ) :
    Tendsto (fun u : ℝ => u - c * Real.logb 2 u) atTop atTop := by
  have hlittle : (fun u : ℝ => (c / Real.log 2) * Real.log u) =o[atTop] fun u : ℝ => u := by
    simpa using Real.isLittleO_log_id_atTop.const_mul_left (c / Real.log 2)
  have hbound := hlittle.def (c := (1 / 2 : ℝ)) (by norm_num)
  have hev : ∀ᶠ u : ℝ in atTop, u / 2 ≤ u - c * Real.logb 2 u := by
    filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with u hu hu0
    have habs : |(c / Real.log 2) * Real.log u| ≤ (1 / 2) * u := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0] at hu
      exact hu
    have hle : (c / Real.log 2) * Real.log u ≤ (1 / 2) * u :=
      le_trans (le_abs_self _) habs
    have hlogb : c * Real.logb 2 u = (c / Real.log 2) * Real.log u := by
      rw [Real.logb]
      ring
    rw [hlogb]
    linarith
  exact tendsto_atTop_mono' atTop hev (tendsto_id.atTop_div_const (by norm_num))

/-- The Day gap bound `log₂ log₂ n - c · log₂ log₂ log₂ n` tends to `+∞`. -/
lemma tendsto_dayGapBound_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => Real.logb 2 (Real.logb 2 n)
      - c * Real.logb 2 (Real.logb 2 (Real.logb 2 n))) atTop atTop := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have h1 : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop hb).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.logb 2 (Real.logb 2 n)) atTop atTop :=
    (Real.tendsto_logb_atTop hb).comp h1
  exact (tendsto_sub_const_mul_logb_atTop c).comp h2

/-- **The quantitative half of Day's separation implies the qualitative half.**
If for infinitely many lengths some string realises the `log log` gap, then `KM_D - KA` is
unbounded, so the full `GacsDaySeparationStatement D` follows. -/
theorem gacsDaySeparationStatement_of_quantitative
    (D : BitStream → BitStream)
    (h : ∃ c : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ x : BitString, x.length = n ∧
      KA x + Real.logb 2 (Real.logb 2 n) - c * Real.logb 2 (Real.logb 2 (Real.logb 2 n))
        ≤ ((KMOf D x).toNat : ℝ)) :
    GacsDaySeparationStatement D := by
  obtain ⟨c, hc⟩ := h
  refine ⟨?_, ⟨c, hc⟩⟩
  rintro ⟨c', hc'⟩
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 ((tendsto_dayGapBound_atTop c).eventually_gt_atTop c')
  obtain ⟨n, hn, x, _hlen, hx⟩ := hc N
  have h1 := hc' x
  have h2 := hN n hn
  linarith

end Kolmogorov
