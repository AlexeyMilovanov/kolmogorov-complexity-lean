import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable

/-!
# Gain families for selected-bit prediction

The antichain-packing argument for selected bits multiplies the mass of a word by a *gain* at
each forced position on its path.  The gain at stage `s` depends on the current sibling ratio
`r = b / (a + b)`, where `a` is the stage mass of the valid child and `b` the stage mass of the
forbidden child.  This module fixes the abstract interface that the numerical core and the
effective construction need from such a gain, and two small helpers.

* `ratioOf a b = b / (a + b)`: the real sibling ratio, `0` when `a + b = 0`.
* `natRatio nv nw = nw / (nv + nw)`: the same ratio on natural numerators, as a computable
  rational function (`computable₂_natRatio`), with `cast_natRatio` relating the two.
* `GainFamily`: a stage-dependent rational gain `gain s r ≥ 1`, computable in `(s, r)`, with
  the scalar *packing* inequality (the mass-weighted gains of consecutive blocks below the
  valid mass fit into `a s + b s`), a limit multiplier `target` reached in the lower-limit sense
  (`target_liminf`), and the logarithmic estimate `kappa * e ^ beta ≤ log (target e)`.
* `mul_log_two_le_log_one_add`: `x log 2 ≤ log (1 + x)` on `[0, 1]`, shared by the two
  instances (`Gain/Square`, `Gain/Staircase`).

The gains are rational so that they can enter the enumerator of the demands; all analysis of
the packing inequality and of the limits is carried out in `ℝ`.
-/

namespace Kolmogorov.SelectedBits

open Filter Topology

/-! ### Sibling ratios -/

/-- The real sibling ratio `b / (a + b)`: the share of the second mass `b` in the total.  Real
division makes it `0` when `a + b = 0`. -/
noncomputable def ratioOf (a b : ℝ) : ℝ := b / (a + b)

/-- The sibling ratio of two nonnegative masses is nonnegative. -/
theorem ratioOf_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ratioOf a b :=
  div_nonneg hb (add_nonneg ha hb)

/-- The sibling ratio of two nonnegative masses is at most `1`. -/
theorem ratioOf_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ratioOf a b ≤ 1 :=
  div_le_one_of_le₀ (le_add_of_nonneg_left ha) (add_nonneg ha hb)

/-- The sibling ratio is monotone in the second mass. -/
theorem ratioOf_le_ratioOf {a b b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hbb : b ≤ b') :
    ratioOf a b ≤ ratioOf a b' := by
  unfold ratioOf
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact div_nonneg (hb.trans hbb) (add_nonneg ha (hb.trans hbb))
  · have h' : 0 < a + b' := by linarith
    rw [div_le_div_iff₀ h h']
    nlinarith

/-- The sibling ratio `nw / (nv + nw)` of two natural numerators, as a rational number; it is
`0` when both numerators vanish. -/
def natRatio (nv nw : ℕ) : ℚ := (nw : ℚ) / ((nv : ℚ) + nw)

/-- The rational ratio of numerators is the real sibling ratio of their casts. -/
theorem cast_natRatio (nv nw : ℕ) :
    ((natRatio nv nw : ℚ) : ℝ) = ratioOf (nv : ℝ) (nw : ℝ) := by
  simp [natRatio, ratioOf]

/-- The ratio of numerators is computable. -/
theorem computable₂_natRatio : Computable₂ natRatio := by
  refine computable_of_num_den (f := fun p : ℕ × ℕ => natRatio p.1 p.2)
    (N := fun p : ℕ × ℕ => (p.2 : ℤ)) (D := fun p : ℕ × ℕ => max 1 (p.1 + p.2))
    (ComputableReals.primrec_natCastInt.to_comp.comp Computable.snd)
    (Primrec.nat_max.comp (Primrec.const 1)
      (Primrec.nat_add.comp Primrec.fst Primrec.snd)).to_comp
    (fun p => lt_max_of_lt_left one_pos) (fun p => ?_)
  rcases Nat.eq_zero_or_pos (p.1 + p.2) with h | h
  · have h2 : p.2 = 0 := by omega
    simp [natRatio, h2]
  · rw [max_eq_right h]
    simp [natRatio]

/-! ### Gain families -/

/-- A **gain family**: a rational gain `gain s r ≥ 1` at stage `s` and sibling ratio `r`,
computable in `(s, r)`, together with

* `packing`: for nondecreasing nonnegative masses `a`, `b` and a nondecreasing cumulative mass
  `w` with `w 0 = 0` whose blocks end below the valid mass (`w (t + 1) ≤ a t`), the blocks
  weighted by the gain at the current ratio `r t = ratioOf (a t) (b t)` fit into `a s + b s`;
* `target`: the limit multiplier of a final error `e ∈ [0, 1]`, at least `1`, reached by the
  gains along every rational sequence of errors converging to `e` in the lower-limit sense
  `target_liminf`;
* `log_target`: the logarithmic estimate `kappa * e ^ beta ≤ log (target e)` on `[0, 1]`.

The ratios enter as a rational sequence `r` together with the hypothesis identifying their real
casts with `ratioOf (a t) (b t)`, since the gain itself is rational. -/
structure GainFamily where
  /-- The rational gain at stage `s` and sibling ratio `r`. -/
  gain : ℕ → ℚ → ℚ
  /-- Every gain is at least `1`. -/
  one_le : ∀ s r, 1 ≤ gain s r
  /-- The gain is computable in the stage and the ratio. -/
  computable : Computable₂ gain
  /-- The scalar packing inequality. -/
  packing : ∀ (s : ℕ) (a b w : ℕ → ℝ) (r : ℕ → ℚ),
    Monotone a → Monotone b → (∀ t, 0 ≤ a t) → (∀ t, 0 ≤ b t) → Monotone w → w 0 = 0 →
    (∀ t ≤ s, w (t + 1) ≤ a t) → (∀ t ≤ s, (r t : ℝ) = ratioOf (a t) (b t)) →
    ∑ t ∈ Finset.range (s + 1), (w (t + 1) - w t) * (gain t (r t) : ℝ) ≤ a s + b s
  /-- The limit multiplier of a final error. -/
  target : ℝ → ℝ
  /-- The limit multiplier of an error in `[0, 1]` is at least `1`. -/
  one_le_target : ∀ e, 0 ≤ e → e ≤ 1 → 1 ≤ target e
  /-- Along rational errors converging to `e ∈ [0, 1]` the gains eventually exceed every value
  below `target e`. -/
  target_liminf : ∀ e : ℝ, 0 ≤ e → e ≤ 1 → ∀ es : ℕ → ℚ,
    Tendsto (fun s => (es s : ℝ)) atTop (𝓝 e) →
    ∀ c, c < target e → ∀ᶠ s in atTop, c < (gain s (es s) : ℝ)
  /-- The constant of the logarithmic estimate. -/
  kappa : ℝ
  /-- The exponent of the logarithmic estimate. -/
  beta : ℝ
  /-- The constant of the logarithmic estimate is positive. -/
  kappa_pos : 0 < kappa
  /-- The logarithmic estimate of the limit multiplier. -/
  log_target : ∀ e, 0 ≤ e → e ≤ 1 → kappa * e ^ beta ≤ Real.log (target e)

namespace GainFamily

variable (G : GainFamily)

/-- Every gain is positive. -/
theorem gain_pos (s : ℕ) (r : ℚ) : 0 < G.gain s r :=
  lt_of_lt_of_le one_pos (G.one_le s r)

/-- Every gain is nonnegative. -/
theorem gain_nonneg (s : ℕ) (r : ℚ) : 0 ≤ G.gain s r :=
  (G.gain_pos s r).le

/-- The real cast of every gain is at least `1`. -/
theorem one_le_gain_cast (s : ℕ) (r : ℚ) : (1 : ℝ) ≤ (G.gain s r : ℝ) := by
  exact_mod_cast G.one_le s r

/-- The real cast of every gain is positive. -/
theorem gain_cast_pos (s : ℕ) (r : ℚ) : (0 : ℝ) < (G.gain s r : ℝ) := by
  exact_mod_cast G.gain_pos s r

/-- The limit multiplier of an error in `[0, 1]` is positive. -/
theorem target_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) : 0 < G.target e :=
  lt_of_lt_of_le one_pos (G.one_le_target e he0 he1)

end GainFamily

/-! ### A logarithmic estimate shared by the instances -/

/-- On `[0, 1]`, `x log 2 ≤ log (1 + x)`: Bernoulli's inequality `2 ^ x ≤ 1 + x` for exponents
in `[0, 1]`, followed by the logarithm. -/
theorem mul_log_two_le_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * Real.log 2 ≤ Real.log (1 + x) := by
  have h : (1 + 1 : ℝ) ^ x ≤ 1 + x * 1 :=
    rpow_one_add_le_one_add_mul_self (by norm_num) hx0 hx1
  have h2 : (0 : ℝ) < 2 ^ x := Real.rpow_pos_of_pos two_pos x
  calc x * Real.log 2 = Real.log ((2 : ℝ) ^ x) := (Real.log_rpow two_pos x).symm
    _ ≤ Real.log (1 + x) := Real.log_le_log h2 (by norm_num at h; linarith)

end Kolmogorov.SelectedBits
