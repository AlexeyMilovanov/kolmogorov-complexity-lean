/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Prefix.Symmetry

/-!
# Algorithmic Statistics: Basic Glue and Helpers

This module provides basic notation and helper lemmas for the algorithmic
statistics formalization, based on Vereshchagin and Shen, "Algorithmic statistics:
forty years later".

It builds on the existing prefix complexity infrastructure and introduces
easy lemmas about `complexityWeight` and `ENNReal` arithmetic to support
multiplicative deficiency bounds.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Complexity Weight Helpers -/

/-- The complexity weight `2^{-KP(x | y)}` is bounded by 1. -/
theorem complexityWeight_KP_le_one (U : Map) (x y : BitString) :
    complexityWeight (KP U x y) ≤ 1 :=
  complexityWeight_le_one (KP U x y)

/-- The complexity weight `2^{-KPPlain(x)}` is bounded by 1. -/
theorem complexityWeight_KPPlain_le_one (U : Map) (x : BitString) :
    complexityWeight (KPPlain U x) ≤ 1 :=
  complexityWeight_le_one (KPPlain U x)

/-! ### ENNReal Power and Monotonicity Helpers -/

/-- `2^n` is monotonic in `n`. -/
theorem pow_two_mono {n m : ℕ} (h : n ≤ m) :
    (2 : ℝ≥0∞) ^ n ≤ (2 : ℝ≥0∞) ^ m := by
  exact pow_le_pow_right₀ one_le_two h

/-- `2^0 = 1` for `ENNReal`. -/
@[simp] theorem pow_two_zero : (2 : ℝ≥0∞) ^ 0 = 1 :=
  pow_zero _

/-- Multiplication by zero. -/
@[simp] theorem ENNReal_pow_two_mul_zero (beta : ℕ) :
    ((2 : ℝ≥0∞) ^ beta) * 0 = 0 :=
  mul_zero _

/-- Multiplication by one. -/
@[simp] theorem ENNReal_pow_two_mul_one (beta : ℕ) :
    ((2 : ℝ≥0∞) ^ beta) * 1 = (2 : ℝ≥0∞) ^ beta :=
  mul_one _

end Kolmogorov
