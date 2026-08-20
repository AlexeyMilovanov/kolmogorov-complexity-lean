import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Monotonicity of the charged noise radius

The strong-model noise-transport statements all carry a *charged radius* of the
shape `c * epsilon + logSlack c n`, added to both the model-complexity budget
`alpha` and the deficiency budget `beta`.  When several regimes are combined,
each supplies its own constant `c'` and the disjunction has to be re-expressed
with a single common constant `c`.

This file isolates that bookkeeping: the radius is monotone in its constant
(`logSlack_radius_mono`), and stochasticity at a smaller radius lifts to
stochasticity at a larger one (`isStochastic_radius_mono`).
-/

namespace Kolmogorov

/-- The charged radius `c * epsilon + logSlack c n` is monotone in the
constant `c`. -/
theorem logSlack_radius_mono {c c' : ℕ} (h : c' ≤ c) (epsilon n : ℕ) :
    c' * epsilon + logSlack c' n ≤ c * epsilon + logSlack c n :=
  Nat.add_le_add (Nat.mul_le_mul_right _ h) (logSlack_mono_left h n)

/-- Stochasticity with budgets widened by the charged radius of a smaller
constant lifts to the charged radius of a larger constant. -/
theorem isStochastic_radius_mono {U : Map} {x : BitString} {alpha beta c c' : ℕ}
    (h : c' ≤ c) (epsilon n : ℕ)
    (hs : IsStochastic U x (alpha + (c' * epsilon + logSlack c' n))
      (beta + (c' * epsilon + logSlack c' n))) :
    IsStochastic U x (alpha + (c * epsilon + logSlack c n))
      (beta + (c * epsilon + logSlack c n)) :=
  isStochastic_mono (Nat.add_le_add_left (logSlack_radius_mono h epsilon n) alpha)
    (Nat.add_le_add_left (logSlack_radius_mono h epsilon n) beta) hs

end Kolmogorov
