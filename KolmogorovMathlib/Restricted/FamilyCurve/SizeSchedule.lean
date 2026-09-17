import Mathlib.Data.List.Basic

/-!
# Size schedules of powers of two

The effective runs of `Restricted/FamilyCurve` are driven by a *size schedule*: a list
`sizes` of cardinality bounds, one per stage, whose entries are the powers `2 ^ t s` of a
sequence of exponents `t`.  Two conditions on such a schedule occur again and again — that
its entries really are those powers up to the last stage `N`, and that the exponents decrease
along the run — so they are named here, in the lowest module that can state them.

The shifted schedules of the anchored run (whose stage `s` carries the exponent `t (s + 1)`,
stage `0` being the ambient cube) are the same predicate at the shifted exponent sequence
`fun s => t (s + 1)`.
-/

namespace Kolmogorov

/-- The list `sizes` is the schedule of the powers `2 ^ t s`: its entry at every stage
`s ≤ N` is `2 ^ t s` (missing entries read as `0`). -/
def IsPowerSizeSchedule (sizes : List ℕ) (N : ℕ) (t : ℕ → ℕ) : Prop :=
  ∀ s ≤ N, sizes.getD s 0 = 2 ^ t s

/-- The exponent sequence `t` does not increase at any step below `N`. -/
def ExponentsAntitone (t : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ s < N, t (s + 1) ≤ t s

end Kolmogorov
