import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerMinimalWitness

/-!
# The length-uniform model as a stochasticity witness, and what minimality forces

The corner research direction isolated in `BudgetedCornerMinimalWitness.lean` may be
assumed to concern a Pareto-minimal stochasticity witness.  This module extracts
a concrete structural consequence of that minimality, using the cheapest model
available for an arbitrary string: the uniform distribution on the cube
`{0,1}^{l(x)}`, whose complexity is `O(log l(x))`.

* `deficiencyLe_codedLengthUniform_of_length_le` — the randomness deficiency of
  `x` in the length-uniform model is at most `beta` as soon as
  `l(x) ≤ K(x | cube) + beta`.  This is the additive reading of the
  multiplicative deficiency definition, since the cube gives every string of
  length `l(x)` mass `2 ^ (-l(x))`.
* `isStochastic_lengthUniform_of_length_le` — consequently every such `x` is
  `(2·l(bits l(x)) + c, beta)`-stochastic.
* `cube_conditional_complexity_lt_of_minimal_alpha` — hence, whenever the
  complexity coordinate `alpha` of a witness is minimal and exceeds the
  logarithmic cube cost, the string must satisfy
  `K(x | cube) + beta < l(x)`: it is compressible given its own length by at
  least `beta` bits.

In the open regime of the plain corner the deficiency parameter is
superpolynomial in `C(x)`, so the last item says that any remaining
counterexample would have to be *massively* compressible given its length.
Nothing here assumes an open statement.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Additive form of the deficiency bound for the length-uniform model.**  The
cube `{0,1}^n` assigns `x` the mass `2 ^ (-n)`, so the multiplicative deficiency
inequality `2 ^ (-K(x | cube)) ≤ 2 ^ beta · 2 ^ (-n)` is exactly the additive
bound `n ≤ K(x | cube) + beta`. -/
theorem deficiencyLe_codedLengthUniform_of_length_le
    (U : Map) (x : BitString) (n beta : ℕ) (hx : x.length = n)
    (h : (n : ENat) ≤ KP U x (codedLengthUniform n).code + (beta : ENat)) :
    DeficiencyLe U (codedLengthUniform n) x beta := by
  have hkey : (2 : ℝ≥0∞)⁻¹ ^ beta * complexityWeight (KP U x (codedLengthUniform n).code)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    have h1 := complexityWeight_le_of_le h
    rw [complexityWeight_add_nat, complexityWeight_coe] at h1
    rw [mul_comm]
    exact h1
  have hne0 : ((2 : ℝ≥0∞) ^ beta) ≠ 0 := pow_ne_zero beta two_ne_zero
  have hnetop : ((2 : ℝ≥0∞) ^ beta) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hcancel : (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ beta = 1 := by
    rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel hne0 hnetop]
  unfold DeficiencyLe CodedFiniteDistribution.DeficiencyLe
  rw [codedLengthUniform_mass_of_mem n x hx]
  calc complexityWeight (KP U x (codedLengthUniform n).code)
      = (2 : ℝ≥0∞) ^ beta *
          ((2 : ℝ≥0∞)⁻¹ ^ beta * complexityWeight (KP U x (codedLengthUniform n).code)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ beta * (2 : ℝ≥0∞)⁻¹ ^ n := by gcongr

/-- **The cube witnesses stochasticity at logarithmic complexity.**  If `x` is
compressible given the cube at its own length by no more than `beta` bits below
that length, then `x` is `(2·l(bits l(x)) + c, beta)`-stochastic. -/
theorem isStochastic_lengthUniform_of_length_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (beta : ℕ),
      (x.length : ENat) ≤ KP U x (codedLengthUniform x.length).code + (beta : ENat) →
      IsStochastic U x (2 * (Nat.bits x.length).length + c) beta := by
  obtain ⟨c, hc⟩ := isStochastic_lengthUniform_log U hU
  refine ⟨c, fun x beta h => ?_⟩
  exact hc x beta (deficiencyLe_codedLengthUniform_of_length_le U x x.length beta rfl h)

/-- **What minimality of the complexity coordinate forces.**  If no complexity
level strictly below `alpha` admits a model of deficiency at most `beta`, and
`alpha` exceeds the logarithmic cost of the cube at the length of `x`, then the
cube itself must fail to be a `beta`-fitting model, i.e.

```text
K(x | cube at l(x)) + beta < l(x).
```

So a Pareto-minimal witness with a non-logarithmic complexity coordinate forces
`x` to be compressible given its length by more than `beta` bits. -/
theorem cube_conditional_complexity_lt_of_minimal_alpha
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (alpha beta : ℕ),
      (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
      2 * (Nat.bits x.length).length + c < alpha →
      KP U x (codedLengthUniform x.length).code + (beta : ENat) < (x.length : ENat) := by
  obtain ⟨c, hc⟩ := isStochastic_lengthUniform_of_length_le U hU
  refine ⟨c, fun x alpha beta hamin hlog => ?_⟩
  by_contra hle
  push_neg at hle
  exact hamin (2 * (Nat.bits x.length).length + c) hlog (hc x beta hle)

/-- **The open regime of the plain corner may assume massive compressibility.**
A further sharpening of `budgetedPlainCorner_of_hard_regime_superpoly_minimal`:
for the fixed cube constant supplied by
`cube_conditional_complexity_lt_of_minimal_alpha`, the remaining regime may in
addition be assumed to satisfy

```text
alpha ≤ 2·l(bits l(x)) + cCube   or   K(x | cube at l(x)) + beta < l(x).
```

Since the deficiency parameter is superpolynomial in `C(x)` in that regime, the
second alternative says that a remaining counterexample would have to be
compressible given its own length by more than `beta` bits, while the first
confines its model complexity to `O(log l(x))`.

The disjunction is *not* an extra assumption: it is derived from the minimality
of the complexity coordinate of the witness. -/
theorem budgetedPlainCorner_of_hard_regime_superpoly_minimal_compressible
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (k : ℕ)
    (hHard : ∀ cCube : ℕ, ∃ c : ℕ, ∀ (x : BitString) (kx baseBudget alpha beta : ℕ),
      plainK V x = (kx : ENat) →
      kx ≤ baseBudget →
      alpha < kx →
      baseBudget ^ k < beta →
      baseBudget ^ k < x.length →
      (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha →
        beta < x.length ∧ kx + beta < x.length + m) →
      IsStochastic U x alpha beta →
      (∀ b : ℕ, b < beta → ¬ IsStochastic U x alpha b) →
      (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
      (alpha ≤ 2 * (Nat.bits x.length).length + cCube ∨
        KP U x (codedLengthUniform x.length).code + (beta : ENat) < (x.length : ENat)) →
      ∃ i j,
        InPlainDescriptionProfile V x i j ∧
        i ≤ alpha + logSlack c baseBudget ∧
        i + j ≤ kx + beta + logSlack c baseBudget) :
    BudgetedPlainProfileCornerStatement V U := by
  obtain ⟨cCube, hCube⟩ := cube_conditional_complexity_lt_of_minimal_alpha U hU
  obtain ⟨c, hc⟩ := hHard cCube
  refine budgetedPlainCorner_of_hard_regime_superpoly_minimal V U hV hU k ⟨c, ?_⟩
  intro x kx baseBudget alpha beta hkx hkxB hka hbeta hlen hnotsimple hstoch hbmin hamin
  refine hc x kx baseBudget alpha beta hkx hkxB hka hbeta hlen hnotsimple hstoch hbmin hamin ?_
  by_cases hlog : alpha ≤ 2 * (Nat.bits x.length).length + cCube
  · exact Or.inl hlog
  · exact Or.inr (hCube x alpha beta hamin (by omega))

end Kolmogorov
