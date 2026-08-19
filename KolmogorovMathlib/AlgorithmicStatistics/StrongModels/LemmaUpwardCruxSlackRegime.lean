import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaUpwardCruxReduction

/-!
# Sharpening the boundary regimes of the upward crux

`lemmaUpwardCrux_of_hardRegime` (`LemmaUpwardCruxReduction.lean`) discharges the
boundary regimes `K(x) ≤ alpha` (canonical singleton) and
`l(x) + m ≤ K(x) + beta` for some bound `m ≤ alpha` on `K(l(x))` (full cube).
Both boundaries are in fact available with a *logarithmic margin*: the singleton
model only has to fit into `alpha + logSlack c K(x)` and the cube model only has
to have complexity `m + O(1)` with `m ≤ alpha + logSlack w K(x)`, because the
conclusion of the crux itself carries the slack `logSlack c K(x)`.

This module records that sharpening.  For *every* constant `w`, the open regime
may be narrowed to

```text
alpha + logSlack w K(x) < K(x),
K(x) ^ k < beta,
K(x) + beta < l(x) + m  for every bound m ≤ alpha + logSlack w K(x) on K(l(x)),
```

which is a strictly stronger set of restrictions than the ones in
`LemmaUpwardCruxHardRegimeStatement`.  Nothing is assumed: the hard-regime
statement only ever appears as a hypothesis.
-/

namespace Kolmogorov

/-- **The hard regime of the upward crux, with logarithmic boundary margins.**
Same as `LemmaUpwardCruxHardRegimeStatement`, except that the singleton boundary
and the simple-length boundary are both pushed outwards by `logSlack w K(x)`:
the conversion is required only when

* `alpha + logSlack w K(x) < K(x)` (the singleton model is out of budget even
  after spending the logarithmic slack);
* `K(x) ^ k < beta`;
* `K(x) + beta < l(x) + m` for every bound `m ≤ alpha + logSlack w K(x)` on
  `K(l(x))` (the full cube is out of budget even after spending the logarithmic
  slack);
* the stochasticity witness is Pareto-minimal in both coordinates. -/
def LemmaUpwardCruxHardRegimeSlackStatement (U : Map) (k w : ℕ) : Prop :=
  ∃ c : ℕ, ∀ (x : BitString) (p alpha beta : ℕ),
    KPPlain U x = (p : ENat) →
    alpha + logSlack w p < p →
    p ^ k < beta →
    (∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) → m ≤ alpha + logSlack w p →
      p + beta < x.length + m) →
    IsStochastic U x alpha beta →
    (∀ b : ℕ, b < beta → ¬ IsStochastic U x alpha b) →
    (∀ a : ℕ, a < alpha → ¬ IsStochastic U x a beta) →
    IsOptimalSetStochastic U x
      (alpha + logSlack c p) (beta + logSlack c p)

/-- **The upward crux is open only in its logarithmically narrowed hard regime.**
For every exponent `k` *and every margin constant `w`*, the full
`alpha, beta`-independent optimal-set conversion follows from its restriction to
Pareto-minimal witnesses with

```text
alpha + logSlack w K(x) < K(x),   K(x) ^ k < beta,
K(x) + beta < l(x) + m for every bound m ≤ alpha + logSlack w K(x) on K(l(x)).
```

The two boundary regimes are discharged exactly as in
`lemmaUpwardCrux_of_hardRegime`, but now with the additional `logSlack w K(x)`
of room, which the conclusion's own slack absorbs
(`logSlack_add_const_le`). -/
theorem lemmaUpwardCrux_of_hardRegime_slack
    (U : Map) (hU : IsOptimalPrefixConditional U) (k w : ℕ)
    (hHard : LemmaUpwardCruxHardRegimeSlackStatement U k w) :
    LemmaUpwardCruxStatement U := by
  classical
  obtain ⟨c1, h1⟩ := isOptimalSetStochastic_singleton_of_KPPlain U hU
  obtain ⟨cCube, hCube⟩ := isOptimalSetStochastic_fullCube_of_simple_length U hU
  obtain ⟨c0, h0⟩ := stochasticity_to_optimal_set_budget U hU
  obtain ⟨C, hC⟩ := logSlack_linear_bound c0 3 0
  obtain ⟨C2, hC2⟩ := logSlack_le_of_le_pow C (k + 1)
  obtain ⟨cH, hH⟩ := hHard
  refine ⟨w + c1 + cCube + C2 + cH, fun x p alpha beta hp hst => ?_⟩
  set c := w + c1 + cCube + C2 + cH with hcdef
  have hcs : c ≤ logSlack c p := by unfold logSlack; omega
  -- the three foldings of a constant, resp. a `logSlack w p`, into `logSlack c p`
  have hfoldH : logSlack cH p ≤ logSlack c p := logSlack_mono_left (by omega) p
  have hfoldC2 : logSlack C2 p ≤ logSlack c p := logSlack_mono_left (by omega) p
  have hfold1 : logSlack w p + c1 ≤ logSlack c p :=
    (logSlack_add_const_le w c1 p).trans (logSlack_mono_left (by omega) p)
  have hfoldCube : logSlack w p + cCube ≤ logSlack c p :=
    (logSlack_add_const_le w cCube p).trans (logSlack_mono_left (by omega) p)
  obtain ⟨a, b, hale, hble, hstab, hbmin, hamin⟩ :=
    exists_pareto_minimal_stochastic_witness U x alpha beta hst
  rcases Nat.lt_or_ge (a + logSlack w p) p with hpa | hpa
  · rcases Nat.lt_or_ge (p ^ k) b with hbp | hbp
    · by_cases hlen : ∀ m : ℕ, KPPlain U (natCode x.length) ≤ (m : ENat) →
          m ≤ a + logSlack w p → p + b < x.length + m
      · -- the genuinely open regime
        exact ((hH x p a b hp hpa hbp hlen hstab hbmin hamin).mono_alpha
          (by omega)).mono_beta (by omega)
      · -- simple-length regime, now with a logarithmic margin on the cube budget
        push Not at hlen
        obtain ⟨m, hm, hma, hmlen⟩ := hlen
        have hsum : x.length + m + cCube ≤ p + (beta + logSlack c p) := by omega
        exact (hCube x p m (beta + logSlack c p) hp hm hsum).mono_alpha (by omega)
    · -- polynomial-`beta` regime: the proved conversion folds into a single `logSlack C2 p`
      have hp1 : 1 ≤ p := by omega
      have hmax : max p b ≤ p ^ (k + 1) := by
        refine max_le (Nat.le_self_pow (by omega) p) (le_trans hbp ?_)
        exact Nat.pow_le_pow_right hp1 (Nat.le_succ k)
      have hfold : logSlack c0 (p + a + b) ≤ logSlack c p := by
        have h3 : logSlack c0 (p + a + b) ≤ logSlack c0 (3 * max p b + 0) := by
          refine logSlack_mono_right c0 ?_
          have hh1 : p ≤ max p b := le_max_left _ _
          have hh2 : b ≤ max p b := le_max_right _ _
          omega
        have hCp : logSlack c0 (3 * max p b + 0) ≤ logSlack C (max p b) := hC (max p b)
        have hC2p : logSlack C (max p b) ≤ logSlack C2 p := hC2 p (max p b) hmax
        omega
      exact ((h0 x p a b hp hstab).mono_alpha (by omega)).mono_beta (by omega)
  · -- singleton regime, now with a logarithmic margin on the singleton budget
    have hbeta : c1 ≤ beta + logSlack c p := by omega
    exact (h1 x p (beta + logSlack c p) hp hbeta).mono_alpha (by omega)

/-- **The narrowed regime really is a sub-regime.**  Every instance of the
slack-margin hard regime is an instance of the original hard regime
(`LemmaUpwardCruxHardRegimeStatement`): the margin only shrinks the set of
tuples on which the conversion is demanded, so
`lemmaUpwardCrux_of_hardRegime_slack` is a strictly stronger reduction than
`lemmaUpwardCrux_of_hardRegime`. -/
theorem lemmaUpwardCruxHardRegimeSlackStatement_of_hardRegimeStatement
    (U : Map) (k w : ℕ) (h : LemmaUpwardCruxHardRegimeStatement U k) :
    LemmaUpwardCruxHardRegimeSlackStatement U k w := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x p alpha beta hp hpa hbp hlen hst hbmin hamin => ?_⟩
  refine hc x p alpha beta hp (by omega) hbp (fun m hm hma => ?_) hst hbmin hamin
  exact hlen m hm (by omega)

/-- **`prop:upward` from the logarithmically narrowed hard-regime crux.**
Composes `lemmaUpwardCrux_of_hardRegime_slack` with
`propUpward_of_optimalSetConversion_budget`: for every exponent `k` and every
margin constant `w`, the whole remaining distance to an unconditional
`prop:upward` is the optimal-set conversion for Pareto-minimal witnesses in the
single regime `alpha + logSlack w K(x) < K(x)`, `K(x) ^ k < beta`,
non-simple length with a logarithmic margin. -/
theorem propUpward_of_hardRegimeCrux_slack
    (V U T : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) (k w : ℕ)
    (hHard : LemmaUpwardCruxHardRegimeSlackStatement U k w) :
    PropUpwardStatement U T :=
  propUpward_of_optimalSetConversion_budget V U T hV hU hT
    (lemmaUpwardCrux_of_hardRegime_slack U hU k w hHard)

end Kolmogorov
