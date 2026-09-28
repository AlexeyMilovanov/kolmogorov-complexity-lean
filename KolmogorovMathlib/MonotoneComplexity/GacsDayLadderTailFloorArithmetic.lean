import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailController

/-!
# Arithmetic of the terminal root floor, and a refuted shortcut

The final adjustment of the tail controller raises every outer root request to
`grayTailTargetFloor q a`.  Section 6.7 of the Gacs-Day tail blueprint
identifies one identity as indispensable for the coupled hereditary estimate,

```text
halfAmplification (q + 1) * grayTailTargetFloor q a = (3 / 4) * dyadicScale a,
```

and this file proves it, together with the two elementary decompositions that
the coupled inequality is built from.

It then settles a question that the blueprint leaves open, and which every
attempt at the coupled inequality is tempted by.  The controller supplies one
signed lower bound *per frozen round*,

```text
kappa * (2 * selectedRequest_r - totalRequest_r) <= grayMass_r ,
```

and `grayTailRound_selected_positivePart` clamps each of them at zero.  Since

```text
∑ r, max 0 z r  ≥  max 0 (∑ r, z r),
```

it is tempting to collapse the whole round family into the single aggregate
positive part and then argue with `Γ = ∑ γ` and one owner charge.  Section 6.6
warns against this in the *unclamped* case; `not_aggregatedGrayTailFloorBound`
below shows that the warning survives clamping: even the **aggregated positive
part** is strictly too weak, at a set of parameters that satisfies every
per-son cap, the threshold rule, the exact source scale `B * eps = alpha`, the
exact floor `(3/4) * alpha / kappa'`, and the one-quarter stopping bound.

The witness has `kappa = 2` (i.e. `q = 2`, the first tail stage), `eps = 1`,
`n = 4` outer roots with `B = 4` source sons each.  Twelve sons carry
`gamma = 15/16`, which is above the raise threshold `eps - eps/(6*kappa) =
11/12`, are resolved, and are charged their maximal owner increment
`y = 1/24 = eps/(12*kappa)`.  The remaining four sons — exactly one quarter of
all sons, so the stopping rule is met with equality — sit under the fourth
root, carry no request and stay unresolved.  Then

```text
aggregated credit  = max 0 (kappa * (45/4 - 2 * 1/2)) = 41/2,
reserve credit     = 12,
target             = (kappa + 1/2) * (3 * 4 + 6/5) = 33,
```

so the aggregated bound asks for `33 ≤ 65/2`, which is false.

The moral is exactly the one the blueprint states for the unclamped sum: the
round-by-round positive parts must be *kept apart*.  In the witness above the
whole owner charge is concentrated in one round, so the honest per-round sum
`∑ r max 0 (…)` loses only the last round rather than the whole owner charge,
and it is comfortably larger than the aggregate.
-/

namespace Kolmogorov

open Finset

/-! ### The floor identity -/

/-- Each stage raises the amplification factor by `1 / 2`. -/
lemma halfAmplification_succ (k : ℕ) :
    halfAmplification (k + 1) = halfAmplification k + 1 / 2 := by
  unfold halfAmplification
  push_cast
  ring

/-- **The indispensable floor identity.**  The next amplification exactly
converts the terminal per-root floor into three quarters of the root scale. -/
theorem halfAmplification_mul_grayTailTargetFloor (q a : ℕ) :
    halfAmplification (q + 1) * grayTailTargetFloor q a =
      (3 / 4 : ℚ) * dyadicScale a := by
  unfold grayTailTargetFloor
  have hk : halfAmplification (q + 1) ≠ 0 := ne_of_gt (halfAmplification_pos _)
  field_simp

/-! ### The two elementary decompositions -/

/-- Splitting the terminal `max` into the pre-floor request and its deficit. -/
lemma mul_max_eq_add_deficit {k s f : ℚ} (hk : 0 ≤ k) :
    k * max s f = k * s + max 0 (k * f - k * s) := by
  rcases le_total s f with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
    ring
  · rw [max_eq_left h, max_eq_left (by nlinarith)]
    ring

/-- The per-son estimate for an unresolved son: its floor share costs at most
three quarters of `eps`, minus half of the request it already carries. -/
lemma unresolved_son_deficit_le {eps g kappa' : ℚ}
    (heps : 0 < eps) (hg : 0 ≤ g) (hge : g ≤ eps) (hk : 1 / 2 ≤ kappa') :
    max 0 ((3 / 4 : ℚ) * eps - kappa' * g) ≤ (3 / 4 : ℚ) * eps - g / 2 := by
  rcases le_total ((3 / 4 : ℚ) * eps) (kappa' * g) with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith
  · rw [max_eq_right (by linarith)]
    nlinarith

/-! ### The aggregated shortcut, and its refutation -/

/-- The tempting "one aggregate positive part" form of the coupled hereditary
estimate at the full family, stated with every feasible-history constraint the
blueprint lists except the per-participating-son lower gain, and with all
frozen rounds collapsed into a single clamped signed term. -/
def AggregatedGrayTailFloorBound : Prop :=
  ∀ (n B : ℕ) (eps kappa : ℚ)
    (gamma y : Fin n → Fin B → ℚ) (res : Fin n → Fin B → Bool),
    1 ≤ n → 1 ≤ B → 0 < eps → 2 ≤ kappa →
    (∀ i c, 0 ≤ gamma i c) →
    (∀ i c, gamma i c ≤ eps) →
    (∀ i c, 0 ≤ y i c) →
    (∀ i c, y i c ≤ gamma i c) →
    (∀ i c, y i c ≤ eps / (12 * kappa)) →
    (∀ i c, eps - eps / (6 * kappa) < gamma i c → res i c = true) →
    4 * ((univ.filter fun p : Fin n × Fin B => res p.1 p.2 = false).card) ≤ n * B →
    (kappa + 1 / 2) *
        (∑ i, max (∑ c, if eps - eps / (6 * kappa) < gamma i c then eps else gamma i c)
          ((3 / 4 * (B * eps)) / (kappa + 1 / 2)))
      ≤ max 0 (kappa * ((∑ i, ∑ c, gamma i c) -
            2 * ∑ i, ∑ c, if res i c then y i c else 0))
          + eps * ((univ.filter fun p : Fin n × Fin B => res p.1 p.2 = true).card)

/-- **The aggregated shortcut is false.**  Collapsing the frozen rounds into a
single clamped signed term loses too much: the per-round positive parts of
`grayTailRound_selected_positivePart` have to be retained separately. -/
theorem not_aggregatedGrayTailFloorBound : ¬ AggregatedGrayTailFloorBound := by
  intro H
  have h := H 4 4 1 2
    (fun i _ => if i.val = 3 then 0 else 15 / 16)
    (fun i _ => if i.val = 3 then 0 else 1 / 24)
    (fun i _ => decide (i.val ≠ 3))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i c; dsimp only; split <;> norm_num)
    (by intro i c; dsimp only; split <;> norm_num)
    (by intro i c; dsimp only; split <;> norm_num)
    (by intro i c; dsimp only; split <;> norm_num)
    (by intro i c; dsimp only; split <;> norm_num)
    (by
      intro i c hgt
      by_cases hi : i.val = 3
      · simp [hi] at hgt
        norm_num at hgt
      · simpa using hi)
    (by decide)
  have hcard : (univ.filter fun p : Fin 4 × Fin 4 => ¬ (p.1.val = 3)).card = 12 := by
    decide
  revert h
  norm_num [Fin.sum_univ_four, hcard]

end Kolmogorov
