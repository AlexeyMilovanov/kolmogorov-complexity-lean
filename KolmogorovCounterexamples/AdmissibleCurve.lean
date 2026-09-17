/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib

/-!
# The five-field curve-admissibility packaging is unsatisfiable

The modelling mistake closed here is the packaging of the Section-3 admissibility
conditions (A1)–(A4) for the structure function of a string as five *exact*
fields on a curve `h : ℕ → ℕ`: antitonicity, the two endpoints, a slope-`1`
condition and a sufficiency line quantified over *all* zeros of `h`.  The five
fields contradict each other, so a claim of the form `∃ h, AdmissibleCurve n h`
is false and cannot be the formal reading of the section.  The provable
replacement, phrased directly on the structure function and with logarithmic
slack, is `Kolmogorov.structureFunction_admissible`.
-/

namespace Kolmogorov

/-- Curve admissibility (A1)–(A5) in an inconsistent form.

**Warning (mathematically flawed – kept only to document the fix).**  This
predicate is **unsatisfiable**: no `h : ℕ → ℕ` can meet all five fields at once, so
any `∃ h, AdmissibleCurve n h` claim is false.  See
`AdmissibleCurve_unsatisfiable`.

The defect is the interaction of `antitone` + `bottom` + `sufficient`: `bottom`
gives a zero `k₀`, `antitone` propagates it to `k₀ + 1`, and `sufficient` at
`i := k₀`, `k := k₀ + 1` then demands `k₀ + 1 ≤ k₀`.  The intended `sufficient`
(sufficiency line `i + h_x(i) ≥ K(x) - O(log)`) must be quantified at the *minimal*
zero (or over `i ≤` that zero) and carry logarithmic slack, not universally over
all zeros `k`.  Independently, `slope` ("the log-size drops by at most one per unit
of complexity budget") is **not** a universal property of structure functions:
non-stochastic strings (cf. `NonStochastic.lean`) have arbitrarily steep drops, so
no slope-≤1 curve can stay within a fixed `logSlack` band of such a structure
function.  The corrected, provable Section-3 statement is
`structureFunction_admissible` below, phrased directly on `structureFunction`. -/
structure AdmissibleCurve (n : ℕ) (h : ℕ → ℕ) : Prop where
  antitone   : ∀ i, h (i + 1) ≤ h i                         -- (A1)
  top        : h 0 ≤ n                                       -- (A2a)
  bottom     : ∃ k ≤ n, h k = 0                              -- (A2b)
  slope      : ∀ i, h i ≤ h (i + 1) + 1                      -- (A3)
  sufficient : ∀ i k, h k = 0 → k ≤ i + h i                  -- (A4)

/-- The `AdmissibleCurve` predicate above is unsatisfiable, so the earlier
`profile_is_admissible` (which asserted such a curve exists) was false as stated.
Proof: a zero of `h` (from `bottom`) is propagated one step by `antitone`, and
`sufficient` applied to those two points forces `k₀ + 1 ≤ k₀`. -/
theorem AdmissibleCurve_unsatisfiable (n : ℕ) : ¬ ∃ h : ℕ → ℕ, AdmissibleCurve n h := by
  rintro ⟨h, hac⟩
  obtain ⟨k0, _, hk0⟩ := hac.bottom
  have h1 : h (k0 + 1) = 0 := Nat.le_zero.mp (hk0 ▸ hac.antitone k0)
  have h2 := hac.sufficient k0 (k0 + 1) h1
  omega

end Kolmogorov
