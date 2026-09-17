/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib

/-!
# The dyadic floor-selector reading of computability of a measure is too strong

The modelling mistake closed here is the reading of "the measure of every
cylinder is a computable real" in which the approximant is required to sit
*below* the mass on the same dyadic grid as the error,
`a x s / 2^s ≤ μ[x] ≤ a x s / 2^s + 2^{-s}`.  That silently demands a computable
dyadic floor selector `⌊2^s · μ[x]⌋`, and with it the representation theorem
77(b) becomes false: an exactly additive lower-semicomputable continuous
semimeasure is exhibited whose floors would separate a computably inseparable
pair.  The faithful two-sided reading is `Kolmogorov.IsComputableMeasure`, for
which the representation theorem is proved in
`MonotoneComplexity/TwoSidedMeasureRepresentation.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-- The floor-selector strengthening of `IsComputableMeasure`: the approximant
is required to sit *below* the mass on the same dyadic grid as the error.  Kept
only as the target of the machine-checked refutation of Theorem 77(b) for this
reading; do not use it as the hypothesis or conclusion of new chapter
theorems. -/
def IsFloorComputableMeasure (μ : Measure CantorSeq) : Prop :=
  ∃ a : BitString → ℕ → ℕ, Computable₂ a ∧ ∀ x s,
    dyadicValue (a x s) s ≤ cantorMass μ x ∧
      cantorMass μ x ≤ dyadicValue (a x s) s + dyadicValue 1 s

/-- The floor-selector notion implies the faithful two-sided one. -/
lemma IsFloorComputableMeasure.isComputableMeasure {μ : Measure CantorSeq}
    (h : IsFloorComputableMeasure μ) : IsComputableMeasure μ := by
  rcases h with ⟨a, hcomp, hbound⟩
  exact isComputableMeasure_of_dyadicFloorApprox hcomp hbound

/-- The uniform (fair-coin) measure does admit a computable dyadic floor
selector: its cylinder masses are dyadic. -/
lemma isFloorComputableMeasure_uniform :
    IsFloorComputableMeasure uniformMeasure :=
  ⟨uniformApprox, uniformApprox_computable, fun x s =>
    ⟨uniformApprox_le_mass x s, mass_le_uniformApprox_add x s⟩⟩

/-! ### The refutation -/

/-- **The floor-selector representation statement is false.**

There is no way to represent *every* exactly additive lower-semicomputable
continuous semimeasure by a measure admitting a computable dyadic floor
selector (`IsFloorComputableMeasure`).  Theorem 77(b) for the faithful
two-sided `IsComputableMeasure` is proved in
`TwoSidedMeasureRepresentation.lean`; this refutation documents that the
floor-selector strengthening is genuinely stronger. -/
theorem not_forall_exists_isFloorComputableMeasure_of_exact :
    ¬ ∀ a : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure a →
        (∀ x, a x = a (x ++ [false]) + a (x ++ [true])) →
        ∃ μ : Measure CantorSeq, IsFloorComputableMeasure μ ∧ ∀ x, cantorMass μ x = a x := by
  intro H
  obtain ⟨μ, ⟨sel, hsel_comp, hsel⟩, hmass⟩ :=
    H hardTree isLowerSemicomputableContinuousSemimeasure_hardTree hardTree_exact
  have hnode : Computable (fun e : ℕ => hardNode e) := by
    have h : Primrec (fun e : ℕ => hardNode e) :=
      (Primrec.list_append.comp
        (Primrec.list_replicate.comp Primrec.id (Primrec.const true))
        (Primrec.const [false, false]))
    exact h.to_comp
  have hval : Computable (fun e : ℕ => sel (hardNode e) (e + 2)) :=
    hsel_comp.comp hnode ((Primrec.succ.comp (Primrec.succ)).to_comp)
  have hle : Computable₂ (fun a b : ℕ => decide (a ≤ b)) := by
    obtain ⟨inst, h⟩ := Primrec.nat_le
    have h2 : Primrec (fun p : ℕ × ℕ => @decide (p.1 ≤ p.2) (Nat.decLe p.1 p.2)) :=
      h.of_eq (fun p => by rw [Subsingleton.elim (inst p) (Nat.decLe p.1 p.2)])
    exact Computable₂.mk h2.to_comp
  have hS : Computable (fun e : ℕ => decide (1 ≤ sel (hardNode e) (e + 2))) :=
    hle.comp (Computable.const 1) hval
  refine no_computable_diagonal_separator hS ?_ ?_
  · intro e he
    have hgt : dyadicValue 1 (e + 2) < cantorMass μ (hardNode e) := by
      rw [hmass]; exact hardTree_hardNode_gt he
    by_contra hcon
    have hz : sel (hardNode e) (e + 2) = 0 := by
      simp only [decide_eq_true_eq] at hcon
      omega
    have hup := (hsel (hardNode e) (e + 2)).2
    rw [hz, dyadicValue_zero, zero_add] at hup
    exact absurd hup (not_le.mpr hgt)
  · intro e he
    have hlt : cantorMass μ (hardNode e) < dyadicValue 1 (e + 2) := by
      rw [hmass]; exact hardTree_hardNode_lt he
    by_contra hcon
    simp only [Bool.not_eq_false, decide_eq_true_eq] at hcon
    have hlow := (hsel (hardNode e) (e + 2)).1
    have : dyadicValue 1 (e + 2) ≤ dyadicValue (sel (hardNode e) (e + 2)) (e + 2) :=
      dyadicValue_le _ _ _ hcon
    exact absurd (this.trans hlow) (not_le.mpr hlt)

end Kolmogorov
