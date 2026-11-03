/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.MDLPrediction.Mean.Brackets

/-!
# Certified conditional quotients

The denominator is an upper mass bracket. The numerator is a lower bracket, and the
quotient is emitted only after a positive lower certificate for the parent appears.
Blueprint nodes: `exp:quotient-lower`.
-/

namespace Kolmogorov.MDLPrediction

open MeasureTheory
open scoped ENNReal

/-- A gated lower request for one conditional probability.
Blueprint node `exp:quotient-lower`. -/
noncomputable def conditionalLower (e s : ℕ) (y : BitString) (b : Bool) : ℝ :=
  if 0 < massLower e s y then
    (massLower e s (y ++ [b])).toReal / (massUpper e s y).toReal
  else 0

/-- At positive parent mass the certified quotients converge from below, while
an upper denominator bracket stays positive. Blueprint node `exp:quotient-lower`. -/
theorem exp_quotient_lower (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (y : BitString) (b : Bool)
    (hy : 0 < cantorMass P y) :
    (∀ s, 0 < massUpper e s y) ∧
    (∀ s, conditionalLower e s y b ≤ conditionalLower e (s + 1) y b) ∧
    (∀ s, conditionalLower e s y b ≤ condProb (cantorMass P) y b) ∧
    Filter.Tendsto (fun s => conditionalLower e s y b) Filter.atTop
      (nhds (condProb (cantorMass P) y b)) := by
  obtain ⟨hLy, hUy, hBy, hsupy, hinfy⟩ := exp_dyadic_bracket P e he y
  obtain ⟨hLyb, -, hByb, hsupyb, -⟩ := exp_dyadic_bracket P e he (y ++ [b])
  have hPy : cantorMass P y ≠ ⊤ := measure_ne_top P _
  have hPyb : cantorMass P (y ++ [b]) ≠ ⊤ := measure_ne_top P _
  have hUtop : ∀ t, massUpper e t y ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hBy t).2.2
  have hLtop : ∀ t, massLower e t (y ++ [b]) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hPyb (hByb t).1
  -- (1) every upper bracket is positive (true for every code `e`)
  have hUpos : ∀ s, 0 < massUpper e s y := by
    intro s
    unfold massUpper
    rw [Finset.lt_inf_iff ENNReal.zero_lt_top]
    intro k _
    split
    · refine lt_min one_pos ?_
      unfold dyadicValue
      exact ENNReal.div_pos (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    · exact one_pos
  refine ⟨hUpos, ?_, ?_, ?_⟩
  · -- (2) the gate opens monotonically, numerator up, denominator down
    intro s
    unfold conditionalLower
    by_cases h0 : 0 < massLower e s y
    · have h1 : 0 < massLower e (s + 1) y := h0.trans_le (hLy s)
      simp only [h0, h1, ↓reduceIte]
      exact div_le_div₀ ENNReal.toReal_nonneg
        ((ENNReal.toReal_le_toReal (hLtop s) (hLtop (s + 1))).mpr (hLyb s))
        (ENNReal.toReal_pos (hUpos (s + 1)).ne' (hUtop (s + 1)))
        ((ENNReal.toReal_le_toReal (hUtop (s + 1)) (hUtop s)).mpr (hUy s))
    · simp only [h0, ↓reduceIte]
      split_ifs
      · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      · exact le_rfl
  · -- (3) certified: lower numerator over upper denominator
    intro s
    unfold conditionalLower condProb
    split_ifs
    · calc (massLower e s (y ++ [b])).toReal / (massUpper e s y).toReal
          ≤ (cantorMass P (y ++ [b])).toReal / (massUpper e s y).toReal :=
            div_le_div_of_nonneg_right (ENNReal.toReal_mono hPyb (hByb s).1)
              ENNReal.toReal_nonneg
        _ ≤ (cantorMass P (y ++ [b])).toReal / (cantorMass P y).toReal :=
            div_le_div_of_nonneg_left ENNReal.toReal_nonneg (ENNReal.toReal_pos hy.ne' hPy)
              (ENNReal.toReal_mono (hUtop s) (hBy s).2.1)
    · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · -- (4) monotone convergence of both brackets, the gate is eventually open
    have hL0 : Filter.Tendsto (fun s => massLower e s y) Filter.atTop
        (nhds (cantorMass P y)) := by
      rw [← hsupy]; exact tendsto_atTop_iSup (monotone_nat_of_le_succ hLy)
    have hL1 : Filter.Tendsto (fun s => massLower e s (y ++ [b])) Filter.atTop
        (nhds (cantorMass P (y ++ [b]))) := by
      rw [← hsupyb]; exact tendsto_atTop_iSup (monotone_nat_of_le_succ hLyb)
    have hU0 : Filter.Tendsto (fun s => massUpper e s y) Filter.atTop
        (nhds (cantorMass P y)) := by
      rw [← hinfy]; exact tendsto_atTop_iInf (antitone_nat_of_succ_le hUy)
    have hq : Filter.Tendsto
        (fun s => (massLower e s (y ++ [b])).toReal / (massUpper e s y).toReal)
        Filter.atTop (nhds (condProb (cantorMass P) y b)) :=
      ((ENNReal.tendsto_toReal hPyb).comp hL1).div ((ENNReal.tendsto_toReal hPy).comp hU0)
        (ENNReal.toReal_pos hy.ne' hPy).ne'
    refine hq.congr' ?_
    filter_upwards [(tendsto_order.1 hL0).1 0 hy] with s hs
    unfold conditionalLower
    simp only [hs, ↓reduceIte]

/-- At a zero parent mass, the support gate never emits a positive request.
Blueprint node `exp:quotient-lower`. -/
theorem conditionalLower_zero (P : Measure CantorSeq) [IsProbabilityMeasure P]
    (e : ℕ) (he : IsComputableMeasureIndex P e) (y : BitString) (b : Bool)
    (hy : cantorMass P y = 0) :
    ∀ s, conditionalLower e s y b = 0 := by
  intro s
  unfold conditionalLower
  have h_le := (exp_dyadic_bracket P e he y).2.2.1 s
  have h_le2 : massLower e s y ≤ 0 := hy ▸ h_le.1
  have h_eq_zero : massLower e s y = 0 := le_antisymm h_le2 (zero_le)
  have h_not_lt : ¬ (0 < massLower e s y) := by
    rw [h_eq_zero]
    exact lt_irrefl 0
  rw [ite_eq_right_iff.mpr]
  intro h_false
  exact False.elim (h_not_lt h_false)

/-- Upper denominator brackets stay positive even at a zero-mass parent.
Blueprint node `exp:quotient-lower`. -/
theorem exp_quotient_upper_pos (e : ℕ) (y : BitString) :
    ∀ s, 0 < massUpper e s y := by
  intro s
  unfold massUpper
  rw [Finset.lt_inf_iff ENNReal.zero_lt_top]
  intro k _
  split
  · rename_i a _
    apply lt_min
    · exact zero_lt_one
    · unfold dyadicValue
      apply ENNReal.div_pos_iff.mpr
      constructor
      · intro h
        apply Nat.succ_ne_zero a
        exact Nat.cast_eq_zero.mp h
      · apply ENNReal.pow_ne_top
        exact ENNReal.coe_ne_top
  · exact zero_lt_one

end Kolmogorov.MDLPrediction
