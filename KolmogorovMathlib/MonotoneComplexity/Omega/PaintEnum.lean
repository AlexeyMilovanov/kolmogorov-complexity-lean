/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Omega.PaintLsc

/-!
# Paint attached to an enumerable set of indices (SUV Theorem 109, p. 164)

The stage values needed by `not_isMartinLofRandomReal_of_stagePaint` when the paint
attached to the index `i` is "the weight `r i`, if `i` ever gets enumerated": the stage
value is `0` until the enumeration test fires and `r i` afterwards, so its increments
charge `r i` exactly once, at the stage at which `i` appears.

No statement of the source is rendered in this file.
-/

namespace Kolmogorov

open ENNReal

variable {E : ℚ × ℕ → ℕ → Bool} {r : ℕ → ℚ}

/-- The stage-`s` value of the paint attached to the index `p.2`: the weight `r p.2` as
soon as the test `E p` has fired, and `0` before that. -/
def enumStageVal (E : ℚ × ℕ → ℕ → Bool) (r : ℕ → ℚ) (p : ℚ × ℕ) (s : ℕ) : ℚ :=
  cond (optFirst E p s).isSome (r p.2) 0

/-- The stage values of the paint enumeration are nonnegative when the weights are. -/
theorem enumStageVal_nonneg (hr0 : ∀ i, 0 ≤ r i) (p : ℚ × ℕ) (s : ℕ) :
    0 ≤ enumStageVal E r p s := by
  rw [enumStageVal]
  cases h : (optFirst E p s).isSome with
  | true => exact hr0 _
  | false => exact le_rfl

/-- The stage values of the paint enumeration are non-decreasing in the stage. -/
theorem enumStageVal_mono (hr0 : ∀ i, 0 ≤ r i) (p : ℚ × ℕ) (s : ℕ) :
    enumStageVal E r p s ≤ enumStageVal E r p (s + 1) := by
  rw [enumStageVal, enumStageVal]
  cases h : (optFirst E p s).isSome with
  | false =>
      cases h2 : (optFirst E p (s + 1)).isSome with
      | true => exact hr0 _
      | false => exact le_rfl
  | true =>
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h
      have hj2 : optFirst E p (s + 1) = some j := optFirst_stable hj _ (Nat.le_succ s)
      rw [hj2]
      exact le_rfl

/-- The stage values of the paint enumeration are computable. -/
theorem computable_enumStageVal (hE : Computable₂ E) (hr : Computable r) :
    Computable (fun z : (ℚ × ℕ) × ℕ => enumStageVal E r z.1 z.2) := by
  have hfirst := computable_optFirst hE
  have hisSome := Primrec.option_isSome.to_comp.comp hfirst
  have hproj : Computable (fun z : (ℚ × ℕ) × ℕ => z.1.2) :=
    Computable.snd.comp Computable.fst
  have hval := hr.comp hproj
  have h := Computable.cond hisSome hval
    (Computable.const (0 : ℚ) : Computable (fun _ : (ℚ × ℕ) × ℕ => (0 : ℚ)))
  exact h.of_eq (fun z => rfl)

/-- If the test fires, the paint attached to `p.2` totals `r p.2`. -/
theorem iSup_ofReal_enumStageVal_of_fires (_hr0 : ∀ i, 0 ≤ r i) (p : ℚ × ℕ)
    (hex : ∃ k, E p k = true) :
    (⨆ s, ENNReal.ofReal ((enumStageVal E r p s : ℚ) : ℝ))
      = ENNReal.ofReal ((r p.2 : ℚ) : ℝ) := by
  obtain ⟨k, hk⟩ := hex
  refine le_antisymm (iSup_le (fun s => ?_)) ?_
  · rw [enumStageVal]
    cases h : (optFirst E p s).isSome with
    | true => exact le_rfl
    | false => simp
  · obtain ⟨j, hj⟩ := optFirst_isSome_of (le_refl k) hk
    have hval : enumStageVal E r p k = r p.2 := by
      rw [enumStageVal, hj]
      rfl
    refine le_trans (le_of_eq ?_)
      (le_iSup (fun s => ENNReal.ofReal ((enumStageVal E r p s : ℚ) : ℝ)) k)
    rw [hval]

/-- If the test never fires, no paint is attached to `p.2`. -/
theorem iSup_ofReal_enumStageVal_of_never (p : ℚ × ℕ) (hex : ∀ k, E p k ≠ true) :
    (⨆ s, ENNReal.ofReal ((enumStageVal E r p s : ℚ) : ℝ)) = 0 := by
  have hzero : ∀ s, enumStageVal E r p s = 0 := by
    intro s
    rw [enumStageVal]
    rcases hs : optFirst E p s with _ | j
    · rfl
    · exact absurd (optFirst_spec hs).2.1 (hex j)
  refine le_antisymm (iSup_le (fun s => ?_)) (zero_le _)
  rw [hzero s]
  simp

end Kolmogorov
