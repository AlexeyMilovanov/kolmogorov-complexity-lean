import KolmogorovMathlib.MonotoneComplexity.GacsDayGame

/-!
# Height padding for the uniform winning condition

`GacsDayGameStatement` asks for a winning strategy at the *padded* height
`C * d`, while every controller wins at its own, smaller height.  The one
monotonicity step that bridges the two is isolated here so that it does not
live inside any particular controller's module.
-/

namespace Kolmogorov

/-- A uniform winning strategy stays winning when the height bound is relaxed. -/
lemma isUniformWinningStrategy_mono_height {h b d h' : ℕ} (hh : h ≤ h') {σ : ClientStrategy}
    (hw : IsUniformWinningStrategy h b d σ) : IsUniformWinningStrategy h' b d σ := by
  constructor
  · exact isWinningStrategyUnserved_mono_height hh hw.1
  · exact hw.2

end Kolmogorov
