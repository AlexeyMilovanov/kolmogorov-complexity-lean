import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile

/-!
# Exact splitting of the conditional-randomness gain

The add-noise arguments of VS40 §7 branch on whether a noise string `y` is
already conditionally random given `z`, or whether it loses some exact number
`k` of bits.  This module records that dichotomy with explicit natural-number
witnesses, so that later arguments can use `k` as an ordinary natural number
instead of manipulating an `ENat` difference.

No optimality hypothesis on the machine is needed: when the conditional
complexity is infinite the first alternative holds trivially.
-/

namespace Kolmogorov

/-- Either `y` is already conditionally random given `z`, or its conditional
complexity is an exact natural number `t < |y|` and the gain `k = |y| - t`
restores the length exactly. -/
theorem condK_exact_gain_or_no_gain (V : Map) (y z : BitString) :
    (y.length : ENat) ≤ condK V y z ∨
      ∃ t k : Nat,
        condK V y z = (t : ENat) ∧
        t < y.length ∧
        k = y.length - t ∧
        condK V y z + (k : ENat) = (y.length : ENat) := by
  rcases eq_or_ne (condK V y z) ⊤ with htop | hfin
  · exact Or.inl (by rw [htop]; exact le_top)
  · set t : Nat := (condK V y z).toNat with htdef
    have hteq : condK V y z = (t : ENat) := (ENat.coe_toNat hfin).symm
    rcases lt_or_ge t y.length with hlt | hge
    · refine Or.inr ⟨t, y.length - t, hteq, hlt, rfl, ?_⟩
      rw [hteq]
      have : t + (y.length - t) = y.length := by omega
      exact_mod_cast congrArg (Nat.cast : Nat → ENat) this
    · exact Or.inl (by rw [hteq]; exact_mod_cast hge)

end Kolmogorov
