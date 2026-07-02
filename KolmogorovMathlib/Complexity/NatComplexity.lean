import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic
import Mathlib.Data.ENat.Lattice
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.Incompressibility

/-!
# Complexity of Natural Numbers

This module lifts the concept of Kolmogorov complexity from bit strings
to natural numbers using the standard injective binary representation (`Nat.bits`).
It proves the existence of arbitrarily complex natural numbers,
establishes logarithmic upper bounds on their complexity, and proves
that the complexity is invariant (up to a constant) under any computable
change of encoding.
-/

namespace Kolmogorov

/-! ### Complexity of Natural Numbers -/

/-- The plain Kolmogorov complexity of a natural number. -/
noncomputable def plainKNat (U : Map) (n : ℕ) : ENat :=
  plainK U (Nat.bits n)

/-- The conditional Kolmogorov complexity of a natural number given string y. -/
noncomputable def condKNat (U : Map) (n : ℕ) (y : BitString) : ENat :=
  condK U (Nat.bits n) y

/-! ### Existence of Complex Numbers (Corollary) -/

/-- The Fundamental Theorem for Natural Numbers: For any threshold L,
    there exists a natural number n whose complexity is strictly greater than L.
    This follows directly from the generalized Pigeonhole Principle. -/
theorem existsPlainKNatGt (U : Map) (L : ℕ) :
    ∃ n : ℕ, plainKNat U n > (L : ENat) := by
  -- Updated the identifier to match the new CamelCase name from Incompressibility.lean
  exact existsComplexInjective natBitsInjective U L

/-! ### Upper Bounds (Logarithmic Bound) -/

/-- Upper bound for nat complexity. We use ℕ instead of ENat for the
    constant c to ensure it is finite and usable in Berry's paradox. -/
lemma plainKNatLeLength (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, plainKNat U n ≤ (programLength (Nat.bits n) : ENat) + c := by
  obtain ⟨c, hc⟩ := plainKLeLength U hU
  exact ⟨c, fun n => hc (Nat.bits n)⟩

/-! ### Invariance of Encoding (Universality) -/

/-- Invariance theorem: if an alternative encoding `e` is computable from
    our standard one via some computable function `f`, then the
    complexity difference is bounded by a constant. -/
theorem plainKNatInvariance (U : Map) (hU : isOptimalConditional U)
    (e : ℕ → BitString) (f : BitString → BitString) (hf : Computable f)
    (h_map : ∀ n, e n = f (Nat.bits n)) :
    ∃ c : ℕ, ∀ n : ℕ, plainK U (e n) ≤ plainKNat U n + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe U hU f hf
  exact ⟨c, fun n => by rw [h_map n]; exact hc (Nat.bits n)⟩

end Kolmogorov
