import Mathlib.Computability.Partrec
import Mathlib.Data.ENat.Lattice

/-!
# Core Definitions of Algorithmic Information Theory

This module establishes the foundational ontology for Kolmogorov complexity.
It defines maps as partial recursive functions (`Partrec`),
programs, and the core metrics: conditional (`condK`) and plain (`plainK`) complexity.
Finally, it formalizes the concept of an optimal universal decompressor,
which is the prerequisite for the Invariance Theorem.
-/

namespace Kolmogorov

/-! ### Finiteness of an `ℕ∞`-valued complexity -/

/-- An `ℕ∞`-valued quantity bounded by a natural number is finite.  Every "the complexity
with respect to an optimal machine is not `⊤`" lemma of the library is this lemma applied to
that measure's `length + O(1)` bound. -/
theorem ne_top_of_le_natCast {a : ℕ∞} {n : ℕ} (h : a ≤ (n : ℕ∞)) : a ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top n) h

/-- The same finiteness bound with the additive constant written out, which is the shape the
`length + c` bounds of the complexity measures have. -/
theorem ne_top_of_le_natCast_add {a : ℕ∞} {n c : ℕ} (h : a ≤ (n : ℕ∞) + (c : ℕ∞)) : a ≠ ⊤ :=
  ne_top_of_le_natCast (n := n + c) (by simpa using h)

/-! ### Basic Types -/

/-- A bit string is simply a list of booleans. -/
abbrev BitString := List Bool

/-- A Map in our context is a partial function taking a pair of
    (program, context) and potentially returning a computed BitString.
    We use `Part` to naturally model programs that loop indefinitely. -/
abbrev Map := BitString × BitString →. BitString

/-! ### Metrics & Execution -/

/-- The length of a program is the number of bits it contains.
    Defined as `abbrev` so Lean automatically reduces it to `List.length`. -/
abbrev programLength (p : BitString) : ℕ := p.length

/-- A map is a valid decompressor if its execution is partial recursive. -/
abbrev isDecompressor (D : Map) : Prop := Partrec D

/-- A map `D` produces output `x` given program `p` and context `y`.
    Using the membership operator `∈` is the standard Mathlib idiom for `Part.some`. -/
abbrev produces (D : Map) (p y x : BitString) : Prop := x ∈ D (p, y)

/-- The set of lengths of all valid programs that produce `x` given `y`. -/
abbrev candidateLengths (D : Map) (x y : BitString) : Set ENat :=
  {n | ∃ p, produces D p y x ∧ (programLength p : ENat) = n}

/-! ### Kolmogorov Complexity Definitions -/

/-- Conditional Kolmogorov Complexity K_D(x|y).
    Defined as the infimum of the lengths of all valid programs.
    If no program produces `x`, the set is empty, and `sInf ∅ = ⊤` (infinity). -/
noncomputable def condK (D : Map) (x y : BitString) : ENat :=
  sInf (candidateLengths D x y)

/-- Plain Kolmogorov Complexity K_D(x).
    Defined as the conditional complexity with an empty context. -/
noncomputable def plainK (D : Map) (x : BitString) : ENat :=
  condK D x []

/-! ### Optimality (Universality) -/

/-- A map `U` is optimal (universal) if it can simulate any other
    computable decompressor `D` with at most a constant additive overhead `c`
    to the program length. -/
def isOptimalConditional (U : Map) : Prop :=
  isDecompressor U ∧
  ∀ D, isDecompressor D → ∃ c : ℕ, ∀ x y, condK U x y ≤ condK D x y + (c : ENat)

end Kolmogorov
