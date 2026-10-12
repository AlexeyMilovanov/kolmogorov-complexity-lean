import Mathlib.Order.Filter.AtTopBot.Defs
import KolmogorovMathlib.StrongMerging.Basic

/-!
# Merging strong sufficient statistics: definitions of the remaining upper statements

The uniform-selector notions and the one-sided `o(n)` predicate used by the frozen statements of
`StrongMerging.StatementsExtra`.  They live in their own module so that the proofs of those
statements can import them without importing `StatementsExtra` itself.
-/

namespace Kolmogorov.StrongMerging

open Filter

/-- **A total witness of length at most `e`** (the blueprint's class `𝒯_e`, section
`bp-upper-interfaces`): the program `p` halts under the canonical total interpreter
`universalDecompressor` on every binary condition, and `|p| ≤ e`. -/
def IsBoundedTotalWitness (e : ℕ) (p : BitString) : Prop :=
  IsTotalProgram universalDecompressor p ∧ p.length ≤ e

/-- **An exact partition selector** (`cor:partition`, `thm:extractability-envelope`; blueprint
`UpperPartitionFilter`).  The program `q` halts under `universalDecompressor` on every input `z`
(`IsTotalProgram`), its output on `z` is the canonical code of the finite set `Q z`, every output
contains its input, and `q⁻¹(q(z)) = q(z)`: a string `y` lies in `Q z` exactly when `Q y = Q z`.
The output on `z` is unique and `canonicalFiniteSetCode` is injective, so `Q` is determined by
`q`; totality and containment are implied by the other two clauses and are kept for
readability. -/
def IsExactPartitionSelector (q : BitString) (Q : BitString → Finset BitString) : Prop :=
  IsTotalProgram universalDecompressor q ∧
    (∀ z : BitString, produces universalDecompressor q z (canonicalFiniteSetCode (Q z))) ∧
    (∀ z : BitString, z ∈ Q z) ∧
    ∀ z y : BitString, y ∈ Q z ↔ Q y = Q z

/-- **A qualifying instance of the uniform selectors** (`cor:partition`,
`thm:extractability-envelope`; blueprint "Exact top-level targets"): `n ≥ 2`, `e ≤ n`, `x` has
length `n`, the witnesses `p_A, p_B` output on `x` the canonical codes of `A` and `B`
(`A = p_A(x)`, `B = p_B(x)` are valid model outputs), and `A, B ∋ x` are `e`-sufficient.
Strength is not a separate clause: when `p_A` is moreover a total witness of length at most `e`
(`IsBoundedTotalWitness e p_A`, as in every selector statement below), it gives
`CT(A | x) ≤ e`, and likewise for `B`. -/
def IsWitnessedInstance (V : Map) (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) :
    Prop :=
  2 ≤ n ∧ e ≤ n ∧ x.length = n ∧
    produces universalDecompressor pA x (canonicalFiniteSetCode A) ∧
    produces universalDecompressor pB x (canonicalFiniteSetCode B) ∧
    IsSufficientModel V x A e ∧ IsSufficientModel V x B e

/-- **`f = o(n)` from above along an index** (blueprint target Q04): for every `η > 0`,
eventually `f j ≤ η n_j`.  It bounds `f` from above only; for a nonnegative `f` and `n_j > 0`
eventually (for instance `n_j → ∞`) it is `f j / n j → 0`. -/
def SublinearAbove (f : ℕ → ℝ) (n : ℕ → ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, f j ≤ η * n j

end Kolmogorov.StrongMerging
