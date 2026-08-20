import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainProfile

/-!
# Extensional marking predicates and Figure 6 regions for Theorem `t1`

These definitions freeze the three source families used by the strange-string
marking construction.  They are extensional: finite models are represented by
their canonical uniform codes, and the `C` predicate records the actual plain
description-profile condition on that code.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- A length-`n` string has a `b`-mark when it lies in a model of plain
complexity at most `epsilon` and cardinality at most `2^(n-epsilon-4)`. -/
noncomputable def T1BMarked
    (V : Map) (n epsilon : Nat) (x : BitString) : Prop :=
  x.length = n ∧
    ∃ (B : Finset BitString) (hB : B.Nonempty),
      x ∈ B ∧
      plainSetComplexity V B hB ≤ (epsilon : ENat) ∧
      B.card ≤ 2 ^ (n - epsilon - 4)

/-- A length-`n` string has a `c`-mark when it lies in a small model of plain
complexity at most `k` whose canonical code has a `(d,n)` plain description.
The later construction instantiates `d = epsilon + O(log n)`. -/
noncomputable def T1CMarked
    (V : Map) (n k d : Nat) (x : BitString) : Prop :=
  x.length = n ∧
    ∃ (M : Finset BitString) (hM : M.Nonempty),
      x ∈ M ∧
      plainSetComplexity V M hM ≤ (k : ENat) ∧
      M.card ≤ 2 ^ (n - k - 4) ∧
      InPlainDescriptionProfile V (codedUniformOn M hM).code d n

/-- A length-`n` string has a `d`-mark exactly when its ordinary plain
complexity is strictly below `k`. -/
noncomputable def T1DMarked
    (V : Map) (n k : Nat) (x : BitString) : Prop :=
  x.length = n ∧ plainK V x < (k : ENat)

/-- Figure 6 dashed region: below complexity `epsilon` its boundary is
`i+j=n`, and from `epsilon` onward it is `i+j=k`. -/
def t1PlainPolygon (n k epsilon : Nat) : Set (Nat × Nat) :=
  {q | if q.1 < epsilon then n ≤ q.1 + q.2 else k ≤ q.1 + q.2}

/-- Figure 6 solid region: the diagonal `i+j=n` up to `i=k`, followed by
the vertical ray `i=k`. -/
def t1StrongPolygon (n k : Nat) : Set (Nat × Nat) :=
  {q | k ≤ q.1 ∨ n ≤ q.1 + q.2}

end Kolmogorov
