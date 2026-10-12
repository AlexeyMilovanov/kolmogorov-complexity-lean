import Mathlib.Analysis.SpecialFunctions.Pow.Real
import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.SharedCoding

/-!
# Solomonoff prediction of selected bits: the basic notions

The setting of Bauwens–Kuznetsov, *Solomonoff induction of selected bits* (slides of 26 August
2026).  A computable prefix tree `T` fixes a pattern; along an infinite branch `ω` of `T` the
predictor is only judged at the *forced* positions, those `i` at which the sibling
`ω_{<i} (1 - ω_i)` of the observed bit leaves the tree.  The predictor is the normalized
Solomonoff predictor `M(x b) / (M(x 0) + M(x 1))` of the universal lower semicomputable tree
semimeasure `M = universalContinuousSemimeasure`.  The loss at a forced position is the
normalized probability of the forbidden sibling, and the γ-power loss sums the γ-th powers of
these errors over the forced positions.

* `DecidesTree e T`: the partial-recursive code with index `e` is a total Boolean membership
  test of the prefix tree `T`, answering `1` on the members and `0` elsewhere.
* `IsComputablePrefixTree T`: some computable Boolean function decides membership in `T`.
* `Branch T ω`: every finite prefix of `ω` belongs to `T`.
* `normalizedSiblingProb a x b`: the sibling-normalized next-bit probability
  `a(x b) / (a(x 0) + a(x 1))`.  It differs from `condProb`, whose denominator is `a x`.
* `normalizedError a ω i`: the normalized probability of the wrong bit at position `i`.
* `ForcedPosition T ω i`: the observed child is in `T` and its sibling is not.
* `forcedErrorTerm a T ω γ i`: `normalizedError a ω i ^ γ` at a forced position, else `0`.
* `partialPowerLoss a T ω γ n`: the sum of these terms over `i < n`.
* `treeComplexity U T`: the least prefix complexity `KPNat U e` of an index `e` deciding `T`.

Positions are zero-based: position `i` predicts the bit `ω i` after the prefix
`cantorPrefix ω i`.
-/

namespace Kolmogorov.SelectedBits

open scoped ENNReal

/-- A set of binary words is prefix closed when it contains every prefix of each member. -/
def PrefixClosed (T : Set BitString) : Prop :=
  ∀ ⦃x y : BitString⦄, x <+: y → y ∈ T → x ∈ T

/-- A prefix tree: a prefix-closed set of words containing the empty word. -/
def IsPrefixTree (T : Set BitString) : Prop :=
  [] ∈ T ∧ PrefixClosed T

/-- The code with index `e` (in the enumeration `Denumerable.ofNat Nat.Partrec.Code`) is a total
Boolean membership test of the prefix tree `T`: on the encoding of every word it halts with
output `1` on the members of `T` and with output `0` on the non-members. -/
def DecidesTree (e : ℕ) (T : Set BitString) : Prop :=
  IsPrefixTree T ∧
    ∀ x : BitString, ∃ b : Bool,
      (if b then 1 else 0 : ℕ) ∈
        (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode x) ∧
      (b = true ↔ x ∈ T)

/-- A prefix tree with a computable Boolean membership test. -/
def IsComputablePrefixTree (T : Set BitString) : Prop :=
  IsPrefixTree T ∧ ∃ d : BitString → Bool, Computable d ∧ ∀ x, d x = true ↔ x ∈ T

/-- Every finite prefix of the sequence `ω` belongs to `T`.  No computability or randomness
assumption is placed on the branch. -/
def Branch (T : Set BitString) (ω : CantorSeq) : Prop :=
  ∀ n : ℕ, cantorPrefix ω n ∈ T

/-- The sibling-normalized next-bit probability `a(x b) / (a(x 0) + a(x 1))`, as a real number.
Real division makes it `0` when the denominator vanishes; for the universal semimeasure both
child masses are positive and finite. -/
noncomputable def normalizedSiblingProb (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    ℝ :=
  (a (x ++ [b])).toReal / ((a (x ++ [false])).toReal + (a (x ++ [true])).toReal)

/-- The normalized probability of the wrong bit at the zero-based position `i` of `ω`. -/
noncomputable def normalizedError (a : BitString → ℝ≥0∞) (ω : CantorSeq) (i : ℕ) : ℝ :=
  normalizedSiblingProb a (cantorPrefix ω i) (!(ω i))

/-- Position `i` of `ω` is forced by `T`: the observed child `ω_{<i} ω_i` is in `T` and its
sibling `ω_{<i} (1 - ω_i)` is not. -/
def ForcedPosition (T : Set BitString) (ω : CantorSeq) (i : ℕ) : Prop :=
  cantorPrefix ω i ++ [ω i] ∈ T ∧ cantorPrefix ω i ++ [!(ω i)] ∉ T

/-- The γ-th power of the normalized error at position `i` when the position is forced by `T`,
and `0` otherwise. -/
noncomputable def forcedErrorTerm (a : BitString → ℝ≥0∞) (T : Set BitString) (ω : CantorSeq)
    (γ : ℝ) (i : ℕ) : ℝ := by
  classical
  exact if ForcedPosition T ω i then normalizedError a ω i ^ γ else 0

/-- The γ-power loss of the normalized predictor of `a` on the first `n` positions of `ω`: the
sum of `normalizedError a ω i ^ γ` over the forced positions `i < n`. -/
noncomputable def partialPowerLoss (a : BitString → ℝ≥0∞) (T : Set BitString) (ω : CantorSeq)
    (γ : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, forcedErrorTerm a T ω γ i

/-- The prefix complexity of a tree: the least `KPNat U e` over the indices `e` deciding `T`,
as an extended natural number (`⊤` when no index decides `T`). -/
noncomputable def treeComplexity (U : Map) (T : Set BitString) : ℕ∞ :=
  ⨅ e ∈ {e : ℕ | DecidesTree e T}, KPNat U e

end Kolmogorov.SelectedBits
