import KolmogorovMathlib.Complexity.GeneralScheme.Regular
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.AlgorithmicRandomness.Cantor

/-!
# Decision complexity: definitions (SUV Section 6.1)

SUV Section 6.1 (printed pp. 193–197) introduces *decision complexity* `KR`, first studied by
Loveland. A decompressor reads a terminated input string `p` and prints bits one by one without
being obliged to stop. Its output `M(p)` is a finite or infinite bit sequence. `KR_M(x)` is the
least length of a `p` such that `M(p)` starts with `x`.

We represent a machine by the relation `M.rel p x` ("`M(p)` starts with `x`"). This relation is
enumerable, contains `(p, [])`, is closed under prefixes of `x`, and the strings related to one
`p` are pairwise compatible. Such a relation is the same thing as a machine printing a finite or
infinite sequence: the machine prints the longest string enumerated so far. Equivalently it is
an enumerable `=`-`≍`-regular relation of Section 6.2 that is closed under prefixes of the
object.

As in the rest of the library there is no fixed optimal decompressor. Statements take an optimal
`R : DecisionDecompressor` with `R.IsOptimal`, and complexities are `ℕ∞`-valued.

The module also defines the variants used in SUV Problems 193–196: continuous maps `ℕ⊥ → Σ`
(`ContDecisionMap`), bitwise decompressors (`bitwiseKR`), and printing programs (`programKR`,
`programKP`).
-/

namespace Kolmogorov

namespace GeneralScheme

open Nat.Partrec (Code)

/-- SUV Section 6.1: a *decision decompressor*. It is a machine that reads a terminated binary
input `p` and prints a finite or infinite bit sequence `M(p)`, represented by the relation
`rel p x` saying "`M(p)` starts with `x`". -/
structure DecisionDecompressor where
  /-- `rel p x`: the output of the machine on input `p` starts with `x`. -/
  rel : BitString → BitString → Prop
  /-- The machine is computable: the set of pairs `(p, x)` is enumerable. -/
  re : IsRE (fun q : BitString × BitString => rel q.1 q.2)
  /-- Every output starts with the empty string. -/
  nil_mem : ∀ p, rel p []
  /-- A prefix of a prefix of the output is a prefix of the output. -/
  prefix_closed : ∀ ⦃p x x' : BitString⦄, rel p x → x' <+: x → rel p x'
  /-- The prefixes of one output are pairwise compatible (`=`-`≍`-regularity). -/
  regular : IsRegular .eq .compat rel

/-- `KR_M(x)`: the least length of an input `p` whose output `M(p)` starts with `x` (`⊤` if there
is none). -/
noncomputable def KROf (M : DecisionDecompressor) (x : BitString) : ℕ∞ :=
  modeComplexity M.rel x

/-- An optimal decision decompressor: `KR_R ≤ KR_M + O(1)` for every decision decompressor `M`
(SUV Problem 192). -/
def DecisionDecompressor.IsOptimal (R : DecisionDecompressor) : Prop :=
  ∀ M : DecisionDecompressor, ∃ c : ℕ, ∀ x, KROf R x ≤ KROf M x + c

/-- Decision complexity of an infinite sequence: the limit (supremum) of the non-decreasing
complexities of its prefixes (SUV Theorem 127 (b)). -/
noncomputable def KRSeq (M : DecisionDecompressor) (w : CantorSeq) : ℕ∞ :=
  ⨆ n, KROf M (cantorPrefix w n)

/-! ### Continuous maps `ℕ⊥ → Σ` (SUV Problem 193) -/

/-- SUV Problem 193: a computable continuous map `ℕ⊥ → Σ`, with `⊥` represented by `none`.
Unlike a `DecisionDecompressor`, the value on `⊥` may be a nonempty string, and every value
extends it. -/
structure ContDecisionMap where
  /-- `rel a x`: the value of the map at `a ∈ ℕ⊥` starts with `x`. -/
  rel : Option BitString → BitString → Prop
  /-- Computability: the set of pairs `(a, x)` is enumerable. -/
  re : IsRE (fun q : Option BitString × BitString => rel q.1 q.2)
  /-- Every value starts with the empty string. -/
  nil_mem : ∀ a, rel a []
  /-- Closure under prefixes of the object. -/
  prefix_closed : ∀ ⦃a x x'⦄, rel a x → x' <+: x → rel a x'
  /-- The prefixes of one value are pairwise compatible. -/
  compatible : ∀ ⦃a x₁ x₂⦄, rel a x₁ → rel a x₂ → x₁ <+: x₂ ∨ x₂ <+: x₁
  /-- Monotonicity: the value at `⊥` is a prefix of every value. -/
  bot_le : ∀ ⦃x⦄, rel none x → ∀ p, rel (some p) x

/-- The complexity defined by a continuous map `ℕ⊥ → Σ`. Descriptions are the strings `p`
(the element `⊥` is not a description). -/
noncomputable def ContDecisionMap.complexity (F : ContDecisionMap) (x : BitString) : ℕ∞ :=
  modeComplexity (fun p x => F.rel (some p) x) x

/-! ### Bitwise decompressors (SUV Problem 194) -/

/-- SUV Problem 194: for a partial function `S(y, i)` with bit values, `KR_S(x)` is the least
length of `y` such that `S(y, i) = x_i` for all `i < l(x)`. -/
noncomputable def bitwiseKR (S : BitString × ℕ →. Bool) (x : BitString) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ y, (∀ i (hi : i < x.length), x[i] ∈ S (y, i)) ∧ l = y.length}

/-- An optimal bitwise decompressor: partial computable and minimal up to an additive constant
among partial computable bitwise decompressors. -/
def IsOptimalBitwise (S : BitString × ℕ →. Bool) : Prop :=
  Partrec S ∧
    ∀ S' : BitString × ℕ →. Bool, Partrec S' → ∃ c : ℕ, ∀ x, bitwiseKR S x ≤ bitwiseKR S' x + c

/-! ### Printing programs (SUV Problems 195, 196) -/

/-- The program with code `e` prints `x` or an extension of `x`. Programs are
`Nat.Partrec.Code`s. The program ignores its input, and its `i`-th output bit is its value at
`i` (`1` for `true`, `0` for `false`). -/
def PrintsPrefix (e : ℕ) (x : BitString) : Prop :=
  ∀ i (hi : i < x.length), (x[i]).toNat ∈ (Denumerable.ofNat Code e).eval i

/-- SUV Problem 195: the least plain complexity `C(e)` of a program `e` that prints `x` or an
extension of `x`. The program text is `Nat.bits e`, as in `programComplexity`. -/
noncomputable def programKR (U : Map) (x : BitString) : ℕ∞ :=
  ⨅ (e : ℕ) (_ : PrintsPrefix e x), plainK U (Nat.bits e)

/-- SUV Problem 196: the least prefix complexity `K(e)` of a program `e` that prints `x` or an
extension of `x`. -/
noncomputable def programKP (U : Map) (x : BitString) : ℕ∞ :=
  ⨅ (e : ℕ) (_ : PrintsPrefix e x), KPPlain U (Nat.bits e)

/-- **SUV Theorem 127 (a) (Section 6.1, printed p. 194).** If `x` is a prefix of `y`, then
`KR_M(x) ≤ KR_M(y)` for every decision decompressor `M`. A description of `y` is a description
of every prefix of `y` (`prefix_closed`). -/
theorem KROf_mono_of_prefix (M : DecisionDecompressor) {x y : BitString} (h : x <+: y) :
    KROf M x ≤ KROf M y :=
  sInf_le_sInf fun _ ⟨p, hp, hl⟩ => ⟨p, M.prefix_closed hp h, hl⟩

end GeneralScheme

end Kolmogorov
