import KolmogorovMathlib.Core.UniversalDecompressor
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.PairComplexity.Basic
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Problems, operations on problems and their complexity (SUV §13.1)

Shen–Uspensky–Vereshchagin, Chapter 13, "Information and logic".  A *problem* is an arbitrary
set of bit strings (its *solutions*); its complexity is the minimal plain complexity of a
solution, `+∞` for the empty problem.

The operations on problems depend on a pairing function `[x, y]`, on two tags (`0`, `1`) and on
a programming language `[p](x)` with the Gödel property.  The book fixes one such choice and
remarks (Problem 339) that every other choice changes complexities only by `O(1)`.  We bundle
the choice in `ProblemCalculus`; `ProblemCalculus.Admissible` lists the book's assumptions, and
every theorem of the chapter is stated for an arbitrary admissible calculus.  The concrete
calculus `std L` uses the library pair code `pairCode`, the tags `[false]`, `[true]` and a
Gödel language `L` (its admissibility is `std_admissible` in `Bridges`).

A programming language is a `Map` (the library's type of partial maps
`BitString × BitString →. BitString`), read as `L (p, x) = [p](x)`.
-/

namespace Kolmogorov
namespace InformationLogic

/-! ### Complexity of a problem -/

/-- SUV §13.1 (printed p. 401): the complexity of a problem `X` (a set of strings) with respect
to the decompressor `D`, `C(X) = min {C(x) | x ∈ X}`; the empty problem has complexity `⊤`. -/
noncomputable def problemK (D : Map) (X : Set BitString) : ℕ∞ := ⨅ x ∈ X, plainK D x

/-- SUV Section 13.1, definition of `C(X)` (printed p. 401).  The unsolvable (empty) problem
has complexity `+∞` ("As usual, the empty set, i.e., the unsolvable problem, has complexity
`+∞`"): the infimum over the empty set is `⊤`. -/
@[simp] theorem problemK_empty (D : Map) : problemK D ∅ = ⊤ := by simp [problemK]

/-- SUV Section 13.1, example after the definition of `C(X)` (printed p. 401).  The complexity
of a singleton `{x}` is the complexity of the string `x`: the infimum has one term. -/
@[simp] theorem problemK_singleton (D : Map) (x : BitString) : problemK D {x} = plainK D x := by
  simp [problemK]

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 401).  A solution bounds
the complexity of the problem from above: `C(X) ≤ C(x)` for `x ∈ X`, by the definition of
`C(X)` as a minimum. -/
theorem problemK_le_of_mem (D : Map) {X : Set BitString} {x : BitString} (hx : x ∈ X) :
    problemK D X ≤ plainK D x :=
  biInf_le _ hx

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 401).  A problem with
more solutions is simpler: `X ⊆ Y` gives `C(Y) ≤ C(X)` (a minimum over a larger set). -/
theorem problemK_mono (D : Map) {X Y : Set BitString} (h : X ⊆ Y) :
    problemK D Y ≤ problemK D X :=
  biInf_mono h

/-- Auxiliary lemma, not a numbered SUV item (Section 13.1, printed p. 401).  The minimum in the
definition of `problemK` is attained on a nonempty problem (`ℕ∞` is well ordered). -/
theorem exists_mem_plainK_eq_problemK (D : Map) {X : Set BitString} (hX : X.Nonempty) :
    ∃ x ∈ X, plainK D x = problemK D X := by
  obtain ⟨x, hx, hxeq⟩ := csInf_mem (hX.image (plainK D))
  exact ⟨x, hx, by rw [hxeq, problemK, sInf_image]⟩

/-! ### Programming languages with the Gödel property -/

/-- SUV §13.1 (printed p. 402): a programming language `L`, read as `[p](x) = L (p, x)`, is
universal and has the *Gödel property*: it is partial computable, and every partial computable
language `V` can be translated into it by a total computable translation `t`,
`[t(s)]_L(x) = V(s, x)` for all `s, x`.  (Universality is the special case `V (s, x) = f x`,
which ignores its program.) -/
def IsGodelLang (L : Map) : Prop :=
  Partrec L ∧ ∀ V : Map, Partrec V →
    ∃ t : BitString → BitString, Computable t ∧ ∀ s x, L (t s, x) = V (s, x)

/-! ### Problem calculi: pairing, tags, programming language -/

/-- The data the operations on problems depend on (SUV §13.2, printed p. 404): a pairing
function with its inverse, the two tags of the disjunction and a programming language. -/
structure ProblemCalculus where
  /-- The pairing function `[x, y]`. -/
  pair : BitString → BitString → BitString
  /-- Its inverse: `unpair z = some (x, y)` iff `z = [x, y]`. -/
  unpair : BitString → Option (BitString × BitString)
  /-- The tag of the left disjunct (the book's `0`). -/
  tag0 : BitString
  /-- The tag of the right disjunct (the book's `1`). -/
  tag1 : BitString
  /-- The programming language: `lang (p, x) = [p](x)`. -/
  lang : Map

namespace ProblemCalculus

/-- The book's assumptions on a calculus (SUV §13.2, printed p. 404): the pairing function is a
computable injection with a computable inverse on its decidable range (the book asks for
computable bijections; only injectivity and the computable inverse are used), the tags differ,
and the language has the Gödel property. -/
def Admissible (P : ProblemCalculus) : Prop :=
  Computable₂ P.pair ∧ Computable P.unpair ∧
    (∀ x y, P.unpair (P.pair x y) = some (x, y)) ∧
    (∀ z x y, P.unpair z = some (x, y) → P.pair x y = z) ∧
    P.tag0 ≠ P.tag1 ∧ IsGodelLang P.lang

/-- SUV §13.1 (printed p. 401): the conjunction `X ∧ Y = {[x, y] | x ∈ X, y ∈ Y}`. -/
def conj (P : ProblemCalculus) (X Y : Set BitString) : Set BitString :=
  Set.image2 P.pair X Y

/-- SUV §13.1 (printed p. 401): the disjunction
`X ∨ Y = {[0, x] | x ∈ X} ∪ {[1, y] | y ∈ Y}`. -/
def disj (P : ProblemCalculus) (X Y : Set BitString) : Set BitString :=
  P.pair P.tag0 '' X ∪ P.pair P.tag1 '' Y

/-- SUV §13.1 (printed p. 402): the pseudo-disjunction `X ∨~ Y = {[x, y] | x ∈ X or y ∈ Y}`. -/
def pdisj (P : ProblemCalculus) (X Y : Set BitString) : Set BitString :=
  {z | ∃ x y, P.pair x y = z ∧ (x ∈ X ∨ y ∈ Y)}

/-- SUV §13.1 (printed p. 402): the implication `X → Y`, the set of programs `p` such that for
every `x ∈ X` the value `[p](x)` is defined and belongs to `Y`. -/
def imp (P : ProblemCalculus) (X Y : Set BitString) : Set BitString :=
  {p | ∀ x ∈ X, ∃ y ∈ Y, y ∈ P.lang (p, x)}

end ProblemCalculus

/-! ### The standard calculus -/

/-- The inverse of the library pair code: `pairUnpair z = some (x, y)` iff `z = pairCode x y`. -/
def pairUnpair (z : BitString) : Option (BitString × BitString) :=
  if pairCode (decodeFirst z) (decodeSecond z) = z then some (decodeFirst z, decodeSecond z)
  else none

/-- The standard calculus over a language `L`: the pair code `pairCode`, the tags `[false]`
(the book's `0`) and `[true]` (the book's `1`). -/
def std (L : Map) : ProblemCalculus where
  pair := pairCode
  unpair := pairUnpair
  tag0 := [false]
  tag1 := [true]
  lang := L

/-! ### Algorithmic reducibility of problems -/

/-- `X` reduces to `Y` if one partial computable function maps every solution of `X` to some
solution of `Y` (SUV §13.5, printed p. 414: "algorithmically equivalent" is reducibility in both
directions). -/
def ProblemReduces (X Y : Set BitString) : Prop :=
  ∃ f : BitString →. BitString, Partrec f ∧ ∀ x ∈ X, ∃ y ∈ Y, y ∈ f x

/-- SUV §13.5 (printed p. 414): algorithmic equivalence of problems. -/
def ProblemEquiv (X Y : Set BitString) : Prop :=
  ProblemReduces X Y ∧ ProblemReduces Y X

end InformationLogic
end Kolmogorov
