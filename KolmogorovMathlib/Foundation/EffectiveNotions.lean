import KolmogorovMathlib.Interface.StandardMachine
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Encoding.Tuples
import Mathlib.Computability.TuringDegree

/-!
# Effective notions: enumerability, semicomputability, oracles

Upper semicomputability of `ℕ∞`-valued functions, enumerable and decidable sets,
enumerable families of sets, Post simplicity, `r`-separability, decompressors
computable relative to an oracle, the oracle for the halting problem, and the
natural-number values `cVal`, `condCVal` of a complexity.

All definitions here are conservative reformulations of standard notions.
Asymptotic error terms elsewhere in the library are always expressed by explicit
existentially quantified constants, using `logSlack` for `O(log ·)` slack.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### Enumerability and semicomputability -/

/-- A set is *enumerable* (computably enumerable) if membership is an RE
predicate. -/
def IsEnumerableSet {α : Type*} [Primcodable α] (A : Set α) : Prop :=
  IsRE (fun a : α => a ∈ A)

/-- A set is *decidable* if its characteristic function is computable. -/
def IsDecidableSet {α : Type*} [Primcodable α] (A : Set α) : Prop :=
  ∃ f : α → Bool, Computable f ∧ ∀ a, f a = true ↔ a ∈ A

/-- A family `V : ℕ → Set α` is *enumerable* if the set of pairs
`{(n, a) | a ∈ V n}` is enumerable. -/
def IsEnumerableFamily {α : Type*} [Primcodable α] (V : ℕ → Set α) : Prop :=
  IsRE (fun p : ℕ × α => p.2 ∈ V p.1)

/-- A `ℕ∞`-valued function is *upper semicomputable* (enumerable from above) if
its upper graph `{(a, n) | f a < n}` is enumerable.  This is the standard
equivalent form of the definition by a computable nonincreasing approximation
`F (a, 0) ≥ F (a, 1) ≥ ⋯ → f a`. -/
def IsUpperSemicomputable {α : Type*} [Primcodable α] (f : α → ℕ∞) : Prop :=
  IsRE (fun p : α × ℕ => f p.1 < (p.2 : ℕ∞))

/-- A `ℕ∞`-valued function of two arguments is *upper semicomputable* if its
upper graph is enumerable. -/
def IsUpperSemicomputable₂ {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → β → ℕ∞) : Prop :=
  IsRE (fun p : α × β × ℕ => f p.1 p.2.1 < (p.2.2 : ℕ∞))

/-! ### Post simplicity and `r`-separability -/

/-- An enumerable set is *simple in the sense of Post* if its complement is
infinite but contains no infinite enumerable subset. -/
def IsPostSimple {α : Type*} [Primcodable α] (A : Set α) : Prop :=
  IsEnumerableSet A ∧ Aᶜ.Infinite ∧
    ∀ B : Set α, B ⊆ Aᶜ → IsEnumerableSet B → B.Finite

/-- A set `U` is *`r`-separable* if every enumerable set disjoint from `U` can be
separated from `U` by a decidable set. -/
def IsRSeparable {α : Type*} [Primcodable α] (U : Set α) : Prop :=
  ∀ V : Set α, IsEnumerableSet V → Disjoint U V →
    ∃ R : Set α, IsDecidableSet R ∧ V ⊆ R ∧ Disjoint U R

/-! ### Oracle computability -/

/-- The numerical version of a `Map`, obtained by encoding inputs and outputs;
this is the function that oracle computability statements talk about. -/
noncomputable def mapToNatFun (D : Map) : ℕ →. ℕ := fun n =>
  (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
    (fun a => (D a).map Encodable.encode)

/-- A decompressor computable with the oracle `O`. -/
def IsDecompressorIn (O : ℕ →. ℕ) (D : Map) : Prop :=
  RecursiveIn {O} (mapToNatFun D)

/-- Optimality of a conditional decompressor relative to an oracle `O`: it is
`O`-computable and not worse than any other `O`-computable decompressor. -/
def IsOptimalConditionalIn (O : ℕ →. ℕ) (U : Map) : Prop :=
  IsDecompressorIn O U ∧
    ∀ D, IsDecompressorIn O D → ∃ c : ℕ, ∀ x y, condK U x y ≤ condK D x y + (c : ℕ∞)

/-- The *semicharacteristic* function of the halting set: on input `e` it halts
exactly when the `e`-th partial computable function halts on input `e`, and
diverges otherwise.

This is **not** the halting oracle `0'`.  A query to a partial oracle that
diverges makes the querying computation diverge as well, so an oracle machine
with this oracle can only semi-decide halting; it cannot decide it, and
`RecursiveIn {haltingSemicharacteristic}` is strictly weaker than
`RecursiveIn {haltingOracle}`.  Use `haltingOracle` for the book's `0'`. -/
noncomputable def haltingSemicharacteristic : ℕ →. ℕ := fun e =>
  ((Denumerable.ofNat Code e).eval e).map (fun _ => 0)

open Classical in
/-- The oracle given by the (total) characteristic function of a set of naturals. -/
noncomputable def charOracle (A : Set ℕ) : ℕ →. ℕ := fun n =>
  Part.some (if n ∈ A then 1 else 0)

/-- The oracle for the halting problem, i.e. the book's `0'`: the *total*
characteristic function of `{e | φ_e (e) halts}`.  Every query returns, so an
oracle machine can branch on the answer and decide halting. -/
noncomputable def haltingOracle : ℕ →. ℕ :=
  charOracle {e : ℕ | ((Denumerable.ofNat Code e).eval e).Dom}

/-- A total function `ℕ → ℕ`, viewed as an oracle. -/
def totalOracle (g : ℕ → ℕ) : ℕ →. ℕ := fun n => Part.some (g n)

/-! ### Numeric value of a complexity -/

/-- The natural-number value of a plain complexity (`0` on the — for optimal
decompressors impossible — value `⊤`). -/
noncomputable def cVal (U : Map) (x : BitString) : ℕ := (plainK U x).toNat

/-- The natural-number value of a conditional complexity. -/
noncomputable def condCVal (U : Map) (x y : BitString) : ℕ := (condK U x y).toNat

/-- Binary encoding of a natural number as a bit string. -/
def natBits (n : ℕ) : BitString := Nat.bits n

end Kolmogorov
