/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Tuples.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import Mathlib.Computability.Partrec

/-!
# Stability of Kolmogorov properties under relativization: definitions

An. A. Muchnik and A. E. Romashchenko, *Stability of properties of Kolmogorov complexity under
relativization*, Problems of Information Transmission 46(1), 2010.  This file fixes the
vocabulary of the paper; the statements are in the other files of
`KolmogorovMathlib/Relativization/`.

Conventions.

* Complexities are plain complexities with respect to a decompressor `D`; every statement
  assumes `isOptimalConditional D`, so all of them are finite and we work with their values in
  `ℕ` (`natK`, `natCondK`).
* A finite oracle is a string `z`; relativizing to `z` puts `z` into every condition, and
  `K(a | b, z)` is `natCondK D a (pairCode b z)`.
* An `n`-tuple is a function `Fin n → BitString`; the subtuple `x_V` is coded by
  `subtupleCode x V`, and the tuple `⟨x̄, ȳ⟩` is `Fin.append x y`.
* `O(log N)` is `logSlack c N` with an existentially quantified constant `c`.
* `I(x̄ : z) ≤ δ` is written without subtraction as `K(x̄) ≤ K(x̄ | z) + δ`, the form of
  Proposition 1 of the paper.
-/

namespace Kolmogorov.Relativization

open Finset

variable {n m : ℕ}

/-! ### Natural-valued complexities -/

/-- Plain complexity `K(x)` as a natural number. -/
noncomputable def natK (D : Map) (x : BitString) : ℕ := (plainK D x).toNat

/-- Conditional plain complexity `K(x | y)` as a natural number. -/
noncomputable def natCondK (D : Map) (x y : BitString) : ℕ := (condK D x y).toNat

/-- `K(x_V)`: the complexity of a subtuple.  Section 3.1. -/
noncomputable def subK (D : Map) (x : Fin n → BitString) (V : Finset (Fin n)) : ℕ :=
  natK D (subtupleCode x V)

/-- `K(x_V | z)`: the complexity of a subtuple relativized to the oracle `z`.  Section 3.1. -/
noncomputable def subKRel (D : Map) (x : Fin n → BitString) (z : BitString)
    (V : Finset (Fin n)) : ℕ :=
  natCondK D (subtupleCode x V) z

/-- `K(x_V | x_W)`: a component of the extended complexity profile.  Definition 3. -/
noncomputable def subCondK (D : Map) (x : Fin n → BitString) (V W : Finset (Fin n)) : ℕ :=
  natCondK D (subtupleCode x V) (subtupleCode x W)

/-- `K(x_V | x_W, z)`: a component of the extended complexity profile relativized to `z`.
Definition 3. -/
noncomputable def subCondKRel (D : Map) (x : Fin n → BitString) (z : BitString)
    (V W : Finset (Fin n)) : ℕ :=
  natCondK D (subtupleCode x V) (pairCode (subtupleCode x W) z)

/-- `I(x : z) ≤ δ`, in the form `K(x) ≤ K(x | z) + δ`. -/
def MutualInfoLe (D : Map) (x z : BitString) (δ : ℕ) : Prop :=
  natK D x ≤ natCondK D x z + δ

/-! ### Complexity profiles (Definitions 2 and 3) -/

/-- Two complexity profiles, indexed by the non-empty subsets of `{1, …, n}`, are at distance at
most `d` in the `l∞` norm.  Section 3.1. -/
def ProfileWithin (a b : Finset (Fin n) → ℕ) (d : ℕ) : Prop :=
  ∀ V : Finset (Fin n), V.Nonempty → a V ≤ b V + d ∧ b V ≤ a V + d

/-- Two extended complexity profiles, indexed by the pairs `(V, W)` of disjoint subsets of
`{1, …, n}` with `V ≠ ∅`, are at distance at most `d` in the `l∞` norm.  Section 3.1. -/
def ExtProfileWithin (a b : Finset (Fin n) → Finset (Fin n) → ℕ) (d : ℕ) : Prop :=
  ∀ V W : Finset (Fin n), V.Nonempty → Disjoint V W → a V W ≤ b V W + d ∧ b V W ≤ a V W + d

/-- The extended complexity profile of `a` is componentwise not greater than that of `b`:
`K(a_V | a_W) ≤ K(b_V | b_W)` for all disjoint `V, W` with `V ≠ ∅`.  Section 3.1. -/
def ExtProfileLe (D : Map) (a b : Fin n → BitString) : Prop :=
  ∀ V W : Finset (Fin n), V.Nonempty → Disjoint V W → subCondK D a V W ≤ subCondK D b V W

/-! ### Typization (Definition 4) -/

/-- The typization `T(x̄ | ȳ)`: the tuples `x̄'` with `K'(x̄', ȳ) ≤ K'(x̄, ȳ)`.  Definition 4. -/
def typization (D : Map) (x : Fin n → BitString) (y : Fin m → BitString) :
    Set (Fin n → BitString) :=
  {x' | ExtProfileLe D (Fin.append x' y) (Fin.append x y)}

/-- The `k`-strong typization `ST_k(x̄ | ȳ)`: the members of `T(x̄ | ȳ)` whose extended profile
is at `l∞`-distance at most `k` from that of `⟨x̄, ȳ⟩`.  Definition 4. -/
def strongTypization (D : Map) (k : ℕ) (x : Fin n → BitString) (y : Fin m → BitString) :
    Set (Fin n → BitString) :=
  {x' | ExtProfileLe D (Fin.append x' y) (Fin.append x y) ∧
    ∀ V W : Finset (Fin (n + m)), V.Nonempty → Disjoint V W →
      subCondK D (Fin.append x y) V W ≤ subCondK D (Fin.append x' y) V W + k}

/-! ### Combinatorial entropy (Definition 5) -/

/-- `π_V σ_W(A | u_W)`: the `V`-projection of the section of `A` over the value `u_W` of the
`W`-coordinates, as a set of subtuple codes.  Section 3.3. -/
def sectionProjection (A : Finset (Fin n → BitString)) (V W : Finset (Fin n))
    (u : Fin n → BitString) : Finset BitString :=
  (A.filter fun a => subtupleCode a W = subtupleCode u W).image fun a => subtupleCode a V

/-- `n_{V|W}(A)`: the largest size of the `V`-projection of a `W`-section of `A`.
Section 3.3. -/
def maxSectionCard (A : Finset (Fin n → BitString)) (V W : Finset (Fin n)) : ℕ :=
  A.sup fun u => (sectionProjection A V W u).card

/-- The combinatorial entropy `ent_{V|W}(A) = ⌈log n_{V|W}(A)⌉`.  Definition 5. -/
def combEnt (A : Finset (Fin n → BitString)) (V W : Finset (Fin n)) : ℕ :=
  Nat.clog 2 (maxSectionCard A V W)

/-- The code of a finite set of strings: its ordered list. -/
def finsetListCode (A : Finset BitString) : BitString := listCode (canonicalFinsetList A)

/-- `list(A)`: the code of a finite set of `n`-tuples.  Lemma 4. -/
def tupleSetCode (A : Finset (Fin n → BitString)) : BitString :=
  finsetListCode (A.image tupleCode)

/-! ### Stochastic strings and equivalence (Definition 1 and Section 2) -/

/-- `x` is `(α, β)`-stochastic: there is a finite set `A ∋ x` whose ordered list has complexity
at most `α` and with `K(x | list A) ≥ log |A| − β`.  Definition 1. -/
def IsSetStochastic (D : Map) (x : BitString) (α β : ℕ) : Prop :=
  ∃ A : Finset BitString, x ∈ A ∧ natK D (finsetListCode A) ≤ α ∧
    A.card ≤ 2 ^ (natCondK D x (finsetListCode A) + β)

/-- An `n`-tuple is `(α, β)`-stochastic when its code is.  Definition 1. -/
def IsStochasticTuple (D : Map) (x : Fin n → BitString) (α β : ℕ) : Prop :=
  IsSetStochastic D (tupleCode x) α β

/-- `a ∼_C b`: each of the two strings is simple given the other, with threshold
`O(log K(a, b))` and constant `C`.  Section 2. -/
def EquivWithin (D : Map) (C : ℕ) (a b : BitString) : Prop :=
  natCondK D a b ≤ logSlack C (natK D (pairCode a b)) ∧
    natCondK D b a ≤ logSlack C (natK D (pairCode a b))

/-! ### Bunches (Definitions 6 and 7) -/

/-- An `(α, β, γ)`-bunch.  Definition 6. -/
def IsBunch (D : Map) (α β γ : ℕ) (X : Finset BitString) : Prop :=
  X.card = 2 ^ α ∧ (∀ x₁ ∈ X, ∀ x₂ ∈ X, natCondK D x₁ x₂ < β) ∧ ∀ x ∈ X, natK D x < γ

open scoped Classical in
/-- An `(α, β, γ)`-semi-bunch: for each `x₁ ∈ X` more than half of the `x₂ ∈ X` satisfy
`K(x₂ | x₁) < β`.  Definition 7. -/
def IsSemiBunch (D : Map) (α β γ : ℕ) (X : Finset BitString) : Prop :=
  X.card = 2 ^ α ∧
    (∀ x₁ ∈ X, X.card < 2 * (X.filter fun x₂ => natCondK D x₂ x₁ < β).card) ∧
    ∀ x ∈ X, natK D x < γ

/-- The conclusion shared by Lemmas 5 and 6 for a class `P α β γ` of finite sets of strings:
there is a constant `c` and a list `U α β γ 0, …, U α β γ (cnt α β γ - 1)` of members of the
class, produced by an algorithm from `(α, β, γ)`, such that every member `X` of the class meets
some `U α β γ i` in at least `2 ^ (2α − β − c)` points, and the list has at most
`2 ^ (β + γ − 2α + c)` entries.  "Produced by an algorithm" means that a partial computable
function `F` is defined at `(α, β, γ, i)` exactly when `i < cnt α β γ`, and then its value is the
ordered list of `U α β γ i`: computing `F (α, β, γ, 0), F (α, β, γ, 1), …` enumerates the list
and nothing else.  The list may be empty, and the algorithm need not know its length. -/
def HasStandardCover (P : ℕ → ℕ → ℕ → Finset BitString → Prop) : Prop :=
  ∃ c : ℕ, ∃ cnt : ℕ → ℕ → ℕ → ℕ, ∃ U : ℕ → ℕ → ℕ → ℕ → Finset BitString,
    (∃ F : ℕ × ℕ × ℕ × ℕ →. BitString, Partrec F ∧
      ∀ α β γ i : ℕ, ∀ s : BitString,
        s ∈ F (α, β, γ, i) ↔ i < cnt α β γ ∧ s = finsetListCode (U α β γ i)) ∧
    ∀ α β γ : ℕ,
      (∀ i < cnt α β γ, P α β γ (U α β γ i)) ∧
      (∀ X : Finset BitString, P α β γ X →
        ∃ i < cnt α β γ, 2 ^ (2 * α) ≤ (X ∩ U α β γ i).card * 2 ^ (β + c)) ∧
      cnt α β γ * 2 ^ (2 * α) ≤ 2 ^ (β + γ + c)

/-! ### Extracting common information (Section 1) -/

/-- `q` bits of common information can be extracted from `x₁, x₂` for the threshold `k`:
`∃ w, K(w) ≥ q` and `K(w | xᵢ) ≤ k`. -/
def CommonInfoExtractable (D : Map) (x₁ x₂ : BitString) (q k : ℕ) : Prop :=
  ∃ w : BitString, q ≤ natK D w ∧ natCondK D w x₁ ≤ k ∧ natCondK D w x₂ ≤ k

/-- `q` bits of common information can be extracted from `x₁, x₂` for the threshold `k` with the
oracle `z`: `∃ v, K(v | z) ≥ q` and `K(v | xᵢ, z) ≤ k`. -/
def CommonInfoExtractableRel (D : Map) (x₁ x₂ z : BitString) (q k : ℕ) : Prop :=
  ∃ v : BitString, q ≤ natCondK D v z ∧
    natCondK D v (pairCode x₁ z) ≤ k ∧ natCondK D v (pairCode x₂ z) ≤ k

/-! ### The open conjectures -/

/-- **Conjecture 2** of the paper (open).  For every `C₁` there is a `C₂` such that for all
`x₁, x₂, z` with `N = K(x₁, x₂, z)`: if `I(z : x̄) ≤ C₁ log N` and `q` bits of common information
can be extracted from `x₁, x₂` with the oracle `z` for the threshold `C₁ log N`, then the same
`q` bits can be extracted without the oracle for the threshold `C₂ log N`. -/
def Conjecture2 (D : Map) : Prop :=
  ∀ C₁ : ℕ, ∃ C₂ : ℕ, ∀ (x₁ x₂ z : BitString) (q : ℕ),
    MutualInfoLe D (pairCode x₁ x₂) z
        (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      CommonInfoExtractableRel D x₁ x₂ z q
        (logSlack C₁ (natK D (pairCode (pairCode x₁ x₂) z))) →
      CommonInfoExtractable D x₁ x₂ q (logSlack C₂ (natK D (pairCode (pairCode x₁ x₂) z)))

/-- **Conjecture 3** of the paper (open).  If `I(x̄ : z) ≤ δ`, then for every `ȳ` there is a
`ȳ'` such that the complexity profiles `K(x̄, ȳ | z)` and `K(x̄, ȳ')` differ componentwise by at
most `δ + O(log K(x̄, ȳ, z))`; the constant depends on the lengths of the tuples only. -/
def Conjecture3 (D : Map) : Prop :=
  ∀ n m : ℕ, ∃ c : ℕ, ∀ (x : Fin n → BitString) (z : BitString) (δ : ℕ),
    MutualInfoLe D (tupleCode x) z δ →
      ∀ y : Fin m → BitString, ∃ y' : Fin m → BitString,
        ProfileWithin (subKRel D (Fin.append x y) z) (subK D (Fin.append x y'))
          (δ + logSlack c (natK D (pairCode (tupleCode (Fin.append x y)) z)))

end Kolmogorov.Relativization
