import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic

/-!
# Common Information: Definitions
-/

namespace Kolmogorov

/-- A finite exact value of plain complexity. -/
def HasPlainComplexityValue (V : Map) (x : BitString) (k : Nat) : Prop :=
  plainK V x = (k : ENat)

/-- A finite exact value of plain conditional complexity. -/
def HasPlainConditionalComplexityValue (V : Map) (x y : BitString) (k : Nat) : Prop :=
  condK V x y = (k : ENat)

/-- Plain-complexity equivalence with an explicit two-way conditional budget. -/
def PlainEquivalentWithin (V : Map) (x y : BitString) (c : Nat) : Prop :=
  condK V x y <= (c : ENat) /\ condK V y x <= (c : ENat)

/-- `x` is incompressible up to `c`: its literal length is at most its plain
complexity plus the allowed deficiency. -/
def PlainIncompressibleWithin (V : Map) (x : BitString) (c : Nat) : Prop :=
  (x.length : ENat) <= plainK V x + (c : ENat)

/-- Plain complexity of a canonically encoded pair. -/
noncomputable def pairPlainK (V : Map) (x y : BitString) : ENat :=
  plainK V (pairCode x y)

/-- Additive, subtraction-free assertion that `x` and `y` have at least `m`
bits of mutual information. -/
def MutualInformationAtLeast (V : Map) (x y : BitString) (m : Nat) : Prop :=
  pairPlainK V x y + (m : ENat) <= plainK V x + plainK V y

def NatCloseWithin (a b d : Nat) : Prop :=
  a ≤ b + d ∧ b ≤ a + d

def commonInformationSlack (c d n : Nat) : Nat :=
  c * d + logSlack c n

def MutualInformationAtMost
    (V : Map) (x y : BitString) (m : Nat) : Prop :=
  plainK V x + plainK V y ≤ pairPlainK V x y + (m : ENat)

def MutualInformationEq
    (V : Map) (x y : BitString) (m : Nat) : Prop :=
  pairPlainK V x y + (m : ENat) = plainK V x + plainK V y

def MutualInformationWithin
    (V : Map) (x y : BitString) (m d : Nat) : Prop :=
  pairPlainK V x y + (m : ENat) ≤
      plainK V x + plainK V y + (d : ENat) ∧
  plainK V x + plainK V y ≤
      pairPlainK V x y + (m : ENat) + (d : ENat)

def ExtractableCommonInformationWithin
    (V : Map) (x y z : BitString) (m d : Nat) : Prop :=
  condK V z x ≤ (d : ENat) ∧
  condK V z y ≤ (d : ENat) ∧
  plainK V z ≤ (m + d : Nat) ∧
  (m : ENat) ≤ plainK V z + (d : ENat)

abbrev CommonInformationTriple := Nat × Nat × Nat

def CommonInformationRegion
    (V : Map) (x y : BitString) : Set CommonInformationTriple :=
  {t | ∃ z,
    plainK V z < (t.1 : ENat) ∧
    condK V x z < (t.2.1 : ENat) ∧
    condK V y z < (t.2.2 : ENat)}

def OverlapRepresentationWithin
    (V : Map) (x y u : BitString)
    (kx ky kxy d : Nat) : Prop :=
  ∃ lx ly,
    u.length = kxy ∧
    lx ≤ u.length ∧ ly ≤ u.length ∧
    NatCloseWithin lx kx d ∧
    NatCloseWithin ly ky d ∧
    PlainEquivalentWithin V x (u.take lx) d ∧
    PlainEquivalentWithin V y
      (u.drop (u.length - ly)) d ∧
    PlainEquivalentWithin V (pairCode x y) u d ∧
    PlainIncompressibleWithin V u d

def RawSharedDescriptionWithin
    (V : Map) (x y z a p b : BitString)
    (kx ky kxy m d : Nat) : Prop :=
  produces V p [] z ∧
  produces V a z x ∧
  produces V b z y ∧
  NatCloseWithin p.length m d ∧
  NatCloseWithin (a.length + p.length) kx d ∧
  NatCloseWithin (p.length + b.length) ky d ∧
  NatCloseWithin (a.length + p.length + b.length) kxy d

/-- Composing two common-information slack budgets can be absorbed into one
budget with a larger constant. -/
theorem commonInformationSlack_comp (c₁ c₂ : Nat) :
  ∃ C, ∀ d n,
    commonInformationSlack c₁
        (commonInformationSlack c₂ d n) n ≤
      commonInformationSlack C d n := by
  use c₁ * (c₂ + 1)
  intro d n
  unfold commonInformationSlack logSlack
  nlinarith [Nat.zero_le (c₁ * d)]

end Kolmogorov
