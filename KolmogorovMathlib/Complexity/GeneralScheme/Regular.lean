import KolmogorovMathlib.MonotoneComplexity.ConsistentRelationComplexity

/-!
# Regular relations: the α-β description modes of SUV Sections 6.2 and 6.3

SUV Section 6.2 (printed p. 197) describes the four complexities `C`, `K`, `KM`, `KR` uniformly.
Bit strings carry two relations, equality `=` and compatibility `≍` (one string is a prefix of
the other). For `α, β ∈ {=, ≍}` a relation `R` between descriptions and objects is
*α-β-regular* if `R p₁ x₁`, `R p₂ x₂` and `p₁ α p₂` imply `x₁ β x₂`. An *α-β description mode*
is an enumerable α-β-regular relation. Its complexity `modeComplexity R x` is the least length
of a `p` with `R p x`. Section 6.3 (printed p. 200) does the same for triples
`⟨description, object, condition⟩` with a third relation `γ` on conditions.

The relation is a predicate `R p x` (description first, object second), as in
`consistentRelationKMOf`. The ≍-≍ case is the library's `IsConsistentStreamRelation`
(`isRegular_compat_compat_iff`), and `modeComplexity` is `consistentRelationKMOf`
(`modeComplexity_eq_consistentRelationKMOf`).
-/

namespace Kolmogorov

namespace GeneralScheme

/-- The two relations on bit strings of SUV Section 6.2: equality `=` and compatibility `≍`. -/
inductive StrRel
  | eq
  | compat
  deriving DecidableEq

/-- The meaning of `StrRel`: `eq` is equality, `compat` says that one string is a prefix of the
other. -/
def StrRel.Holds : StrRel → BitString → BitString → Prop
  | .eq, x, y => x = y
  | .compat, x, y => x <+: y ∨ y <+: x

/-- **SUV Section 6.2 (printed p. 197), helper.** Every relation of the scheme is reflexive:
`x = x`, and `x` is compatible with itself. -/
theorem StrRel.holds_refl (α : StrRel) (x : BitString) : α.Holds x x := by
  cases α
  · rfl
  · exact Or.inl (List.prefix_refl x)

/-- **SUV Section 6.2 (printed p. 197), helper.** Equality implies every relation of the scheme
(by reflexivity). -/
theorem StrRel.holds_of_eq (α : StrRel) {x y : BitString} (h : x = y) : α.Holds x y :=
  h ▸ α.holds_refl x

/-- SUV Section 6.2: `R` (descriptions first) is *α-β-regular* if `R p₁ x₁`, `R p₂ x₂` and
`p₁ α p₂` imply `x₁ β x₂`. -/
def IsRegular (α β : StrRel) (R : BitString → BitString → Prop) : Prop :=
  ∀ ⦃p₁ x₁ p₂ x₂ : BitString⦄, R p₁ x₁ → R p₂ x₂ → α.Holds p₁ p₂ → β.Holds x₁ x₂

/-- An *α-β description mode* (SUV Section 6.2): an enumerable α-β-regular relation. -/
def IsDescriptionMode (α β : StrRel) (R : BitString → BitString → Prop) : Prop :=
  IsRE (fun q : BitString × BitString => R q.1 q.2) ∧ IsRegular α β R

/-- The complexity `K_R(x)` of a description mode: the least length of a description `p` with
`R p x`, and `⊤` if there is none. -/
noncomputable def modeComplexity (R : BitString → BitString → Prop) (x : BitString) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ p, R p x ∧ l = p.length}

/-- An optimal α-β description mode: a description mode whose complexity is minimal up to an
additive constant among all α-β description modes. -/
def IsOptimalDescriptionMode (α β : StrRel) (R : BitString → BitString → Prop) : Prop :=
  IsDescriptionMode α β R ∧
    ∀ S, IsDescriptionMode α β S → ∃ c : ℕ, ∀ x, modeComplexity R x ≤ modeComplexity S x + c

/-- **SUV Section 6.2 (printed p. 197), helper.** The ≍-≍-regular relations are the consistent
stream relations of SUV Problem 137. The two definitions differ only in the order of the
arguments. -/
theorem isRegular_compat_compat_iff (R : BitString → BitString → Prop) :
    IsRegular .compat .compat R ↔ IsConsistentStreamRelation R :=
  ⟨fun h _ _ _ _ h₁ h₂ hx => h h₁ h₂ hx, fun h p₁ x₁ p₂ x₂ h₁ h₂ hp => h p₁ p₂ x₁ x₂ h₁ h₂ hp⟩

/-- **SUV Section 6.2 (printed p. 198), helper.** The complexity `K_S` of a description mode is
the library's `consistentRelationKMOf` (same formula, by definition). -/
theorem modeComplexity_eq_consistentRelationKMOf (R : BitString → BitString → Prop)
    (x : BitString) : modeComplexity R x = consistentRelationKMOf R x :=
  rfl

/-- **SUV Section 6.2 (printed p. 198), helper.** A description gives an upper bound for the
complexity: `R p x` implies `K_R(x) ≤ l(p)` (definition of `K_R` as a minimum). -/
theorem modeComplexity_le_length {R : BitString → BitString → Prop} {p x : BitString}
    (h : R p x) : modeComplexity R x ≤ p.length :=
  sInf_le ⟨p, h, rfl⟩

/-! ### Conditional description modes (SUV Section 6.3) -/

/-- SUV Section 6.3: a set `S` of triples `⟨p, x, y⟩` (description, object, condition) is
`(α, β) | γ`-regular if `S p₁ x₁ y₁`, `S p₂ x₂ y₂`, `p₁ α p₂` and `y₁ γ y₂` imply `x₁ β x₂`. -/
def IsCondRegular (α β γ : StrRel) (S : BitString → BitString → BitString → Prop) : Prop :=
  ∀ ⦃p₁ x₁ y₁ p₂ x₂ y₂ : BitString⦄, S p₁ x₁ y₁ → S p₂ x₂ y₂ → α.Holds p₁ p₂ → γ.Holds y₁ y₂ →
    β.Holds x₁ x₂

/-- An `(α, β) | γ`-decompressor (SUV Section 6.3): an enumerable `(α, β) | γ`-regular set of
triples. -/
def IsCondDescriptionMode (α β γ : StrRel) (S : BitString → BitString → BitString → Prop) :
    Prop :=
  IsRE (fun q : BitString × BitString × BitString => S q.1 q.2.1 q.2.2) ∧ IsCondRegular α β γ S

/-- `K_S(x | y)`: the least length of a `p` with `S p x y`, and `⊤` if there is none. -/
noncomputable def condModeComplexity (S : BitString → BitString → BitString → Prop)
    (x y : BitString) : ℕ∞ :=
  sInf {l : ℕ∞ | ∃ p, S p x y ∧ l = p.length}

/-- An optimal `(α, β) | γ`-decompressor: minimal conditional complexity up to an additive
constant among all `(α, β) | γ`-decompressors. -/
def IsOptimalCondDescriptionMode (α β γ : StrRel)
    (S : BitString → BitString → BitString → Prop) : Prop :=
  IsCondDescriptionMode α β γ S ∧
    ∀ T, IsCondDescriptionMode α β γ T →
      ∃ c : ℕ, ∀ x y, condModeComplexity S x y ≤ condModeComplexity T x y + c

/-- **SUV Problem 201 (Section 6.3, printed p. 201), helper.** Compatibility of conditions is a
stronger requirement than equality: an `(α, β) | ≍`-decompressor is an
`(α, β) | =`-decompressor, because equal conditions are compatible. -/
theorem IsCondDescriptionMode.of_compat {α β : StrRel}
    {S : BitString → BitString → BitString → Prop}
    (h : IsCondDescriptionMode α β .compat S) : IsCondDescriptionMode α β .eq S :=
  ⟨h.1, fun _ _ _ _ _ _ h₁ h₂ hp hy => h.2 h₁ h₂ hp (StrRel.holds_of_eq _ hy)⟩

end GeneralScheme

end Kolmogorov
