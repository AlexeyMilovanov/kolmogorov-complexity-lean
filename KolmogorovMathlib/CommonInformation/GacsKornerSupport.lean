import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Relation

/-!
# Support blocks and common functions (Gács–Körner combinatorial core)

The Gács–Körner criterion for extractable common information is combinatorial:
a joint weight function `P : A → B → ℝ` admits a nonconstant function of `a`
that agrees on the support with a function of `b` exactly when its support
splits into (at least) two combinatorial blocks.

This file proves the finite two-block form of that equivalence.  Only the
support `{(a, b) | 0 < P a b}` matters; no probabilistic hypotheses are used.
-/

namespace Kolmogorov

/-- A support-block splitting is equivalent to a nonconstant Boolean function
of `a` that agrees on the support with a Boolean function of `b`. -/
theorem supportBlock_iff_exists_nontrivial_bool_commonFunction
    {A B : Type*} [Finite A] [Finite B] (P : A → B → ℝ) :
    (∃ L : Finset A, ∃ R : Finset B,
        (∀ a b, 0 < P a b → (a ∈ L ↔ b ∈ R)) ∧
        (∃ a b, a ∈ L ∧ b ∈ R ∧ 0 < P a b) ∧
        (∃ a b, a ∉ L ∧ b ∉ R ∧ 0 < P a b)) ↔
    (∃ left : A → Bool, ∃ right : B → Bool,
        (∀ a b, 0 < P a b → left a = right b) ∧
        ∃ a₀ b₀ a₁ b₁,
          0 < P a₀ b₀ ∧ 0 < P a₁ b₁ ∧ left a₀ ≠ left a₁) := by
  classical
  cases nonempty_fintype A
  cases nonempty_fintype B
  constructor
  · rintro ⟨L, R, hiff, ⟨a₀, b₀, ha₀, hb₀, hP₀⟩, ⟨a₁, b₁, ha₁, hb₁, hP₁⟩⟩
    refine ⟨fun a => decide (a ∈ L), fun b => decide (b ∈ R), ?_,
      a₀, b₀, a₁, b₁, hP₀, hP₁, ?_⟩
    · intro a b hab
      simp [hiff a b hab]
    · simp [ha₀, ha₁]
  · rintro ⟨left, right, hagree, a₀, b₀, a₁, b₁, hP₀, hP₁, hne⟩
    refine ⟨Finset.univ.filter fun a => left a = left a₀,
      Finset.univ.filter fun b => right b = left a₀, ?_, ?_, ?_⟩
    · intro a b hab
      simp [Finset.mem_filter, hagree a b hab]
    · exact ⟨a₀, b₀, by simp, by simp [(hagree a₀ b₀ hP₀).symm], hP₀⟩
    · exact ⟨a₁, b₁, by simp [Ne.symm hne], by simp [(hagree a₁ b₁ hP₁).symm, Ne.symm hne], hP₁⟩

/-- Two rows `a`, `a'` are *linked* when some column `b` lies in the support of
both of them. -/
def SupportLink {A B : Type*} (P : A → B → ℝ) (a a' : A) : Prop :=
  ∃ b, 0 < P a b ∧ 0 < P a' b

/-- Reachability in the support graph: the reflexive transitive closure of
`SupportLink`.  Two rows are related exactly when they are joined by a chain of
support entries. -/
def SupportReach {A B : Type*} (P : A → B → ℝ) : A → A → Prop :=
  Relation.ReflTransGen (SupportLink P)

theorem supportReach_refl {A B : Type*} (P : A → B → ℝ) (a : A) : SupportReach P a a :=
  Relation.ReflTransGen.refl

theorem supportReach_tail {A B : Type*} {P : A → B → ℝ} {a a' a'' : A}
    (h : SupportReach P a a') (hlink : SupportLink P a' a'') : SupportReach P a a'' :=
  Relation.ReflTransGen.tail h hlink

/-- A common function is constant along support-connected rows: this is the
"easy" half of the Gács–Körner criterion, valid for values in an arbitrary
type. -/
theorem commonFunction_eq_of_supportReach {A B C : Type*} (P : A → B → ℝ)
    (left : A → C) (right : B → C) (hagree : ∀ a b, 0 < P a b → left a = right b)
    {a a' : A} (h : SupportReach P a a') : left a = left a' := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
    obtain ⟨b, hb1, hb2⟩ := hlast
    exact ih.trans ((hagree _ b hb1).trans (hagree _ b hb2).symm)

/-- The general Gács–Körner criterion in graph form: a nonconstant Boolean
common function exists exactly when the support graph is disconnected, i.e.
some two rows meeting the support are not joined by a chain of support
entries.  No finiteness hypothesis is needed. -/
theorem exists_nontrivial_bool_commonFunction_iff_not_supportReach
    {A B : Type*} (P : A → B → ℝ) :
    (∃ left : A → Bool, ∃ right : B → Bool,
        (∀ a b, 0 < P a b → left a = right b) ∧
        ∃ a₀ b₀ a₁ b₁,
          0 < P a₀ b₀ ∧ 0 < P a₁ b₁ ∧ left a₀ ≠ left a₁) ↔
    (∃ a₀ b₀ a₁ b₁, 0 < P a₀ b₀ ∧ 0 < P a₁ b₁ ∧ ¬ SupportReach P a₀ a₁) := by
  classical
  constructor
  · rintro ⟨left, right, hagree, a₀, b₀, a₁, b₁, h0, h1, hne⟩
    exact ⟨a₀, b₀, a₁, b₁, h0, h1, fun hreach =>
      hne (commonFunction_eq_of_supportReach P left right hagree hreach)⟩
  · rintro ⟨a₀, b₀, a₁, b₁, h0, h1, hreach⟩
    refine ⟨fun a => decide (SupportReach P a₀ a),
      fun b => decide (∃ a, 0 < P a b ∧ SupportReach P a₀ a), ?_,
      a₀, b₀, a₁, b₁, h0, h1, ?_⟩
    · intro a b hab
      have key : SupportReach P a₀ a ↔ ∃ a', 0 < P a' b ∧ SupportReach P a₀ a' :=
        ⟨fun h => ⟨a, hab, h⟩, fun ⟨a', hab', h'⟩ => supportReach_tail h' ⟨b, hab', hab⟩⟩
      simp [key]
    · simp only [ne_eq, decide_eq_decide]
      simp [hreach, supportReach_refl P a₀]

/-- Combining the two criteria: the support of a finite joint weight function
splits into two combinatorial blocks exactly when its support graph is
disconnected. -/
theorem supportBlock_iff_not_supportReach
    {A B : Type*} [Finite A] [Finite B] (P : A → B → ℝ) :
    (∃ L : Finset A, ∃ R : Finset B,
        (∀ a b, 0 < P a b → (a ∈ L ↔ b ∈ R)) ∧
        (∃ a b, a ∈ L ∧ b ∈ R ∧ 0 < P a b) ∧
        (∃ a b, a ∉ L ∧ b ∉ R ∧ 0 < P a b)) ↔
    (∃ a₀ b₀ a₁ b₁, 0 < P a₀ b₀ ∧ 0 < P a₁ b₁ ∧ ¬ SupportReach P a₀ a₁) :=
  (supportBlock_iff_exists_nontrivial_bool_commonFunction P).trans
    (exists_nontrivial_bool_commonFunction_iff_not_supportReach P)

end Kolmogorov
