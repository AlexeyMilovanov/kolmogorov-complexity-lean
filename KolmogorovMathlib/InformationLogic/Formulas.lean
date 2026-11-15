import KolmogorovMathlib.InformationLogic.Problems

/-!
# Propositional formulas, intuitionistic provability, Kripke models (SUV §§13.2, 13.4, 13.5)

Formulas of SUV Chapter 13 are built from variables with `∧`, `∨`, `→` only (no `⊥`, no
negation).  Substituting problems for the variables gives a problem (`PFormula.eval`).

*Provability in IPC.*  For negation-free formulas, provability in intuitionistic propositional
calculus coincides with provability in its positive fragment (IPC is conservative over positive
logic).  `PFormula.Provable` is the standard Hilbert system of positive intuitionistic logic:
the axiom schemes of `→`, `∧`, `∨` and modus ponens.

*Kripke models.*  A Kripke model is a preorder of worlds with a monotone valuation; forcing of
`A → B` at `w` quantifies over all worlds above `w`.  Chapter 13 uses finite rooted partial
orders (SUV §13.5, printed p. 414).

*Critical implications* (SUV §13.4, printed p. 412):
`((P₁ → Q₁) → Q₁) ∧ … ∧ ((P_N → Q_N) → Q_N) → R`, `R` the disjunction of all variables
`s₁ … s_k`, `P_l` a conjunction and `Q_l` a disjunction of nonempty disjoint sets of variables.
Multiple conjunctions and disjunctions are nested to the right, as in the book's technical note
(printed p. 410).
-/

namespace Kolmogorov
namespace InformationLogic

/-- Propositional formulas with connectives `∧`, `∨`, `→` over variables of type `ι`. -/
inductive PFormula (ι : Type*) where
  /-- A propositional variable. -/
  | var : ι → PFormula ι
  /-- Conjunction. -/
  | conj : PFormula ι → PFormula ι → PFormula ι
  /-- Disjunction. -/
  | disj : PFormula ι → PFormula ι → PFormula ι
  /-- Implication. -/
  | imp : PFormula ι → PFormula ι → PFormula ι

namespace PFormula

variable {ι κ : Type*}

/-- SUV §13.2 (printed p. 404): the problem `Φ(X, Y, …)` obtained by substituting the problems
`v i` for the variables of `Φ` and reading the connectives as operations on problems of the
calculus `P`. -/
def eval (P : ProblemCalculus) (v : ι → Set BitString) : PFormula ι → Set BitString
  | var i => v i
  | conj A B => P.conj (eval P v A) (eval P v B)
  | disj A B => P.disj (eval P v A) (eval P v B)
  | imp A B => P.imp (eval P v A) (eval P v B)

/-- Substitution of formulas `T i` for the variables `i` (the book's `Φ(T₁, …, T_m)`). -/
def subst (T : ι → PFormula κ) : PFormula ι → PFormula κ
  | var i => T i
  | conj A B => conj (subst T A) (subst T B)
  | disj A B => disj (subst T A) (subst T B)
  | imp A B => imp (subst T A) (subst T B)

/-- A formula without implications (built from variables by `∧` and `∨` only). -/
def ImpFree : PFormula ι → Prop
  | var _ => True
  | conj A B => ImpFree A ∧ ImpFree B
  | disj A B => ImpFree A ∧ ImpFree B
  | imp _ _ => False

/-- Provability in (the positive fragment of) intuitionistic propositional calculus: the
Hilbert system with the axiom schemes of `→`, `∧`, `∨` and modus ponens.  For the
negation-free formulas of SUV Chapter 13 this is provability in IPC. -/
inductive Provable : PFormula ι → Prop
  | ax_k (A B : PFormula ι) : Provable (imp A (imp B A))
  | ax_s (A B C : PFormula ι) :
      Provable (imp (imp A (imp B C)) (imp (imp A B) (imp A C)))
  | ax_conj_left (A B : PFormula ι) : Provable (imp (conj A B) A)
  | ax_conj_right (A B : PFormula ι) : Provable (imp (conj A B) B)
  | ax_conj_intro (A B : PFormula ι) : Provable (imp A (imp B (conj A B)))
  | ax_disj_left (A B : PFormula ι) : Provable (imp A (disj A B))
  | ax_disj_right (A B : PFormula ι) : Provable (imp B (disj A B))
  | ax_disj_elim (A B C : PFormula ι) :
      Provable (imp (imp A C) (imp (imp B C) (imp (disj A B) C)))
  | mp {A B : PFormula ι} : Provable (imp A B) → Provable A → Provable B

/-- Forcing in a Kripke model with worlds `W` and valuation `V` (`V w i`: the variable `i` is
true at `w`). -/
def Forces {W : Type*} [Preorder W] (V : W → ι → Prop) : W → PFormula ι → Prop
  | w, var i => V w i
  | w, conj A B => Forces V w A ∧ Forces V w B
  | w, disj A B => Forces V w A ∨ Forces V w B
  | w, imp A B => ∀ w', w ≤ w' → Forces V w' A → Forces V w' B

/-- Right-nested conjunction `A₁ ∧ (A₂ ∧ (… ∧ A_m))` of a list of formulas; the default `d`
is returned for the empty list (it is never used for the nonempty lists of the chapter). -/
def conjList (d : PFormula ι) : List (PFormula ι) → PFormula ι
  | [] => d
  | [A] => A
  | A :: B :: l => conj A (conjList d (B :: l))

/-- Right-nested disjunction `A₁ ∨ (A₂ ∨ (… ∨ A_m))` of a list of formulas; the default `d`
is returned for the empty list. -/
def disjList (d : PFormula ι) : List (PFormula ι) → PFormula ι
  | [] => d
  | [A] => A
  | A :: B :: l => disj A (disjList d (B :: l))

/-- Auxiliary lemma, not a numbered SUV item (Section 13.4, printed p. 413).  Evaluating a
substitution instance: `Φ(T₁, …, T_m)(v) = Φ(T₁(v), …, T_m(v))`, by induction on `Φ`. -/
theorem eval_subst (P : ProblemCalculus) (T : ι → PFormula κ) (v : κ → Set BitString) :
    ∀ Φ : PFormula ι, (Φ.subst T).eval P v = Φ.eval P (fun i => (T i).eval P v)
  | var _ => rfl
  | conj A B => by simp only [subst, eval, eval_subst P T v A, eval_subst P T v B]
  | disj A B => by simp only [subst, eval, eval_subst P T v A, eval_subst P T v B]
  | imp A B => by simp only [subst, eval, eval_subst P T v A, eval_subst P T v B]

/-- Auxiliary lemma, not a numbered SUV item (Section 13.4, proof of Theorem 238, printed
p. 413: "Those sets are finite, since formulas `T_i` … do not contain implication").  An
implication-free formula evaluated at finite problems is a finite problem, by induction. -/
theorem eval_finite_of_impFree (P : ProblemCalculus) {v : ι → Set BitString}
    (hv : ∀ i, (v i).Finite) : ∀ {Φ : PFormula ι}, Φ.ImpFree → (Φ.eval P v).Finite
  | var i, _ => hv i
  | conj _ _, h => (eval_finite_of_impFree P hv h.1).image2 _ (eval_finite_of_impFree P hv h.2)
  | disj _ _, h =>
      ((eval_finite_of_impFree P hv h.1).image _).union ((eval_finite_of_impFree P hv h.2).image _)
  | imp _ _, h => False.elim h

end PFormula

/-- A valuation is monotone if truth persists upwards. -/
def IsMonotoneValuation {ι W : Type*} [Preorder W] (V : W → ι → Prop) : Prop :=
  ∀ ⦃w w' : W⦄, w ≤ w' → ∀ i, V w i → V w' i

open PFormula

/-- The variables indexed by a finset `I ⊆ Fin k`, in increasing order. -/
def finsetVars {k : ℕ} (I : Finset (Fin k)) : List (PFormula (Fin k)) :=
  ((List.finRange k).filter (fun i => decide (i ∈ I))).map var

/-- The data of a critical implication on the variables `Fin k` (SUV §13.4, printed p. 412): a
nonempty list of pairs `(I_l, J_l)` of nonempty disjoint index sets.  The field `pos` (which
follows from the others) provides the default variable of `conjList` / `disjList`. -/
structure CriticalData (k : ℕ) where
  /-- The pairs `(I_l, J_l)`. -/
  pairs : List (Finset (Fin k) × Finset (Fin k))
  pairs_ne_nil : pairs ≠ []
  left_nonempty : ∀ p ∈ pairs, p.1.Nonempty
  right_nonempty : ∀ p ∈ pairs, p.2.Nonempty
  disjoint : ∀ p ∈ pairs, Disjoint p.1 p.2
  pos : 0 < k

namespace CriticalData

variable {k : ℕ}

/-- The default variable `s₁`. -/
def dflt (C : CriticalData k) : PFormula (Fin k) := var ⟨0, C.pos⟩

/-- `P_l`: the conjunction of the variables of `I`. -/
def premise (C : CriticalData k) (I : Finset (Fin k)) : PFormula (Fin k) :=
  conjList C.dflt (finsetVars I)

/-- `Q_l`: the disjunction of the variables of `J`. -/
def target (C : CriticalData k) (J : Finset (Fin k)) : PFormula (Fin k) :=
  disjList C.dflt (finsetVars J)

/-- `R`: the disjunction of all the variables `s₁ ∨ … ∨ s_k`. -/
def conclusion (C : CriticalData k) : PFormula (Fin k) :=
  disjList C.dflt (finsetVars Finset.univ)

/-- The critical implication
`((P₁ → Q₁) → Q₁) ∧ … ∧ ((P_N → Q_N) → Q_N) → R`. -/
def formula (C : CriticalData k) : PFormula (Fin k) :=
  imp (conjList C.dflt (C.pairs.map fun p =>
      imp (imp (C.premise p.1) (C.target p.2)) (C.target p.2)))
    C.conclusion

end CriticalData

/-- A formula is a critical implication if it is the formula of some critical data. -/
def IsCriticalImplication {k : ℕ} (J : PFormula (Fin k)) : Prop :=
  ∃ C : CriticalData k, C.formula = J

/-- The code of the tuple of all `u t` with `t ≠ m` (in increasing order of `t`): the condition
"all other strings" of SUV Theorems 243 and 244. -/
def othersCode {k : ℕ} (u : Fin k → BitString) (m : Fin k) : BitString :=
  listCode (((List.finRange k).filter (fun t => decide (t ≠ m))).map u)

end InformationLogic
end Kolmogorov
