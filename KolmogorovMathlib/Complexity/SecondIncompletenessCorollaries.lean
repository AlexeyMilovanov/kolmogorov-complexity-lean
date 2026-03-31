import KolmogorovMathlib.Complexity.SecondIncompleteness

/-!
# Corollaries of the Second Incompleteness Theorem

This module provides a generalized interface for applying the Kritchman-Raz proof
of Gödel's Second Incompleteness Theorem. It demonstrates how standard
properties of formal logic—specifically Hilbert-Bernays-Löb (HBL) derivability
conditions, Σ₁-completeness, and logical soundness—naturally fulfill the
abstract axioms of our `KRFormalSystem`.
-/

namespace Kolmogorov

/-! ### Standard Arithmetical Systems -/

/-- A formal system representing standard theories like Peano Arithmetic (PA) or ZFC.
    Instead of requiring the user to prove upper counting bounds inside the formal system,
    this interface uses a Semantic Bridge (`eval` + `soundness`) to derive the
    upper bound directly from Lean's mathematical truth. -/
structure PeanoLikeSystem (U : Map) extends FormalSystem U where
  -- 1. Basic Propositional Logic
  impl : Formula → Formula → Formula
  not : Formula → Formula
  mp : ∀ A B, provable (impl A B) → provable A → provable B
  mt : ∀ A B, provable (impl A B) → provable (not B) → provable (not A)

  -- 2. Vocabulary
  exprCon : Formula
  exprMGt : ℕ → ℕ → Formula
  exprMEq : ℕ → ℕ → Formula
  exprExistsProvKGt : ℕ → Formula

  -- 3. Semantics & Soundness (The Semantic Bridge)
  eval : Formula → Prop
  soundness : ∀ φ, provable φ → eval φ

  -- The semantic truth of `exprMGt L i` implies that `i` cannot exceed the total number
  -- of strings in the interval [0, 2^{L+1}], which is exactly 2^{L+1} + 1.
  evalExprMGtBound : ∀ L i, eval (exprMGt L i) → i ≤ 2 ^ (L + 1) + 1

  -- 4. Basic Arithmetic
  arithBase : ∀ L, provable (exprMGt L 1)
  -- Note: `arithBound` is derived automatically via the Semantic Bridge!
  arithSplit : ∀ L i, provable (impl (exprMGt L i) (impl (not (exprMEq L i)) (exprMGt L (i + 1))))

  -- 5. The HBL Consequence (Equation 1 in Kritchman-Raz)
  -- By applying Hilbert-Bernays conditions to Chaitin's First Theorem:
  -- A consistent system cannot prove that any specific string is complex.
  hblEq1 : ∀ L, provable (impl exprCon (not (exprExistsProvKGt L)))

  -- 6. The Σ₁-Completeness Consequence (Equation 2 in Kritchman-Raz)
  -- Because K(y) <= L is a Σ₁ formula (it just requires running a program),
  -- true instances are provable. Thus, if the system knows exactly how many
  -- complex strings exist (m = i), it can prove the remaining one is complex.
  sigma1Eq2 : ∀ L i, provable (impl (exprMEq L i) (exprExistsProvKGt L))

/-! ### Bridging the Logic -/

/-- Any sound `PeanoLikeSystem` possessing HBL properties and Σ₁-completeness
    canonically instantiates a `KRFormalSystem`. The impossible upper bound is
    derived automatically from the system's soundness. -/
def PeanoLikeSystem.toKRFormalSystem {U : Map} (sys : PeanoLikeSystem U) : KRFormalSystem U := {
  toFormalSystem := sys.toFormalSystem
  impl := sys.impl
  not := sys.not
  mp := sys.mp
  mt := sys.mt
  exprCon := sys.exprCon
  exprMGt := sys.exprMGt
  exprMEq := sys.exprMEq
  exprExistsProvKGt := sys.exprExistsProvKGt
  krBase := sys.arithBase
  krEq3 := sys.hblEq1
  krStep4 := sys.sigma1Eq2
  krMSplit := sys.arithSplit
  -- WE DERIVE THE KR_BOUND AUTOMATICALLY HERE:
  krBound := fun L hProv => by
    -- 1. If the system proved it, it must be true in reality (soundness)
    have hEval := sys.soundness _ hProv
    -- 2. The mathematical meaning implies the count cannot exceed the range
    have hBound := sys.evalExprMGtBound L (2 ^ (L + 1) + 2) hEval
    -- 3. Lean's arithmetic solver sees that `2^(L+1) + 2 ≤ 2^(L+1) + 1` is False!
    omega
}

/-! ### The Grand Corollary for Gödel's Second Theorem -/

/-- If a formal system satisfies basic arithmetic, HBL derivability conditions,
    Σ₁-completeness, and is sound, it is subject to Gödel's Second Incompleteness Theorem
    and cannot prove its own consistency. -/
theorem secondIncompletenessGeneralized (U : Map) (sys : PeanoLikeSystem U) :
    ¬ sys.provable sys.exprCon := by
  -- We seamlessly map the standard logical properties into the KR paradox induction
  exact KRFormalSystem.secondIncompleteness sys.toKRFormalSystem

end Kolmogorov
