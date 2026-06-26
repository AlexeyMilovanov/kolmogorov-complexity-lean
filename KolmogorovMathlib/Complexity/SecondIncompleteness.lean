/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Complexity.Chaitin

/-!
# The Second Incompleteness Theorem (Kritchman-Raz)

This module formalizes a modern proof of Gödel's Second Incompleteness Theorem
based on Kolmogorov Complexity, following the approach of Shira Kritchman and Ran Raz (2010).

Instead of formalizing the entirety of Peano Arithmetic and Provability Logic (GL),
we extend our `FormalSystem` with the exact meta-logical properties required by the
Kritchman-Raz induction. This allows us to prove the Second Incompleteness Theorem
abstractly, cleanly separating the information-theoretic paradox from first-order
logic boilerplate.
-/

namespace Kolmogorov

/-! ### Kritchman-Raz Formal System -/

/-- An extension of `FormalSystem` that includes the logical connectives and
    the internalized knowledge required for the Kritchman-Raz induction. -/
structure KRFormalSystem (U : Map) extends FormalSystem U where
  /-- Logical implication. -/
  impl : Formula → Formula → Formula
  /-- Logical negation. -/
  not : Formula → Formula

  /-- Modus ponens deduction rule. -/
  mp : ∀ A B, provable (impl A B) → provable A → provable B
  /-- Modus tollens deduction rule. -/
  mt : ∀ A B, provable (impl A B) → provable (not B) → provable (not A)

  /-- Formula asserting the consistency of the formal system. -/
  exprCon : Formula

  /-- `exprMGt L i` means "The number of strings x <= 2^{L+1} with K(x) > L is >= i" -/
  exprMGt : ℕ → ℕ → Formula

  /-- `exprMEq L i` means "The number of strings x <= 2^{L+1} with K(x) > L is exactly i" -/
  exprMEq : ℕ → ℕ → Formula

  /-- `exprExistsProvKGt L` means "\exists x, Pr_T(K(x) > L)" -/
  exprExistsProvKGt : ℕ → Formula

  /-- Base Case: The system knows the Pigeonhole Principle (there is at least 1 complex string). -/
  krBase : ∀ L, provable (exprMGt L 1)

  /-- Soundness Bound: The system cannot prove a false upper bound.
      The true number of such strings is bounded by 2^{L+1} + 1. -/
  krBound : ∀ L, provable (exprMGt L (2 ^ (L + 1) + 2)) → False

  /-- Equation 3 (Chaitin Internalized): If the system is consistent, it cannot prove K(x) > L. -/
  krEq3 : ∀ L, provable (impl exprCon (not (exprExistsProvKGt L)))

  /-- KR Step 4: If m = i, the system can eliminate all K(y) <= L cases
   and deduce the remaining one. -/
  krStep4 : ∀ L i, provable (impl (exprMEq L i) (exprExistsProvKGt L))

  /-- Logical Dichotomy: (m >= i) -> ~(m = i) -> (m >= i + 1) -/
  krMSplit : ∀ L i, provable (impl (exprMGt L i)
    (impl (not (exprMEq L i)) (exprMGt L (i + 1))))

/-! ### The Second Incompleteness Theorem -/

namespace KRFormalSystem

variable {U : Map} (KRF : KRFormalSystem U)

/-- The core induction of the Kritchman-Raz proof.
    If the system can prove its own consistency, it can logically deduce
    `m >= i` for any arbitrarily large `i`, leading to a contradiction. -/
lemma krInduction (L : ℕ) (hCon : KRF.provable KRF.exprCon) (i : ℕ) :
    KRF.provable (KRF.exprMGt L (i + 1)) := by
  induction i with
  | zero =>
    -- Base case: i = 0 means m >= 1
    exact KRF.krBase L
  | succ i ih =>
    -- Inductive step: Assume m >= i + 1, prove m >= i + 2
    -- 1. From Con, we know ~ \exists x, Pr_T(K(x) > L)
    have hNotExists := KRF.mp _ _ (KRF.krEq3 L) hCon
    -- 2. By Step 4, if m = i+1, we would have \exists x, Pr_T(K(x) > L).
    --    By Modus Tollens, we deduce ~(m = i+1)
    have hNotEq := KRF.mt _ _ (KRF.krStep4 L (i + 1)) hNotExists
    -- 3. Apply the dichotomy: (m >= i+1) -> ~(m = i+1) -> (m >= i+2)
    have hSplit := KRF.mp _ _ (KRF.krMSplit L (i + 1)) ih
    -- 4. Conclude m >= i+2
    exact KRF.mp _ _ hSplit hNotEq

/-- Gödel's Second Incompleteness Theorem (via Kritchman & Raz).
    No sound formal system satisfying the basic properties of Kolmogorov complexity
    can prove its own consistency. -/
theorem secondIncompleteness : ¬ KRF.provable KRF.exprCon := by
  intro hCon
  -- Pick an arbitrary L (e.g., L = 0)
  let L := 0
  -- Run the induction up to i = 2^{L+1} + 1
  let maxI := 2 ^ (L + 1) + 1
  have hAbsurd := KRF.krInduction L hCon maxI
  -- This gives us `provable (exprMGt L (maxI + 1))`,
  -- which evaluates to `provable (exprMGt L (2 ^ (L + 1) + 2))`
  -- This contradicts the soundness bound.
  exact KRF.krBound L hAbsurd

end KRFormalSystem
end Kolmogorov
