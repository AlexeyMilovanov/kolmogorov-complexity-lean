import Mathlib.Computability.Partrec
import KolmogorovMathlib.Core.Basic
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.Complexity.Chaitin

/-!
# Corollaries of Chaitin's Theorem

This module provides a generalized interface for applying Chaitin's Theorem.
It proves that any sufficiently strong formal system—specifically, one that
can express all co-RE (co-computably enumerable) relations—is subject to
information-theoretic incompleteness.
-/

namespace Kolmogorov

/-! ### General Formal System Interface -/

/-- A generalized formal system that provides an enumerable set of theorems
    but does not yet specify a strict parser for complexity bounds. -/
structure GeneralSystem where
  Formula : Type
  enc : Primcodable Formula
  provable : Formula → Prop
  enumThm : ℕ → Option Formula
  hEnumComp : Computable enumThm
  hEnumExact : ∀ φ, provable φ ↔ ∃ i, enumThm i = some φ

attribute [instance] GeneralSystem.enc

/-- An interface asserting that a `GeneralSystem` can successfully express,
    parse, and soundly prove a specific mathematical relation `R`. -/
structure Expresses (sys : GeneralSystem) (R : ℕ × ℕ → Prop) where
  expr : ℕ → ℕ → sys.Formula
  parse : sys.Formula → Option (ℕ × ℕ)
  hParseComp : Computable parse
  hParseForward : ∀ x L, parse (expr x L) = some (x, L)
  hParseInv : ∀ φ x L, parse φ = some (x, L) → φ = expr x L
  hSound : ∀ x L, sys.provable (expr x L) → R (x, L)

/-! ### Bridging the Complexity Gap -/

/-- The relation `K(x) > L` defined over natural numbers is co-computably enumerable. -/
lemma plainKNatGtIsCore (U : Map) (hU : isOptimalConditional U) :
    IsCoRE (fun (p : ℕ × ℕ) => (p.2 : ENat) < plainKNat U p.1) := by
  unfold IsCoRE plainKNat
  have h_base := plainKGtIsCore U hU
  unfold IsCoRE IsRE at h_base
  obtain ⟨f, hf_partrec, hf_dom⟩ := h_base
  refine ⟨fun p => f (Nat.bits p.1, p.2), ?_, ?_⟩
  · have h_trans : Computable (fun (p : ℕ × ℕ) => (Nat.bits p.1, p.2)) :=
      Computable.pair (natBitsComputable.comp Computable.fst) Computable.snd
    exact Partrec.comp hf_partrec h_trans
  · intro p
    exact hf_dom (Nat.bits p.1, p.2)

/-! ### The Grand Corollary -/

/-- If a general formal system can express all co-RE relations, it must be incomplete
    with respect to Kolmogorov complexity. There exists a true lower bound `K(x) > L`
    that the system cannot prove. -/
theorem chaitinGeneralized (U : Map) (hU : isOptimalConditional U)
    (sys : GeneralSystem)
    (hExpressCore : ∀ (R : ℕ × ℕ → Prop), IsCoRE R → Expresses sys R) :
    ∃ x L : ℕ,
      (L : ENat) < plainKNat U x ∧
      let KRel := fun (p : ℕ × ℕ) => (p.2 : ENat) < plainKNat U p.1
      let expr := (hExpressCore KRel (plainKNatGtIsCore U hU)).expr
      ¬ sys.provable (expr x L) := by
  let KRel := fun (p : ℕ × ℕ) => (p.2 : ENat) < plainKNat U p.1
  let hCore := plainKNatGtIsCore U hU
  let exprPack := hExpressCore KRel hCore
  let F : FormalSystem U := {
    Formula := sys.Formula,
    enc := sys.enc,
    provable := sys.provable,
    enumThm := sys.enumThm,
    hEnumComp := sys.hEnumComp,
    hEnumExact := sys.hEnumExact,
    exprKGt := exprPack.expr,
    parseKGt := exprPack.parse,
    hParseComp := exprPack.hParseComp,
    hParseForward := exprPack.hParseForward,
    hParseInv := exprPack.hParseInv,
    hSound := exprPack.hSound
  }
  exact F.chaitinIncompleteness hU

end Kolmogorov
