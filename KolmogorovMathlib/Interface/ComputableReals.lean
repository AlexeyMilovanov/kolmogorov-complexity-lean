/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.Interface.ComputableReals.Part01
import KolmogorovMathlib.Interface.ComputableReals.ClosureProperties
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Computable and lower semicomputable reals

## The gap this file fills

Before this file the library had **no API for computable sequences of rationals** at all:
`Computable q` for `q : ℕ → ℚ` goes through `Primcodable ℚ`, which mathlib provides only via
`Primcodable.ofDenumerable` and `Denumerable.ofEncodableOfInfinite`, i.e. through the
*counting* enumeration of the range of `Rat.instEncodable`.  Nothing relates that encoding to
the field structure of `ℚ`, so not even `Computable (fun p : ℚ × ℚ => max p.1 p.2)` was
available, and every attempt at Theorem 44, Theorem 45 and Exercises 94/95 of
Shen–Uspensky–Vereshchagin drowned in this plumbing.

Two traps are worth recording.

* `Encodable ℚ` resolves to `Rat.instEncodable` (the structural numerator/denominator code,
  called `ratCode` here) while `Primcodable ℚ` carries a **different** encodable structure
  (the counting index, called `ratIndex` here).  Writing a bare `Encodable.encode` at type
  `ℚ` in a computability statement therefore picks the wrong encoding and makes elaboration
  diverge; always use `ratIndex`, `Denumerable.ofNat ℚ` or an explicit instance.
* mathlib has no `Primrec` API for `ℤ` or for `Nat.gcd` either, so those are built here too.

## What this file provides

Groundwork (`ℤ`, `Nat.gcd`, and the two encodings of `ℚ`):

* `Kolmogorov.ComputableReals.primrec_intToNat`, `primrec_intNegToNat`, `primrec_natSubInt`,
  `primrec_intNatAbs`, `primrec_natCastInt`, `primrec_intAdd`, `primrec_intMul`, `primrec_intLe`,
  `primrec_intLt`;
* `primrec_natGcd`;
* `ratCode`, `isCode`, `unrank` and the bridge `ratCode_ofNat`, giving `primrec_ratCode`,
  `primrec_ratNum`, `primrec_ratDen`;
* `primrec_ratLe`, `primrec_ratLt`, `primrec_ratMax`, `primrec_ratMin`, the search principle
  `computable_of_verifier`, and `computable_ratAdd`, `computable_ratNeg`, `computable_ratSub`,
  `computable_natCastRat`, `computable_invSucc`.

Lower semicomputable reals:

* monotonisation: `runningMax`, `computable_runningMax`, `monotone_runningMax`,
  `isLUB_range_runningMax`, and the workhorse `isLowerSemicomputableReal_of_isLUB`;
* the book's characterisation `isLowerSemicomputableReal_iff_isRE`
  (`IsLowerSemicomputableReal a ↔ IsRE (fun r : ℚ => (r : ℝ) < a)`, SUV after Problem 95),
  both directions;
* closure and comparison: `IsComputableReal.isLowerSemicomputableReal`,
  `IsLowerSemicomputableReal.add`, `IsLowerSemicomputableReal.add_rat`,
  `IsLowerSemicomputableReal.exists_lower_approx`, `.exists_upper_approx`, and
  `isComputableReal_of_lower_of_lower_neg`;
* suprema of enumerated families: `isLowerSemicomputableSeq_of_monotone`;
* the monotone partial-sums bridge `isLowerSemicomputableReal_of_partialSums` (the abstract
  form of "the halting probability is the increasing limit of the probabilities of halting
  within `n` steps"), with `computable_partialSum`.

The predicates `IsLowerSemicomputableReal`, `IsComputableReal` and
`IsLowerSemicomputableSeq` are *definitionally identical* to the `Kolmogorov`-level
predicates of the same names (in `MonotoneComplexity.Omega.Basic.Part01` and
`Interface.ComputableReals.LowerSemicomputableReals`); those modules are deliberately not
imported (they are downstream of `Interface`), and `isLowerSemicomputableReal_iff`,
`isComputableReal_iff` and
`isLowerSemicomputableSeq_iff` unfold them so that results can be transported by `rw`.
-/
