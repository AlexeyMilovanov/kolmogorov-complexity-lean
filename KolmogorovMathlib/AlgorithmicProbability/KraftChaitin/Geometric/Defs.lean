/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import Mathlib
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple

import KolmogorovMathlib.AlgorithmicProbability.LSC.Defs
import KolmogorovMathlib.AlgorithmicProbability.LSC.Truncate
import KolmogorovMathlib.AlgorithmicProbability.LSC.Computability

namespace Kolmogorov

open scoped ENNReal
open Computability

/-! ### Geometric (threshold-crossing) dyadic request extraction

The geometric request stream emits, for each output `o` and dyadic length `l ≥ 1`,
exactly one request `(o, l)` precisely when the lower-semicomputable approximation
of `f o ctx` first crosses the threshold `2^{-(l-1)}` at some stage `s`. The
per-output requested lengths therefore form an upward-closed set `{ l ≥ L }`, whose
Kraft tail `∑_{l ≥ L} 2^{-l} = 2 · 2^{-L}` is bounded by `f o ctx`, while the
largest single weight `2^{-L}` geometrically dominates `f o ctx` (within `2^2`).
This is the decomposition consumed by `realization_bound_of_machine`. -/

/-- The threshold-crossing predicate: the stage-`s` dyadic value of `approx · o ctx`
has reached `2^{-(l-1)}`, i.e. `2^s ≤ approx s o ctx · 2^(l-1)` (and `l ≥ 1`). -/
def geomCross (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString) (l s : ℕ) : Prop :=
  1 ≤ l ∧ 2 ^ s ≤ approx s o ctx * 2 ^ (l - 1)

instance (approx : ℕ → BitString → BitString → ℕ) (o ctx : BitString) (l s : ℕ) :
    Decidable (geomCross approx o ctx l s) := by
  unfold geomCross; infer_instance

/-- The geometric request stream. Decode `n` into `(o, l, s)` via two `Nat.unpair`s
(and `evOut` for the output), and emit `(o, l)` exactly at the first stage `s` at
which `geomCross` becomes true for `(o, l)`. -/
lemma decide_or_not_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∨ ¬b) = cond (decide a) true (cond (decide b) false true) := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

lemma decide_and_eq {a b : Prop} [Decidable a] [Decidable b] :
    decide (a ∧ b) = cond (decide a) (decide b) false := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

lemma ite_eq_some {P : Prop} [Decidable P] {α : Type _} {x : α} :
    (if P then some x else none) = cond (decide P) (some x) none := by
  by_cases hP : P <;> simp_all

/-- Body of the geometric request stream. -/
def geomReqBody (approx : ℕ → BitString → BitString → ℕ) (p : (BitString × ℕ) × BitString) : Option (BitString × ℕ) :=
  if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧ ((evK (Nat.unpair p.1.2).1) = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) ((evK (Nat.unpair p.1.2).1) - 1)) then
    some (p.2, ((Nat.unpair p.1.2).2))
  else none

lemma geomReqBody_eq (approx : ℕ → BitString → BitString → ℕ) (p : (BitString × ℕ) × BitString) :
  geomReqBody approx p =
    if geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) (evK (Nat.unpair p.1.2).1) ∧ ((evK (Nat.unpair p.1.2).1) = 0 ∨ ¬ geomCross approx p.2 p.1.1 ((Nat.unpair p.1.2).2) ((evK (Nat.unpair p.1.2).1) - 1)) then
      some (p.2, ((Nat.unpair p.1.2).2))
    else none := rfl

/-- Geometric request stream. -/
def geomReq (approx : ℕ → BitString → BitString → ℕ) (ctx : BitString) (n : ℕ) :
    Option (BitString × ℕ) :=
  (evOut (Nat.unpair n).1).bind fun o => geomReqBody approx ((ctx, n), o)


end Kolmogorov
