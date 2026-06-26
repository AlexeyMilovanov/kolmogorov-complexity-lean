/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.Prefix.Combinators
import KolmogorovMathlib.AlgorithmicProbability.SimulationComplexity
import KolmogorovMathlib.AlgorithmicProbability.UniversalMixture

/-!
# A Machine-Realized Universal A Priori Semimeasure

The `taggedUnion` of `Prefix.Combinators` glues a countable family `M : ℕ → Map`
of prefix machines into a *single* prefix machine by prepending the
self-delimiting unary tag `natCode i = 1ⁱ0` to the programs of `M i`. So far that
construction is purely combinatorial: it proves a per-program coding bound
(`taggedUnion_KP_le_of_produces`) but is not connected to the abstract
`ProgramSimulation` / `IsUniversalFor` vocabulary of the semimeasure layer.

This module supplies the bridge. The tag-prepending map is an injective,
length-bounded, output-preserving translation of `M i`'s programs into
`taggedUnion M`'s programs, i.e. a `ProgramSimulation (taggedUnion M) (M i) (i+1)`
(`taggedUnionSimulation`). Through the existing
`ProgramSimulation.aprioriMeasure_dominates`, this yields that the a priori
semimeasure of `taggedUnion M` multiplicatively dominates each component's, with
the dyadic constant `2^{-(i+1)} = dyadicWeight i`. Packaging the domination with
the conditional-semimeasure property of a prefix machine gives the headline
`aprioriMeasure_taggedUnion_isUniversalFor`.

Unlike `mixture_dyadicWeight_aprioriMeasure_isUniversalFor`, whose universal
object is a *mixture* (a weighted infinite sum of semimeasures), the universal
object here is the a priori semimeasure of a *single, explicitly constructed
prefix machine*. This is the project's first **machine-realized** universal
conditional a priori semimeasure for a countable family of prefix machines.

We keep the family `M : ℕ → Map` abstract: building a *globally* universal `U` by
enumerating all prefix decompressors needs `Nat.Partrec.Code` and belongs to a
later slot. Everything stays in `ENat` (additive `KP`) and `ℝ≥0∞`
(multiplicative `≤×`): no real logarithms and no coding-theorem equality.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **The tag-prepending program simulation.** Prepending the unary tag
`natCode i` injects `M i`'s programs into `taggedUnion M`'s programs with length
overhead exactly `i + 1` (the `i` ones plus the terminating `0`), preserving the
produced output. This bundles the combinatorial facts of `Prefix.Combinators`
(`taggedUnion_produces_natCode`, `length_natCode`, `List.append_cancel_left`) into
the `ProgramSimulation` structure consumed by the semimeasure layer. -/
def taggedUnionSimulation (M : ℕ → Map) (i : ℕ) :
    ProgramSimulation (taggedUnion M) (M i) (i + 1) where
  translate := fun p => natCode i ++ p
  injective := fun _ _ h => List.append_cancel_left h
  length_le := fun p => by
    simp only [programLength, List.length_append, length_natCode]; omega
  simulates := fun _ _ _ hp => taggedUnion_produces_natCode hp

/-- **Component-wise domination.** The a priori semimeasure of `taggedUnion M`
dominates that of each component `M i` with the dyadic constant
`dyadicWeight i = 2^{-(i+1)}`, the weight of the `(i+1)`-bit tag overhead. -/
theorem aprioriMeasure_taggedUnion_dominates (M : ℕ → Map) (i : ℕ) :
    Dominates (aprioriMeasure (taggedUnion M)) (aprioriMeasure (M i))
      (dyadicWeight i) :=
  (taggedUnionSimulation M i).aprioriMeasure_dominates

/-- **Machine-realized universal a priori semimeasure.** For any countable family
of prefix machines `M : ℕ → Map`, the a priori semimeasure of the single prefix
machine `taggedUnion M` is universal for the family: it is a conditional
semimeasure (`taggedUnion M` is a prefix machine by `taggedUnion_isPrefixMachine`)
and dominates every component by the strictly positive constant `dyadicWeight i`.

This is the headline of the slot: a universal object realized by an actual
machine, not by an abstract weighted mixture as in
`mixture_dyadicWeight_aprioriMeasure_isUniversalFor`. -/
theorem aprioriMeasure_taggedUnion_isUniversalFor (M : ℕ → Map)
    (hM : ∀ i, IsPrefixMachine (M i)) :
    IsUniversalFor (aprioriMeasure (taggedUnion M))
      (fun i => aprioriMeasure (M i)) :=
  ⟨aprioriMeasure_isConditionalSemimeasure (taggedUnion M)
      (taggedUnion_isPrefixMachine hM),
   fun i => ⟨dyadicWeight i, dyadicWeight_pos i,
     aprioriMeasure_taggedUnion_dominates M i⟩⟩

/-- **Additive `KP` companion.** On the conditional prefix complexity side, the
same tag-prepending simulation gives the uniform-in-`x,y` bound
`KP (taggedUnion M) x y ≤ KP (M i) x y + (i + 1)`. This is the `KP`-shadow of the
multiplicative domination above, with the identical overhead constant `i + 1`,
and complements the per-program `taggedUnion_KP_le_of_produces`. -/
theorem taggedUnion_KP_le (M : ℕ → Map) (i : ℕ) (x y : BitString) :
    KP (taggedUnion M) x y ≤ KP (M i) x y + ((i + 1 : ℕ) : ENat) :=
  (taggedUnionSimulation M i).KP_le x y

end Kolmogorov
