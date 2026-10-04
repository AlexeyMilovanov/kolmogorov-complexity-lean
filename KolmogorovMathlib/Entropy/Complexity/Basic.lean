/-
Copyright (c) 2024 The KolmogorovMathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The KolmogorovMathlib Contributors
-/
import KolmogorovMathlib.Entropy.Basic
import KolmogorovMathlib.Entropy.Codes.Alphabet
import Mathlib.Algebra.Group.Indicator

/-!
# Vocabulary shared by the complexity–entropy statements

SUV Section 7.3, pp. 226–232.

Section 7.3 compares the Kolmogorov complexity of a word over a `k`-letter alphabet with the
Shannon entropy of the distribution that generated it.  Two pieces of vocabulary are common to all
of its statements and are fixed here.

* `finWordBits α w` is the bit string that encodes a word `w : Fin N → α` of length `N` over the
  alphabet `α`.  It is the fixed block encoding `wordBits` of
  `KolmogorovMathlib.Entropy.Codes.Alphabet`, the library's choice among the computable injective
  encodings that the book leaves open; all of them agree up to an additive constant, which is
  absorbed by the `O(1)` and `O(log N)` terms of the section.  The complexity of an `α`-word of
  length `N` is therefore `plainK D (finWordBits α w)`, and its prefix complexity is
  `KPPlain U (finWordBits α w)`.
* `FiniteProbSpace.probOfPred μ P` is the probability of a property of the outcome that need not
  be decidable, which is what the events of Theorems 149–151 are (they are described by
  inequalities between real numbers).
-/

namespace Kolmogorov

open Finset

/-- The bit string encoding a word of length `N` over the alphabet `α`: the fixed-width blocks of
its letters, concatenated (`wordBits`).  The plain complexity of the word is
`plainK D (finWordBits α w)`.  SUV Section 7.3, pp. 226 and 229. -/
def finWordBits (α : Type*) [Fintype α] [Encodable α] {N : ℕ} (w : Fin N → α) : BitString :=
  wordBits α (List.ofFn w)

variable {Ω : Type*} [Fintype Ω]

/-- The probability of an arbitrary property of the outcome.  Unlike `FiniteProbSpace.probOf`,
which takes a `Finset` of outcomes, this takes a predicate that need not be decidable, as the
events of SUV Theorems 149–151 are.  SUV Section 7.3.4, p. 230. -/
noncomputable def FiniteProbSpace.probOfPred (μ : FiniteProbSpace Ω) (P : Ω → Prop) : ℝ :=
  ∑ ω, Set.indicator {ω | P ω} μ.prob ω

/-- The probability of a property is non-negative. -/
theorem FiniteProbSpace.probOfPred_nonneg (μ : FiniteProbSpace Ω) (P : Ω → Prop) :
    0 ≤ μ.probOfPred P := by
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : ω ∈ {ω | P ω}
  · rw [Set.indicator_of_mem h]
    exact μ.prob_nonneg ω
  · rw [Set.indicator_of_notMem h]

end Kolmogorov
