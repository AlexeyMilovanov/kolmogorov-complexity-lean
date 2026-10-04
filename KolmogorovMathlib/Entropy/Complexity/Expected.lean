/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Complexity.Expected.Basic
import KolmogorovMathlib.Entropy.Complexity.Expected.Monotone
import KolmogorovMathlib.Entropy.Complexity.Expected.Uniform

/-!
# The expected complexity of an i.i.d. word

SUV Section 7.3.2, p. 228.

Fix a `k`-letter alphabet `A` and a distribution `p₁, …, p_k` on it, let `ξ` be a random variable
with that distribution and let `ξ^N` be the word formed by `N` independent copies of `ξ`.
Theorem 147 says that the expected value of `K(ξ^N | N)` is `N H(ξ) + O(1)`, with a constant that
may depend on `ξ` but not on `N`.

The model: the alphabet itself is the probability space, `μ : FiniteProbSpace A` carries the
distribution `p`, and `μ.power N` is the distribution of `ξ^N` on the words `Fin N → A`; the
entropy `H(ξ)` is `entropyDist μ.prob`.  The complexity is the *conditional prefix* complexity
`KP U x y` of the block encoding `finWordBits A w`, with the condition `natCode N`, and `U` is an
optimal prefix decompressor.  The `ℕ∞`-valued complexity is read through `ENat.toNat`, which is
faithful because an optimal decompressor gives every string a finite complexity.

The two bounds are separate statements, as in the book: the lower bound `N H(ξ) ≤ E K(ξ^N|N)`
holds exactly, with no constant and with no assumption on the `p_i` (it is Theorem 138(a) applied
to the prefix code of shortest descriptions), while the upper bound carries a constant, quantified
before `N`, and assumes that the `p_i` are positive rationals, so that a good prefix code can be
computed from `N`.

The section is split by topic: Theorem 147 in `Expected/Basic.lean`, the monotone complexity
version (Problem 236) in `Expected/Monotone.lean`, and the uniform version (Problem 237) in
`Expected/Uniform.lean`.
-/
