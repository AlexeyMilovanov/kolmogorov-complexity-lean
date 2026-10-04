/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Entropy.Complexity.ShannonCoding.Basic
import KolmogorovMathlib.Entropy.Complexity.ShannonCoding.Conditional
import KolmogorovMathlib.Entropy.Complexity.ShannonCoding.RealProbabilities

/-!
# The Shannon coding theorem

SUV Section 7.3.5, pp. 231–232.

Let `ξ` be a random variable with values in a `k`-letter alphabet `A` and let `ξ^N` be the word
formed by `N` independent copies of it.  An *encoder* is any map `A^N → 𝔹^m` and a *decoder* any
map `𝔹^m → A^N`; a value of `ξ^N` causes an error when decoding its encoding does not give it back.
Theorem 150 characterises the pairs `(N, m)` supporting a code with error probability at most `ε`,
and Theorem 151 shows that `N H(ξ) ± c√N` bits are the threshold: with `N H(ξ) + c√N` bits the
error can be made at most `ε`, and with `N H(ξ) − c√N` bits the probability of correct decoding
is at most `ε`.

Encoders and decoders are arbitrary functions (the book stresses that coding "is not performed by
an algorithm"), so these statements are purely probabilistic.  The words of length `m` over `𝔹`
are `Fin m → Bool`.  The model of `ξ^N` is `μ.power N` on the words `Fin N → A`, and the
probability of the error event is `probOfPred`.

**Computability of the `p_i`.**  The book proves Theorem 151 from Theorem 149, and part (b) through
the complexity of correctly decoded words, which needs the `p_i` to be computable; Problem 240
asks to remove that assumption.  Theorem 151 is therefore stated with rational `p_i`, and the
declarations of Problem 240 are Theorem 149 and Theorem 151(b) for arbitrary real `p_i`.
Problem 241 is the conditional version, with the side information `η^N` known to both ends; the
book leaves its statement to the reader, and the statement here is the expected one
(`m = N H(ξ|η) ± c√N`).

The section is split by topic: Theorems 150 and 151 in `ShannonCoding/Basic.lean`, the version
for arbitrary real probabilities (Problem 240) in `ShannonCoding/RealProbabilities.lean`, and the
conditional version (Problem 241) in `ShannonCoding/Conditional.lean`.
-/
