/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.LawsOfLargeNumbers.PrefixFrequency
import KolmogorovMathlib.Complexity.Applications.LawsOfLargeNumbers.IteratedLogarithm
import KolmogorovMathlib.Complexity.Applications.LawsOfLargeNumbers.KMUpperBound

/-!
# Laws of Large Numbers (SUV Section 8.4, pp. 238-241)

The Strong Law for Martin-Löf random sequences is already in the library
(`tendsto_freqOne_of_isMartinLofRandom_uniform`, Theorems 32-33), as are the two facts this section
combines: the Levin-Schnorr criterion `isMartinLofRandom_uniform_iff_KA_KMOf_eq_length`
(Theorems 90, 94) and the entropy bound for words with given frequencies
`exists_plainK_word_le_entropy_freq` (Theorem 146).

The new statements are the class of Theorem 155, larger than the random sequences, and the upper
half of the Law of the Iterated Logarithm for random sequences, Theorem 156.
-/
