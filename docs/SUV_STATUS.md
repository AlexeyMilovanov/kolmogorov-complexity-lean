# Status of the items of the SUV book

Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*: the state of
every numbered theorem and problem of the book in this library.  The declarations that cover the
formalized items are tabulated in [`SUV_COVERAGE.md`](SUV_COVERAGE.md); this file counts the
items by chapter and lists every item that is not formalized in full.

An item is counted as *formalized* when a proved declaration states it, possibly in an
equivalent form or as a direct instance of a more general theorem; *in part or weaker* when only
some of its parts, one direction or a weaker statement is proved; *archived* when it was judged
not worth formalizing and its statement is kept in [`ARCHIVED_TARGETS.md`](ARCHIVED_TARGETS.md);
*no definite claim* when the problem asks for an explanation and states nothing to prove.

## Summary by chapter

| Chapter | Theorems | formalized | in part or weaker | archived | not formalized | Problems | formalized | in part or weaker | archived | not formalized | no definite claim |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 15 | 14 | 1 | 0 | 0 | 15 | 12 | 0 | 3 | 0 | 0 |
| 2 | 11 | 9 | 2 | 0 | 0 | 50 | 42 | 0 | 8 | 0 | 0 |
| 3 | 17 | 16 | 1 | 0 | 0 | 28 | 16 | 3 | 0 | 8 | 1 |
| 4 | 30 | 27 | 0 | 1 | 2 | 24 | 21 | 1 | 1 | 1 | 0 |
| 5 | 52 | 50 | 0 | 0 | 2 | 74 | 37 | 4 | 0 | 33 | 0 |
| 6 | 10 | 10 | 0 | 0 | 0 | 22 | 17 | 4 | 0 | 1 | 0 |
| 7 | 15 | 15 | 0 | 0 | 0 | 28 | 27 | 0 | 0 | 0 | 1 |
| 8 | 14 | 14 | 0 | 0 | 0 | 11 | 10 | 1 | 0 | 0 | 0 |
| 9 | 38 | 38 | 0 | 0 | 0 | 28 | 27 | 1 | 0 | 0 | 0 |
| 10 | 17 | 16 | 0 | 1 | 0 | 24 | 17 | 0 | 7 | 0 | 0 |
| 11 | 8 | 8 | 0 | 0 | 0 | 12 | 12 | 0 | 0 | 0 | 0 |
| 12 | 9 | 9 | 0 | 0 | 0 | 16 | 13 | 0 | 1 | 2 | 0 |
| 13 | 10 | 10 | 0 | 0 | 0 | 12 | 12 | 0 | 0 | 0 | 0 |
| 14 | 15 | 10 | 3 | 2 | 0 | 24 | 12 | 6 | 6 | 0 | 0 |
| all | 261 | 246 | 7 | 4 | 4 | 368 | 275 | 20 | 26 | 45 | 2 |

Theorems 1-6 of the introduction are counted with Chapter 1.

## Items not formalized in full

| Item | Chapter | Status | Statement and what is available |
| --- | --- | --- | --- |
| Theorem 6 | 1 | weaker form | If a partial computable k from strings to N satisfies k(x) <= C(x) wherever it is defined, then k is bounded (Berry paradox). Related: `Kolmogorov.not_computable_unbounded_lowerBound`, `Kolmogorov.FormalSystem.chaitin_bound`. |
| Theorem 18 | 2 | in part | C(x\|y) <= C(x)+O(1); C(x\|x)=O(1); C(f(x,y)\|y) <= C(x\|y)+O(1) for computable f of two arguments; C(x\|y) <= C(x\|g(y))+O(1). Related: `Kolmogorov.condK_le_plainK`, `Kolmogorov.condK_self`, `Kolmogorov.condK_map_le`, `Kolmogorov.condK_cond_map_le`. |
| Theorem 26 | 2 | in part | 2C(x,y,z) <= C(x,y) + C(x,z) + C(y,z) + O(log n) for strings of complexity <= n. Related: `Kolmogorov.tuple_complexity_le_weighted_sum_iff`, `Kolmogorov.holdsForEntropies_iff_holdsForComplexitiesCplx`, `Kolmogorov.two_mul_entropySub_le_sum_pairs`. |
| Theorem 29 | 3 | in part | A set is effectively null iff all its elements are non-ML-random; non-random sequences form the largest effectively null set, and random sequences have measure 1. Related: `Kolmogorov.isEffectivelyNull_iff_forall_not_random`, `Kolmogorov.not_isMartinLofRandom_iff_mem_universal_test`. |
| Theorem 51 | 4 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Theorem 68 | 4 | not formalized | K(x,y,z) = K(z \| x,y,K(x,y)) + K(y \| x,K(x)) + K(x) + O(1). |
| Theorem 69 | 4 | not formalized | K(K(x) \| x, y, K(x,y)) = O(1) and K(K(y \| x,K(x)) \| x, y, K(x,y)) = O(1). |
| Theorem 125 | 5 | not formalized | van Lambalgen: a pair (xi, eta) is ML-random for P x Q iff xi is P-random and eta is Q-random relative to xi. |
| Theorem 126 | 5 | not formalized | Kucera-Gacs: every sequence alpha equals f(omega) for some uniformly ML-random omega and computable f. |
| Theorem 220 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Theorem 250 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Theorem 252 | 14 | weaker form | If x is in A and i ≤ log#A, some A' ∋ x has #A' ≤ #A/2^i and C(A') ≤ C(A)+i+O(log min(i,C(A))). Related: `Kolmogorov.inDescriptionProfile_portion`, `Kolmogorov.descriptionShift_complexity`. |
| Theorem 254 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Theorem 258 | 14 | in part | If x of length n has at least 2^k (i*j)-descriptions from an enumerable family 𝒜, it has an ((i−k)*j)-description from 𝒜, and under (3) also an (i*(j−k))-one. Related: `Kolmogorov.exists_familyComplexityRefinedSet`, `Kolmogorov.inDescriptionProfileIn_improving_complexity`, `Kolmogorov.inDescriptionProfileIn_improving_size`. |
| Theorem 261 | 14 | in part | The standard part B_{x,l} of size 2^s is an ((l−s)*s)-description of x, and (l−s, s) lies on the boundary of P_x (up to O(log l)). Related: `Kolmogorov.prop_std_pos`, `Kolmogorov.setComplexity_standardBlock_upper`, `Kolmogorov.standardBlock_gap_le_of_suffix_lower`, `Kolmogorov.suffixCoordinate_lower_of_model_code`. |
| Problem 7 | 1 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 9 | 1 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 10 | 1 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 20 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 30 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 31 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 32 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 46 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 47 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 56 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 57 | 2 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 66 | 3 | available in Mathlib | Ω is homeomorphic to the middle-thirds Cantor set. Mathlib: `cantorSetHomeomorphNatToBool`. |
| Problem 68 | 3 | in part | Effective nullity is equivalent whether one bounds the sum of measures of the covering intervals or the measure of their union. Related: `Kolmogorov.isEffectiveAlphaNull_one_iff_isEffectivelyNull_uniform`, `Kolmogorov.isEffectiveAlphaNull_one_of_isEffectivelyNull_uniform`, `Kolmogorov.isEffectivelyNull_uniform_of_isEffectiveAlphaNull_one`, `Kolmogorov.tsum_measure_disjEnum`. |
| Problem 74 | 3 | in part | Sum, difference, product and quotient of computable reals are computable reals. Related: `Kolmogorov.ComputableReals.IsComputableReal.add`, `Kolmogorov.ComputableReals.IsComputableReal.sub`, `Kolmogorov.ComputableReals.IsComputableReal.mul`, `Kolmogorov.ComputableReals.IsComputableReal.neg`. |
| Problem 76 | 3 | not formalized | Elementary functions (roots, sine, exp, log, ...) map computable arguments to computable values. |
| Problem 77 | 3 | no definite claim | Explain why the definition of correctness (of the regular-function lemma) has to be changed. |
| Problem 78 | 3 | not formalized | For an upper semicomputable measure there exists a largest effectively null set. |
| Problem 79 | 3 | not formalized | There is a non-computable measure with no largest effectively null set. |
| Problem 80 | 3 | not formalized | There is a non-computable measure for which a largest effectively null set exists. |
| Problem 86 | 3 | weaker form | The minimal point not covered by an enumerable family of rational open intervals is lower semicomputable. Related: `Kolmogorov.isLowerSemicomputableReal_leftmostReal`, `Kolmogorov.exists_isLowerSemicomputableReal_isMartinLofRandomReal`. |
| Problem 87 | 3 | not formalized | If x_i is a computable sequence of strings whose sum of 2^{-l(x_i)} is less than 1 and computable, then there is a computable sequence with no x_i as a prefix. |
| Problem 88 | 3 | not formalized | Requiring the cover's total measure to equal exactly eps gives a definition equivalent to Schnorr effectively null sets. |
| Problem 89 | 3 | not formalized | There is a Schnorr random sequence whose prefixes have complexity C = O(log n). |
| Problem 91 | 3 | not formalized | A set is Kurtz effectively null iff it is contained in the complement of an effectively open set of measure 1. |
| Problem 96 | 4 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 104 | 4 | weaker form | If A and B are prefix-free sets of strings, then AB = {ab : a in A, b in B} is prefix-free. Related: `Kolmogorov.Code.isPrefixFree_concat`. |
| Problem 113 | 4 | not formalized | Give a direct proof of Theorem 69 (recover K(x) from x, y, K(x,y) by searching for d with K(y\|x,d) + d = K(x,y)). |
| Problem 122 | 5 | not formalized | Theorem 76 (every lsc semimeasure is generated by a probabilistic algorithm) still holds when the fair-coin input is replaced by any computable atomless distribution. |
| Problem 124 | 5 | not formalized | The theory of generators and maximal semimeasures carries over to algorithms that output natural numbers, i.e. to lsc semimeasures on finite and infinite sequences of naturals. |
| Problem 125 | 5 | not formalized | The maximal semimeasure on sequences of naturals restricted to length-1 sequences equals discrete a priori probability, and restricted to binary sequences equals the maximal binary semimeasure, both up to O(1). |
| Problem 127 | 5 | not formalized | There is c such that for every n some string x has KA(x) < c and KA(x reversed) > n. |
| Problem 130 | 5 | not formalized | KA(xy) ≤ K(x) + KA(y) + O(1), and this fails for KA(yx). |
| Problem 138 | 5 | not formalized | For infinitely many n, every string of length n has KM(x) − KA(x) ≤ log log log n (or any unbounded non-decreasing computable function). |
| Problem 139 | 5 | not formalized | In the Gács–Day game, if the tree height is below d/4 then Server, not Client, has a winning strategy. |
| Problem 142 | 5 | not formalized | In the Levin–Schnorr proof, the first half needs only an upper semicomputable P and the second half only a lower semicomputable P. |
| Problem 148 | 5 | in part | For omega ML-random w.r.t. a computable mu: (a) -log mu(x) − K(x) → −∞ along prefixes; (b) if K(x) ≤ -log mu(x) + log l(x) + c for all prefixes, omega is not random. Related: `Kolmogorov.tsum_two_pow_mul_complexityWeight_KPPlain_ne_top_of_isMartinLofRandom_uniform`, `Kolmogorov.isMartinLofRandom_uniform_iff_tsum_prefixExcess_ne_top`, `Kolmogorov.problem_146_isMaximalExpectationBoundedTest`. |
| Problem 149 | 5 | in part | Theorem 98 (ML-random iff C((ω)_n) ≥ n − K(n) − O(1)) still holds with conditional complexity C((ω)_n \| n). Related: `Kolmogorov.le_condK_cantorPrefix_add_KPPlain_of_isMartinLofRandom_uniform`, `Kolmogorov.isMartinLofRandom_uniform_of_le_plainK_add_KPPlain`, `Kolmogorov.exists_const_condK_le_plainK`. |
| Problem 150 | 5 | not formalized | f(n) = 2 log n does not work in Theorem 96: some non-random sequence has C((ω)_n\|n) ≥ n − 2 log n − O(1); likewise no computably convergent f works. |
| Problem 152 | 5 | not formalized | Theorem 99 holds for every constant c, including negative ones, not just for some c. |
| Problem 153 | 5 | not formalized | Conditional version of Theorem 99 with log n replaced by a computable f with divergent sum 2^{−f(n)}: C((ω)_n\|n) ≤ n − f(n) + c infinitely often. |
| Problem 154 | 5 | weaker form | For ML-random omega and computable f with ∑2^{−f(n)} computably convergent, C((ω)_n\|n) ≥ n − f(n) for all large n, with no additive constant. Related: `Kolmogorov.le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform`, `Kolmogorov.le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform_general`. |
| Problem 155 | 5 | not formalized | For almost every omega (uniform measure) there is c with C((ω)_n\|n) ≥ n − c for infinitely many n. |
| Problem 156 | 5 | not formalized | If C((ω)_n\|n) ≥ n − c for infinitely many n, then omega is ML-random. |
| Problem 157 | 5 | not formalized | Problem 156 holds with unconditional C((ω)_n) in place of C((ω)_n\|n). |
| Problem 159 | 5 | not formalized | The square (sine, exponent) of a random real is a random real. |
| Problem 160 | 5 | not formalized | The sum of two random reals can be non-random (e.g. dependent reals like α and −α). |
| Problem 163 | 5 | not formalized | If U is an effectively open subset of [0,1] with measure < 1 containing all non-ML-random reals, then the measure of U is a lower semicomputable ML-random real. |
| Problem 164 | 5 | not formalized | For an optimal prefix-free decompressor U, f(p,x,n) (l(p) if U(p)=x in exactly n steps, else 2l(p)+2l(x)+2log n) bounds K(p,x,n) from above, tightly on shortest slow descriptions; this gives another proof of existence of Solovay functions. |
| Problem 166 | 5 | not formalized | Define alpha-null sets of reals via arbitrary (unaligned) intervals and show A in [0,1] is alpha-null iff the set of binary representations of A is alpha-null in Cantor space. |
| Problem 168 | 5 | not formalized | Define Hausdorff dimension in R^3, explain why it is 3/2/1/0 for solids, surfaces, curves, points, and show every d in [0,3] occurs. |
| Problem 171 | 5 | not formalized | For an effectively closed subset of Cantor space the effective Hausdorff dimension equals the classical Hausdorff dimension. |
| Problem 173 | 5 | in part | For every real alpha in [0,1] there is a subset of Omega of classical Hausdorff dimension alpha (sequences with zeros at specified places). Related: `Kolmogorov.dilSet`, `Kolmogorov.isEffectiveAlphaNull_dilSet`, `Kolmogorov.not_isAlphaNull_dilSet`, `Kolmogorov.IsEffectiveAlphaNull.isAlphaNull`. |
| Problem 175 | 5 | not formalized | A sequence random w.r.t. some computable measure is either computable or Turing-equivalent to a uniformly ML-random sequence. |
| Problem 177 | 5 | available in Mathlib | Baire category theorem for Cantor space: intersection of countably many dense open sets is dense. Mathlib: `dense_iInter_of_isOpen`. |
| Problem 178 | 5 | not formalized | Every (weakly 1-)generic sequence violates the strong law of large numbers. |
| Problem 179 | 5 | not formalized | No generic sequence is computable. |
| Problem 180 | 5 | not formalized | A generic sequence is not ML-random w.r.t. any computable measure. |
| Problem 181 | 5 | not formalized | There is an enumerable set whose characteristic sequence is not random w.r.t. any computable measure. |
| Problem 182 | 5 | not formalized | There is an enumerable undecidable set whose characteristic sequence is ML-random w.r.t. some computable measure. |
| Problem 183 | 5 | not formalized | There is a non-computable oracle A such that no A-computable sequence is random w.r.t. a computable measure (except computable sequences at atoms). |
| Problem 184 | 5 | not formalized | There is a sequence Turing-equivalent to a uniformly ML-random sequence but not random w.r.t. any computable measure. |
| Problem 188 | 5 | not formalized | Every ML-random sequence for Bernoulli(1/3) can be turned into a uniformly ML-random sequence by replacing some zeros with ones. |
| Problem 189 | 5 | not formalized | Two computable maps with the same output semimeasure whose images of the uniformly random sequences differ. |
| Problem 190 | 5 | not formalized | The random sequence in the Kucera-Gacs proof is computable from oracles alpha and 0'. |
| Problem 191 | 5 | not formalized | For every sequence alpha there is an ML-random omega with alpha <=_T omega with use n + o(n). |
| Problem 197 | 6 | in part or weaker | part (c) in a weaker form; see `docs/suv_chapter_06.md` |
| Problem 203 | 6 | in part or weaker | weaker form; see `docs/suv_chapter_06.md` |
| Problem 204 | 6 | in part or weaker | in part; see `docs/suv_chapter_06.md` |
| Problem 207 | 6 | not formalized | Prefix complexity with a set condition K(x\|\|A) is the same up to O(1) whether decompressors are prefix-stable in the first argument or computable continuous maps Sigma -> F (partial functions N -> N). |
| Problem 210 | 6 | in part or weaker | in part; see `docs/suv_chapter_06.md` |
| Problem 223 | 7 | no definite claim | Look closely at the alternative proof of the entropy pair inequality and trace how it corresponds to the earlier proof. |
| Problem 245 | 8 | in part or weaker | weaker form; see `docs/suv_chapters_08_09.md` |
| Problem 277 | 9 | in part or weaker | weaker form; see `docs/suv_chapters_08_09.md` |
| Problem 290 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 291 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 294 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 295 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 299 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 300 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 304 | 10 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 320 | 12 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 329 | 12 | not formalized | Using random linear transformations, give a probabilistic algorithm that finds the maximal flow in a directed acyclic graph with integer capacities (hint: test whether a flow of size n exists by random matrices at vertices and an n×n invertibility check). |
| Problem 330 | 12 | not formalized | If every value of theta has positive probability, whether N(X) is a sufficient statistic depends only on P[X=x \| theta=t]. Equivalently, N is sufficient iff arguments with equal N-value have proportional likelihood vectors. |
| Problem 346 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 347 | 14 | weaker form | Prefix deficiency d_P(x\|A) = log\|A\| − K(x\|A) is the maximal lower semicomputable δ with (1/\|A\|)·Σ_{x∈A} 2^{δ(x\|A)} ≤ 1. Related: `Kolmogorov.canonicalTest`, `Kolmogorov.canonicalTest_expectation_le_one`, `Kolmogorov.canonicalTest_is_maximal`. |
| Problem 349 | 14 | partly archived | one half proved, the other kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 351 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 352 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 355 | 14 | in part | For n' < n, the string k_{n'} is O(log n)-equivalent to the length-n' prefix of k_n; the same holds for m_n. Related: `Kolmogorov.prop_omega_equivalence`, `Kolmogorov.prop_omegas`, `Kolmogorov.prop_busy_beavers`. |
| Problem 361 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 362 | 14 | in part | x (n-bit, complexity k) is (α,β)-stochastic iff (α, C(x)−α+β) ∈ P_x or α > C(x), with log accuracy. Related: `Kolmogorov.stochasticity_to_optimal_set_thm`, `Kolmogorov.isOptimalSetStochastic_imp_profile`, `Kolmogorov.setOptimalityDeficiencyLe_of_profile`, `Kolmogorov.randomness_optimality`. |
| Problem 364 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 366 | 14 | partly archived | one half proved, the other kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 367 | 14 | archived | statement kept in `docs/ARCHIVED_TARGETS.md` |
| Problem 368 | 14 | in part | For 𝒜 satisfying (1)–(3) and α ≤ C(x), three conditions are equivalent with log precision: some A∈𝒜 with C(A)≤α and d(x\|A)≤β; the same with δ(x\|A)≤β; and (α, C(x)−α+β) ∈ P_x^𝒜. Related: `Kolmogorov.restricted_stochasticity_to_optimal_set_thm`, `Kolmogorov.randomness_optimality`, `Kolmogorov.setOptimalityDeficiencyLe_of_profile`, `Kolmogorov.inDescriptionProfileIn_improving_size`. |
