# Archived SUV targets

These book items were deliberately **not** formalised.  Each was reviewed against the
book text on 2026-09-06 and judged to be a reader exercise or a restatement of material
the library already carries, rather than a result whose formalisation adds anything.
The Lean statements are preserved verbatim below, so any of them can be restored.  The
items that *are* formalised are the ones the book itself attributes to a publication or
presents as a theorem of the subject; they live with the rest of their topic, and
`docs/SUV_COVERAGE.md` says where.  The module paths quoted under the individual entries
refer to a statements-only directory that the library no longer has.

A second batch, eleven items of Chapters 10 and 12, was archived on 2026-09-29 for other
reasons: results the book cites without proof, and exercises that need machinery outside
its scope.  It is the last section below.

Problem 291 was archived separately on 2026-10-01 after its core uniformity lemma resisted
the proof campaign; its complete Lean source is preserved in the final section.

---

## ch01-exercise-7

Counting exercise: every string has a Hamming-distance-one neighbour of complexity `n - log n + O(1)`. Half a page in the book, no downstream use.

Was in `KolmogorovMathlib/SUVStatements/Chapter01.lean`.

```lean
/-- **Exercise 7.** Every string of positive length `n` has a Hamming-distance one
neighbour of complexity at most `n - log n + O(1)`. -/
theorem exercise07_hamming_neighbour (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (n : ℕ) (hn : 0 < n) (x : BitString), x.length = n → ∃ i < n,
      plainK U (x.set i (!x.getD i false)) ≤ ((n - Nat.log 2 n + k : ℕ) : ℕ∞) := by
  sorry
```


## ch01-exercise-9

Relativisation of Theorem 15 to `0'`. Meaningful only as a corollary once Theorem 15 is proved; no independent content.

Was in `KolmogorovMathlib/SUVStatements/Chapter01.lean`.

```lean
/-- **Exercise 9.** Relative to the halting oracle all nine canonical objects have
complexity `O(log n)`. -/
theorem exercise09_relativized (U : Map) (hU : isOptimalConditional U)
    (c : Code) (hc : IsCodeFor c U)
    (W : Map) (hW : IsOptimalConditionalIn
      (charOracle { e | ((Denumerable.ofNat Code e).eval e).Dom }) W) :
    ∃ k : ℕ, ∀ i ≤ 8, ∀ n : ℕ,
      plainK W (canonicalObject U c i n) ≤ ((logSlack k n : ℕ) : ℕ∞) := by
  sorry
```


## ch01-exercise-10

The book asks to "find **some** upper bound for the number of oracle queries" - it prescribes no statement at all, so any Lean rendering picks an arbitrary bound (this one picked `2^(n+k)`). There is nothing here to be faithful to.

Was in `KolmogorovMathlib/SUVStatements/Chapter01.lean`.

```lean
/-- **Exercise 10.** The `2 ^ (n + c)` answers of the oracle `{(x, k) | C(x) < k}`
on the strings of length `n + c` and threshold `n + c` suffice to solve the
halting problem for a fixed machine on all inputs of length at most `n`; this is
the query bound provided by the argument of the book. -/
theorem exercise10_query_bound (U : Map) (hU : isOptimalConditional U)
    (M : BitString →. BitString) (hM : Partrec M) :
    ∃ k : ℕ, ∃ A : ℕ × List Bool → List BitString, Computable A ∧
      ∀ (n : ℕ) (x : BitString),
        x ∈ A (n, (allStrings (n + k)).map
            (fun y => decide (plainK U y < ((n + k : ℕ) : ℕ∞)))) ↔
          (x.length ≤ n ∧ (M x).Dom) := by
  sorry
```


## ch02-exercise-20

The coefficient 2 in Theorem 16 cannot be lowered to 1 but any 1+eps works. A variation on Theorem 16 whose content is the convergence of a series; the most expensive item of the whole effort (14 attempts) for the least content.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 20, negative half.** The coefficient `2` in Theorem 16 cannot be
replaced by `1` at any depth `m ≥ 1`. -/
theorem exercise20_coefficient_one_false (U : Map) (hU : isOptimalConditional U)
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y +
        ((((List.range m).map (fun i => (Nat.log 2)^[i + 1] (cVal U x))).sum + k : ℕ) : ℕ∞) := by
  sorry
```

```lean
/-- **Exercise 20, positive half.** Every coefficient `1 + ε` is sufficient at
any depth `m ≥ 1`. -/
theorem exercise20_coefficient_one_plus_eps (U : Map) (hU : isOptimalConditional U)
    (eps : ℝ) (heps : 0 < eps) (m : ℕ) (hm : 1 ≤ m) :
    ∃ k : ℕ, ∀ x y : BitString,
      (cPairVal U x y : ℝ) ≤
        (cVal U x : ℝ) + (cVal U y : ℝ) +
        (((List.range (m - 1)).map (fun i => (Real.logb 2)^[i + 1] (cVal U x : ℝ))).sum : ℝ) +
        (1 + eps) * (Real.logb 2)^[m] (cVal U x : ℝ) + (k : ℝ) := by
  sorry
```


## ch02-exercise-30

Total conditional complexity can exceed the ordinary one. Textbook illustration.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 30.** Total conditional complexity can exceed conditional
complexity by a linear amount. -/
theorem exercise30_total_gap (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ n : ℕ, ∃ x y : BitString, x.length = n ∧ y.length = n ∧
      condK U x y ≤ (k : ℕ∞) ∧ (n : ℕ∞) ≤ totalCondComplexity U x y := by
  sorry
```


## ch02-exercise-31

Permutation of complexity at most `2n + O(1)` mapping x to y. Textbook.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 31.** Small total conditional complexity in both directions gives a
computable permutation of complexity at most `2 n + O(1)` mapping `x` to `y`. -/
theorem exercise31_permutation (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString),
      totalCondComplexity U x y ≤ (n : ℕ∞) → totalCondComplexity U y x ≤ (n : ℕ∞) →
      ∃ (pi : BitString → BitString) (e : ℕ), Function.Bijective pi ∧ pi x = y ∧
        (∀ w : BitString, Encodable.encode (pi w) ∈
          (Denumerable.ofNat Code e).eval (Encodable.encode w)) ∧
        plainKNat U e ≤ ((2 * n + k : ℕ) : ℕ∞) := by
  sorry
```


## ch02-exercise-32

Matching lower bound for Problem 31. Textbook, and only meaningful together with 31.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 32.** The bound of the preceding exercise is essentially optimal:
there are simple strings of length `n = 2 k + O(1)` all of whose connecting
permutations have complexity at least `2 k`. -/
theorem exercise32_permutation_lower_bound (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ k : ℕ, ∃ (n : ℕ) (x y : BitString), x.length = n ∧ y.length = n ∧
      n ≤ 2 * k + c ∧ 2 * k ≤ n + c ∧
      plainK U x ≤ ((k + c : ℕ) : ℕ∞) ∧ plainK U y ≤ ((k + c : ℕ) : ℕ∞) ∧
      ∀ (pi : BitString → BitString) (e : ℕ),
        (∀ w : BitString, w.length = n → (pi w).length = n) →
        (∀ w1 w2 : BitString, w1.length = n → w2.length = n → pi w1 = pi w2 → w1 = w2) →
        pi x = y →
        (∀ w : BitString, w.length = n → Encodable.encode (pi w) ∈
          (Denumerable.ofNat Code e).eval (Encodable.encode w)) →
        ((2 * k : ℕ) : ℕ∞) ≤ plainKNat U e := by
  sorry
```


## ch02-exercise-46

`exists y of length n with C(xy) >= C(x|n) + n - c`. A direct application of Theorem 19, auxiliary to Problem 47.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 46.** One can append `n` bits raising the complexity by
essentially `n`. -/
theorem exercise46_append (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), ∃ y : BitString, y.length = n ∧
      condK U x (Nat.bits n) + (n : ℕ∞) ≤ plainK U (x ++ y) + (c : ℕ∞) := by
  sorry
```


## ch02-exercise-47

Realisation of a prescribed complexity profile for the prefixes of a sequence. Textbook construction.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 47.** Every admissible growth profile is realized by an infinite
sequence, with `O(1)` precision. -/
theorem exercise47_profile (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (eps : ℝ) (heps : 0 < eps) (H : ℕ)
    (hlow : ∀ n h : ℕ, H ≤ h → (f n : ℝ) + eps * h ≤ (f (n + h) : ℝ))
    (hhigh : ∀ n h : ℕ, H ≤ h → (f (n + h) : ℝ) ≤ (f n : ℝ) + (1 - eps) * h) :
    ∃ (w : ℕ → Bool) (c : ℕ), ∀ n : ℕ,
      plainK U (seqPrefix w n) ≤ ((f n + c : ℕ) : ℕ∞) ∧
        ((f n : ℕ) : ℕ∞) ≤ plainK U (seqPrefix w n) + (c : ℕ∞) := by
  sorry
```


## ch02-exercise-56

The deficiency chain rule `d(xy) = d(x) + d(y|x) + O(log d(xy))`. A restatement of the symmetry of information in deficiency language.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 56.** Chain rule for randomness deficiencies:
`d(xy) = d(x) + d(y | x) + O(log d(xy))`, where `d(y | x) = |y| - C(y | x)`. -/
theorem exercise56_deficiency_chain (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (n : ℕ) (x y : BitString), x.length = n → y.length = n →
      |deficiency U (x ++ y) -
          (deficiency U x + ((y.length : ℤ) - (condCVal U y x : ℤ)))| ≤
        (c : ℤ) * ((Nat.log 2 (deficiency U (x ++ y)).toNat : ℤ) + 1) := by
  sorry
```


## ch02-exercise-57

`{(x,y) : C(x|y) < c}` is Turing complete. Short classical exercise.

Was in `KolmogorovMathlib/SUVStatements/Chapter02.lean`.

```lean
/-- **Exercise 57.** For all sufficiently large thresholds `c`, the enumerable set
`{(x, y) | C(x | y) < c}` is Turing complete. -/
theorem exercise57_turing_complete (U : Map) (hU : isOptimalConditional U) :
    ∃ c0 : ℕ, ∀ c ≥ c0, IsEnumerableSet {p : BitString × BitString | condK U p.1 p.2 < (c : ℕ∞)} ∧
      RecursiveIn {charOracle
        {n : ℕ | ∃ p : BitString × BitString, Encodable.encode p = n ∧
          condK U p.1 p.2 < (c : ℕ∞)}}
        (charOracle {e | ((Denumerable.ofNat Code e).eval e).Dom}) := by
  sorry
```


## ch04-theorem-51

Robust programs compute exactly the computable prefix-stable functions. Interface result for the prefix-machine section; the library already has the prefix-stability layer it motivates.

Was in `KolmogorovMathlib/SUVStatements/Chapter04.lean`.

```lean
/-- **Theorem 51 (a).** The function computed by a robust program is computable
and prefix stable. -/
theorem theorem51_robust_prefixStable (c : Code) (f : BitString →. BitString)
    (hc : IsRobustProgram c) (hf : NBComputes c f) :
    Partrec f ∧ IsPrefixStableFun f := by
  sorry
```

```lean
/-- **Theorem 51 (b).** Every computable prefix-stable function is computed by a
robust program. -/
theorem theorem51_prefixStable_robust (f : BitString →. BitString)
    (hf : Partrec f) (hs : IsPrefixStableFun f) :
    ∃ c : Code, IsRobustProgram c ∧ NBComputes c f := by
  sorry
```


## ch04-exercise-96

Robustification algorithm; the constructive companion of Theorem 51, archived with it.

Was in `KolmogorovMathlib/SUVStatements/Chapter04.lean`.

```lean
/-- **Exercise 96.** There is an algorithm turning every asynchronous program
into a robust one that computes the same function whenever the original program
was already robust (and a computable prefix-stable function in any case). -/
theorem exercise96_robustification :
    ∃ g : Code → Code, Computable g ∧ (∀ c, IsRobustProgram (g c)) ∧
      (∀ c, ∃ f, NBComputes (g c) f ∧ Partrec f ∧ IsPrefixStableFun f) ∧
      (∀ c f, IsRobustProgram c → NBComputes c f → NBComputes (g c) f) := by
  sorry
```


## ch14-theorem-250

Fraction of non-(alpha,beta)-stochastic strings. The library formalises Chapter 14 through Vereshchagin-Shen, *Algorithmic statistics: forty years later*, which is sharper than the chapter; the counting statements here should follow from the profile-cardinality and profile-comparison theorems already proved in the library rather than be re-proved from the book.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
open Classical in
/-- **Theorem 250.** If `2 alpha + beta < n - O(log n)`, then at least a
`2^{-2 alpha - beta - O(log n)}` fraction of the strings of length `n` fails to be
`(alpha, beta)`-stochastic. -/
theorem theorem250_nonstochastic_fraction (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n alpha beta : ℕ),
      2 * alpha + beta + logSlack c n < n →
      2 ^ n ≤ 2 ^ (2 * alpha + beta + logSlack c n) *
        ((stringsOfLength n).filter (fun x => IsNonStochastic U x alpha beta)).card := by
  sorry
```


## ch14-theorem-254

Four equivalent descriptions of the two-dimensional strata. Technical repackaging of the stratification; the substance is already carried by the profile layer taken from the paper.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Theorem 254.** The four properties (a)–(d) of a string `x` are equivalent,
each implying the others after a logarithmic change of the parameters.  The
simplicity budget for the algorithms in (b), (c), (d) is `O(log n)`, and every
implication shifts the parameters by at most `logSlack c n`. -/
theorem theorem254_equivalences (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j : ℕ), x.length = n → i + j ≤ n →
      (Prop254a U x i j →
        Prop254c U x (logSlack c n) (i + logSlack c n) (j + logSlack c n)) ∧
      (Prop254c U x (logSlack c n) i j →
        Prop254a U x (i + logSlack c n) j) ∧
      (Prop254a U x i j →
        Prop254b U x (logSlack c n) (i + logSlack c n) j) ∧
      (Prop254b U x (logSlack c n) i j →
        Prop254a U x (i + logSlack c n) j) ∧
      (Prop254a U x i j →
        Prop254d V U x (logSlack c n) (i + j + logSlack c n) j) ∧
      (Prop254d V U x (logSlack c n) (i + j) j →
        Prop254b U x (logSlack c n) (i + logSlack c n) j) := by
  sorry
```


## ch14-exercise-346

Universality of the randomness deficiency among normalised lower-semicomputable non-typicality measures. The book itself calls it "a direct corollary" of Theorem 19.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
open Classical in
/-- **Exercise 346.** The plain randomness deficiency is maximal, up to an additive
constant, among lower-semicomputable tests obeying the counting bound. -/
theorem exercise346_deficiency_maximal (U : Map) (hU : isOptimalConditional U)
    (delta : BitString → BitString → ℕ) (hlsc : IsLowerSemicomputableTest delta)
    (hcount : ∀ (A : Finset BitString) (hA : A.Nonempty) (k : ℕ),
      (A.filter (fun x => k < delta x (codedUniformOn A hA).code)).card * 2 ^ k < A.card) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString), x ∈ A →
      (delta x (codedUniformOn A hA).code : ℕ∞) ≤ plainDeficiencyValue U A hA x + (c : ℕ∞) := by
  sorry
```


## ch14-exercise-349

Prefixes of a measure-ML-random sequence are `(O(log n), O(log n))`-stochastic. The second half of the problem is already proved in the library as SUV Theorem 122; this half is a bridge exercise.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Exercise 349, first part.** All prefixes of a sequence that is Martin-Löf
random for a computable measure are `(O(log n), O(log n))`-stochastic. -/
theorem exercise349_random_prefixes_stochastic (U : Map) (hU : IsOptimalPrefixConditional U)
    (mu : MeasureTheory.Measure _root_.CantorSeq)
    (hmu : MeasureTheory.IsProbabilityMeasure mu)
    (hmuc : Kolmogorov.IsComputableMeasure mu)
    (w : _root_.CantorSeq) (hw : Kolmogorov.IsMartinLofRandom mu w) :
    ∃ c : ℕ, ∀ n : ℕ,
      IsStochastic U (_root_.cantorPrefix w n) (logSlack c n) (logSlack c n) := by
  sorry
```


## ch14-exercise-351

A counting remark showing the `O(m)` term of Theorem 253 cannot be dropped.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Exercise 351.** The dependence on the complexity `m` of the prescribed
curve in the profile-realization theorem `exists_string_with_profile` cannot be
removed: there is no realization with a purely logarithmic error term. -/
theorem exercise351_curve_complexity_needed (U : Map) (hU : IsOptimalPrefixConditional U) :
    ¬ ∃ c_real : ℕ, ∀ (c n kx m : ℕ) (h : ℕ → ℕ), ProfileCurve U c n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, InDescriptionProfile U x (i + logSlack c_real n) (h i + logSlack c_real n)) ∧
        (∀ i, ¬ InDescriptionProfile U x i (h i - logSlack c_real n)
            ∨ h i ≤ logSlack c_real n) := by
  sorry
```


## ch14-exercise-352

No algorithm finds the boundary of `P_x` within `O(log l(x))`. The book itself points elsewhere for the real result: "Stronger results on non-computability of the boundary of P_x can be found in [203]". Pure reader exercise, and the most bureaucracy-generating item in the campaign.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Exercise 352.** The boundary of the description profile `P_x` is not
computable with accuracy `O(log |x|)`: no total computable function of `x` and
the complexity budget locates the whole boundary of `P_x` within a logarithmic
slack.

The algorithm returns `Option ℕ` so that it can report the vertical part of the
boundary, where the structure function is `⊤` because `x` has no description at
that complexity budget: `none` must be answered exactly there.  Guarding the
approximation by `structureFunction U x i ≠ ⊤` instead would let the algorithm
answer arbitrarily on that region, which asks for strictly more than the source
does; demanding a numeric answer there would make the statement vacuous, since
`⊤ ≤ (v : ℕ∞) + slack` is unsatisfiable. -/
theorem exercise352_boundary_not_computable (U : Map) (hU : IsOptimalPrefixConditional U) :
    ¬ ∃ (f : BitString → ℕ → Option ℕ), Computable₂ f ∧ ∃ c : ℕ, ∀ (x : BitString) (i : ℕ),
      (f x i = none ↔ structureFunction U x i = ⊤) ∧
      ∀ v : ℕ, f x i = some v →
        structureFunction U x i ≤ (v : ℕ∞) + (logSlack c x.length : ℕ∞) ∧
        (v : ℕ∞) ≤ structureFunction U x i + (logSlack c x.length : ℕ∞) := by
  sorry
```


## ch14-exercise-361

Hamming-ball description profiles. Structural, but part of the paper-based layer rather than a result the chapter adds.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Exercise 361 (1).** With `O(log n)` precision, `C_r(x)` is the minimal `i`
such that `x` has an `(i * log V(r))`-description that is a Hamming ball. -/
theorem exercise361_approxComplexity_eq_hammingBallProfileMin (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n r : ℕ), x.length = n → 2 * r ≤ n →
      approxComplexity V x r ≤ hammingBallProfileMin U x n r + (logSlack c n : ℕ∞) ∧
      hammingBallProfileMin U x n r ≤ approxComplexity V x r + (logSlack c n : ℕ∞) := by
  sorry
```

```lean
/-- **Exercise 361 (2), shape constraints.** The function `r ↦ C_r(x)` starts at
`C(x)`, reaches `O(log n)` at radius `n / 2`, is nonincreasing, and decreases by at most
`log (V(b)/V(a))` between radii `a < b`. -/
theorem exercise361_approxComplexity_shape (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), x.length = n →
      approxComplexity V x 0 = plainK V x ∧
      approxComplexity V x (n / 2) ≤ (logSlack c n : ℕ∞) ∧
      (∀ a b : ℕ, a < b → 2 * b ≤ n →
        approxComplexity V x b ≤ approxComplexity V x a ∧
        approxComplexity V x a ≤ approxComplexity V x b
          + ((Nat.log 2 (hammingVol n b) - Nat.log 2 (hammingVol n a) : ℕ) : ℕ∞)
          + (logSlack c n : ℕ∞)) := by
  sorry
```

```lean
/-- **Exercise 361 (2), realization.** Every shape satisfying those constraints
is realized, with precision `O(√(n log n))`, by the approximation-complexity
function of some string of length `n` and complexity `k + O(√(n log n))`. -/
theorem exercise361_approxComplexity_realization (V U : Map)
    (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n k : ℕ) (t : ℕ → ℕ), k ≤ n → t 0 = k → t (n / 2) = 0 →
      (∀ a b : ℕ, a < b → 2 * b ≤ n → t b ≤ t a ∧
        t a ≤ t b + (Nat.log 2 (hammingVol n b) - Nat.log 2 (hammingVol n a))) →
      ∃ x : BitString, x.length = n ∧
        plainK V x ≤ ((k + sqrtLogSlack c n : ℕ) : ℕ∞) ∧
        ((k : ℕ∞) ≤ plainK V x + (sqrtLogSlack c n : ℕ∞)) ∧
        ∀ a : ℕ, 2 * a ≤ n →
          approxComplexity V x a ≤ ((t a + sqrtLogSlack c n : ℕ) : ℕ∞) ∧
          ((t a : ℕ∞) ≤ approxComplexity V x a + (sqrtLogSlack c n : ℕ∞)) := by
  sorry
```


## ch14-exercise-364

Sharpening of Theorem 250 to `alpha + beta`. Archived with Theorem 250, for the same reason.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
open Classical in
/-- **Exercise 364.** Under the weaker hypothesis `alpha + beta < n - O(log n)`,
the fraction of non-`(alpha, beta)`-stochastic strings of length `n` is at least
`2^{-alpha-beta-O(log n)}` (note: this exponent is `alpha + beta`, not the
`2 alpha + beta` of Theorem 250). -/
theorem exercise364_nonstochastic_fraction_weak (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n alpha beta : ℕ),
      alpha + beta + logSlack c n < n →
      2 ^ n ≤ 2 ^ (alpha + beta + logSlack c n) *
        ((stringsOfLength n).filter (fun x => IsNonStochastic U x alpha beta)).card := by
  sorry
```


## ch14-exercise-366

Characterisation of the stochasticity region `Q_x`. The structural half is already proved in the library; the realisation half belongs to the paper-based layer.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Exercise 366, realization half.** Every admissible shape is the
stochasticity profile of some string, up to `O(log n) + O(m)` precision, where
`m` bounds the complexity of the prescribed shape. -/
theorem exercise366_profile_realization (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (n kx m : ℕ) (s : ℕ → ℕ) (e : ℕ),
      kx ≤ n →
      Ch04.kNat U e ≤ (m : ℕ∞) →
      (∀ a, Encodable.encode (s a) ∈ (Denumerable.ofNat Code e).eval (Encodable.encode a)) →
      Antitone s → s 0 ≤ n - kx → s kx = 0 →
      ∃ x : BitString, x.length = n ∧
        KPPlain U x ≤ ((kx + logSlack c n + m : ℕ) : ℕ∞) ∧
        ((kx : ℕ∞) ≤ KPPlain U x + ((logSlack c n + m : ℕ) : ℕ∞)) ∧
        (∀ alpha beta : ℕ, alpha ≤ kx → s alpha ≤ beta →
          IsStochastic U x (alpha + logSlack c n + m) (beta + logSlack c n + m)) ∧
        (∀ alpha beta : ℕ, alpha + logSlack c n + m ≤ kx →
          beta + logSlack c n + m < s (alpha + logSlack c n + m) →
          IsNonStochastic U x alpha beta) := by
  sorry
```


## ch14-exercise-367

A slope `-1` segment on the boundary of `P_x`. Same layer, same reason.

Was in `KolmogorovMathlib/SUVStatements/Chapter14.lean`.

```lean
/-- **Exercise 367.** Suppose that among the hypotheses of complexity at most
`alpha` some set `A` achieves the minimal randomness deficiency `d`, and that its
optimality deficiency exceeds `d` by `gamma`.  Then the boundary of `P_x` — the
structure function — contains a segment of slope `-1` covering the interval
`[alpha - gamma, alpha]`: the quantity `i + h_x(i)` is constant there, up to
`O(log n)`. -/
theorem exercise367_slope_minus_one_segment (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n alpha gamma d : ℕ)
      (A : Finset BitString) (hA : A.Nonempty),
      x.length = n → x ∈ A →
      setComplexity U A hA ≤ (alpha : ℕ∞) →
      deficiencyValue U A hA x = (d : ℕ∞) →
      (∀ (B : Finset BitString) (hB : B.Nonempty), x ∈ B →
        setComplexity U B hB ≤ (alpha : ℕ∞) → (d : ℕ∞) ≤ deficiencyValue U B hB x) →
      optimalityDeficiencyValue U A hA x = ((d + gamma : ℕ) : ℕ∞) →
      ∀ i i' : ℕ, alpha - gamma ≤ i → i ≤ i' → i' ≤ alpha →
        (i' : ℕ∞) + structureFunction U x i'
            ≤ (i : ℕ∞) + structureFunction U x i + (logSlack c (n + alpha + gamma + d) : ℕ∞) ∧
        (i : ℕ∞) + structureFunction U x i
            ≤ (i' : ℕ∞) + structureFunction U x i' + (logSlack c (n + alpha + gamma + d) : ℕ∞) := by
  sorry
```


---

## 2026-09-29: chapters 10 and 12

Eleven items of Chapters 10 and 12, archived on 2026-09-29 by the owner's decision.  An axiom
sweep of the chapter statements (frozen at `22b2df6`) sorted the open items by where their
difficulty comes from.  Four are results the book **cites without proof** — formalising them
would mean reproducing the cited papers, not the book — and a fifth, Problem 304, had one of
them as its only proof route.  The other six are exercises that need **machinery outside the
book's scope** (a model-theoretic transfer between fields, a polyhedral computation in
`ℝ^15`, non-stochastic strings) or whose statement the book leaves to the reader.  No other
declaration of the library used any of them.

Each block below is the file text verbatim — docstrings, section context and bodies, with the
private helpers and the definitions that served only the item — so it can be restored by
pasting it back at the place named.  Bodies that were `sorry` are `sorry` here as well.  The
deleted declarations are recorded as `deleted` rows in `docs/history/phase24_recut.tsv`, the
table the statement-freeze check reads.

### ch10-theorem-220

Theorem 220 (Ahlswede–Körner), p. 347: the unique information of `k` independent copies can be deleted at a cost `o(k)`.  Cited without proof in the book: [2], with the proof in [113, Lemma 5].  In the book it serves only the *second* proof of Theorem 218; the library proves Theorem 218 by the first (artificial independence), and the steps of the second proof that do not use Theorem 220 (`mutualInfo_add_two_condEntropy_eq`, `mutualInfo_le_nonShannon_add_three_condEntropy`) stay.  Here it was the only proof route of Problem 304, archived below.  The definition `iidCopies` existed only to state these two.

Was in `KolmogorovMathlib/InformationInequalities/NonShannonTheorems.lean`, after the deduction rule (`holdsForEntropies_of_deduction_rule`) and before the section "The second proof of Theorem 218".

```lean
/-! ### Deleting the unique information: Ahlswede–Körner -/

/-- The `k` independent copies of a random variable, as **one** random variable on the product
space `Fin k → Ω` (with `FiniteProbSpace.power`): the tuple `(X(ω₁), …, X(ω_k))`.

This is not a second notion of an i.i.d. sequence: `FiniteProbSpace.power` already carries the
product measure, and its docstring writes the i.i.d. *family* of copies of `X` as
`fun i ω => X (ω i)`, a function `Fin k → ((Fin k → Ω) → α)`.  Theorem 220 speaks of the
entropies of the tuple `A = ⟨α₁, …, α_k⟩` as a single variable, so what it needs is that
family packed into one `α`-tuple-valued variable, i.e. `Function.swap` of it — which is what
`iidCopies` is.  SUV Theorem 220, p. 347. -/
def iidCopies {Ω α : Type} (k : ℕ) (X : Ω → α) : (Fin k → Ω) → (Fin k → α) :=
  fun ω i => X (ω i)

/-- **Theorem 220 (Ahlswede–Körner)**, stated in the book **without proof** (reference [2];
proof in [113, Lemma 5]).  Let `α, β, ε` be jointly distributed and let `A, B, E` be the
tuples of `k` independent copies.  There is a random variable `E'` on the same space such that
six of the seven regions of the diagram of `(A, B, E')` — `H(A|B,E')`, `H(B|A,E')`,
`I(A:B|E')`, `I(A:E'|B)`, `I(B:E'|A)` and `I(A:B:E')` — agree with those of `(A, B, E)` up to
`o(k)`, while the seventh, `H(E'|A,B)`, is `o(k)`.  The `o(k)` is written as: for every
`ε > 0`, for all large `k`, the error is at most `ε · k`.  SUV Theorem 220, p. 347. -/
theorem exists_delete_unique_information {Ω : Type} [Fintype Ω] {α β γ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (μ : FiniteProbSpace Ω)
    (A : Ω → α) (B : Ω → β) (E : Ω → γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ E' : (Fin k → Ω) → ℕ,
      |condEntropy (μ.power k) (iidCopies k A) (pairRV (iidCopies k B) E')
          - condEntropy (μ.power k) (iidCopies k A) (pairRV (iidCopies k B) (iidCopies k E))|
        ≤ ε * k ∧
      |condEntropy (μ.power k) (iidCopies k B) (pairRV (iidCopies k A) E')
          - condEntropy (μ.power k) (iidCopies k B) (pairRV (iidCopies k A) (iidCopies k E))|
        ≤ ε * k ∧
      |condMutualInfo (μ.power k) (iidCopies k A) (iidCopies k B) E'
          - condMutualInfo (μ.power k) (iidCopies k A) (iidCopies k B) (iidCopies k E)|
        ≤ ε * k ∧
      |condMutualInfo (μ.power k) (iidCopies k A) E' (iidCopies k B)
          - condMutualInfo (μ.power k) (iidCopies k A) (iidCopies k E) (iidCopies k B)|
        ≤ ε * k ∧
      |condMutualInfo (μ.power k) (iidCopies k B) E' (iidCopies k A)
          - condMutualInfo (μ.power k) (iidCopies k B) (iidCopies k E) (iidCopies k A)|
        ≤ ε * k ∧
      |tripleInfo (μ.power k) (iidCopies k A) (iidCopies k B) E'
          - tripleInfo (μ.power k) (iidCopies k A) (iidCopies k B) (iidCopies k E)|
        ≤ ε * k ∧
      condEntropy (μ.power k) E' (pairRV (iidCopies k A) (iidCopies k B)) ≤ ε * k := by
  sorry
```

### ch10-problem-304

Problem 304, p. 348: the two-variable case of Theorem 220.  Its only proof here was Theorem 220 applied to a triple whose first variable is constant, so it goes with that theorem; nothing depends on it.  The private lemma `condEntropy_pairRV_const_left` served only that reduction.

Was in `KolmogorovMathlib/InformationInequalities/NonShannonTheorems.lean`, right after Theorem 220 (restore that block first).

```lean
/-- Conditioning on a pair whose first component is constant is conditioning on the second
component alone: `H(ξ | c, η) = H(ξ | η)`. -/
private theorem condEntropy_pairRV_const_left {Ω α β γ : Type} [Fintype Ω] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : FiniteProbSpace Ω) (X : Ω → α) (Y : Ω → β) (c : γ) :
    condEntropy μ X (pairRV (fun _ => c) Y) = condEntropy μ X Y := by
  rw [condEntropy_eq_sub, condEntropy_eq_sub]
  have e1 : entropy μ (pairRV X (pairRV (fun _ => c) Y)) = entropy μ (pairRV X Y) :=
    entropy_eq_of_comp μ _ _ (fun p => (p.1, (c, p.2)))
      (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; simp only [Prod.mk.injEq] at h ⊢; tauto) fun _ => rfl
  have e2 : entropy μ (pairRV (fun _ => c) Y) = entropy μ Y :=
    entropy_eq_of_comp μ _ _ (fun b => (c, b))
      (by intro b b' h; simp only [Prod.mk.injEq] at h; exact h.2) fun _ => rfl
  rw [e1, e2]

/-- **Problem 304.**  The Ahlswede–Körner statement for two variables: for `k` independent
copies `A₁, A₂` of a pair `(α₁, α₂)` there is `A₂'` on the same space such that the regions
`H(A₁|A₂')` and `I(A₁:A₂')` of the diagram agree with `H(A₁|A₂)` and `I(A₁:A₂)` up to `o(k)`,
while `H(A₂'|A₁)` is `o(k)`.  SUV Problem 304, p. 348. -/
theorem exists_delete_unique_information_two {Ω : Type} [Fintype Ω] {α β : Type}
    [DecidableEq α] [DecidableEq β] (μ : FiniteProbSpace Ω) (A₁ : Ω → α) (A₂ : Ω → β)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ A₂' : (Fin k → Ω) → ℕ,
      |condEntropy (μ.power k) (iidCopies k A₁) A₂'
          - condEntropy (μ.power k) (iidCopies k A₁) (iidCopies k A₂)| ≤ ε * k ∧
      |mutualInfo (μ.power k) (iidCopies k A₁) A₂'
          - mutualInfo (μ.power k) (iidCopies k A₁) (iidCopies k A₂)| ≤ ε * k ∧
      condEntropy (μ.power k) A₂' (iidCopies k A₁) ≤ ε * k := by
  -- Theorem 220 for the triple `(constant, α₁, α₂)`: the constant carries no information.
  obtain ⟨N, hN⟩ := exists_delete_unique_information μ (fun _ : Ω => (0 : ℕ)) A₁ A₂ hε
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨A₂', -, h2, -, -, -, -, h7⟩ := hN k hk
  have hconst : iidCopies k (fun _ : Ω => (0 : ℕ)) = fun _ => (fun _ => 0) := rfl
  rw [hconst, condEntropy_pairRV_const_left, condEntropy_pairRV_const_left] at h2
  rw [hconst, condEntropy_pairRV_const_left] at h7
  refine ⟨A₂', h2, ?_, h7⟩
  have e : mutualInfo (μ.power k) (iidCopies k A₁) A₂'
        - mutualInfo (μ.power k) (iidCopies k A₁) (iidCopies k A₂)
      = -(condEntropy (μ.power k) (iidCopies k A₁) A₂'
        - condEntropy (μ.power k) (iidCopies k A₁) (iidCopies k A₂)) := by
    simp only [mutualInfo, condEntropy_eq_sub]; ring
  rw [e, abs_neg]
  exact h2
```

### ch10-theorem-219-kolmogorov

The Kolmogorov-complexity version of Theorem 219, p. 346: strings whose three pairwise conditional informations are `O(log n)` have fully extractable common information.  Cited without proof in the book ("proved in [154]"); nothing depends on it.  The definition `stringCondInfo` existed only to state it.

Was in `KolmogorovMathlib/InformationInequalities/NonShannonTheorems.lean`, right after Theorem 219 (`exists_common_information_of_pairwiseCondInfoSum_eq_zero`).

```lean
/-- The conditional mutual information of strings, `I(x : y | z) = C(x|z) + C(y|z) − C(x,y|z)`,
with plain complexities with respect to `D`.  The pair `(x, y)` is coded by `pairCode`; any
other computable pairing changes the value by `O(1)` only, which the logarithmic precision of
the statement absorbs.  Used only to state the cited Kolmogorov-complexity version of
Theorem 219.  SUV Section 10.13, p. 346. -/
noncomputable def stringCondInfo (D : Map) (x y z : BitString) : ℝ :=
  ((condK D x z).toNat : ℝ) + ((condK D y z).toNat : ℝ) - ((condK D (pairCode x y) z).toNat : ℝ)

/-- **Kolmogorov-complexity version of Theorem 219**, cited from the book's reference [154]
without proof.  If `a, b, c` are strings with `I(a:b|c)`, `I(a:c|b)` and `I(b:c|a)` all
`O(log(|a| + |b| + |c|))`, then there is a string `d` with `C(d|a)`, `C(d|b)`, `C(d|c)`,
`I(a:b|d)`, `I(b:c|d)` and `I(a:c|d)` all `O(log(|a| + |b| + |c|))`.  The constant `c₁` of
the hypothesis is arbitrary and the constant `c₂` of the conclusion depends on it; both are
quantified before the strings, and `N ≥ |a| + |b| + |c|` (the third string is `e` here).
SUV Section 10.13, p. 346 (cited without proof). -/
theorem exists_common_information_string (D : Map) (hD : isOptimalConditional D) :
    ∀ c₁ : ℕ, ∃ c₂ : ℕ, ∀ (N : ℕ) (a b e : BitString), a.length + b.length + e.length ≤ N →
      stringCondInfo D a b e ≤ (logSlack c₁ N : ℝ) →
      stringCondInfo D a e b ≤ (logSlack c₁ N : ℝ) →
      stringCondInfo D b e a ≤ (logSlack c₁ N : ℝ) →
      ∃ d : BitString,
        (condK D d a).toNat ≤ logSlack c₂ N ∧ (condK D d b).toNat ≤ logSlack c₂ N ∧
        (condK D d e).toNat ≤ logSlack c₂ N ∧
        stringCondInfo D a b d ≤ (logSlack c₂ N : ℝ) ∧
        stringCondInfo D b e d ≤ (logSlack c₂ N : ℝ) ∧
        stringCondInfo D a e d ≤ (logSlack c₂ N : ℝ) := by
  sorry
```

### ch12-program-simplification

Vyugin's "simplifying a program", p. 389 (Section 12.11): the cut-flow conditions of the request of Figure 48 are not sufficient.  Cited without proof in the book: [140]; nothing depends on it.  It was the whole content of its module, which is removed together with its import in `KolmogorovMathlib.lean`.

Was `KolmogorovMathlib/Multisource/ProgramSimplification.lean`, the whole file:

```lean
import KolmogorovMathlib.Multisource.Requests

/-!
# Simplifying a program: Vyugin's example

The request of SUV Figure 48 has two input nodes, holding a program `P` and a string `A`, and
one output node holding `A` as well, which must produce `B`; the channel from `P` has capacity
`k`.  Its cut-flow conditions are `C(B|A) ≤ k` and `C(B|A,P) ≈ 0`: the message may depend on
`P` only, and must let a decoder that knows `A` produce `B`.  In other words, is there always a
program of the minimal possible complexity `C(B|A)` from `A` to `B` that is a simplification
of `P` (carries no information beyond `P`)?

Vyugin's answer is no; the book states this without proof (reference [140]).  The statement
below is the negation of the sufficiency of the cut-flow conditions, in the same shape as
Muchnik's theorem, which is what the section contrasts it with.

SUV Section 12.11, p. 389.
-/

namespace Kolmogorov

private def IsProgramSimplificationCounterexample (D : Map) (c n k : ℕ)
    (P A B : BitString) : Prop :=
  plainK D P ≤ (n : ℕ∞) ∧ plainK D A ≤ (n : ℕ∞) ∧ plainK D B ≤ (n : ℕ∞) ∧
    condK D B A ≤ (k : ℕ∞) ∧
    condK D B (pairCode A P) ≤ (logSlack c n : ℕ∞) ∧
    ∀ X : BitString, X.length ≤ k + logSlack c n →
      ¬ (condK D X P ≤ (logSlack c n : ℕ∞) ∧
        condK D B (pairCode A X) ≤ (logSlack c n : ℕ∞))

-- This is the non-reducible-description construction cited by the book from [140].
private theorem exists_program_simplification_counterexample
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ n k : ℕ, ∃ P A B : BitString,
      IsProgramSimplificationCounterexample D c n k P A B := by
  sorry

/-- The cut-flow conditions of the request of SUV Figure 48 are not sufficient: no constant
`c` makes them yield a message `X` of length `k + O(log n)` that is simple given `P` and lets
a decoder knowing `A` produce `B`.

SUV Section 12.11, p. 389 (unnumbered claim, cited from [140] without proof). -/
theorem not_exists_programSimplification (D : Map) (hD : isOptimalConditional D) :
    ¬ ∃ c : ℕ, ∀ (n k : ℕ) (P A B : BitString),
        plainK D P ≤ (n : ℕ∞) → plainK D A ≤ (n : ℕ∞) → plainK D B ≤ (n : ℕ∞) →
        condK D B A ≤ (k : ℕ∞) → condK D B (pairCode A P) ≤ (logSlack c n : ℕ∞) →
        ∃ X : BitString, X.length ≤ k + logSlack c n ∧
          condK D X P ≤ (logSlack c n : ℕ∞) ∧
          condK D B (pairCode A X) ≤ (logSlack c n : ℕ∞) := by
  rintro ⟨c, hc⟩
  obtain ⟨n, k, P, A, B, hP, hA, hB, hBA, hBAP, hbad⟩ :=
    exists_program_simplification_counterexample D hD c
  obtain ⟨X, hXlen, hXP, hBAX⟩ := hc n k P A B hP hA hB hBA hBAP
  exact hbad X hXlen ⟨hXP, hBAX⟩

end Kolmogorov
```

### ch12-muchnik-optimality

The optimality remark after Muchnik's theorem, p. 373 (Section 12.3): the precision `O(log n)` cannot be improved to `O(log m)`, `m` bounding the two conditional complexities.  Cited without proof in the book: [205, Section 5]; nothing depends on it.

Was in `KolmogorovMathlib/Multisource/Muchnik.lean`, after Problem 319 (`exists_muchnikCode_of_complexity_left`).

```lean
/-- The precision of Muchnik's theorem cannot be improved from `O(log n)`, with `n` the
maximal *unconditional* complexity of `A` and `B`, to `O(log m)` with `m` the maximal
conditional complexity `max(C(A|B), C(B|A))`.

The book states this without proof (reference [205, Section 5]); the statement below is the
negation of the improved form, with `m` supplied as a bound on both conditional complexities.

SUV Section 12.3, p. 373 (unnumbered remark, cited). -/
theorem not_exists_muchnikCode_condLog (D : Map) (hD : isOptimalConditional D) :
    ¬ ∃ c : ℕ, ∀ (m : ℕ) (A B : BitString),
        condK D A B ≤ (m : ℕ∞) → condK D B A ≤ (m : ℕ∞) →
        ∃ X : BitString,
          (X.length : ℕ∞) ≤ condK D A B + (logSlack c m : ℕ∞) ∧
          condK D X A ≤ (logSlack c m : ℕ∞) ∧
          condK D A (pairCode B X) ≤ (logSlack c m : ℕ∞) := by
  sorry
```

### ch10-problem-295

Problem 295, p. 340: Theorem 216 over an arbitrary field.  An exercise requiring a model-theoretic transfer principle outside the book's scope: the dimensions of the sums are ranks, i.e. conditions on minors, which pass to an algebraically closed field and then, by the elementary equivalence of the algebraically closed fields of one characteristic and the Nullstellensatz, to a finite field.  Problem 294 was routed through it and is archived below.  The block also holds the proved coordinatisation lemma and the public reduction `exists_finite_field_finrank_subspaceSum_eq`, which nothing else used.

Was in `KolmogorovMathlib/InformationInequalities/Ingleton.lean`, right after Theorem 216 (`holdsForSubspaces_of_holdsForEntropies`).

```lean
/-- Coordinatisation: a tuple of finite-dimensional subspaces of an arbitrary vector space has
the same dimension vector as a tuple of subspaces of a coordinate space `F^d`, `d` being the
dimension of the sum of the subspaces.  This is the step from subspaces to matrices in the
book's proof of Problem 295: each `W_i` is spanned by the rows of a matrix, and
`dim ∑_{i ∈ I} W_i` is the rank of the matrix stacked from the blocks with `i ∈ I`.
SUV Problem 295, p. 340. -/
private lemma exists_pi_finrank_subspaceSum_eq {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] (W : Fin n → Submodule F V) [∀ i, FiniteDimensional F (W i)] :
    ∃ (d : ℕ) (W' : Fin n → Submodule F (Fin d → F)),
      ∀ I, Module.finrank F (subspaceSum W' I) = Module.finrank F (subspaceSum W I) := by
  -- `U`, the sum of all the `W i`, is finite-dimensional; a basis identifies it with `F^d`
  set U : Submodule F V := ⨆ i, W i with hU
  haveI : FiniteDimensional F U := Submodule.finiteDimensional_iSup W
  have hle : ∀ i, W i ≤ U := fun i => le_iSup W i
  set e : U ≃ₗ[F] (Fin (Module.finrank F U) → F) := (Module.finBasis F U).equivFun
  refine ⟨Module.finrank F U, fun i => ((W i).comap U.subtype).map e.toLinearMap, fun I => ?_⟩
  -- the sum of the `W i` viewed inside `U` maps back onto the sum of the `W i`
  have hmapU : ∀ I, (subspaceSum (fun i => (W i).comap U.subtype) I).map U.subtype
      = subspaceSum W I := by
    intro I
    simp only [subspaceSum, Submodule.map_iSup, Submodule.map_comap_subtype,
      inf_eq_right.2 (hle _)]
  have hmape : subspaceSum (fun i => ((W i).comap U.subtype).map e.toLinearMap) I
      = (subspaceSum (fun i => (W i).comap U.subtype) I).map e.toLinearMap := by
    simp only [subspaceSum, Submodule.map_iSup]
  rw [hmape, LinearEquiv.finrank_map_eq, ← hmapU I, Submodule.finrank_map_subtype_eq]

/-- The transfer principle for subspaces of a coordinate space: the dimension vector of a
tuple of subspaces of `F^d`, `F` an arbitrary field, is the dimension vector of a tuple of
subspaces of `F'^d` for some finite field `F'`.  The book's route: the dimensions are ranks of
matrices, hence determined by the vanishing and non-vanishing of finitely many minors; these
are polynomial conditions on the finitely many matrix entries, which survive passage to an
extension field, so the entries may be taken in an algebraically closed field, and then, by
elementary equivalence of the algebraically closed fields of one characteristic and the
Nullstellensatz, in a finite extension of a prime field `ℤ/pℤ`.  SUV Problem 295, p. 340. -/
private lemma exists_finite_field_finrank_subspaceSum_pi_eq {F : Type} [Field F] (d : ℕ)
    (W : Fin n → Submodule F (Fin d → F)) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (W' : Fin n → Submodule F' (Fin d → F')),
      ∀ I, Module.finrank F' (subspaceSum W' I) = Module.finrank F (subspaceSum W I) := by
  sorry

/-- The core of Problem 295: the vector of dimensions `I ↦ dim ∑_{i ∈ I} W_i` of a tuple of
finite-dimensional subspaces of a vector space over an arbitrary field is also the dimension
vector of a tuple of subspaces of a vector space over a *finite* field.  The book's route:
the dimensions are ranks of minors of a matrix, which survive passage to an extension field,
so algebraically closed fields suffice; those of one characteristic are elementarily
equivalent, so `ℂ` or the algebraic closure of `ℤ/pℤ` may be taken; there the matrix has
algebraic entries, which lie in a finite extension of the prime field.  SUV Problem 295,
p. 340. -/
theorem exists_finite_field_finrank_subspaceSum_eq {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] (W : Fin n → Submodule F V) [∀ i, FiniteDimensional F (W i)] :
    ∃ (F' V' : Type) (_ : Field F') (_ : Finite F') (_ : AddCommGroup V') (_ : Module F' V')
      (W' : Fin n → Submodule F' V'), (∀ i, FiniteDimensional F' (W' i)) ∧
        ∀ I, Module.finrank F' (subspaceSum W' I) = Module.finrank F (subspaceSum W I) := by
  -- first move to the coordinate space `F^d`, then change the field
  obtain ⟨d, W₁, h₁⟩ := exists_pi_finrank_subspaceSum_eq W
  obtain ⟨F', _, _, W', h'⟩ := exists_finite_field_finrank_subspaceSum_pi_eq d W₁
  exact ⟨F', Fin d → F', inferInstance, inferInstance, inferInstance, inferInstance, W',
    fun i => inferInstance, fun I => (h' I).trans (h₁ I)⟩

/-- **Problem 295.**  Theorem 216 holds over an arbitrary field: an entropy inequality is true
for dimensions of sums of finite-dimensional subspaces of any vector space over any field.  The
book's route is a transfer principle (configurations of subspaces are statements about minors,
algebraically closed fields of one characteristic are elementarily equivalent, and a finite
extension of the prime field suffices).  SUV Problem 295, p. 340. -/
theorem evalDim_nonpos_of_holdsForEntropies (f : LinearForm n) (h : HoldsForEntropies f)
    {F V : Type} [Field F] [AddCommGroup V] [Module F V] (W : Fin n → Submodule F V)
    [∀ i, FiniteDimensional F (W i)] : f.evalDim W ≤ 0 := by
  obtain ⟨F', V', _, _, _, _, W', hW', hdim⟩ := exists_finite_field_finrank_subspaceSum_eq W
  have hsub := holdsForSubspaces_of_holdsForEntropies f h F' V' W'
  unfold LinearForm.evalDim at hsub ⊢
  simpa only [hdim] using hsub
```

### ch10-problem-294

Problem 294, p. 340: Theorem 216 over `ℝ` and `ℂ`.  The book's hint is analytic (project a random point of the unit ball onto the subspaces, round, and let the rounding get finer): continuous random variables and a limit of discretised entropies, whereas the book, like the library, defines entropy on finite probability spaces only.  Here the real case was routed instead through the transfer principle of Problem 295 and the complex case through the real one, so both go with it.  Nothing depends on them.  With them go the imports `Mathlib.Data.Complex.Basic` and `Mathlib.LinearAlgebra.Complex.FiniteDimensional` of `Ingleton.lean`, which only the complex case needed.

Was in `KolmogorovMathlib/InformationInequalities/Ingleton.lean`, right after Problem 295 (restore that block first).

```lean
/-- **Problem 294**, real case: Theorem 216 holds for finite-dimensional subspaces of real
vector spaces.  The book's hint projects a random point of the unit ball onto the subspaces and
rounds.  SUV Problem 294, p. 340. -/
theorem evalDim_nonpos_real_of_holdsForEntropies (f : LinearForm n) (h : HoldsForEntropies f)
    {V : Type} [AddCommGroup V] [Module ℝ V] (W : Fin n → Submodule ℝ V)
    [∀ i, FiniteDimensional ℝ (W i)] : f.evalDim W ≤ 0 := by
  -- the transfer principle of Problem 295, applied to `ℝ`: a finite-field model of the
  -- configuration has the same dimension vector, and Theorem 216 applies to it
  obtain ⟨F', V', _, _, _, _, W', hW', hdim⟩ := exists_finite_field_finrank_subspaceSum_eq W
  have hsub := holdsForSubspaces_of_holdsForEntropies f h F' V' W'
  unfold LinearForm.evalDim at hsub ⊢
  simpa only [hdim] using hsub

/-- **Problem 294**, complex case: Theorem 216 holds for finite-dimensional subspaces of complex
vector spaces (the real dimension is twice the complex one).  SUV Problem 294, p. 340. -/
theorem evalDim_nonpos_complex_of_holdsForEntropies (f : LinearForm n) (h : HoldsForEntropies f)
    {V : Type} [AddCommGroup V] [Module ℂ V] (W : Fin n → Submodule ℂ V)
    [∀ i, FiniteDimensional ℂ (W i)] : f.evalDim W ≤ 0 := by
  -- the same subspaces over `ℝ`: every dimension doubles, so the form's value doubles
  have hsum : ∀ I, subspaceSum (fun i => (W i).restrictScalars ℝ) I
      = (subspaceSum W I).restrictScalars ℝ := by
    intro I; simp only [subspaceSum, Submodule.restrictScalars_iSup]
  have key : ∀ I, (Module.finrank ℝ (subspaceSum (fun i => (W i).restrictScalars ℝ) I) : ℝ)
      = 2 * Module.finrank ℂ (subspaceSum W I) := by
    intro I
    rw [hsum,
      ((Submodule.restrictScalarsEquiv ℝ ℂ V (subspaceSum W I)).restrictScalars ℝ).finrank_eq,
      finrank_real_of_complex]
    push_cast; ring
  haveI : ∀ i, FiniteDimensional ℝ ((W i).restrictScalars ℝ) := fun i =>
    LinearEquiv.finiteDimensional
      ((Submodule.restrictScalarsEquiv ℝ ℂ V (W i)).restrictScalars ℝ).symm
  have hreal := evalDim_nonpos_real_of_holdsForEntropies f h fun i => (W i).restrictScalars ℝ
  simp only [LinearForm.evalDim, key] at hreal
  have h2 : (2 : ℝ) * ∑ I ∈ nonemptyParts n, f I * (Module.finrank ℂ (subspaceSum W I) : ℝ)
      = ∑ I ∈ nonemptyParts n, f I * (2 * (Module.finrank ℂ (subspaceSum W I) : ℝ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun I _ => by ring
  unfold LinearForm.evalDim
  linarith
```

### ch10-problem-299

Problem 299, p. 342: every inequality for the dimensions of four subspaces that holds over all fields is a consequence of the basic inequalities and Ingleton's inequality in all orderings of the variables.  An exercise requiring what the book's hint itself calls a long computation: the faces of the cone in `ℝ^15` generated by the non-special extreme rays of the cone of basic inequalities, and Farkas' lemma for that polyhedral cone.  Problem 300 depended on it.  The block holds the definitions `LinearForm.relabel`, `IsIngletonType` and `ingletonCone`, used only here and in Problem 300, and the proved easy half (a form of Ingleton type is valid over every field) with its private helpers.

Was in `KolmogorovMathlib/InformationInequalities/Ingleton.lean`, after Problem 298 (`ingletonForm_evalGroupIndex_nonpos`), at the end of the file.

```lean
/-- A linear form with its variables renamed along a permutation `σ`: the coefficient of `I`
is the old coefficient of `σ(I)`.  Used to speak of an inequality "for all orderings of the
variables", as Problem 299 does for Ingleton's inequality.  Relabelling along `σ⁻¹` instead
gives the same orbit over all permutations, which is all the statement uses.
SUV Problem 299, p. 342. -/
def LinearForm.relabel (σ : Equiv.Perm (Fin n)) (f : LinearForm n) : LinearForm n :=
  fun I => f (I.map σ.toEmbedding)

/-- A four-variable form is of Ingleton type when it is a non-negative combination of basic
inequalities and of Ingleton's inequality for the various orderings of the variables, the
coefficients at the empty set being disregarded.  SUV Problem 299, p. 342. -/
def IsIngletonType (f : LinearForm 4) : Prop :=
  ∃ (m : ℕ) (g : Fin m → LinearForm 4) (c : Fin m → ℝ), (∀ k, 0 ≤ c k) ∧
    (∀ k, g k ∈ shannonGenerators 4 ∨
      ∃ σ : Equiv.Perm (Fin 4), g k = LinearForm.relabel σ ingletonForm) ∧
    ∀ I : Finset (Fin 4), I.Nonempty → f I = ∑ k, c k * g k I

section DimsBasic

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

/-- The sum over a union of index sets is the sum of the two sums. -/
private lemma subspaceSum_union (W : Fin n → Submodule F V) (I J : Finset (Fin n)) :
    subspaceSum W (I ∪ J) = subspaceSum W I ⊔ subspaceSum W J := by
  simp only [subspaceSum, Finset.iSup_union]

/-- The sum over an intersection of index sets lies in the intersection of the sums. -/
private lemma subspaceSum_inter_le (W : Fin n → Submodule F V) (I J : Finset (Fin n)) :
    subspaceSum W (I ∩ J) ≤ subspaceSum W I ⊓ subspaceSum W J :=
  le_inf (iSup₂_mono' fun i hi => ⟨i, Finset.mem_of_mem_inter_left hi, le_rfl⟩)
    (iSup₂_mono' fun i hi => ⟨i, Finset.mem_of_mem_inter_right hi, le_rfl⟩)

/-- Monotonicity of the sum in the index set. -/
private lemma subspaceSum_mono (W : Fin n → Submodule F V) {I J : Finset (Fin n)}
    (h : I ⊆ J) : subspaceSum W I ≤ subspaceSum W J :=
  iSup₂_mono' fun i hi => ⟨i, h hi, le_rfl⟩

/-- The indicator coefficient at `T` picks out `dim ∑_{i ∈ T} W_i` from the sum over
non-empty sets; for `T = ∅` both sides vanish. -/
private lemma sum_ite_mul_finrank_subspaceSum (W : Fin n → Submodule F V)
    (T : Finset (Fin n)) :
    ∑ S ∈ nonemptyParts n, (if S = T then (1 : ℝ) else 0)
        * (Module.finrank F (subspaceSum W S) : ℝ)
      = Module.finrank F (subspaceSum W T) := by
  by_cases hT : T.Nonempty
  · simp [ite_mul, Finset.sum_ite_eq', hT]
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.1 hT
    have h0 : Module.finrank F (subspaceSum W ∅) = 0 := by rw [subspaceSum_empty]; simp
    simp [ite_mul, Finset.sum_ite_eq', hT, h0]

variable (W : Fin n → Submodule F V) [∀ i, FiniteDimensional F (W i)]

/-- A sum of finitely many finite-dimensional subspaces is finite-dimensional. -/
private instance finiteDimensional_subspaceSum (I : Finset (Fin n)) :
    FiniteDimensional F (subspaceSum W I) :=
  Submodule.finiteDimensional_of_le (iSup₂_le fun i _ => le_iSup W i : subspaceSum W I ≤ ⨆ i, W i)

/-- Submodularity of dimensions of sums of subspaces:
`dim ∑_{I∩J} + dim ∑_{I∪J} ≤ dim ∑_I + dim ∑_J`, over any field. -/
private lemma finrank_subspaceSum_inter_add_union_le (I J : Finset (Fin n)) :
    Module.finrank F (subspaceSum W (I ∩ J)) + Module.finrank F (subspaceSum W (I ∪ J))
      ≤ Module.finrank F (subspaceSum W I) + Module.finrank F (subspaceSum W J) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (subspaceSum W I) (subspaceSum W J)
  have hm := Submodule.finrank_mono (subspaceSum_inter_le W I J)
  rw [subspaceSum_union]
  omega

/-- A basic inequality holds for dimensions over any field. -/
private lemma evalDim_basicInequality_nonpos (I J K : Finset (Fin n)) :
    (basicInequality n I J K).evalDim W ≤ 0 := by
  have hsub := finrank_subspaceSum_inter_add_union_le W (I ∪ K) (J ∪ K)
  have hmono := Submodule.finrank_mono (subspaceSum_mono W
    (Finset.subset_inter (Finset.subset_union_right : K ⊆ I ∪ K)
      (Finset.subset_union_right : K ⊆ J ∪ K)))
  have hU : I ∪ K ∪ (J ∪ K) = I ∪ J ∪ K := by
    ext x; simp only [Finset.mem_union]; tauto
  rw [hU] at hsub
  simp only [LinearForm.evalDim, basicInequality, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ite_mul_finrank_subspaceSum]
  have hsub' : (Module.finrank F (subspaceSum W ((I ∪ K) ∩ (J ∪ K))) : ℝ)
      + Module.finrank F (subspaceSum W (I ∪ J ∪ K))
      ≤ Module.finrank F (subspaceSum W (I ∪ K)) + Module.finrank F (subspaceSum W (J ∪ K)) := by
    exact_mod_cast hsub
  have hmono' : (Module.finrank F (subspaceSum W K) : ℝ)
      ≤ Module.finrank F (subspaceSum W ((I ∪ K) ∩ (J ∪ K))) := by exact_mod_cast hmono
  linarith

/-- A monotonicity form holds for dimensions over any field. -/
private lemma evalDim_monotonicityForm_nonpos (I J : Finset (Fin n)) :
    (monotonicityForm n I J).evalDim W ≤ 0 := by
  have hmono := Submodule.finrank_mono (subspaceSum_mono W
    (Finset.subset_union_left : I ⊆ I ∪ J))
  simp only [LinearForm.evalDim, monotonicityForm, sub_mul, Finset.sum_sub_distrib,
    sum_ite_mul_finrank_subspaceSum]
  have hmono' : (Module.finrank F (subspaceSum W I) : ℝ)
      ≤ Module.finrank F (subspaceSum W (I ∪ J)) := by exact_mod_cast hmono
  linarith

end DimsBasic

/-- Relabelling the variables of a form along `σ` and the subspaces along `σ⁻¹` gives the
same value: `(relabel σ f).evalDim W = f.evalDim (W ∘ σ⁻¹)`. -/
private lemma evalDim_relabel {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (σ : Equiv.Perm (Fin n)) (f : LinearForm n) (W : Fin n → Submodule F V) :
    (LinearForm.relabel σ f).evalDim W = f.evalDim fun i => W (σ.symm i) := by
  unfold LinearForm.evalDim LinearForm.relabel
  have hsum : ∀ I : Finset (Fin n),
      subspaceSum (fun i => W (σ.symm i)) (I.map σ.toEmbedding) = subspaceSum W I := by
    intro I
    simp only [subspaceSum]
    apply le_antisymm
    · refine iSup₂_le fun j hj => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
      have := le_iSup₂ (f := fun i (_ : i ∈ I) => W i) i hi
      simpa using this
    · refine iSup₂_le fun i hi => ?_
      have := le_iSup₂ (f := fun j (_ : j ∈ I.map σ.toEmbedding) => W (σ.symm j)) (σ i)
        (Finset.mem_map_of_mem _ hi)
      simpa using this
  have hbij : ∀ I ∈ nonemptyParts n, I.map σ.toEmbedding ∈ nonemptyParts n := by
    intro I hI
    rw [mem_nonemptyParts] at hI ⊢
    exact hI.map
  refine Finset.sum_nbij' (fun I => I.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    hbij (fun J hJ => ?_) (fun I _ => ?_) (fun J _ => ?_) (fun I _ => ?_)
  · rw [mem_nonemptyParts] at hJ ⊢; exact hJ.map
  · ext i; simp
  · ext j; simp
  · rw [hsum]

/-- The easy half of Problem 299: a form of Ingleton type is valid for dimensions of four
finite-dimensional subspaces over every field, since the basic inequalities and Ingleton's
inequality (Theorem 215) are, in every ordering of the variables.  SUV Problem 299, p. 342. -/
private lemma evalDim_nonpos_of_isIngletonType (f : LinearForm 4) (hf : IsIngletonType f)
    (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    (W : Fin 4 → Submodule F V) [∀ i, FiniteDimensional F (W i)] : f.evalDim W ≤ 0 := by
  obtain ⟨m, g, c, hc, hg, hf⟩ := hf
  have hgen : ∀ k, (g k).evalDim W ≤ 0 := by
    intro k
    rcases hg k with hk | ⟨σ, hk⟩
    · rcases hk with ⟨I, J, K, hk⟩ | ⟨I, J, hk⟩
      · rw [hk]; exact evalDim_basicInequality_nonpos W I J K
      · rw [hk]; exact evalDim_monotonicityForm_nonpos W I J
    · rw [hk, evalDim_relabel]
      have key := ingleton_finrank (W (σ.symm 0)) (W (σ.symm 1)) (W (σ.symm 2)) (W (σ.symm 3))
      rw [sup_assoc, sup_assoc] at key
      rw [ingletonForm, LinearForm.evalDim, LinearForm.sum_ofTable_mul _ _ (by decide)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, subspaceSum]
      repeat rw [Finset.iSup_insert]
      repeat rw [Finset.iSup_singleton]
      have h' : (Module.finrank F ↥(W (σ.symm 0) ⊔ W (σ.symm 1)) : ℝ)
          + Module.finrank F (W (σ.symm 2)) + Module.finrank F (W (σ.symm 3))
          + Module.finrank F ↥(W (σ.symm 0) ⊔ (W (σ.symm 2) ⊔ W (σ.symm 3)))
          + Module.finrank F ↥(W (σ.symm 1) ⊔ (W (σ.symm 2) ⊔ W (σ.symm 3)))
          ≤ Module.finrank F ↥(W (σ.symm 0) ⊔ W (σ.symm 2))
          + Module.finrank F ↥(W (σ.symm 1) ⊔ W (σ.symm 2))
          + Module.finrank F ↥(W (σ.symm 0) ⊔ W (σ.symm 3))
          + Module.finrank F ↥(W (σ.symm 1) ⊔ W (σ.symm 3))
          + Module.finrank F ↥(W (σ.symm 2) ⊔ W (σ.symm 3)) := by exact_mod_cast key
      linarith
  have hsplit : f.evalDim W = ∑ k, c k * (g k).evalDim W := by
    simp only [LinearForm.evalDim, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hf I (mem_nonemptyParts.1 hI), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_iff.2 (Or.inl ⟨hc k, hgen k⟩)

/-- The cone cut out by the basic inequalities together with Ingleton's inequality for all
orderings of the four variables.  The book's hint: it is the cone generated by the non-special
extreme rays of the cone of basic inequalities, and every one of those rays is realised by
subspaces over a finite field.  SUV Problem 299, p. 342. -/
def ingletonCone : Set (Finset (Fin 4) → ℝ) :=
  {v | v ∈ basicCone 4 ∧ ∀ σ : Equiv.Perm (Fin 4),
    ∑ I ∈ nonemptyParts 4, LinearForm.relabel σ ingletonForm I * v I ≤ 0}

/-- Farkas' lemma for the Ingleton cone: a form that is non-positive on every point of the
cone cut out by the basic inequalities and the Ingleton inequalities is a non-negative
combination of those inequalities, i.e. of Ingleton type.  This is the duality step of the
book's hint: the dual of the polyhedral cone `{v | ∀ g ∈ S, ⟪g, v⟫ ≤ 0}` cut out by a finite
set `S` of forms is the cone generated by `S`, and the constraints `v_∅ = 0`, `v_I ≥ 0` of
`basicCone` are monotonicity forms with the coefficient at `∅` disregarded.
SUV Problem 299, p. 342. -/
private lemma isIngletonType_of_forall_ingletonCone_nonpos (f : LinearForm 4)
    (h : ∀ v ∈ ingletonCone, ∑ I ∈ nonemptyParts 4, f I * v I ≤ 0) : IsIngletonType f := by
  sorry

/-- The realisation half of the book's hint: every point of the Ingleton cone is a
non-negative combination of dimension vectors of quadruples of finite-dimensional subspaces
over a finite field.  The cone is generated by the non-special extreme rays of the cone of
basic inequalities, each of which is realised by subspaces over every large enough finite
field; one field and one ambient space serve for all the rays, by taking a direct sum.
SUV Problem 299, p. 342. -/
private lemma exists_finrank_combination_of_mem_ingletonCone {v : Finset (Fin 4) → ℝ}
    (hv : v ∈ ingletonCone) :
    ∃ (F V : Type) (_ : Field F) (_ : Finite F) (_ : AddCommGroup V) (_ : Module F V)
      (m : ℕ) (c : Fin m → ℝ) (W : Fin m → Fin 4 → Submodule F V),
      (∀ k, 0 ≤ c k) ∧ (∀ k i, FiniteDimensional F (W k i)) ∧
        ∀ I : Finset (Fin 4), I.Nonempty →
          v I = ∑ k, c k * (Module.finrank F (subspaceSum (W k) I) : ℝ) := by
  sorry

/-- The common core of the hard halves of Problems 299 and 300: a form valid for the
dimensions of four finite-dimensional subspaces over every *finite* field is of Ingleton type.
The book's hint: the cone generated by the non-special extreme rays of the cone of basic
inequalities is cut out by the basic inequalities together with the Ingleton inequalities for
all orderings of the variables, and each of those rays is realised by subspaces over a finite
field; the computation of the faces is not carried out here.  SUV Problem 299, p. 342. -/
private lemma isIngletonType_of_holdsForSubspaces (f : LinearForm 4)
    (h : HoldsForSubspaces f) : IsIngletonType f := by
  refine isIngletonType_of_forall_ingletonCone_nonpos f fun v hv => ?_
  obtain ⟨F, V, _, _, _, _, m, c, W, hc, hW, hv'⟩ :=
    exists_finrank_combination_of_mem_ingletonCone hv
  -- the pairing of `f` with a combination of dimension vectors is the combination of the
  -- values of `f` on the configurations, each of which is non-positive by hypothesis
  have hsplit : ∑ I ∈ nonemptyParts 4, f I * v I = ∑ k, c k * f.evalDim (W k) := by
    simp only [LinearForm.evalDim, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hv' I (mem_nonemptyParts.1 hI), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  refine Finset.sum_nonpos fun k _ => mul_nonpos_iff.2 (Or.inl ⟨hc k, ?_⟩)
  haveI : ∀ i, FiniteDimensional F (W k i) := hW k
  exact h F V (W k)

/-- **Problem 299.**  Every linear inequality for dimensions that involves only four subspaces
and is true for all finite-dimensional subspaces of all vector spaces is a consequence of the
basic inequalities and Ingleton's inequality for the various orderings of the variables; the
converse holds by Theorem 215.  The book does not say over which fields "true" is meant; here
it is over every field.  The book's hint rests on a long computation of the faces of the cone
generated by the non-special extreme rays.  SUV Problem 299, p. 342. -/
theorem forall_evalDim_nonpos_iff_isIngletonType (f : LinearForm 4) :
    (∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
        (W : Fin 4 → Submodule F V) [∀ i, FiniteDimensional F (W i)], f.evalDim W ≤ 0) ↔
      IsIngletonType f :=
  ⟨fun h => isIngletonType_of_holdsForSubspaces f fun F _ _ V _ _ W _ => h F V W,
    fun hf F _ V _ _ W _ => evalDim_nonpos_of_isIngletonType f hf F V W⟩
```

### ch10-problem-300

Problem 300, p. 342: the analogue of Problem 299 for four subgroups of a finite abelian group.  The same computation, and the book leaves the statement to the reader ("formulate and prove"), so the formulation was ours.  Its hard half reduced to that of Problem 299; nothing depends on it.

Was in `KolmogorovMathlib/InformationInequalities/Ingleton.lean`, right after Problem 299 (restore that block first).

```lean
/-- Relabelling the variables of a form along `σ` and relabelling the subgroups along `σ⁻¹`
give the same value: `(relabel σ f).evalGroupIndex H = f.evalGroupIndex (H ∘ σ⁻¹)`. -/
private lemma evalGroupIndex_relabel {G : Type} [Group G] (σ : Equiv.Perm (Fin n))
    (f : LinearForm n) (H : Fin n → Subgroup G) :
    (LinearForm.relabel σ f).evalGroupIndex H = f.evalGroupIndex fun i => H (σ.symm i) := by
  unfold LinearForm.evalGroupIndex LinearForm.relabel
  have hmeet : ∀ I : Finset (Fin n),
      subgroupMeet (fun i => H (σ.symm i)) (I.map σ.toEmbedding) = subgroupMeet H I := by
    intro I
    simp only [subgroupMeet]
    apply le_antisymm
    · refine le_iInf₂ fun i hi => ?_
      have := iInf₂_le (f := fun j (_ : j ∈ I.map σ.toEmbedding) => H (σ.symm j)) (σ i)
        (Finset.mem_map_of_mem _ hi)
      simpa using this
    · refine le_iInf₂ fun j hj => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
      have := iInf₂_le (f := fun i (_ : i ∈ I) => H i) i hi
      simpa using this
  have hbij : ∀ I ∈ nonemptyParts n, I.map σ.toEmbedding ∈ nonemptyParts n := by
    intro I hI
    rw [mem_nonemptyParts] at hI ⊢
    exact hI.map
  refine Finset.sum_nbij' (fun I => I.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    hbij (fun J hJ => ?_) (fun I _ => ?_) (fun J _ => ?_) (fun I _ => ?_)
  · rw [mem_nonemptyParts] at hJ ⊢; exact hJ.map
  · ext i; simp
  · ext j; simp
  · rw [hmeet]

/-- A form that is of Ingleton type is valid for the indices of four subgroups of every finite
abelian group: the basic inequalities are valid for all groups (Theorem 209) and Ingleton's
inequality for abelian ones (Problem 298), in every ordering of the variables.
SUV Problem 300, p. 342. -/
private lemma evalGroupIndex_abelian_nonpos_of_isIngletonType (f : LinearForm 4)
    (hf : IsIngletonType f) (G : Type) [CommGroup G] [Finite G] (H : Fin 4 → Subgroup G) :
    f.evalGroupIndex H ≤ 0 := by
  obtain ⟨m, g, c, hc, hg, hf⟩ := hf
  have hgen : ∀ k, (g k).evalGroupIndex H ≤ 0 := by
    intro k
    rcases hg k with hk | ⟨σ, hk⟩
    · have hS : IsShannonType (g k) :=
        ⟨1, fun _ => g k, fun _ => 1, fun _ => zero_le_one, fun _ => hk, fun I _ => by simp⟩
      exact (holdsForEntropies_iff_holdsForGroups (g k)).1
        (holdsForEntropies_of_isShannonType (g k) hS) G H
    · rw [hk, evalGroupIndex_relabel]
      exact ingletonForm_evalGroupIndex_nonpos _
  have hsplit : f.evalGroupIndex H = ∑ k, c k * (g k).evalGroupIndex H := by
    simp only [LinearForm.evalGroupIndex, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hf I (mem_nonemptyParts.1 hI), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_iff.2 (Or.inl ⟨hc k, hgen k⟩)

/-- The hard half of Problem 300: a form valid for the indices of four subgroups of every
finite abelian group is of Ingleton type.  The dual of a finite-dimensional space over a finite
field is a finite abelian group whose annihilator subgroups realise the dimension dictionary,
so the form is valid for dimensions over every finite field, and the core of Problem 299
applies.  SUV Problem 300, p. 342. -/
private lemma isIngletonType_of_forall_evalGroupIndex_abelian_nonpos (f : LinearForm 4)
    (h : ∀ (G : Type) [CommGroup G] [Finite G] (H : Fin 4 → Subgroup G),
      f.evalGroupIndex H ≤ 0) : IsIngletonType f :=
  isIngletonType_of_holdsForSubspaces f
    (holdsForSubspaces_of_forall_evalGroupIndex_abelian_nonpos f h)

/-- **Problem 300.**  The analogue of Problem 299 for four subgroups of a finite abelian group:
a linear form is valid for the indices of four subgroups of every finite abelian group, under
the translation `H(ξ_I) ↦ log₂ (|G| / |G_I|)`, if and only if it is of Ingleton type.  The book
leaves the statement to the reader; this is the formulation chosen here.
SUV Problem 300, p. 342. -/
theorem forall_evalGroupIndex_abelian_nonpos_iff_isIngletonType (f : LinearForm 4) :
    (∀ (G : Type) [CommGroup G] [Finite G] (H : Fin 4 → Subgroup G),
        f.evalGroupIndex H ≤ 0) ↔ IsIngletonType f :=
  ⟨isIngletonType_of_forall_evalGroupIndex_abelian_nonpos f,
    fun hf G _ _ H => evalGroupIndex_abelian_nonpos_of_isIngletonType f hf G H⟩
```

### ch12-problem-320

Problem 320, p. 375: a shortest description `X` of `A` with `C(A|X) = O(log n)` whose total conditional complexity given `A` is `O(log n)`, and the impossibility of making both conditional complexities total.  An exercise requiring total conditional complexity and, for the second part, non-stochastic strings (the book's hint points to Chapter 14), outside the chapter's scope; nothing depends on it.  With it goes the import of `KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalComplexity` in `MuchnikGame.lean`.

Was in `KolmogorovMathlib/Multisource/MuchnikGame.lean`, after Theorem 230 (`exists_muchnikGame_winningStrategy`), at the end of the file.

```lean
/-- Muchnik's construction with an empty condition and all fingerprints declared at once: for
every string `A` of length `n` there is a string `X` of length `C(A)` with `C(A|X) = O(log n)`
whose *total* conditional complexity given `A` is `O(log n)`.

SUV Problem 320, p. 375 (first part). -/
theorem exists_shortestDescription_totalSimple (D T : Map) (hD : isOptimalConditional D)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (n : ℕ) (A : BitString), A.length = n →
      ∃ X : BitString, (X.length : ℕ∞) = plainK D A ∧
        condK D A X ≤ (logSlack c n : ℕ∞) ∧ totalCondK T X A ≤ (logSlack c n : ℕ∞) := by
  sorry

/-- One cannot replace *both* conditional complexities of Problem 320 by total conditional
complexities; the book's hint is the existence of non-stochastic strings (Chapter 14).

SUV Problem 320, p. 375 (second part). -/
theorem not_exists_shortestDescription_totalBoth (D T : Map) (hD : isOptimalConditional D)
    (hT : IsOptimalTotalConditional T) :
    ¬ ∃ c : ℕ, ∀ (n : ℕ) (A : BitString), A.length = n →
      ∃ X : BitString, (X.length : ℕ∞) = plainK D A ∧
        totalCondK T A X ≤ (logSlack c n : ℕ∞) ∧
        totalCondK T X A ≤ (logSlack c n : ℕ∞) := by
  sorry
```

### ch10-problem-290

Problem 290, p. 332: Theorem 213 for inequalities with conditional terms.  The book asks the reader to formulate the generalisation, so, as for ch01-exercise-10, there is no printed statement to be faithful to: the formulation below was ours, and its proof would rerun that of Theorem 213 (itself still open) with maximal sections for projections.  Nothing depends on it.

Was in `KolmogorovMathlib/InformationInequalities/Combinatorial.lean`, right after Theorem 213 (`cover_iff_complexity_inequality`).

```lean
/-- **Problem 290** (the formulation is ours; the book asks the reader to make it).
Theorem 213 generalises to inequalities whose terms are conditional.  Both sides are now
indexed by finite families of **disjoint pairs** `(J_k, I_k)` of index sets — the pairs of the
left-hand side all different from the pairs of the right-hand side — and the translation is
the one of Problem 283, `C(x_J | x_I) ↦ log m_A(J | I)`, so the cover condition of
Theorem 213 becomes `m_{B_k}(J_k | I_k) ≤ n_k · (2 + log₂ |A|)^d`.  Unconditional terms are
the pairs with `I_k = ∅`, since `m_A(J | ∅) = m_A(J)` and `C(x_J | x_∅) = C(x_J)`, so
Theorem 213 is the special case in which every `I_k` is empty.

The left family is non-empty and the polylogarithmic factor is `(2 + log₂ |A|)^d` for the
reasons given for Theorem 213.  SUV Problem 290, p. 332. -/
theorem cover_iff_cond_complexity_inequality (D : Map) (hD : isOptimalConditional D)
    (p q : ℕ) (hp : 0 < p)
    (JL IL : Fin p → Finset (Fin n)) (JR IR : Fin q → Finset (Fin n))
    (hLdisj : ∀ k, Disjoint (JL k) (IL k)) (hRdisj : ∀ l, Disjoint (JR l) (IR l))
    (hLne : ∀ k, (JL k).Nonempty) (hRne : ∀ l, (JR l).Nonempty)
    (hLR : ∀ k l, (JL k, IL k) ≠ (JR l, IR l))
    (lam : Fin p → ℝ) (mu : Fin q → ℝ) (hlam : ∀ k, 0 < lam k) (hmu : ∀ l, 0 < mu l) :
    (∃ d : ℕ, ∀ (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
        (A : Finset (∀ i, Y i)), A.Nonempty → ∀ nk : Fin p → ℝ, (∀ k, 0 < nk k) →
        ∏ k, nk k ^ lam k = ∏ l, (maxSection A (JR l) (IR l) : ℝ) ^ mu l →
        ∃ B : Fin p → Finset (∀ i, Y i), A ⊆ Finset.univ.biUnion B ∧
          ∀ k, (maxSection (B k) (JL k) (IL k) : ℝ)
            ≤ nk k * (2 + Real.logb 2 A.card) ^ d) ↔
      ∃ c : ℕ, ∀ (N : ℕ) (x : Fin n → BitString), (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
        ∑ k, lam k * ((tupleCondK D x (JL k) (IL k)).toNat : ℝ)
          ≤ ∑ l, mu l * ((tupleCondK D x (JR l) (IR l)).toNat : ℝ) + (logSlack c N : ℝ) := by
  sorry
```

## 2026-10-01: SUV Problem 291

Problem 291, p. 337: for the XOR generator `e`, the multiple `t · e` belongs to the
three-variable entropy region exactly when `t = log₂ k` for a positive integer `k`;
consequently, that entropy region is not convex.

This target was archived because its core helper, `dist_eq_of_entropy_triple`, could not be
proved as stated: it claims that the entropy profile `(t, 2t, 2t)` forces a uniform marginal
distribution.  The modular-XOR construction helpers were proved, but the uniformity lemma
is false in this formalisation: `FiniteProbSpace` permits zero-probability outcomes, while
`rangeFinset` includes values seen only at those outcomes.  The corrected positive-support
statement and its logarithm consequence are provable, but the frozen statement of the
problem depends on the false helper.  The public Problem 291 declarations and their
Problem-291-only dependency chain were removed from
`KolmogorovMathlib/InformationInequalities/TwoThree.lean`.

Full removed Lean text (verbatim):

```lean
/-- Reading the coordinates of `t · e`: it is the entropy vector of the triple `X` exactly when
each variable has entropy `t` while every pair and the whole triple have entropy `2t`. -/
private theorem smul_xorGenerator_eq_entropyVector_iff {m : ℕ} (μ : FiniteProbSpace (Fin m))
    (X : Fin 3 → Fin m → ℕ) (t : ℝ) :
    (fun I => t * threeGenerators 7 I) = entropyVector μ X ↔
      (∀ i, entropy μ (X i) = t) ∧ entropySub μ X {0, 1} = 2 * t ∧
        entropySub μ X {0, 2} = 2 * t ∧ entropySub μ X {1, 2} = 2 * t ∧
        entropySub μ X {0, 1, 2} = 2 * t := by
  constructor
  · intro h
    have hI : ∀ I, t * threeGenerators 7 I = entropyVector μ X I := fun I => congrFun h I
    have h01 := hI {0, 1}
    have h02 := hI {0, 2}
    have h12 := hI {1, 2}
    have h012 := hI {0, 1, 2}
    simp +decide [threeGenerators, LinearForm.ofTable, entropyVector] at h01 h02 h12 h012
    refine ⟨fun i => ?_, by linarith, by linarith, by linarith, by linarith⟩
    have hi := hI {i}
    have h1i : threeGenerators 7 {i} = 1 := by
      fin_cases i <;> simp +decide [threeGenerators, LinearForm.ofTable]
    rw [entropyVector, entropySub_singleton', h1i, mul_one] at hi
    exact hi.symm
  · rintro ⟨h1, h01, h02, h12, h012⟩
    funext I
    rcases cases8 I with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [threeGenerators, LinearForm.ofTable, entropyVector]
    all_goals
      simp +decide [threeGenerators, LinearForm.ofTable, entropyVector, entropySub_singleton',
        h1, h01, h02, h12, h012]
      try ring

/-- A random variable whose distribution is constant on its range is uniform there, and its
entropy is the logarithm of the size of the range. -/
private theorem entropy_eq_logb_card_of_dist_const {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Ω → ℕ) (c : ℝ) (hc : ∀ a ∈ rangeFinset X, μ.dist X a = c) :
    entropy μ X = Real.logb 2 (rangeFinset X).card := by
  have hsum := μ.sum_dist_eq_one X
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul] at hsum
  have hk : (0 : ℝ) < (rangeFinset X).card := by
    rcases (Nat.cast_nonneg (rangeFinset X).card : (0 : ℝ) ≤ (rangeFinset X).card).lt_or_eq
      with h | h
    · exact h
    · rw [← h, zero_mul] at hsum
      exact absurd hsum zero_ne_one
  have hc' : c = 1 / (rangeFinset X).card := by
    rw [eq_div_iff hk.ne']
    linarith
  rw [entropy, Finset.sum_congr rfl fun a ha => by rw [hc a ha], Finset.sum_const, nsmul_eq_mul,
    hc', negMulLog2, Real.negMulLog, one_div, Real.log_inv, Real.logb]
  field_simp

/-- Under the entropy equalities of Problem 291 the first variable is uniformly distributed on
its range.  Indeed `ξ₁` and `ξ₂` are independent and each of the three variables is determined
by the other two, so for a fixed value of `ξ₃` the values of `ξ₁` and `ξ₂` are matched
bijectively and the distribution of `ξ₁` is carried onto those of `ξ₂` and `ξ₃`; the three
ranges have a common size and all three distributions are uniform.  SUV Problem 291, p. 337. -/
private theorem dist_eq_of_entropy_triple {m : ℕ} (μ : FiniteProbSpace (Fin m))
    (X : Fin 3 → Fin m → ℕ) (t : ℝ) (h1 : ∀ i, entropy μ (X i) = t)
    (h01 : entropySub μ X {0, 1} = 2 * t) (h02 : entropySub μ X {0, 2} = 2 * t)
    (h12 : entropySub μ X {1, 2} = 2 * t) (h012 : entropySub μ X {0, 1, 2} = 2 * t) :
    ∀ a ∈ rangeFinset (X 0), μ.dist (X 0) a = 1 / (rangeFinset (X 0)).card := by
  sorry

/-- The uniform distribution on `k * k` outcomes: the outcome `ω` carries the pair
`(ω / k, ω % k)` of two independent uniform variables on `k` values. -/
private noncomputable def uniformSq (k : ℕ) (hk : 0 < k) : FiniteProbSpace (Fin (k * k)) where
  prob _ := 1 / ((k : ℝ) * k)
  prob_nonneg _ := by positivity
  sum_prob := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-- Two independent uniform variables on `k` values and their sum modulo `k`, as a triple of
`ℕ`-valued variables on the uniform space `Fin (k * k)`. -/
private def modTriple (k : ℕ) : Fin 3 → Fin (k * k) → ℕ :=
  ![fun ω => ω.val / k, fun ω => ω.val % k, fun ω => (ω.val / k + ω.val % k) % k]

/-- Each variable of `modTriple k` is uniform on `k` values: its entropy is `log₂ k`. -/
private theorem filter_div_card (k a : ℕ) (hk : 0 < k) (ha : a < k) :
    (Finset.univ.filter (fun ω : Fin (k * k) => ω.val / k = a)).card = k := by
  have Hlt : ∀ i : Fin k, a * k + i.val < k * k := fun i => by
    calc
      a * k + i.val < a * k + k := Nat.add_lt_add_left i.isLt _
      _ = (a + 1) * k := by ring
      _ ≤ k * k := Nat.mul_le_mul_right k ha
  have h_eq : (Finset.univ.filter (fun ω : Fin (k * k) => ω.val / k = a)) =
    Finset.image (fun i : Fin k => (⟨a * k + i.val, Hlt i⟩ : Fin (k * k))) Finset.univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      use ⟨x.val % k, Nat.mod_lt _ hk⟩
      ext
      change a * k + x.val % k = x.val
      have h1 := Nat.div_add_mod x.val k
      rw [hx] at h1
      have : k * a + x.val % k = a * k + x.val % k := by ring
      rw [← this, h1]
    · rintro ⟨i, rfl⟩
      have H1 : (a * k + i.val) / k = a := by
        have : (a * k + i.val) / k = (i.val + k * a) / k := by congr 1; ring
        rw [this, Nat.add_mul_div_left _ _ hk]
        have : i.val / k = 0 := Nat.div_eq_of_lt i.isLt
        rw [this, zero_add]
      exact H1
  rw [h_eq, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro x y hxy
    ext
    have hxy' : a * k + x.val = a * k + y.val := congrArg Fin.val hxy
    omega

private theorem filter_mod_card (k b : ℕ) (hk : 0 < k) (hb : b < k) :
    (Finset.univ.filter (fun ω : Fin (k * k) => ω.val % k = b)).card = k := by
  have Hlt : ∀ i : Fin k, i.val * k + b < k * k := fun i => by
    calc
      i.val * k + b < i.val * k + k := Nat.add_lt_add_left hb _
      _ = (i.val + 1) * k := by ring
      _ ≤ k * k := Nat.mul_le_mul_right k i.isLt
  have h_eq : (Finset.univ.filter (fun ω : Fin (k * k) => ω.val % k = b)) =
    Finset.image (fun i : Fin k => (⟨i.val * k + b, Hlt i⟩ : Fin (k * k))) Finset.univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      use ⟨x.val / k, by
        have : x.val / k < k * k / k := Nat.div_lt_div_of_lt_of_dvd ⟨k, rfl⟩ x.isLt
        rw [Nat.mul_div_cancel_left k hk] at this
        exact this⟩
      ext
      change (x.val / k) * k + b = x.val
      have h1 := Nat.div_add_mod x.val k
      rw [hx] at h1
      have : k * (x.val / k) + b = (x.val / k) * k + b := by ring
      rw [← this, h1]
    · rintro ⟨i, rfl⟩
      have H2 : (i.val * k + b) % k = b := by
        have : (i.val * k + b) % k = (b + k * i.val) % k := by congr 1; ring
        rw [this, Nat.add_mul_mod_self_left _ _ _]
        exact Nat.mod_eq_of_lt hb
      exact H2
  rw [h_eq, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro x y hxy
    ext
    have hxy' : x.val * k + b = y.val * k + b := congrArg Fin.val hxy
    have : x.val * k = y.val * k := by omega
    exact Nat.eq_of_mul_eq_mul_right hk this

private theorem filter_sum_mod_card (k c : ℕ) (hk : 0 < k) (hc : c < k) :
    (Finset.univ.filter (fun ω : Fin (k * k) => (ω.val / k + ω.val % k) % k = c)).card = k := by
  have Hlt : ∀ i : Fin k, ((c + k - i.val) % k) * k + i.val < k * k := fun i => by
    have h1 : (c + k - i.val) % k < k := Nat.mod_lt _ hk
    calc
      ((c + k - i.val) % k) * k + i.val
          < ((c + k - i.val) % k) * k + k := Nat.add_lt_add_left i.isLt _
      _ = ((c + k - i.val) % k + 1) * k := by ring
      _ ≤ k * k := Nat.mul_le_mul_right k h1
  have h_eq : (Finset.univ.filter (fun ω : Fin (k * k) => (ω.val / k + ω.val % k) % k = c)) =
      Finset.image (fun i : Fin k =>
        (⟨((c + k - i.val) % k) * k + i.val, Hlt i⟩ : Fin (k * k))) Finset.univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      use ⟨x.val % k, Nat.mod_lt _ hk⟩
      ext
      change ((c + k - x.val % k) % k) * k + x.val % k = x.val
      have h1 := Nat.div_add_mod x.val k
      have H3 : x.val / k < k := Nat.div_lt_of_lt_mul x.isLt
      have H4 : x.val % k < k := Nat.mod_lt _ hk
      have H2 : x.val / k = (c + k - x.val % k) % k := by
        have Hmod : ((x.val / k) + x.val % k) % k = c := by rw [hx]
        have hA : x.val / k + x.val % k < 2 * k := by
          calc x.val / k + x.val % k < k + k := Nat.add_lt_add H3 H4
          _ = 2 * k := by ring
        have h1 : x.val / k + x.val % k = c ∨ x.val / k + x.val % k = c + k := by
          have h2 : (x.val / k + x.val % k) % k = c := by exact Hmod
          have h3 := Nat.div_add_mod (x.val / k + x.val % k) k
          rw [h2] at h3
          have h4 : (x.val / k + x.val % k) / k = 0 ∨ (x.val / k + x.val % k) / k = 1 := by
            have : (x.val / k + x.val % k) / k < 2 := by
              have hdvd : k ∣ k * 2 := dvd_mul_right k 2
              have hA_lt : x.val / k + x.val % k < k * 2 := by
                have : 2 * k = k * 2 := by ring
                rw [← this]
                exact hA
              have H : (x.val / k + x.val % k) / k < (k * 2) / k :=
                Nat.div_lt_div_of_lt_of_dvd hdvd hA_lt
              rw [Nat.mul_div_cancel_left 2 hk] at H
              exact H
            have Hpos : 0 ≤ (x.val / k + x.val % k) / k := Nat.zero_le _
            omega
          rcases h4 with h4 | h4
          · left
            have h3' : x.val / k + x.val % k =
                k * ((x.val / k + x.val % k) / k) + c := h3.symm
            have : k * ((x.val / k + x.val % k) / k) + c = k * 0 + c := by rw [h4]
            rw [this] at h3'
            have : k * 0 + c = c := by ring
            rw [this] at h3'
            exact h3'
          · right
            have h3' : x.val / k + x.val % k =
                k * ((x.val / k + x.val % k) / k) + c := h3.symm
            have : k * ((x.val / k + x.val % k) / k) + c = k * 1 + c := by rw [h4]
            rw [this] at h3'
            have : k * 1 + c = c + k := by ring
            rw [this] at h3'
            exact h3'
        rcases h1 with h1 | h1
        · have h_eq : x.val / k = c - x.val % k := by
            have : x.val / k + x.val % k = c := h1
            have : x.val / k + x.val % k - x.val % k = c - x.val % k := by rw [h1]
            have hsub : x.val / k + x.val % k - x.val % k = x.val / k := by
              exact Nat.add_sub_cancel (x.val / k) (x.val % k)
            rw [hsub] at this
            exact this
          rw [h_eq]
          have hc_ge : x.val % k ≤ c := by
            have : x.val / k + x.val % k = c := h1
            have : x.val % k ≤ x.val / k + x.val % k := Nat.le_add_left _ _
            rw [h1] at this
            exact this
          have h_eq2 : (c + k - x.val % k) % k = c - x.val % k := by
            have : c + k - x.val % k = (c - x.val % k) + k := by
              have h1' : x.val % k ≤ c := hc_ge
              omega
            rw [this, Nat.add_mod_right]
            have : c - x.val % k < k := by
              omega
            exact Nat.mod_eq_of_lt this
          exact h_eq2.symm
        · have h_eq : x.val / k = c + k - x.val % k := by
            have : x.val / k + x.val % k = c + k := h1
            have : x.val / k + x.val % k - x.val % k = c + k - x.val % k := by rw [h1]
            have hsub : x.val / k + x.val % k - x.val % k = x.val / k := by
              exact Nat.add_sub_cancel (x.val / k) (x.val % k)
            rw [hsub] at this
            exact this
          rw [h_eq]
          have h_eq2 : (c + k - x.val % k) % k = c + k - x.val % k := by
            have : c + k - x.val % k < k := by
              have : x.val / k = c + k - x.val % k := by
                have h1' : x.val / k + x.val % k = c + k := h1
                omega
              rw [← this]
              exact H3
            exact Nat.mod_eq_of_lt this
          exact h_eq2.symm
      rw [← H2]
      have h1' : (x.val / k) * k + x.val % k = x.val := by
        have hh : (x.val / k) * k = k * (x.val / k) := by ring
        rw [hh]
        exact h1
      exact h1'
    · rintro ⟨i, rfl⟩
      have H1 : (((c + k - i.val) % k) * k + i.val) / k = (c + k - i.val) % k := by
        have : (((c + k - i.val) % k) * k + i.val) / k =
            (i.val + k * ((c + k - i.val) % k)) / k := by
          congr 1
          ring
        rw [this, Nat.add_mul_div_left _ _ hk]
        have : i.val / k = 0 := Nat.div_eq_of_lt i.isLt
        rw [this, zero_add]
      have H2 : (((c + k - i.val) % k) * k + i.val) % k = i.val := by
        have : (((c + k - i.val) % k) * k + i.val) % k =
            (i.val + k * ((c + k - i.val) % k)) % k := by
          congr 1
          ring
        rw [this, Nat.add_mul_mod_self_left _ _ _]
        exact Nat.mod_eq_of_lt i.isLt
      change ((((c + k - i.val) % k) * k + i.val) / k +
        (((c + k - i.val) % k) * k + i.val) % k) % k = c
      rw [H1, H2]
      have : ((c + k - i.val) % k + i.val) % k = (c + k - i.val + i.val) % k := by
        have H := Nat.add_mod (c + k - i.val) i.val k
        have : i.val % k = i.val := Nat.mod_eq_of_lt i.isLt
        rw [this] at H
        exact H.symm
      rw [this]
      have : c + k - i.val + i.val = c + k := Nat.sub_add_cancel (by
        have hk' : i.val < k := i.isLt
        omega)
      rw [this, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hc]
  rw [h_eq, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro x y hxy
    ext
    have hxy' : ((c + k - x.val) % k) * k + x.val =
        ((c + k - y.val) % k) * k + y.val := congrArg Fin.val hxy
    have h1 : (((c + k - x.val) % k) * k + x.val) % k =
        (((c + k - y.val) % k) * k + y.val) % k := by
      rw [hxy']
    have h2 : (((c + k - x.val) % k) * k + x.val) % k = x.val := by
      have : (((c + k - x.val) % k) * k + x.val) % k =
          (x.val + k * ((c + k - x.val) % k)) % k := by
        congr 1
        ring
      rw [this, Nat.add_mul_mod_self_left _ _ _]
      exact Nat.mod_eq_of_lt x.isLt
    have h3 : (((c + k - y.val) % k) * k + y.val) % k = y.val := by
      have : (((c + k - y.val) % k) * k + y.val) % k =
          (y.val + k * ((c + k - y.val) % k)) % k := by
        congr 1
        ring
      rw [this, Nat.add_mul_mod_self_left _ _ _]
      exact Nat.mod_eq_of_lt y.isLt
    rw [h2, h3] at h1
    exact h1

private theorem entropy_modTriple (k : ℕ) (hk : 0 < k) (i : Fin 3) :
    entropy (uniformSq k hk) (modTriple k i) = Real.logb 2 k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine (entropy_eq_logb_card_of_dist_const _ _ (1 / k) ?_).trans ?_
  · intro a ha
    have hd : (uniformSq k hk).dist (modTriple k i) a =
        (uniformSq k hk).probOf
          (Finset.univ.filter (fun ω : Fin (k * k) => modTriple k i ω = a)) := rfl
    rw [hd]
    have hp : (uniformSq k hk).probOf
        (Finset.univ.filter (fun ω : Fin (k * k) => modTriple k i ω = a)) =
          ∑ ω ∈ Finset.univ.filter (fun ω : Fin (k * k) => modTriple k i ω = a),
            (uniformSq k hk).prob ω := rfl
    rw [hp]
    have Hprob : ∀ ω, (uniformSq k hk).prob ω = 1 / ((k : ℝ) * k) := fun _ => rfl
    rw [Finset.sum_congr rfl (fun ω _ => Hprob ω), Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun ω : Fin (k * k) => modTriple k i ω = a)).card = k := by
      have hlt : a < k := by
        have Hmem := mem_image.1 ha
        rcases Hmem with ⟨ω, _, h_eq⟩
        rw [← h_eq]
        fin_cases i
        · exact Nat.div_lt_of_lt_mul ω.isLt
        · exact Nat.mod_lt _ hk
        · exact Nat.mod_lt _ hk
      fin_cases i
      · exact filter_div_card k a hk hlt
      · exact filter_mod_card k a hk hlt
      · exact filter_sum_mod_card k a hk hlt
    rw [hcard]
    have Hdiv : (k : ℝ) * (1 / ((k : ℝ) * k)) = 1 / k := by
      rw [mul_one_div]
      have hh : ((k : ℝ) * k) = (k : ℝ) * (k : ℝ) := rfl
      rw [hh]
      rw [div_mul_eq_div_div, div_self hk'.ne', one_div]
    exact Hdiv
  · have Hrange : (rangeFinset (modTriple k i)).card = k := by
      have h1 : ∀ a < k, a ∈ rangeFinset (modTriple k i) := by
        intro a ha
        rw [mem_rangeFinset]
        fin_cases i
        · use ⟨a * k, by
            calc a * k < k * k := Nat.mul_lt_mul_of_pos_right ha hk
            _ = k * k := rfl⟩
          change a * k / k = a
          rw [Nat.mul_div_cancel _ hk]
        · use ⟨a, by
            calc a < k := ha
            _ ≤ k * k := by
              have : k ≤ k * k := Nat.le_mul_self k
              omega⟩
          change a % k = a
          exact Nat.mod_eq_of_lt ha
        · use ⟨a, by
            calc a < k := ha
            _ ≤ k * k := by
              have : k ≤ k * k := Nat.le_mul_self k
              omega⟩
          change (a / k + a % k) % k = a
          have : a / k = 0 := Nat.div_eq_of_lt ha
          rw [this, zero_add, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha]
      have h2 : ∀ a ∈ rangeFinset (modTriple k i), a < k := by
        intro a ha
        have Hmem := mem_rangeFinset.1 ha
        rcases Hmem with ⟨ω, h_eq⟩
        rw [← h_eq]
        fin_cases i
        · exact Nat.div_lt_of_lt_mul ω.isLt
        · exact Nat.mod_lt _ hk
        · exact Nat.mod_lt _ hk
      have h_eq : rangeFinset (modTriple k i) = Finset.Iio k := by
        ext x
        rw [Finset.mem_Iio]
        constructor
        · exact h2 x
        · exact h1 x
      have : Finset.Iio k = Finset.Ico 0 k := by
        ext x
        simp only [Finset.mem_Iio, Finset.mem_Ico, zero_le, true_and]
      rw [h_eq, this, Nat.card_Ico, Nat.sub_zero]
    rw [Hrange]

/-- Any two of the variables of `modTriple k` determine the outcome, so a subtuple containing
two of them has the entropy `2 log₂ k` of the uniform outcome. -/
private theorem entropySub_modTriple_of_pair (k : ℕ) (hk : 0 < k) (I : Finset (Fin 3))
    (i j : Fin 3) (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    entropySub (uniformSq k hk) (modTriple k) I = 2 * Real.logb 2 k := by
  have hdivmod (ω₁ ω₂ : Fin (k * k)) (hdiv : ω₁.val / k = ω₂.val / k)
      (hmod : ω₁.val % k = ω₂.val % k) : ω₁ = ω₂ := by
    apply Fin.ext
    calc
      ω₁.val = k * (ω₁.val / k) + ω₁.val % k := (Nat.div_add_mod ω₁.val k).symm
      _ = k * (ω₂.val / k) + ω₂.val % k := by rw [hdiv, hmod]
      _ = ω₂.val := Nat.div_add_mod ω₂.val k
  have hdivsum (ω₁ ω₂ : Fin (k * k)) (hdiv : ω₁.val / k = ω₂.val / k)
      (hsum : (ω₁.val / k + ω₁.val % k) % k =
        (ω₂.val / k + ω₂.val % k) % k) : ω₁ = ω₂ := by
    apply hdivmod ω₁ ω₂ hdiv
    have hq : ω₁.val / k ≡ ω₂.val / k [MOD k] := by rw [hdiv]
    have hs : ω₁.val / k + ω₁.val % k ≡
        ω₂.val / k + ω₂.val % k [MOD k] := hsum
    exact (hq.add_left_cancel hs).eq_of_lt_of_lt (Nat.mod_lt _ hk) (Nat.mod_lt _ hk)
  have hmodsum (ω₁ ω₂ : Fin (k * k)) (hmod : ω₁.val % k = ω₂.val % k)
      (hsum : (ω₁.val / k + ω₁.val % k) % k =
        (ω₂.val / k + ω₂.val % k) % k) : ω₁ = ω₂ := by
    apply hdivmod ω₁ ω₂
    · have hr : ω₁.val % k ≡ ω₂.val % k [MOD k] := by rw [hmod]
      have hs : ω₁.val / k + ω₁.val % k ≡
          ω₂.val / k + ω₂.val % k [MOD k] := hsum
      exact (hr.add_right_cancel hs).eq_of_lt_of_lt
        (Nat.div_lt_of_lt_mul ω₁.isLt) (Nat.div_lt_of_lt_mul ω₂.isLt)
    · exact hmod
  have hinj : Function.Injective (subtuple (modTriple k) I) := by
    intro ω₁ ω₂ hω
    have h_i := congrFun hω ⟨i, hi⟩
    have h_j := congrFun hω ⟨j, hj⟩
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [subtuple, modTriple] using hdivmod ω₁ ω₂ h_i h_j
    · simpa [subtuple, modTriple] using hdivsum ω₁ ω₂ h_i h_j
    · simpa [subtuple, modTriple] using hdivmod ω₁ ω₂ h_j h_i
    · exact (hij rfl).elim
    · simpa [subtuple, modTriple] using hmodsum ω₁ ω₂ h_i h_j
    · simpa [subtuple, modTriple] using hdivsum ω₁ ω₂ h_j h_i
    · simpa [subtuple, modTriple] using hmodsum ω₁ ω₂ h_j h_i
    · exact (hij rfl).elim
  have hsub : entropySub (uniformSq k hk) (modTriple k) I =
      entropy (uniformSq k hk) (fun ω : Fin (k * k) => ω.val) := by
    calc
      entropySub (uniformSq k hk) (modTriple k) I =
          entropy (uniformSq k hk) (fun ω : Fin (k * k) => ω) := by
        simpa [entropySub, Function.comp_def] using
          entropy_comp_of_injective (uniformSq k hk) (fun ω : Fin (k * k) => ω) hinj
      _ = entropy (uniformSq k hk) (fun ω : Fin (k * k) => ω.val) := by
        simpa [Function.comp_def] using
          (entropy_comp_of_injective (uniformSq k hk) (fun ω : Fin (k * k) => ω)
            Fin.val_injective).symm
  have houtcome : entropy (uniformSq k hk) (fun ω : Fin (k * k) => ω.val) =
      Real.logb 2 (k * k) := by
    refine (entropy_eq_logb_card_of_dist_const _ _ (1 / ((k : ℝ) * k)) ?_).trans ?_
    · intro a ha
      obtain ⟨ω, rfl⟩ := mem_rangeFinset.1 ha
      have hf : (Finset.univ.filter fun x : Fin (k * k) => x.val = ω.val) = {ω} := by
        ext x
        simp [Fin.ext_iff]
      rw [FiniteProbSpace.dist, FiniteProbSpace.probOf, hf, Finset.sum_singleton]
      rfl
    · rw [rangeFinset, Finset.card_image_of_injective _ Fin.val_injective,
        Finset.card_univ, Fintype.card_fin]
      norm_num
  rw [hsub, houtcome, Real.logb_mul]
  · ring
  · exact_mod_cast hk.ne'
  · exact_mod_cast hk.ne'

/-- The multiple `log₂ k · e` of the eighth generator is the entropy vector of two independent
uniform variables on `k` values and their sum modulo `k`.  SUV Problem 291, p. 337. -/
private theorem smul_xorGenerator_mem_entropyRegion_of_pos (k : ℕ) (hk : 0 < k) :
    (fun I => Real.logb 2 k * threeGenerators 7 I) ∈ entropyRegion 3 := by
  refine ⟨k * k, uniformSq k hk, modTriple k,
    (smul_xorGenerator_eq_entropyVector_iff _ _ _).2 ⟨entropy_modTriple k hk, ?_, ?_, ?_, ?_⟩⟩
  · exact entropySub_modTriple_of_pair k hk _ 0 1 (by decide) (by decide) (by decide)
  · exact entropySub_modTriple_of_pair k hk _ 0 2 (by decide) (by decide) (by decide)
  · exact entropySub_modTriple_of_pair k hk _ 1 2 (by decide) (by decide) (by decide)
  · exact entropySub_modTriple_of_pair k hk _ 0 1 (by decide) (by decide) (by decide)

/-- **Problem 291.**  For the last generator `e` of the three-variable cone (two independent
bits and their sum), the multiple `t · e` is an entropy vector if and only if `t` is the
logarithm of a positive integer.  SUV Problem 291, p. 337. -/
theorem smul_xorGenerator_mem_entropyRegion_iff (t : ℝ) :
    (fun I => t * threeGenerators 7 I) ∈ entropyRegion 3 ↔
      ∃ k : ℕ, 0 < k ∧ t = Real.logb 2 k := by
  constructor
  · rintro ⟨m, μ, X, hX⟩
    obtain ⟨h1, h01, h02, h12, h012⟩ := (smul_xorGenerator_eq_entropyVector_iff μ X t).1 hX
    refine ⟨(rangeFinset (X 0)).card, ?_, ?_⟩
    · refine Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 fun hemp => ?_)
      have := μ.sum_dist_eq_one (X 0)
      rw [hemp, Finset.sum_empty] at this
      exact zero_ne_one this
    · rw [← h1 0, entropy_eq_logb_card_of_dist_const μ (X 0) _
        (dist_eq_of_entropy_triple μ X t h1 h01 h02 h12 h012)]
  · rintro ⟨k, hk, rfl⟩
    exact smul_xorGenerator_mem_entropyRegion_of_pos k hk

/-- **Problem 291.**  The entropy region for three variables is not convex.
SUV Problem 291, p. 337. -/
theorem not_convex_entropyRegion_three : ¬ Convex ℝ (entropyRegion 3) := by
  intro hconv
  have h1 : (fun I => (1 : ℝ) * threeGenerators 7 I) ∈ entropyRegion 3 :=
    (smul_xorGenerator_mem_entropyRegion_iff 1).2
      ⟨2, by norm_num, by rw [Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num)]⟩
  have h2 : (fun I => (2 : ℝ) * threeGenerators 7 I) ∈ entropyRegion 3 :=
    (smul_xorGenerator_mem_entropyRegion_iff 2).2
      ⟨4, by norm_num, by
        rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        norm_num⟩
  have hmid := hconv h1 h2 (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have heq : (1 / 2 : ℝ) • (fun I => (1 : ℝ) * threeGenerators 7 I)
      + (1 / 2 : ℝ) • (fun I => (2 : ℝ) * threeGenerators 7 I)
      = fun I => (3 / 2 : ℝ) * threeGenerators 7 I := by
    funext I
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq] at hmid
  obtain ⟨k, hk, hk'⟩ := (smul_xorGenerator_mem_entropyRegion_iff (3 / 2)).1 hmid
  have hkR : ((k : ℝ)) = (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [hk', Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hk)]
  have hsq : ((k : ℝ)) ^ 2 = 8 := by
    rw [hkR, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hsqN : k ^ 2 = 8 := by exact_mod_cast hsq
  have hk2 : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

```
