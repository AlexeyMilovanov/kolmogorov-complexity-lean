# Archived SUV targets

These book items were deliberately **not** formalised.  Each was reviewed against the
book text on 2026-09-06 and judged to be a reader exercise or a restatement of material
the library already carries, rather than a result whose formalisation adds anything.
The Lean statements are preserved verbatim below, so any of them can be restored by
pasting the block back into its chapter file; none of them is dispatched to the
autonomous provers any more.

The eleven items that *are* being formalised are the ones the book itself attributes to
a publication or presents as a theorem of the subject; they stay in
`SUVStatements/Chapter{01,02,04}.lean`.

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
