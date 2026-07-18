# Formalization plan: VS40 §6 — Descriptions of restricted type

Cycle: Gemini (plan) → Codex (review/verify) → Opus (implement) → Aristotle
(close frozen sorries). **Every 5th iteration is STRATEGIC** (see protocol at
the end). Source: Vereshchagin–Shen, *Algorithmic statistics: forty years
later*, §6 (`~/kolmogorov-complexity-literature/algorithmic-statistics/
arxiv-1607.08077v3/extracted/arxiv-submission05.03.2017.tex`, lines
1381–1609); most results cite [vv10] = Vereshchagin–Vitányi 2010.

## Goal

Formalize the restricted-family theory: description families 𝒜 with
conditions (1)–(3), the restricted profile `P_x^𝒜`, its basic properties,
the restricted Improving Descriptions theorem (both halves), and the
equivalence of randomness/optimality deficiencies in the restricted case.
Stretch goals: Hamming-ball instance, the `P_x` vs `P_x^𝒜` gap, the
restricted curve-realization theorem.

## Current priority override (2026-07-14)

The section owner has chosen the honest covering-code route for the Hamming
instance (decision D1).  This decision supersedes the iteration-040/045 advice
to park M3 and work only on M7.

The old proof architecture in `Examples/HammingBalls.lean` was wrong: it
restricted covering centers to the original ball and tried to prove a uniform
polynomial lower bound for `B(z,r) ∩ B(y,r_c)` at every boundary point `y`.
That intermediate statement is false.  Do not restore or restate
`shell_intersection_lower_bound`, `hammingVol_good_col_exists`, or
`hammingBall_intersection_lower_bound`.

The immediate priority is Proposition 26's sphere-wise proof described under
M3 below.  Preserve the public declarations `hammingBall_cover_centers`,
`hammingFamily_cover`, and `hammingOverhead n = (n + 1)^7`.  First isolate and
prove the coordinate-flip and sphere-incidence leaves; then assemble the shell
cover.  Only after `hammingFamily` is sound and sorry-free should ordinary
iterations return to M7 `exists_restricted_scale_state`.

**Non-goals (do NOT start):** bounded-time complexity variants (survey
explicitly says 𝒜 does not enter that picture), Epstein–Levin, Milovanov's
common-model results, strong models (§7).

## Frozen environment (do not re-litigate in ordinary iterations)

- Repo `~/kolmogorov-complexity-lean-28`, branch `fable/scalability-refactor`
  (or its successor), Lean/Mathlib pinned v4.28 (Aristotle-compatible). Never
  change pins.
- **Read `COVERAGE.md` first** — build on existing theorems, never re-derive.
  Update `COVERAGE.md` in every merge that adds/renames a paper-facing result.
- Conventions: paper-facing statements against `StandardMachine`
  (`Interface/StandardMachine.lean`); lists/tuples via `listCode`
  (`Encoding/Tuples.lean`), never hand-nested `pairCode`; new general
  `Primrec` lemmas go in `Foundation/PrimrecExtras.lean`; slack via
  `logSlack` + `SlackArith` combinators, always at one visible budget.
- Section discipline: each milestone OWNS its files (map below); no two
  parallel work streams may touch the same file. Gates: `lake build` green,
  0 `sorry` outside the section's own files, no new `axiom`, statements of
  already-frozen theorems byte-identical.
- The old unrestricted machinery to imitate: `TwoPart/Profile.lean`
  (`InDescriptionProfile`, `structureFunction`), `TwoPart/DescriptionShift.lean`
  (chunking = the special case of condition (3) for the full family),
  `TwoPart/GapCounting.lean` (`candidateCodes`/`appearanceListCodes` =
  enumeration of (i,j)-descriptions), `docs/section3-online-half-rich-cover.md`.
- **Warning from repo history:** the first `AdmissibleCurve` packaging of §3
  was *unsatisfiable* (see `AdmissibleCurve_unsatisfiable`). State properties
  directly on profile sets / structure functions, never as a bundled
  ∃-curve predicate, and stress-test every frozen ∃-statement on the trivial
  family and on the full family before freezing.

## Milestones

Dependency order: M0 → M1 → {M2, M4} → M5; M3 anytime after M1 (examples,
parallel track); M6 and M7 are stretch, after M4.

### M0 — Enumeration-complexity layer (prerequisite, ~1–2 iterations)

The single most-used informal step of §6: *"the selected set can be described
by its ordinal number in an enumeration, so its complexity is ≤ log(count) +
O(log n)"*. This exists ad hoc in `GapCounting.lean`
(`candidateCodes`, `appearanceListCodes`, `indexSelectorFn`,
`code_mem_appearanceListCodes`); M0 extracts and generalizes it.

Owns: `KolmogorovMathlib/Foundation/EnumerationComplexity.lean`.

Target statements (freeze in iteration 1 after checking against the actual
GapCounting shapes — the shapes below are drafts):

```lean
/-- A computable enumeration (with repetitions allowed) of bitstrings,
presented in stages: `enum t` is the finite list produced in the first `t`
steps, monotone in `t`. -/
structure StagedEnumeration where
  enum : ℕ → List BitString
  mono : ∀ t, enum t <+: enum (t + 1)   -- prefix-monotone
  computable : Computable enum          -- or Primrec, decide at freeze time

/-- Complexity of the k-th distinct enumerated element: ≤ log k + O(1),
given a program for the enumeration in the condition. -/
theorem KP_le_log_index_of_enumeration (U : Map)
    (hU : IsOptimalPrefixConditional U) : ...
```

Acceptance: `GapCounting.lean`'s local machinery is either re-pointed to M0
(preferred) or explicitly documented as a to-be-migrated duplicate. The M0
API must be exercised by at least one real consumer before M4 freezes.

### M1 — Description families and the restricted profile (~1 iteration)

Owns: `KolmogorovMathlib/Restricted/Family.lean`.

```lean
/-- A family of finite sets of bitstrings satisfying VS40 §6 conditions
(1)–(3). Condition (3) carries an explicit covering-overhead function
`overhead : ℕ → ℕ` instead of "some polynomial": all downstream slack is
`logSlack` of it, so polynomial growth is only needed where a final
`O(log n)` is claimed — record it as a separate `Prop` field or a mixin. -/
structure DescriptionFamily where
  mem : Finset BitString → Prop
  -- (1) enumerability: a StagedEnumeration of the canonical codes of members
  enumerable : ...
  -- (2) full cubes: stringsOfLength n ∈ family
  fullCube : ∀ n, mem (stringsOfLength n)
  -- (3) covering: ∀ A ∈ family, n, 0 < c < A.card, ∃ cover ⊆ family,
  --     members of card ≤ c, covering the n-bit part of A,
  --     cover.length ≤ overhead n * A.card / c
  cover : ...

/-- Restricted (i,j)-descriptions and profile. -/
def IsIJDescriptionIn (𝒜 : DescriptionFamily) (U : Map) (x : BitString)
    (S : Finset BitString) (hS : S.Nonempty) (i j : ℕ) : Prop :=
  𝒜.mem S ∧ IsIJDescription U x S hS i j

def InDescriptionProfileIn (𝒜 : DescriptionFamily) (U : Map)
    (x : BitString) (i j : ℕ) : Prop := ...

def fullFamily : DescriptionFamily := ...   -- all finite nonempty sets

/-- Sanity: the restricted profile for `fullFamily` is the unrestricted one. -/
theorem inDescriptionProfileIn_fullFamily_iff : ...
```

Design decisions to settle at freeze (STRATEGIC input, iteration 1 counts as
strategic for this purpose):
- condition (3) with explicit `overhead : ℕ → ℕ` + a separate `PolyOverhead`
  predicate (recommended), vs baked-in polynomial — explicit function keeps
  the abstract theorems slack-honest and lets Hamming balls plug in their own
  bound;
- `mem : Finset BitString → Prop` + enumerability of codes (recommended,
  matches `setComplexity`/`codedUniformOn`), vs a primitive enumeration with
  `mem` derived.
- Monotonicity lemmas (`mono_i`, `mono_j`) and the `fullFamily` sanity
  theorem are mandatory before anything is built on M1.

### M2 — Basic properties of `P_x^𝒜` (Prop. `prop:a-family`, ~1–2 iterations)

Owns: `KolmogorovMathlib/Restricted/BasicProfile.lean`.

1. (a1) `(O(log n), n) ∈ P_x^𝒜` — from `fullCube` + the existing
   `FullSetComplexityGate` proof pattern (`fullSetComplexityGate`).
2. (a2) `(K(x)+O(1), 0) ∈ P_x^𝒜` — condition (3) with `c = 1`, `A = 𝔹ⁿ`
   gives singletons ∈ 𝒜; reuse `singletonSetComplexityGate` pattern.
   NOTE: (a2) as stated needs singletons in 𝒜 — this is a *derived* fact
   from (2)+(3), prove it as a standalone lemma `singleton_mem`.
3. (a3) restricted description shift: `(i,j) ∈ P_x^𝒜 → (i+k+O(log n), j−k)
   ∈ P_x^𝒜` — search the enumeration for the cover promised by (3), take the
   first covering set containing x, complexity ≤ i + k + log(overhead) +
   O(log n) via M0. This is the restricted analogue of
   `inDescriptionProfile_portion` — read that proof first.

### M3 — Example instances (parallel track, independent leaves)

Owns: `KolmogorovMathlib/Restricted/Examples/Cylinders.lean`,
`.../Examples/Masks.lean`, `.../Examples/HammingBalls.lean`.

- Cylinders (n-bit strings with prefix u): easy; covering = extend the prefix.
- Ternary masks (fix arbitrary bit positions): medium; covering = fix more
  bits; counting is exact powers of 2, no estimates needed.
- **Hamming balls: current priority; use Proposition 26's sphere-wise proof.**
  The ball cardinality, radius-growth bound, full-cube probabilistic cover,
  sphere decomposition, sphere cardinality, and `greedy_cover_indexed` are
  already available.  Do not try to lower-bound the intersection of the
  original ball with every covering ball.

  Correct proof architecture:

  1. If the target radius is larger than `n / 2`, cover the whole cube using
     `hamming_probabilistic_cover`; compare `2^n` with the target ball volume.
  2. Otherwise decompose the target ball into at most `n + 1` distance
     spheres.  Spheres of radius `a ≤ r_c` are covered by the one ball centered
     at `z`.
  3. For `r_c < a ≤ n / 2`, choose a center-shell radius `f`.  For every
     `r_c`-subset `E` of coordinates, the prefix-flip path
     `E △ {0, ..., t-1}` starts at weight `r_c`, ends at `n-r_c`, and changes
     weight by one per step, so it hits weight `a`.  Pigeonhole over the
     `n + 1` times to obtain one `f` for which at least a `1/(n+1)` fraction of
     the radius-`r_c` sphere lies in the target radius-`a` sphere.
  4. Prove the corresponding sphere-incidence graph is regular (or prove the
     two exact degree formulas and their double-count identity).  Apply
     `greedy_cover_indexed` with centers on `hammingSphere n z f`.
  5. Concatenate the shell covers.  Use
     `hammingVol n r_c ≤ c ≤ (n+1) * hammingVol n r_c`, the sphere/ball
     `(n+1)` factors, the greedy logarithm `≤ n+1`, and the shell count
     `≤ n+1`.  The frozen `(n+1)^7` overhead has spare factors.

  Recommended Lean leaves, in order:

  - a reusable `flipPositions` representation and lemmas for length,
    injectivity, and Hamming distance as symmetric-difference cardinality;
  - `prefix_flip_path_hits` and `exists_dense_hamming_center_shell`;
  - `hammingSphere_incidence_regular` (or exact row/column degree lemmas);
  - `hammingSphere_cover_centers` using `greedy_cover_indexed`;
  - the final `hammingBall_cover_centers` shell/full-cube dispatcher.

  Every ordinary iteration must leave at most 1–3 honest named leaf holes for
  Aristotle.  Numerical experiments are diagnostics only, never proof terms.

The abstract theory (M2, M4, M5) must NEVER depend on M3.

### M4 — Restricted Improving Descriptions (`thm:improving-descriptions-1-gen`,
core of the section, ~3–5 iterations)

Owns: `KolmogorovMathlib/Restricted/GreedyCover.lean`,
`.../Restricted/Selection.lean`, `.../Restricted/Improving.lean`.

- Part 1 (size half, `(i,j) → (i+d+O(log n), j−d+O(log n))`): same move as
  M2(a3). Cheap once M2 lands.
- Part 2 (complexity half, `2^k` descriptions → `(i−k+O(log n), j+O(log n))`):
  **use the CONSTRUCTIVE proof, not the probabilistic one** (finite-game
  determinacy + Chebyshev is formalizable but strictly harder in Lean; the
  constructive selection strategy is elementary and matches the repo's
  existing style — cf. `docs/section3-online-half-rich-cover.md`, which is
  the unrestricted cousin of exactly this argument).
  Decomposition (freeze each as its own lemma):
  1. `GreedyCover.lean`: the greedy covering lemma — if every element of a
     finite set `T` is covered by ≥ m of the sets in a finite family `S`
     (|S| = M), then greedy selection covers `T` with ≤ (M/m)·(log |T| + 1)
     sets. Pure finite combinatorics, no computability. This is the
     workhorse; Aristotle-friendly.
  2. `Selection.lean`: the substrategy bookkeeping — substrategy `s` wakes
     every `2^s` steps, marks greedy covers of the "≥ 2^k/i-multiplicity"
     elements among the last `2^s` sets; total marked ≤ i²·n·2^{i−k}·ln 2
     (in Lean: an explicit `⌈…⌉` bound, no `ln`); the binary-representation
     argument that every string with `2^k` descriptions is covered after
     every step. All statements about explicit list-processing functions —
     define the selection process as a computable function on the staged
     enumeration (M0), not as a "strategy" in game language.
  3. `Improving.lean`: assemble — marked sets are enumerable, so the marked
     set containing x has complexity ≤ (i−k) + O(log n) by M0's index bound.
- The `+O(1)`-vs-multiplicity subtlety: "2^k different descriptions" must be
  counted among *canonical codes* (distinct Finsets), matching
  `ManyIJDescriptions` in the unrestricted case — reuse that definition
  restricted to 𝒜, do not invent a new multiplicity notion.

### M5 — Deficiency equivalence, restricted (`thm:improving-descriptions-2-gen`
+ corollary, ~2 iterations)

Owns: `KolmogorovMathlib/Restricted/DeficiencyEquiv.lean`.

- `K(A|x) ≥ k` version: from M4 part 2 (the marked-set argument applied to
  the enumeration filtered by membership of x, exactly as the unrestricted
  `improving_descriptions_*` chain does — read `ImprovingDescriptions.lean`
  first).
- Corollary: for x of length n, TFAE up to O(log n): ∃A∈𝒜 (complexity ≤ α,
  randomness deficiency ≤ β) ↔ ∃A∈𝒜 (complexity ≤ α, optimality deficiency
  ≤ β) ↔ (α, K(x)−α+β) ∈ P_x^𝒜. Reuse `DeficiencyLe`,
  `SetOptimalityDeficiencyLe`, and mirror `stochasticity_to_optimal_set_thm`'s
  proof skeleton.
- Also the uniform proposition for arbitrary enumerable 𝒜 (slack
  O(K(p)+log K(A)+log n+log log #A)) — state with the enumeration program in
  the condition; cheap corollary of the same machinery, good Aristotle leaf.

### M6 — Hamming gap (stretch, after M3-balls or with balls axiomatized as
a section hypothesis)

Owns: `KolmogorovMathlib/Restricted/HammingGap.lean`.

`prop:hamming-gap`: ∃ x of length n with dist(P_x, P_x^𝒜) ≥ εn for 𝒜 =
Hamming balls. Needs a list-decoding-type set E (|E| = 2ⁿ/V, every αn-ball
contains ≤ n points of E) — probabilistic existence becomes a counting
argument; E found by exhaustive search ⟹ K(E) = O(log n) via the
"lexicographically-first witness" pattern (`ProfileRealization` uses it).
STRATEGIC checkpoint before starting: confirm the counting inequality
formalizes at reasonable cost.

### M7 — Restricted curve realization (`thm:family-curve`, stretch, hardest)

Owns: `KolmogorovMathlib/Restricted/FamilyCurve.lean`.

O(√(n log n)) precision; multi-scale good-set maintenance with thresholds
ν_s = α^{-s}·2^{j_s}/2 and update counting. Prerequisites: M2, M4, and a new
slack scale — freeze `sqrtSlack c n := c * Nat.sqrt (n * (Nat.bits n).length)
+ c` in `SlackArith` with the same combinator kit before starting. Do NOT
attempt before M4 is closed; expect several iterations; the unrestricted
`ProfileRealization.lean` (3.7k lines) is the model and lower bound on effort.

## Iteration protocol

Ordinary iteration (1–4, 6–9, …):
1. **Gemini (plan):** pick exactly ONE open target from the current
   milestone (respect dependency order and file ownership); read the source
   §6 passage and the named repo files; produce target lemma statements +
   proof sketch + verification commands. Flag any statement that would be
   fake or weaker than the paper (e.g. dropping the "distinct descriptions"
   multiplicity, or quantifying a slack constant after the string).
2. **Codex (review/verify):** adversarially check the plan: does the
   statement degenerate on `fullFamily`? on a singleton family? does it
   contradict an existing repo theorem? does it re-derive something in
   COVERAGE.md? Then run/verify any empirical checks (`#eval` sanity on
   small n where applicable).
3. **Opus (implement):** implement in the milestone's own files only; leaf
   sorries allowed only in those files; keep frozen statements byte-stable;
   `lake build` + sorry-count + axiom audit before handing off.
4. **Aristotle:** submit remaining leaf sorries (statements frozen; v4.28
   branch only). Treat Aristotle refutations as high-quality signals: verify,
   then obey (repo history: it was right about a false leaf twice).

Gate for every merge: build green; sorries only in own files and
non-increasing per section; no new `axiom`; `COVERAGE.md` updated;
frozen-statement diff empty.

**STRATEGIC iteration (every 5th):** no new proofs. Instead:
1. Re-read this plan + `COVERAGE.md` + all milestone files; check every
   frozen statement against the survey text once more (especially slack
   shapes and quantifier order — the repo's two historical bugs were exactly
   these).
2. Kill stuck routes: if a leaf has resisted ≥ 3 Aristotle submissions,
   either re-decompose it (new disjoint files!) or file it as a
   counterexample candidate and try to REFUTE the statement instead.
3. Re-prioritize milestones; decide pending design questions (marked
   STRATEGIC above); descope stretch goals if the main line is behind.
4. Update this plan file (append a dated log entry at the bottom; never
   rewrite history) and `COVERAGE.md`.
5. Check ops: `pgrep` the loops, disk, stale `_worktree`s, PAUSE files.

## Known traps (from this repo's own history)

- Unsatisfiable bundled predicates (`AdmissibleCurve`): test every frozen
  ∃-structure on trivial instances before freezing.
- Quantifier order on slack constants: `∃ c, ∀ x n …` — the constant NEVER
  depends on the string; per-ε/per-n existentials die at the next diagonal.
- Padding exponents is not free (harper lesson): keep `overhead` honest,
  absorb polylogs only in `logSlack` constants.
- `prepare_worktree` never refreshes; delete section worktrees after any
  interface change.
- Sections must own disjoint files; the merge gate copies whole files.
- Multiplicity of descriptions = distinct canonical codes; off-by-one in
  "at least 2^k" vs "more than 2^k" changes the improving bound by 1 — match
  `ManyIJDescriptions` exactly.

## Log

- 2026-07-11: plan created (Fable session). M0–M7 defined; nothing frozen
  yet. First iteration should freeze M0+M1 statements (counts as strategic).
