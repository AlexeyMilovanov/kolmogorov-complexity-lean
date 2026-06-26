# Aristotle Reconstruction Review — KolmogorovMathlib (Lean 4.31)

Status: static source/architecture review only. No source files were modified; no
proofs were attempted. This document is the requested deliverable: an engineering
report with a prioritized plan, concrete file/declaration targets, risks, and
rollback criteria.

References read: `CURRENT_431_DIAGNOSIS.txt`, `GEMINI_RECONSTRUCTION_PLAN.md`,
`CODEX_RECONSTRUCTION_PLAN.md`, and the sources
`AlgorithmicProbability/{KraftChaitinCore,KraftChaitinAllocator,UniversalSemimeasure,PairProjection,KraftChaitin}.lean`,
plus `Core/Basic.lean`, `Prefix/{Basic,Combinators}.lean`, and the root
`KolmogorovMathlib.lean`.

---

## 0. Ground truth observed in the snapshot

Confirmed facts the recommendations depend on:

- Base types are thin aliases: `abbrev BitString := List Bool`,
  `abbrev Map := BitString × BitString →. BitString` (`Core/Basic.lean:25,30`).
  So `Primcodable BitString` is just `Primcodable (List Bool)` — already optimal;
  there is *nothing to "flatten"* at the base-type level.
- Dependency layering is already largely correct:
  - `KraftChaitinAllocator.lean` imports only `Prefix.Basic` (a near-leaf).
  - `KraftChaitinCore.lean` imports the allocator + `Coding` + `Prefix.Optimal`.
  - `KraftChaitin.lean` is a thin facade re-exporting Core's public theorems.
  - `UniversalSemimeasure`, `PairProjection`, `ConditionalCoding` sit *above* the
    facade. No cycles observed.
- The allocator already applies the correct performance lever:
  `attribute [local irreducible] splitNode allocateOne` and later
  `attribute [local irreducible] allocatorState` (Allocator.lean ~821, ~881),
  with an explicit comment that reducibility makes combinator unification
  whnf-unfold large defs. Core does this only for `evK`/`evOut`
  (`@[irreducible]`), **not** for `incNum`, `cumNum`, `truncG*`.
- All four heartbeat sites share exactly one root cause: witnesses for
  `Computable`/`Primrec` are assembled by hand from `Computable.pair/.comp/.fst/
  .snd` over deeply nested `Primcodable` products such as
  `(ℕ × BitString × BitString) × ℕ` and
  `((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString`, combined
  with `Nat.rec` / `Nat.casesOn` / `Option.bind`. The proofs already partly
  mitigate with the local helpers `beta_pair`, `beta_pair3`, `beta_pair4` and
  `Computable.of_eq`.
- `UniversalSemimeasure.approxEnum_computable` is a machine-generated
  `convert`/`rotate`/`grind +locals` blob — same smell, lower readability.

Stale/incorrect comments worth fixing opportunistically (not blockers):
- Core still describes the allocator as "to-be-built" near the LSC section even
  though `exists_online_prefixFree_family` is proved later in the same file.
- Allocator references an `AllocGood` structure in a comment that does not exist.

---

## 1. Evaluation of the Gemini and Codex plans

### Diagnosis: both agree on the root cause, and they are right
Both plans correctly identify that the heartbeat pressure comes from manual,
point-free `Computable` combinators over deeply nested `Primcodable` products,
not from "messy" proofs. Gemini's framing of this as the *scaling* bottleneck
(rather than a cosmetic one) is the single most valuable insight in either
document and should anchor the whole effort.

### Where I agree with Gemini
- Root-cause attribution (nested-product combinator plumbing) is correct.
- Optimizing against profiler/heartbeat hotspots and tactic-vs-combinator ratio
  is a better signal than warning counts.
- Reconstruction work belongs on a branch allowed to break temporarily, while
  polishing stays green and local.

### Where I disagree with Gemini (important)
- **"Replace nested products with named `structure`s + custom `Computable`
  projection API" is the wrong first move and may not even help.** Mathlib's
  `Computable`/`Primcodable` ecosystem is built around `×`, `Option`, `List`,
  `ℕ`, and `Sum`. A bespoke `structure` does **not** get good computability
  support for free: you must give it a `Primcodable` instance (in practice via an
  `Equiv`/encoding to the *same* nested product) and then prove each field
  projection computable *through that encoding* — which reintroduces the exact
  nested-product plumbing plus a layer of indirection. The claim that structures
  "elaborate instantly" and that deriving `Primcodable` is painless is
  unverified and runs against how the typeclass actually works. Risk: heartbeats
  stay flat or get worse, and you've paid a large rewrite cost.
- **Structures-first inverts the safe order.** It is a representation change
  (Codex's Stage 4) promoted to Stage 1, maximizing blast radius before any
  measurement confirms the hypothesis.
- The `derive_computable` macro is a real idea but oversold as near-term. A robust
  tactic that synthesizes `Computable.pair/.comp` chains from goal structure is
  its own subproject; build the manual combinator *library* first and only
  macro-ify once the patterns are stable.

### Where I agree with Codex (this is the better plan)
- Commit the green state, work on a branch, every stage ends green, rollback per
  stage. Correct discipline.
- **Split modules first without changing declarations**, then split proof layers,
  then add a small reusable computability API, and only *then* (if measurement
  demands) touch representation. This is the standard Mathlib-style order and
  minimizes the window of breakage.
- Prefer `abbrev` type aliases (e.g. `StageOutCtx := ℕ × BitString × BitString`)
  over structures for readability without changing elaboration behavior.
- "Do not chase zero heartbeats as the primary metric" — a justified local
  heartbeat can be better than a destabilizing abstraction. Agreed; with the
  refinement in §4 that `incNum_computable` and `truncGTerm_computable_then` are
  the two most likely to be removable cleanly.
- The acceptance matrix (public-API `#check`, `#print axioms` allowlist,
  dependency/perf hygiene, reusability) is the right shape.

### Where I'd push Codex slightly further
- Codex's Stage 3 ("add small APIs") is where the actual heartbeat win lives, but
  it is under-specified. §5 below makes it concrete: a single
  `Computability/Tuple.lean` of named projection/composition lemmas for the ~7
  recurring product shapes, plus Option-combinator wrappers, plus extracting the
  allocator `Nat.rec` step into a named `def` with one `Computable` lemma.
- Codex keeps Core as "the assembler" but Core currently also *contains* the
  entire LSC + truncation + computability development (1961 lines). The split
  must physically move those out (see §2), not just relabel.

### One-line verdict
Adopt the **Codex order and discipline**, powered by **Gemini's root-cause
diagnosis**, and explicitly **reject Gemini's structures-first representation
change** as the entry point. Keep structures as a *measured, last-resort* option.

---

## 2. Recommended reconstruction order (concrete)

Branch: `refactor/kc-computability-architecture`. Commit current green state
first. Intermediate commits may break; **every numbered stage must end green** on
the explicit per-module builds listed under each stage.

### Stage A — Carve a computability-combinator module (new, additive, low risk)
Create `KolmogorovMathlib/AlgorithmicProbability/Computability/Tuple.lean`
(near-leaf; imports `Mathlib` only, or just `Mathlib.Computability.Primrec`
families if narrowing later). Move/generalize the existing local helpers and add
the reusable API from §5. This is purely additive — nothing else changes yet, so
it stays green by construction. Doing it first means Stages C–E can consume it.

Verify: `lake build KolmogorovMathlib.AlgorithmicProbability.Computability.Tuple`.

### Stage B — Split the allocator into proof layers
`KraftChaitinAllocator.lean` (1097 lines) → directory
`AlgorithmicProbability/KraftChaitin/Allocator/`:
- `Basic.lean`: `splitNode`, `allocateOne`, `allocatorState`, `allocFun`,
  `nodeMass`, `freeMass`, `reqMass`, `usedMass`, `DescLengths`, and the pure
  equational lemmas (`*_eq_map`, `*_eq_rec`, `*_eq_bind`).
- `Invariants.lean`: prefix-free / descendant / mass / serviceability lemmas
  (`allocateOne_prefixFree`, `allocatorState_prefixFree`, `*_descLengths`,
  `*_mass`, `usedMass_le_tsum`, `allocatorState_isSome`, `exists_fit_of_mass_ge`,
  …).
- `Computability.lean`: `drop_primrec`, `take_primrec`, `replicate_false_primrec`,
  `getElem!_primrec`, `findIdx?_pred_primrec`, `splitNode_primrec/_computable`,
  `allocateOne_computable`, `allocStep`(new, §5)+`allocStep_computable`,
  `allocatorState_computable`, `allocFun_computable`.
- `API.lean`: re-export the three public obligations `allocFun_computable`,
  `allocFun_prefixFree`, `allocFun_success`. Downstream imports only this.

Keep declaration names and statements identical (the proofs may be tightened in
Stage D). No representation change here.

Verify: build each new module, then the old importers
(`KraftChaitinCore`, then `KolmogorovMathlib`).

### Stage C — Split Core into LSC / truncation / request / assembler
`KraftChaitinCore.lean` (1961 lines) → :
- `AlgorithmicProbability/LSC/Defs.lean`: `dyadicValue`, `IsLSC`,
  `iSup_dyadicValue_shift`, `computable_dyadicValue_shift`, `IsLSC.div_two_pow`.
- `AlgorithmicProbability/LSC/Truncate.lean`: `incNum`, `evK`, `evOut`, `evNum`,
  `cumNum`, `truncCum`, `truncGapprox`, `truncG`, the packed variants and all the
  `*_eq`/`*_eq_packed`/`*_eq_cases` characterization lemmas, and the
  real-analytic lemmas (`dyadicValue_*`, `tsum_*`, `truncG_eq_*`), plus
  `IsLSC.truncate`.
- `AlgorithmicProbability/LSC/Computability.lean`: the generic helpers
  (`computable_range_sum`, `primrec_two_pow_aux`, `computable_two_mul`,
  `evOut_computable`, `evK_computable`) and the witness lemmas
  (`incNum_computable`, `evNum_computable`, `cumNumTerm_computable`,
  `cumNum_computable`, `truncGTerm_computable*`, `truncGapprox_computable`, and
  the `*_uniform` family). Consumes `Computability/Tuple.lean`.
- `AlgorithmicProbability/KraftChaitin/Request.lean`: `geomCross`, `geomReqBody`,
  `geomReq`, `geomReq_computable`, `extract_request_stream`,
  `extract_request_stream_geometric`, `geomReq_kraft_le_one`,
  `geomReq_geometric_bound`, and the Kraft-mass lemmas.
- `KraftChaitinCore.lean` stays the **assembler only**:
  `exists_online_prefixFree_family`, `construct_pred_computable`,
  `construct_out_partrec`, `construct_prefix_machine`,
  `realization_bound_of_machine`, `kraftChaitin_realization_bound_unit`,
  `kraftChaitin_realization_bound`.

Statement preservation is mandatory in this stage. The only allowed edits are
moving declarations and repairing imports/`open`s.

Verify: build each module bottom-up; then `KraftChaitin` facade; then
`UniversalSemimeasure`, `PairProjection`, `ConditionalCoding`; then the root.

### Stage D — Tighten the four heartbeat proofs against the new API
Only now rewrite `incNum_computable`, `truncGTerm_computable_then`,
`allocatorState_computable`, `allocFun_computable` using the Stage-A combinators
and the extracted `allocStep`. Target: remove/relax `maxHeartbeats` per §4. This
is the measured payoff stage.

Verify: per-declaration profiler before/after (see §7).

### Stage E — Apply the same treatment to UniversalSemimeasure
Rewrite `approxEnum_computable` (replace the `convert/grind` blob) and
`lscEnumApprox_uniform_computable` using `Computability/Tuple.lean` and a named
`evaln`-of-decoded-code helper. No statement changes.

### Stage F — Optional, measured: representation change
Only if Stage D leaves an unacceptable hotspot. Prefer, in order:
1. more `attribute [local irreducible]` on heavy defs during combinator proofs;
2. `abbrev` shape aliases for readability;
3. a `structure` *only* for a shape that is genuinely reused widely AND for which
   a clean `Primcodable` via `Equiv` to the existing product measurably lowers
   heartbeats. Treat as a hypothesis to be A/B-tested on one declaration before
   rolling out.

### Stage G — Optional: `derive_computable`-style automation
After the manual library exists and patterns are stable, consider a tactic/macro
that discharges `Computable (fun p => f p.…)` goals by structural recursion on the
tuple. Scope it as a separate task with its own acceptance bar.

---

## 3. Architectural blockers vs. acceptable rough edges

### Genuine blockers for 10–100× growth
1. **Two oversized multi-role files** (`KraftChaitinCore` 1961, `Allocator` 1097).
   At 10× they become unmergeable and unbuildable-incrementally. Splitting
   (Stages B–C) is the prerequisite for everything else.
2. **No reusable computability-combinator layer.** Every new computable
   construction re-derives projection/composition witnesses by hand; cost grows
   with product depth and with the number of constructions. This is the true
   scaling wall and the source of all four heartbeat sites (Stage A/D).
3. **Computability proofs interleaved with math and with public theorems.** This
   couples unrelated change-rates and forces wide rebuilds. Layer separation
   (Defs / Invariants / Computability / API) fixes it.
4. **`import Mathlib` in heavy theory files** (Core, Allocator). Tolerable now;
   at scale it inflates rebuild times and obscures the real dependency graph.
   Narrow *after* the splits, not before.

### Acceptable local rough edges (do not gate the refactor on these)
- The four `set_option maxHeartbeats` themselves. They are scoped, documented,
  and on isolated witness lemmas. They are a symptom of #2, not an independent
  problem; treat as a metric, not a blocker.
- Large but mostly-aggregating files like `Prefix/Properties.lean` (1082 lines).
- Stale comments ("allocator to-be-built", nonexistent `AllocGood`). Fix in
  passing.
- The `approxEnum_computable` machine-generated proof — ugly but isolated;
  clean in Stage E.

---

## 4. Disposition of each `set_option maxHeartbeats` site

| Site | Decl | Budget | Root cause | Recommendation |
|---|---|---|---|---|
| `KraftChaitinCore.lean:598` | `incNum_computable` | 500k | `Nat.casesOn` over packed `(ℕ × BitString × BitString)` projections | **Reduce by local proof cleanup + API.** Add named projection lemmas for the `Ctx3` and `Ctx3 × ℕ` shapes (§5); mark `incNum` (and the local step) `irreducible` during the proof. Most likely fully removable. |
| `KraftChaitinCore.lean:710` | `truncGTerm_computable_then` | 2M | multiplication term over nested packed args; shared argument tuple re-derived | **Reduce/redesign API.** Factor the shared `(q.2, q.1.2.2)` and `(q.1.1 - evK q.2)` subterms into named computable lemmas reused across the `cond_*` siblings; this de-duplicates witness construction. Likely removable or down to a small budget. |
| `KraftChaitinAllocator.lean:883` | `allocatorState_computable` | 8M | `Nat.rec` step built inline over `Option (List BitString)` nested in products with `Primcodable` encoders | **Redesign API (highest priority).** Extract the step as a top-level `def allocStep (req …) : ℕ × Option (List BitString) → Option (List BitString)` and prove `allocStep_computable` once; then `Computable.nat_rec` sees an opaque computable step. Keep a (much smaller) local budget only if measurement still requires it. |
| `KraftChaitinAllocator.lean:931` | `allocFun_computable` | 500k | `option_bind` of `allocatorState_computable` + `getD/map` chain | **Hide behind API.** Once `allocatorState_computable` is opaque-with-lemma and the Option-combinator wrappers (§5) exist, this composes from O(1) named lemmas. Expect removable or near-default. |

Cross-cutting: none of these should be "kept as-is" long term, but **keeping the
existing budgets as the safe checkpoint at the end of Stage C is acceptable** —
they are only attacked in Stage D, after the structure is in place. Do **not**
introduce any *new* heartbeat site whose budget exceeds the one it replaces
without removing another bottleneck (rollback trigger, §"Risks").

---

## 5. Exact intermediate lemmas / APIs to add before large refactors

Put these in `AlgorithmicProbability/Computability/Tuple.lean` (Stage A). Names
are suggestions; keep them distinctive to avoid Mathlib collisions.

### 5.1 Promote and generalize the existing beta helpers
`beta_pair`, `beta_pair3`, `beta_pair4` already exist locally in Core — move them
here and document them. They convert `Computable.of_eq` obligations for
curried-vs-tupled application; they are load-bearing and should be shared.

### 5.2 Named projection bundles for the recurring shapes
The witnesses repeatedly re-derive the same projections. Provide them once per
shape (each as a `Computable …` lemma), for the shapes actually used:
- `Ctx3 := ℕ × BitString × BitString` → `.1`, `.2.1`, `.2.2`.
- `Ctx3 × ℕ` → `.1.1`, `.1.2.1`, `.1.2.2`, `.2`, plus `(.2 + 1)`.
- `ℕ × ℕ × BitString` and `(ℕ × ℕ × BitString) × ℕ`.
- `ℕ × ℕ × ℕ × BitString` and `(ℕ × ℕ × ℕ × BitString) × ℕ`.
- `ℕ × ℕ × BitString × BitString` and `(ℕ × ℕ × BitString × BitString) × ℕ`.
- Allocator shapes: `BitString × ℕ`, `List BitString × ℕ`, and the step shape
  `((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString`.
Consider `abbrev` aliases for the first few to improve readability of downstream
signatures (Codex's suggestion), but the *lemmas* are what cut elaboration cost.

### 5.3 Packed-application / argument-tuple combinators
Small lemmas that build `Computable (fun p => f (g₁ p) (g₂ p) (g₃ p))` from
`Computable g₁/g₂/g₃` for arity 2/3/4 without spelling out `Computable.pair`
nests at each call site (a typed wrapper around `Computable.pair` + `of_eq` +
`beta_pair*`). This is the single biggest readability+speed lever for Core.

### 5.4 Option-combinator wrappers for the recurring patterns
Thin, reusable lemmas over `Computable.option_map/bind/getD/casesOn` specialized
to the two patterns that appear in the allocator and Core:
- `((req …).map (fun pr => …)).getD (some/none …)` is computable, given the
  inner computable;
- `X.bind (fun free => …)` step shape used by `allocatorState`.

### 5.5 Allocator step extraction
- `def allocStep (req : ℕ → Option (BitString × ℕ)) : ℕ × Option (List BitString) → Option (List BitString)`
  matching the current inline `fun y IH => …` in `allocatorState_eq_rec`.
- `lemma allocStep_computable …` proven once (uses 5.3/5.4).
- Restate `allocatorState_eq_rec` in terms of `allocStep` so
  `allocatorState_computable` is a one-line `Computable.nat_rec`.

### 5.6 `Nat.rec` / `Nat.casesOn` wrappers
Specialized `Computable.nat_rec`/`nat_casesOn` lemmas where the step/branch is
already packaged as a named computable function, so the generic recursor is never
elaborated against an inline lambda over nested products. Covers
`incNum_computable` (casesOn) and `allocatorState_computable` (rec).

### 5.7 `evaln`-of-decoded-code helper (for Stage E)
A named `def`/lemma capturing
`Nat.Partrec.Code.evaln s ((decode i).getD zero) (encode (s', out, ctx))` as a
computable function of `(i, s, s', out, ctx)`, so `approxEnum_computable` becomes
a `computable_finset_range_sup` of a named computable term instead of a
`convert/grind` blob.

### 5.8 What is NOT needed
No new `Primcodable` instances are required for the current representation:
`BitString = List Bool`, products, `Option`, `List`, `ℕ` all have them. Only if
Stage F introduces a `structure` would an `Equiv`-based `Primcodable` be needed —
and that is exactly the cost that argues against doing it early.

---

## 6. Suggested Gemini / Codex / Aristotle workflow

Principle: **broad reconstruction may break a branch; final checkpoints must be
green and theorem statements must not be weakened.**

- **Gemini — architecture & mathematics audit (no code authority).**
  - Audit theorem boundaries against SUV/LV; flag any over-strong or vacuous
    statements *before* refactoring (cheaper to fix on paper).
  - Maintain the dependency-direction map and propose module boundaries.
  - Owns: §3 blocker list upkeep and the public-API freeze list (see §7).
- **Codex — mechanical reconstruction & staged verification.**
  - Executes Stages A–E: move declarations, repair imports/`open`s, create the
    new modules, run per-module builds, keep each stage's final commit green.
  - Authors the small API lemmas of §5 whose proofs are routine.
  - Owns the green-checkpoint gate and statement-preservation diff.
- **Aristotle — bounded, single-lemma proof search with frozen statements.**
  - Receives one lemma at a time, imports fixed, **no permission to change public
    statements**. Good fit for the §8 tasks.
  - Caveat: Aristotle's prover runs on a different Lean/Mathlib than 4.31; treat
    its output as a proof *sketch to port*, and re-verify under 4.31 on the
    branch before accepting.

Branch policy:
- Long-lived `refactor/kc-computability-architecture`; intermediate red commits
  allowed. Each Stage ends with a green tag (`stageA-green`, …).
- `main` is protected by the §7 acceptance matrix; merge only via a fully green,
  statement-preserving squash.
- Every PR/commit that claims "green" runs the verification command block for the
  modules it touches **plus** the public-API and axiom checks.

Hygiene gate to run at each green checkpoint:
```
lake build KolmogorovMathlib
rg -n 'sorry|admit|axiom|unsafe|implemented_by|native_decide|sorryAx' KolmogorovMathlib
rg -n 'set_option maxHeartbeats' KolmogorovMathlib   # must be monotone non-increasing
```

---

## 7. Acceptance / review metrics (better than raw counts)

1. **Theorem-statement preservation (hard gate).** Freeze a list of public
   results and diff their elaborated signatures, not their proofs. Minimum set:
   `kraftChaitin_realization_bound`, `kraftChaitin_realization_bound_unit`,
   `exists_online_prefixFree_family`, `allocFun_prefixFree`, `allocFun_success`,
   `aprioriMeasure_le_complexityWeight_optimal`, `exists_universalSemimeasure`,
   `universalSemimeasure_equiv_prefixComplexity`,
   `pairMarginal_coding_bound`, and the `ConditionalCoding` public results.
   A `Scratch/ApiFreeze.lean` with `#check @name` for each, compared before/after,
   is sufficient and cheap. Any change is a blocker unless explicitly approved and
   documented.
2. **Axiom hygiene.** `Scratch/AxiomCheck.lean` runs `#print axioms` on the frozen
   list; accept only `propext`, `Classical.choice`, `Quot.sound`
   (+ `Lean.trustCompiler` if the toolchain emits it). Any other axiom is a
   blocker.
3. **Dependency hygiene.** No upward imports (high-level modules must not be
   imported by foundational ones); import graph stays acyclic; track module
   in-degree and DAG depth; a moved lemma must not pull in a strictly
   higher-level theory. Target: leaf computability modules eventually drop
   `import Mathlib` for narrow imports (post-refactor goal, not a gate).
4. **Module build time / per-declaration heartbeats.** Record `lake build` time
   per touched module and, via `set_option profiler true` (in scratch, not
   committed), the max heartbeats per declaration. Gate: no refactor may increase
   a module's build time or a declaration's heartbeat count without a documented
   net reduction elsewhere. Track total count and sum of `maxHeartbeats` budgets
   as a monotone-down series.
5. **Proof maintainability.** Combinator-vs-tactic ratio; count of raw
   `Computable.pair` chains (should fall as §5 lands); average proof length, with
   a soft flag at >50 lines; API reuse ratio (each new combinator lemma should be
   used ≥2×, else it's a renamed chunk, not an API).

Explicitly **demote** raw error/warning/sorry counts to a binary precondition
(must be zero at green checkpoints) rather than an optimization target.

---

## 8. Bounded tasks appropriate to submit to Aristotle (post-plan)

Submit individually, statements frozen, after the module structure (Stages A–C)
exists. Re-verify each under 4.31 because of the toolchain gap.

Smallest / safest first:
1. Each named projection lemma in §5.2 (one per field per shape) — trivial but
   bounded; ideal warm-ups.
2. The Option-combinator wrappers in §5.4.
3. The packed-application combinators in §5.3 (arity 2/3/4).
4. `allocStep_computable` (§5.5) and the restated `allocatorState_eq_rec`.
5. Re-prove, statement-unchanged, to hit a heartbeat target:
   `incNum_computable`, then `truncGTerm_computable_then`,
   then `allocatorState_computable`, then `allocFun_computable`.
6. Clean-room reproof of `approxEnum_computable` (§5.7) and
   `lscEnumApprox_uniform_computable` using the new helpers.

Avoid sending Aristotle: the module splits themselves (mechanical — Codex), and
any task that would require changing a public statement.

---

## 9. Risks and rollback criteria

Rollback the **current stage** (not the whole branch) if any of:
- a public theorem statement is weakened or generalized-away to make a proof pass;
- a module dependency cycle is introduced;
- a moved lemma requires importing a strictly higher-level theory;
- a new/edited proof introduces a `maxHeartbeats` budget exceeding the one it
  replaces without removing another bottleneck (net-negative perf);
- `#print axioms` on any frozen result gains a non-allowlisted axiom;
- `UniversalSemimeasure` / `ConditionalCoding` start depending on allocator
  *implementation* details instead of the Kraft-Chaitin public API.

Specific bets and their fallbacks:
- **Bet:** extracting `allocStep` + named combinators removes most of the 8M
  budget. **Fallback:** if heartbeats stay high, keep a reduced local budget and
  document it; do *not* jump to structures.
- **Bet (Gemini's):** structures cut heartbeats. **Treat as hypothesis only**;
  A/B-test on a single declaration in Stage F before any rollout. Abandon if it
  does not measurably help, since it costs `Primcodable`/`Computable` glue.

---

## 10. One-paragraph executive summary

The repository is in good logical health (no `sorry`/`axiom`/`unsafe`; sane
layering; the allocator already uses the right `irreducible` lever). The only real
scaling risk is structural: two oversized multi-role files and the absence of a
reusable computability-combinator layer, which together force hand-built witnesses
over deeply nested `Primcodable` products and produce the four heartbeat sites.
Adopt Codex's staged, statement-preserving order — split modules, then proof
layers, then add a concrete computability API (named projections, packed-
application and Option wrappers, an extracted allocator step) — and only then tune
the heartbeat proofs. Use Gemini's root-cause framing but reject its
structures-first representation change as the entry point; keep structures as a
measured last resort. Gate acceptance on statement preservation, axiom hygiene,
dependency direction, per-declaration heartbeats/build time, and proof
reusability rather than raw warning counts. Hand Aristotle the bounded,
frozen-statement lemmas in §8 once the new module skeleton is in place.
