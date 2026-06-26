# Architecture Reconstruction Plan for the Lean 4.31 Kolmogorov Project

This file is the canonical plan for the long-running Gemini -> Codex reconstruction loop.
It should be edited when the strategy changes. The runner reads prompts from
`/home/lesha/kolmogorov-complexity-lean-runs/kc_reconstruction_prompts` on every
iteration, so the implementation strategy can be changed while the process is paused.

## Mission

Prepare the Lean 4.31 version of `kolmogorov-complexity-lean` for a 10x-100x expansion
of the formalized theory of Kolmogorov complexity. The immediate pain point is not a
mathematical `sorry`; the current project builds, but several core computability proofs
need high heartbeat limits and are too monolithic. The target is a Mathlib-style skeleton:
small modules, stable APIs, reusable computability lemmas, low heartbeat pressure, and
proofs that can be extended without repeatedly rebuilding ad hoc product encodings.

## Starting Point

The current 4.31 project is based on the GitHub-ready branch with commit
`9f4bb67 Update KolmogorovMathlib to Lean 4.31`. It builds with Lean/Mathlib 4.31 and has
no known `sorry`, `admit`, custom `axiom`, `unsafe`, or `set_option profiler true` in the
library.

The known remaining rough spots are concentrated in large manual computability proofs:

* `KolmogorovMathlib/AlgorithmicProbability/KraftChaitinCore.lean`
  * `incNum_computable`
  * `truncGTerm_computable_then`
* `KolmogorovMathlib/AlgorithmicProbability/KraftChaitinAllocator.lean`
  * `allocatorState_computable`
  * `allocFun_computable`

These currently use local high heartbeat settings. The goal is not merely to hide those
settings, but to make the local APIs good enough that such proofs become shorter and more
stable.

## Non-Negotiables

* Preserve all existing public theorem statements unless a deliberate compatibility shim is
  added and the old import path still works.
* Keep `lake build` green at committed checkpoints.
* Do not add `sorry`, `admit`, new `axiom`, `unsafe`, `implemented_by`, or
  `set_option profiler true`.
* Do not add new `set_option linter.style... false` suppressions.
* Do not increase heartbeat limits as a substitute for reconstruction. A temporary local
  heartbeat can be used only while repairing a broken state, and it must be called out in
  the handoff.
* Prefer additive helper APIs before moving existing declarations.
* Keep import compatibility files when splitting modules.
* Make every split reversible: small commits, clear changelog, no bulk renaming unless it
  unlocks an actual proof simplification.

## Lessons From Aristotle's Review

Aristotle's review agrees that the root cause is manual `Computable`/`Primrec` witnesses
for deeply nested products and decoded data. It specifically warns against a large early
representation swap to custom structures: the current Mathlib computability API is mostly
built around products, options, lists, and naturals, so a structures-first rewrite would
likely add coercion friction before it removes any real complexity.

The recommended approach is conservative and staged:

1. Build reusable tuple/projection/packed-application computability lemmas.
2. Split the large Kraft-Chaitin allocator and LSC/Kraft-Chaitin core modules along natural
   mathematical boundaries.
3. Reprove the four expensive computability theorems using the new helpers.
4. Only after the pattern is stable, consider optional representation wrappers or proof
   automation.

The full Aristotle report is copied next to this file as
`docs/reconstruction-review/ARISTOTLE_RECONSTRUCTION_REVIEW.md`.

## Stage A: Computability Tuple API

Create a new additive module, tentatively:

`KolmogorovMathlib/AlgorithmicProbability/Computability/Tuple.lean`

Possible surrounding namespace:

`Kolmogorov.Computability` or the local namespace already used in nearby files.

This module should collect reusable helpers that are currently scattered or repeated:

* promote/move existing helpers such as `beta_pair`, `beta_pair3`, `beta_pair4` if they
  are present locally;
* projection helpers for common shapes:
  * `Nat x BitString x BitString` / the corresponding nested product currently used;
  * that context paired with a natural recursion index;
  * `Nat x Nat x BitString`;
  * `(Nat x Nat x BitString) x Nat`;
  * `Nat x Nat x Nat x BitString`;
  * `(Nat x Nat x Nat x BitString) x Nat`;
  * `Nat x Nat x BitString x BitString`;
  * `(Nat x Nat x BitString x BitString) x Nat`;
  * allocator shapes such as `BitString x Nat`, `List BitString x Nat`, and the nested
    allocator state/request shapes currently used in `KraftChaitinAllocator`.
* packed application combinators for arity 2, 3, and 4;
* small wrappers for `Option.map`, `Option.bind`, `Option.getD`, `Option.casesOn` when
  used under `Computable`;
* small wrappers around `Nat.rec`/`Nat.casesOn` when they simplify recurring proofs.

Acceptance criteria for Stage A:

* The new module builds independently and is imported by existing files only where useful.
* At least one existing local proof is shortened or made clearer using the new helpers.
* No theorem statements are removed.
* No new heartbeat or linter suppressions are introduced.

## Stage B: Split KraftChaitinAllocator

Split `KolmogorovMathlib/AlgorithmicProbability/KraftChaitinAllocator.lean` into a folder
structure similar to:

* `AlgorithmicProbability/KraftChaitin/Allocator/Basic.lean`
* `AlgorithmicProbability/KraftChaitin/Allocator/Invariants.lean`
* `AlgorithmicProbability/KraftChaitin/Allocator/Computability.lean`
* `AlgorithmicProbability/KraftChaitin/Allocator/API.lean`

Keep the old file as an import aggregator until downstream imports have moved naturally.

Important local target:

* Extract a named `allocStep` for the state transition.
* Prove a reusable `allocStep_computable`.
* Restate the recursive allocator state theorem in terms of `allocStep`.
* Make `allocatorState_computable` and `allocFun_computable` shorter, ideally without
  local high heartbeat settings.

Acceptance criteria for Stage B:

* The old import path still works.
* The allocator API file exposes the declarations that downstream files actually use.
* Build remains green.
* At least one allocator heartbeat setting is removed or its proof is significantly
  simplified with a clear path to removal.

## Stage C: Split LSC and KraftChaitin Core

Split `KolmogorovMathlib/AlgorithmicProbability/KraftChaitinCore.lean` along conceptual
boundaries, tentatively:

* `AlgorithmicProbability/LSC/Defs.lean`
* `AlgorithmicProbability/LSC/Truncate.lean`
* `AlgorithmicProbability/LSC/Computability.lean`
* `AlgorithmicProbability/KraftChaitin/Request.lean`

Keep `KraftChaitinCore.lean` as a compatibility aggregator while the tree stabilizes.

Important local target:

* Separate definitions from computability proofs.
* Expose clean lemmas for truncated lower-semicomputable approximations.
* Make `incNum_computable` and `truncGTerm_computable_then` use the Stage A tuple API.

Acceptance criteria for Stage C:

* Old imports still work.
* New files have acyclic, downward imports.
* Build remains green.
* The `KraftChaitinCore` heartbeat settings are removed or are isolated behind much
  smaller named lemmas.

## Stage D: Heartbeat and Style Pass

After the structural split, remove or reduce the four known `set_option maxHeartbeats`
settings. If a theorem still needs a local heartbeat, document why in this file and in the
agent handoff. The desired end state is zero project-specific heartbeat settings in core
library files, or at least a very small and clearly justified number.

Metrics to record in the run directory:

* `lake build` return code and elapsed time;
* count and location of `set_option maxHeartbeats`;
* count and location of linter suppressions;
* warning count from build logs;
* local git diff summary;
* which stage was advanced.

## Stage E: UniversalSemimeasure API

Once the Kraft-Chaitin and LSC skeleton is stable, apply the same style to universal
semimeasure files:

* keep definitions and API lemmas separate from expensive computability proofs;
* add helper lemmas for evaluating decoded codes where they currently appear inline;
* keep theorem names stable and preserve imports.

This stage is not urgent until Stages A-D have made genuine progress.

## Stage F: Optional Representation Wrappers

Only after the tuple API works, consider lightweight structures or abbreviations for common
contexts. They should be API wrappers, not a wholesale rewrite. Every wrapper must come with
encoding/computability lemmas and must make at least one important proof simpler before it is
expanded across the project.

## Stage G: Future Automation

A `derive_computable`-style local tactic or macro may be useful later, but only after the
manual helper API has stabilized. Do not build automation before the repeated proof shapes
are known.

## Scaling Rules for a 10x-100x Project

* Every mathematical topic should have a small `Defs`/`Basic` layer and a separate
  `Computability` or `Encoding` layer when proofs get heavy.
* Compatibility aggregators are allowed during migration but should stay thin.
* Avoid hidden global dependencies: files about prefix complexity should not import heavy
  algorithmic probability machinery unless they need it.
* Prefer many small named lemmas over single huge proof blocks.
* Make theorem names searchable and descriptive. Avoid generated-looking local names in the
  public API.
* Keep examples/checks near the API while it is evolving, but remove debugging artifacts
  before GitHub-ready commits.

## Runner Protocol

The reconstruction runner is intentionally open-ended. It alternates Gemini and Codex until
it is stopped. Prompts are external and editable:

`/home/lesha/kolmogorov-complexity-lean-runs/kc_reconstruction_prompts`

Control files live in:

`/home/lesha/kolmogorov-complexity-lean-runs`

* `kc_reconstruction.pause`: pause before starting the next agent or next iteration.
* `kc_reconstruction.stop`: stop before starting the next iteration.
* `kc_reconstruction.stop_after_iteration`: finish the current Gemini -> Codex iteration,
  then stop.
* `kc_reconstruction.stop_after_green`: stop after the next successful build and local git
  checkpoint commit.

The runner reads prompt files fresh on every iteration. To change strategy, create the
pause file, edit prompts or this plan, then remove the pause file.

Committed checkpoints should be build-green. Broken intermediate states may exist in the
working tree between agents; the next agent is expected to repair them. The last local git
commit is the last accepted checkpoint.
