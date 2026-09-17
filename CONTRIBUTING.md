# Contributing

This library formalises plain, prefix and monotone Kolmogorov complexity and
algorithmic statistics.  One page of conventions; everything else follows
[Mathlib's style guide](https://leanprover-community.github.io/contribute/style.html).

## Build and gates

```
lake build                 # KolmogorovMathlib and KolmogorovCounterexamples
bash scripts/audit.sh      # the completion gate, see below
```

(The scripts are tracked without the execute bit, so run them through `bash`
or `python3`; a fresh clone cannot execute `scripts/audit.sh` directly.)

`scripts/audit.sh` runs, in order: the forbidden-construct scan (no `sorry`,
`axiom`, `admit`, `unsafe`, `native_decide`, no resource override), the build of
every maximal root, a **warning gate** (a `warning:` line fails the audit), the
co-import smoke test (every root must elaborate together with the aggregate
root), the axiom sweep (`propext`, `Classical.choice`, `Quot.sound` only) and
the public tactic smoke tests.  It also runs, between the file-size gate and
the docstring gate, the **mechanical-cut gate** `scripts/cut_quality.py`: a
pure-text checker that flags the shapes four independent audits agreed mark a
lemma as a mechanical cut rather than a fact worth naming — `RFL-BINDER`,
`SINGLE-USE-TAIL`, `WRAPPER`, `LONG-STATEMENT`, `THEOREM-HYP`, `SIBLING-PAIR`,
`PADDED-BOUND` and `BINDER-RESTATE`.  A finding fails the audit unless it is
listed, with a reason a reviewer would accept, in
`docs/history/cut_quality_allow.tsv` (columns: code, fqn, reason).  Fix the
declaration in preference to adding a row.  A change is not finished until
`audit.sh` is green.

Auxiliary tools:

* The statement freeze.  The canonical invocation — the one CI runs, and the
  one to use by hand — passes all three tables:

  ```
  python3 scripts/check_headers.py --rev REV --by-name --allow-underscore \
    --renames docs/history/phase3_renames.tsv \
    --definition-merges docs/history/phase15_definition_merges.tsv \
    --recut docs/history/phase24_recut.tsv
  ```

  It compares the token sequence of every declaration header against the git
  revision `REV`, following renames through the rename table, rewriting a
  reference to a merged-away definition to its survivor (with the recorded
  argument map) through the definition-merge table, and accepting through the
  re-cut table the declarations that phase 24's cut-quality work deliberately
  deleted or restated.  The last two tables are not optional extras: against
  the commit before phase 24, dropping them turns 33 recorded deletions and
  53 recorded restatements into 86 reported problems.
* `scripts/cut_quality.py [--root DIR] [--allow FILE] [--no-allow]
  [--code CODE]` — the mechanical-cut gate described above; run with
  `--no-allow` to see every finding, including the allow-listed ones.  Its
  self-test is `scripts/tests/cut_quality_selftest.py`.
* `scripts/rename_decls.py TABLE` — performs a rename tree-wide, leaves a
  `@[deprecated] alias` for every public name, and appends to the rename table.

Do **not** run `lake exe shake`: imports that exist only for an `open`, a
notation, a tactic or an instance are invisible to it, and applying its
suggestions has broken the build before.  Import minimisation needs a
protect-list first (`scripts/noshake.json` is a start).

`python3 scripts/import_hygiene.py --check` rejects duplicate direct imports.
For nontrivial minimisation, record accepted removals in
`docs/history/phase25_imports.tsv` and imports retained for instances, notation,
`simp` lemmas or other implicit effects in `docs/history/import_protect.tsv`.
An import that directly owns an API used by a module should stay explicit even
when another current dependency happens to re-export it transitively.

## Continuous integration

`.github/workflows/ci.yml` runs two jobs on every push to `main` and every pull
request: **build and audit** (`lake exe cache get`, `lake build`,
`scripts/audit.sh`, the test scripts under `scripts/tests/`, and — on a
pull request — the statement freeze against the base commit) and
**documentation** (the `docbuild/` side package, uploaded as an artifact).

Every CI step is one named step of `scripts/ci_local.sh`, and the workflow
calls that script rather than repeating the commands, so the two cannot drift
apart.  Rehearse CI locally with

```
scripts/ci_local.sh --list          # the steps, in the order CI runs them
scripts/ci_local.sh                 # all of them
scripts/ci_local.sh audit           # one of them
BASE_REV=origin/main scripts/ci_local.sh header-freeze
SKIP_DOCS=1 scripts/ci_local.sh     # everything but the multi-hour docs build
```

Add a check by adding a step to `scripts/ci_local.sh` and a step to the
workflow that calls it.  The three test scripts
(`scripts/tests/check_headers_selftest.py`,
`scripts/tests/cut_quality_selftest.py`,
`scripts/tests/cut_quality_calibration.py`) are CI steps in their own right
even though `audit.sh` also runs the calibration: a red calibration has to
fail CI even if `audit.sh` stops calling it.

## Mathematical conventions

**Complexities are `ℕ∞`-valued, with `ℕ` shadows.**  `plainK U x`, `condK U x y`,
`KP`, `KPPlain` take values in `ℕ∞ = ENat`, so that "no description" is `⊤`
rather than a junk value.  Each has a `ℕ`-valued shadow (`plainKNat`, `cVal`,
`condCVal`, …) that agrees with it whenever the value is finite; the bridging
lemmas are `kVal_eq_coe`, `kNatVal_eq_coe` and their kin.  State a theorem in
`ℕ∞` when `⊤` is possible and in the shadow when the surrounding argument is
arithmetic.

**`O(1)` and `O(log)` are explicit.**  An `O(1)` term is a natural constant
quantified *before* everything else (`∃ c : ℕ, ∀ x, …`).  An `O(log n)` term is
`logSlack c n = c * (Nat.bits n).length + c`.  There is no unbound `O`
predicate; a statement never hides a constant behind a `Filter`.

**Plain versus prefix.**  Plain complexity is `plainK`/`condK` with
`isOptimalConditional`; prefix complexity is `KPPlain`/`KP` with
`IsOptimalPrefixConditional`.  The algorithmic-statistics layer
(`setComplexity`, `DeficiencyLe`, `IsStochastic`, `structureFunction`) is built
on the *prefix* complexity, while the book states those results for plain
complexity; the difference is absorbed by the explicit `logSlack` terms.  Say
which one a new statement uses in its docstring.

**Computability, the `Primrec`-level recipe.**  Build a computability proof
bottom-up from `Primrec`/`Computable` combinators for the *pieces*, then
transport it to the function you care about with `.of_eq (fun _ => rfl)` (or
`Primrec.of_eq`).  Never elaborate a combinator proof against an unfolded body:
that is what makes these proofs need a heartbeat override, and heartbeat
overrides are not allowed here.  `scripts/smoke/PrimrecAuto.lean` keeps the
public entry points of the recipe honest.

**Formulas are checked against the rendered page.**  The book text is read from
the scan, never from an OCR dump; two Problem 59 exponents were misread from
OCR before this rule existed.  A formula that disagrees with the rendered page
is a bug even if the OCR agrees with it.

## Naming

* Theorems and lemmas: `snake_case`, describing the statement
  (`condK_le_plainK`, `plainK_pair_le_add_two_log`).  A camelCase *identifier*
  from the library keeps its spelling inside the name (`card_stringsOfLength`,
  `exists_plainKNat_gt`).
* Functions and other `def`s: `lowerCamelCase` (`canonicalObject`, `logSlack`).
* Types, structures, classes and `Prop`-valued predicates: `UpperCamelCase`
  (`IsOptimalPrefixConditional`, `CanonicalObjectReduces`).
* **No book numbering in a name.**  A theorem is named after its mathematics;
  the book reference goes at the end of its docstring ("SUV Problem 59, p. 45").
  `docs/SUV_COVERAGE.md` maps book items to theorem names.
* A helper used once is `private`.
* Renaming a public name means leaving `@[deprecated (since := "…")] alias
  old := new` behind and recording the pair in
  `docs/history/phase3_renames.tsv`.

## Documentation

Every public `def`, `structure`, `class` and every theorem a reader would look
up carries a docstring that says what it *means*, with the book reference last.
A docstring describes the statement, not how the proof was found: no
"banked", "earlier attempt", "the previous rendering".

## Counterexamples

`KolmogorovCounterexamples` collects refutations of *our own* superseded
readings of the source.  Each module says which modelling mistake it closes and
points at the faithful statement that replaced it.  The library is deliberately
not imported by `KolmogorovMathlib`.  Negative results that the book itself
states (a converse that fails, "no algorithm computes …") are ordinary theorems
and stay in the main library.

## File size

Files stay under about 1,000 lines; split by topic (`Part01`, `Part02` only
when no topical split exists).  Proofs over about 150 lines are cut into named
lemmas wherever a natural cut exists.

## Module paths

An `import` line stays at or under **85 characters**, so a module path is at
most 78.  The budget is spent by the whole path, and a deep one spends it
fastest: a `PartNN` level costs seven characters and says nothing, and a
directory name repeated in its own leaves (`FamilyEnumeration/` under
`EnumerableFamilies/`) spends it twice.  Name a directory for its subject, drop
the qualifier the parent already supplies, and split by topic rather than by
`PartNN`.  Chopping a word short (`Conditio`, `SolovayFn`) is never the way to
fit.
