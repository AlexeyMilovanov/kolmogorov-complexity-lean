# Iteration 28 Affected-Check Baseline

`scripts/check_affected.py` provides a fast feedback layer for changed project
Lean sources. It does not replace `scripts/audit.sh` or the uncached strict
sweep used for final acceptance.

The command parses every source under `KolmogorovMathlib/` together with
`KolmogorovMathlib.lean`, validates all project imports, and computes the full
transitive reverse-import closure. It directly elaborates each changed module
with `flexible`, `longLine`, `multiGoal`, and `openClassical` enabled. Any
direct-check output is an error, including a linter warning. It then asks Lake
to build the maximal modules in the affected closure. Explicit `+Module`
targets disambiguate the root module from the `KolmogorovMathlib` library
target; building the maximal modules covers every path through the closure
without putting every affected module on the command line.

The graph check fails closed on a missing source, ambiguous input path,
ambiguous module, unresolved project import, import cycle, or unsupported
import syntax. Existing non-project Lean files and non-Lean paths are reported
and skipped.

## Representative closures

Run from the repository root:

```bash
scripts/check_affected.py --dry-run \
  KolmogorovMathlib/Restricted/GreedyCover.lean
scripts/check_affected.py --dry-run \
  KolmogorovMathlib/Core/Basic.lean
scripts/check_affected.py --dry-run KolmogorovMathlib.lean
```

The deterministic expected closure sizes are:

| Changed source | Affected modules | Reason |
|---|---:|---|
| `Restricted/GreedyCover.lean` | 24 | Restricted dependents and root |
| `Core/Basic.lean` | 112 | High-fan-out foundation source used by almost the whole project |
| `KolmogorovMathlib.lean` | 1 | Root import module has no project dependents |

The leaf and root cases each have the sole maximal target
`+KolmogorovMathlib`. The high-fan-out foundation case has six maximal targets:
the root plus `KraftChaitinOnline`, `FiniteDistribution`, `KPPairSwap`,
`Restricted.FamilyCurve.BadSets`, and `Restricted.FamilyCurve.GoodSets`.
These standalone leaves are not imported by the root module. Lake still
rebuilds only stale dependencies; the explicit `+` prevents accidentally
selecting the whole library target by name.

An ordinary affected check is:

```bash
scripts/check_affected.py KolmogorovMathlib/Restricted/GreedyCover.lean
```

The release gate remains:

```bash
bash scripts/audit.sh
```

## Iteration 28 verification

- All 118 project modules and all 491 import commands were inventoried.
- The three representative dry runs reproduced closure sizes 24, 112, and 1.
- A real `GreedyCover.lean` affected check passed its strict direct elaboration
  and maximal-module Lake build.
- A nonexistent project source failed closed, and a temporary warning-producing
  fixture was rejected despite Lean returning success.
- `scripts/audit.sh` passed its 2,843-job build and empty uncached 118-file
  strict sweep on 2026-07-24.
