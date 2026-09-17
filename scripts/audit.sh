#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== forbidden constructs and resource overrides =="
# Comment-aware: prose in comments/docstrings must not trip the audit.
if ! python3 -B scripts/forbidden_scan.py --mode forbidden \
    KolmogorovMathlib KolmogorovMathlib.lean \
    KolmogorovCounterexamples KolmogorovCounterexamples.lean; then
  echo "ERROR: forbidden construct or resource override found"
  exit 1
fi

echo "== sorry scan =="
# Strict by default (completion gate). Merge-time invocations set
# AUDIT_ALLOW_SORRY=1: honest sorry leaves may land in the shared root within
# the merge gate's per-merge budget, so hard-theorem skeletons can merge early.
if ! python3 -B scripts/forbidden_scan.py --mode sorry \
    KolmogorovMathlib KolmogorovMathlib.lean \
    KolmogorovCounterexamples KolmogorovCounterexamples.lean; then
  if [ "${AUDIT_ALLOW_SORRY:-0}" = "1" ]; then
    echo "NOTE: sorry leaves present (allowed at merge time, forbidden at completion)"
  else
    echo "ERROR: sorry found in completed project"
    exit 1
  fi
fi

echo "== SUV coverage table =="
# docs/SUV_COVERAGE.md is generated; it must be current and every declaration
# it cites for a proved item must exist in the tree.
if ! python3 -B scripts/gen_suv_coverage.py --check; then
  echo "ERROR: docs/SUV_COVERAGE.md is stale or cites a missing declaration"
  exit 1
fi

echo "== deprecated aliases =="
# The `@[deprecated] alias`es live in `Deprecated/` only, and are generated
# from the public rows of the rename table.
if ! python3 -B scripts/gen_deprecated.py --check; then
  echo "ERROR: the Deprecated modules are stale; run scripts/gen_deprecated.py"
  exit 1
fi

echo "== file size gate =="
# Files stay under 1,000 lines; split by topic (CONTRIBUTING, "File size").
if oversized="$(
  find KolmogorovMathlib KolmogorovCounterexamples -name '*.lean' -print0 |
    xargs -0 wc -l | awk '$2 != "total" && $1 > 1000 { print $1, $2 }'
)"; [ -n "$oversized" ]; then
  echo "$oversized"
  echo "ERROR: the files above exceed 1,000 lines; split them by topic"
  exit 1
fi

echo "== mechanical-cut gate =="
# Flags the shapes four audits agreed are mechanical cuts (RFL-BINDER,
# SINGLE-USE-TAIL, WRAPPER, LONG-STATEMENT, THEOREM-HYP, SIBLING-PAIR,
# PADDED-BOUND, BINDER-RESTATE).  Justified exceptions live, with a reason,
# in docs/history/cut_quality_allow.tsv.
if ! python3 -B scripts/cut_quality.py; then
  echo "ERROR: mechanical-cut finding that is not in docs/history/cut_quality_allow.tsv"
  exit 1
fi

echo "== mechanical-cut gate: calibration against the audits =="
# The gate has to keep catching the ten cases four read-only audits called
# mechanical; fixtures for them live in scripts/tests/cut_quality_fixtures/.
# A rule loosened until a reference case slips through fails here.
if ! python3 -B scripts/tests/cut_quality_calibration.py; then
  echo "ERROR: scripts/cut_quality.py no longer catches every reference cut"
  exit 1
fi

echo "== docstring coverage of the fully documented directories =="
# A directory that has reached full docstring coverage must stay there.
if ! python3 -B scripts/docstring_coverage.py --check; then
  echo "ERROR: an undocumented public declaration was added to a fully documented directory"
  exit 1
fi

echo "== module docstring coverage =="
if ! python3 -B scripts/module_docs.py --check; then
  echo "ERROR: every Lean module must have a module docstring"
  exit 1
fi

echo "== import hygiene =="
if ! python3 -B scripts/import_hygiene.py --check; then
  echo "ERROR: duplicate direct imports found"
  exit 1
fi

echo "== Gacs-Day endpoint assembly guard =="
if ! python3 -B scripts/forbidden_scan.py --mode sorry \
    KolmogorovMathlib/MonotoneComplexity/GacsDayTheorems.lean; then
  echo "ERROR: public Gacs-Day endpoints must not contain direct sorry leaves"
  exit 1
fi

echo "== lake build, root plus standalone modules =="
export PATH="$HOME/.elan/bin:$PATH"
if ! build_roots_output="$(
  python3 -B scripts/check_affected.py --print-project-build-roots
)"; then
  echo "ERROR: failed to discover project build roots"
  exit 1
fi
if [[ -z "$build_roots_output" ]]; then
  echo "ERROR: project build-root discovery returned no modules"
  exit 1
fi
mapfile -t build_roots <<<"$build_roots_output"
# The counterexample library is a second root: it is deliberately not imported
# by `KolmogorovMathlib`, so root discovery over the main library misses it.
build_roots+=("KolmogorovCounterexamples")
build_log="$(mktemp)"
trap 'rm -f "$build_log" "${coimport_file:-}"' EXIT
if ! lake build "${build_roots[@]}" 2>&1 | tee "$build_log"; then
  echo "ERROR: lake build failed"
  exit 1
fi

echo "== warning-count gate =="
# The tree is warning-free and must stay that way: a `warning:` line in the
# build output fails the audit.  Fix the warning rather than silencing the
# linter.
if grep -n 'warning:' "$build_log"; then
  echo "ERROR: lake build produced warnings (see the lines above); the tree must build warning-free"
  exit 1
fi

echo "== co-import smoke test =="
# Every maximal root must be importable *together with* the aggregate root:
# a root that only elaborates in isolation hides a name or instance clash.
coimport_file="./coimport_smoke_$$.lean"
{
  echo "/- Generated by scripts/audit.sh; every maximal build root, co-imported. -/"
  echo "import KolmogorovMathlib"
  for root in "${build_roots[@]}"; do
    if [[ "$root" != "KolmogorovMathlib" ]]; then
      echo "import $root"
    fi
  done
} >"$coimport_file"
if ! lake env lean "$coimport_file"; then
  echo "ERROR: the maximal build roots do not co-import with KolmogorovMathlib"
  exit 1
fi
rm -f "$coimport_file"
coimport_file=""

echo "== axiom sweep =="
if ! python3 -B scripts/axiom_sweep.py; then
  echo "ERROR: a theorem depends on an axiom outside propext / Classical.choice / Quot.sound"
  exit 1
fi

echo "== public tactic smoke tests =="
if ! lake env lean scripts/smoke/PrimrecAuto.lean; then
  echo "ERROR: public tactic smoke test failed"
  exit 1
fi

if ! lake env lean scripts/smoke/GacsDayPublicGoals.lean; then
  echo "ERROR: Gacs-Day public goals are missing or their statements changed"
  exit 1
fi


echo "AUDIT OK"
