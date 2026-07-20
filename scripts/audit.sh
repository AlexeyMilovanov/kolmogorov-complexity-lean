#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== forbidden constructs and resource overrides =="
if grep -RInE '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)' \
    KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: forbidden construct or resource override found"
  exit 1
fi

echo "== sorry-free project =="
if grep -RInE '\bsorry\b|sorryAx' KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: sorry found in completed project"
  exit 1
fi

echo "== imports, suppressions, and measurement scaffolding =="
if grep -RInE '^import Mathlib$|#nolint|set_option linter\.|#count_heartbeats|set_option Elab\.async false|set_option profiler true|trace_state' \
    KolmogorovMathlib --include='*.lean' 2>/dev/null; then
  echo "ERROR: broad import, suppression, or temporary scaffolding found"
  exit 1
fi

echo "== project-level linter debt =="
if grep -nE '^(weak\.)?linter\..*= *false\b' lakefile.toml; then
  echo "TRANSITIONAL DEBT: strict linters remain disabled; merge may proceed only as measured cleanup progress"
  strict_linters_enabled=0
else
  strict_linters_enabled=1
fi

echo "== lake build, root plus standalone modules =="
export PATH="$HOME/.elan/bin:$PATH"
build_log="$(mktemp)"
trap 'rm -f "$build_log"' EXIT
lake build KolmogorovMathlib \
  KolmogorovMathlib.AlgorithmicProbability.KraftChaitinOnline \
  KolmogorovMathlib.AlgorithmicStatistics.FiniteDistribution \
  KolmogorovMathlib.Prefix.KPPairSwap 2>&1 | tee "$build_log"
if grep -E '(^|:)[[:space:]]*warning:' "$build_log" >/dev/null; then
  echo "ERROR: Lean warnings found"
  exit 1
fi

if [[ "$strict_linters_enabled" == 1 ]]; then
  echo "== uncached strict linter sweep =="
  bash scripts/strict_lint_sweep.sh
fi

echo "AUDIT OK"
