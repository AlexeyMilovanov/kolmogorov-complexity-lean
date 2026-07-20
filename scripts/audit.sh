#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== forbidden constructs =="
if grep -RInE '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option maxHeartbeats' \
    KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: forbidden construct or heartbeat override found"
  exit 1
fi

echo "== sorry-free project =="
if grep -RInE '\bsorry\b|sorryAx' KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: sorry found"
  exit 1
fi

echo "== broad imports and suppressions =="
if grep -RInE '^import Mathlib$|#nolint|set_option linter\.' KolmogorovMathlib --include='*.lean' 2>/dev/null; then
  echo "ERROR: broad import or linter suppression found"
  exit 1
fi

echo "== temporary measurement scaffolding =="
if grep -RInE '#count_heartbeats|set_option Elab\.async false|set_option profiler true|trace_state' \
    KolmogorovMathlib --include='*.lean' 2>/dev/null; then
  echo "ERROR: measurement scaffolding found"
  exit 1
fi

echo "== lake build =="
export PATH="$HOME/.elan/bin:$PATH"
build_log="$(mktemp)"
trap 'rm -f "$build_log"' EXIT
lake build KolmogorovMathlib 2>&1 | tee "$build_log"
if grep -E '(^|:)[[:space:]]*warning:' "$build_log" >/dev/null; then
  echo "ERROR: Lean warnings found"
  exit 1
fi

echo "AUDIT OK"
