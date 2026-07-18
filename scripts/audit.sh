#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== escape hatch grep =="
if grep -RInE '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option maxHeartbeats 0' KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: hard escape hatch found"
  exit 1
fi

echo "== sorry-free project =="
if grep -RInE '\bsorry\b|sorryAx' KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: sorry found in completed project"
  exit 1
fi

echo "== polishing debt snapshot =="
heartbeat_lines="$(grep -RIn 'set_option maxHeartbeats' KolmogorovMathlib --include='*.lean' 2>/dev/null || true)"
if [[ -n "$heartbeat_lines" ]]; then
  echo "$heartbeat_lines"
  echo "maxHeartbeats overrides: $(printf '%s\n' "$heartbeat_lines" | wc -l)"
else
  echo "maxHeartbeats overrides: 0"
fi

echo "== lake build =="
export PATH="$HOME/.elan/bin:$PATH"
lake build KolmogorovMathlib

echo "AUDIT OK"
