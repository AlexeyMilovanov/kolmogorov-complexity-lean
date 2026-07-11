#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== escape hatch grep =="
if grep -RInE '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option maxHeartbeats 0' KolmogorovMathlib KolmogorovMathlib.lean 2>/dev/null; then
  echo "ERROR: hard escape hatch found"
  exit 1
fi

echo "== sorry containment =="
# sorries are allowed ONLY in loop-owned files (Restricted/ + EnumerationComplexity)
if grep -RInE '\bsorry\b|sorryAx' KolmogorovMathlib 2>/dev/null \
  | grep -vE '^KolmogorovMathlib/(Restricted/|Foundation/EnumerationComplexity\.lean)'; then
  echo "ERROR: sorry outside loop-owned files"
  exit 1
fi
echo "sorries (if any) are contained in loop-owned files."

echo "== lake build =="
export PATH="$HOME/.elan/bin:$PATH"
lake build KolmogorovMathlib

echo "AUDIT OK"
