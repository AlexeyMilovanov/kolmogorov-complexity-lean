#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

release=false
if [[ "${1:-}" == "--release" ]]; then
  release=true
  shift
fi
if [[ $# -ne 0 ]]; then
  echo "ERROR: usage: scripts/audit.sh [--release]"
  exit 1
fi

echo "== forbidden constructs and resource overrides =="
if grep -RInE '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)' \
    KolmogorovMathlib KolmogorovMathlib.lean scripts/smoke 2>/dev/null; then
  echo "ERROR: forbidden construct or resource override found"
  exit 1
fi

echo "== sorry-free project =="
if grep -RInE '\bsorry\b|sorryAx' \
    KolmogorovMathlib KolmogorovMathlib.lean scripts/smoke 2>/dev/null; then
  echo "ERROR: sorry found in completed project"
  exit 1
fi

echo "== imports, suppressions, and measurement scaffolding =="
if grep -RInE '^import Mathlib$|#nolint|set_option linter\.|#count_heartbeats|set_option Elab\.async false|set_option profiler true|trace_state' \
    KolmogorovMathlib scripts/smoke --include='*.lean' 2>/dev/null; then
  echo "ERROR: broad import, suppression, or temporary scaffolding found"
  exit 1
fi

echo "== project-level linter debt =="
project_linter_debt="$(
  grep -nE '^(weak\.)?linter\..*= *false\b' lakefile.toml || true
)"
if [[ -n "$project_linter_debt" ]]; then
  printf '%s\n' "$project_linter_debt"
  if [[ "$release" == true ]]; then
    echo "ERROR: project-level linter suppressions remain"
    exit 1
  fi
  echo "TRANSITIONAL DEBT: touched Lean files must still pass strict direct checks"
  strict_linters_enabled=false
else
  strict_linters_enabled=true
fi

echo "== migration fidelity =="
python3 -B scripts/test_migration_fidelity.py
python3 -B scripts/check_migration_fidelity.py

echo "== lake build, root plus standalone modules =="
export PATH="$HOME/.elan/bin:$PATH"
build_log="$(mktemp)"
smoke_log="$(mktemp)"
trap 'rm -f "$build_log" "$smoke_log"' EXIT
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
lake build "${build_roots[@]}" 2>&1 | tee "$build_log"
if grep -E '(^|:)[[:space:]]*warning:' "$build_log" >/dev/null; then
  echo "ERROR: Lean warnings found"
  exit 1
fi

echo "== public tactic smoke tests =="
if ! lake env lean scripts/smoke/PrimrecAuto.lean >"$smoke_log" 2>&1; then
  cat "$smoke_log"
  echo "ERROR: public tactic smoke test failed"
  exit 1
fi
if [[ -s "$smoke_log" ]]; then
  cat "$smoke_log"
  echo "ERROR: public tactic smoke test emitted output"
  exit 1
fi

echo "== compatibility smoke test =="
if ! lake env lean scripts/smoke/MigrationCompatibility.lean >"$smoke_log" 2>&1; then
  cat "$smoke_log"
  echo "ERROR: compatibility smoke test failed"
  exit 1
fi
if [[ -s "$smoke_log" ]]; then
  cat "$smoke_log"
  echo "ERROR: compatibility smoke test emitted output"
  exit 1
fi

if [[ "$strict_linters_enabled" == true ]]; then
  echo "== uncached strict linter sweep =="
  bash scripts/strict_lint_sweep.sh
elif [[ "$release" == true ]]; then
  echo "ERROR: release audit cannot skip the strict linter sweep"
  exit 1
fi

echo "AUDIT OK"
