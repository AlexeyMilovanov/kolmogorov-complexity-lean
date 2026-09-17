#!/usr/bin/env bash
# Local rehearsal of .github/workflows/ci.yml.
#
# The workflow runs every one of its checks by calling this script with the
# name of a single step, so the two cannot drift apart: to change what CI does,
# change a step here.  Run without arguments to rehearse the whole workflow in
# the order the runner would execute it (the two jobs, one after the other).
#
#     .github/ci_local.sh                 # every step of both jobs
#     .github/ci_local.sh build-job       # the "build and audit" job only
#     .github/ci_local.sh docs-job        # the "documentation" job only
#     .github/ci_local.sh audit           # one named step
#     .github/ci_local.sh --list          # the step names, in order
#
# Environment:
#   BASE_REV   the revision the declaration-header freeze compares against.
#              On a pull request CI sets it to `origin/$GITHUB_BASE_REF`.
#              Unset locally, the freeze step is reported as skipped, exactly
#              as the workflow skips it outside a pull request.
#   SKIP_DOCS  set to 1 to leave the documentation job out of a full run
#              (it is a multi-hour build that also rebuilds Mathlib's docs).

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
export PATH="$HOME/.elan/bin:$PATH"

BUILD_JOB_STEPS=(
  toolchain
  cache
  build
  audit
  headers-selftest
  cut-quality-selftest
  cut-quality-calibration
  import-hygiene-selftest
  header-freeze
)
DOCS_JOB_STEPS=(
  toolchain
  cache
  docs
)

banner() { printf '\n=== %s ===\n' "$1"; }

step_toolchain() {
  lean --version
  lake --version
}

# The Mathlib cache.  Verified to work for Mathlib at the revision pinned in
# `lake-manifest.json`: the Azure cache answers and the oleans
# decompress.
step_cache() {
  lake exe cache get
}

step_build() {
  lake build
}

# Forbidden constructs, the `sorry` scan, the generated-table checks, the file
# size gate, the mechanical-cut gate and its calibration, docstring coverage,
# the build of every maximal root, the warning gate, the co-import smoke test,
# the axiom sweep and the tactic smoke tests.
# Invoked through `bash`: `scripts/audit.sh` is mode 100644 in git, so a fresh
# checkout (a CI runner, or a new clone) has no execute bit on it and calling
# it directly fails with "Permission denied".
step_audit() {
  bash scripts/audit.sh
}

# The test scripts run as steps of their own, so that a red one breaks
# CI even if `scripts/audit.sh` is edited to stop calling it.  (Today
# `audit.sh` calls the calibration and import check, but not their self-tests.)
step_headers_selftest()          { python3 -B scripts/tests/check_headers_selftest.py; }
step_cut_quality_selftest()      { python3 -B scripts/tests/cut_quality_selftest.py; }
step_cut_quality_calibration()   { python3 -B scripts/tests/cut_quality_calibration.py; }
step_import_hygiene_selftest()   { python3 -B scripts/tests/import_hygiene_selftest.py; }

# The statement freeze, in the invocation documented in CONTRIBUTING.md: the
# rename table, the definition-merge table and the phase-24 re-cut table are
# all required — without the last two the check reports the recorded deletions
# and restatements as problems and fails.
step_header_freeze() {
  if [[ -z "${BASE_REV:-}" ]]; then
    echo "BASE_REV is unset: skipped (CI runs this step on pull requests only)"
    return 0
  fi
  python3 -B scripts/check_headers.py --rev "$BASE_REV" \
    --by-name --allow-underscore \
    --renames docs/history/phase3_renames.tsv \
    --definition-merges docs/history/phase15_definition_merges.tsv \
    --recut docs/history/phase24_recut.tsv
}

# `doc-gen4` is required from the side package `docbuild/` only, so that the
# main build never depends on it.  Its revision is pinned in
# `docbuild/lakefile.toml`: `main` carries a newer lean-toolchain and `lake
# update` would switch the whole side package to it.
step_docs() {
  if [[ ! -f docbuild/lake-manifest.json ]]; then
    # `lake update doc-gen4` resolves the pinned revision and writes
    # `docbuild/lake-manifest.json`, and then runs Mathlib's post-update hook
    # (`lake exe cache get`), which fails on a tree whose ProofWidgets cloud
    # release is not unpacked ("Failed to prune ProofWidgets cloud release").
    # The resolution has already succeeded at that point, so the check is that
    # the manifest was written, not the exit status of the update.
    (cd docbuild && lake update doc-gen4) || true
    if [[ ! -f docbuild/lake-manifest.json ]]; then
      echo "lake update doc-gen4 did not write docbuild/lake-manifest.json" >&2
      return 1
    fi
  fi
  (cd docbuild && lake build KolmogorovMathlib:docs KolmogorovCounterexamples:docs)
}

run_step() {
  case "$1" in
    toolchain)                banner "$1"; step_toolchain ;;
    cache)                    banner "$1"; step_cache ;;
    build)                    banner "$1"; step_build ;;
    audit)                    banner "$1"; step_audit ;;
    headers-selftest)         banner "$1"; step_headers_selftest ;;
    cut-quality-selftest)     banner "$1"; step_cut_quality_selftest ;;
    cut-quality-calibration)  banner "$1"; step_cut_quality_calibration ;;
    import-hygiene-selftest)  banner "$1"; step_import_hygiene_selftest ;;
    header-freeze)            banner "$1"; step_header_freeze ;;
    docs)                     banner "$1"; step_docs ;;
    *) echo "unknown step: $1" >&2; exit 2 ;;
  esac
}

case "${1:-all}" in
  --list)
    printf 'build and audit:\n'; printf '  %s\n' "${BUILD_JOB_STEPS[@]}"
    printf 'documentation:\n';   printf '  %s\n' "${DOCS_JOB_STEPS[@]}"
    ;;
  all)
    for s in "${BUILD_JOB_STEPS[@]}"; do run_step "$s"; done
    if [[ "${SKIP_DOCS:-0}" = 1 ]]; then
      echo "SKIP_DOCS=1: the documentation job is skipped"
    else
      for s in "${DOCS_JOB_STEPS[@]}"; do run_step "$s"; done
    fi
    echo "CI REHEARSAL OK"
    ;;
  build-job)
    for s in "${BUILD_JOB_STEPS[@]}"; do run_step "$s"; done
    echo "CI REHEARSAL (build and audit) OK"
    ;;
  docs-job)
    for s in "${DOCS_JOB_STEPS[@]}"; do run_step "$s"; done
    echo "CI REHEARSAL (documentation) OK"
    ;;
  *)
    run_step "$1"
    ;;
esac
