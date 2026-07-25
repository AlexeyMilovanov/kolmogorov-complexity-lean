#!/usr/bin/env python3
"""Ask Codex whether accepted Lean 4.28 is ready, then hand off to migration."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from watch_polish_then_start_migration import Handoff


DEFAULT_POLISH_ROOT = Path("/home/lesha/kolmogorov-complexity-lean-28")
DEFAULT_POLISH_RUN = Path(
    "/home/lesha/kolmogorov-complexity-lean-runs/"
    "kc28_strict_polish_five_stage_20260720T111508Z"
)
DEFAULT_MIGRATION_ROOT = Path(
    "/home/lesha/kolmogorov-complexity-lean-31-port-current-28"
)
DEFAULT_RUNS_ROOT = Path("/home/lesha/kolmogorov-complexity-lean-runs")
CODEX = Path("/home/lesha/.npm-global/bin/codex")
READY = re.compile(r"(?im)^STATUS:\s*READY_FOR_MIGRATION\s*$")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def utc_stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def build_prompt(polish_root: Path, polish_run: Path) -> str:
    accepted = (
        polish_run
        / "full_project_polish"
        / "iter_040_proof"
    )
    return f"""
You are the sole final release-readiness reviewer for the accepted Lean 4.28
KolmogorovMathlib tree at `{polish_root}`.

This is deliberately NOT an ideality or strategy round. Do not demand that no
possible proof can ever be polished further. Decide whether the release
candidate is already excellent, formally complete for its current scope,
stable, and safe to freeze as the exact source for migration to Lean 4.31.

Iteration 40 is the accepted base checkpoint. Its evidence is under:
`{accepted}`.

The preceding release-readiness review found one concrete public-API defect:
`primrec_auto` could not expand for an external consumer because
`Primrec.to_comp` was unavailable at the macro declaration site. The current
tree contains the narrow corrective delta after iteration 40:

- `Foundation/PrimrecExtras.lean` imports
  `Mathlib.Computability.Partrec` at the defining site and documents why;
- `scripts/smoke/PrimrecAuto.lean` exercises the tactic as an external
  consumer;
- `scripts/audit.sh` runs that smoke test after rebuilding project modules.

The target module and external smoke test have already passed locally. Treat
this small delta as the subject of this review, not as unexplained drift. The
fail-closed handoff below will perform the full uncached validation before
committing it.

Inspect the actual repository, the corrective delta, accepted manifests and
merge-gate reports, current proof/style debt, audit scripts, import graph
tooling, and migration plan. The root Git tree is expected to contain the
accepted changes as an uncommitted batch; that alone is not a blocker because
the hard handoff gate will commit it after your verdict.

Do not edit any file. Do not start migration. A separate fail-closed handoff
will, after a positive verdict:

1. rerun the complete strict linter sweep;
2. rerun the full six-root project audit;
3. verify the accepted source did not change;
4. commit the final Lean 4.28 state;
5. create a read-only migration snapshot;
6. audit and checkpoint the Lean 4.31 baseline;
7. start the automated 28 -> 31 migration loop.

Use `STATUS: NOT_READY_FOR_MIGRATION` only for a concrete blocker such as a
formal hole, failing or unsound validation gate, emitted warning, forbidden
construct, semantic/API instability, missing required result, or material
unreviewed source drift. Optional proof golf, possible future module splits,
remaining contextual tactic candidates, and infrastructure that would matter
only after 10x-100x growth are not blockers if the present version is excellent
and the migration can safely preserve it.

Your first line must be exactly one of:

STATUS: READY_FOR_MIGRATION
STATUS: NOT_READY_FOR_MIGRATION

Then report:

## Evidence
State what you inspected and why it supports the verdict.

## Blocking Issues
Write `None` for a positive verdict, otherwise list exact blockers.

## Non-Blocking Future Improvements
List optional work that should not delay migration.

## Migration Constraints
State the invariants the 4.31 migration must preserve.
""".strip() + "\n"


def run_codex(
    *,
    polish_root: Path,
    polish_run: Path,
    gate_dir: Path,
    timeout: int,
) -> tuple[subprocess.CompletedProcess[str], str]:
    prompt = build_prompt(polish_root, polish_run)
    (gate_dir / "prompt.md").write_text(prompt, encoding="utf-8")
    command = [
        str(CODEX),
        "exec",
        "--ephemeral",
        "--skip-git-repo-check",
        "--sandbox",
        "read-only",
        "-C",
        str(polish_root),
        "--color",
        "never",
        "-m",
        "gpt-5.6-sol",
        "-c",
        'model_reasoning_effort="xhigh"',
        "-",
    ]
    result = subprocess.run(
        command,
        input=prompt,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )
    report = result.stdout.strip()
    (gate_dir / "codex_report.md").write_text(report + "\n", encoding="utf-8")
    write_json(
        gate_dir / "codex_raw.json",
        {
            "command": command,
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
        },
    )
    return result, report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--polish-root", type=Path, default=DEFAULT_POLISH_ROOT)
    parser.add_argument("--polish-run", type=Path, default=DEFAULT_POLISH_RUN)
    parser.add_argument("--migration-root", type=Path, default=DEFAULT_MIGRATION_ROOT)
    parser.add_argument("--runs-root", type=Path, default=DEFAULT_RUNS_ROOT)
    parser.add_argument("--codex-timeout", type=int, default=7200)
    parser.add_argument("--audit-timeout", type=int, default=7200)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    args.polish_root = args.polish_root.resolve()
    args.polish_run = args.polish_run.resolve()
    args.migration_root = args.migration_root.resolve()
    args.runs_root = args.runs_root.resolve()
    args.poll_seconds = 30

    gate_dir = args.polish_run / f"release_readiness_gate_{utc_stamp()}"
    gate_dir.mkdir(parents=True)
    log_path = gate_dir / "gate.log"

    def log(message: str) -> None:
        line = f"[{utc_now()}] {message}"
        print(line, flush=True)
        with log_path.open("a", encoding="utf-8") as handle:
            handle.write(line + "\n")

    handoff = Handoff(args)
    handoff.save_state(
        status="release_readiness_gate_running",
        release_gate=str(gate_dir),
    )
    source_before = handoff.source_fingerprint()
    log("Starting one-shot Codex release-readiness review")

    try:
        result, report = run_codex(
            polish_root=args.polish_root,
            polish_run=args.polish_run,
            gate_dir=gate_dir,
            timeout=args.codex_timeout,
        )
    except Exception as exc:
        handoff.save_state(
            status="release_readiness_gate_failed",
            release_gate_error=str(exc),
        )
        log(f"Codex release-readiness review failed: {exc}")
        return 1

    if result.returncode != 0:
        handoff.save_state(
            status="release_readiness_gate_failed",
            release_gate_returncode=result.returncode,
        )
        log(f"Codex exited with {result.returncode}; migration remains stopped")
        return 1

    if source_before != handoff.source_fingerprint():
        handoff.save_state(
            status="release_readiness_gate_failed",
            release_gate_error="source changed during read-only Codex review",
        )
        log("Source changed during Codex review; migration remains stopped")
        return 1

    if not READY.search(report):
        handoff.save_state(
            status="not_ready_for_migration",
            release_gate_report=str(gate_dir / "codex_report.md"),
        )
        log("Codex did not approve migration; polishing remains paused")
        return 2

    handoff.save_state(
        status="release_readiness_approved",
        release_gate_report=str(gate_dir / "codex_report.md"),
    )
    log("Codex approved the accepted Lean 4.28 checkpoint")
    try:
        handoff.finalize_and_handoff(40)
    except Exception as exc:
        handoff.save_state(
            status="handoff_failed_after_release_approval",
            handoff_error=str(exc),
        )
        log(f"Hard handoff gate failed after Codex approval: {exc}")
        return 1
    log("Migration handoff completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
