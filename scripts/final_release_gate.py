#!/usr/bin/env python3
"""Freeze Lean 4.32.1 only after deterministic and Codex release-readiness gates."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SOURCE_CONFIG = ROOT / "proof_loop" / "migration_source.json"
CODEX = Path("/home/lesha/.npm-global/bin/codex")
READY_STATUS = "STATUS: RELEASE_READY_32"
COMMIT_PATHS = (
    "KolmogorovMathlib",
    "KolmogorovMathlib.lean",
    "lakefile.toml",
    "lean-toolchain",
    "lake-manifest.json",
    "COVERAGE.md",
    "README.md",
    "MIGRATION_31_TO_32.md",
    "MIGRATION_STATUS.md",
    "SCALABILITY_32_PLAN.md",
    "MIGRATION_28_TO_31.md",
    "SCALABILITY_31_PLAN.md",
    "scripts",
    "proof_loop/sections.json",
    "proof_loop/migration_compatibility.json",
    "proof_loop/migration_source.json",
)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def run(
    command: list[str],
    *,
    timeout: int,
    check: bool = True,
    cwd: Path = ROOT,
    extra_env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
    if extra_env:
        env.update(extra_env)
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        env=env,
    )
    if check and result.returncode:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(command)}\n"
            f"{result.stdout[-12000:]}"
        )
    return result


def candidate_pathspecs(
    root: Path = ROOT,
    commit_paths: tuple[str, ...] = COMMIT_PATHS,
) -> list[str]:
    stageable_paths = []
    for path in commit_paths:
        full_path = root / path
        tracked = run(
            ["git", "ls-files", "--", path],
            timeout=60,
            cwd=root,
        ).stdout.strip()
        if full_path.exists() or full_path.is_symlink() or tracked:
            stageable_paths.append(path)
    return stageable_paths


def candidate_tree(
    root: Path = ROOT,
    commit_paths: tuple[str, ...] = COMMIT_PATHS,
) -> str:
    """Return the exact Git tree that commit_release would create."""
    stageable_paths = candidate_pathspecs(root, commit_paths)
    with tempfile.TemporaryDirectory(prefix="kolmogorov-release-index-") as tmp:
        index = Path(tmp) / "index"
        env = {"GIT_INDEX_FILE": str(index)}
        run(["git", "read-tree", "HEAD"], timeout=60, cwd=root, extra_env=env)
        if stageable_paths:
            run(
                ["git", "add", "-A", "--", *stageable_paths],
                timeout=120,
                cwd=root,
                extra_env=env,
            )
        return run(
            ["git", "write-tree"],
            timeout=60,
            cwd=root,
            extra_env=env,
        ).stdout.strip()


def is_release_ready(report: str) -> bool:
    lines = [line.strip() for line in report.splitlines()]
    status_lines = [line for line in lines if line.startswith("STATUS:")]
    return bool(lines) and lines[0] == READY_STATUS and status_lines == [READY_STATUS]


def source_info() -> dict[str, object]:
    value = json.loads(SOURCE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError("invalid migration source configuration")
    source = Path(str(value.get("root", ""))).resolve()
    if not source.is_dir():
        raise RuntimeError(f"final Lean 4.31 snapshot is unavailable: {source}")
    value["root"] = str(source)
    return value


def codex_prompt(source: dict[str, object], strategy_report: Path | None) -> str:
    strategy = (
        strategy_report.read_text(encoding="utf-8", errors="replace")
        if strategy_report and strategy_report.is_file()
        else "(no strategy report supplied)"
    )
    return f"""
You are the final read-only release reviewer for KolmogorovMathlib on Lean
4.32.1. The deterministic release audit has already passed.

Target repository: `{ROOT}`
Final polished Lean 4.31 authority: `{source['root']}`
Final 4.31 commit: `{source.get('commit')}`

This is not a request for metaphysical perfection. Approve only if the Lean
4.32.1 tree is excellent, complete for the formalized scope, at least as polished
as final Lean 4.31, and engineered for planned 10x-100x growth.

Verify directly:

- all 118 final-4.31 modules and public declaration names are represented;
- every documented 4.32.1 API adaptation preserves or strengthens the source;
- no theorem, assumption, public name, attribute, executable semantics,
  encoding order, or quantitative constant was lost;
- zero `sorry`, warnings, forbidden constructs, resource overrides, broad
  imports, source/project linter suppressions, or temporary scaffolding;
- every source passes uncached strict linters and exported tactics have
  external consumer smoke tests;
- import-graph, affected-build, standalone-root, and full-audit tooling is
  robust enough that a 10x-100x larger library need not rely on full builds for
  ordinary feedback;
- proofs are robust Mathlib style with no known actionable cleanup whose risk
  and value justify delaying release.

Optional future proof golf or speculative module splitting is not a blocker.
The completion marker is deliberately written only after this review approves,
the second deterministic audit passes, and the release commit is created.
Therefore a missing or stale `proof_loop/MIGRATION_COMPLETE.json` is expected
pre-release state and is not a review blocker. Review the candidate release
files and audit evidence themselves; do not require a pre-existing completion
marker or release commit.

Do not edit files or launch background agents. You may run ordinary read-only
shell commands to inspect the target, the immutable source, and existing audit
artifacts.

Latest migration strategy report:

```markdown
{strategy[-30000:]}
```

First line exactly:

STATUS: RELEASE_READY_32
or
STATUS: NOT_RELEASE_READY_32

Then provide `Evidence`, `Blocking Issues`, `Non-Blocking Improvements`, and
`Growth Readiness`.
""".strip() + "\n"


def run_codex(
    source: dict[str, object],
    strategy_report: Path | None,
    output_dir: Path,
    timeout: int,
) -> str:
    prompt = codex_prompt(source, strategy_report)
    (output_dir / "final_codex.prompt.md").write_text(prompt, encoding="utf-8")
    command = [
        str(CODEX),
        "exec",
        "--ephemeral",
        "--skip-git-repo-check",
        "--sandbox",
        "read-only",
        "-C",
        str(ROOT),
        "--add-dir",
        str(source["root"]),
        "--color",
        "never",
        "-m",
        os.environ.get("KOLMOGOROV_CODEX_MODEL", "gpt-5.6-sol"),
        "-c",
        f'model_reasoning_effort="{os.environ.get("KOLMOGOROV_CODEX_EFFORT", "xhigh")}"',
        "-",
    ]
    result = subprocess.run(
        command,
        cwd=ROOT,
        input=prompt,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )
    write_json(
        output_dir / "final_codex.raw.json",
        {
            "command": command,
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
        },
    )
    report = result.stdout.strip()
    (output_dir / "final_codex.md").write_text(report + "\n", encoding="utf-8")
    if result.returncode:
        raise RuntimeError(f"final Codex exited with {result.returncode}")
    return report


def commit_release(expected_tree: str) -> str:
    stageable_paths = candidate_pathspecs()
    if stageable_paths:
        run(["git", "add", "-A", "--", *stageable_paths], timeout=120)
    staged = run(
        ["git", "diff", "--cached", "--quiet"],
        timeout=60,
        check=False,
    )
    if staged.returncode == 1:
        run(
            ["git", "commit", "-m", "Finalize full-fidelity Lean 4.32.1 release"],
            timeout=120,
        )
    elif staged.returncode != 0:
        raise RuntimeError("git diff --cached --quiet failed")
    if candidate_tree() != expected_tree:
        raise RuntimeError("candidate Git tree changed while committing")
    status = run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        timeout=60,
    ).stdout.strip()
    if status:
        raise RuntimeError(f"release worktree is dirty after commit:\n{status}")
    commit = run(["git", "rev-parse", "HEAD"], timeout=60).stdout.strip()
    committed_tree = run(
        ["git", "rev-parse", f"{commit}^{{tree}}"],
        timeout=60,
    ).stdout.strip()
    if committed_tree != expected_tree:
        raise RuntimeError(
            f"committed tree {committed_tree} differs from reviewed tree {expected_tree}"
        )
    return commit


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--strategy-report", type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=7200)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    state_path = output_dir / "final_release_gate.json"
    try:
        source = source_info()
        before = candidate_tree()
        audit = run(
            ["bash", "scripts/audit.sh", "--release"],
            timeout=args.timeout_seconds,
        )
        (output_dir / "final_audit.log").write_text(audit.stdout, encoding="utf-8")
        report = run_codex(
            source,
            args.strategy_report,
            output_dir,
            args.timeout_seconds,
        )
        if before != candidate_tree():
            raise RuntimeError("candidate Git tree changed during read-only final review")
        if not is_release_ready(report):
            write_json(
                state_path,
                {
                    "status": "not_release_ready",
                    "finished_at": utc_now(),
                    "report": str(output_dir / "final_codex.md"),
                },
            )
            return 2
        second_audit = run(
            ["bash", "scripts/audit.sh", "--release"],
            timeout=args.timeout_seconds,
        )
        (output_dir / "final_audit_after_review.log").write_text(
            second_audit.stdout,
            encoding="utf-8",
        )
        if before != candidate_tree():
            raise RuntimeError("candidate Git tree changed during the second audit")
        commit = commit_release(before)
        result = {
            "status": "release_complete",
            "finished_at": utc_now(),
            "commit_32": commit,
            "source_31": source,
            "report": str(output_dir / "final_codex.md"),
        }
        write_json(state_path, result)
        write_json(ROOT / "proof_loop" / "MIGRATION_COMPLETE.json", result)
        return 0
    except Exception as error:
        write_json(
            state_path,
            {
                "status": "gate_failed",
                "finished_at": utc_now(),
                "error": f"{type(error).__name__}: {error}",
            },
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
