#!/usr/bin/env python3
"""Finish strict 4.28 polishing and hand the accepted tree to 4.31 migration."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import time
from typing import Any


DEFAULT_POLISH_ROOT = Path("/home/lesha/kolmogorov-complexity-lean-28")
DEFAULT_POLISH_RUN = Path(
    "/home/lesha/kolmogorov-complexity-lean-runs/"
    "kc28_strict_polish_five_stage_20260720T111508Z"
)
DEFAULT_MIGRATION_ROOT = Path(
    "/home/lesha/kolmogorov-complexity-lean-31-port-current-28"
)
DEFAULT_RUNS_ROOT = Path("/home/lesha/kolmogorov-complexity-lean-runs")
SECTION = "full_project_polish"


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def utc_stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def read_json(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


class Handoff:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.polish_root = args.polish_root.resolve()
        self.polish_run = args.polish_run.resolve()
        self.migration_root = args.migration_root.resolve()
        self.log_path = self.polish_run / "polish_to_migration_handoff.log"
        self.state_path = self.polish_run / "polish_to_migration_handoff.json"
        self.state = read_json(
            self.state_path,
            {"checked_strategy_iterations": [], "status": "watching"},
        )

    def log(self, message: str) -> None:
        line = f"[{utc_now()}] {message}"
        print(line, flush=True)
        self.log_path.parent.mkdir(parents=True, exist_ok=True)
        with self.log_path.open("a", encoding="utf-8") as handle:
            handle.write(line + "\n")

    def save_state(self, **updates: Any) -> None:
        self.state.update(updates)
        self.state["updated_at"] = utc_now()
        self.state_path.write_text(
            json.dumps(self.state, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

    def run(
        self,
        command: list[str],
        *,
        cwd: Path | None = None,
        timeout: int | None = None,
        check: bool = True,
    ) -> subprocess.CompletedProcess[str]:
        self.log("RUN " + " ".join(command))
        result = subprocess.run(
            command,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        if result.stdout:
            with self.log_path.open("a", encoding="utf-8") as handle:
                handle.write(result.stdout)
                if not result.stdout.endswith("\n"):
                    handle.write("\n")
        if check and result.returncode != 0:
            raise RuntimeError(
                f"command failed with exit code {result.returncode}: {' '.join(command)}"
            )
        return result

    def completed_strategies(self) -> list[tuple[int, Path, dict[str, Any]]]:
        section_dir = self.polish_run / SECTION
        result: list[tuple[int, Path, dict[str, Any]]] = []
        for directory in section_dir.glob("iter_*_strategy"):
            match = re.fullmatch(r"iter_(\d+)_strategy", directory.name)
            if not match:
                continue
            manifest = read_json(directory / "manifest.json", {})
            if manifest.get("status") != "complete":
                continue
            result.append((int(match.group(1)), directory, manifest))
        return sorted(result)

    @staticmethod
    def aristotle_complete(manifest: dict[str, Any]) -> bool:
        aristotle = manifest.get("aristotle", {})
        followup = aristotle.get("followup", {})
        return bool(aristotle.get("submitted")) and followup.get("status") == "COMPLETE"

    @staticmethod
    def codex_declares_ideal(directory: Path) -> bool:
        report = directory / "04_codex.md"
        if not report.exists():
            return False
        text = report.read_text(encoding="utf-8", errors="replace")
        return bool(re.search(r"(?im)^STATUS:\s*NO_SAFE_IMPROVEMENT\s*$", text))

    def record_aristotle_summary(self, manifest: dict[str, Any]) -> None:
        archive_name = manifest.get("aristotle", {}).get("followup", {}).get("archive")
        if not archive_name:
            return
        archive = Path(archive_name)
        if not archive.exists():
            return
        try:
            with tarfile.open(archive) as bundle:
                members = [
                    member
                    for member in bundle.getmembers()
                    if member.isfile() and member.name.endswith("ARISTOTLE_SUMMARY.md")
                ]
                if not members:
                    return
                extracted = bundle.extractfile(members[-1])
                if extracted is None:
                    return
                summary = extracted.read().decode("utf-8", errors="replace")
                self.log("Aristotle strategic summary follows:\n" + summary[:12000])
        except Exception as exc:
            self.log(f"Could not read Aristotle archive: {exc}")

    def source_fingerprint(self) -> str:
        result = subprocess.run(
            [
                "git",
                "diff",
                "--binary",
                "--",
                "KolmogorovMathlib",
                "KolmogorovMathlib.lean",
                "lakefile.toml",
            ],
            cwd=self.polish_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=True,
        )
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=self.polish_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=True,
        ).stdout
        return hashlib.sha256((head + result.stdout).encode()).hexdigest()

    def static_cleanliness(self) -> None:
        lean_paths = list((self.polish_root / "KolmogorovMathlib").rglob("*.lean"))
        lean_paths.append(self.polish_root / "KolmogorovMathlib.lean")
        forbidden = re.compile(
            r"\b(?:axiom|admit|unsafe|implemented_by|native_decide|sorry|sorryAx)\b"
            r"|set_option\s+(?:maxHeartbeats|maxRecDepth)"
            r"|^import Mathlib$|#nolint|set_option\s+linter\."
            r"|#count_heartbeats|set_option\s+Elab\.async\s+false"
            r"|set_option\s+profiler\s+true|trace_state",
            re.MULTILINE,
        )
        findings: list[str] = []
        for path in lean_paths:
            text = path.read_text(encoding="utf-8", errors="replace")
            for match in forbidden.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                findings.append(f"{path.relative_to(self.polish_root)}:{line}: {match.group(0)}")
                if len(findings) >= 30:
                    break
        lakefile = (self.polish_root / "lakefile.toml").read_text(
            encoding="utf-8", errors="replace"
        )
        for match in re.finditer(r"(?m)^(?:weak\.)?linter\..*=\s*false\b", lakefile):
            line = lakefile.count("\n", 0, match.start()) + 1
            findings.append(f"lakefile.toml:{line}: {match.group(0)}")
        status = self.run(
            ["git", "status", "--porcelain=v1"], cwd=self.polish_root
        ).stdout.splitlines()
        for entry in status:
            if not entry.startswith("?? "):
                continue
            rel = entry[3:].strip()
            if rel == "KolmogorovMathlib.lean" or rel.startswith("KolmogorovMathlib/"):
                findings.append(f"untracked source: {rel}")
        if findings:
            raise RuntimeError("static cleanliness gate failed:\n" + "\n".join(findings))

    def machine_gate(self) -> None:
        before = self.source_fingerprint()
        self.static_cleanliness()
        self.run(
            ["bash", "scripts/strict_lint_sweep.sh"],
            cwd=self.polish_root,
            timeout=self.args.audit_timeout,
        )
        self.run(
            ["bash", "scripts/audit.sh"],
            cwd=self.polish_root,
            timeout=self.args.audit_timeout,
        )
        after = self.source_fingerprint()
        if before != after:
            raise RuntimeError("accepted 4.28 source changed while the ideality gate was running")

    @staticmethod
    def process_table() -> dict[int, tuple[int, str]]:
        table: dict[int, tuple[int, str]] = {}
        for proc in Path("/proc").iterdir():
            if not proc.name.isdigit():
                continue
            try:
                status = (proc / "status").read_text(encoding="utf-8")
                ppid_match = re.search(r"(?m)^PPid:\s+(\d+)$", status)
                command = (proc / "cmdline").read_bytes().replace(b"\0", b" ").decode(
                    "utf-8", errors="replace"
                )
                table[int(proc.name)] = (
                    int(ppid_match.group(1)) if ppid_match else 0,
                    command,
                )
            except (FileNotFoundError, PermissionError, ProcessLookupError):
                continue
        return table

    def polish_runner_pids(self) -> list[int]:
        needle = str(self.polish_run)
        return [
            pid
            for pid, (_, command) in self.process_table().items()
            if "run_proof_section_loop.py" in command and needle in command
        ]

    def migration_runner_pids(self) -> list[int]:
        return [
            pid
            for pid, (_, command) in self.process_table().items()
            if "run_migration_loop.py" in command
        ]

    def stop_polish(self) -> None:
        pause = self.polish_root / "proof_loop" / f"PAUSE.{SECTION}"
        pause.touch()
        table = self.process_table()
        roots = self.polish_runner_pids()
        targets = set(roots)
        changed = True
        while changed:
            changed = False
            for pid, (ppid, _) in table.items():
                if ppid in targets and pid not in targets:
                    targets.add(pid)
                    changed = True
        for pid in sorted(targets, reverse=True):
            try:
                os.kill(pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline and any(Path(f"/proc/{pid}").exists() for pid in targets):
            time.sleep(1)
        for pid in targets:
            if Path(f"/proc/{pid}").exists():
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        self.log(f"Polish runner stopped; pause marker: {pause}")

    def commit_paths(self, root: Path, paths: list[str], message: str) -> str:
        self.run(["git", "add", "-A", "--", *paths], cwd=root)
        staged = self.run(
            ["git", "diff", "--cached", "--quiet"], cwd=root, check=False
        )
        if staged.returncode == 1:
            self.run(["git", "commit", "-m", message], cwd=root)
        elif staged.returncode != 0:
            raise RuntimeError("git diff --cached --quiet failed")
        return self.run(["git", "rev-parse", "HEAD"], cwd=root).stdout.strip()

    def commit_final_28(self) -> str:
        return self.commit_paths(
            self.polish_root,
            [
                "KolmogorovMathlib",
                "KolmogorovMathlib.lean",
                "lakefile.toml",
                "COVERAGE.md",
                "README.md",
                "POLISHING_28_PLAN.md",
                "SCALABILITY_28_PLAN.md",
                "proof_loop/sections.json",
                "scripts",
            ],
            "Finalize strict Lean 4.28 Mathlib-style polishing",
        )

    def make_snapshot(self, commit: str) -> Path:
        snapshot = self.args.runs_root.parent / (
            f"kolmogorov-complexity-lean-28-migration-source-final-{utc_stamp()}"
        )

        def ignore(directory: str, names: list[str]) -> set[str]:
            ignored = {
                name
                for name in names
                if name in {".git", ".lake", "proof_loop_runs", "__pycache__"}
                or name.startswith("PAUSE")
                or name == "MERGE_GATE.lock"
                or name.endswith((".olean", ".ilean", ".log"))
            }
            return ignored

        shutil.copytree(self.polish_root, snapshot, symlinks=True, ignore=ignore)
        for path in [snapshot, *snapshot.rglob("*")]:
            try:
                mode = path.stat(follow_symlinks=False).st_mode
                path.chmod(mode & ~(stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH))
            except (FileNotFoundError, NotImplementedError):
                continue
        (snapshot.parent / f"{snapshot.name}.json").write_text(
            json.dumps(
                {"source": str(self.polish_root), "commit": commit, "created_at": utc_now()},
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        self.log(f"Created read-only 4.28 migration snapshot: {snapshot}")
        return snapshot

    def prepare_migration_root(self) -> str:
        if self.migration_runner_pids():
            raise RuntimeError("a Lean 4.31 migration runner is already active")
        for pycache in self.migration_root.rglob("__pycache__"):
            shutil.rmtree(pycache, ignore_errors=True)
        self.run(
            ["bash", "scripts/audit.sh"],
            cwd=self.migration_root,
            timeout=self.args.audit_timeout,
        )
        return self.commit_paths(
            self.migration_root,
            [
                "KolmogorovMathlib",
                "KolmogorovMathlib.lean",
                "lakefile.toml",
                "MIGRATION_28_TO_31.md",
                "MIGRATION_STATUS.md",
                "README.md",
                "scripts",
                "proof_loop/sections.json",
            ],
            "Checkpoint accepted Lean 4.31 migration baseline",
        )

    def start_migration(self, snapshot: Path) -> tuple[Path, int]:
        pause = self.migration_root / "proof_loop" / "PAUSE.migration_28_to_31"
        lock = self.migration_root / "proof_loop" / "MERGE_GATE.lock"
        pause.unlink(missing_ok=True)
        lock.unlink(missing_ok=True)
        run_dir = self.args.runs_root / f"kc31_migration_from_final28_{utc_stamp()}"
        run_dir.mkdir(parents=True)
        command = [
            sys.executable,
            "scripts/run_migration_loop.py",
            "--section",
            "migration_28_to_31",
            "--iterations",
            "25",
            "--start-iteration",
            "1",
            "--strategy-first",
            "1",
            "--strategy-every",
            "5",
            "--max-sorry-increase-per-merge",
            "0",
            "--timeout-seconds",
            "7200",
            "--aristotle-timeout-seconds",
            "86400",
            "--audit-timeout-seconds",
            str(self.args.audit_timeout),
            "--run-dir",
            str(run_dir),
        ]
        env = os.environ.copy()
        env.update(
            {
                "KOLMOGOROV_MIGRATION_SOURCE_28": str(snapshot),
                "KOLMOGOROV_CODEX_MODEL": "gpt-5.6-sol",
                "KOLMOGOROV_CODEX_EFFORT": "xhigh",
            }
        )
        output = (run_dir / "runner.log").open("a", encoding="utf-8")
        process = subprocess.Popen(
            command,
            cwd=self.migration_root,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=output,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        output.close()
        (run_dir / "runner.pid").write_text(f"{process.pid}\n", encoding="ascii")
        time.sleep(3)
        if process.poll() is not None:
            raise RuntimeError(f"migration runner exited immediately with {process.returncode}")
        self.log(f"Started Lean 4.31 migration PID {process.pid}: {run_dir}")
        return run_dir, process.pid

    def start_polish_continuation(self, start_iteration: int) -> int:
        pause = self.polish_root / "proof_loop" / f"PAUSE.{SECTION}"
        if pause.exists():
            return 0
        command = [
            sys.executable,
            "scripts/run_proof_section_loop.py",
            "--section",
            SECTION,
            "--iterations",
            "15",
            "--start-iteration",
            str(start_iteration),
            "--strategy-first",
            "1",
            "--strategy-every",
            "5",
            "--max-sorry-increase-per-merge",
            "0",
            "--timeout-seconds",
            "7200",
            "--aristotle-timeout-seconds",
            "86400",
            "--audit-timeout-seconds",
            str(self.args.audit_timeout),
            "--submit-aristotle",
            "--run-dir",
            str(self.polish_run),
        ]
        env = os.environ.copy()
        env.update(
            {
                "KOLMOGOROV_CODEX_MODEL": "gpt-5.6-sol",
                "KOLMOGOROV_CODEX_EFFORT": "xhigh",
            }
        )
        output = (self.polish_run / f"runner_restart_{start_iteration:03d}.log").open(
            "a", encoding="utf-8"
        )
        process = subprocess.Popen(
            command,
            cwd=self.polish_root,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=output,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        output.close()
        self.log(f"Restarted polishing at iteration {start_iteration}, PID {process.pid}")
        return process.pid

    def ensure_polishing_continues(self) -> None:
        if self.polish_runner_pids():
            return
        pause = self.polish_root / "proof_loop" / f"PAUSE.{SECTION}"
        if pause.exists():
            self.log(f"Polishing remains manually paused by {pause}")
            return
        manifests = list((self.polish_run / SECTION).glob("iter_*/manifest.json"))
        if not manifests:
            return
        iterations = [read_json(path, {}).get("iteration", 0) for path in manifests]
        latest = max(int(value) for value in iterations)
        latest_manifest = next(
            read_json(path, {})
            for path in manifests
            if int(read_json(path, {}).get("iteration", 0)) == latest
        )
        if latest_manifest.get("status") not in {"complete", "merged", "rejected"}:
            return
        self.start_polish_continuation(latest + 1)

    def finalize_and_handoff(self, iteration: int) -> None:
        self.stop_polish()
        self.log("Repeating the complete ideality gate on the stopped 4.28 tree")
        self.machine_gate()
        commit28 = self.commit_final_28()
        snapshot = self.make_snapshot(commit28)
        commit31 = self.prepare_migration_root()
        run_dir, migration_pid = self.start_migration(snapshot)
        completion = {
            "status": "migration_started",
            "strategic_iteration": iteration,
            "completed_at": utc_now(),
            "commit_28": commit28,
            "snapshot_28": str(snapshot),
            "commit_31_baseline": commit31,
            "migration_run": str(run_dir),
            "migration_pid": migration_pid,
        }
        marker = self.polish_root / "proof_loop" / "POLISHING_COMPLETE.json"
        marker.write_text(json.dumps(completion, indent=2) + "\n", encoding="utf-8")
        self.save_state(**completion)
        self.log("Strict polishing handoff completed successfully")

    def watch(self) -> int:
        checked = {int(value) for value in self.state.get("checked_strategy_iterations", [])}
        self.log("Watching strategic polishing rounds for a strict ideality verdict")
        while True:
            for iteration, directory, manifest in self.completed_strategies():
                if iteration in checked:
                    continue
                checked.add(iteration)
                self.state["checked_strategy_iterations"] = sorted(checked)
                self.record_aristotle_summary(manifest)
                if not self.aristotle_complete(manifest):
                    self.log(f"Strategy {iteration}: Aristotle review is not complete; no handoff")
                    self.save_state(last_checked_strategy=iteration)
                    continue
                if not self.codex_declares_ideal(directory):
                    self.log(
                        f"Strategy {iteration}: final Codex did not declare "
                        "STATUS: NO_SAFE_IMPROVEMENT; polishing continues"
                    )
                    self.save_state(last_checked_strategy=iteration)
                    continue
                self.log(f"Strategy {iteration}: semantic ideality verdict received; running hard gate")
                try:
                    self.machine_gate()
                except Exception as exc:
                    self.log(f"Strategy {iteration}: hard ideality gate failed: {exc}")
                    self.save_state(last_checked_strategy=iteration, last_gate_error=str(exc))
                    continue
                self.finalize_and_handoff(iteration)
                return 0
            self.save_state(checked_strategy_iterations=sorted(checked))
            self.ensure_polishing_continues()
            time.sleep(self.args.poll_seconds)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--polish-root", type=Path, default=DEFAULT_POLISH_ROOT)
    parser.add_argument("--polish-run", type=Path, default=DEFAULT_POLISH_RUN)
    parser.add_argument("--migration-root", type=Path, default=DEFAULT_MIGRATION_ROOT)
    parser.add_argument("--runs-root", type=Path, default=DEFAULT_RUNS_ROOT)
    parser.add_argument("--poll-seconds", type=int, default=30)
    parser.add_argument("--audit-timeout", type=int, default=7200)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    handoff = Handoff(args)
    try:
        return handoff.watch()
    except KeyboardInterrupt:
        handoff.log("Watcher interrupted")
        return 130
    except Exception as exc:
        handoff.save_state(status="failed", error=str(exc))
        handoff.log(f"FATAL: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
