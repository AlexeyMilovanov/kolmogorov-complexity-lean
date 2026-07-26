#!/usr/bin/env python3
"""Regression tests for the final release verdict and Git-tree fingerprint."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile

import final_release_gate as gate


def git(root: Path, *args: str) -> None:
    subprocess.run(
        ["git", *args],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )


def test_status_parser() -> None:
    assert gate.is_release_ready("STATUS: RELEASE_READY_32\n\nEvidence")
    assert not gate.is_release_ready("note\nSTATUS: RELEASE_READY_32")
    assert not gate.is_release_ready(
        "STATUS: RELEASE_READY_32\nSTATUS: NOT_RELEASE_READY_32"
    )


def test_candidate_tree() -> None:
    with tempfile.TemporaryDirectory(prefix="kolmogorov-gate-test-") as tmp:
        root = Path(tmp)
        scripts = root / "scripts"
        scripts.mkdir()
        tracked = root / "tracked.txt"
        obsolete = root / "obsolete.md"
        executable = scripts / "tool.sh"
        tracked.write_text("stable\n", encoding="utf-8")
        obsolete.write_text("obsolete\n", encoding="utf-8")
        executable.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
        executable.chmod(0o755)

        git(root, "init", "-q")
        git(root, "config", "user.name", "Release Gate Test")
        git(root, "config", "user.email", "release-gate@example.invalid")
        git(root, "add", "-A")
        git(root, "commit", "-qm", "baseline")

        paths = ("tracked.txt", "obsolete.md", "scripts")
        baseline = gate.candidate_tree(root, paths)

        tracked.write_text("changed\n", encoding="utf-8")
        assert gate.candidate_tree(root, paths) != baseline
        tracked.write_text("stable\n", encoding="utf-8")
        assert gate.candidate_tree(root, paths) == baseline

        executable.chmod(0o644)
        assert gate.candidate_tree(root, paths) != baseline
        executable.chmod(0o755)
        assert gate.candidate_tree(root, paths) == baseline

        obsolete.unlink()
        deleted = gate.candidate_tree(root, paths)
        assert deleted != baseline
        git(root, "add", "-A")
        git(root, "commit", "-qm", "delete obsolete document")
        assert gate.candidate_tree(root, paths) == deleted

        obsolete.write_text("obsolete\n", encoding="utf-8")
        assert gate.candidate_tree(root, paths) == baseline

        new_script = scripts / "new.sh"
        new_script.write_text("#!/usr/bin/env bash\n", encoding="utf-8")
        assert gate.candidate_tree(root, paths) != baseline


def main() -> int:
    test_status_parser()
    if os.name != "nt":
        test_candidate_tree()
    print("FINAL RELEASE GATE REGRESSION TESTS OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
