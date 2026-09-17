#!/usr/bin/env python3
"""Comment-aware scan of Lean sources for forbidden constructs.

Replaces the naive audit greps: `--` line comments, nested `/- ... -/` block
comments (including doc comments), and string literals are stripped before
matching, so prose like "admit a uniformly computable sequence" in a docstring
no longer trips the audit. Only code can trigger a finding.

Usage: forbidden_scan.py --mode {forbidden,sorry} [ROOT...]
Prints `path:line:text` for each finding and exits 1 if any were found.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

FORBIDDEN_RE = re.compile(
    r"\b(axiom|admit|unsafe|implemented_by|native_decide)\b"
    r"|set_option\s+(maxHeartbeats|maxRecDepth)"
)
RESOURCE_RE = re.compile(r"set_option\s+(maxHeartbeats|maxRecDepth)")
DEFAULT_ALLOWLIST = Path("scripts/resource_override_allowlist.txt")


def load_allowlist(path: Path) -> set[str]:
    """File paths whose *resource overrides* are sanctioned.

    Only `maxHeartbeats` / `maxRecDepth` are ever excused, and only in the
    files named here; `axiom`, `admit`, `unsafe`, `implemented_by` and
    `native_decide` remain forbidden everywhere.
    """
    if not path.exists():
        return set()
    out = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            out.add(line)
    return out
SORRY_RE = re.compile(r"\bsorry\b|sorryAx")


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments and string literals, preserving line structure."""
    out = list(text)
    i = 0
    n = len(text)
    depth = 0  # nested block comments
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if ch != "\n":
                out[i] = " "
            i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if ch == '"':
            out[i] = " "
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out[i] = " "
                    if text[i + 1] != "\n":
                        out[i + 1] = " "
                    i += 2
                    continue
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def scan_file(path: Path, pattern: re.Pattern[str],
              resource_ok: bool = False) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return [f"{path}:0:unreadable ({exc})"]
    findings = []
    stripped = strip_comments_and_strings(text)
    original_lines = text.splitlines()
    for lineno, line in enumerate(stripped.splitlines(), start=1):
        if pattern.search(line):
            if resource_ok and RESOURCE_RE.search(line) and not re.search(
                    r"\b(axiom|admit|unsafe|implemented_by|native_decide)\b", line):
                continue
            shown = original_lines[lineno - 1] if lineno <= len(original_lines) else line
            findings.append(f"{path}:{lineno}:{shown.strip()}")
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["forbidden", "sorry"], required=True)
    parser.add_argument("roots", nargs="*", default=None)
    parser.add_argument("--allowlist", type=Path, default=DEFAULT_ALLOWLIST,
                        help="file listing paths whose resource overrides are sanctioned")
    args = parser.parse_args()
    pattern = FORBIDDEN_RE if args.mode == "forbidden" else SORRY_RE
    allowed = load_allowlist(args.allowlist) if args.mode == "forbidden" else set()
    roots = [Path(r) for r in (args.roots or ["KolmogorovMathlib", "KolmogorovMathlib.lean"])]
    findings: list[str] = []
    for root in roots:
        if root.is_dir():
            for path in sorted(root.rglob("*.lean")):
                findings.extend(scan_file(path, pattern, str(path) in allowed))
        elif root.exists():
            findings.extend(scan_file(root, pattern, str(root) in allowed))
    for line in findings:
        print(line)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
