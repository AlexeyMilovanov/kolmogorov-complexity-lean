#!/usr/bin/env python3
"""Check or remove duplicate direct imports in Lean modules."""

from __future__ import annotations

import argparse
from pathlib import Path


DEFAULT_ROOTS = (
    Path("KolmogorovMathlib"),
    Path("KolmogorovCounterexamples"),
    Path("KolmogorovMathlib.lean"),
    Path("KolmogorovCounterexamples.lean"),
)


def lean_files(roots: list[Path]) -> list[Path]:
    files: set[Path] = set()
    for root in roots:
        if root.is_file() and root.suffix == ".lean":
            files.add(root)
        elif root.is_dir():
            files.update(root.rglob("*.lean"))
    return sorted(files)


def process_file(path: Path, fix: bool) -> list[tuple[int, int, str]]:
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    first_seen: dict[str, int] = {}
    duplicates: list[tuple[int, int, str]] = []
    kept: list[str] = []

    for line_no, line in enumerate(lines, start=1):
        if line.startswith("import "):
            module = line.removeprefix("import ").strip()
            if module in first_seen:
                duplicates.append((line_no, first_seen[module], module))
                if fix:
                    continue
            else:
                first_seen[module] = line_no
        kept.append(line)

    if fix and duplicates:
        path.write_text("".join(kept), encoding="utf-8")
    return duplicates


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="report duplicates (the default)")
    mode.add_argument("--fix", action="store_true", help="remove duplicate import lines")
    parser.add_argument("roots", nargs="*", type=Path, default=list(DEFAULT_ROOTS))
    args = parser.parse_args()

    total = 0
    for path in lean_files(args.roots):
        duplicates = process_file(path, args.fix)
        total += len(duplicates)
        if not args.fix:
            for line_no, first_line, module in duplicates:
                print(f"{path}:{line_no}: duplicate import {module!r} (first at line {first_line})")

    if args.fix:
        print(f"removed {total} duplicate import lines")
        return 0
    if total:
        print(f"ERROR: found {total} duplicate import lines")
        return 1
    print("import hygiene: OK (no duplicate direct imports)")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
