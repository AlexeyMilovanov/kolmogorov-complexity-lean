#!/usr/bin/env python3
"""Module-docstring gate.

Every module of `KolmogorovMathlib` and `KolmogorovCounterexamples` — including
the two library roots — must carry a `/-! … -/` module docstring before its
first declaration, so that its doc-gen4 page renders with a description.

Usage:

    python3 scripts/module_docs.py            # list the modules without one
    python3 scripts/module_docs.py --check    # exit 1 if any module lacks one

A module docstring counts only if it opens with `/-!` at the start of a line
before the module's first declaration.  Scoping lines (`namespace`, `section`,
`open`, `variable`, `set_option`, `universe`, `import`) and line comments may
precede it; a `def`, `theorem`, `instance`, `notation`, … may not.
"""

from __future__ import annotations

import argparse
import pathlib
import sys

ROOTS = ["KolmogorovMathlib", "KolmogorovCounterexamples"]

# Lines that may precede the module docstring without ending the preamble.
PREAMBLE_PREFIXES = (
    "import ",
    "set_option ",
    "universe ",
    "namespace ",
    "section",
    "noncomputable section",
    "open ",
    "open\n",
    "variable ",
    "end ",
    "suppress_compilation",
)


def lean_files(base: pathlib.Path) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for root in ROOTS:
        top = base / f"{root}.lean"
        if top.exists():
            files.append(top)
        directory = base / root
        if directory.is_dir():
            files.extend(sorted(directory.rglob("*.lean")))
    return files


def strip_block_comments(lines: list[str]) -> list[tuple[int, str]]:
    """Return the (index, text) of the lines outside `/- … -/` comments.

    `/-!` blocks are *not* stripped: the gate needs to see them.
    """
    out: list[tuple[int, str]] = []
    depth = 0
    for i, line in enumerate(lines):
        rest = line
        emitted = ""
        while rest:
            if depth == 0:
                start = rest.find("/-")
                if start < 0:
                    emitted += rest
                    rest = ""
                elif rest.startswith("/-!", start):
                    emitted += rest[start:]
                    rest = ""
                else:
                    emitted += rest[:start]
                    rest = rest[start + 2 :]
                    depth = 1
            else:
                end = rest.find("-/")
                if end < 0:
                    rest = ""
                else:
                    rest = rest[end + 2 :]
                    depth = 0
        out.append((i, emitted))
    return out


def has_module_docstring(path: pathlib.Path) -> bool:
    lines = path.read_text(encoding="utf-8").splitlines()
    for _, text in strip_block_comments(lines):
        stripped = text.strip()
        if not stripped:
            continue
        if stripped.startswith("/-!"):
            return True
        if any(stripped.startswith(p) for p in PREAMBLE_PREFIXES):
            continue
        if stripped.startswith("--"):
            continue
        return False
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 if a module lacks one")
    parser.add_argument("--base", default=None, help="project root (default: the repository)")
    args = parser.parse_args()

    base = pathlib.Path(args.base) if args.base else pathlib.Path(__file__).resolve().parent.parent
    missing = [p for p in lean_files(base) if not has_module_docstring(p)]
    for p in missing:
        print(p.relative_to(base))
    total = len(lean_files(base))
    if args.check:
        if missing:
            print(f"ERROR: {len(missing)} of {total} modules have no module docstring")
            return 1
        print(f"module docstrings: OK ({total} modules)")
    else:
        print(f"{len(missing)} of {total} modules have no module docstring")
    return 0


if __name__ == "__main__":
    sys.exit(main())
