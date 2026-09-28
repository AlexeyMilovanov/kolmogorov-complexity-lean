#!/usr/bin/env python3
"""Repair the ``file`` column of ``docs/history/phase3_renames.tsv``.

After a module is split, the declarations it used to hold live in a different
file.  This script relocates every row whose target name is no longer declared
in the recorded file but is declared, unambiguously, somewhere else in the tree.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLE = ROOT / "docs" / "history" / "phase3_renames.tsv"

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|alias)\s+"
    r"([A-Za-z_0-9'.\u00c0-\uffff]+)",
    re.MULTILINE,
)


def declared_names(path: Path) -> set[str]:
    try:
        return {m.group(1).split(".")[-1] for m in DECL.finditer(path.read_text())}
    except OSError:
        return set()


def main() -> int:
    index: dict[Path, set[str]] = {}
    for lib in ("KolmogorovMathlib", "KolmogorovCounterexamples"):
        for p in (ROOT / lib).rglob("*.lean"):
            if "Deprecated" in p.parts:
                continue
            index[p] = declared_names(p)

    rows = [l.rstrip("\n").split("\t") for l in TABLE.read_text().splitlines() if l.strip()]
    changed = 0
    for row in rows:
        if len(row) < 3:
            continue
        base = row[1].split(".")[-1]
        rec = ROOT / row[2]
        if rec in index and base in index[rec]:
            continue
        hits = [p for p, names in index.items() if base in names]
        if len(hits) == 1:
            row[2] = str(hits[0].relative_to(ROOT))
            changed += 1
    TABLE.write_text("".join("\t".join(r) + "\n" for r in rows))
    print(f"relocated {changed} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
