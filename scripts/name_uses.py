#!/usr/bin/env python3
"""Where is a short declaration name used?  Counts occurrences per file.

Usage:  python3 scripts/name_uses.py NAME [NAME ...]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DIRS = ['KolmogorovMathlib', 'KolmogorovCounterexamples']


def main(argv: list[str]) -> int:
    files = [p for d in DIRS for p in sorted((REPO / d).rglob('*.lean'))]
    files += [REPO / 'KolmogorovMathlib.lean',
              REPO / 'KolmogorovCounterexamples.lean']
    texts = {p: p.read_text() for p in files if p.exists()}
    for name in argv[1:]:
        pat = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
        hits = [(str(p.relative_to(REPO)), len(pat.findall(t)))
                for p, t in texts.items() if pat.search(t)]
        print(f'{name}: ' + ', '.join(f'{f}({n})' for f, n in hits))
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
