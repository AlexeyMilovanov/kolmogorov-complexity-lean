#!/usr/bin/env python3
"""Find proof-history prose in comments and docstrings.

A docstring describes what a statement means, not how its proof was found
(CONTRIBUTING, "Documentation").  This tool lists the comment lines that still
narrate the development process, so that they can be rewritten.  Only text
inside `--` line comments and `/- ... -/` block comments is searched, so an
identifier such as `S1` or a variable named `s1` in a proof is never reported.

Usage:
    python3 scripts/prose_scan.py [ROOT ...]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PATTERN = re.compile(
    r'wave|audit item|interface problem|banked|earlier attempt|previous rendering|'
    r'residual obligation|iteration [0-9]|milestone [A-Z][0-9]|skeleton stage|'
    r'draft leaf|open leaf|\bTODO\b|\bWIP\b|\bIP-[A-Z0-9]|\bS[1-7]\b', re.IGNORECASE)


def comment_lines(text: str):
    """Yield `(line number, comment text)` for every comment in `text`."""
    depth = 0
    for i, line in enumerate(text.split('\n'), start=1):
        out = []
        j = 0
        while j < len(line):
            two = line[j:j + 2]
            if depth == 0 and two == '--':
                out.append(line[j:])
                break
            if two == '/-':
                depth += 1
                j += 2
                continue
            if two == '-/':
                depth = max(depth - 1, 0)
                j += 2
                continue
            if depth > 0:
                out.append(line[j])
            j += 1
        if out:
            yield i, ''.join(out)


def main(argv: list[str]) -> int:
    roots = argv or ['KolmogorovMathlib', 'KolmogorovCounterexamples']
    count = 0
    for root in roots:
        for p in sorted(Path(root).rglob('*.lean')):
            if 'Deprecated' in p.parts:
                continue
            for i, comment in comment_lines(p.read_text()):
                if PATTERN.search(comment):
                    print(f'{p}:{i}: {comment.strip()}')
                    count += 1
    print(f'{count} comment lines matched')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
