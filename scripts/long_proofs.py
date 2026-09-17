#!/usr/bin/env python3
"""List declarations whose source span exceeds a line threshold.

A declaration spans from its first modifier/keyword line (docstring and
attributes excluded) to the line before the next top-level command.  Block
comments are tracked so that prose does not open a declaration.

Usage:
    python3 scripts/long_proofs.py [--min 150] [--summary] [ROOT ...]
"""
from __future__ import annotations

import argparse
import re
from collections import Counter
from pathlib import Path

KEYWORDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure',
            'inductive', 'class', 'opaque', 'example', 'macro', 'notation',
            'syntax', 'elab', 'mutual', 'initialize', 'alias')
MODIFIERS = ('private', 'protected', 'nonrec', 'noncomputable', 'partial',
             'scoped', 'unsafe')
DECL_RE = re.compile(
    r'^(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*(?:' + '|'.join(KEYWORDS) +
    r')\b')
NAME_RE = re.compile(
    r'^(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*(?:' + '|'.join(KEYWORDS) +
    r')\s+([^\s({\[:]+)')
CONTEXT_RE = re.compile(r'^(open|variable|local|attribute|universe|set_option'
                        r'|namespace|end|section|omit|include|import|/-!|/--|@\[)')


def top_level_flags(lines: list[str]) -> list[bool]:
    """True for a line that starts outside any block comment."""
    flags, depth = [], 0
    for line in lines:
        flags.append(depth == 0)
        i = 0
        while i < len(line) - 1:
            if line[i:i + 2] == '/-':
                depth += 1
                i += 2
                continue
            if line[i:i + 2] == '-/':
                depth = max(0, depth - 1)
                i += 2
                continue
            i += 1
    return flags


def spans(path: Path):
    lines = path.read_text().split('\n')
    flags = top_level_flags(lines)
    starts = [i for i, l in enumerate(lines)
              if flags[i] and DECL_RE.match(l)]
    tops = [i for i, l in enumerate(lines)
            if flags[i] and (DECL_RE.match(l) or CONTEXT_RE.match(l))]
    for i in starts:
        nxt = next((j for j in tops if j > i), len(lines))
        while nxt - 1 > i and lines[nxt - 1].strip() == '':
            nxt -= 1
        m = NAME_RE.match(lines[i])
        yield (m.group(1) if m else '?'), i + 1, nxt - i


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('roots', nargs='*',
                    default=['KolmogorovMathlib', 'KolmogorovCounterexamples'])
    ap.add_argument('--min', type=int, default=150)
    ap.add_argument('--summary', action='store_true')
    args = ap.parse_args()

    root = Path(__file__).resolve().parent.parent
    found = []
    for r in args.roots:
        p = root / r
        files = sorted(p.rglob('*.lean')) if p.is_dir() else [p]
        for f in files:
            if 'Deprecated' in f.parts:
                continue
            for name, line, length in spans(f):
                if length > args.min:
                    found.append((length, f.relative_to(root), line, name))
    found.sort(reverse=True)
    if args.summary:
        c = Counter(str(f).split('/')[1] for _, f, _, _ in found)
        for k, v in c.most_common():
            print(f'{v:5d}  {k}')
    else:
        for length, f, line, name in found:
            print(f'{length:5d}  {f}:{line}  {name}')
    print(f'{len(found)} declarations over {args.min} lines')


if __name__ == '__main__':
    main()
