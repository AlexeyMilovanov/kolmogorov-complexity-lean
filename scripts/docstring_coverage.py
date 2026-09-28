#!/usr/bin/env python3
"""Docstring coverage of public declarations, per directory and overall.

A declaration counts as documented when the line above it (skipping attribute
lines and a single `open ... in`) ends a `/-- ... -/` docstring.

Usage:
    python3 scripts/docstring_coverage.py [ROOT ...]
        report coverage per directory and overall;
    python3 scripts/docstring_coverage.py --check [ROOT ...]
        list every undocumented public declaration under the given roots and
        exit non-zero if there is one.  `audit.sh` calls this for the
        directories that have reached full coverage, so that they stay there.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

DECL = re.compile(
    r'^(?P<attrs>(?:@\[[^\]]*\]\s+)*)(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|'
    r'unsafe\s+)*)(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive)'
    r'\s+(?P<name>[^\s({\[:]+)')
SKIP = re.compile(r'^(@\[|open .* in$|omit .* in$|attribute)')

# Directories whose public declarations are all documented.  `audit.sh` passes
# these to `--check`; add a directory here once it reaches full coverage.
COMPLETE = [
    'KolmogorovMathlib/AlgorithmicProbability',
    'KolmogorovMathlib/AlgorithmicRandomness',
    'KolmogorovMathlib/AlgorithmicStatistics',
    'KolmogorovMathlib/CommonInformation',
    'KolmogorovMathlib/Complexity',
    'KolmogorovMathlib/Core',
    'KolmogorovMathlib/Encoding',
    'KolmogorovMathlib/Foundation',
    'KolmogorovMathlib/Interface',
    'KolmogorovMathlib/MonotoneComplexity',
    'KolmogorovMathlib/Prefix',
    'KolmogorovMathlib/Restricted',
    'KolmogorovMathlib/StoppingComplexity',
]


def decl_lines(lines: list[str]):
    """Yield `(index, match)` for every declaration line outside a block comment.

    Block comments are tracked with a nesting depth so that prose inside a
    module docstring that happens to start with `theorem ...` is not mistaken
    for a declaration.
    """
    depth = 0
    for i, line in enumerate(lines):
        start_depth = depth
        j = 0
        while j < len(line) - 1:
            if line[j:j + 2] == '/-':
                depth += 1
                j += 2
            elif line[j:j + 2] == '-/':
                depth = max(depth - 1, 0)
                j += 2
            else:
                j += 1
        if start_depth == 0:
            m = DECL.match(line)
            if m:
                yield i, m


def undocumented(roots: list[str]) -> list[tuple[str, int, str]]:
    """Every undocumented public declaration under `roots`, as (file, line, name)."""
    out: list[tuple[str, int, str]] = []
    for root in roots:
        p0 = Path(root)
        paths = sorted(p0.rglob('*.lean')) if p0.is_dir() else [p0]
        for p in paths:
            lines = p.read_text().split('\n')
            for i, m in decl_lines(lines):
                if 'private' in m.group('mods'):
                    continue
                j = i - 1
                while j >= 0 and SKIP.match(lines[j].strip()):
                    j -= 1
                if not (j >= 0 and lines[j].rstrip().endswith('-/')):
                    out.append((str(p), i + 1, m.group('name')))
    return out


def scan(roots: list[str]) -> tuple[int, int, dict[str, tuple[int, int]]]:
    total = undoc = 0
    per: dict[str, list[int]] = {}
    for root in roots:
        for p in sorted(Path(root).rglob('*.lean')):
            key = '/'.join(p.parts[:2])
            lines = p.read_text().split('\n')
            for i, m in decl_lines(lines):
                if 'private' in m.group('mods'):
                    continue
                j = i - 1
                while j >= 0 and SKIP.match(lines[j].strip()):
                    j -= 1
                documented = j >= 0 and lines[j].rstrip().endswith('-/')
                total += 1
                per.setdefault(key, [0, 0])[0] += 1
                if not documented:
                    undoc += 1
                    per[key][1] += 1
    return total, undoc, {k: (v[0], v[1]) for k, v in per.items()}


def main(argv: list[str]) -> int:
    if argv and argv[0] == '--check':
        roots = argv[1:] or COMPLETE
        bad = undocumented(roots)
        for path, line, name in bad:
            print(f'{path}:{line}: undocumented public declaration `{name}`')
        if bad:
            print(f'{len(bad)} undocumented public declarations in directories '
                  f'that must stay fully documented')
            return 1
        print(f'all public declarations documented in: {", ".join(roots)}')
        return 0

    roots = argv or ['KolmogorovMathlib', 'KolmogorovCounterexamples']
    total, undoc, per = scan(roots)
    for k in sorted(per, key=lambda k: -per[k][1]):
        t, u = per[k]
        print(f'{u:6d} / {t:6d}  {k}')
    print(f'{undoc} of {total} public declarations without a docstring '
          f'({100 * undoc / max(total, 1):.0f}%)')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
