#!/usr/bin/env python3
"""List the book-numbered declaration, namespace and section names of a file.

For each hit the tool prints the line number, the visibility, the current name
and — as an aid to choosing a name that describes the mathematics — the first
line of its docstring and the header of the declaration.

Usage:  python3 scripts/show_numbered.py FILE [FILE ...]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

NUMBERED = re.compile(
    r'(([A-Za-z_0-9.]*[._])?(thm|theorem|exercise|ex|Ex|Thm|Theorem|Exercise)'
    r'_?[0-9]|[A-Za-z_0-9.]*[a-z](Thm|Theorem|Exercise|Ex)[0-9])')
DECL = re.compile(
    r'^(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*)'
    r'(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance|'
    r'namespace|section)\s+(?P<name>[^\s({\[:]+)')


def header(lines: list[str], i: int, limit: int = 6) -> str:
    out = []
    for line in lines[i:i + limit]:
        out.append(line.rstrip())
        if ':=' in line or line.rstrip().endswith('by'):
            break
    return ' '.join(out)


def doc(lines: list[str], i: int) -> str:
    j = i - 1
    while j >= 0 and re.match(r'^(@\[|open .* in$|omit .* in$)', lines[j].strip()):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith('-/'):
        return ''
    k = j
    while k >= 0 and not lines[k].lstrip().startswith('/--'):
        k -= 1
    return ' '.join(x.strip() for x in lines[max(k, 0):j + 1])[:400]


def main(argv: list[str]) -> int:
    for arg in argv[1:]:
        p = Path(arg)
        lines = p.read_text().split('\n')
        print(f'### {p}')
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m or not NUMBERED.search(m.group('name')):
                continue
            vis = 'private' if 'private' in m.group('mods') else 'public'
            print(f'{i + 1}\t{vis}\t{m.group("kind")}\t{m.group("name")}')
            d = doc(lines, i)
            if d:
                print(f'\tDOC {d}')
            print(f'\tHDR {header(lines, i)[:400]}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
