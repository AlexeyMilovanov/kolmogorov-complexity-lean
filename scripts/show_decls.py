#!/usr/bin/env python3
"""Print the header (docstring plus signature) of book-numbered declarations.

Usage:  python3 scripts/show_decls.py FILE [FILE ...] [--all]

Without `--all` only declarations whose name still carries a book number are
shown, which is what the phase-4 renaming pass works from.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

DECL = re.compile(
    r'^(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|'
    r'unsafe\s+)*)(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|'
    r'instance)\s+(?P<name>[^\s({\[:]+)')
BOOK = re.compile(r'(thm|Thm|theorem|Theorem|exercise|Exercise|ex[0-9]|Ex[0-9]'
                  r'|problem[0-9]|Problem[0-9])')


def main(argv: list[str]) -> int:
    show_all = '--all' in argv
    for arg in argv[1:]:
        if arg.startswith('--'):
            continue
        path = Path(arg)
        lines = path.read_text().split('\n')
        print(f'=== {path}')
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m:
                continue
            if not show_all and not BOOK.search(m.group('name')):
                continue
            j = i - 1
            while j >= 0 and (lines[j].startswith('@[')
                              or lines[j].strip().endswith(' in')):
                j -= 1
            doc: list[str] = []
            if j >= 0 and lines[j].rstrip().endswith('-/'):
                k = j
                while k >= 0 and not lines[k].lstrip().startswith('/--'):
                    k -= 1
                doc = lines[k:j + 1]
            sig = [lines[i]]
            k = i + 1
            while k < len(lines) and len(sig) < 8 and ':= by' not in sig[-1] \
                    and not sig[-1].rstrip().endswith(':='):
                sig.append(lines[k])
                k += 1
            print(f'--- {i + 1}: {m.group("name")}')
            for d in doc:
                print('   ' + d)
            for s in sig:
                print('   ' + s)
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
