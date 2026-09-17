#!/usr/bin/env python3
"""Move deprecated aliases out of the topic files.

`scripts/rename_decls.py` writes an `@[deprecated] alias old := new` next to the
declaration it renames.  The aliases live in `KolmogorovMathlib/Deprecated/`
instead (see `scripts/gen_deprecated.py`), so this tool deletes the inline ones
whose pair appears in the rename table; run `gen_deprecated.py` afterwards to
regenerate the `Deprecated/` modules from the table.

Usage:  python3 scripts/strip_inline_aliases.py
"""
from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RENAMES = REPO / 'docs/history/phase3_renames.tsv'
SINCE = '2026-09-08'
ATTR = f'@[deprecated (since := "{SINCE}")]'
LIBS = ('KolmogorovMathlib', 'KolmogorovCounterexamples')


def main() -> int:
    pairs = set()
    for line in RENAMES.read_text().split('\n'):
        parts = line.rstrip('\n').split('\t')
        if len(parts) >= 2:
            pairs.add((parts[0].split('.')[-1], parts[1].split('.')[-1]))

    removed = 0
    for lib in LIBS:
        for path in sorted((REPO / lib).rglob('*.lean')):
            if 'Deprecated' in path.parts:
                continue
            lines = path.read_text().split('\n')
            out: list[str] = []
            i = 0
            changed = False
            while i < len(lines):
                if lines[i] == ATTR and i + 1 < len(lines):
                    one = re.fullmatch(r'alias (\S+) := (\S+)', lines[i + 1])
                    two = re.fullmatch(r'alias (\S+) :=', lines[i + 1])
                    cont = (re.fullmatch(r'\s+(\S+)', lines[i + 2])
                            if two and i + 2 < len(lines) else None)
                    if one and (one.group(1), one.group(2)) in pairs:
                        step = 2
                    elif cont and (two.group(1), cont.group(1)) in pairs:
                        step = 3
                    else:
                        step = 0
                    if step:
                        if out and out[-1] == '':
                            out.pop()
                        i += step
                        changed = True
                        removed += 1
                        continue
                out.append(lines[i])
                i += 1
            if changed:
                path.write_text(re.sub(r'\n{3,}', '\n\n', '\n'.join(out)))
    print(f'removed {removed} inline aliases')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
