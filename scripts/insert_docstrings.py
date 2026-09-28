#!/usr/bin/env python3
"""Insert docstrings.

Input: a TSV-ish file with records of the form

    @@ <path> <name>
    <docstring line>
    <docstring line>

The docstring is inserted directly above the declaration `<name>`, above any
attribute lines that precede it but below any `open ... in` / `omit ... in`
modifier, which must stay in front of the docstring.

Docstring lines may be given either as plain text or already wrapped in
`/-- ... -/`.
"""
import re, sys
from pathlib import Path

SKIP = re.compile(r'^@\[')
DECL = re.compile(
    r'^(?P<attrs>(?:@\[[^\]]*\]\s+)*)(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|'
    r'unsafe\s+)*)(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance)'
    r'\s+(?P<name>[^\s({\[:]+)')

records = []
cur = None
for raw in Path(sys.argv[1]).read_text().split('\n'):
    if raw.startswith('@@ '):
        _, path, name = raw.split(' ', 2)
        cur = (path, name.strip(), [])
        records.append(cur)
    elif cur is not None and raw.strip() != '':
        cur[2].append(raw)

byfile = {}
for path, name, doc in records:
    byfile.setdefault(path, []).append((name, doc))

for path, items in byfile.items():
    lines = Path(path).read_text().split('\n')
    inserts = []  # (index, text lines)
    for name, doc in items:
        idx = None
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if m and m.group('name') == name:
                idx = i
                break
        if idx is None:
            print(f'MISSING {path} {name}', file=sys.stderr)
            sys.exit(1)
        j = idx
        while j - 1 >= 0 and SKIP.match(lines[j - 1].strip()):
            j -= 1
        if lines[j - 1].rstrip().endswith('-/'):
            print(f'ALREADY DOCUMENTED {path} {name}', file=sys.stderr)
            continue
        if doc[0].lstrip().startswith('/--'):
            block = list(doc)
        elif len(doc) == 1:
            block = [f'/-- {doc[0]} -/']
        else:
            block = ['/-- ' + doc[0]] + doc[1:-1] + [doc[-1] + ' -/']
        inserts.append((j, block))
    for j, block in sorted(inserts, reverse=True):
        lines[j:j] = block
    Path(path).write_text('\n'.join(lines))
    print(f'{path}: inserted {len(inserts)}')
