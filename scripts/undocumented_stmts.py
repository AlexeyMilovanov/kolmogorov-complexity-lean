#!/usr/bin/env python3
"""Print undocumented public declarations of a file with their statements.

Also reports how many files in the two libraries (excluding `Deprecated/`)
mention the name, so single-file helpers can be spotted.
"""
import re, sys, pickle, os
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from docstring_coverage import undocumented

ROOT = Path(__file__).resolve().parent.parent
CACHE = Path('/tmp/token_index.pkl')
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?.]*")

def build_index():
    idx = {}
    for lib in ['KolmogorovMathlib', 'KolmogorovCounterexamples']:
        for p in (ROOT / lib).rglob('*.lean'):
            if 'Deprecated' in p.parts:
                continue
            text = p.read_text()
            for t in set(TOK.findall(text)):
                idx.setdefault(t, set()).add(str(p.relative_to(ROOT)))
    return idx

if CACHE.exists() and os.environ.get('REFRESH') != '1':
    idx = pickle.load(CACHE.open('rb'))
else:
    idx = build_index()
    pickle.dump(idx, CACHE.open('wb'))

for path in sys.argv[1:]:
    lines = Path(path).read_text().split('\n')
    for (_f, ln, name) in undocumented([path]):
        out = []
        i = ln - 1
        while i < len(lines) and i < ln - 1 + 25:
            out.append(lines[i])
            if re.search(r':=|where\s*$', lines[i]):
                break
            i += 1
        files = idx.get(name, set())
        print(f'### {path}:{ln} {name}  [files: {len(files)}]')
        print('\n'.join(out))
        print()
