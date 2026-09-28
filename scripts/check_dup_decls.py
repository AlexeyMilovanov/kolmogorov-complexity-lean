#!/usr/bin/env python3
"""Report fully qualified declaration names declared in more than one module.

Flattening a namespace can make two declarations collide; the collision only
shows up in the build when both modules are imported together, so it is worth
detecting directly.  Private declarations are reported too: two `private`
declarations of the same name are harmless, so they are marked as such.

Usage:  python3 scripts/check_dup_decls.py [ROOT ...]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s+)*'
    r'(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|'
    r'unsafe\s+)*)'
    r'(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+'
    r"(?P<name>[^\s({\[:]+)")


def main(argv: list[str]) -> int:
    roots = argv[1:] or ['KolmogorovMathlib', 'KolmogorovCounterexamples']
    seen: dict[str, list[tuple[str, bool]]] = {}
    for root in roots:
        for path in sorted((REPO / root).rglob('*.lean')):
            if 'Deprecated' in path.parts:
                continue
            ns: list[str] = []
            for line in path.read_text().split('\n'):
                if line.startswith('namespace '):
                    ns.append(line.split()[1])
                elif line.startswith('end ') and ns and line.split()[1] == ns[-1]:
                    ns.pop()
                m = DECL_RE.match(line)
                if m:
                    fqn = '.'.join(ns + [m.group('name')])
                    seen.setdefault(fqn, []).append(
                        (str(path.relative_to(REPO)),
                         'private' in m.group('mods')))
    bad = 0
    for fqn, sites in sorted(seen.items()):
        if len(sites) < 2:
            continue
        if all(priv for _, priv in sites):
            continue
        bad += 1
        print(fqn)
        for where, priv in sites:
            print(f'    {"private " if priv else ""}{where}')
    print(f'{bad} clashing names')
    return 1 if bad else 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
