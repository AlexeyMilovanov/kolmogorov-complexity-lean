#!/usr/bin/env python3
"""Inventory of declarations in the project's Lean libraries.

Emits one TSV row per declaration: kind, visibility, name, file, line.
Used by the naming and docstring audits.
"""
import re, sys, pathlib

KIND = re.compile(
    r'^(?:@\[[^\]]*\]\s+)*(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)'
    r'(?P<kind>theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+'
    r'(?P<name>[^\s({\[:]+)')

def scan(root):
    out = []
    for p in sorted(pathlib.Path(root).rglob('*.lean')):
        ns = []
        prev_doc = False
        for i, line in enumerate(p.read_text().split('\n'), 1):
            if line.startswith('namespace '):
                ns.append(line.split()[1])
            elif line.startswith('end ') and ns and line.split()[1] == ns[-1]:
                ns.pop()
            m = KIND.match(line)
            if m:
                out.append((m.group('kind'),
                            'private' if 'private' in m.group('mods') else 'public',
                            '.'.join(ns + [m.group('name')]),
                            m.group('name'), str(p), i))
    return out

if __name__ == '__main__':
    for row in scan(sys.argv[1] if len(sys.argv) > 1 else 'KolmogorovMathlib'):
        print('\t'.join(map(str, row)))
