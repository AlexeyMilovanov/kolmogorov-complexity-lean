#!/usr/bin/env python3
"""Fully qualified declaration names of a git revision, indexed by name only.

The rename table must stay both chain-free *and* complete: every public fully
qualified name that exists in the revision a cleanup phase started from and no
longer exists afterwards needs a row of its own, even when it was itself the
target of an earlier row.  Deciding that needs the set of names the base
revision declares, and it has to be independent of the *file* a declaration
lived in, because a module move changes the path (that is exactly how phase 4
lost fourteen rows).

Usage as a library:

    from base_decls import base_fqns
    if name in base_fqns('f40bb33'): ...
"""
from __future__ import annotations

import re
import subprocess
import sys
from functools import lru_cache
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s+)*'
    r'(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+'
    r"([^\s({\[:]+)")


@lru_cache(maxsize=None)
def base_fqns(rev: str) -> frozenset[str]:
    """Every fully qualified declaration name of the tree at `rev`."""
    listing = subprocess.run(['git', 'ls-tree', '-r', '--name-only', rev],
                             cwd=REPO, check=True, capture_output=True,
                             text=True).stdout.split('\n')
    out: set[str] = set()
    for rel in listing:
        if not rel.endswith('.lean'):
            continue
        text = subprocess.run(['git', 'show', f'{rev}:{rel}'], cwd=REPO,
                              check=True, capture_output=True,
                              text=True).stdout
        ns: list[str] = []
        for line in text.split('\n'):
            if line.startswith('namespace '):
                ns.append(line.split()[1])
            elif line.startswith('end ') and ns and line.split()[1] == ns[-1]:
                ns.pop()
            m = DECL_RE.match(line)
            if m:
                out.add('.'.join(ns + [m.group(1)]))
    return frozenset(out)


if __name__ == '__main__':
    rev = sys.argv[1] if len(sys.argv) > 1 else 'HEAD'
    print(len(base_fqns(rev)))
