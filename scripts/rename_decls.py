#!/usr/bin/env python3
"""Rename declarations by topic, leaving a deprecated alias for every public name.

Input: a TSV with `old_short_name <TAB> new_short_name` and, optionally, a
declaration site and a substitution scope
(`old <TAB> new <TAB> site_file <TAB> scope_prefix[,scope_prefix...]`; blank
lines and lines starting with `#` are ignored).  For each row the tool

* checks that `old_short_name` is declared exactly once in the tree, or, when a
  site file is given, exactly once in that file (which is how a name that two
  modules declare independently is renamed in one of them only);
* restricts the rewrite to the files under the scope prefixes, if given;
* rewrites every whole-word occurrence of the old name in every `.lean` file of
  the project (source and prose alike);
* appends `old_fqn <TAB> new_fqn <TAB> file <TAB> public|private` to
  `docs/history/phase3_renames.tsv`, and retargets the earlier rows that point
  at the renamed name, so the table stays chain-free; a name that the base
  revision declares also keeps a row of its own, so the table stays complete;
* with `--inline-alias`, inserts

      @[deprecated (since := "2026-09-08")]
      alias old_short_name := new_short_name

  immediately after a renamed public declaration.  The aliases normally live in
  `Deprecated/` instead: run `scripts/gen_deprecated.py` after the rename and
  the public rows of the table become aliases there.

Run from the repository root:  `python3 scripts/rename_decls.py renames.tsv`.
"""
from __future__ import annotations

import os
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from base_decls import base_fqns  # noqa: E402

SINCE = '2026-09-08'
# The revision this cleanup phase started from; see `scripts/base_decls.py`.
BASE_REV = os.environ.get('PHASE_BASE_REV', 'f40bb33')
LEAN_DIRS = ['KolmogorovMathlib', 'KolmogorovCounterexamples', 'scripts']
RENAME_LOG = pathlib.Path('docs/history/phase3_renames.tsv')

DECL_KINDS = (
    'theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'instance',
    'inductive',
)
# an attribute list written on the declaration line itself, `@[simp] theorem f`
ATTR_PREFIX = r'(?:@\[[^\]]*\]\s+)*'
# a line that begins a new top-level command
CMD_START = re.compile(
    r'^(/--|/-!|/-|--|@\[|attribute|open |section|namespace|end |variable|'
    r'private |protected |noncomputable |partial |unsafe |'
    + '|'.join(k + ' ' for k in DECL_KINDS) + r'|set_option|alias |example|'
    r'deriving|universe|local |scoped |initialize|macro|syntax|notation|'
    r'declare_syntax_cat|elab|#|omit |/-\*)')


def lean_files() -> list[pathlib.Path]:
    out: list[pathlib.Path] = []
    for d in LEAN_DIRS:
        out += sorted(pathlib.Path(d).rglob('*.lean'))
    out += [pathlib.Path('KolmogorovMathlib.lean'),
            pathlib.Path('KolmogorovCounterexamples.lean')]
    return [p for p in out if p.exists()]


def word(name: str) -> re.Pattern[str]:
    return re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")


_TEXT_CACHE: dict[pathlib.Path, list[str]] = {}


def lines_of(p: pathlib.Path) -> list[str]:
    if p not in _TEXT_CACHE:
        _TEXT_CACHE[p] = p.read_text().split('\n')
    return _TEXT_CACHE[p]


def find_decl(files, name):
    """Return (path, line index, is_private, namespace) of the declaration."""
    pat = re.compile(
        r'^' + ATTR_PREFIX +
        r'(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|'
        r'unsafe\s+)*)(?:' + '|'.join(DECL_KINDS) + r')\s+' +
        re.escape(name) + r"(?![\w'.])")
    hits = []
    for p in files:
        ns: list[str] = []
        lines = lines_of(p)
        for i, line in enumerate(lines):
            if line.startswith('namespace '):
                ns.append(line.split()[1])
            elif line.startswith('end ') and ns and line.split()[1] == ns[-1]:
                ns.pop()
            m = pat.match(line)
            if m:
                hits.append((p, i, 'private' in m.group('mods'), list(ns)))
    return hits


def decl_end(lines: list[str], start: int) -> int:
    """Index of the first line after the declaration beginning at `start`."""
    i = start + 1
    while i < len(lines):
        line = lines[i]
        if line and not line[0].isspace() and CMD_START.match(line):
            break
        i += 1
    while i > start + 1 and lines[i - 1].strip() == '':
        i -= 1
    return i


def main(argv: list[str]) -> int:
    argv = list(argv)
    inline_alias = '--inline-alias' in argv
    argv = [a for a in argv if a != '--inline-alias']
    table = []
    for raw in pathlib.Path(argv[1]).read_text().split('\n'):
        raw = raw.strip()
        if not raw or raw.startswith('#'):
            continue
        cells = raw.split('\t')
        old, new = cells[0], cells[1]
        site = cells[2] if len(cells) > 2 and cells[2] else None
        scope = ([c for c in cells[3].split(',') if c]
                 if len(cells) > 3 and cells[3] else None)
        table.append((old, new, site, scope))

    files = lean_files()
    plans = []
    for old, new, site, scope in table:
        hits = find_decl(files, old)
        if site:
            hits = [h for h in hits if str(h[0]) == site]
        if len(hits) != 1:
            print(f'SKIP {old}: {len(hits)} declaration sites', file=sys.stderr)
            continue
        if find_decl(files, new):
            print(f'SKIP {old}: target name {new} already exists',
                  file=sys.stderr)
            continue
        plans.append((old, new, hits[0], scope))

    # 1. textual rename, over the whole tree or over the scope of the row
    subs = [(word(old), new, scope) for old, new, _, scope in plans]
    for p in files:
        s = original = p.read_text()
        for pat, new, scope in subs:
            if scope and not any(str(p).startswith(c) for c in scope):
                continue
            s = pat.sub(new, s)
        if s != original:
            p.write_text(s)

    # 2. deprecated aliases for public names, in reverse line order per file
    by_file: dict[pathlib.Path, list] = {}
    for old, new, (p, line, priv, ns), _ in plans:
        by_file.setdefault(p, []).append((line, old, new, priv, ns))
    log_rows = []
    for p, entries in by_file.items():
        lines = p.read_text().split('\n')
        for line, old, new, priv, ns in sorted(entries, reverse=True):
            if inline_alias and not priv:
                end = decl_end(lines, line)
                lines[end:end] = ['', f'@[deprecated (since := "{SINCE}")]',
                                  f'alias {old} := {new}']
            log_rows.append(('.'.join(ns + [old]), '.'.join(ns + [new]),
                             str(p), 'private' if priv else 'public'))
        p.write_text('\n'.join(lines))

    # 3. the table stays chain-free and complete: an earlier row that points at
    #    a name renamed here is retargeted, and a renamed name that the base
    #    revision declares keeps a row of its own even so.
    retarget = {old: new for old, new, _, _ in log_rows}
    rows = [line.split('\t') for line in
            RENAME_LOG.read_text().split('\n') if line.strip()] \
        if RENAME_LOG.exists() else []
    used = set()
    for row in rows:
        if row[1] in retarget:
            used.add(row[1])
            row[1] = retarget[row[1]]
    base = base_fqns(BASE_REV)
    fresh = [r for r in log_rows if r[0] not in used or r[0] in base]

    RENAME_LOG.parent.mkdir(parents=True, exist_ok=True)
    RENAME_LOG.write_text(
        '\n'.join('\t'.join(r) for r in rows + [list(r) for r in
                                                sorted(fresh)]) + '\n')
    print(f'renamed {len(plans)} declarations: {len(fresh)} new rows, '
          f'{len(used)} retargeted rows')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
