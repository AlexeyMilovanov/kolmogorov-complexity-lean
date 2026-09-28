#!/usr/bin/env python3
"""Flag mechanical proof cuts in `KolmogorovMathlib/` and `KolmogorovCounterexamples/`.

Four independent quality audits agreed on what a *mechanical* cut looks like: a
lemma that is not a fact one would state, but a slice of one parent proof whose
context was hoisted into binders.  This checker recognises the recurring
shapes by pure text analysis (no Lean, no build) and fails when a finding is
not listed in `docs/history/cut_quality_allow.tsv`.

Codes:

* `RFL-BINDER`      a `Prop` hypothesis that *every* call site discharges
                    with nothing -- `rfl` / `le_rfl` / `by rfl` / `by omega` /
                    `by simp` / `by decide` / `by norm_num`, or an equation the
                    caller itself produced with `set … with h` -- whether or
                    not the constant it constrains reaches the conclusion; two
                    such binders, or one in a statement that already carries
                    eight explicit arguments;
* `SINGLE-USE-TAIL` a lemma with eight or more explicit binders and a single
                    call site anywhere in the library, whose conclusion, after
                    the call's own arguments are substituted for the binders
                    and the caller's `set` abbreviations expanded, is the text
                    of the `have` the caller writes for it, unless the caller
                    proves every one of its hypotheses on the spot with a
                    `by …` block or a term of its own;
* `WRAPPER`         a body that is one `exact`, one `simpa … using`, or a term
                    application of a single other declaration of the same shape,
                    unless the two names are a Mathlib general/special pair
                    (`foo` beside `foo'`, `foo_aux` or `foo_of_<hypothesis>`),
                    or the wrapper supplies an argument of its own rather than
                    merely re-indexing the binders;
* `LONG-STATEMENT`  a statement over 15 lines or with over 8 explicit
                    hypothesis binders;
* `THEOREM-HYP`     a hypothesis that is itself a whole theorem (a `∀ … → …`
                    binder, or a binder whose type is another declaration's
                    statement);
* `SIBLING-PAIR`    two lemmas with the same single caller whose statements
                    differ in exactly one identifier; two different projections
                    of the same argument are two facts, not a pair;
* `PADDED-BOUND`    an inequality that carries the same three or more summands
                    on both sides: the content is the bound without them;
* `BINDER-RESTATE`  a body whose first step restates one of its own hypotheses
                    verbatim.

The gate fails on a finding that the allow-list does not list, and on an
allow row that no longer corresponds to a finding: a licence nobody uses is a
licence for the next regression under the same name.

Usage:
    python3 scripts/cut_quality.py [--root DIR] [--allow FILE] [--code CODE]
                                   [--no-allow] [ROOT ...]
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

DEFAULT_ROOTS = ('KolmogorovMathlib', 'KolmogorovCounterexamples')
ALLOW_FILE = 'docs/history/cut_quality_allow.tsv'

KEYWORDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure',
            'inductive', 'class', 'opaque', 'example', 'macro', 'notation',
            'syntax', 'elab', 'mutual', 'initialize', 'alias')
MODIFIERS = ('private', 'protected', 'nonrec', 'noncomputable', 'partial',
             'scoped', 'unsafe')
DECL_RE = re.compile(r'^(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*(?:' +
                     '|'.join(KEYWORDS) + r')\b')
NAME_RE = re.compile(r'^(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*(' +
                     '|'.join(KEYWORDS) + r')\s+([^\s({\[:]+)')
CONTEXT_RE = re.compile(r'^(open|variable|local|attribute|universe|set_option'
                        r'|namespace|end|section|omit|include|import|/-!|/--|@\[)')

OPENERS = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
CLOSERS = {v: k for k, v in OPENERS.items()}

PROP_MARKS = ('=', '≤', '<', '≥', '>', '∈', '⊆', '∀', '∃', '∧', '∨', '→', '¬',
              '≠', '↔', '∣', '≡', '⊂', '∉')

# The arguments that close a hypothesis without using anything.  They say
# the hypothesis was empty at the call site, not that the caller knew a fact.
CONTENTLESS_RE = re.compile(
    r"rfl|le_rfl|(?:Nat\.)?le_refl(?:\s+\S+)?"
    r"|by\s+(?:rfl|omega|decide|norm_num|simp(?:\s+only)?)")


def ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?."


def tokens(text: str) -> list[str]:
    """Split Lean source text into identifier and single-symbol tokens."""
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ident_char(ch):
            j = i
            while j < n and ident_char(text[j]):
                j += 1
            out.append(text[i:j])
            i = j
        else:
            out.append(ch)
            i += 1
    return out


def norm(text: str) -> str:
    """Whitespace-normalised token text."""
    return ' '.join(tokens(text))


def mask_comments(text: str) -> str:
    """Blank out comments and string literals, preserving every offset."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and two == '--':
            while i < n and text[i] != '\n':
                out[i] = ' '
                i += 1
            continue
        if two == '/-':
            depth += 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if two == '-/' and depth:
            depth -= 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if depth:
            if text[i] != '\n':
                out[i] = ' '
            i += 1
            continue
        if text[i] == '"':
            out[i] = ' '
            i += 1
            while i < n and text[i] != '"':
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
            if i < n:
                out[i] = ' '
                i += 1
            continue
        i += 1
    return ''.join(out)


@dataclass
class Binder:
    names: list[str]
    type_text: str
    kind: str            # 'explicit' | 'implicit' | 'inst' | 'strict'
    positions: list[int]  # explicit positions, empty when not explicit


@dataclass
class Decl:
    name: str
    fqn: str
    kind: str
    file: str
    line: int
    start: int           # char offset of the keyword
    end: int             # char offset just past the declaration
    stmt: str
    body: str
    binders: list[Binder] = field(default_factory=list)
    concl: str = ''
    stmt_lines: int = 0
    doc: str = ''
    sites: list[tuple[str, int]] = field(default_factory=list)  # (file, offset)

    @property
    def loc(self) -> str:
        return f'{self.file}:{self.line}'

    def explicit_count(self) -> int:
        return sum(len(b.positions) for b in self.binders)


def split_top(text: str) -> tuple[str, str]:
    """Split a declaration into (statement, body) at the top-level `:=`."""
    depth, i, n = 0, 0, len(text)
    while i < n:
        ch = text[i]
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
        elif depth == 0 and text[i:i + 3] == 'let' and (
                i == 0 or not ident_char(text[i - 1])) and (
                i + 3 >= n or not ident_char(text[i + 3])):
            # A `let` binder inside a *statement* owns the `:=` that follows
            # it; the declaration does not end there.
            j = text.find(':=', i)
            if j < 0:
                return text, ''
            i = j + 2
            continue
        elif depth == 0 and text[i:i + 2] == ':=':
            return text[:i], text[i + 2:]
        elif depth == 0 and text[i:i + 5] == 'where' and (
                i + 5 >= n or not ident_char(text[i + 5])):
            return text[:i], text[i + 5:]
        i += 1
    return text, ''


def parse_binders(stmt: str) -> tuple[list[Binder], str]:
    """Parse the binder groups of a statement; return them and the conclusion."""
    m = NAME_RE.match(stmt)
    i = m.end() if m else 0
    binders: list[Binder] = []
    pos = 0
    n = len(stmt)
    while i < n:
        ch = stmt[i]
        if ch.isspace():
            i += 1
            continue
        if ch == ':' and stmt[i:i + 2] != ':=':
            return binders, stmt[i + 1:]
        if ch in OPENERS:
            close = OPENERS[ch]
            depth, j = 0, i
            while j < n:
                if stmt[j] in OPENERS:
                    depth += 1
                elif stmt[j] in CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            group = stmt[i + 1:j]
            kind = {'(': 'explicit', '{': 'implicit', '[': 'inst',
                    '⦃': 'strict'}.get(ch, 'explicit')
            names, tp = group, ''
            depth2, k = 0, 0
            while k < len(group):
                if group[k] in OPENERS:
                    depth2 += 1
                elif group[k] in CLOSERS:
                    depth2 -= 1
                elif depth2 == 0 and group[k] == ':' and group[k:k + 2] != ':=':
                    names, tp = group[:k], group[k + 1:]
                    break
                k += 1
            name_list = names.split()
            spots: list[int] = []
            if kind == 'explicit':
                spots = list(range(pos, pos + len(name_list)))
                pos += len(name_list)
            binders.append(Binder(name_list, tp.strip(), kind, spots))
            i = j + 1
            continue
        # anything else (a `variable`-style leftover): give up on binders
        break
    return binders, ''


def parse_file(path: Path, rel: str) -> list[Decl]:
    raw = path.read_text()
    masked = mask_comments(raw)
    lines = masked.split('\n')
    offsets, acc = [], 0
    for line in lines:
        offsets.append(acc)
        acc += len(line) + 1
    starts = [i for i, l in enumerate(lines) if DECL_RE.match(l)]
    tops = [i for i, l in enumerate(lines)
            if DECL_RE.match(l) or CONTEXT_RE.match(l)]
    ns: list[str] = []
    ns_at: dict[int, list[str]] = {}
    for i, line in enumerate(lines):
        ns_at[i] = list(ns)
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            ns.extend(m.group(1).split('.'))
        elif re.match(r'^end\s+(\S+)', line):
            name = re.match(r'^end\s+(\S+)', line).group(1)
            for part in reversed(name.split('.')):
                if ns and ns[-1] == part:
                    ns.pop()
    decls: list[Decl] = []
    for i in starts:
        nxt = next((j for j in tops if j > i), len(lines))
        while nxt - 1 > i and lines[nxt - 1].strip() == '':
            nxt -= 1
        m = NAME_RE.match(lines[i])
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if kind not in ('theorem', 'lemma', 'def', 'abbrev', 'instance',
                        'structure', 'inductive', 'class', 'abbrev'):
            continue
        text = '\n'.join(lines[i:nxt])
        stmt, body = split_top(text)
        binders, concl = parse_binders(stmt)
        doc = ''
        k = i - 1
        while k >= 0 and (lines[k].strip().startswith('@[') or
                          not lines[k].strip()):
            k -= 1
        if k >= 0 and raw.split('\n')[k].rstrip().endswith('-/'):
            j = k
            while j >= 0 and '/--' not in raw.split('\n')[j]:
                j -= 1
            if j >= 0:
                doc = '\n'.join(raw.split('\n')[j:k + 1])
        prefix = '.'.join(ns_at[i])
        fqn = f'{prefix}.{name}' if prefix else name
        end_off = offsets[nxt - 1] + len(lines[nxt - 1]) if nxt else len(masked)
        decls.append(Decl(name=name, fqn=fqn, kind=kind, file=rel, line=i + 1,
                          start=offsets[i], end=end_off, stmt=stmt, body=body,
                          binders=binders, concl=concl.strip(),
                          stmt_lines=stmt.count('\n') + 1, doc=doc))
    return decls


# --------------------------------------------------------------------------
# call sites


def read_arg(text: str, i: int, base_indent: int) -> tuple[str, int] | None:
    """Read one application argument of a call starting at offset `i`."""
    n = len(text)
    while i < n and text[i] in ' \t\n':
        if text[i] == '\n':
            j = i + 1
            k = j
            while k < n and text[k] == ' ':
                k += 1
            if k >= n or text[k] == '\n' or (k - j) <= base_indent:
                return None
            i = k
            continue
        i += 1
    if i >= n:
        return None
    ch = text[i]
    if ch in ')]}⟩,;':
        return None
    if ch in OPENERS:
        depth, j = 0, i
        while j < n:
            if text[j] in OPENERS:
                depth += 1
            elif text[j] in CLOSERS:
                depth -= 1
                if depth == 0:
                    break
            j += 1
        return text[i:j + 1], j + 1
    j = i
    while j < n and ident_char(text[j]):
        j += 1
    if j == i:
        return None
    tok = text[i:j]
    if tok in ('with', 'then', 'else', 'do', 'from', 'at', 'using', 'by',
               'have', 'exact', 'refine', 'calc', 'fun', 'let', 'if', 'match'):
        return None
    if tok.startswith('.'):
        return None
    return tok, j


def call_args(text: str, pos: int) -> tuple[list[str], dict[str, str]]:
    """Positional and named arguments of the application at offset `pos`."""
    line_start = text.rfind('\n', 0, pos) + 1
    base_indent = len(text[line_start:]) - len(text[line_start:].lstrip(' '))
    i = pos
    args: list[str] = []
    named: dict[str, str] = {}
    while True:
        got = read_arg(text, i, base_indent)
        if got is None:
            break
        arg, i = got
        inner = arg[1:-1].strip() if arg[:1] in OPENERS else arg
        m = re.match(r"^([A-Za-z_][^\s:=]*)\s*:=\s*(.*)$", inner, re.S)
        if arg.startswith('(') and m:
            named[m.group(1)] = m.group(2).strip()
        else:
            args.append(inner if arg.startswith('(') else arg)
        if len(args) > 40:
            break
    return args, named


def word_sites(masked: str, name: str) -> list[int]:
    pat = re.compile(r'(?<![A-Za-z0-9_.\'])' + re.escape(name) +
                     r'(?![A-Za-z0-9_.\'])')
    return [m.start() for m in pat.finditer(masked)]


# --------------------------------------------------------------------------
# caller context


def enclosing_decl(decls: list[Decl], off: int) -> Decl | None:
    for d in decls:
        if d.start <= off < d.end:
            return d
    return None


SET_RE = re.compile(
    r'^([ \t]*)(?:set|let)[ \t]+([A-Za-z_][A-Za-z0-9_\'₀-₉]*)[ \t]*'
    r'(?::[^:=\n]*)?:=', re.M)
WITH_RE = re.compile(r"\bwith[ \t]+([A-Za-z_][A-Za-z0-9_'₀-₉]*)[ \t]*$")


def set_bindings(text: str) -> tuple[dict[str, str], set[str]]:
    """`set`/`let` abbreviations of a proof: x ↦ e, and the `with h` names.

    A `set` tactic may span several lines; its value, and the `with h` that
    names the equation, run to the end of the tactic, which is the last line
    indented deeper than the `set` keyword itself.
    """
    subst: dict[str, str] = {}
    eqs: set[str] = set()
    lines = text.split('\n')
    for m in SET_RE.finditer(text):
        indent = len(m.group(1).expandtabs(2))
        row = text.count('\n', 0, m.start())
        eol = text.find('\n', m.end())
        chunk = [text[m.end():eol if eol >= 0 else len(text)]]
        k = row + 1
        while k < len(lines) and lines[k].strip():
            width = len(lines[k]) - len(lines[k].lstrip(' '))
            if width <= indent:
                break
            chunk.append(lines[k])
            k += 1
        value = ' '.join(part.strip() for part in chunk).strip()
        w = WITH_RE.search(value)
        if w:
            eqs.add(w.group(1))
            value = value[:w.start()].strip()
        subst[m.group(2)] = value
    return subst, eqs


def substitute(text: str, mapping: dict[str, str]) -> str:
    """Replace each mapped name by its value, also under a projection."""
    def expand(rep: str) -> str:
        return rep if rep.startswith('(') else f'( {norm(rep)} )'

    out = []
    for tok in tokens(text):
        if tok in mapping and norm(mapping[tok]) == tok:
            out.append(tok)
        elif tok in mapping:
            out.append(expand(mapping[tok]))
        elif '.' in tok and tok.split('.')[0] in mapping and \
                norm(mapping[tok.split('.')[0]]) == tok.split('.')[0]:
            out.append(tok)
        elif '.' in tok and tok.split('.')[0] in mapping:
            head, rest = tok.split('.', 1)
            out.append(f'{expand(mapping[head])} .{rest}')
        else:
            out.append(tok)
    return ' '.join(out)


def have_before(text: str, pos: int) -> tuple[str, str] | None:
    """The `have name : type` whose block contains offset `pos`."""
    idx = text.rfind('have ', 0, pos)
    while idx >= 0:
        chunk = text[idx:pos]
        stmt, _ = split_top(chunk)
        m = re.match(r'^have\s+([^:\s]*)\s*:(.*)$', stmt, re.S)
        if m and ':=' in chunk:
            return m.group(1).strip(), m.group(2).strip()
        idx = text.rfind('have ', 0, idx)
    return None


# --------------------------------------------------------------------------
# the checks


def is_hypothesis(binder: Binder) -> bool:
    tp = binder.type_text
    if not tp:
        return False
    return (any(mark in tp for mark in PROP_MARKS) or
            all(nm.startswith('h') for nm in binder.names))


def top_split(tks: list[str], syms: tuple[str, ...]) -> tuple[int, str] | None:
    """Position and symbol of the first top-level occurrence of `syms`."""
    depth = 0
    for i, t in enumerate(tks):
        if t in OPENERS:
            depth += 1
        elif t in CLOSERS:
            depth -= 1
        elif depth == 0 and t in syms:
            return i, t
    return None


def proves_inline(arg: str) -> bool:
    """Whether a call site *proves* the hypothesis it is filling there.

    A bare identifier is a fact the caller already had -- its own binder, its
    own `have`, a field of one of them -- under whatever name it chose; a
    `by …` block, or a term the caller assembles, is a proof it had to write.
    """
    return re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'₀-₉.!?]*",
                        norm(arg)) is None


def summands(tks: list[str]) -> list[str]:
    """Flatten a top-level `+`-sum, descending into parenthesised groups."""
    parts, depth, cur = [], 0, []
    for t in tks:
        if t in OPENERS:
            depth += 1
            cur.append(t)
        elif t in CLOSERS:
            depth -= 1
            cur.append(t)
        elif depth == 0 and t == '+':
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    parts.append(cur)
    out = []
    for p in parts:
        stripped = False
        while len(p) >= 2 and p[0] == '(' and p[-1] == ')':
            inner = p[1:-1]
            depth = 0
            ok = True
            for t in inner:
                depth += (t in OPENERS) - (t in CLOSERS)
                if depth < 0:
                    ok = False
                    break
            if not ok or depth != 0:
                break
            p, stripped = inner, True
        if stripped and top_split(p, ('+',)) is not None:
            out += summands(p)
        elif p:
            out.append(' '.join(p))
    return out


def match_pattern(pat: list[str], txt: list[str], variables: set[str],
                  budget: int = 60000) -> dict[str, str] | None:
    """Match `pat` against `txt`, letting each variable stand for a term.

    A variable matches a non-empty, bracket-balanced span of at most twelve
    tokens, consistently at every occurrence.  Returns the binding or None.
    """
    if len(pat) > 300 or len(txt) > 300:
        return None
    steps = [budget]

    def balanced(span: list[str]) -> bool:
        depth = 0
        for t in span:
            depth += (t in OPENERS) - (t in CLOSERS)
            if depth < 0:
                return False
        return depth == 0

    def go(i: int, j: int, env: dict[str, str]) -> dict[str, str] | None:
        steps[0] -= 1
        if steps[0] <= 0:
            return None
        if i == len(pat):
            return env if j == len(txt) else None
        tok = pat[i]
        if tok in variables:
            if tok in env:
                span = env[tok].split(' ')
                if txt[j:j + len(span)] == span:
                    return go(i + 1, j + len(span), env)
                return None
            for k in range(1, 13):
                span = txt[j:j + k]
                if len(span) < k:
                    break
                if not balanced(span):
                    continue
                res = go(i + 1, j + k, {**env, tok: ' '.join(span)})
                if res is not None:
                    return res
            return None
        if j < len(txt) and txt[j] == tok:
            return go(i + 1, j + 1, env)
        return None

    return go(0, 0, {})


def general_special_pair(a: str, b: str) -> bool:
    """Whether `a` and `b` are a Mathlib general/special naming pair.

    Mathlib states the general lemma as `foo'` or as `foo_of_<hypothesis>` and
    keeps the convenient special case under the bare name `foo`, whose body is
    then one application of the sibling.  That is the naming convention, not a
    mechanical cut: the two statements differ in a hypothesis, and both names
    belong to the API.
    """
    for x, y in ((a, b), (b, a)):
        if y == x + "'":
            return True
        if y.startswith(x + '_of_') and len(y) > len(x) + len('_of_'):
            return True
    return False


def head_shape(concl: str) -> str:
    tks = tokens(concl)
    depth = 0
    for i, t in enumerate(tks):
        if t in OPENERS:
            depth += 1
        elif t in CLOSERS:
            depth -= 1
        elif depth == 0 and t in ('=', '≤', '<', '≥', '>', '∈', '⊆', '≠', '↔'):
            return t
    return tks[0] if tks else ''


@dataclass
class Finding:
    code: str
    fqn: str
    loc: str
    detail: str

    def line(self) -> str:
        return f'{self.code}\t{self.fqn}\t{self.loc}\t{self.detail}'


class Tree:
    def __init__(self, root: Path, roots: tuple[str, ...]):
        self.root = root
        self.files: dict[str, str] = {}
        self.decls: list[Decl] = []
        self.by_file: dict[str, list[Decl]] = defaultdict(list)
        for r in roots:
            base = root / r
            paths = sorted(base.rglob('*.lean')) if base.is_dir() else []
            extra = root / f'{r}.lean'
            if extra.is_file():
                paths.append(extra)
            for p in paths:
                if 'Deprecated' in p.parts:
                    continue
                rel = str(p.relative_to(root))
                self.files[rel] = mask_comments(p.read_text())
                for d in parse_file(p, rel):
                    self.decls.append(d)
                    self.by_file[rel].append(d)
        self.by_name: dict[str, list[Decl]] = defaultdict(list)
        for d in self.decls:
            self.by_name[d.name].append(d)
        self._sets: dict[tuple[str, int], tuple[dict[str, str], set[str]]] = {}
        self._index_sites()

    def set_bindings_of(self, rel: str,
                        caller: Decl) -> tuple[dict[str, str], set[str]]:
        """The `set`/`let` abbreviations of one caller's proof, cached."""
        key = (rel, caller.start)
        got = self._sets.get(key)
        if got is None:
            got = set_bindings(self.files[rel][caller.start:caller.end])
            self._sets[key] = got
        return got

    def _index_sites(self) -> None:
        names = set(self.by_name)
        occ: dict[str, list[tuple[str, int]]] = defaultdict(list)
        pat = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉!?]*")
        for rel, text in self.files.items():
            for m in pat.finditer(text):
                tok = m.group(0)
                if tok in names:
                    # skip a match that is part of a dotted name
                    if m.start() and text[m.start() - 1] in "._'":
                        continue
                    if m.end() < len(text) and text[m.end()] in "._'":
                        continue
                    occ[tok].append((rel, m.start()))
        for d in self.decls:
            d.sites = [(f, o) for (f, o) in occ.get(d.name, [])
                       if not (f == d.file and d.start <= o < d.end)]

    # -- individual checks ------------------------------------------------

    def is_local_cut(self, d: Decl) -> bool:
        """A declaration that only one module consumes: a cut, not an API."""
        return (1 <= len(d.sites) <= 2 and
                all(f == d.file for f, _ in d.sites))

    def check_rfl_binder(self, d: Decl) -> list[Finding]:
        # A lemma with three or more consumers is an interface whose
        # reflexive binder happens to be reflexive here; the pattern the
        # audits describe is a cut serving one or two call sites.
        if not d.sites or len(d.sites) > 2:
            return []
        out = []
        for b in d.binders:
            if b.kind != 'explicit' or len(b.names) != 1 or \
                    not is_hypothesis(b):
                continue
            hname = b.names[0]
            spot = b.positions[0]
            how: list[str] = []
            ok = True
            for rel, off in d.sites:
                text = self.files[rel]
                args, named = call_args(text, off + len(d.name))
                arg = named.get(hname)
                if arg is None:
                    if spot >= len(args):
                        ok = False
                        break
                    arg = args[spot]
                verdict = self._discharge(arg, rel, off)
                if verdict is None:
                    ok = False
                    break
                how.append(verdict)
            if ok and how:
                out.append(f'({hname} : {norm(b.type_text)}) := '
                           + ' / '.join(sorted(set(how))))
        # One binder a caller happens to close by `rfl` is bookkeeping; the
        # cut is mechanical when two of them are, or when one sits in a
        # signature that already carries eight explicit arguments.  All of a
        # declaration's empty binders are one finding.
        if len(out) >= 2 or (len(out) == 1 and d.explicit_count() >= 8):
            return [Finding('RFL-BINDER', d.fqn, d.loc,
                            f'{len(out)} binder(s) carry no content at any '
                            f'of the {len(d.sites)} call site(s): '
                            + '; '.join(out))]
        return []

    def _discharge(self, arg: str, rel: str, off: int) -> str | None:
        """How a call site fills a binder, when it fills it with nothing.

        Either the argument is one of the closers that say the hypothesis was
        empty -- a reflexivity proof, or a decision procedure the binder's own
        statement settles -- or it is an equation the caller itself produced
        with `set … with h`, i.e. the caller handing back its own
        abbreviation.  What the binder constrains, and whether that constant
        reaches the conclusion, does not enter: an argument that proves
        nothing carries nothing.
        """
        a = norm(arg)
        if CONTENTLESS_RE.fullmatch(a):
            return a
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*", a):
            caller = enclosing_decl(self.by_file[rel], off)
            if caller is not None:
                _, eqs = self.set_bindings_of(rel, caller)
                if a in eqs:
                    return f'`set … with {a}`'
        return None

    def check_single_use_tail(self, d: Decl) -> list[Finding]:
        """One call site, and the conclusion is the caller's own next `have`.

        Restricted to statements with at least eight explicit binders: a
        short single-use lemma applied in a typed `have` is an ordinary step,
        while one that had to hoist eight or more of the parent's parameters to
        say the same sentence is the mechanical cut the audits describe.  The
        caller is looked for in the whole library: a tail is a tail wherever
        the parent happens to be written.
        """
        if len(d.sites) != 1 or d.explicit_count() < 8:
            return []
        rel, off = d.sites[0]
        text = self.files[rel]
        caller = enclosing_decl(self.by_file[rel], off)
        if caller is None or not d.concl:
            return []
        got = have_before(text[caller.start:caller.end],
                          off - caller.start)
        if got is None:
            return []
        hname, htype = got
        args, named = call_args(text, off + len(d.name))
        mapping: dict[str, str] = {}
        free: set[str] = set()
        for b in d.binders:
            if b.kind == 'explicit':
                for nm, spot in zip(b.names, b.positions):
                    if nm in named:
                        mapping[nm] = named[nm]
                    elif spot < len(args):
                        mapping[nm] = args[spot]
                    else:
                        free.add(nm)
            elif not is_hypothesis(b):
                free.update(b.names)
        # The signal is the text of the conclusion.  A lemma whose every
        # hypothesis the caller has to *prove* on the spot -- a tactic block,
        # a term it assembles -- is a lemma the caller uses; hypotheses handed
        # over as bare identifiers are the parent's own context, whatever the
        # parent calls them, and a statement with no hypotheses at all (a pure
        # specialisation of arithmetic) has no context to hand over.  How many
        # binders come back under their own names corroborates, it does not
        # decide.
        nhyp = handed = inline = 0
        for b in d.binders:
            if b.kind != 'explicit' or not is_hypothesis(b):
                continue
            for nm, spot in zip(b.names, b.positions):
                nhyp += 1
                arg = named.get(nm)
                if arg is None and spot < len(args):
                    arg = args[spot]
                if arg is None:
                    continue
                if proves_inline(arg):
                    inline += 1
                elif norm(arg) == nm:
                    handed += 1
        if nhyp and inline == nhyp:
            return []
        subst, _ = self.set_bindings_of(rel, caller)
        left = substitute(substitute(d.concl, mapping), subst)
        right = strip_leading_forall(substitute(htype, subst))
        pat = strip_parens(left).split()
        txt = strip_parens(right).split()
        if not pat or not txt:
            return []
        detail = (f'sole call site {rel}:{line_of(text, off)} is '
                  f'`have {hname} : …`, text-identical to the conclusion '
                  f'after substitution')
        if handed:
            detail += (f'; {handed}/{nhyp} hypotheses handed back under '
                       'their own names')
        if pat == txt:
            return [Finding('SINGLE-USE-TAIL', d.fqn, d.loc, detail)]
        variables = {v for v in free if v in pat}
        fixed = [t for t in pat if t not in variables]
        if variables and len(variables) <= 8 and len(fixed) >= 10 and \
                match_pattern(pat, txt, variables) is not None:
            return [Finding(
                'SINGLE-USE-TAIL', d.fqn, d.loc,
                detail + f' (implicit arguments {", ".join(sorted(variables))}'
                         ' instantiated)')]
        return []

    def check_padded_bound(self, d: Decl) -> list[Finding]:
        """An inequality padded on both sides with the caller's constants."""
        if not self.is_local_cut(d):
            return []
        tks = tokens(d.concl)
        got = top_split(tks, ('≤', '<'))
        if got is None:
            return []
        i = got[0]
        lhs, rhs = summands(tks[:i]), summands(tks[i + 1:])
        shared = sorted(set(lhs) & set(rhs))
        if len(shared) >= 3:
            return [Finding('PADDED-BOUND', d.fqn, d.loc,
                            f'{len(shared)} summands occur on both sides of '
                            f'the bound ({"; ".join(shared)[:70]}…): the '
                            'content is the inequality without them')]
        return []

    def check_binder_restate(self, d: Decl) -> list[Finding]:
        """The proof opens by restating one of its own hypotheses."""
        types = {}
        for b in d.binders:
            for nm in b.names:
                types[nm] = strip_parens(norm(b.type_text))
        for m in re.finditer(r'have\s+[^:\s]*\s*:(.*?):=\s*([A-Za-z_][\w\'₀-₉]*)'
                             r'\s*(?:\n|$)', d.body, re.S):
            tp, val = m.group(1), m.group(2).strip()
            if val in types and types[val] and \
                    strip_parens(norm(tp)) == types[val]:
                return [Finding('BINDER-RESTATE', d.fqn, d.loc,
                                f'the body restates the hypothesis `{val}` '
                                'verbatim as its first step')]
        return []

    def check_wrapper(self, d: Decl) -> list[Finding]:
        body = d.body.strip()
        # A restatement used all over the library is a convenience alias
        # with its own consumers; one or two consumers make it a cut.
        if not body or len(d.sites) > 2:
            return []
        head = None
        m = re.fullmatch(r'by\s+exact\s+(.*)', body, re.S) or \
            re.fullmatch(r'exact\s+(.*)', body, re.S)
        if m:
            head = m.group(1)
        else:
            m = re.fullmatch(r'by\s+simpa(.*?)\susing\s+(.*)', body, re.S)
            if m:
                head = m.group(2)
            elif not body.startswith('by') and '\n' not in body.strip():
                head = body
        if head is None:
            return []
        tks = tokens(head)
        if not tks or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", tks[0]):
            return []
        callee = tks[0].split('.')[-1]
        # Mathlib convention: the public lemma states the fact and its primed
        # or `_aux` sibling carries the proof.  Applying one's own sibling is
        # that convention, not a mechanical cut.
        if callee in (d.name + "'", d.name + '_aux'):
            return []
        cands = [c for c in self.by_name.get(callee, []) if c.fqn != d.fqn]
        args, named = call_args(head, len(tks[0]))
        # A wrapper that has to *supply* something -- a proof the wrapped
        # declaration demands, a term it must build -- is a specialisation
        # doing work of its own; only a pure re-indexing of the binders is
        # the restatement the audits describe.
        if named or any(len(tokens(a)) != 1 for a in args):
            return []
        for c in cands:
            if head_shape(c.concl) != head_shape(d.concl) or \
                    c.explicit_count() != d.explicit_count():
                continue
            if general_special_pair(d.name, c.name):
                continue
            mapping: dict[str, str] = {}
            for b in c.binders:
                for nm, spot in zip(b.names, b.positions):
                    if nm in named:
                        mapping[nm] = named[nm]
                    elif spot < len(args):
                        mapping[nm] = args[spot]
            inst = strip_parens(substitute(c.concl, mapping))
            if inst == strip_parens(norm(d.concl)):
                return [Finding('WRAPPER', d.fqn, d.loc,
                                f'body is one application of {c.fqn} '
                                f'({c.loc}), whose conclusion instantiates to '
                                'the same statement')]
        return []

    def check_long_statement(self, d: Decl) -> list[Finding]:
        # Only for a lemma with a single consumer: a long statement that
        # several modules use is an interface, judged elsewhere.
        if not self.is_local_cut(d) or len(d.sites) != 1:
            return []
        hyps = [b for b in d.binders if b.kind == 'explicit' and
                is_hypothesis(b)]
        nh = sum(len(b.names) for b in hyps)
        # Both thresholds together: over fifteen lines is common for a
        # statement about a run of the machine, and nine hypotheses are
        # common in an interface; a statement that is both is a signature
        # copied wholesale.
        if d.stmt_lines <= 15 or nh <= 8:
            return []
        # A long statement is a defect of *cutting* when it is long because
        # it copies its parent's signature; a long statement a proof of its
        # own needs is a statement, and the docstring gate judges it.
        shared = self.shared_binders(d)
        if len(shared) < 10:
            return []
        return [Finding('LONG-STATEMENT', d.fqn, d.loc,
                        f'statement spans {d.stmt_lines} lines with '
                        f'{nh} explicit hypothesis binders; '
                        f'{len(shared)} binders are copied from the signature '
                        f'of its only caller ({", ".join(sorted(shared))})')]

    def shared_binders(self, d: Decl) -> set[str]:
        """Binder names `d` shares with the signature of its only caller."""
        if len(d.sites) != 1:
            return set()
        rel, off = d.sites[0]
        caller = enclosing_decl(self.by_file[rel], off)
        if caller is None:
            return set()
        mine = {nm for b in d.binders for nm in b.names}
        theirs = {nm for b in caller.binders for nm in b.names}
        return mine & theirs

    def check_theorem_hyp(self, d: Decl, stmt_index: dict[str, Decl]
                          ) -> list[Finding]:
        if not self.is_local_cut(d) or len(d.sites) != 1:
            return []
        out = []
        quantified = []
        for b in d.binders:
            if b.kind not in ('explicit', 'strict'):
                continue
            tp = b.type_text.strip()
            if not tp:
                continue
            if tp.startswith('∀') and '→' in tp:
                quantified.append(b)
                continue
            key = strip_parens(norm(tp))
            other = stmt_index.get(key)
            if other is not None and other.fqn != d.fqn and len(key) > 25:
                out.append(Finding(
                    'THEOREM-HYP', d.fqn, d.loc,
                    f'({" ".join(b.names)} : …) is the statement of '
                    f'{other.fqn} ({other.loc})'))
        # One or two quantified interface hypotheses are a legitimate
        # abstraction (an interface a caller instantiates); three or more are
        # the parent's context hoisted into the signature.
        if len(quantified) >= 3:
            names = ', '.join(' '.join(b.names) for b in quantified)
            out.append(Finding(
                'THEOREM-HYP', d.fqn, d.loc,
                f'{len(quantified)} hypotheses ({names}) are quantified '
                'implications, i.e. theorems in their own right'))
        return out

    def sibling_pairs(self) -> list[Finding]:
        parents: dict[tuple[str, str], list[Decl]] = defaultdict(list)
        for d in self.decls:
            if d.kind not in ('theorem', 'lemma') or len(d.sites) != 1:
                continue
            rel, off = d.sites[0]
            caller = enclosing_decl(self.by_file[rel], off)
            if caller is not None:
                parents[(rel, caller.fqn)].append(d)
        out = []
        for (_, parent), group in sorted(parents.items()):
            group.sort(key=lambda d: (d.file, d.line))
            # A family cut by one mechanical pass is reported once, not once
            # per pair: `lower_0 … lower_7` is one finding, not twenty-eight.
            comp = {d.fqn: d.fqn for d in group}

            def root(x: str) -> str:
                while comp[x] != x:
                    x = comp[x]
                return x

            diffs: dict[str, set[str]] = defaultdict(set)
            for i, a in enumerate(group):
                for b in group[i + 1:]:
                    ta, tb = tokens(drop_name(a.stmt)), tokens(drop_name(b.stmt))
                    if len(ta) != len(tb) or len(ta) < 6:
                        continue
                    diff = [(x, y) for x, y in zip(ta, tb) if x != y]
                    if len(diff) != 1:
                        continue
                    x, y = diff[0]
                    # Two lemmas about two different named objects are two
                    # facts; the mechanical pair differs in a constant or a
                    # hypothesis name only.
                    if x.split('.')[-1] in self.by_name and \
                            y.split('.')[-1] in self.by_name:
                        continue
                    # Two *different projections of the same argument* --
                    # `q.num` and `q.den`, `r.1.1` and `r.2` -- are two
                    # different facts about it, not one statement cut twice.
                    if '.' in x and '.' in y and \
                            x.split('.')[0] == y.split('.')[0]:
                        continue
                    ra, rb = root(a.fqn), root(b.fqn)
                    comp[rb] = ra
                    diffs[root(a.fqn)] |= {x, y}
            members: dict[str, list[Decl]] = defaultdict(list)
            for d in group:
                members[root(d.fqn)].append(d)
            for key, fam in sorted(members.items()):
                if len(fam) < 2:
                    continue
                head = fam[0]
                others = ', '.join(f'{d.fqn} ({d.loc})' for d in fam[1:])
                varying = ', '.join(f'`{t}`' for t in sorted(diffs[key]))
                out.append(Finding(
                    'SIBLING-PAIR', head.fqn, head.loc,
                    f'statement differs only in {varying} from {others}; '
                    f'all cut from {parent}'))
        return out

    def run(self, codes: set[str] | None = None) -> list[Finding]:
        stmt_index: dict[str, Decl] = {}
        for d in self.decls:
            if d.kind in ('theorem', 'lemma') and not d.binders and d.concl:
                stmt_index.setdefault(strip_parens(norm(d.concl)), d)
        found: list[Finding] = []
        for d in self.decls:
            if d.kind not in ('theorem', 'lemma'):
                continue
            found += self.check_rfl_binder(d)
            found += self.check_single_use_tail(d)
            found += self.check_wrapper(d)
            found += self.check_long_statement(d)
            found += self.check_theorem_hyp(d, stmt_index)
            found += self.check_padded_bound(d)
            found += self.check_binder_restate(d)
        found += self.sibling_pairs()
        if codes:
            found = [f for f in found if f.code in codes]
        found.sort(key=lambda f: (f.code, f.fqn, f.loc))
        return found


def drop_name(stmt: str) -> str:
    """The statement without its modifiers, keyword and declared name."""
    m = NAME_RE.match(stmt)
    return stmt[m.end():] if m else stmt


def strip_leading_forall(text: str) -> str:
    """Drop a leading `∀ … ,` prefix: the caller often closes the step."""
    if not text.startswith('∀'):
        return text
    depth = 0
    for i, ch in enumerate(text):
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
        elif ch == ',' and depth == 0:
            return text[i + 1:].strip()
    return text


def strip_parens(text: str) -> str:
    """Compare terms up to bracketing and up to spacing before a projection."""
    return text.replace('( ', '').replace(' )', '').replace('(', '') \
               .replace(')', '').replace(' .', '.').strip()


def line_of(text: str, off: int) -> int:
    return text.count('\n', 0, off) + 1


def load_allow(path: Path) -> dict[tuple[str, str], str]:
    allow: dict[tuple[str, str], str] = {}
    if not path.is_file():
        return allow
    for raw in path.read_text().split('\n'):
        if not raw.strip() or raw.startswith('#'):
            continue
        cols = raw.split('\t')
        if len(cols) < 3:
            continue
        if cols[0].strip() == 'code' and cols[1].strip() == 'fqn':
            continue          # the table's own header row
        allow[(cols[0].strip(), cols[1].strip())] = cols[2].strip()
    return allow


def main() -> int:
    sys.setrecursionlimit(10000)
    ap = argparse.ArgumentParser()
    ap.add_argument('roots', nargs='*', default=list(DEFAULT_ROOTS))
    ap.add_argument('--root', default=None,
                    help='repository root to analyse (default: this one)')
    ap.add_argument('--allow', default=None, help='allow-list TSV')
    ap.add_argument('--no-allow', action='store_true',
                    help='ignore the allow-list (calibration mode)')
    ap.add_argument('--code', action='append', default=None,
                    help='restrict to a code (repeatable)')
    args = ap.parse_args()

    here = Path(__file__).resolve().parent.parent
    root = Path(args.root).resolve() if args.root else here
    tree = Tree(root, tuple(args.roots))
    findings = tree.run(set(args.code) if args.code else None)

    allow = {} if args.no_allow else load_allow(
        Path(args.allow) if args.allow else here / ALLOW_FILE)
    unlisted = [f for f in findings if (f.code, f.fqn) not in allow]
    for f in findings:
        print(f.line())
    # An allow row whose finding is gone is a licence nobody is using: it
    # outlives the declaration it excused and hides the next regression under
    # the same name.  It fails the gate as loudly as an unlisted finding.
    live = {(f.code, f.fqn) for f in findings}
    stale = sorted(k for k in allow if k not in live)
    for code, fqn in stale:
        print(f'STALE\t{code}\t{fqn}\tallow-listed, but the gate no longer '
              'reports this finding: delete the row')
    counts: dict[str, int] = defaultdict(int)
    for f in findings:
        counts[f.code] += 1
    summary = ', '.join(f'{c}={counts[c]}' for c in sorted(counts)) or 'none'
    print(f'SUMMARY\t{len(findings)} finding(s) [{summary}]; '
          f'{len(findings) - len(unlisted)} allow-listed; '
          f'{len(unlisted)} unlisted; {len(stale)} stale allow row(s)')
    return 1 if unlisted or stale else 0


if __name__ == '__main__':
    sys.exit(main())
