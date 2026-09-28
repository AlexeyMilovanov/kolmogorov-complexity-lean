#!/usr/bin/env python3
"""Declaration-header freeze check.

Compares the *token sequence* of every declaration header in the working tree
against a git revision (default `HEAD`).  A header is everything from the
declaration keyword up to, but not including, the `:=` (or `where`) that starts
the body, together with any attribute lines immediately above it.

Whitespace and line breaks are ignored, so reflowing an over-long header line
is allowed; adding, removing, reordering or renaming a binder is not.  Renaming
a binder to an underscore-prefixed name shows up as a token difference and is
reported, which is exactly what a cleanup wants to be able to list.

The header also carries the *section context* of the declaration: the
`variable` binders in force that the statement actually depends on (the ones it
mentions, together with the instance binders and dependencies they drag in),
and any `omit … in` / `include … in` prefix.  Two declarations whose written
headers agree token for token are therefore still different statements when
they sit in different `variable` contexts, which is what the de-duplication
needs to see.

With `--by-name` the headers are keyed by *fully qualified name* (the enclosing
`namespace` prefix plus the declared name) across the whole tree instead of per
file, so a declaration that moves to another module with an unchanged header
passes.  In that mode a copy that disappears while a declaration with the same
statement survives is reported as `DUPLICATE REMOVED` rather than as a problem;
"same statement" means the header token sequences agree once the declared names
are dropped and -- for a `def`-like declaration, whose value is part of what it
states -- the bodies agree too.

With `--renames FILE` the rename table written by `scripts/rename_decls.py`
(`old_fqn`, `new_fqn`, file, visibility) is read as well: a declaration that is
missing under its old fully qualified name is looked up under its new one, and
the two headers are compared with the declared name removed.  A rename whose
header agrees is reported as `RENAMED`; one whose header does not is a problem
unless the re-cut table below records it, which is exactly the statement freeze
the cleanup promises.

With `--recut FILE` a table of recorded re-cuts (`fqn`, `deleted|restated`,
`reason`, `visibility`) is read: a declaration the table names as `deleted` may
be inlined and one it names as `restated` may change its header, each reported
with its reason rather than as a problem.  A recorded restatement still prints
the old/new header diff under its `RECORDED RESTATEMENT` line, so that what
changed stays visible to a reviewer even though it does not count as a problem.
The `visibility` column says whether the declaration was `public` or `private`
at the base revision; a row without it, or one whose visibility disagrees with
the base revision, is itself a problem and licenses nothing.  The table is for
declarations a phase was asked by name to inline or re-cut; every other change
is still a problem.

With `--definition-merges FILE` the definition-merge table of phase 15
(`deleted_def`, `survivor_def`, `equality_lemma`, `argument_map`) is read too:
before two headers are compared, every reference to a definition that the
phase merged away is rewritten to its survivor, and the recorded argument map
is applied to the arguments written after it.  A theorem whose header changed
*only* by that substitution therefore reads as unchanged, while any other
change is still reported.  The deleted definition itself is reported as
`DEFINITION MERGED`, with the equality lemma that justified the merge.

Usage:
    python3 scripts/check_headers.py [--rev HEAD] [--allow-underscore]
                                     [--by-name] [--renames FILE]
                                     [--definition-merges FILE]
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Declaration keywords.  `example` is deliberately absent: it declares nothing.
PROOF_KEYWORDS = ('theorem', 'lemma')
VALUE_KEYWORDS = ('def', 'abbrev', 'instance', 'structure', 'inductive',
                  'class', 'opaque', 'axiom', 'alias')
KEYWORDS = PROOF_KEYWORDS + VALUE_KEYWORDS
MODIFIERS = ('private', 'protected', 'nonrec', 'noncomputable', 'unsafe',
             'partial', 'scoped', 'local')

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s+)*'  # inline attributes: `@[simp] theorem …`
    r'(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*'
    r'(' + '|'.join(KEYWORDS) + r')\b(.*)$')
NAME_RE = re.compile(r"[^\s({\[:⦃⟨}]+")
TOKEN_RE = re.compile(r"[A-Za-z_\u00c0-\u024f\u0370-\u1fff\u2100-\u214f\u2200-\u22ff\u2c00-\ud7ff]"
                      r"[A-Za-z0-9_'!?\u00c0-\u024f\u0370-\u1fff\u2080-\u209c\u2100-\u214f"
                      r"\u2200-\u22ff\u2c00-\ud7ff\u2093]*"
                      r"|\d+|:=|=>|<;>|->|\S")

# Commands that end the extent of the declaration above them.
BOUNDARY_RE = re.compile(
    r'^(?:import|open|variable|universe|attribute|namespace|section|end|'
    r'noncomputable\s+section|include|omit|set_option|macro|macro_rules|'
    r'notation|syntax|elab|example|@\[|/--|/-!|#)')

VARIABLE_RE = re.compile(r'^variable\b(.*)$')
PREFIX_RE = re.compile(r'^(omit|include)\b(.*?)\bin\s*$')
IDENT_RE = re.compile(r"[A-Za-z_\u00c0-\u024f\u0370-\u1fff\u2100-\u214f"
                      r"\u2200-\u22ff\u2c00-\ud7ff]"
                      r"[A-Za-z0-9_'!?\u00c0-\u024f\u0370-\u1fff\u2080-\u209c"
                      r"\u2100-\u214f\u2200-\u22ff\u2c00-\ud7ff\u2093]*")
CTX_MARK = '\u27e6ctx\u27e7'

BIND_RE = re.compile(r"(?:let|have)(?![\w'])")

# An equation alternative of a pattern-matching declaration: `| pat => body`.
# A statement that merely starts a line with `|` (an absolute value, a
# `Finset.filter` bar) has no top-level `=>` on that line.
EQUATION_RE = re.compile(r'^\s*\|(?![|=]).*=>')

NAMESPACE_RE = re.compile(r'^namespace\s+(\S+)\s*$')
SECTION_RE = re.compile(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$')
END_RE = re.compile(r'^end(?:\s+(\S+))?\s*$')


def strip_comments(text: str) -> str:
    """Blank out comments, keeping the line structure intact."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0:
                break
            out.append('\n')
            i = j + 1
        elif text.startswith('/-', i):
            depth += 1
            i += 2
        elif text.startswith('-/', i) and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def attribute_start(src: list[str], i: int) -> int:
    """First line of the attribute block attached to the declaration at `i`."""
    start = i
    k = i - 1
    acc = ''
    while k >= 0:
        line = src[k]
        s = line.strip()
        if not s:
            break
        if line.startswith('@['):
            acc = line + acc
            start = k
            k -= 1
            if acc.count('[') == acc.count(']'):
                acc = ''
                continue
            continue
        if acc and acc.count('[') != acc.count(']'):
            # continuation line of a multi-line attribute block
            acc = line + acc
            start = k
            k -= 1
            continue
        break
    return start


def header_tokens(src: list[str], i: int,
                  kind: str = 'def') -> tuple[list[str], int, str]:
    """Header token list of the declaration starting at line `i`, the line
    after the header, and whatever follows `:=` on the header's last line.

    A statement may itself bind values -- `theorem foo … : let h : P := …; Q` --
    and the `:=` of such a binding does not start the body: one top-level `:=`
    is skipped for every top-level `let` or `have` seen so far, so that the
    header of a `let`-statement is the whole statement and not its first line.
    """
    depth = 0
    j = i
    chunk: list[str] = []
    stop = False
    tail = ''
    pending = 0     # top-level `let`/`have` bindings whose `:=` is still ahead
    n = len(src)
    while j < n and not stop and j - i < 500:
        line = src[j]
        if j > i and line and line[0] not in ' \t' and (
                BOUNDARY_RE.match(line) or DECL_RE.match(line)):
            break
        if j > i and line.lstrip().startswith('|') and (
                kind in VALUE_KEYWORDS or EQUATION_RE.match(line)):
            # the equations of a pattern-matching declaration: the header of
            # `def f (a : α) : β` ends before the first `| pat => ...`.
            # In a theorem a leading `|` usually opens an absolute value and
            # the statement continues, so there the line has to look like an
            # equation alternative (`| pat => proof`) before it is read as the
            # start of the proof.
            break
        buf = []
        p = 0
        while p < len(line):
            ch = line[p]
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif depth == 0 and line.startswith(':=', p):
                if pending:
                    pending -= 1
                    buf.append(':')
                    buf.append('=')
                    p += 2
                    continue
                stop = True
                tail = line[p + 2:]
                break
            elif depth == 0 and BIND_RE.match(line, p) and (
                    p == 0 or not re.match(r"[\w'.]", line[p - 1])):
                pending += 1
            buf.append(ch)
            p += 1
        chunk.append(''.join(buf))
        if not stop and depth == 0 and re.search(r'(?<![A-Za-z0-9_])where\s*$',
                                                 line):
            stop = True
        j += 1
    start = attribute_start(src, i)
    header = '\n'.join(src[start:i] + chunk)
    return TOKEN_RE.findall(header), j, tail


OPEN = '({[\u2983'
CLOSE = ')}]\u2984'


def gather_command(src: list[str], i: int) -> tuple[str, int]:
    """The (possibly multi-line) command starting at line `i`, and the line
    after it.  A command continues while its brackets are unbalanced or the
    next line is indented."""
    depth = 0
    j = i
    parts: list[str] = []
    while j < len(src):
        line = src[j]
        if j > i and (depth <= 0 and (not line or line[0] not in ' \t')):
            break
        for ch in line:
            if ch in OPEN:
                depth += 1
            elif ch in CLOSE:
                depth -= 1
        parts.append(line)
        j += 1
    return ' '.join(parts), j


class Binder:
    """One `variable` binder, e.g. `{A : Type*}` or `[FiniteLetterCode A]`."""

    __slots__ = ('names', 'tokens', 'idents', 'is_inst')

    def __init__(self, names, tokens, idents, is_inst):
        self.names = names
        self.tokens = tokens
        self.idents = idents
        self.is_inst = is_inst


def parse_binders(text: str) -> list[Binder]:
    """Split the text after `variable` into its bracketed binder groups."""
    out: list[Binder] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch not in OPEN:
            i += 1
            continue
        depth = 0
        j = i
        while j < n:
            if text[j] in OPEN:
                depth += 1
            elif text[j] in CLOSE:
                depth -= 1
                if depth == 0:
                    break
            j += 1
        group = text[i:j + 1]
        inner = group[1:-1]
        is_inst = ch == '['
        head, sep, typ = inner.partition(':')
        if sep and not head.strip().startswith('inst'):
            names = head.split()
        elif sep:
            names = [x for x in head.split() if not x.startswith('inst')]
        else:
            names, typ = [], inner
        if is_inst and not sep:
            names = []
        out.append(Binder(names, TOKEN_RE.findall(group),
                          set(IDENT_RE.findall(typ)), is_inst))
        i = j + 1
    return out


def header_bound_names(header: list[str]) -> set[str]:
    """The names the declaration's own binders introduce.

    A `variable` of the same name is shadowed by them and is then no part of
    the statement.
    """
    out: set[str] = set()
    depth = 0
    k = 0
    while k < len(header):
        t = header[k]
        if t in OPEN:
            depth += 1
            if depth == 1:
                # a binder group `(x y : T)`; a bracketed *term* such as
                # `(A × B)` has no `:` and binds nothing.  A brace group of
                # bare identifiers -- `{α β}` -- is the implicit binder whose
                # type Lean infers, and it binds its names too.
                names, j = [], k + 1
                while j < len(header):
                    if header[j] == ':':
                        out.update(names)
                        break
                    if header[j] in CLOSE:
                        if names and t in '{\u2983':
                            out.update(names)
                        break
                    if IDENT_RE.fullmatch(header[j]):
                        names.append(header[j])
                    else:
                        break
                    j += 1
        elif t in CLOSE:
            depth -= 1
        elif depth == 0 and t == ':':
            # the statement begins: what follows binds nothing at this level
            break
        k += 1
    return out


def context_tokens(binders: list[Binder], header: list[str]) -> list[str]:
    """The tokens of the `variable` binders the header actually depends on.

    A binder is in force for a declaration when the declaration mentions one of
    its names, when an included binder's type mentions one of its names, or --
    for an instance binder -- when its type mentions an included name.  That is
    Lean's own rule for which section variables enter a statement.
    """
    shadowed = header_bound_names(header)
    var_names = {n for b in binders for n in b.names}

    def dead(b: Binder) -> bool:
        if b.names:
            return all(n in shadowed for n in b.names)
        # An anonymous instance binder `[Primcodable α]` is in force only
        # through the variables it mentions; when the declaration re-binds
        # every one of them, Lean does not include it either.
        refs = [i for i in b.idents if i in var_names]
        return bool(refs) and all(i in shadowed for i in refs)

    binders = [b for b in binders if not dead(b)]
    mentioned = set(header)
    chosen: list[int] = []
    picked = [False] * len(binders)
    changed = True
    while changed:
        changed = False
        for k, b in enumerate(binders):
            if picked[k]:
                continue
            take = any(nm in mentioned for nm in b.names)
            if not take and b.is_inst:
                take = any(
                    ident in mentioned
                    for ident in b.idents
                    if any(ident in b2.names
                           for j, b2 in enumerate(binders) if picked[j]))
            if take:
                picked[k] = True
                chosen.append(k)
                mentioned |= b.idents
                changed = True
    toks: list[str] = []
    for k, b in enumerate(binders):
        if picked[k]:
            toks.extend(b.tokens)
    return toks


class Decl:
    __slots__ = ('name', 'kind', 'header', 'body', 'file', 'line')

    def __init__(self, name, kind, header, body, line):
        self.name = name
        self.kind = kind
        self.header = header
        self.body = body
        self.line = line


def parse(text: str, qualify: bool = False) -> dict[str, Decl]:
    """Map key -> declaration.  With `qualify`, the key is the fully qualified
    name; otherwise the declared name as written."""
    src = strip_comments(text).split('\n')
    res: dict[str, Decl] = {}
    # ('ns'|'sec'|'file', name, binders in force in this scope)
    stack: list[list] = [['file', None, []]]
    prefix: list[str] = []      # tokens of a pending `omit … in` / `include … in`
    i, n = 0, len(src)
    while i < n:
        line = src[i]
        if not line or line[0] in ' \t':
            i += 1
            continue
        m = NAMESPACE_RE.match(line)
        if m:
            stack.append(['ns', m.group(1), []])
            prefix = []
            i += 1
            continue
        m = SECTION_RE.match(line)
        if m:
            stack.append(['sec', m.group(1), []])
            prefix = []
            i += 1
            continue
        m = END_RE.match(line)
        if m:
            nm = m.group(1)
            prefix = []
            if nm is None:
                if len(stack) > 1:
                    stack.pop()
            else:
                for k in range(len(stack) - 1, 0, -1):
                    if stack[k][1] == nm:
                        del stack[k:]
                        break
                else:
                    if len(stack) > 1:
                        stack.pop()
            i += 1
            continue
        m = VARIABLE_RE.match(line)
        if m:
            chunk, i = gather_command(src, i)
            stack[-1][2].extend(
                parse_binders(chunk[len('variable'):]))
            prefix = []
            continue
        m = PREFIX_RE.match(line)
        if m:
            prefix = TOKEN_RE.findall(line)
            i += 1
            continue
        m = DECL_RE.match(line)
        if not m:
            i += 1
            continue
        toks, after, tail = header_tokens(src, i, m.group(1))
        # extent of the whole declaration, for `def`-like body comparison
        j = after
        while j < n:
            ln = src[j]
            if ln and ln[0] not in ' \t' and BOUNDARY_RE.match(ln):
                break
            if ln and ln[0] not in ' \t' and DECL_RE.match(ln):
                break
            j += 1
        body = TOKEN_RE.findall('\n'.join([tail] + src[after:j]))
        kw = m.group(1)
        rest = m.group(2).strip()
        nm = NAME_RE.match(rest)
        if nm and not nm.group(0).startswith(':'):
            name = nm.group(0)
        else:
            # an anonymous `instance ... : C where`: key it by its own header,
            # so that the anonymous instances of the two trees are compared as
            # a multiset of headers
            name = '_anon:' + kw + ':' + ' '.join(toks[1:])
        if name.startswith('_root_.'):
            # `_root_` escapes the enclosing namespaces
            name = name[len('_root_.'):]
        elif qualify:
            nsprefix = '.'.join(f[1] for f in stack if f[0] == 'ns' and f[1])
            name = f'{nsprefix}.{name}' if nsprefix else name
        binders = [b for frame in stack for b in frame[2]]
        ctx = context_tokens(binders, toks)
        if ctx or prefix:
            toks = toks + [CTX_MARK] + prefix + ctx
        prefix = []
        key = name
        c = 2
        while key in res:
            key = f'{name}#{c}'
            c += 1
        res[key] = Decl(name, kw, toks, body, i + 1)
        i = max(after, i + 1)
    return res


def collect(rev: str | None,
            qualify: bool = False) -> dict[str, dict[str, Decl]]:
    out: dict[str, dict[str, Decl]] = {}
    if rev is None:
        files = subprocess.run(
            ['git', 'ls-files', '--cached', '--others', '--exclude-standard',
             '*.lean'],
            cwd=REPO, capture_output=True, text=True).stdout.split()
    else:
        files = subprocess.run(['git', 'ls-tree', '-r', '--name-only', rev],
                               cwd=REPO, capture_output=True,
                               text=True).stdout.split()
        files = [f for f in files if f.endswith('.lean')]
    # `scripts/tests/cut_quality_fixtures/` holds frozen extracts of the
    # library as it read at an older revision, so that the mechanical-cut gate
    # can be calibrated against the audits.  They are test data, not library:
    # a copy there must not make a deleted declaration look present.
    files = [f for f in files
             if not f.startswith('scripts/tests/cut_quality_fixtures/')]
    for f in files:
        if rev is None:
            p = REPO / f
            if not p.exists():
                continue
            text = p.read_text()
        else:
            r = subprocess.run(['git', 'show', f'{rev}:{f}'], cwd=REPO,
                               capture_output=True, text=True)
            if r.returncode != 0:
                continue
            text = r.stdout
        decls = parse(text, qualify=qualify)
        for d in decls.values():
            d.file = f
        out[f] = decls
    return out


def by_name_index(tree: dict[str, dict[str, Decl]]) -> dict[str, list[Decl]]:
    idx: dict[str, list[Decl]] = {}
    for decls in tree.values():
        for key, d in decls.items():
            idx.setdefault(key.split('#')[0], []).append(d)
    return idx


def underscore_diff(toks: list[str], ntoks: list[str]) -> list[str] | None:
    """The binders renamed to `_x`, or None if the headers differ otherwise."""
    if len(ntoks) != len(toks):
        return None
    diffs = [(a, b) for a, b in zip(toks, ntoks) if a != b]
    if diffs and all(b == '_' + a for a, b in diffs):
        return [a for a, _ in diffs]
    return None


# `lemma` and `theorem` declare the same thing, and `Nat` and `ℕ` (and their
# kin) name the same type: a copy that spells one of them differently states
# exactly what the other states, so both spellings are normalised before two
# headers are compared.  Everything else is compared literally.
KIND_SYNONYMS = {'lemma': 'theorem'}
TYPE_SYNONYMS = {'Nat': 'ℕ', 'Int': 'ℤ', 'Rat': 'ℚ', 'Real': 'ℝ',
                 'ENat': 'ℕ∞'}


def normalize(toks: list[str]) -> list[str]:
    """The token list with keyword and type-name synonyms folded together.

    A qualified name keeps its head (`Nat.bits` is not `ℕ.bits`), so the
    replacement is skipped when the next token is a `.`.

    A leading `_root_.` is dropped: it disambiguates which constant a name
    resolves to, and says nothing about the statement.
    """
    out: list[str] = []
    for k, t in enumerate(toks):
        nxt = toks[k + 1] if k + 1 < len(toks) else None
        if t == '_root_' and nxt == '.':
            continue
        if t == '.' and k > 0 and toks[k - 1] == '_root_':
            continue
        if t in KIND_SYNONYMS:
            out.append(KIND_SYNONYMS[t])
        elif t in TYPE_SYNONYMS and nxt != '.':
            out.append(TYPE_SYNONYMS[t])
        else:
            out.append(t)
    return out


def statement(d: Decl) -> tuple:
    """What the declaration states, with its own name removed.

    For a theorem that is the header without the name; for a `def`-like
    declaration the value is part of the statement, so the body counts too.
    """
    short = d.name.split('.')[-1]
    # attributes are not part of what a declaration states
    toks = d.header
    if d.kind in toks:
        toks = toks[toks.index(d.kind):]
    # only the declared name itself is dropped: the same token elsewhere in
    # the statement names something else (`ComputableIn.fst` is about
    # `Prod.fst`, and dropping every `fst` would make it read like `snd`).
    # The name may be written dotted -- `theorem Ns.foo ...` inside another
    # namespace -- and then the whole chain is the declared name.
    rest = toks[1:]
    j = 0
    if rest and IDENT_RE.fullmatch(rest[0] or ''):
        j = 1
        while (j + 1 < len(rest) and rest[j] == '.'
               and IDENT_RE.fullmatch(rest[j + 1] or '')):
            j += 2
    if j and rest[j - 1] == short:
        head = tuple(['SELF'] + list(rest[j:]))
    else:
        head = tuple(t for t in toks if t != short)
    head = tuple(normalize(list(head)))
    kind = KIND_SYNONYMS.get(d.kind, d.kind)
    if d.kind in PROOF_KEYWORDS:
        return (kind, head)
    body = tuple('SELF' if t == short else t for t in d.body)
    return (kind, head, tuple(normalize(list(body))))


OPENERS = {'(', '{', '[', '\u2983'}
QUANTS = {'\u2200', '\u2203', 'fun', '\u03bb', '\u2211', '\u220f', '\u2a06',
          '\u2a05', '\u222b'}
# A binder name is short: at most four characters (`n`, `hx`, `w'`, `x\u2081`,
# `h01`).  A handful of equally short *constants* would otherwise be renamed
# along with them, which would make `max` and `min` read alike.
SHORT_RE = re.compile(
    r"^[A-Za-z_\u03b1-\u03c9][A-Za-z0-9'\u2080-\u2089_\u03b1-\u03c9]{0,3}$")
CONSTANTS = {'max', 'min', 'id', 'abs', 'fst', 'snd', 'not', 'and', 'or',
             'ite', 'succ', 'pred', 'inl', 'inr', 'some', 'none', 'sum',
             'zero', 'one', 'two', 'neg', 'inv', 'pow', 'log', 'exp'}


def bound_names(toks: list[str]) -> set[str]:
    """The names a statement binds: binder groups and quantifiers."""
    out: set[str] = set()
    i = 0
    while i < len(toks):
        t = toks[i]
        if t in OPENERS or t in QUANTS:
            j = i + 1
            while j < len(toks) and toks[j] not in {':', ',', '=>', ')', '}',
                                                    ']', '\u2984', '\u2208'}:
                if IDENT_RE.fullmatch(toks[j]):
                    out.add(toks[j])
                elif toks[j] != '_':
                    break
                j += 1
            i = j
            continue
        i += 1
    return out


def alpha(toks) -> tuple:
    """The statement with its bound names renamed to positional placeholders.

    Two headers that agree after this renaming state the same thing up to the
    choice of binder names, which is what this tool calls alpha-equivalent
    and is allowed to de-duplicate.
    """
    toks = list(toks)
    names = {n for n in bound_names(toks)
             if SHORT_RE.match(n) and n not in CONSTANTS}
    ren: dict[str, str] = {}
    out = []
    for k, t in enumerate(toks):
        if t in names and not (k > 0 and toks[k - 1] == '.'):
            ren.setdefault(t, f'\u27e8v{len(ren)}\u27e9')
            out.append(ren[t])
        else:
            out.append(t)
    return tuple(out)


def alpha_statement(d: Decl) -> tuple:
    st = statement(d)
    return (st[0], alpha(st[1])) + tuple(st[2:])


def print_diff(toks: list[str], ntoks: list[str]) -> None:
    shown = 0
    for a, b in zip(toks, ntoks):
        if a != b:
            print(f'    {a!r} -> {b!r}')
            shown += 1
            if shown >= 10:
                print('    ...')
                break
    if len(ntoks) != len(toks):
        print(f'    token count {len(toks)} -> {len(ntoks)}')


def check_by_file(old, new, allow_underscore: bool) -> int:
    problems = 0
    underscore = []
    for f, decls in old.items():
        ndecls = new.get(f)
        if ndecls is None:
            print(f'MISSING FILE {f}')
            problems += 1
            continue
        for name, d in decls.items():
            nd = ndecls.get(name)
            if nd is None:
                print(f'MISSING DECL {f}: {name}')
                problems += 1
                continue
            if nd.header == d.header:
                continue
            ds = underscore_diff(d.header, nd.header)
            if ds is not None:
                underscore.append((f, name, ds))
                if allow_underscore:
                    continue
            print(f'HEADER CHANGED {f}: {name}')
            print_diff(d.header, nd.header)
            problems += 1
    for f, name, ds in underscore:
        print(f'UNDERSCORED {f}: {name}: {", ".join(ds)}')
    print(f'{sum(len(d) for d in old.values())} headers compared, '
          f'{len(underscore)} underscore renames, {problems} problems')
    return problems


def read_renames(path: str | None) -> dict[str, str]:
    """The `old_fqn -> new_fqn` table written by `scripts/rename_decls.py`."""
    table: dict[str, str] = {}
    if not path:
        return table
    for line in Path(path).read_text().split('\n'):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split('\t')
        if len(parts) >= 2:
            table[parts[0]] = parts[1]
    return table


class Merge:
    """One row of the definition-merge table.

    `deleted` is the fully qualified name of the definition that was removed,
    `survivor` the one that replaced it, `lemma` the equality lemma that was
    proved before the removal, and `perm` the argument map: `perm[k]` is the
    position, in the deleted definition's argument list, of the argument the
    survivor takes in position `k`.  An empty `perm` is the identity.
    """

    __slots__ = ('deleted', 'survivor', 'lemma', 'perm')

    def __init__(self, deleted, survivor, lemma, perm):
        self.deleted = deleted
        self.survivor = survivor
        self.lemma = lemma
        self.perm = perm


def read_definition_merges(path: str | None) -> dict[str, Merge]:
    """The definition-merge table, keyed by deleted fully qualified name.

    The columns are `deleted_def`, `survivor_def`, `equality_lemma` and
    `argument_map`.  The argument map is a comma-separated permutation of
    argument positions (`1,0` for a two-argument definition whose arguments
    were swapped); `-`, `id` and the empty string mean unchanged arguments.
    """
    table: dict[str, Merge] = {}
    if not path:
        return table
    for line in Path(path).read_text().split('\n'):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split('\t')
        if parts[0] == 'deleted_def' or len(parts) < 2:
            continue
        deleted, survivor = parts[0].strip(), parts[1].strip()
        lemma = parts[2].strip() if len(parts) > 2 else ''
        raw = (parts[3] if len(parts) > 3 else '').strip()
        perm: list[int] = []
        if raw and raw not in ('-', 'id'):
            try:
                perm = [int(x) for x in raw.replace(' ', '').split(',')]
            except ValueError:
                perm = []
        table[deleted] = Merge(deleted, survivor, lemma, perm)
    return table


CLOSERS = {')', '}', ']', '\u2984'}


def argument_groups(toks: list[str], start: int,
                    count: int) -> tuple[list[list[str]] | None, int]:
    """The first `count` argument groups of an application starting at `start`.

    An argument is an atom, a dotted name or a balanced bracketed group.
    Returns `(None, start)` when that many arguments are not written out, in
    which case the application is left alone.
    """
    groups: list[list[str]] = []
    i = start
    while i < len(toks) and len(groups) < count:
        t = toks[i]
        if t in OPENERS:
            depth, j = 0, i
            while j < len(toks):
                if toks[j] in OPENERS:
                    depth += 1
                elif toks[j] in CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if j >= len(toks):
                return None, start
            groups.append(toks[i:j + 1])
            i = j + 1
        elif IDENT_RE.fullmatch(t) or t.isdigit():
            j = i
            while j + 2 < len(toks) and toks[j + 1] == '.':
                j += 2
            groups.append(toks[i:j + 1])
            i = j + 1
        else:
            return None, start
    if len(groups) < count:
        return None, start
    return groups, i


def apply_merges(toks: list[str], owner: str,
                 merges: dict[str, Merge]) -> list[str]:
    """Rewrite references to merged-away definitions in an old header.

    Every occurrence of a deleted definition's name is replaced by the
    survivor's name, and the survivor's argument map is applied to the
    arguments written after it.  A reference is taken to be a reference to the
    deleted copy when it is qualified by the deleted definition's namespace, or
    when the declaration whose header this is lives in that namespace -- the
    two copies of a merged definition usually share their short name, and only
    the namespace tells them apart.
    """
    if not merges:
        return toks
    by_short: dict[str, list[Merge]] = {}
    for m in merges.values():
        by_short.setdefault(m.deleted.split('.')[-1], []).append(m)
    owner_ns = owner.rsplit('.', 1)[0] if '.' in owner else ''
    out: list[str] = []
    i = 0
    while i < len(toks):
        t = toks[i]
        cands = by_short.get(t)
        if not cands:
            out.append(t)
            i += 1
            continue
        # the dotted prefix already written in front of this token
        pref: list[str] = []
        k = len(out) - 1
        while k >= 1 and out[k] == '.' and IDENT_RE.fullmatch(out[k - 1] or ''):
            pref.insert(0, out[k - 1])
            k -= 2
        chosen = None
        for m in cands:
            dns = m.deleted.rsplit('.', 1)[0]
            dparts = dns.split('.') if dns else []
            qualified = bool(pref) and dparts[-len(pref):] == pref
            inside = bool(dns) and (owner_ns == dns
                                    or owner_ns.startswith(dns + '.'))
            if qualified or (not pref and inside):
                chosen = m
                break
        if chosen is None:
            out.append(t)
            i += 1
            continue
        # drop the qualifying prefix that named the deleted copy
        for _ in range(len(pref)):
            out.pop()
            out.pop()
        out.append(chosen.survivor.split('.')[-1])
        i += 1
        if chosen.perm:
            groups, after = argument_groups(toks, i, len(chosen.perm))
            if groups is not None:
                for k in chosen.perm:
                    out.extend(groups[k])
                i = after
    return out


def declared_visibility(d: 'Decl') -> str:
    """`private` or `public`, read off the modifiers in front of the keyword."""
    for t in d.header:
        if t in KEYWORDS:
            break
        if t == 'private':
            return 'private'
    return 'public'


def read_recut(path: str | None,
               oldidx: dict[str, list] | None = None
               ) -> tuple[dict[str, tuple[str, str]], list[str]]:
    """The recorded re-cut table (`fqn`, `deleted|restated`, `reason`,
    `visibility`), together with the problems the table itself has.

    A phase that is asked to inline or re-cut a *named* declaration cannot
    leave its header untouched.  Recording the name, what happened to it and
    why turns that change from an unexplained freeze violation into an entry
    a reviewer can check; anything not in the table is still a problem.

    The fourth column records whether the declaration was `public` or
    `private` at the base revision, which is what says whether the change
    could have been seen from outside the library.  It is mandatory, and it is
    checked against `oldidx` (the base revision indexed by fully qualified
    name) when that is available: a row whose visibility is missing, is not
    `public`/`private`, or disagrees with the base revision is reported and
    licenses nothing.
    """
    table: dict[str, tuple[str, str]] = {}
    problems: list[str] = []
    if not path:
        return table, problems
    for line in Path(path).read_text().split('\n'):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split('\t')
        if len(parts) < 2 or parts[1] not in ('deleted', 'restated'):
            continue
        name = parts[0]
        if len(parts) < 4 or parts[3].strip() not in ('public', 'private'):
            problems.append(f'RECUT ROW {name}: the visibility column is '
                            f'missing or is not public/private')
            continue
        if len(parts) < 3 or not parts[2].strip():
            problems.append(f'RECUT ROW {name}: the reason is empty')
            continue
        vis = parts[3].strip()
        entries = (oldidx or {}).get(name)
        if entries:
            actual = declared_visibility(entries[0])
            if actual != vis:
                problems.append(
                    f'RECUT VISIBILITY {name}: the table says {vis}, the base '
                    f'revision declares it {actual}')
                continue
        table[name] = (parts[1], parts[2])
    return table, problems


def check_by_name(old, new, allow_underscore: bool,
                  list_moves: str | None = None,
                  renames: dict[str, str] | None = None,
                  merges: dict[str, Merge] | None = None,
                  recut: dict[str, tuple[str, str]] | None = None,
                  recut_problems: int = 0) -> int:
    """Compare headers keyed by fully qualified name, tree-wide.

    A declaration may move between modules freely.  A copy of a declaration
    that disappears is not a problem when a surviving declaration states the
    same thing: that is the de-duplication the cleanup is meant to perform, and
    it is reported separately.
    """
    oldidx = by_name_index(old)
    newidx = by_name_index(new)
    renames = renames or {}
    merges = merges or {}
    # A rename also rewrites the *references* to the renamed constant inside
    # other headers, so compare headers modulo the rename table.
    short = {o.split('.')[-1]: n.split('.')[-1] for o, n in renames.items()}
    # Namespace components that the rename table dissolves: a reference written
    # `Ch04.kNat` in the old tree is a reference to the renamed constant
    # `Kolmogorov.SUV.Ch04.kNat`, and reads `kNat` once the namespace is gone.
    dropped: set[str] = set()
    for o, n in renames.items():
        oldparts, newparts = o.split('.')[:-1], n.split('.')[:-1]
        dropped |= {c for c in oldparts if c not in newparts}

    # A merged definition's survivor may live in a namespace the deleted copy
    # did not, so that a reference to it reads `ShortDescriptions.padBits`
    # where the old tree wrote `padBits`.  The qualifying prefix in front of a
    # survivor's name is dropped on both sides, which makes the two spellings
    # of the same reference compare equal.
    survivor_prefix: dict[str, list[str]] = {}
    for m in merges.values():
        parts = m.survivor.split('.')
        if len(parts) > 1:
            survivor_prefix.setdefault(parts[-1], []).extend(parts[:-1])

    def strip_survivor_prefix(toks: list[str]) -> list[str]:
        if not survivor_prefix:
            return toks
        out: list[str] = []
        for t in toks:
            pref = survivor_prefix.get(t)
            if pref:
                while (len(out) >= 2 and out[-1] == '.'
                       and out[-2] in pref):
                    out.pop()
                    out.pop()
            out.append(t)
        return out

    def canon(toks: list[str]) -> list[str]:
        # visibility and elaboration modifiers are not part of the statement:
        # making a helper `private` must not read as a changed header
        toks = strip_survivor_prefix(toks)
        i = 0
        while i < len(toks) and toks[i] in MODIFIERS:
            i += 1
        out: list[str] = []
        toks = toks[i:]
        j = 0
        while j < len(toks):
            if (toks[j] in dropped and j + 1 < len(toks)
                    and toks[j + 1] == '.'):
                j += 2
                continue
            out.append(short.get(toks[j], toks[j]))
            j += 1
        return normalize(out)

    def canon_old(toks: list[str], owner: str) -> list[str]:
        # The old side, and only it, still mentions the definitions that this
        # phase merged away: rewrite those references to the survivor before
        # comparing, so that a statement whose header changed *only* by the
        # substitution reads as unchanged.
        return canon(apply_merges(toks, owner, merges))

    def canon_new(toks: list[str]) -> list[str]:
        # The same namespace elision, on the new side: a namespace component
        # that the table dissolves for some declarations may still qualify a
        # reference to one it does not (`Ch02.cPair` while `Ch02` is going
        # away for everything else), and must read the same on both sides.
        toks = strip_survivor_prefix(toks)
        i = 0
        while i < len(toks) and toks[i] in MODIFIERS:
            i += 1
        out: list[str] = []
        toks = toks[i:]
        j = 0
        while j < len(toks):
            if (toks[j] in dropped and j + 1 < len(toks)
                    and toks[j + 1] == '.'):
                j += 2
                continue
            out.append(toks[j])
            j += 1
        return normalize(out)

    survivors: dict[tuple, Decl] = {}
    survivors_alpha: dict[tuple, Decl] = {}
    for entries in newidx.values():
        for d in entries:
            survivors.setdefault(statement(d), d)
            survivors_alpha.setdefault(alpha_statement(d), d)

    # the re-cut table's own problems (a missing or wrong visibility column)
    problems = recut_problems
    underscore: list[tuple[str, str, list[str]]] = []
    moved: list[tuple[str, str, str]] = []
    removed_dups: list[tuple[str, str, str, str]] = []
    renamed: list[tuple[str, str, str]] = []
    merged_defs: list[tuple[str, str, str, str]] = []
    inlined: list[tuple[str, str, str]] = []
    restated: list[tuple[str, str, str, list[str], list[str]]] = []
    compared = 0
    common = 0
    aliases = 0
    for name in sorted(oldidx):
        entries = oldidx[name]
        newentries = newidx.get(name, [])
        if newentries:
            common += 1
        for d in entries:
            compared += 1
            # An `alias` declares no statement of its own: it inherits the type
            # of its target.  A deprecated alias that still exists under the
            # same name -- in `KolmogorovMathlib/Deprecated/`, where phase 4
            # collects them -- therefore freezes nothing and is not compared.
            if d.kind == 'alias' and any(nd.kind == 'alias'
                                         for nd in newentries):
                aliases += 1
                continue
            merge = merges.get(name)
            # A merge that keeps the name -- two private copies in the same
            # namespace -- leaves the survivor to be compared as usual; a
            # deprecated alias under the old name states nothing of its own.
            if merge is not None and not [nd for nd in newentries
                                          if nd.kind != 'alias']:
                merged_defs.append((name, merge.survivor, merge.lemma,
                                    d.file))
                continue
            target = renames.get(name)
            if target is not None and all(nd.kind == 'alias'
                                          for nd in newentries):
                newentries = []
            same = [nd for nd in newentries
                    if canon(nd.header) == canon_old(d.header, name)]
            if same:
                if all(nd.file != d.file for nd in same):
                    moved.append((name, d.file, same[0].file))
                continue
            if newentries:
                nd = newentries[0]
                ds = underscore_diff(canon_old(d.header, name),
                                     canon(nd.header))
                if ds is not None:
                    underscore.append((nd.file, name, ds))
                    if allow_underscore:
                        continue
                # This copy is gone from its own file while other declarations
                # keep the name elsewhere (the same short name in two
                # namespaces, or a second copy of a generic helper).  If some
                # declaration still states what it stated, nothing was lost.
                if all(nd2.file != d.file for nd2 in newentries):
                    twin = survivors.get(statement(d)) or \
                        survivors_alpha.get(alpha_statement(d))
                    if twin is not None:
                        removed_dups.append((name, d.file, twin.name,
                                             twin.file))
                        continue
                row = (recut or {}).get(name)
                if row is not None and row[0] == 'restated':
                    restated.append((name, nd.file, row[1], d.header,
                                     nd.header))
                    continue
                print(f'HEADER CHANGED {name} ({d.file} -> {nd.file})')
                print_diff(d.header, nd.header)
                problems += 1
                continue
            if target is not None:
                tentries = newidx.get(target, [])
                if tentries:
                    # the target name may have several copies (a generic helper
                    # that also lives in another module); any of them proves
                    # that the statement survives
                    match = next(
                        (nd for nd in tentries
                         if canon_old(list(statement(d)[1]), name)
                         == canon_new(list(statement(nd)[1]))), None)
                    if match is None:
                        # binder names are allowed to differ: a cleanup may
                        # merge alpha-equivalent copies
                        match = next(
                            (nd for nd in tentries
                             if alpha(canon_old(list(statement(d)[1]), name))
                             == alpha(canon_new(list(statement(nd)[1])))),
                            None)
                    if match is not None:
                        renamed.append((name, target, match.file))
                        continue
                    nd = tentries[0]
                    # A rename whose target states the same thing with its
                    # arguments in another order is still a header change; it
                    # is allowed exactly when the re-cut table records it,
                    # which is the rule the un-renamed path already follows.
                    row = (recut or {}).get(name)
                    if row is not None and row[0] == 'restated':
                        restated.append((name, nd.file, row[1], d.header,
                                         nd.header))
                        continue
                    print(f'HEADER CHANGED UNDER RENAME {name} -> {target} '
                          f'({d.file} -> {nd.file})')
                    print_diff(d.header, nd.header)
                    problems += 1
                    continue
                print(f'MISSING RENAME TARGET {name} -> {target}')
                problems += 1
                continue
            twin = survivors.get(statement(d)) or \
                survivors_alpha.get(alpha_statement(d))
            if twin is not None:
                removed_dups.append((name, d.file, twin.name, twin.file))
                continue
            row = (recut or {}).get(name)
            if row is not None and row[0] == 'deleted':
                inlined.append((name, d.file, row[1]))
                continue
            print(f'MISSING DECL {name} (was in {d.file})')
            problems += 1
    for f, name, ds in underscore:
        print(f'UNDERSCORED {name} ({f}): {", ".join(ds)}')
    for name, f, reason in inlined:
        print(f'RECORDED DELETION {name} ({f}): {reason}')
    for name, f, reason, oldh, newh in restated:
        print(f'RECORDED RESTATEMENT {name} ({f}): {reason}')
        print_diff(oldh, newh)
    for name, target, f in renamed:
        print(f'RENAMED {name} -> {target} ({f})')
    for name, survivor, lemma, f in merged_defs:
        print(f'DEFINITION MERGED {name} -> {survivor} '
              f'({lemma or "no equality lemma recorded"}, {f})')
    for name, oldf, survivor, f in removed_dups:
        print(f'DUPLICATE REMOVED {name} ({oldf}) -> {survivor} ({f})')
    if list_moves:
        seen: dict[tuple[str, str], str] = {}
        for name, oldf, newf in moved:
            seen.setdefault((oldf, newf), name)
        with open(list_moves, 'w') as fh:
            fh.write('old_file\tnew_file\tfirst_declaration\n')
            for (oldf, newf), name in sorted(seen.items()):
                fh.write(f'{oldf}\t{newf}\t{name}\n')
        print(f'{len(seen)} (old file -> new file) pairs written to {list_moves}')
    print(f'{compared} headers compared by name, {common} common names, '
          f'{len(moved)} moved modules, '
          f'{len(underscore)} underscore renames, '
          f'{len(removed_dups)} duplicate copies removed, '
          f'{aliases} deprecated aliases relocated, '
          f'{len(inlined)} recorded deletions, '
          f'{len(restated)} recorded restatements, '
          f'{len(renamed)} renames verified, '
          f'{len(merged_defs)} definitions merged, {problems} problems')
    return problems


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--rev', default='HEAD')
    ap.add_argument('--allow-underscore', action='store_true',
                    help='treat `x` -> `_x` binder renames as allowed')
    ap.add_argument('--by-name', action='store_true',
                    help='key headers by fully qualified name, tree-wide, so '
                         'that a declaration may move between modules')
    ap.add_argument('--renames', default=None,
                    help='rename table (old_fqn TAB new_fqn) to resolve '
                         'declarations that changed name')
    ap.add_argument('--definition-merges', default=None,
                    help='definition-merge table (deleted_def, survivor_def, '
                         'equality_lemma, argument_map): references to a '
                         'deleted definition are rewritten to the survivor '
                         'before headers are compared')
    ap.add_argument('--recut', default=None,
                    help='recorded re-cut table (fqn, deleted|restated, '
                         'reason, visibility): a declaration this table names '
                         'may be inlined or restated without counting as a '
                         'problem; the visibility column is mandatory and is '
                         'checked against the base revision')
    ap.add_argument('--list-moves', default=None,
                    help='write the (old file, new file) moves to this TSV')
    args = ap.parse_args()

    old = collect(args.rev, qualify=args.by_name)
    new = collect(None, qualify=args.by_name)

    if args.by_name:
        recut, recut_problems = read_recut(args.recut, by_name_index(old))
        for problem in recut_problems:
            print(problem)
        return 1 if check_by_name(
            old, new, args.allow_underscore, args.list_moves,
            read_renames(args.renames),
            read_definition_merges(args.definition_merges),
            recut, len(recut_problems)) else 0
    return 1 if check_by_file(old, new, args.allow_underscore) else 0


if __name__ == '__main__':
    raise SystemExit(main())
