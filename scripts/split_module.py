#!/usr/bin/env python3
"""Split an oversized Lean module into a chain of smaller modules.

The file is cut at top-level command boundaries.  Every part imports the part
before it, so the sequential order of the original file -- and hence every
`variable`, `open`, and declaration dependency -- is preserved.  Namespaces,
`open`s, `variable`s and `local` commands in force at a cut point are re-emitted
in the prologue of the following part, since those do not travel through
`import`.

A `private` declaration is only visible inside its own module, so it and every
user of it have to end up in the same part.  Rather than merge the whole span
between the first and the last use -- which produces one enormous part when a
private helper is used again much later in the file -- the private declaration
and the *upward closure* of its users are relocated, in their original relative
order, to the position of the last of them, and pinned together as one
uncuttable block.  Moving a declaration later is safe for dependencies (all of
its own dependencies stay behind it), and the upward closure makes sure nothing
left behind still refers to what moved.  A relocation is only performed when
the two positions carry the same namespace stack and the source context is a
prefix of the destination context; otherwise the span is merged as before.

Usage:
    python3 scripts/split_module.py SOURCE --outdir DIR --module MOD_PREFIX
        [--max-lines 1000] [--names NAME1,NAME2,...] [--auto-names] [--dry-run]

`MOD_PREFIX` is the Lean module prefix of the produced parts, e.g.
`KolmogorovMathlib.SUV.Chapter02`; part `k` becomes `MOD_PREFIX.<name_k>`.
With `--auto-names` each part is named after the first `/-! ### ... -/` section
heading it contains.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

KEYWORDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure',
            'inductive', 'class', 'opaque', 'example', 'macro', 'notation',
            'syntax', 'elab', 'mutual', 'initialize', 'alias')
MODIFIERS = ('private', 'protected', 'nonrec', 'noncomputable', 'partial',
             'scoped', 'unsafe')
CMD_RE = re.compile(
    r'^(?:(?:' + '|'.join(MODIFIERS) + r')\s+)*(?:' + '|'.join(KEYWORDS) +
    r')\b')
CONTEXT_RE = re.compile(r'^(open|variable|local|attribute|universe|set_option'
                        r'|namespace|end|section|omit|include)\b')
NCSECTION_RE = re.compile(r'^noncomputable section\b')
DECL_NAME_RE = re.compile(
    r'^(?:(?:private|protected|nonrec|noncomputable|partial|scoped|unsafe)\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque'
    r'|alias)\s+'
    r'([^\s({\[:]+)')
IN_SUFFIX_RE = re.compile(r'(?<![A-Za-z0-9_])in\s*$')
HEADING_RE = re.compile(r'^/-!\s*#*\s*(.+?)\s*(-/)?\s*$')


def top_level_flags(lines: list[str]) -> list[bool]:
    """True for a line that starts outside any block comment."""
    out = []
    depth = 0
    for line in lines:
        out.append(depth == 0)
        i = 0
        while i < len(line):
            if line.startswith('/-', i):
                depth += 1
                i += 2
            elif line.startswith('-/', i) and depth > 0:
                depth -= 1
                i += 2
            elif depth == 0 and line.startswith('--', i):
                break
            else:
                i += 1
    return out


class Unit:
    def __init__(self, lines: list[str], start: int = 0,
                 top: list[bool] | None = None):
        self.lines = lines
        self.start = start
        # per-line flag: the line begins outside a block comment
        self.top = top if top is not None else [True] * len(lines)
        # `open X in` / `set_option ... in` are prefixes of the command that
        # follows them, so the unit's command is the first line that starts a
        # declaration, and only failing that a context command
        self.cmd = next((c for c in lines if CMD_RE.match(c)), None)
        if self.cmd is None:
            self.cmd = next((c for c in lines
                             if CONTEXT_RE.match(c) or NCSECTION_RE.match(c)),
                            lines[0])
        if CMD_RE.match(self.cmd):
            self.kind = 'decl'
        elif CONTEXT_RE.match(self.cmd) or NCSECTION_RE.match(self.cmd):
            self.kind = 'context'
        elif lines[0].startswith('/-!'):
            self.kind = 'section-comment'
        else:
            self.kind = 'other'
        m = DECL_NAME_RE.match(self.cmd)
        self.name = m.group(1) if m else None
        self.private = self.cmd.startswith('private')
        self.state: tuple = ((), ())
        self.cur_heading: str | None = None

    @property
    def size(self) -> int:
        return len(self.lines)

    def text(self) -> str:
        return '\n'.join(self.lines)

    def code_text(self) -> str:
        """The unit's lines with comments removed, for identifier search."""
        out = []
        for line, is_top in zip(self.lines, self.top):
            if not is_top:
                continue
            if line.lstrip().startswith('--'):
                continue
            cut = line.find('/-')
            if cut >= 0:
                line = line[:cut]
            cut = line.find('--')
            if cut >= 0:
                line = line[:cut]
            out.append(line)
        return '\n'.join(out)

    def heading(self) -> str | None:
        for line in self.lines:
            m = HEADING_RE.match(line)
            if m:
                return m.group(1)
        return None


def parse_units(lines: list[str], body_start: int) -> list[Unit]:
    top = top_level_flags(lines)
    starts: list[int] = []
    for i in range(body_start, len(lines)):
        line = lines[i]
        if not top[i] or not line or line[0] in ' \t':
            continue
        if (CMD_RE.match(line) or CONTEXT_RE.match(line)
                or NCSECTION_RE.match(line) or line.startswith('/-')
                or line.startswith('@[') or line.startswith('#')):
            starts.append(i)
    # A docstring, an attribute block or a `... in` modifier belongs to the
    # command below it, so a unit starts at the first line of that prefix run.
    heads: list[int] = []      # first line of each unit
    pending: int | None = None
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        block = lines[i:j]
        last = next((b for b in reversed(block) if b.strip()), '')
        head = block[0]
        is_prefix = (head.startswith('@[') or head.startswith('/--')
                     or IN_SUFFIX_RE.search(last))
        if is_prefix and k + 1 < len(starts):
            if pending is None:
                pending = i
            continue
        heads.append(pending if pending is not None else i)
        pending = None
    units: list[Unit] = []
    for k, i in enumerate(heads):
        j = heads[k + 1] if k + 1 < len(heads) else len(lines)
        units.append(Unit(lines[i:j], i, top[i:j]))
    if heads and heads[0] > body_start:
        units.insert(0, Unit(lines[body_start:heads[0]], body_start,
                             top[body_start:heads[0]]))
    return units


def annotate_states(units: list[Unit]) -> None:
    """Record the namespace stack and context commands in force at each unit."""
    ns_stack: list[str] = []
    ctx: list[tuple[int, str]] = []
    for u in units:
        u.state = (tuple(ns_stack), tuple(c for _, c in ctx))
        for c, is_top in zip(u.lines, u.top):
            if not is_top:
                continue
            if not (CONTEXT_RE.match(c) or NCSECTION_RE.match(c)):
                continue
            if IN_SUFFIX_RE.search(c):
                continue
            if (c.startswith('namespace') or c.startswith('section')
                    or NCSECTION_RE.match(c)):
                ns_stack.append(c)
            elif c.startswith('end'):
                if ns_stack:
                    ns_stack.pop()
                ctx = [(d, l) for d, l in ctx if d <= len(ns_stack)]
            elif (c.startswith('open') or c.startswith('variable')
                  or c.startswith('local') or c.startswith('universe')
                  or c.startswith('include') or c.startswith('omit')):
                ctx.append((len(ns_stack), c))


def closer_for(opener: str) -> str:
    o = opener.strip()
    if o.startswith('namespace'):
        return 'end ' + o.split(None, 1)[1].strip()
    if o.startswith('section'):
        rest = o[len('section'):].strip()
        return 'end ' + rest if rest else 'end'
    return 'end'


def uses(name: str, text: str) -> bool:
    return bool(re.search(r'(?<![A-Za-z0-9_])' + re.escape(name) +
                          r'(?![A-Za-z0-9_])', text))


STOP_WORDS = {'the', 'a', 'an', 'of', 'for', 'and', 'to', 'in', 'is', 'its',
              'that', 'with', 'by', 'on', 'as', 'at', 'from', 'it', 'this'}


def camel(title: str) -> str:
    """A module-name-shaped abbreviation of a section heading."""
    title = re.sub(r'`[^`]*`', ' ', title)
    title = re.sub(r'\([^)]*\)', ' ', title)
    title = title.split(':')[0]
    title = re.sub(r'[^A-Za-z0-9 ]', ' ', title)
    words = [w for w in title.split() if w]
    keep = [w for w in words if w.lower() not in STOP_WORDS] or words
    out = ''.join(w[0].upper() + w[1:] for w in keep[:4])
    out = re.sub(r'^[0-9]+', '', out)
    return out or ''


HARD_ANCHOR_RE = re.compile(r'^(variable|attribute|set_option|namespace|end'
                            r'|section|noncomputable section|include|omit'
                            r'|local)\b')


def group_private(units: list[Unit], verbose: bool) -> list[list[Unit]]:
    """Group the units into blocks that must not be cut apart, and order them.

    A `private` declaration and every user of it must share a module, so the
    units are merged into groups: a private declaration with its direct users,
    plus whatever a dependency cycle forces on top of that.  The groups are
    then emitted in a topological order keyed by the position of the group's
    last member, which keeps the order of the file wherever the dependencies
    allow it and moves a private helper forward to its last user rather than
    dragging everything in between along with it.

    A `variable`, `attribute`, `namespace` or `end` command is a hard anchor:
    the groups before it stay before it and the groups after it stay after it.
    An `open` is a soft anchor -- a declaration may be moved past it, gaining
    the wider scope, but nothing that follows it may be moved before it.
    """
    n = len(units)
    code = [u.code_text() for u in units]
    names = [u.name for u in units]
    # v depends on u  <=>  v mentions the name u declares
    deps: list[set[int]] = [set() for _ in range(n)]   # deps[v] = {u}
    for k in range(n):
        if not names[k]:
            continue
        pat = re.compile(r'(?<![A-Za-z0-9_])' + re.escape(names[k]) +
                         r'(?![A-Za-z0-9_])')
        for j in range(n):
            if j != k and pat.search(code[j]):
                deps[j].add(k)

    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: int, b: int) -> None:
        a, b = find(a), find(b)
        if a != b:
            parent[max(a, b)] = min(a, b)

    for k, u in enumerate(units):
        if u.private and u.name:
            for j in range(n):
                if k in deps[j]:
                    union(k, j)
        # a non-`local` `attribute` command may only be applied in the module
        # that declares the constant, so it travels with it
        if (u.kind == 'context' and u.cmd.startswith('attribute')
                and 'local' not in u.cmd.split(']')[0]):
            for j in deps[k]:
                union(k, j)

    hard = [k for k, u in enumerate(units)
            if u.kind == 'context' and HARD_ANCHOR_RE.match(u.cmd)]
    soft = [k for k, u in enumerate(units)
            if u.kind == 'context' and not HARD_ANCHOR_RE.match(u.cmd)]

    def build_edges() -> tuple[dict[int, set[int]], dict[int, list[int]]]:
        groups: dict[int, list[int]] = {}
        for k in range(n):
            groups.setdefault(find(k), []).append(k)
        pos = {g: max(m) for g, m in groups.items()}
        edges: dict[int, set[int]] = {g: set() for g in groups}
        for v in range(n):
            for u in deps[v]:
                a, b = find(u), find(v)
                if a != b:
                    edges[a].add(b)
        for a in hard:
            ga = find(a)
            for g in groups:
                if g == ga:
                    continue
                if pos[g] > pos[ga]:
                    edges[ga].add(g)
                else:
                    edges[g].add(ga)
        for a in soft:
            ga = find(a)
            for g in groups:
                if g != ga and pos[g] > pos[ga]:
                    edges[ga].add(g)
        return edges, groups

    # merge whatever a cycle in the combined order forces together
    while True:
        # a group must not span a `namespace`/`end`: moving a declaration out
        # of the namespace it was written in would rename it
        merged_ns = False
        spans: dict[int, list[int]] = {}
        for k in range(n):
            spans.setdefault(find(k), []).append(k)
        for members in spans.values():
            if len({units[k].state[0] for k in members}) > 1:
                lo, hi = min(members), max(members)
                for k in range(lo, hi + 1):
                    if find(k) != find(lo):
                        union(lo, k)
                        merged_ns = True
        if merged_ns:
            continue
        edges, groups = build_edges()
        color: dict[int, int] = {}
        stack: list[int] = []
        found = False

        def dfs(v: int) -> bool:
            color[v] = 1
            stack.append(v)
            for w in sorted(edges.get(v, ())):
                if color.get(w, 0) == 0:
                    if dfs(w):
                        return True
                elif color.get(w) == 1:
                    for x in stack[stack.index(w):]:
                        union(x, w)
                    return True
            color[v] = 2
            stack.pop()
            return False

        for v in sorted(edges):
            if color.get(v, 0) == 0 and dfs(v):
                found = True
                break
        if not found:
            break

    pos = {g: max(m) for g, m in groups.items()}
    indeg = {g: 0 for g in groups}
    for g, ws in edges.items():
        for w in ws:
            indeg[w] += 1
    import heapq
    ready = [(pos[g], g) for g in groups if indeg[g] == 0]
    heapq.heapify(ready)
    order: list[int] = []
    while ready:
        _, g = heapq.heappop(ready)
        order.append(g)
        for w in sorted(edges.get(g, ())):
            indeg[w] -= 1
            if indeg[w] == 0:
                heapq.heappush(ready, (pos[w], w))
    if len(order) != len(groups):
        raise SystemExit('split_module: the module order graph is cyclic')

    if verbose:
        natural = sorted(groups, key=lambda g: pos[g])
        moved = sum(1 for a, b in zip(order, natural) if a != b)
        print(f'  {len(groups)} groups, {moved} of them out of file order')
        for g in sorted(groups, key=lambda x: -sum(units[k].size
                                                   for k in groups[x]))[:3]:
            size = sum(units[k].size for k in groups[g])
            if size > 1000:
                privs = [units[k].name for k in groups[g] if units[k].private]
                print(f'  group of {size} lines held together by '
                      f'{len(privs)} private declarations: '
                      f'{", ".join(str(x) for x in privs[:6])}')

    return [[units[k] for k in sorted(groups[g])] for g in order]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('source')
    ap.add_argument('--outdir', required=True)
    ap.add_argument('--module', required=True)
    ap.add_argument('--max-lines', type=int, default=1000)
    ap.add_argument('--names', default='')
    ap.add_argument('--auto-names', action='store_true')
    ap.add_argument('--aggregator', default=None,
                    help='write an aggregator module importing every part, '
                         'carrying the original module docstring')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()

    src = Path(args.source)
    lines = src.read_text().split('\n')

    i = 0
    imports: list[str] = []
    while i < len(lines) and (lines[i].startswith('import')
                              or not lines[i].strip()):
        if lines[i].startswith('import'):
            imports.append(lines[i])
        i += 1
    doc_start = i
    if i < len(lines) and lines[i].startswith('/-!'):
        while i < len(lines) and not lines[i].rstrip().endswith('-/'):
            i += 1
        i += 1
    module_doc = '\n'.join(lines[doc_start:i]).strip()
    body_start = i

    units = parse_units(lines, body_start)
    annotate_states(units)
    cur_heading: str | None = None
    for u in units:
        h = u.heading()
        if h:
            cur_heading = h
        u.cur_heading = cur_heading
    blocks = group_private(units, args.verbose)

    base_depth = min((len(u.state[0]) for b in blocks for u in b
                      if u.kind == 'decl'), default=0)

    def pack(limit: int) -> list[dict]:
        """Cut the blocks into parts of at most `limit` lines where possible."""
        parts: list[dict] = []
        cur: list[Unit] = []
        cur_lines = 0
        pending_state: tuple = ((), ())
        for b in blocks:
            head = b[0]
            bsize = sum(u.size for u in b)
            # A part re-emits the namespace/section stack and the context
            # commands in force at its first unit, so a cut is legitimate at
            # any depth; only a context command itself must not be cut off
            # from what it governs.
            cuttable = head.kind in ('decl', 'section-comment')
            if cur_lines and cur_lines + bsize > limit and cuttable:
                carry: list[Unit] = []
                while cur and cur[-1].kind == 'section-comment':
                    carry.insert(0, cur.pop())
                if cur:
                    parts.append({'units': cur, 'state': pending_state})
                    cur = carry
                    cur_lines = sum(c.size for c in carry)
                    pending_state = carry[0].state if carry else head.state
            if not cur:
                pending_state = head.state
            cur += b
            cur_lines += bsize
        if cur:
            parts.append({'units': cur, 'state': pending_state})
        return parts

    total = sum(u.size for b in blocks for u in b)
    # leave room for the prologue the parts carry: imports, namespaces, opens
    overhead = len(imports) + 12
    limit = max(args.max_lines - overhead, 1)
    parts = pack(limit)
    # equalise: the same number of parts, of roughly the same size
    biggest = max(sum(u.size for u in b) for b in blocks)
    balanced = pack(max(-(-total // len(parts)), biggest))
    if len(balanced) == len(parts):
        parts = balanced

    # the namespace stack still open at the end of each part
    for p in parts:
        p['end_state'] = list(p['units'][-1].state[0])
        last = p['units'][-1]
        # the last unit may itself open or close namespaces
        stack = list(last.state[0])
        for c, is_top in zip(last.lines, last.top):
            if not is_top or IN_SUFFIX_RE.search(c):
                continue
            if (c.startswith('namespace') or c.startswith('section')
                    or NCSECTION_RE.match(c)):
                stack.append(c)
            elif c.startswith('end') and CONTEXT_RE.match(c):
                if stack:
                    stack.pop()
        p['end_state'] = stack

    room = 100 - len('import ') - len(args.module) - 1

    def fit(name: str, reserve: int = 0) -> str:
        """Shorten `name` so that the import line stays under the limit."""
        if len(name) <= room - reserve:
            return name
        words = re.findall(r'[A-Z0-9][^A-Z]*', name) or [name]
        out = ''
        for w in words:
            if len(out) + len(w) > room - reserve:
                break
            out += w
        return out or name[:max(room - reserve, 1)]

    names = [n for n in args.names.split(',') if n]
    if args.auto_names and not names:
        used: set[str] = set()
        for k, p in enumerate(parts):
            title = p['units'][0].cur_heading
            nm = fit(camel(title), 1) if title else ''
            if not nm:
                nm = f'Part{k + 1:02d}'
            base = nm
            suffix = 0
            while nm in used:
                suffix += 1
                nm = base + chr(ord('B') + suffix - 1)
            used.add(nm)
            names.append(nm)
    while len(names) < len(parts):
        names.append(f'Part{len(names) + 1:02d}')
    names = [fit(nm, 1) if len(nm) > room else nm for nm in names]
    if len(set(names)) != len(names) or any(len(nm) > room for nm in names):
        raise SystemExit(f'split_module: cannot name the parts of '
                         f'{args.module} within the line limit: {names}')
    names = names[:len(parts)]

    outdir = Path(args.outdir)
    for k, p in enumerate(parts):
        ns_state, ctx_state = p['state']
        head = list(imports)
        if k:
            head.append(f'import {args.module}.{names[k - 1]}')
        body = '\n'.join(u.text() for u in p['units']).strip('\n')
        pro: list[str] = []
        if k == 0 and module_doc and not args.aggregator:
            pro.append(module_doc)
        pro += list(ns_state)
        pro += list(ctx_state)
        closers = [closer_for(o) for o in reversed(p['end_state'])]
        text = ('\n'.join(head) + '\n\n' + '\n'.join(x for x in pro if x)
                + '\n\n' + body + '\n\n' + '\n'.join(closers) + '\n')
        target = outdir / f'{names[k]}.lean'
        lo = min(u.start for u in p['units']) + 1
        hi = max(u.start + u.size for u in p['units'])
        print(f'{text.count(chr(10)):6d}  {target}   '
              f'[source lines {lo}-{hi}]  {p["units"][0].cur_heading or ""}')
        if not args.dry_run:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
    if not args.dry_run:
        if args.aggregator:
            text = '\n'.join(f'import {args.module}.{nm}' for nm in names)
            if module_doc:
                text += '\n\n' + module_doc
            Path(args.aggregator).write_text(text + '\n')
            print(f'aggregator {args.aggregator}')
        else:
            print('aggregator imports:')
            for nm in names:
                print(f'import {args.module}.{nm}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
