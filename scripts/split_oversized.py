#!/usr/bin/env python3
"""Split every oversized project module with `scripts/split_module.py`.

For `KolmogorovMathlib/A/B.lean` the parts are written to
`KolmogorovMathlib/A/B/` and `KolmogorovMathlib/A/B.lean` is replaced by an
aggregator that imports them and keeps the original module docstring, so that
importers of `KolmogorovMathlib.A.B` see exactly what they saw before.

Usage:
    python3 scripts/split_oversized.py [--max-lines 1000] [--limit N]
                                       [--dry-run] [FILE ...]

With no FILE arguments every project module above the cap is split, largest
first.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SPLITTER = REPO / 'scripts' / 'split_module.py'


def oversized(max_lines: int) -> list[Path]:
    out = []
    for p in sorted((REPO / 'KolmogorovMathlib').rglob('*.lean')):
        n = len(p.read_text().split('\n'))
        if n > max_lines:
            out.append((n, p))
    out.sort(reverse=True)
    return [p for _, p in out]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='*')
    ap.add_argument('--max-lines', type=int, default=1000)
    ap.add_argument('--limit', type=int, default=None)
    ap.add_argument('--dry-run', action='store_true')
    args = ap.parse_args()

    files = ([REPO / f for f in args.files] if args.files
             else oversized(args.max_lines))
    if args.limit:
        files = files[:args.limit]
    for src in files:
        rel = src.relative_to(REPO)
        module = '.'.join(rel.with_suffix('').parts)
        outdir = src.with_suffix('')
        print(f'==== {rel}  ({len(src.read_text().split(chr(10)))} lines)')
        cmd = [sys.executable, str(SPLITTER), str(rel),
               '--outdir', str(outdir.relative_to(REPO)),
               '--module', module, '--auto-names',
               '--max-lines', str(args.max_lines)]
        if args.dry_run:
            cmd.append('--dry-run')
        else:
            cmd += ['--aggregator', str(rel)]
        r = subprocess.run(cmd, cwd=REPO)
        if r.returncode:
            print(f'FAILED on {rel}')
            return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
