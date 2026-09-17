#!/usr/bin/env python3
"""Calibration test for `scripts/cut_quality.py` against the audits.

Audit #4 (`~/phase17_hints/quality_sample4.md`, Part A) read 85 declarations
of the library at `80c1cbe` beside the parents they were cut from and called
eleven of them MECHANICAL.  Ten of those eleven still exist at `c989552`
(`restrictedAnchoredState_model_complexity_against_calc` was renamed away
before it), and `scripts/tests/cut_quality_fixtures/` holds one extract per
case: the lemma, its caller with the `set`/`have` context around the call, and
nothing else.  The extracts are verbatim lines of `git show c989552:<file>`,
listed in each fixture's own header, so the gate reads exactly the text the
audit read.  They are not meant to compile.

Every one of the ten must be reported under at least one code.  A rule
loosened until a reference case slips through fails here, which is what
happened between `c989552` and this test: a gate tuned only against its own
self-test drifted to 6 of 10 while its self-test stayed green.

`hereditary_family_step_budget` is split over two fixtures because its caller
really does live in another module (`Steps.lean`), which is the property
the cross-module call-site search has to keep.

Usage:  python3 scripts/tests/cut_quality_calibration.py
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECKER = Path(os.environ.get('CUT_QUALITY', HERE.parent / 'cut_quality.py'))
FIXTURES = 'cut_quality_fixtures'

# The ten testable MECHANICAL cases of audit #4, Part A, in its own order.
CASES = [
    'nearLength_reverse_bound',
    'logSlack_sum_six_add_const_le',
    'hereditary_family_step_budget',
    'prop_min_hereditary_slack_sum',
    'restrictedEffectiveSampledRun_live_retained',
    'restrictedEffectiveSampledRun_model_retained',
    'chain_sample_pair_and_slack_le',
    'param_bound_le',
    'slack_param_bound_le_C_mul_add',
    'sum_size_chainSplit_param_le',
]


def main() -> int:
    if not (HERE / FIXTURES).is_dir():
        print(f'FAIL  {HERE / FIXTURES} is missing')
        return 1
    out = subprocess.run(
        [sys.executable, '-B', str(CHECKER), '--root', str(HERE),
         '--no-allow', FIXTURES],
        capture_output=True, text=True)
    if out.returncode not in (0, 1):
        print(out.stdout + out.stderr)
        print(f'FAIL  the checker exited {out.returncode}')
        return 1
    codes: dict[str, list[str]] = {}
    for line in out.stdout.split('\n'):
        cols = line.split('\t')
        if len(cols) >= 2 and cols[0] != 'SUMMARY':
            codes.setdefault(cols[1].split('.')[-1], []).append(cols[0])
    caught = 0
    for name in CASES:
        got = sorted(set(codes.get(name, [])))
        if got:
            caught += 1
            print(f'ok    {name}  [{", ".join(got)}]')
        else:
            print(f'FAIL  {name}  reported under no code')
    print(f'calibration {caught}/{len(CASES)}')
    return 0 if caught == len(CASES) else 1


if __name__ == '__main__':
    sys.exit(main())
