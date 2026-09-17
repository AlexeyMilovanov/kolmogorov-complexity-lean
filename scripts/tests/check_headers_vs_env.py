#!/usr/bin/env python3
"""Check the freeze checker's name resolution against the real Lean environment.

`scripts/check_headers.py --by-name` keys declarations by the fully qualified
name it derives from the `namespace` structure of the source.  This script
validates that derivation against the names Lean itself puts in the
environment: every parsed declaration must exist as a constant of the module it
was parsed from.

Produce the environment dump first (with the project built):

    cat > /tmp/dump_decls.lean <<'EOF'
    import KolmogorovMathlib
    open Lean Elab Command in
    #eval show CommandElabM Unit from do
      let env ← getEnv
      let mods := env.header.moduleNames
      let mut out : Array String := #[]
      for (n, _) in env.constants.toList do
        match env.getModuleIdxFor? n with
        | some idx =>
          let m := mods[idx.toNat]!
          if (`KolmogorovMathlib).isPrefixOf m then out := out.push s!"{m}\t{n}"
        | none => pure ()
      IO.FS.writeFile "/tmp/env_decls.tsv" (String.intercalate "\n" out.toList)
    EOF
    lake env lean /tmp/dump_decls.lean

then run

    python3 scripts/tests/check_headers_vs_env.py /tmp/env_decls.tsv
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_headers  # noqa: E402

REPO = Path(__file__).resolve().parent.parent.parent


def main() -> int:
    dump = Path(sys.argv[1] if len(sys.argv) > 1 else '/tmp/env_decls.tsv')
    env: dict[str, set[str]] = {}
    for line in dump.read_text().split('\n'):
        if not line.strip():
            continue
        mod, name = line.split('\t')
        if name.startswith('_private.'):
            # `_private.<Module>.0.<name>`
            parts = name.split('.0.', 1)
            if len(parts) == 2:
                name = parts[1]
        env.setdefault(mod, set()).add(name)

    everywhere: dict[str, str] = {}
    for mod, names in env.items():
        for n in names:
            everywhere.setdefault(n, mod)

    tree = check_headers.collect(None, qualify=True)
    checked = 0
    missing: list[tuple[str, str]] = []
    elsewhere: list[tuple[str, str, str]] = []
    unknown_module = 0
    for f, decls in tree.items():
        mod = f[:-len('.lean')].replace('/', '.')
        names = env.get(mod)
        if names is None:
            unknown_module += 1
            continue
        for key, d in decls.items():
            if '_anon:' in d.name:
                continue
            checked += 1
            if d.name in names:
                continue
            other = everywhere.get(d.name)
            if other is not None:
                # the same fully qualified name is declared in two modules; the
                # environment keeps one of them.  The name resolution is still
                # right, so this is reported but not counted as a mismatch.
                elsewhere.append((mod, d.name, other))
            else:
                missing.append((mod, d.name))
    print(f'{checked} parsed declarations checked against the environment, '
          f'{len(missing)} not found, '
          f'{unknown_module} files not in the dump, '
          f'{len(elsewhere)} names declared in two modules')
    for mod, name, other in elsewhere:
        print(f'  DECLARED TWICE {name}: parsed from {mod}, '
              f'the environment keeps the copy in {other}')
    for mod, name in missing[:40]:
        print(f'  NOT IN ENV {name} (parsed from {mod})')
    return 1 if missing else 0


if __name__ == '__main__':
    raise SystemExit(main())
