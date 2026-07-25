#!/usr/bin/env python3
"""Fail closed when the Lean 4.31 tree loses final Lean 4.28 public surface."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
SOURCE_CONFIG = ROOT / "proof_loop" / "migration_source.json"
COMPATIBILITY_CONFIG = ROOT / "proof_loop" / "migration_compatibility.json"
DECL_RE = re.compile(
    r"(?m)^[ \t]*"
    r"(?:(?:noncomputable|protected|partial)[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque)[ \t]+"
    r"((?:_root_\.)?[A-Za-z_][A-Za-z0-9_'.]*)"
)
REQUIRED_INFRASTRUCTURE = (
    "scripts/audit.sh",
    "scripts/check_affected.py",
    "scripts/check_migration_fidelity.py",
    "scripts/final_release_gate.py",
    "scripts/smoke/PrimrecAuto.lean",
    "scripts/strict_lint_sweep.sh",
    "SCALABILITY_31_PLAN.md",
)


class FidelityError(Exception):
    """A missing or inconsistent migration invariant."""


def load_json(path: Path) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise FidelityError(f"cannot read {path.relative_to(ROOT)}: {error}") from error


def source_root() -> tuple[Path, dict[str, object]]:
    raw = load_json(SOURCE_CONFIG)
    if not isinstance(raw, dict):
        raise FidelityError("proof_loop/migration_source.json is not an object")
    configured = os.environ.get("KOLMOGOROV_MIGRATION_SOURCE_28")
    source = Path(configured or str(raw.get("root", ""))).resolve()
    if not source.is_dir():
        raise FidelityError(f"final Lean 4.28 source is unavailable: {source}")
    metadata_path = Path(str(raw.get("metadata", "")))
    metadata = load_json(metadata_path)
    if not isinstance(metadata, dict):
        raise FidelityError(f"source metadata is not an object: {metadata_path}")
    expected_commit = str(raw.get("commit", ""))
    if metadata.get("commit") != expected_commit:
        raise FidelityError(
            f"source commit mismatch: expected {expected_commit}, "
            f"metadata has {metadata.get('commit')}"
        )
    return source, raw


def lean_sources(root: Path) -> dict[str, Path]:
    source_dir = root / "KolmogorovMathlib"
    root_source = root / "KolmogorovMathlib.lean"
    if not source_dir.is_dir() or not root_source.is_file():
        raise FidelityError(f"project Lean roots are missing under {root}")
    paths = [root_source, *sorted(source_dir.rglob("*.lean"))]
    return {path.relative_to(root).as_posix(): path for path in paths}


def public_declarations(paths: dict[str, Path]) -> set[str]:
    declarations: set[str] = set()
    for path in paths.values():
        text = path.read_text(encoding="utf-8", errors="replace")
        declarations.update(DECL_RE.findall(text))
    return declarations


def compatibility() -> dict[str, tuple[str, ...]]:
    raw = load_json(COMPATIBILITY_CONFIG)
    if not isinstance(raw, dict):
        raise FidelityError("migration compatibility ledger is not an object")
    result: dict[str, tuple[str, ...]] = {}
    for source_name, target_names in raw.items():
        if not isinstance(source_name, str) or not isinstance(target_names, list):
            raise FidelityError("invalid compatibility-ledger entry")
        names = tuple(name for name in target_names if isinstance(name, str) and name)
        if not names:
            raise FidelityError(f"empty compatibility evidence for {source_name}")
        result[source_name] = names
    return result


def check_infrastructure() -> None:
    missing = [path for path in REQUIRED_INFRASTRUCTURE if not (ROOT / path).is_file()]
    if missing:
        raise FidelityError(
            "required validation/scalability infrastructure is missing: "
            + ", ".join(missing)
        )


def main() -> int:
    try:
        source, source_info = source_root()
        source_paths = lean_sources(source)
        target_paths = lean_sources(ROOT)
        source_modules = set(source_paths)
        target_modules = set(target_paths)
        missing_modules = sorted(source_modules - target_modules)
        extra_modules = sorted(target_modules - source_modules)
        if missing_modules or extra_modules:
            raise FidelityError(
                f"module-path mismatch; missing={missing_modules}, extra={extra_modules}"
            )

        source_decls = public_declarations(source_paths)
        target_decls = public_declarations(target_paths)
        ledger = compatibility()
        source_text = "\n".join(
            path.read_text(encoding="utf-8", errors="replace")
            for path in source_paths.values()
        )
        target_text = "\n".join(
            path.read_text(encoding="utf-8", errors="replace")
            for path in target_paths.values()
        )
        stale_sources = sorted(name for name in ledger if name not in source_decls)
        if stale_sources:
            raise FidelityError(
                "compatibility ledger names absent from final 4.28: "
                + ", ".join(stale_sources)
            )
        missing_decls = sorted(source_decls - target_decls)
        undocumented = [name for name in missing_decls if name not in ledger]
        if undocumented:
            raise FidelityError(
                "source public declarations lack a same-named target or compatibility "
                "entry: " + ", ".join(undocumented)
            )
        missing_evidence = {
            name: targets
            for name, targets in ledger.items()
            if name in missing_decls and not all(target in target_text for target in targets)
        }
        if missing_evidence:
            raise FidelityError(
                "compatibility evidence is absent from target source: "
                + json.dumps(missing_evidence, sort_keys=True)
            )
        if not all(name in source_text for name in source_decls):
            raise FidelityError("internal source declaration inventory inconsistency")
        check_infrastructure()
        print(
            "FIDELITY OK: "
            f"{len(source_modules)} modules, "
            f"{len(source_decls)} final-4.28 declaration names, "
            f"{len(missing_decls)} documented 4.31 adaptations, "
            f"source commit {source_info.get('commit')}"
        )
        return 0
    except (FidelityError, OSError, UnicodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
