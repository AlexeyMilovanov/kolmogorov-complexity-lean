#!/usr/bin/env python3
"""Fail closed when the Lean 4.31 tree loses final Lean 4.28 public surface."""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
SOURCE_CONFIG = ROOT / "proof_loop" / "migration_source.json"
COMPATIBILITY_CONFIG = ROOT / "proof_loop" / "migration_compatibility.json"
COMPATIBILITY_SMOKE = ROOT / "scripts" / "smoke" / "MigrationCompatibility.lean"
PRIMREC_COVERAGE_ROW_RE = re.compile(r"(?m)^\| Primrec toolkit \|.*$")
LEAN_NAME = r"(?:_root_\.)?[\w][\w'.]*"
COMMAND_RE = re.compile(
    r"(?m)^[ \t]*(?:"
    r"namespace[ \t]+(?P<namespace>[\w][\w'.]*)[ \t]*$"
    r"|(?P<section>section)(?:[ \t]+[\w][\w']*)?[ \t]*$"
    r"|(?P<end>end)(?:[ \t]+[\w][\w'.]*)?[ \t]*$"
    r"|(?P<attrs>(?:@\[[^\]]*\][ \t]*(?:\n[ \t]*)?)*)"
    r"(?P<modifiers>(?:(?:noncomputable|protected|partial)[ \t]+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|opaque)"
    rf"[ \t]+(?P<name>{LEAN_NAME})"
    r")"
)
COMPATIBILITY_ASSERTION_RE = re.compile(
    rf'(?m)^[ \t]*assert_compat[ \t]+"(?P<source>[^"\r\n]+)"'
    rf"[ \t\r\n]*=>[ \t\r\n]*(?P<target>{LEAN_NAME})[ \t]*$"
)
REQUIRED_INFRASTRUCTURE = (
    "COVERAGE.md",
    "scripts/audit.sh",
    "scripts/check_affected.py",
    "scripts/check_migration_fidelity.py",
    "scripts/final_release_gate.py",
    "scripts/smoke/MigrationCompatibility.lean",
    "scripts/smoke/PrimrecAuto.lean",
    "scripts/strict_lint_sweep.sh",
    "scripts/test_migration_fidelity.py",
    "SCALABILITY_31_PLAN.md",
)


class FidelityError(Exception):
    """A missing or inconsistent migration invariant."""


@dataclass(frozen=True)
class Declaration:
    module: str
    raw_name: str
    qualified_name: str
    kind: str
    attributes: tuple[str, ...]
    line: int

    @property
    def identity(self) -> str:
        return self.qualified_name


def display_path(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def load_json(path: Path) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise FidelityError(f"cannot read {display_path(path)}: {error}") from error


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


def mask_lean(text: str, *, strings: bool = True) -> str:
    """Mask comments and optionally strings while preserving offsets and newlines."""
    chars = list(text)
    index = 0
    block_depth = 0
    in_string = False
    while index < len(chars):
        pair = text[index : index + 2]
        if block_depth:
            if pair == "/-":
                chars[index : index + 2] = "  "
                block_depth += 1
                index += 2
            elif pair == "-/":
                chars[index : index + 2] = "  "
                block_depth -= 1
                index += 2
            else:
                if chars[index] != "\n":
                    chars[index] = " "
                index += 1
            continue
        if in_string:
            if text[index] == "\\" and index + 1 < len(chars):
                chars[index : index + 2] = "  "
                index += 2
            else:
                if chars[index] != "\n":
                    chars[index] = " "
                if text[index] == '"':
                    in_string = False
                index += 1
            continue
        if pair == "/-":
            chars[index : index + 2] = "  "
            block_depth = 1
            index += 2
        elif pair == "--":
            chars[index : index + 2] = "  "
            index += 2
            while index < len(chars) and text[index] != "\n":
                chars[index] = " "
                index += 1
        elif strings and text[index] == '"':
            chars[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    if block_depth:
        raise FidelityError("unterminated Lean block comment")
    if strings and in_string:
        raise FidelityError("unterminated Lean string")
    return "".join(chars)


def split_top_level_commas(text: str) -> list[str]:
    pieces: list[str] = []
    start = 0
    depth = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            pieces.append(text[start:index])
            start = index + 1
    pieces.append(text[start:])
    return pieces


def attribute_names(text: str) -> tuple[str, ...]:
    names: list[str] = []
    for block in re.findall(r"@\[(.*?)\]", text, flags=re.DOTALL):
        for item in split_top_level_commas(block):
            match = re.match(r"\s*([\w][\w'.]*)", item)
            if match:
                names.append(match.group(1))
    return tuple(sorted(names))


def qualify(namespace: list[str], raw_name: str) -> str:
    if raw_name.startswith("_root_."):
        return raw_name
    return ".".join([*namespace, raw_name]) if namespace else raw_name


def declarations_for(module: str, path: Path) -> list[Declaration]:
    text = path.read_text(encoding="utf-8", errors="strict")
    code = mask_lean(text)
    namespace: list[str] = []
    blocks: list[tuple[str, int]] = []
    declarations: list[Declaration] = []
    for match in COMMAND_RE.finditer(code):
        namespace_name = match.group("namespace")
        if namespace_name:
            blocks.append(("namespace", len(namespace)))
            namespace.extend(namespace_name.split("."))
            continue
        if match.group("section"):
            blocks.append(("section", len(namespace)))
            continue
        if match.group("end"):
            if blocks:
                _, namespace_length = blocks.pop()
                del namespace[namespace_length:]
            continue
        raw_name = match.group("name")
        if raw_name is None:
            continue
        declarations.append(
            Declaration(
                module=module,
                raw_name=raw_name,
                qualified_name=qualify(namespace, raw_name),
                kind=match.group("kind"),
                attributes=attribute_names(match.group("attrs") or ""),
                line=code.count("\n", 0, match.start()) + 1,
            )
        )
    return declarations


def public_declarations(paths: dict[str, Path]) -> list[Declaration]:
    declarations: list[Declaration] = []
    for module, path in paths.items():
        declarations.extend(declarations_for(module, path))
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
        if len(names) != len(target_names) or not names:
            raise FidelityError(f"invalid compatibility evidence for {source_name}")
        result[source_name] = names
    return result


def compatibility_assertions(path: Path = COMPATIBILITY_SMOKE) -> Counter[tuple[str, str]]:
    text = path.read_text(encoding="utf-8", errors="strict")
    uncommented = mask_lean(text, strings=False)
    assertions = Counter(
        (match.group("source"), match.group("target"))
        for match in COMPATIBILITY_ASSERTION_RE.finditer(uncommented)
    )
    return assertions


def normalize_coverage(text: str) -> str:
    rows = PRIMREC_COVERAGE_ROW_RE.findall(text)
    if len(rows) != 1:
        raise FidelityError(
            f"COVERAGE.md must contain exactly one Primrec toolkit row, found {len(rows)}"
        )
    return PRIMREC_COVERAGE_ROW_RE.sub(
        "| Primrec toolkit | VERSION-SPECIFIC API |", text
    )


def check_infrastructure() -> None:
    missing = [path for path in REQUIRED_INFRASTRUCTURE if not (ROOT / path).is_file()]
    if missing:
        raise FidelityError(
            "required validation/scalability infrastructure is missing: "
            + ", ".join(missing)
        )


def expanded_missing(
    source: list[Declaration], target: list[Declaration]
) -> list[Declaration]:
    remaining = Counter(declaration.identity for declaration in source)
    remaining.subtract(declaration.identity for declaration in target)
    remaining = +remaining
    result: list[Declaration] = []
    for declaration in source:
        if remaining[declaration.identity]:
            result.append(declaration)
            remaining[declaration.identity] -= 1
    return result


def check_attributes(source: list[Declaration], target: list[Declaration]) -> None:
    target_by_identity: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in target:
        target_by_identity[declaration.identity].append(declaration)
    missing: list[str] = []
    for declaration in source:
        candidates = target_by_identity.get(declaration.identity, [])
        if not candidates:
            continue
        source_attributes = set(declaration.attributes)
        if source_attributes and not any(
            source_attributes.issubset(set(candidate.attributes))
            for candidate in candidates
        ):
            missing.append(
                f"{declaration.module}:{declaration.line}:"
                f"{declaration.qualified_name} {sorted(source_attributes)}"
            )
    if missing:
        raise FidelityError(
            "source declaration attributes are missing from same-named targets: "
            + "; ".join(missing)
        )


def kind_class(kind: str) -> str:
    return "theorem" if kind in {"theorem", "lemma"} else kind


def check_kinds(source: list[Declaration], target: list[Declaration]) -> None:
    source_kinds: dict[str, Counter[str]] = defaultdict(Counter)
    target_kinds: dict[str, Counter[str]] = defaultdict(Counter)
    for declaration in source:
        source_kinds[declaration.identity][kind_class(declaration.kind)] += 1
    for declaration in target:
        target_kinds[declaration.identity][kind_class(declaration.kind)] += 1
    mismatches = {
        name: {
            "source": dict(source_kinds[name]),
            "target": dict(target_kinds[name]),
        }
        for name in source_kinds.keys() & target_kinds.keys()
        if source_kinds[name] != target_kinds[name]
        and sum(source_kinds[name].values()) == sum(target_kinds[name].values())
    }
    if mismatches:
        raise FidelityError(
            "same-named declarations changed declaration kind: "
            + json.dumps(mismatches, sort_keys=True)
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
        missing_decls = expanded_missing(source_decls, target_decls)

        source_by_raw: dict[str, list[Declaration]] = defaultdict(list)
        missing_by_raw: dict[str, list[Declaration]] = defaultdict(list)
        for declaration in source_decls:
            source_by_raw[declaration.raw_name].append(declaration)
        for declaration in missing_decls:
            missing_by_raw[declaration.raw_name].append(declaration)

        stale_sources = sorted(name for name in ledger if name not in source_by_raw)
        if stale_sources:
            raise FidelityError(
                "compatibility ledger names absent from final Lean 4.28: "
                + ", ".join(stale_sources)
            )
        ambiguous_sources = {
            name: [
                f"{declaration.module}:{declaration.line}:"
                f"{declaration.qualified_name}"
                for declaration in missing_by_raw.get(name, [])
            ]
            for name in ledger
            if len(missing_by_raw.get(name, [])) != 1
        }
        if ambiguous_sources:
            raise FidelityError(
                "compatibility source must identify exactly one missing declaration: "
                + json.dumps(ambiguous_sources, sort_keys=True)
            )
        undocumented = [
            f"{declaration.module}:{declaration.line}:{declaration.qualified_name}"
            for declaration in missing_decls
            if declaration.raw_name not in ledger
        ]
        if undocumented:
            raise FidelityError(
                "source public declarations lack a same-named target or compatibility "
                "entry: " + ", ".join(undocumented)
            )

        expected_assertions = Counter(
            (source_name, target_name)
            for source_name, target_names in ledger.items()
            for target_name in target_names
        )
        actual_assertions = compatibility_assertions()
        if actual_assertions != expected_assertions:
            missing_assertions = expected_assertions - actual_assertions
            extra_assertions = actual_assertions - expected_assertions
            raise FidelityError(
                "compatibility smoke assertions do not exactly match the ledger; "
                f"missing={sorted(missing_assertions.elements())}, "
                f"extra={sorted(extra_assertions.elements())}"
            )

        check_kinds(source_decls, target_decls)
        check_attributes(source_decls, target_decls)
        target_coverage = (ROOT / "COVERAGE.md").read_text(encoding="utf-8")
        source_coverage = (source / "COVERAGE.md").read_text(encoding="utf-8")
        if normalize_coverage(target_coverage) != normalize_coverage(source_coverage):
            raise FidelityError(
                "COVERAGE.md differs from source in more than the Primrec toolkit row"
            )

        check_infrastructure()
        unique_source = len({declaration.identity for declaration in source_decls})
        print(
            "FIDELITY OK: "
            f"{len(source_modules)} modules, "
            f"{unique_source} unique / {len(source_decls)} occurrence-qualified "
            "final-4.28 declarations, "
            f"{len(missing_decls)} documented 4.31 adaptations, "
            f"source commit {source_info.get('commit')}"
        )
        return 0
    except (FidelityError, OSError, UnicodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
