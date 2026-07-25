#!/usr/bin/env python3
"""Strictly check the project modules affected by one or more source changes."""

from __future__ import annotations

import argparse
import heapq
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
ROOT_MODULE = "KolmogorovMathlib"
SOURCE_DIRECTORY = REPO_ROOT / ROOT_MODULE
ROOT_SOURCE = REPO_ROOT / f"{ROOT_MODULE}.lean"
IMPORT_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
    r"[ \t]*$"
)
BUILD_WARNING_RE = re.compile(r"(?:^|:)[ \t]*warning:", re.MULTILINE)
STRICT_OPTIONS = (
    "-Dlinter.flexible=true",
    "-Dlinter.style.longLine=true",
    "-Dlinter.style.multiGoal=true",
    "-Dlinter.style.openClassical=true",
)


class CheckError(Exception):
    """A condition that makes an affected check potentially unsound."""


def project_sources() -> list[Path]:
    """Return every project source in deterministic module-path order."""
    if not ROOT_SOURCE.is_file() or not SOURCE_DIRECTORY.is_dir():
        raise CheckError("project source roots are missing")
    return [ROOT_SOURCE, *sorted(SOURCE_DIRECTORY.rglob("*.lean"))]


def module_name(source: Path) -> str:
    """Convert a canonical project source path to its Lean module name."""
    relative = source.relative_to(REPO_ROOT)
    if relative == ROOT_SOURCE.relative_to(REPO_ROOT):
        return ROOT_MODULE
    if relative.parts[0] != ROOT_MODULE or source.suffix != ".lean":
        raise CheckError(f"not a project Lean source: {relative}")
    return ".".join(relative.with_suffix("").parts)


def uncommented_header_lines(text: str) -> Iterable[tuple[int, str]]:
    """Yield header lines with nested Lean comments removed."""
    block_depth = 0
    for line_number, line in enumerate(text.splitlines(), start=1):
        output: list[str] = []
        index = 0
        while index < len(line):
            if block_depth:
                if line.startswith("/-", index):
                    block_depth += 1
                    index += 2
                elif line.startswith("-/", index):
                    block_depth -= 1
                    index += 2
                else:
                    index += 1
            elif line.startswith("--", index):
                break
            elif line.startswith("/-", index):
                block_depth = 1
                index += 2
            else:
                output.append(line[index])
                index += 1
        yield line_number, "".join(output)
    if block_depth:
        raise CheckError("unterminated block comment in module header")


def parse_imports(source: Path) -> tuple[str, ...]:
    """Parse the initial import commands, failing on unsupported syntax."""
    imports: list[str] = []
    text = source.read_text(encoding="utf-8")
    try:
        for line_number, line in uncommented_header_lines(text):
            stripped = line.strip()
            if not stripped or stripped == "prelude":
                continue
            match = IMPORT_RE.fullmatch(line)
            if match:
                imports.append(match.group(1))
                continue
            if re.match(
                r"^[ \t]*(?:[A-Za-z_][A-Za-z0-9_']*[ \t]+)?import\b",
                line,
            ):
                raise CheckError(f"unsupported import syntax at line {line_number}")
            break
    except CheckError as error:
        relative = source.relative_to(REPO_ROOT)
        raise CheckError(f"{relative}: {error}") from error
    return tuple(imports)


def is_project_module(name: str) -> bool:
    return name == ROOT_MODULE or name.startswith(f"{ROOT_MODULE}.")


def cycle_blocked_modules(
    forward_graph: dict[str, tuple[str, ...]],
) -> tuple[str, ...]:
    """Return modules blocked by a project import cycle."""
    dependencies = {
        module: {
            imported for imported in imports if is_project_module(imported)
        }
        for module, imports in forward_graph.items()
    }
    dependency_count = {
        module: len(imports) for module, imports in dependencies.items()
    }
    dependents = {module: set() for module in forward_graph}
    for module, imports in dependencies.items():
        for imported in imports:
            dependents[imported].add(module)

    ready = [
        module for module, count in dependency_count.items() if count == 0
    ]
    heapq.heapify(ready)
    processed: set[str] = set()
    while ready:
        module = heapq.heappop(ready)
        processed.add(module)
        for dependent in sorted(dependents[module]):
            dependency_count[dependent] -= 1
            if dependency_count[dependent] == 0:
                heapq.heappush(ready, dependent)
    return tuple(sorted(set(forward_graph) - processed))


def build_graph() -> tuple[
    dict[str, Path], dict[str, tuple[str, ...]], dict[str, set[str]]
]:
    """Build and validate the complete project import graph."""
    modules: dict[str, Path] = {}
    paths: dict[Path, str] = {}
    for source in project_sources():
        canonical = source.resolve()
        try:
            name = module_name(canonical)
        except ValueError as error:
            raise CheckError(f"project source escapes repository: {source}") from error
        if name in modules:
            raise CheckError(
                f"ambiguous module {name}: {modules[name]} and {canonical}"
            )
        if canonical in paths:
            raise CheckError(
                f"source {canonical} resolves to both {paths[canonical]} and {name}"
            )
        modules[name] = canonical
        paths[canonical] = name

    forward_graph = {
        name: parse_imports(source) for name, source in sorted(modules.items())
    }
    unresolved = sorted(
        (dependent, imported)
        for dependent, imports in forward_graph.items()
        for imported in imports
        if is_project_module(imported) and imported not in modules
    )
    if unresolved:
        details = ", ".join(
            f"{dependent} imports {imported}" for dependent, imported in unresolved
        )
        raise CheckError(f"unresolved project imports: {details}")

    blocked = cycle_blocked_modules(forward_graph)
    if blocked:
        raise CheckError(
            "project import cycle blocks: " + ", ".join(blocked)
        )

    reverse_graph = {name: set() for name in modules}
    for dependent, imports in forward_graph.items():
        for imported in imports:
            if imported in modules:
                reverse_graph[imported].add(dependent)
    return modules, forward_graph, reverse_graph


def resolve_input(raw_path: str) -> Path | None:
    """Resolve an input path, preferring neither the CWD nor repository root."""
    supplied = Path(raw_path)
    if supplied.suffix != ".lean":
        return None

    if supplied.is_absolute():
        candidates = [supplied.resolve()]
    else:
        candidates = list(
            {
                (Path.cwd() / supplied).resolve(),
                (REPO_ROOT / supplied).resolve(),
            }
        )
    existing = sorted(
        {candidate for candidate in candidates if candidate.is_file()},
        key=str,
    )
    if len(existing) > 1:
        choices = ", ".join(str(path) for path in existing)
        raise CheckError(f"ambiguous input path {raw_path}: {choices}")
    if not existing:
        raise CheckError(f"Lean input does not exist: {raw_path}")
    return existing[0]


def changed_modules(raw_paths: Iterable[str], modules: dict[str, Path]) -> set[str]:
    """Resolve changed project sources and skip irrelevant non-project files."""
    modules_by_path = {path: name for name, path in modules.items()}
    changed: set[str] = set()
    for raw_path in raw_paths:
        source = resolve_input(raw_path)
        if source is None:
            print(f"Skipping non-Lean input: {raw_path}")
            continue
        name = modules_by_path.get(source)
        if name is None:
            print(f"Skipping non-project Lean input: {raw_path}")
            continue
        changed.add(name)
    return changed


def reverse_closure(changed: set[str], reverse_graph: dict[str, set[str]]) -> set[str]:
    """Compute the changed modules and all transitive project dependents."""
    affected: set[str] = set()
    pending = list(changed)
    while pending:
        current = pending.pop()
        if current in affected:
            continue
        affected.add(current)
        pending.extend(reverse_graph[current])
    return affected


def build_roots(affected: set[str], reverse_graph: dict[str, set[str]]) -> list[str]:
    """Return maximal affected modules; building them covers the whole closure."""
    return sorted(
        module for module in affected if not (reverse_graph[module] & affected)
    )


def print_modules(label: str, modules: Iterable[str]) -> None:
    ordered = sorted(modules)
    print(f"{label} ({len(ordered)}):")
    for module in ordered:
        print(f"  {module}")


def run_strict_check(module: str, source: Path) -> None:
    relative = source.relative_to(REPO_ROOT)
    command = ["lake", "env", "lean", *STRICT_OPTIONS, str(relative)]
    print(f"Strict direct check: {module}", flush=True)
    result = subprocess.run(
        command,
        cwd=REPO_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.returncode:
        raise CheckError(f"strict direct check failed for {module}")
    if result.stdout:
        raise CheckError(f"strict direct check emitted output for {module}")


def run_affected_build(roots: list[str]) -> None:
    targets = [f"+{module}" for module in roots]
    print(f"Affected Lake build ({len(targets)} maximal targets)", flush=True)
    result = subprocess.run(
        ["lake", "build", *targets],
        cwd=REPO_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.returncode:
        raise CheckError("affected Lake build failed")
    if BUILD_WARNING_RE.search(result.stdout):
        raise CheckError("affected Lake build emitted a warning")


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run strict direct checks on changed project Lean files and, unless "
            "--direct-only is selected, build their reverse-import closure."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--dry-run",
        "--list",
        action="store_true",
        dest="dry_run",
        help="print the checked closure and maximal Lake targets without building",
    )
    mode.add_argument(
        "--print-project-build-roots",
        action="store_true",
        help=(
            "validate the complete graph and print one sorted maximal module "
            "per line, without headers"
        ),
    )
    mode.add_argument(
        "--direct-only",
        action="store_true",
        dest="direct_only",
        help=(
            "strictly check changed sources but skip the affected Lake build; "
            "affected validation and the full audit remain required"
        ),
    )
    parser.add_argument("files", nargs="*", help="changed paths (Lean or otherwise)")
    args = parser.parse_args()
    if args.print_project_build_roots:
        if args.files:
            parser.error("--print-project-build-roots does not accept changed paths")
    elif not args.files:
        parser.error("the following arguments are required: files")
    return args


def main() -> int:
    args = parse_arguments()
    try:
        modules, _, reverse_graph = build_graph()

        if args.print_project_build_roots:
            roots = build_roots(set(modules.keys()), reverse_graph)
            for module in roots:
                print(module)
            return 0

        changed = changed_modules(args.files, modules)
        if not changed:
            print("No project Lean files selected.")
            return 0

        affected = reverse_closure(changed, reverse_graph)
        roots = build_roots(affected, reverse_graph)
        print_modules("Changed modules", changed)
        print_modules("Affected modules", affected)
        print_modules("Maximal Lake module targets", roots)
        if args.dry_run:
            return 0

        for module in sorted(changed):
            run_strict_check(module, modules[module])

        if args.direct_only:
            print(
                "Direct strict checks passed. Affected validation and the full "
                "audit remain required."
            )
            return 0

        run_affected_build(roots)
        print("Affected checks passed.")
        return 0
    except (CheckError, OSError, UnicodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
