#!/usr/bin/env python3
"""Validate and query justified file/proof size exceptions."""
from __future__ import annotations

import argparse
import re
from pathlib import Path

HEADER = "kind\tname\treason"
MIN_REASON_CHARS = 40
GENERIC_REASON_RE = re.compile(
    r"(?:^(?:there is |this has )?(?:no natural (?:boundary|split)(?: exists)?|"
    r"cannot (?:be )?split|too (?:long|hard|complex)|exception(?: requested)?|"
    r"because (?:it|this) is (?:long|complex))[.!]?$|\b(?:boilerplate|placeholder)\b)",
    re.IGNORECASE,
)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][\w'.]*(?:\.[A-Za-z_][\w']*)*)\s*$")
SECTION_RE = re.compile(r"^section(?:\s+\S+)?\s*$")
END_RE = re.compile(r"^end(?:\s+\S+)?\s*$")
DECL_NAME_RE = re.compile(
    r"^(?:(?:private|protected|nonrec|noncomputable|partial|scoped|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|example|"
    r"macro|notation|syntax|elab|mutual|initialize|alias)\s+([^\s({\[:]+)"
)


def valid_reason(reason: str) -> str:
    """Return an error for a non-substantive reason, or the empty string."""
    text = reason.strip()
    if len(text) < MIN_REASON_CHARS:
        return "reason must contain at least %d characters" % MIN_REASON_CHARS
    if len(text.split()) < 7 or not re.search(r"[.!?]$", text):
        return "reason must be a complete, specific sentence"
    if GENERIC_REASON_RE.search(text):
        return "reason is boilerplate; describe the actual structural constraint"
    return ""


def load(path: Path) -> tuple[dict[tuple[str, str], str], list[str]]:
    """Load an allow-list, returning its keyed rows and validation errors."""
    errors: list[str] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        return {}, ["%s: %s" % (path, exc)]
    if not lines or lines[0] != HEADER:
        errors.append("%s:1: header must be exactly %r" % (path, HEADER))
    rows: dict[tuple[str, str], str] = {}
    for number, line in enumerate(lines[1:], 2):
        columns = line.split("\t")
        if len(columns) != 3:
            errors.append("%s:%d: expected kind<TAB>name<TAB>reason" % (path, number))
            continue
        kind, name, reason = (column.strip() for column in columns)
        if kind not in {"file", "proof"}:
            errors.append("%s:%d: kind must be file or proof" % (path, number))
        if not name:
            errors.append("%s:%d: name must not be empty" % (path, number))
        if kind == "file" and (name.startswith("/") or not name.endswith(".lean")):
            errors.append("%s:%d: file name must be a repo-relative .lean path" %
                          (path, number))
        if kind == "proof" and ("." not in name or "/" in name):
            errors.append("%s:%d: proof name must be fully qualified" % (path, number))
        reason_error = valid_reason(reason)
        if reason_error:
            errors.append("%s:%d: %s" % (path, number, reason_error))
        key = (kind, name)
        if key in rows:
            errors.append("%s:%d: duplicate %s entry %s" % (path, number, kind, name))
        rows[key] = reason
    return rows, errors


def top_level_flags(lines: list[str]) -> list[bool]:
    flags, depth = [], 0
    for line in lines:
        flags.append(depth == 0)
        index = 0
        while index < len(line) - 1:
            if line[index:index + 2] == "/-":
                depth += 1
                index += 2
            elif line[index:index + 2] == "-/":
                depth = max(0, depth - 1)
                index += 2
            else:
                index += 1
    return flags


def qualified_declarations(path: Path, name_re: re.Pattern[str]) -> list[tuple[str, str]]:
    """Return (fully-qualified, written) declaration names in a Lean file."""
    lines = path.read_text(encoding="utf-8").splitlines()
    flags = top_level_flags(lines)
    namespaces: list[str] = []
    scopes: list[tuple[str, int]] = []
    result = []
    for line, top_level in zip(lines, flags):
        if not top_level:
            continue
        stripped = line.strip()
        namespace = NAMESPACE_RE.match(stripped)
        if namespace:
            parts = namespace.group(1).split(".")
            namespaces.extend(parts)
            scopes.append(("namespace", len(parts)))
            continue
        if SECTION_RE.match(stripped):
            scopes.append(("section", 0))
            continue
        if END_RE.match(stripped):
            if scopes:
                kind, count = scopes.pop()
                if kind == "namespace" and count:
                    del namespaces[-count:]
            continue
        declaration = name_re.match(line)
        if not declaration:
            continue
        written = declaration.group(1)
        if written.startswith("_root_."):
            qualified = written[len("_root_."):]
        else:
            qualified = ".".join(namespaces + [written])
        result.append((qualified, written))
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--path", type=Path)
    parser.add_argument("--kind", choices=["file", "proof"])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--declarations", type=Path,
                        help="print fully-qualified and written declaration names")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    path = args.path or root / "docs/history/size_allow.tsv"
    if args.declarations:
        declaration_path = args.declarations
        if not declaration_path.is_absolute():
            declaration_path = root / declaration_path
        for qualified, written in qualified_declarations(declaration_path, DECL_NAME_RE):
            print("%s\t%s" % (qualified, written))
        return
    rows, errors = load(path)
    if errors:
        raise SystemExit("\n".join(errors))
    if args.kind:
        for kind, name in rows:
            if kind == args.kind:
                print(name)
    elif args.check:
        print("size allow-list OK (%d entries)" % len(rows))


if __name__ == "__main__":
    main()
