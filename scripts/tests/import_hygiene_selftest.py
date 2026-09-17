#!/usr/bin/env python3
"""Self-test for the duplicate-import checker."""

from __future__ import annotations

import importlib.util
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "import_hygiene.py"


def load_checker():
    spec = importlib.util.spec_from_file_location("import_hygiene", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    checker = load_checker()
    original = (
        "import Example.First\n"
        "import Example.Second\n"
        "import Example.First\n"
        "\n"
        "/-! Test module. -/\n"
        "\n"
        "def answer := 42\n"
    )
    expected = (
        "import Example.First\n"
        "import Example.Second\n"
        "\n"
        "/-! Test module. -/\n"
        "\n"
        "def answer := 42\n"
    )

    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "Sample.lean"
        source.write_text(original, encoding="utf-8")

        duplicates = checker.process_file(source, fix=False)
        assert duplicates == [(3, 1, "Example.First")]
        assert source.read_text(encoding="utf-8") == original

        fixed = checker.process_file(source, fix=True)
        assert fixed == duplicates
        assert source.read_text(encoding="utf-8") == expected
        assert checker.process_file(source, fix=False) == []

    print("import hygiene self-test: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
